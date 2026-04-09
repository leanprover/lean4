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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_ST_Prim_Ref_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_ExprStructEq_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_ExprStructEq_beq(lean_object*, lean_object*);
lean_object* l_Lean_Core_checkSystem(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLetFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepthErrorMessage;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sym"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__0_value;
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "issues"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(230, 3, 132, 38, 134, 149, 222, 229)}};
static const lean_ctor_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(255, 90, 109, 68, 195, 255, 174, 185)}};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__2_value;
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "found `Expr.proj` with invalid field index `"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__9;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__10;
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "found `Expr.proj` but `"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_Grind_foldProjs___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "` is not marked as structure"};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__0___closed__13_value;
static lean_once_cell_t l_Lean_Meta_Grind_foldProjs___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___closed__14;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Grind_foldProjs___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 2}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Grind_foldProjs___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___closed__0 = (const lean_object*)&l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__9(uint8_t, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Grind_foldProjs___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Expr_isProj___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_foldProjs___closed__0 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___closed__0_value;
static const lean_closure_object l_Lean_Meta_Grind_foldProjs___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_foldProjs___lam__0___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_foldProjs___closed__1 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___closed__1_value;
static const lean_closure_object l_Lean_Meta_Grind_foldProjs___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Grind_foldProjs___lam__1___boxed, .m_arity = 6, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Grind_foldProjs___closed__2 = (const lean_object*)&l_Lean_Meta_Grind_foldProjs___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_1361__overap_153_; lean_object* v___x_154_; 
v___x_151_ = l_Lean_instInhabitedLocalContext_default;
v___x_152_ = l_instInhabitedOfMonad___redArg(v___x_150_, v___x_151_);
v___x_1361__overap_153_ = lean_panic_fn_borrowed(v___x_152_, v_msg_96_);
lean_dec(v___x_152_);
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
lean_inc(v___y_98_);
lean_inc_ref(v___y_97_);
v___x_154_ = lean_apply_5(v___x_1361__overap_153_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, lean_box(0));
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
v___x_221_ = lean_unsigned_to_nat(635u);
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
lean_dec_ref(v___x_230_);
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
lean_dec_ref(v___x_358_);
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
size_t v_x_4510__boxed_452_; size_t v_x_4511__boxed_453_; lean_object* v_res_454_; 
v_x_4510__boxed_452_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_x_4511__boxed_453_ = lean_unbox_usize(v_x_445_);
lean_dec(v_x_445_);
v_res_454_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_442_, v_x_443_, v_x_4510__boxed_452_, v_x_4511__boxed_453_, v_x_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
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
size_t v_x_4896__boxed_719_; size_t v_x_4897__boxed_720_; lean_object* v_res_721_; 
v_x_4896__boxed_719_ = lean_unbox_usize(v_x_715_);
lean_dec(v_x_715_);
v_x_4897__boxed_720_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_res_721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_714_, v_x_4896__boxed_719_, v_x_4897__boxed_720_, v_x_717_, v_x_718_);
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
lean_object* v___x_733_; lean_object* v_mctx_734_; lean_object* v_cache_735_; lean_object* v_zetaDeltaFVarIds_736_; lean_object* v_postponed_737_; lean_object* v_diag_738_; lean_object* v___x_740_; uint8_t v_isShared_741_; uint8_t v_isSharedCheck_766_; 
v___x_733_ = lean_st_ref_take(v___y_731_);
v_mctx_734_ = lean_ctor_get(v___x_733_, 0);
v_cache_735_ = lean_ctor_get(v___x_733_, 1);
v_zetaDeltaFVarIds_736_ = lean_ctor_get(v___x_733_, 2);
v_postponed_737_ = lean_ctor_get(v___x_733_, 3);
v_diag_738_ = lean_ctor_get(v___x_733_, 4);
v_isSharedCheck_766_ = !lean_is_exclusive(v___x_733_);
if (v_isSharedCheck_766_ == 0)
{
v___x_740_ = v___x_733_;
v_isShared_741_ = v_isSharedCheck_766_;
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
v_isShared_741_ = v_isSharedCheck_766_;
goto v_resetjp_739_;
}
v_resetjp_739_:
{
lean_object* v_depth_742_; lean_object* v_levelAssignDepth_743_; lean_object* v_lmvarCounter_744_; lean_object* v_mvarCounter_745_; lean_object* v_lDecls_746_; lean_object* v_decls_747_; lean_object* v_userNames_748_; lean_object* v_lAssignment_749_; lean_object* v_eAssignment_750_; lean_object* v_dAssignment_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_765_; 
v_depth_742_ = lean_ctor_get(v_mctx_734_, 0);
v_levelAssignDepth_743_ = lean_ctor_get(v_mctx_734_, 1);
v_lmvarCounter_744_ = lean_ctor_get(v_mctx_734_, 2);
v_mvarCounter_745_ = lean_ctor_get(v_mctx_734_, 3);
v_lDecls_746_ = lean_ctor_get(v_mctx_734_, 4);
v_decls_747_ = lean_ctor_get(v_mctx_734_, 5);
v_userNames_748_ = lean_ctor_get(v_mctx_734_, 6);
v_lAssignment_749_ = lean_ctor_get(v_mctx_734_, 7);
v_eAssignment_750_ = lean_ctor_get(v_mctx_734_, 8);
v_dAssignment_751_ = lean_ctor_get(v_mctx_734_, 9);
v_isSharedCheck_765_ = !lean_is_exclusive(v_mctx_734_);
if (v_isSharedCheck_765_ == 0)
{
v___x_753_ = v_mctx_734_;
v_isShared_754_ = v_isSharedCheck_765_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_dAssignment_751_);
lean_inc(v_eAssignment_750_);
lean_inc(v_lAssignment_749_);
lean_inc(v_userNames_748_);
lean_inc(v_decls_747_);
lean_inc(v_lDecls_746_);
lean_inc(v_mvarCounter_745_);
lean_inc(v_lmvarCounter_744_);
lean_inc(v_levelAssignDepth_743_);
lean_inc(v_depth_742_);
lean_dec(v_mctx_734_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_765_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_755_; lean_object* v___x_757_; 
v___x_755_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_eAssignment_750_, v_mvarId_729_, v_val_730_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 8, v___x_755_);
v___x_757_ = v___x_753_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_764_; 
v_reuseFailAlloc_764_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_764_, 0, v_depth_742_);
lean_ctor_set(v_reuseFailAlloc_764_, 1, v_levelAssignDepth_743_);
lean_ctor_set(v_reuseFailAlloc_764_, 2, v_lmvarCounter_744_);
lean_ctor_set(v_reuseFailAlloc_764_, 3, v_mvarCounter_745_);
lean_ctor_set(v_reuseFailAlloc_764_, 4, v_lDecls_746_);
lean_ctor_set(v_reuseFailAlloc_764_, 5, v_decls_747_);
lean_ctor_set(v_reuseFailAlloc_764_, 6, v_userNames_748_);
lean_ctor_set(v_reuseFailAlloc_764_, 7, v_lAssignment_749_);
lean_ctor_set(v_reuseFailAlloc_764_, 8, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_764_, 9, v_dAssignment_751_);
v___x_757_ = v_reuseFailAlloc_764_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_759_; 
if (v_isShared_741_ == 0)
{
lean_ctor_set(v___x_740_, 0, v___x_757_);
v___x_759_ = v___x_740_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_cache_735_);
lean_ctor_set(v_reuseFailAlloc_763_, 2, v_zetaDeltaFVarIds_736_);
lean_ctor_set(v_reuseFailAlloc_763_, 3, v_postponed_737_);
lean_ctor_set(v_reuseFailAlloc_763_, 4, v_diag_738_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_760_ = lean_st_ref_set(v___y_731_, v___x_759_);
v___x_761_ = lean_box(0);
v___x_762_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_762_, 0, v___x_761_);
return v___x_762_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg___boxed(lean_object* v_mvarId_767_, lean_object* v_val_768_, lean_object* v___y_769_, lean_object* v___y_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_767_, v_val_768_, v___y_769_);
lean_dec(v___y_769_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars(lean_object* v_mvarId_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_778_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_772_);
v___x_779_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_772_, v___x_778_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v___x_780_; 
lean_dec_ref(v___x_779_);
lean_inc(v_mvarId_772_);
v___x_780_ = l_Lean_MVarId_getDecl(v_mvarId_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_780_) == 0)
{
lean_object* v_a_781_; lean_object* v_userName_782_; lean_object* v_lctx_783_; lean_object* v_type_784_; lean_object* v_localInstances_785_; lean_object* v___x_786_; 
v_a_781_ = lean_ctor_get(v___x_780_, 0);
lean_inc(v_a_781_);
lean_dec_ref(v___x_780_);
v_userName_782_ = lean_ctor_get(v_a_781_, 0);
lean_inc(v_userName_782_);
v_lctx_783_ = lean_ctor_get(v_a_781_, 1);
lean_inc_ref(v_lctx_783_);
v_type_784_ = lean_ctor_get(v_a_781_, 2);
lean_inc_ref(v_type_784_);
v_localInstances_785_ = lean_ctor_get(v_a_781_, 4);
lean_inc_ref(v_localInstances_785_);
lean_dec(v_a_781_);
v___x_786_ = l_Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0(v_lctx_783_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_786_) == 0)
{
lean_object* v_a_787_; lean_object* v___x_788_; lean_object* v_a_789_; uint8_t v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v_a_787_ = lean_ctor_get(v___x_786_, 0);
lean_inc(v_a_787_);
lean_dec_ref(v___x_786_);
v___x_788_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_type_784_, v_a_774_);
v_a_789_ = lean_ctor_get(v___x_788_, 0);
lean_inc(v_a_789_);
lean_dec_ref(v___x_788_);
v___x_790_ = 2;
v___x_791_ = lean_unsigned_to_nat(0u);
v___x_792_ = l_Lean_Meta_mkFreshExprMVarAt(v_a_787_, v_localInstances_785_, v_a_789_, v___x_790_, v_userName_782_, v___x_791_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
if (lean_obj_tag(v___x_792_) == 0)
{
lean_object* v_a_793_; lean_object* v___x_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_802_; 
v_a_793_ = lean_ctor_get(v___x_792_, 0);
lean_inc_n(v_a_793_, 2);
lean_dec_ref(v___x_792_);
v___x_794_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_772_, v_a_793_, v_a_774_);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_794_);
if (v_isSharedCheck_802_ == 0)
{
lean_object* v_unused_803_; 
v_unused_803_ = lean_ctor_get(v___x_794_, 0);
lean_dec(v_unused_803_);
v___x_796_ = v___x_794_;
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
else
{
lean_dec(v___x_794_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_802_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; lean_object* v___x_800_; 
v___x_798_ = l_Lean_Expr_mvarId_x21(v_a_793_);
lean_dec(v_a_793_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 0, v___x_798_);
v___x_800_ = v___x_796_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_798_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_mvarId_772_);
v_a_804_ = lean_ctor_get(v___x_792_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_792_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_792_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_792_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v_localInstances_785_);
lean_dec_ref(v_type_784_);
lean_dec(v_userName_782_);
lean_dec(v_mvarId_772_);
v_a_812_ = lean_ctor_get(v___x_786_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_786_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_786_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_786_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec(v_mvarId_772_);
v_a_820_ = lean_ctor_get(v___x_780_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_780_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_780_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_780_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
else
{
lean_object* v_a_828_; lean_object* v___x_830_; uint8_t v_isShared_831_; uint8_t v_isSharedCheck_835_; 
lean_dec(v_mvarId_772_);
v_a_828_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_835_ == 0)
{
v___x_830_ = v___x_779_;
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
else
{
lean_inc(v_a_828_);
lean_dec(v___x_779_);
v___x_830_ = lean_box(0);
v_isShared_831_ = v_isSharedCheck_835_;
goto v_resetjp_829_;
}
v_resetjp_829_:
{
lean_object* v___x_833_; 
if (v_isShared_831_ == 0)
{
v___x_833_ = v___x_830_;
goto v_reusejp_832_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
v___x_833_ = v_reuseFailAlloc_834_;
goto v_reusejp_832_;
}
v_reusejp_832_:
{
return v___x_833_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_instantiateGoalMVars___boxed(lean_object* v_mvarId_836_, lean_object* v_a_837_, lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l_Lean_MVarId_instantiateGoalMVars(v_mvarId_836_, v_a_837_, v_a_838_, v_a_839_, v_a_840_);
lean_dec(v_a_840_);
lean_dec_ref(v_a_839_);
lean_dec(v_a_838_);
lean_dec_ref(v_a_837_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(lean_object* v_mvarId_843_, lean_object* v_val_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_843_, v_val_844_, v___y_846_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___boxed(lean_object* v_mvarId_851_, lean_object* v_val_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_, lean_object* v___y_856_, lean_object* v___y_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1(v_mvarId_851_, v_val_852_, v___y_853_, v___y_854_, v___y_855_, v___y_856_);
lean_dec(v___y_856_);
lean_dec_ref(v___y_855_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(lean_object* v_00_u03b4_859_, lean_object* v_t_860_, lean_object* v_k_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___redArg(v_t_860_, v_k_861_);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0___boxed(lean_object* v_00_u03b4_863_, lean_object* v_t_864_, lean_object* v_k_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__0(v_00_u03b4_863_, v_t_864_, v_k_865_);
lean_dec(v_k_865_);
lean_dec(v_t_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4(lean_object* v_00_u03b2_867_, lean_object* v_x_868_, lean_object* v_x_869_, lean_object* v_x_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4___redArg(v_x_868_, v_x_869_, v_x_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(lean_object* v_00_u03b2_872_, lean_object* v_x_873_, size_t v_x_874_, size_t v_x_875_, lean_object* v_x_876_, lean_object* v_x_877_){
_start:
{
lean_object* v___x_878_; 
v___x_878_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_873_, v_x_874_, v_x_875_, v_x_876_, v_x_877_);
return v___x_878_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___boxed(lean_object* v_00_u03b2_879_, lean_object* v_x_880_, lean_object* v_x_881_, lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_x_884_){
_start:
{
size_t v_x_5262__boxed_885_; size_t v_x_5263__boxed_886_; lean_object* v_res_887_; 
v_x_5262__boxed_885_ = lean_unbox_usize(v_x_881_);
lean_dec(v_x_881_);
v_x_5263__boxed_886_ = lean_unbox_usize(v_x_882_);
lean_dec(v_x_882_);
v_res_887_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(v_00_u03b2_879_, v_x_880_, v_x_5262__boxed_885_, v_x_5263__boxed_886_, v_x_883_, v_x_884_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10(lean_object* v_00_u03b2_888_, lean_object* v_n_889_, lean_object* v_k_890_, lean_object* v_v_891_){
_start:
{
lean_object* v___x_892_; 
v___x_892_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10___redArg(v_n_889_, v_k_890_, v_v_891_);
return v___x_892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(lean_object* v_00_u03b2_893_, size_t v_depth_894_, lean_object* v_keys_895_, lean_object* v_vals_896_, lean_object* v_heq_897_, lean_object* v_i_898_, lean_object* v_entries_899_){
_start:
{
lean_object* v___x_900_; 
v___x_900_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___redArg(v_depth_894_, v_keys_895_, v_vals_896_, v_i_898_, v_entries_899_);
return v___x_900_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11___boxed(lean_object* v_00_u03b2_901_, lean_object* v_depth_902_, lean_object* v_keys_903_, lean_object* v_vals_904_, lean_object* v_heq_905_, lean_object* v_i_906_, lean_object* v_entries_907_){
_start:
{
size_t v_depth_boxed_908_; lean_object* v_res_909_; 
v_depth_boxed_908_ = lean_unbox_usize(v_depth_902_);
lean_dec(v_depth_902_);
v_res_909_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__11(v_00_u03b2_901_, v_depth_boxed_908_, v_keys_903_, v_vals_904_, v_heq_905_, v_i_906_, v_entries_907_);
lean_dec_ref(v_vals_904_);
lean_dec_ref(v_keys_903_);
return v_res_909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12(lean_object* v_00_u03b2_910_, lean_object* v_x_911_, lean_object* v_x_912_, lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
lean_object* v___x_915_; 
v___x_915_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6_spec__10_spec__12___redArg(v_x_911_, v_x_912_, v_x_913_, v_x_914_);
return v___x_915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(lean_object* v_k_916_, lean_object* v_b_917_, lean_object* v_c_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_){
_start:
{
lean_object* v___x_924_; 
lean_inc(v___y_922_);
lean_inc_ref(v___y_921_);
lean_inc(v___y_920_);
lean_inc_ref(v___y_919_);
v___x_924_ = lean_apply_7(v_k_916_, v_b_917_, v_c_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, lean_box(0));
return v___x_924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed(lean_object* v_k_925_, lean_object* v_b_926_, lean_object* v_c_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(v_k_925_, v_b_926_, v_c_927_, v___y_928_, v___y_929_, v___y_930_, v___y_931_);
lean_dec(v___y_931_);
lean_dec_ref(v___y_930_);
lean_dec(v___y_929_);
lean_dec_ref(v___y_928_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(lean_object* v_e_934_, lean_object* v_k_935_, uint8_t v_cleanupAnnotations_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_){
_start:
{
lean_object* v___f_942_; uint8_t v___x_943_; uint8_t v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; 
v___f_942_ = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_942_, 0, v_k_935_);
v___x_943_ = 1;
v___x_944_ = 0;
v___x_945_ = lean_box(0);
v___x_946_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(lean_box(0), v_e_934_, v___x_943_, v___x_944_, v___x_943_, v___x_944_, v___x_945_, v___f_942_, v_cleanupAnnotations_936_, v___y_937_, v___y_938_, v___y_939_, v___y_940_);
if (lean_obj_tag(v___x_946_) == 0)
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
v_a_947_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_946_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_946_);
v___x_949_ = lean_box(0);
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
v_resetjp_948_:
{
lean_object* v___x_952_; 
if (v_isShared_950_ == 0)
{
v___x_952_ = v___x_949_;
goto v_reusejp_951_;
}
else
{
lean_object* v_reuseFailAlloc_953_; 
v_reuseFailAlloc_953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
v___x_952_ = v_reuseFailAlloc_953_;
goto v_reusejp_951_;
}
v_reusejp_951_:
{
return v___x_952_;
}
}
}
else
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_962_; 
v_a_955_ = lean_ctor_get(v___x_946_, 0);
v_isSharedCheck_962_ = !lean_is_exclusive(v___x_946_);
if (v_isSharedCheck_962_ == 0)
{
v___x_957_ = v___x_946_;
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_946_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_962_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
lean_object* v___x_960_; 
if (v_isShared_958_ == 0)
{
v___x_960_ = v___x_957_;
goto v_reusejp_959_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_a_955_);
v___x_960_ = v_reuseFailAlloc_961_;
goto v_reusejp_959_;
}
v_reusejp_959_:
{
return v___x_960_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___boxed(lean_object* v_e_963_, lean_object* v_k_964_, lean_object* v_cleanupAnnotations_965_, lean_object* v___y_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_971_; lean_object* v_res_972_; 
v_cleanupAnnotations_boxed_971_ = lean_unbox(v_cleanupAnnotations_965_);
v_res_972_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_963_, v_k_964_, v_cleanupAnnotations_boxed_971_, v___y_966_, v___y_967_, v___y_968_, v___y_969_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
lean_dec(v___y_967_);
lean_dec_ref(v___y_966_);
return v_res_972_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(lean_object* v_00_u03b1_973_, lean_object* v_e_974_, lean_object* v_k_975_, uint8_t v_cleanupAnnotations_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_){
_start:
{
lean_object* v___x_982_; 
v___x_982_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_e_974_, v_k_975_, v_cleanupAnnotations_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___boxed(lean_object* v_00_u03b1_983_, lean_object* v_e_984_, lean_object* v_k_985_, lean_object* v_cleanupAnnotations_986_, lean_object* v___y_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_992_; lean_object* v_res_993_; 
v_cleanupAnnotations_boxed_992_ = lean_unbox(v_cleanupAnnotations_986_);
v_res_993_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0(v_00_u03b1_983_, v_e_984_, v_k_985_, v_cleanupAnnotations_boxed_992_, v___y_987_, v___y_988_, v___y_989_, v___y_990_);
lean_dec(v___y_990_);
lean_dec_ref(v___y_989_);
lean_dec(v___y_988_);
lean_dec_ref(v___y_987_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(lean_object* v_mvarId_994_, lean_object* v_x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_){
_start:
{
lean_object* v___x_1001_; 
v___x_1001_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_994_, v_x_995_, v___y_996_, v___y_997_, v___y_998_, v___y_999_);
if (lean_obj_tag(v___x_1001_) == 0)
{
lean_object* v_a_1002_; lean_object* v___x_1004_; uint8_t v_isShared_1005_; uint8_t v_isSharedCheck_1009_; 
v_a_1002_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_1004_ = v___x_1001_;
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
else
{
lean_inc(v_a_1002_);
lean_dec(v___x_1001_);
v___x_1004_ = lean_box(0);
v_isShared_1005_ = v_isSharedCheck_1009_;
goto v_resetjp_1003_;
}
v_resetjp_1003_:
{
lean_object* v___x_1007_; 
if (v_isShared_1005_ == 0)
{
v___x_1007_ = v___x_1004_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_1001_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1001_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_1001_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_1001_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg___boxed(lean_object* v_mvarId_1018_, lean_object* v_x_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1018_, v_x_1019_, v___y_1020_, v___y_1021_, v___y_1022_, v___y_1023_);
lean_dec(v___y_1023_);
lean_dec_ref(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec_ref(v___y_1020_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(lean_object* v_00_u03b1_1026_, lean_object* v_mvarId_1027_, lean_object* v_x_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
lean_object* v___x_1034_; 
v___x_1034_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1027_, v_x_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
return v___x_1034_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___boxed(lean_object* v_00_u03b1_1035_, lean_object* v_mvarId_1036_, lean_object* v_x_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
lean_object* v_res_1043_; 
v_res_1043_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1(v_00_u03b1_1035_, v_mvarId_1036_, v_x_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
return v_res_1043_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0(uint8_t v___x_1044_, uint8_t v___x_1045_, lean_object* v_xs_1046_, lean_object* v_body_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
uint8_t v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = 1;
v___x_1054_ = l_Lean_Meta_mkForallFVars(v_xs_1046_, v_body_1047_, v___x_1044_, v___x_1045_, v___x_1045_, v___x_1053_, v___y_1048_, v___y_1049_, v___y_1050_, v___y_1051_);
return v___x_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__0___boxed(lean_object* v___x_1055_, lean_object* v___x_1056_, lean_object* v_xs_1057_, lean_object* v_body_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
uint8_t v___x_1951__boxed_1064_; uint8_t v___x_1952__boxed_1065_; lean_object* v_res_1066_; 
v___x_1951__boxed_1064_ = lean_unbox(v___x_1055_);
v___x_1952__boxed_1065_ = lean_unbox(v___x_1056_);
v_res_1066_ = l_Lean_MVarId_abstractMVars___lam__0(v___x_1951__boxed_1064_, v___x_1952__boxed_1065_, v_xs_1057_, v_body_1058_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
lean_dec(v___y_1062_);
lean_dec_ref(v___y_1061_);
lean_dec(v___y_1060_);
lean_dec_ref(v___y_1059_);
lean_dec_ref(v_xs_1057_);
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1(lean_object* v_a_1067_, uint8_t v___x_1068_, lean_object* v___f_1069_, lean_object* v_mvarId_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = l_Lean_Meta_abstractMVars(v_a_1067_, v___x_1068_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1076_) == 0)
{
lean_object* v_a_1077_; lean_object* v_mvars_1078_; lean_object* v_expr_1079_; lean_object* v___x_1080_; 
v_a_1077_ = lean_ctor_get(v___x_1076_, 0);
lean_inc(v_a_1077_);
lean_dec_ref(v___x_1076_);
v_mvars_1078_ = lean_ctor_get(v_a_1077_, 1);
lean_inc_ref(v_mvars_1078_);
v_expr_1079_ = lean_ctor_get(v_a_1077_, 2);
lean_inc_ref(v_expr_1079_);
lean_dec(v_a_1077_);
v___x_1080_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg(v_expr_1079_, v___f_1069_, v___x_1068_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___x_1082_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref(v___x_1080_);
lean_inc(v_mvarId_1070_);
v___x_1082_ = l_Lean_MVarId_getTag(v_mvarId_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_object* v_a_1083_; lean_object* v___x_1084_; 
v_a_1083_ = lean_ctor_get(v___x_1082_, 0);
lean_inc(v_a_1083_);
lean_dec_ref(v___x_1082_);
v___x_1084_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1081_, v_a_1083_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1095_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc_n(v_a_1085_, 2);
lean_dec_ref(v___x_1084_);
v___x_1086_ = l_Lean_mkAppN(v_a_1085_, v_mvars_1078_);
lean_dec_ref(v_mvars_1078_);
v___x_1087_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1070_, v___x_1086_, v___y_1072_);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1095_ == 0)
{
lean_object* v_unused_1096_; 
v_unused_1096_ = lean_ctor_get(v___x_1087_, 0);
lean_dec(v_unused_1096_);
v___x_1089_ = v___x_1087_;
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v___x_1087_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = l_Lean_Expr_mvarId_x21(v_a_1085_);
lean_dec(v_a_1085_);
if (v_isShared_1090_ == 0)
{
lean_ctor_set(v___x_1089_, 0, v___x_1091_);
v___x_1093_ = v___x_1089_;
goto v_reusejp_1092_;
}
else
{
lean_object* v_reuseFailAlloc_1094_; 
v_reuseFailAlloc_1094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1094_, 0, v___x_1091_);
v___x_1093_ = v_reuseFailAlloc_1094_;
goto v_reusejp_1092_;
}
v_reusejp_1092_:
{
return v___x_1093_;
}
}
}
else
{
lean_object* v_a_1097_; lean_object* v___x_1099_; uint8_t v_isShared_1100_; uint8_t v_isSharedCheck_1104_; 
lean_dec_ref(v_mvars_1078_);
lean_dec(v_mvarId_1070_);
v_a_1097_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1104_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1099_ = v___x_1084_;
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
else
{
lean_inc(v_a_1097_);
lean_dec(v___x_1084_);
v___x_1099_ = lean_box(0);
v_isShared_1100_ = v_isSharedCheck_1104_;
goto v_resetjp_1098_;
}
v_resetjp_1098_:
{
lean_object* v___x_1102_; 
if (v_isShared_1100_ == 0)
{
v___x_1102_ = v___x_1099_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_a_1097_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
else
{
lean_object* v_a_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1112_; 
lean_dec(v_a_1081_);
lean_dec_ref(v_mvars_1078_);
lean_dec(v_mvarId_1070_);
v_a_1105_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1112_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1112_ == 0)
{
v___x_1107_ = v___x_1082_;
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_a_1105_);
lean_dec(v___x_1082_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1112_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v___x_1110_; 
if (v_isShared_1108_ == 0)
{
v___x_1110_ = v___x_1107_;
goto v_reusejp_1109_;
}
else
{
lean_object* v_reuseFailAlloc_1111_; 
v_reuseFailAlloc_1111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_a_1105_);
v___x_1110_ = v_reuseFailAlloc_1111_;
goto v_reusejp_1109_;
}
v_reusejp_1109_:
{
return v___x_1110_;
}
}
}
}
else
{
lean_object* v_a_1113_; lean_object* v___x_1115_; uint8_t v_isShared_1116_; uint8_t v_isSharedCheck_1120_; 
lean_dec_ref(v_mvars_1078_);
lean_dec(v_mvarId_1070_);
v_a_1113_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1115_ = v___x_1080_;
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
else
{
lean_inc(v_a_1113_);
lean_dec(v___x_1080_);
v___x_1115_ = lean_box(0);
v_isShared_1116_ = v_isSharedCheck_1120_;
goto v_resetjp_1114_;
}
v_resetjp_1114_:
{
lean_object* v___x_1118_; 
if (v_isShared_1116_ == 0)
{
v___x_1118_ = v___x_1115_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v_a_1113_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_mvarId_1070_);
lean_dec_ref(v___f_1069_);
v_a_1121_ = lean_ctor_get(v___x_1076_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1076_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1076_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1076_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___lam__1___boxed(lean_object* v_a_1129_, lean_object* v___x_1130_, lean_object* v___f_1131_, lean_object* v_mvarId_1132_, lean_object* v___y_1133_, lean_object* v___y_1134_, lean_object* v___y_1135_, lean_object* v___y_1136_, lean_object* v___y_1137_){
_start:
{
uint8_t v___x_1977__boxed_1138_; lean_object* v_res_1139_; 
v___x_1977__boxed_1138_ = lean_unbox(v___x_1130_);
v_res_1139_ = l_Lean_MVarId_abstractMVars___lam__1(v_a_1129_, v___x_1977__boxed_1138_, v___f_1131_, v_mvarId_1132_, v___y_1133_, v___y_1134_, v___y_1135_, v___y_1136_);
lean_dec(v___y_1136_);
lean_dec_ref(v___y_1135_);
lean_dec(v___y_1134_);
lean_dec_ref(v___y_1133_);
return v_res_1139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars(lean_object* v_mvarId_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_, lean_object* v_a_1144_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1146_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_1140_);
v___x_1147_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1140_, v___x_1146_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
if (lean_obj_tag(v___x_1147_) == 0)
{
lean_object* v___x_1148_; 
lean_dec_ref(v___x_1147_);
lean_inc(v_mvarId_1140_);
v___x_1148_ = l_Lean_MVarId_getType(v_mvarId_1140_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
if (lean_obj_tag(v___x_1148_) == 0)
{
lean_object* v_a_1149_; lean_object* v___x_1150_; lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1166_; 
v_a_1149_ = lean_ctor_get(v___x_1148_, 0);
lean_inc(v_a_1149_);
lean_dec_ref(v___x_1148_);
v___x_1150_ = l_Lean_instantiateMVars___at___00Lean_MVarId_ensureNoMVar_spec__0___redArg(v_a_1149_, v_a_1142_);
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1166_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1166_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
uint8_t v___x_1155_; 
v___x_1155_ = l_Lean_Expr_hasExprMVar(v_a_1151_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1157_; 
lean_dec(v_a_1151_);
if (v_isShared_1154_ == 0)
{
lean_ctor_set(v___x_1153_, 0, v_mvarId_1140_);
v___x_1157_ = v___x_1153_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_mvarId_1140_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
else
{
uint8_t v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___f_1162_; lean_object* v___x_1163_; lean_object* v___f_1164_; lean_object* v___x_1165_; 
lean_del_object(v___x_1153_);
v___x_1159_ = 0;
v___x_1160_ = lean_box(v___x_1159_);
v___x_1161_ = lean_box(v___x_1155_);
v___f_1162_ = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__0___boxed), 9, 2);
lean_closure_set(v___f_1162_, 0, v___x_1160_);
lean_closure_set(v___f_1162_, 1, v___x_1161_);
v___x_1163_ = lean_box(v___x_1159_);
lean_inc(v_mvarId_1140_);
v___f_1164_ = lean_alloc_closure((void*)(l_Lean_MVarId_abstractMVars___lam__1___boxed), 9, 4);
lean_closure_set(v___f_1164_, 0, v_a_1151_);
lean_closure_set(v___f_1164_, 1, v___x_1163_);
lean_closure_set(v___f_1164_, 2, v___f_1162_);
lean_closure_set(v___f_1164_, 3, v_mvarId_1140_);
v___x_1165_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1140_, v___f_1164_, v_a_1141_, v_a_1142_, v_a_1143_, v_a_1144_);
return v___x_1165_;
}
}
}
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
lean_dec(v_mvarId_1140_);
v_a_1167_ = lean_ctor_get(v___x_1148_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1148_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1148_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1148_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
else
{
lean_object* v_a_1175_; lean_object* v___x_1177_; uint8_t v_isShared_1178_; uint8_t v_isSharedCheck_1182_; 
lean_dec(v_mvarId_1140_);
v_a_1175_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1182_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1182_ == 0)
{
v___x_1177_ = v___x_1147_;
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
else
{
lean_inc(v_a_1175_);
lean_dec(v___x_1147_);
v___x_1177_ = lean_box(0);
v_isShared_1178_ = v_isSharedCheck_1182_;
goto v_resetjp_1176_;
}
v_resetjp_1176_:
{
lean_object* v___x_1180_; 
if (v_isShared_1178_ == 0)
{
v___x_1180_ = v___x_1177_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1181_; 
v_reuseFailAlloc_1181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1181_, 0, v_a_1175_);
v___x_1180_ = v_reuseFailAlloc_1181_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
return v___x_1180_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_abstractMVars___boxed(lean_object* v_mvarId_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l_Lean_MVarId_abstractMVars(v_mvarId_1183_, v_a_1184_, v_a_1185_, v_a_1186_, v_a_1187_);
lean_dec(v_a_1187_);
lean_dec_ref(v_a_1186_);
lean_dec(v_a_1185_);
lean_dec_ref(v_a_1184_);
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0(lean_object* v_mvarId_1190_, lean_object* v___x_1191_, lean_object* v_f_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_){
_start:
{
lean_object* v___x_1198_; 
lean_inc(v_mvarId_1190_);
v___x_1198_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1190_, v___x_1191_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1198_) == 0)
{
lean_object* v___x_1199_; 
lean_dec_ref(v___x_1198_);
lean_inc(v_mvarId_1190_);
v___x_1199_ = l_Lean_MVarId_getTag(v_mvarId_1190_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1199_) == 0)
{
lean_object* v_a_1200_; lean_object* v___x_1201_; 
v_a_1200_ = lean_ctor_get(v___x_1199_, 0);
lean_inc(v_a_1200_);
lean_dec_ref(v___x_1199_);
lean_inc(v_mvarId_1190_);
v___x_1201_ = l_Lean_MVarId_getType(v_mvarId_1190_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1203_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref(v___x_1201_);
lean_inc(v___y_1196_);
lean_inc_ref(v___y_1195_);
lean_inc(v___y_1194_);
lean_inc_ref(v___y_1193_);
v___x_1203_ = lean_apply_6(v_f_1192_, v_a_1202_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_, lean_box(0));
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1205_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref(v___x_1203_);
v___x_1205_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1204_, v_a_1200_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec_ref(v___y_1193_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1215_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc_n(v_a_1206_, 2);
lean_dec_ref(v___x_1205_);
v___x_1207_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1190_, v_a_1206_, v___y_1194_);
lean_dec(v___y_1194_);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1207_);
if (v_isSharedCheck_1215_ == 0)
{
lean_object* v_unused_1216_; 
v_unused_1216_ = lean_ctor_get(v___x_1207_, 0);
lean_dec(v_unused_1216_);
v___x_1209_ = v___x_1207_;
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
else
{
lean_dec(v___x_1207_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = l_Lean_Expr_mvarId_x21(v_a_1206_);
lean_dec(v_a_1206_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1211_);
v___x_1213_ = v___x_1209_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
else
{
lean_object* v_a_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1224_; 
lean_dec(v___y_1194_);
lean_dec(v_mvarId_1190_);
v_a_1217_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1224_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1224_ == 0)
{
v___x_1219_ = v___x_1205_;
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_a_1217_);
lean_dec(v___x_1205_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1224_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1222_; 
if (v_isShared_1220_ == 0)
{
v___x_1222_ = v___x_1219_;
goto v_reusejp_1221_;
}
else
{
lean_object* v_reuseFailAlloc_1223_; 
v_reuseFailAlloc_1223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1223_, 0, v_a_1217_);
v___x_1222_ = v_reuseFailAlloc_1223_;
goto v_reusejp_1221_;
}
v_reusejp_1221_:
{
return v___x_1222_;
}
}
}
}
else
{
lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1232_; 
lean_dec(v_a_1200_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v_mvarId_1190_);
v_a_1225_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1232_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1232_ == 0)
{
v___x_1227_ = v___x_1203_;
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_dec(v___x_1203_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1232_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1230_; 
if (v_isShared_1228_ == 0)
{
v___x_1230_ = v___x_1227_;
goto v_reusejp_1229_;
}
else
{
lean_object* v_reuseFailAlloc_1231_; 
v_reuseFailAlloc_1231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1231_, 0, v_a_1225_);
v___x_1230_ = v_reuseFailAlloc_1231_;
goto v_reusejp_1229_;
}
v_reusejp_1229_:
{
return v___x_1230_;
}
}
}
}
else
{
lean_object* v_a_1233_; lean_object* v___x_1235_; uint8_t v_isShared_1236_; uint8_t v_isSharedCheck_1240_; 
lean_dec(v_a_1200_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_f_1192_);
lean_dec(v_mvarId_1190_);
v_a_1233_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1240_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1240_ == 0)
{
v___x_1235_ = v___x_1201_;
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
else
{
lean_inc(v_a_1233_);
lean_dec(v___x_1201_);
v___x_1235_ = lean_box(0);
v_isShared_1236_ = v_isSharedCheck_1240_;
goto v_resetjp_1234_;
}
v_resetjp_1234_:
{
lean_object* v___x_1238_; 
if (v_isShared_1236_ == 0)
{
v___x_1238_ = v___x_1235_;
goto v_reusejp_1237_;
}
else
{
lean_object* v_reuseFailAlloc_1239_; 
v_reuseFailAlloc_1239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_a_1233_);
v___x_1238_ = v_reuseFailAlloc_1239_;
goto v_reusejp_1237_;
}
v_reusejp_1237_:
{
return v___x_1238_;
}
}
}
}
else
{
lean_object* v_a_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1248_; 
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_f_1192_);
lean_dec(v_mvarId_1190_);
v_a_1241_ = lean_ctor_get(v___x_1199_, 0);
v_isSharedCheck_1248_ = !lean_is_exclusive(v___x_1199_);
if (v_isSharedCheck_1248_ == 0)
{
v___x_1243_ = v___x_1199_;
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_a_1241_);
lean_dec(v___x_1199_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1248_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1246_; 
if (v_isShared_1244_ == 0)
{
v___x_1246_ = v___x_1243_;
goto v_reusejp_1245_;
}
else
{
lean_object* v_reuseFailAlloc_1247_; 
v_reuseFailAlloc_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1247_, 0, v_a_1241_);
v___x_1246_ = v_reuseFailAlloc_1247_;
goto v_reusejp_1245_;
}
v_reusejp_1245_:
{
return v___x_1246_;
}
}
}
}
else
{
lean_object* v_a_1249_; lean_object* v___x_1251_; uint8_t v_isShared_1252_; uint8_t v_isSharedCheck_1256_; 
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec_ref(v_f_1192_);
lean_dec(v_mvarId_1190_);
v_a_1249_ = lean_ctor_get(v___x_1198_, 0);
v_isSharedCheck_1256_ = !lean_is_exclusive(v___x_1198_);
if (v_isSharedCheck_1256_ == 0)
{
v___x_1251_ = v___x_1198_;
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
else
{
lean_inc(v_a_1249_);
lean_dec(v___x_1198_);
v___x_1251_ = lean_box(0);
v_isShared_1252_ = v_isSharedCheck_1256_;
goto v_resetjp_1250_;
}
v_resetjp_1250_:
{
lean_object* v___x_1254_; 
if (v_isShared_1252_ == 0)
{
v___x_1254_ = v___x_1251_;
goto v_reusejp_1253_;
}
else
{
lean_object* v_reuseFailAlloc_1255_; 
v_reuseFailAlloc_1255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1255_, 0, v_a_1249_);
v___x_1254_ = v_reuseFailAlloc_1255_;
goto v_reusejp_1253_;
}
v_reusejp_1253_:
{
return v___x_1254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___lam__0___boxed(lean_object* v_mvarId_1257_, lean_object* v___x_1258_, lean_object* v_f_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_){
_start:
{
lean_object* v_res_1265_; 
v_res_1265_ = l_Lean_MVarId_transformTarget___lam__0(v_mvarId_1257_, v___x_1258_, v_f_1259_, v___y_1260_, v___y_1261_, v___y_1262_, v___y_1263_);
return v_res_1265_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget(lean_object* v_mvarId_1266_, lean_object* v_f_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_){
_start:
{
lean_object* v___x_1273_; lean_object* v___f_1274_; lean_object* v___x_1275_; 
v___x_1273_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
lean_inc(v_mvarId_1266_);
v___f_1274_ = lean_alloc_closure((void*)(l_Lean_MVarId_transformTarget___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1274_, 0, v_mvarId_1266_);
lean_closure_set(v___f_1274_, 1, v___x_1273_);
lean_closure_set(v___f_1274_, 2, v_f_1267_);
v___x_1275_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1266_, v___f_1274_, v_a_1268_, v_a_1269_, v_a_1270_, v_a_1271_);
return v___x_1275_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_transformTarget___boxed(lean_object* v_mvarId_1276_, lean_object* v_f_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v_res_1283_; 
v_res_1283_ = l_Lean_MVarId_transformTarget(v_mvarId_1276_, v_f_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
lean_dec(v_a_1281_);
lean_dec_ref(v_a_1280_);
lean_dec(v_a_1279_);
lean_dec_ref(v_a_1278_);
return v_res_1283_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible(lean_object* v_mvarId_1285_, lean_object* v_a_1286_, lean_object* v_a_1287_, lean_object* v_a_1288_, lean_object* v_a_1289_){
_start:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = ((lean_object*)(l_Lean_MVarId_unfoldReducible___closed__0));
v___x_1292_ = l_Lean_MVarId_transformTarget(v_mvarId_1285_, v___x_1291_, v_a_1286_, v_a_1287_, v_a_1288_, v_a_1289_);
return v___x_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_unfoldReducible___boxed(lean_object* v_mvarId_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_MVarId_unfoldReducible(v_mvarId_1293_, v_a_1294_, v_a_1295_, v_a_1296_, v_a_1297_);
lean_dec(v_a_1297_);
lean_dec_ref(v_a_1296_);
lean_dec(v_a_1295_);
lean_dec_ref(v_a_1294_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0(lean_object* v_x_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l_Lean_Core_betaReduce(v_x_1300_, v___y_1303_, v___y_1304_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___lam__0___boxed(lean_object* v_x_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v_res_1313_; 
v_res_1313_ = l_Lean_MVarId_betaReduce___lam__0(v_x_1307_, v___y_1308_, v___y_1309_, v___y_1310_, v___y_1311_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
lean_dec(v___y_1309_);
lean_dec_ref(v___y_1308_);
return v_res_1313_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce(lean_object* v_mvarId_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v___f_1321_; lean_object* v___x_1322_; 
v___f_1321_ = ((lean_object*)(l_Lean_MVarId_betaReduce___closed__0));
v___x_1322_ = l_Lean_MVarId_transformTarget(v_mvarId_1315_, v___f_1321_, v_a_1316_, v_a_1317_, v_a_1318_, v_a_1319_);
return v___x_1322_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_betaReduce___boxed(lean_object* v_mvarId_1323_, lean_object* v_a_1324_, lean_object* v_a_1325_, lean_object* v_a_1326_, lean_object* v_a_1327_, lean_object* v_a_1328_){
_start:
{
lean_object* v_res_1329_; 
v_res_1329_ = l_Lean_MVarId_betaReduce(v_mvarId_1323_, v_a_1324_, v_a_1325_, v_a_1326_, v_a_1327_);
lean_dec(v_a_1327_);
lean_dec_ref(v_a_1326_);
lean_dec(v_a_1325_);
lean_dec_ref(v_a_1324_);
return v_res_1329_;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; 
v___x_1333_ = lean_box(0);
v___x_1334_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___lam__0___closed__1));
v___x_1335_ = l_Lean_mkConst(v___x_1334_, v___x_1333_);
return v___x_1335_;
}
}
static lean_object* _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6(void){
_start:
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = lean_box(0);
v___x_1342_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___lam__0___closed__5));
v___x_1343_ = l_Lean_mkConst(v___x_1342_, v___x_1341_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0(lean_object* v_mvarId_1344_, lean_object* v___x_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; 
lean_inc(v_mvarId_1344_);
v___x_1351_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1344_, v___x_1345_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1351_) == 0)
{
lean_object* v___x_1352_; 
lean_dec_ref(v___x_1351_);
lean_inc(v_mvarId_1344_);
v___x_1352_ = l_Lean_MVarId_getType(v_mvarId_1344_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; lean_object* v___x_1355_; uint8_t v_isShared_1356_; uint8_t v_isSharedCheck_1407_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1407_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1407_ == 0)
{
v___x_1355_ = v___x_1352_;
v_isShared_1356_ = v_isSharedCheck_1407_;
goto v_resetjp_1354_;
}
else
{
lean_inc(v_a_1353_);
lean_dec(v___x_1352_);
v___x_1355_ = lean_box(0);
v_isShared_1356_ = v_isSharedCheck_1407_;
goto v_resetjp_1354_;
}
v_resetjp_1354_:
{
uint8_t v___x_1357_; 
lean_inc(v_a_1353_);
v___x_1357_ = l_Lean_Expr_isFalse(v_a_1353_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; 
lean_del_object(v___x_1355_);
lean_inc(v_a_1353_);
v___x_1358_ = l_Lean_mkNot(v_a_1353_);
v___x_1359_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__2, &l_Lean_MVarId_byContra_x3f___lam__0___closed__2_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__2);
v___x_1360_ = l_Lean_mkArrow(v___x_1358_, v___x_1359_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1360_) == 0)
{
lean_object* v_a_1361_; lean_object* v___x_1362_; 
v_a_1361_ = lean_ctor_get(v___x_1360_, 0);
lean_inc(v_a_1361_);
lean_dec_ref(v___x_1360_);
lean_inc(v_mvarId_1344_);
v___x_1362_ = l_Lean_MVarId_getTag(v_mvarId_1344_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v_a_1363_; lean_object* v___x_1364_; 
v_a_1363_ = lean_ctor_get(v___x_1362_, 0);
lean_inc(v_a_1363_);
lean_dec_ref(v___x_1362_);
v___x_1364_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_a_1361_, v_a_1363_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1377_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc_n(v_a_1365_, 2);
lean_dec_ref(v___x_1364_);
v___x_1366_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__6, &l_Lean_MVarId_byContra_x3f___lam__0___closed__6_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6);
v___x_1367_ = l_Lean_mkAppB(v___x_1366_, v_a_1353_, v_a_1365_);
v___x_1368_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_1344_, v___x_1367_, v___y_1347_);
v_isSharedCheck_1377_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1377_ == 0)
{
lean_object* v_unused_1378_; 
v_unused_1378_ = lean_ctor_get(v___x_1368_, 0);
lean_dec(v_unused_1378_);
v___x_1370_ = v___x_1368_;
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
else
{
lean_dec(v___x_1368_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1377_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1375_; 
v___x_1372_ = l_Lean_Expr_mvarId_x21(v_a_1365_);
lean_dec(v_a_1365_);
v___x_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1372_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v___x_1373_);
v___x_1375_ = v___x_1370_;
goto v_reusejp_1374_;
}
else
{
lean_object* v_reuseFailAlloc_1376_; 
v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1373_);
v___x_1375_ = v_reuseFailAlloc_1376_;
goto v_reusejp_1374_;
}
v_reusejp_1374_:
{
return v___x_1375_;
}
}
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_a_1353_);
lean_dec(v_mvarId_1344_);
v_a_1379_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1364_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1364_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1384_; 
if (v_isShared_1382_ == 0)
{
v___x_1384_ = v___x_1381_;
goto v_reusejp_1383_;
}
else
{
lean_object* v_reuseFailAlloc_1385_; 
v_reuseFailAlloc_1385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1385_, 0, v_a_1379_);
v___x_1384_ = v_reuseFailAlloc_1385_;
goto v_reusejp_1383_;
}
v_reusejp_1383_:
{
return v___x_1384_;
}
}
}
}
else
{
lean_object* v_a_1387_; lean_object* v___x_1389_; uint8_t v_isShared_1390_; uint8_t v_isSharedCheck_1394_; 
lean_dec(v_a_1361_);
lean_dec(v_a_1353_);
lean_dec(v_mvarId_1344_);
v_a_1387_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1394_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1394_ == 0)
{
v___x_1389_ = v___x_1362_;
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
else
{
lean_inc(v_a_1387_);
lean_dec(v___x_1362_);
v___x_1389_ = lean_box(0);
v_isShared_1390_ = v_isSharedCheck_1394_;
goto v_resetjp_1388_;
}
v_resetjp_1388_:
{
lean_object* v___x_1392_; 
if (v_isShared_1390_ == 0)
{
v___x_1392_ = v___x_1389_;
goto v_reusejp_1391_;
}
else
{
lean_object* v_reuseFailAlloc_1393_; 
v_reuseFailAlloc_1393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1393_, 0, v_a_1387_);
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
lean_dec(v_a_1353_);
lean_dec(v_mvarId_1344_);
v_a_1395_ = lean_ctor_get(v___x_1360_, 0);
v_isSharedCheck_1402_ = !lean_is_exclusive(v___x_1360_);
if (v_isSharedCheck_1402_ == 0)
{
v___x_1397_ = v___x_1360_;
v_isShared_1398_ = v_isSharedCheck_1402_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_a_1395_);
lean_dec(v___x_1360_);
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
lean_object* v___x_1403_; lean_object* v___x_1405_; 
lean_dec(v_a_1353_);
lean_dec(v_mvarId_1344_);
v___x_1403_ = lean_box(0);
if (v_isShared_1356_ == 0)
{
lean_ctor_set(v___x_1355_, 0, v___x_1403_);
v___x_1405_ = v___x_1355_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1406_; 
v_reuseFailAlloc_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1406_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1406_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
return v___x_1405_;
}
}
}
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v_mvarId_1344_);
v_a_1408_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1352_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1352_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v_mvarId_1344_);
v_a_1416_ = lean_ctor_get(v___x_1351_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1351_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1351_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1351_);
v___x_1418_ = lean_box(0);
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
v_resetjp_1417_:
{
lean_object* v___x_1421_; 
if (v_isShared_1419_ == 0)
{
v___x_1421_ = v___x_1418_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v_a_1416_);
v___x_1421_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
return v___x_1421_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___lam__0___boxed(lean_object* v_mvarId_1424_, lean_object* v___x_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_, lean_object* v___y_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_Lean_MVarId_byContra_x3f___lam__0(v_mvarId_1424_, v___x_1425_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
lean_dec(v___y_1429_);
lean_dec_ref(v___y_1428_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f(lean_object* v_mvarId_1436_, lean_object* v_a_1437_, lean_object* v_a_1438_, lean_object* v_a_1439_, lean_object* v_a_1440_){
_start:
{
lean_object* v___x_1442_; lean_object* v___f_1443_; lean_object* v___x_1444_; 
v___x_1442_ = ((lean_object*)(l_Lean_MVarId_byContra_x3f___closed__1));
lean_inc(v_mvarId_1436_);
v___f_1443_ = lean_alloc_closure((void*)(l_Lean_MVarId_byContra_x3f___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1443_, 0, v_mvarId_1436_);
lean_closure_set(v___f_1443_, 1, v___x_1442_);
v___x_1444_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1436_, v___f_1443_, v_a_1437_, v_a_1438_, v_a_1439_, v_a_1440_);
return v___x_1444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_byContra_x3f___boxed(lean_object* v_mvarId_1445_, lean_object* v_a_1446_, lean_object* v_a_1447_, lean_object* v_a_1448_, lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v_res_1451_; 
v_res_1451_ = l_Lean_MVarId_byContra_x3f(v_mvarId_1445_, v_a_1446_, v_a_1447_, v_a_1448_, v_a_1449_);
lean_dec(v_a_1449_);
lean_dec_ref(v_a_1448_);
lean_dec(v_a_1447_);
lean_dec_ref(v_a_1446_);
return v_res_1451_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__0));
v___x_1454_ = l_Lean_stringToMessageData(v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; 
v___x_1456_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__2));
v___x_1457_ = l_Lean_stringToMessageData(v___x_1456_);
return v___x_1457_;
}
}
static lean_object* _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__4));
v___x_1460_ = l_Lean_stringToMessageData(v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(lean_object* v_as_x27_1461_, lean_object* v_b_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_){
_start:
{
if (lean_obj_tag(v_as_x27_1461_) == 0)
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1468_, 0, v_b_1462_);
return v___x_1468_;
}
else
{
lean_object* v_head_1469_; lean_object* v_tail_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1524_; 
v_head_1469_ = lean_ctor_get(v_as_x27_1461_, 0);
v_tail_1470_ = lean_ctor_get(v_as_x27_1461_, 1);
v_isSharedCheck_1524_ = !lean_is_exclusive(v_as_x27_1461_);
if (v_isSharedCheck_1524_ == 0)
{
v___x_1472_ = v_as_x27_1461_;
v_isShared_1473_ = v_isSharedCheck_1524_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_tail_1470_);
lean_inc(v_head_1469_);
lean_dec(v_as_x27_1461_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1524_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1474_; 
lean_inc(v_head_1469_);
lean_inc(v_b_1462_);
v___x_1474_ = l_Lean_MVarId_clear(v_b_1462_, v_head_1469_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; 
lean_del_object(v___x_1472_);
lean_dec(v_head_1469_);
lean_dec(v_b_1462_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref(v___x_1474_);
v_as_x27_1461_ = v_tail_1470_;
v_b_1462_ = v_a_1475_;
goto _start;
}
else
{
lean_object* v_a_1477_; uint8_t v___y_1479_; uint8_t v___x_1522_; 
v_a_1477_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1477_);
v___x_1522_ = l_Lean_Exception_isInterrupt(v_a_1477_);
if (v___x_1522_ == 0)
{
uint8_t v___x_1523_; 
v___x_1523_ = l_Lean_Exception_isRuntime(v_a_1477_);
v___y_1479_ = v___x_1523_;
goto v___jp_1478_;
}
else
{
lean_dec(v_a_1477_);
v___y_1479_ = v___x_1522_;
goto v___jp_1478_;
}
v___jp_1478_:
{
if (v___y_1479_ == 0)
{
lean_object* v___x_1481_; uint8_t v_isShared_1482_; uint8_t v_isSharedCheck_1520_; 
v_isSharedCheck_1520_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1520_ == 0)
{
lean_object* v_unused_1521_; 
v_unused_1521_ = lean_ctor_get(v___x_1474_, 0);
lean_dec(v_unused_1521_);
v___x_1481_ = v___x_1474_;
v_isShared_1482_ = v_isSharedCheck_1520_;
goto v_resetjp_1480_;
}
else
{
lean_dec(v___x_1474_);
v___x_1481_ = lean_box(0);
v_isShared_1482_ = v_isSharedCheck_1520_;
goto v_resetjp_1480_;
}
v_resetjp_1480_:
{
lean_object* v___x_1483_; 
v___x_1483_ = l_Lean_FVarId_getDecl___redArg(v_head_1469_, v___y_1463_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; uint8_t v___x_1485_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
lean_inc(v_a_1484_);
lean_dec_ref(v___x_1483_);
v___x_1485_ = l_Lean_LocalDecl_isAuxDecl(v_a_1484_);
if (v___x_1485_ == 0)
{
lean_dec(v_a_1484_);
lean_del_object(v___x_1481_);
lean_del_object(v___x_1472_);
v_as_x27_1461_ = v_tail_1470_;
goto _start;
}
else
{
lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1492_; 
v___x_1487_ = l_Lean_LocalDecl_userName(v_a_1484_);
lean_dec(v_a_1484_);
v___x_1488_ = ((lean_object*)(l_Lean_MVarId_ensureNoMVar___closed__1));
v___x_1489_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__1);
v___x_1490_ = l_Lean_MessageData_ofName(v___x_1487_);
lean_inc_ref(v___x_1490_);
if (v_isShared_1473_ == 0)
{
lean_ctor_set_tag(v___x_1472_, 7);
lean_ctor_set(v___x_1472_, 1, v___x_1490_);
lean_ctor_set(v___x_1472_, 0, v___x_1489_);
v___x_1492_ = v___x_1472_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1490_);
v___x_1492_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1499_; 
v___x_1493_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__3);
v___x_1494_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1494_, 0, v___x_1492_);
lean_ctor_set(v___x_1494_, 1, v___x_1493_);
v___x_1495_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1495_, 0, v___x_1494_);
lean_ctor_set(v___x_1495_, 1, v___x_1490_);
v___x_1496_ = lean_obj_once(&l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5, &l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5_once, _init_l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___closed__5);
v___x_1497_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1497_, 0, v___x_1495_);
lean_ctor_set(v___x_1497_, 1, v___x_1496_);
if (v_isShared_1482_ == 0)
{
lean_ctor_set(v___x_1481_, 0, v___x_1497_);
v___x_1499_ = v___x_1481_;
goto v_reusejp_1498_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1497_);
v___x_1499_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1498_;
}
v_reusejp_1498_:
{
lean_object* v___x_1500_; 
lean_inc(v_b_1462_);
v___x_1500_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1488_, v_b_1462_, v___x_1499_, v___y_1463_, v___y_1464_, v___y_1465_, v___y_1466_);
if (lean_obj_tag(v___x_1500_) == 0)
{
lean_dec_ref(v___x_1500_);
v_as_x27_1461_ = v_tail_1470_;
goto _start;
}
else
{
lean_object* v_a_1502_; lean_object* v___x_1504_; uint8_t v_isShared_1505_; uint8_t v_isSharedCheck_1509_; 
lean_dec(v_tail_1470_);
lean_dec(v_b_1462_);
v_a_1502_ = lean_ctor_get(v___x_1500_, 0);
v_isSharedCheck_1509_ = !lean_is_exclusive(v___x_1500_);
if (v_isSharedCheck_1509_ == 0)
{
v___x_1504_ = v___x_1500_;
v_isShared_1505_ = v_isSharedCheck_1509_;
goto v_resetjp_1503_;
}
else
{
lean_inc(v_a_1502_);
lean_dec(v___x_1500_);
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
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_del_object(v___x_1481_);
lean_del_object(v___x_1472_);
lean_dec(v_tail_1470_);
lean_dec(v_b_1462_);
v_a_1512_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1483_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1483_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
}
else
{
lean_del_object(v___x_1472_);
lean_dec(v_tail_1470_);
lean_dec(v_head_1469_);
lean_dec(v_b_1462_);
return v___x_1474_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg___boxed(lean_object* v_as_x27_1525_, lean_object* v_b_1526_, lean_object* v___y_1527_, lean_object* v___y_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1525_, v_b_1526_, v___y_1527_, v___y_1528_, v___y_1529_, v___y_1530_);
lean_dec(v___y_1530_);
lean_dec_ref(v___y_1529_);
lean_dec(v___y_1528_);
lean_dec_ref(v___y_1527_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(lean_object* v_as_1533_, size_t v_sz_1534_, size_t v_i_1535_, lean_object* v_b_1536_){
_start:
{
uint8_t v___x_1538_; 
v___x_1538_ = lean_usize_dec_lt(v_i_1535_, v_sz_1534_);
if (v___x_1538_ == 0)
{
lean_object* v___x_1539_; 
v___x_1539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1539_, 0, v_b_1536_);
return v___x_1539_;
}
else
{
lean_object* v_snd_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1558_; 
v_snd_1540_ = lean_ctor_get(v_b_1536_, 1);
v_isSharedCheck_1558_ = !lean_is_exclusive(v_b_1536_);
if (v_isSharedCheck_1558_ == 0)
{
lean_object* v_unused_1559_; 
v_unused_1559_ = lean_ctor_get(v_b_1536_, 0);
lean_dec(v_unused_1559_);
v___x_1542_ = v_b_1536_;
v_isShared_1543_ = v_isSharedCheck_1558_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_snd_1540_);
lean_dec(v_b_1536_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1558_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; lean_object* v_a_1546_; lean_object* v_a_1553_; 
v___x_1544_ = lean_box(0);
v_a_1553_ = lean_array_uget_borrowed(v_as_1533_, v_i_1535_);
if (lean_obj_tag(v_a_1553_) == 0)
{
v_a_1546_ = v_snd_1540_;
goto v___jp_1545_;
}
else
{
lean_object* v_val_1554_; uint8_t v___x_1555_; 
v_val_1554_ = lean_ctor_get(v_a_1553_, 0);
v___x_1555_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1554_);
if (v___x_1555_ == 0)
{
v_a_1546_ = v_snd_1540_;
goto v___jp_1545_;
}
else
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = l_Lean_LocalDecl_fvarId(v_val_1554_);
v___x_1557_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1557_, 0, v___x_1556_);
lean_ctor_set(v___x_1557_, 1, v_snd_1540_);
v_a_1546_ = v___x_1557_;
goto v___jp_1545_;
}
}
v___jp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 1, v_a_1546_);
lean_ctor_set(v___x_1542_, 0, v___x_1544_);
v___x_1548_ = v___x_1542_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v_a_1546_);
v___x_1548_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
size_t v___x_1549_; size_t v___x_1550_; 
v___x_1549_ = ((size_t)1ULL);
v___x_1550_ = lean_usize_add(v_i_1535_, v___x_1549_);
v_i_1535_ = v___x_1550_;
v_b_1536_ = v___x_1548_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg___boxed(lean_object* v_as_1560_, lean_object* v_sz_1561_, lean_object* v_i_1562_, lean_object* v_b_1563_, lean_object* v___y_1564_){
_start:
{
size_t v_sz_boxed_1565_; size_t v_i_boxed_1566_; lean_object* v_res_1567_; 
v_sz_boxed_1565_ = lean_unbox_usize(v_sz_1561_);
lean_dec(v_sz_1561_);
v_i_boxed_1566_ = lean_unbox_usize(v_i_1562_);
lean_dec(v_i_1562_);
v_res_1567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1560_, v_sz_boxed_1565_, v_i_boxed_1566_, v_b_1563_);
lean_dec_ref(v_as_1560_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(lean_object* v_as_1568_, size_t v_sz_1569_, size_t v_i_1570_, lean_object* v_b_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
uint8_t v___x_1577_; 
v___x_1577_ = lean_usize_dec_lt(v_i_1570_, v_sz_1569_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1578_, 0, v_b_1571_);
return v___x_1578_;
}
else
{
lean_object* v_snd_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1597_; 
v_snd_1579_ = lean_ctor_get(v_b_1571_, 1);
v_isSharedCheck_1597_ = !lean_is_exclusive(v_b_1571_);
if (v_isSharedCheck_1597_ == 0)
{
lean_object* v_unused_1598_; 
v_unused_1598_ = lean_ctor_get(v_b_1571_, 0);
lean_dec(v_unused_1598_);
v___x_1581_ = v_b_1571_;
v_isShared_1582_ = v_isSharedCheck_1597_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_snd_1579_);
lean_dec(v_b_1571_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1597_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1583_; lean_object* v_a_1585_; lean_object* v_a_1592_; 
v___x_1583_ = lean_box(0);
v_a_1592_ = lean_array_uget_borrowed(v_as_1568_, v_i_1570_);
if (lean_obj_tag(v_a_1592_) == 0)
{
v_a_1585_ = v_snd_1579_;
goto v___jp_1584_;
}
else
{
lean_object* v_val_1593_; uint8_t v___x_1594_; 
v_val_1593_ = lean_ctor_get(v_a_1592_, 0);
v___x_1594_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1593_);
if (v___x_1594_ == 0)
{
v_a_1585_ = v_snd_1579_;
goto v___jp_1584_;
}
else
{
lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1595_ = l_Lean_LocalDecl_fvarId(v_val_1593_);
v___x_1596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1596_, 0, v___x_1595_);
lean_ctor_set(v___x_1596_, 1, v_snd_1579_);
v_a_1585_ = v___x_1596_;
goto v___jp_1584_;
}
}
v___jp_1584_:
{
lean_object* v___x_1587_; 
if (v_isShared_1582_ == 0)
{
lean_ctor_set(v___x_1581_, 1, v_a_1585_);
lean_ctor_set(v___x_1581_, 0, v___x_1583_);
v___x_1587_ = v___x_1581_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1583_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v_a_1585_);
v___x_1587_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
size_t v___x_1588_; size_t v___x_1589_; lean_object* v___x_1590_; 
v___x_1588_ = ((size_t)1ULL);
v___x_1589_ = lean_usize_add(v_i_1570_, v___x_1588_);
v___x_1590_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_1568_, v_sz_1569_, v___x_1589_, v___x_1587_);
return v___x_1590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2___boxed(lean_object* v_as_1599_, lean_object* v_sz_1600_, lean_object* v_i_1601_, lean_object* v_b_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_){
_start:
{
size_t v_sz_boxed_1608_; size_t v_i_boxed_1609_; lean_object* v_res_1610_; 
v_sz_boxed_1608_ = lean_unbox_usize(v_sz_1600_);
lean_dec(v_sz_1600_);
v_i_boxed_1609_ = lean_unbox_usize(v_i_1601_);
lean_dec(v_i_1601_);
v_res_1610_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_as_1599_, v_sz_boxed_1608_, v_i_boxed_1609_, v_b_1602_, v___y_1603_, v___y_1604_, v___y_1605_, v___y_1606_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec(v___y_1604_);
lean_dec_ref(v___y_1603_);
lean_dec_ref(v_as_1599_);
return v_res_1610_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(lean_object* v_init_1611_, lean_object* v_n_1612_, lean_object* v_b_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
if (lean_obj_tag(v_n_1612_) == 0)
{
lean_object* v_cs_1619_; lean_object* v___x_1621_; uint8_t v_isShared_1622_; uint8_t v_isSharedCheck_1653_; 
v_cs_1619_ = lean_ctor_get(v_n_1612_, 0);
v_isSharedCheck_1653_ = !lean_is_exclusive(v_n_1612_);
if (v_isSharedCheck_1653_ == 0)
{
v___x_1621_ = v_n_1612_;
v_isShared_1622_ = v_isSharedCheck_1653_;
goto v_resetjp_1620_;
}
else
{
lean_inc(v_cs_1619_);
lean_dec(v_n_1612_);
v___x_1621_ = lean_box(0);
v_isShared_1622_ = v_isSharedCheck_1653_;
goto v_resetjp_1620_;
}
v_resetjp_1620_:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; size_t v_sz_1625_; size_t v___x_1626_; lean_object* v___x_1627_; 
v___x_1623_ = lean_box(0);
v___x_1624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1623_);
lean_ctor_set(v___x_1624_, 1, v_b_1613_);
v_sz_1625_ = lean_array_size(v_cs_1619_);
v___x_1626_ = ((size_t)0ULL);
v___x_1627_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1611_, v_cs_1619_, v_sz_1625_, v___x_1626_, v___x_1624_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec_ref(v_cs_1619_);
if (lean_obj_tag(v___x_1627_) == 0)
{
lean_object* v_a_1628_; lean_object* v___x_1630_; uint8_t v_isShared_1631_; uint8_t v_isSharedCheck_1644_; 
v_a_1628_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1644_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1644_ == 0)
{
v___x_1630_ = v___x_1627_;
v_isShared_1631_ = v_isSharedCheck_1644_;
goto v_resetjp_1629_;
}
else
{
lean_inc(v_a_1628_);
lean_dec(v___x_1627_);
v___x_1630_ = lean_box(0);
v_isShared_1631_ = v_isSharedCheck_1644_;
goto v_resetjp_1629_;
}
v_resetjp_1629_:
{
lean_object* v_fst_1632_; 
v_fst_1632_ = lean_ctor_get(v_a_1628_, 0);
if (lean_obj_tag(v_fst_1632_) == 0)
{
lean_object* v_snd_1633_; lean_object* v___x_1635_; 
v_snd_1633_ = lean_ctor_get(v_a_1628_, 1);
lean_inc(v_snd_1633_);
lean_dec(v_a_1628_);
if (v_isShared_1622_ == 0)
{
lean_ctor_set_tag(v___x_1621_, 1);
lean_ctor_set(v___x_1621_, 0, v_snd_1633_);
v___x_1635_ = v___x_1621_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_snd_1633_);
v___x_1635_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
lean_object* v___x_1637_; 
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v___x_1635_);
v___x_1637_ = v___x_1630_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
return v___x_1637_;
}
}
}
else
{
lean_object* v_val_1640_; lean_object* v___x_1642_; 
lean_inc_ref(v_fst_1632_);
lean_dec(v_a_1628_);
lean_del_object(v___x_1621_);
v_val_1640_ = lean_ctor_get(v_fst_1632_, 0);
lean_inc(v_val_1640_);
lean_dec_ref(v_fst_1632_);
if (v_isShared_1631_ == 0)
{
lean_ctor_set(v___x_1630_, 0, v_val_1640_);
v___x_1642_ = v___x_1630_;
goto v_reusejp_1641_;
}
else
{
lean_object* v_reuseFailAlloc_1643_; 
v_reuseFailAlloc_1643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1643_, 0, v_val_1640_);
v___x_1642_ = v_reuseFailAlloc_1643_;
goto v_reusejp_1641_;
}
v_reusejp_1641_:
{
return v___x_1642_;
}
}
}
}
else
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1652_; 
lean_del_object(v___x_1621_);
v_a_1645_ = lean_ctor_get(v___x_1627_, 0);
v_isSharedCheck_1652_ = !lean_is_exclusive(v___x_1627_);
if (v_isSharedCheck_1652_ == 0)
{
v___x_1647_ = v___x_1627_;
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1627_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1652_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
lean_object* v___x_1650_; 
if (v_isShared_1648_ == 0)
{
v___x_1650_ = v___x_1647_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_a_1645_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
}
else
{
lean_object* v_vs_1654_; lean_object* v___x_1656_; uint8_t v_isShared_1657_; uint8_t v_isSharedCheck_1688_; 
v_vs_1654_ = lean_ctor_get(v_n_1612_, 0);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_n_1612_);
if (v_isSharedCheck_1688_ == 0)
{
v___x_1656_ = v_n_1612_;
v_isShared_1657_ = v_isSharedCheck_1688_;
goto v_resetjp_1655_;
}
else
{
lean_inc(v_vs_1654_);
lean_dec(v_n_1612_);
v___x_1656_ = lean_box(0);
v_isShared_1657_ = v_isSharedCheck_1688_;
goto v_resetjp_1655_;
}
v_resetjp_1655_:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; size_t v_sz_1660_; size_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1658_ = lean_box(0);
v___x_1659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1659_, 0, v___x_1658_);
lean_ctor_set(v___x_1659_, 1, v_b_1613_);
v_sz_1660_ = lean_array_size(v_vs_1654_);
v___x_1661_ = ((size_t)0ULL);
v___x_1662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2(v_vs_1654_, v_sz_1660_, v___x_1661_, v___x_1659_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
lean_dec_ref(v_vs_1654_);
if (lean_obj_tag(v___x_1662_) == 0)
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1679_; 
v_a_1663_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1665_ = v___x_1662_;
v_isShared_1666_ = v_isSharedCheck_1679_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1662_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1679_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v_fst_1667_; 
v_fst_1667_ = lean_ctor_get(v_a_1663_, 0);
if (lean_obj_tag(v_fst_1667_) == 0)
{
lean_object* v_snd_1668_; lean_object* v___x_1670_; 
v_snd_1668_ = lean_ctor_get(v_a_1663_, 1);
lean_inc(v_snd_1668_);
lean_dec(v_a_1663_);
if (v_isShared_1657_ == 0)
{
lean_ctor_set(v___x_1656_, 0, v_snd_1668_);
v___x_1670_ = v___x_1656_;
goto v_reusejp_1669_;
}
else
{
lean_object* v_reuseFailAlloc_1674_; 
v_reuseFailAlloc_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1674_, 0, v_snd_1668_);
v___x_1670_ = v_reuseFailAlloc_1674_;
goto v_reusejp_1669_;
}
v_reusejp_1669_:
{
lean_object* v___x_1672_; 
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v___x_1670_);
v___x_1672_ = v___x_1665_;
goto v_reusejp_1671_;
}
else
{
lean_object* v_reuseFailAlloc_1673_; 
v_reuseFailAlloc_1673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
v___x_1672_ = v_reuseFailAlloc_1673_;
goto v_reusejp_1671_;
}
v_reusejp_1671_:
{
return v___x_1672_;
}
}
}
else
{
lean_object* v_val_1675_; lean_object* v___x_1677_; 
lean_inc_ref(v_fst_1667_);
lean_dec(v_a_1663_);
lean_del_object(v___x_1656_);
v_val_1675_ = lean_ctor_get(v_fst_1667_, 0);
lean_inc(v_val_1675_);
lean_dec_ref(v_fst_1667_);
if (v_isShared_1666_ == 0)
{
lean_ctor_set(v___x_1665_, 0, v_val_1675_);
v___x_1677_ = v___x_1665_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_val_1675_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v_a_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1687_; 
lean_del_object(v___x_1656_);
v_a_1680_ = lean_ctor_get(v___x_1662_, 0);
v_isSharedCheck_1687_ = !lean_is_exclusive(v___x_1662_);
if (v_isSharedCheck_1687_ == 0)
{
v___x_1682_ = v___x_1662_;
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
else
{
lean_inc(v_a_1680_);
lean_dec(v___x_1662_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1687_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1685_; 
if (v_isShared_1683_ == 0)
{
v___x_1685_ = v___x_1682_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1686_; 
v_reuseFailAlloc_1686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1686_, 0, v_a_1680_);
v___x_1685_ = v_reuseFailAlloc_1686_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
return v___x_1685_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(lean_object* v_init_1689_, lean_object* v_as_1690_, size_t v_sz_1691_, size_t v_i_1692_, lean_object* v_b_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_, lean_object* v___y_1697_){
_start:
{
uint8_t v___x_1699_; 
v___x_1699_ = lean_usize_dec_lt(v_i_1692_, v_sz_1691_);
if (v___x_1699_ == 0)
{
lean_object* v___x_1700_; 
v___x_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_b_1693_);
return v___x_1700_;
}
else
{
lean_object* v_snd_1701_; lean_object* v___x_1703_; uint8_t v_isShared_1704_; uint8_t v_isSharedCheck_1735_; 
v_snd_1701_ = lean_ctor_get(v_b_1693_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_b_1693_);
if (v_isSharedCheck_1735_ == 0)
{
lean_object* v_unused_1736_; 
v_unused_1736_ = lean_ctor_get(v_b_1693_, 0);
lean_dec(v_unused_1736_);
v___x_1703_ = v_b_1693_;
v_isShared_1704_ = v_isSharedCheck_1735_;
goto v_resetjp_1702_;
}
else
{
lean_inc(v_snd_1701_);
lean_dec(v_b_1693_);
v___x_1703_ = lean_box(0);
v_isShared_1704_ = v_isSharedCheck_1735_;
goto v_resetjp_1702_;
}
v_resetjp_1702_:
{
lean_object* v_a_1705_; lean_object* v___x_1706_; 
v_a_1705_ = lean_array_uget_borrowed(v_as_1690_, v_i_1692_);
lean_inc(v_snd_1701_);
lean_inc(v_a_1705_);
v___x_1706_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1689_, v_a_1705_, v_snd_1701_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1726_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1726_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1726_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1726_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1726_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
if (lean_obj_tag(v_a_1707_) == 0)
{
lean_object* v___x_1711_; lean_object* v___x_1713_; 
v___x_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1711_, 0, v_a_1707_);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 0, v___x_1711_);
v___x_1713_ = v___x_1703_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1717_, 1, v_snd_1701_);
v___x_1713_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1715_; 
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1713_);
v___x_1715_ = v___x_1709_;
goto v_reusejp_1714_;
}
else
{
lean_object* v_reuseFailAlloc_1716_; 
v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
v___x_1715_ = v_reuseFailAlloc_1716_;
goto v_reusejp_1714_;
}
v_reusejp_1714_:
{
return v___x_1715_;
}
}
}
else
{
lean_object* v_a_1718_; lean_object* v___x_1719_; lean_object* v___x_1721_; 
lean_del_object(v___x_1709_);
lean_dec(v_snd_1701_);
v_a_1718_ = lean_ctor_get(v_a_1707_, 0);
lean_inc(v_a_1718_);
lean_dec_ref(v_a_1707_);
v___x_1719_ = lean_box(0);
if (v_isShared_1704_ == 0)
{
lean_ctor_set(v___x_1703_, 1, v_a_1718_);
lean_ctor_set(v___x_1703_, 0, v___x_1719_);
v___x_1721_ = v___x_1703_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1725_; 
v_reuseFailAlloc_1725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1719_);
lean_ctor_set(v_reuseFailAlloc_1725_, 1, v_a_1718_);
v___x_1721_ = v_reuseFailAlloc_1725_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
size_t v___x_1722_; size_t v___x_1723_; 
v___x_1722_ = ((size_t)1ULL);
v___x_1723_ = lean_usize_add(v_i_1692_, v___x_1722_);
v_i_1692_ = v___x_1723_;
v_b_1693_ = v___x_1721_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1729_; uint8_t v_isShared_1730_; uint8_t v_isSharedCheck_1734_; 
lean_del_object(v___x_1703_);
lean_dec(v_snd_1701_);
v_a_1727_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1729_ = v___x_1706_;
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
else
{
lean_inc(v_a_1727_);
lean_dec(v___x_1706_);
v___x_1729_ = lean_box(0);
v_isShared_1730_ = v_isSharedCheck_1734_;
goto v_resetjp_1728_;
}
v_resetjp_1728_:
{
lean_object* v___x_1732_; 
if (v_isShared_1730_ == 0)
{
v___x_1732_ = v___x_1729_;
goto v_reusejp_1731_;
}
else
{
lean_object* v_reuseFailAlloc_1733_; 
v_reuseFailAlloc_1733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1733_, 0, v_a_1727_);
v___x_1732_ = v_reuseFailAlloc_1733_;
goto v_reusejp_1731_;
}
v_reusejp_1731_:
{
return v___x_1732_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1737_, lean_object* v_as_1738_, lean_object* v_sz_1739_, lean_object* v_i_1740_, lean_object* v_b_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_, lean_object* v___y_1746_){
_start:
{
size_t v_sz_boxed_1747_; size_t v_i_boxed_1748_; lean_object* v_res_1749_; 
v_sz_boxed_1747_ = lean_unbox_usize(v_sz_1739_);
lean_dec(v_sz_1739_);
v_i_boxed_1748_ = lean_unbox_usize(v_i_1740_);
lean_dec(v_i_1740_);
v_res_1749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1737_, v_as_1738_, v_sz_boxed_1747_, v_i_boxed_1748_, v_b_1741_, v___y_1742_, v___y_1743_, v___y_1744_, v___y_1745_);
lean_dec(v___y_1745_);
lean_dec_ref(v___y_1744_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec_ref(v_as_1738_);
lean_dec(v_init_1737_);
return v_res_1749_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0___boxed(lean_object* v_init_1750_, lean_object* v_n_1751_, lean_object* v_b_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1750_, v_n_1751_, v_b_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_);
lean_dec(v___y_1756_);
lean_dec_ref(v___y_1755_);
lean_dec(v___y_1754_);
lean_dec_ref(v___y_1753_);
lean_dec(v_init_1750_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(lean_object* v_as_1759_, size_t v_sz_1760_, size_t v_i_1761_, lean_object* v_b_1762_){
_start:
{
uint8_t v___x_1764_; 
v___x_1764_ = lean_usize_dec_lt(v_i_1761_, v_sz_1760_);
if (v___x_1764_ == 0)
{
lean_object* v___x_1765_; 
v___x_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1765_, 0, v_b_1762_);
return v___x_1765_;
}
else
{
lean_object* v_snd_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1784_; 
v_snd_1766_ = lean_ctor_get(v_b_1762_, 1);
v_isSharedCheck_1784_ = !lean_is_exclusive(v_b_1762_);
if (v_isSharedCheck_1784_ == 0)
{
lean_object* v_unused_1785_; 
v_unused_1785_ = lean_ctor_get(v_b_1762_, 0);
lean_dec(v_unused_1785_);
v___x_1768_ = v_b_1762_;
v_isShared_1769_ = v_isSharedCheck_1784_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_snd_1766_);
lean_dec(v_b_1762_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1784_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1770_; lean_object* v_a_1772_; lean_object* v_a_1779_; 
v___x_1770_ = lean_box(0);
v_a_1779_ = lean_array_uget_borrowed(v_as_1759_, v_i_1761_);
if (lean_obj_tag(v_a_1779_) == 0)
{
v_a_1772_ = v_snd_1766_;
goto v___jp_1771_;
}
else
{
lean_object* v_val_1780_; uint8_t v___x_1781_; 
v_val_1780_ = lean_ctor_get(v_a_1779_, 0);
v___x_1781_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1780_);
if (v___x_1781_ == 0)
{
v_a_1772_ = v_snd_1766_;
goto v___jp_1771_;
}
else
{
lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = l_Lean_LocalDecl_fvarId(v_val_1780_);
v___x_1783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1782_);
lean_ctor_set(v___x_1783_, 1, v_snd_1766_);
v_a_1772_ = v___x_1783_;
goto v___jp_1771_;
}
}
v___jp_1771_:
{
lean_object* v___x_1774_; 
if (v_isShared_1769_ == 0)
{
lean_ctor_set(v___x_1768_, 1, v_a_1772_);
lean_ctor_set(v___x_1768_, 0, v___x_1770_);
v___x_1774_ = v___x_1768_;
goto v_reusejp_1773_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1770_);
lean_ctor_set(v_reuseFailAlloc_1778_, 1, v_a_1772_);
v___x_1774_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1773_;
}
v_reusejp_1773_:
{
size_t v___x_1775_; size_t v___x_1776_; 
v___x_1775_ = ((size_t)1ULL);
v___x_1776_ = lean_usize_add(v_i_1761_, v___x_1775_);
v_i_1761_ = v___x_1776_;
v_b_1762_ = v___x_1774_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v_as_1786_, lean_object* v_sz_1787_, lean_object* v_i_1788_, lean_object* v_b_1789_, lean_object* v___y_1790_){
_start:
{
size_t v_sz_boxed_1791_; size_t v_i_boxed_1792_; lean_object* v_res_1793_; 
v_sz_boxed_1791_ = lean_unbox_usize(v_sz_1787_);
lean_dec(v_sz_1787_);
v_i_boxed_1792_ = lean_unbox_usize(v_i_1788_);
lean_dec(v_i_1788_);
v_res_1793_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1786_, v_sz_boxed_1791_, v_i_boxed_1792_, v_b_1789_);
lean_dec_ref(v_as_1786_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(lean_object* v_as_1794_, size_t v_sz_1795_, size_t v_i_1796_, lean_object* v_b_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_){
_start:
{
uint8_t v___x_1803_; 
v___x_1803_ = lean_usize_dec_lt(v_i_1796_, v_sz_1795_);
if (v___x_1803_ == 0)
{
lean_object* v___x_1804_; 
v___x_1804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1804_, 0, v_b_1797_);
return v___x_1804_;
}
else
{
lean_object* v_snd_1805_; lean_object* v___x_1807_; uint8_t v_isShared_1808_; uint8_t v_isSharedCheck_1823_; 
v_snd_1805_ = lean_ctor_get(v_b_1797_, 1);
v_isSharedCheck_1823_ = !lean_is_exclusive(v_b_1797_);
if (v_isSharedCheck_1823_ == 0)
{
lean_object* v_unused_1824_; 
v_unused_1824_ = lean_ctor_get(v_b_1797_, 0);
lean_dec(v_unused_1824_);
v___x_1807_ = v_b_1797_;
v_isShared_1808_ = v_isSharedCheck_1823_;
goto v_resetjp_1806_;
}
else
{
lean_inc(v_snd_1805_);
lean_dec(v_b_1797_);
v___x_1807_ = lean_box(0);
v_isShared_1808_ = v_isSharedCheck_1823_;
goto v_resetjp_1806_;
}
v_resetjp_1806_:
{
lean_object* v___x_1809_; lean_object* v_a_1811_; lean_object* v_a_1818_; 
v___x_1809_ = lean_box(0);
v_a_1818_ = lean_array_uget_borrowed(v_as_1794_, v_i_1796_);
if (lean_obj_tag(v_a_1818_) == 0)
{
v_a_1811_ = v_snd_1805_;
goto v___jp_1810_;
}
else
{
lean_object* v_val_1819_; uint8_t v___x_1820_; 
v_val_1819_ = lean_ctor_get(v_a_1818_, 0);
v___x_1820_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1819_);
if (v___x_1820_ == 0)
{
v_a_1811_ = v_snd_1805_;
goto v___jp_1810_;
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1821_ = l_Lean_LocalDecl_fvarId(v_val_1819_);
v___x_1822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
lean_ctor_set(v___x_1822_, 1, v_snd_1805_);
v_a_1811_ = v___x_1822_;
goto v___jp_1810_;
}
}
v___jp_1810_:
{
lean_object* v___x_1813_; 
if (v_isShared_1808_ == 0)
{
lean_ctor_set(v___x_1807_, 1, v_a_1811_);
lean_ctor_set(v___x_1807_, 0, v___x_1809_);
v___x_1813_ = v___x_1807_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1817_; 
v_reuseFailAlloc_1817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1817_, 0, v___x_1809_);
lean_ctor_set(v_reuseFailAlloc_1817_, 1, v_a_1811_);
v___x_1813_ = v_reuseFailAlloc_1817_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
size_t v___x_1814_; size_t v___x_1815_; lean_object* v___x_1816_; 
v___x_1814_ = ((size_t)1ULL);
v___x_1815_ = lean_usize_add(v_i_1796_, v___x_1814_);
v___x_1816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1794_, v_sz_1795_, v___x_1815_, v___x_1813_);
return v___x_1816_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1___boxed(lean_object* v_as_1825_, lean_object* v_sz_1826_, lean_object* v_i_1827_, lean_object* v_b_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
size_t v_sz_boxed_1834_; size_t v_i_boxed_1835_; lean_object* v_res_1836_; 
v_sz_boxed_1834_ = lean_unbox_usize(v_sz_1826_);
lean_dec(v_sz_1826_);
v_i_boxed_1835_ = lean_unbox_usize(v_i_1827_);
lean_dec(v_i_1827_);
v_res_1836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_as_1825_, v_sz_boxed_1834_, v_i_boxed_1835_, v_b_1828_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
lean_dec(v___y_1832_);
lean_dec_ref(v___y_1831_);
lean_dec(v___y_1830_);
lean_dec_ref(v___y_1829_);
lean_dec_ref(v_as_1825_);
return v_res_1836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(lean_object* v_t_1837_, lean_object* v_init_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_){
_start:
{
lean_object* v_root_1844_; lean_object* v_tail_1845_; lean_object* v___x_1846_; 
v_root_1844_ = lean_ctor_get(v_t_1837_, 0);
lean_inc_ref(v_root_1844_);
v_tail_1845_ = lean_ctor_get(v_t_1837_, 1);
lean_inc_ref(v_tail_1845_);
lean_dec_ref(v_t_1837_);
lean_inc(v_init_1838_);
v___x_1846_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1838_, v_root_1844_, v_init_1838_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec(v_init_1838_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1849_; uint8_t v_isShared_1850_; uint8_t v_isSharedCheck_1883_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1883_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1883_ == 0)
{
v___x_1849_ = v___x_1846_;
v_isShared_1850_ = v_isSharedCheck_1883_;
goto v_resetjp_1848_;
}
else
{
lean_inc(v_a_1847_);
lean_dec(v___x_1846_);
v___x_1849_ = lean_box(0);
v_isShared_1850_ = v_isSharedCheck_1883_;
goto v_resetjp_1848_;
}
v_resetjp_1848_:
{
if (lean_obj_tag(v_a_1847_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1853_; 
lean_dec_ref(v_tail_1845_);
v_a_1851_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_a_1851_);
lean_dec_ref(v_a_1847_);
if (v_isShared_1850_ == 0)
{
lean_ctor_set(v___x_1849_, 0, v_a_1851_);
v___x_1853_ = v___x_1849_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v_a_1851_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
else
{
lean_object* v_a_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; size_t v_sz_1858_; size_t v___x_1859_; lean_object* v___x_1860_; 
lean_del_object(v___x_1849_);
v_a_1855_ = lean_ctor_get(v_a_1847_, 0);
lean_inc(v_a_1855_);
lean_dec_ref(v_a_1847_);
v___x_1856_ = lean_box(0);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1856_);
lean_ctor_set(v___x_1857_, 1, v_a_1855_);
v_sz_1858_ = lean_array_size(v_tail_1845_);
v___x_1859_ = ((size_t)0ULL);
v___x_1860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1(v_tail_1845_, v_sz_1858_, v___x_1859_, v___x_1857_, v___y_1839_, v___y_1840_, v___y_1841_, v___y_1842_);
lean_dec_ref(v_tail_1845_);
if (lean_obj_tag(v___x_1860_) == 0)
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1874_; 
v_a_1861_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1874_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1874_ == 0)
{
v___x_1863_ = v___x_1860_;
v_isShared_1864_ = v_isSharedCheck_1874_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1860_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1874_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v_fst_1865_; 
v_fst_1865_ = lean_ctor_get(v_a_1861_, 0);
if (lean_obj_tag(v_fst_1865_) == 0)
{
lean_object* v_snd_1866_; lean_object* v___x_1868_; 
v_snd_1866_ = lean_ctor_get(v_a_1861_, 1);
lean_inc(v_snd_1866_);
lean_dec(v_a_1861_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v_snd_1866_);
v___x_1868_ = v___x_1863_;
goto v_reusejp_1867_;
}
else
{
lean_object* v_reuseFailAlloc_1869_; 
v_reuseFailAlloc_1869_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_snd_1866_);
v___x_1868_ = v_reuseFailAlloc_1869_;
goto v_reusejp_1867_;
}
v_reusejp_1867_:
{
return v___x_1868_;
}
}
else
{
lean_object* v_val_1870_; lean_object* v___x_1872_; 
lean_inc_ref(v_fst_1865_);
lean_dec(v_a_1861_);
v_val_1870_ = lean_ctor_get(v_fst_1865_, 0);
lean_inc(v_val_1870_);
lean_dec_ref(v_fst_1865_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 0, v_val_1870_);
v___x_1872_ = v___x_1863_;
goto v_reusejp_1871_;
}
else
{
lean_object* v_reuseFailAlloc_1873_; 
v_reuseFailAlloc_1873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_val_1870_);
v___x_1872_ = v_reuseFailAlloc_1873_;
goto v_reusejp_1871_;
}
v_reusejp_1871_:
{
return v___x_1872_;
}
}
}
}
else
{
lean_object* v_a_1875_; lean_object* v___x_1877_; uint8_t v_isShared_1878_; uint8_t v_isSharedCheck_1882_; 
v_a_1875_ = lean_ctor_get(v___x_1860_, 0);
v_isSharedCheck_1882_ = !lean_is_exclusive(v___x_1860_);
if (v_isSharedCheck_1882_ == 0)
{
v___x_1877_ = v___x_1860_;
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
else
{
lean_inc(v_a_1875_);
lean_dec(v___x_1860_);
v___x_1877_ = lean_box(0);
v_isShared_1878_ = v_isSharedCheck_1882_;
goto v_resetjp_1876_;
}
v_resetjp_1876_:
{
lean_object* v___x_1880_; 
if (v_isShared_1878_ == 0)
{
v___x_1880_ = v___x_1877_;
goto v_reusejp_1879_;
}
else
{
lean_object* v_reuseFailAlloc_1881_; 
v_reuseFailAlloc_1881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_a_1875_);
v___x_1880_ = v_reuseFailAlloc_1881_;
goto v_reusejp_1879_;
}
v_reusejp_1879_:
{
return v___x_1880_;
}
}
}
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec_ref(v_tail_1845_);
v_a_1884_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1846_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1846_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0___boxed(lean_object* v_t_1892_, lean_object* v_init_1893_, lean_object* v___y_1894_, lean_object* v___y_1895_, lean_object* v___y_1896_, lean_object* v___y_1897_, lean_object* v___y_1898_){
_start:
{
lean_object* v_res_1899_; 
v_res_1899_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_t_1892_, v_init_1893_, v___y_1894_, v___y_1895_, v___y_1896_, v___y_1897_);
lean_dec(v___y_1897_);
lean_dec_ref(v___y_1896_);
lean_dec(v___y_1895_);
lean_dec_ref(v___y_1894_);
return v_res_1899_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0(lean_object* v_mvarId_1900_, lean_object* v___x_1901_, lean_object* v___y_1902_, lean_object* v___y_1903_, lean_object* v___y_1904_, lean_object* v___y_1905_){
_start:
{
lean_object* v___x_1907_; 
lean_inc(v_mvarId_1900_);
v___x_1907_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1900_, v___x_1901_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_lctx_1908_; lean_object* v_decls_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
lean_dec_ref(v___x_1907_);
v_lctx_1908_ = lean_ctor_get(v___y_1902_, 2);
v_decls_1909_ = lean_ctor_get(v_lctx_1908_, 1);
v___x_1910_ = lean_box(0);
lean_inc_ref(v_decls_1909_);
v___x_1911_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0(v_decls_1909_, v___x_1910_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1921_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1921_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1921_ == 0)
{
v___x_1914_ = v___x_1911_;
v_isShared_1915_ = v_isSharedCheck_1921_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1911_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1921_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
uint8_t v___x_1916_; 
v___x_1916_ = l_List_isEmpty___redArg(v_a_1912_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; 
lean_del_object(v___x_1914_);
v___x_1917_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_a_1912_, v_mvarId_1900_, v___y_1902_, v___y_1903_, v___y_1904_, v___y_1905_);
lean_dec_ref(v___y_1902_);
return v___x_1917_;
}
else
{
lean_object* v___x_1919_; 
lean_dec(v_a_1912_);
lean_dec_ref(v___y_1902_);
if (v_isShared_1915_ == 0)
{
lean_ctor_set(v___x_1914_, 0, v_mvarId_1900_);
v___x_1919_ = v___x_1914_;
goto v_reusejp_1918_;
}
else
{
lean_object* v_reuseFailAlloc_1920_; 
v_reuseFailAlloc_1920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_mvarId_1900_);
v___x_1919_ = v_reuseFailAlloc_1920_;
goto v_reusejp_1918_;
}
v_reusejp_1918_:
{
return v___x_1919_;
}
}
}
}
else
{
lean_object* v_a_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1929_; 
lean_dec_ref(v___y_1902_);
lean_dec(v_mvarId_1900_);
v_a_1922_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1924_ = v___x_1911_;
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_a_1922_);
lean_dec(v___x_1911_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1929_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v_a_1922_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
return v___x_1927_;
}
}
}
}
else
{
lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec_ref(v___y_1902_);
lean_dec(v_mvarId_1900_);
v_a_1930_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1907_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_dec(v___x_1907_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___lam__0___boxed(lean_object* v_mvarId_1938_, lean_object* v___x_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_Lean_MVarId_clearImplDetails___lam__0(v_mvarId_1938_, v___x_1939_, v___y_1940_, v___y_1941_, v___y_1942_, v___y_1943_);
lean_dec(v___y_1943_);
lean_dec_ref(v___y_1942_);
lean_dec(v___y_1941_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails(lean_object* v_mvarId_1950_, lean_object* v_a_1951_, lean_object* v_a_1952_, lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___x_1956_; lean_object* v___f_1957_; lean_object* v___x_1958_; 
v___x_1956_ = ((lean_object*)(l_Lean_MVarId_clearImplDetails___closed__1));
lean_inc(v_mvarId_1950_);
v___f_1957_ = lean_alloc_closure((void*)(l_Lean_MVarId_clearImplDetails___lam__0___boxed), 7, 2);
lean_closure_set(v___f_1957_, 0, v_mvarId_1950_);
lean_closure_set(v___f_1957_, 1, v___x_1956_);
v___x_1958_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_abstractMVars_spec__1___redArg(v_mvarId_1950_, v___f_1957_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_clearImplDetails___boxed(lean_object* v_mvarId_1959_, lean_object* v_a_1960_, lean_object* v_a_1961_, lean_object* v_a_1962_, lean_object* v_a_1963_, lean_object* v_a_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_MVarId_clearImplDetails(v_mvarId_1959_, v_a_1960_, v_a_1961_, v_a_1962_, v_a_1963_);
lean_dec(v_a_1963_);
lean_dec_ref(v_a_1962_);
lean_dec(v_a_1961_);
lean_dec_ref(v_a_1960_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(lean_object* v_as_1966_, lean_object* v_as_x27_1967_, lean_object* v_b_1968_, lean_object* v_a_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___redArg(v_as_x27_1967_, v_b_1968_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1___boxed(lean_object* v_as_1976_, lean_object* v_as_x27_1977_, lean_object* v_b_1978_, lean_object* v_a_1979_, lean_object* v___y_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_List_forIn_x27_loop___at___00Lean_MVarId_clearImplDetails_spec__1(v_as_1976_, v_as_x27_1977_, v_b_1978_, v_a_1979_, v___y_1980_, v___y_1981_, v___y_1982_, v___y_1983_);
lean_dec(v___y_1983_);
lean_dec_ref(v___y_1982_);
lean_dec(v___y_1981_);
lean_dec_ref(v___y_1980_);
lean_dec(v_as_1976_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(lean_object* v_as_1986_, size_t v_sz_1987_, size_t v_i_1988_, lean_object* v_b_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_, lean_object* v___y_1992_, lean_object* v___y_1993_){
_start:
{
lean_object* v___x_1995_; 
v___x_1995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___redArg(v_as_1986_, v_sz_1987_, v_i_1988_, v_b_1989_);
return v___x_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4___boxed(lean_object* v_as_1996_, lean_object* v_sz_1997_, lean_object* v_i_1998_, lean_object* v_b_1999_, lean_object* v___y_2000_, lean_object* v___y_2001_, lean_object* v___y_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_){
_start:
{
size_t v_sz_boxed_2005_; size_t v_i_boxed_2006_; lean_object* v_res_2007_; 
v_sz_boxed_2005_ = lean_unbox_usize(v_sz_1997_);
lean_dec(v_sz_1997_);
v_i_boxed_2006_ = lean_unbox_usize(v_i_1998_);
lean_dec(v_i_1998_);
v_res_2007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__1_spec__4(v_as_1996_, v_sz_boxed_2005_, v_i_boxed_2006_, v_b_1999_, v___y_2000_, v___y_2001_, v___y_2002_, v___y_2003_);
lean_dec(v___y_2003_);
lean_dec_ref(v___y_2002_);
lean_dec(v___y_2001_);
lean_dec_ref(v___y_2000_);
lean_dec_ref(v_as_1996_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(lean_object* v_as_2008_, size_t v_sz_2009_, size_t v_i_2010_, lean_object* v_b_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___redArg(v_as_2008_, v_sz_2009_, v_i_2010_, v_b_2011_);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_as_2018_, lean_object* v_sz_2019_, lean_object* v_i_2020_, lean_object* v_b_2021_, lean_object* v___y_2022_, lean_object* v___y_2023_, lean_object* v___y_2024_, lean_object* v___y_2025_, lean_object* v___y_2026_){
_start:
{
size_t v_sz_boxed_2027_; size_t v_i_boxed_2028_; lean_object* v_res_2029_; 
v_sz_boxed_2027_ = lean_unbox_usize(v_sz_2019_);
lean_dec(v_sz_2019_);
v_i_boxed_2028_ = lean_unbox_usize(v_i_2020_);
lean_dec(v_i_2020_);
v_res_2029_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__2_spec__4(v_as_2018_, v_sz_boxed_2027_, v_i_boxed_2028_, v_b_2021_, v___y_2022_, v___y_2023_, v___y_2024_, v___y_2025_);
lean_dec(v___y_2025_);
lean_dec_ref(v___y_2024_);
lean_dec(v___y_2023_);
lean_dec_ref(v___y_2022_);
lean_dec_ref(v_as_2018_);
return v_res_2029_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(lean_object* v_e_2030_, lean_object* v___y_2031_, lean_object* v___y_2032_){
_start:
{
switch(lean_obj_tag(v_e_2030_))
{
case 8:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_e_2030_);
v___x_2035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2035_, 0, v___x_2034_);
return v___x_2035_;
}
case 6:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2036_, 0, v_e_2030_);
v___x_2037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2036_);
return v___x_2037_;
}
case 10:
{
lean_object* v_expr_2038_; lean_object* v___x_2039_; lean_object* v___x_2040_; 
v_expr_2038_ = lean_ctor_get(v_e_2030_, 1);
lean_inc_ref(v_expr_2038_);
lean_dec_ref(v_e_2030_);
v___x_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2039_, 0, v_expr_2038_);
v___x_2040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2040_, 0, v___x_2039_);
return v___x_2040_;
}
default: 
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2041_, 0, v_e_2030_);
v___x_2042_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
v___x_2043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2043_, 0, v___x_2042_);
return v___x_2043_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0___boxed(lean_object* v_e_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__0(v_e_2044_, v___y_2045_, v___y_2046_);
lean_dec(v___y_2046_);
lean_dec_ref(v___y_2045_);
return v_res_2048_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(lean_object* v_e_2049_, lean_object* v___y_2050_, lean_object* v___y_2051_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; 
v___x_2053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2053_, 0, v_e_2049_);
v___x_2054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2054_, 0, v___x_2053_);
return v___x_2054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1___boxed(lean_object* v_e_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v_res_2059_; 
v_res_2059_ = l_Lean_Meta_Grind_eraseIrrelevantMData___lam__1(v_e_2055_, v___y_2056_, v___y_2057_);
lean_dec(v___y_2057_);
lean_dec_ref(v___y_2056_);
return v_res_2059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_object* v_00_u03b1_2060_, lean_object* v_x_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_){
_start:
{
lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2065_ = lean_apply_1(v_x_2061_, lean_box(0));
v___x_2066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2066_, 0, v___x_2065_);
return v___x_2066_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2067_, lean_object* v_x_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(v_00_u03b1_2067_, v_x_2068_, v___y_2069_, v___y_2070_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(lean_object* v_a_2073_, lean_object* v_x_2074_){
_start:
{
if (lean_obj_tag(v_x_2074_) == 0)
{
lean_object* v___x_2075_; 
v___x_2075_ = lean_box(0);
return v___x_2075_;
}
else
{
lean_object* v_key_2076_; lean_object* v_value_2077_; lean_object* v_tail_2078_; uint8_t v___x_2079_; 
v_key_2076_ = lean_ctor_get(v_x_2074_, 0);
v_value_2077_ = lean_ctor_get(v_x_2074_, 1);
v_tail_2078_ = lean_ctor_get(v_x_2074_, 2);
v___x_2079_ = l_Lean_ExprStructEq_beq(v_key_2076_, v_a_2073_);
if (v___x_2079_ == 0)
{
v_x_2074_ = v_tail_2078_;
goto _start;
}
else
{
lean_object* v___x_2081_; 
lean_inc(v_value_2077_);
v___x_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2081_, 0, v_value_2077_);
return v___x_2081_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg___boxed(lean_object* v_a_2082_, lean_object* v_x_2083_){
_start:
{
lean_object* v_res_2084_; 
v_res_2084_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2082_, v_x_2083_);
lean_dec(v_x_2083_);
lean_dec_ref(v_a_2082_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(lean_object* v_m_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v_buckets_2087_; lean_object* v___x_2088_; uint64_t v___x_2089_; uint64_t v___x_2090_; uint64_t v___x_2091_; uint64_t v_fold_2092_; uint64_t v___x_2093_; uint64_t v___x_2094_; uint64_t v___x_2095_; size_t v___x_2096_; size_t v___x_2097_; size_t v___x_2098_; size_t v___x_2099_; size_t v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; 
v_buckets_2087_ = lean_ctor_get(v_m_2085_, 1);
v___x_2088_ = lean_array_get_size(v_buckets_2087_);
v___x_2089_ = l_Lean_ExprStructEq_hash(v_a_2086_);
v___x_2090_ = 32ULL;
v___x_2091_ = lean_uint64_shift_right(v___x_2089_, v___x_2090_);
v_fold_2092_ = lean_uint64_xor(v___x_2089_, v___x_2091_);
v___x_2093_ = 16ULL;
v___x_2094_ = lean_uint64_shift_right(v_fold_2092_, v___x_2093_);
v___x_2095_ = lean_uint64_xor(v_fold_2092_, v___x_2094_);
v___x_2096_ = lean_uint64_to_usize(v___x_2095_);
v___x_2097_ = lean_usize_of_nat(v___x_2088_);
v___x_2098_ = ((size_t)1ULL);
v___x_2099_ = lean_usize_sub(v___x_2097_, v___x_2098_);
v___x_2100_ = lean_usize_land(v___x_2096_, v___x_2099_);
v___x_2101_ = lean_array_uget_borrowed(v_buckets_2087_, v___x_2100_);
v___x_2102_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2086_, v___x_2101_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_m_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v_res_2105_; 
v_res_2105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2103_, v_a_2104_);
lean_dec_ref(v_a_2104_);
lean_dec_ref(v_m_2103_);
return v_res_2105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_object* v_00_u03b1_2106_, lean_object* v_x_2107_, lean_object* v___y_2108_, lean_object* v___y_2109_){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_apply_1(v_x_2107_, lean_box(0));
v___x_2112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0___boxed(lean_object* v_00_u03b1_2113_, lean_object* v_x_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(v_00_u03b1_2113_, v_x_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
return v_res_2118_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = l_Lean_maxRecDepthErrorMessage;
v___x_2125_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2125_, 0, v___x_2124_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; 
v___x_2126_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__3);
v___x_2127_ = l_Lean_MessageData_ofFormat(v___x_2126_);
return v___x_2127_;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5(void){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; 
v___x_2128_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__4);
v___x_2129_ = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__2));
v___x_2130_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2129_);
lean_ctor_set(v___x_2130_, 1, v___x_2128_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(lean_object* v_ref_2131_){
_start:
{
lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v___x_2133_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_2134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2134_, 0, v_ref_2131_);
lean_ctor_set(v___x_2134_, 1, v___x_2133_);
v___x_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2134_);
return v___x_2135_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___boxed(lean_object* v_ref_2136_, lean_object* v___y_2137_){
_start:
{
lean_object* v_res_2138_; 
v_res_2138_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2136_);
return v_res_2138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(lean_object* v_x_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
lean_object* v___y_2145_; lean_object* v_fileName_2154_; lean_object* v_fileMap_2155_; lean_object* v_options_2156_; lean_object* v_currRecDepth_2157_; lean_object* v_maxRecDepth_2158_; lean_object* v_ref_2159_; lean_object* v_currNamespace_2160_; lean_object* v_openDecls_2161_; lean_object* v_initHeartbeats_2162_; lean_object* v_maxHeartbeats_2163_; lean_object* v_quotContext_2164_; lean_object* v_currMacroScope_2165_; uint8_t v_diag_2166_; lean_object* v_cancelTk_x3f_2167_; uint8_t v_suppressElabErrors_2168_; lean_object* v_inheritedTraceOptions_2169_; lean_object* v___x_2175_; uint8_t v___x_2176_; 
v_fileName_2154_ = lean_ctor_get(v___y_2141_, 0);
v_fileMap_2155_ = lean_ctor_get(v___y_2141_, 1);
v_options_2156_ = lean_ctor_get(v___y_2141_, 2);
v_currRecDepth_2157_ = lean_ctor_get(v___y_2141_, 3);
v_maxRecDepth_2158_ = lean_ctor_get(v___y_2141_, 4);
v_ref_2159_ = lean_ctor_get(v___y_2141_, 5);
v_currNamespace_2160_ = lean_ctor_get(v___y_2141_, 6);
v_openDecls_2161_ = lean_ctor_get(v___y_2141_, 7);
v_initHeartbeats_2162_ = lean_ctor_get(v___y_2141_, 8);
v_maxHeartbeats_2163_ = lean_ctor_get(v___y_2141_, 9);
v_quotContext_2164_ = lean_ctor_get(v___y_2141_, 10);
v_currMacroScope_2165_ = lean_ctor_get(v___y_2141_, 11);
v_diag_2166_ = lean_ctor_get_uint8(v___y_2141_, sizeof(void*)*14);
v_cancelTk_x3f_2167_ = lean_ctor_get(v___y_2141_, 12);
v_suppressElabErrors_2168_ = lean_ctor_get_uint8(v___y_2141_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2169_ = lean_ctor_get(v___y_2141_, 13);
v___x_2175_ = lean_unsigned_to_nat(0u);
v___x_2176_ = lean_nat_dec_eq(v_maxRecDepth_2158_, v___x_2175_);
if (v___x_2176_ == 0)
{
uint8_t v___x_2177_; 
v___x_2177_ = lean_nat_dec_eq(v_currRecDepth_2157_, v_maxRecDepth_2158_);
if (v___x_2177_ == 0)
{
goto v___jp_2170_;
}
else
{
lean_object* v___x_2178_; 
lean_dec_ref(v_x_2139_);
lean_inc(v_ref_2159_);
v___x_2178_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2159_);
v___y_2145_ = v___x_2178_;
goto v___jp_2144_;
}
}
else
{
goto v___jp_2170_;
}
v___jp_2144_:
{
if (lean_obj_tag(v___y_2145_) == 0)
{
return v___y_2145_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2148_; uint8_t v_isShared_2149_; uint8_t v_isSharedCheck_2153_; 
v_a_2146_ = lean_ctor_get(v___y_2145_, 0);
v_isSharedCheck_2153_ = !lean_is_exclusive(v___y_2145_);
if (v_isSharedCheck_2153_ == 0)
{
v___x_2148_ = v___y_2145_;
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
else
{
lean_inc(v_a_2146_);
lean_dec(v___y_2145_);
v___x_2148_ = lean_box(0);
v_isShared_2149_ = v_isSharedCheck_2153_;
goto v_resetjp_2147_;
}
v_resetjp_2147_:
{
lean_object* v___x_2151_; 
if (v_isShared_2149_ == 0)
{
v___x_2151_ = v___x_2148_;
goto v_reusejp_2150_;
}
else
{
lean_object* v_reuseFailAlloc_2152_; 
v_reuseFailAlloc_2152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2152_, 0, v_a_2146_);
v___x_2151_ = v_reuseFailAlloc_2152_;
goto v_reusejp_2150_;
}
v_reusejp_2150_:
{
return v___x_2151_;
}
}
}
}
v___jp_2170_:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2171_ = lean_unsigned_to_nat(1u);
v___x_2172_ = lean_nat_add(v_currRecDepth_2157_, v___x_2171_);
lean_inc_ref(v_inheritedTraceOptions_2169_);
lean_inc(v_cancelTk_x3f_2167_);
lean_inc(v_currMacroScope_2165_);
lean_inc(v_quotContext_2164_);
lean_inc(v_maxHeartbeats_2163_);
lean_inc(v_initHeartbeats_2162_);
lean_inc(v_openDecls_2161_);
lean_inc(v_currNamespace_2160_);
lean_inc(v_ref_2159_);
lean_inc(v_maxRecDepth_2158_);
lean_inc_ref(v_options_2156_);
lean_inc_ref(v_fileMap_2155_);
lean_inc_ref(v_fileName_2154_);
v___x_2173_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2173_, 0, v_fileName_2154_);
lean_ctor_set(v___x_2173_, 1, v_fileMap_2155_);
lean_ctor_set(v___x_2173_, 2, v_options_2156_);
lean_ctor_set(v___x_2173_, 3, v___x_2172_);
lean_ctor_set(v___x_2173_, 4, v_maxRecDepth_2158_);
lean_ctor_set(v___x_2173_, 5, v_ref_2159_);
lean_ctor_set(v___x_2173_, 6, v_currNamespace_2160_);
lean_ctor_set(v___x_2173_, 7, v_openDecls_2161_);
lean_ctor_set(v___x_2173_, 8, v_initHeartbeats_2162_);
lean_ctor_set(v___x_2173_, 9, v_maxHeartbeats_2163_);
lean_ctor_set(v___x_2173_, 10, v_quotContext_2164_);
lean_ctor_set(v___x_2173_, 11, v_currMacroScope_2165_);
lean_ctor_set(v___x_2173_, 12, v_cancelTk_x3f_2167_);
lean_ctor_set(v___x_2173_, 13, v_inheritedTraceOptions_2169_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*14, v_diag_2166_);
lean_ctor_set_uint8(v___x_2173_, sizeof(void*)*14 + 1, v_suppressElabErrors_2168_);
lean_inc(v___y_2142_);
lean_inc(v___y_2140_);
v___x_2174_ = lean_apply_4(v_x_2139_, v___y_2140_, v___x_2173_, v___y_2142_, lean_box(0));
v___y_2145_ = v___x_2174_;
goto v___jp_2144_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2179_, v___y_2180_, v___y_2181_, v___y_2182_);
lean_dec(v___y_2182_);
lean_dec_ref(v___y_2181_);
lean_dec(v___y_2180_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_2185_, lean_object* v_x_2186_){
_start:
{
if (lean_obj_tag(v_x_2186_) == 0)
{
return v_x_2185_;
}
else
{
lean_object* v_key_2187_; lean_object* v_value_2188_; lean_object* v_tail_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2212_; 
v_key_2187_ = lean_ctor_get(v_x_2186_, 0);
v_value_2188_ = lean_ctor_get(v_x_2186_, 1);
v_tail_2189_ = lean_ctor_get(v_x_2186_, 2);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_x_2186_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2191_ = v_x_2186_;
v_isShared_2192_ = v_isSharedCheck_2212_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_tail_2189_);
lean_inc(v_value_2188_);
lean_inc(v_key_2187_);
lean_dec(v_x_2186_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2212_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; uint64_t v___x_2194_; uint64_t v___x_2195_; uint64_t v___x_2196_; uint64_t v_fold_2197_; uint64_t v___x_2198_; uint64_t v___x_2199_; uint64_t v___x_2200_; size_t v___x_2201_; size_t v___x_2202_; size_t v___x_2203_; size_t v___x_2204_; size_t v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2193_ = lean_array_get_size(v_x_2185_);
v___x_2194_ = l_Lean_ExprStructEq_hash(v_key_2187_);
v___x_2195_ = 32ULL;
v___x_2196_ = lean_uint64_shift_right(v___x_2194_, v___x_2195_);
v_fold_2197_ = lean_uint64_xor(v___x_2194_, v___x_2196_);
v___x_2198_ = 16ULL;
v___x_2199_ = lean_uint64_shift_right(v_fold_2197_, v___x_2198_);
v___x_2200_ = lean_uint64_xor(v_fold_2197_, v___x_2199_);
v___x_2201_ = lean_uint64_to_usize(v___x_2200_);
v___x_2202_ = lean_usize_of_nat(v___x_2193_);
v___x_2203_ = ((size_t)1ULL);
v___x_2204_ = lean_usize_sub(v___x_2202_, v___x_2203_);
v___x_2205_ = lean_usize_land(v___x_2201_, v___x_2204_);
v___x_2206_ = lean_array_uget_borrowed(v_x_2185_, v___x_2205_);
lean_inc(v___x_2206_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 2, v___x_2206_);
v___x_2208_ = v___x_2191_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_key_2187_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v_value_2188_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v___x_2206_);
v___x_2208_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_array_uset(v_x_2185_, v___x_2205_, v___x_2208_);
v_x_2185_ = v___x_2209_;
v_x_2186_ = v_tail_2189_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_2213_, lean_object* v_source_2214_, lean_object* v_target_2215_){
_start:
{
lean_object* v___x_2216_; uint8_t v___x_2217_; 
v___x_2216_ = lean_array_get_size(v_source_2214_);
v___x_2217_ = lean_nat_dec_lt(v_i_2213_, v___x_2216_);
if (v___x_2217_ == 0)
{
lean_dec_ref(v_source_2214_);
lean_dec(v_i_2213_);
return v_target_2215_;
}
else
{
lean_object* v_es_2218_; lean_object* v___x_2219_; lean_object* v_source_2220_; lean_object* v_target_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v_es_2218_ = lean_array_fget(v_source_2214_, v_i_2213_);
v___x_2219_ = lean_box(0);
v_source_2220_ = lean_array_fset(v_source_2214_, v_i_2213_, v___x_2219_);
v_target_2221_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_2215_, v_es_2218_);
v___x_2222_ = lean_unsigned_to_nat(1u);
v___x_2223_ = lean_nat_add(v_i_2213_, v___x_2222_);
lean_dec(v_i_2213_);
v_i_2213_ = v___x_2223_;
v_source_2214_ = v_source_2220_;
v_target_2215_ = v_target_2221_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_2225_){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v_nbuckets_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2226_ = lean_array_get_size(v_data_2225_);
v___x_2227_ = lean_unsigned_to_nat(2u);
v_nbuckets_2228_ = lean_nat_mul(v___x_2226_, v___x_2227_);
v___x_2229_ = lean_unsigned_to_nat(0u);
v___x_2230_ = lean_box(0);
v___x_2231_ = lean_mk_array(v_nbuckets_2228_, v___x_2230_);
v___x_2232_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_2229_, v_data_2225_, v___x_2231_);
return v___x_2232_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_2233_, lean_object* v_x_2234_){
_start:
{
if (lean_obj_tag(v_x_2234_) == 0)
{
uint8_t v___x_2235_; 
v___x_2235_ = 0;
return v___x_2235_;
}
else
{
lean_object* v_key_2236_; lean_object* v_tail_2237_; uint8_t v___x_2238_; 
v_key_2236_ = lean_ctor_get(v_x_2234_, 0);
v_tail_2237_ = lean_ctor_get(v_x_2234_, 2);
v___x_2238_ = l_Lean_ExprStructEq_beq(v_key_2236_, v_a_2233_);
if (v___x_2238_ == 0)
{
v_x_2234_ = v_tail_2237_;
goto _start;
}
else
{
return v___x_2238_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_2240_, lean_object* v_x_2241_){
_start:
{
uint8_t v_res_2242_; lean_object* v_r_2243_; 
v_res_2242_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(v_a_2240_, v_x_2241_);
lean_dec(v_x_2241_);
lean_dec_ref(v_a_2240_);
v_r_2243_ = lean_box(v_res_2242_);
return v_r_2243_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_2244_, lean_object* v_b_2245_, lean_object* v_x_2246_){
_start:
{
if (lean_obj_tag(v_x_2246_) == 0)
{
lean_dec(v_b_2245_);
lean_dec_ref(v_a_2244_);
return v_x_2246_;
}
else
{
lean_object* v_key_2247_; lean_object* v_value_2248_; lean_object* v_tail_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2261_; 
v_key_2247_ = lean_ctor_get(v_x_2246_, 0);
v_value_2248_ = lean_ctor_get(v_x_2246_, 1);
v_tail_2249_ = lean_ctor_get(v_x_2246_, 2);
v_isSharedCheck_2261_ = !lean_is_exclusive(v_x_2246_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2251_ = v_x_2246_;
v_isShared_2252_ = v_isSharedCheck_2261_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_tail_2249_);
lean_inc(v_value_2248_);
lean_inc(v_key_2247_);
lean_dec(v_x_2246_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2261_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
uint8_t v___x_2253_; 
v___x_2253_ = l_Lean_ExprStructEq_beq(v_key_2247_, v_a_2244_);
if (v___x_2253_ == 0)
{
lean_object* v___x_2254_; lean_object* v___x_2256_; 
v___x_2254_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_a_2244_, v_b_2245_, v_tail_2249_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 2, v___x_2254_);
v___x_2256_ = v___x_2251_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_key_2247_);
lean_ctor_set(v_reuseFailAlloc_2257_, 1, v_value_2248_);
lean_ctor_set(v_reuseFailAlloc_2257_, 2, v___x_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
else
{
lean_object* v___x_2259_; 
lean_dec(v_value_2248_);
lean_dec(v_key_2247_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 1, v_b_2245_);
lean_ctor_set(v___x_2251_, 0, v_a_2244_);
v___x_2259_ = v___x_2251_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_a_2244_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_b_2245_);
lean_ctor_set(v_reuseFailAlloc_2260_, 2, v_tail_2249_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(lean_object* v_m_2262_, lean_object* v_a_2263_, lean_object* v_b_2264_){
_start:
{
lean_object* v_size_2265_; lean_object* v_buckets_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2309_; 
v_size_2265_ = lean_ctor_get(v_m_2262_, 0);
v_buckets_2266_ = lean_ctor_get(v_m_2262_, 1);
v_isSharedCheck_2309_ = !lean_is_exclusive(v_m_2262_);
if (v_isSharedCheck_2309_ == 0)
{
v___x_2268_ = v_m_2262_;
v_isShared_2269_ = v_isSharedCheck_2309_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_buckets_2266_);
lean_inc(v_size_2265_);
lean_dec(v_m_2262_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2309_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2270_; uint64_t v___x_2271_; uint64_t v___x_2272_; uint64_t v___x_2273_; uint64_t v_fold_2274_; uint64_t v___x_2275_; uint64_t v___x_2276_; uint64_t v___x_2277_; size_t v___x_2278_; size_t v___x_2279_; size_t v___x_2280_; size_t v___x_2281_; size_t v___x_2282_; lean_object* v_bkt_2283_; uint8_t v___x_2284_; 
v___x_2270_ = lean_array_get_size(v_buckets_2266_);
v___x_2271_ = l_Lean_ExprStructEq_hash(v_a_2263_);
v___x_2272_ = 32ULL;
v___x_2273_ = lean_uint64_shift_right(v___x_2271_, v___x_2272_);
v_fold_2274_ = lean_uint64_xor(v___x_2271_, v___x_2273_);
v___x_2275_ = 16ULL;
v___x_2276_ = lean_uint64_shift_right(v_fold_2274_, v___x_2275_);
v___x_2277_ = lean_uint64_xor(v_fold_2274_, v___x_2276_);
v___x_2278_ = lean_uint64_to_usize(v___x_2277_);
v___x_2279_ = lean_usize_of_nat(v___x_2270_);
v___x_2280_ = ((size_t)1ULL);
v___x_2281_ = lean_usize_sub(v___x_2279_, v___x_2280_);
v___x_2282_ = lean_usize_land(v___x_2278_, v___x_2281_);
v_bkt_2283_ = lean_array_uget_borrowed(v_buckets_2266_, v___x_2282_);
v___x_2284_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(v_a_2263_, v_bkt_2283_);
if (v___x_2284_ == 0)
{
lean_object* v___x_2285_; lean_object* v_size_x27_2286_; lean_object* v___x_2287_; lean_object* v_buckets_x27_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; uint8_t v___x_2294_; 
v___x_2285_ = lean_unsigned_to_nat(1u);
v_size_x27_2286_ = lean_nat_add(v_size_2265_, v___x_2285_);
lean_dec(v_size_2265_);
lean_inc(v_bkt_2283_);
v___x_2287_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2287_, 0, v_a_2263_);
lean_ctor_set(v___x_2287_, 1, v_b_2264_);
lean_ctor_set(v___x_2287_, 2, v_bkt_2283_);
v_buckets_x27_2288_ = lean_array_uset(v_buckets_2266_, v___x_2282_, v___x_2287_);
v___x_2289_ = lean_unsigned_to_nat(4u);
v___x_2290_ = lean_nat_mul(v_size_x27_2286_, v___x_2289_);
v___x_2291_ = lean_unsigned_to_nat(3u);
v___x_2292_ = lean_nat_div(v___x_2290_, v___x_2291_);
lean_dec(v___x_2290_);
v___x_2293_ = lean_array_get_size(v_buckets_x27_2288_);
v___x_2294_ = lean_nat_dec_le(v___x_2292_, v___x_2293_);
lean_dec(v___x_2292_);
if (v___x_2294_ == 0)
{
lean_object* v_val_2295_; lean_object* v___x_2297_; 
v_val_2295_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_2288_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v_val_2295_);
lean_ctor_set(v___x_2268_, 0, v_size_x27_2286_);
v___x_2297_ = v___x_2268_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_size_x27_2286_);
lean_ctor_set(v_reuseFailAlloc_2298_, 1, v_val_2295_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
else
{
lean_object* v___x_2300_; 
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v_buckets_x27_2288_);
lean_ctor_set(v___x_2268_, 0, v_size_x27_2286_);
v___x_2300_ = v___x_2268_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_size_x27_2286_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_buckets_x27_2288_);
v___x_2300_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
return v___x_2300_;
}
}
}
else
{
lean_object* v___x_2302_; lean_object* v_buckets_x27_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2307_; 
lean_inc(v_bkt_2283_);
v___x_2302_ = lean_box(0);
v_buckets_x27_2303_ = lean_array_uset(v_buckets_2266_, v___x_2282_, v___x_2302_);
v___x_2304_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_a_2263_, v_b_2264_, v_bkt_2283_);
v___x_2305_ = lean_array_uset(v_buckets_x27_2303_, v___x_2282_, v___x_2304_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 1, v___x_2305_);
v___x_2307_ = v___x_2268_;
goto v_reusejp_2306_;
}
else
{
lean_object* v_reuseFailAlloc_2308_; 
v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_size_2265_);
lean_ctor_set(v_reuseFailAlloc_2308_, 1, v___x_2305_);
v___x_2307_ = v_reuseFailAlloc_2308_;
goto v_reusejp_2306_;
}
v_reusejp_2306_:
{
return v___x_2307_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(lean_object* v_a_2310_, lean_object* v_e_2311_, lean_object* v_a_2312_){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
v___x_2314_ = lean_st_ref_take(v_a_2310_);
v___x_2315_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___x_2314_, v_e_2311_, v_a_2312_);
v___x_2316_ = lean_st_ref_set(v_a_2310_, v___x_2315_);
v___x_2317_ = lean_box(0);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2318_, lean_object* v_e_2319_, lean_object* v_a_2320_, lean_object* v___y_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(v_a_2318_, v_e_2319_, v_a_2320_);
lean_dec(v_a_2318_);
return v_res_2322_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2324_; lean_object* v_dummy_2325_; 
v___x_2324_ = lean_box(0);
v_dummy_2325_ = l_Lean_Expr_sort___override(v___x_2324_);
return v_dummy_2325_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(lean_object* v_pre_2326_, lean_object* v_post_2327_, size_t v_sz_2328_, size_t v_i_2329_, lean_object* v_bs_2330_, lean_object* v___y_2331_, lean_object* v___y_2332_, lean_object* v___y_2333_){
_start:
{
uint8_t v___x_2335_; 
v___x_2335_ = lean_usize_dec_lt(v_i_2329_, v_sz_2328_);
if (v___x_2335_ == 0)
{
lean_object* v___x_2336_; 
lean_dec_ref(v_post_2327_);
lean_dec_ref(v_pre_2326_);
v___x_2336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2336_, 0, v_bs_2330_);
return v___x_2336_;
}
else
{
lean_object* v_v_2337_; lean_object* v___x_2338_; 
v_v_2337_ = lean_array_uget_borrowed(v_bs_2330_, v_i_2329_);
lean_inc(v_v_2337_);
lean_inc_ref(v_post_2327_);
lean_inc_ref(v_pre_2326_);
v___x_2338_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2326_, v_post_2327_, v_v_2337_, v___y_2331_, v___y_2332_, v___y_2333_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; lean_object* v_bs_x27_2341_; size_t v___x_2342_; size_t v___x_2343_; lean_object* v___x_2344_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref(v___x_2338_);
v___x_2340_ = lean_unsigned_to_nat(0u);
v_bs_x27_2341_ = lean_array_uset(v_bs_2330_, v_i_2329_, v___x_2340_);
v___x_2342_ = ((size_t)1ULL);
v___x_2343_ = lean_usize_add(v_i_2329_, v___x_2342_);
v___x_2344_ = lean_array_uset(v_bs_x27_2341_, v_i_2329_, v_a_2339_);
v_i_2329_ = v___x_2343_;
v_bs_2330_ = v___x_2344_;
goto _start;
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_dec_ref(v_bs_2330_);
lean_dec_ref(v_post_2327_);
lean_dec_ref(v_pre_2326_);
v_a_2346_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___x_2338_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___x_2338_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(lean_object* v_pre_2354_, lean_object* v_post_2355_, lean_object* v_x_2356_, lean_object* v_x_2357_, lean_object* v_x_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
if (lean_obj_tag(v_x_2356_) == 5)
{
lean_object* v_fn_2363_; lean_object* v_arg_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v_fn_2363_ = lean_ctor_get(v_x_2356_, 0);
lean_inc_ref(v_fn_2363_);
v_arg_2364_ = lean_ctor_get(v_x_2356_, 1);
lean_inc_ref(v_arg_2364_);
lean_dec_ref(v_x_2356_);
v___x_2365_ = lean_array_set(v_x_2357_, v_x_2358_, v_arg_2364_);
v___x_2366_ = lean_unsigned_to_nat(1u);
v___x_2367_ = lean_nat_sub(v_x_2358_, v___x_2366_);
lean_dec(v_x_2358_);
v_x_2356_ = v_fn_2363_;
v_x_2357_ = v___x_2365_;
v_x_2358_ = v___x_2367_;
goto _start;
}
else
{
lean_object* v___x_2369_; 
lean_dec(v_x_2358_);
lean_inc_ref(v_post_2355_);
lean_inc_ref(v_pre_2354_);
v___x_2369_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2354_, v_post_2355_, v_x_2356_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_object* v_a_2370_; size_t v_sz_2371_; size_t v___x_2372_; lean_object* v___x_2373_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
lean_inc(v_a_2370_);
lean_dec_ref(v___x_2369_);
v_sz_2371_ = lean_array_size(v_x_2357_);
v___x_2372_ = ((size_t)0ULL);
lean_inc_ref(v_post_2355_);
lean_inc_ref(v_pre_2354_);
v___x_2373_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2354_, v_post_2355_, v_sz_2371_, v___x_2372_, v_x_2357_, v___y_2359_, v___y_2360_, v___y_2361_);
if (lean_obj_tag(v___x_2373_) == 0)
{
lean_object* v_a_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v_a_2374_ = lean_ctor_get(v___x_2373_, 0);
lean_inc(v_a_2374_);
lean_dec_ref(v___x_2373_);
v___x_2375_ = l_Lean_mkAppN(v_a_2370_, v_a_2374_);
lean_dec(v_a_2374_);
v___x_2376_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2354_, v_post_2355_, v___x_2375_, v___y_2359_, v___y_2360_, v___y_2361_);
return v___x_2376_;
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_dec(v_a_2370_);
lean_dec_ref(v_post_2355_);
lean_dec_ref(v_pre_2354_);
v_a_2377_ = lean_ctor_get(v___x_2373_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2373_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2373_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2373_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
else
{
lean_dec_ref(v_x_2357_);
lean_dec_ref(v_post_2355_);
lean_dec_ref(v_pre_2354_);
return v___x_2369_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(lean_object* v___x_2385_, lean_object* v_pre_2386_, lean_object* v_e_2387_, lean_object* v_post_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; uint8_t v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; uint8_t v___y_2401_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; uint8_t v___y_2414_; lean_object* v___y_2415_; uint8_t v___y_2416_; lean_object* v___y_2424_; lean_object* v___y_2425_; uint8_t v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; uint8_t v___y_2429_; lean_object* v___x_2436_; 
v___x_2436_ = l_Lean_Core_checkSystem(v___x_2385_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2436_) == 0)
{
lean_object* v___x_2437_; 
lean_dec_ref(v___x_2436_);
lean_inc_ref(v_pre_2386_);
lean_inc(v___y_2391_);
lean_inc_ref(v___y_2390_);
lean_inc_ref(v_e_2387_);
v___x_2437_ = lean_apply_4(v_pre_2386_, v_e_2387_, v___y_2390_, v___y_2391_, lean_box(0));
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2527_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2440_ = v___x_2437_;
v_isShared_2441_ = v_isSharedCheck_2527_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2437_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2527_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___y_2443_; 
switch(lean_obj_tag(v_a_2438_))
{
case 0:
{
lean_object* v_e_2517_; lean_object* v___x_2519_; 
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_e_2387_);
lean_dec_ref(v_pre_2386_);
v_e_2517_ = lean_ctor_get(v_a_2438_, 0);
lean_inc_ref(v_e_2517_);
lean_dec_ref(v_a_2438_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 0, v_e_2517_);
v___x_2519_ = v___x_2440_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_e_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
case 1:
{
lean_object* v_e_2521_; lean_object* v___x_2522_; 
lean_del_object(v___x_2440_);
lean_dec_ref(v_e_2387_);
v_e_2521_ = lean_ctor_get(v_a_2438_, 0);
lean_inc_ref(v_e_2521_);
lean_dec_ref(v_a_2438_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2522_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_e_2521_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2522_) == 0)
{
lean_object* v_a_2523_; lean_object* v___x_2524_; 
v_a_2523_ = lean_ctor_get(v___x_2522_, 0);
lean_inc(v_a_2523_);
lean_dec_ref(v___x_2522_);
v___x_2524_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v_a_2523_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2524_;
}
else
{
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2522_;
}
}
default: 
{
lean_object* v_e_x3f_2525_; 
lean_del_object(v___x_2440_);
v_e_x3f_2525_ = lean_ctor_get(v_a_2438_, 0);
lean_inc(v_e_x3f_2525_);
lean_dec_ref(v_a_2438_);
if (lean_obj_tag(v_e_x3f_2525_) == 0)
{
v___y_2443_ = v_e_2387_;
goto v___jp_2442_;
}
else
{
lean_object* v_val_2526_; 
lean_dec_ref(v_e_2387_);
v_val_2526_ = lean_ctor_get(v_e_x3f_2525_, 0);
lean_inc(v_val_2526_);
lean_dec_ref(v_e_x3f_2525_);
v___y_2443_ = v_val_2526_;
goto v___jp_2442_;
}
}
}
v___jp_2442_:
{
switch(lean_obj_tag(v___y_2443_))
{
case 7:
{
lean_object* v_binderName_2444_; lean_object* v_binderType_2445_; lean_object* v_body_2446_; uint8_t v_binderInfo_2447_; lean_object* v___x_2448_; 
v_binderName_2444_ = lean_ctor_get(v___y_2443_, 0);
lean_inc(v_binderName_2444_);
v_binderType_2445_ = lean_ctor_get(v___y_2443_, 1);
v_body_2446_ = lean_ctor_get(v___y_2443_, 2);
v_binderInfo_2447_ = lean_ctor_get_uint8(v___y_2443_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2445_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2448_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_binderType_2445_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v___x_2450_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref(v___x_2448_);
lean_inc_ref(v_body_2446_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2450_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_body_2446_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; size_t v___x_2452_; size_t v___x_2453_; uint8_t v___x_2454_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref(v___x_2450_);
v___x_2452_ = lean_ptr_addr(v_binderType_2445_);
v___x_2453_ = lean_ptr_addr(v_a_2449_);
v___x_2454_ = lean_usize_dec_eq(v___x_2452_, v___x_2453_);
if (v___x_2454_ == 0)
{
v___y_2424_ = v_a_2451_;
v___y_2425_ = v_binderName_2444_;
v___y_2426_ = v_binderInfo_2447_;
v___y_2427_ = v___y_2443_;
v___y_2428_ = v_a_2449_;
v___y_2429_ = v___x_2454_;
goto v___jp_2423_;
}
else
{
size_t v___x_2455_; size_t v___x_2456_; uint8_t v___x_2457_; 
v___x_2455_ = lean_ptr_addr(v_body_2446_);
v___x_2456_ = lean_ptr_addr(v_a_2451_);
v___x_2457_ = lean_usize_dec_eq(v___x_2455_, v___x_2456_);
v___y_2424_ = v_a_2451_;
v___y_2425_ = v_binderName_2444_;
v___y_2426_ = v_binderInfo_2447_;
v___y_2427_ = v___y_2443_;
v___y_2428_ = v_a_2449_;
v___y_2429_ = v___x_2457_;
goto v___jp_2423_;
}
}
else
{
lean_dec(v_a_2449_);
lean_dec_ref(v___y_2443_);
lean_dec(v_binderName_2444_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2450_;
}
}
else
{
lean_dec(v_binderName_2444_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2448_;
}
}
case 6:
{
lean_object* v_binderName_2458_; lean_object* v_binderType_2459_; lean_object* v_body_2460_; uint8_t v_binderInfo_2461_; lean_object* v___x_2462_; 
v_binderName_2458_ = lean_ctor_get(v___y_2443_, 0);
lean_inc(v_binderName_2458_);
v_binderType_2459_ = lean_ctor_get(v___y_2443_, 1);
v_body_2460_ = lean_ctor_get(v___y_2443_, 2);
v_binderInfo_2461_ = lean_ctor_get_uint8(v___y_2443_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2459_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2462_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_binderType_2459_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2462_);
lean_inc_ref(v_body_2460_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2464_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_body_2460_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; size_t v___x_2466_; size_t v___x_2467_; uint8_t v___x_2468_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref(v___x_2464_);
v___x_2466_ = lean_ptr_addr(v_binderType_2459_);
v___x_2467_ = lean_ptr_addr(v_a_2463_);
v___x_2468_ = lean_usize_dec_eq(v___x_2466_, v___x_2467_);
if (v___x_2468_ == 0)
{
v___y_2411_ = v_a_2463_;
v___y_2412_ = v_binderName_2458_;
v___y_2413_ = v___y_2443_;
v___y_2414_ = v_binderInfo_2461_;
v___y_2415_ = v_a_2465_;
v___y_2416_ = v___x_2468_;
goto v___jp_2410_;
}
else
{
size_t v___x_2469_; size_t v___x_2470_; uint8_t v___x_2471_; 
v___x_2469_ = lean_ptr_addr(v_body_2460_);
v___x_2470_ = lean_ptr_addr(v_a_2465_);
v___x_2471_ = lean_usize_dec_eq(v___x_2469_, v___x_2470_);
v___y_2411_ = v_a_2463_;
v___y_2412_ = v_binderName_2458_;
v___y_2413_ = v___y_2443_;
v___y_2414_ = v_binderInfo_2461_;
v___y_2415_ = v_a_2465_;
v___y_2416_ = v___x_2471_;
goto v___jp_2410_;
}
}
else
{
lean_dec(v_a_2463_);
lean_dec_ref(v___y_2443_);
lean_dec(v_binderName_2458_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2464_;
}
}
else
{
lean_dec_ref(v___y_2443_);
lean_dec(v_binderName_2458_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2462_;
}
}
case 8:
{
lean_object* v_declName_2472_; lean_object* v_type_2473_; lean_object* v_value_2474_; lean_object* v_body_2475_; uint8_t v_nondep_2476_; lean_object* v___x_2477_; 
v_declName_2472_ = lean_ctor_get(v___y_2443_, 0);
lean_inc(v_declName_2472_);
v_type_2473_ = lean_ctor_get(v___y_2443_, 1);
v_value_2474_ = lean_ctor_get(v___y_2443_, 2);
v_body_2475_ = lean_ctor_get(v___y_2443_, 3);
lean_inc_ref(v_body_2475_);
v_nondep_2476_ = lean_ctor_get_uint8(v___y_2443_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2473_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2477_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_type_2473_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; lean_object* v___x_2479_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2477_);
lean_inc_ref(v_value_2474_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2479_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_value_2474_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2479_) == 0)
{
lean_object* v_a_2480_; lean_object* v___x_2481_; 
v_a_2480_ = lean_ctor_get(v___x_2479_, 0);
lean_inc(v_a_2480_);
lean_dec_ref(v___x_2479_);
lean_inc_ref(v_body_2475_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2481_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_body_2475_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; size_t v___x_2483_; size_t v___x_2484_; uint8_t v___x_2485_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref(v___x_2481_);
v___x_2483_ = lean_ptr_addr(v_type_2473_);
v___x_2484_ = lean_ptr_addr(v_a_2478_);
v___x_2485_ = lean_usize_dec_eq(v___x_2483_, v___x_2484_);
if (v___x_2485_ == 0)
{
v___y_2394_ = v_a_2478_;
v___y_2395_ = v_a_2480_;
v___y_2396_ = v_a_2482_;
v___y_2397_ = v___y_2443_;
v___y_2398_ = v_nondep_2476_;
v___y_2399_ = v_body_2475_;
v___y_2400_ = v_declName_2472_;
v___y_2401_ = v___x_2485_;
goto v___jp_2393_;
}
else
{
size_t v___x_2486_; size_t v___x_2487_; uint8_t v___x_2488_; 
v___x_2486_ = lean_ptr_addr(v_value_2474_);
v___x_2487_ = lean_ptr_addr(v_a_2480_);
v___x_2488_ = lean_usize_dec_eq(v___x_2486_, v___x_2487_);
v___y_2394_ = v_a_2478_;
v___y_2395_ = v_a_2480_;
v___y_2396_ = v_a_2482_;
v___y_2397_ = v___y_2443_;
v___y_2398_ = v_nondep_2476_;
v___y_2399_ = v_body_2475_;
v___y_2400_ = v_declName_2472_;
v___y_2401_ = v___x_2488_;
goto v___jp_2393_;
}
}
else
{
lean_dec(v_a_2480_);
lean_dec(v_a_2478_);
lean_dec_ref(v_body_2475_);
lean_dec(v_declName_2472_);
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2481_;
}
}
else
{
lean_dec(v_a_2478_);
lean_dec_ref(v_body_2475_);
lean_dec_ref(v___y_2443_);
lean_dec(v_declName_2472_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2479_;
}
}
else
{
lean_dec_ref(v_body_2475_);
lean_dec_ref(v___y_2443_);
lean_dec(v_declName_2472_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2477_;
}
}
case 5:
{
lean_object* v_dummy_2489_; lean_object* v_nargs_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
v_dummy_2489_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_2490_ = l_Lean_Expr_getAppNumArgs(v___y_2443_);
lean_inc(v_nargs_2490_);
v___x_2491_ = lean_mk_array(v_nargs_2490_, v_dummy_2489_);
v___x_2492_ = lean_unsigned_to_nat(1u);
v___x_2493_ = lean_nat_sub(v_nargs_2490_, v___x_2492_);
lean_dec(v_nargs_2490_);
v___x_2494_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2386_, v_post_2388_, v___y_2443_, v___x_2491_, v___x_2493_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2494_;
}
case 10:
{
lean_object* v_data_2495_; lean_object* v_expr_2496_; lean_object* v___x_2497_; 
v_data_2495_ = lean_ctor_get(v___y_2443_, 0);
v_expr_2496_ = lean_ctor_get(v___y_2443_, 1);
lean_inc_ref(v_expr_2496_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2497_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_expr_2496_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; size_t v___x_2499_; size_t v___x_2500_; uint8_t v___x_2501_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref(v___x_2497_);
v___x_2499_ = lean_ptr_addr(v_expr_2496_);
v___x_2500_ = lean_ptr_addr(v_a_2498_);
v___x_2501_ = lean_usize_dec_eq(v___x_2499_, v___x_2500_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; lean_object* v___x_2503_; 
lean_inc(v_data_2495_);
lean_dec_ref(v___y_2443_);
v___x_2502_ = l_Lean_Expr_mdata___override(v_data_2495_, v_a_2498_);
v___x_2503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2502_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2503_;
}
else
{
lean_object* v___x_2504_; 
lean_dec(v_a_2498_);
v___x_2504_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2443_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2504_;
}
}
else
{
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2497_;
}
}
case 11:
{
lean_object* v_typeName_2505_; lean_object* v_idx_2506_; lean_object* v_struct_2507_; lean_object* v___x_2508_; 
v_typeName_2505_ = lean_ctor_get(v___y_2443_, 0);
v_idx_2506_ = lean_ctor_get(v___y_2443_, 1);
v_struct_2507_ = lean_ctor_get(v___y_2443_, 2);
lean_inc_ref(v_struct_2507_);
lean_inc_ref(v_post_2388_);
lean_inc_ref(v_pre_2386_);
v___x_2508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2386_, v_post_2388_, v_struct_2507_, v___y_2389_, v___y_2390_, v___y_2391_);
if (lean_obj_tag(v___x_2508_) == 0)
{
lean_object* v_a_2509_; size_t v___x_2510_; size_t v___x_2511_; uint8_t v___x_2512_; 
v_a_2509_ = lean_ctor_get(v___x_2508_, 0);
lean_inc(v_a_2509_);
lean_dec_ref(v___x_2508_);
v___x_2510_ = lean_ptr_addr(v_struct_2507_);
v___x_2511_ = lean_ptr_addr(v_a_2509_);
v___x_2512_ = lean_usize_dec_eq(v___x_2510_, v___x_2511_);
if (v___x_2512_ == 0)
{
lean_object* v___x_2513_; lean_object* v___x_2514_; 
lean_inc(v_idx_2506_);
lean_inc(v_typeName_2505_);
lean_dec_ref(v___y_2443_);
v___x_2513_ = l_Lean_Expr_proj___override(v_typeName_2505_, v_idx_2506_, v_a_2509_);
v___x_2514_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2513_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2514_;
}
else
{
lean_object* v___x_2515_; 
lean_dec(v_a_2509_);
v___x_2515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2443_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2515_;
}
}
else
{
lean_dec_ref(v___y_2443_);
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_pre_2386_);
return v___x_2508_;
}
}
default: 
{
lean_object* v___x_2516_; 
v___x_2516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2443_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2516_;
}
}
}
}
}
else
{
lean_object* v_a_2528_; lean_object* v___x_2530_; uint8_t v_isShared_2531_; uint8_t v_isSharedCheck_2535_; 
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_e_2387_);
lean_dec_ref(v_pre_2386_);
v_a_2528_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2535_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2535_ == 0)
{
v___x_2530_ = v___x_2437_;
v_isShared_2531_ = v_isSharedCheck_2535_;
goto v_resetjp_2529_;
}
else
{
lean_inc(v_a_2528_);
lean_dec(v___x_2437_);
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
else
{
lean_object* v_a_2536_; lean_object* v___x_2538_; uint8_t v_isShared_2539_; uint8_t v_isSharedCheck_2543_; 
lean_dec_ref(v_post_2388_);
lean_dec_ref(v_e_2387_);
lean_dec_ref(v_pre_2386_);
v_a_2536_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2538_ = v___x_2436_;
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
else
{
lean_inc(v_a_2536_);
lean_dec(v___x_2436_);
v___x_2538_ = lean_box(0);
v_isShared_2539_ = v_isSharedCheck_2543_;
goto v_resetjp_2537_;
}
v_resetjp_2537_:
{
lean_object* v___x_2541_; 
if (v_isShared_2539_ == 0)
{
v___x_2541_ = v___x_2538_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v_a_2536_);
v___x_2541_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
return v___x_2541_;
}
}
}
v___jp_2393_:
{
if (v___y_2401_ == 0)
{
lean_object* v___x_2402_; lean_object* v___x_2403_; 
lean_dec_ref(v___y_2399_);
lean_dec_ref(v___y_2397_);
v___x_2402_ = l_Lean_Expr_letE___override(v___y_2400_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2398_);
v___x_2403_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2402_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2403_;
}
else
{
size_t v___x_2404_; size_t v___x_2405_; uint8_t v___x_2406_; 
v___x_2404_ = lean_ptr_addr(v___y_2399_);
lean_dec_ref(v___y_2399_);
v___x_2405_ = lean_ptr_addr(v___y_2396_);
v___x_2406_ = lean_usize_dec_eq(v___x_2404_, v___x_2405_);
if (v___x_2406_ == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
lean_dec_ref(v___y_2397_);
v___x_2407_ = l_Lean_Expr_letE___override(v___y_2400_, v___y_2394_, v___y_2395_, v___y_2396_, v___y_2398_);
v___x_2408_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2407_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2408_;
}
else
{
lean_object* v___x_2409_; 
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec_ref(v___y_2394_);
v___x_2409_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2397_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2409_;
}
}
}
v___jp_2410_:
{
if (v___y_2416_ == 0)
{
lean_object* v___x_2417_; lean_object* v___x_2418_; 
lean_dec_ref(v___y_2413_);
v___x_2417_ = l_Lean_Expr_lam___override(v___y_2412_, v___y_2411_, v___y_2415_, v___y_2414_);
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
lean_dec_ref(v___y_2413_);
v___x_2420_ = l_Lean_Expr_lam___override(v___y_2412_, v___y_2411_, v___y_2415_, v___y_2414_);
v___x_2421_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2420_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2421_;
}
else
{
lean_object* v___x_2422_; 
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
v___x_2422_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2413_, v___y_2389_, v___y_2390_, v___y_2391_);
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
v___x_2430_ = l_Lean_Expr_forallE___override(v___y_2425_, v___y_2428_, v___y_2424_, v___y_2426_);
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
v___x_2433_ = l_Lean_Expr_forallE___override(v___y_2425_, v___y_2428_, v___y_2424_, v___y_2426_);
v___x_2434_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___x_2433_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2434_;
}
else
{
lean_object* v___x_2435_; 
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
v___x_2435_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2386_, v_post_2388_, v___y_2427_, v___y_2389_, v___y_2390_, v___y_2391_);
return v___x_2435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed(lean_object* v___x_2544_, lean_object* v_pre_2545_, lean_object* v_e_2546_, lean_object* v_post_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_){
_start:
{
lean_object* v_res_2552_; 
v_res_2552_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(v___x_2544_, v_pre_2545_, v_e_2546_, v_post_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v___y_2548_);
return v_res_2552_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(lean_object* v_pre_2553_, lean_object* v_post_2554_, lean_object* v_e_2555_, lean_object* v_a_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; 
lean_inc(v_a_2556_);
v___x_2560_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2560_, 0, lean_box(0));
lean_closure_set(v___x_2560_, 1, lean_box(0));
lean_closure_set(v___x_2560_, 2, v_a_2556_);
v___x_2561_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___x_2560_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2593_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2564_ = v___x_2561_;
v_isShared_2565_ = v_isSharedCheck_2593_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2561_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2593_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2566_; 
v___x_2566_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_2562_, v_e_2555_);
lean_dec(v_a_2562_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; lean_object* v___f_2568_; lean_object* v___x_2569_; 
lean_del_object(v___x_2564_);
v___x_2567_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_2555_);
v___f_2568_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed), 8, 4);
lean_closure_set(v___f_2568_, 0, v___x_2567_);
lean_closure_set(v___f_2568_, 1, v_pre_2553_);
lean_closure_set(v___f_2568_, 2, v_e_2555_);
lean_closure_set(v___f_2568_, 3, v_post_2554_);
v___x_2569_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v___f_2568_, v_a_2556_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___f_2571_; lean_object* v___x_2572_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc_n(v_a_2570_, 2);
lean_dec_ref(v___x_2569_);
lean_inc(v_a_2556_);
v___f_2571_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2571_, 0, v_a_2556_);
lean_closure_set(v___f_2571_, 1, v_e_2555_);
lean_closure_set(v___f_2571_, 2, v_a_2570_);
v___x_2572_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___f_2571_, v___y_2557_, v___y_2558_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2579_; 
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2579_ == 0)
{
lean_object* v_unused_2580_; 
v_unused_2580_ = lean_ctor_get(v___x_2572_, 0);
lean_dec(v_unused_2580_);
v___x_2574_ = v___x_2572_;
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
else
{
lean_dec(v___x_2572_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2579_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v___x_2577_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v_a_2570_);
v___x_2577_ = v___x_2574_;
goto v_reusejp_2576_;
}
else
{
lean_object* v_reuseFailAlloc_2578_; 
v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2570_);
v___x_2577_ = v_reuseFailAlloc_2578_;
goto v_reusejp_2576_;
}
v_reusejp_2576_:
{
return v___x_2577_;
}
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_dec(v_a_2570_);
v_a_2581_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2572_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2572_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
else
{
lean_dec_ref(v_e_2555_);
return v___x_2569_;
}
}
else
{
lean_object* v_val_2589_; lean_object* v___x_2591_; 
lean_dec_ref(v_e_2555_);
lean_dec_ref(v_post_2554_);
lean_dec_ref(v_pre_2553_);
v_val_2589_ = lean_ctor_get(v___x_2566_, 0);
lean_inc(v_val_2589_);
lean_dec_ref(v___x_2566_);
if (v_isShared_2565_ == 0)
{
lean_ctor_set(v___x_2564_, 0, v_val_2589_);
v___x_2591_ = v___x_2564_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_val_2589_);
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
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec_ref(v_e_2555_);
lean_dec_ref(v_post_2554_);
lean_dec_ref(v_pre_2553_);
v_a_2594_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2561_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2561_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v___x_2599_; 
if (v_isShared_2597_ == 0)
{
v___x_2599_ = v___x_2596_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_a_2594_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(lean_object* v_pre_2602_, lean_object* v_post_2603_, lean_object* v_e_2604_, lean_object* v_a_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
lean_object* v___x_2609_; 
lean_inc_ref(v_post_2603_);
lean_inc(v___y_2607_);
lean_inc_ref(v___y_2606_);
lean_inc_ref(v_e_2604_);
v___x_2609_ = lean_apply_4(v_post_2603_, v_e_2604_, v___y_2606_, v___y_2607_, lean_box(0));
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2628_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2612_ = v___x_2609_;
v_isShared_2613_ = v_isSharedCheck_2628_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2609_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2628_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
switch(lean_obj_tag(v_a_2610_))
{
case 0:
{
lean_object* v_e_2614_; lean_object* v___x_2616_; 
lean_dec_ref(v_e_2604_);
lean_dec_ref(v_post_2603_);
lean_dec_ref(v_pre_2602_);
v_e_2614_ = lean_ctor_get(v_a_2610_, 0);
lean_inc_ref(v_e_2614_);
lean_dec_ref(v_a_2610_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v_e_2614_);
v___x_2616_ = v___x_2612_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_e_2614_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
case 1:
{
lean_object* v_e_2618_; lean_object* v___x_2619_; 
lean_del_object(v___x_2612_);
lean_dec_ref(v_e_2604_);
v_e_2618_ = lean_ctor_get(v_a_2610_, 0);
lean_inc_ref(v_e_2618_);
lean_dec_ref(v_a_2610_);
v___x_2619_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2602_, v_post_2603_, v_e_2618_, v_a_2605_, v___y_2606_, v___y_2607_);
return v___x_2619_;
}
default: 
{
lean_object* v_e_x3f_2620_; 
lean_dec_ref(v_post_2603_);
lean_dec_ref(v_pre_2602_);
v_e_x3f_2620_ = lean_ctor_get(v_a_2610_, 0);
lean_inc(v_e_x3f_2620_);
lean_dec_ref(v_a_2610_);
if (lean_obj_tag(v_e_x3f_2620_) == 0)
{
lean_object* v___x_2622_; 
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v_e_2604_);
v___x_2622_ = v___x_2612_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_e_2604_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
else
{
lean_object* v_val_2624_; lean_object* v___x_2626_; 
lean_dec_ref(v_e_2604_);
v_val_2624_ = lean_ctor_get(v_e_x3f_2620_, 0);
lean_inc(v_val_2624_);
lean_dec_ref(v_e_x3f_2620_);
if (v_isShared_2613_ == 0)
{
lean_ctor_set(v___x_2612_, 0, v_val_2624_);
v___x_2626_ = v___x_2612_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_val_2624_);
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
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec_ref(v_e_2604_);
lean_dec_ref(v_post_2603_);
lean_dec_ref(v_pre_2602_);
v_a_2629_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2609_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2609_);
v___x_2631_ = lean_box(0);
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
v_resetjp_2630_:
{
lean_object* v___x_2634_; 
if (v_isShared_2632_ == 0)
{
v___x_2634_ = v___x_2631_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_a_2629_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
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
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(lean_object* v_input_2683_, lean_object* v_pre_2684_, lean_object* v_post_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_){
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
lean_dec_ref(v___x_2692_);
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
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___boxed(lean_object* v_input_2704_, lean_object* v_pre_2705_, lean_object* v_post_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v_res_2710_; 
v_res_2710_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_input_2704_, v_pre_2705_, v_post_2706_, v___y_2707_, v___y_2708_);
lean_dec(v___y_2708_);
lean_dec_ref(v___y_2707_);
return v_res_2710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object* v_e_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_){
_start:
{
lean_object* v___f_2718_; lean_object* v___x_2719_; 
v___f_2718_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0));
v___x_2719_ = lean_find_expr(v___f_2718_, v_e_2714_);
if (lean_obj_tag(v___x_2719_) == 0)
{
lean_object* v___x_2720_; 
v___x_2720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2720_, 0, v_e_2714_);
return v___x_2720_;
}
else
{
lean_object* v_pre_2721_; lean_object* v___f_2722_; lean_object* v___x_2723_; 
lean_dec_ref(v___x_2719_);
v_pre_2721_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1));
v___f_2722_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2));
v___x_2723_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_e_2714_, v_pre_2721_, v___f_2722_, v_a_2715_, v_a_2716_);
return v___x_2723_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___boxed(lean_object* v_e_2724_, lean_object* v_a_2725_, lean_object* v_a_2726_, lean_object* v_a_2727_){
_start:
{
lean_object* v_res_2728_; 
v_res_2728_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_2724_, v_a_2725_, v_a_2726_);
lean_dec(v_a_2726_);
lean_dec_ref(v_a_2725_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2729_, lean_object* v_m_2730_, lean_object* v_a_2731_){
_start:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2730_, v_a_2731_);
return v___x_2732_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2733_, lean_object* v_m_2734_, lean_object* v_a_2735_){
_start:
{
lean_object* v_res_2736_; 
v_res_2736_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(v_00_u03b2_2733_, v_m_2734_, v_a_2735_);
lean_dec_ref(v_a_2735_);
lean_dec_ref(v_m_2734_);
return v_res_2736_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_2737_, lean_object* v_ref_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_){
_start:
{
lean_object* v___x_2742_; 
v___x_2742_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2738_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2743_, lean_object* v_ref_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_){
_start:
{
lean_object* v_res_2748_; 
v_res_2748_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_2743_, v_ref_2744_, v___y_2745_, v___y_2746_);
lean_dec(v___y_2746_);
lean_dec_ref(v___y_2745_);
return v_res_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_2749_, lean_object* v_x_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_){
_start:
{
lean_object* v___x_2755_; 
v___x_2755_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2750_, v___y_2751_, v___y_2752_, v___y_2753_);
return v___x_2755_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2756_, lean_object* v_x_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(v_00_u03b1_2756_, v_x_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_2763_, lean_object* v_m_2764_, lean_object* v_a_2765_, lean_object* v_b_2766_){
_start:
{
lean_object* v___x_2767_; 
v___x_2767_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_2764_, v_a_2765_, v_b_2766_);
return v___x_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_2768_, lean_object* v_a_2769_, lean_object* v_x_2770_){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2769_, v_x_2770_);
return v___x_2771_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2772_, lean_object* v_a_2773_, lean_object* v_x_2774_){
_start:
{
lean_object* v_res_2775_; 
v_res_2775_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_2772_, v_a_2773_, v_x_2774_);
lean_dec(v_x_2774_);
lean_dec_ref(v_a_2773_);
return v_res_2775_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_2776_, lean_object* v_a_2777_, lean_object* v_x_2778_){
_start:
{
uint8_t v___x_2779_; 
v___x_2779_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(v_a_2777_, v_x_2778_);
return v___x_2779_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_2780_, lean_object* v_a_2781_, lean_object* v_x_2782_){
_start:
{
uint8_t v_res_2783_; lean_object* v_r_2784_; 
v_res_2783_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_2780_, v_a_2781_, v_x_2782_);
lean_dec(v_x_2782_);
lean_dec_ref(v_a_2781_);
v_r_2784_ = lean_box(v_res_2783_);
return v_r_2784_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_2785_, lean_object* v_data_2786_){
_start:
{
lean_object* v___x_2787_; 
v___x_2787_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_data_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_2788_, lean_object* v_a_2789_, lean_object* v_b_2790_, lean_object* v_x_2791_){
_start:
{
lean_object* v___x_2792_; 
v___x_2792_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_a_2789_, v_b_2790_, v_x_2791_);
return v___x_2792_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_2793_, lean_object* v_i_2794_, lean_object* v_source_2795_, lean_object* v_target_2796_){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_2794_, v_source_2795_, v_target_2796_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_2798_, lean_object* v_x_2799_, lean_object* v_x_2800_){
_start:
{
lean_object* v___x_2801_; 
v___x_2801_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_2799_, v_x_2800_);
return v___x_2801_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0_spec__0(lean_object* v_msgData_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_){
_start:
{
lean_object* v___x_2808_; lean_object* v_env_2809_; lean_object* v___x_2810_; lean_object* v_mctx_2811_; lean_object* v_lctx_2812_; lean_object* v_options_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2808_ = lean_st_ref_get(v___y_2806_);
v_env_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc_ref(v_env_2809_);
lean_dec(v___x_2808_);
v___x_2810_ = lean_st_ref_get(v___y_2804_);
v_mctx_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc_ref(v_mctx_2811_);
lean_dec(v___x_2810_);
v_lctx_2812_ = lean_ctor_get(v___y_2803_, 2);
v_options_2813_ = lean_ctor_get(v___y_2805_, 2);
lean_inc_ref(v_options_2813_);
lean_inc_ref(v_lctx_2812_);
v___x_2814_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2814_, 0, v_env_2809_);
lean_ctor_set(v___x_2814_, 1, v_mctx_2811_);
lean_ctor_set(v___x_2814_, 2, v_lctx_2812_);
lean_ctor_set(v___x_2814_, 3, v_options_2813_);
v___x_2815_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2815_, 0, v___x_2814_);
lean_ctor_set(v___x_2815_, 1, v_msgData_2802_);
v___x_2816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
return v___x_2816_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_2817_, lean_object* v___y_2818_, lean_object* v___y_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_){
_start:
{
lean_object* v_res_2823_; 
v_res_2823_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0_spec__0(v_msgData_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2821_);
lean_dec_ref(v___y_2820_);
lean_dec(v___y_2819_);
lean_dec_ref(v___y_2818_);
return v_res_2823_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2824_; double v___x_2825_; 
v___x_2824_ = lean_unsigned_to_nat(0u);
v___x_2825_ = lean_float_of_nat(v___x_2824_);
return v___x_2825_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0(lean_object* v_cls_2829_, lean_object* v_msg_2830_, lean_object* v___y_2831_, lean_object* v___y_2832_, lean_object* v___y_2833_, lean_object* v___y_2834_){
_start:
{
lean_object* v_ref_2836_; lean_object* v___x_2837_; lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2882_; 
v_ref_2836_ = lean_ctor_get(v___y_2833_, 5);
v___x_2837_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0_spec__0(v_msg_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_);
v_a_2838_ = lean_ctor_get(v___x_2837_, 0);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2882_ == 0)
{
v___x_2840_ = v___x_2837_;
v_isShared_2841_ = v_isSharedCheck_2882_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2837_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2882_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v_traceState_2843_; lean_object* v_env_2844_; lean_object* v_nextMacroScope_2845_; lean_object* v_ngen_2846_; lean_object* v_auxDeclNGen_2847_; lean_object* v_cache_2848_; lean_object* v_messages_2849_; lean_object* v_infoState_2850_; lean_object* v_snapshotTasks_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2881_; 
v___x_2842_ = lean_st_ref_take(v___y_2834_);
v_traceState_2843_ = lean_ctor_get(v___x_2842_, 4);
v_env_2844_ = lean_ctor_get(v___x_2842_, 0);
v_nextMacroScope_2845_ = lean_ctor_get(v___x_2842_, 1);
v_ngen_2846_ = lean_ctor_get(v___x_2842_, 2);
v_auxDeclNGen_2847_ = lean_ctor_get(v___x_2842_, 3);
v_cache_2848_ = lean_ctor_get(v___x_2842_, 5);
v_messages_2849_ = lean_ctor_get(v___x_2842_, 6);
v_infoState_2850_ = lean_ctor_get(v___x_2842_, 7);
v_snapshotTasks_2851_ = lean_ctor_get(v___x_2842_, 8);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2853_ = v___x_2842_;
v_isShared_2854_ = v_isSharedCheck_2881_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_snapshotTasks_2851_);
lean_inc(v_infoState_2850_);
lean_inc(v_messages_2849_);
lean_inc(v_cache_2848_);
lean_inc(v_traceState_2843_);
lean_inc(v_auxDeclNGen_2847_);
lean_inc(v_ngen_2846_);
lean_inc(v_nextMacroScope_2845_);
lean_inc(v_env_2844_);
lean_dec(v___x_2842_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2881_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
uint64_t v_tid_2855_; lean_object* v_traces_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2880_; 
v_tid_2855_ = lean_ctor_get_uint64(v_traceState_2843_, sizeof(void*)*1);
v_traces_2856_ = lean_ctor_get(v_traceState_2843_, 0);
v_isSharedCheck_2880_ = !lean_is_exclusive(v_traceState_2843_);
if (v_isSharedCheck_2880_ == 0)
{
v___x_2858_ = v_traceState_2843_;
v_isShared_2859_ = v_isSharedCheck_2880_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_traces_2856_);
lean_dec(v_traceState_2843_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2880_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2860_; double v___x_2861_; uint8_t v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2870_; 
v___x_2860_ = lean_box(0);
v___x_2861_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__0);
v___x_2862_ = 0;
v___x_2863_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__1));
v___x_2864_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2864_, 0, v_cls_2829_);
lean_ctor_set(v___x_2864_, 1, v___x_2860_);
lean_ctor_set(v___x_2864_, 2, v___x_2863_);
lean_ctor_set_float(v___x_2864_, sizeof(void*)*3, v___x_2861_);
lean_ctor_set_float(v___x_2864_, sizeof(void*)*3 + 8, v___x_2861_);
lean_ctor_set_uint8(v___x_2864_, sizeof(void*)*3 + 16, v___x_2862_);
v___x_2865_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__2));
v___x_2866_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2864_);
lean_ctor_set(v___x_2866_, 1, v_a_2838_);
lean_ctor_set(v___x_2866_, 2, v___x_2865_);
lean_inc(v_ref_2836_);
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v_ref_2836_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = l_Lean_PersistentArray_push___redArg(v_traces_2856_, v___x_2867_);
if (v_isShared_2859_ == 0)
{
lean_ctor_set(v___x_2858_, 0, v___x_2868_);
v___x_2870_ = v___x_2858_;
goto v_reusejp_2869_;
}
else
{
lean_object* v_reuseFailAlloc_2879_; 
v_reuseFailAlloc_2879_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2879_, 0, v___x_2868_);
lean_ctor_set_uint64(v_reuseFailAlloc_2879_, sizeof(void*)*1, v_tid_2855_);
v___x_2870_ = v_reuseFailAlloc_2879_;
goto v_reusejp_2869_;
}
v_reusejp_2869_:
{
lean_object* v___x_2872_; 
if (v_isShared_2854_ == 0)
{
lean_ctor_set(v___x_2853_, 4, v___x_2870_);
v___x_2872_ = v___x_2853_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_env_2844_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_nextMacroScope_2845_);
lean_ctor_set(v_reuseFailAlloc_2878_, 2, v_ngen_2846_);
lean_ctor_set(v_reuseFailAlloc_2878_, 3, v_auxDeclNGen_2847_);
lean_ctor_set(v_reuseFailAlloc_2878_, 4, v___x_2870_);
lean_ctor_set(v_reuseFailAlloc_2878_, 5, v_cache_2848_);
lean_ctor_set(v_reuseFailAlloc_2878_, 6, v_messages_2849_);
lean_ctor_set(v_reuseFailAlloc_2878_, 7, v_infoState_2850_);
lean_ctor_set(v_reuseFailAlloc_2878_, 8, v_snapshotTasks_2851_);
v___x_2872_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2876_; 
v___x_2873_ = lean_st_ref_set(v___y_2834_, v___x_2872_);
v___x_2874_ = lean_box(0);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 0, v___x_2874_);
v___x_2876_ = v___x_2840_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v___x_2874_);
v___x_2876_ = v_reuseFailAlloc_2877_;
goto v_reusejp_2875_;
}
v_reusejp_2875_:
{
return v___x_2876_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___boxed(lean_object* v_cls_2883_, lean_object* v_msg_2884_, lean_object* v___y_2885_, lean_object* v___y_2886_, lean_object* v___y_2887_, lean_object* v___y_2888_, lean_object* v___y_2889_){
_start:
{
lean_object* v_res_2890_; 
v_res_2890_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0(v_cls_2883_, v_msg_2884_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_);
lean_dec(v___y_2888_);
lean_dec_ref(v___y_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
return v_res_2890_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2899_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__2));
v___x_2900_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__4));
v___x_2901_ = l_Lean_Name_append(v___x_2900_, v___x_2899_);
return v___x_2901_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2903_; lean_object* v___x_2904_; 
v___x_2903_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__6));
v___x_2904_ = l_Lean_stringToMessageData(v___x_2903_);
return v___x_2904_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__8));
v___x_2907_ = l_Lean_stringToMessageData(v___x_2906_);
return v___x_2907_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__10(void){
_start:
{
uint8_t v___x_2908_; uint64_t v___x_2909_; 
v___x_2908_ = 1;
v___x_2909_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2908_);
return v___x_2909_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2911_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__11));
v___x_2912_ = l_Lean_stringToMessageData(v___x_2911_);
return v___x_2912_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__14(void){
_start:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
v___x_2914_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__13));
v___x_2915_ = l_Lean_stringToMessageData(v___x_2914_);
return v___x_2915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0(lean_object* v_e_2916_, lean_object* v___y_2917_, lean_object* v___y_2918_, lean_object* v___y_2919_, lean_object* v___y_2920_){
_start:
{
if (lean_obj_tag(v_e_2916_) == 11)
{
lean_object* v_typeName_2928_; lean_object* v_idx_2929_; lean_object* v_struct_2930_; lean_object* v___x_2931_; lean_object* v_env_2932_; lean_object* v___x_2933_; 
v_typeName_2928_ = lean_ctor_get(v_e_2916_, 0);
v_idx_2929_ = lean_ctor_get(v_e_2916_, 1);
v_struct_2930_ = lean_ctor_get(v_e_2916_, 2);
v___x_2931_ = lean_st_ref_get(v___y_2920_);
v_env_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc_ref(v_env_2932_);
lean_dec(v___x_2931_);
lean_inc(v_typeName_2928_);
v___x_2933_ = l_Lean_getStructureInfo_x3f(v_env_2932_, v_typeName_2928_);
if (lean_obj_tag(v___x_2933_) == 1)
{
lean_object* v_val_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_3033_; 
v_val_2934_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_2936_ = v___x_2933_;
v_isShared_2937_ = v_isSharedCheck_3033_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_val_2934_);
lean_dec(v___x_2933_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_3033_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v_fieldNames_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v_fieldNames_2938_ = lean_ctor_get(v_val_2934_, 1);
lean_inc_ref(v_fieldNames_2938_);
lean_dec(v_val_2934_);
v___x_2939_ = lean_array_get_size(v_fieldNames_2938_);
v___x_2940_ = lean_nat_dec_lt(v_idx_2929_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_object* v_options_2941_; uint8_t v_hasTrace_2942_; 
lean_dec_ref(v_fieldNames_2938_);
v_options_2941_ = lean_ctor_get(v___y_2919_, 2);
v_hasTrace_2942_ = lean_ctor_get_uint8(v_options_2941_, sizeof(void*)*1);
if (v_hasTrace_2942_ == 0)
{
lean_del_object(v___x_2936_);
goto v___jp_2922_;
}
else
{
lean_object* v_inheritedTraceOptions_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; uint8_t v___x_2946_; 
v_inheritedTraceOptions_2943_ = lean_ctor_get(v___y_2919_, 13);
v___x_2944_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__2));
v___x_2945_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__5, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__5_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__5);
v___x_2946_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2943_, v_options_2941_, v___x_2945_);
if (v___x_2946_ == 0)
{
lean_del_object(v___x_2936_);
goto v___jp_2922_;
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
v___x_2947_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__7, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__7_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__7);
lean_inc(v_idx_2929_);
v___x_2948_ = l_Nat_reprFast(v_idx_2929_);
if (v_isShared_2937_ == 0)
{
lean_ctor_set_tag(v___x_2936_, 3);
lean_ctor_set(v___x_2936_, 0, v___x_2948_);
v___x_2950_ = v___x_2936_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; 
v___x_2951_ = l_Lean_MessageData_ofFormat(v___x_2950_);
v___x_2952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2947_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__9, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__9_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__9);
v___x_2954_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2954_, 0, v___x_2952_);
lean_ctor_set(v___x_2954_, 1, v___x_2953_);
lean_inc_ref(v_e_2916_);
v___x_2955_ = l_Lean_indentExpr(v_e_2916_);
v___x_2956_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2956_, 0, v___x_2954_);
lean_ctor_set(v___x_2956_, 1, v___x_2955_);
v___x_2957_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0(v___x_2944_, v___x_2956_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_dec_ref(v___x_2957_);
goto v___jp_2922_;
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_dec_ref(v_e_2916_);
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2967_; uint8_t v_foApprox_2968_; uint8_t v_ctxApprox_2969_; uint8_t v_quasiPatternApprox_2970_; uint8_t v_constApprox_2971_; uint8_t v_isDefEqStuckEx_2972_; uint8_t v_unificationHints_2973_; uint8_t v_proofIrrelevance_2974_; uint8_t v_assignSyntheticOpaque_2975_; uint8_t v_offsetCnstrs_2976_; uint8_t v_etaStruct_2977_; uint8_t v_univApprox_2978_; uint8_t v_iota_2979_; uint8_t v_beta_2980_; uint8_t v_proj_2981_; uint8_t v_zeta_2982_; uint8_t v_zetaDelta_2983_; uint8_t v_zetaUnused_2984_; uint8_t v_zetaHave_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3032_; 
lean_inc_ref(v_struct_2930_);
lean_inc(v_idx_2929_);
lean_dec_ref(v_e_2916_);
v___x_2967_ = l_Lean_Meta_Context_config(v___y_2917_);
v_foApprox_2968_ = lean_ctor_get_uint8(v___x_2967_, 0);
v_ctxApprox_2969_ = lean_ctor_get_uint8(v___x_2967_, 1);
v_quasiPatternApprox_2970_ = lean_ctor_get_uint8(v___x_2967_, 2);
v_constApprox_2971_ = lean_ctor_get_uint8(v___x_2967_, 3);
v_isDefEqStuckEx_2972_ = lean_ctor_get_uint8(v___x_2967_, 4);
v_unificationHints_2973_ = lean_ctor_get_uint8(v___x_2967_, 5);
v_proofIrrelevance_2974_ = lean_ctor_get_uint8(v___x_2967_, 6);
v_assignSyntheticOpaque_2975_ = lean_ctor_get_uint8(v___x_2967_, 7);
v_offsetCnstrs_2976_ = lean_ctor_get_uint8(v___x_2967_, 8);
v_etaStruct_2977_ = lean_ctor_get_uint8(v___x_2967_, 10);
v_univApprox_2978_ = lean_ctor_get_uint8(v___x_2967_, 11);
v_iota_2979_ = lean_ctor_get_uint8(v___x_2967_, 12);
v_beta_2980_ = lean_ctor_get_uint8(v___x_2967_, 13);
v_proj_2981_ = lean_ctor_get_uint8(v___x_2967_, 14);
v_zeta_2982_ = lean_ctor_get_uint8(v___x_2967_, 15);
v_zetaDelta_2983_ = lean_ctor_get_uint8(v___x_2967_, 16);
v_zetaUnused_2984_ = lean_ctor_get_uint8(v___x_2967_, 17);
v_zetaHave_2985_ = lean_ctor_get_uint8(v___x_2967_, 18);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_2987_ = v___x_2967_;
v_isShared_2988_ = v_isSharedCheck_3032_;
goto v_resetjp_2986_;
}
else
{
lean_dec(v___x_2967_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3032_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
uint8_t v_trackZetaDelta_2989_; lean_object* v_zetaDeltaSet_2990_; lean_object* v_lctx_2991_; lean_object* v_localInstances_2992_; lean_object* v_defEqCtx_x3f_2993_; lean_object* v_synthPendingDepth_2994_; lean_object* v_canUnfold_x3f_2995_; uint8_t v_univApprox_2996_; uint8_t v_inTypeClassResolution_2997_; uint8_t v_cacheInferType_2998_; uint8_t v___x_2999_; lean_object* v_config_3001_; 
v_trackZetaDelta_2989_ = lean_ctor_get_uint8(v___y_2917_, sizeof(void*)*7);
v_zetaDeltaSet_2990_ = lean_ctor_get(v___y_2917_, 1);
v_lctx_2991_ = lean_ctor_get(v___y_2917_, 2);
v_localInstances_2992_ = lean_ctor_get(v___y_2917_, 3);
v_defEqCtx_x3f_2993_ = lean_ctor_get(v___y_2917_, 4);
v_synthPendingDepth_2994_ = lean_ctor_get(v___y_2917_, 5);
v_canUnfold_x3f_2995_ = lean_ctor_get(v___y_2917_, 6);
v_univApprox_2996_ = lean_ctor_get_uint8(v___y_2917_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2997_ = lean_ctor_get_uint8(v___y_2917_, sizeof(void*)*7 + 2);
v_cacheInferType_2998_ = lean_ctor_get_uint8(v___y_2917_, sizeof(void*)*7 + 3);
v___x_2999_ = 1;
if (v_isShared_2988_ == 0)
{
v_config_3001_ = v___x_2987_;
goto v_reusejp_3000_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 0, v_foApprox_2968_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 1, v_ctxApprox_2969_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 2, v_quasiPatternApprox_2970_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 3, v_constApprox_2971_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 4, v_isDefEqStuckEx_2972_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 5, v_unificationHints_2973_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 6, v_proofIrrelevance_2974_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 7, v_assignSyntheticOpaque_2975_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 8, v_offsetCnstrs_2976_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 10, v_etaStruct_2977_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 11, v_univApprox_2978_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 12, v_iota_2979_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 13, v_beta_2980_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 14, v_proj_2981_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 15, v_zeta_2982_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 16, v_zetaDelta_2983_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 17, v_zetaUnused_2984_);
lean_ctor_set_uint8(v_reuseFailAlloc_3031_, 18, v_zetaHave_2985_);
v_config_3001_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3000_;
}
v_reusejp_3000_:
{
uint64_t v___x_3002_; uint64_t v___x_3003_; uint64_t v___x_3004_; lean_object* v___x_3005_; uint64_t v___x_3006_; uint64_t v___x_3007_; uint64_t v_key_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; 
lean_ctor_set_uint8(v_config_3001_, 9, v___x_2999_);
v___x_3002_ = l_Lean_Meta_Context_configKey(v___y_2917_);
v___x_3003_ = 2ULL;
v___x_3004_ = lean_uint64_shift_right(v___x_3002_, v___x_3003_);
v___x_3005_ = lean_array_fget(v_fieldNames_2938_, v_idx_2929_);
lean_dec(v_idx_2929_);
lean_dec_ref(v_fieldNames_2938_);
v___x_3006_ = lean_uint64_shift_left(v___x_3004_, v___x_3003_);
v___x_3007_ = lean_uint64_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__10, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__10_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__10);
v_key_3008_ = lean_uint64_lor(v___x_3006_, v___x_3007_);
v___x_3009_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3009_, 0, v_config_3001_);
lean_ctor_set_uint64(v___x_3009_, sizeof(void*)*1, v_key_3008_);
lean_inc(v_canUnfold_x3f_2995_);
lean_inc(v_synthPendingDepth_2994_);
lean_inc(v_defEqCtx_x3f_2993_);
lean_inc_ref(v_localInstances_2992_);
lean_inc_ref(v_lctx_2991_);
lean_inc(v_zetaDeltaSet_2990_);
v___x_3010_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3010_, 0, v___x_3009_);
lean_ctor_set(v___x_3010_, 1, v_zetaDeltaSet_2990_);
lean_ctor_set(v___x_3010_, 2, v_lctx_2991_);
lean_ctor_set(v___x_3010_, 3, v_localInstances_2992_);
lean_ctor_set(v___x_3010_, 4, v_defEqCtx_x3f_2993_);
lean_ctor_set(v___x_3010_, 5, v_synthPendingDepth_2994_);
lean_ctor_set(v___x_3010_, 6, v_canUnfold_x3f_2995_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*7, v_trackZetaDelta_2989_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*7 + 1, v_univApprox_2996_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2997_);
lean_ctor_set_uint8(v___x_3010_, sizeof(void*)*7 + 3, v_cacheInferType_2998_);
v___x_3011_ = l_Lean_Meta_mkProjection(v_struct_2930_, v___x_3005_, v___x_3010_, v___y_2918_, v___y_2919_, v___y_2920_);
lean_dec_ref(v___x_3010_);
if (lean_obj_tag(v___x_3011_) == 0)
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3022_; 
v_a_3012_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3014_ = v___x_3011_;
v_isShared_3015_ = v_isSharedCheck_3022_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3011_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3022_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_2937_ == 0)
{
lean_ctor_set(v___x_2936_, 0, v_a_3012_);
v___x_3017_ = v___x_2936_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
lean_object* v___x_3019_; 
if (v_isShared_3015_ == 0)
{
lean_ctor_set(v___x_3014_, 0, v___x_3017_);
v___x_3019_ = v___x_3014_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3017_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_del_object(v___x_2936_);
v_a_3023_ = lean_ctor_get(v___x_3011_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_3011_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_3011_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_3011_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
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
lean_object* v_options_3034_; uint8_t v_hasTrace_3035_; 
lean_dec(v___x_2933_);
v_options_3034_ = lean_ctor_get(v___y_2919_, 2);
v_hasTrace_3035_ = lean_ctor_get_uint8(v_options_3034_, sizeof(void*)*1);
if (v_hasTrace_3035_ == 0)
{
goto v___jp_2925_;
}
else
{
lean_object* v_inheritedTraceOptions_3036_; lean_object* v___x_3037_; lean_object* v___x_3038_; uint8_t v___x_3039_; 
v_inheritedTraceOptions_3036_ = lean_ctor_get(v___y_2919_, 13);
v___x_3037_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__2));
v___x_3038_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__5, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__5_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__5);
v___x_3039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3036_, v_options_3034_, v___x_3038_);
if (v___x_3039_ == 0)
{
goto v___jp_2925_;
}
else
{
lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; 
v___x_3040_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__12, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__12_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__12);
lean_inc(v_typeName_2928_);
v___x_3041_ = l_Lean_MessageData_ofName(v_typeName_2928_);
v___x_3042_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3042_, 0, v___x_3040_);
lean_ctor_set(v___x_3042_, 1, v___x_3041_);
v___x_3043_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__14, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__14_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__14);
v___x_3044_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3044_, 0, v___x_3042_);
lean_ctor_set(v___x_3044_, 1, v___x_3043_);
lean_inc_ref(v_e_2916_);
v___x_3045_ = l_Lean_indentExpr(v_e_2916_);
v___x_3046_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3046_, 0, v___x_3044_);
lean_ctor_set(v___x_3046_, 1, v___x_3045_);
v___x_3047_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0(v___x_3037_, v___x_3046_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_);
if (lean_obj_tag(v___x_3047_) == 0)
{
lean_dec_ref(v___x_3047_);
goto v___jp_2925_;
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec_ref(v_e_2916_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3047_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3047_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3047_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3056_, 0, v_e_2916_);
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
return v___x_3057_;
}
v___jp_2922_:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v_e_2916_);
v___x_2924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2924_, 0, v___x_2923_);
return v___x_2924_;
}
v___jp_2925_:
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2926_, 0, v_e_2916_);
v___x_2927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
return v___x_2927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___boxed(lean_object* v_e_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Meta_Grind_foldProjs___lam__0(v_e_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1(lean_object* v_x_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___x_3073_; lean_object* v___x_3074_; 
v___x_3073_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__1___closed__0));
v___x_3074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3074_, 0, v___x_3073_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1___boxed(lean_object* v_x_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_Lean_Meta_Grind_foldProjs___lam__1(v_x_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec_ref(v_x_3075_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_3082_, lean_object* v_x_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v___x_3089_; lean_object* v___x_3090_; 
v___x_3089_ = lean_apply_1(v_x_3083_, lean_box(0));
v___x_3090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3090_, 0, v___x_3089_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_3091_, lean_object* v_x_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v_res_3098_; 
v_res_3098_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(v_00_u03b1_3091_, v_x_3092_, v___y_3093_, v___y_3094_, v___y_3095_, v___y_3096_);
lean_dec(v___y_3096_);
lean_dec_ref(v___y_3095_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
return v_res_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg(lean_object* v_ref_3099_){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3102_, 0, v_ref_3099_);
lean_ctor_set(v___x_3102_, 1, v___x_3101_);
v___x_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg___boxed(lean_object* v_ref_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v_res_3106_; 
v_res_3106_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg(v_ref_3104_);
return v_res_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg(lean_object* v_x_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v___y_3115_; lean_object* v_fileName_3124_; lean_object* v_fileMap_3125_; lean_object* v_options_3126_; lean_object* v_currRecDepth_3127_; lean_object* v_maxRecDepth_3128_; lean_object* v_ref_3129_; lean_object* v_currNamespace_3130_; lean_object* v_openDecls_3131_; lean_object* v_initHeartbeats_3132_; lean_object* v_maxHeartbeats_3133_; lean_object* v_quotContext_3134_; lean_object* v_currMacroScope_3135_; uint8_t v_diag_3136_; lean_object* v_cancelTk_x3f_3137_; uint8_t v_suppressElabErrors_3138_; lean_object* v_inheritedTraceOptions_3139_; lean_object* v___x_3145_; uint8_t v___x_3146_; 
v_fileName_3124_ = lean_ctor_get(v___y_3111_, 0);
v_fileMap_3125_ = lean_ctor_get(v___y_3111_, 1);
v_options_3126_ = lean_ctor_get(v___y_3111_, 2);
v_currRecDepth_3127_ = lean_ctor_get(v___y_3111_, 3);
v_maxRecDepth_3128_ = lean_ctor_get(v___y_3111_, 4);
v_ref_3129_ = lean_ctor_get(v___y_3111_, 5);
v_currNamespace_3130_ = lean_ctor_get(v___y_3111_, 6);
v_openDecls_3131_ = lean_ctor_get(v___y_3111_, 7);
v_initHeartbeats_3132_ = lean_ctor_get(v___y_3111_, 8);
v_maxHeartbeats_3133_ = lean_ctor_get(v___y_3111_, 9);
v_quotContext_3134_ = lean_ctor_get(v___y_3111_, 10);
v_currMacroScope_3135_ = lean_ctor_get(v___y_3111_, 11);
v_diag_3136_ = lean_ctor_get_uint8(v___y_3111_, sizeof(void*)*14);
v_cancelTk_x3f_3137_ = lean_ctor_get(v___y_3111_, 12);
v_suppressElabErrors_3138_ = lean_ctor_get_uint8(v___y_3111_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3139_ = lean_ctor_get(v___y_3111_, 13);
v___x_3145_ = lean_unsigned_to_nat(0u);
v___x_3146_ = lean_nat_dec_eq(v_maxRecDepth_3128_, v___x_3145_);
if (v___x_3146_ == 0)
{
uint8_t v___x_3147_; 
v___x_3147_ = lean_nat_dec_eq(v_currRecDepth_3127_, v_maxRecDepth_3128_);
if (v___x_3147_ == 0)
{
goto v___jp_3140_;
}
else
{
lean_object* v___x_3148_; 
lean_dec_ref(v_x_3107_);
lean_inc(v_ref_3129_);
v___x_3148_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg(v_ref_3129_);
v___y_3115_ = v___x_3148_;
goto v___jp_3114_;
}
}
else
{
goto v___jp_3140_;
}
v___jp_3114_:
{
if (lean_obj_tag(v___y_3115_) == 0)
{
return v___y_3115_;
}
else
{
lean_object* v_a_3116_; lean_object* v___x_3118_; uint8_t v_isShared_3119_; uint8_t v_isSharedCheck_3123_; 
v_a_3116_ = lean_ctor_get(v___y_3115_, 0);
v_isSharedCheck_3123_ = !lean_is_exclusive(v___y_3115_);
if (v_isSharedCheck_3123_ == 0)
{
v___x_3118_ = v___y_3115_;
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
else
{
lean_inc(v_a_3116_);
lean_dec(v___y_3115_);
v___x_3118_ = lean_box(0);
v_isShared_3119_ = v_isSharedCheck_3123_;
goto v_resetjp_3117_;
}
v_resetjp_3117_:
{
lean_object* v___x_3121_; 
if (v_isShared_3119_ == 0)
{
v___x_3121_ = v___x_3118_;
goto v_reusejp_3120_;
}
else
{
lean_object* v_reuseFailAlloc_3122_; 
v_reuseFailAlloc_3122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_a_3116_);
v___x_3121_ = v_reuseFailAlloc_3122_;
goto v_reusejp_3120_;
}
v_reusejp_3120_:
{
return v___x_3121_;
}
}
}
}
v___jp_3140_:
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; 
v___x_3141_ = lean_unsigned_to_nat(1u);
v___x_3142_ = lean_nat_add(v_currRecDepth_3127_, v___x_3141_);
lean_inc_ref(v_inheritedTraceOptions_3139_);
lean_inc(v_cancelTk_x3f_3137_);
lean_inc(v_currMacroScope_3135_);
lean_inc(v_quotContext_3134_);
lean_inc(v_maxHeartbeats_3133_);
lean_inc(v_initHeartbeats_3132_);
lean_inc(v_openDecls_3131_);
lean_inc(v_currNamespace_3130_);
lean_inc(v_ref_3129_);
lean_inc(v_maxRecDepth_3128_);
lean_inc_ref(v_options_3126_);
lean_inc_ref(v_fileMap_3125_);
lean_inc_ref(v_fileName_3124_);
v___x_3143_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3143_, 0, v_fileName_3124_);
lean_ctor_set(v___x_3143_, 1, v_fileMap_3125_);
lean_ctor_set(v___x_3143_, 2, v_options_3126_);
lean_ctor_set(v___x_3143_, 3, v___x_3142_);
lean_ctor_set(v___x_3143_, 4, v_maxRecDepth_3128_);
lean_ctor_set(v___x_3143_, 5, v_ref_3129_);
lean_ctor_set(v___x_3143_, 6, v_currNamespace_3130_);
lean_ctor_set(v___x_3143_, 7, v_openDecls_3131_);
lean_ctor_set(v___x_3143_, 8, v_initHeartbeats_3132_);
lean_ctor_set(v___x_3143_, 9, v_maxHeartbeats_3133_);
lean_ctor_set(v___x_3143_, 10, v_quotContext_3134_);
lean_ctor_set(v___x_3143_, 11, v_currMacroScope_3135_);
lean_ctor_set(v___x_3143_, 12, v_cancelTk_x3f_3137_);
lean_ctor_set(v___x_3143_, 13, v_inheritedTraceOptions_3139_);
lean_ctor_set_uint8(v___x_3143_, sizeof(void*)*14, v_diag_3136_);
lean_ctor_set_uint8(v___x_3143_, sizeof(void*)*14 + 1, v_suppressElabErrors_3138_);
lean_inc(v___y_3112_);
lean_inc(v___y_3110_);
lean_inc_ref(v___y_3109_);
lean_inc(v___y_3108_);
v___x_3144_ = lean_apply_6(v_x_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___x_3143_, v___y_3112_, lean_box(0));
v___y_3115_ = v___x_3144_;
goto v___jp_3114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_x_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg(v_x_3149_, v___y_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0(lean_object* v_k_3157_, lean_object* v___y_3158_, lean_object* v_b_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v___x_3165_; 
lean_inc(v___y_3163_);
lean_inc_ref(v___y_3162_);
lean_inc(v___y_3161_);
lean_inc_ref(v___y_3160_);
lean_inc(v___y_3158_);
v___x_3165_ = lean_apply_7(v_k_3157_, v_b_3159_, v___y_3158_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_, lean_box(0));
return v___x_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_k_3166_, lean_object* v___y_3167_, lean_object* v_b_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v_res_3174_; 
v_res_3174_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0(v_k_3166_, v___y_3167_, v_b_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3167_);
return v_res_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(lean_object* v_name_3175_, uint8_t v_bi_3176_, lean_object* v_type_3177_, lean_object* v_k_3178_, uint8_t v_kind_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_){
_start:
{
lean_object* v___f_3186_; lean_object* v___x_3187_; 
lean_inc(v___y_3180_);
v___f_3186_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3186_, 0, v_k_3178_);
lean_closure_set(v___f_3186_, 1, v___y_3180_);
v___x_3187_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3175_, v_bi_3176_, v_type_3177_, v___f_3186_, v_kind_3179_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
if (lean_obj_tag(v___x_3187_) == 0)
{
return v___x_3187_;
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
v_a_3188_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___x_3187_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___x_3187_);
v___x_3190_ = lean_box(0);
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
v_resetjp_3189_:
{
lean_object* v___x_3193_; 
if (v_isShared_3191_ == 0)
{
v___x_3193_ = v___x_3190_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3194_; 
v_reuseFailAlloc_3194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3194_, 0, v_a_3188_);
v___x_3193_ = v_reuseFailAlloc_3194_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
return v___x_3193_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___boxed(lean_object* v_name_3196_, lean_object* v_bi_3197_, lean_object* v_type_3198_, lean_object* v_k_3199_, lean_object* v_kind_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_, lean_object* v___y_3204_, lean_object* v___y_3205_, lean_object* v___y_3206_){
_start:
{
uint8_t v_bi_boxed_3207_; uint8_t v_kind_boxed_3208_; lean_object* v_res_3209_; 
v_bi_boxed_3207_ = lean_unbox(v_bi_3197_);
v_kind_boxed_3208_ = lean_unbox(v_kind_3200_);
v_res_3209_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(v_name_3196_, v_bi_boxed_3207_, v_type_3198_, v_k_3199_, v_kind_boxed_3208_, v___y_3201_, v___y_3202_, v___y_3203_, v___y_3204_, v___y_3205_);
lean_dec(v___y_3205_);
lean_dec_ref(v___y_3204_);
lean_dec(v___y_3203_);
lean_dec_ref(v___y_3202_);
lean_dec(v___y_3201_);
return v_res_3209_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__2(lean_object* v___x_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3216_, 0, v___x_3210_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__2___boxed(lean_object* v___x_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
lean_object* v_res_3223_; 
v_res_3223_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__2(v___x_3217_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
return v_res_3223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg(lean_object* v_name_3224_, lean_object* v_type_3225_, lean_object* v_val_3226_, lean_object* v_k_3227_, uint8_t v_nondep_3228_, uint8_t v_kind_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_){
_start:
{
lean_object* v___f_3236_; lean_object* v___x_3237_; 
lean_inc(v___y_3230_);
v___f_3236_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3236_, 0, v_k_3227_);
lean_closure_set(v___f_3236_, 1, v___y_3230_);
v___x_3237_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3224_, v_type_3225_, v_val_3226_, v___f_3236_, v_nondep_3228_, v_kind_3229_, v___y_3231_, v___y_3232_, v___y_3233_, v___y_3234_);
if (lean_obj_tag(v___x_3237_) == 0)
{
return v___x_3237_;
}
else
{
lean_object* v_a_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3245_; 
v_a_3238_ = lean_ctor_get(v___x_3237_, 0);
v_isSharedCheck_3245_ = !lean_is_exclusive(v___x_3237_);
if (v_isSharedCheck_3245_ == 0)
{
v___x_3240_ = v___x_3237_;
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_a_3238_);
lean_dec(v___x_3237_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3245_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3243_; 
if (v_isShared_3241_ == 0)
{
v___x_3243_ = v___x_3240_;
goto v_reusejp_3242_;
}
else
{
lean_object* v_reuseFailAlloc_3244_; 
v_reuseFailAlloc_3244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3244_, 0, v_a_3238_);
v___x_3243_ = v_reuseFailAlloc_3244_;
goto v_reusejp_3242_;
}
v_reusejp_3242_:
{
return v___x_3243_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg___boxed(lean_object* v_name_3246_, lean_object* v_type_3247_, lean_object* v_val_3248_, lean_object* v_k_3249_, lean_object* v_nondep_3250_, lean_object* v_kind_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
uint8_t v_nondep_boxed_3258_; uint8_t v_kind_boxed_3259_; lean_object* v_res_3260_; 
v_nondep_boxed_3258_ = lean_unbox(v_nondep_3250_);
v_kind_boxed_3259_ = lean_unbox(v_kind_3251_);
v_res_3260_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg(v_name_3246_, v_type_3247_, v_val_3248_, v_k_3249_, v_nondep_boxed_3258_, v_kind_boxed_3259_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
lean_dec(v___y_3256_);
lean_dec_ref(v___y_3255_);
lean_dec(v___y_3254_);
lean_dec_ref(v___y_3253_);
lean_dec(v___y_3252_);
return v_res_3260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___lam__0(lean_object* v_fvars_3263_, lean_object* v_pre_3264_, lean_object* v_post_3265_, uint8_t v_usedLetOnly_3266_, uint8_t v_skipConstInApp_3267_, uint8_t v_skipInstances_3268_, lean_object* v_body_3269_, lean_object* v_x_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_){
_start:
{
lean_object* v___x_3277_; lean_object* v___x_3278_; 
v___x_3277_ = lean_array_push(v_fvars_3263_, v_x_3270_);
v___x_3278_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7(v_pre_3264_, v_post_3265_, v_usedLetOnly_3266_, v_skipConstInApp_3267_, v_skipInstances_3268_, v___x_3277_, v_body_3269_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
return v___x_3278_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___lam__0___boxed(lean_object* v_fvars_3279_, lean_object* v_pre_3280_, lean_object* v_post_3281_, lean_object* v_usedLetOnly_3282_, lean_object* v_skipConstInApp_3283_, lean_object* v_skipInstances_3284_, lean_object* v_body_3285_, lean_object* v_x_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
uint8_t v_usedLetOnly_boxed_3293_; uint8_t v_skipConstInApp_boxed_3294_; uint8_t v_skipInstances_boxed_3295_; lean_object* v_res_3296_; 
v_usedLetOnly_boxed_3293_ = lean_unbox(v_usedLetOnly_3282_);
v_skipConstInApp_boxed_3294_ = lean_unbox(v_skipConstInApp_3283_);
v_skipInstances_boxed_3295_ = lean_unbox(v_skipInstances_3284_);
v_res_3296_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___lam__0(v_fvars_3279_, v_pre_3280_, v_post_3281_, v_usedLetOnly_boxed_3293_, v_skipConstInApp_boxed_3294_, v_skipInstances_boxed_3295_, v_body_3285_, v_x_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(lean_object* v_pre_3297_, lean_object* v_post_3298_, uint8_t v_usedLetOnly_3299_, uint8_t v_skipConstInApp_3300_, uint8_t v_skipInstances_3301_, lean_object* v_e_3302_, lean_object* v_a_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v___x_3309_; 
lean_inc_ref(v_post_3298_);
lean_inc(v___y_3307_);
lean_inc_ref(v___y_3306_);
lean_inc(v___y_3305_);
lean_inc_ref(v___y_3304_);
lean_inc_ref(v_e_3302_);
v___x_3309_ = lean_apply_6(v_post_3298_, v_e_3302_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, lean_box(0));
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; lean_object* v___x_3312_; uint8_t v_isShared_3313_; uint8_t v_isSharedCheck_3328_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3312_ = v___x_3309_;
v_isShared_3313_ = v_isSharedCheck_3328_;
goto v_resetjp_3311_;
}
else
{
lean_inc(v_a_3310_);
lean_dec(v___x_3309_);
v___x_3312_ = lean_box(0);
v_isShared_3313_ = v_isSharedCheck_3328_;
goto v_resetjp_3311_;
}
v_resetjp_3311_:
{
switch(lean_obj_tag(v_a_3310_))
{
case 0:
{
lean_object* v_e_3314_; lean_object* v___x_3316_; 
lean_dec_ref(v_e_3302_);
lean_dec_ref(v_post_3298_);
lean_dec_ref(v_pre_3297_);
v_e_3314_ = lean_ctor_get(v_a_3310_, 0);
lean_inc_ref(v_e_3314_);
lean_dec_ref(v_a_3310_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v_e_3314_);
v___x_3316_ = v___x_3312_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3317_; 
v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_e_3314_);
v___x_3316_ = v_reuseFailAlloc_3317_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
return v___x_3316_;
}
}
case 1:
{
lean_object* v_e_3318_; lean_object* v___x_3319_; 
lean_del_object(v___x_3312_);
lean_dec_ref(v_e_3302_);
v_e_3318_ = lean_ctor_get(v_a_3310_, 0);
lean_inc_ref(v_e_3318_);
lean_dec_ref(v_a_3310_);
v___x_3319_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3297_, v_post_3298_, v_usedLetOnly_3299_, v_skipConstInApp_3300_, v_skipInstances_3301_, v_e_3318_, v_a_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
return v___x_3319_;
}
default: 
{
lean_object* v_e_x3f_3320_; 
lean_dec_ref(v_post_3298_);
lean_dec_ref(v_pre_3297_);
v_e_x3f_3320_ = lean_ctor_get(v_a_3310_, 0);
lean_inc(v_e_x3f_3320_);
lean_dec_ref(v_a_3310_);
if (lean_obj_tag(v_e_x3f_3320_) == 0)
{
lean_object* v___x_3322_; 
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v_e_3302_);
v___x_3322_ = v___x_3312_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_e_3302_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
else
{
lean_object* v_val_3324_; lean_object* v___x_3326_; 
lean_dec_ref(v_e_3302_);
v_val_3324_ = lean_ctor_get(v_e_x3f_3320_, 0);
lean_inc(v_val_3324_);
lean_dec_ref(v_e_x3f_3320_);
if (v_isShared_3313_ == 0)
{
lean_ctor_set(v___x_3312_, 0, v_val_3324_);
v___x_3326_ = v___x_3312_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_val_3324_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
}
else
{
lean_object* v_a_3329_; lean_object* v___x_3331_; uint8_t v_isShared_3332_; uint8_t v_isSharedCheck_3336_; 
lean_dec_ref(v_e_3302_);
lean_dec_ref(v_post_3298_);
lean_dec_ref(v_pre_3297_);
v_a_3329_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3336_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3336_ == 0)
{
v___x_3331_ = v___x_3309_;
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
else
{
lean_inc(v_a_3329_);
lean_dec(v___x_3309_);
v___x_3331_ = lean_box(0);
v_isShared_3332_ = v_isSharedCheck_3336_;
goto v_resetjp_3330_;
}
v_resetjp_3330_:
{
lean_object* v___x_3334_; 
if (v_isShared_3332_ == 0)
{
v___x_3334_ = v___x_3331_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_a_3329_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
return v___x_3334_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7(lean_object* v_pre_3337_, lean_object* v_post_3338_, uint8_t v_usedLetOnly_3339_, uint8_t v_skipConstInApp_3340_, uint8_t v_skipInstances_3341_, lean_object* v_fvars_3342_, lean_object* v_e_3343_, lean_object* v_a_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
if (lean_obj_tag(v_e_3343_) == 6)
{
lean_object* v_binderName_3350_; lean_object* v_binderType_3351_; lean_object* v_body_3352_; uint8_t v_binderInfo_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; 
v_binderName_3350_ = lean_ctor_get(v_e_3343_, 0);
lean_inc(v_binderName_3350_);
v_binderType_3351_ = lean_ctor_get(v_e_3343_, 1);
lean_inc_ref(v_binderType_3351_);
v_body_3352_ = lean_ctor_get(v_e_3343_, 2);
lean_inc_ref(v_body_3352_);
v_binderInfo_3353_ = lean_ctor_get_uint8(v_e_3343_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3343_);
v___x_3354_ = lean_expr_instantiate_rev(v_binderType_3351_, v_fvars_3342_);
lean_dec_ref(v_binderType_3351_);
lean_inc_ref(v_post_3338_);
lean_inc_ref(v_pre_3337_);
v___x_3355_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3337_, v_post_3338_, v_usedLetOnly_3339_, v_skipConstInApp_3340_, v_skipInstances_3341_, v___x_3354_, v_a_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___f_3360_; uint8_t v___x_3361_; lean_object* v___x_3362_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
lean_inc(v_a_3356_);
lean_dec_ref(v___x_3355_);
v___x_3357_ = lean_box(v_usedLetOnly_3339_);
v___x_3358_ = lean_box(v_skipConstInApp_3340_);
v___x_3359_ = lean_box(v_skipInstances_3341_);
v___f_3360_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3360_, 0, v_fvars_3342_);
lean_closure_set(v___f_3360_, 1, v_pre_3337_);
lean_closure_set(v___f_3360_, 2, v_post_3338_);
lean_closure_set(v___f_3360_, 3, v___x_3357_);
lean_closure_set(v___f_3360_, 4, v___x_3358_);
lean_closure_set(v___f_3360_, 5, v___x_3359_);
lean_closure_set(v___f_3360_, 6, v_body_3352_);
v___x_3361_ = 0;
v___x_3362_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(v_binderName_3350_, v_binderInfo_3353_, v_a_3356_, v___f_3360_, v___x_3361_, v_a_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
return v___x_3362_;
}
else
{
lean_dec_ref(v_body_3352_);
lean_dec(v_binderName_3350_);
lean_dec_ref(v_fvars_3342_);
lean_dec_ref(v_post_3338_);
lean_dec_ref(v_pre_3337_);
return v___x_3355_;
}
}
else
{
lean_object* v___x_3363_; lean_object* v___x_3364_; 
v___x_3363_ = lean_expr_instantiate_rev(v_e_3343_, v_fvars_3342_);
lean_dec_ref(v_e_3343_);
lean_inc_ref(v_post_3338_);
lean_inc_ref(v_pre_3337_);
v___x_3364_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3337_, v_post_3338_, v_usedLetOnly_3339_, v_skipConstInApp_3340_, v_skipInstances_3341_, v___x_3363_, v_a_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
if (lean_obj_tag(v___x_3364_) == 0)
{
lean_object* v_a_3365_; uint8_t v___x_3366_; uint8_t v___x_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; 
v_a_3365_ = lean_ctor_get(v___x_3364_, 0);
lean_inc(v_a_3365_);
lean_dec_ref(v___x_3364_);
v___x_3366_ = 0;
v___x_3367_ = 1;
v___x_3368_ = 1;
v___x_3369_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3342_, v_a_3365_, v___x_3366_, v_usedLetOnly_3339_, v___x_3366_, v___x_3367_, v___x_3368_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec_ref(v_fvars_3342_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v_a_3370_; lean_object* v___x_3371_; 
v_a_3370_ = lean_ctor_get(v___x_3369_, 0);
lean_inc(v_a_3370_);
lean_dec_ref(v___x_3369_);
v___x_3371_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3337_, v_post_3338_, v_usedLetOnly_3339_, v_skipConstInApp_3340_, v_skipInstances_3341_, v_a_3370_, v_a_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
return v___x_3371_;
}
else
{
lean_dec_ref(v_post_3338_);
lean_dec_ref(v_pre_3337_);
return v___x_3369_;
}
}
else
{
lean_dec_ref(v_fvars_3342_);
lean_dec_ref(v_post_3338_);
lean_dec_ref(v_pre_3337_);
return v___x_3364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___lam__0(lean_object* v_fvars_3372_, lean_object* v_pre_3373_, lean_object* v_post_3374_, uint8_t v_usedLetOnly_3375_, uint8_t v_skipConstInApp_3376_, uint8_t v_skipInstances_3377_, lean_object* v_body_3378_, lean_object* v_x_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_){
_start:
{
lean_object* v___x_3386_; lean_object* v___x_3387_; 
v___x_3386_ = lean_array_push(v_fvars_3372_, v_x_3379_);
v___x_3387_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8(v_pre_3373_, v_post_3374_, v_usedLetOnly_3375_, v_skipConstInApp_3376_, v_skipInstances_3377_, v___x_3386_, v_body_3378_, v___y_3380_, v___y_3381_, v___y_3382_, v___y_3383_, v___y_3384_);
return v___x_3387_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___lam__0___boxed(lean_object* v_fvars_3388_, lean_object* v_pre_3389_, lean_object* v_post_3390_, lean_object* v_usedLetOnly_3391_, lean_object* v_skipConstInApp_3392_, lean_object* v_skipInstances_3393_, lean_object* v_body_3394_, lean_object* v_x_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
uint8_t v_usedLetOnly_boxed_3402_; uint8_t v_skipConstInApp_boxed_3403_; uint8_t v_skipInstances_boxed_3404_; lean_object* v_res_3405_; 
v_usedLetOnly_boxed_3402_ = lean_unbox(v_usedLetOnly_3391_);
v_skipConstInApp_boxed_3403_ = lean_unbox(v_skipConstInApp_3392_);
v_skipInstances_boxed_3404_ = lean_unbox(v_skipInstances_3393_);
v_res_3405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___lam__0(v_fvars_3388_, v_pre_3389_, v_post_3390_, v_usedLetOnly_boxed_3402_, v_skipConstInApp_boxed_3403_, v_skipInstances_boxed_3404_, v_body_3394_, v_x_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___y_3396_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8(lean_object* v_pre_3406_, lean_object* v_post_3407_, uint8_t v_usedLetOnly_3408_, uint8_t v_skipConstInApp_3409_, uint8_t v_skipInstances_3410_, lean_object* v_fvars_3411_, lean_object* v_e_3412_, lean_object* v_a_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
if (lean_obj_tag(v_e_3412_) == 8)
{
lean_object* v_declName_3419_; lean_object* v_type_3420_; lean_object* v_value_3421_; lean_object* v_body_3422_; uint8_t v_nondep_3423_; lean_object* v___x_3424_; lean_object* v___x_3425_; 
v_declName_3419_ = lean_ctor_get(v_e_3412_, 0);
lean_inc(v_declName_3419_);
v_type_3420_ = lean_ctor_get(v_e_3412_, 1);
lean_inc_ref(v_type_3420_);
v_value_3421_ = lean_ctor_get(v_e_3412_, 2);
lean_inc_ref(v_value_3421_);
v_body_3422_ = lean_ctor_get(v_e_3412_, 3);
lean_inc_ref(v_body_3422_);
v_nondep_3423_ = lean_ctor_get_uint8(v_e_3412_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3412_);
v___x_3424_ = lean_expr_instantiate_rev(v_type_3420_, v_fvars_3411_);
lean_dec_ref(v_type_3420_);
lean_inc_ref(v_post_3407_);
lean_inc_ref(v_pre_3406_);
v___x_3425_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3406_, v_post_3407_, v_usedLetOnly_3408_, v_skipConstInApp_3409_, v_skipInstances_3410_, v___x_3424_, v_a_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3425_) == 0)
{
lean_object* v_a_3426_; lean_object* v___x_3427_; lean_object* v___x_3428_; 
v_a_3426_ = lean_ctor_get(v___x_3425_, 0);
lean_inc(v_a_3426_);
lean_dec_ref(v___x_3425_);
v___x_3427_ = lean_expr_instantiate_rev(v_value_3421_, v_fvars_3411_);
lean_dec_ref(v_value_3421_);
lean_inc_ref(v_post_3407_);
lean_inc_ref(v_pre_3406_);
v___x_3428_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3406_, v_post_3407_, v_usedLetOnly_3408_, v_skipConstInApp_3409_, v_skipInstances_3410_, v___x_3427_, v_a_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3428_) == 0)
{
lean_object* v_a_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___f_3433_; uint8_t v___x_3434_; lean_object* v___x_3435_; 
v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
lean_inc(v_a_3429_);
lean_dec_ref(v___x_3428_);
v___x_3430_ = lean_box(v_usedLetOnly_3408_);
v___x_3431_ = lean_box(v_skipConstInApp_3409_);
v___x_3432_ = lean_box(v_skipInstances_3410_);
v___f_3433_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3433_, 0, v_fvars_3411_);
lean_closure_set(v___f_3433_, 1, v_pre_3406_);
lean_closure_set(v___f_3433_, 2, v_post_3407_);
lean_closure_set(v___f_3433_, 3, v___x_3430_);
lean_closure_set(v___f_3433_, 4, v___x_3431_);
lean_closure_set(v___f_3433_, 5, v___x_3432_);
lean_closure_set(v___f_3433_, 6, v_body_3422_);
v___x_3434_ = 0;
v___x_3435_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg(v_declName_3419_, v_a_3426_, v_a_3429_, v___f_3433_, v_nondep_3423_, v___x_3434_, v_a_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3435_;
}
else
{
lean_dec(v_a_3426_);
lean_dec_ref(v_body_3422_);
lean_dec(v_declName_3419_);
lean_dec_ref(v_fvars_3411_);
lean_dec_ref(v_post_3407_);
lean_dec_ref(v_pre_3406_);
return v___x_3428_;
}
}
else
{
lean_dec_ref(v_body_3422_);
lean_dec_ref(v_value_3421_);
lean_dec(v_declName_3419_);
lean_dec_ref(v_fvars_3411_);
lean_dec_ref(v_post_3407_);
lean_dec_ref(v_pre_3406_);
return v___x_3425_;
}
}
else
{
lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3436_ = lean_expr_instantiate_rev(v_e_3412_, v_fvars_3411_);
lean_dec_ref(v_e_3412_);
lean_inc_ref(v_post_3407_);
lean_inc_ref(v_pre_3406_);
v___x_3437_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3406_, v_post_3407_, v_usedLetOnly_3408_, v_skipConstInApp_3409_, v_skipInstances_3410_, v___x_3436_, v_a_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
if (lean_obj_tag(v___x_3437_) == 0)
{
lean_object* v_a_3438_; uint8_t v___x_3439_; uint8_t v___x_3440_; lean_object* v___x_3441_; 
v_a_3438_ = lean_ctor_get(v___x_3437_, 0);
lean_inc(v_a_3438_);
lean_dec_ref(v___x_3437_);
v___x_3439_ = 0;
v___x_3440_ = 1;
v___x_3441_ = l_Lean_Meta_mkLetFVars(v_fvars_3411_, v_a_3438_, v_usedLetOnly_3408_, v___x_3439_, v___x_3440_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec_ref(v_fvars_3411_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
v___x_3443_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3406_, v_post_3407_, v_usedLetOnly_3408_, v_skipConstInApp_3409_, v_skipInstances_3410_, v_a_3442_, v_a_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
return v___x_3443_;
}
else
{
lean_dec_ref(v_post_3407_);
lean_dec_ref(v_pre_3406_);
return v___x_3441_;
}
}
else
{
lean_dec_ref(v_fvars_3411_);
lean_dec_ref(v_post_3407_);
lean_dec_ref(v_pre_3406_);
return v___x_3437_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__3(lean_object* v_pre_3444_, lean_object* v_post_3445_, uint8_t v_usedLetOnly_3446_, uint8_t v_skipConstInApp_3447_, uint8_t v_skipInstances_3448_, size_t v_sz_3449_, size_t v_i_3450_, lean_object* v_bs_3451_, lean_object* v___y_3452_, lean_object* v___y_3453_, lean_object* v___y_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_){
_start:
{
uint8_t v___x_3458_; 
v___x_3458_ = lean_usize_dec_lt(v_i_3450_, v_sz_3449_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; 
lean_dec_ref(v_post_3445_);
lean_dec_ref(v_pre_3444_);
v___x_3459_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3459_, 0, v_bs_3451_);
return v___x_3459_;
}
else
{
lean_object* v_v_3460_; lean_object* v___x_3461_; 
v_v_3460_ = lean_array_uget_borrowed(v_bs_3451_, v_i_3450_);
lean_inc(v_v_3460_);
lean_inc_ref(v_post_3445_);
lean_inc_ref(v_pre_3444_);
v___x_3461_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3444_, v_post_3445_, v_usedLetOnly_3446_, v_skipConstInApp_3447_, v_skipInstances_3448_, v_v_3460_, v___y_3452_, v___y_3453_, v___y_3454_, v___y_3455_, v___y_3456_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; lean_object* v___x_3463_; lean_object* v_bs_x27_3464_; size_t v___x_3465_; size_t v___x_3466_; lean_object* v___x_3467_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
v___x_3463_ = lean_unsigned_to_nat(0u);
v_bs_x27_3464_ = lean_array_uset(v_bs_3451_, v_i_3450_, v___x_3463_);
v___x_3465_ = ((size_t)1ULL);
v___x_3466_ = lean_usize_add(v_i_3450_, v___x_3465_);
v___x_3467_ = lean_array_uset(v_bs_x27_3464_, v_i_3450_, v_a_3462_);
v_i_3450_ = v___x_3466_;
v_bs_3451_ = v___x_3467_;
goto _start;
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_dec_ref(v_bs_3451_);
lean_dec_ref(v_post_3445_);
lean_dec_ref(v_pre_3444_);
v_a_3469_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3461_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3461_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0(lean_object* v_pre_3477_, lean_object* v_post_3478_, uint8_t v_usedLetOnly_3479_, uint8_t v_skipConstInApp_3480_, uint8_t v_skipInstances_3481_, lean_object* v___x_3482_, lean_object* v___y_3483_, lean_object* v_b_3484_, lean_object* v_a_3485_, lean_object* v___y_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_){
_start:
{
lean_object* v___x_3491_; 
v___x_3491_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3477_, v_post_3478_, v_usedLetOnly_3479_, v_skipConstInApp_3480_, v_skipInstances_3481_, v___x_3482_, v___y_3483_, v___y_3486_, v___y_3487_, v___y_3488_, v___y_3489_);
if (lean_obj_tag(v___x_3491_) == 0)
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3501_; 
v_a_3492_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3501_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3501_ == 0)
{
v___x_3494_ = v___x_3491_;
v_isShared_3495_ = v_isSharedCheck_3501_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3491_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3501_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3499_; 
v___x_3496_ = lean_array_fset(v_b_3484_, v_a_3485_, v_a_3492_);
v___x_3497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3497_, 0, v___x_3496_);
if (v_isShared_3495_ == 0)
{
lean_ctor_set(v___x_3494_, 0, v___x_3497_);
v___x_3499_ = v___x_3494_;
goto v_reusejp_3498_;
}
else
{
lean_object* v_reuseFailAlloc_3500_; 
v_reuseFailAlloc_3500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3500_, 0, v___x_3497_);
v___x_3499_ = v_reuseFailAlloc_3500_;
goto v_reusejp_3498_;
}
v_reusejp_3498_:
{
return v___x_3499_;
}
}
}
else
{
lean_object* v_a_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3509_; 
lean_dec_ref(v_b_3484_);
v_a_3502_ = lean_ctor_get(v___x_3491_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3491_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3504_ = v___x_3491_;
v_isShared_3505_ = v_isSharedCheck_3509_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_a_3502_);
lean_dec(v___x_3491_);
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
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v_pre_3510_, lean_object* v_post_3511_, lean_object* v_usedLetOnly_3512_, lean_object* v_skipConstInApp_3513_, lean_object* v_skipInstances_3514_, lean_object* v___x_3515_, lean_object* v___y_3516_, lean_object* v_b_3517_, lean_object* v_a_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
uint8_t v_usedLetOnly_boxed_3524_; uint8_t v_skipConstInApp_boxed_3525_; uint8_t v_skipInstances_boxed_3526_; lean_object* v_res_3527_; 
v_usedLetOnly_boxed_3524_ = lean_unbox(v_usedLetOnly_3512_);
v_skipConstInApp_boxed_3525_ = lean_unbox(v_skipConstInApp_3513_);
v_skipInstances_boxed_3526_ = lean_unbox(v_skipInstances_3514_);
v_res_3527_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0(v_pre_3510_, v_post_3511_, v_usedLetOnly_boxed_3524_, v_skipConstInApp_boxed_3525_, v_skipInstances_boxed_3526_, v___x_3515_, v___y_3516_, v_b_3517_, v_a_3518_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v_a_3518_);
lean_dec(v___y_3516_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg(lean_object* v_upperBound_3528_, lean_object* v___x_3529_, lean_object* v_pre_3530_, lean_object* v_post_3531_, uint8_t v_usedLetOnly_3532_, uint8_t v_skipConstInApp_3533_, uint8_t v_skipInstances_3534_, lean_object* v_a_3535_, lean_object* v_b_3536_, lean_object* v___y_3537_, lean_object* v___y_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_){
_start:
{
lean_object* v___y_3544_; uint8_t v___x_3567_; 
v___x_3567_ = lean_nat_dec_lt(v_a_3535_, v_upperBound_3528_);
if (v___x_3567_ == 0)
{
lean_object* v___x_3568_; 
lean_dec(v_a_3535_);
lean_dec_ref(v_post_3531_);
lean_dec_ref(v_pre_3530_);
v___x_3568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3568_, 0, v_b_3536_);
return v___x_3568_;
}
else
{
lean_object* v___x_3569_; lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3569_ = lean_array_fget_borrowed(v_b_3536_, v_a_3535_);
v___x_3570_ = lean_array_get_size(v___x_3529_);
v___x_3571_ = lean_nat_dec_lt(v_a_3535_, v___x_3570_);
if (v___x_3571_ == 0)
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___f_3575_; 
lean_inc(v___x_3569_);
v___x_3572_ = lean_box(v_usedLetOnly_3532_);
v___x_3573_ = lean_box(v_skipConstInApp_3533_);
v___x_3574_ = lean_box(v_skipInstances_3534_);
lean_inc(v_a_3535_);
lean_inc(v___y_3537_);
lean_inc_ref(v_post_3531_);
lean_inc_ref(v_pre_3530_);
v___f_3575_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3575_, 0, v_pre_3530_);
lean_closure_set(v___f_3575_, 1, v_post_3531_);
lean_closure_set(v___f_3575_, 2, v___x_3572_);
lean_closure_set(v___f_3575_, 3, v___x_3573_);
lean_closure_set(v___f_3575_, 4, v___x_3574_);
lean_closure_set(v___f_3575_, 5, v___x_3569_);
lean_closure_set(v___f_3575_, 6, v___y_3537_);
lean_closure_set(v___f_3575_, 7, v_b_3536_);
lean_closure_set(v___f_3575_, 8, v_a_3535_);
v___y_3544_ = v___f_3575_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3576_; uint8_t v_isInstance_3577_; 
v___x_3576_ = lean_array_fget_borrowed(v___x_3529_, v_a_3535_);
v_isInstance_3577_ = lean_ctor_get_uint8(v___x_3576_, sizeof(void*)*1 + 4);
if (v_isInstance_3577_ == 0)
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___f_3581_; 
lean_inc(v___x_3569_);
v___x_3578_ = lean_box(v_usedLetOnly_3532_);
v___x_3579_ = lean_box(v_skipConstInApp_3533_);
v___x_3580_ = lean_box(v_skipInstances_3534_);
lean_inc(v_a_3535_);
lean_inc(v___y_3537_);
lean_inc_ref(v_post_3531_);
lean_inc_ref(v_pre_3530_);
v___f_3581_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3581_, 0, v_pre_3530_);
lean_closure_set(v___f_3581_, 1, v_post_3531_);
lean_closure_set(v___f_3581_, 2, v___x_3578_);
lean_closure_set(v___f_3581_, 3, v___x_3579_);
lean_closure_set(v___f_3581_, 4, v___x_3580_);
lean_closure_set(v___f_3581_, 5, v___x_3569_);
lean_closure_set(v___f_3581_, 6, v___y_3537_);
lean_closure_set(v___f_3581_, 7, v_b_3536_);
lean_closure_set(v___f_3581_, 8, v_a_3535_);
v___y_3544_ = v___f_3581_;
goto v___jp_3543_;
}
else
{
lean_object* v___x_3582_; lean_object* v___f_3583_; 
v___x_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3582_, 0, v_b_3536_);
v___f_3583_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3583_, 0, v___x_3582_);
v___y_3544_ = v___f_3583_;
goto v___jp_3543_;
}
}
}
v___jp_3543_:
{
lean_object* v___x_3545_; 
lean_inc(v___y_3541_);
lean_inc_ref(v___y_3540_);
lean_inc(v___y_3539_);
lean_inc_ref(v___y_3538_);
v___x_3545_ = lean_apply_5(v___y_3544_, v___y_3538_, v___y_3539_, v___y_3540_, v___y_3541_, lean_box(0));
if (lean_obj_tag(v___x_3545_) == 0)
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3558_; 
v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3548_ = v___x_3545_;
v_isShared_3549_ = v_isSharedCheck_3558_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3545_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3558_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
if (lean_obj_tag(v_a_3546_) == 0)
{
lean_object* v_a_3550_; lean_object* v___x_3552_; 
lean_dec(v_a_3535_);
lean_dec_ref(v_post_3531_);
lean_dec_ref(v_pre_3530_);
v_a_3550_ = lean_ctor_get(v_a_3546_, 0);
lean_inc(v_a_3550_);
lean_dec_ref(v_a_3546_);
if (v_isShared_3549_ == 0)
{
lean_ctor_set(v___x_3548_, 0, v_a_3550_);
v___x_3552_ = v___x_3548_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3550_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
else
{
lean_object* v_a_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; 
lean_del_object(v___x_3548_);
v_a_3554_ = lean_ctor_get(v_a_3546_, 0);
lean_inc(v_a_3554_);
lean_dec_ref(v_a_3546_);
v___x_3555_ = lean_unsigned_to_nat(1u);
v___x_3556_ = lean_nat_add(v_a_3535_, v___x_3555_);
lean_dec(v_a_3535_);
v_a_3535_ = v___x_3556_;
v_b_3536_ = v_a_3554_;
goto _start;
}
}
}
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_a_3535_);
lean_dec_ref(v_post_3531_);
lean_dec_ref(v_pre_3530_);
v_a_3559_ = lean_ctor_get(v___x_3545_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3545_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3545_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3545_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3564_; 
if (v_isShared_3562_ == 0)
{
v___x_3564_ = v___x_3561_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v_a_3559_);
v___x_3564_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
return v___x_3564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__9(uint8_t v_skipInstances_3584_, lean_object* v_pre_3585_, lean_object* v_post_3586_, uint8_t v_usedLetOnly_3587_, uint8_t v_skipConstInApp_3588_, lean_object* v_x_3589_, lean_object* v_x_3590_, lean_object* v_x_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_, lean_object* v___y_3595_, lean_object* v___y_3596_){
_start:
{
lean_object* v_f_3599_; lean_object* v___y_3600_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; 
if (lean_obj_tag(v_x_3589_) == 5)
{
lean_object* v_fn_3647_; lean_object* v_arg_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_fn_3647_ = lean_ctor_get(v_x_3589_, 0);
lean_inc_ref(v_fn_3647_);
v_arg_3648_ = lean_ctor_get(v_x_3589_, 1);
lean_inc_ref(v_arg_3648_);
lean_dec_ref(v_x_3589_);
v___x_3649_ = lean_array_set(v_x_3590_, v_x_3591_, v_arg_3648_);
v___x_3650_ = lean_unsigned_to_nat(1u);
v___x_3651_ = lean_nat_sub(v_x_3591_, v___x_3650_);
lean_dec(v_x_3591_);
v_x_3589_ = v_fn_3647_;
v_x_3590_ = v___x_3649_;
v_x_3591_ = v___x_3651_;
goto _start;
}
else
{
lean_dec(v_x_3591_);
if (v_skipConstInApp_3588_ == 0)
{
goto v___jp_3644_;
}
else
{
uint8_t v___x_3653_; 
v___x_3653_ = l_Lean_Expr_isConst(v_x_3589_);
if (v___x_3653_ == 0)
{
goto v___jp_3644_;
}
else
{
v_f_3599_ = v_x_3589_;
v___y_3600_ = v___y_3592_;
v___y_3601_ = v___y_3593_;
v___y_3602_ = v___y_3594_;
v___y_3603_ = v___y_3595_;
v___y_3604_ = v___y_3596_;
goto v___jp_3598_;
}
}
}
v___jp_3598_:
{
if (v_skipInstances_3584_ == 0)
{
size_t v_sz_3605_; size_t v___x_3606_; lean_object* v___x_3607_; 
v_sz_3605_ = lean_array_size(v_x_3590_);
v___x_3606_ = ((size_t)0ULL);
lean_inc_ref(v_post_3586_);
lean_inc_ref(v_pre_3585_);
v___x_3607_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__3(v_pre_3585_, v_post_3586_, v_usedLetOnly_3587_, v_skipConstInApp_3588_, v_skipInstances_3584_, v_sz_3605_, v___x_3606_, v_x_3590_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref(v___x_3607_);
v___x_3609_ = l_Lean_mkAppN(v_f_3599_, v_a_3608_);
lean_dec(v_a_3608_);
v___x_3610_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3585_, v_post_3586_, v_usedLetOnly_3587_, v_skipConstInApp_3588_, v_skipInstances_3584_, v___x_3609_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
return v___x_3610_;
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_post_3586_);
lean_dec_ref(v_pre_3585_);
v_a_3611_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3607_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3607_);
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
else
{
lean_object* v___x_3619_; lean_object* v___x_3620_; 
v___x_3619_ = lean_array_get_size(v_x_3590_);
lean_inc_ref(v_f_3599_);
v___x_3620_ = l_Lean_Meta_getFunInfoNArgs(v_f_3599_, v___x_3619_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3620_) == 0)
{
lean_object* v_a_3621_; lean_object* v_paramInfo_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; 
v_a_3621_ = lean_ctor_get(v___x_3620_, 0);
lean_inc(v_a_3621_);
lean_dec_ref(v___x_3620_);
v_paramInfo_3622_ = lean_ctor_get(v_a_3621_, 0);
lean_inc_ref(v_paramInfo_3622_);
lean_dec(v_a_3621_);
v___x_3623_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3586_);
lean_inc_ref(v_pre_3585_);
v___x_3624_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg(v___x_3619_, v_paramInfo_3622_, v_pre_3585_, v_post_3586_, v_usedLetOnly_3587_, v_skipConstInApp_3588_, v_skipInstances_3584_, v___x_3623_, v_x_3590_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
lean_dec_ref(v_paramInfo_3622_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref(v___x_3624_);
v___x_3626_ = l_Lean_mkAppN(v_f_3599_, v_a_3625_);
lean_dec(v_a_3625_);
v___x_3627_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3585_, v_post_3586_, v_usedLetOnly_3587_, v_skipConstInApp_3588_, v_skipInstances_3584_, v___x_3626_, v___y_3600_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
return v___x_3627_;
}
else
{
lean_object* v_a_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_post_3586_);
lean_dec_ref(v_pre_3585_);
v_a_3628_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3630_ = v___x_3624_;
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_a_3628_);
lean_dec(v___x_3624_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3635_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3633_; 
if (v_isShared_3631_ == 0)
{
v___x_3633_ = v___x_3630_;
goto v_reusejp_3632_;
}
else
{
lean_object* v_reuseFailAlloc_3634_; 
v_reuseFailAlloc_3634_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3634_, 0, v_a_3628_);
v___x_3633_ = v_reuseFailAlloc_3634_;
goto v_reusejp_3632_;
}
v_reusejp_3632_:
{
return v___x_3633_;
}
}
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_dec_ref(v_f_3599_);
lean_dec_ref(v_x_3590_);
lean_dec_ref(v_post_3586_);
lean_dec_ref(v_pre_3585_);
v_a_3636_ = lean_ctor_get(v___x_3620_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3620_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3620_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3620_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
v___jp_3644_:
{
lean_object* v___x_3645_; 
lean_inc_ref(v_post_3586_);
lean_inc_ref(v_pre_3585_);
v___x_3645_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3585_, v_post_3586_, v_usedLetOnly_3587_, v_skipConstInApp_3588_, v_skipInstances_3584_, v_x_3589_, v___y_3592_, v___y_3593_, v___y_3594_, v___y_3595_, v___y_3596_);
if (lean_obj_tag(v___x_3645_) == 0)
{
lean_object* v_a_3646_; 
v_a_3646_ = lean_ctor_get(v___x_3645_, 0);
lean_inc(v_a_3646_);
lean_dec_ref(v___x_3645_);
v_f_3599_ = v_a_3646_;
v___y_3600_ = v___y_3592_;
v___y_3601_ = v___y_3593_;
v___y_3602_ = v___y_3594_;
v___y_3603_ = v___y_3595_;
v___y_3604_ = v___y_3596_;
goto v___jp_3598_;
}
else
{
lean_dec_ref(v_x_3590_);
lean_dec_ref(v_post_3586_);
lean_dec_ref(v_pre_3585_);
return v___x_3645_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1(lean_object* v___x_3654_, lean_object* v_pre_3655_, lean_object* v_e_3656_, lean_object* v_post_3657_, uint8_t v_usedLetOnly_3658_, uint8_t v_skipConstInApp_3659_, uint8_t v_skipInstances_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
lean_object* v___x_3667_; 
v___x_3667_ = l_Lean_Core_checkSystem(v___x_3654_, v___y_3664_, v___y_3665_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v___x_3668_; 
lean_dec_ref(v___x_3667_);
lean_inc_ref(v_pre_3655_);
lean_inc(v___y_3665_);
lean_inc_ref(v___y_3664_);
lean_inc(v___y_3663_);
lean_inc_ref(v___y_3662_);
lean_inc_ref(v_e_3656_);
v___x_3668_ = lean_apply_6(v_pre_3655_, v_e_3656_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_, lean_box(0));
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3717_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3717_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3717_ == 0)
{
v___x_3671_ = v___x_3668_;
v_isShared_3672_ = v_isSharedCheck_3717_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3668_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3717_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___y_3674_; 
switch(lean_obj_tag(v_a_3669_))
{
case 0:
{
lean_object* v_e_3709_; lean_object* v___x_3711_; 
lean_dec_ref(v_post_3657_);
lean_dec_ref(v_e_3656_);
lean_dec_ref(v_pre_3655_);
v_e_3709_ = lean_ctor_get(v_a_3669_, 0);
lean_inc_ref(v_e_3709_);
lean_dec_ref(v_a_3669_);
if (v_isShared_3672_ == 0)
{
lean_ctor_set(v___x_3671_, 0, v_e_3709_);
v___x_3711_ = v___x_3671_;
goto v_reusejp_3710_;
}
else
{
lean_object* v_reuseFailAlloc_3712_; 
v_reuseFailAlloc_3712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3712_, 0, v_e_3709_);
v___x_3711_ = v_reuseFailAlloc_3712_;
goto v_reusejp_3710_;
}
v_reusejp_3710_:
{
return v___x_3711_;
}
}
case 1:
{
lean_object* v_e_3713_; lean_object* v___x_3714_; 
lean_del_object(v___x_3671_);
lean_dec_ref(v_e_3656_);
v_e_3713_ = lean_ctor_get(v_a_3669_, 0);
lean_inc_ref(v_e_3713_);
lean_dec_ref(v_a_3669_);
v___x_3714_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v_e_3713_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3714_;
}
default: 
{
lean_object* v_e_x3f_3715_; 
lean_del_object(v___x_3671_);
v_e_x3f_3715_ = lean_ctor_get(v_a_3669_, 0);
lean_inc(v_e_x3f_3715_);
lean_dec_ref(v_a_3669_);
if (lean_obj_tag(v_e_x3f_3715_) == 0)
{
v___y_3674_ = v_e_3656_;
goto v___jp_3673_;
}
else
{
lean_object* v_val_3716_; 
lean_dec_ref(v_e_3656_);
v_val_3716_ = lean_ctor_get(v_e_x3f_3715_, 0);
lean_inc(v_val_3716_);
lean_dec_ref(v_e_x3f_3715_);
v___y_3674_ = v_val_3716_;
goto v___jp_3673_;
}
}
}
v___jp_3673_:
{
switch(lean_obj_tag(v___y_3674_))
{
case 7:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; 
v___x_3675_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___closed__0));
v___x_3676_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v___x_3675_, v___y_3674_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3676_;
}
case 6:
{
lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3677_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___closed__0));
v___x_3678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v___x_3677_, v___y_3674_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3678_;
}
case 8:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; 
v___x_3679_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___closed__0));
v___x_3680_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v___x_3679_, v___y_3674_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3680_;
}
case 5:
{
lean_object* v_dummy_3681_; lean_object* v_nargs_3682_; lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3685_; lean_object* v___x_3686_; 
v_dummy_3681_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_3682_ = l_Lean_Expr_getAppNumArgs(v___y_3674_);
lean_inc(v_nargs_3682_);
v___x_3683_ = lean_mk_array(v_nargs_3682_, v_dummy_3681_);
v___x_3684_ = lean_unsigned_to_nat(1u);
v___x_3685_ = lean_nat_sub(v_nargs_3682_, v___x_3684_);
lean_dec(v_nargs_3682_);
v___x_3686_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__9(v_skipInstances_3660_, v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v___y_3674_, v___x_3683_, v___x_3685_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3686_;
}
case 10:
{
lean_object* v_data_3687_; lean_object* v_expr_3688_; lean_object* v___x_3689_; 
v_data_3687_ = lean_ctor_get(v___y_3674_, 0);
v_expr_3688_ = lean_ctor_get(v___y_3674_, 1);
lean_inc_ref(v_expr_3688_);
lean_inc_ref(v_post_3657_);
lean_inc_ref(v_pre_3655_);
v___x_3689_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v_expr_3688_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
if (lean_obj_tag(v___x_3689_) == 0)
{
lean_object* v_a_3690_; size_t v___x_3691_; size_t v___x_3692_; uint8_t v___x_3693_; 
v_a_3690_ = lean_ctor_get(v___x_3689_, 0);
lean_inc(v_a_3690_);
lean_dec_ref(v___x_3689_);
v___x_3691_ = lean_ptr_addr(v_expr_3688_);
v___x_3692_ = lean_ptr_addr(v_a_3690_);
v___x_3693_ = lean_usize_dec_eq(v___x_3691_, v___x_3692_);
if (v___x_3693_ == 0)
{
lean_object* v___x_3694_; lean_object* v___x_3695_; 
lean_inc(v_data_3687_);
lean_dec_ref(v___y_3674_);
v___x_3694_ = l_Lean_Expr_mdata___override(v_data_3687_, v_a_3690_);
v___x_3695_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v___x_3694_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3695_;
}
else
{
lean_object* v___x_3696_; 
lean_dec(v_a_3690_);
v___x_3696_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v___y_3674_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3696_;
}
}
else
{
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_post_3657_);
lean_dec_ref(v_pre_3655_);
return v___x_3689_;
}
}
case 11:
{
lean_object* v_typeName_3697_; lean_object* v_idx_3698_; lean_object* v_struct_3699_; lean_object* v___x_3700_; 
v_typeName_3697_ = lean_ctor_get(v___y_3674_, 0);
v_idx_3698_ = lean_ctor_get(v___y_3674_, 1);
v_struct_3699_ = lean_ctor_get(v___y_3674_, 2);
lean_inc_ref(v_struct_3699_);
lean_inc_ref(v_post_3657_);
lean_inc_ref(v_pre_3655_);
v___x_3700_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v_struct_3699_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
if (lean_obj_tag(v___x_3700_) == 0)
{
lean_object* v_a_3701_; size_t v___x_3702_; size_t v___x_3703_; uint8_t v___x_3704_; 
v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
lean_inc(v_a_3701_);
lean_dec_ref(v___x_3700_);
v___x_3702_ = lean_ptr_addr(v_struct_3699_);
v___x_3703_ = lean_ptr_addr(v_a_3701_);
v___x_3704_ = lean_usize_dec_eq(v___x_3702_, v___x_3703_);
if (v___x_3704_ == 0)
{
lean_object* v___x_3705_; lean_object* v___x_3706_; 
lean_inc(v_idx_3698_);
lean_inc(v_typeName_3697_);
lean_dec_ref(v___y_3674_);
v___x_3705_ = l_Lean_Expr_proj___override(v_typeName_3697_, v_idx_3698_, v_a_3701_);
v___x_3706_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v___x_3705_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3706_;
}
else
{
lean_object* v___x_3707_; 
lean_dec(v_a_3701_);
v___x_3707_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v___y_3674_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3707_;
}
}
else
{
lean_dec_ref(v___y_3674_);
lean_dec_ref(v_post_3657_);
lean_dec_ref(v_pre_3655_);
return v___x_3700_;
}
}
default: 
{
lean_object* v___x_3708_; 
v___x_3708_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3655_, v_post_3657_, v_usedLetOnly_3658_, v_skipConstInApp_3659_, v_skipInstances_3660_, v___y_3674_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
return v___x_3708_;
}
}
}
}
}
else
{
lean_object* v_a_3718_; lean_object* v___x_3720_; uint8_t v_isShared_3721_; uint8_t v_isSharedCheck_3725_; 
lean_dec_ref(v_post_3657_);
lean_dec_ref(v_e_3656_);
lean_dec_ref(v_pre_3655_);
v_a_3718_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3725_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3725_ == 0)
{
v___x_3720_ = v___x_3668_;
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
else
{
lean_inc(v_a_3718_);
lean_dec(v___x_3668_);
v___x_3720_ = lean_box(0);
v_isShared_3721_ = v_isSharedCheck_3725_;
goto v_resetjp_3719_;
}
v_resetjp_3719_:
{
lean_object* v___x_3723_; 
if (v_isShared_3721_ == 0)
{
v___x_3723_ = v___x_3720_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v_a_3718_);
v___x_3723_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
return v___x_3723_;
}
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_dec_ref(v_post_3657_);
lean_dec_ref(v_e_3656_);
lean_dec_ref(v_pre_3655_);
v_a_3726_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3667_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3667_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___boxed(lean_object* v___x_3734_, lean_object* v_pre_3735_, lean_object* v_e_3736_, lean_object* v_post_3737_, lean_object* v_usedLetOnly_3738_, lean_object* v_skipConstInApp_3739_, lean_object* v_skipInstances_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
uint8_t v_usedLetOnly_boxed_3747_; uint8_t v_skipConstInApp_boxed_3748_; uint8_t v_skipInstances_boxed_3749_; lean_object* v_res_3750_; 
v_usedLetOnly_boxed_3747_ = lean_unbox(v_usedLetOnly_3738_);
v_skipConstInApp_boxed_3748_ = lean_unbox(v_skipConstInApp_3739_);
v_skipInstances_boxed_3749_ = lean_unbox(v_skipInstances_3740_);
v_res_3750_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1(v___x_3734_, v_pre_3735_, v_e_3736_, v_post_3737_, v_usedLetOnly_boxed_3747_, v_skipConstInApp_boxed_3748_, v_skipInstances_boxed_3749_, v___y_3741_, v___y_3742_, v___y_3743_, v___y_3744_, v___y_3745_);
lean_dec(v___y_3745_);
lean_dec_ref(v___y_3744_);
lean_dec(v___y_3743_);
lean_dec_ref(v___y_3742_);
lean_dec(v___y_3741_);
return v_res_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(lean_object* v_pre_3751_, lean_object* v_post_3752_, uint8_t v_usedLetOnly_3753_, uint8_t v_skipConstInApp_3754_, uint8_t v_skipInstances_3755_, lean_object* v_e_3756_, lean_object* v_a_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_, lean_object* v___y_3760_, lean_object* v___y_3761_){
_start:
{
lean_object* v___x_3763_; lean_object* v___x_3764_; 
lean_inc(v_a_3757_);
v___x_3763_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3763_, 0, lean_box(0));
lean_closure_set(v___x_3763_, 1, lean_box(0));
lean_closure_set(v___x_3763_, 2, v_a_3757_);
v___x_3764_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_box(0), v___x_3763_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3799_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3767_ = v___x_3764_;
v_isShared_3768_ = v_isSharedCheck_3799_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3764_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3799_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3769_; 
v___x_3769_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_3765_, v_e_3756_);
lean_dec(v_a_3765_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___f_3774_; lean_object* v___x_3775_; 
lean_del_object(v___x_3767_);
v___x_3770_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
v___x_3771_ = lean_box(v_usedLetOnly_3753_);
v___x_3772_ = lean_box(v_skipConstInApp_3754_);
v___x_3773_ = lean_box(v_skipInstances_3755_);
lean_inc_ref(v_e_3756_);
v___f_3774_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___boxed), 13, 7);
lean_closure_set(v___f_3774_, 0, v___x_3770_);
lean_closure_set(v___f_3774_, 1, v_pre_3751_);
lean_closure_set(v___f_3774_, 2, v_e_3756_);
lean_closure_set(v___f_3774_, 3, v_post_3752_);
lean_closure_set(v___f_3774_, 4, v___x_3771_);
lean_closure_set(v___f_3774_, 5, v___x_3772_);
lean_closure_set(v___f_3774_, 6, v___x_3773_);
v___x_3775_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg(v___f_3774_, v_a_3757_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___f_3777_; lean_object* v___x_3778_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
lean_inc_n(v_a_3776_, 2);
lean_dec_ref(v___x_3775_);
lean_inc(v_a_3757_);
v___f_3777_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3777_, 0, v_a_3757_);
lean_closure_set(v___f_3777_, 1, v_e_3756_);
lean_closure_set(v___f_3777_, 2, v_a_3776_);
v___x_3778_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_box(0), v___f_3777_, v___y_3758_, v___y_3759_, v___y_3760_, v___y_3761_);
if (lean_obj_tag(v___x_3778_) == 0)
{
lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3785_; 
v_isSharedCheck_3785_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3785_ == 0)
{
lean_object* v_unused_3786_; 
v_unused_3786_ = lean_ctor_get(v___x_3778_, 0);
lean_dec(v_unused_3786_);
v___x_3780_ = v___x_3778_;
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
else
{
lean_dec(v___x_3778_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3785_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3783_; 
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v_a_3776_);
v___x_3783_ = v___x_3780_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v_a_3776_);
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
lean_object* v_a_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3794_; 
lean_dec(v_a_3776_);
v_a_3787_ = lean_ctor_get(v___x_3778_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v___x_3778_);
if (v_isSharedCheck_3794_ == 0)
{
v___x_3789_ = v___x_3778_;
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_a_3787_);
lean_dec(v___x_3778_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3794_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3792_; 
if (v_isShared_3790_ == 0)
{
v___x_3792_ = v___x_3789_;
goto v_reusejp_3791_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_a_3787_);
v___x_3792_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3791_;
}
v_reusejp_3791_:
{
return v___x_3792_;
}
}
}
}
else
{
lean_dec_ref(v_e_3756_);
return v___x_3775_;
}
}
else
{
lean_object* v_val_3795_; lean_object* v___x_3797_; 
lean_dec_ref(v_e_3756_);
lean_dec_ref(v_post_3752_);
lean_dec_ref(v_pre_3751_);
v_val_3795_ = lean_ctor_get(v___x_3769_, 0);
lean_inc(v_val_3795_);
lean_dec_ref(v___x_3769_);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v_val_3795_);
v___x_3797_ = v___x_3767_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_val_3795_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec_ref(v_e_3756_);
lean_dec_ref(v_post_3752_);
lean_dec_ref(v_pre_3751_);
v_a_3800_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3764_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3764_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___lam__0___boxed(lean_object* v_fvars_3808_, lean_object* v_pre_3809_, lean_object* v_post_3810_, lean_object* v_usedLetOnly_3811_, lean_object* v_skipConstInApp_3812_, lean_object* v_skipInstances_3813_, lean_object* v_body_3814_, lean_object* v_x_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
uint8_t v_usedLetOnly_boxed_3822_; uint8_t v_skipConstInApp_boxed_3823_; uint8_t v_skipInstances_boxed_3824_; lean_object* v_res_3825_; 
v_usedLetOnly_boxed_3822_ = lean_unbox(v_usedLetOnly_3811_);
v_skipConstInApp_boxed_3823_ = lean_unbox(v_skipConstInApp_3812_);
v_skipInstances_boxed_3824_ = lean_unbox(v_skipInstances_3813_);
v_res_3825_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___lam__0(v_fvars_3808_, v_pre_3809_, v_post_3810_, v_usedLetOnly_boxed_3822_, v_skipConstInApp_boxed_3823_, v_skipInstances_boxed_3824_, v_body_3814_, v_x_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6(lean_object* v_pre_3826_, lean_object* v_post_3827_, uint8_t v_usedLetOnly_3828_, uint8_t v_skipConstInApp_3829_, uint8_t v_skipInstances_3830_, lean_object* v_fvars_3831_, lean_object* v_e_3832_, lean_object* v_a_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
if (lean_obj_tag(v_e_3832_) == 7)
{
lean_object* v_binderName_3839_; lean_object* v_binderType_3840_; lean_object* v_body_3841_; uint8_t v_binderInfo_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; 
v_binderName_3839_ = lean_ctor_get(v_e_3832_, 0);
lean_inc(v_binderName_3839_);
v_binderType_3840_ = lean_ctor_get(v_e_3832_, 1);
lean_inc_ref(v_binderType_3840_);
v_body_3841_ = lean_ctor_get(v_e_3832_, 2);
lean_inc_ref(v_body_3841_);
v_binderInfo_3842_ = lean_ctor_get_uint8(v_e_3832_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3832_);
v___x_3843_ = lean_expr_instantiate_rev(v_binderType_3840_, v_fvars_3831_);
lean_dec_ref(v_binderType_3840_);
lean_inc_ref(v_post_3827_);
lean_inc_ref(v_pre_3826_);
v___x_3844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3826_, v_post_3827_, v_usedLetOnly_3828_, v_skipConstInApp_3829_, v_skipInstances_3830_, v___x_3843_, v_a_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___f_3849_; uint8_t v___x_3850_; lean_object* v___x_3851_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref(v___x_3844_);
v___x_3846_ = lean_box(v_usedLetOnly_3828_);
v___x_3847_ = lean_box(v_skipConstInApp_3829_);
v___x_3848_ = lean_box(v_skipInstances_3830_);
v___f_3849_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3849_, 0, v_fvars_3831_);
lean_closure_set(v___f_3849_, 1, v_pre_3826_);
lean_closure_set(v___f_3849_, 2, v_post_3827_);
lean_closure_set(v___f_3849_, 3, v___x_3846_);
lean_closure_set(v___f_3849_, 4, v___x_3847_);
lean_closure_set(v___f_3849_, 5, v___x_3848_);
lean_closure_set(v___f_3849_, 6, v_body_3841_);
v___x_3850_ = 0;
v___x_3851_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(v_binderName_3839_, v_binderInfo_3842_, v_a_3845_, v___f_3849_, v___x_3850_, v_a_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
return v___x_3851_;
}
else
{
lean_dec_ref(v_body_3841_);
lean_dec(v_binderName_3839_);
lean_dec_ref(v_fvars_3831_);
lean_dec_ref(v_post_3827_);
lean_dec_ref(v_pre_3826_);
return v___x_3844_;
}
}
else
{
lean_object* v___x_3852_; lean_object* v___x_3853_; 
v___x_3852_ = lean_expr_instantiate_rev(v_e_3832_, v_fvars_3831_);
lean_dec_ref(v_e_3832_);
lean_inc_ref(v_post_3827_);
lean_inc_ref(v_pre_3826_);
v___x_3853_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3826_, v_post_3827_, v_usedLetOnly_3828_, v_skipConstInApp_3829_, v_skipInstances_3830_, v___x_3852_, v_a_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
if (lean_obj_tag(v___x_3853_) == 0)
{
lean_object* v_a_3854_; uint8_t v___x_3855_; uint8_t v___x_3856_; uint8_t v___x_3857_; lean_object* v___x_3858_; 
v_a_3854_ = lean_ctor_get(v___x_3853_, 0);
lean_inc(v_a_3854_);
lean_dec_ref(v___x_3853_);
v___x_3855_ = 0;
v___x_3856_ = 1;
v___x_3857_ = 1;
v___x_3858_ = l_Lean_Meta_mkForallFVars(v_fvars_3831_, v_a_3854_, v___x_3855_, v_usedLetOnly_3828_, v___x_3856_, v___x_3857_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec_ref(v_fvars_3831_);
if (lean_obj_tag(v___x_3858_) == 0)
{
lean_object* v_a_3859_; lean_object* v___x_3860_; 
v_a_3859_ = lean_ctor_get(v___x_3858_, 0);
lean_inc(v_a_3859_);
lean_dec_ref(v___x_3858_);
v___x_3860_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3826_, v_post_3827_, v_usedLetOnly_3828_, v_skipConstInApp_3829_, v_skipInstances_3830_, v_a_3859_, v_a_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
return v___x_3860_;
}
else
{
lean_dec_ref(v_post_3827_);
lean_dec_ref(v_pre_3826_);
return v___x_3858_;
}
}
else
{
lean_dec_ref(v_fvars_3831_);
lean_dec_ref(v_post_3827_);
lean_dec_ref(v_pre_3826_);
return v___x_3853_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___lam__0(lean_object* v_fvars_3861_, lean_object* v_pre_3862_, lean_object* v_post_3863_, uint8_t v_usedLetOnly_3864_, uint8_t v_skipConstInApp_3865_, uint8_t v_skipInstances_3866_, lean_object* v_body_3867_, lean_object* v_x_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_array_push(v_fvars_3861_, v_x_3868_);
v___x_3876_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6(v_pre_3862_, v_post_3863_, v_usedLetOnly_3864_, v_skipConstInApp_3865_, v_skipInstances_3866_, v___x_3875_, v_body_3867_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
return v___x_3876_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4___boxed(lean_object* v_pre_3877_, lean_object* v_post_3878_, lean_object* v_usedLetOnly_3879_, lean_object* v_skipConstInApp_3880_, lean_object* v_skipInstances_3881_, lean_object* v_e_3882_, lean_object* v_a_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_){
_start:
{
uint8_t v_usedLetOnly_boxed_3889_; uint8_t v_skipConstInApp_boxed_3890_; uint8_t v_skipInstances_boxed_3891_; lean_object* v_res_3892_; 
v_usedLetOnly_boxed_3889_ = lean_unbox(v_usedLetOnly_3879_);
v_skipConstInApp_boxed_3890_ = lean_unbox(v_skipConstInApp_3880_);
v_skipInstances_boxed_3891_ = lean_unbox(v_skipInstances_3881_);
v_res_3892_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3877_, v_post_3878_, v_usedLetOnly_boxed_3889_, v_skipConstInApp_boxed_3890_, v_skipInstances_boxed_3891_, v_e_3882_, v_a_3883_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
lean_dec(v___y_3887_);
lean_dec_ref(v___y_3886_);
lean_dec(v___y_3885_);
lean_dec_ref(v___y_3884_);
lean_dec(v_a_3883_);
return v_res_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__3___boxed(lean_object* v_pre_3893_, lean_object* v_post_3894_, lean_object* v_usedLetOnly_3895_, lean_object* v_skipConstInApp_3896_, lean_object* v_skipInstances_3897_, lean_object* v_sz_3898_, lean_object* v_i_3899_, lean_object* v_bs_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
uint8_t v_usedLetOnly_boxed_3907_; uint8_t v_skipConstInApp_boxed_3908_; uint8_t v_skipInstances_boxed_3909_; size_t v_sz_boxed_3910_; size_t v_i_boxed_3911_; lean_object* v_res_3912_; 
v_usedLetOnly_boxed_3907_ = lean_unbox(v_usedLetOnly_3895_);
v_skipConstInApp_boxed_3908_ = lean_unbox(v_skipConstInApp_3896_);
v_skipInstances_boxed_3909_ = lean_unbox(v_skipInstances_3897_);
v_sz_boxed_3910_ = lean_unbox_usize(v_sz_3898_);
lean_dec(v_sz_3898_);
v_i_boxed_3911_ = lean_unbox_usize(v_i_3899_);
lean_dec(v_i_3899_);
v_res_3912_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__3(v_pre_3893_, v_post_3894_, v_usedLetOnly_boxed_3907_, v_skipConstInApp_boxed_3908_, v_skipInstances_boxed_3909_, v_sz_boxed_3910_, v_i_boxed_3911_, v_bs_3900_, v___y_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
return v_res_3912_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___boxed(lean_object* v_pre_3913_, lean_object* v_post_3914_, lean_object* v_usedLetOnly_3915_, lean_object* v_skipConstInApp_3916_, lean_object* v_skipInstances_3917_, lean_object* v_e_3918_, lean_object* v_a_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
uint8_t v_usedLetOnly_boxed_3925_; uint8_t v_skipConstInApp_boxed_3926_; uint8_t v_skipInstances_boxed_3927_; lean_object* v_res_3928_; 
v_usedLetOnly_boxed_3925_ = lean_unbox(v_usedLetOnly_3915_);
v_skipConstInApp_boxed_3926_ = lean_unbox(v_skipConstInApp_3916_);
v_skipInstances_boxed_3927_ = lean_unbox(v_skipInstances_3917_);
v_res_3928_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3913_, v_post_3914_, v_usedLetOnly_boxed_3925_, v_skipConstInApp_boxed_3926_, v_skipInstances_boxed_3927_, v_e_3918_, v_a_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v___y_3921_);
lean_dec_ref(v___y_3920_);
lean_dec(v_a_3919_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___boxed(lean_object* v_pre_3929_, lean_object* v_post_3930_, lean_object* v_usedLetOnly_3931_, lean_object* v_skipConstInApp_3932_, lean_object* v_skipInstances_3933_, lean_object* v_fvars_3934_, lean_object* v_e_3935_, lean_object* v_a_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_){
_start:
{
uint8_t v_usedLetOnly_boxed_3942_; uint8_t v_skipConstInApp_boxed_3943_; uint8_t v_skipInstances_boxed_3944_; lean_object* v_res_3945_; 
v_usedLetOnly_boxed_3942_ = lean_unbox(v_usedLetOnly_3931_);
v_skipConstInApp_boxed_3943_ = lean_unbox(v_skipConstInApp_3932_);
v_skipInstances_boxed_3944_ = lean_unbox(v_skipInstances_3933_);
v_res_3945_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6(v_pre_3929_, v_post_3930_, v_usedLetOnly_boxed_3942_, v_skipConstInApp_boxed_3943_, v_skipInstances_boxed_3944_, v_fvars_3934_, v_e_3935_, v_a_3936_, v___y_3937_, v___y_3938_, v___y_3939_, v___y_3940_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v___y_3938_);
lean_dec_ref(v___y_3937_);
lean_dec(v_a_3936_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___boxed(lean_object* v_pre_3946_, lean_object* v_post_3947_, lean_object* v_usedLetOnly_3948_, lean_object* v_skipConstInApp_3949_, lean_object* v_skipInstances_3950_, lean_object* v_fvars_3951_, lean_object* v_e_3952_, lean_object* v_a_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
uint8_t v_usedLetOnly_boxed_3959_; uint8_t v_skipConstInApp_boxed_3960_; uint8_t v_skipInstances_boxed_3961_; lean_object* v_res_3962_; 
v_usedLetOnly_boxed_3959_ = lean_unbox(v_usedLetOnly_3948_);
v_skipConstInApp_boxed_3960_ = lean_unbox(v_skipConstInApp_3949_);
v_skipInstances_boxed_3961_ = lean_unbox(v_skipInstances_3950_);
v_res_3962_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7(v_pre_3946_, v_post_3947_, v_usedLetOnly_boxed_3959_, v_skipConstInApp_boxed_3960_, v_skipInstances_boxed_3961_, v_fvars_3951_, v_e_3952_, v_a_3953_, v___y_3954_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
lean_dec_ref(v___y_3954_);
lean_dec(v_a_3953_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___boxed(lean_object* v_pre_3963_, lean_object* v_post_3964_, lean_object* v_usedLetOnly_3965_, lean_object* v_skipConstInApp_3966_, lean_object* v_skipInstances_3967_, lean_object* v_fvars_3968_, lean_object* v_e_3969_, lean_object* v_a_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_, lean_object* v___y_3974_, lean_object* v___y_3975_){
_start:
{
uint8_t v_usedLetOnly_boxed_3976_; uint8_t v_skipConstInApp_boxed_3977_; uint8_t v_skipInstances_boxed_3978_; lean_object* v_res_3979_; 
v_usedLetOnly_boxed_3976_ = lean_unbox(v_usedLetOnly_3965_);
v_skipConstInApp_boxed_3977_ = lean_unbox(v_skipConstInApp_3966_);
v_skipInstances_boxed_3978_ = lean_unbox(v_skipInstances_3967_);
v_res_3979_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8(v_pre_3963_, v_post_3964_, v_usedLetOnly_boxed_3976_, v_skipConstInApp_boxed_3977_, v_skipInstances_boxed_3978_, v_fvars_3968_, v_e_3969_, v_a_3970_, v___y_3971_, v___y_3972_, v___y_3973_, v___y_3974_);
lean_dec(v___y_3974_);
lean_dec_ref(v___y_3973_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v_a_3970_);
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_upperBound_3980_, lean_object* v___x_3981_, lean_object* v_pre_3982_, lean_object* v_post_3983_, lean_object* v_usedLetOnly_3984_, lean_object* v_skipConstInApp_3985_, lean_object* v_skipInstances_3986_, lean_object* v_a_3987_, lean_object* v_b_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_, lean_object* v___y_3993_, lean_object* v___y_3994_){
_start:
{
uint8_t v_usedLetOnly_boxed_3995_; uint8_t v_skipConstInApp_boxed_3996_; uint8_t v_skipInstances_boxed_3997_; lean_object* v_res_3998_; 
v_usedLetOnly_boxed_3995_ = lean_unbox(v_usedLetOnly_3984_);
v_skipConstInApp_boxed_3996_ = lean_unbox(v_skipConstInApp_3985_);
v_skipInstances_boxed_3997_ = lean_unbox(v_skipInstances_3986_);
v_res_3998_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg(v_upperBound_3980_, v___x_3981_, v_pre_3982_, v_post_3983_, v_usedLetOnly_boxed_3995_, v_skipConstInApp_boxed_3996_, v_skipInstances_boxed_3997_, v_a_3987_, v_b_3988_, v___y_3989_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
lean_dec(v___y_3993_);
lean_dec_ref(v___y_3992_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
lean_dec_ref(v___x_3981_);
lean_dec(v_upperBound_3980_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__9___boxed(lean_object* v_skipInstances_3999_, lean_object* v_pre_4000_, lean_object* v_post_4001_, lean_object* v_usedLetOnly_4002_, lean_object* v_skipConstInApp_4003_, lean_object* v_x_4004_, lean_object* v_x_4005_, lean_object* v_x_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
uint8_t v_skipInstances_boxed_4013_; uint8_t v_usedLetOnly_boxed_4014_; uint8_t v_skipConstInApp_boxed_4015_; lean_object* v_res_4016_; 
v_skipInstances_boxed_4013_ = lean_unbox(v_skipInstances_3999_);
v_usedLetOnly_boxed_4014_ = lean_unbox(v_usedLetOnly_4002_);
v_skipConstInApp_boxed_4015_ = lean_unbox(v_skipConstInApp_4003_);
v_res_4016_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__9(v_skipInstances_boxed_4013_, v_pre_4000_, v_post_4001_, v_usedLetOnly_boxed_4014_, v_skipConstInApp_boxed_4015_, v_x_4004_, v_x_4005_, v_x_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_object* v_00_u03b1_4017_, lean_object* v_x_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v___x_4024_; lean_object* v___x_4025_; 
v___x_4024_ = lean_apply_1(v_x_4018_, lean_box(0));
v___x_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4024_);
return v___x_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0___boxed(lean_object* v_00_u03b1_4026_, lean_object* v_x_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v_res_4033_; 
v_res_4033_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(v_00_u03b1_4026_, v_x_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
lean_dec(v___y_4029_);
lean_dec_ref(v___y_4028_);
return v_res_4033_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1(lean_object* v_input_4034_, lean_object* v_pre_4035_, lean_object* v_post_4036_, uint8_t v_usedLetOnly_4037_, uint8_t v_skipConstInApp_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_){
_start:
{
lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v_a_4046_; uint8_t v___x_4047_; lean_object* v___x_4048_; 
v___x_4044_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_4045_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_box(0), v___x_4044_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
lean_inc(v_a_4046_);
lean_dec_ref(v___x_4045_);
v___x_4047_ = 0;
v___x_4048_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_4035_, v_post_4036_, v_usedLetOnly_4037_, v_skipConstInApp_4038_, v___x_4047_, v_input_4034_, v_a_4046_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4058_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4049_);
lean_dec_ref(v___x_4048_);
v___x_4050_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4050_, 0, lean_box(0));
lean_closure_set(v___x_4050_, 1, lean_box(0));
lean_closure_set(v___x_4050_, 2, v_a_4046_);
v___x_4051_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_box(0), v___x_4050_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
v_isSharedCheck_4058_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4058_ == 0)
{
lean_object* v_unused_4059_; 
v_unused_4059_ = lean_ctor_get(v___x_4051_, 0);
lean_dec(v_unused_4059_);
v___x_4053_ = v___x_4051_;
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
else
{
lean_dec(v___x_4051_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4058_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v___x_4056_; 
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v_a_4049_);
v___x_4056_ = v___x_4053_;
goto v_reusejp_4055_;
}
else
{
lean_object* v_reuseFailAlloc_4057_; 
v_reuseFailAlloc_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4057_, 0, v_a_4049_);
v___x_4056_ = v_reuseFailAlloc_4057_;
goto v_reusejp_4055_;
}
v_reusejp_4055_:
{
return v___x_4056_;
}
}
}
else
{
lean_dec(v_a_4046_);
return v___x_4048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___boxed(lean_object* v_input_4060_, lean_object* v_pre_4061_, lean_object* v_post_4062_, lean_object* v_usedLetOnly_4063_, lean_object* v_skipConstInApp_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
uint8_t v_usedLetOnly_boxed_4070_; uint8_t v_skipConstInApp_boxed_4071_; lean_object* v_res_4072_; 
v_usedLetOnly_boxed_4070_ = lean_unbox(v_usedLetOnly_4063_);
v_skipConstInApp_boxed_4071_ = lean_unbox(v_skipConstInApp_4064_);
v_res_4072_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1(v_input_4060_, v_pre_4061_, v_post_4062_, v_usedLetOnly_boxed_4070_, v_skipConstInApp_boxed_4071_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec(v___y_4066_);
lean_dec_ref(v___y_4065_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object* v_e_4076_, lean_object* v_a_4077_, lean_object* v_a_4078_, lean_object* v_a_4079_, lean_object* v_a_4080_){
_start:
{
lean_object* v___f_4082_; lean_object* v___x_4083_; 
v___f_4082_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__0));
v___x_4083_ = lean_find_expr(v___f_4082_, v_e_4076_);
if (lean_obj_tag(v___x_4083_) == 0)
{
lean_object* v___x_4084_; 
v___x_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4084_, 0, v_e_4076_);
return v___x_4084_;
}
else
{
lean_object* v_post_4085_; lean_object* v___f_4086_; uint8_t v___x_4087_; lean_object* v___x_4088_; 
lean_dec_ref(v___x_4083_);
v_post_4085_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__1));
v___f_4086_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__2));
v___x_4087_ = 0;
v___x_4088_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1(v_e_4076_, v___f_4086_, v_post_4085_, v___x_4087_, v___x_4087_, v_a_4077_, v_a_4078_, v_a_4079_, v_a_4080_);
return v___x_4088_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object* v_e_4089_, lean_object* v_a_4090_, lean_object* v_a_4091_, lean_object* v_a_4092_, lean_object* v_a_4093_, lean_object* v_a_4094_){
_start:
{
lean_object* v_res_4095_; 
v_res_4095_ = l_Lean_Meta_Grind_foldProjs(v_e_4089_, v_a_4090_, v_a_4091_, v_a_4092_, v_a_4093_);
lean_dec(v_a_4093_);
lean_dec_ref(v_a_4092_);
lean_dec(v_a_4091_);
lean_dec_ref(v_a_4090_);
return v_res_4095_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5(lean_object* v_upperBound_4096_, lean_object* v___x_4097_, lean_object* v_pre_4098_, lean_object* v_post_4099_, uint8_t v_usedLetOnly_4100_, uint8_t v_skipConstInApp_4101_, uint8_t v_skipInstances_4102_, lean_object* v___x_4103_, lean_object* v_inst_4104_, lean_object* v_R_4105_, lean_object* v_a_4106_, lean_object* v_b_4107_, lean_object* v_c_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v___x_4115_; 
v___x_4115_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg(v_upperBound_4096_, v___x_4097_, v_pre_4098_, v_post_4099_, v_usedLetOnly_4100_, v_skipConstInApp_4101_, v_skipInstances_4102_, v_a_4106_, v_b_4107_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_4116_ = _args[0];
lean_object* v___x_4117_ = _args[1];
lean_object* v_pre_4118_ = _args[2];
lean_object* v_post_4119_ = _args[3];
lean_object* v_usedLetOnly_4120_ = _args[4];
lean_object* v_skipConstInApp_4121_ = _args[5];
lean_object* v_skipInstances_4122_ = _args[6];
lean_object* v___x_4123_ = _args[7];
lean_object* v_inst_4124_ = _args[8];
lean_object* v_R_4125_ = _args[9];
lean_object* v_a_4126_ = _args[10];
lean_object* v_b_4127_ = _args[11];
lean_object* v_c_4128_ = _args[12];
lean_object* v___y_4129_ = _args[13];
lean_object* v___y_4130_ = _args[14];
lean_object* v___y_4131_ = _args[15];
lean_object* v___y_4132_ = _args[16];
lean_object* v___y_4133_ = _args[17];
lean_object* v___y_4134_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4135_; uint8_t v_skipConstInApp_boxed_4136_; uint8_t v_skipInstances_boxed_4137_; lean_object* v_res_4138_; 
v_usedLetOnly_boxed_4135_ = lean_unbox(v_usedLetOnly_4120_);
v_skipConstInApp_boxed_4136_ = lean_unbox(v_skipConstInApp_4121_);
v_skipInstances_boxed_4137_ = lean_unbox(v_skipInstances_4122_);
v_res_4138_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5(v_upperBound_4116_, v___x_4117_, v_pre_4118_, v_post_4119_, v_usedLetOnly_boxed_4135_, v_skipConstInApp_boxed_4136_, v_skipInstances_boxed_4137_, v___x_4123_, v_inst_4124_, v_R_4125_, v_a_4126_, v_b_4127_, v_c_4128_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_);
lean_dec(v___y_4133_);
lean_dec_ref(v___y_4132_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec(v___x_4123_);
lean_dec_ref(v___x_4117_);
lean_dec(v_upperBound_4116_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7(lean_object* v_00_u03b1_4139_, lean_object* v_name_4140_, uint8_t v_bi_4141_, lean_object* v_type_4142_, lean_object* v_k_4143_, uint8_t v_kind_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_, lean_object* v___y_4149_){
_start:
{
lean_object* v___x_4151_; 
v___x_4151_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(v_name_4140_, v_bi_4141_, v_type_4142_, v_k_4143_, v_kind_4144_, v___y_4145_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4152_, lean_object* v_name_4153_, lean_object* v_bi_4154_, lean_object* v_type_4155_, lean_object* v_k_4156_, lean_object* v_kind_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_){
_start:
{
uint8_t v_bi_boxed_4164_; uint8_t v_kind_boxed_4165_; lean_object* v_res_4166_; 
v_bi_boxed_4164_ = lean_unbox(v_bi_4154_);
v_kind_boxed_4165_ = lean_unbox(v_kind_4157_);
v_res_4166_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7(v_00_u03b1_4152_, v_name_4153_, v_bi_boxed_4164_, v_type_4155_, v_k_4156_, v_kind_boxed_4165_, v___y_4158_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
return v_res_4166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10(lean_object* v_00_u03b1_4167_, lean_object* v_name_4168_, lean_object* v_type_4169_, lean_object* v_val_4170_, lean_object* v_k_4171_, uint8_t v_nondep_4172_, uint8_t v_kind_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v___x_4180_; 
v___x_4180_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg(v_name_4168_, v_type_4169_, v_val_4170_, v_k_4171_, v_nondep_4172_, v_kind_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
return v___x_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4181_, lean_object* v_name_4182_, lean_object* v_type_4183_, lean_object* v_val_4184_, lean_object* v_k_4185_, lean_object* v_nondep_4186_, lean_object* v_kind_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
uint8_t v_nondep_boxed_4194_; uint8_t v_kind_boxed_4195_; lean_object* v_res_4196_; 
v_nondep_boxed_4194_ = lean_unbox(v_nondep_4186_);
v_kind_boxed_4195_ = lean_unbox(v_kind_4187_);
v_res_4196_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10(v_00_u03b1_4181_, v_name_4182_, v_type_4183_, v_val_4184_, v_k_4185_, v_nondep_boxed_4194_, v_kind_boxed_4195_, v___y_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
lean_dec(v___y_4188_);
return v_res_4196_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13(lean_object* v_00_u03b1_4197_, lean_object* v_ref_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_, lean_object* v___y_4201_, lean_object* v___y_4202_){
_start:
{
lean_object* v___x_4204_; 
v___x_4204_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg(v_ref_4198_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___boxed(lean_object* v_00_u03b1_4205_, lean_object* v_ref_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v_res_4212_; 
v_res_4212_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13(v_00_u03b1_4205_, v_ref_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
lean_dec(v___y_4210_);
lean_dec_ref(v___y_4209_);
lean_dec(v___y_4208_);
lean_dec_ref(v___y_4207_);
return v_res_4212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10(lean_object* v_00_u03b1_4213_, lean_object* v_x_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v___x_4221_; 
v___x_4221_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg(v_x_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_, v___y_4219_);
return v___x_4221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___boxed(lean_object* v_00_u03b1_4222_, lean_object* v_x_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v_res_4230_; 
v_res_4230_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10(v_00_u03b1_4222_, v_x_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_);
lean_dec(v___y_4228_);
lean_dec_ref(v___y_4227_);
lean_dec(v___y_4226_);
lean_dec_ref(v___y_4225_);
lean_dec(v___y_4224_);
return v_res_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object* v_e_4238_, lean_object* v_config_4239_, lean_object* v_a_4240_, lean_object* v_a_4241_, lean_object* v_a_4242_, lean_object* v_a_4243_, lean_object* v_a_00___x40___internal___hyg_4244_){
_start:
{
lean_object* v_res_4245_; 
v_res_4245_ = lean_grind_normalize(v_e_4238_, v_config_4239_, v_a_4240_, v_a_4241_, v_a_4242_, v_a_4243_);
return v_res_4245_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4(void){
_start:
{
lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; 
v___x_4253_ = lean_box(0);
v___x_4254_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_4255_ = l_Lean_mkConst(v___x_4254_, v___x_4253_);
return v___x_4255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object* v_e_4256_){
_start:
{
lean_object* v___x_4257_; lean_object* v___x_4258_; 
v___x_4257_ = lean_obj_once(&l_Lean_Meta_Grind_markAsMatchCond___closed__4, &l_Lean_Meta_Grind_markAsMatchCond___closed__4_once, _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4);
v___x_4258_ = l_Lean_Expr_app___override(v___x_4257_, v_e_4256_);
return v___x_4258_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object* v_e_4259_){
_start:
{
lean_object* v___x_4260_; lean_object* v___x_4261_; uint8_t v___x_4262_; 
v___x_4260_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_4261_ = lean_unsigned_to_nat(1u);
v___x_4262_ = l_Lean_Expr_isAppOfArity(v_e_4259_, v___x_4260_, v___x_4261_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object* v_e_4263_){
_start:
{
uint8_t v_res_4264_; lean_object* v_r_4265_; 
v_res_4264_ = l_Lean_Meta_Grind_isMatchCond(v_e_4263_);
lean_dec_ref(v_e_4263_);
v_r_4265_ = lean_box(v_res_4264_);
return v_r_4265_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2(void){
_start:
{
lean_object* v___x_4271_; lean_object* v___x_4272_; lean_object* v___x_4273_; 
v___x_4271_ = lean_box(0);
v___x_4272_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4273_ = l_Lean_mkConst(v___x_4272_, v___x_4271_);
return v___x_4273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object* v_e_4274_){
_start:
{
lean_object* v___x_4275_; lean_object* v___x_4276_; 
v___x_4275_ = lean_obj_once(&l_Lean_Meta_Grind_markAsPreMatchCond___closed__2, &l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once, _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2);
v___x_4276_ = l_Lean_Expr_app___override(v___x_4275_, v_e_4274_);
return v___x_4276_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object* v_e_4277_){
_start:
{
lean_object* v___x_4278_; lean_object* v___x_4279_; uint8_t v___x_4280_; 
v___x_4278_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4279_ = lean_unsigned_to_nat(1u);
v___x_4280_ = l_Lean_Expr_isAppOfArity(v_e_4277_, v___x_4278_, v___x_4279_);
return v___x_4280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object* v_e_4281_){
_start:
{
uint8_t v_res_4282_; lean_object* v_r_4283_; 
v_res_4282_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_4281_);
lean_dec_ref(v_e_4281_);
v_r_4283_ = lean_box(v_res_4282_);
return v_r_4283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object* v_e_4284_, lean_object* v_a_4285_){
_start:
{
lean_object* v___x_4287_; 
lean_inc_ref(v_e_4284_);
v___x_4287_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4284_, v_a_4285_);
if (lean_obj_tag(v___x_4287_) == 0)
{
lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4304_; 
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4304_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4304_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4304_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4297_; uint8_t v___x_4298_; 
v___x_4297_ = l_Lean_Expr_cleanupAnnotations(v_a_4288_);
v___x_4298_ = l_Lean_Expr_isApp(v___x_4297_);
if (v___x_4298_ == 0)
{
lean_dec_ref(v___x_4297_);
lean_dec_ref(v_e_4284_);
goto v___jp_4292_;
}
else
{
lean_object* v___x_4299_; lean_object* v___x_4300_; uint8_t v___x_4301_; 
v___x_4299_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4297_);
v___x_4300_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4301_ = l_Lean_Expr_isConstOf(v___x_4299_, v___x_4300_);
lean_dec_ref(v___x_4299_);
if (v___x_4301_ == 0)
{
lean_dec_ref(v_e_4284_);
goto v___jp_4292_;
}
else
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
lean_del_object(v___x_4290_);
v___x_4302_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4302_, 0, v_e_4284_);
v___x_4303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4302_);
return v___x_4303_;
}
}
v___jp_4292_:
{
lean_object* v___x_4293_; lean_object* v___x_4295_; 
v___x_4293_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__1___closed__0));
if (v_isShared_4291_ == 0)
{
lean_ctor_set(v___x_4290_, 0, v___x_4293_);
v___x_4295_ = v___x_4290_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
else
{
lean_object* v_a_4305_; lean_object* v___x_4307_; uint8_t v_isShared_4308_; uint8_t v_isSharedCheck_4312_; 
lean_dec_ref(v_e_4284_);
v_a_4305_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4312_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4312_ == 0)
{
v___x_4307_ = v___x_4287_;
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
else
{
lean_inc(v_a_4305_);
lean_dec(v___x_4287_);
v___x_4307_ = lean_box(0);
v_isShared_4308_ = v_isSharedCheck_4312_;
goto v_resetjp_4306_;
}
v_resetjp_4306_:
{
lean_object* v___x_4310_; 
if (v_isShared_4308_ == 0)
{
v___x_4310_ = v___x_4307_;
goto v_reusejp_4309_;
}
else
{
lean_object* v_reuseFailAlloc_4311_; 
v_reuseFailAlloc_4311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4311_, 0, v_a_4305_);
v___x_4310_ = v_reuseFailAlloc_4311_;
goto v_reusejp_4309_;
}
v_reusejp_4309_:
{
return v___x_4310_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object* v_e_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_){
_start:
{
lean_object* v_res_4316_; 
v_res_4316_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_4313_, v_a_4314_);
lean_dec(v_a_4314_);
return v_res_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object* v_e_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_, lean_object* v_a_4320_, lean_object* v_a_4321_, lean_object* v_a_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_){
_start:
{
lean_object* v___x_4326_; 
v___x_4326_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_4317_, v_a_4322_);
return v___x_4326_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object* v_e_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_, lean_object* v_a_4331_, lean_object* v_a_4332_, lean_object* v_a_4333_, lean_object* v_a_4334_, lean_object* v_a_4335_){
_start:
{
lean_object* v_res_4336_; 
v_res_4336_ = l_Lean_Meta_Grind_reducePreMatchCond(v_e_4327_, v_a_4328_, v_a_4329_, v_a_4330_, v_a_4331_, v_a_4332_, v_a_4333_, v_a_4334_);
lean_dec(v_a_4334_);
lean_dec_ref(v_a_4333_);
lean_dec(v_a_4332_);
lean_dec_ref(v_a_4331_);
lean_dec(v_a_4330_);
lean_dec_ref(v_a_4329_);
lean_dec(v_a_4328_);
return v_res_4336_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; lean_object* v___x_4357_; 
v___x_4354_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4355_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4356_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond___boxed), 9, 0);
v___x_4357_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4354_, v___x_4355_, v___x_4356_);
return v___x_4357_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10____boxed(lean_object* v_a_4358_){
_start:
{
lean_object* v_res_4359_; 
v_res_4359_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
return v_res_4359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object* v_s_4360_, lean_object* v_a_4361_, lean_object* v_a_4362_){
_start:
{
lean_object* v___x_4364_; uint8_t v___x_4365_; lean_object* v___x_4366_; 
v___x_4364_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4365_ = 0;
v___x_4366_ = l_Lean_Meta_Simp_Simprocs_add(v_s_4360_, v___x_4364_, v___x_4365_, v_a_4361_, v_a_4362_);
return v___x_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object* v_s_4367_, lean_object* v_a_4368_, lean_object* v_a_4369_, lean_object* v_a_4370_){
_start:
{
lean_object* v_res_4371_; 
v_res_4371_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_4367_, v_a_4368_, v_a_4369_);
lean_dec(v_a_4369_);
lean_dec_ref(v_a_4368_);
return v_res_4371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object* v_e_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_){
_start:
{
lean_object* v___x_4382_; uint8_t v___x_4383_; 
lean_inc_ref(v_e_4372_);
v___x_4382_ = l_Lean_Expr_cleanupAnnotations(v_e_4372_);
v___x_4383_ = l_Lean_Expr_isApp(v___x_4382_);
if (v___x_4383_ == 0)
{
lean_dec_ref(v___x_4382_);
goto v___jp_4378_;
}
else
{
lean_object* v_arg_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; uint8_t v___x_4387_; 
v_arg_4384_ = lean_ctor_get(v___x_4382_, 1);
lean_inc_ref(v_arg_4384_);
v___x_4385_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4382_);
v___x_4386_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4387_ = l_Lean_Expr_isConstOf(v___x_4385_, v___x_4386_);
lean_dec_ref(v___x_4385_);
if (v___x_4387_ == 0)
{
lean_dec_ref(v_arg_4384_);
goto v___jp_4378_;
}
else
{
lean_object* v___x_4388_; lean_object* v___x_4389_; lean_object* v___x_4390_; lean_object* v___x_4391_; 
lean_dec_ref(v_e_4372_);
v___x_4388_ = l_Lean_Meta_Grind_markAsMatchCond(v_arg_4384_);
v___x_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4389_, 0, v___x_4388_);
v___x_4390_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4390_, 0, v___x_4389_);
v___x_4391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4391_, 0, v___x_4390_);
return v___x_4391_;
}
}
v___jp_4378_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4379_, 0, v_e_4372_);
v___x_4380_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4380_, 0, v___x_4379_);
v___x_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4381_, 0, v___x_4380_);
return v___x_4381_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(lean_object* v_e_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(v_e_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
return v_res_4398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1(lean_object* v_e_4399_, lean_object* v___y_4400_, lean_object* v___y_4401_, lean_object* v___y_4402_, lean_object* v___y_4403_){
_start:
{
lean_object* v___x_4405_; lean_object* v___x_4406_; 
v___x_4405_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4405_, 0, v_e_4399_);
v___x_4406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4406_, 0, v___x_4405_);
return v___x_4406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(lean_object* v_e_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_){
_start:
{
lean_object* v_res_4413_; 
v_res_4413_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(v_e_4407_, v___y_4408_, v___y_4409_, v___y_4410_, v___y_4411_);
lean_dec(v___y_4411_);
lean_dec_ref(v___y_4410_);
lean_dec(v___y_4409_);
lean_dec_ref(v___y_4408_);
return v_res_4413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(lean_object* v_x_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_, lean_object* v___y_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_){
_start:
{
lean_object* v___y_4422_; lean_object* v_fileName_4431_; lean_object* v_fileMap_4432_; lean_object* v_options_4433_; lean_object* v_currRecDepth_4434_; lean_object* v_maxRecDepth_4435_; lean_object* v_ref_4436_; lean_object* v_currNamespace_4437_; lean_object* v_openDecls_4438_; lean_object* v_initHeartbeats_4439_; lean_object* v_maxHeartbeats_4440_; lean_object* v_quotContext_4441_; lean_object* v_currMacroScope_4442_; uint8_t v_diag_4443_; lean_object* v_cancelTk_x3f_4444_; uint8_t v_suppressElabErrors_4445_; lean_object* v_inheritedTraceOptions_4446_; lean_object* v___x_4452_; uint8_t v___x_4453_; 
v_fileName_4431_ = lean_ctor_get(v___y_4418_, 0);
v_fileMap_4432_ = lean_ctor_get(v___y_4418_, 1);
v_options_4433_ = lean_ctor_get(v___y_4418_, 2);
v_currRecDepth_4434_ = lean_ctor_get(v___y_4418_, 3);
v_maxRecDepth_4435_ = lean_ctor_get(v___y_4418_, 4);
v_ref_4436_ = lean_ctor_get(v___y_4418_, 5);
v_currNamespace_4437_ = lean_ctor_get(v___y_4418_, 6);
v_openDecls_4438_ = lean_ctor_get(v___y_4418_, 7);
v_initHeartbeats_4439_ = lean_ctor_get(v___y_4418_, 8);
v_maxHeartbeats_4440_ = lean_ctor_get(v___y_4418_, 9);
v_quotContext_4441_ = lean_ctor_get(v___y_4418_, 10);
v_currMacroScope_4442_ = lean_ctor_get(v___y_4418_, 11);
v_diag_4443_ = lean_ctor_get_uint8(v___y_4418_, sizeof(void*)*14);
v_cancelTk_x3f_4444_ = lean_ctor_get(v___y_4418_, 12);
v_suppressElabErrors_4445_ = lean_ctor_get_uint8(v___y_4418_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4446_ = lean_ctor_get(v___y_4418_, 13);
v___x_4452_ = lean_unsigned_to_nat(0u);
v___x_4453_ = lean_nat_dec_eq(v_maxRecDepth_4435_, v___x_4452_);
if (v___x_4453_ == 0)
{
uint8_t v___x_4454_; 
v___x_4454_ = lean_nat_dec_eq(v_currRecDepth_4434_, v_maxRecDepth_4435_);
if (v___x_4454_ == 0)
{
goto v___jp_4447_;
}
else
{
lean_object* v___x_4455_; 
lean_dec_ref(v_x_4414_);
lean_inc(v_ref_4436_);
v___x_4455_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_4436_);
v___y_4422_ = v___x_4455_;
goto v___jp_4421_;
}
}
else
{
goto v___jp_4447_;
}
v___jp_4421_:
{
if (lean_obj_tag(v___y_4422_) == 0)
{
return v___y_4422_;
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
v_a_4423_ = lean_ctor_get(v___y_4422_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___y_4422_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___y_4422_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___y_4422_);
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
v___jp_4447_:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; 
v___x_4448_ = lean_unsigned_to_nat(1u);
v___x_4449_ = lean_nat_add(v_currRecDepth_4434_, v___x_4448_);
lean_inc_ref(v_inheritedTraceOptions_4446_);
lean_inc(v_cancelTk_x3f_4444_);
lean_inc(v_currMacroScope_4442_);
lean_inc(v_quotContext_4441_);
lean_inc(v_maxHeartbeats_4440_);
lean_inc(v_initHeartbeats_4439_);
lean_inc(v_openDecls_4438_);
lean_inc(v_currNamespace_4437_);
lean_inc(v_ref_4436_);
lean_inc(v_maxRecDepth_4435_);
lean_inc_ref(v_options_4433_);
lean_inc_ref(v_fileMap_4432_);
lean_inc_ref(v_fileName_4431_);
v___x_4450_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4450_, 0, v_fileName_4431_);
lean_ctor_set(v___x_4450_, 1, v_fileMap_4432_);
lean_ctor_set(v___x_4450_, 2, v_options_4433_);
lean_ctor_set(v___x_4450_, 3, v___x_4449_);
lean_ctor_set(v___x_4450_, 4, v_maxRecDepth_4435_);
lean_ctor_set(v___x_4450_, 5, v_ref_4436_);
lean_ctor_set(v___x_4450_, 6, v_currNamespace_4437_);
lean_ctor_set(v___x_4450_, 7, v_openDecls_4438_);
lean_ctor_set(v___x_4450_, 8, v_initHeartbeats_4439_);
lean_ctor_set(v___x_4450_, 9, v_maxHeartbeats_4440_);
lean_ctor_set(v___x_4450_, 10, v_quotContext_4441_);
lean_ctor_set(v___x_4450_, 11, v_currMacroScope_4442_);
lean_ctor_set(v___x_4450_, 12, v_cancelTk_x3f_4444_);
lean_ctor_set(v___x_4450_, 13, v_inheritedTraceOptions_4446_);
lean_ctor_set_uint8(v___x_4450_, sizeof(void*)*14, v_diag_4443_);
lean_ctor_set_uint8(v___x_4450_, sizeof(void*)*14 + 1, v_suppressElabErrors_4445_);
lean_inc(v___y_4419_);
lean_inc(v___y_4417_);
lean_inc_ref(v___y_4416_);
lean_inc(v___y_4415_);
v___x_4451_ = lean_apply_6(v_x_4414_, v___y_4415_, v___y_4416_, v___y_4417_, v___x_4450_, v___y_4419_, lean_box(0));
v___y_4422_ = v___x_4451_;
goto v___jp_4421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v_res_4463_; 
v_res_4463_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_4456_, v___y_4457_, v___y_4458_, v___y_4459_, v___y_4460_, v___y_4461_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
lean_dec(v___y_4459_);
lean_dec_ref(v___y_4458_);
lean_dec(v___y_4457_);
return v_res_4463_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(lean_object* v_pre_4464_, lean_object* v_post_4465_, size_t v_sz_4466_, size_t v_i_4467_, lean_object* v_bs_4468_, lean_object* v___y_4469_, lean_object* v___y_4470_, lean_object* v___y_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_){
_start:
{
uint8_t v___x_4475_; 
v___x_4475_ = lean_usize_dec_lt(v_i_4467_, v_sz_4466_);
if (v___x_4475_ == 0)
{
lean_object* v___x_4476_; 
lean_dec_ref(v_post_4465_);
lean_dec_ref(v_pre_4464_);
v___x_4476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4476_, 0, v_bs_4468_);
return v___x_4476_;
}
else
{
lean_object* v_v_4477_; lean_object* v___x_4478_; 
v_v_4477_ = lean_array_uget_borrowed(v_bs_4468_, v_i_4467_);
lean_inc(v_v_4477_);
lean_inc_ref(v_post_4465_);
lean_inc_ref(v_pre_4464_);
v___x_4478_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4464_, v_post_4465_, v_v_4477_, v___y_4469_, v___y_4470_, v___y_4471_, v___y_4472_, v___y_4473_);
if (lean_obj_tag(v___x_4478_) == 0)
{
lean_object* v_a_4479_; lean_object* v___x_4480_; lean_object* v_bs_x27_4481_; size_t v___x_4482_; size_t v___x_4483_; lean_object* v___x_4484_; 
v_a_4479_ = lean_ctor_get(v___x_4478_, 0);
lean_inc(v_a_4479_);
lean_dec_ref(v___x_4478_);
v___x_4480_ = lean_unsigned_to_nat(0u);
v_bs_x27_4481_ = lean_array_uset(v_bs_4468_, v_i_4467_, v___x_4480_);
v___x_4482_ = ((size_t)1ULL);
v___x_4483_ = lean_usize_add(v_i_4467_, v___x_4482_);
v___x_4484_ = lean_array_uset(v_bs_x27_4481_, v_i_4467_, v_a_4479_);
v_i_4467_ = v___x_4483_;
v_bs_4468_ = v___x_4484_;
goto _start;
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec_ref(v_bs_4468_);
lean_dec_ref(v_post_4465_);
lean_dec_ref(v_pre_4464_);
v_a_4486_ = lean_ctor_get(v___x_4478_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4478_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4478_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4478_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(lean_object* v_pre_4494_, lean_object* v_post_4495_, lean_object* v_x_4496_, lean_object* v_x_4497_, lean_object* v_x_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
if (lean_obj_tag(v_x_4496_) == 5)
{
lean_object* v_fn_4505_; lean_object* v_arg_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; 
v_fn_4505_ = lean_ctor_get(v_x_4496_, 0);
lean_inc_ref(v_fn_4505_);
v_arg_4506_ = lean_ctor_get(v_x_4496_, 1);
lean_inc_ref(v_arg_4506_);
lean_dec_ref(v_x_4496_);
v___x_4507_ = lean_array_set(v_x_4497_, v_x_4498_, v_arg_4506_);
v___x_4508_ = lean_unsigned_to_nat(1u);
v___x_4509_ = lean_nat_sub(v_x_4498_, v___x_4508_);
lean_dec(v_x_4498_);
v_x_4496_ = v_fn_4505_;
v_x_4497_ = v___x_4507_;
v_x_4498_ = v___x_4509_;
goto _start;
}
else
{
lean_object* v___x_4511_; 
lean_dec(v_x_4498_);
lean_inc_ref(v_post_4495_);
lean_inc_ref(v_pre_4494_);
v___x_4511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4494_, v_post_4495_, v_x_4496_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_object* v_a_4512_; size_t v_sz_4513_; size_t v___x_4514_; lean_object* v___x_4515_; 
v_a_4512_ = lean_ctor_get(v___x_4511_, 0);
lean_inc(v_a_4512_);
lean_dec_ref(v___x_4511_);
v_sz_4513_ = lean_array_size(v_x_4497_);
v___x_4514_ = ((size_t)0ULL);
lean_inc_ref(v_post_4495_);
lean_inc_ref(v_pre_4494_);
v___x_4515_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_4494_, v_post_4495_, v_sz_4513_, v___x_4514_, v_x_4497_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
if (lean_obj_tag(v___x_4515_) == 0)
{
lean_object* v_a_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; 
v_a_4516_ = lean_ctor_get(v___x_4515_, 0);
lean_inc(v_a_4516_);
lean_dec_ref(v___x_4515_);
v___x_4517_ = l_Lean_mkAppN(v_a_4512_, v_a_4516_);
lean_dec(v_a_4516_);
v___x_4518_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4494_, v_post_4495_, v___x_4517_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
return v___x_4518_;
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_dec(v_a_4512_);
lean_dec_ref(v_post_4495_);
lean_dec_ref(v_pre_4494_);
v_a_4519_ = lean_ctor_get(v___x_4515_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4515_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4515_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4515_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_dec_ref(v_x_4497_);
lean_dec_ref(v_post_4495_);
lean_dec_ref(v_pre_4494_);
return v___x_4511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(lean_object* v___x_4527_, lean_object* v_pre_4528_, lean_object* v_e_4529_, lean_object* v_post_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_){
_start:
{
lean_object* v___y_4538_; lean_object* v___y_4539_; lean_object* v___y_4540_; lean_object* v___y_4541_; lean_object* v___y_4542_; uint8_t v___y_4543_; lean_object* v___y_4544_; uint8_t v___y_4545_; lean_object* v___y_4555_; lean_object* v___y_4556_; lean_object* v___y_4557_; uint8_t v___y_4558_; lean_object* v___y_4559_; uint8_t v___y_4560_; lean_object* v___y_4568_; lean_object* v___y_4569_; lean_object* v___y_4570_; uint8_t v___y_4571_; lean_object* v___y_4572_; uint8_t v___y_4573_; lean_object* v___x_4580_; 
v___x_4580_ = l_Lean_Core_checkSystem(v___x_4527_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4580_) == 0)
{
lean_object* v___x_4581_; 
lean_dec_ref(v___x_4580_);
lean_inc_ref(v_pre_4528_);
lean_inc(v___y_4535_);
lean_inc_ref(v___y_4534_);
lean_inc(v___y_4533_);
lean_inc_ref(v___y_4532_);
lean_inc_ref(v_e_4529_);
v___x_4581_ = lean_apply_6(v_pre_4528_, v_e_4529_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_, lean_box(0));
if (lean_obj_tag(v___x_4581_) == 0)
{
lean_object* v_a_4582_; lean_object* v___x_4584_; uint8_t v_isShared_4585_; uint8_t v_isSharedCheck_4671_; 
v_a_4582_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4671_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4671_ == 0)
{
v___x_4584_ = v___x_4581_;
v_isShared_4585_ = v_isSharedCheck_4671_;
goto v_resetjp_4583_;
}
else
{
lean_inc(v_a_4582_);
lean_dec(v___x_4581_);
v___x_4584_ = lean_box(0);
v_isShared_4585_ = v_isSharedCheck_4671_;
goto v_resetjp_4583_;
}
v_resetjp_4583_:
{
lean_object* v___y_4587_; 
switch(lean_obj_tag(v_a_4582_))
{
case 0:
{
lean_object* v_e_4661_; lean_object* v___x_4663_; 
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_e_4529_);
lean_dec_ref(v_pre_4528_);
v_e_4661_ = lean_ctor_get(v_a_4582_, 0);
lean_inc_ref(v_e_4661_);
lean_dec_ref(v_a_4582_);
if (v_isShared_4585_ == 0)
{
lean_ctor_set(v___x_4584_, 0, v_e_4661_);
v___x_4663_ = v___x_4584_;
goto v_reusejp_4662_;
}
else
{
lean_object* v_reuseFailAlloc_4664_; 
v_reuseFailAlloc_4664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4664_, 0, v_e_4661_);
v___x_4663_ = v_reuseFailAlloc_4664_;
goto v_reusejp_4662_;
}
v_reusejp_4662_:
{
return v___x_4663_;
}
}
case 1:
{
lean_object* v_e_4665_; lean_object* v___x_4666_; 
lean_del_object(v___x_4584_);
lean_dec_ref(v_e_4529_);
v_e_4665_ = lean_ctor_get(v_a_4582_, 0);
lean_inc_ref(v_e_4665_);
lean_dec_ref(v_a_4582_);
lean_inc_ref(v_post_4530_);
lean_inc_ref(v_pre_4528_);
v___x_4666_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4528_, v_post_4530_, v_e_4665_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v_a_4667_; lean_object* v___x_4668_; 
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
lean_inc(v_a_4667_);
lean_dec_ref(v___x_4666_);
v___x_4668_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v_a_4667_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4668_;
}
else
{
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_pre_4528_);
return v___x_4666_;
}
}
default: 
{
lean_object* v_e_x3f_4669_; 
lean_del_object(v___x_4584_);
v_e_x3f_4669_ = lean_ctor_get(v_a_4582_, 0);
lean_inc(v_e_x3f_4669_);
lean_dec_ref(v_a_4582_);
if (lean_obj_tag(v_e_x3f_4669_) == 0)
{
v___y_4587_ = v_e_4529_;
goto v___jp_4586_;
}
else
{
lean_object* v_val_4670_; 
lean_dec_ref(v_e_4529_);
v_val_4670_ = lean_ctor_get(v_e_x3f_4669_, 0);
lean_inc(v_val_4670_);
lean_dec_ref(v_e_x3f_4669_);
v___y_4587_ = v_val_4670_;
goto v___jp_4586_;
}
}
}
v___jp_4586_:
{
switch(lean_obj_tag(v___y_4587_))
{
case 7:
{
lean_object* v_binderName_4588_; lean_object* v_binderType_4589_; lean_object* v_body_4590_; uint8_t v_binderInfo_4591_; lean_object* v___x_4592_; 
v_binderName_4588_ = lean_ctor_get(v___y_4587_, 0);
lean_inc(v_binderName_4588_);
v_binderType_4589_ = lean_ctor_get(v___y_4587_, 1);
v_body_4590_ = lean_ctor_get(v___y_4587_, 2);
v_binderInfo_4591_ = lean_ctor_get_uint8(v___y_4587_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_4589_);
lean_inc_ref(v_post_4530_);
lean_inc_ref(v_pre_4528_);
v___x_4592_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4528_, v_post_4530_, v_binderType_4589_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4592_) == 0)
{
lean_object* v_a_4593_; lean_object* v___x_4594_; 
v_a_4593_ = lean_ctor_get(v___x_4592_, 0);
lean_inc(v_a_4593_);
lean_dec_ref(v___x_4592_);
lean_inc_ref(v_body_4590_);
lean_inc_ref(v_post_4530_);
lean_inc_ref(v_pre_4528_);
v___x_4594_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4528_, v_post_4530_, v_body_4590_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4594_) == 0)
{
lean_object* v_a_4595_; size_t v___x_4596_; size_t v___x_4597_; uint8_t v___x_4598_; 
v_a_4595_ = lean_ctor_get(v___x_4594_, 0);
lean_inc(v_a_4595_);
lean_dec_ref(v___x_4594_);
v___x_4596_ = lean_ptr_addr(v_binderType_4589_);
v___x_4597_ = lean_ptr_addr(v_a_4593_);
v___x_4598_ = lean_usize_dec_eq(v___x_4596_, v___x_4597_);
if (v___x_4598_ == 0)
{
v___y_4568_ = v___y_4587_;
v___y_4569_ = v_binderName_4588_;
v___y_4570_ = v_a_4593_;
v___y_4571_ = v_binderInfo_4591_;
v___y_4572_ = v_a_4595_;
v___y_4573_ = v___x_4598_;
goto v___jp_4567_;
}
else
{
size_t v___x_4599_; size_t v___x_4600_; uint8_t v___x_4601_; 
v___x_4599_ = lean_ptr_addr(v_body_4590_);
v___x_4600_ = lean_ptr_addr(v_a_4595_);
v___x_4601_ = lean_usize_dec_eq(v___x_4599_, v___x_4600_);
v___y_4568_ = v___y_4587_;
v___y_4569_ = v_binderName_4588_;
v___y_4570_ = v_a_4593_;
v___y_4571_ = v_binderInfo_4591_;
v___y_4572_ = v_a_4595_;
v___y_4573_ = v___x_4601_;
goto v___jp_4567_;
}
}
else
{
lean_dec(v_a_4593_);
lean_dec_ref(v___y_4587_);
lean_dec(v_binderName_4588_);
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_pre_4528_);
return v___x_4594_;
}
}
else
{
lean_dec(v_binderName_4588_);
lean_dec_ref(v___y_4587_);
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_pre_4528_);
return v___x_4592_;
}
}
case 6:
{
lean_object* v_binderName_4602_; lean_object* v_binderType_4603_; lean_object* v_body_4604_; uint8_t v_binderInfo_4605_; lean_object* v___x_4606_; 
v_binderName_4602_ = lean_ctor_get(v___y_4587_, 0);
lean_inc(v_binderName_4602_);
v_binderType_4603_ = lean_ctor_get(v___y_4587_, 1);
v_body_4604_ = lean_ctor_get(v___y_4587_, 2);
v_binderInfo_4605_ = lean_ctor_get_uint8(v___y_4587_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_4603_);
lean_inc_ref(v_post_4530_);
lean_inc_ref(v_pre_4528_);
v___x_4606_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4528_, v_post_4530_, v_binderType_4603_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4606_) == 0)
{
lean_object* v_a_4607_; lean_object* v___x_4608_; 
v_a_4607_ = lean_ctor_get(v___x_4606_, 0);
lean_inc(v_a_4607_);
lean_dec_ref(v___x_4606_);
lean_inc_ref(v_body_4604_);
lean_inc_ref(v_post_4530_);
lean_inc_ref(v_pre_4528_);
v___x_4608_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4528_, v_post_4530_, v_body_4604_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4608_) == 0)
{
lean_object* v_a_4609_; size_t v___x_4610_; size_t v___x_4611_; uint8_t v___x_4612_; 
v_a_4609_ = lean_ctor_get(v___x_4608_, 0);
lean_inc(v_a_4609_);
lean_dec_ref(v___x_4608_);
v___x_4610_ = lean_ptr_addr(v_binderType_4603_);
v___x_4611_ = lean_ptr_addr(v_a_4607_);
v___x_4612_ = lean_usize_dec_eq(v___x_4610_, v___x_4611_);
if (v___x_4612_ == 0)
{
v___y_4555_ = v_binderName_4602_;
v___y_4556_ = v___y_4587_;
v___y_4557_ = v_a_4609_;
v___y_4558_ = v_binderInfo_4605_;
v___y_4559_ = v_a_4607_;
v___y_4560_ = v___x_4612_;
goto v___jp_4554_;
}
else
{
size_t v___x_4613_; size_t v___x_4614_; uint8_t v___x_4615_; 
v___x_4613_ = lean_ptr_addr(v_body_4604_);
v___x_4614_ = lean_ptr_addr(v_a_4609_);
v___x_4615_ = lean_usize_dec_eq(v___x_4613_, v___x_4614_);
v___y_4555_ = v_binderName_4602_;
v___y_4556_ = v___y_4587_;
v___y_4557_ = v_a_4609_;
v___y_4558_ = v_binderInfo_4605_;
v___y_4559_ = v_a_4607_;
v___y_4560_ = v___x_4615_;
goto v___jp_4554_;
}
}
else
{
lean_dec(v_a_4607_);
lean_dec_ref(v___y_4587_);
lean_dec(v_binderName_4602_);
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_pre_4528_);
return v___x_4608_;
}
}
else
{
lean_dec(v_binderName_4602_);
lean_dec_ref(v___y_4587_);
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_pre_4528_);
return v___x_4606_;
}
}
case 8:
{
lean_object* v_declName_4616_; lean_object* v_type_4617_; lean_object* v_value_4618_; lean_object* v_body_4619_; uint8_t v_nondep_4620_; lean_object* v___x_4621_; 
v_declName_4616_ = lean_ctor_get(v___y_4587_, 0);
lean_inc(v_declName_4616_);
v_type_4617_ = lean_ctor_get(v___y_4587_, 1);
v_value_4618_ = lean_ctor_get(v___y_4587_, 2);
v_body_4619_ = lean_ctor_get(v___y_4587_, 3);
lean_inc_ref(v_body_4619_);
v_nondep_4620_ = lean_ctor_get_uint8(v___y_4587_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_4617_);
lean_inc_ref(v_post_4530_);
lean_inc_ref(v_pre_4528_);
v___x_4621_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4528_, v_post_4530_, v_type_4617_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4621_) == 0)
{
lean_object* v_a_4622_; lean_object* v___x_4623_; 
v_a_4622_ = lean_ctor_get(v___x_4621_, 0);
lean_inc(v_a_4622_);
lean_dec_ref(v___x_4621_);
lean_inc_ref(v_value_4618_);
lean_inc_ref(v_post_4530_);
lean_inc_ref(v_pre_4528_);
v___x_4623_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4528_, v_post_4530_, v_value_4618_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4623_) == 0)
{
lean_object* v_a_4624_; lean_object* v___x_4625_; 
v_a_4624_ = lean_ctor_get(v___x_4623_, 0);
lean_inc(v_a_4624_);
lean_dec_ref(v___x_4623_);
lean_inc_ref(v_body_4619_);
lean_inc_ref(v_post_4530_);
lean_inc_ref(v_pre_4528_);
v___x_4625_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4528_, v_post_4530_, v_body_4619_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4625_) == 0)
{
lean_object* v_a_4626_; size_t v___x_4627_; size_t v___x_4628_; uint8_t v___x_4629_; 
v_a_4626_ = lean_ctor_get(v___x_4625_, 0);
lean_inc(v_a_4626_);
lean_dec_ref(v___x_4625_);
v___x_4627_ = lean_ptr_addr(v_type_4617_);
v___x_4628_ = lean_ptr_addr(v_a_4622_);
v___x_4629_ = lean_usize_dec_eq(v___x_4627_, v___x_4628_);
if (v___x_4629_ == 0)
{
v___y_4538_ = v___y_4587_;
v___y_4539_ = v_a_4624_;
v___y_4540_ = v_a_4622_;
v___y_4541_ = v_a_4626_;
v___y_4542_ = v_body_4619_;
v___y_4543_ = v_nondep_4620_;
v___y_4544_ = v_declName_4616_;
v___y_4545_ = v___x_4629_;
goto v___jp_4537_;
}
else
{
size_t v___x_4630_; size_t v___x_4631_; uint8_t v___x_4632_; 
v___x_4630_ = lean_ptr_addr(v_value_4618_);
v___x_4631_ = lean_ptr_addr(v_a_4624_);
v___x_4632_ = lean_usize_dec_eq(v___x_4630_, v___x_4631_);
v___y_4538_ = v___y_4587_;
v___y_4539_ = v_a_4624_;
v___y_4540_ = v_a_4622_;
v___y_4541_ = v_a_4626_;
v___y_4542_ = v_body_4619_;
v___y_4543_ = v_nondep_4620_;
v___y_4544_ = v_declName_4616_;
v___y_4545_ = v___x_4632_;
goto v___jp_4537_;
}
}
else
{
lean_dec(v_a_4624_);
lean_dec(v_a_4622_);
lean_dec_ref(v_body_4619_);
lean_dec(v_declName_4616_);
lean_dec_ref(v___y_4587_);
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_pre_4528_);
return v___x_4625_;
}
}
else
{
lean_dec(v_a_4622_);
lean_dec_ref(v_body_4619_);
lean_dec_ref(v___y_4587_);
lean_dec(v_declName_4616_);
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_pre_4528_);
return v___x_4623_;
}
}
else
{
lean_dec_ref(v_body_4619_);
lean_dec_ref(v___y_4587_);
lean_dec(v_declName_4616_);
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_pre_4528_);
return v___x_4621_;
}
}
case 5:
{
lean_object* v_dummy_4633_; lean_object* v_nargs_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v_dummy_4633_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_4634_ = l_Lean_Expr_getAppNumArgs(v___y_4587_);
lean_inc(v_nargs_4634_);
v___x_4635_ = lean_mk_array(v_nargs_4634_, v_dummy_4633_);
v___x_4636_ = lean_unsigned_to_nat(1u);
v___x_4637_ = lean_nat_sub(v_nargs_4634_, v___x_4636_);
lean_dec(v_nargs_4634_);
v___x_4638_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_4528_, v_post_4530_, v___y_4587_, v___x_4635_, v___x_4637_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4638_;
}
case 10:
{
lean_object* v_data_4639_; lean_object* v_expr_4640_; lean_object* v___x_4641_; 
v_data_4639_ = lean_ctor_get(v___y_4587_, 0);
v_expr_4640_ = lean_ctor_get(v___y_4587_, 1);
lean_inc_ref(v_expr_4640_);
lean_inc_ref(v_post_4530_);
lean_inc_ref(v_pre_4528_);
v___x_4641_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4528_, v_post_4530_, v_expr_4640_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4641_) == 0)
{
lean_object* v_a_4642_; size_t v___x_4643_; size_t v___x_4644_; uint8_t v___x_4645_; 
v_a_4642_ = lean_ctor_get(v___x_4641_, 0);
lean_inc(v_a_4642_);
lean_dec_ref(v___x_4641_);
v___x_4643_ = lean_ptr_addr(v_expr_4640_);
v___x_4644_ = lean_ptr_addr(v_a_4642_);
v___x_4645_ = lean_usize_dec_eq(v___x_4643_, v___x_4644_);
if (v___x_4645_ == 0)
{
lean_object* v___x_4646_; lean_object* v___x_4647_; 
lean_inc(v_data_4639_);
lean_dec_ref(v___y_4587_);
v___x_4646_ = l_Lean_Expr_mdata___override(v_data_4639_, v_a_4642_);
v___x_4647_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___x_4646_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4647_;
}
else
{
lean_object* v___x_4648_; 
lean_dec(v_a_4642_);
v___x_4648_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___y_4587_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4648_;
}
}
else
{
lean_dec_ref(v___y_4587_);
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_pre_4528_);
return v___x_4641_;
}
}
case 11:
{
lean_object* v_typeName_4649_; lean_object* v_idx_4650_; lean_object* v_struct_4651_; lean_object* v___x_4652_; 
v_typeName_4649_ = lean_ctor_get(v___y_4587_, 0);
v_idx_4650_ = lean_ctor_get(v___y_4587_, 1);
v_struct_4651_ = lean_ctor_get(v___y_4587_, 2);
lean_inc_ref(v_struct_4651_);
lean_inc_ref(v_post_4530_);
lean_inc_ref(v_pre_4528_);
v___x_4652_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4528_, v_post_4530_, v_struct_4651_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
if (lean_obj_tag(v___x_4652_) == 0)
{
lean_object* v_a_4653_; size_t v___x_4654_; size_t v___x_4655_; uint8_t v___x_4656_; 
v_a_4653_ = lean_ctor_get(v___x_4652_, 0);
lean_inc(v_a_4653_);
lean_dec_ref(v___x_4652_);
v___x_4654_ = lean_ptr_addr(v_struct_4651_);
v___x_4655_ = lean_ptr_addr(v_a_4653_);
v___x_4656_ = lean_usize_dec_eq(v___x_4654_, v___x_4655_);
if (v___x_4656_ == 0)
{
lean_object* v___x_4657_; lean_object* v___x_4658_; 
lean_inc(v_idx_4650_);
lean_inc(v_typeName_4649_);
lean_dec_ref(v___y_4587_);
v___x_4657_ = l_Lean_Expr_proj___override(v_typeName_4649_, v_idx_4650_, v_a_4653_);
v___x_4658_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___x_4657_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4658_;
}
else
{
lean_object* v___x_4659_; 
lean_dec(v_a_4653_);
v___x_4659_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___y_4587_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4659_;
}
}
else
{
lean_dec_ref(v___y_4587_);
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_pre_4528_);
return v___x_4652_;
}
}
default: 
{
lean_object* v___x_4660_; 
v___x_4660_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___y_4587_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4660_;
}
}
}
}
}
else
{
lean_object* v_a_4672_; lean_object* v___x_4674_; uint8_t v_isShared_4675_; uint8_t v_isSharedCheck_4679_; 
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_e_4529_);
lean_dec_ref(v_pre_4528_);
v_a_4672_ = lean_ctor_get(v___x_4581_, 0);
v_isSharedCheck_4679_ = !lean_is_exclusive(v___x_4581_);
if (v_isSharedCheck_4679_ == 0)
{
v___x_4674_ = v___x_4581_;
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
else
{
lean_inc(v_a_4672_);
lean_dec(v___x_4581_);
v___x_4674_ = lean_box(0);
v_isShared_4675_ = v_isSharedCheck_4679_;
goto v_resetjp_4673_;
}
v_resetjp_4673_:
{
lean_object* v___x_4677_; 
if (v_isShared_4675_ == 0)
{
v___x_4677_ = v___x_4674_;
goto v_reusejp_4676_;
}
else
{
lean_object* v_reuseFailAlloc_4678_; 
v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
v___x_4677_ = v_reuseFailAlloc_4678_;
goto v_reusejp_4676_;
}
v_reusejp_4676_:
{
return v___x_4677_;
}
}
}
}
else
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4687_; 
lean_dec_ref(v_post_4530_);
lean_dec_ref(v_e_4529_);
lean_dec_ref(v_pre_4528_);
v_a_4680_ = lean_ctor_get(v___x_4580_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4580_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4682_ = v___x_4580_;
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4580_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4687_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4685_; 
if (v_isShared_4683_ == 0)
{
v___x_4685_ = v___x_4682_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v_a_4680_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
v___jp_4537_:
{
if (v___y_4545_ == 0)
{
lean_object* v___x_4546_; lean_object* v___x_4547_; 
lean_dec_ref(v___y_4542_);
lean_dec_ref(v___y_4538_);
v___x_4546_ = l_Lean_Expr_letE___override(v___y_4544_, v___y_4540_, v___y_4539_, v___y_4541_, v___y_4543_);
v___x_4547_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___x_4546_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4547_;
}
else
{
size_t v___x_4548_; size_t v___x_4549_; uint8_t v___x_4550_; 
v___x_4548_ = lean_ptr_addr(v___y_4542_);
lean_dec_ref(v___y_4542_);
v___x_4549_ = lean_ptr_addr(v___y_4541_);
v___x_4550_ = lean_usize_dec_eq(v___x_4548_, v___x_4549_);
if (v___x_4550_ == 0)
{
lean_object* v___x_4551_; lean_object* v___x_4552_; 
lean_dec_ref(v___y_4538_);
v___x_4551_ = l_Lean_Expr_letE___override(v___y_4544_, v___y_4540_, v___y_4539_, v___y_4541_, v___y_4543_);
v___x_4552_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___x_4551_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4552_;
}
else
{
lean_object* v___x_4553_; 
lean_dec(v___y_4544_);
lean_dec_ref(v___y_4541_);
lean_dec_ref(v___y_4540_);
lean_dec_ref(v___y_4539_);
v___x_4553_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___y_4538_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4553_;
}
}
}
v___jp_4554_:
{
if (v___y_4560_ == 0)
{
lean_object* v___x_4561_; lean_object* v___x_4562_; 
lean_dec_ref(v___y_4556_);
v___x_4561_ = l_Lean_Expr_lam___override(v___y_4555_, v___y_4559_, v___y_4557_, v___y_4558_);
v___x_4562_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___x_4561_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4562_;
}
else
{
uint8_t v___x_4563_; 
v___x_4563_ = l_Lean_instBEqBinderInfo_beq(v___y_4558_, v___y_4558_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; lean_object* v___x_4565_; 
lean_dec_ref(v___y_4556_);
v___x_4564_ = l_Lean_Expr_lam___override(v___y_4555_, v___y_4559_, v___y_4557_, v___y_4558_);
v___x_4565_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___x_4564_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4565_;
}
else
{
lean_object* v___x_4566_; 
lean_dec_ref(v___y_4559_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4555_);
v___x_4566_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___y_4556_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4566_;
}
}
}
v___jp_4567_:
{
if (v___y_4573_ == 0)
{
lean_object* v___x_4574_; lean_object* v___x_4575_; 
lean_dec_ref(v___y_4568_);
v___x_4574_ = l_Lean_Expr_forallE___override(v___y_4569_, v___y_4570_, v___y_4572_, v___y_4571_);
v___x_4575_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___x_4574_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4575_;
}
else
{
uint8_t v___x_4576_; 
v___x_4576_ = l_Lean_instBEqBinderInfo_beq(v___y_4571_, v___y_4571_);
if (v___x_4576_ == 0)
{
lean_object* v___x_4577_; lean_object* v___x_4578_; 
lean_dec_ref(v___y_4568_);
v___x_4577_ = l_Lean_Expr_forallE___override(v___y_4569_, v___y_4570_, v___y_4572_, v___y_4571_);
v___x_4578_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___x_4577_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4578_;
}
else
{
lean_object* v___x_4579_; 
lean_dec_ref(v___y_4572_);
lean_dec_ref(v___y_4570_);
lean_dec(v___y_4569_);
v___x_4579_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4528_, v_post_4530_, v___y_4568_, v___y_4531_, v___y_4532_, v___y_4533_, v___y_4534_, v___y_4535_);
return v___x_4579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(lean_object* v___x_4688_, lean_object* v_pre_4689_, lean_object* v_e_4690_, lean_object* v_post_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_, lean_object* v___y_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_){
_start:
{
lean_object* v_res_4698_; 
v_res_4698_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v___x_4688_, v_pre_4689_, v_e_4690_, v_post_4691_, v___y_4692_, v___y_4693_, v___y_4694_, v___y_4695_, v___y_4696_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec(v___y_4694_);
lean_dec_ref(v___y_4693_);
lean_dec(v___y_4692_);
return v_res_4698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(lean_object* v_pre_4699_, lean_object* v_post_4700_, lean_object* v_e_4701_, lean_object* v_a_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_, lean_object* v___y_4705_, lean_object* v___y_4706_){
_start:
{
lean_object* v___x_4708_; lean_object* v___x_4709_; 
lean_inc(v_a_4702_);
v___x_4708_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4708_, 0, lean_box(0));
lean_closure_set(v___x_4708_, 1, lean_box(0));
lean_closure_set(v___x_4708_, 2, v_a_4702_);
v___x_4709_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_box(0), v___x_4708_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
if (lean_obj_tag(v___x_4709_) == 0)
{
lean_object* v_a_4710_; lean_object* v___x_4712_; uint8_t v_isShared_4713_; uint8_t v_isSharedCheck_4741_; 
v_a_4710_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4741_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4741_ == 0)
{
v___x_4712_ = v___x_4709_;
v_isShared_4713_ = v_isSharedCheck_4741_;
goto v_resetjp_4711_;
}
else
{
lean_inc(v_a_4710_);
lean_dec(v___x_4709_);
v___x_4712_ = lean_box(0);
v_isShared_4713_ = v_isSharedCheck_4741_;
goto v_resetjp_4711_;
}
v_resetjp_4711_:
{
lean_object* v___x_4714_; 
v___x_4714_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_4710_, v_e_4701_);
lean_dec(v_a_4710_);
if (lean_obj_tag(v___x_4714_) == 0)
{
lean_object* v___x_4715_; lean_object* v___f_4716_; lean_object* v___x_4717_; 
lean_del_object(v___x_4712_);
v___x_4715_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___closed__0));
lean_inc_ref(v_e_4701_);
v___f_4716_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed), 10, 4);
lean_closure_set(v___f_4716_, 0, v___x_4715_);
lean_closure_set(v___f_4716_, 1, v_pre_4699_);
lean_closure_set(v___f_4716_, 2, v_e_4701_);
lean_closure_set(v___f_4716_, 3, v_post_4700_);
v___x_4717_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v___f_4716_, v_a_4702_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
if (lean_obj_tag(v___x_4717_) == 0)
{
lean_object* v_a_4718_; lean_object* v___f_4719_; lean_object* v___x_4720_; 
v_a_4718_ = lean_ctor_get(v___x_4717_, 0);
lean_inc_n(v_a_4718_, 2);
lean_dec_ref(v___x_4717_);
lean_inc(v_a_4702_);
v___f_4719_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4719_, 0, v_a_4702_);
lean_closure_set(v___f_4719_, 1, v_e_4701_);
lean_closure_set(v___f_4719_, 2, v_a_4718_);
v___x_4720_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_box(0), v___f_4719_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_);
if (lean_obj_tag(v___x_4720_) == 0)
{
lean_object* v___x_4722_; uint8_t v_isShared_4723_; uint8_t v_isSharedCheck_4727_; 
v_isSharedCheck_4727_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4727_ == 0)
{
lean_object* v_unused_4728_; 
v_unused_4728_ = lean_ctor_get(v___x_4720_, 0);
lean_dec(v_unused_4728_);
v___x_4722_ = v___x_4720_;
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
else
{
lean_dec(v___x_4720_);
v___x_4722_ = lean_box(0);
v_isShared_4723_ = v_isSharedCheck_4727_;
goto v_resetjp_4721_;
}
v_resetjp_4721_:
{
lean_object* v___x_4725_; 
if (v_isShared_4723_ == 0)
{
lean_ctor_set(v___x_4722_, 0, v_a_4718_);
v___x_4725_ = v___x_4722_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_a_4718_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
}
else
{
lean_object* v_a_4729_; lean_object* v___x_4731_; uint8_t v_isShared_4732_; uint8_t v_isSharedCheck_4736_; 
lean_dec(v_a_4718_);
v_a_4729_ = lean_ctor_get(v___x_4720_, 0);
v_isSharedCheck_4736_ = !lean_is_exclusive(v___x_4720_);
if (v_isSharedCheck_4736_ == 0)
{
v___x_4731_ = v___x_4720_;
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
else
{
lean_inc(v_a_4729_);
lean_dec(v___x_4720_);
v___x_4731_ = lean_box(0);
v_isShared_4732_ = v_isSharedCheck_4736_;
goto v_resetjp_4730_;
}
v_resetjp_4730_:
{
lean_object* v___x_4734_; 
if (v_isShared_4732_ == 0)
{
v___x_4734_ = v___x_4731_;
goto v_reusejp_4733_;
}
else
{
lean_object* v_reuseFailAlloc_4735_; 
v_reuseFailAlloc_4735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4735_, 0, v_a_4729_);
v___x_4734_ = v_reuseFailAlloc_4735_;
goto v_reusejp_4733_;
}
v_reusejp_4733_:
{
return v___x_4734_;
}
}
}
}
else
{
lean_dec_ref(v_e_4701_);
return v___x_4717_;
}
}
else
{
lean_object* v_val_4737_; lean_object* v___x_4739_; 
lean_dec_ref(v_e_4701_);
lean_dec_ref(v_post_4700_);
lean_dec_ref(v_pre_4699_);
v_val_4737_ = lean_ctor_get(v___x_4714_, 0);
lean_inc(v_val_4737_);
lean_dec_ref(v___x_4714_);
if (v_isShared_4713_ == 0)
{
lean_ctor_set(v___x_4712_, 0, v_val_4737_);
v___x_4739_ = v___x_4712_;
goto v_reusejp_4738_;
}
else
{
lean_object* v_reuseFailAlloc_4740_; 
v_reuseFailAlloc_4740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4740_, 0, v_val_4737_);
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
else
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4749_; 
lean_dec_ref(v_e_4701_);
lean_dec_ref(v_post_4700_);
lean_dec_ref(v_pre_4699_);
v_a_4742_ = lean_ctor_get(v___x_4709_, 0);
v_isSharedCheck_4749_ = !lean_is_exclusive(v___x_4709_);
if (v_isSharedCheck_4749_ == 0)
{
v___x_4744_ = v___x_4709_;
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4709_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4749_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v___x_4747_; 
if (v_isShared_4745_ == 0)
{
v___x_4747_ = v___x_4744_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4742_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(lean_object* v_pre_4750_, lean_object* v_post_4751_, lean_object* v_e_4752_, lean_object* v_a_4753_, lean_object* v___y_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_){
_start:
{
lean_object* v___x_4759_; 
lean_inc_ref(v_post_4751_);
lean_inc(v___y_4757_);
lean_inc_ref(v___y_4756_);
lean_inc(v___y_4755_);
lean_inc_ref(v___y_4754_);
lean_inc_ref(v_e_4752_);
v___x_4759_ = lean_apply_6(v_post_4751_, v_e_4752_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, lean_box(0));
if (lean_obj_tag(v___x_4759_) == 0)
{
lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4778_; 
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4778_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4778_ == 0)
{
v___x_4762_ = v___x_4759_;
v_isShared_4763_ = v_isSharedCheck_4778_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4759_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4778_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
switch(lean_obj_tag(v_a_4760_))
{
case 0:
{
lean_object* v_e_4764_; lean_object* v___x_4766_; 
lean_dec_ref(v_e_4752_);
lean_dec_ref(v_post_4751_);
lean_dec_ref(v_pre_4750_);
v_e_4764_ = lean_ctor_get(v_a_4760_, 0);
lean_inc_ref(v_e_4764_);
lean_dec_ref(v_a_4760_);
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 0, v_e_4764_);
v___x_4766_ = v___x_4762_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_e_4764_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
case 1:
{
lean_object* v_e_4768_; lean_object* v___x_4769_; 
lean_del_object(v___x_4762_);
lean_dec_ref(v_e_4752_);
v_e_4768_ = lean_ctor_get(v_a_4760_, 0);
lean_inc_ref(v_e_4768_);
lean_dec_ref(v_a_4760_);
v___x_4769_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4750_, v_post_4751_, v_e_4768_, v_a_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_);
return v___x_4769_;
}
default: 
{
lean_object* v_e_x3f_4770_; 
lean_dec_ref(v_post_4751_);
lean_dec_ref(v_pre_4750_);
v_e_x3f_4770_ = lean_ctor_get(v_a_4760_, 0);
lean_inc(v_e_x3f_4770_);
lean_dec_ref(v_a_4760_);
if (lean_obj_tag(v_e_x3f_4770_) == 0)
{
lean_object* v___x_4772_; 
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 0, v_e_4752_);
v___x_4772_ = v___x_4762_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_e_4752_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
else
{
lean_object* v_val_4774_; lean_object* v___x_4776_; 
lean_dec_ref(v_e_4752_);
v_val_4774_ = lean_ctor_get(v_e_x3f_4770_, 0);
lean_inc(v_val_4774_);
lean_dec_ref(v_e_x3f_4770_);
if (v_isShared_4763_ == 0)
{
lean_ctor_set(v___x_4762_, 0, v_val_4774_);
v___x_4776_ = v___x_4762_;
goto v_reusejp_4775_;
}
else
{
lean_object* v_reuseFailAlloc_4777_; 
v_reuseFailAlloc_4777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4777_, 0, v_val_4774_);
v___x_4776_ = v_reuseFailAlloc_4777_;
goto v_reusejp_4775_;
}
v_reusejp_4775_:
{
return v___x_4776_;
}
}
}
}
}
}
else
{
lean_object* v_a_4779_; lean_object* v___x_4781_; uint8_t v_isShared_4782_; uint8_t v_isSharedCheck_4786_; 
lean_dec_ref(v_e_4752_);
lean_dec_ref(v_post_4751_);
lean_dec_ref(v_pre_4750_);
v_a_4779_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4786_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4786_ == 0)
{
v___x_4781_ = v___x_4759_;
v_isShared_4782_ = v_isSharedCheck_4786_;
goto v_resetjp_4780_;
}
else
{
lean_inc(v_a_4779_);
lean_dec(v___x_4759_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_4787_, lean_object* v_post_4788_, lean_object* v_e_4789_, lean_object* v_a_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4787_, v_post_4788_, v_e_4789_, v_a_4790_, v___y_4791_, v___y_4792_, v___y_4793_, v___y_4794_);
lean_dec(v___y_4794_);
lean_dec_ref(v___y_4793_);
lean_dec(v___y_4792_);
lean_dec_ref(v___y_4791_);
lean_dec(v_a_4790_);
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_4797_, lean_object* v_post_4798_, lean_object* v_sz_4799_, lean_object* v_i_4800_, lean_object* v_bs_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
size_t v_sz_boxed_4808_; size_t v_i_boxed_4809_; lean_object* v_res_4810_; 
v_sz_boxed_4808_ = lean_unbox_usize(v_sz_4799_);
lean_dec(v_sz_4799_);
v_i_boxed_4809_ = lean_unbox_usize(v_i_4800_);
lean_dec(v_i_4800_);
v_res_4810_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_4797_, v_post_4798_, v_sz_boxed_4808_, v_i_boxed_4809_, v_bs_4801_, v___y_4802_, v___y_4803_, v___y_4804_, v___y_4805_, v___y_4806_);
lean_dec(v___y_4806_);
lean_dec_ref(v___y_4805_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
lean_dec(v___y_4802_);
return v_res_4810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_4811_, lean_object* v_post_4812_, lean_object* v_x_4813_, lean_object* v_x_4814_, lean_object* v_x_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_, lean_object* v___y_4820_, lean_object* v___y_4821_){
_start:
{
lean_object* v_res_4822_; 
v_res_4822_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_4811_, v_post_4812_, v_x_4813_, v_x_4814_, v_x_4815_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_);
lean_dec(v___y_4820_);
lean_dec_ref(v___y_4819_);
lean_dec(v___y_4818_);
lean_dec_ref(v___y_4817_);
lean_dec(v___y_4816_);
return v_res_4822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(lean_object* v_pre_4823_, lean_object* v_post_4824_, lean_object* v_e_4825_, lean_object* v_a_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4823_, v_post_4824_, v_e_4825_, v_a_4826_, v___y_4827_, v___y_4828_, v___y_4829_, v___y_4830_);
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
lean_dec(v___y_4828_);
lean_dec_ref(v___y_4827_);
lean_dec(v_a_4826_);
return v_res_4832_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(lean_object* v_input_4833_, lean_object* v_pre_4834_, lean_object* v_post_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
lean_object* v___x_4841_; lean_object* v___x_4842_; lean_object* v_a_4843_; lean_object* v___x_4844_; 
v___x_4841_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_4842_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_box(0), v___x_4841_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
v_a_4843_ = lean_ctor_get(v___x_4842_, 0);
lean_inc(v_a_4843_);
lean_dec_ref(v___x_4842_);
v___x_4844_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4834_, v_post_4835_, v_input_4833_, v_a_4843_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
if (lean_obj_tag(v___x_4844_) == 0)
{
lean_object* v_a_4845_; lean_object* v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
v_a_4845_ = lean_ctor_get(v___x_4844_, 0);
lean_inc(v_a_4845_);
lean_dec_ref(v___x_4844_);
v___x_4846_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4846_, 0, lean_box(0));
lean_closure_set(v___x_4846_, 1, lean_box(0));
lean_closure_set(v___x_4846_, 2, v_a_4843_);
v___x_4847_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_box(0), v___x_4846_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4847_);
if (v_isSharedCheck_4854_ == 0)
{
lean_object* v_unused_4855_; 
v_unused_4855_ = lean_ctor_get(v___x_4847_, 0);
lean_dec(v_unused_4855_);
v___x_4849_ = v___x_4847_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_dec(v___x_4847_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
lean_ctor_set(v___x_4849_, 0, v_a_4845_);
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4845_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
else
{
lean_dec(v_a_4843_);
return v___x_4844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___boxed(lean_object* v_input_4856_, lean_object* v_pre_4857_, lean_object* v_post_4858_, lean_object* v___y_4859_, lean_object* v___y_4860_, lean_object* v___y_4861_, lean_object* v___y_4862_, lean_object* v___y_4863_){
_start:
{
lean_object* v_res_4864_; 
v_res_4864_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_input_4856_, v_pre_4857_, v_post_4858_, v___y_4859_, v___y_4860_, v___y_4861_, v___y_4862_);
lean_dec(v___y_4862_);
lean_dec_ref(v___y_4861_);
lean_dec(v___y_4860_);
lean_dec_ref(v___y_4859_);
return v_res_4864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object* v_e_4868_, lean_object* v_a_4869_, lean_object* v_a_4870_, lean_object* v_a_4871_, lean_object* v_a_4872_){
_start:
{
lean_object* v___x_4874_; lean_object* v___x_4875_; 
v___x_4874_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__0));
v___x_4875_ = lean_find_expr(v___x_4874_, v_e_4868_);
if (lean_obj_tag(v___x_4875_) == 0)
{
uint8_t v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4876_ = 1;
v___x_4877_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4877_, 0, v_e_4868_);
lean_ctor_set(v___x_4877_, 1, v___x_4875_);
lean_ctor_set_uint8(v___x_4877_, sizeof(void*)*2, v___x_4876_);
v___x_4878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
return v___x_4878_;
}
else
{
lean_object* v___x_4880_; uint8_t v_isShared_4881_; uint8_t v_isSharedCheck_4927_; 
v_isSharedCheck_4927_ = !lean_is_exclusive(v___x_4875_);
if (v_isSharedCheck_4927_ == 0)
{
lean_object* v_unused_4928_; 
v_unused_4928_ = lean_ctor_get(v___x_4875_, 0);
lean_dec(v_unused_4928_);
v___x_4880_ = v___x_4875_;
v_isShared_4881_ = v_isSharedCheck_4927_;
goto v_resetjp_4879_;
}
else
{
lean_dec(v___x_4875_);
v___x_4880_ = lean_box(0);
v_isShared_4881_ = v_isSharedCheck_4927_;
goto v_resetjp_4879_;
}
v_resetjp_4879_:
{
lean_object* v_pre_4882_; lean_object* v___f_4883_; lean_object* v___x_4884_; 
v_pre_4882_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__1));
v___f_4883_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__2));
lean_inc_ref(v_e_4868_);
v___x_4884_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_e_4868_, v_pre_4882_, v___f_4883_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
if (lean_obj_tag(v___x_4884_) == 0)
{
lean_object* v_a_4885_; lean_object* v___x_4886_; 
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
lean_inc_n(v_a_4885_, 2);
lean_dec_ref(v___x_4884_);
v___x_4886_ = l_Lean_Meta_mkEqRefl(v_a_4885_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
if (lean_obj_tag(v___x_4886_) == 0)
{
lean_object* v_a_4887_; lean_object* v___x_4888_; 
v_a_4887_ = lean_ctor_get(v___x_4886_, 0);
lean_inc(v_a_4887_);
lean_dec_ref(v___x_4886_);
lean_inc(v_a_4885_);
v___x_4888_ = l_Lean_Meta_mkEq(v_e_4868_, v_a_4885_, v_a_4869_, v_a_4870_, v_a_4871_, v_a_4872_);
if (lean_obj_tag(v___x_4888_) == 0)
{
lean_object* v_a_4889_; lean_object* v___x_4891_; uint8_t v_isShared_4892_; uint8_t v_isSharedCheck_4902_; 
v_a_4889_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4891_ = v___x_4888_;
v_isShared_4892_ = v_isSharedCheck_4902_;
goto v_resetjp_4890_;
}
else
{
lean_inc(v_a_4889_);
lean_dec(v___x_4888_);
v___x_4891_ = lean_box(0);
v_isShared_4892_ = v_isSharedCheck_4902_;
goto v_resetjp_4890_;
}
v_resetjp_4890_:
{
uint8_t v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4896_; 
v___x_4893_ = 1;
v___x_4894_ = l_Lean_Meta_mkExpectedPropHint(v_a_4887_, v_a_4889_);
if (v_isShared_4881_ == 0)
{
lean_ctor_set(v___x_4880_, 0, v___x_4894_);
v___x_4896_ = v___x_4880_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v___x_4894_);
v___x_4896_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
lean_object* v___x_4897_; lean_object* v___x_4899_; 
v___x_4897_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4897_, 0, v_a_4885_);
lean_ctor_set(v___x_4897_, 1, v___x_4896_);
lean_ctor_set_uint8(v___x_4897_, sizeof(void*)*2, v___x_4893_);
if (v_isShared_4892_ == 0)
{
lean_ctor_set(v___x_4891_, 0, v___x_4897_);
v___x_4899_ = v___x_4891_;
goto v_reusejp_4898_;
}
else
{
lean_object* v_reuseFailAlloc_4900_; 
v_reuseFailAlloc_4900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4900_, 0, v___x_4897_);
v___x_4899_ = v_reuseFailAlloc_4900_;
goto v_reusejp_4898_;
}
v_reusejp_4898_:
{
return v___x_4899_;
}
}
}
}
else
{
lean_object* v_a_4903_; lean_object* v___x_4905_; uint8_t v_isShared_4906_; uint8_t v_isSharedCheck_4910_; 
lean_dec(v_a_4887_);
lean_dec(v_a_4885_);
lean_del_object(v___x_4880_);
v_a_4903_ = lean_ctor_get(v___x_4888_, 0);
v_isSharedCheck_4910_ = !lean_is_exclusive(v___x_4888_);
if (v_isSharedCheck_4910_ == 0)
{
v___x_4905_ = v___x_4888_;
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
else
{
lean_inc(v_a_4903_);
lean_dec(v___x_4888_);
v___x_4905_ = lean_box(0);
v_isShared_4906_ = v_isSharedCheck_4910_;
goto v_resetjp_4904_;
}
v_resetjp_4904_:
{
lean_object* v___x_4908_; 
if (v_isShared_4906_ == 0)
{
v___x_4908_ = v___x_4905_;
goto v_reusejp_4907_;
}
else
{
lean_object* v_reuseFailAlloc_4909_; 
v_reuseFailAlloc_4909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4909_, 0, v_a_4903_);
v___x_4908_ = v_reuseFailAlloc_4909_;
goto v_reusejp_4907_;
}
v_reusejp_4907_:
{
return v___x_4908_;
}
}
}
}
else
{
lean_object* v_a_4911_; lean_object* v___x_4913_; uint8_t v_isShared_4914_; uint8_t v_isSharedCheck_4918_; 
lean_dec(v_a_4885_);
lean_del_object(v___x_4880_);
lean_dec_ref(v_e_4868_);
v_a_4911_ = lean_ctor_get(v___x_4886_, 0);
v_isSharedCheck_4918_ = !lean_is_exclusive(v___x_4886_);
if (v_isSharedCheck_4918_ == 0)
{
v___x_4913_ = v___x_4886_;
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
else
{
lean_inc(v_a_4911_);
lean_dec(v___x_4886_);
v___x_4913_ = lean_box(0);
v_isShared_4914_ = v_isSharedCheck_4918_;
goto v_resetjp_4912_;
}
v_resetjp_4912_:
{
lean_object* v___x_4916_; 
if (v_isShared_4914_ == 0)
{
v___x_4916_ = v___x_4913_;
goto v_reusejp_4915_;
}
else
{
lean_object* v_reuseFailAlloc_4917_; 
v_reuseFailAlloc_4917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4917_, 0, v_a_4911_);
v___x_4916_ = v_reuseFailAlloc_4917_;
goto v_reusejp_4915_;
}
v_reusejp_4915_:
{
return v___x_4916_;
}
}
}
}
else
{
lean_object* v_a_4919_; lean_object* v___x_4921_; uint8_t v_isShared_4922_; uint8_t v_isSharedCheck_4926_; 
lean_del_object(v___x_4880_);
lean_dec_ref(v_e_4868_);
v_a_4919_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4926_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4926_ == 0)
{
v___x_4921_ = v___x_4884_;
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
else
{
lean_inc(v_a_4919_);
lean_dec(v___x_4884_);
v___x_4921_ = lean_box(0);
v_isShared_4922_ = v_isSharedCheck_4926_;
goto v_resetjp_4920_;
}
v_resetjp_4920_:
{
lean_object* v___x_4924_; 
if (v_isShared_4922_ == 0)
{
v___x_4924_ = v___x_4921_;
goto v_reusejp_4923_;
}
else
{
lean_object* v_reuseFailAlloc_4925_; 
v_reuseFailAlloc_4925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4925_, 0, v_a_4919_);
v___x_4924_ = v_reuseFailAlloc_4925_;
goto v_reusejp_4923_;
}
v_reusejp_4923_:
{
return v___x_4924_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___boxed(lean_object* v_e_4929_, lean_object* v_a_4930_, lean_object* v_a_4931_, lean_object* v_a_4932_, lean_object* v_a_4933_, lean_object* v_a_4934_){
_start:
{
lean_object* v_res_4935_; 
v_res_4935_ = l_Lean_Meta_Grind_replacePreMatchCond(v_e_4929_, v_a_4930_, v_a_4931_, v_a_4932_, v_a_4933_);
lean_dec(v_a_4933_);
lean_dec_ref(v_a_4932_);
lean_dec(v_a_4931_);
lean_dec_ref(v_a_4930_);
return v_res_4935_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4936_, lean_object* v_x_4937_, lean_object* v___y_4938_, lean_object* v___y_4939_, lean_object* v___y_4940_, lean_object* v___y_4941_, lean_object* v___y_4942_){
_start:
{
lean_object* v___x_4944_; 
v___x_4944_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_4937_, v___y_4938_, v___y_4939_, v___y_4940_, v___y_4941_, v___y_4942_);
return v___x_4944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4945_, lean_object* v_x_4946_, lean_object* v___y_4947_, lean_object* v___y_4948_, lean_object* v___y_4949_, lean_object* v___y_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_){
_start:
{
lean_object* v_res_4953_; 
v_res_4953_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(v_00_u03b1_4945_, v_x_4946_, v___y_4947_, v___y_4948_, v___y_4949_, v___y_4950_, v___y_4951_);
lean_dec(v___y_4951_);
lean_dec_ref(v___y_4950_);
lean_dec(v___y_4949_);
lean_dec_ref(v___y_4948_);
lean_dec(v___y_4947_);
return v_res_4953_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isIte(lean_object* v_e_4957_){
_start:
{
lean_object* v___x_4958_; uint8_t v___x_4959_; 
v___x_4958_ = ((lean_object*)(l_Lean_Meta_Grind_isIte___closed__1));
v___x_4959_ = l_Lean_Expr_isAppOf(v_e_4957_, v___x_4958_);
if (v___x_4959_ == 0)
{
return v___x_4959_;
}
else
{
lean_object* v___x_4960_; lean_object* v___x_4961_; uint8_t v___x_4962_; 
v___x_4960_ = lean_unsigned_to_nat(5u);
v___x_4961_ = l_Lean_Expr_getAppNumArgs(v_e_4957_);
v___x_4962_ = lean_nat_dec_le(v___x_4960_, v___x_4961_);
lean_dec(v___x_4961_);
return v___x_4962_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object* v_e_4963_){
_start:
{
uint8_t v_res_4964_; lean_object* v_r_4965_; 
v_res_4964_ = l_Lean_Meta_Grind_isIte(v_e_4963_);
lean_dec_ref(v_e_4963_);
v_r_4965_ = lean_box(v_res_4964_);
return v_r_4965_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isDIte(lean_object* v_e_4969_){
_start:
{
lean_object* v___x_4970_; uint8_t v___x_4971_; 
v___x_4970_ = ((lean_object*)(l_Lean_Meta_Grind_isDIte___closed__1));
v___x_4971_ = l_Lean_Expr_isAppOf(v_e_4969_, v___x_4970_);
if (v___x_4971_ == 0)
{
return v___x_4971_;
}
else
{
lean_object* v___x_4972_; lean_object* v___x_4973_; uint8_t v___x_4974_; 
v___x_4972_ = lean_unsigned_to_nat(5u);
v___x_4973_ = l_Lean_Expr_getAppNumArgs(v_e_4969_);
v___x_4974_ = lean_nat_dec_le(v___x_4972_, v___x_4973_);
lean_dec(v___x_4973_);
return v___x_4974_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object* v_e_4975_){
_start:
{
uint8_t v_res_4976_; lean_object* v_r_4977_; 
v_res_4976_ = l_Lean_Meta_Grind_isDIte(v_e_4975_);
lean_dec_ref(v_e_4975_);
v_r_4977_ = lean_box(v_res_4976_);
return v_r_4977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object* v_e_4978_){
_start:
{
uint8_t v___x_4979_; 
v___x_4979_ = l_Lean_Expr_isApp(v_e_4978_);
if (v___x_4979_ == 0)
{
lean_object* v___x_4980_; 
v___x_4980_ = lean_box(0);
return v___x_4980_;
}
else
{
lean_object* v_f_4981_; uint8_t v___x_4982_; 
v_f_4981_ = l_Lean_Expr_appFn_x21(v_e_4978_);
v___x_4982_ = l_Lean_Expr_isApp(v_f_4981_);
if (v___x_4982_ == 0)
{
lean_object* v___x_4983_; 
lean_dec_ref(v_f_4981_);
v___x_4983_ = lean_box(0);
return v___x_4983_;
}
else
{
lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4984_ = l_Lean_Expr_appFn_x21(v_f_4981_);
lean_dec_ref(v_f_4981_);
v___x_4985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4985_, 0, v___x_4984_);
return v___x_4985_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object* v_e_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l_Lean_Meta_Grind_getBinOp(v_e_4986_);
lean_dec_ref(v_e_4986_);
return v_res_4987_;
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
