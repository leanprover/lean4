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
lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_1357__overap_153_; lean_object* v___x_154_; 
v___x_151_ = l_Lean_instInhabitedLocalContext_default;
v___x_152_ = l_instInhabitedOfMonad___redArg(v___x_150_, v___x_151_);
v___x_1357__overap_153_ = lean_panic_fn(v___x_152_, v_msg_96_);
lean_inc(v___y_100_);
lean_inc_ref(v___y_99_);
lean_inc(v___y_98_);
lean_inc_ref(v___y_97_);
v___x_154_ = lean_apply_5(v___x_1357__overap_153_, v___y_97_, v___y_98_, v___y_99_, v___y_100_, lean_box(0));
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
size_t v_x_4506__boxed_452_; size_t v_x_4507__boxed_453_; lean_object* v_res_454_; 
v_x_4506__boxed_452_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_x_4507__boxed_453_ = lean_unbox_usize(v_x_445_);
lean_dec(v_x_445_);
v_res_454_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_instantiateLCtxMVars___at___00Lean_MVarId_instantiateGoalMVars_spec__0_spec__2_spec__3_spec__5(v_auxDeclToFullName_442_, v_x_443_, v_x_4506__boxed_452_, v_x_4507__boxed_453_, v_x_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_);
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
size_t v_x_4892__boxed_719_; size_t v_x_4893__boxed_720_; lean_object* v_res_721_; 
v_x_4892__boxed_719_ = lean_unbox_usize(v_x_715_);
lean_dec(v_x_715_);
v_x_4893__boxed_720_ = lean_unbox_usize(v_x_716_);
lean_dec(v_x_716_);
v_res_721_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6___redArg(v_x_714_, v_x_4892__boxed_719_, v_x_4893__boxed_720_, v_x_717_, v_x_718_);
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
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_801_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref(v___x_791_);
lean_inc(v_a_792_);
v___x_793_ = l_Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1___redArg(v_mvarId_771_, v_a_792_, v_a_773_);
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
lean_dec(v_a_839_);
lean_dec_ref(v_a_838_);
lean_dec(v_a_837_);
lean_dec_ref(v_a_836_);
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
size_t v_x_5258__boxed_884_; size_t v_x_5259__boxed_885_; lean_object* v_res_886_; 
v_x_5258__boxed_884_ = lean_unbox_usize(v_x_880_);
lean_dec(v_x_880_);
v_x_5259__boxed_885_ = lean_unbox_usize(v_x_881_);
lean_dec(v_x_881_);
v_res_886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_instantiateGoalMVars_spec__1_spec__4_spec__6(v_00_u03b2_878_, v_x_879_, v_x_5258__boxed_884_, v_x_5259__boxed_885_, v_x_882_, v_x_883_);
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
lean_inc(v___y_921_);
lean_inc_ref(v___y_920_);
lean_inc(v___y_919_);
lean_inc_ref(v___y_918_);
v___x_923_ = lean_apply_7(v_k_915_, v_b_916_, v_c_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, lean_box(0));
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0___boxed(lean_object* v_k_924_, lean_object* v_b_925_, lean_object* v_c_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Meta_lambdaTelescope___at___00Lean_MVarId_abstractMVars_spec__0___redArg___lam__0(v_k_924_, v_b_925_, v_c_926_, v___y_927_, v___y_928_, v___y_929_, v___y_930_);
lean_dec(v___y_930_);
lean_dec_ref(v___y_929_);
lean_dec(v___y_928_);
lean_dec_ref(v___y_927_);
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
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
lean_dec(v___y_966_);
lean_dec_ref(v___y_965_);
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
lean_dec(v___y_989_);
lean_dec_ref(v___y_988_);
lean_dec(v___y_987_);
lean_dec_ref(v___y_986_);
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
lean_dec(v___y_1022_);
lean_dec_ref(v___y_1021_);
lean_dec(v___y_1020_);
lean_dec_ref(v___y_1019_);
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
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
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
uint8_t v___x_1951__boxed_1063_; uint8_t v___x_1952__boxed_1064_; lean_object* v_res_1065_; 
v___x_1951__boxed_1063_ = lean_unbox(v___x_1054_);
v___x_1952__boxed_1064_ = lean_unbox(v___x_1055_);
v_res_1065_ = l_Lean_MVarId_abstractMVars___lam__0(v___x_1951__boxed_1063_, v___x_1952__boxed_1064_, v_xs_1056_, v_body_1057_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
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
uint8_t v___x_1977__boxed_1137_; lean_object* v_res_1138_; 
v___x_1977__boxed_1137_ = lean_unbox(v___x_1129_);
v_res_1138_ = l_Lean_MVarId_abstractMVars___lam__1(v_a_1128_, v___x_1977__boxed_1137_, v___f_1130_, v_mvarId_1131_, v___y_1132_, v___y_1133_, v___y_1134_, v___y_1135_);
lean_dec(v___y_1135_);
lean_dec_ref(v___y_1134_);
lean_dec(v___y_1133_);
lean_dec_ref(v___y_1132_);
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
lean_dec(v_a_1186_);
lean_dec_ref(v_a_1185_);
lean_dec(v_a_1184_);
lean_dec_ref(v_a_1183_);
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
lean_dec_ref(v___y_1192_);
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
lean_dec(v_a_1280_);
lean_dec_ref(v_a_1279_);
lean_dec(v_a_1278_);
lean_dec_ref(v_a_1277_);
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
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
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
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
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
lean_dec(v_a_1326_);
lean_dec_ref(v_a_1325_);
lean_dec(v_a_1324_);
lean_dec_ref(v_a_1323_);
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
lean_dec(v___y_1428_);
lean_dec_ref(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec_ref(v___y_1425_);
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
lean_dec(v_a_1448_);
lean_dec_ref(v_a_1447_);
lean_dec(v_a_1446_);
lean_dec_ref(v_a_1445_);
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
lean_dec(v___y_1529_);
lean_dec_ref(v___y_1528_);
lean_dec(v___y_1527_);
lean_dec_ref(v___y_1526_);
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
lean_dec_ref(v___y_1901_);
return v___x_1916_;
}
else
{
lean_object* v___x_1918_; 
lean_dec(v_a_1911_);
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
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
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
lean_dec(v_a_1962_);
lean_dec_ref(v_a_1961_);
lean_dec(v_a_1960_);
lean_dec_ref(v_a_1959_);
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
lean_dec(v___y_1982_);
lean_dec_ref(v___y_1981_);
lean_dec(v___y_1980_);
lean_dec_ref(v___y_1979_);
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
lean_object* v___y_2144_; lean_object* v_fileName_2153_; lean_object* v_fileMap_2154_; lean_object* v_options_2155_; lean_object* v_currRecDepth_2156_; lean_object* v_maxRecDepth_2157_; lean_object* v_ref_2158_; lean_object* v_currNamespace_2159_; lean_object* v_openDecls_2160_; lean_object* v_initHeartbeats_2161_; lean_object* v_maxHeartbeats_2162_; lean_object* v_quotContext_2163_; lean_object* v_currMacroScope_2164_; uint8_t v_diag_2165_; lean_object* v_cancelTk_x3f_2166_; uint8_t v_suppressElabErrors_2167_; lean_object* v_inheritedTraceOptions_2168_; uint8_t v___x_2169_; 
v_fileName_2153_ = lean_ctor_get(v___y_2140_, 0);
lean_inc_ref(v_fileName_2153_);
v_fileMap_2154_ = lean_ctor_get(v___y_2140_, 1);
lean_inc_ref(v_fileMap_2154_);
v_options_2155_ = lean_ctor_get(v___y_2140_, 2);
lean_inc_ref(v_options_2155_);
v_currRecDepth_2156_ = lean_ctor_get(v___y_2140_, 3);
lean_inc(v_currRecDepth_2156_);
v_maxRecDepth_2157_ = lean_ctor_get(v___y_2140_, 4);
lean_inc(v_maxRecDepth_2157_);
v_ref_2158_ = lean_ctor_get(v___y_2140_, 5);
lean_inc(v_ref_2158_);
v_currNamespace_2159_ = lean_ctor_get(v___y_2140_, 6);
lean_inc(v_currNamespace_2159_);
v_openDecls_2160_ = lean_ctor_get(v___y_2140_, 7);
lean_inc(v_openDecls_2160_);
v_initHeartbeats_2161_ = lean_ctor_get(v___y_2140_, 8);
lean_inc(v_initHeartbeats_2161_);
v_maxHeartbeats_2162_ = lean_ctor_get(v___y_2140_, 9);
lean_inc(v_maxHeartbeats_2162_);
v_quotContext_2163_ = lean_ctor_get(v___y_2140_, 10);
lean_inc(v_quotContext_2163_);
v_currMacroScope_2164_ = lean_ctor_get(v___y_2140_, 11);
lean_inc(v_currMacroScope_2164_);
v_diag_2165_ = lean_ctor_get_uint8(v___y_2140_, sizeof(void*)*14);
v_cancelTk_x3f_2166_ = lean_ctor_get(v___y_2140_, 12);
lean_inc(v_cancelTk_x3f_2166_);
v_suppressElabErrors_2167_ = lean_ctor_get_uint8(v___y_2140_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_2168_ = lean_ctor_get(v___y_2140_, 13);
lean_inc_ref(v_inheritedTraceOptions_2168_);
lean_dec_ref(v___y_2140_);
v___x_2169_ = lean_nat_dec_eq(v_currRecDepth_2156_, v_maxRecDepth_2157_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = lean_nat_add(v_currRecDepth_2156_, v___x_2170_);
lean_dec(v_currRecDepth_2156_);
v___x_2172_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_2172_, 0, v_fileName_2153_);
lean_ctor_set(v___x_2172_, 1, v_fileMap_2154_);
lean_ctor_set(v___x_2172_, 2, v_options_2155_);
lean_ctor_set(v___x_2172_, 3, v___x_2171_);
lean_ctor_set(v___x_2172_, 4, v_maxRecDepth_2157_);
lean_ctor_set(v___x_2172_, 5, v_ref_2158_);
lean_ctor_set(v___x_2172_, 6, v_currNamespace_2159_);
lean_ctor_set(v___x_2172_, 7, v_openDecls_2160_);
lean_ctor_set(v___x_2172_, 8, v_initHeartbeats_2161_);
lean_ctor_set(v___x_2172_, 9, v_maxHeartbeats_2162_);
lean_ctor_set(v___x_2172_, 10, v_quotContext_2163_);
lean_ctor_set(v___x_2172_, 11, v_currMacroScope_2164_);
lean_ctor_set(v___x_2172_, 12, v_cancelTk_x3f_2166_);
lean_ctor_set(v___x_2172_, 13, v_inheritedTraceOptions_2168_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*14, v_diag_2165_);
lean_ctor_set_uint8(v___x_2172_, sizeof(void*)*14 + 1, v_suppressElabErrors_2167_);
lean_inc(v___y_2141_);
lean_inc(v___y_2139_);
v___x_2173_ = lean_apply_4(v_x_2138_, v___y_2139_, v___x_2172_, v___y_2141_, lean_box(0));
v___y_2144_ = v___x_2173_;
goto v___jp_2143_;
}
else
{
lean_object* v___x_2174_; 
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
lean_dec_ref(v_x_2138_);
v___x_2174_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2158_);
v___y_2144_ = v___x_2174_;
goto v___jp_2143_;
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
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg___boxed(lean_object* v_x_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_){
_start:
{
lean_object* v_res_2180_; 
v_res_2180_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2175_, v___y_2176_, v___y_2177_, v___y_2178_);
lean_dec(v___y_2178_);
lean_dec(v___y_2176_);
return v_res_2180_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(lean_object* v_x_2181_, lean_object* v_x_2182_){
_start:
{
if (lean_obj_tag(v_x_2182_) == 0)
{
return v_x_2181_;
}
else
{
lean_object* v_key_2183_; lean_object* v_value_2184_; lean_object* v_tail_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2208_; 
v_key_2183_ = lean_ctor_get(v_x_2182_, 0);
v_value_2184_ = lean_ctor_get(v_x_2182_, 1);
v_tail_2185_ = lean_ctor_get(v_x_2182_, 2);
v_isSharedCheck_2208_ = !lean_is_exclusive(v_x_2182_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2187_ = v_x_2182_;
v_isShared_2188_ = v_isSharedCheck_2208_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_tail_2185_);
lean_inc(v_value_2184_);
lean_inc(v_key_2183_);
lean_dec(v_x_2182_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2208_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2189_; uint64_t v___x_2190_; uint64_t v___x_2191_; uint64_t v___x_2192_; uint64_t v_fold_2193_; uint64_t v___x_2194_; uint64_t v___x_2195_; uint64_t v___x_2196_; size_t v___x_2197_; size_t v___x_2198_; size_t v___x_2199_; size_t v___x_2200_; size_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2189_ = lean_array_get_size(v_x_2181_);
v___x_2190_ = l_Lean_ExprStructEq_hash(v_key_2183_);
v___x_2191_ = 32ULL;
v___x_2192_ = lean_uint64_shift_right(v___x_2190_, v___x_2191_);
v_fold_2193_ = lean_uint64_xor(v___x_2190_, v___x_2192_);
v___x_2194_ = 16ULL;
v___x_2195_ = lean_uint64_shift_right(v_fold_2193_, v___x_2194_);
v___x_2196_ = lean_uint64_xor(v_fold_2193_, v___x_2195_);
v___x_2197_ = lean_uint64_to_usize(v___x_2196_);
v___x_2198_ = lean_usize_of_nat(v___x_2189_);
v___x_2199_ = ((size_t)1ULL);
v___x_2200_ = lean_usize_sub(v___x_2198_, v___x_2199_);
v___x_2201_ = lean_usize_land(v___x_2197_, v___x_2200_);
v___x_2202_ = lean_array_uget_borrowed(v_x_2181_, v___x_2201_);
lean_inc(v___x_2202_);
if (v_isShared_2188_ == 0)
{
lean_ctor_set(v___x_2187_, 2, v___x_2202_);
v___x_2204_ = v___x_2187_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_key_2183_);
lean_ctor_set(v_reuseFailAlloc_2207_, 1, v_value_2184_);
lean_ctor_set(v_reuseFailAlloc_2207_, 2, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2205_; 
v___x_2205_ = lean_array_uset(v_x_2181_, v___x_2201_, v___x_2204_);
v_x_2181_ = v___x_2205_;
v_x_2182_ = v_tail_2185_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(lean_object* v_i_2209_, lean_object* v_source_2210_, lean_object* v_target_2211_){
_start:
{
lean_object* v___x_2212_; uint8_t v___x_2213_; 
v___x_2212_ = lean_array_get_size(v_source_2210_);
v___x_2213_ = lean_nat_dec_lt(v_i_2209_, v___x_2212_);
if (v___x_2213_ == 0)
{
lean_dec_ref(v_source_2210_);
lean_dec(v_i_2209_);
return v_target_2211_;
}
else
{
lean_object* v_es_2214_; lean_object* v___x_2215_; lean_object* v_source_2216_; lean_object* v_target_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; 
v_es_2214_ = lean_array_fget(v_source_2210_, v_i_2209_);
v___x_2215_ = lean_box(0);
v_source_2216_ = lean_array_fset(v_source_2210_, v_i_2209_, v___x_2215_);
v_target_2217_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_target_2211_, v_es_2214_);
v___x_2218_ = lean_unsigned_to_nat(1u);
v___x_2219_ = lean_nat_add(v_i_2209_, v___x_2218_);
lean_dec(v_i_2209_);
v_i_2209_ = v___x_2219_;
v_source_2210_ = v_source_2216_;
v_target_2211_ = v_target_2217_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(lean_object* v_data_2221_){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v_nbuckets_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2222_ = lean_array_get_size(v_data_2221_);
v___x_2223_ = lean_unsigned_to_nat(2u);
v_nbuckets_2224_ = lean_nat_mul(v___x_2222_, v___x_2223_);
v___x_2225_ = lean_unsigned_to_nat(0u);
v___x_2226_ = lean_box(0);
v___x_2227_ = lean_mk_array(v_nbuckets_2224_, v___x_2226_);
v___x_2228_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v___x_2225_, v_data_2221_, v___x_2227_);
return v___x_2228_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(lean_object* v_a_2229_, lean_object* v_x_2230_){
_start:
{
if (lean_obj_tag(v_x_2230_) == 0)
{
uint8_t v___x_2231_; 
v___x_2231_ = 0;
return v___x_2231_;
}
else
{
lean_object* v_key_2232_; lean_object* v_tail_2233_; uint8_t v___x_2234_; 
v_key_2232_ = lean_ctor_get(v_x_2230_, 0);
v_tail_2233_ = lean_ctor_get(v_x_2230_, 2);
v___x_2234_ = l_Lean_ExprStructEq_beq(v_key_2232_, v_a_2229_);
if (v___x_2234_ == 0)
{
v_x_2230_ = v_tail_2233_;
goto _start;
}
else
{
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg___boxed(lean_object* v_a_2236_, lean_object* v_x_2237_){
_start:
{
uint8_t v_res_2238_; lean_object* v_r_2239_; 
v_res_2238_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(v_a_2236_, v_x_2237_);
lean_dec(v_x_2237_);
lean_dec_ref(v_a_2236_);
v_r_2239_ = lean_box(v_res_2238_);
return v_r_2239_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(lean_object* v_a_2240_, lean_object* v_b_2241_, lean_object* v_x_2242_){
_start:
{
if (lean_obj_tag(v_x_2242_) == 0)
{
lean_dec(v_b_2241_);
lean_dec_ref(v_a_2240_);
return v_x_2242_;
}
else
{
lean_object* v_key_2243_; lean_object* v_value_2244_; lean_object* v_tail_2245_; lean_object* v___x_2247_; uint8_t v_isShared_2248_; uint8_t v_isSharedCheck_2257_; 
v_key_2243_ = lean_ctor_get(v_x_2242_, 0);
v_value_2244_ = lean_ctor_get(v_x_2242_, 1);
v_tail_2245_ = lean_ctor_get(v_x_2242_, 2);
v_isSharedCheck_2257_ = !lean_is_exclusive(v_x_2242_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2247_ = v_x_2242_;
v_isShared_2248_ = v_isSharedCheck_2257_;
goto v_resetjp_2246_;
}
else
{
lean_inc(v_tail_2245_);
lean_inc(v_value_2244_);
lean_inc(v_key_2243_);
lean_dec(v_x_2242_);
v___x_2247_ = lean_box(0);
v_isShared_2248_ = v_isSharedCheck_2257_;
goto v_resetjp_2246_;
}
v_resetjp_2246_:
{
uint8_t v___x_2249_; 
v___x_2249_ = l_Lean_ExprStructEq_beq(v_key_2243_, v_a_2240_);
if (v___x_2249_ == 0)
{
lean_object* v___x_2250_; lean_object* v___x_2252_; 
v___x_2250_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_a_2240_, v_b_2241_, v_tail_2245_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 2, v___x_2250_);
v___x_2252_ = v___x_2247_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_key_2243_);
lean_ctor_set(v_reuseFailAlloc_2253_, 1, v_value_2244_);
lean_ctor_set(v_reuseFailAlloc_2253_, 2, v___x_2250_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
else
{
lean_object* v___x_2255_; 
lean_dec(v_value_2244_);
lean_dec(v_key_2243_);
if (v_isShared_2248_ == 0)
{
lean_ctor_set(v___x_2247_, 1, v_b_2241_);
lean_ctor_set(v___x_2247_, 0, v_a_2240_);
v___x_2255_ = v___x_2247_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2240_);
lean_ctor_set(v_reuseFailAlloc_2256_, 1, v_b_2241_);
lean_ctor_set(v_reuseFailAlloc_2256_, 2, v_tail_2245_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(lean_object* v_m_2258_, lean_object* v_a_2259_, lean_object* v_b_2260_){
_start:
{
lean_object* v_size_2261_; lean_object* v_buckets_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2305_; 
v_size_2261_ = lean_ctor_get(v_m_2258_, 0);
v_buckets_2262_ = lean_ctor_get(v_m_2258_, 1);
v_isSharedCheck_2305_ = !lean_is_exclusive(v_m_2258_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2264_ = v_m_2258_;
v_isShared_2265_ = v_isSharedCheck_2305_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_buckets_2262_);
lean_inc(v_size_2261_);
lean_dec(v_m_2258_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2305_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; uint64_t v___x_2267_; uint64_t v___x_2268_; uint64_t v___x_2269_; uint64_t v_fold_2270_; uint64_t v___x_2271_; uint64_t v___x_2272_; uint64_t v___x_2273_; size_t v___x_2274_; size_t v___x_2275_; size_t v___x_2276_; size_t v___x_2277_; size_t v___x_2278_; lean_object* v_bkt_2279_; uint8_t v___x_2280_; 
v___x_2266_ = lean_array_get_size(v_buckets_2262_);
v___x_2267_ = l_Lean_ExprStructEq_hash(v_a_2259_);
v___x_2268_ = 32ULL;
v___x_2269_ = lean_uint64_shift_right(v___x_2267_, v___x_2268_);
v_fold_2270_ = lean_uint64_xor(v___x_2267_, v___x_2269_);
v___x_2271_ = 16ULL;
v___x_2272_ = lean_uint64_shift_right(v_fold_2270_, v___x_2271_);
v___x_2273_ = lean_uint64_xor(v_fold_2270_, v___x_2272_);
v___x_2274_ = lean_uint64_to_usize(v___x_2273_);
v___x_2275_ = lean_usize_of_nat(v___x_2266_);
v___x_2276_ = ((size_t)1ULL);
v___x_2277_ = lean_usize_sub(v___x_2275_, v___x_2276_);
v___x_2278_ = lean_usize_land(v___x_2274_, v___x_2277_);
v_bkt_2279_ = lean_array_uget_borrowed(v_buckets_2262_, v___x_2278_);
v___x_2280_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(v_a_2259_, v_bkt_2279_);
if (v___x_2280_ == 0)
{
lean_object* v___x_2281_; lean_object* v_size_x27_2282_; lean_object* v___x_2283_; lean_object* v_buckets_x27_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; 
v___x_2281_ = lean_unsigned_to_nat(1u);
v_size_x27_2282_ = lean_nat_add(v_size_2261_, v___x_2281_);
lean_dec(v_size_2261_);
lean_inc(v_bkt_2279_);
v___x_2283_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2283_, 0, v_a_2259_);
lean_ctor_set(v___x_2283_, 1, v_b_2260_);
lean_ctor_set(v___x_2283_, 2, v_bkt_2279_);
v_buckets_x27_2284_ = lean_array_uset(v_buckets_2262_, v___x_2278_, v___x_2283_);
v___x_2285_ = lean_unsigned_to_nat(4u);
v___x_2286_ = lean_nat_mul(v_size_x27_2282_, v___x_2285_);
v___x_2287_ = lean_unsigned_to_nat(3u);
v___x_2288_ = lean_nat_div(v___x_2286_, v___x_2287_);
lean_dec(v___x_2286_);
v___x_2289_ = lean_array_get_size(v_buckets_x27_2284_);
v___x_2290_ = lean_nat_dec_le(v___x_2288_, v___x_2289_);
lean_dec(v___x_2288_);
if (v___x_2290_ == 0)
{
lean_object* v_val_2291_; lean_object* v___x_2293_; 
v_val_2291_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_buckets_x27_2284_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v_val_2291_);
lean_ctor_set(v___x_2264_, 0, v_size_x27_2282_);
v___x_2293_ = v___x_2264_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_size_x27_2282_);
lean_ctor_set(v_reuseFailAlloc_2294_, 1, v_val_2291_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
else
{
lean_object* v___x_2296_; 
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v_buckets_x27_2284_);
lean_ctor_set(v___x_2264_, 0, v_size_x27_2282_);
v___x_2296_ = v___x_2264_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_size_x27_2282_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_buckets_x27_2284_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
else
{
lean_object* v___x_2298_; lean_object* v_buckets_x27_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2303_; 
lean_inc(v_bkt_2279_);
v___x_2298_ = lean_box(0);
v_buckets_x27_2299_ = lean_array_uset(v_buckets_2262_, v___x_2278_, v___x_2298_);
v___x_2300_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_a_2259_, v_b_2260_, v_bkt_2279_);
v___x_2301_ = lean_array_uset(v_buckets_x27_2299_, v___x_2278_, v___x_2300_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 1, v___x_2301_);
v___x_2303_ = v___x_2264_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_size_2261_);
lean_ctor_set(v_reuseFailAlloc_2304_, 1, v___x_2301_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(lean_object* v_a_2306_, lean_object* v_e_2307_, lean_object* v_a_2308_){
_start:
{
lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2310_ = lean_st_ref_take(v_a_2306_);
v___x_2311_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v___x_2310_, v_e_2307_, v_a_2308_);
v___x_2312_ = lean_st_ref_set(v_a_2306_, v___x_2311_);
v___x_2313_ = lean_box(0);
return v___x_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed(lean_object* v_a_2314_, lean_object* v_e_2315_, lean_object* v_a_2316_, lean_object* v___y_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2(v_a_2314_, v_e_2315_, v_a_2316_);
lean_dec(v_a_2314_);
return v_res_2318_;
}
}
static lean_object* _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0(void){
_start:
{
lean_object* v___x_2319_; lean_object* v_dummy_2320_; 
v___x_2319_ = lean_box(0);
v_dummy_2320_ = l_Lean_Expr_sort___override(v___x_2319_);
return v_dummy_2320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(lean_object* v_pre_2321_, lean_object* v_post_2322_, size_t v_sz_2323_, size_t v_i_2324_, lean_object* v_bs_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
uint8_t v___x_2330_; 
v___x_2330_ = lean_usize_dec_lt(v_i_2324_, v_sz_2323_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; 
lean_dec_ref(v_post_2322_);
lean_dec_ref(v_pre_2321_);
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_bs_2325_);
return v___x_2331_;
}
else
{
lean_object* v_v_2332_; lean_object* v___x_2333_; 
v_v_2332_ = lean_array_uget_borrowed(v_bs_2325_, v_i_2324_);
lean_inc(v_v_2332_);
lean_inc_ref(v_post_2322_);
lean_inc_ref(v_pre_2321_);
v___x_2333_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2321_, v_post_2322_, v_v_2332_, v___y_2326_, v___y_2327_, v___y_2328_);
if (lean_obj_tag(v___x_2333_) == 0)
{
lean_object* v_a_2334_; lean_object* v___x_2335_; lean_object* v_bs_x27_2336_; size_t v___x_2337_; size_t v___x_2338_; lean_object* v___x_2339_; 
v_a_2334_ = lean_ctor_get(v___x_2333_, 0);
lean_inc(v_a_2334_);
lean_dec_ref(v___x_2333_);
v___x_2335_ = lean_unsigned_to_nat(0u);
v_bs_x27_2336_ = lean_array_uset(v_bs_2325_, v_i_2324_, v___x_2335_);
v___x_2337_ = ((size_t)1ULL);
v___x_2338_ = lean_usize_add(v_i_2324_, v___x_2337_);
v___x_2339_ = lean_array_uset(v_bs_x27_2336_, v_i_2324_, v_a_2334_);
v_i_2324_ = v___x_2338_;
v_bs_2325_ = v___x_2339_;
goto _start;
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec_ref(v_bs_2325_);
lean_dec_ref(v_post_2322_);
lean_dec_ref(v_pre_2321_);
v_a_2341_ = lean_ctor_get(v___x_2333_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2333_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2333_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2333_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(lean_object* v_pre_2349_, lean_object* v_post_2350_, lean_object* v_x_2351_, lean_object* v_x_2352_, lean_object* v_x_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_){
_start:
{
if (lean_obj_tag(v_x_2351_) == 5)
{
lean_object* v_fn_2358_; lean_object* v_arg_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v_fn_2358_ = lean_ctor_get(v_x_2351_, 0);
lean_inc_ref(v_fn_2358_);
v_arg_2359_ = lean_ctor_get(v_x_2351_, 1);
lean_inc_ref(v_arg_2359_);
lean_dec_ref(v_x_2351_);
v___x_2360_ = lean_array_set(v_x_2352_, v_x_2353_, v_arg_2359_);
v___x_2361_ = lean_unsigned_to_nat(1u);
v___x_2362_ = lean_nat_sub(v_x_2353_, v___x_2361_);
lean_dec(v_x_2353_);
v_x_2351_ = v_fn_2358_;
v_x_2352_ = v___x_2360_;
v_x_2353_ = v___x_2362_;
goto _start;
}
else
{
lean_object* v___x_2364_; 
lean_dec(v_x_2353_);
lean_inc_ref(v_post_2350_);
lean_inc_ref(v_pre_2349_);
v___x_2364_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2349_, v_post_2350_, v_x_2351_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_object* v_a_2365_; size_t v_sz_2366_; size_t v___x_2367_; lean_object* v___x_2368_; 
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
lean_inc(v_a_2365_);
lean_dec_ref(v___x_2364_);
v_sz_2366_ = lean_array_size(v_x_2352_);
v___x_2367_ = ((size_t)0ULL);
lean_inc_ref(v_post_2350_);
lean_inc_ref(v_pre_2349_);
v___x_2368_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2349_, v_post_2350_, v_sz_2366_, v___x_2367_, v_x_2352_, v___y_2354_, v___y_2355_, v___y_2356_);
if (lean_obj_tag(v___x_2368_) == 0)
{
lean_object* v_a_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_a_2369_ = lean_ctor_get(v___x_2368_, 0);
lean_inc(v_a_2369_);
lean_dec_ref(v___x_2368_);
v___x_2370_ = l_Lean_mkAppN(v_a_2365_, v_a_2369_);
lean_dec(v_a_2369_);
v___x_2371_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2349_, v_post_2350_, v___x_2370_, v___y_2354_, v___y_2355_, v___y_2356_);
return v___x_2371_;
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_dec(v_a_2365_);
lean_dec_ref(v_post_2350_);
lean_dec_ref(v_pre_2349_);
v_a_2372_ = lean_ctor_get(v___x_2368_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2368_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2368_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2368_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
else
{
lean_dec_ref(v_x_2352_);
lean_dec_ref(v_post_2350_);
lean_dec_ref(v_pre_2349_);
return v___x_2364_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(lean_object* v_pre_2380_, lean_object* v_e_2381_, lean_object* v_post_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_){
_start:
{
uint8_t v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; uint8_t v___y_2395_; lean_object* v___y_2405_; lean_object* v___y_2406_; uint8_t v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; uint8_t v___y_2410_; uint8_t v___y_2418_; lean_object* v___y_2419_; lean_object* v___y_2420_; lean_object* v___y_2421_; lean_object* v___y_2422_; uint8_t v___y_2423_; lean_object* v___x_2430_; 
lean_inc_ref(v_pre_2380_);
lean_inc(v___y_2385_);
lean_inc_ref(v___y_2384_);
lean_inc_ref(v_e_2381_);
v___x_2430_ = lean_apply_4(v_pre_2380_, v_e_2381_, v___y_2384_, v___y_2385_, lean_box(0));
if (lean_obj_tag(v___x_2430_) == 0)
{
lean_object* v_a_2431_; lean_object* v___x_2433_; uint8_t v_isShared_2434_; uint8_t v_isSharedCheck_2520_; 
v_a_2431_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2520_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2520_ == 0)
{
v___x_2433_ = v___x_2430_;
v_isShared_2434_ = v_isSharedCheck_2520_;
goto v_resetjp_2432_;
}
else
{
lean_inc(v_a_2431_);
lean_dec(v___x_2430_);
v___x_2433_ = lean_box(0);
v_isShared_2434_ = v_isSharedCheck_2520_;
goto v_resetjp_2432_;
}
v_resetjp_2432_:
{
lean_object* v___y_2436_; 
switch(lean_obj_tag(v_a_2431_))
{
case 0:
{
lean_object* v_e_2510_; lean_object* v___x_2512_; 
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_e_2381_);
lean_dec_ref(v_pre_2380_);
v_e_2510_ = lean_ctor_get(v_a_2431_, 0);
lean_inc_ref(v_e_2510_);
lean_dec_ref(v_a_2431_);
if (v_isShared_2434_ == 0)
{
lean_ctor_set(v___x_2433_, 0, v_e_2510_);
v___x_2512_ = v___x_2433_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_e_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
case 1:
{
lean_object* v_e_2514_; lean_object* v___x_2515_; 
lean_del_object(v___x_2433_);
lean_dec_ref(v_e_2381_);
v_e_2514_ = lean_ctor_get(v_a_2431_, 0);
lean_inc_ref(v_e_2514_);
lean_dec_ref(v_a_2431_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2380_);
v___x_2515_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2380_, v_post_2382_, v_e_2514_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v_a_2516_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2517_;
}
else
{
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2380_);
return v___x_2515_;
}
}
default: 
{
lean_object* v_e_x3f_2518_; 
lean_del_object(v___x_2433_);
v_e_x3f_2518_ = lean_ctor_get(v_a_2431_, 0);
lean_inc(v_e_x3f_2518_);
lean_dec_ref(v_a_2431_);
if (lean_obj_tag(v_e_x3f_2518_) == 0)
{
v___y_2436_ = v_e_2381_;
goto v___jp_2435_;
}
else
{
lean_object* v_val_2519_; 
lean_dec_ref(v_e_2381_);
v_val_2519_ = lean_ctor_get(v_e_x3f_2518_, 0);
lean_inc(v_val_2519_);
lean_dec_ref(v_e_x3f_2518_);
v___y_2436_ = v_val_2519_;
goto v___jp_2435_;
}
}
}
v___jp_2435_:
{
switch(lean_obj_tag(v___y_2436_))
{
case 7:
{
lean_object* v_binderName_2437_; lean_object* v_binderType_2438_; lean_object* v_body_2439_; uint8_t v_binderInfo_2440_; lean_object* v___x_2441_; 
v_binderName_2437_ = lean_ctor_get(v___y_2436_, 0);
lean_inc(v_binderName_2437_);
v_binderType_2438_ = lean_ctor_get(v___y_2436_, 1);
v_body_2439_ = lean_ctor_get(v___y_2436_, 2);
v_binderInfo_2440_ = lean_ctor_get_uint8(v___y_2436_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2438_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2380_);
v___x_2441_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2380_, v_post_2382_, v_binderType_2438_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; lean_object* v___x_2443_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref(v___x_2441_);
lean_inc_ref(v_body_2439_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2380_);
v___x_2443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2380_, v_post_2382_, v_body_2439_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; size_t v___x_2445_; size_t v___x_2446_; uint8_t v___x_2447_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref(v___x_2443_);
v___x_2445_ = lean_ptr_addr(v_binderType_2438_);
v___x_2446_ = lean_ptr_addr(v_a_2442_);
v___x_2447_ = lean_usize_dec_eq(v___x_2445_, v___x_2446_);
if (v___x_2447_ == 0)
{
v___y_2418_ = v_binderInfo_2440_;
v___y_2419_ = v_a_2444_;
v___y_2420_ = v_a_2442_;
v___y_2421_ = v___y_2436_;
v___y_2422_ = v_binderName_2437_;
v___y_2423_ = v___x_2447_;
goto v___jp_2417_;
}
else
{
size_t v___x_2448_; size_t v___x_2449_; uint8_t v___x_2450_; 
v___x_2448_ = lean_ptr_addr(v_body_2439_);
v___x_2449_ = lean_ptr_addr(v_a_2444_);
v___x_2450_ = lean_usize_dec_eq(v___x_2448_, v___x_2449_);
v___y_2418_ = v_binderInfo_2440_;
v___y_2419_ = v_a_2444_;
v___y_2420_ = v_a_2442_;
v___y_2421_ = v___y_2436_;
v___y_2422_ = v_binderName_2437_;
v___y_2423_ = v___x_2450_;
goto v___jp_2417_;
}
}
else
{
lean_dec(v_a_2442_);
lean_dec(v_binderName_2437_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2380_);
return v___x_2443_;
}
}
else
{
lean_dec(v_binderName_2437_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2380_);
return v___x_2441_;
}
}
case 6:
{
lean_object* v_binderName_2451_; lean_object* v_binderType_2452_; lean_object* v_body_2453_; uint8_t v_binderInfo_2454_; lean_object* v___x_2455_; 
v_binderName_2451_ = lean_ctor_get(v___y_2436_, 0);
lean_inc(v_binderName_2451_);
v_binderType_2452_ = lean_ctor_get(v___y_2436_, 1);
v_body_2453_ = lean_ctor_get(v___y_2436_, 2);
v_binderInfo_2454_ = lean_ctor_get_uint8(v___y_2436_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_2452_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2380_);
v___x_2455_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2380_, v_post_2382_, v_binderType_2452_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; lean_object* v___x_2457_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref(v___x_2455_);
lean_inc_ref(v_body_2453_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2380_);
v___x_2457_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2380_, v_post_2382_, v_body_2453_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; size_t v___x_2459_; size_t v___x_2460_; uint8_t v___x_2461_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = lean_ptr_addr(v_binderType_2452_);
v___x_2460_ = lean_ptr_addr(v_a_2456_);
v___x_2461_ = lean_usize_dec_eq(v___x_2459_, v___x_2460_);
if (v___x_2461_ == 0)
{
v___y_2405_ = v_a_2456_;
v___y_2406_ = v_a_2458_;
v___y_2407_ = v_binderInfo_2454_;
v___y_2408_ = v_binderName_2451_;
v___y_2409_ = v___y_2436_;
v___y_2410_ = v___x_2461_;
goto v___jp_2404_;
}
else
{
size_t v___x_2462_; size_t v___x_2463_; uint8_t v___x_2464_; 
v___x_2462_ = lean_ptr_addr(v_body_2453_);
v___x_2463_ = lean_ptr_addr(v_a_2458_);
v___x_2464_ = lean_usize_dec_eq(v___x_2462_, v___x_2463_);
v___y_2405_ = v_a_2456_;
v___y_2406_ = v_a_2458_;
v___y_2407_ = v_binderInfo_2454_;
v___y_2408_ = v_binderName_2451_;
v___y_2409_ = v___y_2436_;
v___y_2410_ = v___x_2464_;
goto v___jp_2404_;
}
}
else
{
lean_dec(v_a_2456_);
lean_dec_ref(v___y_2436_);
lean_dec(v_binderName_2451_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2380_);
return v___x_2457_;
}
}
else
{
lean_dec(v_binderName_2451_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2380_);
return v___x_2455_;
}
}
case 8:
{
lean_object* v_declName_2465_; lean_object* v_type_2466_; lean_object* v_value_2467_; lean_object* v_body_2468_; uint8_t v_nondep_2469_; lean_object* v___x_2470_; 
v_declName_2465_ = lean_ctor_get(v___y_2436_, 0);
lean_inc(v_declName_2465_);
v_type_2466_ = lean_ctor_get(v___y_2436_, 1);
v_value_2467_ = lean_ctor_get(v___y_2436_, 2);
v_body_2468_ = lean_ctor_get(v___y_2436_, 3);
lean_inc_ref(v_body_2468_);
v_nondep_2469_ = lean_ctor_get_uint8(v___y_2436_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_2466_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2380_);
v___x_2470_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2380_, v_post_2382_, v_type_2466_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; lean_object* v___x_2472_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref(v___x_2470_);
lean_inc_ref(v_value_2467_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2380_);
v___x_2472_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2380_, v_post_2382_, v_value_2467_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; lean_object* v___x_2474_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref(v___x_2472_);
lean_inc_ref(v_body_2468_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2380_);
v___x_2474_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2380_, v_post_2382_, v_body_2468_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2474_) == 0)
{
lean_object* v_a_2475_; size_t v___x_2476_; size_t v___x_2477_; uint8_t v___x_2478_; 
v_a_2475_ = lean_ctor_get(v___x_2474_, 0);
lean_inc(v_a_2475_);
lean_dec_ref(v___x_2474_);
v___x_2476_ = lean_ptr_addr(v_type_2466_);
v___x_2477_ = lean_ptr_addr(v_a_2471_);
v___x_2478_ = lean_usize_dec_eq(v___x_2476_, v___x_2477_);
if (v___x_2478_ == 0)
{
v___y_2388_ = v_nondep_2469_;
v___y_2389_ = v_a_2471_;
v___y_2390_ = v_declName_2465_;
v___y_2391_ = v_a_2473_;
v___y_2392_ = v_body_2468_;
v___y_2393_ = v___y_2436_;
v___y_2394_ = v_a_2475_;
v___y_2395_ = v___x_2478_;
goto v___jp_2387_;
}
else
{
size_t v___x_2479_; size_t v___x_2480_; uint8_t v___x_2481_; 
v___x_2479_ = lean_ptr_addr(v_value_2467_);
v___x_2480_ = lean_ptr_addr(v_a_2473_);
v___x_2481_ = lean_usize_dec_eq(v___x_2479_, v___x_2480_);
v___y_2388_ = v_nondep_2469_;
v___y_2389_ = v_a_2471_;
v___y_2390_ = v_declName_2465_;
v___y_2391_ = v_a_2473_;
v___y_2392_ = v_body_2468_;
v___y_2393_ = v___y_2436_;
v___y_2394_ = v_a_2475_;
v___y_2395_ = v___x_2481_;
goto v___jp_2387_;
}
}
else
{
lean_dec(v_a_2473_);
lean_dec(v_a_2471_);
lean_dec_ref(v_body_2468_);
lean_dec_ref(v___y_2436_);
lean_dec(v_declName_2465_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2380_);
return v___x_2474_;
}
}
else
{
lean_dec(v_a_2471_);
lean_dec_ref(v_body_2468_);
lean_dec(v_declName_2465_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2380_);
return v___x_2472_;
}
}
else
{
lean_dec_ref(v_body_2468_);
lean_dec(v_declName_2465_);
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2380_);
return v___x_2470_;
}
}
case 5:
{
lean_object* v_dummy_2482_; lean_object* v_nargs_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v_dummy_2482_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_2483_ = l_Lean_Expr_getAppNumArgs(v___y_2436_);
lean_inc(v_nargs_2483_);
v___x_2484_ = lean_mk_array(v_nargs_2483_, v_dummy_2482_);
v___x_2485_ = lean_unsigned_to_nat(1u);
v___x_2486_ = lean_nat_sub(v_nargs_2483_, v___x_2485_);
lean_dec(v_nargs_2483_);
v___x_2487_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2380_, v_post_2382_, v___y_2436_, v___x_2484_, v___x_2486_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2487_;
}
case 10:
{
lean_object* v_data_2488_; lean_object* v_expr_2489_; lean_object* v___x_2490_; 
v_data_2488_ = lean_ctor_get(v___y_2436_, 0);
v_expr_2489_ = lean_ctor_get(v___y_2436_, 1);
lean_inc_ref(v_expr_2489_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2380_);
v___x_2490_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2380_, v_post_2382_, v_expr_2489_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; size_t v___x_2492_; size_t v___x_2493_; uint8_t v___x_2494_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref(v___x_2490_);
v___x_2492_ = lean_ptr_addr(v_expr_2489_);
v___x_2493_ = lean_ptr_addr(v_a_2491_);
v___x_2494_ = lean_usize_dec_eq(v___x_2492_, v___x_2493_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_inc(v_data_2488_);
lean_dec_ref(v___y_2436_);
v___x_2495_ = l_Lean_Expr_mdata___override(v_data_2488_, v_a_2491_);
v___x_2496_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___x_2495_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2496_;
}
else
{
lean_object* v___x_2497_; 
lean_dec(v_a_2491_);
v___x_2497_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___y_2436_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2497_;
}
}
else
{
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2380_);
return v___x_2490_;
}
}
case 11:
{
lean_object* v_typeName_2498_; lean_object* v_idx_2499_; lean_object* v_struct_2500_; lean_object* v___x_2501_; 
v_typeName_2498_ = lean_ctor_get(v___y_2436_, 0);
v_idx_2499_ = lean_ctor_get(v___y_2436_, 1);
v_struct_2500_ = lean_ctor_get(v___y_2436_, 2);
lean_inc_ref(v_struct_2500_);
lean_inc_ref(v_post_2382_);
lean_inc_ref(v_pre_2380_);
v___x_2501_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2380_, v_post_2382_, v_struct_2500_, v___y_2383_, v___y_2384_, v___y_2385_);
if (lean_obj_tag(v___x_2501_) == 0)
{
lean_object* v_a_2502_; size_t v___x_2503_; size_t v___x_2504_; uint8_t v___x_2505_; 
v_a_2502_ = lean_ctor_get(v___x_2501_, 0);
lean_inc(v_a_2502_);
lean_dec_ref(v___x_2501_);
v___x_2503_ = lean_ptr_addr(v_struct_2500_);
v___x_2504_ = lean_ptr_addr(v_a_2502_);
v___x_2505_ = lean_usize_dec_eq(v___x_2503_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_inc(v_idx_2499_);
lean_inc(v_typeName_2498_);
lean_dec_ref(v___y_2436_);
v___x_2506_ = l_Lean_Expr_proj___override(v_typeName_2498_, v_idx_2499_, v_a_2502_);
v___x_2507_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___x_2506_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2507_;
}
else
{
lean_object* v___x_2508_; 
lean_dec(v_a_2502_);
v___x_2508_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___y_2436_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2508_;
}
}
else
{
lean_dec_ref(v___y_2436_);
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_pre_2380_);
return v___x_2501_;
}
}
default: 
{
lean_object* v___x_2509_; 
v___x_2509_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___y_2436_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2509_;
}
}
}
}
}
else
{
lean_object* v_a_2521_; lean_object* v___x_2523_; uint8_t v_isShared_2524_; uint8_t v_isSharedCheck_2528_; 
lean_dec_ref(v_post_2382_);
lean_dec_ref(v_e_2381_);
lean_dec_ref(v_pre_2380_);
v_a_2521_ = lean_ctor_get(v___x_2430_, 0);
v_isSharedCheck_2528_ = !lean_is_exclusive(v___x_2430_);
if (v_isSharedCheck_2528_ == 0)
{
v___x_2523_ = v___x_2430_;
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
else
{
lean_inc(v_a_2521_);
lean_dec(v___x_2430_);
v___x_2523_ = lean_box(0);
v_isShared_2524_ = v_isSharedCheck_2528_;
goto v_resetjp_2522_;
}
v_resetjp_2522_:
{
lean_object* v___x_2526_; 
if (v_isShared_2524_ == 0)
{
v___x_2526_ = v___x_2523_;
goto v_reusejp_2525_;
}
else
{
lean_object* v_reuseFailAlloc_2527_; 
v_reuseFailAlloc_2527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2527_, 0, v_a_2521_);
v___x_2526_ = v_reuseFailAlloc_2527_;
goto v_reusejp_2525_;
}
v_reusejp_2525_:
{
return v___x_2526_;
}
}
}
v___jp_2387_:
{
if (v___y_2395_ == 0)
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_dec_ref(v___y_2393_);
lean_dec_ref(v___y_2392_);
v___x_2396_ = l_Lean_Expr_letE___override(v___y_2390_, v___y_2389_, v___y_2391_, v___y_2394_, v___y_2388_);
v___x_2397_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___x_2396_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2397_;
}
else
{
size_t v___x_2398_; size_t v___x_2399_; uint8_t v___x_2400_; 
v___x_2398_ = lean_ptr_addr(v___y_2392_);
lean_dec_ref(v___y_2392_);
v___x_2399_ = lean_ptr_addr(v___y_2394_);
v___x_2400_ = lean_usize_dec_eq(v___x_2398_, v___x_2399_);
if (v___x_2400_ == 0)
{
lean_object* v___x_2401_; lean_object* v___x_2402_; 
lean_dec_ref(v___y_2393_);
v___x_2401_ = l_Lean_Expr_letE___override(v___y_2390_, v___y_2389_, v___y_2391_, v___y_2394_, v___y_2388_);
v___x_2402_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___x_2401_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2402_;
}
else
{
lean_object* v___x_2403_; 
lean_dec_ref(v___y_2394_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
v___x_2403_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___y_2393_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2403_;
}
}
}
v___jp_2404_:
{
if (v___y_2410_ == 0)
{
lean_object* v___x_2411_; lean_object* v___x_2412_; 
lean_dec_ref(v___y_2409_);
v___x_2411_ = l_Lean_Expr_lam___override(v___y_2408_, v___y_2405_, v___y_2406_, v___y_2407_);
v___x_2412_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___x_2411_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2412_;
}
else
{
uint8_t v___x_2413_; 
v___x_2413_ = l_Lean_instBEqBinderInfo_beq(v___y_2407_, v___y_2407_);
if (v___x_2413_ == 0)
{
lean_object* v___x_2414_; lean_object* v___x_2415_; 
lean_dec_ref(v___y_2409_);
v___x_2414_ = l_Lean_Expr_lam___override(v___y_2408_, v___y_2405_, v___y_2406_, v___y_2407_);
v___x_2415_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___x_2414_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2415_;
}
else
{
lean_object* v___x_2416_; 
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2406_);
lean_dec_ref(v___y_2405_);
v___x_2416_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___y_2409_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2416_;
}
}
}
v___jp_2417_:
{
if (v___y_2423_ == 0)
{
lean_object* v___x_2424_; lean_object* v___x_2425_; 
lean_dec_ref(v___y_2421_);
v___x_2424_ = l_Lean_Expr_forallE___override(v___y_2422_, v___y_2420_, v___y_2419_, v___y_2418_);
v___x_2425_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___x_2424_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2425_;
}
else
{
uint8_t v___x_2426_; 
v___x_2426_ = l_Lean_instBEqBinderInfo_beq(v___y_2418_, v___y_2418_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec_ref(v___y_2421_);
v___x_2427_ = l_Lean_Expr_forallE___override(v___y_2422_, v___y_2420_, v___y_2419_, v___y_2418_);
v___x_2428_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___x_2427_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2428_;
}
else
{
lean_object* v___x_2429_; 
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2420_);
lean_dec_ref(v___y_2419_);
v___x_2429_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2380_, v_post_2382_, v___y_2421_, v___y_2383_, v___y_2384_, v___y_2385_);
return v___x_2429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_2529_, lean_object* v_e_2530_, lean_object* v_post_2531_, lean_object* v___y_2532_, lean_object* v___y_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1(v_pre_2529_, v_e_2530_, v_post_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
lean_dec(v___y_2534_);
lean_dec_ref(v___y_2533_);
lean_dec(v___y_2532_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(lean_object* v_pre_2537_, lean_object* v_post_2538_, lean_object* v_e_2539_, lean_object* v_a_2540_, lean_object* v___y_2541_, lean_object* v___y_2542_){
_start:
{
lean_object* v___x_2544_; lean_object* v___x_2545_; 
lean_inc(v_a_2540_);
v___x_2544_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2544_, 0, lean_box(0));
lean_closure_set(v___x_2544_, 1, lean_box(0));
lean_closure_set(v___x_2544_, 2, v_a_2540_);
v___x_2545_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___x_2544_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2545_) == 0)
{
lean_object* v_a_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2576_; 
v_a_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2576_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2576_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2576_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_a_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2576_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2550_; 
v___x_2550_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_2546_, v_e_2539_);
lean_dec(v_a_2546_);
if (lean_obj_tag(v___x_2550_) == 0)
{
lean_object* v___f_2551_; lean_object* v___x_2552_; 
lean_del_object(v___x_2548_);
lean_inc_ref(v_e_2539_);
v___f_2551_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___boxed), 7, 3);
lean_closure_set(v___f_2551_, 0, v_pre_2537_);
lean_closure_set(v___f_2551_, 1, v_e_2539_);
lean_closure_set(v___f_2551_, 2, v_post_2538_);
lean_inc_ref(v___y_2541_);
v___x_2552_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v___f_2551_, v_a_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___f_2554_; lean_object* v___x_2555_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref(v___x_2552_);
lean_inc(v_a_2553_);
lean_inc(v_a_2540_);
v___f_2554_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_2554_, 0, v_a_2540_);
lean_closure_set(v___f_2554_, 1, v_e_2539_);
lean_closure_set(v___f_2554_, 2, v_a_2553_);
v___x_2555_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__0(lean_box(0), v___f_2554_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2562_ == 0)
{
lean_object* v_unused_2563_; 
v_unused_2563_ = lean_ctor_get(v___x_2555_, 0);
lean_dec(v_unused_2563_);
v___x_2557_ = v___x_2555_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_dec(v___x_2555_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 0, v_a_2553_);
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2553_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec(v_a_2553_);
v_a_2564_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___x_2555_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___x_2555_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
else
{
lean_dec_ref(v_e_2539_);
return v___x_2552_;
}
}
else
{
lean_object* v_val_2572_; lean_object* v___x_2574_; 
lean_dec_ref(v_e_2539_);
lean_dec_ref(v_post_2538_);
lean_dec_ref(v_pre_2537_);
v_val_2572_ = lean_ctor_get(v___x_2550_, 0);
lean_inc(v_val_2572_);
lean_dec_ref(v___x_2550_);
if (v_isShared_2549_ == 0)
{
lean_ctor_set(v___x_2548_, 0, v_val_2572_);
v___x_2574_ = v___x_2548_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v_val_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
else
{
lean_object* v_a_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2584_; 
lean_dec_ref(v_e_2539_);
lean_dec_ref(v_post_2538_);
lean_dec_ref(v_pre_2537_);
v_a_2577_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2584_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2584_ == 0)
{
v___x_2579_ = v___x_2545_;
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_a_2577_);
lean_dec(v___x_2545_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2584_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2582_; 
if (v_isShared_2580_ == 0)
{
v___x_2582_ = v___x_2579_;
goto v_reusejp_2581_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
v___x_2582_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2581_;
}
v_reusejp_2581_:
{
return v___x_2582_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(lean_object* v_pre_2585_, lean_object* v_post_2586_, lean_object* v_e_2587_, lean_object* v_a_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_){
_start:
{
lean_object* v___x_2592_; 
lean_inc_ref(v_post_2586_);
lean_inc(v___y_2590_);
lean_inc_ref(v___y_2589_);
lean_inc_ref(v_e_2587_);
v___x_2592_ = lean_apply_4(v_post_2586_, v_e_2587_, v___y_2589_, v___y_2590_, lean_box(0));
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2611_; 
v_a_2593_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2611_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2611_ == 0)
{
v___x_2595_ = v___x_2592_;
v_isShared_2596_ = v_isSharedCheck_2611_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___x_2592_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2611_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
switch(lean_obj_tag(v_a_2593_))
{
case 0:
{
lean_object* v_e_2597_; lean_object* v___x_2599_; 
lean_dec_ref(v_e_2587_);
lean_dec_ref(v_post_2586_);
lean_dec_ref(v_pre_2585_);
v_e_2597_ = lean_ctor_get(v_a_2593_, 0);
lean_inc_ref(v_e_2597_);
lean_dec_ref(v_a_2593_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v_e_2597_);
v___x_2599_ = v___x_2595_;
goto v_reusejp_2598_;
}
else
{
lean_object* v_reuseFailAlloc_2600_; 
v_reuseFailAlloc_2600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2600_, 0, v_e_2597_);
v___x_2599_ = v_reuseFailAlloc_2600_;
goto v_reusejp_2598_;
}
v_reusejp_2598_:
{
return v___x_2599_;
}
}
case 1:
{
lean_object* v_e_2601_; lean_object* v___x_2602_; 
lean_del_object(v___x_2595_);
lean_dec_ref(v_e_2587_);
v_e_2601_ = lean_ctor_get(v_a_2593_, 0);
lean_inc_ref(v_e_2601_);
lean_dec_ref(v_a_2593_);
v___x_2602_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2585_, v_post_2586_, v_e_2601_, v_a_2588_, v___y_2589_, v___y_2590_);
return v___x_2602_;
}
default: 
{
lean_object* v_e_x3f_2603_; 
lean_dec_ref(v_post_2586_);
lean_dec_ref(v_pre_2585_);
v_e_x3f_2603_ = lean_ctor_get(v_a_2593_, 0);
lean_inc(v_e_x3f_2603_);
lean_dec_ref(v_a_2593_);
if (lean_obj_tag(v_e_x3f_2603_) == 0)
{
lean_object* v___x_2605_; 
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v_e_2587_);
v___x_2605_ = v___x_2595_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2606_; 
v_reuseFailAlloc_2606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_e_2587_);
v___x_2605_ = v_reuseFailAlloc_2606_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
return v___x_2605_;
}
}
else
{
lean_object* v_val_2607_; lean_object* v___x_2609_; 
lean_dec_ref(v_e_2587_);
v_val_2607_ = lean_ctor_get(v_e_x3f_2603_, 0);
lean_inc(v_val_2607_);
lean_dec_ref(v_e_x3f_2603_);
if (v_isShared_2596_ == 0)
{
lean_ctor_set(v___x_2595_, 0, v_val_2607_);
v___x_2609_ = v___x_2595_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2610_; 
v_reuseFailAlloc_2610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2610_, 0, v_val_2607_);
v___x_2609_ = v_reuseFailAlloc_2610_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
return v___x_2609_;
}
}
}
}
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v_e_2587_);
lean_dec_ref(v_post_2586_);
lean_dec_ref(v_pre_2585_);
v_a_2612_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2592_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2592_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_2620_, lean_object* v_post_2621_, lean_object* v_e_2622_, lean_object* v_a_2623_, lean_object* v___y_2624_, lean_object* v___y_2625_, lean_object* v___y_2626_){
_start:
{
lean_object* v_res_2627_; 
v_res_2627_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__2(v_pre_2620_, v_post_2621_, v_e_2622_, v_a_2623_, v___y_2624_, v___y_2625_);
lean_dec(v___y_2625_);
lean_dec_ref(v___y_2624_);
lean_dec(v_a_2623_);
return v_res_2627_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_2628_, lean_object* v_post_2629_, lean_object* v_sz_2630_, lean_object* v_i_2631_, lean_object* v_bs_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_){
_start:
{
size_t v_sz_boxed_2637_; size_t v_i_boxed_2638_; lean_object* v_res_2639_; 
v_sz_boxed_2637_ = lean_unbox_usize(v_sz_2630_);
lean_dec(v_sz_2630_);
v_i_boxed_2638_ = lean_unbox_usize(v_i_2631_);
lean_dec(v_i_2631_);
v_res_2639_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__1(v_pre_2628_, v_post_2629_, v_sz_boxed_2637_, v_i_boxed_2638_, v_bs_2632_, v___y_2633_, v___y_2634_, v___y_2635_);
lean_dec(v___y_2635_);
lean_dec_ref(v___y_2634_);
lean_dec(v___y_2633_);
return v_res_2639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4___boxed(lean_object* v_pre_2640_, lean_object* v_post_2641_, lean_object* v_x_2642_, lean_object* v_x_2643_, lean_object* v_x_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_, lean_object* v___y_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__4(v_pre_2640_, v_post_2641_, v_x_2642_, v_x_2643_, v_x_2644_, v___y_2645_, v___y_2646_, v___y_2647_);
lean_dec(v___y_2647_);
lean_dec_ref(v___y_2646_);
lean_dec(v___y_2645_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___boxed(lean_object* v_pre_2650_, lean_object* v_post_2651_, lean_object* v_e_2652_, lean_object* v_a_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2650_, v_post_2651_, v_e_2652_, v_a_2653_, v___y_2654_, v___y_2655_);
lean_dec(v___y_2655_);
lean_dec_ref(v___y_2654_);
lean_dec(v_a_2653_);
return v_res_2657_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v___x_2658_ = lean_box(0);
v___x_2659_ = lean_unsigned_to_nat(16u);
v___x_2660_ = lean_mk_array(v___x_2659_, v___x_2658_);
return v___x_2660_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1(void){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; 
v___x_2661_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__0);
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2662_);
lean_ctor_set(v___x_2663_, 1, v___x_2661_);
return v___x_2663_;
}
}
static lean_object* _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2(void){
_start:
{
lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2664_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__1);
v___x_2665_ = lean_alloc_closure((void*)(l_ST_Prim_mkRef___boxed), 4, 3);
lean_closure_set(v___x_2665_, 0, lean_box(0));
lean_closure_set(v___x_2665_, 1, lean_box(0));
lean_closure_set(v___x_2665_, 2, v___x_2664_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(lean_object* v_input_2666_, lean_object* v_pre_2667_, lean_object* v_post_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v_a_2674_; lean_object* v___x_2675_; 
v___x_2672_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_2673_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2672_, v___y_2669_, v___y_2670_);
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref(v___x_2673_);
v___x_2675_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0(v_pre_2667_, v_post_2668_, v_input_2666_, v_a_2674_, v___y_2669_, v___y_2670_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref(v___x_2675_);
v___x_2677_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_2677_, 0, lean_box(0));
lean_closure_set(v___x_2677_, 1, lean_box(0));
lean_closure_set(v___x_2677_, 2, v_a_2674_);
v___x_2678_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___lam__0(lean_box(0), v___x_2677_, v___y_2669_, v___y_2670_);
v_isSharedCheck_2685_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2685_ == 0)
{
lean_object* v_unused_2686_; 
v_unused_2686_ = lean_ctor_get(v___x_2678_, 0);
lean_dec(v_unused_2686_);
v___x_2680_ = v___x_2678_;
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
else
{
lean_dec(v___x_2678_);
v___x_2680_ = lean_box(0);
v_isShared_2681_ = v_isSharedCheck_2685_;
goto v_resetjp_2679_;
}
v_resetjp_2679_:
{
lean_object* v___x_2683_; 
if (v_isShared_2681_ == 0)
{
lean_ctor_set(v___x_2680_, 0, v_a_2676_);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2676_);
v___x_2683_ = v_reuseFailAlloc_2684_;
goto v_reusejp_2682_;
}
v_reusejp_2682_:
{
return v___x_2683_;
}
}
}
else
{
lean_dec(v_a_2674_);
return v___x_2675_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___boxed(lean_object* v_input_2687_, lean_object* v_pre_2688_, lean_object* v_post_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_input_2687_, v_pre_2688_, v_post_2689_, v___y_2690_, v___y_2691_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
return v_res_2693_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData(lean_object* v_e_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v___f_2701_; lean_object* v___x_2702_; 
v___f_2701_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__0));
v___x_2702_ = lean_find_expr(v___f_2701_, v_e_2697_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v___x_2703_; 
v___x_2703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2703_, 0, v_e_2697_);
return v___x_2703_;
}
else
{
lean_object* v_pre_2704_; lean_object* v___f_2705_; lean_object* v___x_2706_; 
lean_dec_ref(v___x_2702_);
v_pre_2704_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__1));
v___f_2705_ = ((lean_object*)(l_Lean_Meta_Grind_eraseIrrelevantMData___closed__2));
v___x_2706_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0(v_e_2697_, v_pre_2704_, v___f_2705_, v_a_2698_, v_a_2699_);
return v___x_2706_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseIrrelevantMData___boxed(lean_object* v_e_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_Meta_Grind_eraseIrrelevantMData(v_e_2707_, v_a_2708_, v_a_2709_);
lean_dec(v_a_2709_);
lean_dec_ref(v_a_2708_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(lean_object* v_00_u03b2_2712_, lean_object* v_m_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_m_2713_, v_a_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___boxed(lean_object* v_00_u03b2_2716_, lean_object* v_m_2717_, lean_object* v_a_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3(v_00_u03b2_2716_, v_m_2717_, v_a_2718_);
lean_dec_ref(v_a_2718_);
lean_dec_ref(v_m_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(lean_object* v_00_u03b1_2720_, lean_object* v_ref_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_2721_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___boxed(lean_object* v_00_u03b1_2726_, lean_object* v_ref_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_res_2731_; 
v_res_2731_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7(v_00_u03b1_2726_, v_ref_2727_, v___y_2728_, v___y_2729_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
return v_res_2731_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(lean_object* v_00_u03b1_2732_, lean_object* v_x_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_){
_start:
{
lean_object* v___x_2738_; 
lean_inc_ref(v___y_2735_);
v___x_2738_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v_x_2733_, v___y_2734_, v___y_2735_, v___y_2736_);
return v___x_2738_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___boxed(lean_object* v_00_u03b1_2739_, lean_object* v_x_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5(v_00_u03b1_2739_, v_x_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
return v_res_2745_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6(lean_object* v_00_u03b2_2746_, lean_object* v_m_2747_, lean_object* v_a_2748_, lean_object* v_b_2749_){
_start:
{
lean_object* v___x_2750_; 
v___x_2750_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6___redArg(v_m_2747_, v_a_2748_, v_b_2749_);
return v___x_2750_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(lean_object* v_00_u03b2_2751_, lean_object* v_a_2752_, lean_object* v_x_2753_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___redArg(v_a_2752_, v_x_2753_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4___boxed(lean_object* v_00_u03b2_2755_, lean_object* v_a_2756_, lean_object* v_x_2757_){
_start:
{
lean_object* v_res_2758_; 
v_res_2758_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3_spec__4(v_00_u03b2_2755_, v_a_2756_, v_x_2757_);
lean_dec(v_x_2757_);
lean_dec_ref(v_a_2756_);
return v_res_2758_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9(lean_object* v_00_u03b2_2759_, lean_object* v_a_2760_, lean_object* v_x_2761_){
_start:
{
uint8_t v___x_2762_; 
v___x_2762_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___redArg(v_a_2760_, v_x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9___boxed(lean_object* v_00_u03b2_2763_, lean_object* v_a_2764_, lean_object* v_x_2765_){
_start:
{
uint8_t v_res_2766_; lean_object* v_r_2767_; 
v_res_2766_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__9(v_00_u03b2_2763_, v_a_2764_, v_x_2765_);
lean_dec(v_x_2765_);
lean_dec_ref(v_a_2764_);
v_r_2767_ = lean_box(v_res_2766_);
return v_r_2767_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10(lean_object* v_00_u03b2_2768_, lean_object* v_data_2769_){
_start:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10___redArg(v_data_2769_);
return v___x_2770_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11(lean_object* v_00_u03b2_2771_, lean_object* v_a_2772_, lean_object* v_b_2773_, lean_object* v_x_2774_){
_start:
{
lean_object* v___x_2775_; 
v___x_2775_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__11___redArg(v_a_2772_, v_b_2773_, v_x_2774_);
return v___x_2775_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11(lean_object* v_00_u03b2_2776_, lean_object* v_i_2777_, lean_object* v_source_2778_, lean_object* v_target_2779_){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11___redArg(v_i_2777_, v_source_2778_, v_target_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12(lean_object* v_00_u03b2_2781_, lean_object* v_x_2782_, lean_object* v_x_2783_){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__6_spec__10_spec__11_spec__12___redArg(v_x_2782_, v_x_2783_);
return v___x_2784_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(lean_object* v_cls_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v_options_2791_; uint8_t v_hasTrace_2792_; 
v_options_2791_ = lean_ctor_get(v___y_2789_, 2);
v_hasTrace_2792_ = lean_ctor_get_uint8(v_options_2791_, sizeof(void*)*1);
if (v_hasTrace_2792_ == 0)
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
lean_dec(v_cls_2788_);
v___x_2793_ = lean_box(v_hasTrace_2792_);
v___x_2794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2793_);
return v___x_2794_;
}
else
{
lean_object* v_inheritedTraceOptions_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; uint8_t v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; 
v_inheritedTraceOptions_2795_ = lean_ctor_get(v___y_2789_, 13);
v___x_2796_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___closed__1));
v___x_2797_ = l_Lean_Name_append(v___x_2796_, v_cls_2788_);
v___x_2798_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2795_, v_options_2791_, v___x_2797_);
lean_dec(v___x_2797_);
v___x_2799_ = lean_box(v___x_2798_);
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2799_);
return v___x_2800_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg___boxed(lean_object* v_cls_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(v_cls_2801_, v___y_2802_);
lean_dec_ref(v___y_2802_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0(lean_object* v_cls_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v___x_2811_; 
v___x_2811_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(v_cls_2805_, v___y_2808_);
return v___x_2811_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___boxed(lean_object* v_cls_2812_, lean_object* v___y_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_res_2818_; 
v_res_2818_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0(v_cls_2812_, v___y_2813_, v___y_2814_, v___y_2815_, v___y_2816_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
lean_dec_ref(v___y_2813_);
return v_res_2818_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__1(lean_object* v_msgData_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_, lean_object* v___y_2822_, lean_object* v___y_2823_){
_start:
{
lean_object* v___x_2825_; lean_object* v_env_2826_; lean_object* v___x_2827_; lean_object* v_mctx_2828_; lean_object* v_lctx_2829_; lean_object* v_options_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2825_ = lean_st_ref_get(v___y_2823_);
v_env_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc_ref(v_env_2826_);
lean_dec(v___x_2825_);
v___x_2827_ = lean_st_ref_get(v___y_2821_);
v_mctx_2828_ = lean_ctor_get(v___x_2827_, 0);
lean_inc_ref(v_mctx_2828_);
lean_dec(v___x_2827_);
v_lctx_2829_ = lean_ctor_get(v___y_2820_, 2);
v_options_2830_ = lean_ctor_get(v___y_2822_, 2);
lean_inc_ref(v_options_2830_);
lean_inc_ref(v_lctx_2829_);
v___x_2831_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2831_, 0, v_env_2826_);
lean_ctor_set(v___x_2831_, 1, v_mctx_2828_);
lean_ctor_set(v___x_2831_, 2, v_lctx_2829_);
lean_ctor_set(v___x_2831_, 3, v_options_2830_);
v___x_2832_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2831_);
lean_ctor_set(v___x_2832_, 1, v_msgData_2819_);
v___x_2833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2833_, 0, v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__1___boxed(lean_object* v_msgData_2834_, lean_object* v___y_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_){
_start:
{
lean_object* v_res_2840_; 
v_res_2840_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__1(v_msgData_2834_, v___y_2835_, v___y_2836_, v___y_2837_, v___y_2838_);
lean_dec(v___y_2838_);
lean_dec_ref(v___y_2837_);
lean_dec(v___y_2836_);
lean_dec_ref(v___y_2835_);
return v_res_2840_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__0(void){
_start:
{
lean_object* v___x_2841_; double v___x_2842_; 
v___x_2841_ = lean_unsigned_to_nat(0u);
v___x_2842_ = lean_float_of_nat(v___x_2841_);
return v___x_2842_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1(lean_object* v_cls_2846_, lean_object* v_msg_2847_, lean_object* v___y_2848_, lean_object* v___y_2849_, lean_object* v___y_2850_, lean_object* v___y_2851_){
_start:
{
lean_object* v_ref_2853_; lean_object* v___x_2854_; lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2899_; 
v_ref_2853_ = lean_ctor_get(v___y_2850_, 5);
v___x_2854_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__1(v_msg_2847_, v___y_2848_, v___y_2849_, v___y_2850_, v___y_2851_);
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2857_ = v___x_2854_;
v_isShared_2858_ = v_isSharedCheck_2899_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2854_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2899_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2859_; lean_object* v_traceState_2860_; lean_object* v_env_2861_; lean_object* v_nextMacroScope_2862_; lean_object* v_ngen_2863_; lean_object* v_auxDeclNGen_2864_; lean_object* v_cache_2865_; lean_object* v_messages_2866_; lean_object* v_infoState_2867_; lean_object* v_snapshotTasks_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2898_; 
v___x_2859_ = lean_st_ref_take(v___y_2851_);
v_traceState_2860_ = lean_ctor_get(v___x_2859_, 4);
v_env_2861_ = lean_ctor_get(v___x_2859_, 0);
v_nextMacroScope_2862_ = lean_ctor_get(v___x_2859_, 1);
v_ngen_2863_ = lean_ctor_get(v___x_2859_, 2);
v_auxDeclNGen_2864_ = lean_ctor_get(v___x_2859_, 3);
v_cache_2865_ = lean_ctor_get(v___x_2859_, 5);
v_messages_2866_ = lean_ctor_get(v___x_2859_, 6);
v_infoState_2867_ = lean_ctor_get(v___x_2859_, 7);
v_snapshotTasks_2868_ = lean_ctor_get(v___x_2859_, 8);
v_isSharedCheck_2898_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2898_ == 0)
{
v___x_2870_ = v___x_2859_;
v_isShared_2871_ = v_isSharedCheck_2898_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_snapshotTasks_2868_);
lean_inc(v_infoState_2867_);
lean_inc(v_messages_2866_);
lean_inc(v_cache_2865_);
lean_inc(v_traceState_2860_);
lean_inc(v_auxDeclNGen_2864_);
lean_inc(v_ngen_2863_);
lean_inc(v_nextMacroScope_2862_);
lean_inc(v_env_2861_);
lean_dec(v___x_2859_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2898_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
uint64_t v_tid_2872_; lean_object* v_traces_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2897_; 
v_tid_2872_ = lean_ctor_get_uint64(v_traceState_2860_, sizeof(void*)*1);
v_traces_2873_ = lean_ctor_get(v_traceState_2860_, 0);
v_isSharedCheck_2897_ = !lean_is_exclusive(v_traceState_2860_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2875_ = v_traceState_2860_;
v_isShared_2876_ = v_isSharedCheck_2897_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_traces_2873_);
lean_dec(v_traceState_2860_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2897_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___x_2877_; double v___x_2878_; uint8_t v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2887_; 
v___x_2877_ = lean_box(0);
v___x_2878_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__0);
v___x_2879_ = 0;
v___x_2880_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__1));
v___x_2881_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2881_, 0, v_cls_2846_);
lean_ctor_set(v___x_2881_, 1, v___x_2877_);
lean_ctor_set(v___x_2881_, 2, v___x_2880_);
lean_ctor_set_float(v___x_2881_, sizeof(void*)*3, v___x_2878_);
lean_ctor_set_float(v___x_2881_, sizeof(void*)*3 + 8, v___x_2878_);
lean_ctor_set_uint8(v___x_2881_, sizeof(void*)*3 + 16, v___x_2879_);
v___x_2882_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___closed__2));
v___x_2883_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set(v___x_2883_, 1, v_a_2855_);
lean_ctor_set(v___x_2883_, 2, v___x_2882_);
lean_inc(v_ref_2853_);
v___x_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2884_, 0, v_ref_2853_);
lean_ctor_set(v___x_2884_, 1, v___x_2883_);
v___x_2885_ = l_Lean_PersistentArray_push___redArg(v_traces_2873_, v___x_2884_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set(v___x_2875_, 0, v___x_2885_);
v___x_2887_ = v___x_2875_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2885_);
lean_ctor_set_uint64(v_reuseFailAlloc_2896_, sizeof(void*)*1, v_tid_2872_);
v___x_2887_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
lean_object* v___x_2889_; 
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 4, v___x_2887_);
v___x_2889_ = v___x_2870_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2895_; 
v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2895_, 0, v_env_2861_);
lean_ctor_set(v_reuseFailAlloc_2895_, 1, v_nextMacroScope_2862_);
lean_ctor_set(v_reuseFailAlloc_2895_, 2, v_ngen_2863_);
lean_ctor_set(v_reuseFailAlloc_2895_, 3, v_auxDeclNGen_2864_);
lean_ctor_set(v_reuseFailAlloc_2895_, 4, v___x_2887_);
lean_ctor_set(v_reuseFailAlloc_2895_, 5, v_cache_2865_);
lean_ctor_set(v_reuseFailAlloc_2895_, 6, v_messages_2866_);
lean_ctor_set(v_reuseFailAlloc_2895_, 7, v_infoState_2867_);
lean_ctor_set(v_reuseFailAlloc_2895_, 8, v_snapshotTasks_2868_);
v___x_2889_ = v_reuseFailAlloc_2895_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2893_; 
v___x_2890_ = lean_st_ref_set(v___y_2851_, v___x_2889_);
v___x_2891_ = lean_box(0);
if (v_isShared_2858_ == 0)
{
lean_ctor_set(v___x_2857_, 0, v___x_2891_);
v___x_2893_ = v___x_2857_;
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
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1___boxed(lean_object* v_cls_2900_, lean_object* v_msg_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_, lean_object* v___y_2904_, lean_object* v___y_2905_, lean_object* v___y_2906_){
_start:
{
lean_object* v_res_2907_; 
v_res_2907_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1(v_cls_2900_, v_msg_2901_, v___y_2902_, v___y_2903_, v___y_2904_, v___y_2905_);
lean_dec(v___y_2905_);
lean_dec_ref(v___y_2904_);
lean_dec(v___y_2903_);
lean_dec_ref(v___y_2902_);
return v_res_2907_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2913_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__2));
v___x_2914_ = l_Lean_stringToMessageData(v___x_2913_);
return v___x_2914_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; 
v___x_2916_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__4));
v___x_2917_ = l_Lean_stringToMessageData(v___x_2916_);
return v___x_2917_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__6(void){
_start:
{
uint8_t v___x_2918_; uint64_t v___x_2919_; 
v___x_2918_ = 1;
v___x_2919_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2918_);
return v___x_2919_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; 
v___x_2921_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__7));
v___x_2922_ = l_Lean_stringToMessageData(v___x_2921_);
return v___x_2922_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2924_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__9));
v___x_2925_ = l_Lean_stringToMessageData(v___x_2924_);
return v___x_2925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0(lean_object* v_e_2926_, lean_object* v___y_2927_, lean_object* v___y_2928_, lean_object* v___y_2929_, lean_object* v___y_2930_){
_start:
{
if (lean_obj_tag(v_e_2926_) == 11)
{
lean_object* v_typeName_2938_; lean_object* v_idx_2939_; lean_object* v_struct_2940_; lean_object* v___x_2941_; lean_object* v_env_2942_; lean_object* v___x_2943_; 
v_typeName_2938_ = lean_ctor_get(v_e_2926_, 0);
v_idx_2939_ = lean_ctor_get(v_e_2926_, 1);
v_struct_2940_ = lean_ctor_get(v_e_2926_, 2);
v___x_2941_ = lean_st_ref_get(v___y_2930_);
v_env_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc_ref(v_env_2942_);
lean_dec(v___x_2941_);
lean_inc(v_typeName_2938_);
v___x_2943_ = l_Lean_getStructureInfo_x3f(v_env_2942_, v_typeName_2938_);
if (lean_obj_tag(v___x_2943_) == 1)
{
lean_object* v_val_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_3045_; 
v_val_2944_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_2946_ = v___x_2943_;
v_isShared_2947_ = v_isSharedCheck_3045_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_val_2944_);
lean_dec(v___x_2943_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_3045_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v_fieldNames_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; 
v_fieldNames_2948_ = lean_ctor_get(v_val_2944_, 1);
lean_inc_ref(v_fieldNames_2948_);
lean_dec(v_val_2944_);
v___x_2949_ = lean_array_get_size(v_fieldNames_2948_);
v___x_2950_ = lean_nat_dec_lt(v_idx_2939_, v___x_2949_);
if (v___x_2950_ == 0)
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2978_; 
lean_dec_ref(v_fieldNames_2948_);
lean_del_object(v___x_2946_);
v___x_2951_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__1));
v___x_2952_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(v___x_2951_, v___y_2929_);
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2978_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2978_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
uint8_t v___x_2957_; 
v___x_2957_ = lean_unbox(v_a_2953_);
lean_dec(v_a_2953_);
if (v___x_2957_ == 0)
{
lean_del_object(v___x_2955_);
goto v___jp_2932_;
}
else
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2961_; 
v___x_2958_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__3, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__3_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__3);
lean_inc(v_idx_2939_);
v___x_2959_ = l_Nat_reprFast(v_idx_2939_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set_tag(v___x_2955_, 3);
lean_ctor_set(v___x_2955_, 0, v___x_2959_);
v___x_2961_ = v___x_2955_;
goto v_reusejp_2960_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v___x_2959_);
v___x_2961_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2960_;
}
v_reusejp_2960_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v___x_2962_ = l_Lean_MessageData_ofFormat(v___x_2961_);
v___x_2963_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2963_, 0, v___x_2958_);
lean_ctor_set(v___x_2963_, 1, v___x_2962_);
v___x_2964_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__5, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__5_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__5);
v___x_2965_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2963_);
lean_ctor_set(v___x_2965_, 1, v___x_2964_);
lean_inc_ref(v_e_2926_);
v___x_2966_ = l_Lean_indentExpr(v_e_2926_);
v___x_2967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2965_);
lean_ctor_set(v___x_2967_, 1, v___x_2966_);
v___x_2968_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1(v___x_2951_, v___x_2967_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_dec_ref(v___x_2968_);
goto v___jp_2932_;
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec_ref(v_e_2926_);
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2968_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2979_; uint8_t v_foApprox_2980_; uint8_t v_ctxApprox_2981_; uint8_t v_quasiPatternApprox_2982_; uint8_t v_constApprox_2983_; uint8_t v_isDefEqStuckEx_2984_; uint8_t v_unificationHints_2985_; uint8_t v_proofIrrelevance_2986_; uint8_t v_assignSyntheticOpaque_2987_; uint8_t v_offsetCnstrs_2988_; uint8_t v_etaStruct_2989_; uint8_t v_univApprox_2990_; uint8_t v_iota_2991_; uint8_t v_beta_2992_; uint8_t v_proj_2993_; uint8_t v_zeta_2994_; uint8_t v_zetaDelta_2995_; uint8_t v_zetaUnused_2996_; uint8_t v_zetaHave_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3044_; 
lean_inc_ref(v_struct_2940_);
lean_inc(v_idx_2939_);
lean_dec_ref(v_e_2926_);
v___x_2979_ = l_Lean_Meta_Context_config(v___y_2927_);
v_foApprox_2980_ = lean_ctor_get_uint8(v___x_2979_, 0);
v_ctxApprox_2981_ = lean_ctor_get_uint8(v___x_2979_, 1);
v_quasiPatternApprox_2982_ = lean_ctor_get_uint8(v___x_2979_, 2);
v_constApprox_2983_ = lean_ctor_get_uint8(v___x_2979_, 3);
v_isDefEqStuckEx_2984_ = lean_ctor_get_uint8(v___x_2979_, 4);
v_unificationHints_2985_ = lean_ctor_get_uint8(v___x_2979_, 5);
v_proofIrrelevance_2986_ = lean_ctor_get_uint8(v___x_2979_, 6);
v_assignSyntheticOpaque_2987_ = lean_ctor_get_uint8(v___x_2979_, 7);
v_offsetCnstrs_2988_ = lean_ctor_get_uint8(v___x_2979_, 8);
v_etaStruct_2989_ = lean_ctor_get_uint8(v___x_2979_, 10);
v_univApprox_2990_ = lean_ctor_get_uint8(v___x_2979_, 11);
v_iota_2991_ = lean_ctor_get_uint8(v___x_2979_, 12);
v_beta_2992_ = lean_ctor_get_uint8(v___x_2979_, 13);
v_proj_2993_ = lean_ctor_get_uint8(v___x_2979_, 14);
v_zeta_2994_ = lean_ctor_get_uint8(v___x_2979_, 15);
v_zetaDelta_2995_ = lean_ctor_get_uint8(v___x_2979_, 16);
v_zetaUnused_2996_ = lean_ctor_get_uint8(v___x_2979_, 17);
v_zetaHave_2997_ = lean_ctor_get_uint8(v___x_2979_, 18);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_2999_ = v___x_2979_;
v_isShared_3000_ = v_isSharedCheck_3044_;
goto v_resetjp_2998_;
}
else
{
lean_dec(v___x_2979_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3044_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
uint8_t v_trackZetaDelta_3001_; lean_object* v_zetaDeltaSet_3002_; lean_object* v_lctx_3003_; lean_object* v_localInstances_3004_; lean_object* v_defEqCtx_x3f_3005_; lean_object* v_synthPendingDepth_3006_; lean_object* v_canUnfold_x3f_3007_; uint8_t v_univApprox_3008_; uint8_t v_inTypeClassResolution_3009_; uint8_t v_cacheInferType_3010_; uint8_t v___x_3011_; lean_object* v_config_3013_; 
v_trackZetaDelta_3001_ = lean_ctor_get_uint8(v___y_2927_, sizeof(void*)*7);
v_zetaDeltaSet_3002_ = lean_ctor_get(v___y_2927_, 1);
v_lctx_3003_ = lean_ctor_get(v___y_2927_, 2);
v_localInstances_3004_ = lean_ctor_get(v___y_2927_, 3);
v_defEqCtx_x3f_3005_ = lean_ctor_get(v___y_2927_, 4);
v_synthPendingDepth_3006_ = lean_ctor_get(v___y_2927_, 5);
v_canUnfold_x3f_3007_ = lean_ctor_get(v___y_2927_, 6);
v_univApprox_3008_ = lean_ctor_get_uint8(v___y_2927_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3009_ = lean_ctor_get_uint8(v___y_2927_, sizeof(void*)*7 + 2);
v_cacheInferType_3010_ = lean_ctor_get_uint8(v___y_2927_, sizeof(void*)*7 + 3);
v___x_3011_ = 1;
if (v_isShared_3000_ == 0)
{
v_config_3013_ = v___x_2999_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 0, v_foApprox_2980_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 1, v_ctxApprox_2981_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 2, v_quasiPatternApprox_2982_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 3, v_constApprox_2983_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 4, v_isDefEqStuckEx_2984_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 5, v_unificationHints_2985_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 6, v_proofIrrelevance_2986_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 7, v_assignSyntheticOpaque_2987_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 8, v_offsetCnstrs_2988_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 10, v_etaStruct_2989_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 11, v_univApprox_2990_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 12, v_iota_2991_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 13, v_beta_2992_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 14, v_proj_2993_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 15, v_zeta_2994_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 16, v_zetaDelta_2995_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 17, v_zetaUnused_2996_);
lean_ctor_set_uint8(v_reuseFailAlloc_3043_, 18, v_zetaHave_2997_);
v_config_3013_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
uint64_t v___x_3014_; uint64_t v___x_3015_; uint64_t v___x_3016_; lean_object* v___x_3017_; uint64_t v___x_3018_; uint64_t v___x_3019_; uint64_t v_key_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; lean_object* v___x_3023_; 
lean_ctor_set_uint8(v_config_3013_, 9, v___x_3011_);
v___x_3014_ = l_Lean_Meta_Context_configKey(v___y_2927_);
v___x_3015_ = 2ULL;
v___x_3016_ = lean_uint64_shift_right(v___x_3014_, v___x_3015_);
v___x_3017_ = lean_array_fget(v_fieldNames_2948_, v_idx_2939_);
lean_dec(v_idx_2939_);
lean_dec_ref(v_fieldNames_2948_);
v___x_3018_ = lean_uint64_shift_left(v___x_3016_, v___x_3015_);
v___x_3019_ = lean_uint64_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__6, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__6_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__6);
v_key_3020_ = lean_uint64_lor(v___x_3018_, v___x_3019_);
v___x_3021_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3021_, 0, v_config_3013_);
lean_ctor_set_uint64(v___x_3021_, sizeof(void*)*1, v_key_3020_);
lean_inc(v_canUnfold_x3f_3007_);
lean_inc(v_synthPendingDepth_3006_);
lean_inc(v_defEqCtx_x3f_3005_);
lean_inc_ref(v_localInstances_3004_);
lean_inc_ref(v_lctx_3003_);
lean_inc(v_zetaDeltaSet_3002_);
v___x_3022_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3022_, 0, v___x_3021_);
lean_ctor_set(v___x_3022_, 1, v_zetaDeltaSet_3002_);
lean_ctor_set(v___x_3022_, 2, v_lctx_3003_);
lean_ctor_set(v___x_3022_, 3, v_localInstances_3004_);
lean_ctor_set(v___x_3022_, 4, v_defEqCtx_x3f_3005_);
lean_ctor_set(v___x_3022_, 5, v_synthPendingDepth_3006_);
lean_ctor_set(v___x_3022_, 6, v_canUnfold_x3f_3007_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*7, v_trackZetaDelta_3001_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*7 + 1, v_univApprox_3008_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3009_);
lean_ctor_set_uint8(v___x_3022_, sizeof(void*)*7 + 3, v_cacheInferType_3010_);
v___x_3023_ = l_Lean_Meta_mkProjection(v_struct_2940_, v___x_3017_, v___x_3022_, v___y_2928_, v___y_2929_, v___y_2930_);
lean_dec_ref(v___x_3022_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___x_3026_; uint8_t v_isShared_3027_; uint8_t v_isSharedCheck_3034_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3026_ = v___x_3023_;
v_isShared_3027_ = v_isSharedCheck_3034_;
goto v_resetjp_3025_;
}
else
{
lean_inc(v_a_3024_);
lean_dec(v___x_3023_);
v___x_3026_ = lean_box(0);
v_isShared_3027_ = v_isSharedCheck_3034_;
goto v_resetjp_3025_;
}
v_resetjp_3025_:
{
lean_object* v___x_3029_; 
if (v_isShared_2947_ == 0)
{
lean_ctor_set(v___x_2946_, 0, v_a_3024_);
v___x_3029_ = v___x_2946_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3024_);
v___x_3029_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
lean_object* v___x_3031_; 
if (v_isShared_3027_ == 0)
{
lean_ctor_set(v___x_3026_, 0, v___x_3029_);
v___x_3031_ = v___x_3026_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v___x_3029_);
v___x_3031_ = v_reuseFailAlloc_3032_;
goto v_reusejp_3030_;
}
v_reusejp_3030_:
{
return v___x_3031_;
}
}
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_del_object(v___x_2946_);
v_a_3035_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3023_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3023_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
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
lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v_a_3048_; uint8_t v___x_3049_; 
lean_dec(v___x_2943_);
v___x_3046_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__1));
v___x_3047_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_Grind_foldProjs_spec__0___redArg(v___x_3046_, v___y_2929_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = lean_unbox(v_a_3048_);
lean_dec(v_a_3048_);
if (v___x_3049_ == 0)
{
goto v___jp_2935_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3050_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__8, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__8_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__8);
lean_inc(v_typeName_2938_);
v___x_3051_ = l_Lean_MessageData_ofName(v_typeName_2938_);
v___x_3052_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3052_, 0, v___x_3050_);
lean_ctor_set(v___x_3052_, 1, v___x_3051_);
v___x_3053_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__10, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__10_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__10);
v___x_3054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3052_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
lean_inc_ref(v_e_2926_);
v___x_3055_ = l_Lean_indentExpr(v_e_2926_);
v___x_3056_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3054_);
lean_ctor_set(v___x_3056_, 1, v___x_3055_);
v___x_3057_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__1(v___x_3046_, v___x_3056_, v___y_2927_, v___y_2928_, v___y_2929_, v___y_2930_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_dec_ref(v___x_3057_);
goto v___jp_2935_;
}
else
{
lean_object* v_a_3058_; lean_object* v___x_3060_; uint8_t v_isShared_3061_; uint8_t v_isSharedCheck_3065_; 
lean_dec_ref(v_e_2926_);
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3060_ = v___x_3057_;
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
else
{
lean_inc(v_a_3058_);
lean_dec(v___x_3057_);
v___x_3060_ = lean_box(0);
v_isShared_3061_ = v_isSharedCheck_3065_;
goto v_resetjp_3059_;
}
v_resetjp_3059_:
{
lean_object* v___x_3063_; 
if (v_isShared_3061_ == 0)
{
v___x_3063_ = v___x_3060_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v_a_3058_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
}
}
}
else
{
lean_object* v___x_3066_; lean_object* v___x_3067_; 
v___x_3066_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3066_, 0, v_e_2926_);
v___x_3067_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
return v___x_3067_;
}
v___jp_2932_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2933_, 0, v_e_2926_);
v___x_2934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2934_, 0, v___x_2933_);
return v___x_2934_;
}
v___jp_2935_:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2936_, 0, v_e_2926_);
v___x_2937_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2936_);
return v___x_2937_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___boxed(lean_object* v_e_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_, lean_object* v___y_3073_){
_start:
{
lean_object* v_res_3074_; 
v_res_3074_ = l_Lean_Meta_Grind_foldProjs___lam__0(v_e_3068_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
lean_dec(v___y_3072_);
lean_dec_ref(v___y_3071_);
lean_dec(v___y_3070_);
lean_dec_ref(v___y_3069_);
return v_res_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1(lean_object* v_x_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_, lean_object* v___y_3081_){
_start:
{
lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3083_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__1___closed__0));
v___x_3084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1___boxed(lean_object* v_x_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_, lean_object* v___y_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_Meta_Grind_foldProjs___lam__1(v_x_3085_, v___y_3086_, v___y_3087_, v___y_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec_ref(v___y_3088_);
lean_dec(v___y_3087_);
lean_dec_ref(v___y_3086_);
lean_dec_ref(v_x_3085_);
return v_res_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_object* v_00_u03b1_3092_, lean_object* v_x_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_, lean_object* v___y_3096_, lean_object* v___y_3097_){
_start:
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
v___x_3099_ = lean_apply_1(v_x_3093_, lean_box(0));
v___x_3100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
return v___x_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0___boxed(lean_object* v_00_u03b1_3101_, lean_object* v_x_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(v_00_u03b1_3101_, v_x_3102_, v___y_3103_, v___y_3104_, v___y_3105_, v___y_3106_);
lean_dec(v___y_3106_);
lean_dec_ref(v___y_3105_);
lean_dec(v___y_3104_);
lean_dec_ref(v___y_3103_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0(lean_object* v_k_3109_, lean_object* v___y_3110_, lean_object* v_b_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; 
lean_inc(v___y_3115_);
lean_inc_ref(v___y_3114_);
lean_inc(v___y_3113_);
lean_inc_ref(v___y_3112_);
lean_inc(v___y_3110_);
v___x_3117_ = lean_apply_7(v_k_3109_, v_b_3111_, v___y_3110_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, lean_box(0));
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0___boxed(lean_object* v_k_3118_, lean_object* v___y_3119_, lean_object* v_b_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0(v_k_3118_, v___y_3119_, v_b_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v___y_3122_);
lean_dec_ref(v___y_3121_);
lean_dec(v___y_3119_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg(lean_object* v_name_3127_, lean_object* v_type_3128_, lean_object* v_val_3129_, lean_object* v_k_3130_, uint8_t v_nondep_3131_, uint8_t v_kind_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___f_3139_; lean_object* v___x_3140_; 
lean_inc(v___y_3133_);
v___f_3139_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3139_, 0, v_k_3130_);
lean_closure_set(v___f_3139_, 1, v___y_3133_);
v___x_3140_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3127_, v_type_3128_, v_val_3129_, v___f_3139_, v_nondep_3131_, v_kind_3132_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3140_) == 0)
{
return v___x_3140_;
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3140_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg___boxed(lean_object* v_name_3149_, lean_object* v_type_3150_, lean_object* v_val_3151_, lean_object* v_k_3152_, lean_object* v_nondep_3153_, lean_object* v_kind_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_, lean_object* v___y_3157_, lean_object* v___y_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_){
_start:
{
uint8_t v_nondep_boxed_3161_; uint8_t v_kind_boxed_3162_; lean_object* v_res_3163_; 
v_nondep_boxed_3161_ = lean_unbox(v_nondep_3153_);
v_kind_boxed_3162_ = lean_unbox(v_kind_3154_);
v_res_3163_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg(v_name_3149_, v_type_3150_, v_val_3151_, v_k_3152_, v_nondep_boxed_3161_, v_kind_boxed_3162_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_, v___y_3159_);
lean_dec(v___y_3159_);
lean_dec_ref(v___y_3158_);
lean_dec(v___y_3157_);
lean_dec_ref(v___y_3156_);
lean_dec(v___y_3155_);
return v_res_3163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(lean_object* v_name_3164_, uint8_t v_bi_3165_, lean_object* v_type_3166_, lean_object* v_k_3167_, uint8_t v_kind_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
lean_object* v___f_3175_; lean_object* v___x_3176_; 
lean_inc(v___y_3169_);
v___f_3175_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3175_, 0, v_k_3167_);
lean_closure_set(v___f_3175_, 1, v___y_3169_);
v___x_3176_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3164_, v_bi_3165_, v_type_3166_, v___f_3175_, v_kind_3168_, v___y_3170_, v___y_3171_, v___y_3172_, v___y_3173_);
if (lean_obj_tag(v___x_3176_) == 0)
{
return v___x_3176_;
}
else
{
lean_object* v_a_3177_; lean_object* v___x_3179_; uint8_t v_isShared_3180_; uint8_t v_isSharedCheck_3184_; 
v_a_3177_ = lean_ctor_get(v___x_3176_, 0);
v_isSharedCheck_3184_ = !lean_is_exclusive(v___x_3176_);
if (v_isSharedCheck_3184_ == 0)
{
v___x_3179_ = v___x_3176_;
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
else
{
lean_inc(v_a_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_box(0);
v_isShared_3180_ = v_isSharedCheck_3184_;
goto v_resetjp_3178_;
}
v_resetjp_3178_:
{
lean_object* v___x_3182_; 
if (v_isShared_3180_ == 0)
{
v___x_3182_ = v___x_3179_;
goto v_reusejp_3181_;
}
else
{
lean_object* v_reuseFailAlloc_3183_; 
v_reuseFailAlloc_3183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3183_, 0, v_a_3177_);
v___x_3182_ = v_reuseFailAlloc_3183_;
goto v_reusejp_3181_;
}
v_reusejp_3181_:
{
return v___x_3182_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg___boxed(lean_object* v_name_3185_, lean_object* v_bi_3186_, lean_object* v_type_3187_, lean_object* v_k_3188_, lean_object* v_kind_3189_, lean_object* v___y_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
uint8_t v_bi_boxed_3196_; uint8_t v_kind_boxed_3197_; lean_object* v_res_3198_; 
v_bi_boxed_3196_ = lean_unbox(v_bi_3186_);
v_kind_boxed_3197_ = lean_unbox(v_kind_3189_);
v_res_3198_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(v_name_3185_, v_bi_boxed_3196_, v_type_3187_, v_k_3188_, v_kind_boxed_3197_, v___y_3190_, v___y_3191_, v___y_3192_, v___y_3193_, v___y_3194_);
lean_dec(v___y_3194_);
lean_dec_ref(v___y_3193_);
lean_dec(v___y_3192_);
lean_dec_ref(v___y_3191_);
lean_dec(v___y_3190_);
return v_res_3198_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__2(lean_object* v___x_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_, lean_object* v___y_3203_){
_start:
{
lean_object* v___x_3205_; 
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3199_);
return v___x_3205_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__2___boxed(lean_object* v___x_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v_res_3212_; 
v_res_3212_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__2(v___x_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
return v_res_3212_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg(lean_object* v_ref_3213_){
_start:
{
lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3215_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3216_, 0, v_ref_3213_);
lean_ctor_set(v___x_3216_, 1, v___x_3215_);
v___x_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3217_, 0, v___x_3216_);
return v___x_3217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg___boxed(lean_object* v_ref_3218_, lean_object* v___y_3219_){
_start:
{
lean_object* v_res_3220_; 
v_res_3220_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg(v_ref_3218_);
return v_res_3220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg(lean_object* v_x_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
lean_object* v___y_3229_; lean_object* v_fileName_3238_; lean_object* v_fileMap_3239_; lean_object* v_options_3240_; lean_object* v_currRecDepth_3241_; lean_object* v_maxRecDepth_3242_; lean_object* v_ref_3243_; lean_object* v_currNamespace_3244_; lean_object* v_openDecls_3245_; lean_object* v_initHeartbeats_3246_; lean_object* v_maxHeartbeats_3247_; lean_object* v_quotContext_3248_; lean_object* v_currMacroScope_3249_; uint8_t v_diag_3250_; lean_object* v_cancelTk_x3f_3251_; uint8_t v_suppressElabErrors_3252_; lean_object* v_inheritedTraceOptions_3253_; uint8_t v___x_3254_; 
v_fileName_3238_ = lean_ctor_get(v___y_3225_, 0);
lean_inc_ref(v_fileName_3238_);
v_fileMap_3239_ = lean_ctor_get(v___y_3225_, 1);
lean_inc_ref(v_fileMap_3239_);
v_options_3240_ = lean_ctor_get(v___y_3225_, 2);
lean_inc_ref(v_options_3240_);
v_currRecDepth_3241_ = lean_ctor_get(v___y_3225_, 3);
lean_inc(v_currRecDepth_3241_);
v_maxRecDepth_3242_ = lean_ctor_get(v___y_3225_, 4);
lean_inc(v_maxRecDepth_3242_);
v_ref_3243_ = lean_ctor_get(v___y_3225_, 5);
lean_inc(v_ref_3243_);
v_currNamespace_3244_ = lean_ctor_get(v___y_3225_, 6);
lean_inc(v_currNamespace_3244_);
v_openDecls_3245_ = lean_ctor_get(v___y_3225_, 7);
lean_inc(v_openDecls_3245_);
v_initHeartbeats_3246_ = lean_ctor_get(v___y_3225_, 8);
lean_inc(v_initHeartbeats_3246_);
v_maxHeartbeats_3247_ = lean_ctor_get(v___y_3225_, 9);
lean_inc(v_maxHeartbeats_3247_);
v_quotContext_3248_ = lean_ctor_get(v___y_3225_, 10);
lean_inc(v_quotContext_3248_);
v_currMacroScope_3249_ = lean_ctor_get(v___y_3225_, 11);
lean_inc(v_currMacroScope_3249_);
v_diag_3250_ = lean_ctor_get_uint8(v___y_3225_, sizeof(void*)*14);
v_cancelTk_x3f_3251_ = lean_ctor_get(v___y_3225_, 12);
lean_inc(v_cancelTk_x3f_3251_);
v_suppressElabErrors_3252_ = lean_ctor_get_uint8(v___y_3225_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3253_ = lean_ctor_get(v___y_3225_, 13);
lean_inc_ref(v_inheritedTraceOptions_3253_);
lean_dec_ref(v___y_3225_);
v___x_3254_ = lean_nat_dec_eq(v_currRecDepth_3241_, v_maxRecDepth_3242_);
if (v___x_3254_ == 0)
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3255_ = lean_unsigned_to_nat(1u);
v___x_3256_ = lean_nat_add(v_currRecDepth_3241_, v___x_3255_);
lean_dec(v_currRecDepth_3241_);
v___x_3257_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3257_, 0, v_fileName_3238_);
lean_ctor_set(v___x_3257_, 1, v_fileMap_3239_);
lean_ctor_set(v___x_3257_, 2, v_options_3240_);
lean_ctor_set(v___x_3257_, 3, v___x_3256_);
lean_ctor_set(v___x_3257_, 4, v_maxRecDepth_3242_);
lean_ctor_set(v___x_3257_, 5, v_ref_3243_);
lean_ctor_set(v___x_3257_, 6, v_currNamespace_3244_);
lean_ctor_set(v___x_3257_, 7, v_openDecls_3245_);
lean_ctor_set(v___x_3257_, 8, v_initHeartbeats_3246_);
lean_ctor_set(v___x_3257_, 9, v_maxHeartbeats_3247_);
lean_ctor_set(v___x_3257_, 10, v_quotContext_3248_);
lean_ctor_set(v___x_3257_, 11, v_currMacroScope_3249_);
lean_ctor_set(v___x_3257_, 12, v_cancelTk_x3f_3251_);
lean_ctor_set(v___x_3257_, 13, v_inheritedTraceOptions_3253_);
lean_ctor_set_uint8(v___x_3257_, sizeof(void*)*14, v_diag_3250_);
lean_ctor_set_uint8(v___x_3257_, sizeof(void*)*14 + 1, v_suppressElabErrors_3252_);
lean_inc(v___y_3226_);
lean_inc(v___y_3224_);
lean_inc_ref(v___y_3223_);
lean_inc(v___y_3222_);
v___x_3258_ = lean_apply_6(v_x_3221_, v___y_3222_, v___y_3223_, v___y_3224_, v___x_3257_, v___y_3226_, lean_box(0));
v___y_3229_ = v___x_3258_;
goto v___jp_3228_;
}
else
{
lean_object* v___x_3259_; 
lean_dec_ref(v_inheritedTraceOptions_3253_);
lean_dec(v_cancelTk_x3f_3251_);
lean_dec(v_currMacroScope_3249_);
lean_dec(v_quotContext_3248_);
lean_dec(v_maxHeartbeats_3247_);
lean_dec(v_initHeartbeats_3246_);
lean_dec(v_openDecls_3245_);
lean_dec(v_currNamespace_3244_);
lean_dec(v_maxRecDepth_3242_);
lean_dec(v_currRecDepth_3241_);
lean_dec_ref(v_options_3240_);
lean_dec_ref(v_fileMap_3239_);
lean_dec_ref(v_fileName_3238_);
lean_dec_ref(v_x_3221_);
v___x_3259_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg(v_ref_3243_);
v___y_3229_ = v___x_3259_;
goto v___jp_3228_;
}
v___jp_3228_:
{
if (lean_obj_tag(v___y_3229_) == 0)
{
return v___y_3229_;
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
v_a_3230_ = lean_ctor_get(v___y_3229_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___y_3229_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___y_3229_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___y_3229_);
v___x_3232_ = lean_box(0);
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
v_resetjp_3231_:
{
lean_object* v___x_3235_; 
if (v_isShared_3233_ == 0)
{
v___x_3235_ = v___x_3232_;
goto v_reusejp_3234_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_a_3230_);
v___x_3235_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3234_;
}
v_reusejp_3234_:
{
return v___x_3235_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg___boxed(lean_object* v_x_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_){
_start:
{
lean_object* v_res_3267_; 
v_res_3267_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg(v_x_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_, v___y_3265_);
lean_dec(v___y_3265_);
lean_dec(v___y_3263_);
lean_dec_ref(v___y_3262_);
lean_dec(v___y_3261_);
return v_res_3267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_object* v_00_u03b1_3268_, lean_object* v_x_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v___x_3275_; lean_object* v___x_3276_; 
v___x_3275_ = lean_apply_1(v_x_3269_, lean_box(0));
v___x_3276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3276_, 0, v___x_3275_);
return v___x_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0___boxed(lean_object* v_00_u03b1_3277_, lean_object* v_x_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v_res_3284_; 
v_res_3284_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(v_00_u03b1_3277_, v_x_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
lean_dec(v___y_3282_);
lean_dec_ref(v___y_3281_);
lean_dec(v___y_3280_);
lean_dec_ref(v___y_3279_);
return v_res_3284_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___lam__0(lean_object* v_fvars_3287_, lean_object* v_pre_3288_, lean_object* v_post_3289_, uint8_t v_usedLetOnly_3290_, uint8_t v_skipConstInApp_3291_, uint8_t v_skipInstances_3292_, lean_object* v_body_3293_, lean_object* v_x_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3301_ = lean_array_push(v_fvars_3287_, v_x_3294_);
v___x_3302_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8(v_pre_3288_, v_post_3289_, v_usedLetOnly_3290_, v_skipConstInApp_3291_, v_skipInstances_3292_, v___x_3301_, v_body_3293_, v___y_3295_, v___y_3296_, v___y_3297_, v___y_3298_, v___y_3299_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___lam__0___boxed(lean_object* v_fvars_3303_, lean_object* v_pre_3304_, lean_object* v_post_3305_, lean_object* v_usedLetOnly_3306_, lean_object* v_skipConstInApp_3307_, lean_object* v_skipInstances_3308_, lean_object* v_body_3309_, lean_object* v_x_3310_, lean_object* v___y_3311_, lean_object* v___y_3312_, lean_object* v___y_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_){
_start:
{
uint8_t v_usedLetOnly_boxed_3317_; uint8_t v_skipConstInApp_boxed_3318_; uint8_t v_skipInstances_boxed_3319_; lean_object* v_res_3320_; 
v_usedLetOnly_boxed_3317_ = lean_unbox(v_usedLetOnly_3306_);
v_skipConstInApp_boxed_3318_ = lean_unbox(v_skipConstInApp_3307_);
v_skipInstances_boxed_3319_ = lean_unbox(v_skipInstances_3308_);
v_res_3320_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___lam__0(v_fvars_3303_, v_pre_3304_, v_post_3305_, v_usedLetOnly_boxed_3317_, v_skipConstInApp_boxed_3318_, v_skipInstances_boxed_3319_, v_body_3309_, v_x_3310_, v___y_3311_, v___y_3312_, v___y_3313_, v___y_3314_, v___y_3315_);
lean_dec(v___y_3315_);
lean_dec_ref(v___y_3314_);
lean_dec(v___y_3313_);
lean_dec_ref(v___y_3312_);
lean_dec(v___y_3311_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(lean_object* v_pre_3321_, lean_object* v_post_3322_, uint8_t v_usedLetOnly_3323_, uint8_t v_skipConstInApp_3324_, uint8_t v_skipInstances_3325_, lean_object* v_e_3326_, lean_object* v_a_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_){
_start:
{
lean_object* v___x_3333_; 
lean_inc_ref(v_post_3322_);
lean_inc(v___y_3331_);
lean_inc_ref(v___y_3330_);
lean_inc(v___y_3329_);
lean_inc_ref(v___y_3328_);
lean_inc_ref(v_e_3326_);
v___x_3333_ = lean_apply_6(v_post_3322_, v_e_3326_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_, lean_box(0));
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3352_; 
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3352_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3352_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
switch(lean_obj_tag(v_a_3334_))
{
case 0:
{
lean_object* v_e_3338_; lean_object* v___x_3340_; 
lean_dec_ref(v_e_3326_);
lean_dec_ref(v_post_3322_);
lean_dec_ref(v_pre_3321_);
v_e_3338_ = lean_ctor_get(v_a_3334_, 0);
lean_inc_ref(v_e_3338_);
lean_dec_ref(v_a_3334_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v_e_3338_);
v___x_3340_ = v___x_3336_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v_e_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
case 1:
{
lean_object* v_e_3342_; lean_object* v___x_3343_; 
lean_del_object(v___x_3336_);
lean_dec_ref(v_e_3326_);
v_e_3342_ = lean_ctor_get(v_a_3334_, 0);
lean_inc_ref(v_e_3342_);
lean_dec_ref(v_a_3334_);
v___x_3343_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3321_, v_post_3322_, v_usedLetOnly_3323_, v_skipConstInApp_3324_, v_skipInstances_3325_, v_e_3342_, v_a_3327_, v___y_3328_, v___y_3329_, v___y_3330_, v___y_3331_);
return v___x_3343_;
}
default: 
{
lean_object* v_e_x3f_3344_; 
lean_dec_ref(v_post_3322_);
lean_dec_ref(v_pre_3321_);
v_e_x3f_3344_ = lean_ctor_get(v_a_3334_, 0);
lean_inc(v_e_x3f_3344_);
lean_dec_ref(v_a_3334_);
if (lean_obj_tag(v_e_x3f_3344_) == 0)
{
lean_object* v___x_3346_; 
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v_e_3326_);
v___x_3346_ = v___x_3336_;
goto v_reusejp_3345_;
}
else
{
lean_object* v_reuseFailAlloc_3347_; 
v_reuseFailAlloc_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_e_3326_);
v___x_3346_ = v_reuseFailAlloc_3347_;
goto v_reusejp_3345_;
}
v_reusejp_3345_:
{
return v___x_3346_;
}
}
else
{
lean_object* v_val_3348_; lean_object* v___x_3350_; 
lean_dec_ref(v_e_3326_);
v_val_3348_ = lean_ctor_get(v_e_x3f_3344_, 0);
lean_inc(v_val_3348_);
lean_dec_ref(v_e_x3f_3344_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v_val_3348_);
v___x_3350_ = v___x_3336_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_val_3348_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
}
}
else
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3360_; 
lean_dec_ref(v_e_3326_);
lean_dec_ref(v_post_3322_);
lean_dec_ref(v_pre_3321_);
v_a_3353_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3355_ = v___x_3333_;
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3333_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3360_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3358_; 
if (v_isShared_3356_ == 0)
{
v___x_3358_ = v___x_3355_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v_a_3353_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8(lean_object* v_pre_3361_, lean_object* v_post_3362_, uint8_t v_usedLetOnly_3363_, uint8_t v_skipConstInApp_3364_, uint8_t v_skipInstances_3365_, lean_object* v_fvars_3366_, lean_object* v_e_3367_, lean_object* v_a_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_){
_start:
{
if (lean_obj_tag(v_e_3367_) == 6)
{
lean_object* v_binderName_3374_; lean_object* v_binderType_3375_; lean_object* v_body_3376_; uint8_t v_binderInfo_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; 
v_binderName_3374_ = lean_ctor_get(v_e_3367_, 0);
lean_inc(v_binderName_3374_);
v_binderType_3375_ = lean_ctor_get(v_e_3367_, 1);
lean_inc_ref(v_binderType_3375_);
v_body_3376_ = lean_ctor_get(v_e_3367_, 2);
lean_inc_ref(v_body_3376_);
v_binderInfo_3377_ = lean_ctor_get_uint8(v_e_3367_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3367_);
v___x_3378_ = lean_expr_instantiate_rev(v_binderType_3375_, v_fvars_3366_);
lean_dec_ref(v_binderType_3375_);
lean_inc_ref(v_post_3362_);
lean_inc_ref(v_pre_3361_);
v___x_3379_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3361_, v_post_3362_, v_usedLetOnly_3363_, v_skipConstInApp_3364_, v_skipInstances_3365_, v___x_3378_, v_a_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; lean_object* v___f_3384_; uint8_t v___x_3385_; lean_object* v___x_3386_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref(v___x_3379_);
v___x_3381_ = lean_box(v_usedLetOnly_3363_);
v___x_3382_ = lean_box(v_skipConstInApp_3364_);
v___x_3383_ = lean_box(v_skipInstances_3365_);
v___f_3384_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3384_, 0, v_fvars_3366_);
lean_closure_set(v___f_3384_, 1, v_pre_3361_);
lean_closure_set(v___f_3384_, 2, v_post_3362_);
lean_closure_set(v___f_3384_, 3, v___x_3381_);
lean_closure_set(v___f_3384_, 4, v___x_3382_);
lean_closure_set(v___f_3384_, 5, v___x_3383_);
lean_closure_set(v___f_3384_, 6, v_body_3376_);
v___x_3385_ = 0;
v___x_3386_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(v_binderName_3374_, v_binderInfo_3377_, v_a_3380_, v___f_3384_, v___x_3385_, v_a_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
return v___x_3386_;
}
else
{
lean_dec_ref(v_body_3376_);
lean_dec(v_binderName_3374_);
lean_dec_ref(v_fvars_3366_);
lean_dec_ref(v_post_3362_);
lean_dec_ref(v_pre_3361_);
return v___x_3379_;
}
}
else
{
lean_object* v___x_3387_; lean_object* v___x_3388_; 
v___x_3387_ = lean_expr_instantiate_rev(v_e_3367_, v_fvars_3366_);
lean_dec_ref(v_e_3367_);
lean_inc_ref(v_post_3362_);
lean_inc_ref(v_pre_3361_);
v___x_3388_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3361_, v_post_3362_, v_usedLetOnly_3363_, v_skipConstInApp_3364_, v_skipInstances_3365_, v___x_3387_, v_a_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; uint8_t v___x_3390_; uint8_t v___x_3391_; uint8_t v___x_3392_; lean_object* v___x_3393_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref(v___x_3388_);
v___x_3390_ = 0;
v___x_3391_ = 1;
v___x_3392_ = 1;
v___x_3393_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3366_, v_a_3389_, v___x_3390_, v_usedLetOnly_3363_, v___x_3390_, v___x_3391_, v___x_3392_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec_ref(v_fvars_3366_);
if (lean_obj_tag(v___x_3393_) == 0)
{
lean_object* v_a_3394_; lean_object* v___x_3395_; 
v_a_3394_ = lean_ctor_get(v___x_3393_, 0);
lean_inc(v_a_3394_);
lean_dec_ref(v___x_3393_);
v___x_3395_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3361_, v_post_3362_, v_usedLetOnly_3363_, v_skipConstInApp_3364_, v_skipInstances_3365_, v_a_3394_, v_a_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
return v___x_3395_;
}
else
{
lean_dec_ref(v_post_3362_);
lean_dec_ref(v_pre_3361_);
return v___x_3393_;
}
}
else
{
lean_dec_ref(v_fvars_3366_);
lean_dec_ref(v_post_3362_);
lean_dec_ref(v_pre_3361_);
return v___x_3388_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___lam__0(lean_object* v_fvars_3396_, lean_object* v_pre_3397_, lean_object* v_post_3398_, uint8_t v_usedLetOnly_3399_, uint8_t v_skipConstInApp_3400_, uint8_t v_skipInstances_3401_, lean_object* v_body_3402_, lean_object* v_x_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___x_3410_; lean_object* v___x_3411_; 
v___x_3410_ = lean_array_push(v_fvars_3396_, v_x_3403_);
v___x_3411_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9(v_pre_3397_, v_post_3398_, v_usedLetOnly_3399_, v_skipConstInApp_3400_, v_skipInstances_3401_, v___x_3410_, v_body_3402_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___lam__0___boxed(lean_object* v_fvars_3412_, lean_object* v_pre_3413_, lean_object* v_post_3414_, lean_object* v_usedLetOnly_3415_, lean_object* v_skipConstInApp_3416_, lean_object* v_skipInstances_3417_, lean_object* v_body_3418_, lean_object* v_x_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_){
_start:
{
uint8_t v_usedLetOnly_boxed_3426_; uint8_t v_skipConstInApp_boxed_3427_; uint8_t v_skipInstances_boxed_3428_; lean_object* v_res_3429_; 
v_usedLetOnly_boxed_3426_ = lean_unbox(v_usedLetOnly_3415_);
v_skipConstInApp_boxed_3427_ = lean_unbox(v_skipConstInApp_3416_);
v_skipInstances_boxed_3428_ = lean_unbox(v_skipInstances_3417_);
v_res_3429_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___lam__0(v_fvars_3412_, v_pre_3413_, v_post_3414_, v_usedLetOnly_boxed_3426_, v_skipConstInApp_boxed_3427_, v_skipInstances_boxed_3428_, v_body_3418_, v_x_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_);
lean_dec(v___y_3424_);
lean_dec_ref(v___y_3423_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9(lean_object* v_pre_3430_, lean_object* v_post_3431_, uint8_t v_usedLetOnly_3432_, uint8_t v_skipConstInApp_3433_, uint8_t v_skipInstances_3434_, lean_object* v_fvars_3435_, lean_object* v_e_3436_, lean_object* v_a_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_){
_start:
{
if (lean_obj_tag(v_e_3436_) == 8)
{
lean_object* v_declName_3443_; lean_object* v_type_3444_; lean_object* v_value_3445_; lean_object* v_body_3446_; uint8_t v_nondep_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; 
v_declName_3443_ = lean_ctor_get(v_e_3436_, 0);
lean_inc(v_declName_3443_);
v_type_3444_ = lean_ctor_get(v_e_3436_, 1);
lean_inc_ref(v_type_3444_);
v_value_3445_ = lean_ctor_get(v_e_3436_, 2);
lean_inc_ref(v_value_3445_);
v_body_3446_ = lean_ctor_get(v_e_3436_, 3);
lean_inc_ref(v_body_3446_);
v_nondep_3447_ = lean_ctor_get_uint8(v_e_3436_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3436_);
v___x_3448_ = lean_expr_instantiate_rev(v_type_3444_, v_fvars_3435_);
lean_dec_ref(v_type_3444_);
lean_inc_ref(v_post_3431_);
lean_inc_ref(v_pre_3430_);
v___x_3449_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3430_, v_post_3431_, v_usedLetOnly_3432_, v_skipConstInApp_3433_, v_skipInstances_3434_, v___x_3448_, v_a_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref(v___x_3449_);
v___x_3451_ = lean_expr_instantiate_rev(v_value_3445_, v_fvars_3435_);
lean_dec_ref(v_value_3445_);
lean_inc_ref(v_post_3431_);
lean_inc_ref(v_pre_3430_);
v___x_3452_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3430_, v_post_3431_, v_usedLetOnly_3432_, v_skipConstInApp_3433_, v_skipInstances_3434_, v___x_3451_, v_a_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___f_3457_; uint8_t v___x_3458_; lean_object* v___x_3459_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref(v___x_3452_);
v___x_3454_ = lean_box(v_usedLetOnly_3432_);
v___x_3455_ = lean_box(v_skipConstInApp_3433_);
v___x_3456_ = lean_box(v_skipInstances_3434_);
v___f_3457_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3457_, 0, v_fvars_3435_);
lean_closure_set(v___f_3457_, 1, v_pre_3430_);
lean_closure_set(v___f_3457_, 2, v_post_3431_);
lean_closure_set(v___f_3457_, 3, v___x_3454_);
lean_closure_set(v___f_3457_, 4, v___x_3455_);
lean_closure_set(v___f_3457_, 5, v___x_3456_);
lean_closure_set(v___f_3457_, 6, v_body_3446_);
v___x_3458_ = 0;
v___x_3459_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg(v_declName_3443_, v_a_3450_, v_a_3453_, v___f_3457_, v_nondep_3447_, v___x_3458_, v_a_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v___x_3459_;
}
else
{
lean_dec(v_a_3450_);
lean_dec_ref(v_body_3446_);
lean_dec(v_declName_3443_);
lean_dec_ref(v_fvars_3435_);
lean_dec_ref(v_post_3431_);
lean_dec_ref(v_pre_3430_);
return v___x_3452_;
}
}
else
{
lean_dec_ref(v_body_3446_);
lean_dec_ref(v_value_3445_);
lean_dec(v_declName_3443_);
lean_dec_ref(v_fvars_3435_);
lean_dec_ref(v_post_3431_);
lean_dec_ref(v_pre_3430_);
return v___x_3449_;
}
}
else
{
lean_object* v___x_3460_; lean_object* v___x_3461_; 
v___x_3460_ = lean_expr_instantiate_rev(v_e_3436_, v_fvars_3435_);
lean_dec_ref(v_e_3436_);
lean_inc_ref(v_post_3431_);
lean_inc_ref(v_pre_3430_);
v___x_3461_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3430_, v_post_3431_, v_usedLetOnly_3432_, v_skipConstInApp_3433_, v_skipInstances_3434_, v___x_3460_, v_a_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; uint8_t v___x_3463_; uint8_t v___x_3464_; lean_object* v___x_3465_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref(v___x_3461_);
v___x_3463_ = 0;
v___x_3464_ = 1;
v___x_3465_ = l_Lean_Meta_mkLetFVars(v_fvars_3435_, v_a_3462_, v_usedLetOnly_3432_, v___x_3463_, v___x_3464_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
lean_dec_ref(v_fvars_3435_);
if (lean_obj_tag(v___x_3465_) == 0)
{
lean_object* v_a_3466_; lean_object* v___x_3467_; 
v_a_3466_ = lean_ctor_get(v___x_3465_, 0);
lean_inc(v_a_3466_);
lean_dec_ref(v___x_3465_);
v___x_3467_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3430_, v_post_3431_, v_usedLetOnly_3432_, v_skipConstInApp_3433_, v_skipInstances_3434_, v_a_3466_, v_a_3437_, v___y_3438_, v___y_3439_, v___y_3440_, v___y_3441_);
return v___x_3467_;
}
else
{
lean_dec_ref(v_post_3431_);
lean_dec_ref(v_pre_3430_);
return v___x_3465_;
}
}
else
{
lean_dec_ref(v_fvars_3435_);
lean_dec_ref(v_post_3431_);
lean_dec_ref(v_pre_3430_);
return v___x_3461_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__4(lean_object* v_pre_3468_, lean_object* v_post_3469_, uint8_t v_usedLetOnly_3470_, uint8_t v_skipConstInApp_3471_, uint8_t v_skipInstances_3472_, size_t v_sz_3473_, size_t v_i_3474_, lean_object* v_bs_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
uint8_t v___x_3482_; 
v___x_3482_ = lean_usize_dec_lt(v_i_3474_, v_sz_3473_);
if (v___x_3482_ == 0)
{
lean_object* v___x_3483_; 
lean_dec_ref(v_post_3469_);
lean_dec_ref(v_pre_3468_);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v_bs_3475_);
return v___x_3483_;
}
else
{
lean_object* v_v_3484_; lean_object* v___x_3485_; 
v_v_3484_ = lean_array_uget_borrowed(v_bs_3475_, v_i_3474_);
lean_inc(v_v_3484_);
lean_inc_ref(v_post_3469_);
lean_inc_ref(v_pre_3468_);
v___x_3485_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3468_, v_post_3469_, v_usedLetOnly_3470_, v_skipConstInApp_3471_, v_skipInstances_3472_, v_v_3484_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_, v___y_3480_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v_a_3486_; lean_object* v___x_3487_; lean_object* v_bs_x27_3488_; size_t v___x_3489_; size_t v___x_3490_; lean_object* v___x_3491_; 
v_a_3486_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_a_3486_);
lean_dec_ref(v___x_3485_);
v___x_3487_ = lean_unsigned_to_nat(0u);
v_bs_x27_3488_ = lean_array_uset(v_bs_3475_, v_i_3474_, v___x_3487_);
v___x_3489_ = ((size_t)1ULL);
v___x_3490_ = lean_usize_add(v_i_3474_, v___x_3489_);
v___x_3491_ = lean_array_uset(v_bs_x27_3488_, v_i_3474_, v_a_3486_);
v_i_3474_ = v___x_3490_;
v_bs_3475_ = v___x_3491_;
goto _start;
}
else
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3500_; 
lean_dec_ref(v_bs_3475_);
lean_dec_ref(v_post_3469_);
lean_dec_ref(v_pre_3468_);
v_a_3493_ = lean_ctor_get(v___x_3485_, 0);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3485_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3495_ = v___x_3485_;
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3485_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3500_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_a_3493_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0(lean_object* v_pre_3501_, lean_object* v_post_3502_, uint8_t v_usedLetOnly_3503_, uint8_t v_skipConstInApp_3504_, uint8_t v_skipInstances_3505_, lean_object* v___x_3506_, lean_object* v___y_3507_, lean_object* v_b_3508_, lean_object* v_a_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_){
_start:
{
lean_object* v___x_3515_; 
v___x_3515_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3501_, v_post_3502_, v_usedLetOnly_3503_, v_skipConstInApp_3504_, v_skipInstances_3505_, v___x_3506_, v___y_3507_, v___y_3510_, v___y_3511_, v___y_3512_, v___y_3513_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3525_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3525_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3525_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3523_; 
v___x_3520_ = lean_array_fset(v_b_3508_, v_a_3509_, v_a_3516_);
v___x_3521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v___x_3521_);
v___x_3523_ = v___x_3518_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
}
else
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3533_; 
lean_dec_ref(v_b_3508_);
v_a_3526_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3528_ = v___x_3515_;
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3515_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3533_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v___x_3531_; 
if (v_isShared_3529_ == 0)
{
v___x_3531_ = v___x_3528_;
goto v_reusejp_3530_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_a_3526_);
v___x_3531_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3530_;
}
v_reusejp_3530_:
{
return v___x_3531_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0___boxed(lean_object* v_pre_3534_, lean_object* v_post_3535_, lean_object* v_usedLetOnly_3536_, lean_object* v_skipConstInApp_3537_, lean_object* v_skipInstances_3538_, lean_object* v___x_3539_, lean_object* v___y_3540_, lean_object* v_b_3541_, lean_object* v_a_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_, lean_object* v___y_3547_){
_start:
{
uint8_t v_usedLetOnly_boxed_3548_; uint8_t v_skipConstInApp_boxed_3549_; uint8_t v_skipInstances_boxed_3550_; lean_object* v_res_3551_; 
v_usedLetOnly_boxed_3548_ = lean_unbox(v_usedLetOnly_3536_);
v_skipConstInApp_boxed_3549_ = lean_unbox(v_skipConstInApp_3537_);
v_skipInstances_boxed_3550_ = lean_unbox(v_skipInstances_3538_);
v_res_3551_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0(v_pre_3534_, v_post_3535_, v_usedLetOnly_boxed_3548_, v_skipConstInApp_boxed_3549_, v_skipInstances_boxed_3550_, v___x_3539_, v___y_3540_, v_b_3541_, v_a_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
lean_dec(v___y_3546_);
lean_dec_ref(v___y_3545_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v_a_3542_);
lean_dec(v___y_3540_);
return v_res_3551_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg(lean_object* v_upperBound_3552_, lean_object* v___x_3553_, lean_object* v_pre_3554_, lean_object* v_post_3555_, uint8_t v_usedLetOnly_3556_, uint8_t v_skipConstInApp_3557_, uint8_t v_skipInstances_3558_, lean_object* v_a_3559_, lean_object* v_b_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
lean_object* v___y_3568_; uint8_t v___x_3591_; 
v___x_3591_ = lean_nat_dec_lt(v_a_3559_, v_upperBound_3552_);
if (v___x_3591_ == 0)
{
lean_object* v___x_3592_; 
lean_dec(v_a_3559_);
lean_dec_ref(v_post_3555_);
lean_dec_ref(v_pre_3554_);
v___x_3592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3592_, 0, v_b_3560_);
return v___x_3592_;
}
else
{
lean_object* v___x_3593_; lean_object* v___x_3594_; uint8_t v___x_3595_; 
v___x_3593_ = lean_array_fget_borrowed(v_b_3560_, v_a_3559_);
v___x_3594_ = lean_array_get_size(v___x_3553_);
v___x_3595_ = lean_nat_dec_lt(v_a_3559_, v___x_3594_);
if (v___x_3595_ == 0)
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___f_3599_; 
lean_inc(v___x_3593_);
v___x_3596_ = lean_box(v_usedLetOnly_3556_);
v___x_3597_ = lean_box(v_skipConstInApp_3557_);
v___x_3598_ = lean_box(v_skipInstances_3558_);
lean_inc(v_a_3559_);
lean_inc(v___y_3561_);
lean_inc_ref(v_post_3555_);
lean_inc_ref(v_pre_3554_);
v___f_3599_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3599_, 0, v_pre_3554_);
lean_closure_set(v___f_3599_, 1, v_post_3555_);
lean_closure_set(v___f_3599_, 2, v___x_3596_);
lean_closure_set(v___f_3599_, 3, v___x_3597_);
lean_closure_set(v___f_3599_, 4, v___x_3598_);
lean_closure_set(v___f_3599_, 5, v___x_3593_);
lean_closure_set(v___f_3599_, 6, v___y_3561_);
lean_closure_set(v___f_3599_, 7, v_b_3560_);
lean_closure_set(v___f_3599_, 8, v_a_3559_);
v___y_3568_ = v___f_3599_;
goto v___jp_3567_;
}
else
{
lean_object* v___x_3600_; uint8_t v_isInstance_3601_; 
v___x_3600_ = lean_array_fget_borrowed(v___x_3553_, v_a_3559_);
v_isInstance_3601_ = lean_ctor_get_uint8(v___x_3600_, sizeof(void*)*1 + 4);
if (v_isInstance_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___f_3605_; 
lean_inc(v___x_3593_);
v___x_3602_ = lean_box(v_usedLetOnly_3556_);
v___x_3603_ = lean_box(v_skipConstInApp_3557_);
v___x_3604_ = lean_box(v_skipInstances_3558_);
lean_inc(v_a_3559_);
lean_inc(v___y_3561_);
lean_inc_ref(v_post_3555_);
lean_inc_ref(v_pre_3554_);
v___f_3605_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3605_, 0, v_pre_3554_);
lean_closure_set(v___f_3605_, 1, v_post_3555_);
lean_closure_set(v___f_3605_, 2, v___x_3602_);
lean_closure_set(v___f_3605_, 3, v___x_3603_);
lean_closure_set(v___f_3605_, 4, v___x_3604_);
lean_closure_set(v___f_3605_, 5, v___x_3593_);
lean_closure_set(v___f_3605_, 6, v___y_3561_);
lean_closure_set(v___f_3605_, 7, v_b_3560_);
lean_closure_set(v___f_3605_, 8, v_a_3559_);
v___y_3568_ = v___f_3605_;
goto v___jp_3567_;
}
else
{
lean_object* v___x_3606_; lean_object* v___f_3607_; 
v___x_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3606_, 0, v_b_3560_);
v___f_3607_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3607_, 0, v___x_3606_);
v___y_3568_ = v___f_3607_;
goto v___jp_3567_;
}
}
}
v___jp_3567_:
{
lean_object* v___x_3569_; 
lean_inc(v___y_3565_);
lean_inc_ref(v___y_3564_);
lean_inc(v___y_3563_);
lean_inc_ref(v___y_3562_);
v___x_3569_ = lean_apply_5(v___y_3568_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_, lean_box(0));
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3582_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3572_ = v___x_3569_;
v_isShared_3573_ = v_isSharedCheck_3582_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3569_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3582_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
if (lean_obj_tag(v_a_3570_) == 0)
{
lean_object* v_a_3574_; lean_object* v___x_3576_; 
lean_dec(v_a_3559_);
lean_dec_ref(v_post_3555_);
lean_dec_ref(v_pre_3554_);
v_a_3574_ = lean_ctor_get(v_a_3570_, 0);
lean_inc(v_a_3574_);
lean_dec_ref(v_a_3570_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v_a_3574_);
v___x_3576_ = v___x_3572_;
goto v_reusejp_3575_;
}
else
{
lean_object* v_reuseFailAlloc_3577_; 
v_reuseFailAlloc_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3577_, 0, v_a_3574_);
v___x_3576_ = v_reuseFailAlloc_3577_;
goto v_reusejp_3575_;
}
v_reusejp_3575_:
{
return v___x_3576_;
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
lean_del_object(v___x_3572_);
v_a_3578_ = lean_ctor_get(v_a_3570_, 0);
lean_inc(v_a_3578_);
lean_dec_ref(v_a_3570_);
v___x_3579_ = lean_unsigned_to_nat(1u);
v___x_3580_ = lean_nat_add(v_a_3559_, v___x_3579_);
lean_dec(v_a_3559_);
v_a_3559_ = v___x_3580_;
v_b_3560_ = v_a_3578_;
goto _start;
}
}
}
else
{
lean_object* v_a_3583_; lean_object* v___x_3585_; uint8_t v_isShared_3586_; uint8_t v_isSharedCheck_3590_; 
lean_dec(v_a_3559_);
lean_dec_ref(v_post_3555_);
lean_dec_ref(v_pre_3554_);
v_a_3583_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3590_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3590_ == 0)
{
v___x_3585_ = v___x_3569_;
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
else
{
lean_inc(v_a_3583_);
lean_dec(v___x_3569_);
v___x_3585_ = lean_box(0);
v_isShared_3586_ = v_isSharedCheck_3590_;
goto v_resetjp_3584_;
}
v_resetjp_3584_:
{
lean_object* v___x_3588_; 
if (v_isShared_3586_ == 0)
{
v___x_3588_ = v___x_3585_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v_a_3583_);
v___x_3588_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
return v___x_3588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__10(uint8_t v_skipInstances_3608_, lean_object* v_pre_3609_, lean_object* v_post_3610_, uint8_t v_usedLetOnly_3611_, uint8_t v_skipConstInApp_3612_, lean_object* v_x_3613_, lean_object* v_x_3614_, lean_object* v_x_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
lean_object* v_f_3623_; lean_object* v___y_3624_; lean_object* v___y_3625_; lean_object* v___y_3626_; lean_object* v___y_3627_; lean_object* v___y_3628_; 
if (lean_obj_tag(v_x_3613_) == 5)
{
lean_object* v_fn_3671_; lean_object* v_arg_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; 
v_fn_3671_ = lean_ctor_get(v_x_3613_, 0);
lean_inc_ref(v_fn_3671_);
v_arg_3672_ = lean_ctor_get(v_x_3613_, 1);
lean_inc_ref(v_arg_3672_);
lean_dec_ref(v_x_3613_);
v___x_3673_ = lean_array_set(v_x_3614_, v_x_3615_, v_arg_3672_);
v___x_3674_ = lean_unsigned_to_nat(1u);
v___x_3675_ = lean_nat_sub(v_x_3615_, v___x_3674_);
lean_dec(v_x_3615_);
v_x_3613_ = v_fn_3671_;
v_x_3614_ = v___x_3673_;
v_x_3615_ = v___x_3675_;
goto _start;
}
else
{
lean_dec(v_x_3615_);
if (v_skipConstInApp_3612_ == 0)
{
goto v___jp_3668_;
}
else
{
uint8_t v___x_3677_; 
v___x_3677_ = l_Lean_Expr_isConst(v_x_3613_);
if (v___x_3677_ == 0)
{
goto v___jp_3668_;
}
else
{
v_f_3623_ = v_x_3613_;
v___y_3624_ = v___y_3616_;
v___y_3625_ = v___y_3617_;
v___y_3626_ = v___y_3618_;
v___y_3627_ = v___y_3619_;
v___y_3628_ = v___y_3620_;
goto v___jp_3622_;
}
}
}
v___jp_3622_:
{
if (v_skipInstances_3608_ == 0)
{
size_t v_sz_3629_; size_t v___x_3630_; lean_object* v___x_3631_; 
v_sz_3629_ = lean_array_size(v_x_3614_);
v___x_3630_ = ((size_t)0ULL);
lean_inc_ref(v_post_3610_);
lean_inc_ref(v_pre_3609_);
v___x_3631_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__4(v_pre_3609_, v_post_3610_, v_usedLetOnly_3611_, v_skipConstInApp_3612_, v_skipInstances_3608_, v_sz_3629_, v___x_3630_, v_x_3614_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
lean_inc(v_a_3632_);
lean_dec_ref(v___x_3631_);
v___x_3633_ = l_Lean_mkAppN(v_f_3623_, v_a_3632_);
lean_dec(v_a_3632_);
v___x_3634_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3609_, v_post_3610_, v_usedLetOnly_3611_, v_skipConstInApp_3612_, v_skipInstances_3608_, v___x_3633_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
return v___x_3634_;
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_dec_ref(v_f_3623_);
lean_dec_ref(v_post_3610_);
lean_dec_ref(v_pre_3609_);
v_a_3635_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3631_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3631_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
else
{
lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3643_ = lean_array_get_size(v_x_3614_);
lean_inc_ref(v_f_3623_);
v___x_3644_ = l_Lean_Meta_getFunInfoNArgs(v_f_3623_, v___x_3643_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v_paramInfo_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref(v___x_3644_);
v_paramInfo_3646_ = lean_ctor_get(v_a_3645_, 0);
lean_inc_ref(v_paramInfo_3646_);
lean_dec(v_a_3645_);
v___x_3647_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3610_);
lean_inc_ref(v_pre_3609_);
v___x_3648_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg(v___x_3643_, v_paramInfo_3646_, v_pre_3609_, v_post_3610_, v_usedLetOnly_3611_, v_skipConstInApp_3612_, v_skipInstances_3608_, v___x_3647_, v_x_3614_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
lean_dec_ref(v_paramInfo_3646_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref(v___x_3648_);
v___x_3650_ = l_Lean_mkAppN(v_f_3623_, v_a_3649_);
lean_dec(v_a_3649_);
v___x_3651_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3609_, v_post_3610_, v_usedLetOnly_3611_, v_skipConstInApp_3612_, v_skipInstances_3608_, v___x_3650_, v___y_3624_, v___y_3625_, v___y_3626_, v___y_3627_, v___y_3628_);
return v___x_3651_;
}
else
{
lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3659_; 
lean_dec_ref(v_f_3623_);
lean_dec_ref(v_post_3610_);
lean_dec_ref(v_pre_3609_);
v_a_3652_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3654_ = v___x_3648_;
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3648_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3659_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3657_; 
if (v_isShared_3655_ == 0)
{
v___x_3657_ = v___x_3654_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_a_3652_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
lean_dec_ref(v_f_3623_);
lean_dec_ref(v_x_3614_);
lean_dec_ref(v_post_3610_);
lean_dec_ref(v_pre_3609_);
v_a_3660_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3644_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3644_);
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
}
v___jp_3668_:
{
lean_object* v___x_3669_; 
lean_inc_ref(v_post_3610_);
lean_inc_ref(v_pre_3609_);
v___x_3669_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3609_, v_post_3610_, v_usedLetOnly_3611_, v_skipConstInApp_3612_, v_skipInstances_3608_, v_x_3613_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_, v___y_3620_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref(v___x_3669_);
v_f_3623_ = v_a_3670_;
v___y_3624_ = v___y_3616_;
v___y_3625_ = v___y_3617_;
v___y_3626_ = v___y_3618_;
v___y_3627_ = v___y_3619_;
v___y_3628_ = v___y_3620_;
goto v___jp_3622_;
}
else
{
lean_dec_ref(v_x_3614_);
lean_dec_ref(v_post_3610_);
lean_dec_ref(v_pre_3609_);
return v___x_3669_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1(lean_object* v_pre_3678_, lean_object* v_e_3679_, lean_object* v_post_3680_, uint8_t v_usedLetOnly_3681_, uint8_t v_skipConstInApp_3682_, uint8_t v_skipInstances_3683_, lean_object* v___y_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_){
_start:
{
lean_object* v___x_3690_; 
lean_inc_ref(v_pre_3678_);
lean_inc(v___y_3688_);
lean_inc_ref(v___y_3687_);
lean_inc(v___y_3686_);
lean_inc_ref(v___y_3685_);
lean_inc_ref(v_e_3679_);
v___x_3690_ = lean_apply_6(v_pre_3678_, v_e_3679_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, lean_box(0));
if (lean_obj_tag(v___x_3690_) == 0)
{
lean_object* v_a_3691_; lean_object* v___x_3693_; uint8_t v_isShared_3694_; uint8_t v_isSharedCheck_3739_; 
v_a_3691_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3739_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3739_ == 0)
{
v___x_3693_ = v___x_3690_;
v_isShared_3694_ = v_isSharedCheck_3739_;
goto v_resetjp_3692_;
}
else
{
lean_inc(v_a_3691_);
lean_dec(v___x_3690_);
v___x_3693_ = lean_box(0);
v_isShared_3694_ = v_isSharedCheck_3739_;
goto v_resetjp_3692_;
}
v_resetjp_3692_:
{
lean_object* v___y_3696_; 
switch(lean_obj_tag(v_a_3691_))
{
case 0:
{
lean_object* v_e_3731_; lean_object* v___x_3733_; 
lean_dec_ref(v_post_3680_);
lean_dec_ref(v_e_3679_);
lean_dec_ref(v_pre_3678_);
v_e_3731_ = lean_ctor_get(v_a_3691_, 0);
lean_inc_ref(v_e_3731_);
lean_dec_ref(v_a_3691_);
if (v_isShared_3694_ == 0)
{
lean_ctor_set(v___x_3693_, 0, v_e_3731_);
v___x_3733_ = v___x_3693_;
goto v_reusejp_3732_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_e_3731_);
v___x_3733_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3732_;
}
v_reusejp_3732_:
{
return v___x_3733_;
}
}
case 1:
{
lean_object* v_e_3735_; lean_object* v___x_3736_; 
lean_del_object(v___x_3693_);
lean_dec_ref(v_e_3679_);
v_e_3735_ = lean_ctor_get(v_a_3691_, 0);
lean_inc_ref(v_e_3735_);
lean_dec_ref(v_a_3691_);
v___x_3736_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v_e_3735_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3736_;
}
default: 
{
lean_object* v_e_x3f_3737_; 
lean_del_object(v___x_3693_);
v_e_x3f_3737_ = lean_ctor_get(v_a_3691_, 0);
lean_inc(v_e_x3f_3737_);
lean_dec_ref(v_a_3691_);
if (lean_obj_tag(v_e_x3f_3737_) == 0)
{
v___y_3696_ = v_e_3679_;
goto v___jp_3695_;
}
else
{
lean_object* v_val_3738_; 
lean_dec_ref(v_e_3679_);
v_val_3738_ = lean_ctor_get(v_e_x3f_3737_, 0);
lean_inc(v_val_3738_);
lean_dec_ref(v_e_x3f_3737_);
v___y_3696_ = v_val_3738_;
goto v___jp_3695_;
}
}
}
v___jp_3695_:
{
switch(lean_obj_tag(v___y_3696_))
{
case 7:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; 
v___x_3697_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___closed__0));
v___x_3698_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v___x_3697_, v___y_3696_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3698_;
}
case 6:
{
lean_object* v___x_3699_; lean_object* v___x_3700_; 
v___x_3699_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___closed__0));
v___x_3700_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v___x_3699_, v___y_3696_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3700_;
}
case 8:
{
lean_object* v___x_3701_; lean_object* v___x_3702_; 
v___x_3701_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___closed__0));
v___x_3702_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v___x_3701_, v___y_3696_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3702_;
}
case 5:
{
lean_object* v_dummy_3703_; lean_object* v_nargs_3704_; lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; 
v_dummy_3703_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_3704_ = l_Lean_Expr_getAppNumArgs(v___y_3696_);
lean_inc(v_nargs_3704_);
v___x_3705_ = lean_mk_array(v_nargs_3704_, v_dummy_3703_);
v___x_3706_ = lean_unsigned_to_nat(1u);
v___x_3707_ = lean_nat_sub(v_nargs_3704_, v___x_3706_);
lean_dec(v_nargs_3704_);
v___x_3708_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__10(v_skipInstances_3683_, v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v___y_3696_, v___x_3705_, v___x_3707_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3708_;
}
case 10:
{
lean_object* v_data_3709_; lean_object* v_expr_3710_; lean_object* v___x_3711_; 
v_data_3709_ = lean_ctor_get(v___y_3696_, 0);
v_expr_3710_ = lean_ctor_get(v___y_3696_, 1);
lean_inc_ref(v_expr_3710_);
lean_inc_ref(v_post_3680_);
lean_inc_ref(v_pre_3678_);
v___x_3711_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v_expr_3710_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; size_t v___x_3713_; size_t v___x_3714_; uint8_t v___x_3715_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref(v___x_3711_);
v___x_3713_ = lean_ptr_addr(v_expr_3710_);
v___x_3714_ = lean_ptr_addr(v_a_3712_);
v___x_3715_ = lean_usize_dec_eq(v___x_3713_, v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
lean_inc(v_data_3709_);
lean_dec_ref(v___y_3696_);
v___x_3716_ = l_Lean_Expr_mdata___override(v_data_3709_, v_a_3712_);
v___x_3717_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v___x_3716_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3717_;
}
else
{
lean_object* v___x_3718_; 
lean_dec(v_a_3712_);
v___x_3718_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v___y_3696_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3718_;
}
}
else
{
lean_dec_ref(v___y_3696_);
lean_dec_ref(v_post_3680_);
lean_dec_ref(v_pre_3678_);
return v___x_3711_;
}
}
case 11:
{
lean_object* v_typeName_3719_; lean_object* v_idx_3720_; lean_object* v_struct_3721_; lean_object* v___x_3722_; 
v_typeName_3719_ = lean_ctor_get(v___y_3696_, 0);
v_idx_3720_ = lean_ctor_get(v___y_3696_, 1);
v_struct_3721_ = lean_ctor_get(v___y_3696_, 2);
lean_inc_ref(v_struct_3721_);
lean_inc_ref(v_post_3680_);
lean_inc_ref(v_pre_3678_);
v___x_3722_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v_struct_3721_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
if (lean_obj_tag(v___x_3722_) == 0)
{
lean_object* v_a_3723_; size_t v___x_3724_; size_t v___x_3725_; uint8_t v___x_3726_; 
v_a_3723_ = lean_ctor_get(v___x_3722_, 0);
lean_inc(v_a_3723_);
lean_dec_ref(v___x_3722_);
v___x_3724_ = lean_ptr_addr(v_struct_3721_);
v___x_3725_ = lean_ptr_addr(v_a_3723_);
v___x_3726_ = lean_usize_dec_eq(v___x_3724_, v___x_3725_);
if (v___x_3726_ == 0)
{
lean_object* v___x_3727_; lean_object* v___x_3728_; 
lean_inc(v_idx_3720_);
lean_inc(v_typeName_3719_);
lean_dec_ref(v___y_3696_);
v___x_3727_ = l_Lean_Expr_proj___override(v_typeName_3719_, v_idx_3720_, v_a_3723_);
v___x_3728_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v___x_3727_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3728_;
}
else
{
lean_object* v___x_3729_; 
lean_dec(v_a_3723_);
v___x_3729_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v___y_3696_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3729_;
}
}
else
{
lean_dec_ref(v___y_3696_);
lean_dec_ref(v_post_3680_);
lean_dec_ref(v_pre_3678_);
return v___x_3722_;
}
}
default: 
{
lean_object* v___x_3730_; 
v___x_3730_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3678_, v_post_3680_, v_usedLetOnly_3681_, v_skipConstInApp_3682_, v_skipInstances_3683_, v___y_3696_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
return v___x_3730_;
}
}
}
}
}
else
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3747_; 
lean_dec_ref(v_post_3680_);
lean_dec_ref(v_e_3679_);
lean_dec_ref(v_pre_3678_);
v_a_3740_ = lean_ctor_get(v___x_3690_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3690_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3742_ = v___x_3690_;
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3690_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3747_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3745_; 
if (v_isShared_3743_ == 0)
{
v___x_3745_ = v___x_3742_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_a_3740_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___boxed(lean_object* v_pre_3748_, lean_object* v_e_3749_, lean_object* v_post_3750_, lean_object* v_usedLetOnly_3751_, lean_object* v_skipConstInApp_3752_, lean_object* v_skipInstances_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
uint8_t v_usedLetOnly_boxed_3760_; uint8_t v_skipConstInApp_boxed_3761_; uint8_t v_skipInstances_boxed_3762_; lean_object* v_res_3763_; 
v_usedLetOnly_boxed_3760_ = lean_unbox(v_usedLetOnly_3751_);
v_skipConstInApp_boxed_3761_ = lean_unbox(v_skipConstInApp_3752_);
v_skipInstances_boxed_3762_ = lean_unbox(v_skipInstances_3753_);
v_res_3763_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1(v_pre_3748_, v_e_3749_, v_post_3750_, v_usedLetOnly_boxed_3760_, v_skipConstInApp_boxed_3761_, v_skipInstances_boxed_3762_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
return v_res_3763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(lean_object* v_pre_3764_, lean_object* v_post_3765_, uint8_t v_usedLetOnly_3766_, uint8_t v_skipConstInApp_3767_, uint8_t v_skipInstances_3768_, lean_object* v_e_3769_, lean_object* v_a_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
lean_object* v___x_3776_; lean_object* v___x_3777_; 
lean_inc(v_a_3770_);
v___x_3776_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3776_, 0, lean_box(0));
lean_closure_set(v___x_3776_, 1, lean_box(0));
lean_closure_set(v___x_3776_, 2, v_a_3770_);
v___x_3777_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_box(0), v___x_3776_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
if (lean_obj_tag(v___x_3777_) == 0)
{
lean_object* v_a_3778_; lean_object* v___x_3780_; uint8_t v_isShared_3781_; uint8_t v_isSharedCheck_3811_; 
v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3780_ = v___x_3777_;
v_isShared_3781_ = v_isSharedCheck_3811_;
goto v_resetjp_3779_;
}
else
{
lean_inc(v_a_3778_);
lean_dec(v___x_3777_);
v___x_3780_ = lean_box(0);
v_isShared_3781_ = v_isSharedCheck_3811_;
goto v_resetjp_3779_;
}
v_resetjp_3779_:
{
lean_object* v___x_3782_; 
v___x_3782_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_3778_, v_e_3769_);
lean_dec(v_a_3778_);
if (lean_obj_tag(v___x_3782_) == 0)
{
lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___f_3786_; lean_object* v___x_3787_; 
lean_del_object(v___x_3780_);
v___x_3783_ = lean_box(v_usedLetOnly_3766_);
v___x_3784_ = lean_box(v_skipConstInApp_3767_);
v___x_3785_ = lean_box(v_skipInstances_3768_);
lean_inc_ref(v_e_3769_);
v___f_3786_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3786_, 0, v_pre_3764_);
lean_closure_set(v___f_3786_, 1, v_e_3769_);
lean_closure_set(v___f_3786_, 2, v_post_3765_);
lean_closure_set(v___f_3786_, 3, v___x_3783_);
lean_closure_set(v___f_3786_, 4, v___x_3784_);
lean_closure_set(v___f_3786_, 5, v___x_3785_);
lean_inc_ref(v___y_3773_);
v___x_3787_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg(v___f_3786_, v_a_3770_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
if (lean_obj_tag(v___x_3787_) == 0)
{
lean_object* v_a_3788_; lean_object* v___f_3789_; lean_object* v___x_3790_; 
v_a_3788_ = lean_ctor_get(v___x_3787_, 0);
lean_inc(v_a_3788_);
lean_dec_ref(v___x_3787_);
lean_inc(v_a_3788_);
lean_inc(v_a_3770_);
v___f_3789_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3789_, 0, v_a_3770_);
lean_closure_set(v___f_3789_, 1, v_e_3769_);
lean_closure_set(v___f_3789_, 2, v_a_3788_);
v___x_3790_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_box(0), v___f_3789_, v___y_3771_, v___y_3772_, v___y_3773_, v___y_3774_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3797_ == 0)
{
lean_object* v_unused_3798_; 
v_unused_3798_ = lean_ctor_get(v___x_3790_, 0);
lean_dec(v_unused_3798_);
v___x_3792_ = v___x_3790_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_dec(v___x_3790_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
lean_ctor_set(v___x_3792_, 0, v_a_3788_);
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3788_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec(v_a_3788_);
v_a_3799_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3790_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3790_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
}
else
{
lean_dec_ref(v_e_3769_);
return v___x_3787_;
}
}
else
{
lean_object* v_val_3807_; lean_object* v___x_3809_; 
lean_dec_ref(v_e_3769_);
lean_dec_ref(v_post_3765_);
lean_dec_ref(v_pre_3764_);
v_val_3807_ = lean_ctor_get(v___x_3782_, 0);
lean_inc(v_val_3807_);
lean_dec_ref(v___x_3782_);
if (v_isShared_3781_ == 0)
{
lean_ctor_set(v___x_3780_, 0, v_val_3807_);
v___x_3809_ = v___x_3780_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v_val_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_dec_ref(v_e_3769_);
lean_dec_ref(v_post_3765_);
lean_dec_ref(v_pre_3764_);
v_a_3812_ = lean_ctor_get(v___x_3777_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3777_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3777_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3777_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
v___x_3817_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
return v___x_3817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___lam__0___boxed(lean_object* v_fvars_3820_, lean_object* v_pre_3821_, lean_object* v_post_3822_, lean_object* v_usedLetOnly_3823_, lean_object* v_skipConstInApp_3824_, lean_object* v_skipInstances_3825_, lean_object* v_body_3826_, lean_object* v_x_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
uint8_t v_usedLetOnly_boxed_3834_; uint8_t v_skipConstInApp_boxed_3835_; uint8_t v_skipInstances_boxed_3836_; lean_object* v_res_3837_; 
v_usedLetOnly_boxed_3834_ = lean_unbox(v_usedLetOnly_3823_);
v_skipConstInApp_boxed_3835_ = lean_unbox(v_skipConstInApp_3824_);
v_skipInstances_boxed_3836_ = lean_unbox(v_skipInstances_3825_);
v_res_3837_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___lam__0(v_fvars_3820_, v_pre_3821_, v_post_3822_, v_usedLetOnly_boxed_3834_, v_skipConstInApp_boxed_3835_, v_skipInstances_boxed_3836_, v_body_3826_, v_x_3827_, v___y_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec(v___y_3828_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7(lean_object* v_pre_3838_, lean_object* v_post_3839_, uint8_t v_usedLetOnly_3840_, uint8_t v_skipConstInApp_3841_, uint8_t v_skipInstances_3842_, lean_object* v_fvars_3843_, lean_object* v_e_3844_, lean_object* v_a_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_){
_start:
{
if (lean_obj_tag(v_e_3844_) == 7)
{
lean_object* v_binderName_3851_; lean_object* v_binderType_3852_; lean_object* v_body_3853_; uint8_t v_binderInfo_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_binderName_3851_ = lean_ctor_get(v_e_3844_, 0);
lean_inc(v_binderName_3851_);
v_binderType_3852_ = lean_ctor_get(v_e_3844_, 1);
lean_inc_ref(v_binderType_3852_);
v_body_3853_ = lean_ctor_get(v_e_3844_, 2);
lean_inc_ref(v_body_3853_);
v_binderInfo_3854_ = lean_ctor_get_uint8(v_e_3844_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3844_);
v___x_3855_ = lean_expr_instantiate_rev(v_binderType_3852_, v_fvars_3843_);
lean_dec_ref(v_binderType_3852_);
lean_inc_ref(v_post_3839_);
lean_inc_ref(v_pre_3838_);
v___x_3856_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3838_, v_post_3839_, v_usedLetOnly_3840_, v_skipConstInApp_3841_, v_skipInstances_3842_, v___x_3855_, v_a_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
if (lean_obj_tag(v___x_3856_) == 0)
{
lean_object* v_a_3857_; lean_object* v___x_3858_; lean_object* v___x_3859_; lean_object* v___x_3860_; lean_object* v___f_3861_; uint8_t v___x_3862_; lean_object* v___x_3863_; 
v_a_3857_ = lean_ctor_get(v___x_3856_, 0);
lean_inc(v_a_3857_);
lean_dec_ref(v___x_3856_);
v___x_3858_ = lean_box(v_usedLetOnly_3840_);
v___x_3859_ = lean_box(v_skipConstInApp_3841_);
v___x_3860_ = lean_box(v_skipInstances_3842_);
v___f_3861_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3861_, 0, v_fvars_3843_);
lean_closure_set(v___f_3861_, 1, v_pre_3838_);
lean_closure_set(v___f_3861_, 2, v_post_3839_);
lean_closure_set(v___f_3861_, 3, v___x_3858_);
lean_closure_set(v___f_3861_, 4, v___x_3859_);
lean_closure_set(v___f_3861_, 5, v___x_3860_);
lean_closure_set(v___f_3861_, 6, v_body_3853_);
v___x_3862_ = 0;
v___x_3863_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(v_binderName_3851_, v_binderInfo_3854_, v_a_3857_, v___f_3861_, v___x_3862_, v_a_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
return v___x_3863_;
}
else
{
lean_dec_ref(v_body_3853_);
lean_dec(v_binderName_3851_);
lean_dec_ref(v_fvars_3843_);
lean_dec_ref(v_post_3839_);
lean_dec_ref(v_pre_3838_);
return v___x_3856_;
}
}
else
{
lean_object* v___x_3864_; lean_object* v___x_3865_; 
v___x_3864_ = lean_expr_instantiate_rev(v_e_3844_, v_fvars_3843_);
lean_dec_ref(v_e_3844_);
lean_inc_ref(v_post_3839_);
lean_inc_ref(v_pre_3838_);
v___x_3865_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3838_, v_post_3839_, v_usedLetOnly_3840_, v_skipConstInApp_3841_, v_skipInstances_3842_, v___x_3864_, v_a_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; uint8_t v___x_3867_; uint8_t v___x_3868_; uint8_t v___x_3869_; lean_object* v___x_3870_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
lean_inc(v_a_3866_);
lean_dec_ref(v___x_3865_);
v___x_3867_ = 0;
v___x_3868_ = 1;
v___x_3869_ = 1;
v___x_3870_ = l_Lean_Meta_mkForallFVars(v_fvars_3843_, v_a_3866_, v___x_3867_, v_usedLetOnly_3840_, v___x_3868_, v___x_3869_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec_ref(v_fvars_3843_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref(v___x_3870_);
v___x_3872_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3838_, v_post_3839_, v_usedLetOnly_3840_, v_skipConstInApp_3841_, v_skipInstances_3842_, v_a_3871_, v_a_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
return v___x_3872_;
}
else
{
lean_dec_ref(v_post_3839_);
lean_dec_ref(v_pre_3838_);
return v___x_3870_;
}
}
else
{
lean_dec_ref(v_fvars_3843_);
lean_dec_ref(v_post_3839_);
lean_dec_ref(v_pre_3838_);
return v___x_3865_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___lam__0(lean_object* v_fvars_3873_, lean_object* v_pre_3874_, lean_object* v_post_3875_, uint8_t v_usedLetOnly_3876_, uint8_t v_skipConstInApp_3877_, uint8_t v_skipInstances_3878_, lean_object* v_body_3879_, lean_object* v_x_3880_, lean_object* v___y_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = lean_array_push(v_fvars_3873_, v_x_3880_);
v___x_3888_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7(v_pre_3874_, v_post_3875_, v_usedLetOnly_3876_, v_skipConstInApp_3877_, v_skipInstances_3878_, v___x_3887_, v_body_3879_, v___y_3881_, v___y_3882_, v___y_3883_, v___y_3884_, v___y_3885_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5___boxed(lean_object* v_pre_3889_, lean_object* v_post_3890_, lean_object* v_usedLetOnly_3891_, lean_object* v_skipConstInApp_3892_, lean_object* v_skipInstances_3893_, lean_object* v_e_3894_, lean_object* v_a_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
uint8_t v_usedLetOnly_boxed_3901_; uint8_t v_skipConstInApp_boxed_3902_; uint8_t v_skipInstances_boxed_3903_; lean_object* v_res_3904_; 
v_usedLetOnly_boxed_3901_ = lean_unbox(v_usedLetOnly_3891_);
v_skipConstInApp_boxed_3902_ = lean_unbox(v_skipConstInApp_3892_);
v_skipInstances_boxed_3903_ = lean_unbox(v_skipInstances_3893_);
v_res_3904_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__5(v_pre_3889_, v_post_3890_, v_usedLetOnly_boxed_3901_, v_skipConstInApp_boxed_3902_, v_skipInstances_boxed_3903_, v_e_3894_, v_a_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v_a_3895_);
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__4___boxed(lean_object* v_pre_3905_, lean_object* v_post_3906_, lean_object* v_usedLetOnly_3907_, lean_object* v_skipConstInApp_3908_, lean_object* v_skipInstances_3909_, lean_object* v_sz_3910_, lean_object* v_i_3911_, lean_object* v_bs_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
uint8_t v_usedLetOnly_boxed_3919_; uint8_t v_skipConstInApp_boxed_3920_; uint8_t v_skipInstances_boxed_3921_; size_t v_sz_boxed_3922_; size_t v_i_boxed_3923_; lean_object* v_res_3924_; 
v_usedLetOnly_boxed_3919_ = lean_unbox(v_usedLetOnly_3907_);
v_skipConstInApp_boxed_3920_ = lean_unbox(v_skipConstInApp_3908_);
v_skipInstances_boxed_3921_ = lean_unbox(v_skipInstances_3909_);
v_sz_boxed_3922_ = lean_unbox_usize(v_sz_3910_);
lean_dec(v_sz_3910_);
v_i_boxed_3923_ = lean_unbox_usize(v_i_3911_);
lean_dec(v_i_3911_);
v_res_3924_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__4(v_pre_3905_, v_post_3906_, v_usedLetOnly_boxed_3919_, v_skipConstInApp_boxed_3920_, v_skipInstances_boxed_3921_, v_sz_boxed_3922_, v_i_boxed_3923_, v_bs_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec(v___y_3913_);
return v_res_3924_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___boxed(lean_object* v_pre_3925_, lean_object* v_post_3926_, lean_object* v_usedLetOnly_3927_, lean_object* v_skipConstInApp_3928_, lean_object* v_skipInstances_3929_, lean_object* v_e_3930_, lean_object* v_a_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
uint8_t v_usedLetOnly_boxed_3937_; uint8_t v_skipConstInApp_boxed_3938_; uint8_t v_skipInstances_boxed_3939_; lean_object* v_res_3940_; 
v_usedLetOnly_boxed_3937_ = lean_unbox(v_usedLetOnly_3927_);
v_skipConstInApp_boxed_3938_ = lean_unbox(v_skipConstInApp_3928_);
v_skipInstances_boxed_3939_ = lean_unbox(v_skipInstances_3929_);
v_res_3940_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_3925_, v_post_3926_, v_usedLetOnly_boxed_3937_, v_skipConstInApp_boxed_3938_, v_skipInstances_boxed_3939_, v_e_3930_, v_a_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec(v_a_3931_);
return v_res_3940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7___boxed(lean_object* v_pre_3941_, lean_object* v_post_3942_, lean_object* v_usedLetOnly_3943_, lean_object* v_skipConstInApp_3944_, lean_object* v_skipInstances_3945_, lean_object* v_fvars_3946_, lean_object* v_e_3947_, lean_object* v_a_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_){
_start:
{
uint8_t v_usedLetOnly_boxed_3954_; uint8_t v_skipConstInApp_boxed_3955_; uint8_t v_skipInstances_boxed_3956_; lean_object* v_res_3957_; 
v_usedLetOnly_boxed_3954_ = lean_unbox(v_usedLetOnly_3943_);
v_skipConstInApp_boxed_3955_ = lean_unbox(v_skipConstInApp_3944_);
v_skipInstances_boxed_3956_ = lean_unbox(v_skipInstances_3945_);
v_res_3957_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7(v_pre_3941_, v_post_3942_, v_usedLetOnly_boxed_3954_, v_skipConstInApp_boxed_3955_, v_skipInstances_boxed_3956_, v_fvars_3946_, v_e_3947_, v_a_3948_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
lean_dec(v___y_3952_);
lean_dec_ref(v___y_3951_);
lean_dec(v___y_3950_);
lean_dec_ref(v___y_3949_);
lean_dec(v_a_3948_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8___boxed(lean_object* v_pre_3958_, lean_object* v_post_3959_, lean_object* v_usedLetOnly_3960_, lean_object* v_skipConstInApp_3961_, lean_object* v_skipInstances_3962_, lean_object* v_fvars_3963_, lean_object* v_e_3964_, lean_object* v_a_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
uint8_t v_usedLetOnly_boxed_3971_; uint8_t v_skipConstInApp_boxed_3972_; uint8_t v_skipInstances_boxed_3973_; lean_object* v_res_3974_; 
v_usedLetOnly_boxed_3971_ = lean_unbox(v_usedLetOnly_3960_);
v_skipConstInApp_boxed_3972_ = lean_unbox(v_skipConstInApp_3961_);
v_skipInstances_boxed_3973_ = lean_unbox(v_skipInstances_3962_);
v_res_3974_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__8(v_pre_3958_, v_post_3959_, v_usedLetOnly_boxed_3971_, v_skipConstInApp_boxed_3972_, v_skipInstances_boxed_3973_, v_fvars_3963_, v_e_3964_, v_a_3965_, v___y_3966_, v___y_3967_, v___y_3968_, v___y_3969_);
lean_dec(v___y_3969_);
lean_dec_ref(v___y_3968_);
lean_dec(v___y_3967_);
lean_dec_ref(v___y_3966_);
lean_dec(v_a_3965_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9___boxed(lean_object* v_pre_3975_, lean_object* v_post_3976_, lean_object* v_usedLetOnly_3977_, lean_object* v_skipConstInApp_3978_, lean_object* v_skipInstances_3979_, lean_object* v_fvars_3980_, lean_object* v_e_3981_, lean_object* v_a_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_, lean_object* v___y_3986_, lean_object* v___y_3987_){
_start:
{
uint8_t v_usedLetOnly_boxed_3988_; uint8_t v_skipConstInApp_boxed_3989_; uint8_t v_skipInstances_boxed_3990_; lean_object* v_res_3991_; 
v_usedLetOnly_boxed_3988_ = lean_unbox(v_usedLetOnly_3977_);
v_skipConstInApp_boxed_3989_ = lean_unbox(v_skipConstInApp_3978_);
v_skipInstances_boxed_3990_ = lean_unbox(v_skipInstances_3979_);
v_res_3991_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9(v_pre_3975_, v_post_3976_, v_usedLetOnly_boxed_3988_, v_skipConstInApp_boxed_3989_, v_skipInstances_boxed_3990_, v_fvars_3980_, v_e_3981_, v_a_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_);
lean_dec(v___y_3986_);
lean_dec_ref(v___y_3985_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v_a_3982_);
return v_res_3991_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg___boxed(lean_object* v_upperBound_3992_, lean_object* v___x_3993_, lean_object* v_pre_3994_, lean_object* v_post_3995_, lean_object* v_usedLetOnly_3996_, lean_object* v_skipConstInApp_3997_, lean_object* v_skipInstances_3998_, lean_object* v_a_3999_, lean_object* v_b_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_){
_start:
{
uint8_t v_usedLetOnly_boxed_4007_; uint8_t v_skipConstInApp_boxed_4008_; uint8_t v_skipInstances_boxed_4009_; lean_object* v_res_4010_; 
v_usedLetOnly_boxed_4007_ = lean_unbox(v_usedLetOnly_3996_);
v_skipConstInApp_boxed_4008_ = lean_unbox(v_skipConstInApp_3997_);
v_skipInstances_boxed_4009_ = lean_unbox(v_skipInstances_3998_);
v_res_4010_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg(v_upperBound_3992_, v___x_3993_, v_pre_3994_, v_post_3995_, v_usedLetOnly_boxed_4007_, v_skipConstInApp_boxed_4008_, v_skipInstances_boxed_4009_, v_a_3999_, v_b_4000_, v___y_4001_, v___y_4002_, v___y_4003_, v___y_4004_, v___y_4005_);
lean_dec(v___y_4005_);
lean_dec_ref(v___y_4004_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v___x_3993_);
lean_dec(v_upperBound_3992_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__10___boxed(lean_object* v_skipInstances_4011_, lean_object* v_pre_4012_, lean_object* v_post_4013_, lean_object* v_usedLetOnly_4014_, lean_object* v_skipConstInApp_4015_, lean_object* v_x_4016_, lean_object* v_x_4017_, lean_object* v_x_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_){
_start:
{
uint8_t v_skipInstances_boxed_4025_; uint8_t v_usedLetOnly_boxed_4026_; uint8_t v_skipConstInApp_boxed_4027_; lean_object* v_res_4028_; 
v_skipInstances_boxed_4025_ = lean_unbox(v_skipInstances_4011_);
v_usedLetOnly_boxed_4026_ = lean_unbox(v_usedLetOnly_4014_);
v_skipConstInApp_boxed_4027_ = lean_unbox(v_skipConstInApp_4015_);
v_res_4028_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__10(v_skipInstances_boxed_4025_, v_pre_4012_, v_post_4013_, v_usedLetOnly_boxed_4026_, v_skipConstInApp_boxed_4027_, v_x_4016_, v_x_4017_, v_x_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
return v_res_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2(lean_object* v_input_4029_, lean_object* v_pre_4030_, lean_object* v_post_4031_, uint8_t v_usedLetOnly_4032_, uint8_t v_skipConstInApp_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
lean_object* v___x_4039_; lean_object* v___x_4040_; lean_object* v_a_4041_; uint8_t v___x_4042_; lean_object* v___x_4043_; 
v___x_4039_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_4040_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_box(0), v___x_4039_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
lean_inc(v_a_4041_);
lean_dec_ref(v___x_4040_);
v___x_4042_ = 0;
v___x_4043_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3(v_pre_4030_, v_post_4031_, v_usedLetOnly_4032_, v_skipConstInApp_4033_, v___x_4042_, v_input_4029_, v_a_4041_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4053_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
lean_inc(v_a_4044_);
lean_dec_ref(v___x_4043_);
v___x_4045_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4045_, 0, lean_box(0));
lean_closure_set(v___x_4045_, 1, lean_box(0));
lean_closure_set(v___x_4045_, 2, v_a_4041_);
v___x_4046_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_box(0), v___x_4045_, v___y_4034_, v___y_4035_, v___y_4036_, v___y_4037_);
v_isSharedCheck_4053_ = !lean_is_exclusive(v___x_4046_);
if (v_isSharedCheck_4053_ == 0)
{
lean_object* v_unused_4054_; 
v_unused_4054_ = lean_ctor_get(v___x_4046_, 0);
lean_dec(v_unused_4054_);
v___x_4048_ = v___x_4046_;
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
else
{
lean_dec(v___x_4046_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4053_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v___x_4051_; 
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v_a_4044_);
v___x_4051_ = v___x_4048_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_a_4044_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
else
{
lean_dec(v_a_4041_);
return v___x_4043_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___boxed(lean_object* v_input_4055_, lean_object* v_pre_4056_, lean_object* v_post_4057_, lean_object* v_usedLetOnly_4058_, lean_object* v_skipConstInApp_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
uint8_t v_usedLetOnly_boxed_4065_; uint8_t v_skipConstInApp_boxed_4066_; lean_object* v_res_4067_; 
v_usedLetOnly_boxed_4065_ = lean_unbox(v_usedLetOnly_4058_);
v_skipConstInApp_boxed_4066_ = lean_unbox(v_skipConstInApp_4059_);
v_res_4067_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2(v_input_4055_, v_pre_4056_, v_post_4057_, v_usedLetOnly_boxed_4065_, v_skipConstInApp_boxed_4066_, v___y_4060_, v___y_4061_, v___y_4062_, v___y_4063_);
lean_dec(v___y_4063_);
lean_dec_ref(v___y_4062_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
return v_res_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object* v_e_4071_, lean_object* v_a_4072_, lean_object* v_a_4073_, lean_object* v_a_4074_, lean_object* v_a_4075_){
_start:
{
lean_object* v___f_4077_; lean_object* v___x_4078_; 
v___f_4077_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__0));
v___x_4078_ = lean_find_expr(v___f_4077_, v_e_4071_);
if (lean_obj_tag(v___x_4078_) == 0)
{
lean_object* v___x_4079_; 
v___x_4079_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4079_, 0, v_e_4071_);
return v___x_4079_;
}
else
{
lean_object* v_post_4080_; lean_object* v___f_4081_; uint8_t v___x_4082_; lean_object* v___x_4083_; 
lean_dec_ref(v___x_4078_);
v_post_4080_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__1));
v___f_4081_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__2));
v___x_4082_ = 0;
v___x_4083_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2(v_e_4071_, v___f_4081_, v_post_4080_, v___x_4082_, v___x_4082_, v_a_4072_, v_a_4073_, v_a_4074_, v_a_4075_);
return v___x_4083_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object* v_e_4084_, lean_object* v_a_4085_, lean_object* v_a_4086_, lean_object* v_a_4087_, lean_object* v_a_4088_, lean_object* v_a_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Lean_Meta_Grind_foldProjs(v_e_4084_, v_a_4085_, v_a_4086_, v_a_4087_, v_a_4088_);
lean_dec(v_a_4088_);
lean_dec_ref(v_a_4087_);
lean_dec(v_a_4086_);
lean_dec_ref(v_a_4085_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6(lean_object* v_upperBound_4091_, lean_object* v___x_4092_, lean_object* v_pre_4093_, lean_object* v_post_4094_, uint8_t v_usedLetOnly_4095_, uint8_t v_skipConstInApp_4096_, uint8_t v_skipInstances_4097_, lean_object* v___x_4098_, lean_object* v_inst_4099_, lean_object* v_R_4100_, lean_object* v_a_4101_, lean_object* v_b_4102_, lean_object* v_c_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_){
_start:
{
lean_object* v___x_4110_; 
v___x_4110_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___redArg(v_upperBound_4091_, v___x_4092_, v_pre_4093_, v_post_4094_, v_usedLetOnly_4095_, v_skipConstInApp_4096_, v_skipInstances_4097_, v_a_4101_, v_b_4102_, v___y_4104_, v___y_4105_, v___y_4106_, v___y_4107_, v___y_4108_);
return v___x_4110_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6___boxed(lean_object** _args){
lean_object* v_upperBound_4111_ = _args[0];
lean_object* v___x_4112_ = _args[1];
lean_object* v_pre_4113_ = _args[2];
lean_object* v_post_4114_ = _args[3];
lean_object* v_usedLetOnly_4115_ = _args[4];
lean_object* v_skipConstInApp_4116_ = _args[5];
lean_object* v_skipInstances_4117_ = _args[6];
lean_object* v___x_4118_ = _args[7];
lean_object* v_inst_4119_ = _args[8];
lean_object* v_R_4120_ = _args[9];
lean_object* v_a_4121_ = _args[10];
lean_object* v_b_4122_ = _args[11];
lean_object* v_c_4123_ = _args[12];
lean_object* v___y_4124_ = _args[13];
lean_object* v___y_4125_ = _args[14];
lean_object* v___y_4126_ = _args[15];
lean_object* v___y_4127_ = _args[16];
lean_object* v___y_4128_ = _args[17];
lean_object* v___y_4129_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4130_; uint8_t v_skipConstInApp_boxed_4131_; uint8_t v_skipInstances_boxed_4132_; lean_object* v_res_4133_; 
v_usedLetOnly_boxed_4130_ = lean_unbox(v_usedLetOnly_4115_);
v_skipConstInApp_boxed_4131_ = lean_unbox(v_skipConstInApp_4116_);
v_skipInstances_boxed_4132_ = lean_unbox(v_skipInstances_4117_);
v_res_4133_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__6(v_upperBound_4111_, v___x_4112_, v_pre_4113_, v_post_4114_, v_usedLetOnly_boxed_4130_, v_skipConstInApp_boxed_4131_, v_skipInstances_boxed_4132_, v___x_4118_, v_inst_4119_, v_R_4120_, v_a_4121_, v_b_4122_, v_c_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_, v___y_4128_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
lean_dec_ref(v___y_4125_);
lean_dec(v___y_4124_);
lean_dec(v___x_4118_);
lean_dec_ref(v___x_4112_);
lean_dec(v_upperBound_4111_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8(lean_object* v_00_u03b1_4134_, lean_object* v_name_4135_, uint8_t v_bi_4136_, lean_object* v_type_4137_, lean_object* v_k_4138_, uint8_t v_kind_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_){
_start:
{
lean_object* v___x_4146_; 
v___x_4146_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___redArg(v_name_4135_, v_bi_4136_, v_type_4137_, v_k_4138_, v_kind_4139_, v___y_4140_, v___y_4141_, v___y_4142_, v___y_4143_, v___y_4144_);
return v___x_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4147_, lean_object* v_name_4148_, lean_object* v_bi_4149_, lean_object* v_type_4150_, lean_object* v_k_4151_, lean_object* v_kind_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
uint8_t v_bi_boxed_4159_; uint8_t v_kind_boxed_4160_; lean_object* v_res_4161_; 
v_bi_boxed_4159_ = lean_unbox(v_bi_4149_);
v_kind_boxed_4160_ = lean_unbox(v_kind_4152_);
v_res_4161_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__7_spec__8(v_00_u03b1_4147_, v_name_4148_, v_bi_boxed_4159_, v_type_4150_, v_k_4151_, v_kind_boxed_4160_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_, v___y_4157_);
lean_dec(v___y_4157_);
lean_dec_ref(v___y_4156_);
lean_dec(v___y_4155_);
lean_dec_ref(v___y_4154_);
lean_dec(v___y_4153_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11(lean_object* v_00_u03b1_4162_, lean_object* v_name_4163_, lean_object* v_type_4164_, lean_object* v_val_4165_, lean_object* v_k_4166_, uint8_t v_nondep_4167_, uint8_t v_kind_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_, lean_object* v___y_4172_, lean_object* v___y_4173_){
_start:
{
lean_object* v___x_4175_; 
v___x_4175_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___redArg(v_name_4163_, v_type_4164_, v_val_4165_, v_k_4166_, v_nondep_4167_, v_kind_4168_, v___y_4169_, v___y_4170_, v___y_4171_, v___y_4172_, v___y_4173_);
return v___x_4175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11___boxed(lean_object* v_00_u03b1_4176_, lean_object* v_name_4177_, lean_object* v_type_4178_, lean_object* v_val_4179_, lean_object* v_k_4180_, lean_object* v_nondep_4181_, lean_object* v_kind_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
uint8_t v_nondep_boxed_4189_; uint8_t v_kind_boxed_4190_; lean_object* v_res_4191_; 
v_nondep_boxed_4189_ = lean_unbox(v_nondep_4181_);
v_kind_boxed_4190_ = lean_unbox(v_kind_4182_);
v_res_4191_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__9_spec__11(v_00_u03b1_4176_, v_name_4177_, v_type_4178_, v_val_4179_, v_k_4180_, v_nondep_boxed_4189_, v_kind_boxed_4190_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
lean_dec(v___y_4185_);
lean_dec_ref(v___y_4184_);
lean_dec(v___y_4183_);
return v_res_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14(lean_object* v_00_u03b1_4192_, lean_object* v_ref_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v___x_4199_; 
v___x_4199_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___redArg(v_ref_4193_);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14___boxed(lean_object* v_00_u03b1_4200_, lean_object* v_ref_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11_spec__14(v_00_u03b1_4200_, v_ref_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11(lean_object* v_00_u03b1_4208_, lean_object* v_x_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v___x_4216_; 
lean_inc_ref(v___y_4213_);
v___x_4216_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___redArg(v_x_4209_, v___y_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11___boxed(lean_object* v_00_u03b1_4217_, lean_object* v_x_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3_spec__11(v_00_u03b1_4217_, v_x_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object* v_e_4233_, lean_object* v_config_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_00___x40___internal___hyg_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = lean_grind_normalize(v_e_4233_, v_config_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
return v_res_4240_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4(void){
_start:
{
lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4248_ = lean_box(0);
v___x_4249_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_4250_ = l_Lean_mkConst(v___x_4249_, v___x_4248_);
return v___x_4250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object* v_e_4251_){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = lean_obj_once(&l_Lean_Meta_Grind_markAsMatchCond___closed__4, &l_Lean_Meta_Grind_markAsMatchCond___closed__4_once, _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4);
v___x_4253_ = l_Lean_Expr_app___override(v___x_4252_, v_e_4251_);
return v___x_4253_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object* v_e_4254_){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; uint8_t v___x_4257_; 
v___x_4255_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_4256_ = lean_unsigned_to_nat(1u);
v___x_4257_ = l_Lean_Expr_isAppOfArity(v_e_4254_, v___x_4255_, v___x_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object* v_e_4258_){
_start:
{
uint8_t v_res_4259_; lean_object* v_r_4260_; 
v_res_4259_ = l_Lean_Meta_Grind_isMatchCond(v_e_4258_);
lean_dec_ref(v_e_4258_);
v_r_4260_ = lean_box(v_res_4259_);
return v_r_4260_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2(void){
_start:
{
lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; 
v___x_4266_ = lean_box(0);
v___x_4267_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4268_ = l_Lean_mkConst(v___x_4267_, v___x_4266_);
return v___x_4268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object* v_e_4269_){
_start:
{
lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4270_ = lean_obj_once(&l_Lean_Meta_Grind_markAsPreMatchCond___closed__2, &l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once, _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2);
v___x_4271_ = l_Lean_Expr_app___override(v___x_4270_, v_e_4269_);
return v___x_4271_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object* v_e_4272_){
_start:
{
lean_object* v___x_4273_; lean_object* v___x_4274_; uint8_t v___x_4275_; 
v___x_4273_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4274_ = lean_unsigned_to_nat(1u);
v___x_4275_ = l_Lean_Expr_isAppOfArity(v_e_4272_, v___x_4273_, v___x_4274_);
return v___x_4275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object* v_e_4276_){
_start:
{
uint8_t v_res_4277_; lean_object* v_r_4278_; 
v_res_4277_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_4276_);
lean_dec_ref(v_e_4276_);
v_r_4278_ = lean_box(v_res_4277_);
return v_r_4278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object* v_e_4279_, lean_object* v_a_4280_){
_start:
{
lean_object* v___x_4282_; 
lean_inc_ref(v_e_4279_);
v___x_4282_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4279_, v_a_4280_);
if (lean_obj_tag(v___x_4282_) == 0)
{
lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4299_; 
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4285_ = v___x_4282_;
v_isShared_4286_ = v_isSharedCheck_4299_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4282_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4299_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4292_; uint8_t v___x_4293_; 
v___x_4292_ = l_Lean_Expr_cleanupAnnotations(v_a_4283_);
v___x_4293_ = l_Lean_Expr_isApp(v___x_4292_);
if (v___x_4293_ == 0)
{
lean_dec_ref(v___x_4292_);
lean_dec_ref(v_e_4279_);
goto v___jp_4287_;
}
else
{
lean_object* v___x_4294_; lean_object* v___x_4295_; uint8_t v___x_4296_; 
v___x_4294_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4292_);
v___x_4295_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4296_ = l_Lean_Expr_isConstOf(v___x_4294_, v___x_4295_);
lean_dec_ref(v___x_4294_);
if (v___x_4296_ == 0)
{
lean_dec_ref(v_e_4279_);
goto v___jp_4287_;
}
else
{
lean_object* v___x_4297_; lean_object* v___x_4298_; 
lean_del_object(v___x_4285_);
v___x_4297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4297_, 0, v_e_4279_);
v___x_4298_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4297_);
return v___x_4298_;
}
}
v___jp_4287_:
{
lean_object* v___x_4288_; lean_object* v___x_4290_; 
v___x_4288_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__1___closed__0));
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 0, v___x_4288_);
v___x_4290_ = v___x_4285_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4288_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
else
{
lean_object* v_a_4300_; lean_object* v___x_4302_; uint8_t v_isShared_4303_; uint8_t v_isSharedCheck_4307_; 
lean_dec_ref(v_e_4279_);
v_a_4300_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4307_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4302_ = v___x_4282_;
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
else
{
lean_inc(v_a_4300_);
lean_dec(v___x_4282_);
v___x_4302_ = lean_box(0);
v_isShared_4303_ = v_isSharedCheck_4307_;
goto v_resetjp_4301_;
}
v_resetjp_4301_:
{
lean_object* v___x_4305_; 
if (v_isShared_4303_ == 0)
{
v___x_4305_ = v___x_4302_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v_a_4300_);
v___x_4305_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
return v___x_4305_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object* v_e_4308_, lean_object* v_a_4309_, lean_object* v_a_4310_){
_start:
{
lean_object* v_res_4311_; 
v_res_4311_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_4308_, v_a_4309_);
lean_dec(v_a_4309_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object* v_e_4312_, lean_object* v_a_4313_, lean_object* v_a_4314_, lean_object* v_a_4315_, lean_object* v_a_4316_, lean_object* v_a_4317_, lean_object* v_a_4318_, lean_object* v_a_4319_){
_start:
{
lean_object* v___x_4321_; 
v___x_4321_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_4312_, v_a_4317_);
return v___x_4321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object* v_e_4322_, lean_object* v_a_4323_, lean_object* v_a_4324_, lean_object* v_a_4325_, lean_object* v_a_4326_, lean_object* v_a_4327_, lean_object* v_a_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v_res_4331_; 
v_res_4331_ = l_Lean_Meta_Grind_reducePreMatchCond(v_e_4322_, v_a_4323_, v_a_4324_, v_a_4325_, v_a_4326_, v_a_4327_, v_a_4328_, v_a_4329_);
lean_dec(v_a_4329_);
lean_dec_ref(v_a_4328_);
lean_dec(v_a_4327_);
lean_dec_ref(v_a_4326_);
lean_dec(v_a_4325_);
lean_dec_ref(v_a_4324_);
lean_dec(v_a_4323_);
return v_res_4331_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4349_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4350_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4351_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond___boxed), 9, 0);
v___x_4352_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4349_, v___x_4350_, v___x_4351_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10____boxed(lean_object* v_a_4353_){
_start:
{
lean_object* v_res_4354_; 
v_res_4354_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
return v_res_4354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object* v_s_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v___x_4359_; uint8_t v___x_4360_; lean_object* v___x_4361_; 
v___x_4359_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4360_ = 0;
v___x_4361_ = l_Lean_Meta_Simp_Simprocs_add(v_s_4355_, v___x_4359_, v___x_4360_, v_a_4356_, v_a_4357_);
return v___x_4361_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object* v_s_4362_, lean_object* v_a_4363_, lean_object* v_a_4364_, lean_object* v_a_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_4362_, v_a_4363_, v_a_4364_);
lean_dec(v_a_4364_);
lean_dec_ref(v_a_4363_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object* v_e_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v___x_4377_; uint8_t v___x_4378_; 
lean_inc_ref(v_e_4367_);
v___x_4377_ = l_Lean_Expr_cleanupAnnotations(v_e_4367_);
v___x_4378_ = l_Lean_Expr_isApp(v___x_4377_);
if (v___x_4378_ == 0)
{
lean_dec_ref(v___x_4377_);
goto v___jp_4373_;
}
else
{
lean_object* v_arg_4379_; lean_object* v___x_4380_; lean_object* v___x_4381_; uint8_t v___x_4382_; 
v_arg_4379_ = lean_ctor_get(v___x_4377_, 1);
lean_inc_ref(v_arg_4379_);
v___x_4380_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4377_);
v___x_4381_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4382_ = l_Lean_Expr_isConstOf(v___x_4380_, v___x_4381_);
lean_dec_ref(v___x_4380_);
if (v___x_4382_ == 0)
{
lean_dec_ref(v_arg_4379_);
goto v___jp_4373_;
}
else
{
lean_object* v___x_4383_; lean_object* v___x_4384_; lean_object* v___x_4385_; lean_object* v___x_4386_; 
lean_dec_ref(v_e_4367_);
v___x_4383_ = l_Lean_Meta_Grind_markAsMatchCond(v_arg_4379_);
v___x_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4384_, 0, v___x_4383_);
v___x_4385_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4385_, 0, v___x_4384_);
v___x_4386_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4386_, 0, v___x_4385_);
return v___x_4386_;
}
}
v___jp_4373_:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4376_; 
v___x_4374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4374_, 0, v_e_4367_);
v___x_4375_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4375_, 0, v___x_4374_);
v___x_4376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4376_, 0, v___x_4375_);
return v___x_4376_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(lean_object* v_e_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_){
_start:
{
lean_object* v_res_4393_; 
v_res_4393_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(v_e_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
lean_dec(v___y_4391_);
lean_dec_ref(v___y_4390_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
return v_res_4393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1(lean_object* v_e_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_, lean_object* v___y_4398_){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4400_, 0, v_e_4394_);
v___x_4401_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4401_, 0, v___x_4400_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(lean_object* v_e_4402_, lean_object* v___y_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v_res_4408_; 
v_res_4408_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(v_e_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
lean_dec(v___y_4406_);
lean_dec_ref(v___y_4405_);
lean_dec(v___y_4404_);
lean_dec_ref(v___y_4403_);
return v_res_4408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(lean_object* v_x_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_){
_start:
{
lean_object* v___y_4417_; lean_object* v_fileName_4426_; lean_object* v_fileMap_4427_; lean_object* v_options_4428_; lean_object* v_currRecDepth_4429_; lean_object* v_maxRecDepth_4430_; lean_object* v_ref_4431_; lean_object* v_currNamespace_4432_; lean_object* v_openDecls_4433_; lean_object* v_initHeartbeats_4434_; lean_object* v_maxHeartbeats_4435_; lean_object* v_quotContext_4436_; lean_object* v_currMacroScope_4437_; uint8_t v_diag_4438_; lean_object* v_cancelTk_x3f_4439_; uint8_t v_suppressElabErrors_4440_; lean_object* v_inheritedTraceOptions_4441_; uint8_t v___x_4442_; 
v_fileName_4426_ = lean_ctor_get(v___y_4413_, 0);
lean_inc_ref(v_fileName_4426_);
v_fileMap_4427_ = lean_ctor_get(v___y_4413_, 1);
lean_inc_ref(v_fileMap_4427_);
v_options_4428_ = lean_ctor_get(v___y_4413_, 2);
lean_inc_ref(v_options_4428_);
v_currRecDepth_4429_ = lean_ctor_get(v___y_4413_, 3);
lean_inc(v_currRecDepth_4429_);
v_maxRecDepth_4430_ = lean_ctor_get(v___y_4413_, 4);
lean_inc(v_maxRecDepth_4430_);
v_ref_4431_ = lean_ctor_get(v___y_4413_, 5);
lean_inc(v_ref_4431_);
v_currNamespace_4432_ = lean_ctor_get(v___y_4413_, 6);
lean_inc(v_currNamespace_4432_);
v_openDecls_4433_ = lean_ctor_get(v___y_4413_, 7);
lean_inc(v_openDecls_4433_);
v_initHeartbeats_4434_ = lean_ctor_get(v___y_4413_, 8);
lean_inc(v_initHeartbeats_4434_);
v_maxHeartbeats_4435_ = lean_ctor_get(v___y_4413_, 9);
lean_inc(v_maxHeartbeats_4435_);
v_quotContext_4436_ = lean_ctor_get(v___y_4413_, 10);
lean_inc(v_quotContext_4436_);
v_currMacroScope_4437_ = lean_ctor_get(v___y_4413_, 11);
lean_inc(v_currMacroScope_4437_);
v_diag_4438_ = lean_ctor_get_uint8(v___y_4413_, sizeof(void*)*14);
v_cancelTk_x3f_4439_ = lean_ctor_get(v___y_4413_, 12);
lean_inc(v_cancelTk_x3f_4439_);
v_suppressElabErrors_4440_ = lean_ctor_get_uint8(v___y_4413_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4441_ = lean_ctor_get(v___y_4413_, 13);
lean_inc_ref(v_inheritedTraceOptions_4441_);
lean_dec_ref(v___y_4413_);
v___x_4442_ = lean_nat_dec_eq(v_currRecDepth_4429_, v_maxRecDepth_4430_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4443_ = lean_unsigned_to_nat(1u);
v___x_4444_ = lean_nat_add(v_currRecDepth_4429_, v___x_4443_);
lean_dec(v_currRecDepth_4429_);
v___x_4445_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4445_, 0, v_fileName_4426_);
lean_ctor_set(v___x_4445_, 1, v_fileMap_4427_);
lean_ctor_set(v___x_4445_, 2, v_options_4428_);
lean_ctor_set(v___x_4445_, 3, v___x_4444_);
lean_ctor_set(v___x_4445_, 4, v_maxRecDepth_4430_);
lean_ctor_set(v___x_4445_, 5, v_ref_4431_);
lean_ctor_set(v___x_4445_, 6, v_currNamespace_4432_);
lean_ctor_set(v___x_4445_, 7, v_openDecls_4433_);
lean_ctor_set(v___x_4445_, 8, v_initHeartbeats_4434_);
lean_ctor_set(v___x_4445_, 9, v_maxHeartbeats_4435_);
lean_ctor_set(v___x_4445_, 10, v_quotContext_4436_);
lean_ctor_set(v___x_4445_, 11, v_currMacroScope_4437_);
lean_ctor_set(v___x_4445_, 12, v_cancelTk_x3f_4439_);
lean_ctor_set(v___x_4445_, 13, v_inheritedTraceOptions_4441_);
lean_ctor_set_uint8(v___x_4445_, sizeof(void*)*14, v_diag_4438_);
lean_ctor_set_uint8(v___x_4445_, sizeof(void*)*14 + 1, v_suppressElabErrors_4440_);
lean_inc(v___y_4414_);
lean_inc(v___y_4412_);
lean_inc_ref(v___y_4411_);
lean_inc(v___y_4410_);
v___x_4446_ = lean_apply_6(v_x_4409_, v___y_4410_, v___y_4411_, v___y_4412_, v___x_4445_, v___y_4414_, lean_box(0));
v___y_4417_ = v___x_4446_;
goto v___jp_4416_;
}
else
{
lean_object* v___x_4447_; 
lean_dec_ref(v_inheritedTraceOptions_4441_);
lean_dec(v_cancelTk_x3f_4439_);
lean_dec(v_currMacroScope_4437_);
lean_dec(v_quotContext_4436_);
lean_dec(v_maxHeartbeats_4435_);
lean_dec(v_initHeartbeats_4434_);
lean_dec(v_openDecls_4433_);
lean_dec(v_currNamespace_4432_);
lean_dec(v_maxRecDepth_4430_);
lean_dec(v_currRecDepth_4429_);
lean_dec_ref(v_options_4428_);
lean_dec_ref(v_fileMap_4427_);
lean_dec_ref(v_fileName_4426_);
lean_dec_ref(v_x_4409_);
v___x_4447_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_4431_);
v___y_4417_ = v___x_4447_;
goto v___jp_4416_;
}
v___jp_4416_:
{
if (lean_obj_tag(v___y_4417_) == 0)
{
return v___y_4417_;
}
else
{
lean_object* v_a_4418_; lean_object* v___x_4420_; uint8_t v_isShared_4421_; uint8_t v_isSharedCheck_4425_; 
v_a_4418_ = lean_ctor_get(v___y_4417_, 0);
v_isSharedCheck_4425_ = !lean_is_exclusive(v___y_4417_);
if (v_isSharedCheck_4425_ == 0)
{
v___x_4420_ = v___y_4417_;
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
else
{
lean_inc(v_a_4418_);
lean_dec(v___y_4417_);
v___x_4420_ = lean_box(0);
v_isShared_4421_ = v_isSharedCheck_4425_;
goto v_resetjp_4419_;
}
v_resetjp_4419_:
{
lean_object* v___x_4423_; 
if (v_isShared_4421_ == 0)
{
v___x_4423_ = v___x_4420_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
v___x_4423_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
return v___x_4423_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec(v___y_4449_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(lean_object* v_pre_4456_, lean_object* v_post_4457_, size_t v_sz_4458_, size_t v_i_4459_, lean_object* v_bs_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_){
_start:
{
uint8_t v___x_4467_; 
v___x_4467_ = lean_usize_dec_lt(v_i_4459_, v_sz_4458_);
if (v___x_4467_ == 0)
{
lean_object* v___x_4468_; 
lean_dec_ref(v_post_4457_);
lean_dec_ref(v_pre_4456_);
v___x_4468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4468_, 0, v_bs_4460_);
return v___x_4468_;
}
else
{
lean_object* v_v_4469_; lean_object* v___x_4470_; 
v_v_4469_ = lean_array_uget_borrowed(v_bs_4460_, v_i_4459_);
lean_inc(v_v_4469_);
lean_inc_ref(v_post_4457_);
lean_inc_ref(v_pre_4456_);
v___x_4470_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4456_, v_post_4457_, v_v_4469_, v___y_4461_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
if (lean_obj_tag(v___x_4470_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4472_; lean_object* v_bs_x27_4473_; size_t v___x_4474_; size_t v___x_4475_; lean_object* v___x_4476_; 
v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
lean_inc(v_a_4471_);
lean_dec_ref(v___x_4470_);
v___x_4472_ = lean_unsigned_to_nat(0u);
v_bs_x27_4473_ = lean_array_uset(v_bs_4460_, v_i_4459_, v___x_4472_);
v___x_4474_ = ((size_t)1ULL);
v___x_4475_ = lean_usize_add(v_i_4459_, v___x_4474_);
v___x_4476_ = lean_array_uset(v_bs_x27_4473_, v_i_4459_, v_a_4471_);
v_i_4459_ = v___x_4475_;
v_bs_4460_ = v___x_4476_;
goto _start;
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_dec_ref(v_bs_4460_);
lean_dec_ref(v_post_4457_);
lean_dec_ref(v_pre_4456_);
v_a_4478_ = lean_ctor_get(v___x_4470_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4470_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4470_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4470_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(lean_object* v_pre_4486_, lean_object* v_post_4487_, lean_object* v_x_4488_, lean_object* v_x_4489_, lean_object* v_x_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
if (lean_obj_tag(v_x_4488_) == 5)
{
lean_object* v_fn_4497_; lean_object* v_arg_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_fn_4497_ = lean_ctor_get(v_x_4488_, 0);
lean_inc_ref(v_fn_4497_);
v_arg_4498_ = lean_ctor_get(v_x_4488_, 1);
lean_inc_ref(v_arg_4498_);
lean_dec_ref(v_x_4488_);
v___x_4499_ = lean_array_set(v_x_4489_, v_x_4490_, v_arg_4498_);
v___x_4500_ = lean_unsigned_to_nat(1u);
v___x_4501_ = lean_nat_sub(v_x_4490_, v___x_4500_);
lean_dec(v_x_4490_);
v_x_4488_ = v_fn_4497_;
v_x_4489_ = v___x_4499_;
v_x_4490_ = v___x_4501_;
goto _start;
}
else
{
lean_object* v___x_4503_; 
lean_dec(v_x_4490_);
lean_inc_ref(v_post_4487_);
lean_inc_ref(v_pre_4486_);
v___x_4503_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4486_, v_post_4487_, v_x_4488_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v_a_4504_; size_t v_sz_4505_; size_t v___x_4506_; lean_object* v___x_4507_; 
v_a_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc(v_a_4504_);
lean_dec_ref(v___x_4503_);
v_sz_4505_ = lean_array_size(v_x_4489_);
v___x_4506_ = ((size_t)0ULL);
lean_inc_ref(v_post_4487_);
lean_inc_ref(v_pre_4486_);
v___x_4507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_4486_, v_post_4487_, v_sz_4505_, v___x_4506_, v_x_4489_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
if (lean_obj_tag(v___x_4507_) == 0)
{
lean_object* v_a_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; 
v_a_4508_ = lean_ctor_get(v___x_4507_, 0);
lean_inc(v_a_4508_);
lean_dec_ref(v___x_4507_);
v___x_4509_ = l_Lean_mkAppN(v_a_4504_, v_a_4508_);
lean_dec(v_a_4508_);
v___x_4510_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4486_, v_post_4487_, v___x_4509_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
return v___x_4510_;
}
else
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4518_; 
lean_dec(v_a_4504_);
lean_dec_ref(v_post_4487_);
lean_dec_ref(v_pre_4486_);
v_a_4511_ = lean_ctor_get(v___x_4507_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4507_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4513_ = v___x_4507_;
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4507_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
if (v_isShared_4514_ == 0)
{
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_a_4511_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
else
{
lean_dec_ref(v_x_4489_);
lean_dec_ref(v_post_4487_);
lean_dec_ref(v_pre_4486_);
return v___x_4503_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(lean_object* v_pre_4519_, lean_object* v_e_4520_, lean_object* v_post_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_){
_start:
{
lean_object* v___y_4529_; lean_object* v___y_4530_; uint8_t v___y_4531_; lean_object* v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; uint8_t v___y_4536_; lean_object* v___y_4546_; uint8_t v___y_4547_; lean_object* v___y_4548_; lean_object* v___y_4549_; lean_object* v___y_4550_; uint8_t v___y_4551_; uint8_t v___y_4559_; lean_object* v___y_4560_; lean_object* v___y_4561_; lean_object* v___y_4562_; lean_object* v___y_4563_; uint8_t v___y_4564_; lean_object* v___x_4571_; 
lean_inc_ref(v_pre_4519_);
lean_inc(v___y_4526_);
lean_inc_ref(v___y_4525_);
lean_inc(v___y_4524_);
lean_inc_ref(v___y_4523_);
lean_inc_ref(v_e_4520_);
v___x_4571_ = lean_apply_6(v_pre_4519_, v_e_4520_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_, lean_box(0));
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4661_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4661_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4661_ == 0)
{
v___x_4574_ = v___x_4571_;
v_isShared_4575_ = v_isSharedCheck_4661_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4571_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4661_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___y_4577_; 
switch(lean_obj_tag(v_a_4572_))
{
case 0:
{
lean_object* v_e_4651_; lean_object* v___x_4653_; 
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_e_4520_);
lean_dec_ref(v_pre_4519_);
v_e_4651_ = lean_ctor_get(v_a_4572_, 0);
lean_inc_ref(v_e_4651_);
lean_dec_ref(v_a_4572_);
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 0, v_e_4651_);
v___x_4653_ = v___x_4574_;
goto v_reusejp_4652_;
}
else
{
lean_object* v_reuseFailAlloc_4654_; 
v_reuseFailAlloc_4654_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4654_, 0, v_e_4651_);
v___x_4653_ = v_reuseFailAlloc_4654_;
goto v_reusejp_4652_;
}
v_reusejp_4652_:
{
return v___x_4653_;
}
}
case 1:
{
lean_object* v_e_4655_; lean_object* v___x_4656_; 
lean_del_object(v___x_4574_);
lean_dec_ref(v_e_4520_);
v_e_4655_ = lean_ctor_get(v_a_4572_, 0);
lean_inc_ref(v_e_4655_);
lean_dec_ref(v_a_4572_);
lean_inc_ref(v_post_4521_);
lean_inc_ref(v_pre_4519_);
v___x_4656_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4519_, v_post_4521_, v_e_4655_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4656_) == 0)
{
lean_object* v_a_4657_; lean_object* v___x_4658_; 
v_a_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc(v_a_4657_);
lean_dec_ref(v___x_4656_);
v___x_4658_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v_a_4657_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4658_;
}
else
{
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_pre_4519_);
return v___x_4656_;
}
}
default: 
{
lean_object* v_e_x3f_4659_; 
lean_del_object(v___x_4574_);
v_e_x3f_4659_ = lean_ctor_get(v_a_4572_, 0);
lean_inc(v_e_x3f_4659_);
lean_dec_ref(v_a_4572_);
if (lean_obj_tag(v_e_x3f_4659_) == 0)
{
v___y_4577_ = v_e_4520_;
goto v___jp_4576_;
}
else
{
lean_object* v_val_4660_; 
lean_dec_ref(v_e_4520_);
v_val_4660_ = lean_ctor_get(v_e_x3f_4659_, 0);
lean_inc(v_val_4660_);
lean_dec_ref(v_e_x3f_4659_);
v___y_4577_ = v_val_4660_;
goto v___jp_4576_;
}
}
}
v___jp_4576_:
{
switch(lean_obj_tag(v___y_4577_))
{
case 7:
{
lean_object* v_binderName_4578_; lean_object* v_binderType_4579_; lean_object* v_body_4580_; uint8_t v_binderInfo_4581_; lean_object* v___x_4582_; 
v_binderName_4578_ = lean_ctor_get(v___y_4577_, 0);
lean_inc(v_binderName_4578_);
v_binderType_4579_ = lean_ctor_get(v___y_4577_, 1);
v_body_4580_ = lean_ctor_get(v___y_4577_, 2);
v_binderInfo_4581_ = lean_ctor_get_uint8(v___y_4577_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_4579_);
lean_inc_ref(v_post_4521_);
lean_inc_ref(v_pre_4519_);
v___x_4582_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4519_, v_post_4521_, v_binderType_4579_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4582_) == 0)
{
lean_object* v_a_4583_; lean_object* v___x_4584_; 
v_a_4583_ = lean_ctor_get(v___x_4582_, 0);
lean_inc(v_a_4583_);
lean_dec_ref(v___x_4582_);
lean_inc_ref(v_body_4580_);
lean_inc_ref(v_post_4521_);
lean_inc_ref(v_pre_4519_);
v___x_4584_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4519_, v_post_4521_, v_body_4580_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; size_t v___x_4586_; size_t v___x_4587_; uint8_t v___x_4588_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_a_4585_);
lean_dec_ref(v___x_4584_);
v___x_4586_ = lean_ptr_addr(v_binderType_4579_);
v___x_4587_ = lean_ptr_addr(v_a_4583_);
v___x_4588_ = lean_usize_dec_eq(v___x_4586_, v___x_4587_);
if (v___x_4588_ == 0)
{
v___y_4559_ = v_binderInfo_4581_;
v___y_4560_ = v_a_4585_;
v___y_4561_ = v_a_4583_;
v___y_4562_ = v_binderName_4578_;
v___y_4563_ = v___y_4577_;
v___y_4564_ = v___x_4588_;
goto v___jp_4558_;
}
else
{
size_t v___x_4589_; size_t v___x_4590_; uint8_t v___x_4591_; 
v___x_4589_ = lean_ptr_addr(v_body_4580_);
v___x_4590_ = lean_ptr_addr(v_a_4585_);
v___x_4591_ = lean_usize_dec_eq(v___x_4589_, v___x_4590_);
v___y_4559_ = v_binderInfo_4581_;
v___y_4560_ = v_a_4585_;
v___y_4561_ = v_a_4583_;
v___y_4562_ = v_binderName_4578_;
v___y_4563_ = v___y_4577_;
v___y_4564_ = v___x_4591_;
goto v___jp_4558_;
}
}
else
{
lean_dec(v_a_4583_);
lean_dec_ref(v___y_4577_);
lean_dec(v_binderName_4578_);
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_pre_4519_);
return v___x_4584_;
}
}
else
{
lean_dec(v_binderName_4578_);
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_pre_4519_);
return v___x_4582_;
}
}
case 6:
{
lean_object* v_binderName_4592_; lean_object* v_binderType_4593_; lean_object* v_body_4594_; uint8_t v_binderInfo_4595_; lean_object* v___x_4596_; 
v_binderName_4592_ = lean_ctor_get(v___y_4577_, 0);
lean_inc(v_binderName_4592_);
v_binderType_4593_ = lean_ctor_get(v___y_4577_, 1);
v_body_4594_ = lean_ctor_get(v___y_4577_, 2);
v_binderInfo_4595_ = lean_ctor_get_uint8(v___y_4577_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_4593_);
lean_inc_ref(v_post_4521_);
lean_inc_ref(v_pre_4519_);
v___x_4596_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4519_, v_post_4521_, v_binderType_4593_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4596_) == 0)
{
lean_object* v_a_4597_; lean_object* v___x_4598_; 
v_a_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc(v_a_4597_);
lean_dec_ref(v___x_4596_);
lean_inc_ref(v_body_4594_);
lean_inc_ref(v_post_4521_);
lean_inc_ref(v_pre_4519_);
v___x_4598_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4519_, v_post_4521_, v_body_4594_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; size_t v___x_4600_; size_t v___x_4601_; uint8_t v___x_4602_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
lean_inc(v_a_4599_);
lean_dec_ref(v___x_4598_);
v___x_4600_ = lean_ptr_addr(v_binderType_4593_);
v___x_4601_ = lean_ptr_addr(v_a_4597_);
v___x_4602_ = lean_usize_dec_eq(v___x_4600_, v___x_4601_);
if (v___x_4602_ == 0)
{
v___y_4546_ = v_a_4597_;
v___y_4547_ = v_binderInfo_4595_;
v___y_4548_ = v_binderName_4592_;
v___y_4549_ = v___y_4577_;
v___y_4550_ = v_a_4599_;
v___y_4551_ = v___x_4602_;
goto v___jp_4545_;
}
else
{
size_t v___x_4603_; size_t v___x_4604_; uint8_t v___x_4605_; 
v___x_4603_ = lean_ptr_addr(v_body_4594_);
v___x_4604_ = lean_ptr_addr(v_a_4599_);
v___x_4605_ = lean_usize_dec_eq(v___x_4603_, v___x_4604_);
v___y_4546_ = v_a_4597_;
v___y_4547_ = v_binderInfo_4595_;
v___y_4548_ = v_binderName_4592_;
v___y_4549_ = v___y_4577_;
v___y_4550_ = v_a_4599_;
v___y_4551_ = v___x_4605_;
goto v___jp_4545_;
}
}
else
{
lean_dec(v_a_4597_);
lean_dec(v_binderName_4592_);
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_pre_4519_);
return v___x_4598_;
}
}
else
{
lean_dec(v_binderName_4592_);
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_pre_4519_);
return v___x_4596_;
}
}
case 8:
{
lean_object* v_declName_4606_; lean_object* v_type_4607_; lean_object* v_value_4608_; lean_object* v_body_4609_; uint8_t v_nondep_4610_; lean_object* v___x_4611_; 
v_declName_4606_ = lean_ctor_get(v___y_4577_, 0);
lean_inc(v_declName_4606_);
v_type_4607_ = lean_ctor_get(v___y_4577_, 1);
v_value_4608_ = lean_ctor_get(v___y_4577_, 2);
v_body_4609_ = lean_ctor_get(v___y_4577_, 3);
lean_inc_ref(v_body_4609_);
v_nondep_4610_ = lean_ctor_get_uint8(v___y_4577_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_4607_);
lean_inc_ref(v_post_4521_);
lean_inc_ref(v_pre_4519_);
v___x_4611_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4519_, v_post_4521_, v_type_4607_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4613_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
lean_inc(v_a_4612_);
lean_dec_ref(v___x_4611_);
lean_inc_ref(v_value_4608_);
lean_inc_ref(v_post_4521_);
lean_inc_ref(v_pre_4519_);
v___x_4613_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4519_, v_post_4521_, v_value_4608_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4613_) == 0)
{
lean_object* v_a_4614_; lean_object* v___x_4615_; 
v_a_4614_ = lean_ctor_get(v___x_4613_, 0);
lean_inc(v_a_4614_);
lean_dec_ref(v___x_4613_);
lean_inc_ref(v_body_4609_);
lean_inc_ref(v_post_4521_);
lean_inc_ref(v_pre_4519_);
v___x_4615_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4519_, v_post_4521_, v_body_4609_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; size_t v___x_4617_; size_t v___x_4618_; uint8_t v___x_4619_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc(v_a_4616_);
lean_dec_ref(v___x_4615_);
v___x_4617_ = lean_ptr_addr(v_type_4607_);
v___x_4618_ = lean_ptr_addr(v_a_4612_);
v___x_4619_ = lean_usize_dec_eq(v___x_4617_, v___x_4618_);
if (v___x_4619_ == 0)
{
v___y_4529_ = v_a_4612_;
v___y_4530_ = v_body_4609_;
v___y_4531_ = v_nondep_4610_;
v___y_4532_ = v_a_4616_;
v___y_4533_ = v_declName_4606_;
v___y_4534_ = v_a_4614_;
v___y_4535_ = v___y_4577_;
v___y_4536_ = v___x_4619_;
goto v___jp_4528_;
}
else
{
size_t v___x_4620_; size_t v___x_4621_; uint8_t v___x_4622_; 
v___x_4620_ = lean_ptr_addr(v_value_4608_);
v___x_4621_ = lean_ptr_addr(v_a_4614_);
v___x_4622_ = lean_usize_dec_eq(v___x_4620_, v___x_4621_);
v___y_4529_ = v_a_4612_;
v___y_4530_ = v_body_4609_;
v___y_4531_ = v_nondep_4610_;
v___y_4532_ = v_a_4616_;
v___y_4533_ = v_declName_4606_;
v___y_4534_ = v_a_4614_;
v___y_4535_ = v___y_4577_;
v___y_4536_ = v___x_4622_;
goto v___jp_4528_;
}
}
else
{
lean_dec(v_a_4614_);
lean_dec(v_a_4612_);
lean_dec_ref(v_body_4609_);
lean_dec(v_declName_4606_);
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_pre_4519_);
return v___x_4615_;
}
}
else
{
lean_dec(v_a_4612_);
lean_dec_ref(v_body_4609_);
lean_dec(v_declName_4606_);
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_pre_4519_);
return v___x_4613_;
}
}
else
{
lean_dec_ref(v_body_4609_);
lean_dec(v_declName_4606_);
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_pre_4519_);
return v___x_4611_;
}
}
case 5:
{
lean_object* v_dummy_4623_; lean_object* v_nargs_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4627_; lean_object* v___x_4628_; 
v_dummy_4623_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_4624_ = l_Lean_Expr_getAppNumArgs(v___y_4577_);
lean_inc(v_nargs_4624_);
v___x_4625_ = lean_mk_array(v_nargs_4624_, v_dummy_4623_);
v___x_4626_ = lean_unsigned_to_nat(1u);
v___x_4627_ = lean_nat_sub(v_nargs_4624_, v___x_4626_);
lean_dec(v_nargs_4624_);
v___x_4628_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_4519_, v_post_4521_, v___y_4577_, v___x_4625_, v___x_4627_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4628_;
}
case 10:
{
lean_object* v_data_4629_; lean_object* v_expr_4630_; lean_object* v___x_4631_; 
v_data_4629_ = lean_ctor_get(v___y_4577_, 0);
v_expr_4630_ = lean_ctor_get(v___y_4577_, 1);
lean_inc_ref(v_expr_4630_);
lean_inc_ref(v_post_4521_);
lean_inc_ref(v_pre_4519_);
v___x_4631_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4519_, v_post_4521_, v_expr_4630_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4631_) == 0)
{
lean_object* v_a_4632_; size_t v___x_4633_; size_t v___x_4634_; uint8_t v___x_4635_; 
v_a_4632_ = lean_ctor_get(v___x_4631_, 0);
lean_inc(v_a_4632_);
lean_dec_ref(v___x_4631_);
v___x_4633_ = lean_ptr_addr(v_expr_4630_);
v___x_4634_ = lean_ptr_addr(v_a_4632_);
v___x_4635_ = lean_usize_dec_eq(v___x_4633_, v___x_4634_);
if (v___x_4635_ == 0)
{
lean_object* v___x_4636_; lean_object* v___x_4637_; 
lean_inc(v_data_4629_);
lean_dec_ref(v___y_4577_);
v___x_4636_ = l_Lean_Expr_mdata___override(v_data_4629_, v_a_4632_);
v___x_4637_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___x_4636_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4637_;
}
else
{
lean_object* v___x_4638_; 
lean_dec(v_a_4632_);
v___x_4638_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___y_4577_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4638_;
}
}
else
{
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_pre_4519_);
return v___x_4631_;
}
}
case 11:
{
lean_object* v_typeName_4639_; lean_object* v_idx_4640_; lean_object* v_struct_4641_; lean_object* v___x_4642_; 
v_typeName_4639_ = lean_ctor_get(v___y_4577_, 0);
v_idx_4640_ = lean_ctor_get(v___y_4577_, 1);
v_struct_4641_ = lean_ctor_get(v___y_4577_, 2);
lean_inc_ref(v_struct_4641_);
lean_inc_ref(v_post_4521_);
lean_inc_ref(v_pre_4519_);
v___x_4642_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4519_, v_post_4521_, v_struct_4641_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; size_t v___x_4644_; size_t v___x_4645_; uint8_t v___x_4646_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4643_);
lean_dec_ref(v___x_4642_);
v___x_4644_ = lean_ptr_addr(v_struct_4641_);
v___x_4645_ = lean_ptr_addr(v_a_4643_);
v___x_4646_ = lean_usize_dec_eq(v___x_4644_, v___x_4645_);
if (v___x_4646_ == 0)
{
lean_object* v___x_4647_; lean_object* v___x_4648_; 
lean_inc(v_idx_4640_);
lean_inc(v_typeName_4639_);
lean_dec_ref(v___y_4577_);
v___x_4647_ = l_Lean_Expr_proj___override(v_typeName_4639_, v_idx_4640_, v_a_4643_);
v___x_4648_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___x_4647_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4648_;
}
else
{
lean_object* v___x_4649_; 
lean_dec(v_a_4643_);
v___x_4649_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___y_4577_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4649_;
}
}
else
{
lean_dec_ref(v___y_4577_);
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_pre_4519_);
return v___x_4642_;
}
}
default: 
{
lean_object* v___x_4650_; 
v___x_4650_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___y_4577_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4650_;
}
}
}
}
}
else
{
lean_object* v_a_4662_; lean_object* v___x_4664_; uint8_t v_isShared_4665_; uint8_t v_isSharedCheck_4669_; 
lean_dec_ref(v_post_4521_);
lean_dec_ref(v_e_4520_);
lean_dec_ref(v_pre_4519_);
v_a_4662_ = lean_ctor_get(v___x_4571_, 0);
v_isSharedCheck_4669_ = !lean_is_exclusive(v___x_4571_);
if (v_isSharedCheck_4669_ == 0)
{
v___x_4664_ = v___x_4571_;
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
else
{
lean_inc(v_a_4662_);
lean_dec(v___x_4571_);
v___x_4664_ = lean_box(0);
v_isShared_4665_ = v_isSharedCheck_4669_;
goto v_resetjp_4663_;
}
v_resetjp_4663_:
{
lean_object* v___x_4667_; 
if (v_isShared_4665_ == 0)
{
v___x_4667_ = v___x_4664_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v_a_4662_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
v___jp_4528_:
{
if (v___y_4536_ == 0)
{
lean_object* v___x_4537_; lean_object* v___x_4538_; 
lean_dec_ref(v___y_4535_);
lean_dec_ref(v___y_4530_);
v___x_4537_ = l_Lean_Expr_letE___override(v___y_4533_, v___y_4529_, v___y_4534_, v___y_4532_, v___y_4531_);
v___x_4538_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___x_4537_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4538_;
}
else
{
size_t v___x_4539_; size_t v___x_4540_; uint8_t v___x_4541_; 
v___x_4539_ = lean_ptr_addr(v___y_4530_);
lean_dec_ref(v___y_4530_);
v___x_4540_ = lean_ptr_addr(v___y_4532_);
v___x_4541_ = lean_usize_dec_eq(v___x_4539_, v___x_4540_);
if (v___x_4541_ == 0)
{
lean_object* v___x_4542_; lean_object* v___x_4543_; 
lean_dec_ref(v___y_4535_);
v___x_4542_ = l_Lean_Expr_letE___override(v___y_4533_, v___y_4529_, v___y_4534_, v___y_4532_, v___y_4531_);
v___x_4543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___x_4542_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4543_;
}
else
{
lean_object* v___x_4544_; 
lean_dec_ref(v___y_4534_);
lean_dec(v___y_4533_);
lean_dec_ref(v___y_4532_);
lean_dec_ref(v___y_4529_);
v___x_4544_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___y_4535_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4544_;
}
}
}
v___jp_4545_:
{
if (v___y_4551_ == 0)
{
lean_object* v___x_4552_; lean_object* v___x_4553_; 
lean_dec_ref(v___y_4549_);
v___x_4552_ = l_Lean_Expr_lam___override(v___y_4548_, v___y_4546_, v___y_4550_, v___y_4547_);
v___x_4553_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___x_4552_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4553_;
}
else
{
uint8_t v___x_4554_; 
v___x_4554_ = l_Lean_instBEqBinderInfo_beq(v___y_4547_, v___y_4547_);
if (v___x_4554_ == 0)
{
lean_object* v___x_4555_; lean_object* v___x_4556_; 
lean_dec_ref(v___y_4549_);
v___x_4555_ = l_Lean_Expr_lam___override(v___y_4548_, v___y_4546_, v___y_4550_, v___y_4547_);
v___x_4556_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___x_4555_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4556_;
}
else
{
lean_object* v___x_4557_; 
lean_dec_ref(v___y_4550_);
lean_dec(v___y_4548_);
lean_dec_ref(v___y_4546_);
v___x_4557_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___y_4549_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4557_;
}
}
}
v___jp_4558_:
{
if (v___y_4564_ == 0)
{
lean_object* v___x_4565_; lean_object* v___x_4566_; 
lean_dec_ref(v___y_4563_);
v___x_4565_ = l_Lean_Expr_forallE___override(v___y_4562_, v___y_4561_, v___y_4560_, v___y_4559_);
v___x_4566_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___x_4565_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4566_;
}
else
{
uint8_t v___x_4567_; 
v___x_4567_ = l_Lean_instBEqBinderInfo_beq(v___y_4559_, v___y_4559_);
if (v___x_4567_ == 0)
{
lean_object* v___x_4568_; lean_object* v___x_4569_; 
lean_dec_ref(v___y_4563_);
v___x_4568_ = l_Lean_Expr_forallE___override(v___y_4562_, v___y_4561_, v___y_4560_, v___y_4559_);
v___x_4569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___x_4568_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4569_;
}
else
{
lean_object* v___x_4570_; 
lean_dec(v___y_4562_);
lean_dec_ref(v___y_4561_);
lean_dec_ref(v___y_4560_);
v___x_4570_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4519_, v_post_4521_, v___y_4563_, v___y_4522_, v___y_4523_, v___y_4524_, v___y_4525_, v___y_4526_);
return v___x_4570_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_4670_, lean_object* v_e_4671_, lean_object* v_post_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v_pre_4670_, v_e_4671_, v_post_4672_, v___y_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v___y_4673_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(lean_object* v_pre_4680_, lean_object* v_post_4681_, lean_object* v_e_4682_, lean_object* v_a_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_){
_start:
{
lean_object* v___x_4689_; lean_object* v___x_4690_; 
lean_inc(v_a_4683_);
v___x_4689_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4689_, 0, lean_box(0));
lean_closure_set(v___x_4689_, 1, lean_box(0));
lean_closure_set(v___x_4689_, 2, v_a_4683_);
v___x_4690_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_box(0), v___x_4689_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
if (lean_obj_tag(v___x_4690_) == 0)
{
lean_object* v_a_4691_; lean_object* v___x_4693_; uint8_t v_isShared_4694_; uint8_t v_isSharedCheck_4721_; 
v_a_4691_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4721_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4721_ == 0)
{
v___x_4693_ = v___x_4690_;
v_isShared_4694_ = v_isSharedCheck_4721_;
goto v_resetjp_4692_;
}
else
{
lean_inc(v_a_4691_);
lean_dec(v___x_4690_);
v___x_4693_ = lean_box(0);
v_isShared_4694_ = v_isSharedCheck_4721_;
goto v_resetjp_4692_;
}
v_resetjp_4692_:
{
lean_object* v___x_4695_; 
v___x_4695_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_4691_, v_e_4682_);
lean_dec(v_a_4691_);
if (lean_obj_tag(v___x_4695_) == 0)
{
lean_object* v___f_4696_; lean_object* v___x_4697_; 
lean_del_object(v___x_4693_);
lean_inc_ref(v_e_4682_);
v___f_4696_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4696_, 0, v_pre_4680_);
lean_closure_set(v___f_4696_, 1, v_e_4682_);
lean_closure_set(v___f_4696_, 2, v_post_4681_);
lean_inc_ref(v___y_4686_);
v___x_4697_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v___f_4696_, v_a_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
if (lean_obj_tag(v___x_4697_) == 0)
{
lean_object* v_a_4698_; lean_object* v___f_4699_; lean_object* v___x_4700_; 
v_a_4698_ = lean_ctor_get(v___x_4697_, 0);
lean_inc(v_a_4698_);
lean_dec_ref(v___x_4697_);
lean_inc(v_a_4698_);
lean_inc(v_a_4683_);
v___f_4699_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4699_, 0, v_a_4683_);
lean_closure_set(v___f_4699_, 1, v_e_4682_);
lean_closure_set(v___f_4699_, 2, v_a_4698_);
v___x_4700_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2_spec__3___lam__0(lean_box(0), v___f_4699_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v___x_4702_; uint8_t v_isShared_4703_; uint8_t v_isSharedCheck_4707_; 
v_isSharedCheck_4707_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4707_ == 0)
{
lean_object* v_unused_4708_; 
v_unused_4708_ = lean_ctor_get(v___x_4700_, 0);
lean_dec(v_unused_4708_);
v___x_4702_ = v___x_4700_;
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
else
{
lean_dec(v___x_4700_);
v___x_4702_ = lean_box(0);
v_isShared_4703_ = v_isSharedCheck_4707_;
goto v_resetjp_4701_;
}
v_resetjp_4701_:
{
lean_object* v___x_4705_; 
if (v_isShared_4703_ == 0)
{
lean_ctor_set(v___x_4702_, 0, v_a_4698_);
v___x_4705_ = v___x_4702_;
goto v_reusejp_4704_;
}
else
{
lean_object* v_reuseFailAlloc_4706_; 
v_reuseFailAlloc_4706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4706_, 0, v_a_4698_);
v___x_4705_ = v_reuseFailAlloc_4706_;
goto v_reusejp_4704_;
}
v_reusejp_4704_:
{
return v___x_4705_;
}
}
}
else
{
lean_object* v_a_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4716_; 
lean_dec(v_a_4698_);
v_a_4709_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4711_ = v___x_4700_;
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_a_4709_);
lean_dec(v___x_4700_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4716_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4714_; 
if (v_isShared_4712_ == 0)
{
v___x_4714_ = v___x_4711_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v_a_4709_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
else
{
lean_dec_ref(v_e_4682_);
return v___x_4697_;
}
}
else
{
lean_object* v_val_4717_; lean_object* v___x_4719_; 
lean_dec_ref(v_e_4682_);
lean_dec_ref(v_post_4681_);
lean_dec_ref(v_pre_4680_);
v_val_4717_ = lean_ctor_get(v___x_4695_, 0);
lean_inc(v_val_4717_);
lean_dec_ref(v___x_4695_);
if (v_isShared_4694_ == 0)
{
lean_ctor_set(v___x_4693_, 0, v_val_4717_);
v___x_4719_ = v___x_4693_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_val_4717_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
}
}
else
{
lean_object* v_a_4722_; lean_object* v___x_4724_; uint8_t v_isShared_4725_; uint8_t v_isSharedCheck_4729_; 
lean_dec_ref(v_e_4682_);
lean_dec_ref(v_post_4681_);
lean_dec_ref(v_pre_4680_);
v_a_4722_ = lean_ctor_get(v___x_4690_, 0);
v_isSharedCheck_4729_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4729_ == 0)
{
v___x_4724_ = v___x_4690_;
v_isShared_4725_ = v_isSharedCheck_4729_;
goto v_resetjp_4723_;
}
else
{
lean_inc(v_a_4722_);
lean_dec(v___x_4690_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(lean_object* v_pre_4730_, lean_object* v_post_4731_, lean_object* v_e_4732_, lean_object* v_a_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v___x_4739_; 
lean_inc_ref(v_post_4731_);
lean_inc(v___y_4737_);
lean_inc_ref(v___y_4736_);
lean_inc(v___y_4735_);
lean_inc_ref(v___y_4734_);
lean_inc_ref(v_e_4732_);
v___x_4739_ = lean_apply_6(v_post_4731_, v_e_4732_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_, lean_box(0));
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4758_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4758_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4758_ == 0)
{
v___x_4742_ = v___x_4739_;
v_isShared_4743_ = v_isSharedCheck_4758_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4739_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4758_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
switch(lean_obj_tag(v_a_4740_))
{
case 0:
{
lean_object* v_e_4744_; lean_object* v___x_4746_; 
lean_dec_ref(v_e_4732_);
lean_dec_ref(v_post_4731_);
lean_dec_ref(v_pre_4730_);
v_e_4744_ = lean_ctor_get(v_a_4740_, 0);
lean_inc_ref(v_e_4744_);
lean_dec_ref(v_a_4740_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v_e_4744_);
v___x_4746_ = v___x_4742_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_e_4744_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
case 1:
{
lean_object* v_e_4748_; lean_object* v___x_4749_; 
lean_del_object(v___x_4742_);
lean_dec_ref(v_e_4732_);
v_e_4748_ = lean_ctor_get(v_a_4740_, 0);
lean_inc_ref(v_e_4748_);
lean_dec_ref(v_a_4740_);
v___x_4749_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4730_, v_post_4731_, v_e_4748_, v_a_4733_, v___y_4734_, v___y_4735_, v___y_4736_, v___y_4737_);
return v___x_4749_;
}
default: 
{
lean_object* v_e_x3f_4750_; 
lean_dec_ref(v_post_4731_);
lean_dec_ref(v_pre_4730_);
v_e_x3f_4750_ = lean_ctor_get(v_a_4740_, 0);
lean_inc(v_e_x3f_4750_);
lean_dec_ref(v_a_4740_);
if (lean_obj_tag(v_e_x3f_4750_) == 0)
{
lean_object* v___x_4752_; 
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v_e_4732_);
v___x_4752_ = v___x_4742_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_e_4732_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
else
{
lean_object* v_val_4754_; lean_object* v___x_4756_; 
lean_dec_ref(v_e_4732_);
v_val_4754_ = lean_ctor_get(v_e_x3f_4750_, 0);
lean_inc(v_val_4754_);
lean_dec_ref(v_e_x3f_4750_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v_val_4754_);
v___x_4756_ = v___x_4742_;
goto v_reusejp_4755_;
}
else
{
lean_object* v_reuseFailAlloc_4757_; 
v_reuseFailAlloc_4757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4757_, 0, v_val_4754_);
v___x_4756_ = v_reuseFailAlloc_4757_;
goto v_reusejp_4755_;
}
v_reusejp_4755_:
{
return v___x_4756_;
}
}
}
}
}
}
else
{
lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
lean_dec_ref(v_e_4732_);
lean_dec_ref(v_post_4731_);
lean_dec_ref(v_pre_4730_);
v_a_4759_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4739_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4739_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_4767_, lean_object* v_post_4768_, lean_object* v_e_4769_, lean_object* v_a_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_){
_start:
{
lean_object* v_res_4776_; 
v_res_4776_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4767_, v_post_4768_, v_e_4769_, v_a_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
lean_dec(v_a_4770_);
return v_res_4776_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_4777_, lean_object* v_post_4778_, lean_object* v_sz_4779_, lean_object* v_i_4780_, lean_object* v_bs_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
size_t v_sz_boxed_4788_; size_t v_i_boxed_4789_; lean_object* v_res_4790_; 
v_sz_boxed_4788_ = lean_unbox_usize(v_sz_4779_);
lean_dec(v_sz_4779_);
v_i_boxed_4789_ = lean_unbox_usize(v_i_4780_);
lean_dec(v_i_4780_);
v_res_4790_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_4777_, v_post_4778_, v_sz_boxed_4788_, v_i_boxed_4789_, v_bs_4781_, v___y_4782_, v___y_4783_, v___y_4784_, v___y_4785_, v___y_4786_);
lean_dec(v___y_4786_);
lean_dec_ref(v___y_4785_);
lean_dec(v___y_4784_);
lean_dec_ref(v___y_4783_);
lean_dec(v___y_4782_);
return v_res_4790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_4791_, lean_object* v_post_4792_, lean_object* v_x_4793_, lean_object* v_x_4794_, lean_object* v_x_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_4791_, v_post_4792_, v_x_4793_, v_x_4794_, v_x_4795_, v___y_4796_, v___y_4797_, v___y_4798_, v___y_4799_, v___y_4800_);
lean_dec(v___y_4800_);
lean_dec_ref(v___y_4799_);
lean_dec(v___y_4798_);
lean_dec_ref(v___y_4797_);
lean_dec(v___y_4796_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(lean_object* v_pre_4803_, lean_object* v_post_4804_, lean_object* v_e_4805_, lean_object* v_a_4806_, lean_object* v___y_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_){
_start:
{
lean_object* v_res_4812_; 
v_res_4812_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4803_, v_post_4804_, v_e_4805_, v_a_4806_, v___y_4807_, v___y_4808_, v___y_4809_, v___y_4810_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
lean_dec(v___y_4808_);
lean_dec_ref(v___y_4807_);
lean_dec(v_a_4806_);
return v_res_4812_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(lean_object* v_input_4813_, lean_object* v_pre_4814_, lean_object* v_post_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_){
_start:
{
lean_object* v___x_4821_; lean_object* v___x_4822_; lean_object* v_a_4823_; lean_object* v___x_4824_; 
v___x_4821_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_4822_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_box(0), v___x_4821_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_);
v_a_4823_ = lean_ctor_get(v___x_4822_, 0);
lean_inc(v_a_4823_);
lean_dec_ref(v___x_4822_);
v___x_4824_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4814_, v_post_4815_, v_input_4813_, v_a_4823_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_);
if (lean_obj_tag(v___x_4824_) == 0)
{
lean_object* v_a_4825_; lean_object* v___x_4826_; lean_object* v___x_4827_; lean_object* v___x_4829_; uint8_t v_isShared_4830_; uint8_t v_isSharedCheck_4834_; 
v_a_4825_ = lean_ctor_get(v___x_4824_, 0);
lean_inc(v_a_4825_);
lean_dec_ref(v___x_4824_);
v___x_4826_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4826_, 0, lean_box(0));
lean_closure_set(v___x_4826_, 1, lean_box(0));
lean_closure_set(v___x_4826_, 2, v_a_4823_);
v___x_4827_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__2___lam__0(lean_box(0), v___x_4826_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_);
v_isSharedCheck_4834_ = !lean_is_exclusive(v___x_4827_);
if (v_isSharedCheck_4834_ == 0)
{
lean_object* v_unused_4835_; 
v_unused_4835_ = lean_ctor_get(v___x_4827_, 0);
lean_dec(v_unused_4835_);
v___x_4829_ = v___x_4827_;
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
else
{
lean_dec(v___x_4827_);
v___x_4829_ = lean_box(0);
v_isShared_4830_ = v_isSharedCheck_4834_;
goto v_resetjp_4828_;
}
v_resetjp_4828_:
{
lean_object* v___x_4832_; 
if (v_isShared_4830_ == 0)
{
lean_ctor_set(v___x_4829_, 0, v_a_4825_);
v___x_4832_ = v___x_4829_;
goto v_reusejp_4831_;
}
else
{
lean_object* v_reuseFailAlloc_4833_; 
v_reuseFailAlloc_4833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4833_, 0, v_a_4825_);
v___x_4832_ = v_reuseFailAlloc_4833_;
goto v_reusejp_4831_;
}
v_reusejp_4831_:
{
return v___x_4832_;
}
}
}
else
{
lean_dec(v_a_4823_);
return v___x_4824_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___boxed(lean_object* v_input_4836_, lean_object* v_pre_4837_, lean_object* v_post_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_, lean_object* v___y_4842_, lean_object* v___y_4843_){
_start:
{
lean_object* v_res_4844_; 
v_res_4844_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_input_4836_, v_pre_4837_, v_post_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_);
lean_dec(v___y_4842_);
lean_dec_ref(v___y_4841_);
lean_dec(v___y_4840_);
lean_dec_ref(v___y_4839_);
return v_res_4844_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object* v_e_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_, lean_object* v_a_4851_, lean_object* v_a_4852_){
_start:
{
lean_object* v___x_4854_; lean_object* v___x_4855_; 
v___x_4854_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__0));
v___x_4855_ = lean_find_expr(v___x_4854_, v_e_4848_);
if (lean_obj_tag(v___x_4855_) == 0)
{
uint8_t v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4856_ = 1;
v___x_4857_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4857_, 0, v_e_4848_);
lean_ctor_set(v___x_4857_, 1, v___x_4855_);
lean_ctor_set_uint8(v___x_4857_, sizeof(void*)*2, v___x_4856_);
v___x_4858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4858_, 0, v___x_4857_);
return v___x_4858_;
}
else
{
lean_object* v___x_4860_; uint8_t v_isShared_4861_; uint8_t v_isSharedCheck_4907_; 
v_isSharedCheck_4907_ = !lean_is_exclusive(v___x_4855_);
if (v_isSharedCheck_4907_ == 0)
{
lean_object* v_unused_4908_; 
v_unused_4908_ = lean_ctor_get(v___x_4855_, 0);
lean_dec(v_unused_4908_);
v___x_4860_ = v___x_4855_;
v_isShared_4861_ = v_isSharedCheck_4907_;
goto v_resetjp_4859_;
}
else
{
lean_dec(v___x_4855_);
v___x_4860_ = lean_box(0);
v_isShared_4861_ = v_isSharedCheck_4907_;
goto v_resetjp_4859_;
}
v_resetjp_4859_:
{
lean_object* v_pre_4862_; lean_object* v___f_4863_; lean_object* v___x_4864_; 
v_pre_4862_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__1));
v___f_4863_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__2));
lean_inc_ref(v_e_4848_);
v___x_4864_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_e_4848_, v_pre_4862_, v___f_4863_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
if (lean_obj_tag(v___x_4864_) == 0)
{
lean_object* v_a_4865_; lean_object* v___x_4866_; 
v_a_4865_ = lean_ctor_get(v___x_4864_, 0);
lean_inc(v_a_4865_);
lean_dec_ref(v___x_4864_);
lean_inc(v_a_4865_);
v___x_4866_ = l_Lean_Meta_mkEqRefl(v_a_4865_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
if (lean_obj_tag(v___x_4866_) == 0)
{
lean_object* v_a_4867_; lean_object* v___x_4868_; 
v_a_4867_ = lean_ctor_get(v___x_4866_, 0);
lean_inc(v_a_4867_);
lean_dec_ref(v___x_4866_);
lean_inc(v_a_4865_);
v___x_4868_ = l_Lean_Meta_mkEq(v_e_4848_, v_a_4865_, v_a_4849_, v_a_4850_, v_a_4851_, v_a_4852_);
if (lean_obj_tag(v___x_4868_) == 0)
{
lean_object* v_a_4869_; lean_object* v___x_4871_; uint8_t v_isShared_4872_; uint8_t v_isSharedCheck_4882_; 
v_a_4869_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4871_ = v___x_4868_;
v_isShared_4872_ = v_isSharedCheck_4882_;
goto v_resetjp_4870_;
}
else
{
lean_inc(v_a_4869_);
lean_dec(v___x_4868_);
v___x_4871_ = lean_box(0);
v_isShared_4872_ = v_isSharedCheck_4882_;
goto v_resetjp_4870_;
}
v_resetjp_4870_:
{
uint8_t v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4876_; 
v___x_4873_ = 1;
v___x_4874_ = l_Lean_Meta_mkExpectedPropHint(v_a_4867_, v_a_4869_);
if (v_isShared_4861_ == 0)
{
lean_ctor_set(v___x_4860_, 0, v___x_4874_);
v___x_4876_ = v___x_4860_;
goto v_reusejp_4875_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___x_4874_);
v___x_4876_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4875_;
}
v_reusejp_4875_:
{
lean_object* v___x_4877_; lean_object* v___x_4879_; 
v___x_4877_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4877_, 0, v_a_4865_);
lean_ctor_set(v___x_4877_, 1, v___x_4876_);
lean_ctor_set_uint8(v___x_4877_, sizeof(void*)*2, v___x_4873_);
if (v_isShared_4872_ == 0)
{
lean_ctor_set(v___x_4871_, 0, v___x_4877_);
v___x_4879_ = v___x_4871_;
goto v_reusejp_4878_;
}
else
{
lean_object* v_reuseFailAlloc_4880_; 
v_reuseFailAlloc_4880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4880_, 0, v___x_4877_);
v___x_4879_ = v_reuseFailAlloc_4880_;
goto v_reusejp_4878_;
}
v_reusejp_4878_:
{
return v___x_4879_;
}
}
}
}
else
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4890_; 
lean_dec(v_a_4867_);
lean_dec(v_a_4865_);
lean_del_object(v___x_4860_);
v_a_4883_ = lean_ctor_get(v___x_4868_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4868_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4885_ = v___x_4868_;
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4868_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4888_; 
if (v_isShared_4886_ == 0)
{
v___x_4888_ = v___x_4885_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_a_4883_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4898_; 
lean_dec(v_a_4865_);
lean_del_object(v___x_4860_);
lean_dec_ref(v_e_4848_);
v_a_4891_ = lean_ctor_get(v___x_4866_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4866_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4893_ = v___x_4866_;
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4866_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
else
{
lean_object* v_a_4899_; lean_object* v___x_4901_; uint8_t v_isShared_4902_; uint8_t v_isSharedCheck_4906_; 
lean_del_object(v___x_4860_);
lean_dec_ref(v_e_4848_);
v_a_4899_ = lean_ctor_get(v___x_4864_, 0);
v_isSharedCheck_4906_ = !lean_is_exclusive(v___x_4864_);
if (v_isSharedCheck_4906_ == 0)
{
v___x_4901_ = v___x_4864_;
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
else
{
lean_inc(v_a_4899_);
lean_dec(v___x_4864_);
v___x_4901_ = lean_box(0);
v_isShared_4902_ = v_isSharedCheck_4906_;
goto v_resetjp_4900_;
}
v_resetjp_4900_:
{
lean_object* v___x_4904_; 
if (v_isShared_4902_ == 0)
{
v___x_4904_ = v___x_4901_;
goto v_reusejp_4903_;
}
else
{
lean_object* v_reuseFailAlloc_4905_; 
v_reuseFailAlloc_4905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4905_, 0, v_a_4899_);
v___x_4904_ = v_reuseFailAlloc_4905_;
goto v_reusejp_4903_;
}
v_reusejp_4903_:
{
return v___x_4904_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___boxed(lean_object* v_e_4909_, lean_object* v_a_4910_, lean_object* v_a_4911_, lean_object* v_a_4912_, lean_object* v_a_4913_, lean_object* v_a_4914_){
_start:
{
lean_object* v_res_4915_; 
v_res_4915_ = l_Lean_Meta_Grind_replacePreMatchCond(v_e_4909_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_);
lean_dec(v_a_4913_);
lean_dec_ref(v_a_4912_);
lean_dec(v_a_4911_);
lean_dec_ref(v_a_4910_);
return v_res_4915_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4916_, lean_object* v_x_4917_, lean_object* v___y_4918_, lean_object* v___y_4919_, lean_object* v___y_4920_, lean_object* v___y_4921_, lean_object* v___y_4922_){
_start:
{
lean_object* v___x_4924_; 
lean_inc_ref(v___y_4921_);
v___x_4924_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_4917_, v___y_4918_, v___y_4919_, v___y_4920_, v___y_4921_, v___y_4922_);
return v___x_4924_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4925_, lean_object* v_x_4926_, lean_object* v___y_4927_, lean_object* v___y_4928_, lean_object* v___y_4929_, lean_object* v___y_4930_, lean_object* v___y_4931_, lean_object* v___y_4932_){
_start:
{
lean_object* v_res_4933_; 
v_res_4933_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(v_00_u03b1_4925_, v_x_4926_, v___y_4927_, v___y_4928_, v___y_4929_, v___y_4930_, v___y_4931_);
lean_dec(v___y_4931_);
lean_dec_ref(v___y_4930_);
lean_dec(v___y_4929_);
lean_dec_ref(v___y_4928_);
lean_dec(v___y_4927_);
return v_res_4933_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isIte(lean_object* v_e_4937_){
_start:
{
lean_object* v___x_4938_; uint8_t v___x_4939_; 
v___x_4938_ = ((lean_object*)(l_Lean_Meta_Grind_isIte___closed__1));
v___x_4939_ = l_Lean_Expr_isAppOf(v_e_4937_, v___x_4938_);
if (v___x_4939_ == 0)
{
return v___x_4939_;
}
else
{
lean_object* v___x_4940_; lean_object* v___x_4941_; uint8_t v___x_4942_; 
v___x_4940_ = lean_unsigned_to_nat(5u);
v___x_4941_ = l_Lean_Expr_getAppNumArgs(v_e_4937_);
v___x_4942_ = lean_nat_dec_le(v___x_4940_, v___x_4941_);
lean_dec(v___x_4941_);
return v___x_4942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object* v_e_4943_){
_start:
{
uint8_t v_res_4944_; lean_object* v_r_4945_; 
v_res_4944_ = l_Lean_Meta_Grind_isIte(v_e_4943_);
lean_dec_ref(v_e_4943_);
v_r_4945_ = lean_box(v_res_4944_);
return v_r_4945_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isDIte(lean_object* v_e_4949_){
_start:
{
lean_object* v___x_4950_; uint8_t v___x_4951_; 
v___x_4950_ = ((lean_object*)(l_Lean_Meta_Grind_isDIte___closed__1));
v___x_4951_ = l_Lean_Expr_isAppOf(v_e_4949_, v___x_4950_);
if (v___x_4951_ == 0)
{
return v___x_4951_;
}
else
{
lean_object* v___x_4952_; lean_object* v___x_4953_; uint8_t v___x_4954_; 
v___x_4952_ = lean_unsigned_to_nat(5u);
v___x_4953_ = l_Lean_Expr_getAppNumArgs(v_e_4949_);
v___x_4954_ = lean_nat_dec_le(v___x_4952_, v___x_4953_);
lean_dec(v___x_4953_);
return v___x_4954_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object* v_e_4955_){
_start:
{
uint8_t v_res_4956_; lean_object* v_r_4957_; 
v_res_4956_ = l_Lean_Meta_Grind_isDIte(v_e_4955_);
lean_dec_ref(v_e_4955_);
v_r_4957_ = lean_box(v_res_4956_);
return v_r_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object* v_e_4958_){
_start:
{
uint8_t v___x_4959_; 
v___x_4959_ = l_Lean_Expr_isApp(v_e_4958_);
if (v___x_4959_ == 0)
{
lean_object* v___x_4960_; 
v___x_4960_ = lean_box(0);
return v___x_4960_;
}
else
{
lean_object* v_f_4961_; uint8_t v___x_4962_; 
v_f_4961_ = l_Lean_Expr_appFn_x21(v_e_4958_);
v___x_4962_ = l_Lean_Expr_isApp(v_f_4961_);
if (v___x_4962_ == 0)
{
lean_object* v___x_4963_; 
lean_dec_ref(v_f_4961_);
v___x_4963_ = lean_box(0);
return v___x_4963_;
}
else
{
lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4964_ = l_Lean_Expr_appFn_x21(v_f_4961_);
lean_dec_ref(v_f_4961_);
v___x_4965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4965_, 0, v___x_4964_);
return v___x_4965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object* v_e_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l_Lean_Meta_Grind_getBinOp(v_e_4966_);
lean_dec_ref(v_e_4966_);
return v_res_4967_;
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
