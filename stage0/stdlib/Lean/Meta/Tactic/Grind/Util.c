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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_1357__overap_153_ = lean_panic_fn_borrowed(v___x_152_, v_msg_96_);
lean_dec(v___x_152_);
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
lean_inc_n(v_a_792_, 2);
lean_dec_ref(v___x_791_);
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
lean_inc_n(v_a_1084_, 2);
lean_dec_ref(v___x_1083_);
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
lean_inc_n(v_a_1205_, 2);
lean_dec_ref(v___x_1204_);
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
lean_inc_n(v_a_1364_, 2);
lean_dec_ref(v___x_1363_);
v___x_1365_ = lean_obj_once(&l_Lean_MVarId_byContra_x3f___lam__0___closed__6, &l_Lean_MVarId_byContra_x3f___lam__0___closed__6_once, _init_l_Lean_MVarId_byContra_x3f___lam__0___closed__6);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(lean_object* v_init_1610_, lean_object* v_n_1611_, lean_object* v_b_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_){
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
v___x_1626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1610_, v_cs_1618_, v_sz_1624_, v___x_1625_, v___x_1623_, v___y_1613_, v___y_1614_, v___y_1615_, v___y_1616_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(lean_object* v_init_1688_, lean_object* v_as_1689_, size_t v_sz_1690_, size_t v_i_1691_, lean_object* v_b_1692_, lean_object* v___y_1693_, lean_object* v___y_1694_, lean_object* v___y_1695_, lean_object* v___y_1696_){
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
v___x_1705_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1688_, v_a_1704_, v_snd_1700_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1___boxed(lean_object* v_init_1736_, lean_object* v_as_1737_, lean_object* v_sz_1738_, lean_object* v_i_1739_, lean_object* v_b_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_, lean_object* v___y_1745_){
_start:
{
size_t v_sz_boxed_1746_; size_t v_i_boxed_1747_; lean_object* v_res_1748_; 
v_sz_boxed_1746_ = lean_unbox_usize(v_sz_1738_);
lean_dec(v_sz_1738_);
v_i_boxed_1747_ = lean_unbox_usize(v_i_1739_);
lean_dec(v_i_1739_);
v_res_1748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0_spec__1(v_init_1736_, v_as_1737_, v_sz_boxed_1746_, v_i_boxed_1747_, v_b_1740_, v___y_1741_, v___y_1742_, v___y_1743_, v___y_1744_);
lean_dec(v___y_1744_);
lean_dec_ref(v___y_1743_);
lean_dec(v___y_1742_);
lean_dec_ref(v___y_1741_);
lean_dec_ref(v_as_1737_);
lean_dec(v_init_1736_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0___boxed(lean_object* v_init_1749_, lean_object* v_n_1750_, lean_object* v_b_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_){
_start:
{
lean_object* v_res_1757_; 
v_res_1757_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_clearImplDetails_spec__0_spec__0(v_init_1749_, v_n_1750_, v_b_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_);
lean_dec(v___y_1755_);
lean_dec_ref(v___y_1754_);
lean_dec(v___y_1753_);
lean_dec_ref(v___y_1752_);
lean_dec(v_init_1749_);
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
v___x_2169_ = lean_nat_dec_eq(v_currRecDepth_2156_, v_maxRecDepth_2157_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2170_ = lean_unsigned_to_nat(1u);
v___x_2171_ = lean_nat_add(v_currRecDepth_2156_, v___x_2170_);
lean_inc_ref(v_inheritedTraceOptions_2168_);
lean_inc(v_cancelTk_x3f_2166_);
lean_inc(v_currMacroScope_2164_);
lean_inc(v_quotContext_2163_);
lean_inc(v_maxHeartbeats_2162_);
lean_inc(v_initHeartbeats_2161_);
lean_inc(v_openDecls_2160_);
lean_inc(v_currNamespace_2159_);
lean_inc(v_ref_2158_);
lean_inc(v_maxRecDepth_2157_);
lean_inc_ref(v_options_2155_);
lean_inc_ref(v_fileMap_2154_);
lean_inc_ref(v_fileName_2153_);
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
lean_dec_ref(v_x_2138_);
lean_inc(v_ref_2158_);
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
lean_dec_ref(v___y_2177_);
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
v___x_2552_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5___redArg(v___f_2551_, v_a_2540_, v___y_2541_, v___y_2542_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___f_2554_; lean_object* v___x_2555_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc_n(v_a_2553_, 2);
lean_dec_ref(v___x_2552_);
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0_spec__0(lean_object* v_msgData_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_){
_start:
{
lean_object* v___x_2791_; lean_object* v_env_2792_; lean_object* v___x_2793_; lean_object* v_mctx_2794_; lean_object* v_lctx_2795_; lean_object* v_options_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2791_ = lean_st_ref_get(v___y_2789_);
v_env_2792_ = lean_ctor_get(v___x_2791_, 0);
lean_inc_ref(v_env_2792_);
lean_dec(v___x_2791_);
v___x_2793_ = lean_st_ref_get(v___y_2787_);
v_mctx_2794_ = lean_ctor_get(v___x_2793_, 0);
lean_inc_ref(v_mctx_2794_);
lean_dec(v___x_2793_);
v_lctx_2795_ = lean_ctor_get(v___y_2786_, 2);
v_options_2796_ = lean_ctor_get(v___y_2788_, 2);
lean_inc_ref(v_options_2796_);
lean_inc_ref(v_lctx_2795_);
v___x_2797_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2797_, 0, v_env_2792_);
lean_ctor_set(v___x_2797_, 1, v_mctx_2794_);
lean_ctor_set(v___x_2797_, 2, v_lctx_2795_);
lean_ctor_set(v___x_2797_, 3, v_options_2796_);
v___x_2798_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
lean_ctor_set(v___x_2798_, 1, v_msgData_2785_);
v___x_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2799_, 0, v___x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0_spec__0___boxed(lean_object* v_msgData_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_){
_start:
{
lean_object* v_res_2806_; 
v_res_2806_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0_spec__0(v_msgData_2800_, v___y_2801_, v___y_2802_, v___y_2803_, v___y_2804_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
return v_res_2806_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2807_; double v___x_2808_; 
v___x_2807_ = lean_unsigned_to_nat(0u);
v___x_2808_ = lean_float_of_nat(v___x_2807_);
return v___x_2808_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0(lean_object* v_cls_2812_, lean_object* v_msg_2813_, lean_object* v___y_2814_, lean_object* v___y_2815_, lean_object* v___y_2816_, lean_object* v___y_2817_){
_start:
{
lean_object* v_ref_2819_; lean_object* v___x_2820_; lean_object* v_a_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2865_; 
v_ref_2819_ = lean_ctor_get(v___y_2816_, 5);
v___x_2820_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0_spec__0(v_msg_2813_, v___y_2814_, v___y_2815_, v___y_2816_, v___y_2817_);
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2823_ = v___x_2820_;
v_isShared_2824_ = v_isSharedCheck_2865_;
goto v_resetjp_2822_;
}
else
{
lean_inc(v_a_2821_);
lean_dec(v___x_2820_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2865_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v_traceState_2826_; lean_object* v_env_2827_; lean_object* v_nextMacroScope_2828_; lean_object* v_ngen_2829_; lean_object* v_auxDeclNGen_2830_; lean_object* v_cache_2831_; lean_object* v_messages_2832_; lean_object* v_infoState_2833_; lean_object* v_snapshotTasks_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2864_; 
v___x_2825_ = lean_st_ref_take(v___y_2817_);
v_traceState_2826_ = lean_ctor_get(v___x_2825_, 4);
v_env_2827_ = lean_ctor_get(v___x_2825_, 0);
v_nextMacroScope_2828_ = lean_ctor_get(v___x_2825_, 1);
v_ngen_2829_ = lean_ctor_get(v___x_2825_, 2);
v_auxDeclNGen_2830_ = lean_ctor_get(v___x_2825_, 3);
v_cache_2831_ = lean_ctor_get(v___x_2825_, 5);
v_messages_2832_ = lean_ctor_get(v___x_2825_, 6);
v_infoState_2833_ = lean_ctor_get(v___x_2825_, 7);
v_snapshotTasks_2834_ = lean_ctor_get(v___x_2825_, 8);
v_isSharedCheck_2864_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2864_ == 0)
{
v___x_2836_ = v___x_2825_;
v_isShared_2837_ = v_isSharedCheck_2864_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_snapshotTasks_2834_);
lean_inc(v_infoState_2833_);
lean_inc(v_messages_2832_);
lean_inc(v_cache_2831_);
lean_inc(v_traceState_2826_);
lean_inc(v_auxDeclNGen_2830_);
lean_inc(v_ngen_2829_);
lean_inc(v_nextMacroScope_2828_);
lean_inc(v_env_2827_);
lean_dec(v___x_2825_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2864_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
uint64_t v_tid_2838_; lean_object* v_traces_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2863_; 
v_tid_2838_ = lean_ctor_get_uint64(v_traceState_2826_, sizeof(void*)*1);
v_traces_2839_ = lean_ctor_get(v_traceState_2826_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v_traceState_2826_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2841_ = v_traceState_2826_;
v_isShared_2842_ = v_isSharedCheck_2863_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_traces_2839_);
lean_dec(v_traceState_2826_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2863_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2843_; double v___x_2844_; uint8_t v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2853_; 
v___x_2843_ = lean_box(0);
v___x_2844_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__0);
v___x_2845_ = 0;
v___x_2846_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__1));
v___x_2847_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2847_, 0, v_cls_2812_);
lean_ctor_set(v___x_2847_, 1, v___x_2843_);
lean_ctor_set(v___x_2847_, 2, v___x_2846_);
lean_ctor_set_float(v___x_2847_, sizeof(void*)*3, v___x_2844_);
lean_ctor_set_float(v___x_2847_, sizeof(void*)*3 + 8, v___x_2844_);
lean_ctor_set_uint8(v___x_2847_, sizeof(void*)*3 + 16, v___x_2845_);
v___x_2848_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___closed__2));
v___x_2849_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v_a_2821_);
lean_ctor_set(v___x_2849_, 2, v___x_2848_);
lean_inc(v_ref_2819_);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v_ref_2819_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
v___x_2851_ = l_Lean_PersistentArray_push___redArg(v_traces_2839_, v___x_2850_);
if (v_isShared_2842_ == 0)
{
lean_ctor_set(v___x_2841_, 0, v___x_2851_);
v___x_2853_ = v___x_2841_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v___x_2851_);
lean_ctor_set_uint64(v_reuseFailAlloc_2862_, sizeof(void*)*1, v_tid_2838_);
v___x_2853_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
lean_object* v___x_2855_; 
if (v_isShared_2837_ == 0)
{
lean_ctor_set(v___x_2836_, 4, v___x_2853_);
v___x_2855_ = v___x_2836_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_env_2827_);
lean_ctor_set(v_reuseFailAlloc_2861_, 1, v_nextMacroScope_2828_);
lean_ctor_set(v_reuseFailAlloc_2861_, 2, v_ngen_2829_);
lean_ctor_set(v_reuseFailAlloc_2861_, 3, v_auxDeclNGen_2830_);
lean_ctor_set(v_reuseFailAlloc_2861_, 4, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2861_, 5, v_cache_2831_);
lean_ctor_set(v_reuseFailAlloc_2861_, 6, v_messages_2832_);
lean_ctor_set(v_reuseFailAlloc_2861_, 7, v_infoState_2833_);
lean_ctor_set(v_reuseFailAlloc_2861_, 8, v_snapshotTasks_2834_);
v___x_2855_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2856_ = lean_st_ref_set(v___y_2817_, v___x_2855_);
v___x_2857_ = lean_box(0);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2857_);
v___x_2859_ = v___x_2823_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v___x_2857_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0___boxed(lean_object* v_cls_2866_, lean_object* v_msg_2867_, lean_object* v___y_2868_, lean_object* v___y_2869_, lean_object* v___y_2870_, lean_object* v___y_2871_, lean_object* v___y_2872_){
_start:
{
lean_object* v_res_2873_; 
v_res_2873_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0(v_cls_2866_, v_msg_2867_, v___y_2868_, v___y_2869_, v___y_2870_, v___y_2871_);
lean_dec(v___y_2871_);
lean_dec_ref(v___y_2870_);
lean_dec(v___y_2869_);
lean_dec_ref(v___y_2868_);
return v_res_2873_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; 
v___x_2882_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__2));
v___x_2883_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__4));
v___x_2884_ = l_Lean_Name_append(v___x_2883_, v___x_2882_);
return v___x_2884_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2886_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__6));
v___x_2887_ = l_Lean_stringToMessageData(v___x_2886_);
return v___x_2887_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__8));
v___x_2890_ = l_Lean_stringToMessageData(v___x_2889_);
return v___x_2890_;
}
}
static uint64_t _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__10(void){
_start:
{
uint8_t v___x_2891_; uint64_t v___x_2892_; 
v___x_2891_ = 1;
v___x_2892_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2891_);
return v___x_2892_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2894_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__11));
v___x_2895_ = l_Lean_stringToMessageData(v___x_2894_);
return v___x_2895_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__14(void){
_start:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; 
v___x_2897_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__13));
v___x_2898_ = l_Lean_stringToMessageData(v___x_2897_);
return v___x_2898_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0(lean_object* v_e_2899_, lean_object* v___y_2900_, lean_object* v___y_2901_, lean_object* v___y_2902_, lean_object* v___y_2903_){
_start:
{
if (lean_obj_tag(v_e_2899_) == 11)
{
lean_object* v_typeName_2911_; lean_object* v_idx_2912_; lean_object* v_struct_2913_; lean_object* v___x_2914_; lean_object* v_env_2915_; lean_object* v___x_2916_; 
v_typeName_2911_ = lean_ctor_get(v_e_2899_, 0);
v_idx_2912_ = lean_ctor_get(v_e_2899_, 1);
v_struct_2913_ = lean_ctor_get(v_e_2899_, 2);
v___x_2914_ = lean_st_ref_get(v___y_2903_);
v_env_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc_ref(v_env_2915_);
lean_dec(v___x_2914_);
lean_inc(v_typeName_2911_);
v___x_2916_ = l_Lean_getStructureInfo_x3f(v_env_2915_, v_typeName_2911_);
if (lean_obj_tag(v___x_2916_) == 1)
{
lean_object* v_val_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_3016_; 
v_val_2917_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_2919_ = v___x_2916_;
v_isShared_2920_ = v_isSharedCheck_3016_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_val_2917_);
lean_dec(v___x_2916_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_3016_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v_fieldNames_2921_; lean_object* v___x_2922_; uint8_t v___x_2923_; 
v_fieldNames_2921_ = lean_ctor_get(v_val_2917_, 1);
lean_inc_ref(v_fieldNames_2921_);
lean_dec(v_val_2917_);
v___x_2922_ = lean_array_get_size(v_fieldNames_2921_);
v___x_2923_ = lean_nat_dec_lt(v_idx_2912_, v___x_2922_);
if (v___x_2923_ == 0)
{
lean_object* v_options_2924_; uint8_t v_hasTrace_2925_; 
lean_dec_ref(v_fieldNames_2921_);
v_options_2924_ = lean_ctor_get(v___y_2902_, 2);
v_hasTrace_2925_ = lean_ctor_get_uint8(v_options_2924_, sizeof(void*)*1);
if (v_hasTrace_2925_ == 0)
{
lean_del_object(v___x_2919_);
goto v___jp_2905_;
}
else
{
lean_object* v_inheritedTraceOptions_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; uint8_t v___x_2929_; 
v_inheritedTraceOptions_2926_ = lean_ctor_get(v___y_2902_, 13);
v___x_2927_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__2));
v___x_2928_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__5, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__5_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__5);
v___x_2929_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2926_, v_options_2924_, v___x_2928_);
if (v___x_2929_ == 0)
{
lean_del_object(v___x_2919_);
goto v___jp_2905_;
}
else
{
lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2933_; 
v___x_2930_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__7, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__7_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__7);
lean_inc(v_idx_2912_);
v___x_2931_ = l_Nat_reprFast(v_idx_2912_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set_tag(v___x_2919_, 3);
lean_ctor_set(v___x_2919_, 0, v___x_2931_);
v___x_2933_ = v___x_2919_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v___x_2931_);
v___x_2933_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; 
v___x_2934_ = l_Lean_MessageData_ofFormat(v___x_2933_);
v___x_2935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2935_, 0, v___x_2930_);
lean_ctor_set(v___x_2935_, 1, v___x_2934_);
v___x_2936_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__9, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__9_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__9);
v___x_2937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2937_, 0, v___x_2935_);
lean_ctor_set(v___x_2937_, 1, v___x_2936_);
lean_inc_ref(v_e_2899_);
v___x_2938_ = l_Lean_indentExpr(v_e_2899_);
v___x_2939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2939_, 0, v___x_2937_);
lean_ctor_set(v___x_2939_, 1, v___x_2938_);
v___x_2940_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0(v___x_2927_, v___x_2939_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2940_) == 0)
{
lean_dec_ref(v___x_2940_);
goto v___jp_2905_;
}
else
{
lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec_ref(v_e_2899_);
v_a_2941_ = lean_ctor_get(v___x_2940_, 0);
v_isSharedCheck_2948_ = !lean_is_exclusive(v___x_2940_);
if (v_isSharedCheck_2948_ == 0)
{
v___x_2943_ = v___x_2940_;
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_a_2941_);
lean_dec(v___x_2940_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2948_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2946_; 
if (v_isShared_2944_ == 0)
{
v___x_2946_ = v___x_2943_;
goto v_reusejp_2945_;
}
else
{
lean_object* v_reuseFailAlloc_2947_; 
v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
v___x_2946_ = v_reuseFailAlloc_2947_;
goto v_reusejp_2945_;
}
v_reusejp_2945_:
{
return v___x_2946_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2950_; uint8_t v_foApprox_2951_; uint8_t v_ctxApprox_2952_; uint8_t v_quasiPatternApprox_2953_; uint8_t v_constApprox_2954_; uint8_t v_isDefEqStuckEx_2955_; uint8_t v_unificationHints_2956_; uint8_t v_proofIrrelevance_2957_; uint8_t v_assignSyntheticOpaque_2958_; uint8_t v_offsetCnstrs_2959_; uint8_t v_etaStruct_2960_; uint8_t v_univApprox_2961_; uint8_t v_iota_2962_; uint8_t v_beta_2963_; uint8_t v_proj_2964_; uint8_t v_zeta_2965_; uint8_t v_zetaDelta_2966_; uint8_t v_zetaUnused_2967_; uint8_t v_zetaHave_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_3015_; 
lean_inc_ref(v_struct_2913_);
lean_inc(v_idx_2912_);
lean_dec_ref(v_e_2899_);
v___x_2950_ = l_Lean_Meta_Context_config(v___y_2900_);
v_foApprox_2951_ = lean_ctor_get_uint8(v___x_2950_, 0);
v_ctxApprox_2952_ = lean_ctor_get_uint8(v___x_2950_, 1);
v_quasiPatternApprox_2953_ = lean_ctor_get_uint8(v___x_2950_, 2);
v_constApprox_2954_ = lean_ctor_get_uint8(v___x_2950_, 3);
v_isDefEqStuckEx_2955_ = lean_ctor_get_uint8(v___x_2950_, 4);
v_unificationHints_2956_ = lean_ctor_get_uint8(v___x_2950_, 5);
v_proofIrrelevance_2957_ = lean_ctor_get_uint8(v___x_2950_, 6);
v_assignSyntheticOpaque_2958_ = lean_ctor_get_uint8(v___x_2950_, 7);
v_offsetCnstrs_2959_ = lean_ctor_get_uint8(v___x_2950_, 8);
v_etaStruct_2960_ = lean_ctor_get_uint8(v___x_2950_, 10);
v_univApprox_2961_ = lean_ctor_get_uint8(v___x_2950_, 11);
v_iota_2962_ = lean_ctor_get_uint8(v___x_2950_, 12);
v_beta_2963_ = lean_ctor_get_uint8(v___x_2950_, 13);
v_proj_2964_ = lean_ctor_get_uint8(v___x_2950_, 14);
v_zeta_2965_ = lean_ctor_get_uint8(v___x_2950_, 15);
v_zetaDelta_2966_ = lean_ctor_get_uint8(v___x_2950_, 16);
v_zetaUnused_2967_ = lean_ctor_get_uint8(v___x_2950_, 17);
v_zetaHave_2968_ = lean_ctor_get_uint8(v___x_2950_, 18);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_2970_ = v___x_2950_;
v_isShared_2971_ = v_isSharedCheck_3015_;
goto v_resetjp_2969_;
}
else
{
lean_dec(v___x_2950_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_3015_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
uint8_t v_trackZetaDelta_2972_; lean_object* v_zetaDeltaSet_2973_; lean_object* v_lctx_2974_; lean_object* v_localInstances_2975_; lean_object* v_defEqCtx_x3f_2976_; lean_object* v_synthPendingDepth_2977_; lean_object* v_canUnfold_x3f_2978_; uint8_t v_univApprox_2979_; uint8_t v_inTypeClassResolution_2980_; uint8_t v_cacheInferType_2981_; uint8_t v___x_2982_; lean_object* v_config_2984_; 
v_trackZetaDelta_2972_ = lean_ctor_get_uint8(v___y_2900_, sizeof(void*)*7);
v_zetaDeltaSet_2973_ = lean_ctor_get(v___y_2900_, 1);
v_lctx_2974_ = lean_ctor_get(v___y_2900_, 2);
v_localInstances_2975_ = lean_ctor_get(v___y_2900_, 3);
v_defEqCtx_x3f_2976_ = lean_ctor_get(v___y_2900_, 4);
v_synthPendingDepth_2977_ = lean_ctor_get(v___y_2900_, 5);
v_canUnfold_x3f_2978_ = lean_ctor_get(v___y_2900_, 6);
v_univApprox_2979_ = lean_ctor_get_uint8(v___y_2900_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2980_ = lean_ctor_get_uint8(v___y_2900_, sizeof(void*)*7 + 2);
v_cacheInferType_2981_ = lean_ctor_get_uint8(v___y_2900_, sizeof(void*)*7 + 3);
v___x_2982_ = 1;
if (v_isShared_2971_ == 0)
{
v_config_2984_ = v___x_2970_;
goto v_reusejp_2983_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 0, v_foApprox_2951_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 1, v_ctxApprox_2952_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 2, v_quasiPatternApprox_2953_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 3, v_constApprox_2954_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 4, v_isDefEqStuckEx_2955_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 5, v_unificationHints_2956_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 6, v_proofIrrelevance_2957_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 7, v_assignSyntheticOpaque_2958_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 8, v_offsetCnstrs_2959_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 10, v_etaStruct_2960_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 11, v_univApprox_2961_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 12, v_iota_2962_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 13, v_beta_2963_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 14, v_proj_2964_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 15, v_zeta_2965_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 16, v_zetaDelta_2966_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 17, v_zetaUnused_2967_);
lean_ctor_set_uint8(v_reuseFailAlloc_3014_, 18, v_zetaHave_2968_);
v_config_2984_ = v_reuseFailAlloc_3014_;
goto v_reusejp_2983_;
}
v_reusejp_2983_:
{
uint64_t v___x_2985_; uint64_t v___x_2986_; uint64_t v___x_2987_; lean_object* v___x_2988_; uint64_t v___x_2989_; uint64_t v___x_2990_; uint64_t v_key_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; 
lean_ctor_set_uint8(v_config_2984_, 9, v___x_2982_);
v___x_2985_ = l_Lean_Meta_Context_configKey(v___y_2900_);
v___x_2986_ = 2ULL;
v___x_2987_ = lean_uint64_shift_right(v___x_2985_, v___x_2986_);
v___x_2988_ = lean_array_fget(v_fieldNames_2921_, v_idx_2912_);
lean_dec(v_idx_2912_);
lean_dec_ref(v_fieldNames_2921_);
v___x_2989_ = lean_uint64_shift_left(v___x_2987_, v___x_2986_);
v___x_2990_ = lean_uint64_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__10, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__10_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__10);
v_key_2991_ = lean_uint64_lor(v___x_2989_, v___x_2990_);
v___x_2992_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_2992_, 0, v_config_2984_);
lean_ctor_set_uint64(v___x_2992_, sizeof(void*)*1, v_key_2991_);
lean_inc(v_canUnfold_x3f_2978_);
lean_inc(v_synthPendingDepth_2977_);
lean_inc(v_defEqCtx_x3f_2976_);
lean_inc_ref(v_localInstances_2975_);
lean_inc_ref(v_lctx_2974_);
lean_inc(v_zetaDeltaSet_2973_);
v___x_2993_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2993_, 0, v___x_2992_);
lean_ctor_set(v___x_2993_, 1, v_zetaDeltaSet_2973_);
lean_ctor_set(v___x_2993_, 2, v_lctx_2974_);
lean_ctor_set(v___x_2993_, 3, v_localInstances_2975_);
lean_ctor_set(v___x_2993_, 4, v_defEqCtx_x3f_2976_);
lean_ctor_set(v___x_2993_, 5, v_synthPendingDepth_2977_);
lean_ctor_set(v___x_2993_, 6, v_canUnfold_x3f_2978_);
lean_ctor_set_uint8(v___x_2993_, sizeof(void*)*7, v_trackZetaDelta_2972_);
lean_ctor_set_uint8(v___x_2993_, sizeof(void*)*7 + 1, v_univApprox_2979_);
lean_ctor_set_uint8(v___x_2993_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2980_);
lean_ctor_set_uint8(v___x_2993_, sizeof(void*)*7 + 3, v_cacheInferType_2981_);
v___x_2994_ = l_Lean_Meta_mkProjection(v_struct_2913_, v___x_2988_, v___x_2993_, v___y_2901_, v___y_2902_, v___y_2903_);
lean_dec_ref(v___x_2993_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3005_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3005_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3005_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 0, v_a_2995_);
v___x_3000_ = v___x_2919_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3004_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
lean_object* v___x_3002_; 
if (v_isShared_2998_ == 0)
{
lean_ctor_set(v___x_2997_, 0, v___x_3000_);
v___x_3002_ = v___x_2997_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v___x_3000_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_del_object(v___x_2919_);
v_a_3006_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2994_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2994_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
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
lean_object* v_options_3017_; uint8_t v_hasTrace_3018_; 
lean_dec(v___x_2916_);
v_options_3017_ = lean_ctor_get(v___y_2902_, 2);
v_hasTrace_3018_ = lean_ctor_get_uint8(v_options_3017_, sizeof(void*)*1);
if (v_hasTrace_3018_ == 0)
{
goto v___jp_2908_;
}
else
{
lean_object* v_inheritedTraceOptions_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; uint8_t v___x_3022_; 
v_inheritedTraceOptions_3019_ = lean_ctor_get(v___y_2902_, 13);
v___x_3020_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__0___closed__2));
v___x_3021_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__5, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__5_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__5);
v___x_3022_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3019_, v_options_3017_, v___x_3021_);
if (v___x_3022_ == 0)
{
goto v___jp_2908_;
}
else
{
lean_object* v___x_3023_; lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; 
v___x_3023_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__12, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__12_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__12);
lean_inc(v_typeName_2911_);
v___x_3024_ = l_Lean_MessageData_ofName(v_typeName_2911_);
v___x_3025_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3025_, 0, v___x_3023_);
lean_ctor_set(v___x_3025_, 1, v___x_3024_);
v___x_3026_ = lean_obj_once(&l_Lean_Meta_Grind_foldProjs___lam__0___closed__14, &l_Lean_Meta_Grind_foldProjs___lam__0___closed__14_once, _init_l_Lean_Meta_Grind_foldProjs___lam__0___closed__14);
v___x_3027_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3027_, 0, v___x_3025_);
lean_ctor_set(v___x_3027_, 1, v___x_3026_);
lean_inc_ref(v_e_2899_);
v___x_3028_ = l_Lean_indentExpr(v_e_2899_);
v___x_3029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3029_, 0, v___x_3027_);
lean_ctor_set(v___x_3029_, 1, v___x_3028_);
v___x_3030_ = l_Lean_addTrace___at___00Lean_Meta_Grind_foldProjs_spec__0(v___x_3020_, v___x_3029_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_3030_) == 0)
{
lean_dec_ref(v___x_3030_);
goto v___jp_2908_;
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_dec_ref(v_e_2899_);
v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3030_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3030_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3030_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_3039_; lean_object* v___x_3040_; 
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_e_2899_);
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v___x_3039_);
return v___x_3040_;
}
v___jp_2905_:
{
lean_object* v___x_2906_; lean_object* v___x_2907_; 
v___x_2906_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2906_, 0, v_e_2899_);
v___x_2907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2906_);
return v___x_2907_;
}
v___jp_2908_:
{
lean_object* v___x_2909_; lean_object* v___x_2910_; 
v___x_2909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2909_, 0, v_e_2899_);
v___x_2910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2909_);
return v___x_2910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__0___boxed(lean_object* v_e_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_){
_start:
{
lean_object* v_res_3047_; 
v_res_3047_ = l_Lean_Meta_Grind_foldProjs___lam__0(v_e_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
lean_dec(v___y_3043_);
lean_dec_ref(v___y_3042_);
return v_res_3047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1(lean_object* v_x_3050_, lean_object* v___y_3051_, lean_object* v___y_3052_, lean_object* v___y_3053_, lean_object* v___y_3054_){
_start:
{
lean_object* v___x_3056_; lean_object* v___x_3057_; 
v___x_3056_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__1___closed__0));
v___x_3057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3056_);
return v___x_3057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___lam__1___boxed(lean_object* v_x_3058_, lean_object* v___y_3059_, lean_object* v___y_3060_, lean_object* v___y_3061_, lean_object* v___y_3062_, lean_object* v___y_3063_){
_start:
{
lean_object* v_res_3064_; 
v_res_3064_ = l_Lean_Meta_Grind_foldProjs___lam__1(v_x_3058_, v___y_3059_, v___y_3060_, v___y_3061_, v___y_3062_);
lean_dec(v___y_3062_);
lean_dec_ref(v___y_3061_);
lean_dec(v___y_3060_);
lean_dec_ref(v___y_3059_);
lean_dec_ref(v_x_3058_);
return v_res_3064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_object* v_00_u03b1_3065_, lean_object* v_x_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; lean_object* v___x_3073_; 
v___x_3072_ = lean_apply_1(v_x_3066_, lean_box(0));
v___x_3073_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0___boxed(lean_object* v_00_u03b1_3074_, lean_object* v_x_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_, lean_object* v___y_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(v_00_u03b1_3074_, v_x_3075_, v___y_3076_, v___y_3077_, v___y_3078_, v___y_3079_);
lean_dec(v___y_3079_);
lean_dec_ref(v___y_3078_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg(lean_object* v_ref_3082_){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg___closed__5);
v___x_3085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3085_, 0, v_ref_3082_);
lean_ctor_set(v___x_3085_, 1, v___x_3084_);
v___x_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg___boxed(lean_object* v_ref_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v_res_3089_; 
v_res_3089_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg(v_ref_3087_);
return v_res_3089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg(lean_object* v_x_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v___y_3098_; lean_object* v_fileName_3107_; lean_object* v_fileMap_3108_; lean_object* v_options_3109_; lean_object* v_currRecDepth_3110_; lean_object* v_maxRecDepth_3111_; lean_object* v_ref_3112_; lean_object* v_currNamespace_3113_; lean_object* v_openDecls_3114_; lean_object* v_initHeartbeats_3115_; lean_object* v_maxHeartbeats_3116_; lean_object* v_quotContext_3117_; lean_object* v_currMacroScope_3118_; uint8_t v_diag_3119_; lean_object* v_cancelTk_x3f_3120_; uint8_t v_suppressElabErrors_3121_; lean_object* v_inheritedTraceOptions_3122_; uint8_t v___x_3123_; 
v_fileName_3107_ = lean_ctor_get(v___y_3094_, 0);
v_fileMap_3108_ = lean_ctor_get(v___y_3094_, 1);
v_options_3109_ = lean_ctor_get(v___y_3094_, 2);
v_currRecDepth_3110_ = lean_ctor_get(v___y_3094_, 3);
v_maxRecDepth_3111_ = lean_ctor_get(v___y_3094_, 4);
v_ref_3112_ = lean_ctor_get(v___y_3094_, 5);
v_currNamespace_3113_ = lean_ctor_get(v___y_3094_, 6);
v_openDecls_3114_ = lean_ctor_get(v___y_3094_, 7);
v_initHeartbeats_3115_ = lean_ctor_get(v___y_3094_, 8);
v_maxHeartbeats_3116_ = lean_ctor_get(v___y_3094_, 9);
v_quotContext_3117_ = lean_ctor_get(v___y_3094_, 10);
v_currMacroScope_3118_ = lean_ctor_get(v___y_3094_, 11);
v_diag_3119_ = lean_ctor_get_uint8(v___y_3094_, sizeof(void*)*14);
v_cancelTk_x3f_3120_ = lean_ctor_get(v___y_3094_, 12);
v_suppressElabErrors_3121_ = lean_ctor_get_uint8(v___y_3094_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_3122_ = lean_ctor_get(v___y_3094_, 13);
v___x_3123_ = lean_nat_dec_eq(v_currRecDepth_3110_, v_maxRecDepth_3111_);
if (v___x_3123_ == 0)
{
lean_object* v___x_3124_; lean_object* v___x_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v___x_3124_ = lean_unsigned_to_nat(1u);
v___x_3125_ = lean_nat_add(v_currRecDepth_3110_, v___x_3124_);
lean_inc_ref(v_inheritedTraceOptions_3122_);
lean_inc(v_cancelTk_x3f_3120_);
lean_inc(v_currMacroScope_3118_);
lean_inc(v_quotContext_3117_);
lean_inc(v_maxHeartbeats_3116_);
lean_inc(v_initHeartbeats_3115_);
lean_inc(v_openDecls_3114_);
lean_inc(v_currNamespace_3113_);
lean_inc(v_ref_3112_);
lean_inc(v_maxRecDepth_3111_);
lean_inc_ref(v_options_3109_);
lean_inc_ref(v_fileMap_3108_);
lean_inc_ref(v_fileName_3107_);
v___x_3126_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_3126_, 0, v_fileName_3107_);
lean_ctor_set(v___x_3126_, 1, v_fileMap_3108_);
lean_ctor_set(v___x_3126_, 2, v_options_3109_);
lean_ctor_set(v___x_3126_, 3, v___x_3125_);
lean_ctor_set(v___x_3126_, 4, v_maxRecDepth_3111_);
lean_ctor_set(v___x_3126_, 5, v_ref_3112_);
lean_ctor_set(v___x_3126_, 6, v_currNamespace_3113_);
lean_ctor_set(v___x_3126_, 7, v_openDecls_3114_);
lean_ctor_set(v___x_3126_, 8, v_initHeartbeats_3115_);
lean_ctor_set(v___x_3126_, 9, v_maxHeartbeats_3116_);
lean_ctor_set(v___x_3126_, 10, v_quotContext_3117_);
lean_ctor_set(v___x_3126_, 11, v_currMacroScope_3118_);
lean_ctor_set(v___x_3126_, 12, v_cancelTk_x3f_3120_);
lean_ctor_set(v___x_3126_, 13, v_inheritedTraceOptions_3122_);
lean_ctor_set_uint8(v___x_3126_, sizeof(void*)*14, v_diag_3119_);
lean_ctor_set_uint8(v___x_3126_, sizeof(void*)*14 + 1, v_suppressElabErrors_3121_);
lean_inc(v___y_3095_);
lean_inc(v___y_3093_);
lean_inc_ref(v___y_3092_);
lean_inc(v___y_3091_);
v___x_3127_ = lean_apply_6(v_x_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___x_3126_, v___y_3095_, lean_box(0));
v___y_3098_ = v___x_3127_;
goto v___jp_3097_;
}
else
{
lean_object* v___x_3128_; 
lean_dec_ref(v_x_3090_);
lean_inc(v_ref_3112_);
v___x_3128_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg(v_ref_3112_);
v___y_3098_ = v___x_3128_;
goto v___jp_3097_;
}
v___jp_3097_:
{
if (lean_obj_tag(v___y_3098_) == 0)
{
return v___y_3098_;
}
else
{
lean_object* v_a_3099_; lean_object* v___x_3101_; uint8_t v_isShared_3102_; uint8_t v_isSharedCheck_3106_; 
v_a_3099_ = lean_ctor_get(v___y_3098_, 0);
v_isSharedCheck_3106_ = !lean_is_exclusive(v___y_3098_);
if (v_isSharedCheck_3106_ == 0)
{
v___x_3101_ = v___y_3098_;
v_isShared_3102_ = v_isSharedCheck_3106_;
goto v_resetjp_3100_;
}
else
{
lean_inc(v_a_3099_);
lean_dec(v___y_3098_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg___boxed(lean_object* v_x_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v_res_3136_; 
v_res_3136_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg(v_x_3129_, v___y_3130_, v___y_3131_, v___y_3132_, v___y_3133_, v___y_3134_);
lean_dec(v___y_3134_);
lean_dec_ref(v___y_3133_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0(lean_object* v_k_3137_, lean_object* v___y_3138_, lean_object* v_b_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_, lean_object* v___y_3142_, lean_object* v___y_3143_){
_start:
{
lean_object* v___x_3145_; 
lean_inc(v___y_3143_);
lean_inc_ref(v___y_3142_);
lean_inc(v___y_3141_);
lean_inc_ref(v___y_3140_);
lean_inc(v___y_3138_);
v___x_3145_ = lean_apply_7(v_k_3137_, v_b_3139_, v___y_3138_, v___y_3140_, v___y_3141_, v___y_3142_, v___y_3143_, lean_box(0));
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0___boxed(lean_object* v_k_3146_, lean_object* v___y_3147_, lean_object* v_b_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_){
_start:
{
lean_object* v_res_3154_; 
v_res_3154_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0(v_k_3146_, v___y_3147_, v_b_3148_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
lean_dec(v___y_3150_);
lean_dec_ref(v___y_3149_);
lean_dec(v___y_3147_);
return v_res_3154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(lean_object* v_name_3155_, uint8_t v_bi_3156_, lean_object* v_type_3157_, lean_object* v_k_3158_, uint8_t v_kind_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v___f_3166_; lean_object* v___x_3167_; 
lean_inc(v___y_3160_);
v___f_3166_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3166_, 0, v_k_3158_);
lean_closure_set(v___f_3166_, 1, v___y_3160_);
v___x_3167_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_3155_, v_bi_3156_, v_type_3157_, v___f_3166_, v_kind_3159_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
if (lean_obj_tag(v___x_3167_) == 0)
{
return v___x_3167_;
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
v_a_3168_ = lean_ctor_get(v___x_3167_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___x_3167_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___x_3167_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___x_3167_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___boxed(lean_object* v_name_3176_, lean_object* v_bi_3177_, lean_object* v_type_3178_, lean_object* v_k_3179_, lean_object* v_kind_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
uint8_t v_bi_boxed_3187_; uint8_t v_kind_boxed_3188_; lean_object* v_res_3189_; 
v_bi_boxed_3187_ = lean_unbox(v_bi_3177_);
v_kind_boxed_3188_ = lean_unbox(v_kind_3180_);
v_res_3189_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(v_name_3176_, v_bi_boxed_3187_, v_type_3178_, v_k_3179_, v_kind_boxed_3188_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
lean_dec(v___y_3181_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__2(lean_object* v___x_3190_, lean_object* v___y_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_){
_start:
{
lean_object* v___x_3196_; 
v___x_3196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3196_, 0, v___x_3190_);
return v___x_3196_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__2___boxed(lean_object* v___x_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_, lean_object* v___y_3202_){
_start:
{
lean_object* v_res_3203_; 
v_res_3203_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__2(v___x_3197_, v___y_3198_, v___y_3199_, v___y_3200_, v___y_3201_);
lean_dec(v___y_3201_);
lean_dec_ref(v___y_3200_);
lean_dec(v___y_3199_);
lean_dec_ref(v___y_3198_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg(lean_object* v_name_3204_, lean_object* v_type_3205_, lean_object* v_val_3206_, lean_object* v_k_3207_, uint8_t v_nondep_3208_, uint8_t v_kind_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___f_3216_; lean_object* v___x_3217_; 
lean_inc(v___y_3210_);
v___f_3216_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg___lam__0___boxed), 8, 2);
lean_closure_set(v___f_3216_, 0, v_k_3207_);
lean_closure_set(v___f_3216_, 1, v___y_3210_);
v___x_3217_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), v_name_3204_, v_type_3205_, v_val_3206_, v___f_3216_, v_nondep_3208_, v_kind_3209_, v___y_3211_, v___y_3212_, v___y_3213_, v___y_3214_);
if (lean_obj_tag(v___x_3217_) == 0)
{
return v___x_3217_;
}
else
{
lean_object* v_a_3218_; lean_object* v___x_3220_; uint8_t v_isShared_3221_; uint8_t v_isSharedCheck_3225_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3225_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3225_ == 0)
{
v___x_3220_ = v___x_3217_;
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
else
{
lean_inc(v_a_3218_);
lean_dec(v___x_3217_);
v___x_3220_ = lean_box(0);
v_isShared_3221_ = v_isSharedCheck_3225_;
goto v_resetjp_3219_;
}
v_resetjp_3219_:
{
lean_object* v___x_3223_; 
if (v_isShared_3221_ == 0)
{
v___x_3223_ = v___x_3220_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3224_; 
v_reuseFailAlloc_3224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3224_, 0, v_a_3218_);
v___x_3223_ = v_reuseFailAlloc_3224_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
return v___x_3223_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg___boxed(lean_object* v_name_3226_, lean_object* v_type_3227_, lean_object* v_val_3228_, lean_object* v_k_3229_, lean_object* v_nondep_3230_, lean_object* v_kind_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_, lean_object* v___y_3237_){
_start:
{
uint8_t v_nondep_boxed_3238_; uint8_t v_kind_boxed_3239_; lean_object* v_res_3240_; 
v_nondep_boxed_3238_ = lean_unbox(v_nondep_3230_);
v_kind_boxed_3239_ = lean_unbox(v_kind_3231_);
v_res_3240_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg(v_name_3226_, v_type_3227_, v_val_3228_, v_k_3229_, v_nondep_boxed_3238_, v_kind_boxed_3239_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
lean_dec(v___y_3236_);
lean_dec_ref(v___y_3235_);
lean_dec(v___y_3234_);
lean_dec_ref(v___y_3233_);
lean_dec(v___y_3232_);
return v_res_3240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___lam__0(lean_object* v_fvars_3243_, lean_object* v_pre_3244_, lean_object* v_post_3245_, uint8_t v_usedLetOnly_3246_, uint8_t v_skipConstInApp_3247_, uint8_t v_skipInstances_3248_, lean_object* v_body_3249_, lean_object* v_x_3250_, lean_object* v___y_3251_, lean_object* v___y_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_){
_start:
{
lean_object* v___x_3257_; lean_object* v___x_3258_; 
v___x_3257_ = lean_array_push(v_fvars_3243_, v_x_3250_);
v___x_3258_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7(v_pre_3244_, v_post_3245_, v_usedLetOnly_3246_, v_skipConstInApp_3247_, v_skipInstances_3248_, v___x_3257_, v_body_3249_, v___y_3251_, v___y_3252_, v___y_3253_, v___y_3254_, v___y_3255_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___lam__0___boxed(lean_object* v_fvars_3259_, lean_object* v_pre_3260_, lean_object* v_post_3261_, lean_object* v_usedLetOnly_3262_, lean_object* v_skipConstInApp_3263_, lean_object* v_skipInstances_3264_, lean_object* v_body_3265_, lean_object* v_x_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_){
_start:
{
uint8_t v_usedLetOnly_boxed_3273_; uint8_t v_skipConstInApp_boxed_3274_; uint8_t v_skipInstances_boxed_3275_; lean_object* v_res_3276_; 
v_usedLetOnly_boxed_3273_ = lean_unbox(v_usedLetOnly_3262_);
v_skipConstInApp_boxed_3274_ = lean_unbox(v_skipConstInApp_3263_);
v_skipInstances_boxed_3275_ = lean_unbox(v_skipInstances_3264_);
v_res_3276_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___lam__0(v_fvars_3259_, v_pre_3260_, v_post_3261_, v_usedLetOnly_boxed_3273_, v_skipConstInApp_boxed_3274_, v_skipInstances_boxed_3275_, v_body_3265_, v_x_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_, v___y_3271_);
lean_dec(v___y_3271_);
lean_dec_ref(v___y_3270_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(lean_object* v_pre_3277_, lean_object* v_post_3278_, uint8_t v_usedLetOnly_3279_, uint8_t v_skipConstInApp_3280_, uint8_t v_skipInstances_3281_, lean_object* v_e_3282_, lean_object* v_a_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v___x_3289_; 
lean_inc_ref(v_post_3278_);
lean_inc(v___y_3287_);
lean_inc_ref(v___y_3286_);
lean_inc(v___y_3285_);
lean_inc_ref(v___y_3284_);
lean_inc_ref(v_e_3282_);
v___x_3289_ = lean_apply_6(v_post_3278_, v_e_3282_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_, lean_box(0));
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v_a_3290_; lean_object* v___x_3292_; uint8_t v_isShared_3293_; uint8_t v_isSharedCheck_3308_; 
v_a_3290_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3292_ = v___x_3289_;
v_isShared_3293_ = v_isSharedCheck_3308_;
goto v_resetjp_3291_;
}
else
{
lean_inc(v_a_3290_);
lean_dec(v___x_3289_);
v___x_3292_ = lean_box(0);
v_isShared_3293_ = v_isSharedCheck_3308_;
goto v_resetjp_3291_;
}
v_resetjp_3291_:
{
switch(lean_obj_tag(v_a_3290_))
{
case 0:
{
lean_object* v_e_3294_; lean_object* v___x_3296_; 
lean_dec_ref(v_e_3282_);
lean_dec_ref(v_post_3278_);
lean_dec_ref(v_pre_3277_);
v_e_3294_ = lean_ctor_get(v_a_3290_, 0);
lean_inc_ref(v_e_3294_);
lean_dec_ref(v_a_3290_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v_e_3294_);
v___x_3296_ = v___x_3292_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_e_3294_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
case 1:
{
lean_object* v_e_3298_; lean_object* v___x_3299_; 
lean_del_object(v___x_3292_);
lean_dec_ref(v_e_3282_);
v_e_3298_ = lean_ctor_get(v_a_3290_, 0);
lean_inc_ref(v_e_3298_);
lean_dec_ref(v_a_3290_);
v___x_3299_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3277_, v_post_3278_, v_usedLetOnly_3279_, v_skipConstInApp_3280_, v_skipInstances_3281_, v_e_3298_, v_a_3283_, v___y_3284_, v___y_3285_, v___y_3286_, v___y_3287_);
return v___x_3299_;
}
default: 
{
lean_object* v_e_x3f_3300_; 
lean_dec_ref(v_post_3278_);
lean_dec_ref(v_pre_3277_);
v_e_x3f_3300_ = lean_ctor_get(v_a_3290_, 0);
lean_inc(v_e_x3f_3300_);
lean_dec_ref(v_a_3290_);
if (lean_obj_tag(v_e_x3f_3300_) == 0)
{
lean_object* v___x_3302_; 
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v_e_3282_);
v___x_3302_ = v___x_3292_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_e_3282_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
else
{
lean_object* v_val_3304_; lean_object* v___x_3306_; 
lean_dec_ref(v_e_3282_);
v_val_3304_ = lean_ctor_get(v_e_x3f_3300_, 0);
lean_inc(v_val_3304_);
lean_dec_ref(v_e_x3f_3300_);
if (v_isShared_3293_ == 0)
{
lean_ctor_set(v___x_3292_, 0, v_val_3304_);
v___x_3306_ = v___x_3292_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_val_3304_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
}
else
{
lean_object* v_a_3309_; lean_object* v___x_3311_; uint8_t v_isShared_3312_; uint8_t v_isSharedCheck_3316_; 
lean_dec_ref(v_e_3282_);
lean_dec_ref(v_post_3278_);
lean_dec_ref(v_pre_3277_);
v_a_3309_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3316_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3316_ == 0)
{
v___x_3311_ = v___x_3289_;
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
else
{
lean_inc(v_a_3309_);
lean_dec(v___x_3289_);
v___x_3311_ = lean_box(0);
v_isShared_3312_ = v_isSharedCheck_3316_;
goto v_resetjp_3310_;
}
v_resetjp_3310_:
{
lean_object* v___x_3314_; 
if (v_isShared_3312_ == 0)
{
v___x_3314_ = v___x_3311_;
goto v_reusejp_3313_;
}
else
{
lean_object* v_reuseFailAlloc_3315_; 
v_reuseFailAlloc_3315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_a_3309_);
v___x_3314_ = v_reuseFailAlloc_3315_;
goto v_reusejp_3313_;
}
v_reusejp_3313_:
{
return v___x_3314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7(lean_object* v_pre_3317_, lean_object* v_post_3318_, uint8_t v_usedLetOnly_3319_, uint8_t v_skipConstInApp_3320_, uint8_t v_skipInstances_3321_, lean_object* v_fvars_3322_, lean_object* v_e_3323_, lean_object* v_a_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
if (lean_obj_tag(v_e_3323_) == 6)
{
lean_object* v_binderName_3330_; lean_object* v_binderType_3331_; lean_object* v_body_3332_; uint8_t v_binderInfo_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_binderName_3330_ = lean_ctor_get(v_e_3323_, 0);
lean_inc(v_binderName_3330_);
v_binderType_3331_ = lean_ctor_get(v_e_3323_, 1);
lean_inc_ref(v_binderType_3331_);
v_body_3332_ = lean_ctor_get(v_e_3323_, 2);
lean_inc_ref(v_body_3332_);
v_binderInfo_3333_ = lean_ctor_get_uint8(v_e_3323_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3323_);
v___x_3334_ = lean_expr_instantiate_rev(v_binderType_3331_, v_fvars_3322_);
lean_dec_ref(v_binderType_3331_);
lean_inc_ref(v_post_3318_);
lean_inc_ref(v_pre_3317_);
v___x_3335_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3317_, v_post_3318_, v_usedLetOnly_3319_, v_skipConstInApp_3320_, v_skipInstances_3321_, v___x_3334_, v_a_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v_a_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___f_3340_; uint8_t v___x_3341_; lean_object* v___x_3342_; 
v_a_3336_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_a_3336_);
lean_dec_ref(v___x_3335_);
v___x_3337_ = lean_box(v_usedLetOnly_3319_);
v___x_3338_ = lean_box(v_skipConstInApp_3320_);
v___x_3339_ = lean_box(v_skipInstances_3321_);
v___f_3340_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3340_, 0, v_fvars_3322_);
lean_closure_set(v___f_3340_, 1, v_pre_3317_);
lean_closure_set(v___f_3340_, 2, v_post_3318_);
lean_closure_set(v___f_3340_, 3, v___x_3337_);
lean_closure_set(v___f_3340_, 4, v___x_3338_);
lean_closure_set(v___f_3340_, 5, v___x_3339_);
lean_closure_set(v___f_3340_, 6, v_body_3332_);
v___x_3341_ = 0;
v___x_3342_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(v_binderName_3330_, v_binderInfo_3333_, v_a_3336_, v___f_3340_, v___x_3341_, v_a_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3342_;
}
else
{
lean_dec_ref(v_body_3332_);
lean_dec(v_binderName_3330_);
lean_dec_ref(v_fvars_3322_);
lean_dec_ref(v_post_3318_);
lean_dec_ref(v_pre_3317_);
return v___x_3335_;
}
}
else
{
lean_object* v___x_3343_; lean_object* v___x_3344_; 
v___x_3343_ = lean_expr_instantiate_rev(v_e_3323_, v_fvars_3322_);
lean_dec_ref(v_e_3323_);
lean_inc_ref(v_post_3318_);
lean_inc_ref(v_pre_3317_);
v___x_3344_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3317_, v_post_3318_, v_usedLetOnly_3319_, v_skipConstInApp_3320_, v_skipInstances_3321_, v___x_3343_, v_a_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; uint8_t v___x_3346_; uint8_t v___x_3347_; uint8_t v___x_3348_; lean_object* v___x_3349_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref(v___x_3344_);
v___x_3346_ = 0;
v___x_3347_ = 1;
v___x_3348_ = 1;
v___x_3349_ = l_Lean_Meta_mkLambdaFVars(v_fvars_3322_, v_a_3345_, v___x_3346_, v_usedLetOnly_3319_, v___x_3346_, v___x_3347_, v___x_3348_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec_ref(v_fvars_3322_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3351_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref(v___x_3349_);
v___x_3351_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3317_, v_post_3318_, v_usedLetOnly_3319_, v_skipConstInApp_3320_, v_skipInstances_3321_, v_a_3350_, v_a_3324_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
return v___x_3351_;
}
else
{
lean_dec_ref(v_post_3318_);
lean_dec_ref(v_pre_3317_);
return v___x_3349_;
}
}
else
{
lean_dec_ref(v_fvars_3322_);
lean_dec_ref(v_post_3318_);
lean_dec_ref(v_pre_3317_);
return v___x_3344_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___lam__0(lean_object* v_fvars_3352_, lean_object* v_pre_3353_, lean_object* v_post_3354_, uint8_t v_usedLetOnly_3355_, uint8_t v_skipConstInApp_3356_, uint8_t v_skipInstances_3357_, lean_object* v_body_3358_, lean_object* v_x_3359_, lean_object* v___y_3360_, lean_object* v___y_3361_, lean_object* v___y_3362_, lean_object* v___y_3363_, lean_object* v___y_3364_){
_start:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; 
v___x_3366_ = lean_array_push(v_fvars_3352_, v_x_3359_);
v___x_3367_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8(v_pre_3353_, v_post_3354_, v_usedLetOnly_3355_, v_skipConstInApp_3356_, v_skipInstances_3357_, v___x_3366_, v_body_3358_, v___y_3360_, v___y_3361_, v___y_3362_, v___y_3363_, v___y_3364_);
return v___x_3367_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___lam__0___boxed(lean_object* v_fvars_3368_, lean_object* v_pre_3369_, lean_object* v_post_3370_, lean_object* v_usedLetOnly_3371_, lean_object* v_skipConstInApp_3372_, lean_object* v_skipInstances_3373_, lean_object* v_body_3374_, lean_object* v_x_3375_, lean_object* v___y_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_, lean_object* v___y_3381_){
_start:
{
uint8_t v_usedLetOnly_boxed_3382_; uint8_t v_skipConstInApp_boxed_3383_; uint8_t v_skipInstances_boxed_3384_; lean_object* v_res_3385_; 
v_usedLetOnly_boxed_3382_ = lean_unbox(v_usedLetOnly_3371_);
v_skipConstInApp_boxed_3383_ = lean_unbox(v_skipConstInApp_3372_);
v_skipInstances_boxed_3384_ = lean_unbox(v_skipInstances_3373_);
v_res_3385_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___lam__0(v_fvars_3368_, v_pre_3369_, v_post_3370_, v_usedLetOnly_boxed_3382_, v_skipConstInApp_boxed_3383_, v_skipInstances_boxed_3384_, v_body_3374_, v_x_3375_, v___y_3376_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
lean_dec(v___y_3380_);
lean_dec_ref(v___y_3379_);
lean_dec(v___y_3378_);
lean_dec_ref(v___y_3377_);
lean_dec(v___y_3376_);
return v_res_3385_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8(lean_object* v_pre_3386_, lean_object* v_post_3387_, uint8_t v_usedLetOnly_3388_, uint8_t v_skipConstInApp_3389_, uint8_t v_skipInstances_3390_, lean_object* v_fvars_3391_, lean_object* v_e_3392_, lean_object* v_a_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_){
_start:
{
if (lean_obj_tag(v_e_3392_) == 8)
{
lean_object* v_declName_3399_; lean_object* v_type_3400_; lean_object* v_value_3401_; lean_object* v_body_3402_; uint8_t v_nondep_3403_; lean_object* v___x_3404_; lean_object* v___x_3405_; 
v_declName_3399_ = lean_ctor_get(v_e_3392_, 0);
lean_inc(v_declName_3399_);
v_type_3400_ = lean_ctor_get(v_e_3392_, 1);
lean_inc_ref(v_type_3400_);
v_value_3401_ = lean_ctor_get(v_e_3392_, 2);
lean_inc_ref(v_value_3401_);
v_body_3402_ = lean_ctor_get(v_e_3392_, 3);
lean_inc_ref(v_body_3402_);
v_nondep_3403_ = lean_ctor_get_uint8(v_e_3392_, sizeof(void*)*4 + 8);
lean_dec_ref(v_e_3392_);
v___x_3404_ = lean_expr_instantiate_rev(v_type_3400_, v_fvars_3391_);
lean_dec_ref(v_type_3400_);
lean_inc_ref(v_post_3387_);
lean_inc_ref(v_pre_3386_);
v___x_3405_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3386_, v_post_3387_, v_usedLetOnly_3388_, v_skipConstInApp_3389_, v_skipInstances_3390_, v___x_3404_, v_a_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
if (lean_obj_tag(v___x_3405_) == 0)
{
lean_object* v_a_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; 
v_a_3406_ = lean_ctor_get(v___x_3405_, 0);
lean_inc(v_a_3406_);
lean_dec_ref(v___x_3405_);
v___x_3407_ = lean_expr_instantiate_rev(v_value_3401_, v_fvars_3391_);
lean_dec_ref(v_value_3401_);
lean_inc_ref(v_post_3387_);
lean_inc_ref(v_pre_3386_);
v___x_3408_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3386_, v_post_3387_, v_usedLetOnly_3388_, v_skipConstInApp_3389_, v_skipInstances_3390_, v___x_3407_, v_a_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
if (lean_obj_tag(v___x_3408_) == 0)
{
lean_object* v_a_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___f_3413_; uint8_t v___x_3414_; lean_object* v___x_3415_; 
v_a_3409_ = lean_ctor_get(v___x_3408_, 0);
lean_inc(v_a_3409_);
lean_dec_ref(v___x_3408_);
v___x_3410_ = lean_box(v_usedLetOnly_3388_);
v___x_3411_ = lean_box(v_skipConstInApp_3389_);
v___x_3412_ = lean_box(v_skipInstances_3390_);
v___f_3413_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3413_, 0, v_fvars_3391_);
lean_closure_set(v___f_3413_, 1, v_pre_3386_);
lean_closure_set(v___f_3413_, 2, v_post_3387_);
lean_closure_set(v___f_3413_, 3, v___x_3410_);
lean_closure_set(v___f_3413_, 4, v___x_3411_);
lean_closure_set(v___f_3413_, 5, v___x_3412_);
lean_closure_set(v___f_3413_, 6, v_body_3402_);
v___x_3414_ = 0;
v___x_3415_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg(v_declName_3399_, v_a_3406_, v_a_3409_, v___f_3413_, v_nondep_3403_, v___x_3414_, v_a_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3415_;
}
else
{
lean_dec(v_a_3406_);
lean_dec_ref(v_body_3402_);
lean_dec(v_declName_3399_);
lean_dec_ref(v_fvars_3391_);
lean_dec_ref(v_post_3387_);
lean_dec_ref(v_pre_3386_);
return v___x_3408_;
}
}
else
{
lean_dec_ref(v_body_3402_);
lean_dec_ref(v_value_3401_);
lean_dec(v_declName_3399_);
lean_dec_ref(v_fvars_3391_);
lean_dec_ref(v_post_3387_);
lean_dec_ref(v_pre_3386_);
return v___x_3405_;
}
}
else
{
lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3416_ = lean_expr_instantiate_rev(v_e_3392_, v_fvars_3391_);
lean_dec_ref(v_e_3392_);
lean_inc_ref(v_post_3387_);
lean_inc_ref(v_pre_3386_);
v___x_3417_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3386_, v_post_3387_, v_usedLetOnly_3388_, v_skipConstInApp_3389_, v_skipInstances_3390_, v___x_3416_, v_a_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
if (lean_obj_tag(v___x_3417_) == 0)
{
lean_object* v_a_3418_; uint8_t v___x_3419_; uint8_t v___x_3420_; lean_object* v___x_3421_; 
v_a_3418_ = lean_ctor_get(v___x_3417_, 0);
lean_inc(v_a_3418_);
lean_dec_ref(v___x_3417_);
v___x_3419_ = 0;
v___x_3420_ = 1;
v___x_3421_ = l_Lean_Meta_mkLetFVars(v_fvars_3391_, v_a_3418_, v_usedLetOnly_3388_, v___x_3419_, v___x_3420_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
lean_dec_ref(v_fvars_3391_);
if (lean_obj_tag(v___x_3421_) == 0)
{
lean_object* v_a_3422_; lean_object* v___x_3423_; 
v_a_3422_ = lean_ctor_get(v___x_3421_, 0);
lean_inc(v_a_3422_);
lean_dec_ref(v___x_3421_);
v___x_3423_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3386_, v_post_3387_, v_usedLetOnly_3388_, v_skipConstInApp_3389_, v_skipInstances_3390_, v_a_3422_, v_a_3393_, v___y_3394_, v___y_3395_, v___y_3396_, v___y_3397_);
return v___x_3423_;
}
else
{
lean_dec_ref(v_post_3387_);
lean_dec_ref(v_pre_3386_);
return v___x_3421_;
}
}
else
{
lean_dec_ref(v_fvars_3391_);
lean_dec_ref(v_post_3387_);
lean_dec_ref(v_pre_3386_);
return v___x_3417_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__3(lean_object* v_pre_3424_, lean_object* v_post_3425_, uint8_t v_usedLetOnly_3426_, uint8_t v_skipConstInApp_3427_, uint8_t v_skipInstances_3428_, size_t v_sz_3429_, size_t v_i_3430_, lean_object* v_bs_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_, lean_object* v___y_3435_, lean_object* v___y_3436_){
_start:
{
uint8_t v___x_3438_; 
v___x_3438_ = lean_usize_dec_lt(v_i_3430_, v_sz_3429_);
if (v___x_3438_ == 0)
{
lean_object* v___x_3439_; 
lean_dec_ref(v_post_3425_);
lean_dec_ref(v_pre_3424_);
v___x_3439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3439_, 0, v_bs_3431_);
return v___x_3439_;
}
else
{
lean_object* v_v_3440_; lean_object* v___x_3441_; 
v_v_3440_ = lean_array_uget_borrowed(v_bs_3431_, v_i_3430_);
lean_inc(v_v_3440_);
lean_inc_ref(v_post_3425_);
lean_inc_ref(v_pre_3424_);
v___x_3441_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3424_, v_post_3425_, v_usedLetOnly_3426_, v_skipConstInApp_3427_, v_skipInstances_3428_, v_v_3440_, v___y_3432_, v___y_3433_, v___y_3434_, v___y_3435_, v___y_3436_);
if (lean_obj_tag(v___x_3441_) == 0)
{
lean_object* v_a_3442_; lean_object* v___x_3443_; lean_object* v_bs_x27_3444_; size_t v___x_3445_; size_t v___x_3446_; lean_object* v___x_3447_; 
v_a_3442_ = lean_ctor_get(v___x_3441_, 0);
lean_inc(v_a_3442_);
lean_dec_ref(v___x_3441_);
v___x_3443_ = lean_unsigned_to_nat(0u);
v_bs_x27_3444_ = lean_array_uset(v_bs_3431_, v_i_3430_, v___x_3443_);
v___x_3445_ = ((size_t)1ULL);
v___x_3446_ = lean_usize_add(v_i_3430_, v___x_3445_);
v___x_3447_ = lean_array_uset(v_bs_x27_3444_, v_i_3430_, v_a_3442_);
v_i_3430_ = v___x_3446_;
v_bs_3431_ = v___x_3447_;
goto _start;
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3451_; uint8_t v_isShared_3452_; uint8_t v_isSharedCheck_3456_; 
lean_dec_ref(v_bs_3431_);
lean_dec_ref(v_post_3425_);
lean_dec_ref(v_pre_3424_);
v_a_3449_ = lean_ctor_get(v___x_3441_, 0);
v_isSharedCheck_3456_ = !lean_is_exclusive(v___x_3441_);
if (v_isSharedCheck_3456_ == 0)
{
v___x_3451_ = v___x_3441_;
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
else
{
lean_inc(v_a_3449_);
lean_dec(v___x_3441_);
v___x_3451_ = lean_box(0);
v_isShared_3452_ = v_isSharedCheck_3456_;
goto v_resetjp_3450_;
}
v_resetjp_3450_:
{
lean_object* v___x_3454_; 
if (v_isShared_3452_ == 0)
{
v___x_3454_ = v___x_3451_;
goto v_reusejp_3453_;
}
else
{
lean_object* v_reuseFailAlloc_3455_; 
v_reuseFailAlloc_3455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3455_, 0, v_a_3449_);
v___x_3454_ = v_reuseFailAlloc_3455_;
goto v_reusejp_3453_;
}
v_reusejp_3453_:
{
return v___x_3454_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0(lean_object* v_pre_3457_, lean_object* v_post_3458_, uint8_t v_usedLetOnly_3459_, uint8_t v_skipConstInApp_3460_, uint8_t v_skipInstances_3461_, lean_object* v___x_3462_, lean_object* v___y_3463_, lean_object* v_b_3464_, lean_object* v_a_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v___x_3471_; 
v___x_3471_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3457_, v_post_3458_, v_usedLetOnly_3459_, v_skipConstInApp_3460_, v_skipInstances_3461_, v___x_3462_, v___y_3463_, v___y_3466_, v___y_3467_, v___y_3468_, v___y_3469_);
if (lean_obj_tag(v___x_3471_) == 0)
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3481_; 
v_a_3472_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3474_ = v___x_3471_;
v_isShared_3475_ = v_isSharedCheck_3481_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3471_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3481_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3476_; lean_object* v___x_3477_; lean_object* v___x_3479_; 
v___x_3476_ = lean_array_fset(v_b_3464_, v_a_3465_, v_a_3472_);
v___x_3477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3477_, 0, v___x_3476_);
if (v_isShared_3475_ == 0)
{
lean_ctor_set(v___x_3474_, 0, v___x_3477_);
v___x_3479_ = v___x_3474_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v___x_3477_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec_ref(v_b_3464_);
v_a_3482_ = lean_ctor_get(v___x_3471_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3471_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3471_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3471_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0___boxed(lean_object* v_pre_3490_, lean_object* v_post_3491_, lean_object* v_usedLetOnly_3492_, lean_object* v_skipConstInApp_3493_, lean_object* v_skipInstances_3494_, lean_object* v___x_3495_, lean_object* v___y_3496_, lean_object* v_b_3497_, lean_object* v_a_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_){
_start:
{
uint8_t v_usedLetOnly_boxed_3504_; uint8_t v_skipConstInApp_boxed_3505_; uint8_t v_skipInstances_boxed_3506_; lean_object* v_res_3507_; 
v_usedLetOnly_boxed_3504_ = lean_unbox(v_usedLetOnly_3492_);
v_skipConstInApp_boxed_3505_ = lean_unbox(v_skipConstInApp_3493_);
v_skipInstances_boxed_3506_ = lean_unbox(v_skipInstances_3494_);
v_res_3507_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0(v_pre_3490_, v_post_3491_, v_usedLetOnly_boxed_3504_, v_skipConstInApp_boxed_3505_, v_skipInstances_boxed_3506_, v___x_3495_, v___y_3496_, v_b_3497_, v_a_3498_, v___y_3499_, v___y_3500_, v___y_3501_, v___y_3502_);
lean_dec(v___y_3502_);
lean_dec_ref(v___y_3501_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v_a_3498_);
lean_dec(v___y_3496_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg(lean_object* v_upperBound_3508_, lean_object* v___x_3509_, lean_object* v_pre_3510_, lean_object* v_post_3511_, uint8_t v_usedLetOnly_3512_, uint8_t v_skipConstInApp_3513_, uint8_t v_skipInstances_3514_, lean_object* v_a_3515_, lean_object* v_b_3516_, lean_object* v___y_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_){
_start:
{
lean_object* v___y_3524_; uint8_t v___x_3547_; 
v___x_3547_ = lean_nat_dec_lt(v_a_3515_, v_upperBound_3508_);
if (v___x_3547_ == 0)
{
lean_object* v___x_3548_; 
lean_dec(v_a_3515_);
lean_dec_ref(v_post_3511_);
lean_dec_ref(v_pre_3510_);
v___x_3548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3548_, 0, v_b_3516_);
return v___x_3548_;
}
else
{
lean_object* v___x_3549_; lean_object* v___x_3550_; uint8_t v___x_3551_; 
v___x_3549_ = lean_array_fget_borrowed(v_b_3516_, v_a_3515_);
v___x_3550_ = lean_array_get_size(v___x_3509_);
v___x_3551_ = lean_nat_dec_lt(v_a_3515_, v___x_3550_);
if (v___x_3551_ == 0)
{
lean_object* v___x_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___f_3555_; 
lean_inc(v___x_3549_);
v___x_3552_ = lean_box(v_usedLetOnly_3512_);
v___x_3553_ = lean_box(v_skipConstInApp_3513_);
v___x_3554_ = lean_box(v_skipInstances_3514_);
lean_inc(v_a_3515_);
lean_inc(v___y_3517_);
lean_inc_ref(v_post_3511_);
lean_inc_ref(v_pre_3510_);
v___f_3555_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3555_, 0, v_pre_3510_);
lean_closure_set(v___f_3555_, 1, v_post_3511_);
lean_closure_set(v___f_3555_, 2, v___x_3552_);
lean_closure_set(v___f_3555_, 3, v___x_3553_);
lean_closure_set(v___f_3555_, 4, v___x_3554_);
lean_closure_set(v___f_3555_, 5, v___x_3549_);
lean_closure_set(v___f_3555_, 6, v___y_3517_);
lean_closure_set(v___f_3555_, 7, v_b_3516_);
lean_closure_set(v___f_3555_, 8, v_a_3515_);
v___y_3524_ = v___f_3555_;
goto v___jp_3523_;
}
else
{
lean_object* v___x_3556_; uint8_t v_isInstance_3557_; 
v___x_3556_ = lean_array_fget_borrowed(v___x_3509_, v_a_3515_);
v_isInstance_3557_ = lean_ctor_get_uint8(v___x_3556_, sizeof(void*)*1 + 4);
if (v_isInstance_3557_ == 0)
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___f_3561_; 
lean_inc(v___x_3549_);
v___x_3558_ = lean_box(v_usedLetOnly_3512_);
v___x_3559_ = lean_box(v_skipConstInApp_3513_);
v___x_3560_ = lean_box(v_skipInstances_3514_);
lean_inc(v_a_3515_);
lean_inc(v___y_3517_);
lean_inc_ref(v_post_3511_);
lean_inc_ref(v_pre_3510_);
v___f_3561_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__0___boxed), 14, 9);
lean_closure_set(v___f_3561_, 0, v_pre_3510_);
lean_closure_set(v___f_3561_, 1, v_post_3511_);
lean_closure_set(v___f_3561_, 2, v___x_3558_);
lean_closure_set(v___f_3561_, 3, v___x_3559_);
lean_closure_set(v___f_3561_, 4, v___x_3560_);
lean_closure_set(v___f_3561_, 5, v___x_3549_);
lean_closure_set(v___f_3561_, 6, v___y_3517_);
lean_closure_set(v___f_3561_, 7, v_b_3516_);
lean_closure_set(v___f_3561_, 8, v_a_3515_);
v___y_3524_ = v___f_3561_;
goto v___jp_3523_;
}
else
{
lean_object* v___x_3562_; lean_object* v___f_3563_; 
v___x_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3562_, 0, v_b_3516_);
v___f_3563_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___lam__2___boxed), 6, 1);
lean_closure_set(v___f_3563_, 0, v___x_3562_);
v___y_3524_ = v___f_3563_;
goto v___jp_3523_;
}
}
}
v___jp_3523_:
{
lean_object* v___x_3525_; 
lean_inc(v___y_3521_);
lean_inc_ref(v___y_3520_);
lean_inc(v___y_3519_);
lean_inc_ref(v___y_3518_);
v___x_3525_ = lean_apply_5(v___y_3524_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_, lean_box(0));
if (lean_obj_tag(v___x_3525_) == 0)
{
lean_object* v_a_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3538_; 
v_a_3526_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3528_ = v___x_3525_;
v_isShared_3529_ = v_isSharedCheck_3538_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_a_3526_);
lean_dec(v___x_3525_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3538_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
if (lean_obj_tag(v_a_3526_) == 0)
{
lean_object* v_a_3530_; lean_object* v___x_3532_; 
lean_dec(v_a_3515_);
lean_dec_ref(v_post_3511_);
lean_dec_ref(v_pre_3510_);
v_a_3530_ = lean_ctor_get(v_a_3526_, 0);
lean_inc(v_a_3530_);
lean_dec_ref(v_a_3526_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 0, v_a_3530_);
v___x_3532_ = v___x_3528_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3530_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
else
{
lean_object* v_a_3534_; lean_object* v___x_3535_; lean_object* v___x_3536_; 
lean_del_object(v___x_3528_);
v_a_3534_ = lean_ctor_get(v_a_3526_, 0);
lean_inc(v_a_3534_);
lean_dec_ref(v_a_3526_);
v___x_3535_ = lean_unsigned_to_nat(1u);
v___x_3536_ = lean_nat_add(v_a_3515_, v___x_3535_);
lean_dec(v_a_3515_);
v_a_3515_ = v___x_3536_;
v_b_3516_ = v_a_3534_;
goto _start;
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_a_3515_);
lean_dec_ref(v_post_3511_);
lean_dec_ref(v_pre_3510_);
v_a_3539_ = lean_ctor_get(v___x_3525_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3525_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3525_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3525_);
v___x_3541_ = lean_box(0);
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
v_resetjp_3540_:
{
lean_object* v___x_3544_; 
if (v_isShared_3542_ == 0)
{
v___x_3544_ = v___x_3541_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_a_3539_);
v___x_3544_ = v_reuseFailAlloc_3545_;
goto v_reusejp_3543_;
}
v_reusejp_3543_:
{
return v___x_3544_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__9(uint8_t v_skipInstances_3564_, lean_object* v_pre_3565_, lean_object* v_post_3566_, uint8_t v_usedLetOnly_3567_, uint8_t v_skipConstInApp_3568_, lean_object* v_x_3569_, lean_object* v_x_3570_, lean_object* v_x_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_){
_start:
{
lean_object* v_f_3579_; lean_object* v___y_3580_; lean_object* v___y_3581_; lean_object* v___y_3582_; lean_object* v___y_3583_; lean_object* v___y_3584_; 
if (lean_obj_tag(v_x_3569_) == 5)
{
lean_object* v_fn_3627_; lean_object* v_arg_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; 
v_fn_3627_ = lean_ctor_get(v_x_3569_, 0);
lean_inc_ref(v_fn_3627_);
v_arg_3628_ = lean_ctor_get(v_x_3569_, 1);
lean_inc_ref(v_arg_3628_);
lean_dec_ref(v_x_3569_);
v___x_3629_ = lean_array_set(v_x_3570_, v_x_3571_, v_arg_3628_);
v___x_3630_ = lean_unsigned_to_nat(1u);
v___x_3631_ = lean_nat_sub(v_x_3571_, v___x_3630_);
lean_dec(v_x_3571_);
v_x_3569_ = v_fn_3627_;
v_x_3570_ = v___x_3629_;
v_x_3571_ = v___x_3631_;
goto _start;
}
else
{
lean_dec(v_x_3571_);
if (v_skipConstInApp_3568_ == 0)
{
goto v___jp_3624_;
}
else
{
uint8_t v___x_3633_; 
v___x_3633_ = l_Lean_Expr_isConst(v_x_3569_);
if (v___x_3633_ == 0)
{
goto v___jp_3624_;
}
else
{
v_f_3579_ = v_x_3569_;
v___y_3580_ = v___y_3572_;
v___y_3581_ = v___y_3573_;
v___y_3582_ = v___y_3574_;
v___y_3583_ = v___y_3575_;
v___y_3584_ = v___y_3576_;
goto v___jp_3578_;
}
}
}
v___jp_3578_:
{
if (v_skipInstances_3564_ == 0)
{
size_t v_sz_3585_; size_t v___x_3586_; lean_object* v___x_3587_; 
v_sz_3585_ = lean_array_size(v_x_3570_);
v___x_3586_ = ((size_t)0ULL);
lean_inc_ref(v_post_3566_);
lean_inc_ref(v_pre_3565_);
v___x_3587_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__3(v_pre_3565_, v_post_3566_, v_usedLetOnly_3567_, v_skipConstInApp_3568_, v_skipInstances_3564_, v_sz_3585_, v___x_3586_, v_x_3570_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
if (lean_obj_tag(v___x_3587_) == 0)
{
lean_object* v_a_3588_; lean_object* v___x_3589_; lean_object* v___x_3590_; 
v_a_3588_ = lean_ctor_get(v___x_3587_, 0);
lean_inc(v_a_3588_);
lean_dec_ref(v___x_3587_);
v___x_3589_ = l_Lean_mkAppN(v_f_3579_, v_a_3588_);
lean_dec(v_a_3588_);
v___x_3590_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3565_, v_post_3566_, v_usedLetOnly_3567_, v_skipConstInApp_3568_, v_skipInstances_3564_, v___x_3589_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
return v___x_3590_;
}
else
{
lean_object* v_a_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3598_; 
lean_dec_ref(v_f_3579_);
lean_dec_ref(v_post_3566_);
lean_dec_ref(v_pre_3565_);
v_a_3591_ = lean_ctor_get(v___x_3587_, 0);
v_isSharedCheck_3598_ = !lean_is_exclusive(v___x_3587_);
if (v_isSharedCheck_3598_ == 0)
{
v___x_3593_ = v___x_3587_;
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_a_3591_);
lean_dec(v___x_3587_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3598_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3596_; 
if (v_isShared_3594_ == 0)
{
v___x_3596_ = v___x_3593_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3591_);
v___x_3596_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
return v___x_3596_;
}
}
}
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = lean_array_get_size(v_x_3570_);
lean_inc_ref(v_f_3579_);
v___x_3600_ = l_Lean_Meta_getFunInfoNArgs(v_f_3579_, v___x_3599_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v_paramInfo_3602_; lean_object* v___x_3603_; lean_object* v___x_3604_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref(v___x_3600_);
v_paramInfo_3602_ = lean_ctor_get(v_a_3601_, 0);
lean_inc_ref(v_paramInfo_3602_);
lean_dec(v_a_3601_);
v___x_3603_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_post_3566_);
lean_inc_ref(v_pre_3565_);
v___x_3604_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg(v___x_3599_, v_paramInfo_3602_, v_pre_3565_, v_post_3566_, v_usedLetOnly_3567_, v_skipConstInApp_3568_, v_skipInstances_3564_, v___x_3603_, v_x_3570_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
lean_dec_ref(v_paramInfo_3602_);
if (lean_obj_tag(v___x_3604_) == 0)
{
lean_object* v_a_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; 
v_a_3605_ = lean_ctor_get(v___x_3604_, 0);
lean_inc(v_a_3605_);
lean_dec_ref(v___x_3604_);
v___x_3606_ = l_Lean_mkAppN(v_f_3579_, v_a_3605_);
lean_dec(v_a_3605_);
v___x_3607_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3565_, v_post_3566_, v_usedLetOnly_3567_, v_skipConstInApp_3568_, v_skipInstances_3564_, v___x_3606_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_, v___y_3584_);
return v___x_3607_;
}
else
{
lean_object* v_a_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3615_; 
lean_dec_ref(v_f_3579_);
lean_dec_ref(v_post_3566_);
lean_dec_ref(v_pre_3565_);
v_a_3608_ = lean_ctor_get(v___x_3604_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3604_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3610_ = v___x_3604_;
v_isShared_3611_ = v_isSharedCheck_3615_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_a_3608_);
lean_dec(v___x_3604_);
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
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_dec_ref(v_f_3579_);
lean_dec_ref(v_x_3570_);
lean_dec_ref(v_post_3566_);
lean_dec_ref(v_pre_3565_);
v_a_3616_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3600_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3600_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
}
v___jp_3624_:
{
lean_object* v___x_3625_; 
lean_inc_ref(v_post_3566_);
lean_inc_ref(v_pre_3565_);
v___x_3625_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3565_, v_post_3566_, v_usedLetOnly_3567_, v_skipConstInApp_3568_, v_skipInstances_3564_, v_x_3569_, v___y_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref(v___x_3625_);
v_f_3579_ = v_a_3626_;
v___y_3580_ = v___y_3572_;
v___y_3581_ = v___y_3573_;
v___y_3582_ = v___y_3574_;
v___y_3583_ = v___y_3575_;
v___y_3584_ = v___y_3576_;
goto v___jp_3578_;
}
else
{
lean_dec_ref(v_x_3570_);
lean_dec_ref(v_post_3566_);
lean_dec_ref(v_pre_3565_);
return v___x_3625_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1(lean_object* v_pre_3634_, lean_object* v_e_3635_, lean_object* v_post_3636_, uint8_t v_usedLetOnly_3637_, uint8_t v_skipConstInApp_3638_, uint8_t v_skipInstances_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_){
_start:
{
lean_object* v___x_3646_; 
lean_inc_ref(v_pre_3634_);
lean_inc(v___y_3644_);
lean_inc_ref(v___y_3643_);
lean_inc(v___y_3642_);
lean_inc_ref(v___y_3641_);
lean_inc_ref(v_e_3635_);
v___x_3646_ = lean_apply_6(v_pre_3634_, v_e_3635_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_, lean_box(0));
if (lean_obj_tag(v___x_3646_) == 0)
{
lean_object* v_a_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3695_; 
v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3695_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_a_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3695_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___y_3652_; 
switch(lean_obj_tag(v_a_3647_))
{
case 0:
{
lean_object* v_e_3687_; lean_object* v___x_3689_; 
lean_dec_ref(v_post_3636_);
lean_dec_ref(v_e_3635_);
lean_dec_ref(v_pre_3634_);
v_e_3687_ = lean_ctor_get(v_a_3647_, 0);
lean_inc_ref(v_e_3687_);
lean_dec_ref(v_a_3647_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set(v___x_3649_, 0, v_e_3687_);
v___x_3689_ = v___x_3649_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v_e_3687_);
v___x_3689_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
return v___x_3689_;
}
}
case 1:
{
lean_object* v_e_3691_; lean_object* v___x_3692_; 
lean_del_object(v___x_3649_);
lean_dec_ref(v_e_3635_);
v_e_3691_ = lean_ctor_get(v_a_3647_, 0);
lean_inc_ref(v_e_3691_);
lean_dec_ref(v_a_3647_);
v___x_3692_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v_e_3691_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3692_;
}
default: 
{
lean_object* v_e_x3f_3693_; 
lean_del_object(v___x_3649_);
v_e_x3f_3693_ = lean_ctor_get(v_a_3647_, 0);
lean_inc(v_e_x3f_3693_);
lean_dec_ref(v_a_3647_);
if (lean_obj_tag(v_e_x3f_3693_) == 0)
{
v___y_3652_ = v_e_3635_;
goto v___jp_3651_;
}
else
{
lean_object* v_val_3694_; 
lean_dec_ref(v_e_3635_);
v_val_3694_ = lean_ctor_get(v_e_x3f_3693_, 0);
lean_inc(v_val_3694_);
lean_dec_ref(v_e_x3f_3693_);
v___y_3652_ = v_val_3694_;
goto v___jp_3651_;
}
}
}
v___jp_3651_:
{
switch(lean_obj_tag(v___y_3652_))
{
case 7:
{
lean_object* v___x_3653_; lean_object* v___x_3654_; 
v___x_3653_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___closed__0));
v___x_3654_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v___x_3653_, v___y_3652_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3654_;
}
case 6:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___closed__0));
v___x_3656_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v___x_3655_, v___y_3652_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3656_;
}
case 8:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; 
v___x_3657_ = ((lean_object*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___closed__0));
v___x_3658_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v___x_3657_, v___y_3652_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3658_;
}
case 5:
{
lean_object* v_dummy_3659_; lean_object* v_nargs_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; 
v_dummy_3659_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_3660_ = l_Lean_Expr_getAppNumArgs(v___y_3652_);
lean_inc(v_nargs_3660_);
v___x_3661_ = lean_mk_array(v_nargs_3660_, v_dummy_3659_);
v___x_3662_ = lean_unsigned_to_nat(1u);
v___x_3663_ = lean_nat_sub(v_nargs_3660_, v___x_3662_);
lean_dec(v_nargs_3660_);
v___x_3664_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__9(v_skipInstances_3639_, v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v___y_3652_, v___x_3661_, v___x_3663_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3664_;
}
case 10:
{
lean_object* v_data_3665_; lean_object* v_expr_3666_; lean_object* v___x_3667_; 
v_data_3665_ = lean_ctor_get(v___y_3652_, 0);
v_expr_3666_ = lean_ctor_get(v___y_3652_, 1);
lean_inc_ref(v_expr_3666_);
lean_inc_ref(v_post_3636_);
lean_inc_ref(v_pre_3634_);
v___x_3667_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v_expr_3666_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; size_t v___x_3669_; size_t v___x_3670_; uint8_t v___x_3671_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref(v___x_3667_);
v___x_3669_ = lean_ptr_addr(v_expr_3666_);
v___x_3670_ = lean_ptr_addr(v_a_3668_);
v___x_3671_ = lean_usize_dec_eq(v___x_3669_, v___x_3670_);
if (v___x_3671_ == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
lean_inc(v_data_3665_);
lean_dec_ref(v___y_3652_);
v___x_3672_ = l_Lean_Expr_mdata___override(v_data_3665_, v_a_3668_);
v___x_3673_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v___x_3672_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3673_;
}
else
{
lean_object* v___x_3674_; 
lean_dec(v_a_3668_);
v___x_3674_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v___y_3652_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3674_;
}
}
else
{
lean_dec_ref(v___y_3652_);
lean_dec_ref(v_post_3636_);
lean_dec_ref(v_pre_3634_);
return v___x_3667_;
}
}
case 11:
{
lean_object* v_typeName_3675_; lean_object* v_idx_3676_; lean_object* v_struct_3677_; lean_object* v___x_3678_; 
v_typeName_3675_ = lean_ctor_get(v___y_3652_, 0);
v_idx_3676_ = lean_ctor_get(v___y_3652_, 1);
v_struct_3677_ = lean_ctor_get(v___y_3652_, 2);
lean_inc_ref(v_struct_3677_);
lean_inc_ref(v_post_3636_);
lean_inc_ref(v_pre_3634_);
v___x_3678_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v_struct_3677_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; size_t v___x_3680_; size_t v___x_3681_; uint8_t v___x_3682_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
lean_inc(v_a_3679_);
lean_dec_ref(v___x_3678_);
v___x_3680_ = lean_ptr_addr(v_struct_3677_);
v___x_3681_ = lean_ptr_addr(v_a_3679_);
v___x_3682_ = lean_usize_dec_eq(v___x_3680_, v___x_3681_);
if (v___x_3682_ == 0)
{
lean_object* v___x_3683_; lean_object* v___x_3684_; 
lean_inc(v_idx_3676_);
lean_inc(v_typeName_3675_);
lean_dec_ref(v___y_3652_);
v___x_3683_ = l_Lean_Expr_proj___override(v_typeName_3675_, v_idx_3676_, v_a_3679_);
v___x_3684_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v___x_3683_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3684_;
}
else
{
lean_object* v___x_3685_; 
lean_dec(v_a_3679_);
v___x_3685_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v___y_3652_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3685_;
}
}
else
{
lean_dec_ref(v___y_3652_);
lean_dec_ref(v_post_3636_);
lean_dec_ref(v_pre_3634_);
return v___x_3678_;
}
}
default: 
{
lean_object* v___x_3686_; 
v___x_3686_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3634_, v_post_3636_, v_usedLetOnly_3637_, v_skipConstInApp_3638_, v_skipInstances_3639_, v___y_3652_, v___y_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
return v___x_3686_;
}
}
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec_ref(v_post_3636_);
lean_dec_ref(v_e_3635_);
lean_dec_ref(v_pre_3634_);
v_a_3696_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3646_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3646_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___boxed(lean_object* v_pre_3704_, lean_object* v_e_3705_, lean_object* v_post_3706_, lean_object* v_usedLetOnly_3707_, lean_object* v_skipConstInApp_3708_, lean_object* v_skipInstances_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_){
_start:
{
uint8_t v_usedLetOnly_boxed_3716_; uint8_t v_skipConstInApp_boxed_3717_; uint8_t v_skipInstances_boxed_3718_; lean_object* v_res_3719_; 
v_usedLetOnly_boxed_3716_ = lean_unbox(v_usedLetOnly_3707_);
v_skipConstInApp_boxed_3717_ = lean_unbox(v_skipConstInApp_3708_);
v_skipInstances_boxed_3718_ = lean_unbox(v_skipInstances_3709_);
v_res_3719_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1(v_pre_3704_, v_e_3705_, v_post_3706_, v_usedLetOnly_boxed_3716_, v_skipConstInApp_boxed_3717_, v_skipInstances_boxed_3718_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
lean_dec(v___y_3714_);
lean_dec_ref(v___y_3713_);
lean_dec(v___y_3712_);
lean_dec_ref(v___y_3711_);
lean_dec(v___y_3710_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(lean_object* v_pre_3720_, lean_object* v_post_3721_, uint8_t v_usedLetOnly_3722_, uint8_t v_skipConstInApp_3723_, uint8_t v_skipInstances_3724_, lean_object* v_e_3725_, lean_object* v_a_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_){
_start:
{
lean_object* v___x_3732_; lean_object* v___x_3733_; 
lean_inc(v_a_3726_);
v___x_3732_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_3732_, 0, lean_box(0));
lean_closure_set(v___x_3732_, 1, lean_box(0));
lean_closure_set(v___x_3732_, 2, v_a_3726_);
v___x_3733_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_box(0), v___x_3732_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3767_; 
v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3736_ = v___x_3733_;
v_isShared_3737_ = v_isSharedCheck_3767_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3733_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3767_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3738_; 
v___x_3738_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_3734_, v_e_3725_);
lean_dec(v_a_3734_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___f_3742_; lean_object* v___x_3743_; 
lean_del_object(v___x_3736_);
v___x_3739_ = lean_box(v_usedLetOnly_3722_);
v___x_3740_ = lean_box(v_skipConstInApp_3723_);
v___x_3741_ = lean_box(v_skipInstances_3724_);
lean_inc_ref(v_e_3725_);
v___f_3742_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__1___boxed), 12, 6);
lean_closure_set(v___f_3742_, 0, v_pre_3720_);
lean_closure_set(v___f_3742_, 1, v_e_3725_);
lean_closure_set(v___f_3742_, 2, v_post_3721_);
lean_closure_set(v___f_3742_, 3, v___x_3739_);
lean_closure_set(v___f_3742_, 4, v___x_3740_);
lean_closure_set(v___f_3742_, 5, v___x_3741_);
v___x_3743_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg(v___f_3742_, v_a_3726_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___f_3745_; lean_object* v___x_3746_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc_n(v_a_3744_, 2);
lean_dec_ref(v___x_3743_);
lean_inc(v_a_3726_);
v___f_3745_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_3745_, 0, v_a_3726_);
lean_closure_set(v___f_3745_, 1, v_e_3725_);
lean_closure_set(v___f_3745_, 2, v_a_3744_);
v___x_3746_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_box(0), v___f_3745_, v___y_3727_, v___y_3728_, v___y_3729_, v___y_3730_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3753_; 
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3753_ == 0)
{
lean_object* v_unused_3754_; 
v_unused_3754_ = lean_ctor_get(v___x_3746_, 0);
lean_dec(v_unused_3754_);
v___x_3748_ = v___x_3746_;
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
else
{
lean_dec(v___x_3746_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3753_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3751_; 
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v_a_3744_);
v___x_3751_ = v___x_3748_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_a_3744_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
lean_dec(v_a_3744_);
v_a_3755_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3746_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3746_);
v___x_3757_ = lean_box(0);
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
v_resetjp_3756_:
{
lean_object* v___x_3760_; 
if (v_isShared_3758_ == 0)
{
v___x_3760_ = v___x_3757_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3761_; 
v_reuseFailAlloc_3761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
v___x_3760_ = v_reuseFailAlloc_3761_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
return v___x_3760_;
}
}
}
}
else
{
lean_dec_ref(v_e_3725_);
return v___x_3743_;
}
}
else
{
lean_object* v_val_3763_; lean_object* v___x_3765_; 
lean_dec_ref(v_e_3725_);
lean_dec_ref(v_post_3721_);
lean_dec_ref(v_pre_3720_);
v_val_3763_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_val_3763_);
lean_dec_ref(v___x_3738_);
if (v_isShared_3737_ == 0)
{
lean_ctor_set(v___x_3736_, 0, v_val_3763_);
v___x_3765_ = v___x_3736_;
goto v_reusejp_3764_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v_val_3763_);
v___x_3765_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3764_;
}
v_reusejp_3764_:
{
return v___x_3765_;
}
}
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v_e_3725_);
lean_dec_ref(v_post_3721_);
lean_dec_ref(v_pre_3720_);
v_a_3768_ = lean_ctor_get(v___x_3733_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3733_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3733_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___lam__0___boxed(lean_object* v_fvars_3776_, lean_object* v_pre_3777_, lean_object* v_post_3778_, lean_object* v_usedLetOnly_3779_, lean_object* v_skipConstInApp_3780_, lean_object* v_skipInstances_3781_, lean_object* v_body_3782_, lean_object* v_x_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_, lean_object* v___y_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_){
_start:
{
uint8_t v_usedLetOnly_boxed_3790_; uint8_t v_skipConstInApp_boxed_3791_; uint8_t v_skipInstances_boxed_3792_; lean_object* v_res_3793_; 
v_usedLetOnly_boxed_3790_ = lean_unbox(v_usedLetOnly_3779_);
v_skipConstInApp_boxed_3791_ = lean_unbox(v_skipConstInApp_3780_);
v_skipInstances_boxed_3792_ = lean_unbox(v_skipInstances_3781_);
v_res_3793_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___lam__0(v_fvars_3776_, v_pre_3777_, v_post_3778_, v_usedLetOnly_boxed_3790_, v_skipConstInApp_boxed_3791_, v_skipInstances_boxed_3792_, v_body_3782_, v_x_3783_, v___y_3784_, v___y_3785_, v___y_3786_, v___y_3787_, v___y_3788_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec(v___y_3786_);
lean_dec_ref(v___y_3785_);
lean_dec(v___y_3784_);
return v_res_3793_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6(lean_object* v_pre_3794_, lean_object* v_post_3795_, uint8_t v_usedLetOnly_3796_, uint8_t v_skipConstInApp_3797_, uint8_t v_skipInstances_3798_, lean_object* v_fvars_3799_, lean_object* v_e_3800_, lean_object* v_a_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_){
_start:
{
if (lean_obj_tag(v_e_3800_) == 7)
{
lean_object* v_binderName_3807_; lean_object* v_binderType_3808_; lean_object* v_body_3809_; uint8_t v_binderInfo_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v_binderName_3807_ = lean_ctor_get(v_e_3800_, 0);
lean_inc(v_binderName_3807_);
v_binderType_3808_ = lean_ctor_get(v_e_3800_, 1);
lean_inc_ref(v_binderType_3808_);
v_body_3809_ = lean_ctor_get(v_e_3800_, 2);
lean_inc_ref(v_body_3809_);
v_binderInfo_3810_ = lean_ctor_get_uint8(v_e_3800_, sizeof(void*)*3 + 8);
lean_dec_ref(v_e_3800_);
v___x_3811_ = lean_expr_instantiate_rev(v_binderType_3808_, v_fvars_3799_);
lean_dec_ref(v_binderType_3808_);
lean_inc_ref(v_post_3795_);
lean_inc_ref(v_pre_3794_);
v___x_3812_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3794_, v_post_3795_, v_usedLetOnly_3796_, v_skipConstInApp_3797_, v_skipInstances_3798_, v___x_3811_, v_a_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___f_3817_; uint8_t v___x_3818_; lean_object* v___x_3819_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref(v___x_3812_);
v___x_3814_ = lean_box(v_usedLetOnly_3796_);
v___x_3815_ = lean_box(v_skipConstInApp_3797_);
v___x_3816_ = lean_box(v_skipInstances_3798_);
v___f_3817_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___lam__0___boxed), 14, 7);
lean_closure_set(v___f_3817_, 0, v_fvars_3799_);
lean_closure_set(v___f_3817_, 1, v_pre_3794_);
lean_closure_set(v___f_3817_, 2, v_post_3795_);
lean_closure_set(v___f_3817_, 3, v___x_3814_);
lean_closure_set(v___f_3817_, 4, v___x_3815_);
lean_closure_set(v___f_3817_, 5, v___x_3816_);
lean_closure_set(v___f_3817_, 6, v_body_3809_);
v___x_3818_ = 0;
v___x_3819_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(v_binderName_3807_, v_binderInfo_3810_, v_a_3813_, v___f_3817_, v___x_3818_, v_a_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
return v___x_3819_;
}
else
{
lean_dec_ref(v_body_3809_);
lean_dec(v_binderName_3807_);
lean_dec_ref(v_fvars_3799_);
lean_dec_ref(v_post_3795_);
lean_dec_ref(v_pre_3794_);
return v___x_3812_;
}
}
else
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = lean_expr_instantiate_rev(v_e_3800_, v_fvars_3799_);
lean_dec_ref(v_e_3800_);
lean_inc_ref(v_post_3795_);
lean_inc_ref(v_pre_3794_);
v___x_3821_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3794_, v_post_3795_, v_usedLetOnly_3796_, v_skipConstInApp_3797_, v_skipInstances_3798_, v___x_3820_, v_a_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; uint8_t v___x_3823_; uint8_t v___x_3824_; uint8_t v___x_3825_; lean_object* v___x_3826_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
lean_inc(v_a_3822_);
lean_dec_ref(v___x_3821_);
v___x_3823_ = 0;
v___x_3824_ = 1;
v___x_3825_ = 1;
v___x_3826_ = l_Lean_Meta_mkForallFVars(v_fvars_3799_, v_a_3822_, v___x_3823_, v_usedLetOnly_3796_, v___x_3824_, v___x_3825_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
lean_dec_ref(v_fvars_3799_);
if (lean_obj_tag(v___x_3826_) == 0)
{
lean_object* v_a_3827_; lean_object* v___x_3828_; 
v_a_3827_ = lean_ctor_get(v___x_3826_, 0);
lean_inc(v_a_3827_);
lean_dec_ref(v___x_3826_);
v___x_3828_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3794_, v_post_3795_, v_usedLetOnly_3796_, v_skipConstInApp_3797_, v_skipInstances_3798_, v_a_3827_, v_a_3801_, v___y_3802_, v___y_3803_, v___y_3804_, v___y_3805_);
return v___x_3828_;
}
else
{
lean_dec_ref(v_post_3795_);
lean_dec_ref(v_pre_3794_);
return v___x_3826_;
}
}
else
{
lean_dec_ref(v_fvars_3799_);
lean_dec_ref(v_post_3795_);
lean_dec_ref(v_pre_3794_);
return v___x_3821_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___lam__0(lean_object* v_fvars_3829_, lean_object* v_pre_3830_, lean_object* v_post_3831_, uint8_t v_usedLetOnly_3832_, uint8_t v_skipConstInApp_3833_, uint8_t v_skipInstances_3834_, lean_object* v_body_3835_, lean_object* v_x_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_){
_start:
{
lean_object* v___x_3843_; lean_object* v___x_3844_; 
v___x_3843_ = lean_array_push(v_fvars_3829_, v_x_3836_);
v___x_3844_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6(v_pre_3830_, v_post_3831_, v_usedLetOnly_3832_, v_skipConstInApp_3833_, v_skipInstances_3834_, v___x_3843_, v_body_3835_, v___y_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
return v___x_3844_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4___boxed(lean_object* v_pre_3845_, lean_object* v_post_3846_, lean_object* v_usedLetOnly_3847_, lean_object* v_skipConstInApp_3848_, lean_object* v_skipInstances_3849_, lean_object* v_e_3850_, lean_object* v_a_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
uint8_t v_usedLetOnly_boxed_3857_; uint8_t v_skipConstInApp_boxed_3858_; uint8_t v_skipInstances_boxed_3859_; lean_object* v_res_3860_; 
v_usedLetOnly_boxed_3857_ = lean_unbox(v_usedLetOnly_3847_);
v_skipConstInApp_boxed_3858_ = lean_unbox(v_skipConstInApp_3848_);
v_skipInstances_boxed_3859_ = lean_unbox(v_skipInstances_3849_);
v_res_3860_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__4(v_pre_3845_, v_post_3846_, v_usedLetOnly_boxed_3857_, v_skipConstInApp_boxed_3858_, v_skipInstances_boxed_3859_, v_e_3850_, v_a_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec(v_a_3851_);
return v_res_3860_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__3___boxed(lean_object* v_pre_3861_, lean_object* v_post_3862_, lean_object* v_usedLetOnly_3863_, lean_object* v_skipConstInApp_3864_, lean_object* v_skipInstances_3865_, lean_object* v_sz_3866_, lean_object* v_i_3867_, lean_object* v_bs_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
uint8_t v_usedLetOnly_boxed_3875_; uint8_t v_skipConstInApp_boxed_3876_; uint8_t v_skipInstances_boxed_3877_; size_t v_sz_boxed_3878_; size_t v_i_boxed_3879_; lean_object* v_res_3880_; 
v_usedLetOnly_boxed_3875_ = lean_unbox(v_usedLetOnly_3863_);
v_skipConstInApp_boxed_3876_ = lean_unbox(v_skipConstInApp_3864_);
v_skipInstances_boxed_3877_ = lean_unbox(v_skipInstances_3865_);
v_sz_boxed_3878_ = lean_unbox_usize(v_sz_3866_);
lean_dec(v_sz_3866_);
v_i_boxed_3879_ = lean_unbox_usize(v_i_3867_);
lean_dec(v_i_3867_);
v_res_3880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__3(v_pre_3861_, v_post_3862_, v_usedLetOnly_boxed_3875_, v_skipConstInApp_boxed_3876_, v_skipInstances_boxed_3877_, v_sz_boxed_3878_, v_i_boxed_3879_, v_bs_3868_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec(v___y_3869_);
return v_res_3880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___boxed(lean_object* v_pre_3881_, lean_object* v_post_3882_, lean_object* v_usedLetOnly_3883_, lean_object* v_skipConstInApp_3884_, lean_object* v_skipInstances_3885_, lean_object* v_e_3886_, lean_object* v_a_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
uint8_t v_usedLetOnly_boxed_3893_; uint8_t v_skipConstInApp_boxed_3894_; uint8_t v_skipInstances_boxed_3895_; lean_object* v_res_3896_; 
v_usedLetOnly_boxed_3893_ = lean_unbox(v_usedLetOnly_3883_);
v_skipConstInApp_boxed_3894_ = lean_unbox(v_skipConstInApp_3884_);
v_skipInstances_boxed_3895_ = lean_unbox(v_skipInstances_3885_);
v_res_3896_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_3881_, v_post_3882_, v_usedLetOnly_boxed_3893_, v_skipConstInApp_boxed_3894_, v_skipInstances_boxed_3895_, v_e_3886_, v_a_3887_, v___y_3888_, v___y_3889_, v___y_3890_, v___y_3891_);
lean_dec(v___y_3891_);
lean_dec_ref(v___y_3890_);
lean_dec(v___y_3889_);
lean_dec_ref(v___y_3888_);
lean_dec(v_a_3887_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6___boxed(lean_object* v_pre_3897_, lean_object* v_post_3898_, lean_object* v_usedLetOnly_3899_, lean_object* v_skipConstInApp_3900_, lean_object* v_skipInstances_3901_, lean_object* v_fvars_3902_, lean_object* v_e_3903_, lean_object* v_a_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_){
_start:
{
uint8_t v_usedLetOnly_boxed_3910_; uint8_t v_skipConstInApp_boxed_3911_; uint8_t v_skipInstances_boxed_3912_; lean_object* v_res_3913_; 
v_usedLetOnly_boxed_3910_ = lean_unbox(v_usedLetOnly_3899_);
v_skipConstInApp_boxed_3911_ = lean_unbox(v_skipConstInApp_3900_);
v_skipInstances_boxed_3912_ = lean_unbox(v_skipInstances_3901_);
v_res_3913_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6(v_pre_3897_, v_post_3898_, v_usedLetOnly_boxed_3910_, v_skipConstInApp_boxed_3911_, v_skipInstances_boxed_3912_, v_fvars_3902_, v_e_3903_, v_a_3904_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec(v___y_3906_);
lean_dec_ref(v___y_3905_);
lean_dec(v_a_3904_);
return v_res_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7___boxed(lean_object* v_pre_3914_, lean_object* v_post_3915_, lean_object* v_usedLetOnly_3916_, lean_object* v_skipConstInApp_3917_, lean_object* v_skipInstances_3918_, lean_object* v_fvars_3919_, lean_object* v_e_3920_, lean_object* v_a_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_, lean_object* v___y_3926_){
_start:
{
uint8_t v_usedLetOnly_boxed_3927_; uint8_t v_skipConstInApp_boxed_3928_; uint8_t v_skipInstances_boxed_3929_; lean_object* v_res_3930_; 
v_usedLetOnly_boxed_3927_ = lean_unbox(v_usedLetOnly_3916_);
v_skipConstInApp_boxed_3928_ = lean_unbox(v_skipConstInApp_3917_);
v_skipInstances_boxed_3929_ = lean_unbox(v_skipInstances_3918_);
v_res_3930_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLambda___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__7(v_pre_3914_, v_post_3915_, v_usedLetOnly_boxed_3927_, v_skipConstInApp_boxed_3928_, v_skipInstances_boxed_3929_, v_fvars_3919_, v_e_3920_, v_a_3921_, v___y_3922_, v___y_3923_, v___y_3924_, v___y_3925_);
lean_dec(v___y_3925_);
lean_dec_ref(v___y_3924_);
lean_dec(v___y_3923_);
lean_dec_ref(v___y_3922_);
lean_dec(v_a_3921_);
return v_res_3930_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8___boxed(lean_object* v_pre_3931_, lean_object* v_post_3932_, lean_object* v_usedLetOnly_3933_, lean_object* v_skipConstInApp_3934_, lean_object* v_skipInstances_3935_, lean_object* v_fvars_3936_, lean_object* v_e_3937_, lean_object* v_a_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
uint8_t v_usedLetOnly_boxed_3944_; uint8_t v_skipConstInApp_boxed_3945_; uint8_t v_skipInstances_boxed_3946_; lean_object* v_res_3947_; 
v_usedLetOnly_boxed_3944_ = lean_unbox(v_usedLetOnly_3933_);
v_skipConstInApp_boxed_3945_ = lean_unbox(v_skipConstInApp_3934_);
v_skipInstances_boxed_3946_ = lean_unbox(v_skipInstances_3935_);
v_res_3947_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8(v_pre_3931_, v_post_3932_, v_usedLetOnly_boxed_3944_, v_skipConstInApp_boxed_3945_, v_skipInstances_boxed_3946_, v_fvars_3936_, v_e_3937_, v_a_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec(v_a_3938_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_upperBound_3948_, lean_object* v___x_3949_, lean_object* v_pre_3950_, lean_object* v_post_3951_, lean_object* v_usedLetOnly_3952_, lean_object* v_skipConstInApp_3953_, lean_object* v_skipInstances_3954_, lean_object* v_a_3955_, lean_object* v_b_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_, lean_object* v___y_3961_, lean_object* v___y_3962_){
_start:
{
uint8_t v_usedLetOnly_boxed_3963_; uint8_t v_skipConstInApp_boxed_3964_; uint8_t v_skipInstances_boxed_3965_; lean_object* v_res_3966_; 
v_usedLetOnly_boxed_3963_ = lean_unbox(v_usedLetOnly_3952_);
v_skipConstInApp_boxed_3964_ = lean_unbox(v_skipConstInApp_3953_);
v_skipInstances_boxed_3965_ = lean_unbox(v_skipInstances_3954_);
v_res_3966_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg(v_upperBound_3948_, v___x_3949_, v_pre_3950_, v_post_3951_, v_usedLetOnly_boxed_3963_, v_skipConstInApp_boxed_3964_, v_skipInstances_boxed_3965_, v_a_3955_, v_b_3956_, v___y_3957_, v___y_3958_, v___y_3959_, v___y_3960_, v___y_3961_);
lean_dec(v___y_3961_);
lean_dec_ref(v___y_3960_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___x_3949_);
lean_dec(v_upperBound_3948_);
return v_res_3966_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__9___boxed(lean_object* v_skipInstances_3967_, lean_object* v_pre_3968_, lean_object* v_post_3969_, lean_object* v_usedLetOnly_3970_, lean_object* v_skipConstInApp_3971_, lean_object* v_x_3972_, lean_object* v_x_3973_, lean_object* v_x_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_){
_start:
{
uint8_t v_skipInstances_boxed_3981_; uint8_t v_usedLetOnly_boxed_3982_; uint8_t v_skipConstInApp_boxed_3983_; lean_object* v_res_3984_; 
v_skipInstances_boxed_3981_ = lean_unbox(v_skipInstances_3967_);
v_usedLetOnly_boxed_3982_ = lean_unbox(v_usedLetOnly_3970_);
v_skipConstInApp_boxed_3983_ = lean_unbox(v_skipConstInApp_3971_);
v_res_3984_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__9(v_skipInstances_boxed_3981_, v_pre_3968_, v_post_3969_, v_usedLetOnly_boxed_3982_, v_skipConstInApp_boxed_3983_, v_x_3972_, v_x_3973_, v_x_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
lean_dec(v___y_3977_);
lean_dec_ref(v___y_3976_);
lean_dec(v___y_3975_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_object* v_00_u03b1_3985_, lean_object* v_x_3986_, lean_object* v___y_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_){
_start:
{
lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3992_ = lean_apply_1(v_x_3986_, lean_box(0));
v___x_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0___boxed(lean_object* v_00_u03b1_3994_, lean_object* v_x_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_){
_start:
{
lean_object* v_res_4001_; 
v_res_4001_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(v_00_u03b1_3994_, v_x_3995_, v___y_3996_, v___y_3997_, v___y_3998_, v___y_3999_);
lean_dec(v___y_3999_);
lean_dec_ref(v___y_3998_);
lean_dec(v___y_3997_);
lean_dec_ref(v___y_3996_);
return v_res_4001_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1(lean_object* v_input_4002_, lean_object* v_pre_4003_, lean_object* v_post_4004_, uint8_t v_usedLetOnly_4005_, uint8_t v_skipConstInApp_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v_a_4014_; uint8_t v___x_4015_; lean_object* v___x_4016_; 
v___x_4012_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_4013_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_box(0), v___x_4012_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4014_);
lean_dec_ref(v___x_4013_);
v___x_4015_ = 0;
v___x_4016_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2(v_pre_4003_, v_post_4004_, v_usedLetOnly_4005_, v_skipConstInApp_4006_, v___x_4015_, v_input_4002_, v_a_4014_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v___x_4018_; lean_object* v___x_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4026_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
lean_inc(v_a_4017_);
lean_dec_ref(v___x_4016_);
v___x_4018_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4018_, 0, lean_box(0));
lean_closure_set(v___x_4018_, 1, lean_box(0));
lean_closure_set(v___x_4018_, 2, v_a_4014_);
v___x_4019_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_box(0), v___x_4018_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
v_isSharedCheck_4026_ = !lean_is_exclusive(v___x_4019_);
if (v_isSharedCheck_4026_ == 0)
{
lean_object* v_unused_4027_; 
v_unused_4027_ = lean_ctor_get(v___x_4019_, 0);
lean_dec(v_unused_4027_);
v___x_4021_ = v___x_4019_;
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
else
{
lean_dec(v___x_4019_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4026_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
lean_object* v___x_4024_; 
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v_a_4017_);
v___x_4024_ = v___x_4021_;
goto v_reusejp_4023_;
}
else
{
lean_object* v_reuseFailAlloc_4025_; 
v_reuseFailAlloc_4025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4025_, 0, v_a_4017_);
v___x_4024_ = v_reuseFailAlloc_4025_;
goto v_reusejp_4023_;
}
v_reusejp_4023_:
{
return v___x_4024_;
}
}
}
else
{
lean_dec(v_a_4014_);
return v___x_4016_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___boxed(lean_object* v_input_4028_, lean_object* v_pre_4029_, lean_object* v_post_4030_, lean_object* v_usedLetOnly_4031_, lean_object* v_skipConstInApp_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_){
_start:
{
uint8_t v_usedLetOnly_boxed_4038_; uint8_t v_skipConstInApp_boxed_4039_; lean_object* v_res_4040_; 
v_usedLetOnly_boxed_4038_ = lean_unbox(v_usedLetOnly_4031_);
v_skipConstInApp_boxed_4039_ = lean_unbox(v_skipConstInApp_4032_);
v_res_4040_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1(v_input_4028_, v_pre_4029_, v_post_4030_, v_usedLetOnly_boxed_4038_, v_skipConstInApp_boxed_4039_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
lean_dec(v___y_4036_);
lean_dec_ref(v___y_4035_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
return v_res_4040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs(lean_object* v_e_4044_, lean_object* v_a_4045_, lean_object* v_a_4046_, lean_object* v_a_4047_, lean_object* v_a_4048_){
_start:
{
lean_object* v___f_4050_; lean_object* v___x_4051_; 
v___f_4050_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__0));
v___x_4051_ = lean_find_expr(v___f_4050_, v_e_4044_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v___x_4052_; 
v___x_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4052_, 0, v_e_4044_);
return v___x_4052_;
}
else
{
lean_object* v_post_4053_; lean_object* v___f_4054_; uint8_t v___x_4055_; lean_object* v___x_4056_; 
lean_dec_ref(v___x_4051_);
v_post_4053_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__1));
v___f_4054_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___closed__2));
v___x_4055_ = 0;
v___x_4056_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1(v_e_4044_, v___f_4054_, v_post_4053_, v___x_4055_, v___x_4055_, v_a_4045_, v_a_4046_, v_a_4047_, v_a_4048_);
return v___x_4056_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_foldProjs___boxed(lean_object* v_e_4057_, lean_object* v_a_4058_, lean_object* v_a_4059_, lean_object* v_a_4060_, lean_object* v_a_4061_, lean_object* v_a_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Lean_Meta_Grind_foldProjs(v_e_4057_, v_a_4058_, v_a_4059_, v_a_4060_, v_a_4061_);
lean_dec(v_a_4061_);
lean_dec_ref(v_a_4060_);
lean_dec(v_a_4059_);
lean_dec_ref(v_a_4058_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5(lean_object* v_upperBound_4064_, lean_object* v___x_4065_, lean_object* v_pre_4066_, lean_object* v_post_4067_, uint8_t v_usedLetOnly_4068_, uint8_t v_skipConstInApp_4069_, uint8_t v_skipInstances_4070_, lean_object* v___x_4071_, lean_object* v_inst_4072_, lean_object* v_R_4073_, lean_object* v_a_4074_, lean_object* v_b_4075_, lean_object* v_c_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_){
_start:
{
lean_object* v___x_4083_; 
v___x_4083_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___redArg(v_upperBound_4064_, v___x_4065_, v_pre_4066_, v_post_4067_, v_usedLetOnly_4068_, v_skipConstInApp_4069_, v_skipInstances_4070_, v_a_4074_, v_b_4075_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
return v___x_4083_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5___boxed(lean_object** _args){
lean_object* v_upperBound_4084_ = _args[0];
lean_object* v___x_4085_ = _args[1];
lean_object* v_pre_4086_ = _args[2];
lean_object* v_post_4087_ = _args[3];
lean_object* v_usedLetOnly_4088_ = _args[4];
lean_object* v_skipConstInApp_4089_ = _args[5];
lean_object* v_skipInstances_4090_ = _args[6];
lean_object* v___x_4091_ = _args[7];
lean_object* v_inst_4092_ = _args[8];
lean_object* v_R_4093_ = _args[9];
lean_object* v_a_4094_ = _args[10];
lean_object* v_b_4095_ = _args[11];
lean_object* v_c_4096_ = _args[12];
lean_object* v___y_4097_ = _args[13];
lean_object* v___y_4098_ = _args[14];
lean_object* v___y_4099_ = _args[15];
lean_object* v___y_4100_ = _args[16];
lean_object* v___y_4101_ = _args[17];
lean_object* v___y_4102_ = _args[18];
_start:
{
uint8_t v_usedLetOnly_boxed_4103_; uint8_t v_skipConstInApp_boxed_4104_; uint8_t v_skipInstances_boxed_4105_; lean_object* v_res_4106_; 
v_usedLetOnly_boxed_4103_ = lean_unbox(v_usedLetOnly_4088_);
v_skipConstInApp_boxed_4104_ = lean_unbox(v_skipConstInApp_4089_);
v_skipInstances_boxed_4105_ = lean_unbox(v_skipInstances_4090_);
v_res_4106_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__5(v_upperBound_4084_, v___x_4085_, v_pre_4086_, v_post_4087_, v_usedLetOnly_boxed_4103_, v_skipConstInApp_boxed_4104_, v_skipInstances_boxed_4105_, v___x_4091_, v_inst_4092_, v_R_4093_, v_a_4094_, v_b_4095_, v_c_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_);
lean_dec(v___y_4101_);
lean_dec_ref(v___y_4100_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec(v___x_4091_);
lean_dec_ref(v___x_4085_);
lean_dec(v_upperBound_4084_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7(lean_object* v_00_u03b1_4107_, lean_object* v_name_4108_, uint8_t v_bi_4109_, lean_object* v_type_4110_, lean_object* v_k_4111_, uint8_t v_kind_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_, lean_object* v___y_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_){
_start:
{
lean_object* v___x_4119_; 
v___x_4119_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___redArg(v_name_4108_, v_bi_4109_, v_type_4110_, v_k_4111_, v_kind_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_, v___y_4117_);
return v___x_4119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4120_, lean_object* v_name_4121_, lean_object* v_bi_4122_, lean_object* v_type_4123_, lean_object* v_k_4124_, lean_object* v_kind_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
uint8_t v_bi_boxed_4132_; uint8_t v_kind_boxed_4133_; lean_object* v_res_4134_; 
v_bi_boxed_4132_ = lean_unbox(v_bi_4122_);
v_kind_boxed_4133_ = lean_unbox(v_kind_4125_);
v_res_4134_ = l_Lean_Meta_withLocalDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitForall___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__6_spec__7(v_00_u03b1_4120_, v_name_4121_, v_bi_boxed_4132_, v_type_4123_, v_k_4124_, v_kind_boxed_4133_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
lean_dec(v___y_4126_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10(lean_object* v_00_u03b1_4135_, lean_object* v_name_4136_, lean_object* v_type_4137_, lean_object* v_val_4138_, lean_object* v_k_4139_, uint8_t v_nondep_4140_, uint8_t v_kind_4141_, lean_object* v___y_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_){
_start:
{
lean_object* v___x_4148_; 
v___x_4148_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___redArg(v_name_4136_, v_type_4137_, v_val_4138_, v_k_4139_, v_nondep_4140_, v_kind_4141_, v___y_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
return v___x_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4149_, lean_object* v_name_4150_, lean_object* v_type_4151_, lean_object* v_val_4152_, lean_object* v_k_4153_, lean_object* v_nondep_4154_, lean_object* v_kind_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
uint8_t v_nondep_boxed_4162_; uint8_t v_kind_boxed_4163_; lean_object* v_res_4164_; 
v_nondep_boxed_4162_ = lean_unbox(v_nondep_4154_);
v_kind_boxed_4163_ = lean_unbox(v_kind_4155_);
v_res_4164_ = l_Lean_Meta_withLetDecl___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit_visitLet___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__8_spec__10(v_00_u03b1_4149_, v_name_4150_, v_type_4151_, v_val_4152_, v_k_4153_, v_nondep_boxed_4162_, v_kind_boxed_4163_, v___y_4156_, v___y_4157_, v___y_4158_, v___y_4159_, v___y_4160_);
lean_dec(v___y_4160_);
lean_dec_ref(v___y_4159_);
lean_dec(v___y_4158_);
lean_dec_ref(v___y_4157_);
lean_dec(v___y_4156_);
return v_res_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13(lean_object* v_00_u03b1_4165_, lean_object* v_ref_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_){
_start:
{
lean_object* v___x_4172_; 
v___x_4172_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___redArg(v_ref_4166_);
return v___x_4172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13___boxed(lean_object* v_00_u03b1_4173_, lean_object* v_ref_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10_spec__13(v_00_u03b1_4173_, v_ref_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10(lean_object* v_00_u03b1_4181_, lean_object* v_x_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; 
v___x_4189_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___redArg(v_x_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10___boxed(lean_object* v_00_u03b1_4190_, lean_object* v_x_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_Meta_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2_spec__10(v_00_u03b1_4190_, v_x_4191_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec(v___y_4192_);
return v_res_4198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_normalize___boxed(lean_object* v_e_4206_, lean_object* v_config_4207_, lean_object* v_a_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_00___x40___internal___hyg_4212_){
_start:
{
lean_object* v_res_4213_; 
v_res_4213_ = lean_grind_normalize(v_e_4206_, v_config_4207_, v_a_4208_, v_a_4209_, v_a_4210_, v_a_4211_);
return v_res_4213_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4(void){
_start:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; 
v___x_4221_ = lean_box(0);
v___x_4222_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_4223_ = l_Lean_mkConst(v___x_4222_, v___x_4221_);
return v___x_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsMatchCond(lean_object* v_e_4224_){
_start:
{
lean_object* v___x_4225_; lean_object* v___x_4226_; 
v___x_4225_ = lean_obj_once(&l_Lean_Meta_Grind_markAsMatchCond___closed__4, &l_Lean_Meta_Grind_markAsMatchCond___closed__4_once, _init_l_Lean_Meta_Grind_markAsMatchCond___closed__4);
v___x_4226_ = l_Lean_Expr_app___override(v___x_4225_, v_e_4224_);
return v___x_4226_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isMatchCond(lean_object* v_e_4227_){
_start:
{
lean_object* v___x_4228_; lean_object* v___x_4229_; uint8_t v___x_4230_; 
v___x_4228_ = ((lean_object*)(l_Lean_Meta_Grind_markAsMatchCond___closed__3));
v___x_4229_ = lean_unsigned_to_nat(1u);
v___x_4230_ = l_Lean_Expr_isAppOfArity(v_e_4227_, v___x_4228_, v___x_4229_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isMatchCond___boxed(lean_object* v_e_4231_){
_start:
{
uint8_t v_res_4232_; lean_object* v_r_4233_; 
v_res_4232_ = l_Lean_Meta_Grind_isMatchCond(v_e_4231_);
lean_dec_ref(v_e_4231_);
v_r_4233_ = lean_box(v_res_4232_);
return v_r_4233_;
}
}
static lean_object* _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2(void){
_start:
{
lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4239_ = lean_box(0);
v___x_4240_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4241_ = l_Lean_mkConst(v___x_4240_, v___x_4239_);
return v___x_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object* v_e_4242_){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4243_ = lean_obj_once(&l_Lean_Meta_Grind_markAsPreMatchCond___closed__2, &l_Lean_Meta_Grind_markAsPreMatchCond___closed__2_once, _init_l_Lean_Meta_Grind_markAsPreMatchCond___closed__2);
v___x_4244_ = l_Lean_Expr_app___override(v___x_4243_, v_e_4242_);
return v___x_4244_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPreMatchCond(lean_object* v_e_4245_){
_start:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; uint8_t v___x_4248_; 
v___x_4246_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4247_ = lean_unsigned_to_nat(1u);
v___x_4248_ = l_Lean_Expr_isAppOfArity(v_e_4245_, v___x_4246_, v___x_4247_);
return v___x_4248_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPreMatchCond___boxed(lean_object* v_e_4249_){
_start:
{
uint8_t v_res_4250_; lean_object* v_r_4251_; 
v_res_4250_ = l_Lean_Meta_Grind_isPreMatchCond(v_e_4249_);
lean_dec_ref(v_e_4249_);
v_r_4251_ = lean_box(v_res_4250_);
return v_r_4251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg(lean_object* v_e_4252_, lean_object* v_a_4253_){
_start:
{
lean_object* v___x_4255_; 
lean_inc_ref(v_e_4252_);
v___x_4255_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4252_, v_a_4253_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; lean_object* v___x_4258_; uint8_t v_isShared_4259_; uint8_t v_isSharedCheck_4272_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4272_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4272_ == 0)
{
v___x_4258_ = v___x_4255_;
v_isShared_4259_ = v_isSharedCheck_4272_;
goto v_resetjp_4257_;
}
else
{
lean_inc(v_a_4256_);
lean_dec(v___x_4255_);
v___x_4258_ = lean_box(0);
v_isShared_4259_ = v_isSharedCheck_4272_;
goto v_resetjp_4257_;
}
v_resetjp_4257_:
{
lean_object* v___x_4265_; uint8_t v___x_4266_; 
v___x_4265_ = l_Lean_Expr_cleanupAnnotations(v_a_4256_);
v___x_4266_ = l_Lean_Expr_isApp(v___x_4265_);
if (v___x_4266_ == 0)
{
lean_dec_ref(v___x_4265_);
lean_dec_ref(v_e_4252_);
goto v___jp_4260_;
}
else
{
lean_object* v___x_4267_; lean_object* v___x_4268_; uint8_t v___x_4269_; 
v___x_4267_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4265_);
v___x_4268_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4269_ = l_Lean_Expr_isConstOf(v___x_4267_, v___x_4268_);
lean_dec_ref(v___x_4267_);
if (v___x_4269_ == 0)
{
lean_dec_ref(v_e_4252_);
goto v___jp_4260_;
}
else
{
lean_object* v___x_4270_; lean_object* v___x_4271_; 
lean_del_object(v___x_4258_);
v___x_4270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4270_, 0, v_e_4252_);
v___x_4271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4271_, 0, v___x_4270_);
return v___x_4271_;
}
}
v___jp_4260_:
{
lean_object* v___x_4261_; lean_object* v___x_4263_; 
v___x_4261_ = ((lean_object*)(l_Lean_Meta_Grind_foldProjs___lam__1___closed__0));
if (v_isShared_4259_ == 0)
{
lean_ctor_set(v___x_4258_, 0, v___x_4261_);
v___x_4263_ = v___x_4258_;
goto v_reusejp_4262_;
}
else
{
lean_object* v_reuseFailAlloc_4264_; 
v_reuseFailAlloc_4264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4264_, 0, v___x_4261_);
v___x_4263_ = v_reuseFailAlloc_4264_;
goto v_reusejp_4262_;
}
v_reusejp_4262_:
{
return v___x_4263_;
}
}
}
}
else
{
lean_object* v_a_4273_; lean_object* v___x_4275_; uint8_t v_isShared_4276_; uint8_t v_isSharedCheck_4280_; 
lean_dec_ref(v_e_4252_);
v_a_4273_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4280_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4280_ == 0)
{
v___x_4275_ = v___x_4255_;
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
else
{
lean_inc(v_a_4273_);
lean_dec(v___x_4255_);
v___x_4275_ = lean_box(0);
v_isShared_4276_ = v_isSharedCheck_4280_;
goto v_resetjp_4274_;
}
v_resetjp_4274_:
{
lean_object* v___x_4278_; 
if (v_isShared_4276_ == 0)
{
v___x_4278_ = v___x_4275_;
goto v_reusejp_4277_;
}
else
{
lean_object* v_reuseFailAlloc_4279_; 
v_reuseFailAlloc_4279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4279_, 0, v_a_4273_);
v___x_4278_ = v_reuseFailAlloc_4279_;
goto v_reusejp_4277_;
}
v_reusejp_4277_:
{
return v___x_4278_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___redArg___boxed(lean_object* v_e_4281_, lean_object* v_a_4282_, lean_object* v_a_4283_){
_start:
{
lean_object* v_res_4284_; 
v_res_4284_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_4281_, v_a_4282_);
lean_dec(v_a_4282_);
return v_res_4284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond(lean_object* v_e_4285_, lean_object* v_a_4286_, lean_object* v_a_4287_, lean_object* v_a_4288_, lean_object* v_a_4289_, lean_object* v_a_4290_, lean_object* v_a_4291_, lean_object* v_a_4292_){
_start:
{
lean_object* v___x_4294_; 
v___x_4294_ = l_Lean_Meta_Grind_reducePreMatchCond___redArg(v_e_4285_, v_a_4290_);
return v___x_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_reducePreMatchCond___boxed(lean_object* v_e_4295_, lean_object* v_a_4296_, lean_object* v_a_4297_, lean_object* v_a_4298_, lean_object* v_a_4299_, lean_object* v_a_4300_, lean_object* v_a_4301_, lean_object* v_a_4302_, lean_object* v_a_4303_){
_start:
{
lean_object* v_res_4304_; 
v_res_4304_ = l_Lean_Meta_Grind_reducePreMatchCond(v_e_4295_, v_a_4296_, v_a_4297_, v_a_4298_, v_a_4299_, v_a_4300_, v_a_4301_, v_a_4302_);
lean_dec(v_a_4302_);
lean_dec_ref(v_a_4301_);
lean_dec(v_a_4300_);
lean_dec_ref(v_a_4299_);
lean_dec(v_a_4298_);
lean_dec_ref(v_a_4297_);
lean_dec(v_a_4296_);
return v_res_4304_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_(){
_start:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; lean_object* v___x_4325_; 
v___x_4322_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4323_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__4_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4324_ = lean_alloc_closure((void*)(l_Lean_Meta_Grind_reducePreMatchCond___boxed), 9, 0);
v___x_4325_ = l_Lean_Meta_Simp_registerBuiltinDSimproc(v___x_4322_, v___x_4323_, v___x_4324_);
return v___x_4325_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10____boxed(lean_object* v_a_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_();
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc(lean_object* v_s_4328_, lean_object* v_a_4329_, lean_object* v_a_4330_){
_start:
{
lean_object* v___x_4332_; uint8_t v___x_4333_; lean_object* v___x_4334_; 
v___x_4332_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Grind_Util_0____regBuiltin_Lean_Meta_Grind_reducePreMatchCond_declare__50___closed__2_00___x40_Lean_Meta_Tactic_Grind_Util_2249970803____hygCtx___hyg_10_));
v___x_4333_ = 0;
v___x_4334_ = l_Lean_Meta_Simp_Simprocs_add(v_s_4328_, v___x_4332_, v___x_4333_, v_a_4329_, v_a_4330_);
return v___x_4334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addPreMatchCondSimproc___boxed(lean_object* v_s_4335_, lean_object* v_a_4336_, lean_object* v_a_4337_, lean_object* v_a_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_Lean_Meta_Grind_addPreMatchCondSimproc(v_s_4335_, v_a_4336_, v_a_4337_);
lean_dec(v_a_4337_);
lean_dec_ref(v_a_4336_);
return v_res_4339_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0(lean_object* v_e_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v___x_4350_; uint8_t v___x_4351_; 
lean_inc_ref(v_e_4340_);
v___x_4350_ = l_Lean_Expr_cleanupAnnotations(v_e_4340_);
v___x_4351_ = l_Lean_Expr_isApp(v___x_4350_);
if (v___x_4351_ == 0)
{
lean_dec_ref(v___x_4350_);
goto v___jp_4346_;
}
else
{
lean_object* v_arg_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; uint8_t v___x_4355_; 
v_arg_4352_ = lean_ctor_get(v___x_4350_, 1);
lean_inc_ref(v_arg_4352_);
v___x_4353_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4350_);
v___x_4354_ = ((lean_object*)(l_Lean_Meta_Grind_markAsPreMatchCond___closed__1));
v___x_4355_ = l_Lean_Expr_isConstOf(v___x_4353_, v___x_4354_);
lean_dec_ref(v___x_4353_);
if (v___x_4355_ == 0)
{
lean_dec_ref(v_arg_4352_);
goto v___jp_4346_;
}
else
{
lean_object* v___x_4356_; lean_object* v___x_4357_; lean_object* v___x_4358_; lean_object* v___x_4359_; 
lean_dec_ref(v_e_4340_);
v___x_4356_ = l_Lean_Meta_Grind_markAsMatchCond(v_arg_4352_);
v___x_4357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4357_, 0, v___x_4356_);
v___x_4358_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4358_, 0, v___x_4357_);
v___x_4359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4359_, 0, v___x_4358_);
return v___x_4359_;
}
}
v___jp_4346_:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4347_, 0, v_e_4340_);
v___x_4348_ = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4347_);
v___x_4349_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4349_, 0, v___x_4348_);
return v___x_4349_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__0___boxed(lean_object* v_e_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v_res_4366_; 
v_res_4366_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__0(v_e_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_);
lean_dec(v___y_4364_);
lean_dec_ref(v___y_4363_);
lean_dec(v___y_4362_);
lean_dec_ref(v___y_4361_);
return v_res_4366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1(lean_object* v_e_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_, lean_object* v___y_4371_){
_start:
{
lean_object* v___x_4373_; lean_object* v___x_4374_; 
v___x_4373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4373_, 0, v_e_4367_);
v___x_4374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4374_, 0, v___x_4373_);
return v___x_4374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___lam__1___boxed(lean_object* v_e_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_, lean_object* v___y_4378_, lean_object* v___y_4379_, lean_object* v___y_4380_){
_start:
{
lean_object* v_res_4381_; 
v_res_4381_ = l_Lean_Meta_Grind_replacePreMatchCond___lam__1(v_e_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_);
lean_dec(v___y_4379_);
lean_dec_ref(v___y_4378_);
lean_dec(v___y_4377_);
lean_dec_ref(v___y_4376_);
return v_res_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(lean_object* v_x_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_){
_start:
{
lean_object* v___y_4390_; lean_object* v_fileName_4399_; lean_object* v_fileMap_4400_; lean_object* v_options_4401_; lean_object* v_currRecDepth_4402_; lean_object* v_maxRecDepth_4403_; lean_object* v_ref_4404_; lean_object* v_currNamespace_4405_; lean_object* v_openDecls_4406_; lean_object* v_initHeartbeats_4407_; lean_object* v_maxHeartbeats_4408_; lean_object* v_quotContext_4409_; lean_object* v_currMacroScope_4410_; uint8_t v_diag_4411_; lean_object* v_cancelTk_x3f_4412_; uint8_t v_suppressElabErrors_4413_; lean_object* v_inheritedTraceOptions_4414_; uint8_t v___x_4415_; 
v_fileName_4399_ = lean_ctor_get(v___y_4386_, 0);
v_fileMap_4400_ = lean_ctor_get(v___y_4386_, 1);
v_options_4401_ = lean_ctor_get(v___y_4386_, 2);
v_currRecDepth_4402_ = lean_ctor_get(v___y_4386_, 3);
v_maxRecDepth_4403_ = lean_ctor_get(v___y_4386_, 4);
v_ref_4404_ = lean_ctor_get(v___y_4386_, 5);
v_currNamespace_4405_ = lean_ctor_get(v___y_4386_, 6);
v_openDecls_4406_ = lean_ctor_get(v___y_4386_, 7);
v_initHeartbeats_4407_ = lean_ctor_get(v___y_4386_, 8);
v_maxHeartbeats_4408_ = lean_ctor_get(v___y_4386_, 9);
v_quotContext_4409_ = lean_ctor_get(v___y_4386_, 10);
v_currMacroScope_4410_ = lean_ctor_get(v___y_4386_, 11);
v_diag_4411_ = lean_ctor_get_uint8(v___y_4386_, sizeof(void*)*14);
v_cancelTk_x3f_4412_ = lean_ctor_get(v___y_4386_, 12);
v_suppressElabErrors_4413_ = lean_ctor_get_uint8(v___y_4386_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4414_ = lean_ctor_get(v___y_4386_, 13);
v___x_4415_ = lean_nat_dec_eq(v_currRecDepth_4402_, v_maxRecDepth_4403_);
if (v___x_4415_ == 0)
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; 
v___x_4416_ = lean_unsigned_to_nat(1u);
v___x_4417_ = lean_nat_add(v_currRecDepth_4402_, v___x_4416_);
lean_inc_ref(v_inheritedTraceOptions_4414_);
lean_inc(v_cancelTk_x3f_4412_);
lean_inc(v_currMacroScope_4410_);
lean_inc(v_quotContext_4409_);
lean_inc(v_maxHeartbeats_4408_);
lean_inc(v_initHeartbeats_4407_);
lean_inc(v_openDecls_4406_);
lean_inc(v_currNamespace_4405_);
lean_inc(v_ref_4404_);
lean_inc(v_maxRecDepth_4403_);
lean_inc_ref(v_options_4401_);
lean_inc_ref(v_fileMap_4400_);
lean_inc_ref(v_fileName_4399_);
v___x_4418_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4418_, 0, v_fileName_4399_);
lean_ctor_set(v___x_4418_, 1, v_fileMap_4400_);
lean_ctor_set(v___x_4418_, 2, v_options_4401_);
lean_ctor_set(v___x_4418_, 3, v___x_4417_);
lean_ctor_set(v___x_4418_, 4, v_maxRecDepth_4403_);
lean_ctor_set(v___x_4418_, 5, v_ref_4404_);
lean_ctor_set(v___x_4418_, 6, v_currNamespace_4405_);
lean_ctor_set(v___x_4418_, 7, v_openDecls_4406_);
lean_ctor_set(v___x_4418_, 8, v_initHeartbeats_4407_);
lean_ctor_set(v___x_4418_, 9, v_maxHeartbeats_4408_);
lean_ctor_set(v___x_4418_, 10, v_quotContext_4409_);
lean_ctor_set(v___x_4418_, 11, v_currMacroScope_4410_);
lean_ctor_set(v___x_4418_, 12, v_cancelTk_x3f_4412_);
lean_ctor_set(v___x_4418_, 13, v_inheritedTraceOptions_4414_);
lean_ctor_set_uint8(v___x_4418_, sizeof(void*)*14, v_diag_4411_);
lean_ctor_set_uint8(v___x_4418_, sizeof(void*)*14 + 1, v_suppressElabErrors_4413_);
lean_inc(v___y_4387_);
lean_inc(v___y_4385_);
lean_inc_ref(v___y_4384_);
lean_inc(v___y_4383_);
v___x_4419_ = lean_apply_6(v_x_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___x_4418_, v___y_4387_, lean_box(0));
v___y_4390_ = v___x_4419_;
goto v___jp_4389_;
}
else
{
lean_object* v___x_4420_; 
lean_dec_ref(v_x_4382_);
lean_inc(v_ref_4404_);
v___x_4420_ = l_Lean_throwMaxRecDepthAt___at___00Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__5_spec__7___redArg(v_ref_4404_);
v___y_4390_ = v___x_4420_;
goto v___jp_4389_;
}
v___jp_4389_:
{
if (lean_obj_tag(v___y_4390_) == 0)
{
return v___y_4390_;
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
v_a_4391_ = lean_ctor_get(v___y_4390_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___y_4390_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___y_4390_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___y_4390_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg___boxed(lean_object* v_x_4421_, lean_object* v___y_4422_, lean_object* v___y_4423_, lean_object* v___y_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_){
_start:
{
lean_object* v_res_4428_; 
v_res_4428_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_4421_, v___y_4422_, v___y_4423_, v___y_4424_, v___y_4425_, v___y_4426_);
lean_dec(v___y_4426_);
lean_dec_ref(v___y_4425_);
lean_dec(v___y_4424_);
lean_dec_ref(v___y_4423_);
lean_dec(v___y_4422_);
return v_res_4428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(lean_object* v_pre_4429_, lean_object* v_post_4430_, size_t v_sz_4431_, size_t v_i_4432_, lean_object* v_bs_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_){
_start:
{
uint8_t v___x_4440_; 
v___x_4440_ = lean_usize_dec_lt(v_i_4432_, v_sz_4431_);
if (v___x_4440_ == 0)
{
lean_object* v___x_4441_; 
lean_dec_ref(v_post_4430_);
lean_dec_ref(v_pre_4429_);
v___x_4441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4441_, 0, v_bs_4433_);
return v___x_4441_;
}
else
{
lean_object* v_v_4442_; lean_object* v___x_4443_; 
v_v_4442_ = lean_array_uget_borrowed(v_bs_4433_, v_i_4432_);
lean_inc(v_v_4442_);
lean_inc_ref(v_post_4430_);
lean_inc_ref(v_pre_4429_);
v___x_4443_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4429_, v_post_4430_, v_v_4442_, v___y_4434_, v___y_4435_, v___y_4436_, v___y_4437_, v___y_4438_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v_a_4444_; lean_object* v___x_4445_; lean_object* v_bs_x27_4446_; size_t v___x_4447_; size_t v___x_4448_; lean_object* v___x_4449_; 
v_a_4444_ = lean_ctor_get(v___x_4443_, 0);
lean_inc(v_a_4444_);
lean_dec_ref(v___x_4443_);
v___x_4445_ = lean_unsigned_to_nat(0u);
v_bs_x27_4446_ = lean_array_uset(v_bs_4433_, v_i_4432_, v___x_4445_);
v___x_4447_ = ((size_t)1ULL);
v___x_4448_ = lean_usize_add(v_i_4432_, v___x_4447_);
v___x_4449_ = lean_array_uset(v_bs_x27_4446_, v_i_4432_, v_a_4444_);
v_i_4432_ = v___x_4448_;
v_bs_4433_ = v___x_4449_;
goto _start;
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec_ref(v_bs_4433_);
lean_dec_ref(v_post_4430_);
lean_dec_ref(v_pre_4429_);
v_a_4451_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4443_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4443_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(lean_object* v_pre_4459_, lean_object* v_post_4460_, lean_object* v_x_4461_, lean_object* v_x_4462_, lean_object* v_x_4463_, lean_object* v___y_4464_, lean_object* v___y_4465_, lean_object* v___y_4466_, lean_object* v___y_4467_, lean_object* v___y_4468_){
_start:
{
if (lean_obj_tag(v_x_4461_) == 5)
{
lean_object* v_fn_4470_; lean_object* v_arg_4471_; lean_object* v___x_4472_; lean_object* v___x_4473_; lean_object* v___x_4474_; 
v_fn_4470_ = lean_ctor_get(v_x_4461_, 0);
lean_inc_ref(v_fn_4470_);
v_arg_4471_ = lean_ctor_get(v_x_4461_, 1);
lean_inc_ref(v_arg_4471_);
lean_dec_ref(v_x_4461_);
v___x_4472_ = lean_array_set(v_x_4462_, v_x_4463_, v_arg_4471_);
v___x_4473_ = lean_unsigned_to_nat(1u);
v___x_4474_ = lean_nat_sub(v_x_4463_, v___x_4473_);
lean_dec(v_x_4463_);
v_x_4461_ = v_fn_4470_;
v_x_4462_ = v___x_4472_;
v_x_4463_ = v___x_4474_;
goto _start;
}
else
{
lean_object* v___x_4476_; 
lean_dec(v_x_4463_);
lean_inc_ref(v_post_4460_);
lean_inc_ref(v_pre_4459_);
v___x_4476_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4459_, v_post_4460_, v_x_4461_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
if (lean_obj_tag(v___x_4476_) == 0)
{
lean_object* v_a_4477_; size_t v_sz_4478_; size_t v___x_4479_; lean_object* v___x_4480_; 
v_a_4477_ = lean_ctor_get(v___x_4476_, 0);
lean_inc(v_a_4477_);
lean_dec_ref(v___x_4476_);
v_sz_4478_ = lean_array_size(v_x_4462_);
v___x_4479_ = ((size_t)0ULL);
lean_inc_ref(v_post_4460_);
lean_inc_ref(v_pre_4459_);
v___x_4480_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_4459_, v_post_4460_, v_sz_4478_, v___x_4479_, v_x_4462_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v___x_4482_; lean_object* v___x_4483_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
lean_inc(v_a_4481_);
lean_dec_ref(v___x_4480_);
v___x_4482_ = l_Lean_mkAppN(v_a_4477_, v_a_4481_);
lean_dec(v_a_4481_);
v___x_4483_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4459_, v_post_4460_, v___x_4482_, v___y_4464_, v___y_4465_, v___y_4466_, v___y_4467_, v___y_4468_);
return v___x_4483_;
}
else
{
lean_object* v_a_4484_; lean_object* v___x_4486_; uint8_t v_isShared_4487_; uint8_t v_isSharedCheck_4491_; 
lean_dec(v_a_4477_);
lean_dec_ref(v_post_4460_);
lean_dec_ref(v_pre_4459_);
v_a_4484_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4491_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4491_ == 0)
{
v___x_4486_ = v___x_4480_;
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
else
{
lean_inc(v_a_4484_);
lean_dec(v___x_4480_);
v___x_4486_ = lean_box(0);
v_isShared_4487_ = v_isSharedCheck_4491_;
goto v_resetjp_4485_;
}
v_resetjp_4485_:
{
lean_object* v___x_4489_; 
if (v_isShared_4487_ == 0)
{
v___x_4489_ = v___x_4486_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_a_4484_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
}
}
else
{
lean_dec_ref(v_x_4462_);
lean_dec_ref(v_post_4460_);
lean_dec_ref(v_pre_4459_);
return v___x_4476_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(lean_object* v_pre_4492_, lean_object* v_e_4493_, lean_object* v_post_4494_, lean_object* v___y_4495_, lean_object* v___y_4496_, lean_object* v___y_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_){
_start:
{
lean_object* v___y_4502_; lean_object* v___y_4503_; uint8_t v___y_4504_; lean_object* v___y_4505_; lean_object* v___y_4506_; lean_object* v___y_4507_; lean_object* v___y_4508_; uint8_t v___y_4509_; lean_object* v___y_4519_; uint8_t v___y_4520_; lean_object* v___y_4521_; lean_object* v___y_4522_; lean_object* v___y_4523_; uint8_t v___y_4524_; uint8_t v___y_4532_; lean_object* v___y_4533_; lean_object* v___y_4534_; lean_object* v___y_4535_; lean_object* v___y_4536_; uint8_t v___y_4537_; lean_object* v___x_4544_; 
lean_inc_ref(v_pre_4492_);
lean_inc(v___y_4499_);
lean_inc_ref(v___y_4498_);
lean_inc(v___y_4497_);
lean_inc_ref(v___y_4496_);
lean_inc_ref(v_e_4493_);
v___x_4544_ = lean_apply_6(v_pre_4492_, v_e_4493_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_, lean_box(0));
if (lean_obj_tag(v___x_4544_) == 0)
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4634_; 
v_a_4545_ = lean_ctor_get(v___x_4544_, 0);
v_isSharedCheck_4634_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4634_ == 0)
{
v___x_4547_ = v___x_4544_;
v_isShared_4548_ = v_isSharedCheck_4634_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4544_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4634_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___y_4550_; 
switch(lean_obj_tag(v_a_4545_))
{
case 0:
{
lean_object* v_e_4624_; lean_object* v___x_4626_; 
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_e_4493_);
lean_dec_ref(v_pre_4492_);
v_e_4624_ = lean_ctor_get(v_a_4545_, 0);
lean_inc_ref(v_e_4624_);
lean_dec_ref(v_a_4545_);
if (v_isShared_4548_ == 0)
{
lean_ctor_set(v___x_4547_, 0, v_e_4624_);
v___x_4626_ = v___x_4547_;
goto v_reusejp_4625_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_e_4624_);
v___x_4626_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4625_;
}
v_reusejp_4625_:
{
return v___x_4626_;
}
}
case 1:
{
lean_object* v_e_4628_; lean_object* v___x_4629_; 
lean_del_object(v___x_4547_);
lean_dec_ref(v_e_4493_);
v_e_4628_ = lean_ctor_get(v_a_4545_, 0);
lean_inc_ref(v_e_4628_);
lean_dec_ref(v_a_4545_);
lean_inc_ref(v_post_4494_);
lean_inc_ref(v_pre_4492_);
v___x_4629_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4492_, v_post_4494_, v_e_4628_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4629_) == 0)
{
lean_object* v_a_4630_; lean_object* v___x_4631_; 
v_a_4630_ = lean_ctor_get(v___x_4629_, 0);
lean_inc(v_a_4630_);
lean_dec_ref(v___x_4629_);
v___x_4631_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v_a_4630_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4631_;
}
else
{
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_pre_4492_);
return v___x_4629_;
}
}
default: 
{
lean_object* v_e_x3f_4632_; 
lean_del_object(v___x_4547_);
v_e_x3f_4632_ = lean_ctor_get(v_a_4545_, 0);
lean_inc(v_e_x3f_4632_);
lean_dec_ref(v_a_4545_);
if (lean_obj_tag(v_e_x3f_4632_) == 0)
{
v___y_4550_ = v_e_4493_;
goto v___jp_4549_;
}
else
{
lean_object* v_val_4633_; 
lean_dec_ref(v_e_4493_);
v_val_4633_ = lean_ctor_get(v_e_x3f_4632_, 0);
lean_inc(v_val_4633_);
lean_dec_ref(v_e_x3f_4632_);
v___y_4550_ = v_val_4633_;
goto v___jp_4549_;
}
}
}
v___jp_4549_:
{
switch(lean_obj_tag(v___y_4550_))
{
case 7:
{
lean_object* v_binderName_4551_; lean_object* v_binderType_4552_; lean_object* v_body_4553_; uint8_t v_binderInfo_4554_; lean_object* v___x_4555_; 
v_binderName_4551_ = lean_ctor_get(v___y_4550_, 0);
lean_inc(v_binderName_4551_);
v_binderType_4552_ = lean_ctor_get(v___y_4550_, 1);
v_body_4553_ = lean_ctor_get(v___y_4550_, 2);
v_binderInfo_4554_ = lean_ctor_get_uint8(v___y_4550_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_4552_);
lean_inc_ref(v_post_4494_);
lean_inc_ref(v_pre_4492_);
v___x_4555_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4492_, v_post_4494_, v_binderType_4552_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4557_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
lean_inc(v_a_4556_);
lean_dec_ref(v___x_4555_);
lean_inc_ref(v_body_4553_);
lean_inc_ref(v_post_4494_);
lean_inc_ref(v_pre_4492_);
v___x_4557_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4492_, v_post_4494_, v_body_4553_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4557_) == 0)
{
lean_object* v_a_4558_; size_t v___x_4559_; size_t v___x_4560_; uint8_t v___x_4561_; 
v_a_4558_ = lean_ctor_get(v___x_4557_, 0);
lean_inc(v_a_4558_);
lean_dec_ref(v___x_4557_);
v___x_4559_ = lean_ptr_addr(v_binderType_4552_);
v___x_4560_ = lean_ptr_addr(v_a_4556_);
v___x_4561_ = lean_usize_dec_eq(v___x_4559_, v___x_4560_);
if (v___x_4561_ == 0)
{
v___y_4532_ = v_binderInfo_4554_;
v___y_4533_ = v_a_4558_;
v___y_4534_ = v_a_4556_;
v___y_4535_ = v_binderName_4551_;
v___y_4536_ = v___y_4550_;
v___y_4537_ = v___x_4561_;
goto v___jp_4531_;
}
else
{
size_t v___x_4562_; size_t v___x_4563_; uint8_t v___x_4564_; 
v___x_4562_ = lean_ptr_addr(v_body_4553_);
v___x_4563_ = lean_ptr_addr(v_a_4558_);
v___x_4564_ = lean_usize_dec_eq(v___x_4562_, v___x_4563_);
v___y_4532_ = v_binderInfo_4554_;
v___y_4533_ = v_a_4558_;
v___y_4534_ = v_a_4556_;
v___y_4535_ = v_binderName_4551_;
v___y_4536_ = v___y_4550_;
v___y_4537_ = v___x_4564_;
goto v___jp_4531_;
}
}
else
{
lean_dec(v_a_4556_);
lean_dec_ref(v___y_4550_);
lean_dec(v_binderName_4551_);
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_pre_4492_);
return v___x_4557_;
}
}
else
{
lean_dec(v_binderName_4551_);
lean_dec_ref(v___y_4550_);
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_pre_4492_);
return v___x_4555_;
}
}
case 6:
{
lean_object* v_binderName_4565_; lean_object* v_binderType_4566_; lean_object* v_body_4567_; uint8_t v_binderInfo_4568_; lean_object* v___x_4569_; 
v_binderName_4565_ = lean_ctor_get(v___y_4550_, 0);
lean_inc(v_binderName_4565_);
v_binderType_4566_ = lean_ctor_get(v___y_4550_, 1);
v_body_4567_ = lean_ctor_get(v___y_4550_, 2);
v_binderInfo_4568_ = lean_ctor_get_uint8(v___y_4550_, sizeof(void*)*3 + 8);
lean_inc_ref(v_binderType_4566_);
lean_inc_ref(v_post_4494_);
lean_inc_ref(v_pre_4492_);
v___x_4569_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4492_, v_post_4494_, v_binderType_4566_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v_a_4570_; lean_object* v___x_4571_; 
v_a_4570_ = lean_ctor_get(v___x_4569_, 0);
lean_inc(v_a_4570_);
lean_dec_ref(v___x_4569_);
lean_inc_ref(v_body_4567_);
lean_inc_ref(v_post_4494_);
lean_inc_ref(v_pre_4492_);
v___x_4571_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4492_, v_post_4494_, v_body_4567_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4571_) == 0)
{
lean_object* v_a_4572_; size_t v___x_4573_; size_t v___x_4574_; uint8_t v___x_4575_; 
v_a_4572_ = lean_ctor_get(v___x_4571_, 0);
lean_inc(v_a_4572_);
lean_dec_ref(v___x_4571_);
v___x_4573_ = lean_ptr_addr(v_binderType_4566_);
v___x_4574_ = lean_ptr_addr(v_a_4570_);
v___x_4575_ = lean_usize_dec_eq(v___x_4573_, v___x_4574_);
if (v___x_4575_ == 0)
{
v___y_4519_ = v_a_4570_;
v___y_4520_ = v_binderInfo_4568_;
v___y_4521_ = v_binderName_4565_;
v___y_4522_ = v___y_4550_;
v___y_4523_ = v_a_4572_;
v___y_4524_ = v___x_4575_;
goto v___jp_4518_;
}
else
{
size_t v___x_4576_; size_t v___x_4577_; uint8_t v___x_4578_; 
v___x_4576_ = lean_ptr_addr(v_body_4567_);
v___x_4577_ = lean_ptr_addr(v_a_4572_);
v___x_4578_ = lean_usize_dec_eq(v___x_4576_, v___x_4577_);
v___y_4519_ = v_a_4570_;
v___y_4520_ = v_binderInfo_4568_;
v___y_4521_ = v_binderName_4565_;
v___y_4522_ = v___y_4550_;
v___y_4523_ = v_a_4572_;
v___y_4524_ = v___x_4578_;
goto v___jp_4518_;
}
}
else
{
lean_dec(v_a_4570_);
lean_dec(v_binderName_4565_);
lean_dec_ref(v___y_4550_);
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_pre_4492_);
return v___x_4571_;
}
}
else
{
lean_dec(v_binderName_4565_);
lean_dec_ref(v___y_4550_);
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_pre_4492_);
return v___x_4569_;
}
}
case 8:
{
lean_object* v_declName_4579_; lean_object* v_type_4580_; lean_object* v_value_4581_; lean_object* v_body_4582_; uint8_t v_nondep_4583_; lean_object* v___x_4584_; 
v_declName_4579_ = lean_ctor_get(v___y_4550_, 0);
lean_inc(v_declName_4579_);
v_type_4580_ = lean_ctor_get(v___y_4550_, 1);
v_value_4581_ = lean_ctor_get(v___y_4550_, 2);
v_body_4582_ = lean_ctor_get(v___y_4550_, 3);
lean_inc_ref(v_body_4582_);
v_nondep_4583_ = lean_ctor_get_uint8(v___y_4550_, sizeof(void*)*4 + 8);
lean_inc_ref(v_type_4580_);
lean_inc_ref(v_post_4494_);
lean_inc_ref(v_pre_4492_);
v___x_4584_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4492_, v_post_4494_, v_type_4580_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4584_) == 0)
{
lean_object* v_a_4585_; lean_object* v___x_4586_; 
v_a_4585_ = lean_ctor_get(v___x_4584_, 0);
lean_inc(v_a_4585_);
lean_dec_ref(v___x_4584_);
lean_inc_ref(v_value_4581_);
lean_inc_ref(v_post_4494_);
lean_inc_ref(v_pre_4492_);
v___x_4586_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4492_, v_post_4494_, v_value_4581_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v___x_4588_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
lean_inc(v_a_4587_);
lean_dec_ref(v___x_4586_);
lean_inc_ref(v_body_4582_);
lean_inc_ref(v_post_4494_);
lean_inc_ref(v_pre_4492_);
v___x_4588_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4492_, v_post_4494_, v_body_4582_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4588_) == 0)
{
lean_object* v_a_4589_; size_t v___x_4590_; size_t v___x_4591_; uint8_t v___x_4592_; 
v_a_4589_ = lean_ctor_get(v___x_4588_, 0);
lean_inc(v_a_4589_);
lean_dec_ref(v___x_4588_);
v___x_4590_ = lean_ptr_addr(v_type_4580_);
v___x_4591_ = lean_ptr_addr(v_a_4585_);
v___x_4592_ = lean_usize_dec_eq(v___x_4590_, v___x_4591_);
if (v___x_4592_ == 0)
{
v___y_4502_ = v_a_4585_;
v___y_4503_ = v_body_4582_;
v___y_4504_ = v_nondep_4583_;
v___y_4505_ = v_a_4589_;
v___y_4506_ = v_declName_4579_;
v___y_4507_ = v_a_4587_;
v___y_4508_ = v___y_4550_;
v___y_4509_ = v___x_4592_;
goto v___jp_4501_;
}
else
{
size_t v___x_4593_; size_t v___x_4594_; uint8_t v___x_4595_; 
v___x_4593_ = lean_ptr_addr(v_value_4581_);
v___x_4594_ = lean_ptr_addr(v_a_4587_);
v___x_4595_ = lean_usize_dec_eq(v___x_4593_, v___x_4594_);
v___y_4502_ = v_a_4585_;
v___y_4503_ = v_body_4582_;
v___y_4504_ = v_nondep_4583_;
v___y_4505_ = v_a_4589_;
v___y_4506_ = v_declName_4579_;
v___y_4507_ = v_a_4587_;
v___y_4508_ = v___y_4550_;
v___y_4509_ = v___x_4595_;
goto v___jp_4501_;
}
}
else
{
lean_dec(v_a_4587_);
lean_dec(v_a_4585_);
lean_dec_ref(v_body_4582_);
lean_dec(v_declName_4579_);
lean_dec_ref(v___y_4550_);
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_pre_4492_);
return v___x_4588_;
}
}
else
{
lean_dec(v_a_4585_);
lean_dec_ref(v_body_4582_);
lean_dec(v_declName_4579_);
lean_dec_ref(v___y_4550_);
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_pre_4492_);
return v___x_4586_;
}
}
else
{
lean_dec_ref(v_body_4582_);
lean_dec(v_declName_4579_);
lean_dec_ref(v___y_4550_);
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_pre_4492_);
return v___x_4584_;
}
}
case 5:
{
lean_object* v_dummy_4596_; lean_object* v_nargs_4597_; lean_object* v___x_4598_; lean_object* v___x_4599_; lean_object* v___x_4600_; lean_object* v___x_4601_; 
v_dummy_4596_ = lean_obj_once(&l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0, &l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0_once, _init_l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__1___closed__0);
v_nargs_4597_ = l_Lean_Expr_getAppNumArgs(v___y_4550_);
lean_inc(v_nargs_4597_);
v___x_4598_ = lean_mk_array(v_nargs_4597_, v_dummy_4596_);
v___x_4599_ = lean_unsigned_to_nat(1u);
v___x_4600_ = lean_nat_sub(v_nargs_4597_, v___x_4599_);
lean_dec(v_nargs_4597_);
v___x_4601_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_4492_, v_post_4494_, v___y_4550_, v___x_4598_, v___x_4600_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4601_;
}
case 10:
{
lean_object* v_data_4602_; lean_object* v_expr_4603_; lean_object* v___x_4604_; 
v_data_4602_ = lean_ctor_get(v___y_4550_, 0);
v_expr_4603_ = lean_ctor_get(v___y_4550_, 1);
lean_inc_ref(v_expr_4603_);
lean_inc_ref(v_post_4494_);
lean_inc_ref(v_pre_4492_);
v___x_4604_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4492_, v_post_4494_, v_expr_4603_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4604_) == 0)
{
lean_object* v_a_4605_; size_t v___x_4606_; size_t v___x_4607_; uint8_t v___x_4608_; 
v_a_4605_ = lean_ctor_get(v___x_4604_, 0);
lean_inc(v_a_4605_);
lean_dec_ref(v___x_4604_);
v___x_4606_ = lean_ptr_addr(v_expr_4603_);
v___x_4607_ = lean_ptr_addr(v_a_4605_);
v___x_4608_ = lean_usize_dec_eq(v___x_4606_, v___x_4607_);
if (v___x_4608_ == 0)
{
lean_object* v___x_4609_; lean_object* v___x_4610_; 
lean_inc(v_data_4602_);
lean_dec_ref(v___y_4550_);
v___x_4609_ = l_Lean_Expr_mdata___override(v_data_4602_, v_a_4605_);
v___x_4610_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___x_4609_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4610_;
}
else
{
lean_object* v___x_4611_; 
lean_dec(v_a_4605_);
v___x_4611_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___y_4550_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4611_;
}
}
else
{
lean_dec_ref(v___y_4550_);
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_pre_4492_);
return v___x_4604_;
}
}
case 11:
{
lean_object* v_typeName_4612_; lean_object* v_idx_4613_; lean_object* v_struct_4614_; lean_object* v___x_4615_; 
v_typeName_4612_ = lean_ctor_get(v___y_4550_, 0);
v_idx_4613_ = lean_ctor_get(v___y_4550_, 1);
v_struct_4614_ = lean_ctor_get(v___y_4550_, 2);
lean_inc_ref(v_struct_4614_);
lean_inc_ref(v_post_4494_);
lean_inc_ref(v_pre_4492_);
v___x_4615_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4492_, v_post_4494_, v_struct_4614_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; size_t v___x_4617_; size_t v___x_4618_; uint8_t v___x_4619_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
lean_inc(v_a_4616_);
lean_dec_ref(v___x_4615_);
v___x_4617_ = lean_ptr_addr(v_struct_4614_);
v___x_4618_ = lean_ptr_addr(v_a_4616_);
v___x_4619_ = lean_usize_dec_eq(v___x_4617_, v___x_4618_);
if (v___x_4619_ == 0)
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
lean_inc(v_idx_4613_);
lean_inc(v_typeName_4612_);
lean_dec_ref(v___y_4550_);
v___x_4620_ = l_Lean_Expr_proj___override(v_typeName_4612_, v_idx_4613_, v_a_4616_);
v___x_4621_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___x_4620_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4621_;
}
else
{
lean_object* v___x_4622_; 
lean_dec(v_a_4616_);
v___x_4622_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___y_4550_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4622_;
}
}
else
{
lean_dec_ref(v___y_4550_);
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_pre_4492_);
return v___x_4615_;
}
}
default: 
{
lean_object* v___x_4623_; 
v___x_4623_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___y_4550_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4623_;
}
}
}
}
}
else
{
lean_object* v_a_4635_; lean_object* v___x_4637_; uint8_t v_isShared_4638_; uint8_t v_isSharedCheck_4642_; 
lean_dec_ref(v_post_4494_);
lean_dec_ref(v_e_4493_);
lean_dec_ref(v_pre_4492_);
v_a_4635_ = lean_ctor_get(v___x_4544_, 0);
v_isSharedCheck_4642_ = !lean_is_exclusive(v___x_4544_);
if (v_isSharedCheck_4642_ == 0)
{
v___x_4637_ = v___x_4544_;
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
else
{
lean_inc(v_a_4635_);
lean_dec(v___x_4544_);
v___x_4637_ = lean_box(0);
v_isShared_4638_ = v_isSharedCheck_4642_;
goto v_resetjp_4636_;
}
v_resetjp_4636_:
{
lean_object* v___x_4640_; 
if (v_isShared_4638_ == 0)
{
v___x_4640_ = v___x_4637_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4641_; 
v_reuseFailAlloc_4641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4641_, 0, v_a_4635_);
v___x_4640_ = v_reuseFailAlloc_4641_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
return v___x_4640_;
}
}
}
v___jp_4501_:
{
if (v___y_4509_ == 0)
{
lean_object* v___x_4510_; lean_object* v___x_4511_; 
lean_dec_ref(v___y_4508_);
lean_dec_ref(v___y_4503_);
v___x_4510_ = l_Lean_Expr_letE___override(v___y_4506_, v___y_4502_, v___y_4507_, v___y_4505_, v___y_4504_);
v___x_4511_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___x_4510_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4511_;
}
else
{
size_t v___x_4512_; size_t v___x_4513_; uint8_t v___x_4514_; 
v___x_4512_ = lean_ptr_addr(v___y_4503_);
lean_dec_ref(v___y_4503_);
v___x_4513_ = lean_ptr_addr(v___y_4505_);
v___x_4514_ = lean_usize_dec_eq(v___x_4512_, v___x_4513_);
if (v___x_4514_ == 0)
{
lean_object* v___x_4515_; lean_object* v___x_4516_; 
lean_dec_ref(v___y_4508_);
v___x_4515_ = l_Lean_Expr_letE___override(v___y_4506_, v___y_4502_, v___y_4507_, v___y_4505_, v___y_4504_);
v___x_4516_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___x_4515_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4516_;
}
else
{
lean_object* v___x_4517_; 
lean_dec_ref(v___y_4507_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec_ref(v___y_4502_);
v___x_4517_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___y_4508_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4517_;
}
}
}
v___jp_4518_:
{
if (v___y_4524_ == 0)
{
lean_object* v___x_4525_; lean_object* v___x_4526_; 
lean_dec_ref(v___y_4522_);
v___x_4525_ = l_Lean_Expr_lam___override(v___y_4521_, v___y_4519_, v___y_4523_, v___y_4520_);
v___x_4526_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___x_4525_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4526_;
}
else
{
uint8_t v___x_4527_; 
v___x_4527_ = l_Lean_instBEqBinderInfo_beq(v___y_4520_, v___y_4520_);
if (v___x_4527_ == 0)
{
lean_object* v___x_4528_; lean_object* v___x_4529_; 
lean_dec_ref(v___y_4522_);
v___x_4528_ = l_Lean_Expr_lam___override(v___y_4521_, v___y_4519_, v___y_4523_, v___y_4520_);
v___x_4529_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___x_4528_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4529_;
}
else
{
lean_object* v___x_4530_; 
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4519_);
v___x_4530_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___y_4522_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4530_;
}
}
}
v___jp_4531_:
{
if (v___y_4537_ == 0)
{
lean_object* v___x_4538_; lean_object* v___x_4539_; 
lean_dec_ref(v___y_4536_);
v___x_4538_ = l_Lean_Expr_forallE___override(v___y_4535_, v___y_4534_, v___y_4533_, v___y_4532_);
v___x_4539_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___x_4538_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4539_;
}
else
{
uint8_t v___x_4540_; 
v___x_4540_ = l_Lean_instBEqBinderInfo_beq(v___y_4532_, v___y_4532_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; lean_object* v___x_4542_; 
lean_dec_ref(v___y_4536_);
v___x_4541_ = l_Lean_Expr_forallE___override(v___y_4535_, v___y_4534_, v___y_4533_, v___y_4532_);
v___x_4542_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___x_4541_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4542_;
}
else
{
lean_object* v___x_4543_; 
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
lean_dec_ref(v___y_4533_);
v___x_4543_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4492_, v_post_4494_, v___y_4536_, v___y_4495_, v___y_4496_, v___y_4497_, v___y_4498_, v___y_4499_);
return v___x_4543_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed(lean_object* v_pre_4643_, lean_object* v_e_4644_, lean_object* v_post_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1(v_pre_4643_, v_e_4644_, v_post_4645_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_, v___y_4650_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(lean_object* v_pre_4653_, lean_object* v_post_4654_, lean_object* v_e_4655_, lean_object* v_a_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v___x_4662_; lean_object* v___x_4663_; 
lean_inc(v_a_4656_);
v___x_4662_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4662_, 0, lean_box(0));
lean_closure_set(v___x_4662_, 1, lean_box(0));
lean_closure_set(v___x_4662_, 2, v_a_4656_);
v___x_4663_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_box(0), v___x_4662_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4663_) == 0)
{
lean_object* v_a_4664_; lean_object* v___x_4666_; uint8_t v_isShared_4667_; uint8_t v_isSharedCheck_4694_; 
v_a_4664_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4666_ = v___x_4663_;
v_isShared_4667_ = v_isSharedCheck_4694_;
goto v_resetjp_4665_;
}
else
{
lean_inc(v_a_4664_);
lean_dec(v___x_4663_);
v___x_4666_ = lean_box(0);
v_isShared_4667_ = v_isSharedCheck_4694_;
goto v_resetjp_4665_;
}
v_resetjp_4665_:
{
lean_object* v___x_4668_; 
v___x_4668_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0_spec__3___redArg(v_a_4664_, v_e_4655_);
lean_dec(v_a_4664_);
if (lean_obj_tag(v___x_4668_) == 0)
{
lean_object* v___f_4669_; lean_object* v___x_4670_; 
lean_del_object(v___x_4666_);
lean_inc_ref(v_e_4655_);
v___f_4669_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___lam__1___boxed), 9, 3);
lean_closure_set(v___f_4669_, 0, v_pre_4653_);
lean_closure_set(v___f_4669_, 1, v_e_4655_);
lean_closure_set(v___f_4669_, 2, v_post_4654_);
v___x_4670_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v___f_4669_, v_a_4656_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4670_) == 0)
{
lean_object* v_a_4671_; lean_object* v___f_4672_; lean_object* v___x_4673_; 
v_a_4671_ = lean_ctor_get(v___x_4670_, 0);
lean_inc_n(v_a_4671_, 2);
lean_dec_ref(v___x_4670_);
lean_inc(v_a_4656_);
v___f_4672_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0_spec__0___lam__2___boxed), 4, 3);
lean_closure_set(v___f_4672_, 0, v_a_4656_);
lean_closure_set(v___f_4672_, 1, v_e_4655_);
lean_closure_set(v___f_4672_, 2, v_a_4671_);
v___x_4673_ = l___private_Lean_Meta_Transform_0__Lean_Meta_transformWithCache_visit___at___00Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1_spec__2___lam__0(lean_box(0), v___f_4672_, v___y_4657_, v___y_4658_, v___y_4659_, v___y_4660_);
if (lean_obj_tag(v___x_4673_) == 0)
{
lean_object* v___x_4675_; uint8_t v_isShared_4676_; uint8_t v_isSharedCheck_4680_; 
v_isSharedCheck_4680_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4680_ == 0)
{
lean_object* v_unused_4681_; 
v_unused_4681_ = lean_ctor_get(v___x_4673_, 0);
lean_dec(v_unused_4681_);
v___x_4675_ = v___x_4673_;
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
else
{
lean_dec(v___x_4673_);
v___x_4675_ = lean_box(0);
v_isShared_4676_ = v_isSharedCheck_4680_;
goto v_resetjp_4674_;
}
v_resetjp_4674_:
{
lean_object* v___x_4678_; 
if (v_isShared_4676_ == 0)
{
lean_ctor_set(v___x_4675_, 0, v_a_4671_);
v___x_4678_ = v___x_4675_;
goto v_reusejp_4677_;
}
else
{
lean_object* v_reuseFailAlloc_4679_; 
v_reuseFailAlloc_4679_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4679_, 0, v_a_4671_);
v___x_4678_ = v_reuseFailAlloc_4679_;
goto v_reusejp_4677_;
}
v_reusejp_4677_:
{
return v___x_4678_;
}
}
}
else
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4689_; 
lean_dec(v_a_4671_);
v_a_4682_ = lean_ctor_get(v___x_4673_, 0);
v_isSharedCheck_4689_ = !lean_is_exclusive(v___x_4673_);
if (v_isSharedCheck_4689_ == 0)
{
v___x_4684_ = v___x_4673_;
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4673_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4689_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v___x_4687_; 
if (v_isShared_4685_ == 0)
{
v___x_4687_ = v___x_4684_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_a_4682_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
}
}
else
{
lean_dec_ref(v_e_4655_);
return v___x_4670_;
}
}
else
{
lean_object* v_val_4690_; lean_object* v___x_4692_; 
lean_dec_ref(v_e_4655_);
lean_dec_ref(v_post_4654_);
lean_dec_ref(v_pre_4653_);
v_val_4690_ = lean_ctor_get(v___x_4668_, 0);
lean_inc(v_val_4690_);
lean_dec_ref(v___x_4668_);
if (v_isShared_4667_ == 0)
{
lean_ctor_set(v___x_4666_, 0, v_val_4690_);
v___x_4692_ = v___x_4666_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_val_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
else
{
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4702_; 
lean_dec_ref(v_e_4655_);
lean_dec_ref(v_post_4654_);
lean_dec_ref(v_pre_4653_);
v_a_4695_ = lean_ctor_get(v___x_4663_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4663_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4697_ = v___x_4663_;
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v___x_4663_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4700_; 
if (v_isShared_4698_ == 0)
{
v___x_4700_ = v___x_4697_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4695_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(lean_object* v_pre_4703_, lean_object* v_post_4704_, lean_object* v_e_4705_, lean_object* v_a_4706_, lean_object* v___y_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_){
_start:
{
lean_object* v___x_4712_; 
lean_inc_ref(v_post_4704_);
lean_inc(v___y_4710_);
lean_inc_ref(v___y_4709_);
lean_inc(v___y_4708_);
lean_inc_ref(v___y_4707_);
lean_inc_ref(v_e_4705_);
v___x_4712_ = lean_apply_6(v_post_4704_, v_e_4705_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, lean_box(0));
if (lean_obj_tag(v___x_4712_) == 0)
{
lean_object* v_a_4713_; lean_object* v___x_4715_; uint8_t v_isShared_4716_; uint8_t v_isSharedCheck_4731_; 
v_a_4713_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4731_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4731_ == 0)
{
v___x_4715_ = v___x_4712_;
v_isShared_4716_ = v_isSharedCheck_4731_;
goto v_resetjp_4714_;
}
else
{
lean_inc(v_a_4713_);
lean_dec(v___x_4712_);
v___x_4715_ = lean_box(0);
v_isShared_4716_ = v_isSharedCheck_4731_;
goto v_resetjp_4714_;
}
v_resetjp_4714_:
{
switch(lean_obj_tag(v_a_4713_))
{
case 0:
{
lean_object* v_e_4717_; lean_object* v___x_4719_; 
lean_dec_ref(v_e_4705_);
lean_dec_ref(v_post_4704_);
lean_dec_ref(v_pre_4703_);
v_e_4717_ = lean_ctor_get(v_a_4713_, 0);
lean_inc_ref(v_e_4717_);
lean_dec_ref(v_a_4713_);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 0, v_e_4717_);
v___x_4719_ = v___x_4715_;
goto v_reusejp_4718_;
}
else
{
lean_object* v_reuseFailAlloc_4720_; 
v_reuseFailAlloc_4720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4720_, 0, v_e_4717_);
v___x_4719_ = v_reuseFailAlloc_4720_;
goto v_reusejp_4718_;
}
v_reusejp_4718_:
{
return v___x_4719_;
}
}
case 1:
{
lean_object* v_e_4721_; lean_object* v___x_4722_; 
lean_del_object(v___x_4715_);
lean_dec_ref(v_e_4705_);
v_e_4721_ = lean_ctor_get(v_a_4713_, 0);
lean_inc_ref(v_e_4721_);
lean_dec_ref(v_a_4713_);
v___x_4722_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4703_, v_post_4704_, v_e_4721_, v_a_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_);
return v___x_4722_;
}
default: 
{
lean_object* v_e_x3f_4723_; 
lean_dec_ref(v_post_4704_);
lean_dec_ref(v_pre_4703_);
v_e_x3f_4723_ = lean_ctor_get(v_a_4713_, 0);
lean_inc(v_e_x3f_4723_);
lean_dec_ref(v_a_4713_);
if (lean_obj_tag(v_e_x3f_4723_) == 0)
{
lean_object* v___x_4725_; 
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 0, v_e_4705_);
v___x_4725_ = v___x_4715_;
goto v_reusejp_4724_;
}
else
{
lean_object* v_reuseFailAlloc_4726_; 
v_reuseFailAlloc_4726_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4726_, 0, v_e_4705_);
v___x_4725_ = v_reuseFailAlloc_4726_;
goto v_reusejp_4724_;
}
v_reusejp_4724_:
{
return v___x_4725_;
}
}
else
{
lean_object* v_val_4727_; lean_object* v___x_4729_; 
lean_dec_ref(v_e_4705_);
v_val_4727_ = lean_ctor_get(v_e_x3f_4723_, 0);
lean_inc(v_val_4727_);
lean_dec_ref(v_e_x3f_4723_);
if (v_isShared_4716_ == 0)
{
lean_ctor_set(v___x_4715_, 0, v_val_4727_);
v___x_4729_ = v___x_4715_;
goto v_reusejp_4728_;
}
else
{
lean_object* v_reuseFailAlloc_4730_; 
v_reuseFailAlloc_4730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4730_, 0, v_val_4727_);
v___x_4729_ = v_reuseFailAlloc_4730_;
goto v_reusejp_4728_;
}
v_reusejp_4728_:
{
return v___x_4729_;
}
}
}
}
}
}
else
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4739_; 
lean_dec_ref(v_e_4705_);
lean_dec_ref(v_post_4704_);
lean_dec_ref(v_pre_4703_);
v_a_4732_ = lean_ctor_get(v___x_4712_, 0);
v_isSharedCheck_4739_ = !lean_is_exclusive(v___x_4712_);
if (v_isSharedCheck_4739_ == 0)
{
v___x_4734_ = v___x_4712_;
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4712_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4739_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
lean_object* v___x_4737_; 
if (v_isShared_4735_ == 0)
{
v___x_4737_ = v___x_4734_;
goto v_reusejp_4736_;
}
else
{
lean_object* v_reuseFailAlloc_4738_; 
v_reuseFailAlloc_4738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4738_, 0, v_a_4732_);
v___x_4737_ = v_reuseFailAlloc_4738_;
goto v_reusejp_4736_;
}
v_reusejp_4736_:
{
return v___x_4737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2___boxed(lean_object* v_pre_4740_, lean_object* v_post_4741_, lean_object* v_e_4742_, lean_object* v_a_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
lean_object* v_res_4749_; 
v_res_4749_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit_visitPost___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__2(v_pre_4740_, v_post_4741_, v_e_4742_, v_a_4743_, v___y_4744_, v___y_4745_, v___y_4746_, v___y_4747_);
lean_dec(v___y_4747_);
lean_dec_ref(v___y_4746_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v_a_4743_);
return v_res_4749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1___boxed(lean_object* v_pre_4750_, lean_object* v_post_4751_, lean_object* v_sz_4752_, lean_object* v_i_4753_, lean_object* v_bs_4754_, lean_object* v___y_4755_, lean_object* v___y_4756_, lean_object* v___y_4757_, lean_object* v___y_4758_, lean_object* v___y_4759_, lean_object* v___y_4760_){
_start:
{
size_t v_sz_boxed_4761_; size_t v_i_boxed_4762_; lean_object* v_res_4763_; 
v_sz_boxed_4761_ = lean_unbox_usize(v_sz_4752_);
lean_dec(v_sz_4752_);
v_i_boxed_4762_ = lean_unbox_usize(v_i_4753_);
lean_dec(v_i_4753_);
v_res_4763_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__1(v_pre_4750_, v_post_4751_, v_sz_boxed_4761_, v_i_boxed_4762_, v_bs_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_, v___y_4759_);
lean_dec(v___y_4759_);
lean_dec_ref(v___y_4758_);
lean_dec(v___y_4757_);
lean_dec_ref(v___y_4756_);
lean_dec(v___y_4755_);
return v_res_4763_;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3___boxed(lean_object* v_pre_4764_, lean_object* v_post_4765_, lean_object* v_x_4766_, lean_object* v_x_4767_, lean_object* v_x_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Expr_withAppAux___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__3(v_pre_4764_, v_post_4765_, v_x_4766_, v_x_4767_, v_x_4768_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
lean_dec(v___y_4769_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0___boxed(lean_object* v_pre_4776_, lean_object* v_post_4777_, lean_object* v_e_4778_, lean_object* v_a_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_, lean_object* v___y_4784_){
_start:
{
lean_object* v_res_4785_; 
v_res_4785_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4776_, v_post_4777_, v_e_4778_, v_a_4779_, v___y_4780_, v___y_4781_, v___y_4782_, v___y_4783_);
lean_dec(v___y_4783_);
lean_dec_ref(v___y_4782_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v_a_4779_);
return v_res_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(lean_object* v_input_4786_, lean_object* v_pre_4787_, lean_object* v_post_4788_, lean_object* v___y_4789_, lean_object* v___y_4790_, lean_object* v___y_4791_, lean_object* v___y_4792_){
_start:
{
lean_object* v___x_4794_; lean_object* v___x_4795_; lean_object* v_a_4796_; lean_object* v___x_4797_; 
v___x_4794_ = lean_obj_once(&l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2, &l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2_once, _init_l_Lean_Core_transform___at___00Lean_Meta_Grind_eraseIrrelevantMData_spec__0___closed__2);
v___x_4795_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_box(0), v___x_4794_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
v_a_4796_ = lean_ctor_get(v___x_4795_, 0);
lean_inc(v_a_4796_);
lean_dec_ref(v___x_4795_);
v___x_4797_ = l___private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0(v_pre_4787_, v_post_4788_, v_input_4786_, v_a_4796_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
if (lean_obj_tag(v___x_4797_) == 0)
{
lean_object* v_a_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4807_; 
v_a_4798_ = lean_ctor_get(v___x_4797_, 0);
lean_inc(v_a_4798_);
lean_dec_ref(v___x_4797_);
v___x_4799_ = lean_alloc_closure((void*)(l_ST_Prim_Ref_get___boxed), 4, 3);
lean_closure_set(v___x_4799_, 0, lean_box(0));
lean_closure_set(v___x_4799_, 1, lean_box(0));
lean_closure_set(v___x_4799_, 2, v_a_4796_);
v___x_4800_ = l_Lean_Meta_transform___at___00Lean_Meta_Grind_foldProjs_spec__1___lam__0(lean_box(0), v___x_4799_, v___y_4789_, v___y_4790_, v___y_4791_, v___y_4792_);
v_isSharedCheck_4807_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4807_ == 0)
{
lean_object* v_unused_4808_; 
v_unused_4808_ = lean_ctor_get(v___x_4800_, 0);
lean_dec(v_unused_4808_);
v___x_4802_ = v___x_4800_;
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
else
{
lean_dec(v___x_4800_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4807_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___x_4805_; 
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v_a_4798_);
v___x_4805_ = v___x_4802_;
goto v_reusejp_4804_;
}
else
{
lean_object* v_reuseFailAlloc_4806_; 
v_reuseFailAlloc_4806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4806_, 0, v_a_4798_);
v___x_4805_ = v_reuseFailAlloc_4806_;
goto v_reusejp_4804_;
}
v_reusejp_4804_:
{
return v___x_4805_;
}
}
}
else
{
lean_dec(v_a_4796_);
return v___x_4797_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0___boxed(lean_object* v_input_4809_, lean_object* v_pre_4810_, lean_object* v_post_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_, lean_object* v___y_4816_){
_start:
{
lean_object* v_res_4817_; 
v_res_4817_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_input_4809_, v_pre_4810_, v_post_4811_, v___y_4812_, v___y_4813_, v___y_4814_, v___y_4815_);
lean_dec(v___y_4815_);
lean_dec_ref(v___y_4814_);
lean_dec(v___y_4813_);
lean_dec_ref(v___y_4812_);
return v_res_4817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond(lean_object* v_e_4821_, lean_object* v_a_4822_, lean_object* v_a_4823_, lean_object* v_a_4824_, lean_object* v_a_4825_){
_start:
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__0));
v___x_4828_ = lean_find_expr(v___x_4827_, v_e_4821_);
if (lean_obj_tag(v___x_4828_) == 0)
{
uint8_t v___x_4829_; lean_object* v___x_4830_; lean_object* v___x_4831_; 
v___x_4829_ = 1;
v___x_4830_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4830_, 0, v_e_4821_);
lean_ctor_set(v___x_4830_, 1, v___x_4828_);
lean_ctor_set_uint8(v___x_4830_, sizeof(void*)*2, v___x_4829_);
v___x_4831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4831_, 0, v___x_4830_);
return v___x_4831_;
}
else
{
lean_object* v___x_4833_; uint8_t v_isShared_4834_; uint8_t v_isSharedCheck_4880_; 
v_isSharedCheck_4880_ = !lean_is_exclusive(v___x_4828_);
if (v_isSharedCheck_4880_ == 0)
{
lean_object* v_unused_4881_; 
v_unused_4881_ = lean_ctor_get(v___x_4828_, 0);
lean_dec(v_unused_4881_);
v___x_4833_ = v___x_4828_;
v_isShared_4834_ = v_isSharedCheck_4880_;
goto v_resetjp_4832_;
}
else
{
lean_dec(v___x_4828_);
v___x_4833_ = lean_box(0);
v_isShared_4834_ = v_isSharedCheck_4880_;
goto v_resetjp_4832_;
}
v_resetjp_4832_:
{
lean_object* v_pre_4835_; lean_object* v___f_4836_; lean_object* v___x_4837_; 
v_pre_4835_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__1));
v___f_4836_ = ((lean_object*)(l_Lean_Meta_Grind_replacePreMatchCond___closed__2));
lean_inc_ref(v_e_4821_);
v___x_4837_ = l_Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0(v_e_4821_, v_pre_4835_, v___f_4836_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
if (lean_obj_tag(v___x_4837_) == 0)
{
lean_object* v_a_4838_; lean_object* v___x_4839_; 
v_a_4838_ = lean_ctor_get(v___x_4837_, 0);
lean_inc_n(v_a_4838_, 2);
lean_dec_ref(v___x_4837_);
v___x_4839_ = l_Lean_Meta_mkEqRefl(v_a_4838_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
if (lean_obj_tag(v___x_4839_) == 0)
{
lean_object* v_a_4840_; lean_object* v___x_4841_; 
v_a_4840_ = lean_ctor_get(v___x_4839_, 0);
lean_inc(v_a_4840_);
lean_dec_ref(v___x_4839_);
lean_inc(v_a_4838_);
v___x_4841_ = l_Lean_Meta_mkEq(v_e_4821_, v_a_4838_, v_a_4822_, v_a_4823_, v_a_4824_, v_a_4825_);
if (lean_obj_tag(v___x_4841_) == 0)
{
lean_object* v_a_4842_; lean_object* v___x_4844_; uint8_t v_isShared_4845_; uint8_t v_isSharedCheck_4855_; 
v_a_4842_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4855_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4855_ == 0)
{
v___x_4844_ = v___x_4841_;
v_isShared_4845_ = v_isSharedCheck_4855_;
goto v_resetjp_4843_;
}
else
{
lean_inc(v_a_4842_);
lean_dec(v___x_4841_);
v___x_4844_ = lean_box(0);
v_isShared_4845_ = v_isSharedCheck_4855_;
goto v_resetjp_4843_;
}
v_resetjp_4843_:
{
uint8_t v___x_4846_; lean_object* v___x_4847_; lean_object* v___x_4849_; 
v___x_4846_ = 1;
v___x_4847_ = l_Lean_Meta_mkExpectedPropHint(v_a_4840_, v_a_4842_);
if (v_isShared_4834_ == 0)
{
lean_ctor_set(v___x_4833_, 0, v___x_4847_);
v___x_4849_ = v___x_4833_;
goto v_reusejp_4848_;
}
else
{
lean_object* v_reuseFailAlloc_4854_; 
v_reuseFailAlloc_4854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4854_, 0, v___x_4847_);
v___x_4849_ = v_reuseFailAlloc_4854_;
goto v_reusejp_4848_;
}
v_reusejp_4848_:
{
lean_object* v___x_4850_; lean_object* v___x_4852_; 
v___x_4850_ = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(v___x_4850_, 0, v_a_4838_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
lean_ctor_set_uint8(v___x_4850_, sizeof(void*)*2, v___x_4846_);
if (v_isShared_4845_ == 0)
{
lean_ctor_set(v___x_4844_, 0, v___x_4850_);
v___x_4852_ = v___x_4844_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v___x_4850_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
else
{
lean_object* v_a_4856_; lean_object* v___x_4858_; uint8_t v_isShared_4859_; uint8_t v_isSharedCheck_4863_; 
lean_dec(v_a_4840_);
lean_dec(v_a_4838_);
lean_del_object(v___x_4833_);
v_a_4856_ = lean_ctor_get(v___x_4841_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4841_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4858_ = v___x_4841_;
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
else
{
lean_inc(v_a_4856_);
lean_dec(v___x_4841_);
v___x_4858_ = lean_box(0);
v_isShared_4859_ = v_isSharedCheck_4863_;
goto v_resetjp_4857_;
}
v_resetjp_4857_:
{
lean_object* v___x_4861_; 
if (v_isShared_4859_ == 0)
{
v___x_4861_ = v___x_4858_;
goto v_reusejp_4860_;
}
else
{
lean_object* v_reuseFailAlloc_4862_; 
v_reuseFailAlloc_4862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4862_, 0, v_a_4856_);
v___x_4861_ = v_reuseFailAlloc_4862_;
goto v_reusejp_4860_;
}
v_reusejp_4860_:
{
return v___x_4861_;
}
}
}
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4871_; 
lean_dec(v_a_4838_);
lean_del_object(v___x_4833_);
lean_dec_ref(v_e_4821_);
v_a_4864_ = lean_ctor_get(v___x_4839_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4839_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4866_ = v___x_4839_;
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4839_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4869_; 
if (v_isShared_4867_ == 0)
{
v___x_4869_ = v___x_4866_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4864_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
}
}
else
{
lean_object* v_a_4872_; lean_object* v___x_4874_; uint8_t v_isShared_4875_; uint8_t v_isSharedCheck_4879_; 
lean_del_object(v___x_4833_);
lean_dec_ref(v_e_4821_);
v_a_4872_ = lean_ctor_get(v___x_4837_, 0);
v_isSharedCheck_4879_ = !lean_is_exclusive(v___x_4837_);
if (v_isSharedCheck_4879_ == 0)
{
v___x_4874_ = v___x_4837_;
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
else
{
lean_inc(v_a_4872_);
lean_dec(v___x_4837_);
v___x_4874_ = lean_box(0);
v_isShared_4875_ = v_isSharedCheck_4879_;
goto v_resetjp_4873_;
}
v_resetjp_4873_:
{
lean_object* v___x_4877_; 
if (v_isShared_4875_ == 0)
{
v___x_4877_ = v___x_4874_;
goto v_reusejp_4876_;
}
else
{
lean_object* v_reuseFailAlloc_4878_; 
v_reuseFailAlloc_4878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4878_, 0, v_a_4872_);
v___x_4877_ = v_reuseFailAlloc_4878_;
goto v_reusejp_4876_;
}
v_reusejp_4876_:
{
return v___x_4877_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_replacePreMatchCond___boxed(lean_object* v_e_4882_, lean_object* v_a_4883_, lean_object* v_a_4884_, lean_object* v_a_4885_, lean_object* v_a_4886_, lean_object* v_a_4887_){
_start:
{
lean_object* v_res_4888_; 
v_res_4888_ = l_Lean_Meta_Grind_replacePreMatchCond(v_e_4882_, v_a_4883_, v_a_4884_, v_a_4885_, v_a_4886_);
lean_dec(v_a_4886_);
lean_dec_ref(v_a_4885_);
lean_dec(v_a_4884_);
lean_dec_ref(v_a_4883_);
return v_res_4888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(lean_object* v_00_u03b1_4889_, lean_object* v_x_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_, lean_object* v___y_4894_, lean_object* v___y_4895_){
_start:
{
lean_object* v___x_4897_; 
v___x_4897_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___redArg(v_x_4890_, v___y_4891_, v___y_4892_, v___y_4893_, v___y_4894_, v___y_4895_);
return v___x_4897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4___boxed(lean_object* v_00_u03b1_4898_, lean_object* v_x_4899_, lean_object* v___y_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v_res_4906_; 
v_res_4906_ = l_Lean_Core_withIncRecDepth___at___00__private_Lean_Meta_Transform_0__Lean_Core_transform_visit___at___00Lean_Core_transform___at___00Lean_Meta_Grind_replacePreMatchCond_spec__0_spec__0_spec__4(v_00_u03b1_4898_, v_x_4899_, v___y_4900_, v___y_4901_, v___y_4902_, v___y_4903_, v___y_4904_);
lean_dec(v___y_4904_);
lean_dec_ref(v___y_4903_);
lean_dec(v___y_4902_);
lean_dec_ref(v___y_4901_);
lean_dec(v___y_4900_);
return v_res_4906_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isIte(lean_object* v_e_4910_){
_start:
{
lean_object* v___x_4911_; uint8_t v___x_4912_; 
v___x_4911_ = ((lean_object*)(l_Lean_Meta_Grind_isIte___closed__1));
v___x_4912_ = l_Lean_Expr_isAppOf(v_e_4910_, v___x_4911_);
if (v___x_4912_ == 0)
{
return v___x_4912_;
}
else
{
lean_object* v___x_4913_; lean_object* v___x_4914_; uint8_t v___x_4915_; 
v___x_4913_ = lean_unsigned_to_nat(5u);
v___x_4914_ = l_Lean_Expr_getAppNumArgs(v_e_4910_);
v___x_4915_ = lean_nat_dec_le(v___x_4913_, v___x_4914_);
lean_dec(v___x_4914_);
return v___x_4915_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isIte___boxed(lean_object* v_e_4916_){
_start:
{
uint8_t v_res_4917_; lean_object* v_r_4918_; 
v_res_4917_ = l_Lean_Meta_Grind_isIte(v_e_4916_);
lean_dec_ref(v_e_4916_);
v_r_4918_ = lean_box(v_res_4917_);
return v_r_4918_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isDIte(lean_object* v_e_4922_){
_start:
{
lean_object* v___x_4923_; uint8_t v___x_4924_; 
v___x_4923_ = ((lean_object*)(l_Lean_Meta_Grind_isDIte___closed__1));
v___x_4924_ = l_Lean_Expr_isAppOf(v_e_4922_, v___x_4923_);
if (v___x_4924_ == 0)
{
return v___x_4924_;
}
else
{
lean_object* v___x_4925_; lean_object* v___x_4926_; uint8_t v___x_4927_; 
v___x_4925_ = lean_unsigned_to_nat(5u);
v___x_4926_ = l_Lean_Expr_getAppNumArgs(v_e_4922_);
v___x_4927_ = lean_nat_dec_le(v___x_4925_, v___x_4926_);
lean_dec(v___x_4926_);
return v___x_4927_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isDIte___boxed(lean_object* v_e_4928_){
_start:
{
uint8_t v_res_4929_; lean_object* v_r_4930_; 
v_res_4929_ = l_Lean_Meta_Grind_isDIte(v_e_4928_);
lean_dec_ref(v_e_4928_);
v_r_4930_ = lean_box(v_res_4929_);
return v_r_4930_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp(lean_object* v_e_4931_){
_start:
{
uint8_t v___x_4932_; 
v___x_4932_ = l_Lean_Expr_isApp(v_e_4931_);
if (v___x_4932_ == 0)
{
lean_object* v___x_4933_; 
v___x_4933_ = lean_box(0);
return v___x_4933_;
}
else
{
lean_object* v_f_4934_; uint8_t v___x_4935_; 
v_f_4934_ = l_Lean_Expr_appFn_x21(v_e_4931_);
v___x_4935_ = l_Lean_Expr_isApp(v_f_4934_);
if (v___x_4935_ == 0)
{
lean_object* v___x_4936_; 
lean_dec_ref(v_f_4934_);
v___x_4936_ = lean_box(0);
return v___x_4936_;
}
else
{
lean_object* v___x_4937_; lean_object* v___x_4938_; 
v___x_4937_ = l_Lean_Expr_appFn_x21(v_f_4934_);
lean_dec_ref(v_f_4934_);
v___x_4938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4938_, 0, v___x_4937_);
return v___x_4938_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getBinOp___boxed(lean_object* v_e_4939_){
_start:
{
lean_object* v_res_4940_; 
v_res_4940_ = l_Lean_Meta_Grind_getBinOp(v_e_4939_);
lean_dec_ref(v_e_4939_);
return v_res_4940_;
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
