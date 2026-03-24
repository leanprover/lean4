// Lean compiler output
// Module: Lean.Meta.Tactic.Subst
// Imports: public import Lean.Meta.AppBuilder public import Lean.Meta.MatchUtil public import Lean.Meta.Tactic.Assert
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
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Meta_FVarSubst_insert(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_MVarId_revert(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*, uint8_t);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_userName(lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_FVarSubst_empty;
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_substCore_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_substCore_spec__1___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_substCore_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "after intro rest "};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__1___closed__1;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Tactic.Subst"};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__4_value;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.substCore"};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__5 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__5_value;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__1___closed__7;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_h"};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__8_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_substCore___lam__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(32, 79, 207, 54, 208, 114, 216, 130)}};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__9 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__9(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__9___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__10(lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__0_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 29, 29, 32, 53, 17, 69, 167)}};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__1 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__1_value;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid equality proof, it is not of the form "};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__3;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "\nafter WHNF, variable expected, but obtained"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__4_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__5;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "argument must be an equality proof"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__6 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__6_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__2___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__6_value)}};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__7 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__7_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__8;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__9;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "reverted variables "};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__10 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__10_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__11;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "after intro2 "};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__12 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__12_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__13;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "after revert "};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__14 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__14_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__15;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__16 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__16_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__17;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "' occurs at"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__18 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__18_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__19;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__20 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__20_value;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__21 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__21_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__2___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__20_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_substCore___lam__2___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__21_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_substCore___lam__2___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__22_value_aux_1),((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 247, 229, 3, 213, 123, 220, 1)}};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__22 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__22_value;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "substituting "};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__23 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__23_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__24;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " (id: "};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__25 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__25_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__26;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ") with "};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__27 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__27_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__28;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "(x = t)"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__29 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__29_value;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "(t = x)"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__30 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__30_value;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_heqToEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l_Lean_Meta_heqToEq___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_heqToEq___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_heqToEq___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_heqToEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_object* l_Lean_Meta_heqToEq___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_heqToEq___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_substVar___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "did not find equation for eliminating '"};
static const lean_object* l_Lean_Meta_substVar___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_substVar___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_substVar___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substVar___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_substVar___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "variable '"};
static const lean_object* l_Lean_Meta_substVar___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_substVar___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_substVar___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substVar___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_substVar___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "' is a let-declaration"};
static const lean_object* l_Lean_Meta_substVar___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_substVar___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_substVar___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substVar___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_substEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 65, .m_capacity = 65, .m_length = 64, .m_data = "invalid equality proof, it is not of the form (x = t) or (t = x)"};
static const lean_object* l_Lean_Meta_substEq___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_substEq___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_substEq___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substEq___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "not an arrow type"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "variable "};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = " has forward dependencies"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "equality rhs not a free variable"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "not an equality"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__10_value;
static const lean_ctor_object l_Lean_Meta_introSubstEq___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__11_value;
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "homo_ndrec"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__12_value;
static const lean_ctor_object l_Lean_Meta_introSubstEq___lam__0___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_heqToEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l_Lean_Meta_introSubstEq___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__13_value_aux_0),((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__12_value),LEAN_SCALAR_PTR_LITERAL(48, 43, 236, 51, 159, 219, 21, 78)}};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__13_value;
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "homo_ndrec_symm"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__14_value;
static const lean_ctor_object l_Lean_Meta_introSubstEq___lam__0___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_heqToEq___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l_Lean_Meta_introSubstEq___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__15_value_aux_0),((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__14_value),LEAN_SCALAR_PTR_LITERAL(50, 157, 119, 52, 76, 119, 237, 183)}};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__15_value;
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 43, .m_capacity = 43, .m_length = 42, .m_data = "hetereogenenous equality isn't homogeneous"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__16 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__17;
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__18 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__18_value;
static const lean_ctor_object l_Lean_Meta_introSubstEq___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_introSubstEq___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__19_value_aux_0),((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(115, 164, 251, 202, 217, 58, 77, 179)}};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__19 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__19_value;
static const lean_string_object l_Lean_Meta_introSubstEq___lam__0___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ndrec_symm"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__20 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__20_value;
static const lean_ctor_object l_Lean_Meta_introSubstEq___lam__0___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__10_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Meta_introSubstEq___lam__0___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__21_value_aux_0),((lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__20_value),LEAN_SCALAR_PTR_LITERAL(71, 160, 179, 99, 219, 64, 47, 167)}};
static const lean_object* l_Lean_Meta_introSubstEq___lam__0___closed__21 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__0___closed__21_value;
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_introSubstEq___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "introSubstEq: now assigned\?"};
static const lean_object* l_Lean_Meta_introSubstEq___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_introSubstEq___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___lam__1___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_introSubstEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "introSubstEq"};
static const lean_object* l_Lean_Meta_introSubstEq___closed__0 = (const lean_object*)&l_Lean_Meta_introSubstEq___closed__0_value;
static const lean_ctor_object l_Lean_Meta_introSubstEq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_introSubstEq___closed__0_value),LEAN_SCALAR_PTR_LITERAL(184, 191, 181, 66, 111, 91, 242, 60)}};
static const lean_object* l_Lean_Meta_introSubstEq___closed__1 = (const lean_object*)&l_Lean_Meta_introSubstEq___closed__1_value;
static const lean_string_object l_Lean_Meta_introSubstEq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "introSubstEq falling back to intro\n"};
static const lean_object* l_Lean_Meta_introSubstEq___closed__2 = (const lean_object*)&l_Lean_Meta_introSubstEq___closed__2_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___closed__3;
static const lean_string_object l_Lean_Meta_introSubstEq___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Meta_introSubstEq___closed__4 = (const lean_object*)&l_Lean_Meta_introSubstEq___closed__4_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___closed__5;
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__20_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__21_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Subst"};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 155, 87, 188, 107, 213, 207, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(46, 207, 184, 108, 123, 194, 122, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 208, 80, 10, 197, 128, 95, 79)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__20_value),LEAN_SCALAR_PTR_LITERAL(7, 62, 56, 132, 111, 90, 85, 225)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(182, 144, 37, 101, 63, 174, 15, 237)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(135, 83, 107, 230, 66, 113, 62, 91)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(250, 5, 105, 244, 179, 13, 109, 21)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__20_value),LEAN_SCALAR_PTR_LITERAL(254, 30, 149, 183, 84, 179, 28, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__21_value),LEAN_SCALAR_PTR_LITERAL(99, 160, 169, 64, 171, 126, 88, 158)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(131, 140, 20, 111, 56, 127, 145, 46)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)(((size_t)(1630641459) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(162, 248, 22, 106, 83, 230, 167, 13)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(141, 29, 223, 229, 152, 3, 25, 165)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(77, 203, 155, 156, 13, 176, 49, 33)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(224, 94, 43, 255, 16, 68, 129, 142)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg___boxed(lean_object* v_e_26_, lean_object* v___y_27_, lean_object* v___y_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_e_26_, v___y_27_);
lean_dec(v___y_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0(lean_object* v_e_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_e_30_, v___y_32_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___boxed(lean_object* v_e_37_, lean_object* v___y_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0(v_e_37_, v___y_38_, v___y_39_, v___y_40_, v___y_41_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
lean_dec(v___y_39_);
lean_dec_ref(v___y_38_);
return v_res_43_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__1(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___f_51_; lean_object* v___x_27672__overap_52_; lean_object* v___x_53_; 
v___f_51_ = ((lean_object*)(l_panic___at___00Lean_Meta_substCore_spec__1___closed__0));
v___x_27672__overap_52_ = lean_panic_fn(v___f_51_, v_msg_45_);
v___x_53_ = lean_apply_5(v___x_27672__overap_52_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, lean_box(0));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__1___boxed(lean_object* v_msg_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_panic___at___00Lean_Meta_substCore_spec__1(v_msg_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg(lean_object* v_cls_64_, lean_object* v___y_65_){
_start:
{
lean_object* v_options_67_; uint8_t v_hasTrace_68_; 
v_options_67_ = lean_ctor_get(v___y_65_, 2);
v_hasTrace_68_ = lean_ctor_get_uint8(v_options_67_, sizeof(void*)*1);
if (v_hasTrace_68_ == 0)
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_dec(v_cls_64_);
v___x_69_ = lean_box(v_hasTrace_68_);
v___x_70_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
return v___x_70_;
}
else
{
lean_object* v_inheritedTraceOptions_71_; lean_object* v___x_72_; lean_object* v___x_73_; uint8_t v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_inheritedTraceOptions_71_ = lean_ctor_get(v___y_65_, 13);
v___x_72_ = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg___closed__1));
v___x_73_ = l_Lean_Name_append(v___x_72_, v_cls_64_);
v___x_74_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_71_, v_options_67_, v___x_73_);
lean_dec(v___x_73_);
v___x_75_ = lean_box(v___x_74_);
v___x_76_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg___boxed(lean_object* v_cls_77_, lean_object* v___y_78_, lean_object* v___y_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg(v_cls_77_, v___y_78_);
lean_dec_ref(v___y_78_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3(lean_object* v_cls_81_, lean_object* v___y_82_, lean_object* v___y_83_, lean_object* v___y_84_, lean_object* v___y_85_){
_start:
{
lean_object* v___x_87_; 
v___x_87_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg(v_cls_81_, v___y_84_);
return v___x_87_;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___boxed(lean_object* v_cls_88_, lean_object* v___y_89_, lean_object* v___y_90_, lean_object* v___y_91_, lean_object* v___y_92_, lean_object* v___y_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3(v_cls_88_, v___y_89_, v___y_90_, v___y_91_, v___y_92_);
lean_dec(v___y_92_);
lean_dec_ref(v___y_91_);
lean_dec(v___y_90_);
lean_dec_ref(v___y_89_);
return v_res_94_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__0(lean_object* v_x_95_){
_start:
{
uint8_t v___x_96_; 
v___x_96_ = 0;
return v___x_96_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__0___boxed(lean_object* v_x_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__0(v_x_97_);
lean_dec(v_x_97_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__1(lean_object* v_fvarId_100_, lean_object* v_x_101_){
_start:
{
uint8_t v___x_102_; 
v___x_102_ = l_Lean_instBEqFVarId_beq(v_fvarId_100_, v_x_101_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__1___boxed(lean_object* v_fvarId_103_, lean_object* v_x_104_){
_start:
{
uint8_t v_res_105_; lean_object* v_r_106_; 
v_res_105_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__1(v_fvarId_103_, v_x_104_);
lean_dec(v_x_104_);
lean_dec(v_fvarId_103_);
v_r_106_ = lean_box(v_res_105_);
return v_r_106_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__1(void){
_start:
{
lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_108_ = lean_box(0);
v___x_109_ = lean_unsigned_to_nat(16u);
v___x_110_ = lean_mk_array(v___x_109_, v___x_108_);
return v___x_110_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_111_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__1);
v___x_112_ = lean_unsigned_to_nat(0u);
v___x_113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_113_, 0, v___x_112_);
lean_ctor_set(v___x_113_, 1, v___x_111_);
return v___x_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(lean_object* v_e_114_, lean_object* v_fvarId_115_, lean_object* v___y_116_){
_start:
{
lean_object* v___x_118_; uint8_t v_fst_120_; lean_object* v_mctx_121_; lean_object* v___y_139_; lean_object* v_mctx_144_; lean_object* v___f_145_; lean_object* v___f_146_; lean_object* v___x_147_; lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_118_ = lean_st_ref_get(v___y_116_);
v_mctx_144_ = lean_ctor_get(v___x_118_, 0);
lean_inc_ref(v_mctx_144_);
lean_dec(v___x_118_);
v___f_145_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__0));
v___f_146_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_146_, 0, v_fvarId_115_);
v___x_147_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___closed__2);
lean_inc_ref(v_mctx_144_);
v___x_148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_148_, 0, v___x_147_);
lean_ctor_set(v___x_148_, 1, v_mctx_144_);
v___x_149_ = l_Lean_Expr_hasFVar(v_e_114_);
if (v___x_149_ == 0)
{
uint8_t v___x_150_; 
v___x_150_ = l_Lean_Expr_hasMVar(v_e_114_);
if (v___x_150_ == 0)
{
lean_dec_ref(v___x_148_);
lean_dec_ref(v___f_146_);
lean_dec_ref(v_e_114_);
v_fst_120_ = v___x_150_;
v_mctx_121_ = v_mctx_144_;
goto v___jp_119_;
}
else
{
lean_object* v___x_151_; 
lean_dec_ref(v_mctx_144_);
v___x_151_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_146_, v___f_145_, v_e_114_, v___x_148_);
v___y_139_ = v___x_151_;
goto v___jp_138_;
}
}
else
{
lean_object* v___x_152_; 
lean_dec_ref(v_mctx_144_);
v___x_152_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_146_, v___f_145_, v_e_114_, v___x_148_);
v___y_139_ = v___x_152_;
goto v___jp_138_;
}
v___jp_119_:
{
lean_object* v___x_122_; lean_object* v_cache_123_; lean_object* v_zetaDeltaFVarIds_124_; lean_object* v_postponed_125_; lean_object* v_diag_126_; lean_object* v___x_128_; uint8_t v_isShared_129_; uint8_t v_isSharedCheck_136_; 
v___x_122_ = lean_st_ref_take(v___y_116_);
v_cache_123_ = lean_ctor_get(v___x_122_, 1);
v_zetaDeltaFVarIds_124_ = lean_ctor_get(v___x_122_, 2);
v_postponed_125_ = lean_ctor_get(v___x_122_, 3);
v_diag_126_ = lean_ctor_get(v___x_122_, 4);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_136_ == 0)
{
lean_object* v_unused_137_; 
v_unused_137_ = lean_ctor_get(v___x_122_, 0);
lean_dec(v_unused_137_);
v___x_128_ = v___x_122_;
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
else
{
lean_inc(v_diag_126_);
lean_inc(v_postponed_125_);
lean_inc(v_zetaDeltaFVarIds_124_);
lean_inc(v_cache_123_);
lean_dec(v___x_122_);
v___x_128_ = lean_box(0);
v_isShared_129_ = v_isSharedCheck_136_;
goto v_resetjp_127_;
}
v_resetjp_127_:
{
lean_object* v___x_131_; 
if (v_isShared_129_ == 0)
{
lean_ctor_set(v___x_128_, 0, v_mctx_121_);
v___x_131_ = v___x_128_;
goto v_reusejp_130_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_mctx_121_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v_cache_123_);
lean_ctor_set(v_reuseFailAlloc_135_, 2, v_zetaDeltaFVarIds_124_);
lean_ctor_set(v_reuseFailAlloc_135_, 3, v_postponed_125_);
lean_ctor_set(v_reuseFailAlloc_135_, 4, v_diag_126_);
v___x_131_ = v_reuseFailAlloc_135_;
goto v_reusejp_130_;
}
v_reusejp_130_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_st_ref_set(v___y_116_, v___x_131_);
v___x_133_ = lean_box(v_fst_120_);
v___x_134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_134_, 0, v___x_133_);
return v___x_134_;
}
}
}
v___jp_138_:
{
lean_object* v_snd_140_; lean_object* v_fst_141_; lean_object* v_mctx_142_; uint8_t v___x_143_; 
v_snd_140_ = lean_ctor_get(v___y_139_, 1);
lean_inc(v_snd_140_);
v_fst_141_ = lean_ctor_get(v___y_139_, 0);
lean_inc(v_fst_141_);
lean_dec_ref(v___y_139_);
v_mctx_142_ = lean_ctor_get(v_snd_140_, 1);
lean_inc_ref(v_mctx_142_);
lean_dec(v_snd_140_);
v___x_143_ = lean_unbox(v_fst_141_);
lean_dec(v_fst_141_);
v_fst_120_ = v___x_143_;
v_mctx_121_ = v_mctx_142_;
goto v___jp_119_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object* v_e_153_, lean_object* v_fvarId_154_, lean_object* v___y_155_, lean_object* v___y_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(v_e_153_, v_fvarId_154_, v___y_155_);
lean_dec(v___y_155_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5(lean_object* v_e_158_, lean_object* v_fvarId_159_, lean_object* v___y_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_){
_start:
{
lean_object* v___x_165_; 
v___x_165_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(v_e_158_, v_fvarId_159_, v___y_161_);
return v___x_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___boxed(lean_object* v_e_166_, lean_object* v_fvarId_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5(v_e_166_, v_fvarId_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(lean_object* v_mvarId_174_, lean_object* v_x_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_){
_start:
{
lean_object* v___x_181_; 
v___x_181_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_174_, v_x_175_, v___y_176_, v___y_177_, v___y_178_, v___y_179_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
v_a_182_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_181_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_181_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
v_a_190_ = lean_ctor_get(v___x_181_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_181_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_181_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_181_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg___boxed(lean_object* v_mvarId_198_, lean_object* v_x_199_, lean_object* v___y_200_, lean_object* v___y_201_, lean_object* v___y_202_, lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(v_mvarId_198_, v_x_199_, v___y_200_, v___y_201_, v___y_202_, v___y_203_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8(lean_object* v_00_u03b1_206_, lean_object* v_mvarId_207_, lean_object* v_x_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(v_mvarId_207_, v_x_208_, v___y_209_, v___y_210_, v___y_211_, v___y_212_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___boxed(lean_object* v_00_u03b1_215_, lean_object* v_mvarId_216_, lean_object* v_x_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_, lean_object* v___y_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8(v_00_u03b1_215_, v_mvarId_216_, v_x_217_, v___y_218_, v___y_219_, v___y_220_, v___y_221_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0(lean_object* v_type_224_, lean_object* v___x_225_, lean_object* v___x_226_, lean_object* v___x_227_, uint8_t v___x_228_, uint8_t v___x_229_, lean_object* v_hAux_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_){
_start:
{
lean_object* v___x_236_; 
lean_inc(v___y_234_);
lean_inc_ref(v___y_233_);
lean_inc(v___y_232_);
lean_inc_ref(v___y_231_);
lean_inc_ref(v_hAux_230_);
v___x_236_ = l_Lean_Meta_mkEqSymm(v_hAux_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
if (lean_obj_tag(v___x_236_) == 0)
{
lean_object* v_a_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; uint8_t v___x_242_; lean_object* v___x_243_; 
v_a_237_ = lean_ctor_get(v___x_236_, 0);
lean_inc(v_a_237_);
lean_dec_ref(v___x_236_);
v___x_238_ = l_Lean_Expr_replaceFVar(v_type_224_, v___x_225_, v_a_237_);
lean_dec(v_a_237_);
v___x_239_ = lean_mk_empty_array_with_capacity(v___x_226_);
v___x_240_ = lean_array_push(v___x_239_, v___x_227_);
v___x_241_ = lean_array_push(v___x_240_, v_hAux_230_);
v___x_242_ = 1;
v___x_243_ = l_Lean_Meta_mkLambdaFVars(v___x_241_, v___x_238_, v___x_228_, v___x_229_, v___x_228_, v___x_229_, v___x_242_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v___x_241_);
return v___x_243_;
}
else
{
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
lean_dec_ref(v_hAux_230_);
lean_dec_ref(v___x_227_);
lean_dec_ref(v___x_225_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object* v_type_244_, lean_object* v___x_245_, lean_object* v___x_246_, lean_object* v___x_247_, lean_object* v___x_248_, lean_object* v___x_249_, lean_object* v_hAux_250_, lean_object* v___y_251_, lean_object* v___y_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_){
_start:
{
uint8_t v___x_32457__boxed_256_; uint8_t v___x_32458__boxed_257_; lean_object* v_res_258_; 
v___x_32457__boxed_256_ = lean_unbox(v___x_248_);
v___x_32458__boxed_257_ = lean_unbox(v___x_249_);
v_res_258_ = l_Lean_Meta_substCore___lam__0(v_type_244_, v___x_245_, v___x_246_, v___x_247_, v___x_32457__boxed_256_, v___x_32458__boxed_257_, v_hAux_250_, v___y_251_, v___y_252_, v___y_253_, v___y_254_);
lean_dec(v___x_246_);
lean_dec_ref(v_type_244_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14_spec__15___redArg(lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_){
_start:
{
lean_object* v_ks_263_; lean_object* v_vs_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_288_; 
v_ks_263_ = lean_ctor_get(v_x_259_, 0);
v_vs_264_ = lean_ctor_get(v_x_259_, 1);
v_isSharedCheck_288_ = !lean_is_exclusive(v_x_259_);
if (v_isSharedCheck_288_ == 0)
{
v___x_266_ = v_x_259_;
v_isShared_267_ = v_isSharedCheck_288_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_vs_264_);
lean_inc(v_ks_263_);
lean_dec(v_x_259_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_288_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; uint8_t v___x_269_; 
v___x_268_ = lean_array_get_size(v_ks_263_);
v___x_269_ = lean_nat_dec_lt(v_x_260_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_273_; 
lean_dec(v_x_260_);
v___x_270_ = lean_array_push(v_ks_263_, v_x_261_);
v___x_271_ = lean_array_push(v_vs_264_, v_x_262_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v___x_271_);
lean_ctor_set(v___x_266_, 0, v___x_270_);
v___x_273_ = v___x_266_;
goto v_reusejp_272_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v___x_271_);
v___x_273_ = v_reuseFailAlloc_274_;
goto v_reusejp_272_;
}
v_reusejp_272_:
{
return v___x_273_;
}
}
else
{
lean_object* v_k_x27_275_; uint8_t v___x_276_; 
v_k_x27_275_ = lean_array_fget_borrowed(v_ks_263_, v_x_260_);
v___x_276_ = l_Lean_instBEqMVarId_beq(v_x_261_, v_k_x27_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_278_; 
if (v_isShared_267_ == 0)
{
v___x_278_ = v___x_266_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_282_; 
v_reuseFailAlloc_282_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_282_, 0, v_ks_263_);
lean_ctor_set(v_reuseFailAlloc_282_, 1, v_vs_264_);
v___x_278_ = v_reuseFailAlloc_282_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_unsigned_to_nat(1u);
v___x_280_ = lean_nat_add(v_x_260_, v___x_279_);
lean_dec(v_x_260_);
v_x_259_ = v___x_278_;
v_x_260_ = v___x_280_;
goto _start;
}
}
else
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_283_ = lean_array_fset(v_ks_263_, v_x_260_, v_x_261_);
v___x_284_ = lean_array_fset(v_vs_264_, v_x_260_, v_x_262_);
lean_dec(v_x_260_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v___x_284_);
lean_ctor_set(v___x_266_, 0, v___x_283_);
v___x_286_ = v___x_266_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v___x_283_);
lean_ctor_set(v_reuseFailAlloc_287_, 1, v___x_284_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14___redArg(lean_object* v_n_289_, lean_object* v_k_290_, lean_object* v_v_291_){
_start:
{
lean_object* v___x_292_; lean_object* v___x_293_; 
v___x_292_ = lean_unsigned_to_nat(0u);
v___x_293_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14_spec__15___redArg(v_n_289_, v___x_292_, v_k_290_, v_v_291_);
return v___x_293_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__0(void){
_start:
{
size_t v___x_294_; size_t v___x_295_; size_t v___x_296_; 
v___x_294_ = ((size_t)5ULL);
v___x_295_ = ((size_t)1ULL);
v___x_296_ = lean_usize_shift_left(v___x_295_, v___x_294_);
return v___x_296_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__1(void){
_start:
{
size_t v___x_297_; size_t v___x_298_; size_t v___x_299_; 
v___x_297_ = ((size_t)1ULL);
v___x_298_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__0);
v___x_299_ = lean_usize_sub(v___x_298_, v___x_297_);
return v___x_299_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__2(void){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg(lean_object* v_x_301_, size_t v_x_302_, size_t v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
if (lean_obj_tag(v_x_301_) == 0)
{
lean_object* v_es_306_; size_t v___x_307_; size_t v___x_308_; size_t v___x_309_; size_t v___x_310_; lean_object* v_j_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v_es_306_ = lean_ctor_get(v_x_301_, 0);
v___x_307_ = ((size_t)5ULL);
v___x_308_ = ((size_t)1ULL);
v___x_309_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__1);
v___x_310_ = lean_usize_land(v_x_302_, v___x_309_);
v_j_311_ = lean_usize_to_nat(v___x_310_);
v___x_312_ = lean_array_get_size(v_es_306_);
v___x_313_ = lean_nat_dec_lt(v_j_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_dec(v_j_311_);
lean_dec(v_x_305_);
lean_dec(v_x_304_);
return v_x_301_;
}
else
{
lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_350_; 
lean_inc_ref(v_es_306_);
v_isSharedCheck_350_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_350_ == 0)
{
lean_object* v_unused_351_; 
v_unused_351_ = lean_ctor_get(v_x_301_, 0);
lean_dec(v_unused_351_);
v___x_315_ = v_x_301_;
v_isShared_316_ = v_isSharedCheck_350_;
goto v_resetjp_314_;
}
else
{
lean_dec(v_x_301_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_350_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v_v_317_; lean_object* v___x_318_; lean_object* v_xs_x27_319_; lean_object* v___y_321_; 
v_v_317_ = lean_array_fget(v_es_306_, v_j_311_);
v___x_318_ = lean_box(0);
v_xs_x27_319_ = lean_array_fset(v_es_306_, v_j_311_, v___x_318_);
switch(lean_obj_tag(v_v_317_))
{
case 0:
{
lean_object* v_key_326_; lean_object* v_val_327_; lean_object* v___x_329_; uint8_t v_isShared_330_; uint8_t v_isSharedCheck_337_; 
v_key_326_ = lean_ctor_get(v_v_317_, 0);
v_val_327_ = lean_ctor_get(v_v_317_, 1);
v_isSharedCheck_337_ = !lean_is_exclusive(v_v_317_);
if (v_isSharedCheck_337_ == 0)
{
v___x_329_ = v_v_317_;
v_isShared_330_ = v_isSharedCheck_337_;
goto v_resetjp_328_;
}
else
{
lean_inc(v_val_327_);
lean_inc(v_key_326_);
lean_dec(v_v_317_);
v___x_329_ = lean_box(0);
v_isShared_330_ = v_isSharedCheck_337_;
goto v_resetjp_328_;
}
v_resetjp_328_:
{
uint8_t v___x_331_; 
v___x_331_ = l_Lean_instBEqMVarId_beq(v_x_304_, v_key_326_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; 
lean_del_object(v___x_329_);
v___x_332_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_326_, v_val_327_, v_x_304_, v_x_305_);
v___x_333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
v___y_321_ = v___x_333_;
goto v___jp_320_;
}
else
{
lean_object* v___x_335_; 
lean_dec(v_val_327_);
lean_dec(v_key_326_);
if (v_isShared_330_ == 0)
{
lean_ctor_set(v___x_329_, 1, v_x_305_);
lean_ctor_set(v___x_329_, 0, v_x_304_);
v___x_335_ = v___x_329_;
goto v_reusejp_334_;
}
else
{
lean_object* v_reuseFailAlloc_336_; 
v_reuseFailAlloc_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_336_, 0, v_x_304_);
lean_ctor_set(v_reuseFailAlloc_336_, 1, v_x_305_);
v___x_335_ = v_reuseFailAlloc_336_;
goto v_reusejp_334_;
}
v_reusejp_334_:
{
v___y_321_ = v___x_335_;
goto v___jp_320_;
}
}
}
}
case 1:
{
lean_object* v_node_338_; lean_object* v___x_340_; uint8_t v_isShared_341_; uint8_t v_isSharedCheck_348_; 
v_node_338_ = lean_ctor_get(v_v_317_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v_v_317_);
if (v_isSharedCheck_348_ == 0)
{
v___x_340_ = v_v_317_;
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
else
{
lean_inc(v_node_338_);
lean_dec(v_v_317_);
v___x_340_ = lean_box(0);
v_isShared_341_ = v_isSharedCheck_348_;
goto v_resetjp_339_;
}
v_resetjp_339_:
{
size_t v___x_342_; size_t v___x_343_; lean_object* v___x_344_; lean_object* v___x_346_; 
v___x_342_ = lean_usize_shift_right(v_x_302_, v___x_307_);
v___x_343_ = lean_usize_add(v_x_303_, v___x_308_);
v___x_344_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg(v_node_338_, v___x_342_, v___x_343_, v_x_304_, v_x_305_);
if (v_isShared_341_ == 0)
{
lean_ctor_set(v___x_340_, 0, v___x_344_);
v___x_346_ = v___x_340_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_344_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
v___y_321_ = v___x_346_;
goto v___jp_320_;
}
}
}
default: 
{
lean_object* v___x_349_; 
v___x_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_349_, 0, v_x_304_);
lean_ctor_set(v___x_349_, 1, v_x_305_);
v___y_321_ = v___x_349_;
goto v___jp_320_;
}
}
v___jp_320_:
{
lean_object* v___x_322_; lean_object* v___x_324_; 
v___x_322_ = lean_array_fset(v_xs_x27_319_, v_j_311_, v___y_321_);
lean_dec(v_j_311_);
if (v_isShared_316_ == 0)
{
lean_ctor_set(v___x_315_, 0, v___x_322_);
v___x_324_ = v___x_315_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v___x_322_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
else
{
lean_object* v_ks_352_; lean_object* v_vs_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_373_; 
v_ks_352_ = lean_ctor_get(v_x_301_, 0);
v_vs_353_ = lean_ctor_get(v_x_301_, 1);
v_isSharedCheck_373_ = !lean_is_exclusive(v_x_301_);
if (v_isSharedCheck_373_ == 0)
{
v___x_355_ = v_x_301_;
v_isShared_356_ = v_isSharedCheck_373_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_vs_353_);
lean_inc(v_ks_352_);
lean_dec(v_x_301_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_373_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v_ks_352_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v_vs_353_);
v___x_358_ = v_reuseFailAlloc_372_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v_newNode_359_; uint8_t v___y_361_; size_t v___x_367_; uint8_t v___x_368_; 
v_newNode_359_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14___redArg(v___x_358_, v_x_304_, v_x_305_);
v___x_367_ = ((size_t)7ULL);
v___x_368_ = lean_usize_dec_le(v___x_367_, v_x_303_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_369_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_359_);
v___x_370_ = lean_unsigned_to_nat(4u);
v___x_371_ = lean_nat_dec_lt(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
v___y_361_ = v___x_371_;
goto v___jp_360_;
}
else
{
v___y_361_ = v___x_368_;
goto v___jp_360_;
}
v___jp_360_:
{
if (v___y_361_ == 0)
{
lean_object* v_ks_362_; lean_object* v_vs_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; 
v_ks_362_ = lean_ctor_get(v_newNode_359_, 0);
lean_inc_ref(v_ks_362_);
v_vs_363_ = lean_ctor_get(v_newNode_359_, 1);
lean_inc_ref(v_vs_363_);
lean_dec_ref(v_newNode_359_);
v___x_364_ = lean_unsigned_to_nat(0u);
v___x_365_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__2);
v___x_366_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15___redArg(v_x_303_, v_ks_362_, v_vs_363_, v___x_364_, v___x_365_);
lean_dec_ref(v_vs_363_);
lean_dec_ref(v_ks_362_);
return v___x_366_;
}
else
{
return v_newNode_359_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15___redArg(size_t v_depth_374_, lean_object* v_keys_375_, lean_object* v_vals_376_, lean_object* v_i_377_, lean_object* v_entries_378_){
_start:
{
lean_object* v___x_379_; uint8_t v___x_380_; 
v___x_379_ = lean_array_get_size(v_keys_375_);
v___x_380_ = lean_nat_dec_lt(v_i_377_, v___x_379_);
if (v___x_380_ == 0)
{
lean_dec(v_i_377_);
return v_entries_378_;
}
else
{
lean_object* v_k_381_; lean_object* v_v_382_; uint64_t v___x_383_; size_t v_h_384_; size_t v___x_385_; lean_object* v___x_386_; size_t v___x_387_; size_t v___x_388_; size_t v___x_389_; size_t v_h_390_; lean_object* v___x_391_; lean_object* v___x_392_; 
v_k_381_ = lean_array_fget_borrowed(v_keys_375_, v_i_377_);
v_v_382_ = lean_array_fget_borrowed(v_vals_376_, v_i_377_);
v___x_383_ = l_Lean_instHashableMVarId_hash(v_k_381_);
v_h_384_ = lean_uint64_to_usize(v___x_383_);
v___x_385_ = ((size_t)5ULL);
v___x_386_ = lean_unsigned_to_nat(1u);
v___x_387_ = ((size_t)1ULL);
v___x_388_ = lean_usize_sub(v_depth_374_, v___x_387_);
v___x_389_ = lean_usize_mul(v___x_385_, v___x_388_);
v_h_390_ = lean_usize_shift_right(v_h_384_, v___x_389_);
v___x_391_ = lean_nat_add(v_i_377_, v___x_386_);
lean_dec(v_i_377_);
lean_inc(v_v_382_);
lean_inc(v_k_381_);
v___x_392_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg(v_entries_378_, v_h_390_, v_depth_374_, v_k_381_, v_v_382_);
v_i_377_ = v___x_391_;
v_entries_378_ = v___x_392_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15___redArg___boxed(lean_object* v_depth_394_, lean_object* v_keys_395_, lean_object* v_vals_396_, lean_object* v_i_397_, lean_object* v_entries_398_){
_start:
{
size_t v_depth_boxed_399_; lean_object* v_res_400_; 
v_depth_boxed_399_ = lean_unbox_usize(v_depth_394_);
lean_dec(v_depth_394_);
v_res_400_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15___redArg(v_depth_boxed_399_, v_keys_395_, v_vals_396_, v_i_397_, v_entries_398_);
lean_dec_ref(v_vals_396_);
lean_dec_ref(v_keys_395_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___boxed(lean_object* v_x_401_, lean_object* v_x_402_, lean_object* v_x_403_, lean_object* v_x_404_, lean_object* v_x_405_){
_start:
{
size_t v_x_32590__boxed_406_; size_t v_x_32591__boxed_407_; lean_object* v_res_408_; 
v_x_32590__boxed_406_ = lean_unbox_usize(v_x_402_);
lean_dec(v_x_402_);
v_x_32591__boxed_407_ = lean_unbox_usize(v_x_403_);
lean_dec(v_x_403_);
v_res_408_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg(v_x_401_, v_x_32590__boxed_406_, v_x_32591__boxed_407_, v_x_404_, v_x_405_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7___redArg(lean_object* v_x_409_, lean_object* v_x_410_, lean_object* v_x_411_){
_start:
{
uint64_t v___x_412_; size_t v___x_413_; size_t v___x_414_; lean_object* v___x_415_; 
v___x_412_ = l_Lean_instHashableMVarId_hash(v_x_410_);
v___x_413_ = lean_uint64_to_usize(v___x_412_);
v___x_414_ = ((size_t)1ULL);
v___x_415_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg(v_x_409_, v___x_413_, v___x_414_, v_x_410_, v_x_411_);
return v___x_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6___redArg(lean_object* v_mvarId_416_, lean_object* v_val_417_, lean_object* v___y_418_){
_start:
{
lean_object* v___x_420_; lean_object* v_mctx_421_; lean_object* v_cache_422_; lean_object* v_zetaDeltaFVarIds_423_; lean_object* v_postponed_424_; lean_object* v_diag_425_; lean_object* v___x_427_; uint8_t v_isShared_428_; uint8_t v_isSharedCheck_452_; 
v___x_420_ = lean_st_ref_take(v___y_418_);
v_mctx_421_ = lean_ctor_get(v___x_420_, 0);
v_cache_422_ = lean_ctor_get(v___x_420_, 1);
v_zetaDeltaFVarIds_423_ = lean_ctor_get(v___x_420_, 2);
v_postponed_424_ = lean_ctor_get(v___x_420_, 3);
v_diag_425_ = lean_ctor_get(v___x_420_, 4);
v_isSharedCheck_452_ = !lean_is_exclusive(v___x_420_);
if (v_isSharedCheck_452_ == 0)
{
v___x_427_ = v___x_420_;
v_isShared_428_ = v_isSharedCheck_452_;
goto v_resetjp_426_;
}
else
{
lean_inc(v_diag_425_);
lean_inc(v_postponed_424_);
lean_inc(v_zetaDeltaFVarIds_423_);
lean_inc(v_cache_422_);
lean_inc(v_mctx_421_);
lean_dec(v___x_420_);
v___x_427_ = lean_box(0);
v_isShared_428_ = v_isSharedCheck_452_;
goto v_resetjp_426_;
}
v_resetjp_426_:
{
lean_object* v_depth_429_; lean_object* v_levelAssignDepth_430_; lean_object* v_mvarCounter_431_; lean_object* v_lDepth_432_; lean_object* v_decls_433_; lean_object* v_userNames_434_; lean_object* v_lAssignment_435_; lean_object* v_eAssignment_436_; lean_object* v_dAssignment_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_451_; 
v_depth_429_ = lean_ctor_get(v_mctx_421_, 0);
v_levelAssignDepth_430_ = lean_ctor_get(v_mctx_421_, 1);
v_mvarCounter_431_ = lean_ctor_get(v_mctx_421_, 2);
v_lDepth_432_ = lean_ctor_get(v_mctx_421_, 3);
v_decls_433_ = lean_ctor_get(v_mctx_421_, 4);
v_userNames_434_ = lean_ctor_get(v_mctx_421_, 5);
v_lAssignment_435_ = lean_ctor_get(v_mctx_421_, 6);
v_eAssignment_436_ = lean_ctor_get(v_mctx_421_, 7);
v_dAssignment_437_ = lean_ctor_get(v_mctx_421_, 8);
v_isSharedCheck_451_ = !lean_is_exclusive(v_mctx_421_);
if (v_isSharedCheck_451_ == 0)
{
v___x_439_ = v_mctx_421_;
v_isShared_440_ = v_isSharedCheck_451_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_dAssignment_437_);
lean_inc(v_eAssignment_436_);
lean_inc(v_lAssignment_435_);
lean_inc(v_userNames_434_);
lean_inc(v_decls_433_);
lean_inc(v_lDepth_432_);
lean_inc(v_mvarCounter_431_);
lean_inc(v_levelAssignDepth_430_);
lean_inc(v_depth_429_);
lean_dec(v_mctx_421_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_451_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_443_; 
v___x_441_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7___redArg(v_eAssignment_436_, v_mvarId_416_, v_val_417_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 7, v___x_441_);
v___x_443_ = v___x_439_;
goto v_reusejp_442_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_depth_429_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_levelAssignDepth_430_);
lean_ctor_set(v_reuseFailAlloc_450_, 2, v_mvarCounter_431_);
lean_ctor_set(v_reuseFailAlloc_450_, 3, v_lDepth_432_);
lean_ctor_set(v_reuseFailAlloc_450_, 4, v_decls_433_);
lean_ctor_set(v_reuseFailAlloc_450_, 5, v_userNames_434_);
lean_ctor_set(v_reuseFailAlloc_450_, 6, v_lAssignment_435_);
lean_ctor_set(v_reuseFailAlloc_450_, 7, v___x_441_);
lean_ctor_set(v_reuseFailAlloc_450_, 8, v_dAssignment_437_);
v___x_443_ = v_reuseFailAlloc_450_;
goto v_reusejp_442_;
}
v_reusejp_442_:
{
lean_object* v___x_445_; 
if (v_isShared_428_ == 0)
{
lean_ctor_set(v___x_427_, 0, v___x_443_);
v___x_445_ = v___x_427_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_449_; 
v_reuseFailAlloc_449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_449_, 0, v___x_443_);
lean_ctor_set(v_reuseFailAlloc_449_, 1, v_cache_422_);
lean_ctor_set(v_reuseFailAlloc_449_, 2, v_zetaDeltaFVarIds_423_);
lean_ctor_set(v_reuseFailAlloc_449_, 3, v_postponed_424_);
lean_ctor_set(v_reuseFailAlloc_449_, 4, v_diag_425_);
v___x_445_ = v_reuseFailAlloc_449_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; 
v___x_446_ = lean_st_ref_set(v___y_418_, v___x_445_);
v___x_447_ = lean_box(0);
v___x_448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
return v___x_448_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6___redArg___boxed(lean_object* v_mvarId_453_, lean_object* v_val_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6___redArg(v_mvarId_453_, v_val_454_, v___y_455_);
lean_dec(v___y_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__4_spec__4(lean_object* v_msgData_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v___x_464_; lean_object* v_env_465_; lean_object* v___x_466_; lean_object* v_mctx_467_; lean_object* v_lctx_468_; lean_object* v_options_469_; lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; 
v___x_464_ = lean_st_ref_get(v___y_462_);
v_env_465_ = lean_ctor_get(v___x_464_, 0);
lean_inc_ref(v_env_465_);
lean_dec(v___x_464_);
v___x_466_ = lean_st_ref_get(v___y_460_);
v_mctx_467_ = lean_ctor_get(v___x_466_, 0);
lean_inc_ref(v_mctx_467_);
lean_dec(v___x_466_);
v_lctx_468_ = lean_ctor_get(v___y_459_, 2);
v_options_469_ = lean_ctor_get(v___y_461_, 2);
lean_inc_ref(v_options_469_);
lean_inc_ref(v_lctx_468_);
v___x_470_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_470_, 0, v_env_465_);
lean_ctor_set(v___x_470_, 1, v_mctx_467_);
lean_ctor_set(v___x_470_, 2, v_lctx_468_);
lean_ctor_set(v___x_470_, 3, v_options_469_);
v___x_471_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_msgData_458_);
v___x_472_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_472_, 0, v___x_471_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__4_spec__4___boxed(lean_object* v_msgData_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__4_spec__4(v_msgData_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_479_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__0(void){
_start:
{
lean_object* v___x_480_; double v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = lean_float_of_nat(v___x_480_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4(lean_object* v_cls_485_, lean_object* v_msg_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_ref_492_; lean_object* v___x_493_; lean_object* v_a_494_; lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_538_; 
v_ref_492_ = lean_ctor_get(v___y_489_, 5);
v___x_493_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__4_spec__4(v_msg_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
v_a_494_ = lean_ctor_get(v___x_493_, 0);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_493_);
if (v_isSharedCheck_538_ == 0)
{
v___x_496_ = v___x_493_;
v_isShared_497_ = v_isSharedCheck_538_;
goto v_resetjp_495_;
}
else
{
lean_inc(v_a_494_);
lean_dec(v___x_493_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_538_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v___x_498_; lean_object* v_traceState_499_; lean_object* v_env_500_; lean_object* v_nextMacroScope_501_; lean_object* v_ngen_502_; lean_object* v_auxDeclNGen_503_; lean_object* v_cache_504_; lean_object* v_messages_505_; lean_object* v_infoState_506_; lean_object* v_snapshotTasks_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_537_; 
v___x_498_ = lean_st_ref_take(v___y_490_);
v_traceState_499_ = lean_ctor_get(v___x_498_, 4);
v_env_500_ = lean_ctor_get(v___x_498_, 0);
v_nextMacroScope_501_ = lean_ctor_get(v___x_498_, 1);
v_ngen_502_ = lean_ctor_get(v___x_498_, 2);
v_auxDeclNGen_503_ = lean_ctor_get(v___x_498_, 3);
v_cache_504_ = lean_ctor_get(v___x_498_, 5);
v_messages_505_ = lean_ctor_get(v___x_498_, 6);
v_infoState_506_ = lean_ctor_get(v___x_498_, 7);
v_snapshotTasks_507_ = lean_ctor_get(v___x_498_, 8);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_498_);
if (v_isSharedCheck_537_ == 0)
{
v___x_509_ = v___x_498_;
v_isShared_510_ = v_isSharedCheck_537_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_snapshotTasks_507_);
lean_inc(v_infoState_506_);
lean_inc(v_messages_505_);
lean_inc(v_cache_504_);
lean_inc(v_traceState_499_);
lean_inc(v_auxDeclNGen_503_);
lean_inc(v_ngen_502_);
lean_inc(v_nextMacroScope_501_);
lean_inc(v_env_500_);
lean_dec(v___x_498_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_537_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint64_t v_tid_511_; lean_object* v_traces_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_536_; 
v_tid_511_ = lean_ctor_get_uint64(v_traceState_499_, sizeof(void*)*1);
v_traces_512_ = lean_ctor_get(v_traceState_499_, 0);
v_isSharedCheck_536_ = !lean_is_exclusive(v_traceState_499_);
if (v_isSharedCheck_536_ == 0)
{
v___x_514_ = v_traceState_499_;
v_isShared_515_ = v_isSharedCheck_536_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_traces_512_);
lean_dec(v_traceState_499_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_536_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; double v___x_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_516_ = lean_box(0);
v___x_517_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__0, &l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__0);
v___x_518_ = 0;
v___x_519_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__1));
v___x_520_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_520_, 0, v_cls_485_);
lean_ctor_set(v___x_520_, 1, v___x_516_);
lean_ctor_set(v___x_520_, 2, v___x_519_);
lean_ctor_set_float(v___x_520_, sizeof(void*)*3, v___x_517_);
lean_ctor_set_float(v___x_520_, sizeof(void*)*3 + 8, v___x_517_);
lean_ctor_set_uint8(v___x_520_, sizeof(void*)*3 + 16, v___x_518_);
v___x_521_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___closed__2));
v___x_522_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_522_, 0, v___x_520_);
lean_ctor_set(v___x_522_, 1, v_a_494_);
lean_ctor_set(v___x_522_, 2, v___x_521_);
lean_inc(v_ref_492_);
v___x_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_523_, 0, v_ref_492_);
lean_ctor_set(v___x_523_, 1, v___x_522_);
v___x_524_ = l_Lean_PersistentArray_push___redArg(v_traces_512_, v___x_523_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 0, v___x_524_);
v___x_526_ = v___x_514_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_535_; 
v_reuseFailAlloc_535_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_535_, 0, v___x_524_);
lean_ctor_set_uint64(v_reuseFailAlloc_535_, sizeof(void*)*1, v_tid_511_);
v___x_526_ = v_reuseFailAlloc_535_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
lean_object* v___x_528_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 4, v___x_526_);
v___x_528_ = v___x_509_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_env_500_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_nextMacroScope_501_);
lean_ctor_set(v_reuseFailAlloc_534_, 2, v_ngen_502_);
lean_ctor_set(v_reuseFailAlloc_534_, 3, v_auxDeclNGen_503_);
lean_ctor_set(v_reuseFailAlloc_534_, 4, v___x_526_);
lean_ctor_set(v_reuseFailAlloc_534_, 5, v_cache_504_);
lean_ctor_set(v_reuseFailAlloc_534_, 6, v_messages_505_);
lean_ctor_set(v_reuseFailAlloc_534_, 7, v_infoState_506_);
lean_ctor_set(v_reuseFailAlloc_534_, 8, v_snapshotTasks_507_);
v___x_528_ = v_reuseFailAlloc_534_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_529_ = lean_st_ref_set(v___y_490_, v___x_528_);
v___x_530_ = lean_box(0);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_530_);
v___x_532_ = v___x_496_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4___boxed(lean_object* v_cls_539_, lean_object* v_msg_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4(v_cls_539_, v_msg_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(lean_object* v_fst_547_, lean_object* v_fst_548_, lean_object* v_n_549_, lean_object* v_i_550_, lean_object* v_a_551_){
_start:
{
lean_object* v_zero_553_; uint8_t v_isZero_554_; 
v_zero_553_ = lean_unsigned_to_nat(0u);
v_isZero_554_ = lean_nat_dec_eq(v_i_550_, v_zero_553_);
if (v_isZero_554_ == 1)
{
lean_object* v___x_555_; 
lean_dec(v_i_550_);
v___x_555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_555_, 0, v_a_551_);
return v___x_555_;
}
else
{
lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v_one_558_; lean_object* v_n_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
v___x_556_ = lean_unsigned_to_nat(2u);
v___x_557_ = lean_box(0);
v_one_558_ = lean_unsigned_to_nat(1u);
v_n_559_ = lean_nat_sub(v_i_550_, v_one_558_);
lean_dec(v_i_550_);
v___x_560_ = lean_nat_sub(v_n_549_, v_n_559_);
v___x_561_ = lean_nat_sub(v___x_560_, v_one_558_);
lean_dec(v___x_560_);
v___x_562_ = lean_nat_add(v___x_561_, v___x_556_);
v___x_563_ = lean_array_get_borrowed(v___x_557_, v_fst_547_, v___x_562_);
lean_dec(v___x_562_);
v___x_564_ = lean_array_fget_borrowed(v_fst_548_, v___x_561_);
lean_dec(v___x_561_);
lean_inc(v___x_564_);
v___x_565_ = l_Lean_mkFVar(v___x_564_);
lean_inc(v___x_563_);
v___x_566_ = l_Lean_Meta_FVarSubst_insert(v_a_551_, v___x_563_, v___x_565_);
v_i_550_ = v_n_559_;
v_a_551_ = v___x_566_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg___boxed(lean_object* v_fst_568_, lean_object* v_fst_569_, lean_object* v_n_570_, lean_object* v_i_571_, lean_object* v_a_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_568_, v_fst_569_, v_n_570_, v_i_571_, v_a_572_);
lean_dec(v_n_570_);
lean_dec_ref(v_fst_569_);
lean_dec_ref(v_fst_568_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg___lam__0(lean_object* v_k_575_, lean_object* v_b_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lean_apply_6(v_k_575_, v_b_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, lean_box(0));
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg___lam__0___boxed(lean_object* v_k_583_, lean_object* v_b_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg___lam__0(v_k_583_, v_b_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg(lean_object* v_name_591_, uint8_t v_bi_592_, lean_object* v_type_593_, lean_object* v_k_594_, uint8_t v_kind_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v___f_601_; lean_object* v___x_602_; 
v___f_601_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_601_, 0, v_k_594_);
v___x_602_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_591_, v_bi_592_, v_type_593_, v___f_601_, v_kind_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
if (lean_obj_tag(v___x_602_) == 0)
{
lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_610_; 
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_610_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_610_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_608_; 
if (v_isShared_606_ == 0)
{
v___x_608_ = v___x_605_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_a_603_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
else
{
lean_object* v_a_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_618_; 
v_a_611_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_618_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_618_ == 0)
{
v___x_613_ = v___x_602_;
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_a_611_);
lean_dec(v___x_602_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_618_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v___x_616_; 
if (v_isShared_614_ == 0)
{
v___x_616_ = v___x_613_;
goto v_reusejp_615_;
}
else
{
lean_object* v_reuseFailAlloc_617_; 
v_reuseFailAlloc_617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_617_, 0, v_a_611_);
v___x_616_ = v_reuseFailAlloc_617_;
goto v_reusejp_615_;
}
v_reusejp_615_:
{
return v___x_616_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg___boxed(lean_object* v_name_619_, lean_object* v_bi_620_, lean_object* v_type_621_, lean_object* v_k_622_, lean_object* v_kind_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_){
_start:
{
uint8_t v_bi_boxed_629_; uint8_t v_kind_boxed_630_; lean_object* v_res_631_; 
v_bi_boxed_629_ = lean_unbox(v_bi_620_);
v_kind_boxed_630_ = lean_unbox(v_kind_623_);
v_res_631_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg(v_name_619_, v_bi_boxed_629_, v_type_621_, v_k_622_, v_kind_boxed_630_, v___y_624_, v___y_625_, v___y_626_, v___y_627_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7___redArg(lean_object* v_name_632_, lean_object* v_type_633_, lean_object* v_k_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
uint8_t v___x_640_; uint8_t v___x_641_; lean_object* v___x_642_; 
v___x_640_ = 0;
v___x_641_ = 0;
v___x_642_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg(v_name_632_, v___x_640_, v_type_633_, v_k_634_, v___x_641_, v___y_635_, v___y_636_, v___y_637_, v___y_638_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7___redArg___boxed(lean_object* v_name_643_, lean_object* v_type_644_, lean_object* v_k_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7___redArg(v_name_643_, v_type_644_, v_k_645_, v___y_646_, v___y_647_, v___y_648_, v___y_649_);
return v_res_651_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__1(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_653_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__0));
v___x_654_ = l_Lean_stringToMessageData(v___x_653_);
return v___x_654_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_656_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__2));
v___x_657_ = l_Lean_stringToMessageData(v___x_656_);
return v___x_657_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__7(void){
_start:
{
lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_661_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__6));
v___x_662_ = lean_unsigned_to_nat(22u);
v___x_663_ = lean_unsigned_to_nat(64u);
v___x_664_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__5));
v___x_665_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__4));
v___x_666_ = l_mkPanicMessageWithDecl(v___x_665_, v___x_664_, v___x_663_, v___x_662_, v___x_661_);
return v___x_666_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object* v_snd_670_, lean_object* v___x_671_, lean_object* v_fvarId_672_, lean_object* v_hFVarId_673_, lean_object* v___x_674_, lean_object* v_fst_675_, lean_object* v_fvarSubst_676_, uint8_t v_clearH_677_, lean_object* v___x_678_, lean_object* v___x_679_, lean_object* v___x_680_, uint8_t v_skip_681_, uint8_t v___x_682_, lean_object* v___x_683_, lean_object* v___x_684_, lean_object* v_a_685_, uint8_t v_symm_686_, uint8_t v___x_687_, lean_object* v___x_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_711_; lean_object* v_mvarId_712_; lean_object* v___y_713_; lean_object* v___y_714_; lean_object* v___y_715_; lean_object* v___y_716_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v_newVal_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_795_; uint8_t v___y_796_; lean_object* v___y_797_; lean_object* v___y_798_; lean_object* v_major_799_; lean_object* v___y_800_; lean_object* v___y_801_; lean_object* v___y_802_; lean_object* v___y_803_; uint8_t v___y_836_; lean_object* v___y_837_; lean_object* v_motive_838_; lean_object* v_newType_839_; lean_object* v___y_840_; lean_object* v___y_841_; lean_object* v___y_842_; lean_object* v___y_843_; lean_object* v___x_854_; 
lean_inc(v_snd_670_);
v___x_854_ = l_Lean_MVarId_getDecl(v_snd_670_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref(v___x_854_);
lean_inc_ref(v___y_689_);
lean_inc(v___x_671_);
v___x_856_ = l_Lean_FVarId_getDecl___redArg(v___x_671_, v___y_689_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_856_) == 0)
{
lean_object* v_a_857_; lean_object* v___x_858_; lean_object* v___x_859_; 
v_a_857_ = lean_ctor_get(v___x_856_, 0);
lean_inc(v_a_857_);
lean_dec_ref(v___x_856_);
v___x_858_ = l_Lean_LocalDecl_type(v_a_857_);
lean_dec(v_a_857_);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
v___x_859_ = l_Lean_Meta_matchEq_x3f(v___x_858_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_859_) == 0)
{
lean_object* v_a_860_; 
v_a_860_ = lean_ctor_get(v___x_859_, 0);
lean_inc(v_a_860_);
lean_dec_ref(v___x_859_);
if (lean_obj_tag(v_a_860_) == 0)
{
lean_object* v___x_861_; lean_object* v___x_862_; 
lean_dec(v_a_855_);
lean_dec(v_a_685_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v___x_861_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__7, &l_Lean_Meta_substCore___lam__1___closed__7_once, _init_l_Lean_Meta_substCore___lam__1___closed__7);
v___x_862_ = l_panic___at___00Lean_Meta_substCore_spec__1(v___x_861_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
return v___x_862_;
}
else
{
lean_object* v_val_863_; lean_object* v_snd_864_; lean_object* v_fst_865_; lean_object* v_snd_866_; lean_object* v_type_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___f_870_; lean_object* v___y_872_; 
v_val_863_ = lean_ctor_get(v_a_860_, 0);
lean_inc(v_val_863_);
lean_dec_ref(v_a_860_);
v_snd_864_ = lean_ctor_get(v_val_863_, 1);
lean_inc(v_snd_864_);
lean_dec(v_val_863_);
v_fst_865_ = lean_ctor_get(v_snd_864_, 0);
lean_inc(v_fst_865_);
v_snd_866_ = lean_ctor_get(v_snd_864_, 1);
lean_inc(v_snd_866_);
lean_dec(v_snd_864_);
v_type_867_ = lean_ctor_get(v_a_855_, 2);
lean_inc_ref(v_type_867_);
lean_dec(v_a_855_);
v___x_868_ = lean_box(v___x_687_);
v___x_869_ = lean_box(v___x_682_);
lean_inc_ref(v___x_678_);
lean_inc(v___x_679_);
lean_inc_ref(v___x_674_);
lean_inc_ref(v_type_867_);
v___f_870_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__0___boxed), 12, 6);
lean_closure_set(v___f_870_, 0, v_type_867_);
lean_closure_set(v___f_870_, 1, v___x_674_);
lean_closure_set(v___f_870_, 2, v___x_679_);
lean_closure_set(v___f_870_, 3, v___x_678_);
lean_closure_set(v___f_870_, 4, v___x_868_);
lean_closure_set(v___f_870_, 5, v___x_869_);
if (v_symm_686_ == 0)
{
lean_dec(v_fst_865_);
v___y_872_ = v_snd_866_;
goto v___jp_871_;
}
else
{
lean_dec(v_snd_866_);
v___y_872_ = v_fst_865_;
goto v___jp_871_;
}
v___jp_871_:
{
lean_object* v___x_873_; lean_object* v_a_874_; lean_object* v___x_875_; lean_object* v_a_876_; uint8_t v___x_877_; 
v___x_873_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_872_, v___y_690_);
v_a_874_ = lean_ctor_get(v___x_873_, 0);
lean_inc(v_a_874_);
lean_dec_ref(v___x_873_);
lean_inc(v___x_671_);
lean_inc_ref(v_type_867_);
v___x_875_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(v_type_867_, v___x_671_, v___y_690_);
v_a_876_ = lean_ctor_get(v___x_875_, 0);
lean_inc(v_a_876_);
lean_dec_ref(v___x_875_);
v___x_877_ = lean_unbox(v_a_876_);
if (v___x_877_ == 0)
{
lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; 
lean_dec_ref(v___f_870_);
v___x_878_ = lean_mk_empty_array_with_capacity(v___x_688_);
lean_inc_ref(v___x_678_);
v___x_879_ = lean_array_push(v___x_878_, v___x_678_);
v___x_880_ = 1;
lean_inc_ref(v_type_867_);
v___x_881_ = l_Lean_Meta_mkLambdaFVars(v___x_879_, v_type_867_, v___x_687_, v___x_682_, v___x_687_, v___x_682_, v___x_880_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec_ref(v___x_879_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref(v___x_881_);
lean_inc_ref(v___x_678_);
v___x_883_ = l_Lean_Expr_replaceFVar(v_type_867_, v___x_678_, v_a_874_);
lean_dec_ref(v_type_867_);
v___x_884_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
v___y_836_ = v___x_884_;
v___y_837_ = v_a_874_;
v_motive_838_ = v_a_882_;
v_newType_839_ = v___x_883_;
v___y_840_ = v___y_689_;
v___y_841_ = v___y_690_;
v___y_842_ = v___y_691_;
v___y_843_ = v___y_692_;
goto v___jp_835_;
}
else
{
lean_object* v_a_885_; lean_object* v___x_887_; uint8_t v_isShared_888_; uint8_t v_isSharedCheck_892_; 
lean_dec(v_a_876_);
lean_dec(v_a_874_);
lean_dec_ref(v_type_867_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v_a_685_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_885_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_892_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_892_ == 0)
{
v___x_887_ = v___x_881_;
v_isShared_888_ = v_isSharedCheck_892_;
goto v_resetjp_886_;
}
else
{
lean_inc(v_a_885_);
lean_dec(v___x_881_);
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
v_reuseFailAlloc_891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v_a_885_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
else
{
lean_object* v___x_893_; lean_object* v___x_894_; 
lean_inc_ref(v___x_678_);
v___x_893_ = l_Lean_Expr_replaceFVar(v_type_867_, v___x_678_, v_a_874_);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc(v_a_874_);
v___x_894_ = l_Lean_Meta_mkEqRefl(v_a_874_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_894_) == 0)
{
lean_object* v_a_895_; lean_object* v___x_896_; 
v_a_895_ = lean_ctor_get(v___x_894_, 0);
lean_inc(v_a_895_);
lean_dec_ref(v___x_894_);
lean_inc_ref(v___x_674_);
v___x_896_ = l_Lean_Expr_replaceFVar(v___x_893_, v___x_674_, v_a_895_);
lean_dec(v_a_895_);
lean_dec_ref(v___x_893_);
if (v_symm_686_ == 0)
{
lean_object* v___x_897_; 
lean_dec_ref(v_type_867_);
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
lean_inc_ref(v___x_678_);
lean_inc(v_a_874_);
v___x_897_ = l_Lean_Meta_mkEq(v_a_874_, v___x_678_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref(v___x_897_);
v___x_899_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__9));
lean_inc(v___y_692_);
lean_inc_ref(v___y_691_);
lean_inc(v___y_690_);
lean_inc_ref(v___y_689_);
v___x_900_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7___redArg(v___x_899_, v_a_898_, v___f_870_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; uint8_t v___x_902_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref(v___x_900_);
v___x_902_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
v___y_836_ = v___x_902_;
v___y_837_ = v_a_874_;
v_motive_838_ = v_a_901_;
v_newType_839_ = v___x_896_;
v___y_840_ = v___y_689_;
v___y_841_ = v___y_690_;
v___y_842_ = v___y_691_;
v___y_843_ = v___y_692_;
goto v___jp_835_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v___x_896_);
lean_dec(v_a_876_);
lean_dec(v_a_874_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v_a_685_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_903_ = lean_ctor_get(v___x_900_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_900_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_900_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_900_);
v___x_905_ = lean_box(0);
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
v_resetjp_904_:
{
lean_object* v___x_908_; 
if (v_isShared_906_ == 0)
{
v___x_908_ = v___x_905_;
goto v_reusejp_907_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_a_903_);
v___x_908_ = v_reuseFailAlloc_909_;
goto v_reusejp_907_;
}
v_reusejp_907_:
{
return v___x_908_;
}
}
}
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v___x_896_);
lean_dec(v_a_876_);
lean_dec(v_a_874_);
lean_dec_ref(v___f_870_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v_a_685_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_911_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_897_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_897_);
v___x_913_ = lean_box(0);
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
v_resetjp_912_:
{
lean_object* v___x_916_; 
if (v_isShared_914_ == 0)
{
v___x_916_ = v___x_913_;
goto v_reusejp_915_;
}
else
{
lean_object* v_reuseFailAlloc_917_; 
v_reuseFailAlloc_917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_917_, 0, v_a_911_);
v___x_916_ = v_reuseFailAlloc_917_;
goto v_reusejp_915_;
}
v_reusejp_915_:
{
return v___x_916_;
}
}
}
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; uint8_t v___x_922_; lean_object* v___x_923_; 
lean_dec_ref(v___f_870_);
v___x_919_ = lean_mk_empty_array_with_capacity(v___x_679_);
lean_inc_ref(v___x_678_);
v___x_920_ = lean_array_push(v___x_919_, v___x_678_);
lean_inc_ref(v___x_674_);
v___x_921_ = lean_array_push(v___x_920_, v___x_674_);
v___x_922_ = 1;
v___x_923_ = l_Lean_Meta_mkLambdaFVars(v___x_921_, v_type_867_, v___x_687_, v___x_682_, v___x_687_, v___x_682_, v___x_922_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec_ref(v___x_921_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_object* v_a_924_; uint8_t v___x_925_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
lean_inc(v_a_924_);
lean_dec_ref(v___x_923_);
v___x_925_ = lean_unbox(v_a_876_);
lean_dec(v_a_876_);
v___y_836_ = v___x_925_;
v___y_837_ = v_a_874_;
v_motive_838_ = v_a_924_;
v_newType_839_ = v___x_896_;
v___y_840_ = v___y_689_;
v___y_841_ = v___y_690_;
v___y_842_ = v___y_691_;
v___y_843_ = v___y_692_;
goto v___jp_835_;
}
else
{
lean_object* v_a_926_; lean_object* v___x_928_; uint8_t v_isShared_929_; uint8_t v_isSharedCheck_933_; 
lean_dec_ref(v___x_896_);
lean_dec(v_a_876_);
lean_dec(v_a_874_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v_a_685_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_926_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_933_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_933_ == 0)
{
v___x_928_ = v___x_923_;
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
else
{
lean_inc(v_a_926_);
lean_dec(v___x_923_);
v___x_928_ = lean_box(0);
v_isShared_929_ = v_isSharedCheck_933_;
goto v_resetjp_927_;
}
v_resetjp_927_:
{
lean_object* v___x_931_; 
if (v_isShared_929_ == 0)
{
v___x_931_ = v___x_928_;
goto v_reusejp_930_;
}
else
{
lean_object* v_reuseFailAlloc_932_; 
v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_932_, 0, v_a_926_);
v___x_931_ = v_reuseFailAlloc_932_;
goto v_reusejp_930_;
}
v_reusejp_930_:
{
return v___x_931_;
}
}
}
}
}
else
{
lean_object* v_a_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_941_; 
lean_dec_ref(v___x_893_);
lean_dec(v_a_876_);
lean_dec(v_a_874_);
lean_dec_ref(v___f_870_);
lean_dec_ref(v_type_867_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v_a_685_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_934_ = lean_ctor_get(v___x_894_, 0);
v_isSharedCheck_941_ = !lean_is_exclusive(v___x_894_);
if (v_isSharedCheck_941_ == 0)
{
v___x_936_ = v___x_894_;
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_a_934_);
lean_dec(v___x_894_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_941_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_939_; 
if (v_isShared_937_ == 0)
{
v___x_939_ = v___x_936_;
goto v_reusejp_938_;
}
else
{
lean_object* v_reuseFailAlloc_940_; 
v_reuseFailAlloc_940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
v___x_939_ = v_reuseFailAlloc_940_;
goto v_reusejp_938_;
}
v_reusejp_938_:
{
return v___x_939_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_942_; lean_object* v___x_944_; uint8_t v_isShared_945_; uint8_t v_isSharedCheck_949_; 
lean_dec(v_a_855_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v_a_685_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_942_ = lean_ctor_get(v___x_859_, 0);
v_isSharedCheck_949_ = !lean_is_exclusive(v___x_859_);
if (v_isSharedCheck_949_ == 0)
{
v___x_944_ = v___x_859_;
v_isShared_945_ = v_isSharedCheck_949_;
goto v_resetjp_943_;
}
else
{
lean_inc(v_a_942_);
lean_dec(v___x_859_);
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
v_reuseFailAlloc_948_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_950_; lean_object* v___x_952_; uint8_t v_isShared_953_; uint8_t v_isSharedCheck_957_; 
lean_dec(v_a_855_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v_a_685_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_950_ = lean_ctor_get(v___x_856_, 0);
v_isSharedCheck_957_ = !lean_is_exclusive(v___x_856_);
if (v_isSharedCheck_957_ == 0)
{
v___x_952_ = v___x_856_;
v_isShared_953_ = v_isSharedCheck_957_;
goto v_resetjp_951_;
}
else
{
lean_inc(v_a_950_);
lean_dec(v___x_856_);
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
else
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_965_; 
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v_a_685_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_958_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_965_ == 0)
{
v___x_960_ = v___x_854_;
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_854_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_965_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
lean_object* v___x_963_; 
if (v_isShared_961_ == 0)
{
v___x_963_ = v___x_960_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v_a_958_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
v___jp_694_:
{
lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_698_ = l_Lean_Meta_FVarSubst_insert(v___y_696_, v_fvarId_672_, v___y_697_);
v___x_699_ = l_Lean_Meta_FVarSubst_insert(v___x_698_, v_hFVarId_673_, v___x_674_);
v___x_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_700_, 0, v___x_699_);
lean_ctor_set(v___x_700_, 1, v___y_695_);
v___x_701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_701_, 0, v___x_700_);
return v___x_701_;
}
v___jp_702_:
{
lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_706_ = lean_array_get_size(v___y_705_);
v___x_707_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_675_, v___y_705_, v___x_706_, v___x_706_, v_fvarSubst_676_);
lean_dec_ref(v___y_705_);
if (v_clearH_677_ == 0)
{
lean_object* v_a_708_; 
lean_dec_ref(v___y_704_);
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref(v___x_707_);
v___y_695_ = v___y_703_;
v___y_696_ = v_a_708_;
v___y_697_ = v___x_678_;
goto v___jp_694_;
}
else
{
lean_object* v_a_709_; 
lean_dec_ref(v___x_678_);
v_a_709_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_709_);
lean_dec_ref(v___x_707_);
v___y_695_ = v___y_703_;
v___y_696_ = v_a_709_;
v___y_697_ = v___y_704_;
goto v___jp_694_;
}
}
v___jp_710_:
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_717_ = lean_array_get_size(v_fst_675_);
v___x_718_ = lean_nat_sub(v___x_717_, v___x_679_);
lean_dec(v___x_679_);
lean_inc(v___y_716_);
lean_inc_ref(v___y_715_);
lean_inc(v___y_714_);
lean_inc_ref(v___y_713_);
lean_inc(v___x_718_);
v___x_719_ = l_Lean_Meta_introNCore(v_mvarId_712_, v___x_718_, v___x_680_, v_skip_681_, v___x_682_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v_a_720_; lean_object* v_fst_721_; lean_object* v_snd_722_; lean_object* v___x_724_; uint8_t v_isShared_725_; uint8_t v_isSharedCheck_755_; 
v_a_720_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_a_720_);
lean_dec_ref(v___x_719_);
v_fst_721_ = lean_ctor_get(v_a_720_, 0);
v_snd_722_ = lean_ctor_get(v_a_720_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_a_720_);
if (v_isSharedCheck_755_ == 0)
{
v___x_724_ = v_a_720_;
v_isShared_725_ = v_isSharedCheck_755_;
goto v_resetjp_723_;
}
else
{
lean_inc(v_snd_722_);
lean_inc(v_fst_721_);
lean_dec(v_a_720_);
v___x_724_ = lean_box(0);
v_isShared_725_ = v_isSharedCheck_755_;
goto v_resetjp_723_;
}
v_resetjp_723_:
{
lean_object* v___x_726_; lean_object* v_a_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_754_; 
lean_inc(v___x_683_);
v___x_726_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg(v___x_683_, v___y_715_);
v_a_727_ = lean_ctor_get(v___x_726_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_726_);
if (v_isSharedCheck_754_ == 0)
{
v___x_729_ = v___x_726_;
v_isShared_730_ = v_isSharedCheck_754_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_a_727_);
lean_dec(v___x_726_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_754_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
uint8_t v___x_731_; 
v___x_731_ = lean_unbox(v_a_727_);
lean_dec(v_a_727_);
if (v___x_731_ == 0)
{
lean_del_object(v___x_729_);
lean_del_object(v___x_724_);
lean_dec(v___x_718_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___x_683_);
v___y_703_ = v_snd_722_;
v___y_704_ = v___y_711_;
v___y_705_ = v_fst_721_;
goto v___jp_702_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_732_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__1, &l_Lean_Meta_substCore___lam__1___closed__1_once, _init_l_Lean_Meta_substCore___lam__1___closed__1);
v___x_733_ = l_Nat_reprFast(v___x_718_);
if (v_isShared_730_ == 0)
{
lean_ctor_set_tag(v___x_729_, 3);
lean_ctor_set(v___x_729_, 0, v___x_733_);
v___x_735_ = v___x_729_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_753_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
lean_object* v___x_736_; lean_object* v___x_738_; 
v___x_736_ = l_Lean_MessageData_ofFormat(v___x_735_);
if (v_isShared_725_ == 0)
{
lean_ctor_set_tag(v___x_724_, 7);
lean_ctor_set(v___x_724_, 1, v___x_736_);
lean_ctor_set(v___x_724_, 0, v___x_732_);
v___x_738_ = v___x_724_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_732_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v___x_736_);
v___x_738_ = v_reuseFailAlloc_752_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_739_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__3, &l_Lean_Meta_substCore___lam__1___closed__3_once, _init_l_Lean_Meta_substCore___lam__1___closed__3);
v___x_740_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_740_, 0, v___x_738_);
lean_ctor_set(v___x_740_, 1, v___x_739_);
lean_inc(v_snd_722_);
v___x_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_741_, 0, v_snd_722_);
v___x_742_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_740_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4(v___x_683_, v___x_742_, v___y_713_, v___y_714_, v___y_715_, v___y_716_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_dec_ref(v___x_743_);
v___y_703_ = v_snd_722_;
v___y_704_ = v___y_711_;
v___y_705_ = v_fst_721_;
goto v___jp_702_;
}
else
{
lean_object* v_a_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_751_; 
lean_dec(v_snd_722_);
lean_dec(v_fst_721_);
lean_dec_ref(v___y_711_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
v_a_744_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_751_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_751_ == 0)
{
v___x_746_ = v___x_743_;
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_a_744_);
lean_dec(v___x_743_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_751_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v___x_749_; 
if (v_isShared_747_ == 0)
{
v___x_749_ = v___x_746_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v_a_744_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
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
lean_object* v_a_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_763_; 
lean_dec(v___x_718_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec_ref(v___y_711_);
lean_dec(v___x_683_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
v_a_756_ = lean_ctor_get(v___x_719_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_719_);
if (v_isSharedCheck_763_ == 0)
{
v___x_758_ = v___x_719_;
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_a_756_);
lean_dec(v___x_719_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_763_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_761_; 
if (v_isShared_759_ == 0)
{
v___x_761_ = v___x_758_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
v___jp_764_:
{
lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_772_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6___redArg(v_snd_670_, v_newVal_767_, v___y_769_);
lean_dec_ref(v___x_772_);
v___x_773_ = l_Lean_Expr_mvarId_x21(v___y_765_);
lean_dec_ref(v___y_765_);
if (v_clearH_677_ == 0)
{
lean_dec(v___x_684_);
lean_dec(v___x_671_);
v___y_711_ = v___y_766_;
v_mvarId_712_ = v___x_773_;
v___y_713_ = v___y_768_;
v___y_714_ = v___y_769_;
v___y_715_ = v___y_770_;
v___y_716_ = v___y_771_;
goto v___jp_710_;
}
else
{
lean_object* v___x_774_; 
lean_inc(v___y_771_);
lean_inc_ref(v___y_770_);
lean_inc(v___y_769_);
lean_inc_ref(v___y_768_);
v___x_774_ = l_Lean_MVarId_clear(v___x_773_, v___x_671_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_776_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref(v___x_774_);
lean_inc(v___y_771_);
lean_inc_ref(v___y_770_);
lean_inc(v___y_769_);
lean_inc_ref(v___y_768_);
v___x_776_ = l_Lean_MVarId_clear(v_a_775_, v___x_684_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
lean_inc(v_a_777_);
lean_dec_ref(v___x_776_);
v___y_711_ = v___y_766_;
v_mvarId_712_ = v_a_777_;
v___y_713_ = v___y_768_;
v___y_714_ = v___y_769_;
v___y_715_ = v___y_770_;
v___y_716_ = v___y_771_;
goto v___jp_710_;
}
else
{
lean_object* v_a_778_; lean_object* v___x_780_; uint8_t v_isShared_781_; uint8_t v_isSharedCheck_785_; 
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec_ref(v___y_766_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
v_a_778_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_785_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_785_ == 0)
{
v___x_780_ = v___x_776_;
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
else
{
lean_inc(v_a_778_);
lean_dec(v___x_776_);
v___x_780_ = lean_box(0);
v_isShared_781_ = v_isSharedCheck_785_;
goto v_resetjp_779_;
}
v_resetjp_779_:
{
lean_object* v___x_783_; 
if (v_isShared_781_ == 0)
{
v___x_783_ = v___x_780_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_a_778_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v___y_771_);
lean_dec_ref(v___y_770_);
lean_dec(v___y_769_);
lean_dec_ref(v___y_768_);
lean_dec_ref(v___y_766_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
v_a_786_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_774_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_774_);
v___x_788_ = lean_box(0);
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
v_resetjp_787_:
{
lean_object* v___x_791_; 
if (v_isShared_789_ == 0)
{
v___x_791_ = v___x_788_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_a_786_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
v___jp_794_:
{
lean_object* v___x_804_; 
lean_inc_ref(v___y_800_);
v___x_804_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_795_, v_a_685_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_804_) == 0)
{
if (v___y_796_ == 0)
{
lean_object* v_a_805_; lean_object* v___x_806_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref(v___x_804_);
lean_inc(v___y_803_);
lean_inc_ref(v___y_802_);
lean_inc(v___y_801_);
lean_inc_ref(v___y_800_);
lean_inc(v_a_805_);
v___x_806_ = l_Lean_Meta_mkEqNDRec(v___y_798_, v_a_805_, v_major_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref(v___x_806_);
v___y_765_ = v_a_805_;
v___y_766_ = v___y_797_;
v_newVal_767_ = v_a_807_;
v___y_768_ = v___y_800_;
v___y_769_ = v___y_801_;
v___y_770_ = v___y_802_;
v___y_771_ = v___y_803_;
goto v___jp_764_;
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_a_805_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v___y_797_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_808_ = lean_ctor_get(v___x_806_, 0);
v_isSharedCheck_815_ = !lean_is_exclusive(v___x_806_);
if (v_isSharedCheck_815_ == 0)
{
v___x_810_ = v___x_806_;
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
else
{
lean_inc(v_a_808_);
lean_dec(v___x_806_);
v___x_810_ = lean_box(0);
v_isShared_811_ = v_isSharedCheck_815_;
goto v_resetjp_809_;
}
v_resetjp_809_:
{
lean_object* v___x_813_; 
if (v_isShared_811_ == 0)
{
v___x_813_ = v___x_810_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_814_; 
v_reuseFailAlloc_814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_814_, 0, v_a_808_);
v___x_813_ = v_reuseFailAlloc_814_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
return v___x_813_;
}
}
}
}
else
{
lean_object* v_a_816_; lean_object* v___x_817_; 
v_a_816_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_816_);
lean_dec_ref(v___x_804_);
lean_inc(v___y_803_);
lean_inc_ref(v___y_802_);
lean_inc(v___y_801_);
lean_inc_ref(v___y_800_);
lean_inc(v_a_816_);
v___x_817_ = l_Lean_Meta_mkEqRec(v___y_798_, v_a_816_, v_major_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref(v___x_817_);
v___y_765_ = v_a_816_;
v___y_766_ = v___y_797_;
v_newVal_767_ = v_a_818_;
v___y_768_ = v___y_800_;
v___y_769_ = v___y_801_;
v___y_770_ = v___y_802_;
v___y_771_ = v___y_803_;
goto v___jp_764_;
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_826_; 
lean_dec(v_a_816_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v___y_797_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_819_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_826_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_826_ == 0)
{
v___x_821_ = v___x_817_;
v_isShared_822_ = v_isSharedCheck_826_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_817_);
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
}
else
{
lean_object* v_a_827_; lean_object* v___x_829_; uint8_t v_isShared_830_; uint8_t v_isSharedCheck_834_; 
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec_ref(v_major_799_);
lean_dec_ref(v___y_798_);
lean_dec_ref(v___y_797_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_827_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_834_ == 0)
{
v___x_829_ = v___x_804_;
v_isShared_830_ = v_isSharedCheck_834_;
goto v_resetjp_828_;
}
else
{
lean_inc(v_a_827_);
lean_dec(v___x_804_);
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
v___jp_835_:
{
if (v_symm_686_ == 0)
{
lean_object* v___x_844_; 
lean_inc(v___y_843_);
lean_inc_ref(v___y_842_);
lean_inc(v___y_841_);
lean_inc_ref(v___y_840_);
lean_inc_ref(v___x_674_);
v___x_844_ = l_Lean_Meta_mkEqSymm(v___x_674_, v___y_840_, v___y_841_, v___y_842_, v___y_843_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref(v___x_844_);
v___y_795_ = v_newType_839_;
v___y_796_ = v___y_836_;
v___y_797_ = v___y_837_;
v___y_798_ = v_motive_838_;
v_major_799_ = v_a_845_;
v___y_800_ = v___y_840_;
v___y_801_ = v___y_841_;
v___y_802_ = v___y_842_;
v___y_803_ = v___y_843_;
goto v___jp_794_;
}
else
{
lean_object* v_a_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_853_; 
lean_dec(v___y_843_);
lean_dec_ref(v___y_842_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec_ref(v_newType_839_);
lean_dec_ref(v_motive_838_);
lean_dec_ref(v___y_837_);
lean_dec(v_a_685_);
lean_dec(v___x_684_);
lean_dec(v___x_683_);
lean_dec(v___x_680_);
lean_dec(v___x_679_);
lean_dec_ref(v___x_678_);
lean_dec(v_fvarSubst_676_);
lean_dec_ref(v___x_674_);
lean_dec(v_hFVarId_673_);
lean_dec(v_fvarId_672_);
lean_dec(v___x_671_);
lean_dec(v_snd_670_);
v_a_846_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_853_ == 0)
{
v___x_848_ = v___x_844_;
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_a_846_);
lean_dec(v___x_844_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_853_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_851_; 
if (v_isShared_849_ == 0)
{
v___x_851_ = v___x_848_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
else
{
lean_inc_ref(v___x_674_);
v___y_795_ = v_newType_839_;
v___y_796_ = v___y_836_;
v___y_797_ = v___y_837_;
v___y_798_ = v_motive_838_;
v_major_799_ = v___x_674_;
v___y_800_ = v___y_840_;
v___y_801_ = v___y_841_;
v___y_802_ = v___y_842_;
v___y_803_ = v___y_843_;
goto v___jp_794_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object** _args){
lean_object* v_snd_966_ = _args[0];
lean_object* v___x_967_ = _args[1];
lean_object* v_fvarId_968_ = _args[2];
lean_object* v_hFVarId_969_ = _args[3];
lean_object* v___x_970_ = _args[4];
lean_object* v_fst_971_ = _args[5];
lean_object* v_fvarSubst_972_ = _args[6];
lean_object* v_clearH_973_ = _args[7];
lean_object* v___x_974_ = _args[8];
lean_object* v___x_975_ = _args[9];
lean_object* v___x_976_ = _args[10];
lean_object* v_skip_977_ = _args[11];
lean_object* v___x_978_ = _args[12];
lean_object* v___x_979_ = _args[13];
lean_object* v___x_980_ = _args[14];
lean_object* v_a_981_ = _args[15];
lean_object* v_symm_982_ = _args[16];
lean_object* v___x_983_ = _args[17];
lean_object* v___x_984_ = _args[18];
lean_object* v___y_985_ = _args[19];
lean_object* v___y_986_ = _args[20];
lean_object* v___y_987_ = _args[21];
lean_object* v___y_988_ = _args[22];
lean_object* v___y_989_ = _args[23];
_start:
{
uint8_t v_clearH_boxed_990_; uint8_t v_skip_boxed_991_; uint8_t v___x_33104__boxed_992_; uint8_t v_symm_boxed_993_; uint8_t v___x_33108__boxed_994_; lean_object* v_res_995_; 
v_clearH_boxed_990_ = lean_unbox(v_clearH_973_);
v_skip_boxed_991_ = lean_unbox(v_skip_977_);
v___x_33104__boxed_992_ = lean_unbox(v___x_978_);
v_symm_boxed_993_ = lean_unbox(v_symm_982_);
v___x_33108__boxed_994_ = lean_unbox(v___x_983_);
v_res_995_ = l_Lean_Meta_substCore___lam__1(v_snd_966_, v___x_967_, v_fvarId_968_, v_hFVarId_969_, v___x_970_, v_fst_971_, v_fvarSubst_972_, v_clearH_boxed_990_, v___x_974_, v___x_975_, v___x_976_, v_skip_boxed_991_, v___x_33104__boxed_992_, v___x_979_, v___x_980_, v_a_981_, v_symm_boxed_993_, v___x_33108__boxed_994_, v___x_984_, v___y_985_, v___y_986_, v___y_987_, v___y_988_);
lean_dec(v___x_984_);
lean_dec_ref(v_fst_971_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__9(size_t v_sz_996_, size_t v_i_997_, lean_object* v_bs_998_){
_start:
{
uint8_t v___x_999_; 
v___x_999_ = lean_usize_dec_lt(v_i_997_, v_sz_996_);
if (v___x_999_ == 0)
{
return v_bs_998_;
}
else
{
lean_object* v_v_1000_; lean_object* v___x_1001_; lean_object* v_bs_x27_1002_; size_t v___x_1003_; size_t v___x_1004_; lean_object* v___x_1005_; 
v_v_1000_ = lean_array_uget(v_bs_998_, v_i_997_);
v___x_1001_ = lean_unsigned_to_nat(0u);
v_bs_x27_1002_ = lean_array_uset(v_bs_998_, v_i_997_, v___x_1001_);
v___x_1003_ = ((size_t)1ULL);
v___x_1004_ = lean_usize_add(v_i_997_, v___x_1003_);
v___x_1005_ = lean_array_uset(v_bs_x27_1002_, v_i_997_, v_v_1000_);
v_i_997_ = v___x_1004_;
v_bs_998_ = v___x_1005_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__9___boxed(lean_object* v_sz_1007_, lean_object* v_i_1008_, lean_object* v_bs_1009_){
_start:
{
size_t v_sz_boxed_1010_; size_t v_i_boxed_1011_; lean_object* v_res_1012_; 
v_sz_boxed_1010_ = lean_unbox_usize(v_sz_1007_);
lean_dec(v_sz_1007_);
v_i_boxed_1011_ = lean_unbox_usize(v_i_1008_);
lean_dec(v_i_1008_);
v_res_1012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__9(v_sz_boxed_1010_, v_i_boxed_1011_, v_bs_1009_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__10(lean_object* v_a_1013_, lean_object* v_a_1014_){
_start:
{
if (lean_obj_tag(v_a_1013_) == 0)
{
lean_object* v___x_1015_; 
v___x_1015_ = l_List_reverse___redArg(v_a_1014_);
return v___x_1015_;
}
else
{
lean_object* v_head_1016_; lean_object* v_tail_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1026_; 
v_head_1016_ = lean_ctor_get(v_a_1013_, 0);
v_tail_1017_ = lean_ctor_get(v_a_1013_, 1);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_a_1013_);
if (v_isSharedCheck_1026_ == 0)
{
v___x_1019_ = v_a_1013_;
v_isShared_1020_ = v_isSharedCheck_1026_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_tail_1017_);
lean_inc(v_head_1016_);
lean_dec(v_a_1013_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1026_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___x_1023_; 
v___x_1021_ = l_Lean_MessageData_ofName(v_head_1016_);
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 1, v_a_1014_);
lean_ctor_set(v___x_1019_, 0, v___x_1021_);
v___x_1023_ = v___x_1019_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1021_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_a_1014_);
v___x_1023_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
v_a_1013_ = v_tail_1017_;
v_a_1014_ = v___x_1023_;
goto _start;
}
}
}
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__2));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__5(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__4));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__8(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__7));
v___x_1040_ = l_Lean_MessageData_ofFormat(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__9(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__8, &l_Lean_Meta_substCore___lam__2___closed__8_once, _init_l_Lean_Meta_substCore___lam__2___closed__8);
v___x_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1042_, 0, v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__11(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__10));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__13(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__12));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__15(void){
_start:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; 
v___x_1050_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__14));
v___x_1051_ = l_Lean_stringToMessageData(v___x_1050_);
return v___x_1051_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__17(void){
_start:
{
lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1053_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__16));
v___x_1054_ = l_Lean_stringToMessageData(v___x_1053_);
return v___x_1054_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__19(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__18));
v___x_1057_ = l_Lean_stringToMessageData(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__24(void){
_start:
{
lean_object* v___x_1065_; lean_object* v___x_1066_; 
v___x_1065_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__23));
v___x_1066_ = l_Lean_stringToMessageData(v___x_1065_);
return v___x_1066_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__26(void){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; 
v___x_1068_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__25));
v___x_1069_ = l_Lean_stringToMessageData(v___x_1068_);
return v___x_1069_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__28(void){
_start:
{
lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1071_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__27));
v___x_1072_ = l_Lean_stringToMessageData(v___x_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object* v_mvarId_1075_, lean_object* v_hFVarId_1076_, lean_object* v___x_1077_, uint8_t v_clearH_1078_, lean_object* v_fvarSubst_1079_, uint8_t v_symm_1080_, uint8_t v_tryToSkip_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___y_1090_; lean_object* v___y_1091_; lean_object* v___y_1092_; lean_object* v___y_1093_; lean_object* v___y_1094_; lean_object* v___x_1125_; 
lean_inc(v_mvarId_1075_);
v___x_1125_ = l_Lean_MVarId_getTag(v_mvarId_1075_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref(v___x_1125_);
v___x_1127_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__1));
lean_inc(v_mvarId_1075_);
v___x_1128_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1075_, v___x_1127_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1128_) == 0)
{
lean_object* v___x_1129_; 
lean_dec_ref(v___x_1128_);
lean_inc_ref(v___y_1082_);
lean_inc(v_hFVarId_1076_);
v___x_1129_ = l_Lean_FVarId_getDecl___redArg(v_hFVarId_1076_, v___y_1082_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1129_) == 0)
{
lean_object* v_a_1130_; lean_object* v___x_1131_; lean_object* v___y_1133_; lean_object* v___y_1134_; lean_object* v___x_1146_; 
v_a_1130_ = lean_ctor_get(v___x_1129_, 0);
lean_inc(v_a_1130_);
lean_dec_ref(v___x_1129_);
v___x_1131_ = l_Lean_LocalDecl_type(v_a_1130_);
lean_dec(v_a_1130_);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc_ref(v___x_1131_);
v___x_1146_ = l_Lean_Meta_matchEq_x3f(v___x_1131_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v_a_1147_; 
v_a_1147_ = lean_ctor_get(v___x_1146_, 0);
lean_inc(v_a_1147_);
lean_dec_ref(v___x_1146_);
if (lean_obj_tag(v_a_1147_) == 0)
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_dec_ref(v___x_1131_);
lean_dec(v_a_1126_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
v___x_1148_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__9, &l_Lean_Meta_substCore___lam__2___closed__9_once, _init_l_Lean_Meta_substCore___lam__2___closed__9);
v___x_1149_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1127_, v_mvarId_1075_, v___x_1148_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v___x_1149_;
}
else
{
lean_object* v_val_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1455_; 
v_val_1150_ = lean_ctor_get(v_a_1147_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_a_1147_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1152_ = v_a_1147_;
v_isShared_1153_ = v_isSharedCheck_1455_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_val_1150_);
lean_dec(v_a_1147_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1455_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
lean_object* v_snd_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1453_; 
v_snd_1154_ = lean_ctor_get(v_val_1150_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_val_1150_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_val_1150_, 0);
lean_dec(v_unused_1454_);
v___x_1156_ = v_val_1150_;
v_isShared_1157_ = v_isSharedCheck_1453_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_snd_1154_);
lean_dec(v_val_1150_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1453_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v_fst_1158_; lean_object* v_snd_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1452_; 
v_fst_1158_ = lean_ctor_get(v_snd_1154_, 0);
v_snd_1159_ = lean_ctor_get(v_snd_1154_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_snd_1154_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1161_ = v_snd_1154_;
v_isShared_1162_ = v_isSharedCheck_1452_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_snd_1159_);
lean_inc(v_fst_1158_);
lean_dec(v_snd_1154_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1452_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
uint8_t v___x_1163_; lean_object* v___y_1165_; lean_object* v___y_1166_; uint8_t v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; lean_object* v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; uint8_t v_skip_1182_; lean_object* v___y_1191_; uint8_t v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; uint8_t v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1202_; lean_object* v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1232_; lean_object* v___y_1233_; uint8_t v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; uint8_t v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1273_; uint8_t v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; uint8_t v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1416_; lean_object* v___y_1417_; lean_object* v___y_1448_; 
v___x_1163_ = 1;
if (v_symm_1080_ == 0)
{
lean_inc(v_fst_1158_);
v___y_1448_ = v_fst_1158_;
goto v___jp_1447_;
}
else
{
lean_inc(v_snd_1159_);
v___y_1448_ = v_snd_1159_;
goto v___jp_1447_;
}
v___jp_1164_:
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___f_1188_; lean_object* v___x_1189_; 
v___x_1183_ = lean_box(v_clearH_1078_);
v___x_1184_ = lean_box(v_skip_1182_);
v___x_1185_ = lean_box(v___x_1163_);
v___x_1186_ = lean_box(v_symm_1080_);
v___x_1187_ = lean_box(v___y_1167_);
v___f_1188_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 24, 19);
lean_closure_set(v___f_1188_, 0, v___y_1165_);
lean_closure_set(v___f_1188_, 1, v___y_1177_);
lean_closure_set(v___f_1188_, 2, v___y_1169_);
lean_closure_set(v___f_1188_, 3, v_hFVarId_1076_);
lean_closure_set(v___f_1188_, 4, v___y_1179_);
lean_closure_set(v___f_1188_, 5, v___y_1173_);
lean_closure_set(v___f_1188_, 6, v_fvarSubst_1079_);
lean_closure_set(v___f_1188_, 7, v___x_1183_);
lean_closure_set(v___f_1188_, 8, v___y_1174_);
lean_closure_set(v___f_1188_, 9, v___y_1166_);
lean_closure_set(v___f_1188_, 10, v___y_1178_);
lean_closure_set(v___f_1188_, 11, v___x_1184_);
lean_closure_set(v___f_1188_, 12, v___x_1185_);
lean_closure_set(v___f_1188_, 13, v___y_1180_);
lean_closure_set(v___f_1188_, 14, v___y_1175_);
lean_closure_set(v___f_1188_, 15, v_a_1126_);
lean_closure_set(v___f_1188_, 16, v___x_1186_);
lean_closure_set(v___f_1188_, 17, v___x_1187_);
lean_closure_set(v___f_1188_, 18, v___y_1176_);
v___x_1189_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(v___y_1181_, v___f_1188_, v___y_1170_, v___y_1172_, v___y_1171_, v___y_1168_);
return v___x_1189_;
}
v___jp_1190_:
{
lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v___x_1207_ = lean_unsigned_to_nat(0u);
lean_inc(v___x_1077_);
v___x_1208_ = lean_array_get(v___x_1077_, v___y_1202_, v___x_1207_);
lean_inc(v___x_1208_);
v___x_1209_ = l_Lean_mkFVar(v___x_1208_);
v___x_1210_ = lean_unsigned_to_nat(1u);
v___x_1211_ = lean_array_get(v___x_1077_, v___y_1202_, v___x_1210_);
lean_dec_ref(v___y_1202_);
lean_inc(v___x_1211_);
v___x_1212_ = l_Lean_mkFVar(v___x_1211_);
if (v_tryToSkip_1081_ == 0)
{
lean_dec_ref(v___y_1201_);
lean_dec(v___y_1198_);
v___y_1165_ = v___y_1191_;
v___y_1166_ = v___y_1193_;
v___y_1167_ = v___y_1192_;
v___y_1168_ = v___y_1206_;
v___y_1169_ = v___y_1197_;
v___y_1170_ = v___y_1203_;
v___y_1171_ = v___y_1205_;
v___y_1172_ = v___y_1204_;
v___y_1173_ = v___y_1194_;
v___y_1174_ = v___x_1209_;
v___y_1175_ = v___x_1208_;
v___y_1176_ = v___x_1210_;
v___y_1177_ = v___x_1211_;
v___y_1178_ = v___y_1195_;
v___y_1179_ = v___x_1212_;
v___y_1180_ = v___y_1196_;
v___y_1181_ = v___y_1200_;
v_skip_1182_ = v___y_1199_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1213_; uint8_t v___x_1214_; 
v___x_1213_ = lean_array_get_size(v___y_1201_);
lean_dec_ref(v___y_1201_);
v___x_1214_ = lean_nat_dec_eq(v___x_1213_, v___y_1198_);
lean_dec(v___y_1198_);
if (v___x_1214_ == 0)
{
v___y_1165_ = v___y_1191_;
v___y_1166_ = v___y_1193_;
v___y_1167_ = v___y_1192_;
v___y_1168_ = v___y_1206_;
v___y_1169_ = v___y_1197_;
v___y_1170_ = v___y_1203_;
v___y_1171_ = v___y_1205_;
v___y_1172_ = v___y_1204_;
v___y_1173_ = v___y_1194_;
v___y_1174_ = v___x_1209_;
v___y_1175_ = v___x_1208_;
v___y_1176_ = v___x_1210_;
v___y_1177_ = v___x_1211_;
v___y_1178_ = v___y_1195_;
v___y_1179_ = v___x_1212_;
v___y_1180_ = v___y_1196_;
v___y_1181_ = v___y_1200_;
v_skip_1182_ = v___y_1199_;
goto v___jp_1164_;
}
else
{
lean_object* v___x_1215_; 
lean_inc(v___y_1200_);
v___x_1215_ = l_Lean_MVarId_getType(v___y_1200_, v___y_1203_, v___y_1204_, v___y_1205_, v___y_1206_);
if (lean_obj_tag(v___x_1215_) == 0)
{
lean_object* v_a_1216_; lean_object* v___x_1217_; lean_object* v_a_1218_; uint8_t v___x_1219_; 
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref(v___x_1215_);
lean_inc(v___x_1208_);
lean_inc(v_a_1216_);
v___x_1217_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(v_a_1216_, v___x_1208_, v___y_1204_);
v_a_1218_ = lean_ctor_get(v___x_1217_, 0);
lean_inc(v_a_1218_);
lean_dec_ref(v___x_1217_);
v___x_1219_ = lean_unbox(v_a_1218_);
lean_dec(v_a_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v_a_1221_; uint8_t v___x_1222_; 
lean_inc(v___x_1211_);
v___x_1220_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(v_a_1216_, v___x_1211_, v___y_1204_);
v_a_1221_ = lean_ctor_get(v___x_1220_, 0);
lean_inc(v_a_1221_);
lean_dec_ref(v___x_1220_);
v___x_1222_ = lean_unbox(v_a_1221_);
lean_dec(v_a_1221_);
if (v___x_1222_ == 0)
{
lean_dec_ref(v___x_1212_);
lean_dec_ref(v___x_1209_);
lean_dec(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec(v___y_1191_);
lean_dec(v_a_1126_);
lean_dec(v_hFVarId_1076_);
v___y_1088_ = v___y_1205_;
v___y_1089_ = v___y_1204_;
v___y_1090_ = v___x_1208_;
v___y_1091_ = v___y_1206_;
v___y_1092_ = v___x_1211_;
v___y_1093_ = v___y_1200_;
v___y_1094_ = v___y_1203_;
goto v___jp_1087_;
}
else
{
v___y_1165_ = v___y_1191_;
v___y_1166_ = v___y_1193_;
v___y_1167_ = v___y_1192_;
v___y_1168_ = v___y_1206_;
v___y_1169_ = v___y_1197_;
v___y_1170_ = v___y_1203_;
v___y_1171_ = v___y_1205_;
v___y_1172_ = v___y_1204_;
v___y_1173_ = v___y_1194_;
v___y_1174_ = v___x_1209_;
v___y_1175_ = v___x_1208_;
v___y_1176_ = v___x_1210_;
v___y_1177_ = v___x_1211_;
v___y_1178_ = v___y_1195_;
v___y_1179_ = v___x_1212_;
v___y_1180_ = v___y_1196_;
v___y_1181_ = v___y_1200_;
v_skip_1182_ = v___y_1199_;
goto v___jp_1164_;
}
}
else
{
lean_dec(v_a_1216_);
v___y_1165_ = v___y_1191_;
v___y_1166_ = v___y_1193_;
v___y_1167_ = v___y_1192_;
v___y_1168_ = v___y_1206_;
v___y_1169_ = v___y_1197_;
v___y_1170_ = v___y_1203_;
v___y_1171_ = v___y_1205_;
v___y_1172_ = v___y_1204_;
v___y_1173_ = v___y_1194_;
v___y_1174_ = v___x_1209_;
v___y_1175_ = v___x_1208_;
v___y_1176_ = v___x_1210_;
v___y_1177_ = v___x_1211_;
v___y_1178_ = v___y_1195_;
v___y_1179_ = v___x_1212_;
v___y_1180_ = v___y_1196_;
v___y_1181_ = v___y_1200_;
v_skip_1182_ = v___y_1199_;
goto v___jp_1164_;
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec_ref(v___x_1212_);
lean_dec(v___x_1211_);
lean_dec_ref(v___x_1209_);
lean_dec(v___x_1208_);
lean_dec(v___y_1206_);
lean_dec_ref(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec_ref(v___y_1203_);
lean_dec(v___y_1200_);
lean_dec(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec(v___y_1191_);
lean_dec(v_a_1126_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v_hFVarId_1076_);
v_a_1223_ = lean_ctor_get(v___x_1215_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1215_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1215_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1215_);
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
}
}
v___jp_1231_:
{
lean_object* v___x_1249_; lean_object* v_a_1250_; uint8_t v___x_1251_; 
lean_inc(v___y_1239_);
v___x_1249_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg(v___y_1239_, v___y_1247_);
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
lean_inc(v_a_1250_);
lean_dec_ref(v___x_1249_);
v___x_1251_ = lean_unbox(v_a_1250_);
lean_dec(v_a_1250_);
if (v___x_1251_ == 0)
{
lean_dec(v___y_1239_);
lean_del_object(v___x_1161_);
v___y_1191_ = v___y_1232_;
v___y_1192_ = v___y_1234_;
v___y_1193_ = v___y_1233_;
v___y_1194_ = v___y_1235_;
v___y_1195_ = v___y_1236_;
v___y_1196_ = v___y_1237_;
v___y_1197_ = v___y_1238_;
v___y_1198_ = v___y_1240_;
v___y_1199_ = v___y_1242_;
v___y_1200_ = v___y_1241_;
v___y_1201_ = v___y_1243_;
v___y_1202_ = v___y_1244_;
v___y_1203_ = v___y_1245_;
v___y_1204_ = v___y_1246_;
v___y_1205_ = v___y_1247_;
v___y_1206_ = v___y_1248_;
goto v___jp_1190_;
}
else
{
lean_object* v___x_1252_; size_t v_sz_1253_; size_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v___x_1252_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__11, &l_Lean_Meta_substCore___lam__2___closed__11_once, _init_l_Lean_Meta_substCore___lam__2___closed__11);
v_sz_1253_ = lean_array_size(v___y_1243_);
v___x_1254_ = ((size_t)0ULL);
lean_inc_ref(v___y_1243_);
v___x_1255_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__9(v_sz_1253_, v___x_1254_, v___y_1243_);
v___x_1256_ = lean_array_to_list(v___x_1255_);
v___x_1257_ = lean_box(0);
v___x_1258_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__10(v___x_1256_, v___x_1257_);
v___x_1259_ = l_Lean_MessageData_ofList(v___x_1258_);
if (v_isShared_1162_ == 0)
{
lean_ctor_set_tag(v___x_1161_, 7);
lean_ctor_set(v___x_1161_, 1, v___x_1259_);
lean_ctor_set(v___x_1161_, 0, v___x_1252_);
v___x_1261_ = v___x_1161_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v___x_1252_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1259_);
v___x_1261_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; 
v___x_1262_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4(v___y_1239_, v___x_1261_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1262_) == 0)
{
lean_dec_ref(v___x_1262_);
v___y_1191_ = v___y_1232_;
v___y_1192_ = v___y_1234_;
v___y_1193_ = v___y_1233_;
v___y_1194_ = v___y_1235_;
v___y_1195_ = v___y_1236_;
v___y_1196_ = v___y_1237_;
v___y_1197_ = v___y_1238_;
v___y_1198_ = v___y_1240_;
v___y_1199_ = v___y_1242_;
v___y_1200_ = v___y_1241_;
v___y_1201_ = v___y_1243_;
v___y_1202_ = v___y_1244_;
v___y_1203_ = v___y_1245_;
v___y_1204_ = v___y_1246_;
v___y_1205_ = v___y_1247_;
v___y_1206_ = v___y_1248_;
goto v___jp_1190_;
}
else
{
lean_object* v_a_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1270_; 
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
lean_dec_ref(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec(v_a_1126_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
v_a_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1270_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1270_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_a_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1270_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1268_; 
if (v_isShared_1266_ == 0)
{
v___x_1268_ = v___x_1265_;
goto v_reusejp_1267_;
}
else
{
lean_object* v_reuseFailAlloc_1269_; 
v_reuseFailAlloc_1269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1269_, 0, v_a_1263_);
v___x_1268_ = v_reuseFailAlloc_1269_;
goto v_reusejp_1267_;
}
v_reusejp_1267_:
{
return v___x_1268_;
}
}
}
}
}
}
v___jp_1272_:
{
lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1287_ = lean_box(0);
lean_inc(v___y_1286_);
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v___y_1279_);
v___x_1288_ = l_Lean_Meta_introNCore(v___y_1282_, v___y_1279_, v___x_1287_, v___y_1280_, v___x_1163_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1288_) == 0)
{
lean_object* v_a_1289_; lean_object* v_fst_1290_; lean_object* v_snd_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1318_; 
v_a_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc(v_a_1289_);
lean_dec_ref(v___x_1288_);
v_fst_1290_ = lean_ctor_get(v_a_1289_, 0);
v_snd_1291_ = lean_ctor_get(v_a_1289_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_a_1289_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1293_ = v_a_1289_;
v_isShared_1294_ = v_isSharedCheck_1318_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_snd_1291_);
lean_inc(v_fst_1290_);
lean_dec(v_a_1289_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1318_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1295_; lean_object* v_a_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1317_; 
lean_inc(v___y_1278_);
v___x_1295_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg(v___y_1278_, v___y_1285_);
v_a_1296_ = lean_ctor_get(v___x_1295_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1295_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1298_ = v___x_1295_;
v_isShared_1299_ = v_isSharedCheck_1317_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_a_1296_);
lean_dec(v___x_1295_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1317_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
uint8_t v___x_1300_; 
v___x_1300_ = lean_unbox(v_a_1296_);
lean_dec(v_a_1296_);
if (v___x_1300_ == 0)
{
lean_del_object(v___x_1298_);
lean_del_object(v___x_1293_);
lean_inc(v_snd_1291_);
v___y_1232_ = v_snd_1291_;
v___y_1233_ = v___y_1273_;
v___y_1234_ = v___y_1274_;
v___y_1235_ = v___y_1275_;
v___y_1236_ = v___x_1287_;
v___y_1237_ = v___y_1276_;
v___y_1238_ = v___y_1277_;
v___y_1239_ = v___y_1278_;
v___y_1240_ = v___y_1279_;
v___y_1241_ = v_snd_1291_;
v___y_1242_ = v___y_1280_;
v___y_1243_ = v___y_1281_;
v___y_1244_ = v_fst_1290_;
v___y_1245_ = v___y_1283_;
v___y_1246_ = v___y_1284_;
v___y_1247_ = v___y_1285_;
v___y_1248_ = v___y_1286_;
goto v___jp_1231_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1303_; 
v___x_1301_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__13, &l_Lean_Meta_substCore___lam__2___closed__13_once, _init_l_Lean_Meta_substCore___lam__2___closed__13);
lean_inc(v_snd_1291_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 1);
lean_ctor_set(v___x_1298_, 0, v_snd_1291_);
v___x_1303_ = v___x_1298_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_snd_1291_);
v___x_1303_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
lean_object* v___x_1305_; 
if (v_isShared_1294_ == 0)
{
lean_ctor_set_tag(v___x_1293_, 7);
lean_ctor_set(v___x_1293_, 1, v___x_1303_);
lean_ctor_set(v___x_1293_, 0, v___x_1301_);
v___x_1305_ = v___x_1293_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1315_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
lean_object* v___x_1306_; 
lean_inc(v___y_1278_);
v___x_1306_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4(v___y_1278_, v___x_1305_, v___y_1283_, v___y_1284_, v___y_1285_, v___y_1286_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_dec_ref(v___x_1306_);
lean_inc(v_snd_1291_);
v___y_1232_ = v_snd_1291_;
v___y_1233_ = v___y_1273_;
v___y_1234_ = v___y_1274_;
v___y_1235_ = v___y_1275_;
v___y_1236_ = v___x_1287_;
v___y_1237_ = v___y_1276_;
v___y_1238_ = v___y_1277_;
v___y_1239_ = v___y_1278_;
v___y_1240_ = v___y_1279_;
v___y_1241_ = v_snd_1291_;
v___y_1242_ = v___y_1280_;
v___y_1243_ = v___y_1281_;
v___y_1244_ = v_fst_1290_;
v___y_1245_ = v___y_1283_;
v___y_1246_ = v___y_1284_;
v___y_1247_ = v___y_1285_;
v___y_1248_ = v___y_1286_;
goto v___jp_1231_;
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_dec(v_snd_1291_);
lean_dec(v_fst_1290_);
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1273_);
lean_del_object(v___x_1161_);
lean_dec(v_a_1126_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
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
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec_ref(v___y_1275_);
lean_dec(v___y_1273_);
lean_del_object(v___x_1161_);
lean_dec(v_a_1126_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
v_a_1319_ = lean_ctor_get(v___x_1288_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1288_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1288_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1288_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1324_; 
if (v_isShared_1322_ == 0)
{
v___x_1324_ = v___x_1321_;
goto v_reusejp_1323_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_a_1319_);
v___x_1324_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1323_;
}
v_reusejp_1323_:
{
return v___x_1324_;
}
}
}
}
v___jp_1327_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; 
v___x_1336_ = lean_unsigned_to_nat(2u);
v___x_1337_ = lean_mk_empty_array_with_capacity(v___x_1336_);
v___x_1338_ = lean_array_push(v___x_1337_, v___y_1331_);
lean_inc(v_hFVarId_1076_);
v___x_1339_ = lean_array_push(v___x_1338_, v_hFVarId_1076_);
v___x_1340_ = 0;
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
v___x_1341_ = l_Lean_MVarId_revert(v_mvarId_1075_, v___x_1339_, v___x_1163_, v___x_1340_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1371_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref(v___x_1341_);
v_fst_1343_ = lean_ctor_get(v_a_1342_, 0);
v_snd_1344_ = lean_ctor_get(v_a_1342_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1342_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1346_ = v_a_1342_;
v_isShared_1347_ = v_isSharedCheck_1371_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_snd_1344_);
lean_inc(v_fst_1343_);
lean_dec(v_a_1342_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1371_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v_a_1349_; lean_object* v___x_1351_; uint8_t v_isShared_1352_; uint8_t v_isSharedCheck_1370_; 
lean_inc(v___y_1330_);
v___x_1348_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg(v___y_1330_, v___y_1334_);
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1351_ = v___x_1348_;
v_isShared_1352_ = v_isSharedCheck_1370_;
goto v_resetjp_1350_;
}
else
{
lean_inc(v_a_1349_);
lean_dec(v___x_1348_);
v___x_1351_ = lean_box(0);
v_isShared_1352_ = v_isSharedCheck_1370_;
goto v_resetjp_1350_;
}
v_resetjp_1350_:
{
uint8_t v___x_1353_; 
v___x_1353_ = lean_unbox(v_a_1349_);
lean_dec(v_a_1349_);
if (v___x_1353_ == 0)
{
lean_del_object(v___x_1351_);
lean_del_object(v___x_1346_);
lean_inc(v_fst_1343_);
v___y_1273_ = v___x_1336_;
v___y_1274_ = v___x_1340_;
v___y_1275_ = v_fst_1343_;
v___y_1276_ = v___y_1328_;
v___y_1277_ = v___y_1329_;
v___y_1278_ = v___y_1330_;
v___y_1279_ = v___x_1336_;
v___y_1280_ = v___x_1340_;
v___y_1281_ = v_fst_1343_;
v___y_1282_ = v_snd_1344_;
v___y_1283_ = v___y_1332_;
v___y_1284_ = v___y_1333_;
v___y_1285_ = v___y_1334_;
v___y_1286_ = v___y_1335_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1354_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__15, &l_Lean_Meta_substCore___lam__2___closed__15_once, _init_l_Lean_Meta_substCore___lam__2___closed__15);
lean_inc(v_snd_1344_);
if (v_isShared_1352_ == 0)
{
lean_ctor_set_tag(v___x_1351_, 1);
lean_ctor_set(v___x_1351_, 0, v_snd_1344_);
v___x_1356_ = v___x_1351_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1369_; 
v_reuseFailAlloc_1369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1369_, 0, v_snd_1344_);
v___x_1356_ = v_reuseFailAlloc_1369_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1358_; 
if (v_isShared_1347_ == 0)
{
lean_ctor_set_tag(v___x_1346_, 7);
lean_ctor_set(v___x_1346_, 1, v___x_1356_);
lean_ctor_set(v___x_1346_, 0, v___x_1354_);
v___x_1358_ = v___x_1346_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1354_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; 
lean_inc(v___y_1330_);
v___x_1359_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4(v___y_1330_, v___x_1358_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_dec_ref(v___x_1359_);
lean_inc(v_fst_1343_);
v___y_1273_ = v___x_1336_;
v___y_1274_ = v___x_1340_;
v___y_1275_ = v_fst_1343_;
v___y_1276_ = v___y_1328_;
v___y_1277_ = v___y_1329_;
v___y_1278_ = v___y_1330_;
v___y_1279_ = v___x_1336_;
v___y_1280_ = v___x_1340_;
v___y_1281_ = v_fst_1343_;
v___y_1282_ = v_snd_1344_;
v___y_1283_ = v___y_1332_;
v___y_1284_ = v___y_1333_;
v___y_1285_ = v___y_1334_;
v___y_1286_ = v___y_1335_;
goto v___jp_1272_;
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec(v___y_1328_);
lean_del_object(v___x_1161_);
lean_dec(v_a_1126_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1367_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1367_ == 0)
{
v___x_1362_ = v___x_1359_;
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
else
{
lean_inc(v_a_1360_);
lean_dec(v___x_1359_);
v___x_1362_ = lean_box(0);
v_isShared_1363_ = v_isSharedCheck_1367_;
goto v_resetjp_1361_;
}
v_resetjp_1361_:
{
lean_object* v___x_1365_; 
if (v_isShared_1363_ == 0)
{
v___x_1365_ = v___x_1362_;
goto v_reusejp_1364_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v_a_1360_);
v___x_1365_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1364_;
}
v_reusejp_1364_:
{
return v___x_1365_;
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
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1330_);
lean_dec(v___y_1329_);
lean_dec(v___y_1328_);
lean_del_object(v___x_1161_);
lean_dec(v_a_1126_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
v_a_1372_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1341_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1341_);
v___x_1374_ = lean_box(0);
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
v_resetjp_1373_:
{
lean_object* v___x_1377_; 
if (v_isShared_1375_ == 0)
{
v___x_1377_ = v___x_1374_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_a_1372_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
v___jp_1380_:
{
lean_object* v___x_1391_; lean_object* v_a_1392_; uint8_t v___x_1393_; 
lean_inc(v___y_1386_);
lean_inc_ref(v___y_1384_);
v___x_1391_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(v___y_1384_, v___y_1386_, v___y_1388_);
v_a_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_a_1392_);
lean_dec_ref(v___x_1391_);
v___x_1393_ = lean_unbox(v_a_1392_);
lean_dec(v_a_1392_);
if (v___x_1393_ == 0)
{
lean_dec_ref(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_del_object(v___x_1156_);
lean_del_object(v___x_1152_);
v___y_1328_ = v___y_1381_;
v___y_1329_ = v___y_1382_;
v___y_1330_ = v___y_1383_;
v___y_1331_ = v___y_1386_;
v___y_1332_ = v___y_1387_;
v___y_1333_ = v___y_1388_;
v___y_1334_ = v___y_1389_;
v___y_1335_ = v___y_1390_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1397_; 
v___x_1394_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__17, &l_Lean_Meta_substCore___lam__2___closed__17_once, _init_l_Lean_Meta_substCore___lam__2___closed__17);
v___x_1395_ = l_Lean_MessageData_ofExpr(v___y_1385_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 7);
lean_ctor_set(v___x_1156_, 1, v___x_1395_);
lean_ctor_set(v___x_1156_, 0, v___x_1394_);
v___x_1397_ = v___x_1156_;
goto v_reusejp_1396_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1394_);
lean_ctor_set(v_reuseFailAlloc_1414_, 1, v___x_1395_);
v___x_1397_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1396_;
}
v_reusejp_1396_:
{
lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1403_; 
v___x_1398_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__19, &l_Lean_Meta_substCore___lam__2___closed__19_once, _init_l_Lean_Meta_substCore___lam__2___closed__19);
v___x_1399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1399_, 0, v___x_1397_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
v___x_1400_ = l_Lean_indentExpr(v___y_1384_);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set(v___x_1152_, 0, v___x_1401_);
v___x_1403_ = v___x_1152_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1401_);
v___x_1403_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; 
lean_inc(v_mvarId_1075_);
v___x_1404_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1127_, v_mvarId_1075_, v___x_1403_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
if (lean_obj_tag(v___x_1404_) == 0)
{
lean_dec_ref(v___x_1404_);
v___y_1328_ = v___y_1381_;
v___y_1329_ = v___y_1382_;
v___y_1330_ = v___y_1383_;
v___y_1331_ = v___y_1386_;
v___y_1332_ = v___y_1387_;
v___y_1333_ = v___y_1388_;
v___y_1334_ = v___y_1389_;
v___y_1335_ = v___y_1390_;
goto v___jp_1327_;
}
else
{
lean_object* v_a_1405_; lean_object* v___x_1407_; uint8_t v_isShared_1408_; uint8_t v_isSharedCheck_1412_; 
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec(v___y_1383_);
lean_dec(v___y_1382_);
lean_dec(v___y_1381_);
lean_del_object(v___x_1161_);
lean_dec(v_a_1126_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
lean_dec(v_mvarId_1075_);
v_a_1405_ = lean_ctor_get(v___x_1404_, 0);
v_isSharedCheck_1412_ = !lean_is_exclusive(v___x_1404_);
if (v_isSharedCheck_1412_ == 0)
{
v___x_1407_ = v___x_1404_;
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
else
{
lean_inc(v_a_1405_);
lean_dec(v___x_1404_);
v___x_1407_ = lean_box(0);
v_isShared_1408_ = v_isSharedCheck_1412_;
goto v_resetjp_1406_;
}
v_resetjp_1406_:
{
lean_object* v___x_1410_; 
if (v_isShared_1408_ == 0)
{
v___x_1410_ = v___x_1407_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1411_; 
v_reuseFailAlloc_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1411_, 0, v_a_1405_);
v___x_1410_ = v_reuseFailAlloc_1411_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
return v___x_1410_;
}
}
}
}
}
}
}
v___jp_1415_:
{
lean_object* v___x_1418_; 
v___x_1418_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1417_, v___y_1083_);
if (lean_obj_tag(v___y_1416_) == 1)
{
lean_object* v_a_1419_; lean_object* v_fvarId_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v_a_1423_; uint8_t v___x_1424_; 
lean_dec_ref(v___x_1131_);
v_a_1419_ = lean_ctor_get(v___x_1418_, 0);
lean_inc(v_a_1419_);
lean_dec_ref(v___x_1418_);
v_fvarId_1420_ = lean_ctor_get(v___y_1416_, 0);
lean_inc(v_fvarId_1420_);
v___x_1421_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__22));
v___x_1422_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg(v___x_1421_, v___y_1084_);
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = lean_unbox(v_a_1423_);
lean_dec(v_a_1423_);
if (v___x_1424_ == 0)
{
lean_inc(v_fvarId_1420_);
v___y_1381_ = v___x_1421_;
v___y_1382_ = v_fvarId_1420_;
v___y_1383_ = v___x_1421_;
v___y_1384_ = v_a_1419_;
v___y_1385_ = v___y_1416_;
v___y_1386_ = v_fvarId_1420_;
v___y_1387_ = v___y_1082_;
v___y_1388_ = v___y_1083_;
v___y_1389_ = v___y_1084_;
v___y_1390_ = v___y_1085_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1425_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__24, &l_Lean_Meta_substCore___lam__2___closed__24_once, _init_l_Lean_Meta_substCore___lam__2___closed__24);
lean_inc_ref(v___y_1416_);
v___x_1426_ = l_Lean_MessageData_ofExpr(v___y_1416_);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__26, &l_Lean_Meta_substCore___lam__2___closed__26_once, _init_l_Lean_Meta_substCore___lam__2___closed__26);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
lean_inc(v_fvarId_1420_);
v___x_1430_ = l_Lean_MessageData_ofName(v_fvarId_1420_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__28, &l_Lean_Meta_substCore___lam__2___closed__28_once, _init_l_Lean_Meta_substCore___lam__2___closed__28);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
lean_inc(v_a_1419_);
v___x_1434_ = l_Lean_MessageData_ofExpr(v_a_1419_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4(v___x_1421_, v___x_1435_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_dec_ref(v___x_1436_);
lean_inc(v_fvarId_1420_);
v___y_1381_ = v___x_1421_;
v___y_1382_ = v_fvarId_1420_;
v___y_1383_ = v___x_1421_;
v___y_1384_ = v_a_1419_;
v___y_1385_ = v___y_1416_;
v___y_1386_ = v_fvarId_1420_;
v___y_1387_ = v___y_1082_;
v___y_1388_ = v___y_1083_;
v___y_1389_ = v___y_1084_;
v___y_1390_ = v___y_1085_;
goto v___jp_1380_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_fvarId_1420_);
lean_dec_ref(v___y_1416_);
lean_dec(v_a_1419_);
lean_del_object(v___x_1161_);
lean_del_object(v___x_1156_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1126_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
lean_dec(v_mvarId_1075_);
v_a_1437_ = lean_ctor_get(v___x_1436_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1436_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1436_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1436_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1418_);
lean_del_object(v___x_1161_);
lean_del_object(v___x_1156_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1126_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
if (v_symm_1080_ == 0)
{
lean_object* v___x_1445_; 
v___x_1445_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__29));
v___y_1133_ = v___y_1416_;
v___y_1134_ = v___x_1445_;
goto v___jp_1132_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__30));
v___y_1133_ = v___y_1416_;
v___y_1134_ = v___x_1446_;
goto v___jp_1132_;
}
}
}
v___jp_1447_:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1448_, v___y_1083_);
if (v_symm_1080_ == 0)
{
lean_object* v_a_1450_; 
lean_dec(v_fst_1158_);
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref(v___x_1449_);
v___y_1416_ = v_a_1450_;
v___y_1417_ = v_snd_1159_;
goto v___jp_1415_;
}
else
{
lean_object* v_a_1451_; 
lean_dec(v_snd_1159_);
v_a_1451_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1449_);
v___y_1416_ = v_a_1451_;
v___y_1417_ = v_fst_1158_;
goto v___jp_1415_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1456_; lean_object* v___x_1458_; uint8_t v_isShared_1459_; uint8_t v_isSharedCheck_1463_; 
lean_dec_ref(v___x_1131_);
lean_dec(v_a_1126_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
lean_dec(v_mvarId_1075_);
v_a_1456_ = lean_ctor_get(v___x_1146_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1146_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1146_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1146_);
v___x_1458_ = lean_box(0);
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
v_resetjp_1457_:
{
lean_object* v___x_1461_; 
if (v_isShared_1459_ == 0)
{
v___x_1461_ = v___x_1458_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v_a_1456_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
return v___x_1461_;
}
}
}
v___jp_1132_:
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1135_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__3, &l_Lean_Meta_substCore___lam__2___closed__3_once, _init_l_Lean_Meta_substCore___lam__2___closed__3);
v___x_1136_ = l_Lean_stringToMessageData(v___y_1134_);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_indentExpr(v___x_1131_);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__5, &l_Lean_Meta_substCore___lam__2___closed__5_once, _init_l_Lean_Meta_substCore___lam__2___closed__5);
v___x_1141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1139_);
lean_ctor_set(v___x_1141_, 1, v___x_1140_);
v___x_1142_ = l_Lean_indentExpr(v___y_1133_);
v___x_1143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1143_, 0, v___x_1141_);
lean_ctor_set(v___x_1143_, 1, v___x_1142_);
v___x_1144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
v___x_1145_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1127_, v_mvarId_1075_, v___x_1144_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
return v___x_1145_;
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_a_1126_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
lean_dec(v_mvarId_1075_);
v_a_1464_ = lean_ctor_get(v___x_1129_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1129_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1129_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1129_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1469_; 
if (v_isShared_1467_ == 0)
{
v___x_1469_ = v___x_1466_;
goto v_reusejp_1468_;
}
else
{
lean_object* v_reuseFailAlloc_1470_; 
v_reuseFailAlloc_1470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1470_, 0, v_a_1464_);
v___x_1469_ = v_reuseFailAlloc_1470_;
goto v_reusejp_1468_;
}
v_reusejp_1468_:
{
return v___x_1469_;
}
}
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_a_1126_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
lean_dec(v_mvarId_1075_);
v_a_1472_ = lean_ctor_get(v___x_1128_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1128_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1128_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1128_);
v___x_1474_ = lean_box(0);
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
v_resetjp_1473_:
{
lean_object* v___x_1477_; 
if (v_isShared_1475_ == 0)
{
v___x_1477_ = v___x_1474_;
goto v_reusejp_1476_;
}
else
{
lean_object* v_reuseFailAlloc_1478_; 
v_reuseFailAlloc_1478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1478_, 0, v_a_1472_);
v___x_1477_ = v_reuseFailAlloc_1478_;
goto v_reusejp_1476_;
}
v_reusejp_1476_:
{
return v___x_1477_;
}
}
}
}
else
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1487_; 
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v_fvarSubst_1079_);
lean_dec(v___x_1077_);
lean_dec(v_hFVarId_1076_);
lean_dec(v_mvarId_1075_);
v_a_1480_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1125_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1125_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v___x_1485_; 
if (v_isShared_1483_ == 0)
{
v___x_1485_ = v___x_1482_;
goto v_reusejp_1484_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v_a_1480_);
v___x_1485_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1484_;
}
v_reusejp_1484_:
{
return v___x_1485_;
}
}
}
v___jp_1087_:
{
if (v_clearH_1078_ == 0)
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1092_);
lean_dec(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_fvarSubst_1079_);
lean_ctor_set(v___x_1095_, 1, v___y_1093_);
v___x_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1096_, 0, v___x_1095_);
return v___x_1096_;
}
else
{
lean_object* v___x_1097_; 
lean_inc(v___y_1091_);
lean_inc_ref(v___y_1088_);
lean_inc(v___y_1089_);
lean_inc_ref(v___y_1094_);
v___x_1097_ = l_Lean_MVarId_clear(v___y_1093_, v___y_1092_, v___y_1094_, v___y_1089_, v___y_1088_, v___y_1091_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref(v___x_1097_);
v___x_1099_ = l_Lean_MVarId_clear(v_a_1098_, v___y_1090_, v___y_1094_, v___y_1089_, v___y_1088_, v___y_1091_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1108_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1102_ = v___x_1099_;
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1099_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1108_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1104_; lean_object* v___x_1106_; 
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v_fvarSubst_1079_);
lean_ctor_set(v___x_1104_, 1, v_a_1100_);
if (v_isShared_1103_ == 0)
{
lean_ctor_set(v___x_1102_, 0, v___x_1104_);
v___x_1106_ = v___x_1102_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v___x_1104_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
else
{
lean_object* v_a_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1116_; 
lean_dec(v_fvarSubst_1079_);
v_a_1109_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1116_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1116_ == 0)
{
v___x_1111_ = v___x_1099_;
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_a_1109_);
lean_dec(v___x_1099_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1116_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1114_; 
if (v_isShared_1112_ == 0)
{
v___x_1114_ = v___x_1111_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_a_1109_);
v___x_1114_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
return v___x_1114_;
}
}
}
}
else
{
lean_object* v_a_1117_; lean_object* v___x_1119_; uint8_t v_isShared_1120_; uint8_t v_isSharedCheck_1124_; 
lean_dec_ref(v___y_1094_);
lean_dec(v___y_1091_);
lean_dec(v___y_1090_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1088_);
lean_dec(v_fvarSubst_1079_);
v_a_1117_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1124_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1119_ = v___x_1097_;
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
else
{
lean_inc(v_a_1117_);
lean_dec(v___x_1097_);
v___x_1119_ = lean_box(0);
v_isShared_1120_ = v_isSharedCheck_1124_;
goto v_resetjp_1118_;
}
v_resetjp_1118_:
{
lean_object* v___x_1122_; 
if (v_isShared_1120_ == 0)
{
v___x_1122_ = v___x_1119_;
goto v_reusejp_1121_;
}
else
{
lean_object* v_reuseFailAlloc_1123_; 
v_reuseFailAlloc_1123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1123_, 0, v_a_1117_);
v___x_1122_ = v_reuseFailAlloc_1123_;
goto v_reusejp_1121_;
}
v_reusejp_1121_:
{
return v___x_1122_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object* v_mvarId_1488_, lean_object* v_hFVarId_1489_, lean_object* v___x_1490_, lean_object* v_clearH_1491_, lean_object* v_fvarSubst_1492_, lean_object* v_symm_1493_, lean_object* v_tryToSkip_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v_clearH_boxed_1500_; uint8_t v_symm_boxed_1501_; uint8_t v_tryToSkip_boxed_1502_; lean_object* v_res_1503_; 
v_clearH_boxed_1500_ = lean_unbox(v_clearH_1491_);
v_symm_boxed_1501_ = lean_unbox(v_symm_1493_);
v_tryToSkip_boxed_1502_ = lean_unbox(v_tryToSkip_1494_);
v_res_1503_ = l_Lean_Meta_substCore___lam__2(v_mvarId_1488_, v_hFVarId_1489_, v___x_1490_, v_clearH_boxed_1500_, v_fvarSubst_1492_, v_symm_boxed_1501_, v_tryToSkip_boxed_1502_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object* v_mvarId_1504_, lean_object* v_hFVarId_1505_, uint8_t v_symm_1506_, lean_object* v_fvarSubst_1507_, uint8_t v_clearH_1508_, uint8_t v_tryToSkip_1509_, lean_object* v_a_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___f_1519_; lean_object* v___x_1520_; 
v___x_1515_ = lean_box(0);
v___x_1516_ = lean_box(v_clearH_1508_);
v___x_1517_ = lean_box(v_symm_1506_);
v___x_1518_ = lean_box(v_tryToSkip_1509_);
lean_inc(v_mvarId_1504_);
v___f_1519_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__2___boxed), 12, 7);
lean_closure_set(v___f_1519_, 0, v_mvarId_1504_);
lean_closure_set(v___f_1519_, 1, v_hFVarId_1505_);
lean_closure_set(v___f_1519_, 2, v___x_1515_);
lean_closure_set(v___f_1519_, 3, v___x_1516_);
lean_closure_set(v___f_1519_, 4, v_fvarSubst_1507_);
lean_closure_set(v___f_1519_, 5, v___x_1517_);
lean_closure_set(v___f_1519_, 6, v___x_1518_);
v___x_1520_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(v_mvarId_1504_, v___f_1519_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
return v___x_1520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* v_mvarId_1521_, lean_object* v_hFVarId_1522_, lean_object* v_symm_1523_, lean_object* v_fvarSubst_1524_, lean_object* v_clearH_1525_, lean_object* v_tryToSkip_1526_, lean_object* v_a_1527_, lean_object* v_a_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_){
_start:
{
uint8_t v_symm_boxed_1532_; uint8_t v_clearH_boxed_1533_; uint8_t v_tryToSkip_boxed_1534_; lean_object* v_res_1535_; 
v_symm_boxed_1532_ = lean_unbox(v_symm_1523_);
v_clearH_boxed_1533_ = lean_unbox(v_clearH_1525_);
v_tryToSkip_boxed_1534_ = lean_unbox(v_tryToSkip_1526_);
v_res_1535_ = l_Lean_Meta_substCore(v_mvarId_1521_, v_hFVarId_1522_, v_symm_boxed_1532_, v_fvarSubst_1524_, v_clearH_boxed_1533_, v_tryToSkip_boxed_1534_, v_a_1527_, v_a_1528_, v_a_1529_, v_a_1530_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(lean_object* v_fst_1536_, lean_object* v_fst_1537_, lean_object* v_n_1538_, lean_object* v_i_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_1536_, v_fst_1537_, v_n_1538_, v_i_1539_, v_a_1541_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___boxed(lean_object* v_fst_1548_, lean_object* v_fst_1549_, lean_object* v_n_1550_, lean_object* v_i_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(v_fst_1548_, v_fst_1549_, v_n_1550_, v_i_1551_, v_a_1552_, v_a_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v___y_1555_);
lean_dec_ref(v___y_1554_);
lean_dec(v_n_1550_);
lean_dec_ref(v_fst_1549_);
lean_dec_ref(v_fst_1548_);
return v_res_1559_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6(lean_object* v_mvarId_1560_, lean_object* v_val_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6___redArg(v_mvarId_1560_, v_val_1561_, v___y_1563_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6___boxed(lean_object* v_mvarId_1568_, lean_object* v_val_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6(v_mvarId_1568_, v_val_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9(lean_object* v_00_u03b1_1576_, lean_object* v_name_1577_, uint8_t v_bi_1578_, lean_object* v_type_1579_, lean_object* v_k_1580_, uint8_t v_kind_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___redArg(v_name_1577_, v_bi_1578_, v_type_1579_, v_k_1580_, v_kind_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9___boxed(lean_object* v_00_u03b1_1588_, lean_object* v_name_1589_, lean_object* v_bi_1590_, lean_object* v_type_1591_, lean_object* v_k_1592_, lean_object* v_kind_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v_bi_boxed_1599_; uint8_t v_kind_boxed_1600_; lean_object* v_res_1601_; 
v_bi_boxed_1599_ = lean_unbox(v_bi_1590_);
v_kind_boxed_1600_ = lean_unbox(v_kind_1593_);
v_res_1601_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7_spec__9(v_00_u03b1_1588_, v_name_1589_, v_bi_boxed_1599_, v_type_1591_, v_k_1592_, v_kind_boxed_1600_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7(lean_object* v_00_u03b1_1602_, lean_object* v_name_1603_, lean_object* v_type_1604_, lean_object* v_k_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7___redArg(v_name_1603_, v_type_1604_, v_k_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7___boxed(lean_object* v_00_u03b1_1612_, lean_object* v_name_1613_, lean_object* v_type_1614_, lean_object* v_k_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__7(v_00_u03b1_1612_, v_name_1613_, v_type_1614_, v_k_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7(lean_object* v_00_u03b2_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7___redArg(v_x_1623_, v_x_1624_, v_x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9(lean_object* v_00_u03b2_1627_, lean_object* v_x_1628_, size_t v_x_1629_, size_t v_x_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg(v_x_1628_, v_x_1629_, v_x_1630_, v_x_1631_, v_x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___boxed(lean_object* v_00_u03b2_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
size_t v_x_34888__boxed_1640_; size_t v_x_34889__boxed_1641_; lean_object* v_res_1642_; 
v_x_34888__boxed_1640_ = lean_unbox_usize(v_x_1636_);
lean_dec(v_x_1636_);
v_x_34889__boxed_1641_ = lean_unbox_usize(v_x_1637_);
lean_dec(v_x_1637_);
v_res_1642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9(v_00_u03b2_1634_, v_x_1635_, v_x_34888__boxed_1640_, v_x_34889__boxed_1641_, v_x_1638_, v_x_1639_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14(lean_object* v_00_u03b2_1643_, lean_object* v_n_1644_, lean_object* v_k_1645_, lean_object* v_v_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14___redArg(v_n_1644_, v_k_1645_, v_v_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15(lean_object* v_00_u03b2_1648_, size_t v_depth_1649_, lean_object* v_keys_1650_, lean_object* v_vals_1651_, lean_object* v_heq_1652_, lean_object* v_i_1653_, lean_object* v_entries_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15___redArg(v_depth_1649_, v_keys_1650_, v_vals_1651_, v_i_1653_, v_entries_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15___boxed(lean_object* v_00_u03b2_1656_, lean_object* v_depth_1657_, lean_object* v_keys_1658_, lean_object* v_vals_1659_, lean_object* v_heq_1660_, lean_object* v_i_1661_, lean_object* v_entries_1662_){
_start:
{
size_t v_depth_boxed_1663_; lean_object* v_res_1664_; 
v_depth_boxed_1663_ = lean_unbox_usize(v_depth_1657_);
lean_dec(v_depth_1657_);
v_res_1664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__15(v_00_u03b2_1656_, v_depth_boxed_1663_, v_keys_1658_, v_vals_1659_, v_heq_1660_, v_i_1661_, v_entries_1662_);
lean_dec_ref(v_vals_1659_);
lean_dec_ref(v_keys_1658_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14_spec__15(lean_object* v_00_u03b2_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9_spec__14_spec__15___redArg(v_x_1666_, v_x_1667_, v_x_1668_, v_x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* v_fvarId_1674_, lean_object* v_mvarId_1675_, uint8_t v_tryToClear_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
lean_inc_ref(v___y_1677_);
lean_inc(v_fvarId_1674_);
v___x_1682_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1674_, v___y_1677_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref(v___x_1682_);
v___x_1684_ = l_Lean_LocalDecl_type(v_a_1683_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
v___x_1685_ = lean_whnf(v___x_1684_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1688_; uint8_t v_isShared_1689_; uint8_t v_isSharedCheck_1770_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1688_ = v___x_1685_;
v_isShared_1689_ = v_isSharedCheck_1770_;
goto v_resetjp_1687_;
}
else
{
lean_inc(v_a_1686_);
lean_dec(v___x_1685_);
v___x_1688_ = lean_box(0);
v_isShared_1689_ = v_isSharedCheck_1770_;
goto v_resetjp_1687_;
}
v_resetjp_1687_:
{
lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1690_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_1691_ = lean_unsigned_to_nat(4u);
v___x_1692_ = l_Lean_Expr_isAppOfArity(v_a_1686_, v___x_1690_, v___x_1691_);
if (v___x_1692_ == 0)
{
lean_object* v___x_1693_; lean_object* v___x_1695_; 
lean_dec(v_a_1686_);
lean_dec(v_a_1683_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
v___x_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1693_, 0, v_fvarId_1674_);
lean_ctor_set(v___x_1693_, 1, v_mvarId_1675_);
if (v_isShared_1689_ == 0)
{
lean_ctor_set(v___x_1688_, 0, v___x_1693_);
v___x_1695_ = v___x_1688_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; 
lean_del_object(v___x_1688_);
v___x_1697_ = l_Lean_Expr_appFn_x21(v_a_1686_);
v___x_1698_ = l_Lean_Expr_appFn_x21(v___x_1697_);
v___x_1699_ = l_Lean_Expr_appFn_x21(v___x_1698_);
v___x_1700_ = l_Lean_Expr_appArg_x21(v___x_1699_);
lean_dec_ref(v___x_1699_);
v___x_1701_ = l_Lean_Expr_appArg_x21(v___x_1697_);
lean_dec_ref(v___x_1697_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
v___x_1702_ = l_Lean_Meta_isExprDefEq(v___x_1700_, v___x_1701_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1702_) == 0)
{
lean_object* v_a_1703_; lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1761_; 
v_a_1703_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1705_ = v___x_1702_;
v_isShared_1706_ = v_isSharedCheck_1761_;
goto v_resetjp_1704_;
}
else
{
lean_inc(v_a_1703_);
lean_dec(v___x_1702_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1761_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
uint8_t v___x_1707_; 
v___x_1707_ = lean_unbox(v_a_1703_);
if (v___x_1707_ == 0)
{
lean_object* v___x_1708_; lean_object* v___x_1710_; 
lean_dec(v_a_1703_);
lean_dec_ref(v___x_1698_);
lean_dec(v_a_1686_);
lean_dec(v_a_1683_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
v___x_1708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1708_, 0, v_fvarId_1674_);
lean_ctor_set(v___x_1708_, 1, v_mvarId_1675_);
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1708_);
v___x_1710_ = v___x_1705_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v___x_1708_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
else
{
lean_object* v___x_1712_; lean_object* v___x_1713_; 
lean_del_object(v___x_1705_);
lean_inc(v_fvarId_1674_);
v___x_1712_ = l_Lean_mkFVar(v_fvarId_1674_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
v___x_1713_ = l_Lean_Meta_mkEqOfHEq(v___x_1712_, v___x_1692_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1713_) == 0)
{
lean_object* v_a_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v_a_1714_ = lean_ctor_get(v___x_1713_, 0);
lean_inc(v_a_1714_);
lean_dec_ref(v___x_1713_);
v___x_1715_ = l_Lean_Expr_appArg_x21(v___x_1698_);
lean_dec_ref(v___x_1698_);
v___x_1716_ = l_Lean_Expr_appArg_x21(v_a_1686_);
lean_dec(v_a_1686_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
v___x_1717_ = l_Lean_Meta_mkEq(v___x_1715_, v___x_1716_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref(v___x_1717_);
v___x_1719_ = l_Lean_LocalDecl_userName(v_a_1683_);
lean_dec(v_a_1683_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
v___x_1720_ = l_Lean_MVarId_assert(v_mvarId_1675_, v___x_1719_, v_a_1718_, v_a_1714_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1720_) == 0)
{
if (v_tryToClear_1676_ == 0)
{
lean_object* v_a_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v_fvarId_1674_);
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref(v___x_1720_);
v___x_1722_ = lean_unbox(v_a_1703_);
lean_dec(v_a_1703_);
v___x_1723_ = l_Lean_Meta_intro1Core(v_a_1721_, v___x_1722_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1723_;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1724_);
lean_dec_ref(v___x_1720_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
v___x_1725_ = l_Lean_MVarId_tryClear(v_a_1724_, v_fvarId_1674_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = lean_unbox(v_a_1703_);
lean_dec(v_a_1703_);
v___x_1728_ = l_Lean_Meta_intro1Core(v_a_1726_, v___x_1727_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
return v___x_1728_;
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_a_1703_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
v_a_1729_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1736_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1736_ == 0)
{
v___x_1731_ = v___x_1725_;
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
else
{
lean_inc(v_a_1729_);
lean_dec(v___x_1725_);
v___x_1731_ = lean_box(0);
v_isShared_1732_ = v_isSharedCheck_1736_;
goto v_resetjp_1730_;
}
v_resetjp_1730_:
{
lean_object* v___x_1734_; 
if (v_isShared_1732_ == 0)
{
v___x_1734_ = v___x_1731_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1735_; 
v_reuseFailAlloc_1735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1735_, 0, v_a_1729_);
v___x_1734_ = v_reuseFailAlloc_1735_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
return v___x_1734_;
}
}
}
}
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_a_1703_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_fvarId_1674_);
v_a_1737_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1720_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1720_);
v___x_1739_ = lean_box(0);
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
v_resetjp_1738_:
{
lean_object* v___x_1742_; 
if (v_isShared_1740_ == 0)
{
v___x_1742_ = v___x_1739_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1743_; 
v_reuseFailAlloc_1743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1743_, 0, v_a_1737_);
v___x_1742_ = v_reuseFailAlloc_1743_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
return v___x_1742_;
}
}
}
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec(v_a_1714_);
lean_dec(v_a_1703_);
lean_dec(v_a_1683_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_mvarId_1675_);
lean_dec(v_fvarId_1674_);
v_a_1745_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1717_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1717_);
v___x_1747_ = lean_box(0);
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
v_resetjp_1746_:
{
lean_object* v___x_1750_; 
if (v_isShared_1748_ == 0)
{
v___x_1750_ = v___x_1747_;
goto v_reusejp_1749_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_a_1745_);
v___x_1750_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1749_;
}
v_reusejp_1749_:
{
return v___x_1750_;
}
}
}
}
else
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1760_; 
lean_dec(v_a_1703_);
lean_dec_ref(v___x_1698_);
lean_dec(v_a_1686_);
lean_dec(v_a_1683_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_mvarId_1675_);
lean_dec(v_fvarId_1674_);
v_a_1753_ = lean_ctor_get(v___x_1713_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1713_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1713_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1713_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
lean_object* v___x_1758_; 
if (v_isShared_1756_ == 0)
{
v___x_1758_ = v___x_1755_;
goto v_reusejp_1757_;
}
else
{
lean_object* v_reuseFailAlloc_1759_; 
v_reuseFailAlloc_1759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1759_, 0, v_a_1753_);
v___x_1758_ = v_reuseFailAlloc_1759_;
goto v_reusejp_1757_;
}
v_reusejp_1757_:
{
return v___x_1758_;
}
}
}
}
}
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec_ref(v___x_1698_);
lean_dec(v_a_1686_);
lean_dec(v_a_1683_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_mvarId_1675_);
lean_dec(v_fvarId_1674_);
v_a_1762_ = lean_ctor_get(v___x_1702_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1702_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1702_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1702_);
v___x_1764_ = lean_box(0);
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
v_resetjp_1763_:
{
lean_object* v___x_1767_; 
if (v_isShared_1765_ == 0)
{
v___x_1767_ = v___x_1764_;
goto v_reusejp_1766_;
}
else
{
lean_object* v_reuseFailAlloc_1768_; 
v_reuseFailAlloc_1768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1768_, 0, v_a_1762_);
v___x_1767_ = v_reuseFailAlloc_1768_;
goto v_reusejp_1766_;
}
v_reusejp_1766_:
{
return v___x_1767_;
}
}
}
}
}
}
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_a_1683_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_mvarId_1675_);
lean_dec(v_fvarId_1674_);
v_a_1771_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1685_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1685_);
v___x_1773_ = lean_box(0);
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
v_resetjp_1772_:
{
lean_object* v___x_1776_; 
if (v_isShared_1774_ == 0)
{
v___x_1776_ = v___x_1773_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_mvarId_1675_);
lean_dec(v_fvarId_1674_);
v_a_1779_ = lean_ctor_get(v___x_1682_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1682_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1682_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1682_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object* v_fvarId_1787_, lean_object* v_mvarId_1788_, lean_object* v_tryToClear_1789_, lean_object* v___y_1790_, lean_object* v___y_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_){
_start:
{
uint8_t v_tryToClear_boxed_1795_; lean_object* v_res_1796_; 
v_tryToClear_boxed_1795_ = lean_unbox(v_tryToClear_1789_);
v_res_1796_ = l_Lean_Meta_heqToEq___lam__0(v_fvarId_1787_, v_mvarId_1788_, v_tryToClear_boxed_1795_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object* v_mvarId_1797_, lean_object* v_fvarId_1798_, uint8_t v_tryToClear_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v___x_1805_; lean_object* v___f_1806_; lean_object* v___x_1807_; 
v___x_1805_ = lean_box(v_tryToClear_1799_);
lean_inc(v_mvarId_1797_);
v___f_1806_ = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1806_, 0, v_fvarId_1798_);
lean_closure_set(v___f_1806_, 1, v_mvarId_1797_);
lean_closure_set(v___f_1806_, 2, v___x_1805_);
v___x_1807_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(v_mvarId_1797_, v___f_1806_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* v_mvarId_1808_, lean_object* v_fvarId_1809_, lean_object* v_tryToClear_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
uint8_t v_tryToClear_boxed_1816_; lean_object* v_res_1817_; 
v_tryToClear_boxed_1816_ = lean_unbox(v_tryToClear_1810_);
v_res_1817_ = l_Lean_Meta_heqToEq(v_mvarId_1808_, v_fvarId_1809_, v_tryToClear_boxed_1816_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1821_, lean_object* v_as_1822_, size_t v_sz_1823_, size_t v_i_1824_, lean_object* v_b_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_){
_start:
{
lean_object* v_a_1832_; uint8_t v___x_1836_; 
v___x_1836_ = lean_usize_dec_lt(v_i_1824_, v_sz_1823_);
if (v___x_1836_ == 0)
{
lean_object* v___x_1837_; 
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_x_1821_);
v___x_1837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1837_, 0, v_b_1825_);
return v___x_1837_;
}
else
{
lean_object* v___x_1838_; lean_object* v_a_1840_; lean_object* v___x_1844_; lean_object* v_a_1845_; 
lean_dec_ref(v_b_1825_);
v___x_1838_ = lean_box(0);
v___x_1844_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1845_ = lean_array_uget(v_as_1822_, v_i_1824_);
if (lean_obj_tag(v_a_1845_) == 0)
{
v_a_1832_ = v___x_1844_;
goto v___jp_1831_;
}
else
{
lean_object* v_val_1846_; lean_object* v___x_1848_; uint8_t v_isShared_1849_; uint8_t v_isSharedCheck_1933_; 
v_val_1846_ = lean_ctor_get(v_a_1845_, 0);
v_isSharedCheck_1933_ = !lean_is_exclusive(v_a_1845_);
if (v_isSharedCheck_1933_ == 0)
{
v___x_1848_ = v_a_1845_;
v_isShared_1849_ = v_isSharedCheck_1933_;
goto v_resetjp_1847_;
}
else
{
lean_inc(v_val_1846_);
lean_dec(v_a_1845_);
v___x_1848_ = lean_box(0);
v_isShared_1849_ = v_isSharedCheck_1933_;
goto v_resetjp_1847_;
}
v_resetjp_1847_:
{
uint8_t v___x_1857_; 
v___x_1857_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1846_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1863_; lean_object* v___x_1864_; 
v___x_1863_ = l_Lean_LocalDecl_type(v_val_1846_);
lean_inc(v___y_1829_);
lean_inc_ref(v___y_1828_);
lean_inc(v___y_1827_);
lean_inc_ref(v___y_1826_);
v___x_1864_ = l_Lean_Meta_matchEq_x3f(v___x_1863_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref(v___x_1864_);
if (lean_obj_tag(v_a_1865_) == 1)
{
lean_object* v_val_1866_; lean_object* v_snd_1867_; lean_object* v_fst_1868_; lean_object* v_snd_1869_; lean_object* v___x_1870_; 
v_val_1866_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_val_1866_);
lean_dec_ref(v_a_1865_);
v_snd_1867_ = lean_ctor_get(v_val_1866_, 1);
lean_inc(v_snd_1867_);
lean_dec(v_val_1866_);
v_fst_1868_ = lean_ctor_get(v_snd_1867_, 0);
lean_inc(v_fst_1868_);
v_snd_1869_ = lean_ctor_get(v_snd_1867_, 1);
lean_inc(v_snd_1869_);
lean_dec(v_snd_1867_);
v___x_1870_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1868_, v___y_1827_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref(v___x_1870_);
v___x_1872_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1869_, v___y_1827_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___y_1875_; uint8_t v___y_1876_; lean_object* v___y_1889_; uint8_t v___y_1894_; uint8_t v___x_1906_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref(v___x_1872_);
v___x_1906_ = l_Lean_Expr_isFVar(v_a_1873_);
if (v___x_1906_ == 0)
{
v___y_1894_ = v___x_1906_;
goto v___jp_1893_;
}
else
{
lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = l_Lean_Expr_fvarId_x21(v_a_1873_);
v___x_1908_ = l_Lean_instBEqFVarId_beq(v___x_1907_, v_x_1821_);
lean_dec(v___x_1907_);
v___y_1894_ = v___x_1908_;
goto v___jp_1893_;
}
v___jp_1874_:
{
if (v___y_1876_ == 0)
{
lean_dec(v___y_1875_);
lean_dec(v_a_1873_);
lean_dec(v_val_1846_);
v_a_1832_ = v___x_1844_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1877_; 
lean_inc(v_x_1821_);
v___x_1877_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(v_a_1873_, v_x_1821_, v___y_1875_);
lean_dec(v___y_1875_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; uint8_t v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref(v___x_1877_);
v___x_1879_ = lean_unbox(v_a_1878_);
lean_dec(v_a_1878_);
if (v___x_1879_ == 0)
{
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_x_1821_);
goto v___jp_1858_;
}
else
{
if (v___x_1857_ == 0)
{
lean_dec(v_val_1846_);
v_a_1832_ = v___x_1844_;
goto v___jp_1831_;
}
else
{
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_x_1821_);
goto v___jp_1858_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_val_1846_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_x_1821_);
v_a_1880_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1877_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1877_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
}
v___jp_1888_:
{
uint8_t v___x_1890_; 
v___x_1890_ = l_Lean_Expr_isFVar(v_a_1871_);
if (v___x_1890_ == 0)
{
lean_dec(v_a_1871_);
v___y_1875_ = v___y_1889_;
v___y_1876_ = v___x_1890_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1891_; uint8_t v___x_1892_; 
v___x_1891_ = l_Lean_Expr_fvarId_x21(v_a_1871_);
lean_dec(v_a_1871_);
v___x_1892_ = l_Lean_instBEqFVarId_beq(v___x_1891_, v_x_1821_);
lean_dec(v___x_1891_);
v___y_1875_ = v___y_1889_;
v___y_1876_ = v___x_1892_;
goto v___jp_1874_;
}
}
v___jp_1893_:
{
if (v___y_1894_ == 0)
{
lean_del_object(v___x_1848_);
lean_inc(v___y_1827_);
v___y_1889_ = v___y_1827_;
goto v___jp_1888_;
}
else
{
lean_object* v___x_1895_; 
lean_inc(v_x_1821_);
lean_inc(v_a_1871_);
v___x_1895_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(v_a_1871_, v_x_1821_, v___y_1827_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; uint8_t v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref(v___x_1895_);
v___x_1897_ = lean_unbox(v_a_1896_);
lean_dec(v_a_1896_);
if (v___x_1897_ == 0)
{
lean_dec(v_a_1873_);
lean_dec(v_a_1871_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_x_1821_);
goto v___jp_1850_;
}
else
{
if (v___x_1857_ == 0)
{
lean_del_object(v___x_1848_);
lean_inc(v___y_1827_);
v___y_1889_ = v___y_1827_;
goto v___jp_1888_;
}
else
{
lean_dec(v_a_1873_);
lean_dec(v_a_1871_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_x_1821_);
goto v___jp_1850_;
}
}
}
else
{
lean_object* v_a_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1905_; 
lean_dec(v_a_1873_);
lean_dec(v_a_1871_);
lean_del_object(v___x_1848_);
lean_dec(v_val_1846_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_x_1821_);
v_a_1898_ = lean_ctor_get(v___x_1895_, 0);
v_isSharedCheck_1905_ = !lean_is_exclusive(v___x_1895_);
if (v_isSharedCheck_1905_ == 0)
{
v___x_1900_ = v___x_1895_;
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_a_1898_);
lean_dec(v___x_1895_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1905_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1903_; 
if (v_isShared_1901_ == 0)
{
v___x_1903_ = v___x_1900_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v_a_1898_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
}
else
{
lean_object* v_a_1909_; lean_object* v___x_1911_; uint8_t v_isShared_1912_; uint8_t v_isSharedCheck_1916_; 
lean_dec(v_a_1871_);
lean_del_object(v___x_1848_);
lean_dec(v_val_1846_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_x_1821_);
v_a_1909_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1916_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1911_ = v___x_1872_;
v_isShared_1912_ = v_isSharedCheck_1916_;
goto v_resetjp_1910_;
}
else
{
lean_inc(v_a_1909_);
lean_dec(v___x_1872_);
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
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_snd_1869_);
lean_del_object(v___x_1848_);
lean_dec(v_val_1846_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_x_1821_);
v_a_1917_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1870_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1870_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
lean_object* v___x_1922_; 
if (v_isShared_1920_ == 0)
{
v___x_1922_ = v___x_1919_;
goto v_reusejp_1921_;
}
else
{
lean_object* v_reuseFailAlloc_1923_; 
v_reuseFailAlloc_1923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1923_, 0, v_a_1917_);
v___x_1922_ = v_reuseFailAlloc_1923_;
goto v_reusejp_1921_;
}
v_reusejp_1921_:
{
return v___x_1922_;
}
}
}
}
else
{
lean_dec(v_a_1865_);
lean_del_object(v___x_1848_);
lean_dec(v_val_1846_);
v_a_1832_ = v___x_1844_;
goto v___jp_1831_;
}
}
else
{
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_del_object(v___x_1848_);
lean_dec(v_val_1846_);
lean_dec(v___y_1829_);
lean_dec_ref(v___y_1828_);
lean_dec(v___y_1827_);
lean_dec_ref(v___y_1826_);
lean_dec(v_x_1821_);
v_a_1925_ = lean_ctor_get(v___x_1864_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1864_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1864_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1864_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v___x_1930_; 
if (v_isShared_1928_ == 0)
{
v___x_1930_ = v___x_1927_;
goto v_reusejp_1929_;
}
else
{
lean_object* v_reuseFailAlloc_1931_; 
v_reuseFailAlloc_1931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1931_, 0, v_a_1925_);
v___x_1930_ = v_reuseFailAlloc_1931_;
goto v_reusejp_1929_;
}
v_reusejp_1929_:
{
return v___x_1930_;
}
}
}
}
else
{
lean_del_object(v___x_1848_);
lean_dec(v_val_1846_);
v_a_1832_ = v___x_1844_;
goto v___jp_1831_;
}
v___jp_1850_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1855_; 
v___x_1851_ = l_Lean_LocalDecl_fvarId(v_val_1846_);
lean_dec(v_val_1846_);
v___x_1852_ = lean_box(v___x_1836_);
v___x_1853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1851_);
lean_ctor_set(v___x_1853_, 1, v___x_1852_);
if (v_isShared_1849_ == 0)
{
lean_ctor_set(v___x_1848_, 0, v___x_1853_);
v___x_1855_ = v___x_1848_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
v_a_1840_ = v___x_1855_;
goto v___jp_1839_;
}
}
v___jp_1858_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1859_ = l_Lean_LocalDecl_fvarId(v_val_1846_);
lean_dec(v_val_1846_);
v___x_1860_ = lean_box(v___x_1857_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
v___x_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
v_a_1840_ = v___x_1862_;
goto v___jp_1839_;
}
}
}
v___jp_1839_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; 
v___x_1841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_a_1840_);
v___x_1842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1838_);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v___x_1842_);
return v___x_1843_;
}
}
v___jp_1831_:
{
size_t v___x_1833_; size_t v___x_1834_; 
v___x_1833_ = ((size_t)1ULL);
v___x_1834_ = lean_usize_add(v_i_1824_, v___x_1833_);
v_i_1824_ = v___x_1834_;
v_b_1825_ = v_a_1832_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1934_, lean_object* v_as_1935_, lean_object* v_sz_1936_, lean_object* v_i_1937_, lean_object* v_b_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_, lean_object* v___y_1943_){
_start:
{
size_t v_sz_boxed_1944_; size_t v_i_boxed_1945_; lean_object* v_res_1946_; 
v_sz_boxed_1944_ = lean_unbox_usize(v_sz_1936_);
lean_dec(v_sz_1936_);
v_i_boxed_1945_ = lean_unbox_usize(v_i_1937_);
lean_dec(v_i_1937_);
v_res_1946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1934_, v_as_1935_, v_sz_boxed_1944_, v_i_boxed_1945_, v_b_1938_, v___y_1939_, v___y_1940_, v___y_1941_, v___y_1942_);
lean_dec_ref(v_as_1935_);
return v_res_1946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object* v_x_1947_, lean_object* v_as_1948_, size_t v_sz_1949_, size_t v_i_1950_, lean_object* v_b_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_a_1958_; uint8_t v___x_1962_; 
v___x_1962_ = lean_usize_dec_lt(v_i_1950_, v_sz_1949_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_x_1947_);
v___x_1963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1963_, 0, v_b_1951_);
return v___x_1963_;
}
else
{
lean_object* v___x_1964_; lean_object* v_a_1966_; lean_object* v___x_1970_; lean_object* v_a_1971_; 
lean_dec_ref(v_b_1951_);
v___x_1964_ = lean_box(0);
v___x_1970_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1971_ = lean_array_uget(v_as_1948_, v_i_1950_);
if (lean_obj_tag(v_a_1971_) == 0)
{
v_a_1958_ = v___x_1970_;
goto v___jp_1957_;
}
else
{
lean_object* v_val_1972_; lean_object* v___x_1974_; uint8_t v_isShared_1975_; uint8_t v_isSharedCheck_2059_; 
v_val_1972_ = lean_ctor_get(v_a_1971_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v_a_1971_);
if (v_isSharedCheck_2059_ == 0)
{
v___x_1974_ = v_a_1971_;
v_isShared_1975_ = v_isSharedCheck_2059_;
goto v_resetjp_1973_;
}
else
{
lean_inc(v_val_1972_);
lean_dec(v_a_1971_);
v___x_1974_ = lean_box(0);
v_isShared_1975_ = v_isSharedCheck_2059_;
goto v_resetjp_1973_;
}
v_resetjp_1973_:
{
uint8_t v___x_1983_; 
v___x_1983_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1972_);
if (v___x_1983_ == 0)
{
lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = l_Lean_LocalDecl_type(v_val_1972_);
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
v___x_1990_ = l_Lean_Meta_matchEq_x3f(v___x_1989_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref(v___x_1990_);
if (lean_obj_tag(v_a_1991_) == 1)
{
lean_object* v_val_1992_; lean_object* v_snd_1993_; lean_object* v_fst_1994_; lean_object* v_snd_1995_; lean_object* v___x_1996_; 
v_val_1992_ = lean_ctor_get(v_a_1991_, 0);
lean_inc(v_val_1992_);
lean_dec_ref(v_a_1991_);
v_snd_1993_ = lean_ctor_get(v_val_1992_, 1);
lean_inc(v_snd_1993_);
lean_dec(v_val_1992_);
v_fst_1994_ = lean_ctor_get(v_snd_1993_, 0);
lean_inc(v_fst_1994_);
v_snd_1995_ = lean_ctor_get(v_snd_1993_, 1);
lean_inc(v_snd_1995_);
lean_dec(v_snd_1993_);
v___x_1996_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1994_, v___y_1953_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; lean_object* v___x_1998_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref(v___x_1996_);
v___x_1998_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1995_, v___y_1953_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___y_2001_; uint8_t v___y_2002_; lean_object* v___y_2015_; uint8_t v___y_2020_; uint8_t v___x_2032_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref(v___x_1998_);
v___x_2032_ = l_Lean_Expr_isFVar(v_a_1999_);
if (v___x_2032_ == 0)
{
v___y_2020_ = v___x_2032_;
goto v___jp_2019_;
}
else
{
lean_object* v___x_2033_; uint8_t v___x_2034_; 
v___x_2033_ = l_Lean_Expr_fvarId_x21(v_a_1999_);
v___x_2034_ = l_Lean_instBEqFVarId_beq(v___x_2033_, v_x_1947_);
lean_dec(v___x_2033_);
v___y_2020_ = v___x_2034_;
goto v___jp_2019_;
}
v___jp_2000_:
{
if (v___y_2002_ == 0)
{
lean_dec(v___y_2001_);
lean_dec(v_a_1999_);
lean_dec(v_val_1972_);
v_a_1958_ = v___x_1970_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_2003_; 
lean_inc(v_x_1947_);
v___x_2003_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(v_a_1999_, v_x_1947_, v___y_2001_);
lean_dec(v___y_2001_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; uint8_t v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref(v___x_2003_);
v___x_2005_ = lean_unbox(v_a_2004_);
lean_dec(v_a_2004_);
if (v___x_2005_ == 0)
{
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_x_1947_);
goto v___jp_1984_;
}
else
{
if (v___x_1983_ == 0)
{
lean_dec(v_val_1972_);
v_a_1958_ = v___x_1970_;
goto v___jp_1957_;
}
else
{
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_x_1947_);
goto v___jp_1984_;
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_val_1972_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_x_1947_);
v_a_2006_ = lean_ctor_get(v___x_2003_, 0);
v_isSharedCheck_2013_ = !lean_is_exclusive(v___x_2003_);
if (v_isSharedCheck_2013_ == 0)
{
v___x_2008_ = v___x_2003_;
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_a_2006_);
lean_dec(v___x_2003_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2013_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2011_; 
if (v_isShared_2009_ == 0)
{
v___x_2011_ = v___x_2008_;
goto v_reusejp_2010_;
}
else
{
lean_object* v_reuseFailAlloc_2012_; 
v_reuseFailAlloc_2012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2012_, 0, v_a_2006_);
v___x_2011_ = v_reuseFailAlloc_2012_;
goto v_reusejp_2010_;
}
v_reusejp_2010_:
{
return v___x_2011_;
}
}
}
}
}
v___jp_2014_:
{
uint8_t v___x_2016_; 
v___x_2016_ = l_Lean_Expr_isFVar(v_a_1997_);
if (v___x_2016_ == 0)
{
lean_dec(v_a_1997_);
v___y_2001_ = v___y_2015_;
v___y_2002_ = v___x_2016_;
goto v___jp_2000_;
}
else
{
lean_object* v___x_2017_; uint8_t v___x_2018_; 
v___x_2017_ = l_Lean_Expr_fvarId_x21(v_a_1997_);
lean_dec(v_a_1997_);
v___x_2018_ = l_Lean_instBEqFVarId_beq(v___x_2017_, v_x_1947_);
lean_dec(v___x_2017_);
v___y_2001_ = v___y_2015_;
v___y_2002_ = v___x_2018_;
goto v___jp_2000_;
}
}
v___jp_2019_:
{
if (v___y_2020_ == 0)
{
lean_del_object(v___x_1974_);
lean_inc(v___y_1953_);
v___y_2015_ = v___y_1953_;
goto v___jp_2014_;
}
else
{
lean_object* v___x_2021_; 
lean_inc(v_x_1947_);
lean_inc(v_a_1997_);
v___x_2021_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__5___redArg(v_a_1997_, v_x_1947_, v___y_1953_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; uint8_t v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref(v___x_2021_);
v___x_2023_ = lean_unbox(v_a_2022_);
lean_dec(v_a_2022_);
if (v___x_2023_ == 0)
{
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_x_1947_);
goto v___jp_1976_;
}
else
{
if (v___x_1983_ == 0)
{
lean_del_object(v___x_1974_);
lean_inc(v___y_1953_);
v___y_2015_ = v___y_1953_;
goto v___jp_2014_;
}
else
{
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_x_1947_);
goto v___jp_1976_;
}
}
}
else
{
lean_object* v_a_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2031_; 
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_del_object(v___x_1974_);
lean_dec(v_val_1972_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_x_1947_);
v_a_2024_ = lean_ctor_get(v___x_2021_, 0);
v_isSharedCheck_2031_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2031_ == 0)
{
v___x_2026_ = v___x_2021_;
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_a_2024_);
lean_dec(v___x_2021_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2031_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
lean_object* v___x_2029_; 
if (v_isShared_2027_ == 0)
{
v___x_2029_ = v___x_2026_;
goto v_reusejp_2028_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v_a_2024_);
v___x_2029_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2028_;
}
v_reusejp_2028_:
{
return v___x_2029_;
}
}
}
}
}
}
else
{
lean_object* v_a_2035_; lean_object* v___x_2037_; uint8_t v_isShared_2038_; uint8_t v_isSharedCheck_2042_; 
lean_dec(v_a_1997_);
lean_del_object(v___x_1974_);
lean_dec(v_val_1972_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_x_1947_);
v_a_2035_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2037_ = v___x_1998_;
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
else
{
lean_inc(v_a_2035_);
lean_dec(v___x_1998_);
v___x_2037_ = lean_box(0);
v_isShared_2038_ = v_isSharedCheck_2042_;
goto v_resetjp_2036_;
}
v_resetjp_2036_:
{
lean_object* v___x_2040_; 
if (v_isShared_2038_ == 0)
{
v___x_2040_ = v___x_2037_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v_a_2035_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_snd_1995_);
lean_del_object(v___x_1974_);
lean_dec(v_val_1972_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_x_1947_);
v_a_2043_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_1996_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_1996_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
lean_dec(v_a_1991_);
lean_del_object(v___x_1974_);
lean_dec(v_val_1972_);
v_a_1958_ = v___x_1970_;
goto v___jp_1957_;
}
}
else
{
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_del_object(v___x_1974_);
lean_dec(v_val_1972_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v_x_1947_);
v_a_2051_ = lean_ctor_get(v___x_1990_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_1990_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_1990_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_1990_);
v___x_2053_ = lean_box(0);
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
v_resetjp_2052_:
{
lean_object* v___x_2056_; 
if (v_isShared_2054_ == 0)
{
v___x_2056_ = v___x_2053_;
goto v_reusejp_2055_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_a_2051_);
v___x_2056_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2055_;
}
v_reusejp_2055_:
{
return v___x_2056_;
}
}
}
}
else
{
lean_del_object(v___x_1974_);
lean_dec(v_val_1972_);
v_a_1958_ = v___x_1970_;
goto v___jp_1957_;
}
v___jp_1976_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1977_ = l_Lean_LocalDecl_fvarId(v_val_1972_);
lean_dec(v_val_1972_);
v___x_1978_ = lean_box(v___x_1962_);
v___x_1979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1977_);
lean_ctor_set(v___x_1979_, 1, v___x_1978_);
if (v_isShared_1975_ == 0)
{
lean_ctor_set(v___x_1974_, 0, v___x_1979_);
v___x_1981_ = v___x_1974_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
v_a_1966_ = v___x_1981_;
goto v___jp_1965_;
}
}
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; 
v___x_1985_ = l_Lean_LocalDecl_fvarId(v_val_1972_);
lean_dec(v_val_1972_);
v___x_1986_ = lean_box(v___x_1983_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
v___x_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1988_, 0, v___x_1987_);
v_a_1966_ = v___x_1988_;
goto v___jp_1965_;
}
}
}
v___jp_1965_:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_a_1966_);
v___x_1968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1968_, 0, v___x_1967_);
lean_ctor_set(v___x_1968_, 1, v___x_1964_);
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v___x_1968_);
return v___x_1969_;
}
}
v___jp_1957_:
{
size_t v___x_1959_; size_t v___x_1960_; lean_object* v___x_1961_; 
v___x_1959_ = ((size_t)1ULL);
v___x_1960_ = lean_usize_add(v_i_1950_, v___x_1959_);
v___x_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1947_, v_as_1948_, v_sz_1949_, v___x_1960_, v_a_1958_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
return v___x_1961_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2060_, lean_object* v_as_2061_, lean_object* v_sz_2062_, lean_object* v_i_2063_, lean_object* v_b_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_){
_start:
{
size_t v_sz_boxed_2070_; size_t v_i_boxed_2071_; lean_object* v_res_2072_; 
v_sz_boxed_2070_ = lean_unbox_usize(v_sz_2062_);
lean_dec(v_sz_2062_);
v_i_boxed_2071_ = lean_unbox_usize(v_i_2063_);
lean_dec(v_i_2063_);
v_res_2072_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2060_, v_as_2061_, v_sz_boxed_2070_, v_i_boxed_2071_, v_b_2064_, v___y_2065_, v___y_2066_, v___y_2067_, v___y_2068_);
lean_dec_ref(v_as_2061_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object* v_x_2073_, lean_object* v_x_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_){
_start:
{
if (lean_obj_tag(v_x_2074_) == 0)
{
lean_object* v_cs_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; size_t v_sz_2083_; size_t v___x_2084_; lean_object* v___x_2085_; 
v_cs_2080_ = lean_ctor_get(v_x_2074_, 0);
v___x_2081_ = lean_box(0);
v___x_2082_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2083_ = lean_array_size(v_cs_2080_);
v___x_2084_ = ((size_t)0ULL);
v___x_2085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2073_, v_cs_2080_, v_sz_2083_, v___x_2084_, v___x_2082_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2085_) == 0)
{
lean_object* v_a_2086_; lean_object* v___x_2088_; uint8_t v_isShared_2089_; uint8_t v_isSharedCheck_2098_; 
v_a_2086_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2088_ = v___x_2085_;
v_isShared_2089_ = v_isSharedCheck_2098_;
goto v_resetjp_2087_;
}
else
{
lean_inc(v_a_2086_);
lean_dec(v___x_2085_);
v___x_2088_ = lean_box(0);
v_isShared_2089_ = v_isSharedCheck_2098_;
goto v_resetjp_2087_;
}
v_resetjp_2087_:
{
lean_object* v_fst_2090_; 
v_fst_2090_ = lean_ctor_get(v_a_2086_, 0);
lean_inc(v_fst_2090_);
lean_dec(v_a_2086_);
if (lean_obj_tag(v_fst_2090_) == 0)
{
lean_object* v___x_2092_; 
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v___x_2081_);
v___x_2092_ = v___x_2088_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v___x_2081_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
else
{
lean_object* v_val_2094_; lean_object* v___x_2096_; 
v_val_2094_ = lean_ctor_get(v_fst_2090_, 0);
lean_inc(v_val_2094_);
lean_dec_ref(v_fst_2090_);
if (v_isShared_2089_ == 0)
{
lean_ctor_set(v___x_2088_, 0, v_val_2094_);
v___x_2096_ = v___x_2088_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_val_2094_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
v_a_2099_ = lean_ctor_get(v___x_2085_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2085_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2085_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2085_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v_vs_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; size_t v_sz_2110_; size_t v___x_2111_; lean_object* v___x_2112_; 
v_vs_2107_ = lean_ctor_get(v_x_2074_, 0);
v___x_2108_ = lean_box(0);
v___x_2109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2110_ = lean_array_size(v_vs_2107_);
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2073_, v_vs_2107_, v_sz_2110_, v___x_2111_, v___x_2109_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2115_; uint8_t v_isShared_2116_; uint8_t v_isSharedCheck_2125_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2115_ = v___x_2112_;
v_isShared_2116_ = v_isSharedCheck_2125_;
goto v_resetjp_2114_;
}
else
{
lean_inc(v_a_2113_);
lean_dec(v___x_2112_);
v___x_2115_ = lean_box(0);
v_isShared_2116_ = v_isSharedCheck_2125_;
goto v_resetjp_2114_;
}
v_resetjp_2114_:
{
lean_object* v_fst_2117_; 
v_fst_2117_ = lean_ctor_get(v_a_2113_, 0);
lean_inc(v_fst_2117_);
lean_dec(v_a_2113_);
if (lean_obj_tag(v_fst_2117_) == 0)
{
lean_object* v___x_2119_; 
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v___x_2108_);
v___x_2119_ = v___x_2115_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2108_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
else
{
lean_object* v_val_2121_; lean_object* v___x_2123_; 
v_val_2121_ = lean_ctor_get(v_fst_2117_, 0);
lean_inc(v_val_2121_);
lean_dec_ref(v_fst_2117_);
if (v_isShared_2116_ == 0)
{
lean_ctor_set(v___x_2115_, 0, v_val_2121_);
v___x_2123_ = v___x_2115_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_val_2121_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
}
}
else
{
lean_object* v_a_2126_; lean_object* v___x_2128_; uint8_t v_isShared_2129_; uint8_t v_isSharedCheck_2133_; 
v_a_2126_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2128_ = v___x_2112_;
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
else
{
lean_inc(v_a_2126_);
lean_dec(v___x_2112_);
v___x_2128_ = lean_box(0);
v_isShared_2129_ = v_isSharedCheck_2133_;
goto v_resetjp_2127_;
}
v_resetjp_2127_:
{
lean_object* v___x_2131_; 
if (v_isShared_2129_ == 0)
{
v___x_2131_ = v___x_2128_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_a_2126_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2134_, lean_object* v_as_2135_, size_t v_sz_2136_, size_t v_i_2137_, lean_object* v_b_2138_, lean_object* v___y_2139_, lean_object* v___y_2140_, lean_object* v___y_2141_, lean_object* v___y_2142_){
_start:
{
uint8_t v___x_2144_; 
v___x_2144_ = lean_usize_dec_lt(v_i_2137_, v_sz_2136_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v_x_2134_);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v_b_2138_);
return v___x_2145_;
}
else
{
lean_object* v_a_2146_; lean_object* v___x_2147_; 
lean_dec_ref(v_b_2138_);
v_a_2146_ = lean_array_uget_borrowed(v_as_2135_, v_i_2137_);
lean_inc(v___y_2142_);
lean_inc_ref(v___y_2141_);
lean_inc(v___y_2140_);
lean_inc_ref(v___y_2139_);
lean_inc(v_x_2134_);
v___x_2147_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2134_, v_a_2146_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
if (lean_obj_tag(v___x_2147_) == 0)
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2162_; 
v_a_2148_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2150_ = v___x_2147_;
v_isShared_2151_ = v_isSharedCheck_2162_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2147_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2162_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2152_; 
v___x_2152_ = lean_box(0);
if (lean_obj_tag(v_a_2148_) == 1)
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2156_; 
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v_x_2134_);
v___x_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_a_2148_);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
lean_ctor_set(v___x_2154_, 1, v___x_2152_);
if (v_isShared_2151_ == 0)
{
lean_ctor_set(v___x_2150_, 0, v___x_2154_);
v___x_2156_ = v___x_2150_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2154_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
else
{
lean_object* v___x_2158_; size_t v___x_2159_; size_t v___x_2160_; 
lean_del_object(v___x_2150_);
lean_dec(v_a_2148_);
v___x_2158_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = lean_usize_add(v_i_2137_, v___x_2159_);
v_i_2137_ = v___x_2160_;
v_b_2138_ = v___x_2158_;
goto _start;
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v___y_2142_);
lean_dec_ref(v___y_2141_);
lean_dec(v___y_2140_);
lean_dec_ref(v___y_2139_);
lean_dec(v_x_2134_);
v_a_2163_ = lean_ctor_get(v___x_2147_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2147_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2147_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2147_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2171_, lean_object* v_as_2172_, lean_object* v_sz_2173_, lean_object* v_i_2174_, lean_object* v_b_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
size_t v_sz_boxed_2181_; size_t v_i_boxed_2182_; lean_object* v_res_2183_; 
v_sz_boxed_2181_ = lean_unbox_usize(v_sz_2173_);
lean_dec(v_sz_2173_);
v_i_boxed_2182_ = lean_unbox_usize(v_i_2174_);
lean_dec(v_i_2174_);
v_res_2183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2171_, v_as_2172_, v_sz_boxed_2181_, v_i_boxed_2182_, v_b_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec_ref(v_as_2172_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2184_, lean_object* v_x_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2184_, v_x_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec_ref(v_x_2185_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object* v_x_2192_, lean_object* v_t_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_){
_start:
{
lean_object* v_root_2199_; lean_object* v_tail_2200_; lean_object* v___x_2201_; 
v_root_2199_ = lean_ctor_get(v_t_2193_, 0);
v_tail_2200_ = lean_ctor_get(v_t_2193_, 1);
lean_inc(v___y_2197_);
lean_inc_ref(v___y_2196_);
lean_inc(v___y_2195_);
lean_inc_ref(v___y_2194_);
lean_inc(v_x_2192_);
v___x_2201_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2192_, v_root_2199_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2201_) == 0)
{
lean_object* v_a_2202_; 
v_a_2202_ = lean_ctor_get(v___x_2201_, 0);
lean_inc(v_a_2202_);
if (lean_obj_tag(v_a_2202_) == 0)
{
lean_object* v___x_2203_; size_t v_sz_2204_; size_t v___x_2205_; lean_object* v___x_2206_; 
lean_dec_ref(v___x_2201_);
v___x_2203_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2204_ = lean_array_size(v_tail_2200_);
v___x_2205_ = ((size_t)0ULL);
v___x_2206_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2192_, v_tail_2200_, v_sz_2204_, v___x_2205_, v___x_2203_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
if (lean_obj_tag(v___x_2206_) == 0)
{
lean_object* v_a_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2219_; 
v_a_2207_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2219_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2219_ == 0)
{
v___x_2209_ = v___x_2206_;
v_isShared_2210_ = v_isSharedCheck_2219_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_a_2207_);
lean_dec(v___x_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2219_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v_fst_2211_; 
v_fst_2211_ = lean_ctor_get(v_a_2207_, 0);
lean_inc(v_fst_2211_);
lean_dec(v_a_2207_);
if (lean_obj_tag(v_fst_2211_) == 0)
{
lean_object* v___x_2213_; 
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v_a_2202_);
v___x_2213_ = v___x_2209_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v_a_2202_);
v___x_2213_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
return v___x_2213_;
}
}
else
{
lean_object* v_val_2215_; lean_object* v___x_2217_; 
v_val_2215_ = lean_ctor_get(v_fst_2211_, 0);
lean_inc(v_val_2215_);
lean_dec_ref(v_fst_2211_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v_val_2215_);
v___x_2217_ = v___x_2209_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_val_2215_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
}
}
else
{
lean_object* v_a_2220_; lean_object* v___x_2222_; uint8_t v_isShared_2223_; uint8_t v_isSharedCheck_2227_; 
v_a_2220_ = lean_ctor_get(v___x_2206_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2206_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2222_ = v___x_2206_;
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
else
{
lean_inc(v_a_2220_);
lean_dec(v___x_2206_);
v___x_2222_ = lean_box(0);
v_isShared_2223_ = v_isSharedCheck_2227_;
goto v_resetjp_2221_;
}
v_resetjp_2221_:
{
lean_object* v___x_2225_; 
if (v_isShared_2223_ == 0)
{
v___x_2225_ = v___x_2222_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
}
}
else
{
lean_dec_ref(v_a_2202_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v_x_2192_);
return v___x_2201_;
}
}
else
{
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v_x_2192_);
return v___x_2201_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* v_x_2228_, lean_object* v_t_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_){
_start:
{
lean_object* v_res_2235_; 
v_res_2235_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2228_, v_t_2229_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
lean_dec_ref(v_t_2229_);
return v_res_2235_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object* v_x_2236_, lean_object* v_lctx_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_){
_start:
{
lean_object* v_decls_2243_; lean_object* v___x_2244_; 
v_decls_2243_ = lean_ctor_get(v_lctx_2237_, 1);
v___x_2244_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2236_, v_decls_2243_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object* v_x_2245_, lean_object* v_lctx_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_res_2252_; 
v_res_2252_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2245_, v_lctx_2246_, v___y_2247_, v___y_2248_, v___y_2249_, v___y_2250_);
lean_dec_ref(v_lctx_2246_);
return v_res_2252_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; 
v___x_2254_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__0));
v___x_2255_ = l_Lean_stringToMessageData(v___x_2254_);
return v___x_2255_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__2));
v___x_2258_ = l_Lean_stringToMessageData(v___x_2257_);
return v___x_2258_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__4));
v___x_2261_ = l_Lean_stringToMessageData(v___x_2260_);
return v___x_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object* v_x_2262_, lean_object* v_mvarId_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v___y_2270_; lean_object* v___y_2271_; lean_object* v___y_2272_; lean_object* v___y_2273_; lean_object* v___x_2318_; 
lean_inc_ref(v___y_2264_);
lean_inc(v_x_2262_);
v___x_2318_ = l_Lean_FVarId_getDecl___redArg(v_x_2262_, v___y_2264_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; uint8_t v___x_2320_; uint8_t v___x_2321_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref(v___x_2318_);
v___x_2320_ = 0;
v___x_2321_ = l_Lean_LocalDecl_isLet(v_a_2319_, v___x_2320_);
lean_dec(v_a_2319_);
if (v___x_2321_ == 0)
{
v___y_2270_ = v___y_2264_;
v___y_2271_ = v___y_2265_;
v___y_2272_ = v___y_2266_;
v___y_2273_ = v___y_2267_;
goto v___jp_2269_;
}
else
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2322_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__1));
v___x_2323_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2262_);
v___x_2324_ = l_Lean_mkFVar(v_x_2262_);
v___x_2325_ = l_Lean_MessageData_ofExpr(v___x_2324_);
v___x_2326_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2326_, 0, v___x_2323_);
lean_ctor_set(v___x_2326_, 1, v___x_2325_);
v___x_2327_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2326_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_inc(v_mvarId_2263_);
v___x_2330_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2322_, v_mvarId_2263_, v___x_2329_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_dec_ref(v___x_2330_);
v___y_2270_ = v___y_2264_;
v___y_2271_ = v___y_2265_;
v___y_2272_ = v___y_2266_;
v___y_2273_ = v___y_2267_;
goto v___jp_2269_;
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v_mvarId_2263_);
lean_dec(v_x_2262_);
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2330_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2330_);
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
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v___y_2267_);
lean_dec_ref(v___y_2266_);
lean_dec(v___y_2265_);
lean_dec_ref(v___y_2264_);
lean_dec(v_mvarId_2263_);
lean_dec(v_x_2262_);
v_a_2339_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2318_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2318_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2344_; 
if (v_isShared_2342_ == 0)
{
v___x_2344_ = v___x_2341_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2345_; 
v_reuseFailAlloc_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2339_);
v___x_2344_ = v_reuseFailAlloc_2345_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
return v___x_2344_;
}
}
}
v___jp_2269_:
{
lean_object* v_lctx_2274_; lean_object* v___x_2275_; 
v_lctx_2274_ = lean_ctor_get(v___y_2270_, 2);
lean_inc(v___y_2273_);
lean_inc_ref(v___y_2272_);
lean_inc(v___y_2271_);
lean_inc_ref(v___y_2270_);
lean_inc(v_x_2262_);
v___x_2275_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2262_, v_lctx_2274_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
if (lean_obj_tag(v___x_2275_) == 0)
{
lean_object* v_a_2276_; 
v_a_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_a_2276_);
lean_dec_ref(v___x_2275_);
if (lean_obj_tag(v_a_2276_) == 1)
{
lean_object* v_val_2277_; lean_object* v_fst_2278_; lean_object* v_snd_2279_; lean_object* v___x_2280_; uint8_t v___x_2281_; uint8_t v___x_2282_; lean_object* v___x_2283_; 
lean_dec(v_x_2262_);
v_val_2277_ = lean_ctor_get(v_a_2276_, 0);
lean_inc(v_val_2277_);
lean_dec_ref(v_a_2276_);
v_fst_2278_ = lean_ctor_get(v_val_2277_, 0);
lean_inc(v_fst_2278_);
v_snd_2279_ = lean_ctor_get(v_val_2277_, 1);
lean_inc(v_snd_2279_);
lean_dec(v_val_2277_);
v___x_2280_ = lean_box(0);
v___x_2281_ = 1;
v___x_2282_ = lean_unbox(v_snd_2279_);
lean_dec(v_snd_2279_);
v___x_2283_ = l_Lean_Meta_substCore(v_mvarId_2263_, v_fst_2278_, v___x_2282_, v___x_2280_, v___x_2281_, v___x_2281_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2292_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2286_ = v___x_2283_;
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2283_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2292_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v_snd_2288_; lean_object* v___x_2290_; 
v_snd_2288_ = lean_ctor_get(v_a_2284_, 1);
lean_inc(v_snd_2288_);
lean_dec(v_a_2284_);
if (v_isShared_2287_ == 0)
{
lean_ctor_set(v___x_2286_, 0, v_snd_2288_);
v___x_2290_ = v___x_2286_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_snd_2288_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
v_a_2293_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2283_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2283_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
lean_dec(v_a_2276_);
v___x_2301_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__1));
v___x_2302_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2303_ = l_Lean_mkFVar(v_x_2262_);
v___x_2304_ = l_Lean_MessageData_ofExpr(v___x_2303_);
v___x_2305_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2305_, 0, v___x_2302_);
lean_ctor_set(v___x_2305_, 1, v___x_2304_);
v___x_2306_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__17, &l_Lean_Meta_substCore___lam__2___closed__17_once, _init_l_Lean_Meta_substCore___lam__2___closed__17);
v___x_2307_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2307_, 0, v___x_2305_);
lean_ctor_set(v___x_2307_, 1, v___x_2306_);
v___x_2308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2308_, 0, v___x_2307_);
v___x_2309_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2301_, v_mvarId_2263_, v___x_2308_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
return v___x_2309_;
}
}
else
{
lean_object* v_a_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec(v_mvarId_2263_);
lean_dec(v_x_2262_);
v_a_2310_ = lean_ctor_get(v___x_2275_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2275_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2275_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_a_2310_);
lean_dec(v___x_2275_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_a_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2347_, lean_object* v_mvarId_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_, lean_object* v___y_2352_, lean_object* v___y_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lean_Meta_substVar___lam__0(v_x_2347_, v_mvarId_2348_, v___y_2349_, v___y_2350_, v___y_2351_, v___y_2352_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2355_, lean_object* v_x_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_, lean_object* v_a_2359_, lean_object* v_a_2360_){
_start:
{
lean_object* v___f_2362_; lean_object* v___x_2363_; 
lean_inc(v_mvarId_2355_);
v___f_2362_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2362_, 0, v_x_2356_);
lean_closure_set(v___f_2362_, 1, v_mvarId_2355_);
v___x_2363_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(v_mvarId_2355_, v___f_2362_, v_a_2357_, v_a_2358_, v_a_2359_, v_a_2360_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2364_, lean_object* v_x_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v_res_2371_; 
v_res_2371_ = l_Lean_Meta_substVar(v_mvarId_2364_, v_x_2365_, v_a_2366_, v_a_2367_, v_a_2368_, v_a_2369_);
return v_res_2371_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2373_; lean_object* v___x_2374_; 
v___x_2373_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2374_ = l_Lean_stringToMessageData(v___x_2373_);
return v___x_2374_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2375_, lean_object* v_snd_2376_, uint8_t v___x_2377_, lean_object* v_fvarSubst_2378_, lean_object* v___y_2379_, lean_object* v___y_2380_, lean_object* v___y_2381_, lean_object* v___y_2382_){
_start:
{
lean_object* v___x_2384_; 
lean_inc_ref(v___y_2379_);
lean_inc(v_fst_2375_);
v___x_2384_ = l_Lean_FVarId_getDecl___redArg(v_fst_2375_, v___y_2379_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2384_) == 0)
{
lean_object* v_a_2385_; lean_object* v___y_2387_; lean_object* v___y_2388_; lean_object* v___y_2389_; lean_object* v___y_2390_; lean_object* v_newType_2399_; uint8_t v_symm_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v___y_2403_; lean_object* v___y_2404_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v_a_2385_ = lean_ctor_get(v___x_2384_, 0);
lean_inc(v_a_2385_);
lean_dec_ref(v___x_2384_);
v___x_2440_ = l_Lean_LocalDecl_type(v_a_2385_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
v___x_2441_ = l_Lean_Meta_matchEq_x3f(v___x_2440_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2441_) == 0)
{
lean_object* v_a_2442_; 
v_a_2442_ = lean_ctor_get(v___x_2441_, 0);
lean_inc(v_a_2442_);
lean_dec_ref(v___x_2441_);
if (lean_obj_tag(v_a_2442_) == 1)
{
lean_object* v_val_2443_; lean_object* v_snd_2444_; lean_object* v_fst_2445_; lean_object* v_snd_2446_; lean_object* v___x_2447_; 
v_val_2443_ = lean_ctor_get(v_a_2442_, 0);
lean_inc(v_val_2443_);
lean_dec_ref(v_a_2442_);
v_snd_2444_ = lean_ctor_get(v_val_2443_, 1);
lean_inc(v_snd_2444_);
lean_dec(v_val_2443_);
v_fst_2445_ = lean_ctor_get(v_snd_2444_, 0);
lean_inc(v_fst_2445_);
v_snd_2446_ = lean_ctor_get(v_snd_2444_, 1);
lean_inc(v_snd_2446_);
lean_dec(v_snd_2444_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v_snd_2446_);
v___x_2447_ = lean_whnf(v_snd_2446_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; uint8_t v___x_2449_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref(v___x_2447_);
v___x_2449_ = l_Lean_Expr_isFVar(v_a_2448_);
if (v___x_2449_ == 0)
{
lean_object* v___x_2450_; 
lean_dec(v_a_2448_);
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
lean_inc(v_fst_2445_);
v___x_2450_ = lean_whnf(v_fst_2445_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2450_) == 0)
{
lean_object* v_a_2451_; uint8_t v___y_2453_; uint8_t v___x_2465_; 
v_a_2451_ = lean_ctor_get(v___x_2450_, 0);
lean_inc(v_a_2451_);
lean_dec_ref(v___x_2450_);
v___x_2465_ = l_Lean_Expr_isFVar(v_a_2451_);
if (v___x_2465_ == 0)
{
lean_dec(v_a_2451_);
lean_dec(v_snd_2446_);
lean_dec(v_fst_2445_);
lean_dec(v_fvarSubst_2378_);
lean_dec(v_fst_2375_);
v___y_2387_ = v___y_2379_;
v___y_2388_ = v___y_2380_;
v___y_2389_ = v___y_2381_;
v___y_2390_ = v___y_2382_;
goto v___jp_2386_;
}
else
{
uint8_t v___x_2466_; 
v___x_2466_ = lean_expr_eqv(v_fst_2445_, v_a_2451_);
lean_dec(v_fst_2445_);
if (v___x_2466_ == 0)
{
v___y_2453_ = v___x_2465_;
goto v___jp_2452_;
}
else
{
v___y_2453_ = v___x_2449_;
goto v___jp_2452_;
}
}
v___jp_2452_:
{
if (v___y_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec(v_a_2451_);
lean_dec(v_snd_2446_);
lean_dec(v_a_2385_);
v___x_2454_ = l_Lean_Meta_substCore(v_snd_2376_, v_fst_2375_, v___y_2453_, v_fvarSubst_2378_, v___x_2377_, v___x_2377_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
return v___x_2454_;
}
else
{
lean_object* v___x_2455_; 
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
v___x_2455_ = l_Lean_Meta_mkEq(v_a_2451_, v_snd_2446_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref(v___x_2455_);
v_newType_2399_ = v_a_2456_;
v_symm_2400_ = v___x_2449_;
v___y_2401_ = v___y_2379_;
v___y_2402_ = v___y_2380_;
v___y_2403_ = v___y_2381_;
v___y_2404_ = v___y_2382_;
goto v___jp_2398_;
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec(v_a_2385_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v_fvarSubst_2378_);
lean_dec(v_snd_2376_);
lean_dec(v_fst_2375_);
v_a_2457_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2455_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2455_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
}
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_snd_2446_);
lean_dec(v_fst_2445_);
lean_dec(v_a_2385_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v_fvarSubst_2378_);
lean_dec(v_snd_2376_);
lean_dec(v_fst_2375_);
v_a_2467_ = lean_ctor_get(v___x_2450_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2450_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2450_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2450_);
v___x_2469_ = lean_box(0);
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
v_resetjp_2468_:
{
lean_object* v___x_2472_; 
if (v_isShared_2470_ == 0)
{
v___x_2472_ = v___x_2469_;
goto v_reusejp_2471_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_a_2467_);
v___x_2472_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2471_;
}
v_reusejp_2471_:
{
return v___x_2472_;
}
}
}
}
else
{
uint8_t v___x_2475_; 
v___x_2475_ = lean_expr_eqv(v_snd_2446_, v_a_2448_);
lean_dec(v_snd_2446_);
if (v___x_2475_ == 0)
{
if (v___x_2449_ == 0)
{
lean_object* v___x_2476_; 
lean_dec(v_a_2448_);
lean_dec(v_fst_2445_);
lean_dec(v_a_2385_);
v___x_2476_ = l_Lean_Meta_substCore(v_snd_2376_, v_fst_2375_, v___x_2377_, v_fvarSubst_2378_, v___x_2377_, v___x_2377_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
return v___x_2476_;
}
else
{
lean_object* v___x_2477_; 
lean_inc(v___y_2382_);
lean_inc_ref(v___y_2381_);
lean_inc(v___y_2380_);
lean_inc_ref(v___y_2379_);
v___x_2477_ = l_Lean_Meta_mkEq(v_fst_2445_, v_a_2448_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref(v___x_2477_);
v_newType_2399_ = v_a_2478_;
v_symm_2400_ = v___x_2377_;
v___y_2401_ = v___y_2379_;
v___y_2402_ = v___y_2380_;
v___y_2403_ = v___y_2381_;
v___y_2404_ = v___y_2382_;
goto v___jp_2398_;
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_a_2385_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v_fvarSubst_2378_);
lean_dec(v_snd_2376_);
lean_dec(v_fst_2375_);
v_a_2479_ = lean_ctor_get(v___x_2477_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2477_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2477_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2477_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
else
{
lean_object* v___x_2487_; 
lean_dec(v_a_2448_);
lean_dec(v_fst_2445_);
lean_dec(v_a_2385_);
v___x_2487_ = l_Lean_Meta_substCore(v_snd_2376_, v_fst_2375_, v___x_2377_, v_fvarSubst_2378_, v___x_2377_, v___x_2377_, v___y_2379_, v___y_2380_, v___y_2381_, v___y_2382_);
return v___x_2487_;
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_snd_2446_);
lean_dec(v_fst_2445_);
lean_dec(v_a_2385_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v_fvarSubst_2378_);
lean_dec(v_snd_2376_);
lean_dec(v_fst_2375_);
v_a_2488_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2447_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2447_);
v___x_2490_ = lean_box(0);
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
v_resetjp_2489_:
{
lean_object* v___x_2493_; 
if (v_isShared_2491_ == 0)
{
v___x_2493_ = v___x_2490_;
goto v_reusejp_2492_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v_a_2488_);
v___x_2493_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2492_;
}
v_reusejp_2492_:
{
return v___x_2493_;
}
}
}
}
else
{
lean_dec(v_a_2442_);
lean_dec(v_fvarSubst_2378_);
lean_dec(v_fst_2375_);
v___y_2387_ = v___y_2379_;
v___y_2388_ = v___y_2380_;
v___y_2389_ = v___y_2381_;
v___y_2390_ = v___y_2382_;
goto v___jp_2386_;
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_a_2385_);
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v_fvarSubst_2378_);
lean_dec(v_snd_2376_);
lean_dec(v_fst_2375_);
v_a_2496_ = lean_ctor_get(v___x_2441_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2441_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2441_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2441_);
v___x_2498_ = lean_box(0);
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
v_resetjp_2497_:
{
lean_object* v___x_2501_; 
if (v_isShared_2499_ == 0)
{
v___x_2501_ = v___x_2498_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_a_2496_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
v___jp_2386_:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2391_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__1));
v___x_2392_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2393_ = l_Lean_LocalDecl_type(v_a_2385_);
lean_dec(v_a_2385_);
v___x_2394_ = l_Lean_indentExpr(v___x_2393_);
v___x_2395_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2392_);
lean_ctor_set(v___x_2395_, 1, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
v___x_2397_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2391_, v_snd_2376_, v___x_2396_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v___x_2397_;
}
v___jp_2398_:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = l_Lean_LocalDecl_userName(v_a_2385_);
lean_dec(v_a_2385_);
lean_inc(v_fst_2375_);
v___x_2406_ = l_Lean_mkFVar(v_fst_2375_);
lean_inc(v___y_2404_);
lean_inc_ref(v___y_2403_);
lean_inc(v___y_2402_);
lean_inc_ref(v___y_2401_);
v___x_2407_ = l_Lean_MVarId_assert(v_snd_2376_, v___x_2405_, v_newType_2399_, v___x_2406_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v___x_2409_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref(v___x_2407_);
lean_inc(v___y_2404_);
lean_inc_ref(v___y_2403_);
lean_inc(v___y_2402_);
lean_inc_ref(v___y_2401_);
v___x_2409_ = l_Lean_Meta_intro1Core(v_a_2408_, v___x_2377_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v_fst_2411_; lean_object* v_snd_2412_; lean_object* v___x_2413_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref(v___x_2409_);
v_fst_2411_ = lean_ctor_get(v_a_2410_, 0);
lean_inc(v_fst_2411_);
v_snd_2412_ = lean_ctor_get(v_a_2410_, 1);
lean_inc(v_snd_2412_);
lean_dec(v_a_2410_);
lean_inc(v___y_2404_);
lean_inc_ref(v___y_2403_);
lean_inc(v___y_2402_);
lean_inc_ref(v___y_2401_);
v___x_2413_ = l_Lean_MVarId_clear(v_snd_2412_, v_fst_2375_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2415_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref(v___x_2413_);
v___x_2415_ = l_Lean_Meta_substCore(v_a_2414_, v_fst_2411_, v_symm_2400_, v_fvarSubst_2378_, v___x_2377_, v___x_2377_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
return v___x_2415_;
}
else
{
lean_object* v_a_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2423_; 
lean_dec(v_fst_2411_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_fvarSubst_2378_);
v_a_2416_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2423_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2423_ == 0)
{
v___x_2418_ = v___x_2413_;
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_a_2416_);
lean_dec(v___x_2413_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2423_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2421_; 
if (v_isShared_2419_ == 0)
{
v___x_2421_ = v___x_2418_;
goto v_reusejp_2420_;
}
else
{
lean_object* v_reuseFailAlloc_2422_; 
v_reuseFailAlloc_2422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2422_, 0, v_a_2416_);
v___x_2421_ = v_reuseFailAlloc_2422_;
goto v_reusejp_2420_;
}
v_reusejp_2420_:
{
return v___x_2421_;
}
}
}
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_fvarSubst_2378_);
lean_dec(v_fst_2375_);
v_a_2424_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2409_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2409_);
v___x_2426_ = lean_box(0);
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
v_resetjp_2425_:
{
lean_object* v___x_2429_; 
if (v_isShared_2427_ == 0)
{
v___x_2429_ = v___x_2426_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2430_; 
v_reuseFailAlloc_2430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2430_, 0, v_a_2424_);
v___x_2429_ = v_reuseFailAlloc_2430_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
return v___x_2429_;
}
}
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_fvarSubst_2378_);
lean_dec(v_fst_2375_);
v_a_2432_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2407_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2407_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v___y_2382_);
lean_dec_ref(v___y_2381_);
lean_dec(v___y_2380_);
lean_dec_ref(v___y_2379_);
lean_dec(v_fvarSubst_2378_);
lean_dec(v_snd_2376_);
lean_dec(v_fst_2375_);
v_a_2504_ = lean_ctor_get(v___x_2384_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2384_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2384_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2384_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2509_; 
if (v_isShared_2507_ == 0)
{
v___x_2509_ = v___x_2506_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2510_; 
v_reuseFailAlloc_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2510_, 0, v_a_2504_);
v___x_2509_ = v_reuseFailAlloc_2510_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
return v___x_2509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2512_, lean_object* v_snd_2513_, lean_object* v___x_2514_, lean_object* v_fvarSubst_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
uint8_t v___x_1941__boxed_2521_; lean_object* v_res_2522_; 
v___x_1941__boxed_2521_ = lean_unbox(v___x_2514_);
v_res_2522_ = l_Lean_Meta_substEq___lam__0(v_fst_2512_, v_snd_2513_, v___x_1941__boxed_2521_, v_fvarSubst_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2523_, lean_object* v_hFVarId_2524_, lean_object* v_fvarSubst_2525_, lean_object* v_a_2526_, lean_object* v_a_2527_, lean_object* v_a_2528_, lean_object* v_a_2529_){
_start:
{
uint8_t v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = 1;
lean_inc(v_a_2529_);
lean_inc_ref(v_a_2528_);
lean_inc(v_a_2527_);
lean_inc_ref(v_a_2526_);
v___x_2532_ = l_Lean_Meta_heqToEq(v_mvarId_2523_, v_hFVarId_2524_, v___x_2531_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v_fst_2534_; lean_object* v_snd_2535_; lean_object* v___x_2536_; lean_object* v___f_2537_; lean_object* v___x_2538_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref(v___x_2532_);
v_fst_2534_ = lean_ctor_get(v_a_2533_, 0);
lean_inc(v_fst_2534_);
v_snd_2535_ = lean_ctor_get(v_a_2533_, 1);
lean_inc(v_snd_2535_);
lean_dec(v_a_2533_);
v___x_2536_ = lean_box(v___x_2531_);
lean_inc(v_snd_2535_);
v___f_2537_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2537_, 0, v_fst_2534_);
lean_closure_set(v___f_2537_, 1, v_snd_2535_);
lean_closure_set(v___f_2537_, 2, v___x_2536_);
lean_closure_set(v___f_2537_, 3, v_fvarSubst_2525_);
v___x_2538_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(v_snd_2535_, v___f_2537_, v_a_2526_, v_a_2527_, v_a_2528_, v_a_2529_);
return v___x_2538_;
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_dec(v_a_2529_);
lean_dec_ref(v_a_2528_);
lean_dec(v_a_2527_);
lean_dec_ref(v_a_2526_);
lean_dec(v_fvarSubst_2525_);
v_a_2539_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2532_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2532_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2547_, lean_object* v_hFVarId_2548_, lean_object* v_fvarSubst_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_){
_start:
{
lean_object* v_res_2555_; 
v_res_2555_ = l_Lean_Meta_substEq(v_mvarId_2547_, v_hFVarId_2548_, v_fvarSubst_2549_, v_a_2550_, v_a_2551_, v_a_2552_, v_a_2553_);
return v_res_2555_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2556_, lean_object* v_mvarId_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_, lean_object* v___y_2561_){
_start:
{
lean_object* v___x_2563_; 
lean_inc_ref(v___y_2558_);
lean_inc(v_h_2556_);
v___x_2563_ = l_Lean_FVarId_getType___redArg(v_h_2556_, v___y_2558_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; lean_object* v___x_2565_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref(v___x_2563_);
lean_inc(v___y_2561_);
lean_inc_ref(v___y_2560_);
lean_inc(v___y_2559_);
lean_inc_ref(v___y_2558_);
lean_inc(v_a_2564_);
v___x_2565_ = l_Lean_Meta_matchEq_x3f(v_a_2564_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2565_) == 0)
{
lean_object* v_a_2566_; 
v_a_2566_ = lean_ctor_get(v___x_2565_, 0);
lean_inc(v_a_2566_);
lean_dec_ref(v___x_2565_);
if (lean_obj_tag(v_a_2566_) == 0)
{
lean_object* v___x_2567_; 
lean_inc(v___y_2561_);
lean_inc_ref(v___y_2560_);
lean_inc(v___y_2559_);
lean_inc_ref(v___y_2558_);
v___x_2567_ = l_Lean_Meta_matchHEq_x3f(v_a_2564_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref(v___x_2567_);
if (lean_obj_tag(v_a_2568_) == 0)
{
lean_object* v___x_2569_; 
v___x_2569_ = l_Lean_Meta_substVar(v_mvarId_2557_, v_h_2556_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
return v___x_2569_;
}
else
{
uint8_t v___x_2570_; lean_object* v___x_2571_; 
lean_dec_ref(v_a_2568_);
v___x_2570_ = 1;
lean_inc(v___y_2561_);
lean_inc_ref(v___y_2560_);
lean_inc(v___y_2559_);
lean_inc_ref(v___y_2558_);
lean_inc(v_h_2556_);
lean_inc(v_mvarId_2557_);
v___x_2571_ = l_Lean_Meta_heqToEq(v_mvarId_2557_, v_h_2556_, v___x_2570_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v_fst_2573_; lean_object* v_snd_2574_; uint8_t v___x_2575_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref(v___x_2571_);
v_fst_2573_ = lean_ctor_get(v_a_2572_, 0);
lean_inc(v_fst_2573_);
v_snd_2574_ = lean_ctor_get(v_a_2572_, 1);
lean_inc(v_snd_2574_);
lean_dec(v_a_2572_);
v___x_2575_ = l_Lean_instBEqMVarId_beq(v_mvarId_2557_, v_snd_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; 
lean_dec(v_mvarId_2557_);
lean_dec(v_h_2556_);
v___x_2576_ = l_Lean_Meta_subst(v_snd_2574_, v_fst_2573_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
return v___x_2576_;
}
else
{
lean_object* v___x_2577_; 
lean_dec(v_snd_2574_);
lean_dec(v_fst_2573_);
v___x_2577_ = l_Lean_Meta_substVar(v_mvarId_2557_, v_h_2556_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
return v___x_2577_;
}
}
else
{
lean_object* v_a_2578_; lean_object* v___x_2580_; uint8_t v_isShared_2581_; uint8_t v_isSharedCheck_2585_; 
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v_mvarId_2557_);
lean_dec(v_h_2556_);
v_a_2578_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2585_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2585_ == 0)
{
v___x_2580_ = v___x_2571_;
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
else
{
lean_inc(v_a_2578_);
lean_dec(v___x_2571_);
v___x_2580_ = lean_box(0);
v_isShared_2581_ = v_isSharedCheck_2585_;
goto v_resetjp_2579_;
}
v_resetjp_2579_:
{
lean_object* v___x_2583_; 
if (v_isShared_2581_ == 0)
{
v___x_2583_ = v___x_2580_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2584_; 
v_reuseFailAlloc_2584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
v___x_2583_ = v_reuseFailAlloc_2584_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
return v___x_2583_;
}
}
}
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v_mvarId_2557_);
lean_dec(v_h_2556_);
v_a_2586_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2567_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2567_);
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
else
{
lean_object* v___x_2594_; lean_object* v___x_2595_; 
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2564_);
v___x_2594_ = lean_box(0);
v___x_2595_ = l_Lean_Meta_substEq(v_mvarId_2557_, v_h_2556_, v___x_2594_, v___y_2558_, v___y_2559_, v___y_2560_, v___y_2561_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2604_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2598_ = v___x_2595_;
v_isShared_2599_ = v_isSharedCheck_2604_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2595_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2604_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v_snd_2600_; lean_object* v___x_2602_; 
v_snd_2600_ = lean_ctor_get(v_a_2596_, 1);
lean_inc(v_snd_2600_);
lean_dec(v_a_2596_);
if (v_isShared_2599_ == 0)
{
lean_ctor_set(v___x_2598_, 0, v_snd_2600_);
v___x_2602_ = v___x_2598_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_snd_2600_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
v_a_2605_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2595_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2595_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2610_; 
if (v_isShared_2608_ == 0)
{
v___x_2610_ = v___x_2607_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_a_2605_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
lean_dec(v_a_2564_);
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v_mvarId_2557_);
lean_dec(v_h_2556_);
v_a_2613_ = lean_ctor_get(v___x_2565_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2565_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2565_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2565_);
v___x_2615_ = lean_box(0);
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
v_resetjp_2614_:
{
lean_object* v___x_2618_; 
if (v_isShared_2616_ == 0)
{
v___x_2618_ = v___x_2615_;
goto v_reusejp_2617_;
}
else
{
lean_object* v_reuseFailAlloc_2619_; 
v_reuseFailAlloc_2619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2619_, 0, v_a_2613_);
v___x_2618_ = v_reuseFailAlloc_2619_;
goto v_reusejp_2617_;
}
v_reusejp_2617_:
{
return v___x_2618_;
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v___y_2561_);
lean_dec_ref(v___y_2560_);
lean_dec(v___y_2559_);
lean_dec_ref(v___y_2558_);
lean_dec(v_mvarId_2557_);
lean_dec(v_h_2556_);
v_a_2621_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2563_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2563_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2629_, lean_object* v_mvarId_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_, lean_object* v___y_2633_, lean_object* v___y_2634_, lean_object* v___y_2635_){
_start:
{
lean_object* v_res_2636_; 
v_res_2636_ = l_Lean_Meta_subst___lam__0(v_h_2629_, v_mvarId_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_);
return v_res_2636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2637_, lean_object* v_h_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v___f_2644_; lean_object* v___x_2645_; 
lean_inc(v_mvarId_2637_);
v___f_2644_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2644_, 0, v_h_2638_);
lean_closure_set(v___f_2644_, 1, v_mvarId_2637_);
v___x_2645_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(v_mvarId_2637_, v___f_2644_, v_a_2639_, v_a_2640_, v_a_2641_, v_a_2642_);
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2646_, lean_object* v_h_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v_res_2653_; 
v_res_2653_ = l_Lean_Meta_subst(v_mvarId_2646_, v_h_2647_, v_a_2648_, v_a_2649_, v_a_2650_, v_a_2651_);
return v_res_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_){
_start:
{
lean_object* v___x_2660_; 
v___x_2660_ = l_Lean_Meta_saveState___redArg(v___y_2656_, v___y_2658_);
if (lean_obj_tag(v___x_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2662_; 
v_a_2661_ = lean_ctor_get(v___x_2660_, 0);
lean_inc(v_a_2661_);
lean_dec_ref(v___x_2660_);
lean_inc(v___y_2658_);
lean_inc(v___y_2656_);
v___x_2662_ = lean_apply_5(v_x_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_, lean_box(0));
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_dec(v_a_2661_);
lean_dec(v___y_2658_);
lean_dec(v___y_2656_);
return v___x_2662_;
}
else
{
lean_object* v_a_2663_; uint8_t v___y_2665_; uint8_t v___x_2683_; 
v_a_2663_ = lean_ctor_get(v___x_2662_, 0);
lean_inc(v_a_2663_);
v___x_2683_ = l_Lean_Exception_isInterrupt(v_a_2663_);
if (v___x_2683_ == 0)
{
uint8_t v___x_2684_; 
lean_inc(v_a_2663_);
v___x_2684_ = l_Lean_Exception_isRuntime(v_a_2663_);
v___y_2665_ = v___x_2684_;
goto v___jp_2664_;
}
else
{
v___y_2665_ = v___x_2683_;
goto v___jp_2664_;
}
v___jp_2664_:
{
if (v___y_2665_ == 0)
{
lean_object* v___x_2666_; 
lean_dec_ref(v___x_2662_);
v___x_2666_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2661_, v___y_2656_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec(v___y_2656_);
lean_dec(v_a_2661_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2673_; 
v_isSharedCheck_2673_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; 
v_unused_2674_ = lean_ctor_get(v___x_2666_, 0);
lean_dec(v_unused_2674_);
v___x_2668_ = v___x_2666_;
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
else
{
lean_dec(v___x_2666_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2673_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2671_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set_tag(v___x_2668_, 1);
lean_ctor_set(v___x_2668_, 0, v_a_2663_);
v___x_2671_ = v___x_2668_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2663_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
else
{
lean_object* v_a_2675_; lean_object* v___x_2677_; uint8_t v_isShared_2678_; uint8_t v_isSharedCheck_2682_; 
lean_dec(v_a_2663_);
v_a_2675_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2682_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2677_ = v___x_2666_;
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
else
{
lean_inc(v_a_2675_);
lean_dec(v___x_2666_);
v___x_2677_ = lean_box(0);
v_isShared_2678_ = v_isSharedCheck_2682_;
goto v_resetjp_2676_;
}
v_resetjp_2676_:
{
lean_object* v___x_2680_; 
if (v_isShared_2678_ == 0)
{
v___x_2680_ = v___x_2677_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_a_2675_);
v___x_2680_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
return v___x_2680_;
}
}
}
}
else
{
lean_dec(v_a_2663_);
lean_dec(v_a_2661_);
lean_dec(v___y_2658_);
lean_dec(v___y_2656_);
return v___x_2662_;
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec_ref(v_x_2654_);
v_a_2685_ = lean_ctor_get(v___x_2660_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2660_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2660_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2660_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2685_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_, lean_object* v___y_2696_, lean_object* v___y_2697_, lean_object* v___y_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2693_, v___y_2694_, v___y_2695_, v___y_2696_, v___y_2697_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2700_, lean_object* v_x_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
return v___x_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2708_, lean_object* v_x_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_){
_start:
{
lean_object* v_res_2715_; 
v_res_2715_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2708_, v_x_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
return v_res_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_ref_2722_; lean_object* v___x_2723_; lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2732_; 
v_ref_2722_ = lean_ctor_get(v___y_2719_, 5);
v___x_2723_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__4_spec__4(v_msg_2716_, v___y_2717_, v___y_2718_, v___y_2719_, v___y_2720_);
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2732_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2732_ == 0)
{
v___x_2726_ = v___x_2723_;
v_isShared_2727_ = v_isSharedCheck_2732_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2732_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2728_; lean_object* v___x_2730_; 
lean_inc(v_ref_2722_);
v___x_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2728_, 0, v_ref_2722_);
lean_ctor_set(v___x_2728_, 1, v_a_2724_);
if (v_isShared_2727_ == 0)
{
lean_ctor_set_tag(v___x_2726_, 1);
lean_ctor_set(v___x_2726_, 0, v___x_2728_);
v___x_2730_ = v___x_2726_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2731_; 
v_reuseFailAlloc_2731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2731_, 0, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2731_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
return v___x_2730_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_res_2739_; 
v_res_2739_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
lean_dec(v___y_2737_);
lean_dec_ref(v___y_2736_);
lean_dec(v___y_2735_);
lean_dec_ref(v___y_2734_);
return v_res_2739_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2741_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2742_ = l_Lean_stringToMessageData(v___x_2741_);
return v___x_2742_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2745_ = l_Lean_stringToMessageData(v___x_2744_);
return v___x_2745_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2748_ = l_Lean_stringToMessageData(v___x_2747_);
return v___x_2748_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2751_ = l_Lean_stringToMessageData(v___x_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2768_ = l_Lean_stringToMessageData(v___x_2767_);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2777_, uint8_t v_substLHS_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_){
_start:
{
lean_object* v___x_2784_; 
lean_inc(v___y_2782_);
lean_inc_ref(v___y_2781_);
lean_inc(v___y_2780_);
lean_inc_ref(v___y_2779_);
lean_inc(v_mvarId_2777_);
v___x_2784_ = l_Lean_MVarId_getType_x27(v_mvarId_2777_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2784_) == 0)
{
lean_object* v_a_2785_; 
v_a_2785_ = lean_ctor_get(v___x_2784_, 0);
lean_inc(v_a_2785_);
lean_dec_ref(v___x_2784_);
if (lean_obj_tag(v_a_2785_) == 7)
{
lean_object* v_binderType_2789_; lean_object* v_body_2790_; uint8_t v___x_2791_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v_fst_2926_; lean_object* v_fst_2927_; lean_object* v_fst_2928_; lean_object* v_snd_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; 
v_binderType_2789_ = lean_ctor_get(v_a_2785_, 1);
lean_inc_ref(v_binderType_2789_);
v_body_2790_ = lean_ctor_get(v_a_2785_, 2);
lean_inc_ref(v_body_2790_);
lean_dec_ref(v_a_2785_);
v___x_2791_ = l_Lean_Expr_hasLooseBVars(v_body_2790_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2945_; 
v___x_2945_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2789_, v___y_2780_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___x_2962_; uint8_t v___x_2963_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref(v___x_2945_);
v___x_2962_ = l_Lean_Expr_cleanupAnnotations(v_a_2946_);
v___x_2963_ = l_Lean_Expr_isApp(v___x_2962_);
if (v___x_2963_ == 0)
{
lean_dec_ref(v___x_2962_);
lean_dec_ref(v_body_2790_);
lean_dec(v_mvarId_2777_);
v___y_2948_ = v___y_2779_;
v___y_2949_ = v___y_2780_;
v___y_2950_ = v___y_2781_;
v___y_2951_ = v___y_2782_;
goto v___jp_2947_;
}
else
{
lean_object* v_arg_2964_; lean_object* v___x_2965_; uint8_t v___x_2966_; 
v_arg_2964_ = lean_ctor_get(v___x_2962_, 1);
lean_inc_ref(v_arg_2964_);
v___x_2965_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2962_);
v___x_2966_ = l_Lean_Expr_isApp(v___x_2965_);
if (v___x_2966_ == 0)
{
lean_dec_ref(v___x_2965_);
lean_dec_ref(v_arg_2964_);
lean_dec_ref(v_body_2790_);
lean_dec(v_mvarId_2777_);
v___y_2948_ = v___y_2779_;
v___y_2949_ = v___y_2780_;
v___y_2950_ = v___y_2781_;
v___y_2951_ = v___y_2782_;
goto v___jp_2947_;
}
else
{
lean_object* v_arg_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v_arg_2967_ = lean_ctor_get(v___x_2965_, 1);
lean_inc_ref(v_arg_2967_);
v___x_2968_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2965_);
v___x_2969_ = l_Lean_Expr_isApp(v___x_2968_);
if (v___x_2969_ == 0)
{
lean_dec_ref(v___x_2968_);
lean_dec_ref(v_arg_2967_);
lean_dec_ref(v_arg_2964_);
lean_dec_ref(v_body_2790_);
lean_dec(v_mvarId_2777_);
v___y_2948_ = v___y_2779_;
v___y_2949_ = v___y_2780_;
v___y_2950_ = v___y_2781_;
v___y_2951_ = v___y_2782_;
goto v___jp_2947_;
}
else
{
lean_object* v_arg_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v_arg_2970_ = lean_ctor_get(v___x_2968_, 1);
lean_inc_ref(v_arg_2970_);
v___x_2971_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2968_);
v___x_2972_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_2973_ = l_Lean_Expr_isConstOf(v___x_2971_, v___x_2972_);
if (v___x_2973_ == 0)
{
uint8_t v___x_2974_; 
v___x_2974_ = l_Lean_Expr_isApp(v___x_2971_);
if (v___x_2974_ == 0)
{
lean_dec_ref(v___x_2971_);
lean_dec_ref(v_arg_2970_);
lean_dec_ref(v_arg_2967_);
lean_dec_ref(v_arg_2964_);
lean_dec_ref(v_body_2790_);
lean_dec(v_mvarId_2777_);
v___y_2948_ = v___y_2779_;
v___y_2949_ = v___y_2780_;
v___y_2950_ = v___y_2781_;
v___y_2951_ = v___y_2782_;
goto v___jp_2947_;
}
else
{
lean_object* v_arg_2975_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v_arg_2975_ = lean_ctor_get(v___x_2971_, 1);
lean_inc_ref(v_arg_2975_);
v___x_2983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2971_);
v___x_2984_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_2985_ = l_Lean_Expr_isConstOf(v___x_2983_, v___x_2984_);
lean_dec_ref(v___x_2983_);
if (v___x_2985_ == 0)
{
lean_dec_ref(v_arg_2975_);
lean_dec_ref(v_arg_2970_);
lean_dec_ref(v_arg_2967_);
lean_dec_ref(v_arg_2964_);
lean_dec_ref(v_body_2790_);
lean_dec(v_mvarId_2777_);
v___y_2948_ = v___y_2779_;
v___y_2949_ = v___y_2780_;
v___y_2950_ = v___y_2781_;
v___y_2951_ = v___y_2782_;
goto v___jp_2947_;
}
else
{
lean_object* v___x_2986_; 
lean_inc(v___y_2782_);
lean_inc_ref(v___y_2781_);
lean_inc(v___y_2780_);
lean_inc_ref(v___y_2779_);
lean_inc_ref(v_arg_2975_);
v___x_2986_ = l_Lean_Meta_isExprDefEq(v_arg_2975_, v_arg_2967_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; uint8_t v___x_2988_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref(v___x_2986_);
v___x_2988_ = lean_unbox(v_a_2987_);
lean_dec(v_a_2987_);
if (v___x_2988_ == 0)
{
lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v_arg_2975_);
lean_dec_ref(v_arg_2970_);
lean_dec_ref(v_arg_2964_);
lean_dec_ref(v_body_2790_);
lean_dec(v_mvarId_2777_);
v___x_2989_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_2990_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2989_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2990_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2990_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
else
{
v___y_2977_ = v___y_2779_;
v___y_2978_ = v___y_2780_;
v___y_2979_ = v___y_2781_;
v___y_2980_ = v___y_2782_;
goto v___jp_2976_;
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v_arg_2975_);
lean_dec_ref(v_arg_2970_);
lean_dec_ref(v_arg_2964_);
lean_dec_ref(v_body_2790_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v_mvarId_2777_);
v_a_2999_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2986_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2986_);
v___x_3001_ = lean_box(0);
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
v_resetjp_3000_:
{
lean_object* v___x_3004_; 
if (v_isShared_3002_ == 0)
{
v___x_3004_ = v___x_3001_;
goto v_reusejp_3003_;
}
else
{
lean_object* v_reuseFailAlloc_3005_; 
v_reuseFailAlloc_3005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3005_, 0, v_a_2999_);
v___x_3004_ = v_reuseFailAlloc_3005_;
goto v_reusejp_3003_;
}
v_reusejp_3003_:
{
return v___x_3004_;
}
}
}
}
v___jp_2976_:
{
if (v_substLHS_2778_ == 0)
{
lean_object* v___x_2981_; 
v___x_2981_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2926_ = v_arg_2975_;
v_fst_2927_ = v_arg_2970_;
v_fst_2928_ = v_arg_2964_;
v_snd_2929_ = v___x_2981_;
v___y_2930_ = v___y_2977_;
v___y_2931_ = v___y_2978_;
v___y_2932_ = v___y_2979_;
v___y_2933_ = v___y_2980_;
goto v___jp_2925_;
}
else
{
lean_object* v___x_2982_; 
v___x_2982_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2926_ = v_arg_2975_;
v_fst_2927_ = v_arg_2964_;
v_fst_2928_ = v_arg_2970_;
v_snd_2929_ = v___x_2982_;
v___y_2930_ = v___y_2977_;
v___y_2931_ = v___y_2978_;
v___y_2932_ = v___y_2979_;
v___y_2933_ = v___y_2980_;
goto v___jp_2925_;
}
}
}
}
else
{
lean_dec_ref(v___x_2971_);
if (v_substLHS_2778_ == 0)
{
lean_object* v___x_3007_; 
v___x_3007_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2926_ = v_arg_2970_;
v_fst_2927_ = v_arg_2967_;
v_fst_2928_ = v_arg_2964_;
v_snd_2929_ = v___x_3007_;
v___y_2930_ = v___y_2779_;
v___y_2931_ = v___y_2780_;
v___y_2932_ = v___y_2781_;
v___y_2933_ = v___y_2782_;
goto v___jp_2925_;
}
else
{
lean_object* v___x_3008_; 
v___x_3008_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2926_ = v_arg_2970_;
v_fst_2927_ = v_arg_2964_;
v_fst_2928_ = v_arg_2967_;
v_snd_2929_ = v___x_3008_;
v___y_2930_ = v___y_2779_;
v___y_2931_ = v___y_2780_;
v___y_2932_ = v___y_2781_;
v___y_2933_ = v___y_2782_;
goto v___jp_2925_;
}
}
}
}
}
v___jp_2947_:
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
v___x_2952_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_2953_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2952_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
lean_dec(v___y_2951_);
lean_dec_ref(v___y_2950_);
lean_dec(v___y_2949_);
lean_dec_ref(v___y_2948_);
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2956_ = v___x_2953_;
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
else
{
lean_inc(v_a_2954_);
lean_dec(v___x_2953_);
v___x_2956_ = lean_box(0);
v_isShared_2957_ = v_isSharedCheck_2961_;
goto v_resetjp_2955_;
}
v_resetjp_2955_:
{
lean_object* v___x_2959_; 
if (v_isShared_2957_ == 0)
{
v___x_2959_ = v___x_2956_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
v___x_2959_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
return v___x_2959_;
}
}
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v_body_2790_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v_mvarId_2777_);
v_a_3009_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2945_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2945_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3014_; 
if (v_isShared_3012_ == 0)
{
v___x_3014_ = v___x_3011_;
goto v_reusejp_3013_;
}
else
{
lean_object* v_reuseFailAlloc_3015_; 
v_reuseFailAlloc_3015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3015_, 0, v_a_3009_);
v___x_3014_ = v_reuseFailAlloc_3015_;
goto v_reusejp_3013_;
}
v_reusejp_3013_:
{
return v___x_3014_;
}
}
}
}
else
{
lean_dec_ref(v_body_2790_);
lean_dec_ref(v_binderType_2789_);
lean_dec(v_mvarId_2777_);
goto v___jp_2786_;
}
v___jp_2792_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; uint8_t v___x_2806_; uint8_t v___x_2807_; lean_object* v___x_2808_; 
v___x_2804_ = lean_mk_empty_array_with_capacity(v___y_2795_);
lean_inc_ref(v___x_2804_);
v___x_2805_ = lean_array_push(v___x_2804_, v___y_2798_);
v___x_2806_ = 1;
v___x_2807_ = 1;
v___x_2808_ = l_Lean_Meta_mkLambdaFVars(v___x_2805_, v_body_2790_, v___x_2791_, v___x_2806_, v___x_2791_, v___x_2806_, v___x_2807_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec_ref(v___x_2805_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref(v___x_2808_);
lean_inc(v___y_2797_);
v___x_2810_ = l_Lean_MVarId_getTag(v___y_2797_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref(v___x_2810_);
lean_inc_ref(v___y_2793_);
v___x_2812_ = lean_array_push(v___x_2804_, v___y_2793_);
lean_inc(v_a_2809_);
v___x_2813_ = l_Lean_Expr_beta(v_a_2809_, v___x_2812_);
lean_inc_ref(v___y_2800_);
lean_inc_ref(v___x_2813_);
v___x_2814_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2813_, v_a_2811_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref(v___x_2814_);
lean_inc(v___y_2803_);
lean_inc_ref(v___y_2802_);
lean_inc(v___y_2801_);
lean_inc_ref(v___y_2800_);
v___x_2816_ = l_Lean_Meta_getLevel(v___x_2813_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref(v___x_2816_);
lean_inc(v___y_2801_);
lean_inc_ref(v___y_2796_);
v___x_2818_ = l_Lean_Meta_getLevel(v___y_2796_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; uint8_t v_isShared_2828_; uint8_t v_isSharedCheck_2836_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2818_);
v___x_2820_ = lean_box(0);
v___x_2821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2821_, 0, v_a_2819_);
lean_ctor_set(v___x_2821_, 1, v___x_2820_);
v___x_2822_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2822_, 0, v_a_2817_);
lean_ctor_set(v___x_2822_, 1, v___x_2821_);
v___x_2823_ = l_Lean_mkConst(v___y_2799_, v___x_2822_);
lean_inc(v_a_2815_);
lean_inc_ref(v___y_2793_);
v___x_2824_ = l_Lean_mkApp4(v___x_2823_, v___y_2796_, v___y_2793_, v_a_2809_, v_a_2815_);
v___x_2825_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6___redArg(v___y_2797_, v___x_2824_, v___y_2801_);
lean_dec(v___y_2801_);
v_isSharedCheck_2836_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2836_ == 0)
{
lean_object* v_unused_2837_; 
v_unused_2837_ = lean_ctor_get(v___x_2825_, 0);
lean_dec(v_unused_2837_);
v___x_2827_ = v___x_2825_;
v_isShared_2828_ = v_isSharedCheck_2836_;
goto v_resetjp_2826_;
}
else
{
lean_dec(v___x_2825_);
v___x_2827_ = lean_box(0);
v_isShared_2828_ = v_isSharedCheck_2836_;
goto v_resetjp_2826_;
}
v_resetjp_2826_:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2834_; 
v___x_2829_ = l_Lean_Meta_FVarSubst_empty;
v___x_2830_ = l_Lean_Meta_FVarSubst_insert(v___x_2829_, v___y_2794_, v___y_2793_);
v___x_2831_ = l_Lean_Expr_mvarId_x21(v_a_2815_);
lean_dec(v_a_2815_);
v___x_2832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2832_, 0, v___x_2830_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
if (v_isShared_2828_ == 0)
{
lean_ctor_set(v___x_2827_, 0, v___x_2832_);
v___x_2834_ = v___x_2827_;
goto v_reusejp_2833_;
}
else
{
lean_object* v_reuseFailAlloc_2835_; 
v_reuseFailAlloc_2835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2835_, 0, v___x_2832_);
v___x_2834_ = v_reuseFailAlloc_2835_;
goto v_reusejp_2833_;
}
v_reusejp_2833_:
{
return v___x_2834_;
}
}
}
else
{
lean_object* v_a_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2845_; 
lean_dec(v_a_2817_);
lean_dec(v_a_2815_);
lean_dec(v_a_2809_);
lean_dec(v___y_2801_);
lean_dec(v___y_2799_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
v_a_2838_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2845_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2845_ == 0)
{
v___x_2840_ = v___x_2818_;
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_a_2838_);
lean_dec(v___x_2818_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2845_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2843_; 
if (v_isShared_2841_ == 0)
{
v___x_2843_ = v___x_2840_;
goto v_reusejp_2842_;
}
else
{
lean_object* v_reuseFailAlloc_2844_; 
v_reuseFailAlloc_2844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_a_2838_);
v___x_2843_ = v_reuseFailAlloc_2844_;
goto v_reusejp_2842_;
}
v_reusejp_2842_:
{
return v___x_2843_;
}
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v_a_2815_);
lean_dec(v_a_2809_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
v_a_2846_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2816_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2816_);
v___x_2848_ = lean_box(0);
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
v_resetjp_2847_:
{
lean_object* v___x_2851_; 
if (v_isShared_2849_ == 0)
{
v___x_2851_ = v___x_2848_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
}
else
{
lean_object* v_a_2854_; lean_object* v___x_2856_; uint8_t v_isShared_2857_; uint8_t v_isSharedCheck_2861_; 
lean_dec_ref(v___x_2813_);
lean_dec(v_a_2809_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
v_a_2854_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2814_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2814_);
v___x_2856_ = lean_box(0);
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
v_resetjp_2855_:
{
lean_object* v___x_2859_; 
if (v_isShared_2857_ == 0)
{
v___x_2859_ = v___x_2856_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_a_2854_);
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
else
{
lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2869_; 
lean_dec(v_a_2809_);
lean_dec_ref(v___x_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
v_a_2862_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2810_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2810_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2867_; 
if (v_isShared_2865_ == 0)
{
v___x_2867_ = v___x_2864_;
goto v_reusejp_2866_;
}
else
{
lean_object* v_reuseFailAlloc_2868_; 
v_reuseFailAlloc_2868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2868_, 0, v_a_2862_);
v___x_2867_ = v_reuseFailAlloc_2868_;
goto v_reusejp_2866_;
}
v_reusejp_2866_:
{
return v___x_2867_;
}
}
}
}
else
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2877_; 
lean_dec_ref(v___x_2804_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v___y_2799_);
lean_dec(v___y_2797_);
lean_dec_ref(v___y_2796_);
lean_dec(v___y_2794_);
lean_dec_ref(v___y_2793_);
v_a_2870_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2808_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2808_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___x_2875_; 
if (v_isShared_2873_ == 0)
{
v___x_2875_ = v___x_2872_;
goto v_reusejp_2874_;
}
else
{
lean_object* v_reuseFailAlloc_2876_; 
v_reuseFailAlloc_2876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2876_, 0, v_a_2870_);
v___x_2875_ = v_reuseFailAlloc_2876_;
goto v_reusejp_2874_;
}
v_reusejp_2874_:
{
return v___x_2875_;
}
}
}
}
v___jp_2878_:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2887_ = l_Lean_Expr_fvarId_x21(v___y_2881_);
v___x_2888_ = lean_unsigned_to_nat(1u);
v___x_2889_ = lean_mk_empty_array_with_capacity(v___x_2888_);
lean_inc(v___x_2887_);
v___x_2890_ = lean_array_push(v___x_2889_, v___x_2887_);
lean_inc(v___y_2886_);
lean_inc_ref(v___y_2885_);
lean_inc(v___y_2884_);
lean_inc_ref(v___y_2883_);
v___x_2891_ = l_Lean_MVarId_revert(v_mvarId_2777_, v___x_2890_, v___x_2791_, v___x_2791_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
if (lean_obj_tag(v___x_2891_) == 0)
{
lean_object* v_a_2892_; lean_object* v_fst_2893_; lean_object* v_snd_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2916_; 
v_a_2892_ = lean_ctor_get(v___x_2891_, 0);
lean_inc(v_a_2892_);
lean_dec_ref(v___x_2891_);
v_fst_2893_ = lean_ctor_get(v_a_2892_, 0);
v_snd_2894_ = lean_ctor_get(v_a_2892_, 1);
v_isSharedCheck_2916_ = !lean_is_exclusive(v_a_2892_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2896_ = v_a_2892_;
v_isShared_2897_ = v_isSharedCheck_2916_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_snd_2894_);
lean_inc(v_fst_2893_);
lean_dec(v_a_2892_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2916_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2898_; uint8_t v___x_2899_; 
v___x_2898_ = lean_array_get_size(v_fst_2893_);
lean_dec(v_fst_2893_);
v___x_2899_ = lean_nat_dec_eq(v___x_2898_, v___x_2888_);
if (v___x_2899_ == 0)
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2903_; 
lean_dec(v_snd_2894_);
lean_dec(v___x_2887_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_body_2790_);
v___x_2900_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2901_ = l_Lean_MessageData_ofExpr(v___y_2881_);
if (v_isShared_2897_ == 0)
{
lean_ctor_set_tag(v___x_2896_, 7);
lean_ctor_set(v___x_2896_, 1, v___x_2901_);
lean_ctor_set(v___x_2896_, 0, v___x_2900_);
v___x_2903_ = v___x_2896_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2900_);
lean_ctor_set(v_reuseFailAlloc_2915_, 1, v___x_2901_);
v___x_2903_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v_a_2907_; lean_object* v___x_2909_; uint8_t v_isShared_2910_; uint8_t v_isSharedCheck_2914_; 
v___x_2904_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2903_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2905_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v___x_2906_);
if (v_isSharedCheck_2914_ == 0)
{
v___x_2909_ = v___x_2906_;
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
else
{
lean_inc(v_a_2907_);
lean_dec(v___x_2906_);
v___x_2909_ = lean_box(0);
v_isShared_2910_ = v_isSharedCheck_2914_;
goto v_resetjp_2908_;
}
v_resetjp_2908_:
{
lean_object* v___x_2912_; 
if (v_isShared_2910_ == 0)
{
v___x_2912_ = v___x_2909_;
goto v_reusejp_2911_;
}
else
{
lean_object* v_reuseFailAlloc_2913_; 
v_reuseFailAlloc_2913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2913_, 0, v_a_2907_);
v___x_2912_ = v_reuseFailAlloc_2913_;
goto v_reusejp_2911_;
}
v_reusejp_2911_:
{
return v___x_2912_;
}
}
}
}
else
{
lean_del_object(v___x_2896_);
v___y_2793_ = v___y_2879_;
v___y_2794_ = v___x_2887_;
v___y_2795_ = v___x_2888_;
v___y_2796_ = v___y_2880_;
v___y_2797_ = v_snd_2894_;
v___y_2798_ = v___y_2881_;
v___y_2799_ = v___y_2882_;
v___y_2800_ = v___y_2883_;
v___y_2801_ = v___y_2884_;
v___y_2802_ = v___y_2885_;
v___y_2803_ = v___y_2886_;
goto v___jp_2792_;
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec(v___x_2887_);
lean_dec(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec(v___y_2882_);
lean_dec_ref(v___y_2881_);
lean_dec_ref(v___y_2880_);
lean_dec_ref(v___y_2879_);
lean_dec_ref(v_body_2790_);
v_a_2917_ = lean_ctor_get(v___x_2891_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2891_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2891_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2891_);
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
v___jp_2925_:
{
uint8_t v___x_2934_; 
v___x_2934_ = l_Lean_Expr_isFVar(v_fst_2928_);
if (v___x_2934_ == 0)
{
lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec(v_snd_2929_);
lean_dec_ref(v_fst_2928_);
lean_dec_ref(v_fst_2927_);
lean_dec_ref(v_fst_2926_);
lean_dec_ref(v_body_2790_);
lean_dec(v_mvarId_2777_);
v___x_2935_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2936_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2935_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v___y_2931_);
lean_dec_ref(v___y_2930_);
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2936_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2936_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
else
{
v___y_2879_ = v_fst_2927_;
v___y_2880_ = v_fst_2926_;
v___y_2881_ = v_fst_2928_;
v___y_2882_ = v_snd_2929_;
v___y_2883_ = v___y_2930_;
v___y_2884_ = v___y_2931_;
v___y_2885_ = v___y_2932_;
v___y_2886_ = v___y_2933_;
goto v___jp_2878_;
}
}
}
else
{
lean_dec(v_a_2785_);
lean_dec(v_mvarId_2777_);
goto v___jp_2786_;
}
v___jp_2786_:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2788_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2787_, v___y_2779_, v___y_2780_, v___y_2781_, v___y_2782_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
return v___x_2788_;
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
lean_dec(v___y_2780_);
lean_dec_ref(v___y_2779_);
lean_dec(v_mvarId_2777_);
v_a_3017_ = lean_ctor_get(v___x_2784_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2784_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_2784_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_2784_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object* v_mvarId_3025_, lean_object* v_substLHS_3026_, lean_object* v___y_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
uint8_t v_substLHS_boxed_3032_; lean_object* v_res_3033_; 
v_substLHS_boxed_3032_ = lean_unbox(v_substLHS_3026_);
v_res_3033_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_3025_, v_substLHS_boxed_3032_, v___y_3027_, v___y_3028_, v___y_3029_, v___y_3030_);
return v_res_3033_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3034_, lean_object* v_i_3035_, lean_object* v_k_3036_){
_start:
{
lean_object* v___x_3037_; uint8_t v___x_3038_; 
v___x_3037_ = lean_array_get_size(v_keys_3034_);
v___x_3038_ = lean_nat_dec_lt(v_i_3035_, v___x_3037_);
if (v___x_3038_ == 0)
{
lean_dec(v_i_3035_);
return v___x_3038_;
}
else
{
lean_object* v_k_x27_3039_; uint8_t v___x_3040_; 
v_k_x27_3039_ = lean_array_fget_borrowed(v_keys_3034_, v_i_3035_);
v___x_3040_ = l_Lean_instBEqMVarId_beq(v_k_3036_, v_k_x27_3039_);
if (v___x_3040_ == 0)
{
lean_object* v___x_3041_; lean_object* v___x_3042_; 
v___x_3041_ = lean_unsigned_to_nat(1u);
v___x_3042_ = lean_nat_add(v_i_3035_, v___x_3041_);
lean_dec(v_i_3035_);
v_i_3035_ = v___x_3042_;
goto _start;
}
else
{
lean_dec(v_i_3035_);
return v___x_3040_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3044_, lean_object* v_i_3045_, lean_object* v_k_3046_){
_start:
{
uint8_t v_res_3047_; lean_object* v_r_3048_; 
v_res_3047_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3044_, v_i_3045_, v_k_3046_);
lean_dec(v_k_3046_);
lean_dec_ref(v_keys_3044_);
v_r_3048_ = lean_box(v_res_3047_);
return v_r_3048_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3049_, size_t v_x_3050_, lean_object* v_x_3051_){
_start:
{
if (lean_obj_tag(v_x_3049_) == 0)
{
lean_object* v_es_3052_; lean_object* v___x_3053_; size_t v___x_3054_; size_t v___x_3055_; size_t v___x_3056_; lean_object* v_j_3057_; lean_object* v___x_3058_; 
v_es_3052_ = lean_ctor_get(v_x_3049_, 0);
lean_inc_ref(v_es_3052_);
lean_dec_ref(v_x_3049_);
v___x_3053_ = lean_box(2);
v___x_3054_ = ((size_t)5ULL);
v___x_3055_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__6_spec__7_spec__9___redArg___closed__1);
v___x_3056_ = lean_usize_land(v_x_3050_, v___x_3055_);
v_j_3057_ = lean_usize_to_nat(v___x_3056_);
v___x_3058_ = lean_array_get(v___x_3053_, v_es_3052_, v_j_3057_);
lean_dec(v_j_3057_);
lean_dec_ref(v_es_3052_);
switch(lean_obj_tag(v___x_3058_))
{
case 0:
{
lean_object* v_key_3059_; uint8_t v___x_3060_; 
v_key_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_key_3059_);
lean_dec_ref(v___x_3058_);
v___x_3060_ = l_Lean_instBEqMVarId_beq(v_x_3051_, v_key_3059_);
lean_dec(v_key_3059_);
return v___x_3060_;
}
case 1:
{
lean_object* v_node_3061_; size_t v___x_3062_; 
v_node_3061_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_node_3061_);
lean_dec_ref(v___x_3058_);
v___x_3062_ = lean_usize_shift_right(v_x_3050_, v___x_3054_);
v_x_3049_ = v_node_3061_;
v_x_3050_ = v___x_3062_;
goto _start;
}
default: 
{
uint8_t v___x_3064_; 
v___x_3064_ = 0;
return v___x_3064_;
}
}
}
else
{
lean_object* v_ks_3065_; lean_object* v___x_3066_; uint8_t v___x_3067_; 
v_ks_3065_ = lean_ctor_get(v_x_3049_, 0);
lean_inc_ref(v_ks_3065_);
lean_dec_ref(v_x_3049_);
v___x_3066_ = lean_unsigned_to_nat(0u);
v___x_3067_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3065_, v___x_3066_, v_x_3051_);
lean_dec_ref(v_ks_3065_);
return v___x_3067_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3068_, lean_object* v_x_3069_, lean_object* v_x_3070_){
_start:
{
size_t v_x_12140__boxed_3071_; uint8_t v_res_3072_; lean_object* v_r_3073_; 
v_x_12140__boxed_3071_ = lean_unbox_usize(v_x_3069_);
lean_dec(v_x_3069_);
v_res_3072_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3068_, v_x_12140__boxed_3071_, v_x_3070_);
lean_dec(v_x_3070_);
v_r_3073_ = lean_box(v_res_3072_);
return v_r_3073_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3074_, lean_object* v_x_3075_){
_start:
{
uint64_t v___x_3076_; size_t v___x_3077_; uint8_t v___x_3078_; 
v___x_3076_ = l_Lean_instHashableMVarId_hash(v_x_3075_);
v___x_3077_ = lean_uint64_to_usize(v___x_3076_);
v___x_3078_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3074_, v___x_3077_, v_x_3075_);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3079_, lean_object* v_x_3080_){
_start:
{
uint8_t v_res_3081_; lean_object* v_r_3082_; 
v_res_3081_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3079_, v_x_3080_);
lean_dec(v_x_3080_);
v_r_3082_ = lean_box(v_res_3081_);
return v_r_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3083_, lean_object* v___y_3084_){
_start:
{
lean_object* v___x_3086_; lean_object* v_mctx_3087_; lean_object* v_eAssignment_3088_; uint8_t v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3086_ = lean_st_ref_get(v___y_3084_);
v_mctx_3087_ = lean_ctor_get(v___x_3086_, 0);
lean_inc_ref(v_mctx_3087_);
lean_dec(v___x_3086_);
v_eAssignment_3088_ = lean_ctor_get(v_mctx_3087_, 7);
lean_inc_ref(v_eAssignment_3088_);
lean_dec_ref(v_mctx_3087_);
v___x_3089_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3088_, v_mvarId_3083_);
v___x_3090_ = lean_box(v___x_3089_);
v___x_3091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3090_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec(v_mvarId_3092_);
return v_res_3095_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3097_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3098_ = l_Lean_stringToMessageData(v___x_3097_);
return v___x_3098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3099_, uint8_t v___y_3100_, lean_object* v_____r_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_){
_start:
{
lean_object* v___y_3108_; lean_object* v___y_3109_; lean_object* v___y_3110_; lean_object* v___y_3111_; lean_object* v___x_3143_; lean_object* v_a_3144_; uint8_t v___x_3145_; 
v___x_3143_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3099_, v___y_3103_);
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref(v___x_3143_);
v___x_3145_ = lean_unbox(v_a_3144_);
lean_dec(v_a_3144_);
if (v___x_3145_ == 0)
{
v___y_3108_ = v___y_3102_;
v___y_3109_ = v___y_3103_;
v___y_3110_ = v___y_3104_;
v___y_3111_ = v___y_3105_;
goto v___jp_3107_;
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
lean_dec(v_mvarId_3099_);
v___x_3146_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3147_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3146_, v___y_3102_, v___y_3103_, v___y_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec_ref(v___y_3104_);
lean_dec(v___y_3103_);
lean_dec_ref(v___y_3102_);
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3147_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3147_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
v_resetjp_3149_:
{
lean_object* v___x_3153_; 
if (v_isShared_3151_ == 0)
{
v___x_3153_ = v___x_3150_;
goto v_reusejp_3152_;
}
else
{
lean_object* v_reuseFailAlloc_3154_; 
v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
v___x_3153_ = v_reuseFailAlloc_3154_;
goto v_reusejp_3152_;
}
v_reusejp_3152_:
{
return v___x_3153_;
}
}
}
v___jp_3107_:
{
lean_object* v___x_3112_; 
lean_inc(v___y_3111_);
lean_inc_ref(v___y_3110_);
lean_inc(v___y_3109_);
lean_inc_ref(v___y_3108_);
v___x_3112_ = l_Lean_Meta_intro1Core(v_mvarId_3099_, v___y_3100_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
if (lean_obj_tag(v___x_3112_) == 0)
{
lean_object* v_a_3113_; lean_object* v_fst_3114_; lean_object* v_snd_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
v_a_3113_ = lean_ctor_get(v___x_3112_, 0);
lean_inc(v_a_3113_);
lean_dec_ref(v___x_3112_);
v_fst_3114_ = lean_ctor_get(v_a_3113_, 0);
lean_inc(v_fst_3114_);
v_snd_3115_ = lean_ctor_get(v_a_3113_, 1);
lean_inc(v_snd_3115_);
lean_dec(v_a_3113_);
v___x_3116_ = lean_box(0);
v___x_3117_ = l_Lean_Meta_substEq(v_snd_3115_, v_fst_3114_, v___x_3116_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
if (lean_obj_tag(v___x_3117_) == 0)
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3126_; 
v_a_3118_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3120_ = v___x_3117_;
v_isShared_3121_ = v_isSharedCheck_3126_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3117_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3126_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3122_; lean_object* v___x_3124_; 
v___x_3122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3122_, 0, v_a_3118_);
if (v_isShared_3121_ == 0)
{
lean_ctor_set(v___x_3120_, 0, v___x_3122_);
v___x_3124_ = v___x_3120_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v___x_3122_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
v_a_3127_ = lean_ctor_get(v___x_3117_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3117_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3117_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3117_);
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
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v___y_3111_);
lean_dec_ref(v___y_3110_);
lean_dec(v___y_3109_);
lean_dec_ref(v___y_3108_);
v_a_3135_ = lean_ctor_get(v___x_3112_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3112_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3112_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3112_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3156_, lean_object* v___y_3157_, lean_object* v_____r_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
uint8_t v___y_12214__boxed_3164_; lean_object* v_res_3165_; 
v___y_12214__boxed_3164_ = lean_unbox(v___y_3157_);
v_res_3165_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3156_, v___y_12214__boxed_3164_, v_____r_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
return v_res_3165_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__3(void){
_start:
{
lean_object* v___x_3170_; lean_object* v___x_3171_; 
v___x_3170_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__2));
v___x_3171_ = l_Lean_stringToMessageData(v___x_3170_);
return v___x_3171_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__5(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; 
v___x_3173_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__4));
v___x_3174_ = l_Lean_stringToMessageData(v___x_3173_);
return v___x_3174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3175_, uint8_t v_substLHS_3176_, lean_object* v_a_3177_, lean_object* v_a_3178_, lean_object* v_a_3179_, lean_object* v_a_3180_){
_start:
{
lean_object* v___y_3183_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___x_3201_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
lean_inc(v_mvarId_3175_);
v___x_3202_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3175_, v___x_3201_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v___x_3203_; lean_object* v___f_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_dec_ref(v___x_3202_);
v___x_3203_ = lean_box(v_substLHS_3176_);
lean_inc(v_mvarId_3175_);
v___f_3204_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3204_, 0, v_mvarId_3175_);
lean_closure_set(v___f_3204_, 1, v___x_3203_);
lean_inc(v_mvarId_3175_);
v___x_3205_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___boxed), 8, 3);
lean_closure_set(v___x_3205_, 0, lean_box(0));
lean_closure_set(v___x_3205_, 1, v_mvarId_3175_);
lean_closure_set(v___x_3205_, 2, v___f_3204_);
lean_inc(v_a_3180_);
lean_inc_ref(v_a_3179_);
lean_inc(v_a_3178_);
lean_inc_ref(v_a_3177_);
v___x_3206_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3205_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_mvarId_3175_);
return v___x_3206_;
}
else
{
lean_object* v_a_3207_; uint8_t v___y_3209_; uint8_t v___x_3240_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
v___x_3240_ = l_Lean_Exception_isInterrupt(v_a_3207_);
if (v___x_3240_ == 0)
{
uint8_t v___x_3241_; 
lean_inc(v_a_3207_);
v___x_3241_ = l_Lean_Exception_isRuntime(v_a_3207_);
v___y_3209_ = v___x_3241_;
goto v___jp_3208_;
}
else
{
v___y_3209_ = v___x_3240_;
goto v___jp_3208_;
}
v___jp_3208_:
{
if (v___y_3209_ == 0)
{
lean_object* v___x_3210_; lean_object* v___x_3211_; lean_object* v_a_3212_; lean_object* v___x_3214_; uint8_t v_isShared_3215_; uint8_t v_isSharedCheck_3239_; 
lean_dec_ref(v___x_3206_);
v___x_3210_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__22));
v___x_3211_ = l_Lean_isTracingEnabledFor___at___00Lean_Meta_substCore_spec__3___redArg(v___x_3210_, v_a_3179_);
v_a_3212_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3214_ = v___x_3211_;
v_isShared_3215_ = v_isSharedCheck_3239_;
goto v_resetjp_3213_;
}
else
{
lean_inc(v_a_3212_);
lean_dec(v___x_3211_);
v___x_3214_ = lean_box(0);
v_isShared_3215_ = v_isSharedCheck_3239_;
goto v_resetjp_3213_;
}
v_resetjp_3213_:
{
uint8_t v___x_3216_; 
v___x_3216_ = lean_unbox(v_a_3212_);
lean_dec(v_a_3212_);
if (v___x_3216_ == 0)
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
lean_del_object(v___x_3214_);
lean_dec(v_a_3207_);
v___x_3217_ = lean_box(0);
v___x_3218_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3175_, v___y_3209_, v___x_3217_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
v___y_3183_ = v___x_3218_;
goto v___jp_3182_;
}
else
{
lean_object* v___x_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3225_; 
v___x_3219_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__3, &l_Lean_Meta_introSubstEq___closed__3_once, _init_l_Lean_Meta_introSubstEq___closed__3);
v___x_3220_ = l_Lean_Exception_toMessageData(v_a_3207_);
v___x_3221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3221_, 0, v___x_3219_);
lean_ctor_set(v___x_3221_, 1, v___x_3220_);
v___x_3222_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__5, &l_Lean_Meta_introSubstEq___closed__5_once, _init_l_Lean_Meta_introSubstEq___closed__5);
v___x_3223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3221_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
lean_inc(v_mvarId_3175_);
if (v_isShared_3215_ == 0)
{
lean_ctor_set_tag(v___x_3214_, 1);
lean_ctor_set(v___x_3214_, 0, v_mvarId_3175_);
v___x_3225_ = v___x_3214_;
goto v_reusejp_3224_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_mvarId_3175_);
v___x_3225_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3224_;
}
v_reusejp_3224_:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3223_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__4(v___x_3210_, v___x_3226_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
if (lean_obj_tag(v___x_3227_) == 0)
{
lean_object* v_a_3228_; lean_object* v___x_3229_; 
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_a_3228_);
lean_dec_ref(v___x_3227_);
v___x_3229_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3175_, v___y_3209_, v_a_3228_, v_a_3177_, v_a_3178_, v_a_3179_, v_a_3180_);
v___y_3183_ = v___x_3229_;
goto v___jp_3182_;
}
else
{
lean_object* v_a_3230_; lean_object* v___x_3232_; uint8_t v_isShared_3233_; uint8_t v_isSharedCheck_3237_; 
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_mvarId_3175_);
v_a_3230_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3237_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3237_ == 0)
{
v___x_3232_ = v___x_3227_;
v_isShared_3233_ = v_isSharedCheck_3237_;
goto v_resetjp_3231_;
}
else
{
lean_inc(v_a_3230_);
lean_dec(v___x_3227_);
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
}
else
{
lean_dec(v_a_3207_);
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_mvarId_3175_);
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_dec(v_a_3180_);
lean_dec_ref(v_a_3179_);
lean_dec(v_a_3178_);
lean_dec_ref(v_a_3177_);
lean_dec(v_mvarId_3175_);
v_a_3242_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3202_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3202_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
v___jp_3182_:
{
if (lean_obj_tag(v___y_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3186_; uint8_t v_isShared_3187_; uint8_t v_isSharedCheck_3192_; 
v_a_3184_ = lean_ctor_get(v___y_3183_, 0);
v_isSharedCheck_3192_ = !lean_is_exclusive(v___y_3183_);
if (v_isSharedCheck_3192_ == 0)
{
v___x_3186_ = v___y_3183_;
v_isShared_3187_ = v_isSharedCheck_3192_;
goto v_resetjp_3185_;
}
else
{
lean_inc(v_a_3184_);
lean_dec(v___y_3183_);
v___x_3186_ = lean_box(0);
v_isShared_3187_ = v_isSharedCheck_3192_;
goto v_resetjp_3185_;
}
v_resetjp_3185_:
{
lean_object* v_a_3188_; lean_object* v___x_3190_; 
v_a_3188_ = lean_ctor_get(v_a_3184_, 0);
lean_inc(v_a_3188_);
lean_dec(v_a_3184_);
if (v_isShared_3187_ == 0)
{
lean_ctor_set(v___x_3186_, 0, v_a_3188_);
v___x_3190_ = v___x_3186_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v_a_3188_);
v___x_3190_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
return v___x_3190_;
}
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
v_a_3193_ = lean_ctor_get(v___y_3183_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___y_3183_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___y_3183_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___y_3183_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object* v_mvarId_3250_, lean_object* v_substLHS_3251_, lean_object* v_a_3252_, lean_object* v_a_3253_, lean_object* v_a_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_){
_start:
{
uint8_t v_substLHS_boxed_3257_; lean_object* v_res_3258_; 
v_substLHS_boxed_3257_ = lean_unbox(v_substLHS_3251_);
v_res_3258_ = l_Lean_Meta_introSubstEq(v_mvarId_3250_, v_substLHS_boxed_3257_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_);
return v_res_3258_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object* v_00_u03b1_3259_, lean_object* v_msg_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_){
_start:
{
lean_object* v___x_3266_; 
v___x_3266_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_3260_, v___y_3261_, v___y_3262_, v___y_3263_, v___y_3264_);
return v___x_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object* v_00_u03b1_3267_, lean_object* v_msg_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_){
_start:
{
lean_object* v_res_3274_; 
v_res_3274_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(v_00_u03b1_3267_, v_msg_3268_, v___y_3269_, v___y_3270_, v___y_3271_, v___y_3272_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object* v_mvarId_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___x_3281_; 
v___x_3281_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3275_, v___y_3277_);
return v___x_3281_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object* v_mvarId_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
lean_dec(v_mvarId_3282_);
return v_res_3288_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object* v_00_u03b2_3289_, lean_object* v_x_3290_, lean_object* v_x_3291_){
_start:
{
uint8_t v___x_3292_; 
v___x_3292_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3290_, v_x_3291_);
return v___x_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3293_, lean_object* v_x_3294_, lean_object* v_x_3295_){
_start:
{
uint8_t v_res_3296_; lean_object* v_r_3297_; 
v_res_3296_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(v_00_u03b2_3293_, v_x_3294_, v_x_3295_);
lean_dec(v_x_3295_);
v_r_3297_ = lean_box(v_res_3296_);
return v_r_3297_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_3298_, lean_object* v_x_3299_, size_t v_x_3300_, lean_object* v_x_3301_){
_start:
{
uint8_t v___x_3302_; 
v___x_3302_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3299_, v_x_3300_, v_x_3301_);
return v___x_3302_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3303_, lean_object* v_x_3304_, lean_object* v_x_3305_, lean_object* v_x_3306_){
_start:
{
size_t v_x_12571__boxed_3307_; uint8_t v_res_3308_; lean_object* v_r_3309_; 
v_x_12571__boxed_3307_ = lean_unbox_usize(v_x_3305_);
lean_dec(v_x_3305_);
v_res_3308_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3303_, v_x_3304_, v_x_12571__boxed_3307_, v_x_3306_);
lean_dec(v_x_3306_);
v_r_3309_ = lean_box(v_res_3308_);
return v_r_3309_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3310_, lean_object* v_keys_3311_, lean_object* v_vals_3312_, lean_object* v_heq_3313_, lean_object* v_i_3314_, lean_object* v_k_3315_){
_start:
{
uint8_t v___x_3316_; 
v___x_3316_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3311_, v_i_3314_, v_k_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3317_, lean_object* v_keys_3318_, lean_object* v_vals_3319_, lean_object* v_heq_3320_, lean_object* v_i_3321_, lean_object* v_k_3322_){
_start:
{
uint8_t v_res_3323_; lean_object* v_r_3324_; 
v_res_3323_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(v_00_u03b2_3317_, v_keys_3318_, v_vals_3319_, v_heq_3320_, v_i_3321_, v_k_3322_);
lean_dec(v_k_3322_);
lean_dec_ref(v_vals_3319_);
lean_dec_ref(v_keys_3318_);
v_r_3324_ = lean_box(v_res_3323_);
return v_r_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* v_x_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
lean_object* v___x_3331_; 
v___x_3331_ = l_Lean_Meta_saveState___redArg(v___y_3327_, v___y_3329_);
if (lean_obj_tag(v___x_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3333_; 
v_a_3332_ = lean_ctor_get(v___x_3331_, 0);
lean_inc(v_a_3332_);
lean_dec_ref(v___x_3331_);
lean_inc(v___y_3329_);
lean_inc(v___y_3327_);
v___x_3333_ = lean_apply_5(v_x_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_, lean_box(0));
if (lean_obj_tag(v___x_3333_) == 0)
{
lean_object* v_a_3334_; lean_object* v___x_3336_; uint8_t v_isShared_3337_; uint8_t v_isSharedCheck_3342_; 
lean_dec(v_a_3332_);
lean_dec(v___y_3329_);
lean_dec(v___y_3327_);
v_a_3334_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3342_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3342_ == 0)
{
v___x_3336_ = v___x_3333_;
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
else
{
lean_inc(v_a_3334_);
lean_dec(v___x_3333_);
v___x_3336_ = lean_box(0);
v_isShared_3337_ = v_isSharedCheck_3342_;
goto v_resetjp_3335_;
}
v_resetjp_3335_:
{
lean_object* v___x_3338_; lean_object* v___x_3340_; 
v___x_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3338_, 0, v_a_3334_);
if (v_isShared_3337_ == 0)
{
lean_ctor_set(v___x_3336_, 0, v___x_3338_);
v___x_3340_ = v___x_3336_;
goto v_reusejp_3339_;
}
else
{
lean_object* v_reuseFailAlloc_3341_; 
v_reuseFailAlloc_3341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3338_);
v___x_3340_ = v_reuseFailAlloc_3341_;
goto v_reusejp_3339_;
}
v_reusejp_3339_:
{
return v___x_3340_;
}
}
}
else
{
lean_object* v_a_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3372_; 
v_a_3343_ = lean_ctor_get(v___x_3333_, 0);
v_isSharedCheck_3372_ = !lean_is_exclusive(v___x_3333_);
if (v_isSharedCheck_3372_ == 0)
{
v___x_3345_ = v___x_3333_;
v_isShared_3346_ = v_isSharedCheck_3372_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_a_3343_);
lean_dec(v___x_3333_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3372_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
uint8_t v___y_3348_; uint8_t v___x_3370_; 
v___x_3370_ = l_Lean_Exception_isInterrupt(v_a_3343_);
if (v___x_3370_ == 0)
{
uint8_t v___x_3371_; 
lean_inc(v_a_3343_);
v___x_3371_ = l_Lean_Exception_isRuntime(v_a_3343_);
v___y_3348_ = v___x_3371_;
goto v___jp_3347_;
}
else
{
v___y_3348_ = v___x_3370_;
goto v___jp_3347_;
}
v___jp_3347_:
{
if (v___y_3348_ == 0)
{
lean_object* v___x_3349_; 
lean_del_object(v___x_3345_);
lean_dec(v_a_3343_);
v___x_3349_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3332_, v___y_3327_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec(v___y_3327_);
lean_dec(v_a_3332_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v___x_3351_; uint8_t v_isShared_3352_; uint8_t v_isSharedCheck_3357_; 
v_isSharedCheck_3357_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3357_ == 0)
{
lean_object* v_unused_3358_; 
v_unused_3358_ = lean_ctor_get(v___x_3349_, 0);
lean_dec(v_unused_3358_);
v___x_3351_ = v___x_3349_;
v_isShared_3352_ = v_isSharedCheck_3357_;
goto v_resetjp_3350_;
}
else
{
lean_dec(v___x_3349_);
v___x_3351_ = lean_box(0);
v_isShared_3352_ = v_isSharedCheck_3357_;
goto v_resetjp_3350_;
}
v_resetjp_3350_:
{
lean_object* v___x_3353_; lean_object* v___x_3355_; 
v___x_3353_ = lean_box(0);
if (v_isShared_3352_ == 0)
{
lean_ctor_set(v___x_3351_, 0, v___x_3353_);
v___x_3355_ = v___x_3351_;
goto v_reusejp_3354_;
}
else
{
lean_object* v_reuseFailAlloc_3356_; 
v_reuseFailAlloc_3356_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3356_, 0, v___x_3353_);
v___x_3355_ = v_reuseFailAlloc_3356_;
goto v_reusejp_3354_;
}
v_reusejp_3354_:
{
return v___x_3355_;
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3366_; 
v_a_3359_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3366_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3366_ == 0)
{
v___x_3361_ = v___x_3349_;
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3349_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3366_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
lean_object* v___x_3364_; 
if (v_isShared_3362_ == 0)
{
v___x_3364_ = v___x_3361_;
goto v_reusejp_3363_;
}
else
{
lean_object* v_reuseFailAlloc_3365_; 
v_reuseFailAlloc_3365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3365_, 0, v_a_3359_);
v___x_3364_ = v_reuseFailAlloc_3365_;
goto v_reusejp_3363_;
}
v_reusejp_3363_:
{
return v___x_3364_;
}
}
}
}
else
{
lean_object* v___x_3368_; 
lean_dec(v_a_3332_);
lean_dec(v___y_3329_);
lean_dec(v___y_3327_);
if (v_isShared_3346_ == 0)
{
v___x_3368_ = v___x_3345_;
goto v_reusejp_3367_;
}
else
{
lean_object* v_reuseFailAlloc_3369_; 
v_reuseFailAlloc_3369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3369_, 0, v_a_3343_);
v___x_3368_ = v_reuseFailAlloc_3369_;
goto v_reusejp_3367_;
}
v_reusejp_3367_:
{
return v___x_3368_;
}
}
}
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec_ref(v_x_3325_);
v_a_3373_ = lean_ctor_get(v___x_3331_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3331_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3331_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3331_);
v___x_3375_ = lean_box(0);
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
v_resetjp_3374_:
{
lean_object* v___x_3378_; 
if (v_isShared_3376_ == 0)
{
v___x_3378_ = v___x_3375_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v_a_3373_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object* v_x_3381_, lean_object* v___y_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v_res_3387_; 
v_res_3387_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3381_, v___y_3382_, v___y_3383_, v___y_3384_, v___y_3385_);
return v_res_3387_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object* v_00_u03b1_3388_, lean_object* v_x_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_){
_start:
{
lean_object* v___x_3395_; 
v___x_3395_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_);
return v___x_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object* v_00_u03b1_3396_, lean_object* v_x_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(v_00_u03b1_3396_, v_x_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* v_mvarId_3404_, lean_object* v_hFVarId_3405_, lean_object* v_a_3406_, lean_object* v_a_3407_, lean_object* v_a_3408_, lean_object* v_a_3409_){
_start:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; 
v___x_3411_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___boxed), 7, 2);
lean_closure_set(v___x_3411_, 0, v_mvarId_3404_);
lean_closure_set(v___x_3411_, 1, v_hFVarId_3405_);
v___x_3412_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3411_, v_a_3406_, v_a_3407_, v_a_3408_, v_a_3409_);
return v___x_3412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object* v_mvarId_3413_, lean_object* v_hFVarId_3414_, lean_object* v_a_3415_, lean_object* v_a_3416_, lean_object* v_a_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_){
_start:
{
lean_object* v_res_3420_; 
v_res_3420_ = l_Lean_Meta_substVar_x3f(v_mvarId_3413_, v_hFVarId_3414_, v_a_3415_, v_a_3416_, v_a_3417_, v_a_3418_);
return v_res_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* v_mvarId_3421_, lean_object* v_hFVarId_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_){
_start:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; 
v___x_3428_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 7, 2);
lean_closure_set(v___x_3428_, 0, v_mvarId_3421_);
lean_closure_set(v___x_3428_, 1, v_hFVarId_3422_);
v___x_3429_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3428_, v_a_3423_, v_a_3424_, v_a_3425_, v_a_3426_);
return v___x_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object* v_mvarId_3430_, lean_object* v_hFVarId_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_){
_start:
{
lean_object* v_res_3437_; 
v_res_3437_ = l_Lean_Meta_subst_x3f(v_mvarId_3430_, v_hFVarId_3431_, v_a_3432_, v_a_3433_, v_a_3434_, v_a_3435_);
return v_res_3437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* v_mvarId_3438_, lean_object* v_hFVarId_3439_, uint8_t v_symm_3440_, lean_object* v_fvarSubst_3441_, uint8_t v_clearH_3442_, uint8_t v_tryToSkip_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; 
v___x_3449_ = lean_box(v_symm_3440_);
v___x_3450_ = lean_box(v_clearH_3442_);
v___x_3451_ = lean_box(v_tryToSkip_3443_);
v___x_3452_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_3452_, 0, v_mvarId_3438_);
lean_closure_set(v___x_3452_, 1, v_hFVarId_3439_);
lean_closure_set(v___x_3452_, 2, v___x_3449_);
lean_closure_set(v___x_3452_, 3, v_fvarSubst_3441_);
lean_closure_set(v___x_3452_, 4, v___x_3450_);
lean_closure_set(v___x_3452_, 5, v___x_3451_);
v___x_3453_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3452_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* v_mvarId_3454_, lean_object* v_hFVarId_3455_, lean_object* v_symm_3456_, lean_object* v_fvarSubst_3457_, lean_object* v_clearH_3458_, lean_object* v_tryToSkip_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_){
_start:
{
uint8_t v_symm_boxed_3465_; uint8_t v_clearH_boxed_3466_; uint8_t v_tryToSkip_boxed_3467_; lean_object* v_res_3468_; 
v_symm_boxed_3465_ = lean_unbox(v_symm_3456_);
v_clearH_boxed_3466_ = lean_unbox(v_clearH_3458_);
v_tryToSkip_boxed_3467_ = lean_unbox(v_tryToSkip_3459_);
v_res_3468_ = l_Lean_Meta_substCore_x3f(v_mvarId_3454_, v_hFVarId_3455_, v_symm_boxed_3465_, v_fvarSubst_3457_, v_clearH_boxed_3466_, v_tryToSkip_boxed_3467_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_);
return v_res_3468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* v_mvarId_3469_, lean_object* v_hFVarId_3470_, lean_object* v_a_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_){
_start:
{
lean_object* v___x_3476_; 
lean_inc(v_mvarId_3469_);
v___x_3476_ = l_Lean_Meta_substVar_x3f(v_mvarId_3469_, v_hFVarId_3470_, v_a_3471_, v_a_3472_, v_a_3473_, v_a_3474_);
if (lean_obj_tag(v___x_3476_) == 0)
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3488_; 
v_a_3477_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3479_ = v___x_3476_;
v_isShared_3480_ = v_isSharedCheck_3488_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3476_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3488_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
if (lean_obj_tag(v_a_3477_) == 0)
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v_mvarId_3469_);
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_mvarId_3469_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
else
{
lean_object* v_val_3484_; lean_object* v___x_3486_; 
lean_dec(v_mvarId_3469_);
v_val_3484_ = lean_ctor_get(v_a_3477_, 0);
lean_inc(v_val_3484_);
lean_dec_ref(v_a_3477_);
if (v_isShared_3480_ == 0)
{
lean_ctor_set(v___x_3479_, 0, v_val_3484_);
v___x_3486_ = v___x_3479_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_val_3484_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec(v_mvarId_3469_);
v_a_3489_ = lean_ctor_get(v___x_3476_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3476_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3476_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3476_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object* v_mvarId_3497_, lean_object* v_hFVarId_3498_, lean_object* v_a_3499_, lean_object* v_a_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_){
_start:
{
lean_object* v_res_3504_; 
v_res_3504_ = l_Lean_Meta_trySubstVar(v_mvarId_3497_, v_hFVarId_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_);
return v_res_3504_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* v_mvarId_3505_, lean_object* v_hFVarId_3506_, lean_object* v_a_3507_, lean_object* v_a_3508_, lean_object* v_a_3509_, lean_object* v_a_3510_){
_start:
{
lean_object* v___x_3512_; 
lean_inc(v_mvarId_3505_);
v___x_3512_ = l_Lean_Meta_subst_x3f(v_mvarId_3505_, v_hFVarId_3506_, v_a_3507_, v_a_3508_, v_a_3509_, v_a_3510_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; lean_object* v___x_3515_; uint8_t v_isShared_3516_; uint8_t v_isSharedCheck_3524_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3524_ == 0)
{
v___x_3515_ = v___x_3512_;
v_isShared_3516_ = v_isSharedCheck_3524_;
goto v_resetjp_3514_;
}
else
{
lean_inc(v_a_3513_);
lean_dec(v___x_3512_);
v___x_3515_ = lean_box(0);
v_isShared_3516_ = v_isSharedCheck_3524_;
goto v_resetjp_3514_;
}
v_resetjp_3514_:
{
if (lean_obj_tag(v_a_3513_) == 0)
{
lean_object* v___x_3518_; 
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v_mvarId_3505_);
v___x_3518_ = v___x_3515_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3519_; 
v_reuseFailAlloc_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3519_, 0, v_mvarId_3505_);
v___x_3518_ = v_reuseFailAlloc_3519_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
return v___x_3518_;
}
}
else
{
lean_object* v_val_3520_; lean_object* v___x_3522_; 
lean_dec(v_mvarId_3505_);
v_val_3520_ = lean_ctor_get(v_a_3513_, 0);
lean_inc(v_val_3520_);
lean_dec_ref(v_a_3513_);
if (v_isShared_3516_ == 0)
{
lean_ctor_set(v___x_3515_, 0, v_val_3520_);
v___x_3522_ = v___x_3515_;
goto v_reusejp_3521_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_val_3520_);
v___x_3522_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3521_;
}
v_reusejp_3521_:
{
return v___x_3522_;
}
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_dec(v_mvarId_3505_);
v_a_3525_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3512_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3512_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object* v_mvarId_3533_, lean_object* v_hFVarId_3534_, lean_object* v_a_3535_, lean_object* v_a_3536_, lean_object* v_a_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_){
_start:
{
lean_object* v_res_3540_; 
v_res_3540_ = l_Lean_Meta_trySubst(v_mvarId_3533_, v_hFVarId_3534_, v_a_3535_, v_a_3536_, v_a_3537_, v_a_3538_);
return v_res_3540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_mvarId_3544_, lean_object* v_as_3545_, size_t v_sz_3546_, size_t v_i_3547_, lean_object* v_b_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
uint8_t v___x_3554_; 
v___x_3554_ = lean_usize_dec_lt(v_i_3547_, v_sz_3546_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; 
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v_mvarId_3544_);
v___x_3555_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3555_, 0, v_b_3548_);
return v___x_3555_;
}
else
{
lean_object* v_snd_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3609_; 
v_snd_3556_ = lean_ctor_get(v_b_3548_, 1);
v_isSharedCheck_3609_ = !lean_is_exclusive(v_b_3548_);
if (v_isSharedCheck_3609_ == 0)
{
lean_object* v_unused_3610_; 
v_unused_3610_ = lean_ctor_get(v_b_3548_, 0);
lean_dec(v_unused_3610_);
v___x_3558_ = v_b_3548_;
v_isShared_3559_ = v_isSharedCheck_3609_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_snd_3556_);
lean_dec(v_b_3548_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3609_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3560_; lean_object* v_a_3562_; lean_object* v_a_3569_; 
v___x_3560_ = lean_box(0);
v_a_3569_ = lean_array_uget(v_as_3545_, v_i_3547_);
if (lean_obj_tag(v_a_3569_) == 0)
{
v_a_3562_ = v_snd_3556_;
goto v___jp_3561_;
}
else
{
lean_object* v_val_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3608_; 
v_val_3570_ = lean_ctor_get(v_a_3569_, 0);
v_isSharedCheck_3608_ = !lean_is_exclusive(v_a_3569_);
if (v_isSharedCheck_3608_ == 0)
{
v___x_3572_ = v_a_3569_;
v_isShared_3573_ = v_isSharedCheck_3608_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_val_3570_);
lean_dec(v_a_3569_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3608_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3574_ = l_Lean_LocalDecl_fvarId(v_val_3570_);
lean_dec(v_val_3570_);
lean_inc(v___y_3552_);
lean_inc_ref(v___y_3551_);
lean_inc(v___y_3550_);
lean_inc_ref(v___y_3549_);
lean_inc(v_mvarId_3544_);
v___x_3575_ = l_Lean_Meta_subst_x3f(v_mvarId_3544_, v___x_3574_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
if (lean_obj_tag(v___x_3575_) == 0)
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3599_; 
v_a_3576_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3578_ = v___x_3575_;
v_isShared_3579_ = v_isSharedCheck_3599_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3575_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3599_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; 
v___x_3580_ = lean_box(0);
if (lean_obj_tag(v_a_3576_) == 1)
{
lean_object* v___x_3582_; 
lean_del_object(v___x_3558_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v_mvarId_3544_);
lean_inc_ref(v_a_3576_);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v_a_3576_);
v___x_3582_ = v___x_3572_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v_a_3576_);
v___x_3582_ = v_reuseFailAlloc_3597_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3595_; 
v_isSharedCheck_3595_ = !lean_is_exclusive(v_a_3576_);
if (v_isSharedCheck_3595_ == 0)
{
lean_object* v_unused_3596_; 
v_unused_3596_ = lean_ctor_get(v_a_3576_, 0);
lean_dec(v_unused_3596_);
v___x_3584_ = v_a_3576_;
v_isShared_3585_ = v_isSharedCheck_3595_;
goto v_resetjp_3583_;
}
else
{
lean_dec(v_a_3576_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3595_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3586_; lean_object* v___x_3588_; 
v___x_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3582_);
lean_ctor_set(v___x_3586_, 1, v___x_3580_);
if (v_isShared_3585_ == 0)
{
lean_ctor_set_tag(v___x_3584_, 0);
lean_ctor_set(v___x_3584_, 0, v___x_3586_);
v___x_3588_ = v___x_3584_;
goto v_reusejp_3587_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v___x_3586_);
v___x_3588_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3587_;
}
v_reusejp_3587_:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3589_);
lean_ctor_set(v___x_3590_, 1, v_snd_3556_);
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 0, v___x_3590_);
v___x_3592_ = v___x_3578_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3593_; 
v_reuseFailAlloc_3593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3593_, 0, v___x_3590_);
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
}
else
{
lean_object* v___x_3598_; 
lean_del_object(v___x_3578_);
lean_dec(v_a_3576_);
lean_del_object(v___x_3572_);
lean_dec(v_snd_3556_);
v___x_3598_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3562_ = v___x_3598_;
goto v___jp_3561_;
}
}
}
else
{
lean_object* v_a_3600_; lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3607_; 
lean_del_object(v___x_3572_);
lean_del_object(v___x_3558_);
lean_dec(v_snd_3556_);
lean_dec(v___y_3552_);
lean_dec_ref(v___y_3551_);
lean_dec(v___y_3550_);
lean_dec_ref(v___y_3549_);
lean_dec(v_mvarId_3544_);
v_a_3600_ = lean_ctor_get(v___x_3575_, 0);
v_isSharedCheck_3607_ = !lean_is_exclusive(v___x_3575_);
if (v_isSharedCheck_3607_ == 0)
{
v___x_3602_ = v___x_3575_;
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
else
{
lean_inc(v_a_3600_);
lean_dec(v___x_3575_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3607_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3605_; 
if (v_isShared_3603_ == 0)
{
v___x_3605_ = v___x_3602_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3606_; 
v_reuseFailAlloc_3606_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3606_, 0, v_a_3600_);
v___x_3605_ = v_reuseFailAlloc_3606_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
return v___x_3605_;
}
}
}
}
}
v___jp_3561_:
{
lean_object* v___x_3564_; 
if (v_isShared_3559_ == 0)
{
lean_ctor_set(v___x_3558_, 1, v_a_3562_);
lean_ctor_set(v___x_3558_, 0, v___x_3560_);
v___x_3564_ = v___x_3558_;
goto v_reusejp_3563_;
}
else
{
lean_object* v_reuseFailAlloc_3568_; 
v_reuseFailAlloc_3568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3568_, 0, v___x_3560_);
lean_ctor_set(v_reuseFailAlloc_3568_, 1, v_a_3562_);
v___x_3564_ = v_reuseFailAlloc_3568_;
goto v_reusejp_3563_;
}
v_reusejp_3563_:
{
size_t v___x_3565_; size_t v___x_3566_; 
v___x_3565_ = ((size_t)1ULL);
v___x_3566_ = lean_usize_add(v_i_3547_, v___x_3565_);
v_i_3547_ = v___x_3566_;
v_b_3548_ = v___x_3564_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_mvarId_3611_, lean_object* v_as_3612_, lean_object* v_sz_3613_, lean_object* v_i_3614_, lean_object* v_b_3615_, lean_object* v___y_3616_, lean_object* v___y_3617_, lean_object* v___y_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_){
_start:
{
size_t v_sz_boxed_3621_; size_t v_i_boxed_3622_; lean_object* v_res_3623_; 
v_sz_boxed_3621_ = lean_unbox_usize(v_sz_3613_);
lean_dec(v_sz_3613_);
v_i_boxed_3622_ = lean_unbox_usize(v_i_3614_);
lean_dec(v_i_3614_);
v_res_3623_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3611_, v_as_3612_, v_sz_boxed_3621_, v_i_boxed_3622_, v_b_3615_, v___y_3616_, v___y_3617_, v___y_3618_, v___y_3619_);
lean_dec_ref(v_as_3612_);
return v_res_3623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object* v_mvarId_3624_, lean_object* v_as_3625_, size_t v_sz_3626_, size_t v_i_3627_, lean_object* v_b_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_){
_start:
{
uint8_t v___x_3634_; 
v___x_3634_ = lean_usize_dec_lt(v_i_3627_, v_sz_3626_);
if (v___x_3634_ == 0)
{
lean_object* v___x_3635_; 
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v_mvarId_3624_);
v___x_3635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3635_, 0, v_b_3628_);
return v___x_3635_;
}
else
{
lean_object* v_snd_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3689_; 
v_snd_3636_ = lean_ctor_get(v_b_3628_, 1);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_b_3628_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v_b_3628_, 0);
lean_dec(v_unused_3690_);
v___x_3638_ = v_b_3628_;
v_isShared_3639_ = v_isSharedCheck_3689_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_snd_3636_);
lean_dec(v_b_3628_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3689_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3640_; lean_object* v_a_3642_; lean_object* v_a_3649_; 
v___x_3640_ = lean_box(0);
v_a_3649_ = lean_array_uget(v_as_3625_, v_i_3627_);
if (lean_obj_tag(v_a_3649_) == 0)
{
v_a_3642_ = v_snd_3636_;
goto v___jp_3641_;
}
else
{
lean_object* v_val_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3688_; 
v_val_3650_ = lean_ctor_get(v_a_3649_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v_a_3649_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3652_ = v_a_3649_;
v_isShared_3653_ = v_isSharedCheck_3688_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_val_3650_);
lean_dec(v_a_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3688_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v___x_3655_; 
v___x_3654_ = l_Lean_LocalDecl_fvarId(v_val_3650_);
lean_dec(v_val_3650_);
lean_inc(v___y_3632_);
lean_inc_ref(v___y_3631_);
lean_inc(v___y_3630_);
lean_inc_ref(v___y_3629_);
lean_inc(v_mvarId_3624_);
v___x_3655_ = l_Lean_Meta_subst_x3f(v_mvarId_3624_, v___x_3654_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
if (lean_obj_tag(v___x_3655_) == 0)
{
lean_object* v_a_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3679_; 
v_a_3656_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3658_ = v___x_3655_;
v_isShared_3659_ = v_isSharedCheck_3679_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_a_3656_);
lean_dec(v___x_3655_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3679_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; 
v___x_3660_ = lean_box(0);
if (lean_obj_tag(v_a_3656_) == 1)
{
lean_object* v___x_3662_; 
lean_del_object(v___x_3638_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v_mvarId_3624_);
lean_inc_ref(v_a_3656_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v_a_3656_);
v___x_3662_ = v___x_3652_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3656_);
v___x_3662_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3675_; 
v_isSharedCheck_3675_ = !lean_is_exclusive(v_a_3656_);
if (v_isSharedCheck_3675_ == 0)
{
lean_object* v_unused_3676_; 
v_unused_3676_ = lean_ctor_get(v_a_3656_, 0);
lean_dec(v_unused_3676_);
v___x_3664_ = v_a_3656_;
v_isShared_3665_ = v_isSharedCheck_3675_;
goto v_resetjp_3663_;
}
else
{
lean_dec(v_a_3656_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3675_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3666_; lean_object* v___x_3668_; 
v___x_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3666_, 0, v___x_3662_);
lean_ctor_set(v___x_3666_, 1, v___x_3660_);
if (v_isShared_3665_ == 0)
{
lean_ctor_set_tag(v___x_3664_, 0);
lean_ctor_set(v___x_3664_, 0, v___x_3666_);
v___x_3668_ = v___x_3664_;
goto v_reusejp_3667_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v___x_3666_);
v___x_3668_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3667_;
}
v_reusejp_3667_:
{
lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
v___x_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3669_);
lean_ctor_set(v___x_3670_, 1, v_snd_3636_);
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 0, v___x_3670_);
v___x_3672_ = v___x_3658_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
}
else
{
lean_object* v___x_3678_; 
lean_del_object(v___x_3658_);
lean_dec(v_a_3656_);
lean_del_object(v___x_3652_);
lean_dec(v_snd_3636_);
v___x_3678_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3642_ = v___x_3678_;
goto v___jp_3641_;
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_del_object(v___x_3652_);
lean_del_object(v___x_3638_);
lean_dec(v_snd_3636_);
lean_dec(v___y_3632_);
lean_dec_ref(v___y_3631_);
lean_dec(v___y_3630_);
lean_dec_ref(v___y_3629_);
lean_dec(v_mvarId_3624_);
v_a_3680_ = lean_ctor_get(v___x_3655_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3655_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3655_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3655_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
}
v___jp_3641_:
{
lean_object* v___x_3644_; 
if (v_isShared_3639_ == 0)
{
lean_ctor_set(v___x_3638_, 1, v_a_3642_);
lean_ctor_set(v___x_3638_, 0, v___x_3640_);
v___x_3644_ = v___x_3638_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3648_; 
v_reuseFailAlloc_3648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3648_, 0, v___x_3640_);
lean_ctor_set(v_reuseFailAlloc_3648_, 1, v_a_3642_);
v___x_3644_ = v_reuseFailAlloc_3648_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
size_t v___x_3645_; size_t v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = ((size_t)1ULL);
v___x_3646_ = lean_usize_add(v_i_3627_, v___x_3645_);
v___x_3647_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3624_, v_as_3625_, v_sz_3626_, v___x_3646_, v___x_3644_, v___y_3629_, v___y_3630_, v___y_3631_, v___y_3632_);
return v___x_3647_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_3691_, lean_object* v_as_3692_, lean_object* v_sz_3693_, lean_object* v_i_3694_, lean_object* v_b_3695_, lean_object* v___y_3696_, lean_object* v___y_3697_, lean_object* v___y_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_){
_start:
{
size_t v_sz_boxed_3701_; size_t v_i_boxed_3702_; lean_object* v_res_3703_; 
v_sz_boxed_3701_ = lean_unbox_usize(v_sz_3693_);
lean_dec(v_sz_3693_);
v_i_boxed_3702_ = lean_unbox_usize(v_i_3694_);
lean_dec(v_i_3694_);
v_res_3703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3691_, v_as_3692_, v_sz_boxed_3701_, v_i_boxed_3702_, v_b_3695_, v___y_3696_, v___y_3697_, v___y_3698_, v___y_3699_);
lean_dec_ref(v_as_3692_);
return v_res_3703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* v_mvarId_3704_, lean_object* v_inh_3705_, lean_object* v_n_3706_, lean_object* v_b_3707_, lean_object* v___y_3708_, lean_object* v___y_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_){
_start:
{
if (lean_obj_tag(v_n_3706_) == 0)
{
lean_object* v_cs_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3747_; 
v_cs_3713_ = lean_ctor_get(v_n_3706_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v_n_3706_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3715_ = v_n_3706_;
v_isShared_3716_ = v_isSharedCheck_3747_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_cs_3713_);
lean_dec(v_n_3706_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3747_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; size_t v_sz_3719_; size_t v___x_3720_; lean_object* v___x_3721_; 
v___x_3717_ = lean_box(0);
v___x_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
lean_ctor_set(v___x_3718_, 1, v_b_3707_);
v_sz_3719_ = lean_array_size(v_cs_3713_);
v___x_3720_ = ((size_t)0ULL);
v___x_3721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_mvarId_3704_, v_inh_3705_, v_cs_3713_, v_sz_3719_, v___x_3720_, v___x_3718_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec_ref(v_cs_3713_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3738_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3724_ = v___x_3721_;
v_isShared_3725_ = v_isSharedCheck_3738_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3738_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v_fst_3726_; 
v_fst_3726_ = lean_ctor_get(v_a_3722_, 0);
if (lean_obj_tag(v_fst_3726_) == 0)
{
lean_object* v_snd_3727_; lean_object* v___x_3729_; 
v_snd_3727_ = lean_ctor_get(v_a_3722_, 1);
lean_inc(v_snd_3727_);
lean_dec(v_a_3722_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set_tag(v___x_3715_, 1);
lean_ctor_set(v___x_3715_, 0, v_snd_3727_);
v___x_3729_ = v___x_3715_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_snd_3727_);
v___x_3729_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
lean_object* v___x_3731_; 
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3729_);
v___x_3731_ = v___x_3724_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v___x_3729_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
else
{
lean_object* v_val_3734_; lean_object* v___x_3736_; 
lean_inc_ref(v_fst_3726_);
lean_dec(v_a_3722_);
lean_del_object(v___x_3715_);
v_val_3734_ = lean_ctor_get(v_fst_3726_, 0);
lean_inc(v_val_3734_);
lean_dec_ref(v_fst_3726_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v_val_3734_);
v___x_3736_ = v___x_3724_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_val_3734_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
else
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3746_; 
lean_del_object(v___x_3715_);
v_a_3739_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3746_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3746_ == 0)
{
v___x_3741_ = v___x_3721_;
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3721_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3746_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3744_; 
if (v_isShared_3742_ == 0)
{
v___x_3744_ = v___x_3741_;
goto v_reusejp_3743_;
}
else
{
lean_object* v_reuseFailAlloc_3745_; 
v_reuseFailAlloc_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3745_, 0, v_a_3739_);
v___x_3744_ = v_reuseFailAlloc_3745_;
goto v_reusejp_3743_;
}
v_reusejp_3743_:
{
return v___x_3744_;
}
}
}
}
}
else
{
lean_object* v_vs_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3782_; 
v_vs_3748_ = lean_ctor_get(v_n_3706_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v_n_3706_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3750_ = v_n_3706_;
v_isShared_3751_ = v_isSharedCheck_3782_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_vs_3748_);
lean_dec(v_n_3706_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3782_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3752_; lean_object* v___x_3753_; size_t v_sz_3754_; size_t v___x_3755_; lean_object* v___x_3756_; 
v___x_3752_ = lean_box(0);
v___x_3753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3753_, 0, v___x_3752_);
lean_ctor_set(v___x_3753_, 1, v_b_3707_);
v_sz_3754_ = lean_array_size(v_vs_3748_);
v___x_3755_ = ((size_t)0ULL);
v___x_3756_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3704_, v_vs_3748_, v_sz_3754_, v___x_3755_, v___x_3753_, v___y_3708_, v___y_3709_, v___y_3710_, v___y_3711_);
lean_dec_ref(v_vs_3748_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3759_; uint8_t v_isShared_3760_; uint8_t v_isSharedCheck_3773_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3759_ = v___x_3756_;
v_isShared_3760_ = v_isSharedCheck_3773_;
goto v_resetjp_3758_;
}
else
{
lean_inc(v_a_3757_);
lean_dec(v___x_3756_);
v___x_3759_ = lean_box(0);
v_isShared_3760_ = v_isSharedCheck_3773_;
goto v_resetjp_3758_;
}
v_resetjp_3758_:
{
lean_object* v_fst_3761_; 
v_fst_3761_ = lean_ctor_get(v_a_3757_, 0);
if (lean_obj_tag(v_fst_3761_) == 0)
{
lean_object* v_snd_3762_; lean_object* v___x_3764_; 
v_snd_3762_ = lean_ctor_get(v_a_3757_, 1);
lean_inc(v_snd_3762_);
lean_dec(v_a_3757_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v_snd_3762_);
v___x_3764_ = v___x_3750_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3768_; 
v_reuseFailAlloc_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3768_, 0, v_snd_3762_);
v___x_3764_ = v_reuseFailAlloc_3768_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3766_; 
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v___x_3764_);
v___x_3766_ = v___x_3759_;
goto v_reusejp_3765_;
}
else
{
lean_object* v_reuseFailAlloc_3767_; 
v_reuseFailAlloc_3767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3767_, 0, v___x_3764_);
v___x_3766_ = v_reuseFailAlloc_3767_;
goto v_reusejp_3765_;
}
v_reusejp_3765_:
{
return v___x_3766_;
}
}
}
else
{
lean_object* v_val_3769_; lean_object* v___x_3771_; 
lean_inc_ref(v_fst_3761_);
lean_dec(v_a_3757_);
lean_del_object(v___x_3750_);
v_val_3769_ = lean_ctor_get(v_fst_3761_, 0);
lean_inc(v_val_3769_);
lean_dec_ref(v_fst_3761_);
if (v_isShared_3760_ == 0)
{
lean_ctor_set(v___x_3759_, 0, v_val_3769_);
v___x_3771_ = v___x_3759_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_val_3769_);
v___x_3771_ = v_reuseFailAlloc_3772_;
goto v_reusejp_3770_;
}
v_reusejp_3770_:
{
return v___x_3771_;
}
}
}
}
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
lean_del_object(v___x_3750_);
v_a_3774_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3756_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3756_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_mvarId_3783_, lean_object* v_inh_3784_, lean_object* v_as_3785_, size_t v_sz_3786_, size_t v_i_3787_, lean_object* v_b_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_){
_start:
{
uint8_t v___x_3794_; 
v___x_3794_ = lean_usize_dec_lt(v_i_3787_, v_sz_3786_);
if (v___x_3794_ == 0)
{
lean_object* v___x_3795_; 
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v_mvarId_3783_);
v___x_3795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3795_, 0, v_b_3788_);
return v___x_3795_;
}
else
{
lean_object* v_snd_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3830_; 
v_snd_3796_ = lean_ctor_get(v_b_3788_, 1);
v_isSharedCheck_3830_ = !lean_is_exclusive(v_b_3788_);
if (v_isSharedCheck_3830_ == 0)
{
lean_object* v_unused_3831_; 
v_unused_3831_ = lean_ctor_get(v_b_3788_, 0);
lean_dec(v_unused_3831_);
v___x_3798_ = v_b_3788_;
v_isShared_3799_ = v_isSharedCheck_3830_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_snd_3796_);
lean_dec(v_b_3788_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3830_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v_a_3800_; lean_object* v___x_3801_; 
v_a_3800_ = lean_array_uget_borrowed(v_as_3785_, v_i_3787_);
lean_inc(v___y_3792_);
lean_inc_ref(v___y_3791_);
lean_inc(v___y_3790_);
lean_inc_ref(v___y_3789_);
lean_inc(v_snd_3796_);
lean_inc(v_a_3800_);
lean_inc(v_mvarId_3783_);
v___x_3801_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_mvarId_3783_, v_inh_3784_, v_a_3800_, v_snd_3796_, v___y_3789_, v___y_3790_, v___y_3791_, v___y_3792_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3821_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3821_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3821_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
if (lean_obj_tag(v_a_3802_) == 0)
{
lean_object* v___x_3806_; lean_object* v___x_3808_; 
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v_mvarId_3783_);
v___x_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3806_, 0, v_a_3802_);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 0, v___x_3806_);
v___x_3808_ = v___x_3798_;
goto v_reusejp_3807_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3806_);
lean_ctor_set(v_reuseFailAlloc_3812_, 1, v_snd_3796_);
v___x_3808_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3807_;
}
v_reusejp_3807_:
{
lean_object* v___x_3810_; 
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3808_);
v___x_3810_ = v___x_3804_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
return v___x_3810_;
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3814_; lean_object* v___x_3816_; 
lean_del_object(v___x_3804_);
lean_dec(v_snd_3796_);
v_a_3813_ = lean_ctor_get(v_a_3802_, 0);
lean_inc(v_a_3813_);
lean_dec_ref(v_a_3802_);
v___x_3814_ = lean_box(0);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 1, v_a_3813_);
lean_ctor_set(v___x_3798_, 0, v___x_3814_);
v___x_3816_ = v___x_3798_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3814_);
lean_ctor_set(v_reuseFailAlloc_3820_, 1, v_a_3813_);
v___x_3816_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
size_t v___x_3817_; size_t v___x_3818_; 
v___x_3817_ = ((size_t)1ULL);
v___x_3818_ = lean_usize_add(v_i_3787_, v___x_3817_);
v_i_3787_ = v___x_3818_;
v_b_3788_ = v___x_3816_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_del_object(v___x_3798_);
lean_dec(v_snd_3796_);
lean_dec(v___y_3792_);
lean_dec_ref(v___y_3791_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v_mvarId_3783_);
v_a_3822_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3801_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3801_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_mvarId_3832_, lean_object* v_inh_3833_, lean_object* v_as_3834_, lean_object* v_sz_3835_, lean_object* v_i_3836_, lean_object* v_b_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_){
_start:
{
size_t v_sz_boxed_3843_; size_t v_i_boxed_3844_; lean_object* v_res_3845_; 
v_sz_boxed_3843_ = lean_unbox_usize(v_sz_3835_);
lean_dec(v_sz_3835_);
v_i_boxed_3844_ = lean_unbox_usize(v_i_3836_);
lean_dec(v_i_3836_);
v_res_3845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_mvarId_3832_, v_inh_3833_, v_as_3834_, v_sz_boxed_3843_, v_i_boxed_3844_, v_b_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_);
lean_dec_ref(v_as_3834_);
lean_dec_ref(v_inh_3833_);
return v_res_3845_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_mvarId_3846_, lean_object* v_inh_3847_, lean_object* v_n_3848_, lean_object* v_b_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_){
_start:
{
lean_object* v_res_3855_; 
v_res_3855_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_mvarId_3846_, v_inh_3847_, v_n_3848_, v_b_3849_, v___y_3850_, v___y_3851_, v___y_3852_, v___y_3853_);
lean_dec_ref(v_inh_3847_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3859_, lean_object* v_as_3860_, size_t v_sz_3861_, size_t v_i_3862_, lean_object* v_b_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
uint8_t v___x_3869_; 
v___x_3869_ = lean_usize_dec_lt(v_i_3862_, v_sz_3861_);
if (v___x_3869_ == 0)
{
lean_object* v___x_3870_; 
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v_mvarId_3859_);
v___x_3870_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3870_, 0, v_b_3863_);
return v___x_3870_;
}
else
{
lean_object* v_snd_3871_; lean_object* v___x_3873_; uint8_t v_isShared_3874_; uint8_t v_isSharedCheck_3923_; 
v_snd_3871_ = lean_ctor_get(v_b_3863_, 1);
v_isSharedCheck_3923_ = !lean_is_exclusive(v_b_3863_);
if (v_isSharedCheck_3923_ == 0)
{
lean_object* v_unused_3924_; 
v_unused_3924_ = lean_ctor_get(v_b_3863_, 0);
lean_dec(v_unused_3924_);
v___x_3873_ = v_b_3863_;
v_isShared_3874_ = v_isSharedCheck_3923_;
goto v_resetjp_3872_;
}
else
{
lean_inc(v_snd_3871_);
lean_dec(v_b_3863_);
v___x_3873_ = lean_box(0);
v_isShared_3874_ = v_isSharedCheck_3923_;
goto v_resetjp_3872_;
}
v_resetjp_3872_:
{
lean_object* v___x_3875_; lean_object* v_a_3877_; lean_object* v_a_3884_; 
v___x_3875_ = lean_box(0);
v_a_3884_ = lean_array_uget(v_as_3860_, v_i_3862_);
if (lean_obj_tag(v_a_3884_) == 0)
{
v_a_3877_ = v_snd_3871_;
goto v___jp_3876_;
}
else
{
lean_object* v_val_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3922_; 
v_val_3885_ = lean_ctor_get(v_a_3884_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v_a_3884_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3887_ = v_a_3884_;
v_isShared_3888_ = v_isSharedCheck_3922_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_val_3885_);
lean_dec(v_a_3884_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3922_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3889_; lean_object* v___x_3890_; 
v___x_3889_ = l_Lean_LocalDecl_fvarId(v_val_3885_);
lean_dec(v_val_3885_);
lean_inc(v___y_3867_);
lean_inc_ref(v___y_3866_);
lean_inc(v___y_3865_);
lean_inc_ref(v___y_3864_);
lean_inc(v_mvarId_3859_);
v___x_3890_ = l_Lean_Meta_subst_x3f(v_mvarId_3859_, v___x_3889_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3913_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3893_ = v___x_3890_;
v_isShared_3894_ = v_isSharedCheck_3913_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_a_3891_);
lean_dec(v___x_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3913_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3895_; 
v___x_3895_ = lean_box(0);
if (lean_obj_tag(v_a_3891_) == 1)
{
lean_object* v___x_3897_; 
lean_del_object(v___x_3873_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v_mvarId_3859_);
lean_inc_ref(v_a_3891_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v_a_3891_);
v___x_3897_ = v___x_3887_;
goto v_reusejp_3896_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3891_);
v___x_3897_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3896_;
}
v_reusejp_3896_:
{
lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3909_; 
v_isSharedCheck_3909_ = !lean_is_exclusive(v_a_3891_);
if (v_isSharedCheck_3909_ == 0)
{
lean_object* v_unused_3910_; 
v_unused_3910_ = lean_ctor_get(v_a_3891_, 0);
lean_dec(v_unused_3910_);
v___x_3899_ = v_a_3891_;
v_isShared_3900_ = v_isSharedCheck_3909_;
goto v_resetjp_3898_;
}
else
{
lean_dec(v_a_3891_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3909_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; lean_object* v___x_3903_; 
v___x_3901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3897_);
lean_ctor_set(v___x_3901_, 1, v___x_3895_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3901_);
v___x_3903_ = v___x_3899_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3908_; 
v_reuseFailAlloc_3908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3908_, 0, v___x_3901_);
v___x_3903_ = v_reuseFailAlloc_3908_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3904_; lean_object* v___x_3906_; 
v___x_3904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
lean_ctor_set(v___x_3904_, 1, v_snd_3871_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v___x_3904_);
v___x_3906_ = v___x_3893_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3907_; 
v_reuseFailAlloc_3907_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3907_, 0, v___x_3904_);
v___x_3906_ = v_reuseFailAlloc_3907_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
return v___x_3906_;
}
}
}
}
}
else
{
lean_object* v___x_3912_; 
lean_del_object(v___x_3893_);
lean_dec(v_a_3891_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3871_);
v___x_3912_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3877_ = v___x_3912_;
goto v___jp_3876_;
}
}
}
else
{
lean_object* v_a_3914_; lean_object* v___x_3916_; uint8_t v_isShared_3917_; uint8_t v_isSharedCheck_3921_; 
lean_del_object(v___x_3887_);
lean_del_object(v___x_3873_);
lean_dec(v_snd_3871_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec(v_mvarId_3859_);
v_a_3914_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3916_ = v___x_3890_;
v_isShared_3917_ = v_isSharedCheck_3921_;
goto v_resetjp_3915_;
}
else
{
lean_inc(v_a_3914_);
lean_dec(v___x_3890_);
v___x_3916_ = lean_box(0);
v_isShared_3917_ = v_isSharedCheck_3921_;
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
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3914_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
return v___x_3919_;
}
}
}
}
}
v___jp_3876_:
{
lean_object* v___x_3879_; 
if (v_isShared_3874_ == 0)
{
lean_ctor_set(v___x_3873_, 1, v_a_3877_);
lean_ctor_set(v___x_3873_, 0, v___x_3875_);
v___x_3879_ = v___x_3873_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3875_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_a_3877_);
v___x_3879_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
size_t v___x_3880_; size_t v___x_3881_; 
v___x_3880_ = ((size_t)1ULL);
v___x_3881_ = lean_usize_add(v_i_3862_, v___x_3880_);
v_i_3862_ = v___x_3881_;
v_b_3863_ = v___x_3879_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3925_, lean_object* v_as_3926_, lean_object* v_sz_3927_, lean_object* v_i_3928_, lean_object* v_b_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_){
_start:
{
size_t v_sz_boxed_3935_; size_t v_i_boxed_3936_; lean_object* v_res_3937_; 
v_sz_boxed_3935_ = lean_unbox_usize(v_sz_3927_);
lean_dec(v_sz_3927_);
v_i_boxed_3936_ = lean_unbox_usize(v_i_3928_);
lean_dec(v_i_3928_);
v_res_3937_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3925_, v_as_3926_, v_sz_boxed_3935_, v_i_boxed_3936_, v_b_3929_, v___y_3930_, v___y_3931_, v___y_3932_, v___y_3933_);
lean_dec_ref(v_as_3926_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_3938_, lean_object* v_as_3939_, size_t v_sz_3940_, size_t v_i_3941_, lean_object* v_b_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
uint8_t v___x_3948_; 
v___x_3948_ = lean_usize_dec_lt(v_i_3941_, v_sz_3940_);
if (v___x_3948_ == 0)
{
lean_object* v___x_3949_; 
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v_mvarId_3938_);
v___x_3949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3949_, 0, v_b_3942_);
return v___x_3949_;
}
else
{
lean_object* v_snd_3950_; lean_object* v___x_3952_; uint8_t v_isShared_3953_; uint8_t v_isSharedCheck_4002_; 
v_snd_3950_ = lean_ctor_get(v_b_3942_, 1);
v_isSharedCheck_4002_ = !lean_is_exclusive(v_b_3942_);
if (v_isSharedCheck_4002_ == 0)
{
lean_object* v_unused_4003_; 
v_unused_4003_ = lean_ctor_get(v_b_3942_, 0);
lean_dec(v_unused_4003_);
v___x_3952_ = v_b_3942_;
v_isShared_3953_ = v_isSharedCheck_4002_;
goto v_resetjp_3951_;
}
else
{
lean_inc(v_snd_3950_);
lean_dec(v_b_3942_);
v___x_3952_ = lean_box(0);
v_isShared_3953_ = v_isSharedCheck_4002_;
goto v_resetjp_3951_;
}
v_resetjp_3951_:
{
lean_object* v___x_3954_; lean_object* v_a_3956_; lean_object* v_a_3963_; 
v___x_3954_ = lean_box(0);
v_a_3963_ = lean_array_uget(v_as_3939_, v_i_3941_);
if (lean_obj_tag(v_a_3963_) == 0)
{
v_a_3956_ = v_snd_3950_;
goto v___jp_3955_;
}
else
{
lean_object* v_val_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_4001_; 
v_val_3964_ = lean_ctor_get(v_a_3963_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v_a_3963_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3966_ = v_a_3963_;
v_isShared_3967_ = v_isSharedCheck_4001_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_val_3964_);
lean_dec(v_a_3963_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_4001_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3968_; lean_object* v___x_3969_; 
v___x_3968_ = l_Lean_LocalDecl_fvarId(v_val_3964_);
lean_dec(v_val_3964_);
lean_inc(v___y_3946_);
lean_inc_ref(v___y_3945_);
lean_inc(v___y_3944_);
lean_inc_ref(v___y_3943_);
lean_inc(v_mvarId_3938_);
v___x_3969_ = l_Lean_Meta_subst_x3f(v_mvarId_3938_, v___x_3968_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3992_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3972_ = v___x_3969_;
v_isShared_3973_ = v_isSharedCheck_3992_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3992_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; 
v___x_3974_ = lean_box(0);
if (lean_obj_tag(v_a_3970_) == 1)
{
lean_object* v___x_3976_; 
lean_del_object(v___x_3952_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v_mvarId_3938_);
lean_inc_ref(v_a_3970_);
if (v_isShared_3967_ == 0)
{
lean_ctor_set(v___x_3966_, 0, v_a_3970_);
v___x_3976_ = v___x_3966_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3970_);
v___x_3976_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3988_; 
v_isSharedCheck_3988_ = !lean_is_exclusive(v_a_3970_);
if (v_isSharedCheck_3988_ == 0)
{
lean_object* v_unused_3989_; 
v_unused_3989_ = lean_ctor_get(v_a_3970_, 0);
lean_dec(v_unused_3989_);
v___x_3978_ = v_a_3970_;
v_isShared_3979_ = v_isSharedCheck_3988_;
goto v_resetjp_3977_;
}
else
{
lean_dec(v_a_3970_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3988_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3980_; lean_object* v___x_3982_; 
v___x_3980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3980_, 0, v___x_3976_);
lean_ctor_set(v___x_3980_, 1, v___x_3974_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v___x_3980_);
v___x_3982_ = v___x_3978_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v___x_3980_);
v___x_3982_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3983_; lean_object* v___x_3985_; 
v___x_3983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3983_, 0, v___x_3982_);
lean_ctor_set(v___x_3983_, 1, v_snd_3950_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v___x_3983_);
v___x_3985_ = v___x_3972_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v___x_3983_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
}
else
{
lean_object* v___x_3991_; 
lean_del_object(v___x_3972_);
lean_dec(v_a_3970_);
lean_del_object(v___x_3966_);
lean_dec(v_snd_3950_);
v___x_3991_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3956_ = v___x_3991_;
goto v___jp_3955_;
}
}
}
else
{
lean_object* v_a_3993_; lean_object* v___x_3995_; uint8_t v_isShared_3996_; uint8_t v_isSharedCheck_4000_; 
lean_del_object(v___x_3966_);
lean_del_object(v___x_3952_);
lean_dec(v_snd_3950_);
lean_dec(v___y_3946_);
lean_dec_ref(v___y_3945_);
lean_dec(v___y_3944_);
lean_dec_ref(v___y_3943_);
lean_dec(v_mvarId_3938_);
v_a_3993_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3995_ = v___x_3969_;
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
else
{
lean_inc(v_a_3993_);
lean_dec(v___x_3969_);
v___x_3995_ = lean_box(0);
v_isShared_3996_ = v_isSharedCheck_4000_;
goto v_resetjp_3994_;
}
v_resetjp_3994_:
{
lean_object* v___x_3998_; 
if (v_isShared_3996_ == 0)
{
v___x_3998_ = v___x_3995_;
goto v_reusejp_3997_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3993_);
v___x_3998_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3997_;
}
v_reusejp_3997_:
{
return v___x_3998_;
}
}
}
}
}
v___jp_3955_:
{
lean_object* v___x_3958_; 
if (v_isShared_3953_ == 0)
{
lean_ctor_set(v___x_3952_, 1, v_a_3956_);
lean_ctor_set(v___x_3952_, 0, v___x_3954_);
v___x_3958_ = v___x_3952_;
goto v_reusejp_3957_;
}
else
{
lean_object* v_reuseFailAlloc_3962_; 
v_reuseFailAlloc_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3962_, 0, v___x_3954_);
lean_ctor_set(v_reuseFailAlloc_3962_, 1, v_a_3956_);
v___x_3958_ = v_reuseFailAlloc_3962_;
goto v_reusejp_3957_;
}
v_reusejp_3957_:
{
size_t v___x_3959_; size_t v___x_3960_; lean_object* v___x_3961_; 
v___x_3959_ = ((size_t)1ULL);
v___x_3960_ = lean_usize_add(v_i_3941_, v___x_3959_);
v___x_3961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3938_, v_as_3939_, v_sz_3940_, v___x_3960_, v___x_3958_, v___y_3943_, v___y_3944_, v___y_3945_, v___y_3946_);
return v___x_3961_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_4004_, lean_object* v_as_4005_, lean_object* v_sz_4006_, lean_object* v_i_4007_, lean_object* v_b_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
size_t v_sz_boxed_4014_; size_t v_i_boxed_4015_; lean_object* v_res_4016_; 
v_sz_boxed_4014_ = lean_unbox_usize(v_sz_4006_);
lean_dec(v_sz_4006_);
v_i_boxed_4015_ = lean_unbox_usize(v_i_4007_);
lean_dec(v_i_4007_);
v_res_4016_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4004_, v_as_4005_, v_sz_boxed_4014_, v_i_boxed_4015_, v_b_4008_, v___y_4009_, v___y_4010_, v___y_4011_, v___y_4012_);
lean_dec_ref(v_as_4005_);
return v_res_4016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4017_, lean_object* v_t_4018_, lean_object* v_init_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
lean_object* v_root_4025_; lean_object* v_tail_4026_; lean_object* v___x_4027_; 
v_root_4025_ = lean_ctor_get(v_t_4018_, 0);
lean_inc_ref(v_root_4025_);
v_tail_4026_ = lean_ctor_get(v_t_4018_, 1);
lean_inc_ref(v_tail_4026_);
lean_dec_ref(v_t_4018_);
lean_inc(v___y_4023_);
lean_inc_ref(v___y_4022_);
lean_inc(v___y_4021_);
lean_inc_ref(v___y_4020_);
lean_inc_ref(v_init_4019_);
lean_inc(v_mvarId_4017_);
v___x_4027_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_mvarId_4017_, v_init_4019_, v_root_4025_, v_init_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec_ref(v_init_4019_);
if (lean_obj_tag(v___x_4027_) == 0)
{
lean_object* v_a_4028_; lean_object* v___x_4030_; uint8_t v_isShared_4031_; uint8_t v_isSharedCheck_4064_; 
v_a_4028_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4030_ = v___x_4027_;
v_isShared_4031_ = v_isSharedCheck_4064_;
goto v_resetjp_4029_;
}
else
{
lean_inc(v_a_4028_);
lean_dec(v___x_4027_);
v___x_4030_ = lean_box(0);
v_isShared_4031_ = v_isSharedCheck_4064_;
goto v_resetjp_4029_;
}
v_resetjp_4029_:
{
if (lean_obj_tag(v_a_4028_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4034_; 
lean_dec_ref(v_tail_4026_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v_mvarId_4017_);
v_a_4032_ = lean_ctor_get(v_a_4028_, 0);
lean_inc(v_a_4032_);
lean_dec_ref(v_a_4028_);
if (v_isShared_4031_ == 0)
{
lean_ctor_set(v___x_4030_, 0, v_a_4032_);
v___x_4034_ = v___x_4030_;
goto v_reusejp_4033_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4032_);
v___x_4034_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4033_;
}
v_reusejp_4033_:
{
return v___x_4034_;
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; size_t v_sz_4039_; size_t v___x_4040_; lean_object* v___x_4041_; 
lean_del_object(v___x_4030_);
v_a_4036_ = lean_ctor_get(v_a_4028_, 0);
lean_inc(v_a_4036_);
lean_dec_ref(v_a_4028_);
v___x_4037_ = lean_box(0);
v___x_4038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4038_, 0, v___x_4037_);
lean_ctor_set(v___x_4038_, 1, v_a_4036_);
v_sz_4039_ = lean_array_size(v_tail_4026_);
v___x_4040_ = ((size_t)0ULL);
v___x_4041_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4017_, v_tail_4026_, v_sz_4039_, v___x_4040_, v___x_4038_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
lean_dec_ref(v_tail_4026_);
if (lean_obj_tag(v___x_4041_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4055_; 
v_a_4042_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4044_ = v___x_4041_;
v_isShared_4045_ = v_isSharedCheck_4055_;
goto v_resetjp_4043_;
}
else
{
lean_inc(v_a_4042_);
lean_dec(v___x_4041_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4055_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v_fst_4046_; 
v_fst_4046_ = lean_ctor_get(v_a_4042_, 0);
if (lean_obj_tag(v_fst_4046_) == 0)
{
lean_object* v_snd_4047_; lean_object* v___x_4049_; 
v_snd_4047_ = lean_ctor_get(v_a_4042_, 1);
lean_inc(v_snd_4047_);
lean_dec(v_a_4042_);
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v_snd_4047_);
v___x_4049_ = v___x_4044_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_snd_4047_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
else
{
lean_object* v_val_4051_; lean_object* v___x_4053_; 
lean_inc_ref(v_fst_4046_);
lean_dec(v_a_4042_);
v_val_4051_ = lean_ctor_get(v_fst_4046_, 0);
lean_inc(v_val_4051_);
lean_dec_ref(v_fst_4046_);
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v_val_4051_);
v___x_4053_ = v___x_4044_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_val_4051_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
v_a_4056_ = lean_ctor_get(v___x_4041_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4041_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4041_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4041_);
v___x_4058_ = lean_box(0);
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
v_resetjp_4057_:
{
lean_object* v___x_4061_; 
if (v_isShared_4059_ == 0)
{
v___x_4061_ = v___x_4058_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_a_4056_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
return v___x_4061_;
}
}
}
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
lean_dec_ref(v_tail_4026_);
lean_dec(v___y_4023_);
lean_dec_ref(v___y_4022_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v_mvarId_4017_);
v_a_4065_ = lean_ctor_get(v___x_4027_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4027_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4027_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4027_);
v___x_4067_ = lean_box(0);
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
v_resetjp_4066_:
{
lean_object* v___x_4070_; 
if (v_isShared_4068_ == 0)
{
v___x_4070_ = v___x_4067_;
goto v_reusejp_4069_;
}
else
{
lean_object* v_reuseFailAlloc_4071_; 
v_reuseFailAlloc_4071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4071_, 0, v_a_4065_);
v___x_4070_ = v_reuseFailAlloc_4071_;
goto v_reusejp_4069_;
}
v_reusejp_4069_:
{
return v___x_4070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4073_, lean_object* v_t_4074_, lean_object* v_init_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_res_4081_; 
v_res_4081_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4073_, v_t_4074_, v_init_4075_, v___y_4076_, v___y_4077_, v___y_4078_, v___y_4079_);
return v_res_4081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_lctx_4091_; lean_object* v_decls_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v___x_4095_; 
v_lctx_4091_ = lean_ctor_get(v___y_4086_, 2);
v_decls_4092_ = lean_ctor_get(v_lctx_4091_, 1);
lean_inc_ref(v_decls_4092_);
v___x_4093_ = lean_box(0);
v___x_4094_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4095_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4085_, v_decls_4092_, v___x_4094_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4095_) == 0)
{
lean_object* v_a_4096_; lean_object* v___x_4098_; uint8_t v_isShared_4099_; uint8_t v_isSharedCheck_4108_; 
v_a_4096_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4098_ = v___x_4095_;
v_isShared_4099_ = v_isSharedCheck_4108_;
goto v_resetjp_4097_;
}
else
{
lean_inc(v_a_4096_);
lean_dec(v___x_4095_);
v___x_4098_ = lean_box(0);
v_isShared_4099_ = v_isSharedCheck_4108_;
goto v_resetjp_4097_;
}
v_resetjp_4097_:
{
lean_object* v_fst_4100_; 
v_fst_4100_ = lean_ctor_get(v_a_4096_, 0);
lean_inc(v_fst_4100_);
lean_dec(v_a_4096_);
if (lean_obj_tag(v_fst_4100_) == 0)
{
lean_object* v___x_4102_; 
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 0, v___x_4093_);
v___x_4102_ = v___x_4098_;
goto v_reusejp_4101_;
}
else
{
lean_object* v_reuseFailAlloc_4103_; 
v_reuseFailAlloc_4103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4103_, 0, v___x_4093_);
v___x_4102_ = v_reuseFailAlloc_4103_;
goto v_reusejp_4101_;
}
v_reusejp_4101_:
{
return v___x_4102_;
}
}
else
{
lean_object* v_val_4104_; lean_object* v___x_4106_; 
v_val_4104_ = lean_ctor_get(v_fst_4100_, 0);
lean_inc(v_val_4104_);
lean_dec_ref(v_fst_4100_);
if (v_isShared_4099_ == 0)
{
lean_ctor_set(v___x_4098_, 0, v_val_4104_);
v___x_4106_ = v___x_4098_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_val_4104_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
}
}
else
{
lean_object* v_a_4109_; lean_object* v___x_4111_; uint8_t v_isShared_4112_; uint8_t v_isSharedCheck_4116_; 
v_a_4109_ = lean_ctor_get(v___x_4095_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4095_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4111_ = v___x_4095_;
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
else
{
lean_inc(v_a_4109_);
lean_dec(v___x_4095_);
v___x_4111_ = lean_box(0);
v_isShared_4112_ = v_isSharedCheck_4116_;
goto v_resetjp_4110_;
}
v_resetjp_4110_:
{
lean_object* v___x_4114_; 
if (v_isShared_4112_ == 0)
{
v___x_4114_ = v___x_4111_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_a_4109_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_){
_start:
{
lean_object* v_res_4123_; 
v_res_4123_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_);
return v_res_4123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v___f_4130_; lean_object* v___x_4131_; 
lean_inc(v_mvarId_4124_);
v___f_4130_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4130_, 0, v_mvarId_4124_);
v___x_4131_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__8___redArg(v_mvarId_4124_, v___f_4130_, v_a_4125_, v_a_4126_, v_a_4127_, v_a_4128_);
return v___x_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v_res_4138_; 
v_res_4138_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4132_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_);
return v_res_4138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_){
_start:
{
lean_object* v___x_4145_; 
lean_inc(v_a_4143_);
lean_inc_ref(v_a_4142_);
lean_inc(v_a_4141_);
lean_inc_ref(v_a_4140_);
lean_inc(v_mvarId_4139_);
v___x_4145_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4139_, v_a_4140_, v_a_4141_, v_a_4142_, v_a_4143_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4148_; uint8_t v_isShared_4149_; uint8_t v_isSharedCheck_4155_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4155_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4155_ == 0)
{
v___x_4148_ = v___x_4145_;
v_isShared_4149_ = v_isSharedCheck_4155_;
goto v_resetjp_4147_;
}
else
{
lean_inc(v_a_4146_);
lean_dec(v___x_4145_);
v___x_4148_ = lean_box(0);
v_isShared_4149_ = v_isSharedCheck_4155_;
goto v_resetjp_4147_;
}
v_resetjp_4147_:
{
if (lean_obj_tag(v_a_4146_) == 1)
{
lean_object* v_val_4150_; 
lean_del_object(v___x_4148_);
lean_dec(v_mvarId_4139_);
v_val_4150_ = lean_ctor_get(v_a_4146_, 0);
lean_inc(v_val_4150_);
lean_dec_ref(v_a_4146_);
v_mvarId_4139_ = v_val_4150_;
goto _start;
}
else
{
lean_object* v___x_4153_; 
lean_dec(v_a_4146_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
if (v_isShared_4149_ == 0)
{
lean_ctor_set(v___x_4148_, 0, v_mvarId_4139_);
v___x_4153_ = v___x_4148_;
goto v_reusejp_4152_;
}
else
{
lean_object* v_reuseFailAlloc_4154_; 
v_reuseFailAlloc_4154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4154_, 0, v_mvarId_4139_);
v___x_4153_ = v_reuseFailAlloc_4154_;
goto v_reusejp_4152_;
}
v_reusejp_4152_:
{
return v___x_4153_;
}
}
}
}
else
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4163_; 
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
lean_dec(v_a_4141_);
lean_dec_ref(v_a_4140_);
lean_dec(v_mvarId_4139_);
v_a_4156_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4158_ = v___x_4145_;
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4145_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4163_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
lean_object* v___x_4161_; 
if (v_isShared_4159_ == 0)
{
v___x_4161_ = v___x_4158_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_a_4156_);
v___x_4161_ = v_reuseFailAlloc_4162_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
return v___x_4161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4164_, lean_object* v_a_4165_, lean_object* v_a_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_){
_start:
{
lean_object* v_res_4170_; 
v_res_4170_ = l_Lean_Meta_substVars(v_mvarId_4164_, v_a_4165_, v_a_4166_, v_a_4167_, v_a_4168_);
return v_res_4170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4233_; uint8_t v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; 
v___x_4233_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__22));
v___x_4234_ = 0;
v___x_4235_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4236_ = l_Lean_registerTraceClass(v___x_4233_, v___x_4234_, v___x_4235_);
return v___x_4236_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4238_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Subst(builtin);
}
#ifdef __cplusplus
}
#endif
