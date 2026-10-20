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
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqNDRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_replaceFVar(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00Lean_Meta_substCore_spec__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00Lean_Meta_substCore_spec__6___closed__0 = (const lean_object*)&l_panic___at___00Lean_Meta_substCore_spec__6___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__0 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_substCore___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__1 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__1_value;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "after intro rest "};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__2 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__1___closed__3;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__4 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__1___closed__5;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_h"};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__6 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__6_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_substCore___lam__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(32, 79, 207, 54, 208, 114, 216, 130)}};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__7 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__7_value;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Tactic.Subst"};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__8 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__8_value;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.substCore"};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__9 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__9_value;
static const lean_string_object l_Lean_Meta_substCore___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_substCore___lam__1___closed__10 = (const lean_object*)&l_Lean_Meta_substCore___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__1___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__0 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__0_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 29, 29, 32, 53, 17, 69, 167)}};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__1 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__1_value;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "invalid equality proof, it is not of the form "};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__2 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__2_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__3;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = "\nafter WHNF, variable expected, but obtained"};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__4 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__4_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__5;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "argument must be an equality proof"};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__6 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__6_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__3___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__6_value)}};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__7 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__7_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__8;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__9;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "reverted variables "};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__10 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__10_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__11;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "after intro2 "};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__12 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__12_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__13;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "after revert "};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__14 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__14_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__15;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__16 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__16_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__17;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "' occurs at"};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__18 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__18_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__19;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__20 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__20_value;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__21 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__21_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__3___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__20_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_substCore___lam__3___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__22_value_aux_0),((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__21_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_substCore___lam__3___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__22_value_aux_1),((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__0_value),LEAN_SCALAR_PTR_LITERAL(60, 247, 229, 3, 213, 123, 220, 1)}};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__22 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__22_value;
static const lean_closure_object l_Lean_Meta_substCore___lam__3___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_substCore___lam__2___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__22_value)} };
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__23 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__23_value;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "substituting "};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__24 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__24_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__25;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " (id: "};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__26 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__26_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__27;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = ") with "};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__28 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__28_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__3___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__3___closed__29;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "(x = t)"};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__30 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__30_value;
static const lean_string_object l_Lean_Meta_substCore___lam__3___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "(t = x)"};
static const lean_object* l_Lean_Meta_substCore___lam__3___closed__31 = (const lean_object*)&l_Lean_Meta_substCore___lam__3___closed__31_value;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_introSubstEq___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___closed__2;
static const lean_string_object l_Lean_Meta_introSubstEq___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "introSubstEq falling back to intro\n"};
static const lean_object* l_Lean_Meta_introSubstEq___closed__3 = (const lean_object*)&l_Lean_Meta_introSubstEq___closed__3_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___closed__4;
static const lean_string_object l_Lean_Meta_introSubstEq___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l_Lean_Meta_introSubstEq___closed__5 = (const lean_object*)&l_Lean_Meta_introSubstEq___closed__5_value;
static lean_once_cell_t l_Lean_Meta_introSubstEq___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_introSubstEq___closed__6;
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__20_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__21_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Subst"};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 155, 87, 188, 107, 213, 207, 175)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(46, 207, 184, 108, 123, 194, 122, 15)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(87, 208, 80, 10, 197, 128, 95, 79)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__20_value),LEAN_SCALAR_PTR_LITERAL(7, 62, 56, 132, 111, 90, 85, 225)}};
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
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__20_value),LEAN_SCALAR_PTR_LITERAL(254, 30, 149, 183, 84, 179, 28, 215)}};
static const lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__21_value),LEAN_SCALAR_PTR_LITERAL(99, 160, 169, 64, 171, 126, 88, 158)}};
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
v___x_21_ = lean_st_ref_put(v___y_2_, v___x_20_);
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
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0(lean_object* v_x_44_){
_start:
{
uint8_t v___x_45_; 
v___x_45_ = 0;
return v___x_45_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0___boxed(lean_object* v_x_46_){
_start:
{
uint8_t v_res_47_; lean_object* v_r_48_; 
v_res_47_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0(v_x_46_);
lean_dec(v_x_46_);
v_r_48_ = lean_box(v_res_47_);
return v_r_48_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1(lean_object* v_fvarId_49_, lean_object* v_x_50_){
_start:
{
uint8_t v___x_51_; 
v___x_51_ = l_Lean_instBEqFVarId_beq(v_fvarId_49_, v_x_50_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1___boxed(lean_object* v_fvarId_52_, lean_object* v_x_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1(v_fvarId_52_, v_x_53_);
lean_dec(v_x_53_);
lean_dec(v_fvarId_52_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_57_ = lean_box(0);
v___x_58_ = lean_unsigned_to_nat(16u);
v___x_59_ = lean_mk_array(v___x_58_, v___x_57_);
return v___x_59_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_60_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__1);
v___x_61_ = lean_unsigned_to_nat(0u);
v___x_62_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_61_);
lean_ctor_set(v___x_62_, 1, v___x_60_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(lean_object* v_e_63_, lean_object* v_fvarId_64_, lean_object* v___y_65_){
_start:
{
lean_object* v___f_67_; lean_object* v___f_68_; lean_object* v___x_69_; uint8_t v_fst_71_; lean_object* v_mctx_72_; lean_object* v___y_90_; lean_object* v_mctx_95_; lean_object* v___x_96_; lean_object* v___x_97_; uint8_t v___x_98_; 
v___f_67_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__0));
v___f_68_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_68_, 0, v_fvarId_64_);
v___x_69_ = lean_st_ref_get(v___y_65_);
v_mctx_95_ = lean_ctor_get(v___x_69_, 0);
lean_inc_ref_n(v_mctx_95_, 2);
lean_dec(v___x_69_);
v___x_96_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__2);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v___x_96_);
lean_ctor_set(v___x_97_, 1, v_mctx_95_);
v___x_98_ = l_Lean_Expr_hasFVar(v_e_63_);
if (v___x_98_ == 0)
{
uint8_t v___x_99_; 
v___x_99_ = l_Lean_Expr_hasMVar(v_e_63_);
if (v___x_99_ == 0)
{
lean_dec_ref_known(v___x_97_, 2);
lean_dec_ref(v___f_68_);
lean_dec_ref(v_e_63_);
v_fst_71_ = v___x_99_;
v_mctx_72_ = v_mctx_95_;
goto v___jp_70_;
}
else
{
lean_object* v___x_100_; 
lean_dec_ref(v_mctx_95_);
v___x_100_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_68_, v___f_67_, v_e_63_, v___x_97_);
v___y_90_ = v___x_100_;
goto v___jp_89_;
}
}
else
{
lean_object* v___x_101_; 
lean_dec_ref(v_mctx_95_);
v___x_101_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_68_, v___f_67_, v_e_63_, v___x_97_);
v___y_90_ = v___x_101_;
goto v___jp_89_;
}
v___jp_70_:
{
lean_object* v___x_73_; lean_object* v_cache_74_; lean_object* v_zetaDeltaFVarIds_75_; lean_object* v_postponed_76_; lean_object* v_diag_77_; lean_object* v___x_79_; uint8_t v_isShared_80_; uint8_t v_isSharedCheck_87_; 
v___x_73_ = lean_st_ref_take(v___y_65_);
v_cache_74_ = lean_ctor_get(v___x_73_, 1);
v_zetaDeltaFVarIds_75_ = lean_ctor_get(v___x_73_, 2);
v_postponed_76_ = lean_ctor_get(v___x_73_, 3);
v_diag_77_ = lean_ctor_get(v___x_73_, 4);
v_isSharedCheck_87_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_87_ == 0)
{
lean_object* v_unused_88_; 
v_unused_88_ = lean_ctor_get(v___x_73_, 0);
lean_dec(v_unused_88_);
v___x_79_ = v___x_73_;
v_isShared_80_ = v_isSharedCheck_87_;
goto v_resetjp_78_;
}
else
{
lean_inc(v_diag_77_);
lean_inc(v_postponed_76_);
lean_inc(v_zetaDeltaFVarIds_75_);
lean_inc(v_cache_74_);
lean_dec(v___x_73_);
v___x_79_ = lean_box(0);
v_isShared_80_ = v_isSharedCheck_87_;
goto v_resetjp_78_;
}
v_resetjp_78_:
{
lean_object* v___x_82_; 
if (v_isShared_80_ == 0)
{
lean_ctor_set(v___x_79_, 0, v_mctx_72_);
v___x_82_ = v___x_79_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_86_; 
v_reuseFailAlloc_86_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_86_, 0, v_mctx_72_);
lean_ctor_set(v_reuseFailAlloc_86_, 1, v_cache_74_);
lean_ctor_set(v_reuseFailAlloc_86_, 2, v_zetaDeltaFVarIds_75_);
lean_ctor_set(v_reuseFailAlloc_86_, 3, v_postponed_76_);
lean_ctor_set(v_reuseFailAlloc_86_, 4, v_diag_77_);
v___x_82_ = v_reuseFailAlloc_86_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_83_ = lean_st_ref_put(v___y_65_, v___x_82_);
v___x_84_ = lean_box(v_fst_71_);
v___x_85_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
return v___x_85_;
}
}
}
v___jp_89_:
{
lean_object* v_snd_91_; lean_object* v_fst_92_; lean_object* v_mctx_93_; uint8_t v___x_94_; 
v_snd_91_ = lean_ctor_get(v___y_90_, 1);
lean_inc(v_snd_91_);
v_fst_92_ = lean_ctor_get(v___y_90_, 0);
lean_inc(v_fst_92_);
lean_dec_ref(v___y_90_);
v_mctx_93_ = lean_ctor_get(v_snd_91_, 1);
lean_inc_ref(v_mctx_93_);
lean_dec(v_snd_91_);
v___x_94_ = lean_unbox(v_fst_92_);
lean_dec(v_fst_92_);
v_fst_71_ = v___x_94_;
v_mctx_72_ = v_mctx_93_;
goto v___jp_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___boxed(lean_object* v_e_102_, lean_object* v_fvarId_103_, lean_object* v___y_104_, lean_object* v___y_105_){
_start:
{
lean_object* v_res_106_; 
v_res_106_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_e_102_, v_fvarId_103_, v___y_104_);
lean_dec(v___y_104_);
return v_res_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3(lean_object* v_e_107_, lean_object* v_fvarId_108_, lean_object* v___y_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_){
_start:
{
lean_object* v___x_114_; 
v___x_114_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_e_107_, v_fvarId_108_, v___y_110_);
return v___x_114_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___boxed(lean_object* v_e_115_, lean_object* v_fvarId_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3(v_e_115_, v_fvarId_116_, v___y_117_, v___y_118_, v___y_119_, v___y_120_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__6(lean_object* v_msg_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_){
_start:
{
lean_object* v___f_130_; lean_object* v___x_24704__overap_131_; lean_object* v___x_132_; 
v___f_130_ = ((lean_object*)(l_panic___at___00Lean_Meta_substCore_spec__6___closed__0));
v___x_24704__overap_131_ = lean_panic_fn_borrowed(v___f_130_, v_msg_124_);
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
lean_inc(v___y_126_);
lean_inc_ref(v___y_125_);
v___x_132_ = lean_apply_5(v___x_24704__overap_131_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__6___boxed(lean_object* v_msg_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_panic___at___00Lean_Meta_substCore_spec__6(v_msg_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
lean_dec(v___y_135_);
lean_dec_ref(v___y_134_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(lean_object* v_mvarId_140_, lean_object* v_x_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v___x_147_; 
v___x_147_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_140_, v_x_141_, v___y_142_, v___y_143_, v___y_144_, v___y_145_);
if (lean_obj_tag(v___x_147_) == 0)
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
v_a_148_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_147_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_147_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
v_a_156_ = lean_ctor_get(v___x_147_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_147_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_147_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_147_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg___boxed(lean_object* v_mvarId_164_, lean_object* v_x_165_, lean_object* v___y_166_, lean_object* v___y_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_){
_start:
{
lean_object* v_res_171_; 
v_res_171_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_164_, v_x_165_, v___y_166_, v___y_167_, v___y_168_, v___y_169_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
lean_dec(v___y_167_);
lean_dec_ref(v___y_166_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(lean_object* v_00_u03b1_172_, lean_object* v_mvarId_173_, lean_object* v_x_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v___x_180_; 
v___x_180_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_173_, v_x_174_, v___y_175_, v___y_176_, v___y_177_, v___y_178_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed(lean_object* v_00_u03b1_181_, lean_object* v_mvarId_182_, lean_object* v_x_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(v_00_u03b1_181_, v_mvarId_182_, v_x_183_, v___y_184_, v___y_185_, v___y_186_, v___y_187_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
lean_dec(v___y_185_);
lean_dec_ref(v___y_184_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0(lean_object* v_type_190_, lean_object* v___x_191_, lean_object* v___x_192_, lean_object* v___x_193_, uint8_t v___x_194_, uint8_t v___x_195_, lean_object* v_hAux_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v___x_202_; 
lean_inc_ref(v_hAux_196_);
v___x_202_ = l_Lean_Meta_mkEqSymm(v_hAux_196_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
if (lean_obj_tag(v___x_202_) == 0)
{
lean_object* v_a_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; 
v_a_203_ = lean_ctor_get(v___x_202_, 0);
lean_inc(v_a_203_);
lean_dec_ref_known(v___x_202_, 1);
v___x_204_ = l_Lean_Expr_replaceFVar(v_type_190_, v___x_191_, v_a_203_);
lean_dec(v_a_203_);
v___x_205_ = lean_mk_empty_array_with_capacity(v___x_192_);
v___x_206_ = lean_array_push(v___x_205_, v___x_193_);
v___x_207_ = lean_array_push(v___x_206_, v_hAux_196_);
v___x_208_ = 1;
v___x_209_ = l_Lean_Meta_mkLambdaFVars(v___x_207_, v___x_204_, v___x_194_, v___x_195_, v___x_194_, v___x_195_, v___x_208_, v___y_197_, v___y_198_, v___y_199_, v___y_200_);
lean_dec_ref(v___x_207_);
return v___x_209_;
}
else
{
lean_dec_ref(v_hAux_196_);
lean_dec_ref(v___x_193_);
lean_dec_ref(v___x_191_);
return v___x_202_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object* v_type_210_, lean_object* v___x_211_, lean_object* v___x_212_, lean_object* v___x_213_, lean_object* v___x_214_, lean_object* v___x_215_, lean_object* v_hAux_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_, lean_object* v___y_220_, lean_object* v___y_221_){
_start:
{
uint8_t v___x_27155__boxed_222_; uint8_t v___x_27156__boxed_223_; lean_object* v_res_224_; 
v___x_27155__boxed_222_ = lean_unbox(v___x_214_);
v___x_27156__boxed_223_ = lean_unbox(v___x_215_);
v_res_224_ = l_Lean_Meta_substCore___lam__0(v_type_210_, v___x_211_, v___x_212_, v___x_213_, v___x_27155__boxed_222_, v___x_27156__boxed_223_, v_hAux_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
lean_dec(v___y_220_);
lean_dec_ref(v___y_219_);
lean_dec(v___y_218_);
lean_dec_ref(v___y_217_);
lean_dec(v___x_212_);
lean_dec_ref(v_type_210_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14___redArg(lean_object* v_x_225_, lean_object* v_x_226_, lean_object* v_x_227_, lean_object* v_x_228_){
_start:
{
lean_object* v_ks_229_; lean_object* v_vs_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_254_; 
v_ks_229_ = lean_ctor_get(v_x_225_, 0);
v_vs_230_ = lean_ctor_get(v_x_225_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v_x_225_);
if (v_isSharedCheck_254_ == 0)
{
v___x_232_ = v_x_225_;
v_isShared_233_ = v_isSharedCheck_254_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_vs_230_);
lean_inc(v_ks_229_);
lean_dec(v_x_225_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_254_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_array_get_size(v_ks_229_);
v___x_235_ = lean_nat_dec_lt(v_x_226_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
lean_dec(v_x_226_);
v___x_236_ = lean_array_push(v_ks_229_, v_x_227_);
v___x_237_ = lean_array_push(v_vs_230_, v_x_228_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v___x_237_);
lean_ctor_set(v___x_232_, 0, v___x_236_);
v___x_239_ = v___x_232_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___x_236_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
else
{
lean_object* v_k_x27_241_; uint8_t v___x_242_; 
v_k_x27_241_ = lean_array_fget_borrowed(v_ks_229_, v_x_226_);
v___x_242_ = l_Lean_instBEqMVarId_beq(v_x_227_, v_k_x27_241_);
if (v___x_242_ == 0)
{
lean_object* v___x_244_; 
if (v_isShared_233_ == 0)
{
v___x_244_ = v___x_232_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_ks_229_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v_vs_230_);
v___x_244_ = v_reuseFailAlloc_248_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_unsigned_to_nat(1u);
v___x_246_ = lean_nat_add(v_x_226_, v___x_245_);
lean_dec(v_x_226_);
v_x_225_ = v___x_244_;
v_x_226_ = v___x_246_;
goto _start;
}
}
else
{
lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_252_; 
v___x_249_ = lean_array_fset(v_ks_229_, v_x_226_, v_x_227_);
v___x_250_ = lean_array_fset(v_vs_230_, v_x_226_, v_x_228_);
lean_dec(v_x_226_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v___x_250_);
lean_ctor_set(v___x_232_, 0, v___x_249_);
v___x_252_ = v___x_232_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_249_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_250_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13___redArg(lean_object* v_n_255_, lean_object* v_k_256_, lean_object* v_v_257_){
_start:
{
lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_258_ = lean_unsigned_to_nat(0u);
v___x_259_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14___redArg(v_n_255_, v___x_258_, v_k_256_, v_v_257_);
return v___x_259_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_260_; 
v___x_260_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(lean_object* v_x_261_, size_t v_x_262_, size_t v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
if (lean_obj_tag(v_x_261_) == 0)
{
lean_object* v_es_266_; size_t v___x_267_; size_t v___x_268_; lean_object* v_j_269_; lean_object* v___x_270_; uint8_t v___x_271_; 
v_es_266_ = lean_ctor_get(v_x_261_, 0);
v___x_267_ = ((size_t)31ULL);
v___x_268_ = lean_usize_land(v_x_262_, v___x_267_);
v_j_269_ = lean_usize_to_nat(v___x_268_);
v___x_270_ = lean_array_get_size(v_es_266_);
v___x_271_ = lean_nat_dec_lt(v_j_269_, v___x_270_);
if (v___x_271_ == 0)
{
lean_dec(v_j_269_);
lean_dec(v_x_265_);
lean_dec(v_x_264_);
return v_x_261_;
}
else
{
lean_object* v___x_273_; uint8_t v_isShared_274_; uint8_t v_isSharedCheck_310_; 
lean_inc_ref(v_es_266_);
v_isSharedCheck_310_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_310_ == 0)
{
lean_object* v_unused_311_; 
v_unused_311_ = lean_ctor_get(v_x_261_, 0);
lean_dec(v_unused_311_);
v___x_273_ = v_x_261_;
v_isShared_274_ = v_isSharedCheck_310_;
goto v_resetjp_272_;
}
else
{
lean_dec(v_x_261_);
v___x_273_ = lean_box(0);
v_isShared_274_ = v_isSharedCheck_310_;
goto v_resetjp_272_;
}
v_resetjp_272_:
{
lean_object* v_v_275_; lean_object* v___x_276_; lean_object* v_xs_x27_277_; lean_object* v___y_279_; 
v_v_275_ = lean_array_fget(v_es_266_, v_j_269_);
v___x_276_ = lean_box(0);
v_xs_x27_277_ = lean_array_fset(v_es_266_, v_j_269_, v___x_276_);
switch(lean_obj_tag(v_v_275_))
{
case 0:
{
lean_object* v_key_284_; lean_object* v_val_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_295_; 
v_key_284_ = lean_ctor_get(v_v_275_, 0);
v_val_285_ = lean_ctor_get(v_v_275_, 1);
v_isSharedCheck_295_ = !lean_is_exclusive(v_v_275_);
if (v_isSharedCheck_295_ == 0)
{
v___x_287_ = v_v_275_;
v_isShared_288_ = v_isSharedCheck_295_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_val_285_);
lean_inc(v_key_284_);
lean_dec(v_v_275_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_295_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
uint8_t v___x_289_; 
v___x_289_ = l_Lean_instBEqMVarId_beq(v_x_264_, v_key_284_);
if (v___x_289_ == 0)
{
lean_object* v___x_290_; lean_object* v___x_291_; 
lean_del_object(v___x_287_);
v___x_290_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_284_, v_val_285_, v_x_264_, v_x_265_);
v___x_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_291_, 0, v___x_290_);
v___y_279_ = v___x_291_;
goto v___jp_278_;
}
else
{
lean_object* v___x_293_; 
lean_dec(v_val_285_);
lean_dec(v_key_284_);
if (v_isShared_288_ == 0)
{
lean_ctor_set(v___x_287_, 1, v_x_265_);
lean_ctor_set(v___x_287_, 0, v_x_264_);
v___x_293_ = v___x_287_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_294_; 
v_reuseFailAlloc_294_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_294_, 0, v_x_264_);
lean_ctor_set(v_reuseFailAlloc_294_, 1, v_x_265_);
v___x_293_ = v_reuseFailAlloc_294_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
v___y_279_ = v___x_293_;
goto v___jp_278_;
}
}
}
}
case 1:
{
lean_object* v_node_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_308_; 
v_node_296_ = lean_ctor_get(v_v_275_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v_v_275_);
if (v_isSharedCheck_308_ == 0)
{
v___x_298_ = v_v_275_;
v_isShared_299_ = v_isSharedCheck_308_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_node_296_);
lean_dec(v_v_275_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_308_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
size_t v___x_300_; size_t v___x_301_; size_t v___x_302_; size_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_306_; 
v___x_300_ = ((size_t)5ULL);
v___x_301_ = lean_usize_shift_right(v_x_262_, v___x_300_);
v___x_302_ = ((size_t)1ULL);
v___x_303_ = lean_usize_add(v_x_263_, v___x_302_);
v___x_304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_node_296_, v___x_301_, v___x_303_, v_x_264_, v_x_265_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_304_);
v___x_306_ = v___x_298_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v___x_304_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
v___y_279_ = v___x_306_;
goto v___jp_278_;
}
}
}
default: 
{
lean_object* v___x_309_; 
v___x_309_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_309_, 0, v_x_264_);
lean_ctor_set(v___x_309_, 1, v_x_265_);
v___y_279_ = v___x_309_;
goto v___jp_278_;
}
}
v___jp_278_:
{
lean_object* v___x_280_; lean_object* v___x_282_; 
v___x_280_ = lean_array_fset(v_xs_x27_277_, v_j_269_, v___y_279_);
lean_dec(v_j_269_);
if (v_isShared_274_ == 0)
{
lean_ctor_set(v___x_273_, 0, v___x_280_);
v___x_282_ = v___x_273_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v___x_280_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
}
else
{
lean_object* v_ks_312_; lean_object* v_vs_313_; lean_object* v___x_315_; uint8_t v_isShared_316_; uint8_t v_isSharedCheck_331_; 
v_ks_312_ = lean_ctor_get(v_x_261_, 0);
v_vs_313_ = lean_ctor_get(v_x_261_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_261_);
if (v_isSharedCheck_331_ == 0)
{
v___x_315_ = v_x_261_;
v_isShared_316_ = v_isSharedCheck_331_;
goto v_resetjp_314_;
}
else
{
lean_inc(v_vs_313_);
lean_inc(v_ks_312_);
lean_dec(v_x_261_);
v___x_315_ = lean_box(0);
v_isShared_316_ = v_isSharedCheck_331_;
goto v_resetjp_314_;
}
v_resetjp_314_:
{
lean_object* v___x_318_; 
if (v_isShared_316_ == 0)
{
v___x_318_ = v___x_315_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v_ks_312_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v_vs_313_);
v___x_318_ = v_reuseFailAlloc_330_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
lean_object* v_newNode_319_; size_t v___x_320_; uint8_t v___x_321_; 
v_newNode_319_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13___redArg(v___x_318_, v_x_264_, v_x_265_);
v___x_320_ = ((size_t)7ULL);
v___x_321_ = lean_usize_dec_le(v___x_320_, v_x_263_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_322_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_319_);
v___x_323_ = lean_unsigned_to_nat(4u);
v___x_324_ = lean_nat_dec_lt(v___x_322_, v___x_323_);
lean_dec(v___x_322_);
if (v___x_324_ == 0)
{
lean_object* v_ks_325_; lean_object* v_vs_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; 
v_ks_325_ = lean_ctor_get(v_newNode_319_, 0);
lean_inc_ref(v_ks_325_);
v_vs_326_ = lean_ctor_get(v_newNode_319_, 1);
lean_inc_ref(v_vs_326_);
lean_dec_ref(v_newNode_319_);
v___x_327_ = lean_unsigned_to_nat(0u);
v___x_328_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___closed__0);
v___x_329_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(v_x_263_, v_ks_325_, v_vs_326_, v___x_327_, v___x_328_);
lean_dec_ref(v_vs_326_);
lean_dec_ref(v_ks_325_);
return v___x_329_;
}
else
{
return v_newNode_319_;
}
}
else
{
return v_newNode_319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(size_t v_depth_332_, lean_object* v_keys_333_, lean_object* v_vals_334_, lean_object* v_i_335_, lean_object* v_entries_336_){
_start:
{
lean_object* v___x_337_; uint8_t v___x_338_; 
v___x_337_ = lean_array_get_size(v_keys_333_);
v___x_338_ = lean_nat_dec_lt(v_i_335_, v___x_337_);
if (v___x_338_ == 0)
{
lean_dec(v_i_335_);
return v_entries_336_;
}
else
{
lean_object* v_k_339_; lean_object* v_v_340_; uint64_t v___x_341_; size_t v_h_342_; size_t v___x_343_; lean_object* v___x_344_; size_t v___x_345_; size_t v___x_346_; size_t v___x_347_; size_t v_h_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_k_339_ = lean_array_fget_borrowed(v_keys_333_, v_i_335_);
v_v_340_ = lean_array_fget_borrowed(v_vals_334_, v_i_335_);
v___x_341_ = l_Lean_instHashableMVarId_hash(v_k_339_);
v_h_342_ = lean_uint64_to_usize(v___x_341_);
v___x_343_ = ((size_t)5ULL);
v___x_344_ = lean_unsigned_to_nat(1u);
v___x_345_ = ((size_t)1ULL);
v___x_346_ = lean_usize_sub(v_depth_332_, v___x_345_);
v___x_347_ = lean_usize_mul(v___x_343_, v___x_346_);
v_h_348_ = lean_usize_shift_right(v_h_342_, v___x_347_);
v___x_349_ = lean_nat_add(v_i_335_, v___x_344_);
lean_dec(v_i_335_);
lean_inc(v_v_340_);
lean_inc(v_k_339_);
v___x_350_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_entries_336_, v_h_348_, v_depth_332_, v_k_339_, v_v_340_);
v_i_335_ = v___x_349_;
v_entries_336_ = v___x_350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_depth_352_, lean_object* v_keys_353_, lean_object* v_vals_354_, lean_object* v_i_355_, lean_object* v_entries_356_){
_start:
{
size_t v_depth_boxed_357_; lean_object* v_res_358_; 
v_depth_boxed_357_ = lean_unbox_usize(v_depth_352_);
lean_dec(v_depth_352_);
v_res_358_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(v_depth_boxed_357_, v_keys_353_, v_vals_354_, v_i_355_, v_entries_356_);
lean_dec_ref(v_vals_354_);
lean_dec_ref(v_keys_353_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_x_359_, lean_object* v_x_360_, lean_object* v_x_361_, lean_object* v_x_362_, lean_object* v_x_363_){
_start:
{
size_t v_x_27276__boxed_364_; size_t v_x_27277__boxed_365_; lean_object* v_res_366_; 
v_x_27276__boxed_364_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_x_27277__boxed_365_ = lean_unbox_usize(v_x_361_);
lean_dec(v_x_361_);
v_res_366_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_359_, v_x_27276__boxed_364_, v_x_27277__boxed_365_, v_x_362_, v_x_363_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5___redArg(lean_object* v_x_367_, lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
uint64_t v___x_370_; size_t v___x_371_; size_t v___x_372_; lean_object* v___x_373_; 
v___x_370_ = l_Lean_instHashableMVarId_hash(v_x_368_);
v___x_371_ = lean_uint64_to_usize(v___x_370_);
v___x_372_ = ((size_t)1ULL);
v___x_373_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_367_, v___x_371_, v___x_372_, v_x_368_, v_x_369_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(lean_object* v_mvarId_374_, lean_object* v_val_375_, lean_object* v___y_376_){
_start:
{
lean_object* v___x_378_; lean_object* v_mctx_379_; lean_object* v_cache_380_; lean_object* v_zetaDeltaFVarIds_381_; lean_object* v_postponed_382_; lean_object* v_diag_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_413_; 
v___x_378_ = lean_st_ref_take(v___y_376_);
v_mctx_379_ = lean_ctor_get(v___x_378_, 0);
v_cache_380_ = lean_ctor_get(v___x_378_, 1);
v_zetaDeltaFVarIds_381_ = lean_ctor_get(v___x_378_, 2);
v_postponed_382_ = lean_ctor_get(v___x_378_, 3);
v_diag_383_ = lean_ctor_get(v___x_378_, 4);
v_isSharedCheck_413_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_413_ == 0)
{
v___x_385_ = v___x_378_;
v_isShared_386_ = v_isSharedCheck_413_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_diag_383_);
lean_inc(v_postponed_382_);
lean_inc(v_zetaDeltaFVarIds_381_);
lean_inc(v_cache_380_);
lean_inc(v_mctx_379_);
lean_dec(v___x_378_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_413_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_depth_387_; lean_object* v_levelAssignDepth_388_; lean_object* v_lmvarCounter_389_; lean_object* v_mvarCounter_390_; lean_object* v_lDecls_391_; lean_object* v_decls_392_; lean_object* v_userNames_393_; lean_object* v_lAssignment_394_; lean_object* v_eAssignment_395_; lean_object* v_dAssignment_396_; lean_object* v_instanceTypedMVars_397_; lean_object* v_synthNormMemo_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_412_; 
v_depth_387_ = lean_ctor_get(v_mctx_379_, 0);
v_levelAssignDepth_388_ = lean_ctor_get(v_mctx_379_, 1);
v_lmvarCounter_389_ = lean_ctor_get(v_mctx_379_, 2);
v_mvarCounter_390_ = lean_ctor_get(v_mctx_379_, 3);
v_lDecls_391_ = lean_ctor_get(v_mctx_379_, 4);
v_decls_392_ = lean_ctor_get(v_mctx_379_, 5);
v_userNames_393_ = lean_ctor_get(v_mctx_379_, 6);
v_lAssignment_394_ = lean_ctor_get(v_mctx_379_, 7);
v_eAssignment_395_ = lean_ctor_get(v_mctx_379_, 8);
v_dAssignment_396_ = lean_ctor_get(v_mctx_379_, 9);
v_instanceTypedMVars_397_ = lean_ctor_get(v_mctx_379_, 10);
v_synthNormMemo_398_ = lean_ctor_get(v_mctx_379_, 11);
v_isSharedCheck_412_ = !lean_is_exclusive(v_mctx_379_);
if (v_isSharedCheck_412_ == 0)
{
v___x_400_ = v_mctx_379_;
v_isShared_401_ = v_isSharedCheck_412_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_synthNormMemo_398_);
lean_inc(v_instanceTypedMVars_397_);
lean_inc(v_dAssignment_396_);
lean_inc(v_eAssignment_395_);
lean_inc(v_lAssignment_394_);
lean_inc(v_userNames_393_);
lean_inc(v_decls_392_);
lean_inc(v_lDecls_391_);
lean_inc(v_mvarCounter_390_);
lean_inc(v_lmvarCounter_389_);
lean_inc(v_levelAssignDepth_388_);
lean_inc(v_depth_387_);
lean_dec(v_mctx_379_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_412_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_405_; 
v___x_402_ = lean_box(0);
v___x_403_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5___redArg(v_eAssignment_395_, v_mvarId_374_, v_val_375_);
if (v_isShared_401_ == 0)
{
lean_ctor_set(v___x_400_, 8, v___x_403_);
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_depth_387_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_levelAssignDepth_388_);
lean_ctor_set(v_reuseFailAlloc_411_, 2, v_lmvarCounter_389_);
lean_ctor_set(v_reuseFailAlloc_411_, 3, v_mvarCounter_390_);
lean_ctor_set(v_reuseFailAlloc_411_, 4, v_lDecls_391_);
lean_ctor_set(v_reuseFailAlloc_411_, 5, v_decls_392_);
lean_ctor_set(v_reuseFailAlloc_411_, 6, v_userNames_393_);
lean_ctor_set(v_reuseFailAlloc_411_, 7, v_lAssignment_394_);
lean_ctor_set(v_reuseFailAlloc_411_, 8, v___x_403_);
lean_ctor_set(v_reuseFailAlloc_411_, 9, v_dAssignment_396_);
lean_ctor_set(v_reuseFailAlloc_411_, 10, v_instanceTypedMVars_397_);
lean_ctor_set(v_reuseFailAlloc_411_, 11, v_synthNormMemo_398_);
v___x_405_ = v_reuseFailAlloc_411_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
lean_object* v___x_407_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_405_);
v___x_407_ = v___x_385_;
goto v_reusejp_406_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v___x_405_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_cache_380_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_zetaDeltaFVarIds_381_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_postponed_382_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_diag_383_);
v___x_407_ = v_reuseFailAlloc_410_;
goto v_reusejp_406_;
}
v_reusejp_406_:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_st_ref_put(v___y_376_, v___x_407_);
v___x_409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_409_, 0, v___x_402_);
return v___x_409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg___boxed(lean_object* v_mvarId_414_, lean_object* v_val_415_, lean_object* v___y_416_, lean_object* v___y_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_mvarId_414_, v_val_415_, v___y_416_);
lean_dec(v___y_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(lean_object* v_fst_419_, lean_object* v_fst_420_, lean_object* v_n_421_, lean_object* v_i_422_, lean_object* v_a_423_){
_start:
{
lean_object* v_zero_425_; uint8_t v_isZero_426_; 
v_zero_425_ = lean_unsigned_to_nat(0u);
v_isZero_426_ = lean_nat_dec_eq(v_i_422_, v_zero_425_);
if (v_isZero_426_ == 1)
{
lean_object* v___x_427_; 
lean_dec(v_i_422_);
v___x_427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_427_, 0, v_a_423_);
return v___x_427_;
}
else
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v_one_430_; lean_object* v_n_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_428_ = lean_unsigned_to_nat(2u);
v___x_429_ = lean_box(0);
v_one_430_ = lean_unsigned_to_nat(1u);
v_n_431_ = lean_nat_sub(v_i_422_, v_one_430_);
lean_dec(v_i_422_);
v___x_432_ = lean_nat_sub(v_n_421_, v_n_431_);
v___x_433_ = lean_nat_sub(v___x_432_, v_one_430_);
lean_dec(v___x_432_);
v___x_434_ = lean_nat_add(v___x_433_, v___x_428_);
v___x_435_ = lean_array_get_borrowed(v___x_429_, v_fst_419_, v___x_434_);
lean_dec(v___x_434_);
v___x_436_ = lean_array_fget_borrowed(v_fst_420_, v___x_433_);
lean_dec(v___x_433_);
lean_inc(v___x_436_);
v___x_437_ = l_Lean_mkFVar(v___x_436_);
lean_inc(v___x_435_);
v___x_438_ = l_Lean_Meta_FVarSubst_insert(v_a_423_, v___x_435_, v___x_437_);
v_i_422_ = v_n_431_;
v_a_423_ = v___x_438_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg___boxed(lean_object* v_fst_440_, lean_object* v_fst_441_, lean_object* v_n_442_, lean_object* v_i_443_, lean_object* v_a_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_440_, v_fst_441_, v_n_442_, v_i_443_, v_a_444_);
lean_dec(v_n_442_);
lean_dec_ref(v_fst_441_);
lean_dec_ref(v_fst_440_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0(lean_object* v_k_447_, lean_object* v_b_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___x_454_; 
lean_inc(v___y_452_);
lean_inc_ref(v___y_451_);
lean_inc(v___y_450_);
lean_inc_ref(v___y_449_);
v___x_454_ = lean_apply_6(v_k_447_, v_b_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_, lean_box(0));
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_455_, lean_object* v_b_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0(v_k_455_, v_b_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_);
lean_dec(v___y_460_);
lean_dec_ref(v___y_459_);
lean_dec(v___y_458_);
lean_dec_ref(v___y_457_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(lean_object* v_name_463_, uint8_t v_bi_464_, lean_object* v_type_465_, lean_object* v_k_466_, uint8_t v_kind_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v___f_473_; lean_object* v___x_474_; 
v___f_473_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_473_, 0, v_k_466_);
v___x_474_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_463_, v_bi_464_, v_type_465_, v___f_473_, v_kind_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
if (lean_obj_tag(v___x_474_) == 0)
{
lean_object* v_a_475_; lean_object* v___x_477_; uint8_t v_isShared_478_; uint8_t v_isSharedCheck_482_; 
v_a_475_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_482_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_482_ == 0)
{
v___x_477_ = v___x_474_;
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
else
{
lean_inc(v_a_475_);
lean_dec(v___x_474_);
v___x_477_ = lean_box(0);
v_isShared_478_ = v_isSharedCheck_482_;
goto v_resetjp_476_;
}
v_resetjp_476_:
{
lean_object* v___x_480_; 
if (v_isShared_478_ == 0)
{
v___x_480_ = v___x_477_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_a_475_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
}
else
{
lean_object* v_a_483_; lean_object* v___x_485_; uint8_t v_isShared_486_; uint8_t v_isSharedCheck_490_; 
v_a_483_ = lean_ctor_get(v___x_474_, 0);
v_isSharedCheck_490_ = !lean_is_exclusive(v___x_474_);
if (v_isSharedCheck_490_ == 0)
{
v___x_485_ = v___x_474_;
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
else
{
lean_inc(v_a_483_);
lean_dec(v___x_474_);
v___x_485_ = lean_box(0);
v_isShared_486_ = v_isSharedCheck_490_;
goto v_resetjp_484_;
}
v_resetjp_484_:
{
lean_object* v___x_488_; 
if (v_isShared_486_ == 0)
{
v___x_488_ = v___x_485_;
goto v_reusejp_487_;
}
else
{
lean_object* v_reuseFailAlloc_489_; 
v_reuseFailAlloc_489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_489_, 0, v_a_483_);
v___x_488_ = v_reuseFailAlloc_489_;
goto v_reusejp_487_;
}
v_reusejp_487_:
{
return v___x_488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___boxed(lean_object* v_name_491_, lean_object* v_bi_492_, lean_object* v_type_493_, lean_object* v_k_494_, lean_object* v_kind_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_){
_start:
{
uint8_t v_bi_boxed_501_; uint8_t v_kind_boxed_502_; lean_object* v_res_503_; 
v_bi_boxed_501_ = lean_unbox(v_bi_492_);
v_kind_boxed_502_ = lean_unbox(v_kind_495_);
v_res_503_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_491_, v_bi_boxed_501_, v_type_493_, v_k_494_, v_kind_boxed_502_, v___y_496_, v___y_497_, v___y_498_, v___y_499_);
lean_dec(v___y_499_);
lean_dec_ref(v___y_498_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(lean_object* v_name_504_, lean_object* v_type_505_, lean_object* v_k_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_){
_start:
{
uint8_t v___x_512_; uint8_t v___x_513_; lean_object* v___x_514_; 
v___x_512_ = 0;
v___x_513_ = 0;
v___x_514_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_504_, v___x_512_, v_type_505_, v_k_506_, v___x_513_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
return v___x_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object* v_name_515_, lean_object* v_type_516_, lean_object* v_k_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
lean_object* v_res_523_; 
v_res_523_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v_name_515_, v_type_516_, v_k_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec_ref(v___y_518_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(lean_object* v_msgData_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v___x_530_; lean_object* v_env_531_; uint8_t v___x_532_; lean_object* v_env_533_; lean_object* v___x_534_; lean_object* v_toCold_535_; lean_object* v_mctx_536_; lean_object* v_lctx_537_; lean_object* v_options_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; 
v___x_530_ = lean_st_ref_get(v___y_528_);
v_env_531_ = lean_ctor_get(v___x_530_, 0);
lean_inc_ref(v_env_531_);
lean_dec(v___x_530_);
v___x_532_ = 0;
v_env_533_ = l_Lean_Environment_setRecordingDeps(v_env_531_, v___x_532_);
v___x_534_ = lean_st_ref_get(v___y_526_);
v_toCold_535_ = lean_ctor_get(v___y_527_, 0);
v_mctx_536_ = lean_ctor_get(v___x_534_, 0);
lean_inc_ref(v_mctx_536_);
lean_dec(v___x_534_);
v_lctx_537_ = lean_ctor_get(v___y_525_, 2);
v_options_538_ = lean_ctor_get(v_toCold_535_, 2);
lean_inc_ref(v_options_538_);
lean_inc_ref(v_lctx_537_);
v___x_539_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_539_, 0, v_env_533_);
lean_ctor_set(v___x_539_, 1, v_mctx_536_);
lean_ctor_set(v___x_539_, 2, v_lctx_537_);
lean_ctor_set(v___x_539_, 3, v_options_538_);
v___x_540_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
lean_ctor_set(v___x_540_, 1, v_msgData_524_);
v___x_541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_541_, 0, v___x_540_);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2___boxed(lean_object* v_msgData_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msgData_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
return v_res_548_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0(void){
_start:
{
lean_object* v___x_549_; double v___x_550_; 
v___x_549_ = lean_unsigned_to_nat(0u);
v___x_550_ = lean_float_of_nat(v___x_549_);
return v___x_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(lean_object* v_cls_554_, lean_object* v_msg_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_ref_561_; lean_object* v___x_562_; lean_object* v_a_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_608_; 
v_ref_561_ = lean_ctor_get(v___y_558_, 2);
v___x_562_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msg_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_);
v_a_563_ = lean_ctor_get(v___x_562_, 0);
v_isSharedCheck_608_ = !lean_is_exclusive(v___x_562_);
if (v_isSharedCheck_608_ == 0)
{
v___x_565_ = v___x_562_;
v_isShared_566_ = v_isSharedCheck_608_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_a_563_);
lean_dec(v___x_562_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_608_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; lean_object* v_traceState_568_; lean_object* v_env_569_; lean_object* v_nextMacroScope_570_; lean_object* v_ngen_571_; lean_object* v_auxDeclNGen_572_; lean_object* v_cache_573_; lean_object* v_recordedDeps_574_; lean_object* v_messages_575_; lean_object* v_infoState_576_; lean_object* v_snapshotTasks_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_607_; 
v___x_567_ = lean_st_ref_take(v___y_559_);
v_traceState_568_ = lean_ctor_get(v___x_567_, 4);
v_env_569_ = lean_ctor_get(v___x_567_, 0);
v_nextMacroScope_570_ = lean_ctor_get(v___x_567_, 1);
v_ngen_571_ = lean_ctor_get(v___x_567_, 2);
v_auxDeclNGen_572_ = lean_ctor_get(v___x_567_, 3);
v_cache_573_ = lean_ctor_get(v___x_567_, 5);
v_recordedDeps_574_ = lean_ctor_get(v___x_567_, 6);
v_messages_575_ = lean_ctor_get(v___x_567_, 7);
v_infoState_576_ = lean_ctor_get(v___x_567_, 8);
v_snapshotTasks_577_ = lean_ctor_get(v___x_567_, 9);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_607_ == 0)
{
v___x_579_ = v___x_567_;
v_isShared_580_ = v_isSharedCheck_607_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_snapshotTasks_577_);
lean_inc(v_infoState_576_);
lean_inc(v_messages_575_);
lean_inc(v_recordedDeps_574_);
lean_inc(v_cache_573_);
lean_inc(v_traceState_568_);
lean_inc(v_auxDeclNGen_572_);
lean_inc(v_ngen_571_);
lean_inc(v_nextMacroScope_570_);
lean_inc(v_env_569_);
lean_dec(v___x_567_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_607_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
uint64_t v_tid_581_; lean_object* v_traces_582_; lean_object* v___x_584_; uint8_t v_isShared_585_; uint8_t v_isSharedCheck_606_; 
v_tid_581_ = lean_ctor_get_uint64(v_traceState_568_, sizeof(void*)*1);
v_traces_582_ = lean_ctor_get(v_traceState_568_, 0);
v_isSharedCheck_606_ = !lean_is_exclusive(v_traceState_568_);
if (v_isSharedCheck_606_ == 0)
{
v___x_584_ = v_traceState_568_;
v_isShared_585_ = v_isSharedCheck_606_;
goto v_resetjp_583_;
}
else
{
lean_inc(v_traces_582_);
lean_dec(v_traceState_568_);
v___x_584_ = lean_box(0);
v_isShared_585_ = v_isSharedCheck_606_;
goto v_resetjp_583_;
}
v_resetjp_583_:
{
lean_object* v___x_586_; lean_object* v___x_587_; double v___x_588_; uint8_t v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
v___x_586_ = lean_box(0);
v___x_587_ = lean_box(0);
v___x_588_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0);
v___x_589_ = 0;
v___x_590_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__1));
v___x_591_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_591_, 0, v_cls_554_);
lean_ctor_set(v___x_591_, 1, v___x_587_);
lean_ctor_set(v___x_591_, 2, v___x_590_);
lean_ctor_set_float(v___x_591_, sizeof(void*)*3, v___x_588_);
lean_ctor_set_float(v___x_591_, sizeof(void*)*3 + 8, v___x_588_);
lean_ctor_set_uint8(v___x_591_, sizeof(void*)*3 + 16, v___x_589_);
v___x_592_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__2));
v___x_593_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_593_, 0, v___x_591_);
lean_ctor_set(v___x_593_, 1, v_a_563_);
lean_ctor_set(v___x_593_, 2, v___x_592_);
lean_inc(v_ref_561_);
v___x_594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_594_, 0, v_ref_561_);
lean_ctor_set(v___x_594_, 1, v___x_593_);
v___x_595_ = l_Lean_PersistentArray_push___redArg(v_traces_582_, v___x_594_);
if (v_isShared_585_ == 0)
{
lean_ctor_set(v___x_584_, 0, v___x_595_);
v___x_597_ = v___x_584_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v___x_595_);
lean_ctor_set_uint64(v_reuseFailAlloc_605_, sizeof(void*)*1, v_tid_581_);
v___x_597_ = v_reuseFailAlloc_605_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
lean_object* v___x_599_; 
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 4, v___x_597_);
v___x_599_ = v___x_579_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v_env_569_);
lean_ctor_set(v_reuseFailAlloc_604_, 1, v_nextMacroScope_570_);
lean_ctor_set(v_reuseFailAlloc_604_, 2, v_ngen_571_);
lean_ctor_set(v_reuseFailAlloc_604_, 3, v_auxDeclNGen_572_);
lean_ctor_set(v_reuseFailAlloc_604_, 4, v___x_597_);
lean_ctor_set(v_reuseFailAlloc_604_, 5, v_cache_573_);
lean_ctor_set(v_reuseFailAlloc_604_, 6, v_recordedDeps_574_);
lean_ctor_set(v_reuseFailAlloc_604_, 7, v_messages_575_);
lean_ctor_set(v_reuseFailAlloc_604_, 8, v_infoState_576_);
lean_ctor_set(v_reuseFailAlloc_604_, 9, v_snapshotTasks_577_);
v___x_599_ = v_reuseFailAlloc_604_;
goto v_reusejp_598_;
}
v_reusejp_598_:
{
lean_object* v___x_600_; lean_object* v___x_602_; 
v___x_600_ = lean_st_ref_put(v___y_559_, v___x_599_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 0, v___x_586_);
v___x_602_ = v___x_565_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v___x_586_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___boxed(lean_object* v_cls_609_, lean_object* v_msg_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v_cls_609_, v_msg_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
return v_res_616_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__2));
v___x_622_ = l_Lean_stringToMessageData(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__5(void){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__4));
v___x_625_ = l_Lean_stringToMessageData(v___x_624_);
return v___x_625_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__11(void){
_start:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v___x_632_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__10));
v___x_633_ = lean_unsigned_to_nat(22u);
v___x_634_ = lean_unsigned_to_nat(64u);
v___x_635_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__9));
v___x_636_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__8));
v___x_637_ = l_mkPanicMessageWithDecl(v___x_636_, v___x_635_, v___x_634_, v___x_633_, v___x_632_);
return v___x_637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object* v_fvarId_638_, lean_object* v_hFVarId_639_, lean_object* v___x_640_, lean_object* v_fst_641_, lean_object* v_fvarSubst_642_, uint8_t v_clearH_643_, lean_object* v___x_644_, lean_object* v___x_645_, lean_object* v___x_646_, uint8_t v_skip_647_, uint8_t v___x_648_, lean_object* v___x_649_, lean_object* v_snd_650_, lean_object* v___x_651_, lean_object* v___x_652_, lean_object* v_a_653_, uint8_t v_symm_654_, uint8_t v___x_655_, lean_object* v___x_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_665_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_673_; lean_object* v___y_679_; lean_object* v_mvarId_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v_newVal_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_763_; lean_object* v___y_764_; lean_object* v___y_765_; uint8_t v___y_766_; lean_object* v_major_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_804_; uint8_t v___y_805_; lean_object* v_motive_806_; lean_object* v_newType_807_; lean_object* v___x_818_; 
lean_inc(v_snd_650_);
v___x_818_ = l_Lean_MVarId_getDecl(v_snd_650_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_818_) == 0)
{
lean_object* v_a_819_; lean_object* v_type_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___f_823_; lean_object* v___x_824_; 
v_a_819_ = lean_ctor_get(v___x_818_, 0);
lean_inc(v_a_819_);
lean_dec_ref_known(v___x_818_, 1);
v_type_820_ = lean_ctor_get(v_a_819_, 2);
lean_inc_ref_n(v_type_820_, 2);
lean_dec(v_a_819_);
v___x_821_ = lean_box(v___x_655_);
v___x_822_ = lean_box(v___x_648_);
lean_inc_ref(v___x_644_);
lean_inc(v___x_645_);
lean_inc_ref(v___x_640_);
v___f_823_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__0___boxed), 12, 6);
lean_closure_set(v___f_823_, 0, v_type_820_);
lean_closure_set(v___f_823_, 1, v___x_640_);
lean_closure_set(v___f_823_, 2, v___x_645_);
lean_closure_set(v___f_823_, 3, v___x_644_);
lean_closure_set(v___f_823_, 4, v___x_821_);
lean_closure_set(v___f_823_, 5, v___x_822_);
lean_inc(v___x_651_);
v___x_824_ = l_Lean_FVarId_getDecl___redArg(v___x_651_, v___y_657_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___x_826_; lean_object* v___x_827_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
v___x_826_ = l_Lean_LocalDecl_type(v_a_825_);
lean_dec(v_a_825_);
v___x_827_ = l_Lean_Meta_matchEq_x3f(v___x_826_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; lean_object* v___y_830_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
if (lean_obj_tag(v_a_828_) == 0)
{
lean_object* v___x_900_; lean_object* v___x_901_; 
lean_dec_ref(v___f_823_);
lean_dec_ref(v_type_820_);
lean_dec(v_a_653_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v___x_900_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__11, &l_Lean_Meta_substCore___lam__1___closed__11_once, _init_l_Lean_Meta_substCore___lam__1___closed__11);
v___x_901_ = l_panic___at___00Lean_Meta_substCore_spec__6(v___x_900_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
return v___x_901_;
}
else
{
lean_object* v_val_902_; lean_object* v_snd_903_; 
v_val_902_ = lean_ctor_get(v_a_828_, 0);
lean_inc(v_val_902_);
lean_dec_ref_known(v_a_828_, 1);
v_snd_903_ = lean_ctor_get(v_val_902_, 1);
lean_inc(v_snd_903_);
lean_dec(v_val_902_);
if (v_symm_654_ == 0)
{
lean_object* v_snd_904_; 
v_snd_904_ = lean_ctor_get(v_snd_903_, 1);
lean_inc(v_snd_904_);
lean_dec(v_snd_903_);
v___y_830_ = v_snd_904_;
goto v___jp_829_;
}
else
{
lean_object* v_fst_905_; 
v_fst_905_ = lean_ctor_get(v_snd_903_, 0);
lean_inc(v_fst_905_);
lean_dec(v_snd_903_);
v___y_830_ = v_fst_905_;
goto v___jp_829_;
}
}
v___jp_829_:
{
lean_object* v___x_831_; lean_object* v_a_832_; lean_object* v___x_833_; lean_object* v_a_834_; uint8_t v___x_835_; 
v___x_831_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_830_, v___y_658_);
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref(v___x_831_);
lean_inc(v___x_651_);
lean_inc_ref(v_type_820_);
v___x_833_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_type_820_, v___x_651_, v___y_658_);
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref(v___x_833_);
v___x_835_ = lean_unbox(v_a_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_837_; uint8_t v___x_838_; lean_object* v___x_839_; 
lean_dec_ref(v___f_823_);
v___x_836_ = lean_mk_empty_array_with_capacity(v___x_656_);
lean_inc_ref(v___x_644_);
v___x_837_ = lean_array_push(v___x_836_, v___x_644_);
v___x_838_ = 1;
lean_inc_ref(v_type_820_);
v___x_839_ = l_Lean_Meta_mkLambdaFVars(v___x_837_, v_type_820_, v___x_655_, v___x_648_, v___x_655_, v___x_648_, v___x_838_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v___x_837_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; uint8_t v___x_842_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
lean_inc_ref(v___x_644_);
v___x_841_ = l_Lean_Expr_replaceFVar(v_type_820_, v___x_644_, v_a_832_);
lean_dec_ref(v_type_820_);
v___x_842_ = lean_unbox(v_a_834_);
lean_dec(v_a_834_);
v___y_804_ = v_a_832_;
v___y_805_ = v___x_842_;
v_motive_806_ = v_a_840_;
v_newType_807_ = v___x_841_;
goto v___jp_803_;
}
else
{
lean_object* v_a_843_; lean_object* v___x_845_; uint8_t v_isShared_846_; uint8_t v_isSharedCheck_850_; 
lean_dec(v_a_834_);
lean_dec(v_a_832_);
lean_dec_ref(v_type_820_);
lean_dec(v_a_653_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_843_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_850_ == 0)
{
v___x_845_ = v___x_839_;
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
else
{
lean_inc(v_a_843_);
lean_dec(v___x_839_);
v___x_845_ = lean_box(0);
v_isShared_846_ = v_isSharedCheck_850_;
goto v_resetjp_844_;
}
v_resetjp_844_:
{
lean_object* v___x_848_; 
if (v_isShared_846_ == 0)
{
v___x_848_ = v___x_845_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v_a_843_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
}
else
{
lean_object* v___x_851_; lean_object* v___x_852_; 
lean_inc_ref(v___x_644_);
v___x_851_ = l_Lean_Expr_replaceFVar(v_type_820_, v___x_644_, v_a_832_);
lean_inc(v_a_832_);
v___x_852_ = l_Lean_Meta_mkEqRefl(v_a_832_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
lean_inc_ref(v___x_640_);
v___x_854_ = l_Lean_Expr_replaceFVar(v___x_851_, v___x_640_, v_a_853_);
lean_dec(v_a_853_);
lean_dec_ref(v___x_851_);
if (v_symm_654_ == 0)
{
lean_object* v___x_855_; 
lean_dec_ref(v_type_820_);
lean_inc_ref(v___x_644_);
lean_inc(v_a_832_);
v___x_855_ = l_Lean_Meta_mkEq(v_a_832_, v___x_644_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__7));
v___x_858_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v___x_857_, v_a_856_, v___f_823_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; uint8_t v___x_860_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
v___x_860_ = lean_unbox(v_a_834_);
lean_dec(v_a_834_);
v___y_804_ = v_a_832_;
v___y_805_ = v___x_860_;
v_motive_806_ = v_a_859_;
v_newType_807_ = v___x_854_;
goto v___jp_803_;
}
else
{
lean_object* v_a_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_868_; 
lean_dec_ref(v___x_854_);
lean_dec(v_a_834_);
lean_dec(v_a_832_);
lean_dec(v_a_653_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_861_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_868_ == 0)
{
v___x_863_ = v___x_858_;
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_a_861_);
lean_dec(v___x_858_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_868_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
lean_object* v___x_866_; 
if (v_isShared_864_ == 0)
{
v___x_866_ = v___x_863_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v_a_861_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
else
{
lean_object* v_a_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_876_; 
lean_dec_ref(v___x_854_);
lean_dec(v_a_834_);
lean_dec(v_a_832_);
lean_dec_ref(v___f_823_);
lean_dec(v_a_653_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_869_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_876_ == 0)
{
v___x_871_ = v___x_855_;
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_a_869_);
lean_dec(v___x_855_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_876_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_874_; 
if (v_isShared_872_ == 0)
{
v___x_874_ = v___x_871_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
else
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; uint8_t v___x_880_; lean_object* v___x_881_; 
lean_dec_ref(v___f_823_);
v___x_877_ = lean_mk_empty_array_with_capacity(v___x_645_);
lean_inc_ref(v___x_644_);
v___x_878_ = lean_array_push(v___x_877_, v___x_644_);
lean_inc_ref(v___x_640_);
v___x_879_ = lean_array_push(v___x_878_, v___x_640_);
v___x_880_ = 1;
v___x_881_ = l_Lean_Meta_mkLambdaFVars(v___x_879_, v_type_820_, v___x_655_, v___x_648_, v___x_655_, v___x_648_, v___x_880_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v___x_879_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; uint8_t v___x_883_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
v___x_883_ = lean_unbox(v_a_834_);
lean_dec(v_a_834_);
v___y_804_ = v_a_832_;
v___y_805_ = v___x_883_;
v_motive_806_ = v_a_882_;
v_newType_807_ = v___x_854_;
goto v___jp_803_;
}
else
{
lean_object* v_a_884_; lean_object* v___x_886_; uint8_t v_isShared_887_; uint8_t v_isSharedCheck_891_; 
lean_dec_ref(v___x_854_);
lean_dec(v_a_834_);
lean_dec(v_a_832_);
lean_dec(v_a_653_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_884_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_891_ == 0)
{
v___x_886_ = v___x_881_;
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
else
{
lean_inc(v_a_884_);
lean_dec(v___x_881_);
v___x_886_ = lean_box(0);
v_isShared_887_ = v_isSharedCheck_891_;
goto v_resetjp_885_;
}
v_resetjp_885_:
{
lean_object* v___x_889_; 
if (v_isShared_887_ == 0)
{
v___x_889_ = v___x_886_;
goto v_reusejp_888_;
}
else
{
lean_object* v_reuseFailAlloc_890_; 
v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_890_, 0, v_a_884_);
v___x_889_ = v_reuseFailAlloc_890_;
goto v_reusejp_888_;
}
v_reusejp_888_:
{
return v___x_889_;
}
}
}
}
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v___x_851_);
lean_dec(v_a_834_);
lean_dec(v_a_832_);
lean_dec_ref(v___f_823_);
lean_dec_ref(v_type_820_);
lean_dec(v_a_653_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_892_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_852_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_852_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v___x_897_; 
if (v_isShared_895_ == 0)
{
v___x_897_ = v___x_894_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_a_892_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
}
}
}
}
else
{
lean_object* v_a_906_; lean_object* v___x_908_; uint8_t v_isShared_909_; uint8_t v_isSharedCheck_913_; 
lean_dec_ref(v___f_823_);
lean_dec_ref(v_type_820_);
lean_dec(v_a_653_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_906_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_913_ == 0)
{
v___x_908_ = v___x_827_;
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
else
{
lean_inc(v_a_906_);
lean_dec(v___x_827_);
v___x_908_ = lean_box(0);
v_isShared_909_ = v_isSharedCheck_913_;
goto v_resetjp_907_;
}
v_resetjp_907_:
{
lean_object* v___x_911_; 
if (v_isShared_909_ == 0)
{
v___x_911_ = v___x_908_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v_a_906_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec_ref(v___f_823_);
lean_dec_ref(v_type_820_);
lean_dec(v_a_653_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_914_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_824_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_824_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_a_653_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_922_ = lean_ctor_get(v___x_818_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_818_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_818_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_818_);
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
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_662_:
{
lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_666_ = l_Lean_Meta_FVarSubst_insert(v___y_663_, v_fvarId_638_, v___y_665_);
v___x_667_ = l_Lean_Meta_FVarSubst_insert(v___x_666_, v_hFVarId_639_, v___x_640_);
v___x_668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
lean_ctor_set(v___x_668_, 1, v___y_664_);
v___x_669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_669_, 0, v___x_668_);
return v___x_669_;
}
v___jp_670_:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_array_get_size(v___y_671_);
v___x_675_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_641_, v___y_671_, v___x_674_, v___x_674_, v_fvarSubst_642_);
lean_dec_ref(v___y_671_);
if (v_clearH_643_ == 0)
{
lean_object* v_a_676_; 
lean_dec_ref(v___y_672_);
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref(v___x_675_);
v___y_663_ = v_a_676_;
v___y_664_ = v___y_673_;
v___y_665_ = v___x_644_;
goto v___jp_662_;
}
else
{
lean_object* v_a_677_; 
lean_dec_ref(v___x_644_);
v_a_677_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_677_);
lean_dec_ref(v___x_675_);
v___y_663_ = v_a_677_;
v___y_664_ = v___y_673_;
v___y_665_ = v___y_672_;
goto v___jp_662_;
}
}
v___jp_678_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_685_ = lean_array_get_size(v_fst_641_);
v___x_686_ = lean_nat_sub(v___x_685_, v___x_645_);
lean_dec(v___x_645_);
lean_inc(v___x_686_);
v___x_687_ = l_Lean_Meta_introNCore(v_mvarId_680_, v___x_686_, v___x_646_, v_skip_647_, v___x_648_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_object* v_a_688_; lean_object* v_toCold_689_; lean_object* v_options_690_; uint8_t v_hasTrace_691_; 
v_a_688_ = lean_ctor_get(v___x_687_, 0);
lean_inc(v_a_688_);
lean_dec_ref_known(v___x_687_, 1);
v_toCold_689_ = lean_ctor_get(v___y_683_, 0);
v_options_690_ = lean_ctor_get(v_toCold_689_, 2);
v_hasTrace_691_ = lean_ctor_get_uint8(v_options_690_, sizeof(void*)*1);
if (v_hasTrace_691_ == 0)
{
lean_object* v_fst_692_; lean_object* v_snd_693_; 
lean_dec(v___x_686_);
lean_dec(v___x_649_);
v_fst_692_ = lean_ctor_get(v_a_688_, 0);
lean_inc(v_fst_692_);
v_snd_693_ = lean_ctor_get(v_a_688_, 1);
lean_inc(v_snd_693_);
lean_dec(v_a_688_);
v___y_671_ = v_fst_692_;
v___y_672_ = v___y_679_;
v___y_673_ = v_snd_693_;
goto v___jp_670_;
}
else
{
lean_object* v_fst_694_; lean_object* v_snd_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_723_; 
v_fst_694_ = lean_ctor_get(v_a_688_, 0);
v_snd_695_ = lean_ctor_get(v_a_688_, 1);
v_isSharedCheck_723_ = !lean_is_exclusive(v_a_688_);
if (v_isSharedCheck_723_ == 0)
{
v___x_697_ = v_a_688_;
v_isShared_698_ = v_isSharedCheck_723_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_snd_695_);
lean_inc(v_fst_694_);
lean_dec(v_a_688_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_723_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_inheritedTraceOptions_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
v_inheritedTraceOptions_699_ = lean_ctor_get(v_toCold_689_, 11);
v___x_700_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
lean_inc(v___x_649_);
v___x_701_ = l_Lean_Name_append(v___x_700_, v___x_649_);
v___x_702_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_699_, v_options_690_, v___x_701_);
lean_dec(v___x_701_);
if (v___x_702_ == 0)
{
lean_del_object(v___x_697_);
lean_dec(v___x_686_);
lean_dec(v___x_649_);
v___y_671_ = v_fst_694_;
v___y_672_ = v___y_679_;
v___y_673_ = v_snd_695_;
goto v___jp_670_;
}
else
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_703_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__3, &l_Lean_Meta_substCore___lam__1___closed__3_once, _init_l_Lean_Meta_substCore___lam__1___closed__3);
v___x_704_ = l_Nat_reprFast(v___x_686_);
v___x_705_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_705_, 0, v___x_704_);
v___x_706_ = l_Lean_MessageData_ofFormat(v___x_705_);
if (v_isShared_698_ == 0)
{
lean_ctor_set_tag(v___x_697_, 7);
lean_ctor_set(v___x_697_, 1, v___x_706_);
lean_ctor_set(v___x_697_, 0, v___x_703_);
v___x_708_ = v___x_697_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_703_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v___x_706_);
v___x_708_ = v_reuseFailAlloc_722_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_709_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__5, &l_Lean_Meta_substCore___lam__1___closed__5_once, _init_l_Lean_Meta_substCore___lam__1___closed__5);
v___x_710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_710_, 0, v___x_708_);
lean_ctor_set(v___x_710_, 1, v___x_709_);
lean_inc(v_snd_695_);
v___x_711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_711_, 0, v_snd_695_);
v___x_712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_710_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
v___x_713_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_649_, v___x_712_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_dec_ref_known(v___x_713_, 1);
v___y_671_ = v_fst_694_;
v___y_672_ = v___y_679_;
v___y_673_ = v_snd_695_;
goto v___jp_670_;
}
else
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_721_; 
lean_dec(v_snd_695_);
lean_dec(v_fst_694_);
lean_dec_ref(v___y_679_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_721_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_721_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_721_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v___x_719_; 
if (v_isShared_717_ == 0)
{
v___x_719_ = v___x_716_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v_a_714_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
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
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_dec(v___x_686_);
lean_dec_ref(v___y_679_);
lean_dec(v___x_649_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_724_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_687_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_687_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_729_; 
if (v_isShared_727_ == 0)
{
v___x_729_ = v___x_726_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
v___jp_732_:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_snd_650_, v_newVal_735_, v___y_737_);
lean_dec_ref(v___x_740_);
v___x_741_ = l_Lean_Expr_mvarId_x21(v___y_733_);
lean_dec_ref(v___y_733_);
if (v_clearH_643_ == 0)
{
lean_dec(v___x_652_);
lean_dec(v___x_651_);
v___y_679_ = v___y_734_;
v_mvarId_680_ = v___x_741_;
v___y_681_ = v___y_736_;
v___y_682_ = v___y_737_;
v___y_683_ = v___y_738_;
v___y_684_ = v___y_739_;
goto v___jp_678_;
}
else
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_MVarId_clear(v___x_741_, v___x_651_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_742_) == 0)
{
lean_object* v_a_743_; lean_object* v___x_744_; 
v_a_743_ = lean_ctor_get(v___x_742_, 0);
lean_inc(v_a_743_);
lean_dec_ref_known(v___x_742_, 1);
v___x_744_ = l_Lean_MVarId_clear(v_a_743_, v___x_652_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
lean_inc(v_a_745_);
lean_dec_ref_known(v___x_744_, 1);
v___y_679_ = v___y_734_;
v_mvarId_680_ = v_a_745_;
v___y_681_ = v___y_736_;
v___y_682_ = v___y_737_;
v___y_683_ = v___y_738_;
v___y_684_ = v___y_739_;
goto v___jp_678_;
}
else
{
lean_object* v_a_746_; lean_object* v___x_748_; uint8_t v_isShared_749_; uint8_t v_isSharedCheck_753_; 
lean_dec_ref(v___y_734_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_746_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_753_ == 0)
{
v___x_748_ = v___x_744_;
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
else
{
lean_inc(v_a_746_);
lean_dec(v___x_744_);
v___x_748_ = lean_box(0);
v_isShared_749_ = v_isSharedCheck_753_;
goto v_resetjp_747_;
}
v_resetjp_747_:
{
lean_object* v___x_751_; 
if (v_isShared_749_ == 0)
{
v___x_751_ = v___x_748_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_a_746_);
v___x_751_ = v_reuseFailAlloc_752_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
return v___x_751_;
}
}
}
}
else
{
lean_object* v_a_754_; lean_object* v___x_756_; uint8_t v_isShared_757_; uint8_t v_isSharedCheck_761_; 
lean_dec_ref(v___y_734_);
lean_dec(v___x_652_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_754_ = lean_ctor_get(v___x_742_, 0);
v_isSharedCheck_761_ = !lean_is_exclusive(v___x_742_);
if (v_isSharedCheck_761_ == 0)
{
v___x_756_ = v___x_742_;
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
else
{
lean_inc(v_a_754_);
lean_dec(v___x_742_);
v___x_756_ = lean_box(0);
v_isShared_757_ = v_isSharedCheck_761_;
goto v_resetjp_755_;
}
v_resetjp_755_:
{
lean_object* v___x_759_; 
if (v_isShared_757_ == 0)
{
v___x_759_ = v___x_756_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
v___x_759_ = v_reuseFailAlloc_760_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
return v___x_759_;
}
}
}
}
}
v___jp_762_:
{
lean_object* v___x_772_; 
v___x_772_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_764_, v_a_653_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_772_) == 0)
{
if (v___y_766_ == 0)
{
lean_object* v_a_773_; lean_object* v___x_774_; 
v_a_773_ = lean_ctor_get(v___x_772_, 0);
lean_inc_n(v_a_773_, 2);
lean_dec_ref_known(v___x_772_, 1);
v___x_774_ = l_Lean_Meta_mkEqNDRec(v___y_763_, v_a_773_, v_major_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
lean_inc(v_a_775_);
lean_dec_ref_known(v___x_774_, 1);
v___y_733_ = v_a_773_;
v___y_734_ = v___y_765_;
v_newVal_735_ = v_a_775_;
v___y_736_ = v___y_768_;
v___y_737_ = v___y_769_;
v___y_738_ = v___y_770_;
v___y_739_ = v___y_771_;
goto v___jp_732_;
}
else
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_783_; 
lean_dec(v_a_773_);
lean_dec_ref(v___y_765_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_776_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_783_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_783_ == 0)
{
v___x_778_ = v___x_774_;
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_774_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_783_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v___x_781_; 
if (v_isShared_779_ == 0)
{
v___x_781_ = v___x_778_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_782_; 
v_reuseFailAlloc_782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_782_, 0, v_a_776_);
v___x_781_ = v_reuseFailAlloc_782_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
return v___x_781_;
}
}
}
}
else
{
lean_object* v_a_784_; lean_object* v___x_785_; 
v_a_784_ = lean_ctor_get(v___x_772_, 0);
lean_inc_n(v_a_784_, 2);
lean_dec_ref_known(v___x_772_, 1);
v___x_785_ = l_Lean_Meta_mkEqRec(v___y_763_, v_a_784_, v_major_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
if (lean_obj_tag(v___x_785_) == 0)
{
lean_object* v_a_786_; 
v_a_786_ = lean_ctor_get(v___x_785_, 0);
lean_inc(v_a_786_);
lean_dec_ref_known(v___x_785_, 1);
v___y_733_ = v_a_784_;
v___y_734_ = v___y_765_;
v_newVal_735_ = v_a_786_;
v___y_736_ = v___y_768_;
v___y_737_ = v___y_769_;
v___y_738_ = v___y_770_;
v___y_739_ = v___y_771_;
goto v___jp_732_;
}
else
{
lean_object* v_a_787_; lean_object* v___x_789_; uint8_t v_isShared_790_; uint8_t v_isSharedCheck_794_; 
lean_dec(v_a_784_);
lean_dec_ref(v___y_765_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_787_ = lean_ctor_get(v___x_785_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v___x_785_);
if (v_isSharedCheck_794_ == 0)
{
v___x_789_ = v___x_785_;
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
else
{
lean_inc(v_a_787_);
lean_dec(v___x_785_);
v___x_789_ = lean_box(0);
v_isShared_790_ = v_isSharedCheck_794_;
goto v_resetjp_788_;
}
v_resetjp_788_:
{
lean_object* v___x_792_; 
if (v_isShared_790_ == 0)
{
v___x_792_ = v___x_789_;
goto v_reusejp_791_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v_a_787_);
v___x_792_ = v_reuseFailAlloc_793_;
goto v_reusejp_791_;
}
v_reusejp_791_:
{
return v___x_792_;
}
}
}
}
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec_ref(v_major_767_);
lean_dec_ref(v___y_765_);
lean_dec_ref(v___y_763_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_795_ = lean_ctor_get(v___x_772_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_772_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_772_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_772_);
v___x_797_ = lean_box(0);
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
v_resetjp_796_:
{
lean_object* v___x_800_; 
if (v_isShared_798_ == 0)
{
v___x_800_ = v___x_797_;
goto v_reusejp_799_;
}
else
{
lean_object* v_reuseFailAlloc_801_; 
v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_801_, 0, v_a_795_);
v___x_800_ = v_reuseFailAlloc_801_;
goto v_reusejp_799_;
}
v_reusejp_799_:
{
return v___x_800_;
}
}
}
}
v___jp_803_:
{
if (v_symm_654_ == 0)
{
lean_object* v___x_808_; 
lean_inc_ref(v___x_640_);
v___x_808_ = l_Lean_Meta_mkEqSymm(v___x_640_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref_known(v___x_808_, 1);
v___y_763_ = v_motive_806_;
v___y_764_ = v_newType_807_;
v___y_765_ = v___y_804_;
v___y_766_ = v___y_805_;
v_major_767_ = v_a_809_;
v___y_768_ = v___y_657_;
v___y_769_ = v___y_658_;
v___y_770_ = v___y_659_;
v___y_771_ = v___y_660_;
goto v___jp_762_;
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec_ref(v_newType_807_);
lean_dec_ref(v_motive_806_);
lean_dec_ref(v___y_804_);
lean_dec(v_a_653_);
lean_dec(v___x_652_);
lean_dec(v___x_651_);
lean_dec(v_snd_650_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_645_);
lean_dec_ref(v___x_644_);
lean_dec(v_fvarSubst_642_);
lean_dec_ref(v___x_640_);
lean_dec(v_hFVarId_639_);
lean_dec(v_fvarId_638_);
v_a_810_ = lean_ctor_get(v___x_808_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_808_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_808_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_808_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
else
{
lean_inc_ref(v___x_640_);
v___y_763_ = v_motive_806_;
v___y_764_ = v_newType_807_;
v___y_765_ = v___y_804_;
v___y_766_ = v___y_805_;
v_major_767_ = v___x_640_;
v___y_768_ = v___y_657_;
v___y_769_ = v___y_658_;
v___y_770_ = v___y_659_;
v___y_771_ = v___y_660_;
goto v___jp_762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object** _args){
lean_object* v_fvarId_930_ = _args[0];
lean_object* v_hFVarId_931_ = _args[1];
lean_object* v___x_932_ = _args[2];
lean_object* v_fst_933_ = _args[3];
lean_object* v_fvarSubst_934_ = _args[4];
lean_object* v_clearH_935_ = _args[5];
lean_object* v___x_936_ = _args[6];
lean_object* v___x_937_ = _args[7];
lean_object* v___x_938_ = _args[8];
lean_object* v_skip_939_ = _args[9];
lean_object* v___x_940_ = _args[10];
lean_object* v___x_941_ = _args[11];
lean_object* v_snd_942_ = _args[12];
lean_object* v___x_943_ = _args[13];
lean_object* v___x_944_ = _args[14];
lean_object* v_a_945_ = _args[15];
lean_object* v_symm_946_ = _args[16];
lean_object* v___x_947_ = _args[17];
lean_object* v___x_948_ = _args[18];
lean_object* v___y_949_ = _args[19];
lean_object* v___y_950_ = _args[20];
lean_object* v___y_951_ = _args[21];
lean_object* v___y_952_ = _args[22];
lean_object* v___y_953_ = _args[23];
_start:
{
uint8_t v_clearH_boxed_954_; uint8_t v_skip_boxed_955_; uint8_t v___x_27786__boxed_956_; uint8_t v_symm_boxed_957_; uint8_t v___x_27792__boxed_958_; lean_object* v_res_959_; 
v_clearH_boxed_954_ = lean_unbox(v_clearH_935_);
v_skip_boxed_955_ = lean_unbox(v_skip_939_);
v___x_27786__boxed_956_ = lean_unbox(v___x_940_);
v_symm_boxed_957_ = lean_unbox(v_symm_946_);
v___x_27792__boxed_958_ = lean_unbox(v___x_947_);
v_res_959_ = l_Lean_Meta_substCore___lam__1(v_fvarId_930_, v_hFVarId_931_, v___x_932_, v_fst_933_, v_fvarSubst_934_, v_clearH_boxed_954_, v___x_936_, v___x_937_, v___x_938_, v_skip_boxed_955_, v___x_27786__boxed_956_, v___x_941_, v_snd_942_, v___x_943_, v___x_944_, v_a_945_, v_symm_boxed_957_, v___x_27792__boxed_958_, v___x_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___x_948_);
lean_dec_ref(v_fst_933_);
return v_res_959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object* v___x_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_, lean_object* v___y_964_){
_start:
{
lean_object* v_toCold_966_; lean_object* v_options_967_; uint8_t v_hasTrace_968_; 
v_toCold_966_ = lean_ctor_get(v___y_963_, 0);
v_options_967_ = lean_ctor_get(v_toCold_966_, 2);
v_hasTrace_968_ = lean_ctor_get_uint8(v_options_967_, sizeof(void*)*1);
if (v_hasTrace_968_ == 0)
{
lean_object* v___x_969_; lean_object* v___x_970_; 
lean_dec(v___x_960_);
v___x_969_ = lean_box(v_hasTrace_968_);
v___x_970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_970_, 0, v___x_969_);
return v___x_970_;
}
else
{
lean_object* v_inheritedTraceOptions_971_; lean_object* v___x_972_; lean_object* v___x_973_; uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
v_inheritedTraceOptions_971_ = lean_ctor_get(v_toCold_966_, 11);
v___x_972_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
v___x_973_ = l_Lean_Name_append(v___x_972_, v___x_960_);
v___x_974_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_971_, v_options_967_, v___x_973_);
lean_dec(v___x_973_);
v___x_975_ = lean_box(v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object* v___x_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_, lean_object* v___y_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l_Lean_Meta_substCore___lam__2(v___x_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(lean_object* v_a_984_, lean_object* v_a_985_){
_start:
{
if (lean_obj_tag(v_a_984_) == 0)
{
lean_object* v___x_986_; 
v___x_986_ = l_List_reverse___redArg(v_a_985_);
return v___x_986_;
}
else
{
lean_object* v_head_987_; lean_object* v_tail_988_; lean_object* v___x_990_; uint8_t v_isShared_991_; uint8_t v_isSharedCheck_997_; 
v_head_987_ = lean_ctor_get(v_a_984_, 0);
v_tail_988_ = lean_ctor_get(v_a_984_, 1);
v_isSharedCheck_997_ = !lean_is_exclusive(v_a_984_);
if (v_isSharedCheck_997_ == 0)
{
v___x_990_ = v_a_984_;
v_isShared_991_ = v_isSharedCheck_997_;
goto v_resetjp_989_;
}
else
{
lean_inc(v_tail_988_);
lean_inc(v_head_987_);
lean_dec(v_a_984_);
v___x_990_ = lean_box(0);
v_isShared_991_ = v_isSharedCheck_997_;
goto v_resetjp_989_;
}
v_resetjp_989_:
{
lean_object* v___x_992_; lean_object* v___x_994_; 
v___x_992_ = l_Lean_MessageData_ofName(v_head_987_);
if (v_isShared_991_ == 0)
{
lean_ctor_set(v___x_990_, 1, v_a_985_);
lean_ctor_set(v___x_990_, 0, v___x_992_);
v___x_994_ = v___x_990_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_992_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_a_985_);
v___x_994_ = v_reuseFailAlloc_996_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
v_a_984_ = v_tail_988_;
v_a_985_ = v___x_994_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(size_t v_sz_998_, size_t v_i_999_, lean_object* v_bs_1000_){
_start:
{
uint8_t v___x_1001_; 
v___x_1001_ = lean_usize_dec_lt(v_i_999_, v_sz_998_);
if (v___x_1001_ == 0)
{
return v_bs_1000_;
}
else
{
lean_object* v_v_1002_; lean_object* v___x_1003_; lean_object* v_bs_x27_1004_; size_t v___x_1005_; size_t v___x_1006_; lean_object* v___x_1007_; 
v_v_1002_ = lean_array_uget(v_bs_1000_, v_i_999_);
v___x_1003_ = lean_unsigned_to_nat(0u);
v_bs_x27_1004_ = lean_array_uset(v_bs_1000_, v_i_999_, v___x_1003_);
v___x_1005_ = ((size_t)1ULL);
v___x_1006_ = lean_usize_add(v_i_999_, v___x_1005_);
v___x_1007_ = lean_array_uset(v_bs_x27_1004_, v_i_999_, v_v_1002_);
v_i_999_ = v___x_1006_;
v_bs_1000_ = v___x_1007_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8___boxed(lean_object* v_sz_1009_, lean_object* v_i_1010_, lean_object* v_bs_1011_){
_start:
{
size_t v_sz_boxed_1012_; size_t v_i_boxed_1013_; lean_object* v_res_1014_; 
v_sz_boxed_1012_ = lean_unbox_usize(v_sz_1009_);
lean_dec(v_sz_1009_);
v_i_boxed_1013_ = lean_unbox_usize(v_i_1010_);
lean_dec(v_i_1010_);
v_res_1014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_boxed_1012_, v_i_boxed_1013_, v_bs_1011_);
return v_res_1014_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__2));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__4));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__7));
v___x_1028_ = l_Lean_MessageData_ofFormat(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__9(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__8, &l_Lean_Meta_substCore___lam__3___closed__8_once, _init_l_Lean_Meta_substCore___lam__3___closed__8);
v___x_1030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1030_, 0, v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__11(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__10));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__13(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__12));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__15(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__14));
v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__17(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__16));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__19(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__18));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__25(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__24));
v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__27(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__26));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__29(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__28));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3(lean_object* v_mvarId_1065_, lean_object* v_hFVarId_1066_, lean_object* v___x_1067_, uint8_t v_clearH_1068_, lean_object* v_fvarSubst_1069_, uint8_t v_symm_1070_, uint8_t v_tryToSkip_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_){
_start:
{
lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___x_1115_; 
lean_inc(v_mvarId_1065_);
v___x_1115_ = l_Lean_MVarId_getTag(v_mvarId_1065_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1117_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
lean_inc(v_mvarId_1065_);
v___x_1118_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1065_, v___x_1117_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1119_; 
lean_dec_ref_known(v___x_1118_, 1);
lean_inc(v_hFVarId_1066_);
v___x_1119_ = l_Lean_FVarId_getDecl___redArg(v_hFVarId_1066_, v___y_1072_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; lean_object* v___x_1121_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___x_1136_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v___x_1121_ = l_Lean_LocalDecl_type(v_a_1120_);
lean_dec(v_a_1120_);
lean_inc_ref(v___x_1121_);
v___x_1136_ = l_Lean_Meta_matchEq_x3f(v___x_1121_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1136_) == 0)
{
lean_object* v_a_1137_; 
v_a_1137_ = lean_ctor_get(v___x_1136_, 0);
lean_inc(v_a_1137_);
lean_dec_ref_known(v___x_1136_, 1);
if (lean_obj_tag(v_a_1137_) == 0)
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec_ref(v___x_1121_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
v___x_1138_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__9, &l_Lean_Meta_substCore___lam__3___closed__9_once, _init_l_Lean_Meta_substCore___lam__3___closed__9);
v___x_1139_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1117_, v_mvarId_1065_, v___x_1138_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v___x_1139_;
}
else
{
lean_object* v_val_1140_; lean_object* v___x_1142_; uint8_t v_isShared_1143_; uint8_t v_isSharedCheck_1458_; 
v_val_1140_ = lean_ctor_get(v_a_1137_, 0);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_a_1137_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1142_ = v_a_1137_;
v_isShared_1143_ = v_isSharedCheck_1458_;
goto v_resetjp_1141_;
}
else
{
lean_inc(v_val_1140_);
lean_dec(v_a_1137_);
v___x_1142_ = lean_box(0);
v_isShared_1143_ = v_isSharedCheck_1458_;
goto v_resetjp_1141_;
}
v_resetjp_1141_:
{
lean_object* v_snd_1144_; lean_object* v___x_1146_; uint8_t v_isShared_1147_; uint8_t v_isSharedCheck_1456_; 
v_snd_1144_ = lean_ctor_get(v_val_1140_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_val_1140_);
if (v_isSharedCheck_1456_ == 0)
{
lean_object* v_unused_1457_; 
v_unused_1457_ = lean_ctor_get(v_val_1140_, 0);
lean_dec(v_unused_1457_);
v___x_1146_ = v_val_1140_;
v_isShared_1147_ = v_isSharedCheck_1456_;
goto v_resetjp_1145_;
}
else
{
lean_inc(v_snd_1144_);
lean_dec(v_val_1140_);
v___x_1146_ = lean_box(0);
v_isShared_1147_ = v_isSharedCheck_1456_;
goto v_resetjp_1145_;
}
v_resetjp_1145_:
{
lean_object* v_fst_1148_; lean_object* v_snd_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1455_; 
v_fst_1148_ = lean_ctor_get(v_snd_1144_, 0);
v_snd_1149_ = lean_ctor_get(v_snd_1144_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_snd_1144_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1151_ = v_snd_1144_;
v_isShared_1152_ = v_isSharedCheck_1455_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_snd_1149_);
lean_inc(v_fst_1148_);
lean_dec(v_snd_1144_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1455_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
uint8_t v___x_1153_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; uint8_t v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; uint8_t v_skip_1172_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; uint8_t v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; uint8_t v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; uint8_t v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; uint8_t v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; uint8_t v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1418_; lean_object* v___y_1419_; lean_object* v___y_1451_; 
v___x_1153_ = 1;
if (v_symm_1070_ == 0)
{
lean_inc(v_fst_1148_);
v___y_1451_ = v_fst_1148_;
goto v___jp_1450_;
}
else
{
lean_inc(v_snd_1149_);
v___y_1451_ = v_snd_1149_;
goto v___jp_1450_;
}
v___jp_1154_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; 
v___x_1173_ = lean_box(v_clearH_1068_);
v___x_1174_ = lean_box(v_skip_1172_);
v___x_1175_ = lean_box(v___x_1153_);
v___x_1176_ = lean_box(v_symm_1070_);
v___x_1177_ = lean_box(v___y_1161_);
v___f_1178_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 24, 19);
lean_closure_set(v___f_1178_, 0, v___y_1163_);
lean_closure_set(v___f_1178_, 1, v_hFVarId_1066_);
lean_closure_set(v___f_1178_, 2, v___y_1164_);
lean_closure_set(v___f_1178_, 3, v___y_1156_);
lean_closure_set(v___f_1178_, 4, v_fvarSubst_1069_);
lean_closure_set(v___f_1178_, 5, v___x_1173_);
lean_closure_set(v___f_1178_, 6, v___y_1159_);
lean_closure_set(v___f_1178_, 7, v___y_1167_);
lean_closure_set(v___f_1178_, 8, v___y_1169_);
lean_closure_set(v___f_1178_, 9, v___x_1174_);
lean_closure_set(v___f_1178_, 10, v___x_1175_);
lean_closure_set(v___f_1178_, 11, v___y_1158_);
lean_closure_set(v___f_1178_, 12, v___y_1162_);
lean_closure_set(v___f_1178_, 13, v___y_1171_);
lean_closure_set(v___f_1178_, 14, v___y_1165_);
lean_closure_set(v___f_1178_, 15, v_a_1116_);
lean_closure_set(v___f_1178_, 16, v___x_1176_);
lean_closure_set(v___f_1178_, 17, v___x_1177_);
lean_closure_set(v___f_1178_, 18, v___y_1157_);
v___x_1179_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v___y_1170_, v___f_1178_, v___y_1160_, v___y_1155_, v___y_1168_, v___y_1166_);
lean_dec(v___y_1166_);
lean_dec_ref(v___y_1168_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1160_);
return v___x_1179_;
}
v___jp_1180_:
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; 
v___x_1197_ = lean_unsigned_to_nat(0u);
v___x_1198_ = lean_array_get(v___x_1067_, v___y_1191_, v___x_1197_);
lean_inc(v___x_1198_);
v___x_1199_ = l_Lean_mkFVar(v___x_1198_);
v___x_1200_ = lean_unsigned_to_nat(1u);
v___x_1201_ = lean_array_get(v___x_1067_, v___y_1191_, v___x_1200_);
lean_dec_ref(v___y_1191_);
lean_inc(v___x_1201_);
v___x_1202_ = l_Lean_mkFVar(v___x_1201_);
if (v_tryToSkip_1071_ == 0)
{
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1188_);
v___y_1155_ = v___y_1194_;
v___y_1156_ = v___y_1182_;
v___y_1157_ = v___x_1200_;
v___y_1158_ = v___y_1183_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1193_;
v___y_1161_ = v___y_1185_;
v___y_1162_ = v___y_1186_;
v___y_1163_ = v___y_1187_;
v___y_1164_ = v___x_1202_;
v___y_1165_ = v___x_1198_;
v___y_1166_ = v___y_1196_;
v___y_1167_ = v___y_1181_;
v___y_1168_ = v___y_1195_;
v___y_1169_ = v___y_1184_;
v___y_1170_ = v___y_1190_;
v___y_1171_ = v___x_1201_;
v_skip_1172_ = v___y_1189_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1203_ = lean_array_get_size(v___y_1192_);
lean_dec_ref(v___y_1192_);
v___x_1204_ = lean_nat_dec_eq(v___x_1203_, v___y_1188_);
lean_dec(v___y_1188_);
if (v___x_1204_ == 0)
{
v___y_1155_ = v___y_1194_;
v___y_1156_ = v___y_1182_;
v___y_1157_ = v___x_1200_;
v___y_1158_ = v___y_1183_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1193_;
v___y_1161_ = v___y_1185_;
v___y_1162_ = v___y_1186_;
v___y_1163_ = v___y_1187_;
v___y_1164_ = v___x_1202_;
v___y_1165_ = v___x_1198_;
v___y_1166_ = v___y_1196_;
v___y_1167_ = v___y_1181_;
v___y_1168_ = v___y_1195_;
v___y_1169_ = v___y_1184_;
v___y_1170_ = v___y_1190_;
v___y_1171_ = v___x_1201_;
v_skip_1172_ = v___y_1189_;
goto v___jp_1154_;
}
else
{
lean_object* v___x_1205_; 
lean_inc(v___y_1190_);
v___x_1205_ = l_Lean_MVarId_getType(v___y_1190_, v___y_1193_, v___y_1194_, v___y_1195_, v___y_1196_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1207_; lean_object* v_a_1208_; uint8_t v___x_1209_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc_n(v_a_1206_, 2);
lean_dec_ref_known(v___x_1205_, 1);
lean_inc(v___x_1198_);
v___x_1207_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1206_, v___x_1198_, v___y_1194_);
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = lean_unbox(v_a_1208_);
lean_dec(v_a_1208_);
if (v___x_1209_ == 0)
{
lean_object* v___x_1210_; lean_object* v_a_1211_; uint8_t v___x_1212_; 
lean_inc(v___x_1201_);
v___x_1210_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1206_, v___x_1201_, v___y_1194_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = lean_unbox(v_a_1211_);
lean_dec(v_a_1211_);
if (v___x_1212_ == 0)
{
lean_dec_ref(v___x_1202_);
lean_dec_ref(v___x_1199_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec(v_a_1116_);
lean_dec(v_hFVarId_1066_);
v___y_1078_ = v___y_1194_;
v___y_1079_ = v___y_1195_;
v___y_1080_ = v___y_1190_;
v___y_1081_ = v___y_1193_;
v___y_1082_ = v___x_1201_;
v___y_1083_ = v___x_1198_;
v___y_1084_ = v___y_1196_;
goto v___jp_1077_;
}
else
{
v___y_1155_ = v___y_1194_;
v___y_1156_ = v___y_1182_;
v___y_1157_ = v___x_1200_;
v___y_1158_ = v___y_1183_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1193_;
v___y_1161_ = v___y_1185_;
v___y_1162_ = v___y_1186_;
v___y_1163_ = v___y_1187_;
v___y_1164_ = v___x_1202_;
v___y_1165_ = v___x_1198_;
v___y_1166_ = v___y_1196_;
v___y_1167_ = v___y_1181_;
v___y_1168_ = v___y_1195_;
v___y_1169_ = v___y_1184_;
v___y_1170_ = v___y_1190_;
v___y_1171_ = v___x_1201_;
v_skip_1172_ = v___y_1189_;
goto v___jp_1154_;
}
}
else
{
lean_dec(v_a_1206_);
v___y_1155_ = v___y_1194_;
v___y_1156_ = v___y_1182_;
v___y_1157_ = v___x_1200_;
v___y_1158_ = v___y_1183_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1193_;
v___y_1161_ = v___y_1185_;
v___y_1162_ = v___y_1186_;
v___y_1163_ = v___y_1187_;
v___y_1164_ = v___x_1202_;
v___y_1165_ = v___x_1198_;
v___y_1166_ = v___y_1196_;
v___y_1167_ = v___y_1181_;
v___y_1168_ = v___y_1195_;
v___y_1169_ = v___y_1184_;
v___y_1170_ = v___y_1190_;
v___y_1171_ = v___x_1201_;
v_skip_1172_ = v___y_1189_;
goto v___jp_1154_;
}
}
else
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1220_; 
lean_dec_ref(v___x_1202_);
lean_dec(v___x_1201_);
lean_dec_ref(v___x_1199_);
lean_dec(v___x_1198_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1194_);
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1190_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
v_a_1213_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1220_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1215_ = v___x_1205_;
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1205_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1220_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1218_; 
if (v_isShared_1216_ == 0)
{
v___x_1218_ = v___x_1215_;
goto v_reusejp_1217_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_a_1213_);
v___x_1218_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1217_;
}
v_reusejp_1217_:
{
return v___x_1218_;
}
}
}
}
}
}
v___jp_1221_:
{
lean_object* v___x_1239_; 
lean_inc_ref(v___y_1231_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
lean_inc(v___y_1236_);
lean_inc_ref(v___y_1235_);
v___x_1239_ = lean_apply_5(v___y_1231_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_, lean_box(0));
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; uint8_t v___x_1241_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
lean_inc(v_a_1240_);
lean_dec_ref_known(v___x_1239_, 1);
v___x_1241_ = lean_unbox(v_a_1240_);
lean_dec(v_a_1240_);
if (v___x_1241_ == 0)
{
lean_dec(v___y_1233_);
lean_del_object(v___x_1151_);
lean_inc(v___y_1227_);
v___y_1181_ = v___y_1222_;
v___y_1182_ = v___y_1223_;
v___y_1183_ = v___y_1224_;
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1226_;
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1230_;
v___y_1189_ = v___y_1232_;
v___y_1190_ = v___y_1227_;
v___y_1191_ = v___y_1229_;
v___y_1192_ = v___y_1234_;
v___y_1193_ = v___y_1235_;
v___y_1194_ = v___y_1236_;
v___y_1195_ = v___y_1237_;
v___y_1196_ = v___y_1238_;
goto v___jp_1180_;
}
else
{
lean_object* v___x_1242_; size_t v_sz_1243_; size_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1242_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__11, &l_Lean_Meta_substCore___lam__3___closed__11_once, _init_l_Lean_Meta_substCore___lam__3___closed__11);
v_sz_1243_ = lean_array_size(v___y_1234_);
v___x_1244_ = ((size_t)0ULL);
lean_inc_ref(v___y_1234_);
v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1243_, v___x_1244_, v___y_1234_);
v___x_1246_ = lean_array_to_list(v___x_1245_);
v___x_1247_ = lean_box(0);
v___x_1248_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(v___x_1246_, v___x_1247_);
v___x_1249_ = l_Lean_MessageData_ofList(v___x_1248_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 7);
lean_ctor_set(v___x_1151_, 1, v___x_1249_);
lean_ctor_set(v___x_1151_, 0, v___x_1242_);
v___x_1251_ = v___x_1151_;
goto v_reusejp_1250_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v___x_1242_);
lean_ctor_set(v_reuseFailAlloc_1261_, 1, v___x_1249_);
v___x_1251_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1250_;
}
v_reusejp_1250_:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1233_, v___x_1251_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_dec_ref_known(v___x_1252_, 1);
lean_inc(v___y_1227_);
v___y_1181_ = v___y_1222_;
v___y_1182_ = v___y_1223_;
v___y_1183_ = v___y_1224_;
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1226_;
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1230_;
v___y_1189_ = v___y_1232_;
v___y_1190_ = v___y_1227_;
v___y_1191_ = v___y_1229_;
v___y_1192_ = v___y_1234_;
v___y_1193_ = v___y_1235_;
v___y_1194_ = v___y_1236_;
v___y_1195_ = v___y_1237_;
v___y_1196_ = v___y_1238_;
goto v___jp_1180_;
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
v_a_1253_ = lean_ctor_get(v___x_1252_, 0);
v_isSharedCheck_1260_ = !lean_is_exclusive(v___x_1252_);
if (v_isSharedCheck_1260_ == 0)
{
v___x_1255_ = v___x_1252_;
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
else
{
lean_inc(v_a_1253_);
lean_dec(v___x_1252_);
v___x_1255_ = lean_box(0);
v_isShared_1256_ = v_isSharedCheck_1260_;
goto v_resetjp_1254_;
}
v_resetjp_1254_:
{
lean_object* v___x_1258_; 
if (v_isShared_1256_ == 0)
{
v___x_1258_ = v___x_1255_;
goto v_reusejp_1257_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
v___x_1258_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1257_;
}
v_reusejp_1257_:
{
return v___x_1258_;
}
}
}
}
}
}
else
{
lean_object* v_a_1262_; lean_object* v___x_1264_; uint8_t v_isShared_1265_; uint8_t v_isSharedCheck_1269_; 
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1223_);
lean_dec(v___y_1222_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
v_a_1262_ = lean_ctor_get(v___x_1239_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1239_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1264_ = v___x_1239_;
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
else
{
lean_inc(v_a_1262_);
lean_dec(v___x_1239_);
v___x_1264_ = lean_box(0);
v_isShared_1265_ = v_isSharedCheck_1269_;
goto v_resetjp_1263_;
}
v_resetjp_1263_:
{
lean_object* v___x_1267_; 
if (v_isShared_1265_ == 0)
{
v___x_1267_ = v___x_1264_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v_a_1262_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
v___jp_1270_:
{
lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1285_ = lean_box(0);
lean_inc(v___y_1277_);
v___x_1286_ = l_Lean_Meta_introNCore(v___y_1272_, v___y_1277_, v___x_1285_, v___y_1279_, v___x_1153_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v_a_1287_; lean_object* v_fst_1288_; lean_object* v_snd_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1318_; 
v_a_1287_ = lean_ctor_get(v___x_1286_, 0);
lean_inc(v_a_1287_);
lean_dec_ref_known(v___x_1286_, 1);
v_fst_1288_ = lean_ctor_get(v_a_1287_, 0);
v_snd_1289_ = lean_ctor_get(v_a_1287_, 1);
v_isSharedCheck_1318_ = !lean_is_exclusive(v_a_1287_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1291_ = v_a_1287_;
v_isShared_1292_ = v_isSharedCheck_1318_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_snd_1289_);
lean_inc(v_fst_1288_);
lean_dec(v_a_1287_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1318_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v___x_1293_; 
lean_inc_ref(v___y_1278_);
lean_inc(v___y_1284_);
lean_inc_ref(v___y_1283_);
lean_inc(v___y_1282_);
lean_inc_ref(v___y_1281_);
v___x_1293_ = lean_apply_5(v___y_1278_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_, lean_box(0));
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; uint8_t v___x_1295_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref_known(v___x_1293_, 1);
v___x_1295_ = lean_unbox(v_a_1294_);
lean_dec(v_a_1294_);
if (v___x_1295_ == 0)
{
lean_del_object(v___x_1291_);
lean_inc_ref(v___y_1273_);
v___y_1222_ = v___y_1271_;
v___y_1223_ = v___y_1273_;
v___y_1224_ = v___y_1274_;
v___y_1225_ = v___x_1285_;
v___y_1226_ = v___y_1275_;
v___y_1227_ = v_snd_1289_;
v___y_1228_ = v___y_1276_;
v___y_1229_ = v_fst_1288_;
v___y_1230_ = v___y_1277_;
v___y_1231_ = v___y_1278_;
v___y_1232_ = v___y_1279_;
v___y_1233_ = v___y_1280_;
v___y_1234_ = v___y_1273_;
v___y_1235_ = v___y_1281_;
v___y_1236_ = v___y_1282_;
v___y_1237_ = v___y_1283_;
v___y_1238_ = v___y_1284_;
goto v___jp_1221_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1299_; 
v___x_1296_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__13, &l_Lean_Meta_substCore___lam__3___closed__13_once, _init_l_Lean_Meta_substCore___lam__3___closed__13);
lean_inc(v_snd_1289_);
v___x_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1297_, 0, v_snd_1289_);
if (v_isShared_1292_ == 0)
{
lean_ctor_set_tag(v___x_1291_, 7);
lean_ctor_set(v___x_1291_, 1, v___x_1297_);
lean_ctor_set(v___x_1291_, 0, v___x_1296_);
v___x_1299_ = v___x_1291_;
goto v_reusejp_1298_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v___x_1296_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1297_);
v___x_1299_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1298_;
}
v_reusejp_1298_:
{
lean_object* v___x_1300_; 
lean_inc(v___y_1280_);
v___x_1300_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1280_, v___x_1299_, v___y_1281_, v___y_1282_, v___y_1283_, v___y_1284_);
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_dec_ref_known(v___x_1300_, 1);
lean_inc_ref(v___y_1273_);
v___y_1222_ = v___y_1271_;
v___y_1223_ = v___y_1273_;
v___y_1224_ = v___y_1274_;
v___y_1225_ = v___x_1285_;
v___y_1226_ = v___y_1275_;
v___y_1227_ = v_snd_1289_;
v___y_1228_ = v___y_1276_;
v___y_1229_ = v_fst_1288_;
v___y_1230_ = v___y_1277_;
v___y_1231_ = v___y_1278_;
v___y_1232_ = v___y_1279_;
v___y_1233_ = v___y_1280_;
v___y_1234_ = v___y_1273_;
v___y_1235_ = v___y_1281_;
v___y_1236_ = v___y_1282_;
v___y_1237_ = v___y_1283_;
v___y_1238_ = v___y_1284_;
goto v___jp_1221_;
}
else
{
lean_object* v_a_1301_; lean_object* v___x_1303_; uint8_t v_isShared_1304_; uint8_t v_isSharedCheck_1308_; 
lean_dec(v_snd_1289_);
lean_dec(v_fst_1288_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1271_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1308_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1308_ == 0)
{
v___x_1303_ = v___x_1300_;
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
else
{
lean_inc(v_a_1301_);
lean_dec(v___x_1300_);
v___x_1303_ = lean_box(0);
v_isShared_1304_ = v_isSharedCheck_1308_;
goto v_resetjp_1302_;
}
v_resetjp_1302_:
{
lean_object* v___x_1306_; 
if (v_isShared_1304_ == 0)
{
v___x_1306_ = v___x_1303_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1307_; 
v_reuseFailAlloc_1307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_a_1301_);
v___x_1306_ = v_reuseFailAlloc_1307_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
return v___x_1306_;
}
}
}
}
}
}
else
{
lean_object* v_a_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1317_; 
lean_del_object(v___x_1291_);
lean_dec(v_snd_1289_);
lean_dec(v_fst_1288_);
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1271_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
v_a_1310_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1317_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1312_ = v___x_1293_;
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_a_1310_);
lean_dec(v___x_1293_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1317_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v___x_1315_; 
if (v_isShared_1313_ == 0)
{
v___x_1315_ = v___x_1312_;
goto v_reusejp_1314_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v_a_1310_);
v___x_1315_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1314_;
}
v_reusejp_1314_:
{
return v___x_1315_;
}
}
}
}
}
else
{
lean_object* v_a_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1326_; 
lean_dec(v___y_1284_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec_ref(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1271_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
v_a_1319_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1326_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1321_ = v___x_1286_;
v_isShared_1322_ = v_isSharedCheck_1326_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_a_1319_);
lean_dec(v___x_1286_);
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
lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; 
v___x_1337_ = lean_unsigned_to_nat(2u);
v___x_1338_ = lean_mk_empty_array_with_capacity(v___x_1337_);
v___x_1339_ = lean_array_push(v___x_1338_, v___y_1330_);
lean_inc(v_hFVarId_1066_);
v___x_1340_ = lean_array_push(v___x_1339_, v_hFVarId_1066_);
v___x_1341_ = 0;
v___x_1342_ = l_Lean_MVarId_revert(v_mvarId_1065_, v___x_1340_, v___x_1153_, v___x_1341_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1342_) == 0)
{
lean_object* v_a_1343_; lean_object* v_fst_1344_; lean_object* v_snd_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1374_; 
v_a_1343_ = lean_ctor_get(v___x_1342_, 0);
lean_inc(v_a_1343_);
lean_dec_ref_known(v___x_1342_, 1);
v_fst_1344_ = lean_ctor_get(v_a_1343_, 0);
v_snd_1345_ = lean_ctor_get(v_a_1343_, 1);
v_isSharedCheck_1374_ = !lean_is_exclusive(v_a_1343_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1347_ = v_a_1343_;
v_isShared_1348_ = v_isSharedCheck_1374_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_snd_1345_);
lean_inc(v_fst_1344_);
lean_dec(v_a_1343_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1374_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; 
lean_inc_ref(v___y_1331_);
lean_inc(v___y_1336_);
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1334_);
lean_inc_ref(v___y_1333_);
v___x_1349_ = lean_apply_5(v___y_1331_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_, lean_box(0));
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; uint8_t v___x_1351_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref_known(v___x_1349_, 1);
v___x_1351_ = lean_unbox(v_a_1350_);
lean_dec(v_a_1350_);
if (v___x_1351_ == 0)
{
lean_del_object(v___x_1347_);
v___y_1271_ = v___x_1337_;
v___y_1272_ = v_snd_1345_;
v___y_1273_ = v_fst_1344_;
v___y_1274_ = v___y_1328_;
v___y_1275_ = v___x_1341_;
v___y_1276_ = v___y_1329_;
v___y_1277_ = v___x_1337_;
v___y_1278_ = v___y_1331_;
v___y_1279_ = v___x_1341_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___y_1333_;
v___y_1282_ = v___y_1334_;
v___y_1283_ = v___y_1335_;
v___y_1284_ = v___y_1336_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1355_; 
v___x_1352_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__15, &l_Lean_Meta_substCore___lam__3___closed__15_once, _init_l_Lean_Meta_substCore___lam__3___closed__15);
lean_inc(v_snd_1345_);
v___x_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1353_, 0, v_snd_1345_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set_tag(v___x_1347_, 7);
lean_ctor_set(v___x_1347_, 1, v___x_1353_);
lean_ctor_set(v___x_1347_, 0, v___x_1352_);
v___x_1355_ = v___x_1347_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1365_; 
v_reuseFailAlloc_1365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1365_, 0, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1365_, 1, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1365_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
lean_object* v___x_1356_; 
lean_inc(v___y_1332_);
v___x_1356_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1332_, v___x_1355_, v___y_1333_, v___y_1334_, v___y_1335_, v___y_1336_);
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_dec_ref_known(v___x_1356_, 1);
v___y_1271_ = v___x_1337_;
v___y_1272_ = v_snd_1345_;
v___y_1273_ = v_fst_1344_;
v___y_1274_ = v___y_1328_;
v___y_1275_ = v___x_1341_;
v___y_1276_ = v___y_1329_;
v___y_1277_ = v___x_1337_;
v___y_1278_ = v___y_1331_;
v___y_1279_ = v___x_1341_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___y_1333_;
v___y_1282_ = v___y_1334_;
v___y_1283_ = v___y_1335_;
v___y_1284_ = v___y_1336_;
goto v___jp_1270_;
}
else
{
lean_object* v_a_1357_; lean_object* v___x_1359_; uint8_t v_isShared_1360_; uint8_t v_isSharedCheck_1364_; 
lean_dec(v_snd_1345_);
lean_dec(v_fst_1344_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec(v___y_1329_);
lean_dec(v___y_1328_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1364_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1364_ == 0)
{
v___x_1359_ = v___x_1356_;
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
else
{
lean_inc(v_a_1357_);
lean_dec(v___x_1356_);
v___x_1359_ = lean_box(0);
v_isShared_1360_ = v_isSharedCheck_1364_;
goto v_resetjp_1358_;
}
v_resetjp_1358_:
{
lean_object* v___x_1362_; 
if (v_isShared_1360_ == 0)
{
v___x_1362_ = v___x_1359_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1363_; 
v_reuseFailAlloc_1363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1363_, 0, v_a_1357_);
v___x_1362_ = v_reuseFailAlloc_1363_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
return v___x_1362_;
}
}
}
}
}
}
else
{
lean_object* v_a_1366_; lean_object* v___x_1368_; uint8_t v_isShared_1369_; uint8_t v_isSharedCheck_1373_; 
lean_del_object(v___x_1347_);
lean_dec(v_snd_1345_);
lean_dec(v_fst_1344_);
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec(v___y_1329_);
lean_dec(v___y_1328_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
v_a_1366_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1373_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1368_ = v___x_1349_;
v_isShared_1369_ = v_isSharedCheck_1373_;
goto v_resetjp_1367_;
}
else
{
lean_inc(v_a_1366_);
lean_dec(v___x_1349_);
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
}
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
lean_dec(v___y_1336_);
lean_dec_ref(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec_ref(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec(v___y_1329_);
lean_dec(v___y_1328_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
v_a_1375_ = lean_ctor_get(v___x_1342_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1342_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1342_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1342_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
v___jp_1383_:
{
lean_object* v___x_1393_; lean_object* v_a_1394_; uint8_t v___x_1395_; 
lean_inc(v___y_1385_);
lean_inc_ref(v___y_1387_);
v___x_1393_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v___y_1387_, v___y_1385_, v___y_1390_);
v_a_1394_ = lean_ctor_get(v___x_1393_, 0);
lean_inc(v_a_1394_);
lean_dec_ref(v___x_1393_);
v___x_1395_ = lean_unbox(v_a_1394_);
lean_dec(v_a_1394_);
if (v___x_1395_ == 0)
{
lean_dec_ref(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_del_object(v___x_1146_);
lean_del_object(v___x_1142_);
lean_inc(v___y_1385_);
lean_inc(v___y_1384_);
v___y_1328_ = v___y_1384_;
v___y_1329_ = v___y_1385_;
v___y_1330_ = v___y_1385_;
v___y_1331_ = v___y_1386_;
v___y_1332_ = v___y_1384_;
v___y_1333_ = v___y_1389_;
v___y_1334_ = v___y_1390_;
v___y_1335_ = v___y_1391_;
v___y_1336_ = v___y_1392_;
goto v___jp_1327_;
}
else
{
lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1399_; 
v___x_1396_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_1397_ = l_Lean_MessageData_ofExpr(v___y_1388_);
if (v_isShared_1147_ == 0)
{
lean_ctor_set_tag(v___x_1146_, 7);
lean_ctor_set(v___x_1146_, 1, v___x_1397_);
lean_ctor_set(v___x_1146_, 0, v___x_1396_);
v___x_1399_ = v___x_1146_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1396_);
lean_ctor_set(v_reuseFailAlloc_1416_, 1, v___x_1397_);
v___x_1399_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1405_; 
v___x_1400_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__19, &l_Lean_Meta_substCore___lam__3___closed__19_once, _init_l_Lean_Meta_substCore___lam__3___closed__19);
v___x_1401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1401_, 0, v___x_1399_);
lean_ctor_set(v___x_1401_, 1, v___x_1400_);
v___x_1402_ = l_Lean_indentExpr(v___y_1387_);
v___x_1403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1403_, 0, v___x_1401_);
lean_ctor_set(v___x_1403_, 1, v___x_1402_);
if (v_isShared_1143_ == 0)
{
lean_ctor_set(v___x_1142_, 0, v___x_1403_);
v___x_1405_ = v___x_1142_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1403_);
v___x_1405_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; 
lean_inc(v_mvarId_1065_);
v___x_1406_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1117_, v_mvarId_1065_, v___x_1405_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1406_) == 0)
{
lean_dec_ref_known(v___x_1406_, 1);
lean_inc(v___y_1385_);
lean_inc(v___y_1384_);
v___y_1328_ = v___y_1384_;
v___y_1329_ = v___y_1385_;
v___y_1330_ = v___y_1385_;
v___y_1331_ = v___y_1386_;
v___y_1332_ = v___y_1384_;
v___y_1333_ = v___y_1389_;
v___y_1334_ = v___y_1390_;
v___y_1335_ = v___y_1391_;
v___y_1336_ = v___y_1392_;
goto v___jp_1327_;
}
else
{
lean_object* v_a_1407_; lean_object* v___x_1409_; uint8_t v_isShared_1410_; uint8_t v_isSharedCheck_1414_; 
lean_dec(v___y_1392_);
lean_dec_ref(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1385_);
lean_dec(v___y_1384_);
lean_del_object(v___x_1151_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
lean_dec(v_mvarId_1065_);
v_a_1407_ = lean_ctor_get(v___x_1406_, 0);
v_isSharedCheck_1414_ = !lean_is_exclusive(v___x_1406_);
if (v_isSharedCheck_1414_ == 0)
{
v___x_1409_ = v___x_1406_;
v_isShared_1410_ = v_isSharedCheck_1414_;
goto v_resetjp_1408_;
}
else
{
lean_inc(v_a_1407_);
lean_dec(v___x_1406_);
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
}
}
}
v___jp_1417_:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1419_, v___y_1073_);
if (lean_obj_tag(v___y_1418_) == 1)
{
lean_object* v_a_1421_; lean_object* v_fvarId_1422_; lean_object* v___x_1423_; lean_object* v___f_1424_; lean_object* v___x_1425_; lean_object* v_a_1426_; uint8_t v___x_1427_; 
lean_dec_ref(v___x_1121_);
v_a_1421_ = lean_ctor_get(v___x_1420_, 0);
lean_inc(v_a_1421_);
lean_dec_ref(v___x_1420_);
v_fvarId_1422_ = lean_ctor_get(v___y_1418_, 0);
lean_inc(v_fvarId_1422_);
v___x_1423_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___f_1424_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__23));
v___x_1425_ = l_Lean_Meta_substCore___lam__2(v___x_1423_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1425_);
v___x_1427_ = lean_unbox(v_a_1426_);
lean_dec(v_a_1426_);
if (v___x_1427_ == 0)
{
v___y_1384_ = v___x_1423_;
v___y_1385_ = v_fvarId_1422_;
v___y_1386_ = v___f_1424_;
v___y_1387_ = v_a_1421_;
v___y_1388_ = v___y_1418_;
v___y_1389_ = v___y_1072_;
v___y_1390_ = v___y_1073_;
v___y_1391_ = v___y_1074_;
v___y_1392_ = v___y_1075_;
goto v___jp_1383_;
}
else
{
lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1428_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__25, &l_Lean_Meta_substCore___lam__3___closed__25_once, _init_l_Lean_Meta_substCore___lam__3___closed__25);
lean_inc_ref(v___y_1418_);
v___x_1429_ = l_Lean_MessageData_ofExpr(v___y_1418_);
v___x_1430_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1428_);
lean_ctor_set(v___x_1430_, 1, v___x_1429_);
v___x_1431_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__27, &l_Lean_Meta_substCore___lam__3___closed__27_once, _init_l_Lean_Meta_substCore___lam__3___closed__27);
v___x_1432_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1431_);
lean_inc(v_fvarId_1422_);
v___x_1433_ = l_Lean_MessageData_ofName(v_fvarId_1422_);
v___x_1434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1432_);
lean_ctor_set(v___x_1434_, 1, v___x_1433_);
v___x_1435_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__29, &l_Lean_Meta_substCore___lam__3___closed__29_once, _init_l_Lean_Meta_substCore___lam__3___closed__29);
v___x_1436_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1434_);
lean_ctor_set(v___x_1436_, 1, v___x_1435_);
lean_inc(v_a_1421_);
v___x_1437_ = l_Lean_MessageData_ofExpr(v_a_1421_);
v___x_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1438_, 0, v___x_1436_);
lean_ctor_set(v___x_1438_, 1, v___x_1437_);
v___x_1439_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_1423_, v___x_1438_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
if (lean_obj_tag(v___x_1439_) == 0)
{
lean_dec_ref_known(v___x_1439_, 1);
v___y_1384_ = v___x_1423_;
v___y_1385_ = v_fvarId_1422_;
v___y_1386_ = v___f_1424_;
v___y_1387_ = v_a_1421_;
v___y_1388_ = v___y_1418_;
v___y_1389_ = v___y_1072_;
v___y_1390_ = v___y_1073_;
v___y_1391_ = v___y_1074_;
v___y_1392_ = v___y_1075_;
goto v___jp_1383_;
}
else
{
lean_object* v_a_1440_; lean_object* v___x_1442_; uint8_t v_isShared_1443_; uint8_t v_isSharedCheck_1447_; 
lean_dec(v_fvarId_1422_);
lean_dec(v_a_1421_);
lean_dec_ref_known(v___y_1418_, 1);
lean_del_object(v___x_1151_);
lean_del_object(v___x_1146_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1116_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
lean_dec(v_mvarId_1065_);
v_a_1440_ = lean_ctor_get(v___x_1439_, 0);
v_isSharedCheck_1447_ = !lean_is_exclusive(v___x_1439_);
if (v_isSharedCheck_1447_ == 0)
{
v___x_1442_ = v___x_1439_;
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
else
{
lean_inc(v_a_1440_);
lean_dec(v___x_1439_);
v___x_1442_ = lean_box(0);
v_isShared_1443_ = v_isSharedCheck_1447_;
goto v_resetjp_1441_;
}
v_resetjp_1441_:
{
lean_object* v___x_1445_; 
if (v_isShared_1443_ == 0)
{
v___x_1445_ = v___x_1442_;
goto v_reusejp_1444_;
}
else
{
lean_object* v_reuseFailAlloc_1446_; 
v_reuseFailAlloc_1446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1446_, 0, v_a_1440_);
v___x_1445_ = v_reuseFailAlloc_1446_;
goto v_reusejp_1444_;
}
v_reusejp_1444_:
{
return v___x_1445_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1420_);
lean_del_object(v___x_1151_);
lean_del_object(v___x_1146_);
lean_del_object(v___x_1142_);
lean_dec(v_a_1116_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
if (v_symm_1070_ == 0)
{
lean_object* v___x_1448_; 
v___x_1448_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__30));
v___y_1123_ = v___y_1418_;
v___y_1124_ = v___x_1448_;
goto v___jp_1122_;
}
else
{
lean_object* v___x_1449_; 
v___x_1449_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__31));
v___y_1123_ = v___y_1418_;
v___y_1124_ = v___x_1449_;
goto v___jp_1122_;
}
}
}
v___jp_1450_:
{
lean_object* v___x_1452_; 
v___x_1452_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1451_, v___y_1073_);
if (v_symm_1070_ == 0)
{
lean_object* v_a_1453_; 
lean_dec(v_fst_1148_);
v_a_1453_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v___x_1452_);
v___y_1418_ = v_a_1453_;
v___y_1419_ = v_snd_1149_;
goto v___jp_1417_;
}
else
{
lean_object* v_a_1454_; 
lean_dec(v_snd_1149_);
v_a_1454_ = lean_ctor_get(v___x_1452_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1452_);
v___y_1418_ = v_a_1454_;
v___y_1419_ = v_fst_1148_;
goto v___jp_1417_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1459_; lean_object* v___x_1461_; uint8_t v_isShared_1462_; uint8_t v_isSharedCheck_1466_; 
lean_dec_ref(v___x_1121_);
lean_dec(v_a_1116_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
lean_dec(v_mvarId_1065_);
v_a_1459_ = lean_ctor_get(v___x_1136_, 0);
v_isSharedCheck_1466_ = !lean_is_exclusive(v___x_1136_);
if (v_isSharedCheck_1466_ == 0)
{
v___x_1461_ = v___x_1136_;
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
else
{
lean_inc(v_a_1459_);
lean_dec(v___x_1136_);
v___x_1461_ = lean_box(0);
v_isShared_1462_ = v_isSharedCheck_1466_;
goto v_resetjp_1460_;
}
v_resetjp_1460_:
{
lean_object* v___x_1464_; 
if (v_isShared_1462_ == 0)
{
v___x_1464_ = v___x_1461_;
goto v_reusejp_1463_;
}
else
{
lean_object* v_reuseFailAlloc_1465_; 
v_reuseFailAlloc_1465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1465_, 0, v_a_1459_);
v___x_1464_ = v_reuseFailAlloc_1465_;
goto v_reusejp_1463_;
}
v_reusejp_1463_:
{
return v___x_1464_;
}
}
}
v___jp_1122_:
{
lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; 
v___x_1125_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__3, &l_Lean_Meta_substCore___lam__3___closed__3_once, _init_l_Lean_Meta_substCore___lam__3___closed__3);
lean_inc_ref(v___y_1124_);
v___x_1126_ = l_Lean_stringToMessageData(v___y_1124_);
v___x_1127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1127_, 0, v___x_1125_);
lean_ctor_set(v___x_1127_, 1, v___x_1126_);
v___x_1128_ = l_Lean_indentExpr(v___x_1121_);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__5, &l_Lean_Meta_substCore___lam__3___closed__5_once, _init_l_Lean_Meta_substCore___lam__3___closed__5);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_indentExpr(v___y_1123_);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1133_);
v___x_1135_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1117_, v_mvarId_1065_, v___x_1134_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
return v___x_1135_;
}
}
else
{
lean_object* v_a_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1474_; 
lean_dec(v_a_1116_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
lean_dec(v_mvarId_1065_);
v_a_1467_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1474_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1474_ == 0)
{
v___x_1469_ = v___x_1119_;
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_a_1467_);
lean_dec(v___x_1119_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1474_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1472_; 
if (v_isShared_1470_ == 0)
{
v___x_1472_ = v___x_1469_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_a_1467_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
else
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1482_; 
lean_dec(v_a_1116_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
lean_dec(v_mvarId_1065_);
v_a_1475_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1482_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1482_ == 0)
{
v___x_1477_ = v___x_1118_;
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1118_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1482_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1480_; 
if (v_isShared_1478_ == 0)
{
v___x_1480_ = v___x_1477_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1481_; 
v_reuseFailAlloc_1481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1481_, 0, v_a_1475_);
v___x_1480_ = v_reuseFailAlloc_1481_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
return v___x_1480_;
}
}
}
}
else
{
lean_object* v_a_1483_; lean_object* v___x_1485_; uint8_t v_isShared_1486_; uint8_t v_isSharedCheck_1490_; 
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v_fvarSubst_1069_);
lean_dec(v_hFVarId_1066_);
lean_dec(v_mvarId_1065_);
v_a_1483_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1485_ = v___x_1115_;
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
else
{
lean_inc(v_a_1483_);
lean_dec(v___x_1115_);
v___x_1485_ = lean_box(0);
v_isShared_1486_ = v_isSharedCheck_1490_;
goto v_resetjp_1484_;
}
v_resetjp_1484_:
{
lean_object* v___x_1488_; 
if (v_isShared_1486_ == 0)
{
v___x_1488_ = v___x_1485_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v_a_1483_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
return v___x_1488_;
}
}
}
v___jp_1077_:
{
if (v_clearH_1068_ == 0)
{
lean_object* v___x_1085_; lean_object* v___x_1086_; 
lean_dec(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v_fvarSubst_1069_);
lean_ctor_set(v___x_1085_, 1, v___y_1080_);
v___x_1086_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1086_, 0, v___x_1085_);
return v___x_1086_;
}
else
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_MVarId_clear(v___y_1080_, v___y_1082_, v___y_1081_, v___y_1078_, v___y_1079_, v___y_1084_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___x_1089_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
v___x_1089_ = l_Lean_MVarId_clear(v_a_1088_, v___y_1083_, v___y_1081_, v___y_1078_, v___y_1079_, v___y_1084_);
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1081_);
if (lean_obj_tag(v___x_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1098_; 
v_a_1090_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1098_ == 0)
{
v___x_1092_ = v___x_1089_;
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_a_1090_);
lean_dec(v___x_1089_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1098_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1096_; 
v___x_1094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1094_, 0, v_fvarSubst_1069_);
lean_ctor_set(v___x_1094_, 1, v_a_1090_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 0, v___x_1094_);
v___x_1096_ = v___x_1092_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v___x_1094_);
v___x_1096_ = v_reuseFailAlloc_1097_;
goto v_reusejp_1095_;
}
v_reusejp_1095_:
{
return v___x_1096_;
}
}
}
else
{
lean_object* v_a_1099_; lean_object* v___x_1101_; uint8_t v_isShared_1102_; uint8_t v_isSharedCheck_1106_; 
lean_dec(v_fvarSubst_1069_);
v_a_1099_ = lean_ctor_get(v___x_1089_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1089_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1101_ = v___x_1089_;
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
else
{
lean_inc(v_a_1099_);
lean_dec(v___x_1089_);
v___x_1101_ = lean_box(0);
v_isShared_1102_ = v_isSharedCheck_1106_;
goto v_resetjp_1100_;
}
v_resetjp_1100_:
{
lean_object* v___x_1104_; 
if (v_isShared_1102_ == 0)
{
v___x_1104_ = v___x_1101_;
goto v_reusejp_1103_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_a_1099_);
v___x_1104_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1103_;
}
v_reusejp_1103_:
{
return v___x_1104_;
}
}
}
}
else
{
lean_object* v_a_1107_; lean_object* v___x_1109_; uint8_t v_isShared_1110_; uint8_t v_isSharedCheck_1114_; 
lean_dec(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1081_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec(v_fvarSubst_1069_);
v_a_1107_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1114_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1114_ == 0)
{
v___x_1109_ = v___x_1087_;
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
else
{
lean_inc(v_a_1107_);
lean_dec(v___x_1087_);
v___x_1109_ = lean_box(0);
v_isShared_1110_ = v_isSharedCheck_1114_;
goto v_resetjp_1108_;
}
v_resetjp_1108_:
{
lean_object* v___x_1112_; 
if (v_isShared_1110_ == 0)
{
v___x_1112_ = v___x_1109_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1113_; 
v_reuseFailAlloc_1113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_a_1107_);
v___x_1112_ = v_reuseFailAlloc_1113_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
return v___x_1112_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3___boxed(lean_object* v_mvarId_1491_, lean_object* v_hFVarId_1492_, lean_object* v___x_1493_, lean_object* v_clearH_1494_, lean_object* v_fvarSubst_1495_, lean_object* v_symm_1496_, lean_object* v_tryToSkip_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_){
_start:
{
uint8_t v_clearH_boxed_1503_; uint8_t v_symm_boxed_1504_; uint8_t v_tryToSkip_boxed_1505_; lean_object* v_res_1506_; 
v_clearH_boxed_1503_ = lean_unbox(v_clearH_1494_);
v_symm_boxed_1504_ = lean_unbox(v_symm_1496_);
v_tryToSkip_boxed_1505_ = lean_unbox(v_tryToSkip_1497_);
v_res_1506_ = l_Lean_Meta_substCore___lam__3(v_mvarId_1491_, v_hFVarId_1492_, v___x_1493_, v_clearH_boxed_1503_, v_fvarSubst_1495_, v_symm_boxed_1504_, v_tryToSkip_boxed_1505_, v___y_1498_, v___y_1499_, v___y_1500_, v___y_1501_);
lean_dec(v___x_1493_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object* v_mvarId_1507_, lean_object* v_hFVarId_1508_, uint8_t v_symm_1509_, lean_object* v_fvarSubst_1510_, uint8_t v_clearH_1511_, uint8_t v_tryToSkip_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_){
_start:
{
lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___f_1522_; lean_object* v___x_1523_; 
v___x_1518_ = lean_box(0);
v___x_1519_ = lean_box(v_clearH_1511_);
v___x_1520_ = lean_box(v_symm_1509_);
v___x_1521_ = lean_box(v_tryToSkip_1512_);
lean_inc(v_mvarId_1507_);
v___f_1522_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__3___boxed), 12, 7);
lean_closure_set(v___f_1522_, 0, v_mvarId_1507_);
lean_closure_set(v___f_1522_, 1, v_hFVarId_1508_);
lean_closure_set(v___f_1522_, 2, v___x_1518_);
lean_closure_set(v___f_1522_, 3, v___x_1519_);
lean_closure_set(v___f_1522_, 4, v_fvarSubst_1510_);
lean_closure_set(v___f_1522_, 5, v___x_1520_);
lean_closure_set(v___f_1522_, 6, v___x_1521_);
v___x_1523_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1507_, v___f_1522_, v_a_1513_, v_a_1514_, v_a_1515_, v_a_1516_);
return v___x_1523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* v_mvarId_1524_, lean_object* v_hFVarId_1525_, lean_object* v_symm_1526_, lean_object* v_fvarSubst_1527_, lean_object* v_clearH_1528_, lean_object* v_tryToSkip_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_){
_start:
{
uint8_t v_symm_boxed_1535_; uint8_t v_clearH_boxed_1536_; uint8_t v_tryToSkip_boxed_1537_; lean_object* v_res_1538_; 
v_symm_boxed_1535_ = lean_unbox(v_symm_1526_);
v_clearH_boxed_1536_ = lean_unbox(v_clearH_1528_);
v_tryToSkip_boxed_1537_ = lean_unbox(v_tryToSkip_1529_);
v_res_1538_ = l_Lean_Meta_substCore(v_mvarId_1524_, v_hFVarId_1525_, v_symm_boxed_1535_, v_fvarSubst_1527_, v_clearH_boxed_1536_, v_tryToSkip_boxed_1537_, v_a_1530_, v_a_1531_, v_a_1532_, v_a_1533_);
lean_dec(v_a_1533_);
lean_dec_ref(v_a_1532_);
lean_dec(v_a_1531_);
lean_dec_ref(v_a_1530_);
return v_res_1538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1(lean_object* v_fst_1539_, lean_object* v_fst_1540_, lean_object* v_n_1541_, lean_object* v_i_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_){
_start:
{
lean_object* v___x_1550_; 
v___x_1550_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_1539_, v_fst_1540_, v_n_1541_, v_i_1542_, v_a_1544_);
return v___x_1550_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___boxed(lean_object* v_fst_1551_, lean_object* v_fst_1552_, lean_object* v_n_1553_, lean_object* v_i_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1(v_fst_1551_, v_fst_1552_, v_n_1553_, v_i_1554_, v_a_1555_, v_a_1556_, v___y_1557_, v___y_1558_, v___y_1559_, v___y_1560_);
lean_dec(v___y_1560_);
lean_dec_ref(v___y_1559_);
lean_dec(v___y_1558_);
lean_dec_ref(v___y_1557_);
lean_dec(v_n_1553_);
lean_dec_ref(v_fst_1552_);
lean_dec_ref(v_fst_1551_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4(lean_object* v_mvarId_1563_, lean_object* v_val_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v___x_1570_; 
v___x_1570_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_mvarId_1563_, v_val_1564_, v___y_1566_);
return v___x_1570_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___boxed(lean_object* v_mvarId_1571_, lean_object* v_val_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v_res_1578_; 
v_res_1578_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4(v_mvarId_1571_, v_val_1572_, v___y_1573_, v___y_1574_, v___y_1575_, v___y_1576_);
lean_dec(v___y_1576_);
lean_dec_ref(v___y_1575_);
lean_dec(v___y_1574_);
lean_dec_ref(v___y_1573_);
return v_res_1578_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7(lean_object* v_00_u03b1_1579_, lean_object* v_name_1580_, uint8_t v_bi_1581_, lean_object* v_type_1582_, lean_object* v_k_1583_, uint8_t v_kind_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_1580_, v_bi_1581_, v_type_1582_, v_k_1583_, v_kind_1584_, v___y_1585_, v___y_1586_, v___y_1587_, v___y_1588_);
return v___x_1590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1591_, lean_object* v_name_1592_, lean_object* v_bi_1593_, lean_object* v_type_1594_, lean_object* v_k_1595_, lean_object* v_kind_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
uint8_t v_bi_boxed_1602_; uint8_t v_kind_boxed_1603_; lean_object* v_res_1604_; 
v_bi_boxed_1602_ = lean_unbox(v_bi_1593_);
v_kind_boxed_1603_ = lean_unbox(v_kind_1596_);
v_res_1604_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7(v_00_u03b1_1591_, v_name_1592_, v_bi_boxed_1602_, v_type_1594_, v_k_1595_, v_kind_boxed_1603_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5(lean_object* v_00_u03b1_1605_, lean_object* v_name_1606_, lean_object* v_type_1607_, lean_object* v_k_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; 
v___x_1614_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v_name_1606_, v_type_1607_, v_k_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
return v___x_1614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___boxed(lean_object* v_00_u03b1_1615_, lean_object* v_name_1616_, lean_object* v_type_1617_, lean_object* v_k_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5(v_00_u03b1_1615_, v_name_1616_, v_type_1617_, v_k_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5(lean_object* v_00_u03b2_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_){
_start:
{
lean_object* v___x_1629_; 
v___x_1629_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5___redArg(v_x_1626_, v_x_1627_, v_x_1628_);
return v___x_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_1630_, lean_object* v_x_1631_, size_t v_x_1632_, size_t v_x_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_1631_, v_x_1632_, v_x_1633_, v_x_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_, lean_object* v_x_1642_){
_start:
{
size_t v_x_29613__boxed_1643_; size_t v_x_29614__boxed_1644_; lean_object* v_res_1645_; 
v_x_29613__boxed_1643_ = lean_unbox_usize(v_x_1639_);
lean_dec(v_x_1639_);
v_x_29614__boxed_1644_ = lean_unbox_usize(v_x_1640_);
lean_dec(v_x_1640_);
v_res_1645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8(v_00_u03b2_1637_, v_x_1638_, v_x_29613__boxed_1643_, v_x_29614__boxed_1644_, v_x_1641_, v_x_1642_);
return v_res_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13(lean_object* v_00_u03b2_1646_, lean_object* v_n_1647_, lean_object* v_k_1648_, lean_object* v_v_1649_){
_start:
{
lean_object* v___x_1650_; 
v___x_1650_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13___redArg(v_n_1647_, v_k_1648_, v_v_1649_);
return v___x_1650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1651_, size_t v_depth_1652_, lean_object* v_keys_1653_, lean_object* v_vals_1654_, lean_object* v_heq_1655_, lean_object* v_i_1656_, lean_object* v_entries_1657_){
_start:
{
lean_object* v___x_1658_; 
v___x_1658_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(v_depth_1652_, v_keys_1653_, v_vals_1654_, v_i_1656_, v_entries_1657_);
return v___x_1658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1659_, lean_object* v_depth_1660_, lean_object* v_keys_1661_, lean_object* v_vals_1662_, lean_object* v_heq_1663_, lean_object* v_i_1664_, lean_object* v_entries_1665_){
_start:
{
size_t v_depth_boxed_1666_; lean_object* v_res_1667_; 
v_depth_boxed_1666_ = lean_unbox_usize(v_depth_1660_);
lean_dec(v_depth_1660_);
v_res_1667_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14(v_00_u03b2_1659_, v_depth_boxed_1666_, v_keys_1661_, v_vals_1662_, v_heq_1663_, v_i_1664_, v_entries_1665_);
lean_dec_ref(v_vals_1662_);
lean_dec_ref(v_keys_1661_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_){
_start:
{
lean_object* v___x_1673_; 
v___x_1673_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14___redArg(v_x_1669_, v_x_1670_, v_x_1671_, v_x_1672_);
return v___x_1673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* v_fvarId_1677_, lean_object* v_mvarId_1678_, uint8_t v_tryToClear_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_){
_start:
{
lean_object* v___x_1685_; 
lean_inc(v_fvarId_1677_);
v___x_1685_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1677_, v___y_1680_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1685_) == 0)
{
lean_object* v_a_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_a_1686_ = lean_ctor_get(v___x_1685_, 0);
lean_inc(v_a_1686_);
lean_dec_ref_known(v___x_1685_, 1);
v___x_1687_ = l_Lean_LocalDecl_type(v_a_1686_);
lean_inc(v___y_1683_);
lean_inc_ref(v___y_1682_);
lean_inc(v___y_1681_);
lean_inc_ref(v___y_1680_);
v___x_1688_ = lean_whnf(v___x_1687_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1691_; uint8_t v_isShared_1692_; uint8_t v_isSharedCheck_1773_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1691_ = v___x_1688_;
v_isShared_1692_ = v_isSharedCheck_1773_;
goto v_resetjp_1690_;
}
else
{
lean_inc(v_a_1689_);
lean_dec(v___x_1688_);
v___x_1691_ = lean_box(0);
v_isShared_1692_ = v_isSharedCheck_1773_;
goto v_resetjp_1690_;
}
v_resetjp_1690_:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint8_t v___x_1695_; 
v___x_1693_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_1694_ = lean_unsigned_to_nat(4u);
v___x_1695_ = l_Lean_Expr_isAppOfArity(v_a_1689_, v___x_1693_, v___x_1694_);
if (v___x_1695_ == 0)
{
lean_object* v___x_1696_; lean_object* v___x_1698_; 
lean_dec(v_a_1689_);
lean_dec(v_a_1686_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
v___x_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1696_, 0, v_fvarId_1677_);
lean_ctor_set(v___x_1696_, 1, v_mvarId_1678_);
if (v_isShared_1692_ == 0)
{
lean_ctor_set(v___x_1691_, 0, v___x_1696_);
v___x_1698_ = v___x_1691_;
goto v_reusejp_1697_;
}
else
{
lean_object* v_reuseFailAlloc_1699_; 
v_reuseFailAlloc_1699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1699_, 0, v___x_1696_);
v___x_1698_ = v_reuseFailAlloc_1699_;
goto v_reusejp_1697_;
}
v_reusejp_1697_:
{
return v___x_1698_;
}
}
else
{
lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
lean_del_object(v___x_1691_);
v___x_1700_ = l_Lean_Expr_appFn_x21(v_a_1689_);
v___x_1701_ = l_Lean_Expr_appFn_x21(v___x_1700_);
v___x_1702_ = l_Lean_Expr_appFn_x21(v___x_1701_);
v___x_1703_ = l_Lean_Expr_appArg_x21(v___x_1702_);
lean_dec_ref(v___x_1702_);
v___x_1704_ = l_Lean_Expr_appArg_x21(v___x_1701_);
lean_dec_ref(v___x_1701_);
v___x_1705_ = l_Lean_Expr_appArg_x21(v___x_1700_);
lean_dec_ref(v___x_1700_);
v___x_1706_ = l_Lean_Expr_appArg_x21(v_a_1689_);
lean_dec(v_a_1689_);
v___x_1707_ = l_Lean_Meta_isExprDefEq(v___x_1703_, v___x_1705_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1707_) == 0)
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1764_; 
v_a_1708_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1710_ = v___x_1707_;
v_isShared_1711_ = v_isSharedCheck_1764_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1707_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1764_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
uint8_t v___x_1712_; 
v___x_1712_ = lean_unbox(v_a_1708_);
if (v___x_1712_ == 0)
{
lean_object* v___x_1713_; lean_object* v___x_1715_; 
lean_dec(v_a_1708_);
lean_dec_ref(v___x_1706_);
lean_dec_ref(v___x_1704_);
lean_dec(v_a_1686_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
v___x_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1713_, 0, v_fvarId_1677_);
lean_ctor_set(v___x_1713_, 1, v_mvarId_1678_);
if (v_isShared_1711_ == 0)
{
lean_ctor_set(v___x_1710_, 0, v___x_1713_);
v___x_1715_ = v___x_1710_;
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
else
{
lean_object* v___x_1717_; lean_object* v___x_1718_; 
lean_del_object(v___x_1710_);
lean_inc(v_fvarId_1677_);
v___x_1717_ = l_Lean_mkFVar(v_fvarId_1677_);
v___x_1718_ = l_Lean_Meta_mkEqOfHEq(v___x_1717_, v___x_1695_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1720_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_a_1719_);
lean_dec_ref_known(v___x_1718_, 1);
v___x_1720_ = l_Lean_Meta_mkEq(v___x_1704_, v___x_1706_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_a_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = l_Lean_LocalDecl_userName(v_a_1686_);
lean_dec(v_a_1686_);
v___x_1723_ = l_Lean_MVarId_assert(v_mvarId_1678_, v___x_1722_, v_a_1721_, v_a_1719_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1723_) == 0)
{
if (v_tryToClear_1679_ == 0)
{
lean_object* v_a_1724_; uint8_t v___x_1725_; lean_object* v___x_1726_; 
lean_dec(v_fvarId_1677_);
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = lean_unbox(v_a_1708_);
lean_dec(v_a_1708_);
v___x_1726_ = l_Lean_Meta_intro1Core(v_a_1724_, v___x_1725_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v___x_1726_;
}
else
{
lean_object* v_a_1727_; lean_object* v___x_1728_; 
v_a_1727_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1728_ = l_Lean_MVarId_tryClear(v_a_1727_, v_fvarId_1677_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
if (lean_obj_tag(v___x_1728_) == 0)
{
lean_object* v_a_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; 
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = lean_unbox(v_a_1708_);
lean_dec(v_a_1708_);
v___x_1731_ = l_Lean_Meta_intro1Core(v_a_1729_, v___x_1730_, v___y_1680_, v___y_1681_, v___y_1682_, v___y_1683_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
return v___x_1731_;
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1734_; uint8_t v_isShared_1735_; uint8_t v_isSharedCheck_1739_; 
lean_dec(v_a_1708_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
v_a_1732_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1739_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1739_ == 0)
{
v___x_1734_ = v___x_1728_;
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
else
{
lean_inc(v_a_1732_);
lean_dec(v___x_1728_);
v___x_1734_ = lean_box(0);
v_isShared_1735_ = v_isSharedCheck_1739_;
goto v_resetjp_1733_;
}
v_resetjp_1733_:
{
lean_object* v___x_1737_; 
if (v_isShared_1735_ == 0)
{
v___x_1737_ = v___x_1734_;
goto v_reusejp_1736_;
}
else
{
lean_object* v_reuseFailAlloc_1738_; 
v_reuseFailAlloc_1738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1738_, 0, v_a_1732_);
v___x_1737_ = v_reuseFailAlloc_1738_;
goto v_reusejp_1736_;
}
v_reusejp_1736_:
{
return v___x_1737_;
}
}
}
}
}
else
{
lean_object* v_a_1740_; lean_object* v___x_1742_; uint8_t v_isShared_1743_; uint8_t v_isSharedCheck_1747_; 
lean_dec(v_a_1708_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_fvarId_1677_);
v_a_1740_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1747_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1742_ = v___x_1723_;
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
else
{
lean_inc(v_a_1740_);
lean_dec(v___x_1723_);
v___x_1742_ = lean_box(0);
v_isShared_1743_ = v_isSharedCheck_1747_;
goto v_resetjp_1741_;
}
v_resetjp_1741_:
{
lean_object* v___x_1745_; 
if (v_isShared_1743_ == 0)
{
v___x_1745_ = v___x_1742_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_a_1740_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
}
}
else
{
lean_object* v_a_1748_; lean_object* v___x_1750_; uint8_t v_isShared_1751_; uint8_t v_isSharedCheck_1755_; 
lean_dec(v_a_1719_);
lean_dec(v_a_1708_);
lean_dec(v_a_1686_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_mvarId_1678_);
lean_dec(v_fvarId_1677_);
v_a_1748_ = lean_ctor_get(v___x_1720_, 0);
v_isSharedCheck_1755_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1755_ == 0)
{
v___x_1750_ = v___x_1720_;
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
else
{
lean_inc(v_a_1748_);
lean_dec(v___x_1720_);
v___x_1750_ = lean_box(0);
v_isShared_1751_ = v_isSharedCheck_1755_;
goto v_resetjp_1749_;
}
v_resetjp_1749_:
{
lean_object* v___x_1753_; 
if (v_isShared_1751_ == 0)
{
v___x_1753_ = v___x_1750_;
goto v_reusejp_1752_;
}
else
{
lean_object* v_reuseFailAlloc_1754_; 
v_reuseFailAlloc_1754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1754_, 0, v_a_1748_);
v___x_1753_ = v_reuseFailAlloc_1754_;
goto v_reusejp_1752_;
}
v_reusejp_1752_:
{
return v___x_1753_;
}
}
}
}
else
{
lean_object* v_a_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1763_; 
lean_dec(v_a_1708_);
lean_dec_ref(v___x_1706_);
lean_dec_ref(v___x_1704_);
lean_dec(v_a_1686_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_mvarId_1678_);
lean_dec(v_fvarId_1677_);
v_a_1756_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1758_ = v___x_1718_;
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
else
{
lean_inc(v_a_1756_);
lean_dec(v___x_1718_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1763_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1761_; 
if (v_isShared_1759_ == 0)
{
v___x_1761_ = v___x_1758_;
goto v_reusejp_1760_;
}
else
{
lean_object* v_reuseFailAlloc_1762_; 
v_reuseFailAlloc_1762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1762_, 0, v_a_1756_);
v___x_1761_ = v_reuseFailAlloc_1762_;
goto v_reusejp_1760_;
}
v_reusejp_1760_:
{
return v___x_1761_;
}
}
}
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec_ref(v___x_1706_);
lean_dec_ref(v___x_1704_);
lean_dec(v_a_1686_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_mvarId_1678_);
lean_dec(v_fvarId_1677_);
v_a_1765_ = lean_ctor_get(v___x_1707_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1707_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1707_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1707_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1770_; 
if (v_isShared_1768_ == 0)
{
v___x_1770_ = v___x_1767_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v_a_1765_);
v___x_1770_ = v_reuseFailAlloc_1771_;
goto v_reusejp_1769_;
}
v_reusejp_1769_:
{
return v___x_1770_;
}
}
}
}
}
}
else
{
lean_object* v_a_1774_; lean_object* v___x_1776_; uint8_t v_isShared_1777_; uint8_t v_isSharedCheck_1781_; 
lean_dec(v_a_1686_);
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_mvarId_1678_);
lean_dec(v_fvarId_1677_);
v_a_1774_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1688_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1688_);
v___x_1776_ = lean_box(0);
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
v_resetjp_1775_:
{
lean_object* v___x_1779_; 
if (v_isShared_1777_ == 0)
{
v___x_1779_ = v___x_1776_;
goto v_reusejp_1778_;
}
else
{
lean_object* v_reuseFailAlloc_1780_; 
v_reuseFailAlloc_1780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1780_, 0, v_a_1774_);
v___x_1779_ = v_reuseFailAlloc_1780_;
goto v_reusejp_1778_;
}
v_reusejp_1778_:
{
return v___x_1779_;
}
}
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
lean_dec(v___y_1683_);
lean_dec_ref(v___y_1682_);
lean_dec(v___y_1681_);
lean_dec_ref(v___y_1680_);
lean_dec(v_mvarId_1678_);
lean_dec(v_fvarId_1677_);
v_a_1782_ = lean_ctor_get(v___x_1685_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1685_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1685_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1685_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object* v_fvarId_1790_, lean_object* v_mvarId_1791_, lean_object* v_tryToClear_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_){
_start:
{
uint8_t v_tryToClear_boxed_1798_; lean_object* v_res_1799_; 
v_tryToClear_boxed_1798_ = lean_unbox(v_tryToClear_1792_);
v_res_1799_ = l_Lean_Meta_heqToEq___lam__0(v_fvarId_1790_, v_mvarId_1791_, v_tryToClear_boxed_1798_, v___y_1793_, v___y_1794_, v___y_1795_, v___y_1796_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object* v_mvarId_1800_, lean_object* v_fvarId_1801_, uint8_t v_tryToClear_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1808_; lean_object* v___f_1809_; lean_object* v___x_1810_; 
v___x_1808_ = lean_box(v_tryToClear_1802_);
lean_inc(v_mvarId_1800_);
v___f_1809_ = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1809_, 0, v_fvarId_1801_);
lean_closure_set(v___f_1809_, 1, v_mvarId_1800_);
lean_closure_set(v___f_1809_, 2, v___x_1808_);
v___x_1810_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1800_, v___f_1809_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* v_mvarId_1811_, lean_object* v_fvarId_1812_, lean_object* v_tryToClear_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
uint8_t v_tryToClear_boxed_1819_; lean_object* v_res_1820_; 
v_tryToClear_boxed_1819_ = lean_unbox(v_tryToClear_1813_);
v_res_1820_ = l_Lean_Meta_heqToEq(v_mvarId_1811_, v_fvarId_1812_, v_tryToClear_boxed_1819_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_);
lean_dec(v_a_1817_);
lean_dec_ref(v_a_1816_);
lean_dec(v_a_1815_);
lean_dec_ref(v_a_1814_);
return v_res_1820_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1824_, lean_object* v_as_1825_, size_t v_sz_1826_, size_t v_i_1827_, lean_object* v_b_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_){
_start:
{
lean_object* v_a_1835_; uint8_t v___x_1839_; 
v___x_1839_ = lean_usize_dec_lt(v_i_1827_, v_sz_1826_);
if (v___x_1839_ == 0)
{
lean_object* v___x_1840_; 
lean_dec(v_x_1824_);
v___x_1840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1840_, 0, v_b_1828_);
return v___x_1840_;
}
else
{
lean_object* v___x_1841_; lean_object* v_a_1843_; lean_object* v___x_1847_; lean_object* v_a_1848_; 
lean_dec_ref(v_b_1828_);
v___x_1841_ = lean_box(0);
v___x_1847_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1848_ = lean_array_uget(v_as_1825_, v_i_1827_);
if (lean_obj_tag(v_a_1848_) == 0)
{
v_a_1835_ = v___x_1847_;
goto v___jp_1834_;
}
else
{
lean_object* v_val_1849_; lean_object* v___x_1851_; uint8_t v_isShared_1852_; uint8_t v_isSharedCheck_1948_; 
v_val_1849_ = lean_ctor_get(v_a_1848_, 0);
v_isSharedCheck_1948_ = !lean_is_exclusive(v_a_1848_);
if (v_isSharedCheck_1948_ == 0)
{
v___x_1851_ = v_a_1848_;
v_isShared_1852_ = v_isSharedCheck_1948_;
goto v_resetjp_1850_;
}
else
{
lean_inc(v_val_1849_);
lean_dec(v_a_1848_);
v___x_1851_ = lean_box(0);
v_isShared_1852_ = v_isSharedCheck_1948_;
goto v_resetjp_1850_;
}
v_resetjp_1850_:
{
uint8_t v___x_1853_; 
v___x_1853_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1849_);
if (v___x_1853_ == 0)
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = l_Lean_LocalDecl_type(v_val_1849_);
v___x_1855_ = l_Lean_Meta_matchEq_x3f(v___x_1854_, v___y_1829_, v___y_1830_, v___y_1831_, v___y_1832_);
if (lean_obj_tag(v___x_1855_) == 0)
{
lean_object* v_a_1856_; 
v_a_1856_ = lean_ctor_get(v___x_1855_, 0);
lean_inc(v_a_1856_);
lean_dec_ref_known(v___x_1855_, 1);
if (lean_obj_tag(v_a_1856_) == 1)
{
lean_object* v_val_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1939_; 
v_val_1857_ = lean_ctor_get(v_a_1856_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_a_1856_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1859_ = v_a_1856_;
v_isShared_1860_ = v_isSharedCheck_1939_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_val_1857_);
lean_dec(v_a_1856_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1939_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v_snd_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1937_; 
v_snd_1861_ = lean_ctor_get(v_val_1857_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_val_1857_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v_val_1857_, 0);
lean_dec(v_unused_1938_);
v___x_1863_ = v_val_1857_;
v_isShared_1864_ = v_isSharedCheck_1937_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_snd_1861_);
lean_dec(v_val_1857_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1937_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v_fst_1865_; lean_object* v_snd_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1936_; 
v_fst_1865_ = lean_ctor_get(v_snd_1861_, 0);
v_snd_1866_ = lean_ctor_get(v_snd_1861_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_snd_1861_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1868_ = v_snd_1861_;
v_isShared_1869_ = v_isSharedCheck_1936_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_snd_1866_);
lean_inc(v_fst_1865_);
lean_dec(v_snd_1861_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1936_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1865_, v___y_1830_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; lean_object* v___x_1872_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1866_, v___y_1830_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___y_1875_; uint8_t v___x_1898_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1898_ = l_Lean_Expr_isFVar(v_a_1873_);
if (v___x_1898_ == 0)
{
lean_del_object(v___x_1863_);
lean_del_object(v___x_1851_);
v___y_1875_ = v___y_1830_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = l_Lean_Expr_fvarId_x21(v_a_1873_);
v___x_1900_ = l_Lean_instBEqFVarId_beq(v___x_1899_, v_x_1824_);
lean_dec(v___x_1899_);
if (v___x_1900_ == 0)
{
lean_del_object(v___x_1863_);
lean_del_object(v___x_1851_);
v___y_1875_ = v___y_1830_;
goto v___jp_1874_;
}
else
{
lean_object* v___x_1901_; 
lean_inc(v_x_1824_);
lean_inc(v_a_1871_);
v___x_1901_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1871_, v_x_1824_, v___y_1830_);
if (lean_obj_tag(v___x_1901_) == 0)
{
lean_object* v_a_1902_; uint8_t v___x_1903_; 
v_a_1902_ = lean_ctor_get(v___x_1901_, 0);
lean_inc(v_a_1902_);
lean_dec_ref_known(v___x_1901_, 1);
v___x_1903_ = lean_unbox(v_a_1902_);
lean_dec(v_a_1902_);
if (v___x_1903_ == 0)
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1907_; 
lean_dec(v_a_1873_);
lean_dec(v_a_1871_);
lean_del_object(v___x_1868_);
lean_del_object(v___x_1859_);
lean_dec(v_x_1824_);
v___x_1904_ = l_Lean_LocalDecl_fvarId(v_val_1849_);
lean_dec(v_val_1849_);
v___x_1905_ = lean_box(v___x_1839_);
if (v_isShared_1864_ == 0)
{
lean_ctor_set(v___x_1863_, 1, v___x_1905_);
lean_ctor_set(v___x_1863_, 0, v___x_1904_);
v___x_1907_ = v___x_1863_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1911_; 
v_reuseFailAlloc_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1911_, 0, v___x_1904_);
lean_ctor_set(v_reuseFailAlloc_1911_, 1, v___x_1905_);
v___x_1907_ = v_reuseFailAlloc_1911_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
lean_object* v___x_1909_; 
if (v_isShared_1852_ == 0)
{
lean_ctor_set(v___x_1851_, 0, v___x_1907_);
v___x_1909_ = v___x_1851_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1907_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
v_a_1843_ = v___x_1909_;
goto v___jp_1842_;
}
}
}
else
{
lean_del_object(v___x_1863_);
lean_del_object(v___x_1851_);
v___y_1875_ = v___y_1830_;
goto v___jp_1874_;
}
}
else
{
lean_object* v_a_1912_; lean_object* v___x_1914_; uint8_t v_isShared_1915_; uint8_t v_isSharedCheck_1919_; 
lean_dec(v_a_1873_);
lean_dec(v_a_1871_);
lean_del_object(v___x_1868_);
lean_del_object(v___x_1863_);
lean_del_object(v___x_1859_);
lean_del_object(v___x_1851_);
lean_dec(v_val_1849_);
lean_dec(v_x_1824_);
v_a_1912_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1914_ = v___x_1901_;
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
else
{
lean_inc(v_a_1912_);
lean_dec(v___x_1901_);
v___x_1914_ = lean_box(0);
v_isShared_1915_ = v_isSharedCheck_1919_;
goto v_resetjp_1913_;
}
v_resetjp_1913_:
{
lean_object* v___x_1917_; 
if (v_isShared_1915_ == 0)
{
v___x_1917_ = v___x_1914_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v_a_1912_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
}
}
v___jp_1874_:
{
uint8_t v___x_1876_; 
v___x_1876_ = l_Lean_Expr_isFVar(v_a_1871_);
if (v___x_1876_ == 0)
{
lean_dec(v_a_1873_);
lean_dec(v_a_1871_);
lean_del_object(v___x_1868_);
lean_del_object(v___x_1859_);
lean_dec(v_val_1849_);
v_a_1835_ = v___x_1847_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1877_; uint8_t v___x_1878_; 
v___x_1877_ = l_Lean_Expr_fvarId_x21(v_a_1871_);
lean_dec(v_a_1871_);
v___x_1878_ = l_Lean_instBEqFVarId_beq(v___x_1877_, v_x_1824_);
lean_dec(v___x_1877_);
if (v___x_1878_ == 0)
{
lean_dec(v_a_1873_);
lean_del_object(v___x_1868_);
lean_del_object(v___x_1859_);
lean_dec(v_val_1849_);
v_a_1835_ = v___x_1847_;
goto v___jp_1834_;
}
else
{
lean_object* v___x_1879_; 
lean_inc(v_x_1824_);
v___x_1879_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1873_, v_x_1824_, v___y_1875_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; uint8_t v___x_1881_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1879_, 1);
v___x_1881_ = lean_unbox(v_a_1880_);
lean_dec(v_a_1880_);
if (v___x_1881_ == 0)
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1885_; 
lean_dec(v_x_1824_);
v___x_1882_ = l_Lean_LocalDecl_fvarId(v_val_1849_);
lean_dec(v_val_1849_);
v___x_1883_ = lean_box(v___x_1853_);
if (v_isShared_1869_ == 0)
{
lean_ctor_set(v___x_1868_, 1, v___x_1883_);
lean_ctor_set(v___x_1868_, 0, v___x_1882_);
v___x_1885_ = v___x_1868_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1889_; 
v_reuseFailAlloc_1889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1889_, 0, v___x_1882_);
lean_ctor_set(v_reuseFailAlloc_1889_, 1, v___x_1883_);
v___x_1885_ = v_reuseFailAlloc_1889_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
lean_object* v___x_1887_; 
if (v_isShared_1860_ == 0)
{
lean_ctor_set(v___x_1859_, 0, v___x_1885_);
v___x_1887_ = v___x_1859_;
goto v_reusejp_1886_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
v___x_1887_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1886_;
}
v_reusejp_1886_:
{
v_a_1843_ = v___x_1887_;
goto v___jp_1842_;
}
}
}
else
{
lean_del_object(v___x_1868_);
lean_del_object(v___x_1859_);
lean_dec(v_val_1849_);
v_a_1835_ = v___x_1847_;
goto v___jp_1834_;
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_del_object(v___x_1868_);
lean_del_object(v___x_1859_);
lean_dec(v_val_1849_);
lean_dec(v_x_1824_);
v_a_1890_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1879_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1879_);
v___x_1892_ = lean_box(0);
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
v_resetjp_1891_:
{
lean_object* v___x_1895_; 
if (v_isShared_1893_ == 0)
{
v___x_1895_ = v___x_1892_;
goto v_reusejp_1894_;
}
else
{
lean_object* v_reuseFailAlloc_1896_; 
v_reuseFailAlloc_1896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1896_, 0, v_a_1890_);
v___x_1895_ = v_reuseFailAlloc_1896_;
goto v_reusejp_1894_;
}
v_reusejp_1894_:
{
return v___x_1895_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
lean_dec(v_a_1871_);
lean_del_object(v___x_1868_);
lean_del_object(v___x_1863_);
lean_del_object(v___x_1859_);
lean_del_object(v___x_1851_);
lean_dec(v_val_1849_);
lean_dec(v_x_1824_);
v_a_1920_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1927_ == 0)
{
v___x_1922_ = v___x_1872_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_inc(v_a_1920_);
lean_dec(v___x_1872_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
}
else
{
lean_object* v_a_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1935_; 
lean_del_object(v___x_1868_);
lean_dec(v_snd_1866_);
lean_del_object(v___x_1863_);
lean_del_object(v___x_1859_);
lean_del_object(v___x_1851_);
lean_dec(v_val_1849_);
lean_dec(v_x_1824_);
v_a_1928_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1935_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1930_ = v___x_1870_;
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_a_1928_);
lean_dec(v___x_1870_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1935_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1934_; 
v_reuseFailAlloc_1934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
v___x_1933_ = v_reuseFailAlloc_1934_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
return v___x_1933_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1856_);
lean_del_object(v___x_1851_);
lean_dec(v_val_1849_);
v_a_1835_ = v___x_1847_;
goto v___jp_1834_;
}
}
else
{
lean_object* v_a_1940_; lean_object* v___x_1942_; uint8_t v_isShared_1943_; uint8_t v_isSharedCheck_1947_; 
lean_del_object(v___x_1851_);
lean_dec(v_val_1849_);
lean_dec(v_x_1824_);
v_a_1940_ = lean_ctor_get(v___x_1855_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v___x_1855_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1942_ = v___x_1855_;
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
else
{
lean_inc(v_a_1940_);
lean_dec(v___x_1855_);
v___x_1942_ = lean_box(0);
v_isShared_1943_ = v_isSharedCheck_1947_;
goto v_resetjp_1941_;
}
v_resetjp_1941_:
{
lean_object* v___x_1945_; 
if (v_isShared_1943_ == 0)
{
v___x_1945_ = v___x_1942_;
goto v_reusejp_1944_;
}
else
{
lean_object* v_reuseFailAlloc_1946_; 
v_reuseFailAlloc_1946_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
v___x_1945_ = v_reuseFailAlloc_1946_;
goto v_reusejp_1944_;
}
v_reusejp_1944_:
{
return v___x_1945_;
}
}
}
}
else
{
lean_del_object(v___x_1851_);
lean_dec(v_val_1849_);
v_a_1835_ = v___x_1847_;
goto v___jp_1834_;
}
}
}
v___jp_1842_:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; 
v___x_1844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1844_, 0, v_a_1843_);
v___x_1845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___x_1841_);
v___x_1846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
return v___x_1846_;
}
}
v___jp_1834_:
{
size_t v___x_1836_; size_t v___x_1837_; 
v___x_1836_ = ((size_t)1ULL);
v___x_1837_ = lean_usize_add(v_i_1827_, v___x_1836_);
lean_inc_ref(v_a_1835_);
v_i_1827_ = v___x_1837_;
v_b_1828_ = v_a_1835_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1949_, lean_object* v_as_1950_, lean_object* v_sz_1951_, lean_object* v_i_1952_, lean_object* v_b_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_){
_start:
{
size_t v_sz_boxed_1959_; size_t v_i_boxed_1960_; lean_object* v_res_1961_; 
v_sz_boxed_1959_ = lean_unbox_usize(v_sz_1951_);
lean_dec(v_sz_1951_);
v_i_boxed_1960_ = lean_unbox_usize(v_i_1952_);
lean_dec(v_i_1952_);
v_res_1961_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1949_, v_as_1950_, v_sz_boxed_1959_, v_i_boxed_1960_, v_b_1953_, v___y_1954_, v___y_1955_, v___y_1956_, v___y_1957_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec_ref(v_as_1950_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object* v_x_1962_, lean_object* v_as_1963_, size_t v_sz_1964_, size_t v_i_1965_, lean_object* v_b_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_){
_start:
{
lean_object* v_a_1973_; uint8_t v___x_1977_; 
v___x_1977_ = lean_usize_dec_lt(v_i_1965_, v_sz_1964_);
if (v___x_1977_ == 0)
{
lean_object* v___x_1978_; 
lean_dec(v_x_1962_);
v___x_1978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1978_, 0, v_b_1966_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v_a_1981_; lean_object* v___x_1985_; lean_object* v_a_1986_; 
lean_dec_ref(v_b_1966_);
v___x_1979_ = lean_box(0);
v___x_1985_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1986_ = lean_array_uget(v_as_1963_, v_i_1965_);
if (lean_obj_tag(v_a_1986_) == 0)
{
v_a_1973_ = v___x_1985_;
goto v___jp_1972_;
}
else
{
lean_object* v_val_1987_; lean_object* v___x_1989_; uint8_t v_isShared_1990_; uint8_t v_isSharedCheck_2086_; 
v_val_1987_ = lean_ctor_get(v_a_1986_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v_a_1986_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_1989_ = v_a_1986_;
v_isShared_1990_ = v_isSharedCheck_2086_;
goto v_resetjp_1988_;
}
else
{
lean_inc(v_val_1987_);
lean_dec(v_a_1986_);
v___x_1989_ = lean_box(0);
v_isShared_1990_ = v_isSharedCheck_2086_;
goto v_resetjp_1988_;
}
v_resetjp_1988_:
{
uint8_t v___x_1991_; 
v___x_1991_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1987_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1992_ = l_Lean_LocalDecl_type(v_val_1987_);
v___x_1993_ = l_Lean_Meta_matchEq_x3f(v___x_1992_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
if (lean_obj_tag(v___x_1993_) == 0)
{
lean_object* v_a_1994_; 
v_a_1994_ = lean_ctor_get(v___x_1993_, 0);
lean_inc(v_a_1994_);
lean_dec_ref_known(v___x_1993_, 1);
if (lean_obj_tag(v_a_1994_) == 1)
{
lean_object* v_val_1995_; lean_object* v___x_1997_; uint8_t v_isShared_1998_; uint8_t v_isSharedCheck_2077_; 
v_val_1995_ = lean_ctor_get(v_a_1994_, 0);
v_isSharedCheck_2077_ = !lean_is_exclusive(v_a_1994_);
if (v_isSharedCheck_2077_ == 0)
{
v___x_1997_ = v_a_1994_;
v_isShared_1998_ = v_isSharedCheck_2077_;
goto v_resetjp_1996_;
}
else
{
lean_inc(v_val_1995_);
lean_dec(v_a_1994_);
v___x_1997_ = lean_box(0);
v_isShared_1998_ = v_isSharedCheck_2077_;
goto v_resetjp_1996_;
}
v_resetjp_1996_:
{
lean_object* v_snd_1999_; lean_object* v___x_2001_; uint8_t v_isShared_2002_; uint8_t v_isSharedCheck_2075_; 
v_snd_1999_ = lean_ctor_get(v_val_1995_, 1);
v_isSharedCheck_2075_ = !lean_is_exclusive(v_val_1995_);
if (v_isSharedCheck_2075_ == 0)
{
lean_object* v_unused_2076_; 
v_unused_2076_ = lean_ctor_get(v_val_1995_, 0);
lean_dec(v_unused_2076_);
v___x_2001_ = v_val_1995_;
v_isShared_2002_ = v_isSharedCheck_2075_;
goto v_resetjp_2000_;
}
else
{
lean_inc(v_snd_1999_);
lean_dec(v_val_1995_);
v___x_2001_ = lean_box(0);
v_isShared_2002_ = v_isSharedCheck_2075_;
goto v_resetjp_2000_;
}
v_resetjp_2000_:
{
lean_object* v_fst_2003_; lean_object* v_snd_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2074_; 
v_fst_2003_ = lean_ctor_get(v_snd_1999_, 0);
v_snd_2004_ = lean_ctor_get(v_snd_1999_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_snd_1999_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2006_ = v_snd_1999_;
v_isShared_2007_ = v_isSharedCheck_2074_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_snd_2004_);
lean_inc(v_fst_2003_);
lean_dec(v_snd_1999_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2074_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v___x_2008_; 
v___x_2008_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_2003_, v___y_1968_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref_known(v___x_2008_, 1);
v___x_2010_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_2004_, v___y_1968_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___y_2013_; uint8_t v___x_2036_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
v___x_2036_ = l_Lean_Expr_isFVar(v_a_2011_);
if (v___x_2036_ == 0)
{
lean_del_object(v___x_2001_);
lean_del_object(v___x_1989_);
v___y_2013_ = v___y_1968_;
goto v___jp_2012_;
}
else
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = l_Lean_Expr_fvarId_x21(v_a_2011_);
v___x_2038_ = l_Lean_instBEqFVarId_beq(v___x_2037_, v_x_1962_);
lean_dec(v___x_2037_);
if (v___x_2038_ == 0)
{
lean_del_object(v___x_2001_);
lean_del_object(v___x_1989_);
v___y_2013_ = v___y_1968_;
goto v___jp_2012_;
}
else
{
lean_object* v___x_2039_; 
lean_inc(v_x_1962_);
lean_inc(v_a_2009_);
v___x_2039_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_2009_, v_x_1962_, v___y_1968_);
if (lean_obj_tag(v___x_2039_) == 0)
{
lean_object* v_a_2040_; uint8_t v___x_2041_; 
v_a_2040_ = lean_ctor_get(v___x_2039_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2039_, 1);
v___x_2041_ = lean_unbox(v_a_2040_);
lean_dec(v_a_2040_);
if (v___x_2041_ == 0)
{
lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2045_; 
lean_dec(v_a_2011_);
lean_dec(v_a_2009_);
lean_del_object(v___x_2006_);
lean_del_object(v___x_1997_);
lean_dec(v_x_1962_);
v___x_2042_ = l_Lean_LocalDecl_fvarId(v_val_1987_);
lean_dec(v_val_1987_);
v___x_2043_ = lean_box(v___x_1977_);
if (v_isShared_2002_ == 0)
{
lean_ctor_set(v___x_2001_, 1, v___x_2043_);
lean_ctor_set(v___x_2001_, 0, v___x_2042_);
v___x_2045_ = v___x_2001_;
goto v_reusejp_2044_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2042_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v___x_2043_);
v___x_2045_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2044_;
}
v_reusejp_2044_:
{
lean_object* v___x_2047_; 
if (v_isShared_1990_ == 0)
{
lean_ctor_set(v___x_1989_, 0, v___x_2045_);
v___x_2047_ = v___x_1989_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2045_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
v_a_1981_ = v___x_2047_;
goto v___jp_1980_;
}
}
}
else
{
lean_del_object(v___x_2001_);
lean_del_object(v___x_1989_);
v___y_2013_ = v___y_1968_;
goto v___jp_2012_;
}
}
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_dec(v_a_2011_);
lean_dec(v_a_2009_);
lean_del_object(v___x_2006_);
lean_del_object(v___x_2001_);
lean_del_object(v___x_1997_);
lean_del_object(v___x_1989_);
lean_dec(v_val_1987_);
lean_dec(v_x_1962_);
v_a_2050_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2039_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2039_);
v___x_2052_ = lean_box(0);
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
v_resetjp_2051_:
{
lean_object* v___x_2055_; 
if (v_isShared_2053_ == 0)
{
v___x_2055_ = v___x_2052_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v_a_2050_);
v___x_2055_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
return v___x_2055_;
}
}
}
}
}
v___jp_2012_:
{
uint8_t v___x_2014_; 
v___x_2014_ = l_Lean_Expr_isFVar(v_a_2009_);
if (v___x_2014_ == 0)
{
lean_dec(v_a_2011_);
lean_dec(v_a_2009_);
lean_del_object(v___x_2006_);
lean_del_object(v___x_1997_);
lean_dec(v_val_1987_);
v_a_1973_ = v___x_1985_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2015_ = l_Lean_Expr_fvarId_x21(v_a_2009_);
lean_dec(v_a_2009_);
v___x_2016_ = l_Lean_instBEqFVarId_beq(v___x_2015_, v_x_1962_);
lean_dec(v___x_2015_);
if (v___x_2016_ == 0)
{
lean_dec(v_a_2011_);
lean_del_object(v___x_2006_);
lean_del_object(v___x_1997_);
lean_dec(v_val_1987_);
v_a_1973_ = v___x_1985_;
goto v___jp_1972_;
}
else
{
lean_object* v___x_2017_; 
lean_inc(v_x_1962_);
v___x_2017_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_2011_, v_x_1962_, v___y_2013_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; uint8_t v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
v___x_2019_ = lean_unbox(v_a_2018_);
lean_dec(v_a_2018_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2023_; 
lean_dec(v_x_1962_);
v___x_2020_ = l_Lean_LocalDecl_fvarId(v_val_1987_);
lean_dec(v_val_1987_);
v___x_2021_ = lean_box(v___x_1991_);
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 1, v___x_2021_);
lean_ctor_set(v___x_2006_, 0, v___x_2020_);
v___x_2023_ = v___x_2006_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2020_);
lean_ctor_set(v_reuseFailAlloc_2027_, 1, v___x_2021_);
v___x_2023_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_1998_ == 0)
{
lean_ctor_set(v___x_1997_, 0, v___x_2023_);
v___x_2025_ = v___x_1997_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
v_a_1981_ = v___x_2025_;
goto v___jp_1980_;
}
}
}
else
{
lean_del_object(v___x_2006_);
lean_del_object(v___x_1997_);
lean_dec(v_val_1987_);
v_a_1973_ = v___x_1985_;
goto v___jp_1972_;
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_del_object(v___x_2006_);
lean_del_object(v___x_1997_);
lean_dec(v_val_1987_);
lean_dec(v_x_1962_);
v_a_2028_ = lean_ctor_get(v___x_2017_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2017_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2017_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2017_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2033_; 
if (v_isShared_2031_ == 0)
{
v___x_2033_ = v___x_2030_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v_a_2028_);
v___x_2033_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
return v___x_2033_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_2009_);
lean_del_object(v___x_2006_);
lean_del_object(v___x_2001_);
lean_del_object(v___x_1997_);
lean_del_object(v___x_1989_);
lean_dec(v_val_1987_);
lean_dec(v_x_1962_);
v_a_2058_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2010_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2010_);
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
lean_ctor_set(v_reuseFailAlloc_2064_, 0, v_a_2058_);
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
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
lean_del_object(v___x_2006_);
lean_dec(v_snd_2004_);
lean_del_object(v___x_2001_);
lean_del_object(v___x_1997_);
lean_del_object(v___x_1989_);
lean_dec(v_val_1987_);
lean_dec(v_x_1962_);
v_a_2066_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2008_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2008_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1994_);
lean_del_object(v___x_1989_);
lean_dec(v_val_1987_);
v_a_1973_ = v___x_1985_;
goto v___jp_1972_;
}
}
else
{
lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2085_; 
lean_del_object(v___x_1989_);
lean_dec(v_val_1987_);
lean_dec(v_x_1962_);
v_a_2078_ = lean_ctor_get(v___x_1993_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v___x_1993_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_2080_ = v___x_1993_;
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_dec(v___x_1993_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2085_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
lean_object* v___x_2083_; 
if (v_isShared_2081_ == 0)
{
v___x_2083_ = v___x_2080_;
goto v_reusejp_2082_;
}
else
{
lean_object* v_reuseFailAlloc_2084_; 
v_reuseFailAlloc_2084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2084_, 0, v_a_2078_);
v___x_2083_ = v_reuseFailAlloc_2084_;
goto v_reusejp_2082_;
}
v_reusejp_2082_:
{
return v___x_2083_;
}
}
}
}
else
{
lean_del_object(v___x_1989_);
lean_dec(v_val_1987_);
v_a_1973_ = v___x_1985_;
goto v___jp_1972_;
}
}
}
v___jp_1980_:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1982_, 0, v_a_1981_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
lean_ctor_set(v___x_1983_, 1, v___x_1979_);
v___x_1984_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1984_, 0, v___x_1983_);
return v___x_1984_;
}
}
v___jp_1972_:
{
size_t v___x_1974_; size_t v___x_1975_; lean_object* v___x_1976_; 
v___x_1974_ = ((size_t)1ULL);
v___x_1975_ = lean_usize_add(v_i_1965_, v___x_1974_);
lean_inc_ref(v_a_1973_);
v___x_1976_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1962_, v_as_1963_, v_sz_1964_, v___x_1975_, v_a_1973_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_);
return v___x_1976_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2087_, lean_object* v_as_2088_, lean_object* v_sz_2089_, lean_object* v_i_2090_, lean_object* v_b_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
size_t v_sz_boxed_2097_; size_t v_i_boxed_2098_; lean_object* v_res_2099_; 
v_sz_boxed_2097_ = lean_unbox_usize(v_sz_2089_);
lean_dec(v_sz_2089_);
v_i_boxed_2098_ = lean_unbox_usize(v_i_2090_);
lean_dec(v_i_2090_);
v_res_2099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2087_, v_as_2088_, v_sz_boxed_2097_, v_i_boxed_2098_, v_b_2091_, v___y_2092_, v___y_2093_, v___y_2094_, v___y_2095_);
lean_dec(v___y_2095_);
lean_dec_ref(v___y_2094_);
lean_dec(v___y_2093_);
lean_dec_ref(v___y_2092_);
lean_dec_ref(v_as_2088_);
return v_res_2099_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object* v_x_2100_, lean_object* v_x_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_){
_start:
{
if (lean_obj_tag(v_x_2101_) == 0)
{
lean_object* v_cs_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; size_t v_sz_2110_; size_t v___x_2111_; lean_object* v___x_2112_; 
v_cs_2107_ = lean_ctor_get(v_x_2101_, 0);
v___x_2108_ = lean_box(0);
v___x_2109_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2110_ = lean_array_size(v_cs_2107_);
v___x_2111_ = ((size_t)0ULL);
v___x_2112_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2100_, v_cs_2107_, v_sz_2110_, v___x_2111_, v___x_2109_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
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
lean_dec_ref_known(v_fst_2117_, 1);
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
else
{
lean_object* v_vs_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; size_t v_sz_2137_; size_t v___x_2138_; lean_object* v___x_2139_; 
v_vs_2134_ = lean_ctor_get(v_x_2101_, 0);
v___x_2135_ = lean_box(0);
v___x_2136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2137_ = lean_array_size(v_vs_2134_);
v___x_2138_ = ((size_t)0ULL);
v___x_2139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2100_, v_vs_2134_, v_sz_2137_, v___x_2138_, v___x_2136_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2152_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2152_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2152_ == 0)
{
v___x_2142_ = v___x_2139_;
v_isShared_2143_ = v_isSharedCheck_2152_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2139_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2152_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v_fst_2144_; 
v_fst_2144_ = lean_ctor_get(v_a_2140_, 0);
lean_inc(v_fst_2144_);
lean_dec(v_a_2140_);
if (lean_obj_tag(v_fst_2144_) == 0)
{
lean_object* v___x_2146_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2135_);
v___x_2146_ = v___x_2142_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2135_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
return v___x_2146_;
}
}
else
{
lean_object* v_val_2148_; lean_object* v___x_2150_; 
v_val_2148_ = lean_ctor_get(v_fst_2144_, 0);
lean_inc(v_val_2148_);
lean_dec_ref_known(v_fst_2144_, 1);
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v_val_2148_);
v___x_2150_ = v___x_2142_;
goto v_reusejp_2149_;
}
else
{
lean_object* v_reuseFailAlloc_2151_; 
v_reuseFailAlloc_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2151_, 0, v_val_2148_);
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
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
v_a_2153_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2139_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2139_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
v___x_2158_ = v___x_2155_;
goto v_reusejp_2157_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
v___x_2158_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2157_;
}
v_reusejp_2157_:
{
return v___x_2158_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2161_, lean_object* v_as_2162_, size_t v_sz_2163_, size_t v_i_2164_, lean_object* v_b_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_){
_start:
{
uint8_t v___x_2171_; 
v___x_2171_ = lean_usize_dec_lt(v_i_2164_, v_sz_2163_);
if (v___x_2171_ == 0)
{
lean_object* v___x_2172_; 
lean_dec(v_x_2161_);
v___x_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2172_, 0, v_b_2165_);
return v___x_2172_;
}
else
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v_a_2175_; lean_object* v___x_2176_; 
lean_dec_ref(v_b_2165_);
v___x_2173_ = lean_box(0);
v___x_2174_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_2175_ = lean_array_uget_borrowed(v_as_2162_, v_i_2164_);
lean_inc(v_x_2161_);
v___x_2176_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2161_, v_a_2175_, v___y_2166_, v___y_2167_, v___y_2168_, v___y_2169_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2189_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2179_ = v___x_2176_;
v_isShared_2180_ = v_isSharedCheck_2189_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_a_2177_);
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2189_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
if (lean_obj_tag(v_a_2177_) == 1)
{
lean_object* v___x_2181_; lean_object* v___x_2182_; lean_object* v___x_2184_; 
lean_dec(v_x_2161_);
v___x_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2181_, 0, v_a_2177_);
v___x_2182_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
lean_ctor_set(v___x_2182_, 1, v___x_2173_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2182_);
v___x_2184_ = v___x_2179_;
goto v_reusejp_2183_;
}
else
{
lean_object* v_reuseFailAlloc_2185_; 
v_reuseFailAlloc_2185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2185_, 0, v___x_2182_);
v___x_2184_ = v_reuseFailAlloc_2185_;
goto v_reusejp_2183_;
}
v_reusejp_2183_:
{
return v___x_2184_;
}
}
else
{
size_t v___x_2186_; size_t v___x_2187_; 
lean_del_object(v___x_2179_);
lean_dec(v_a_2177_);
v___x_2186_ = ((size_t)1ULL);
v___x_2187_ = lean_usize_add(v_i_2164_, v___x_2186_);
v_i_2164_ = v___x_2187_;
v_b_2165_ = v___x_2174_;
goto _start;
}
}
}
else
{
lean_object* v_a_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2197_; 
lean_dec(v_x_2161_);
v_a_2190_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2197_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2197_ == 0)
{
v___x_2192_ = v___x_2176_;
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_a_2190_);
lean_dec(v___x_2176_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2197_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v___x_2195_; 
if (v_isShared_2193_ == 0)
{
v___x_2195_ = v___x_2192_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v_a_2190_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2198_, lean_object* v_as_2199_, lean_object* v_sz_2200_, lean_object* v_i_2201_, lean_object* v_b_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
size_t v_sz_boxed_2208_; size_t v_i_boxed_2209_; lean_object* v_res_2210_; 
v_sz_boxed_2208_ = lean_unbox_usize(v_sz_2200_);
lean_dec(v_sz_2200_);
v_i_boxed_2209_ = lean_unbox_usize(v_i_2201_);
lean_dec(v_i_2201_);
v_res_2210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2198_, v_as_2199_, v_sz_boxed_2208_, v_i_boxed_2209_, v_b_2202_, v___y_2203_, v___y_2204_, v___y_2205_, v___y_2206_);
lean_dec(v___y_2206_);
lean_dec_ref(v___y_2205_);
lean_dec(v___y_2204_);
lean_dec_ref(v___y_2203_);
lean_dec_ref(v_as_2199_);
return v_res_2210_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2211_, lean_object* v_x_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_){
_start:
{
lean_object* v_res_2218_; 
v_res_2218_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2211_, v_x_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec(v___y_2214_);
lean_dec_ref(v___y_2213_);
lean_dec_ref(v_x_2212_);
return v_res_2218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object* v_x_2219_, lean_object* v_t_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_root_2226_; lean_object* v_tail_2227_; lean_object* v___x_2228_; 
v_root_2226_ = lean_ctor_get(v_t_2220_, 0);
v_tail_2227_ = lean_ctor_get(v_t_2220_, 1);
lean_inc(v_x_2219_);
v___x_2228_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2219_, v_root_2226_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2228_) == 0)
{
lean_object* v_a_2229_; 
v_a_2229_ = lean_ctor_get(v___x_2228_, 0);
if (lean_obj_tag(v_a_2229_) == 0)
{
lean_object* v___x_2230_; size_t v_sz_2231_; size_t v___x_2232_; lean_object* v___x_2233_; 
lean_inc(v_a_2229_);
lean_dec_ref_known(v___x_2228_, 1);
v___x_2230_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2231_ = lean_array_size(v_tail_2227_);
v___x_2232_ = ((size_t)0ULL);
v___x_2233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2219_, v_tail_2227_, v_sz_2231_, v___x_2232_, v___x_2230_, v___y_2221_, v___y_2222_, v___y_2223_, v___y_2224_);
if (lean_obj_tag(v___x_2233_) == 0)
{
lean_object* v_a_2234_; lean_object* v___x_2236_; uint8_t v_isShared_2237_; uint8_t v_isSharedCheck_2246_; 
v_a_2234_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2236_ = v___x_2233_;
v_isShared_2237_ = v_isSharedCheck_2246_;
goto v_resetjp_2235_;
}
else
{
lean_inc(v_a_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = lean_box(0);
v_isShared_2237_ = v_isSharedCheck_2246_;
goto v_resetjp_2235_;
}
v_resetjp_2235_:
{
lean_object* v_fst_2238_; 
v_fst_2238_ = lean_ctor_get(v_a_2234_, 0);
lean_inc(v_fst_2238_);
lean_dec(v_a_2234_);
if (lean_obj_tag(v_fst_2238_) == 0)
{
lean_object* v___x_2240_; 
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v_a_2229_);
v___x_2240_ = v___x_2236_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_a_2229_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
else
{
lean_object* v_val_2242_; lean_object* v___x_2244_; 
v_val_2242_ = lean_ctor_get(v_fst_2238_, 0);
lean_inc(v_val_2242_);
lean_dec_ref_known(v_fst_2238_, 1);
if (v_isShared_2237_ == 0)
{
lean_ctor_set(v___x_2236_, 0, v_val_2242_);
v___x_2244_ = v___x_2236_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_val_2242_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
v_a_2247_ = lean_ctor_get(v___x_2233_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2233_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2233_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2233_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
else
{
lean_dec(v_x_2219_);
return v___x_2228_;
}
}
else
{
lean_dec(v_x_2219_);
return v___x_2228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* v_x_2255_, lean_object* v_t_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2255_, v_t_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v_t_2256_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object* v_x_2263_, lean_object* v_lctx_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_, lean_object* v___y_2268_){
_start:
{
lean_object* v_decls_2270_; lean_object* v___x_2271_; 
v_decls_2270_ = lean_ctor_get(v_lctx_2264_, 1);
v___x_2271_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2263_, v_decls_2270_, v___y_2265_, v___y_2266_, v___y_2267_, v___y_2268_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object* v_x_2272_, lean_object* v_lctx_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_){
_start:
{
lean_object* v_res_2279_; 
v_res_2279_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2272_, v_lctx_2273_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
lean_dec(v___y_2277_);
lean_dec_ref(v___y_2276_);
lean_dec(v___y_2275_);
lean_dec_ref(v___y_2274_);
lean_dec_ref(v_lctx_2273_);
return v_res_2279_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2281_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__0));
v___x_2282_ = l_Lean_stringToMessageData(v___x_2281_);
return v___x_2282_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2284_; lean_object* v___x_2285_; 
v___x_2284_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__2));
v___x_2285_ = l_Lean_stringToMessageData(v___x_2284_);
return v___x_2285_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__4));
v___x_2288_ = l_Lean_stringToMessageData(v___x_2287_);
return v___x_2288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object* v_x_2289_, lean_object* v_mvarId_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
lean_object* v___x_2341_; 
lean_inc(v_x_2289_);
v___x_2341_ = l_Lean_FVarId_getDecl___redArg(v_x_2289_, v___y_2291_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2341_) == 0)
{
lean_object* v_a_2342_; uint8_t v___x_2343_; uint8_t v___x_2344_; 
v_a_2342_ = lean_ctor_get(v___x_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___x_2341_, 1);
v___x_2343_ = 0;
v___x_2344_ = l_Lean_LocalDecl_isLet(v_a_2342_, v___x_2343_);
lean_dec(v_a_2342_);
if (v___x_2344_ == 0)
{
goto v___jp_2296_;
}
else
{
lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; 
v___x_2345_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2346_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2289_);
v___x_2347_ = l_Lean_mkFVar(v_x_2289_);
v___x_2348_ = l_Lean_MessageData_ofExpr(v___x_2347_);
v___x_2349_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2349_, 0, v___x_2346_);
lean_ctor_set(v___x_2349_, 1, v___x_2348_);
v___x_2350_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2349_);
lean_ctor_set(v___x_2351_, 1, v___x_2350_);
v___x_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2352_, 0, v___x_2351_);
lean_inc(v_mvarId_2290_);
v___x_2353_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2345_, v_mvarId_2290_, v___x_2352_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2353_) == 0)
{
lean_dec_ref_known(v___x_2353_, 1);
goto v___jp_2296_;
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v_mvarId_2290_);
lean_dec(v_x_2289_);
v_a_2354_ = lean_ctor_get(v___x_2353_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___x_2353_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___x_2353_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___x_2353_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
else
{
lean_object* v_a_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2369_; 
lean_dec(v_mvarId_2290_);
lean_dec(v_x_2289_);
v_a_2362_ = lean_ctor_get(v___x_2341_, 0);
v_isSharedCheck_2369_ = !lean_is_exclusive(v___x_2341_);
if (v_isSharedCheck_2369_ == 0)
{
v___x_2364_ = v___x_2341_;
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_a_2362_);
lean_dec(v___x_2341_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2369_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2367_; 
if (v_isShared_2365_ == 0)
{
v___x_2367_ = v___x_2364_;
goto v_reusejp_2366_;
}
else
{
lean_object* v_reuseFailAlloc_2368_; 
v_reuseFailAlloc_2368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2368_, 0, v_a_2362_);
v___x_2367_ = v_reuseFailAlloc_2368_;
goto v_reusejp_2366_;
}
v_reusejp_2366_:
{
return v___x_2367_;
}
}
}
v___jp_2296_:
{
lean_object* v_lctx_2297_; lean_object* v___x_2298_; 
v_lctx_2297_ = lean_ctor_get(v___y_2291_, 2);
lean_inc(v_x_2289_);
v___x_2298_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2289_, v_lctx_2297_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2298_) == 0)
{
lean_object* v_a_2299_; 
v_a_2299_ = lean_ctor_get(v___x_2298_, 0);
lean_inc(v_a_2299_);
lean_dec_ref_known(v___x_2298_, 1);
if (lean_obj_tag(v_a_2299_) == 1)
{
lean_object* v_val_2300_; lean_object* v_fst_2301_; lean_object* v_snd_2302_; lean_object* v___x_2303_; uint8_t v___x_2304_; uint8_t v___x_2305_; lean_object* v___x_2306_; 
lean_dec(v_x_2289_);
v_val_2300_ = lean_ctor_get(v_a_2299_, 0);
lean_inc(v_val_2300_);
lean_dec_ref_known(v_a_2299_, 1);
v_fst_2301_ = lean_ctor_get(v_val_2300_, 0);
lean_inc(v_fst_2301_);
v_snd_2302_ = lean_ctor_get(v_val_2300_, 1);
lean_inc(v_snd_2302_);
lean_dec(v_val_2300_);
v___x_2303_ = lean_box(0);
v___x_2304_ = 1;
v___x_2305_ = lean_unbox(v_snd_2302_);
lean_dec(v_snd_2302_);
v___x_2306_ = l_Lean_Meta_substCore(v_mvarId_2290_, v_fst_2301_, v___x_2305_, v___x_2303_, v___x_2304_, v___x_2304_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
if (lean_obj_tag(v___x_2306_) == 0)
{
lean_object* v_a_2307_; lean_object* v___x_2309_; uint8_t v_isShared_2310_; uint8_t v_isSharedCheck_2315_; 
v_a_2307_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2309_ = v___x_2306_;
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
else
{
lean_inc(v_a_2307_);
lean_dec(v___x_2306_);
v___x_2309_ = lean_box(0);
v_isShared_2310_ = v_isSharedCheck_2315_;
goto v_resetjp_2308_;
}
v_resetjp_2308_:
{
lean_object* v_snd_2311_; lean_object* v___x_2313_; 
v_snd_2311_ = lean_ctor_get(v_a_2307_, 1);
lean_inc(v_snd_2311_);
lean_dec(v_a_2307_);
if (v_isShared_2310_ == 0)
{
lean_ctor_set(v___x_2309_, 0, v_snd_2311_);
v___x_2313_ = v___x_2309_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_snd_2311_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
v_a_2316_ = lean_ctor_get(v___x_2306_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2306_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2306_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2306_);
v___x_2318_ = lean_box(0);
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
v_resetjp_2317_:
{
lean_object* v___x_2321_; 
if (v_isShared_2319_ == 0)
{
v___x_2321_ = v___x_2318_;
goto v_reusejp_2320_;
}
else
{
lean_object* v_reuseFailAlloc_2322_; 
v_reuseFailAlloc_2322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2322_, 0, v_a_2316_);
v___x_2321_ = v_reuseFailAlloc_2322_;
goto v_reusejp_2320_;
}
v_reusejp_2320_:
{
return v___x_2321_;
}
}
}
}
else
{
lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
lean_dec(v_a_2299_);
v___x_2324_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2325_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2326_ = l_Lean_mkFVar(v_x_2289_);
v___x_2327_ = l_Lean_MessageData_ofExpr(v___x_2326_);
v___x_2328_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2325_);
lean_ctor_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2328_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2331_, 0, v___x_2330_);
v___x_2332_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2324_, v_mvarId_2290_, v___x_2331_, v___y_2291_, v___y_2292_, v___y_2293_, v___y_2294_);
return v___x_2332_;
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_dec(v_mvarId_2290_);
lean_dec(v_x_2289_);
v_a_2333_ = lean_ctor_get(v___x_2298_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2298_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2298_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2298_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2370_, lean_object* v_mvarId_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_Meta_substVar___lam__0(v_x_2370_, v_mvarId_2371_, v___y_2372_, v___y_2373_, v___y_2374_, v___y_2375_);
lean_dec(v___y_2375_);
lean_dec_ref(v___y_2374_);
lean_dec(v___y_2373_);
lean_dec_ref(v___y_2372_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2378_, lean_object* v_x_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v___f_2385_; lean_object* v___x_2386_; 
lean_inc(v_mvarId_2378_);
v___f_2385_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2385_, 0, v_x_2379_);
lean_closure_set(v___f_2385_, 1, v_mvarId_2378_);
v___x_2386_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2378_, v___f_2385_, v_a_2380_, v_a_2381_, v_a_2382_, v_a_2383_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2387_, lean_object* v_x_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v_res_2394_; 
v_res_2394_ = l_Lean_Meta_substVar(v_mvarId_2387_, v_x_2388_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
lean_dec(v_a_2392_);
lean_dec_ref(v_a_2391_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
return v_res_2394_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2397_ = l_Lean_stringToMessageData(v___x_2396_);
return v___x_2397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2398_, lean_object* v_snd_2399_, uint8_t v___x_2400_, lean_object* v_fvarSubst_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_){
_start:
{
lean_object* v___x_2407_; 
lean_inc(v_fst_2398_);
v___x_2407_ = l_Lean_FVarId_getDecl___redArg(v_fst_2398_, v___y_2402_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v_a_2408_; lean_object* v_newType_2410_; uint8_t v_symm_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___y_2455_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v_a_2408_ = lean_ctor_get(v___x_2407_, 0);
lean_inc(v_a_2408_);
lean_dec_ref_known(v___x_2407_, 1);
v___x_2463_ = l_Lean_LocalDecl_type(v_a_2408_);
v___x_2464_ = l_Lean_Meta_matchEq_x3f(v___x_2463_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2464_) == 0)
{
lean_object* v_a_2465_; 
v_a_2465_ = lean_ctor_get(v___x_2464_, 0);
lean_inc(v_a_2465_);
lean_dec_ref_known(v___x_2464_, 1);
if (lean_obj_tag(v_a_2465_) == 1)
{
lean_object* v_val_2466_; lean_object* v_snd_2467_; lean_object* v_fst_2468_; lean_object* v_snd_2469_; lean_object* v___x_2470_; 
v_val_2466_ = lean_ctor_get(v_a_2465_, 0);
lean_inc(v_val_2466_);
lean_dec_ref_known(v_a_2465_, 1);
v_snd_2467_ = lean_ctor_get(v_val_2466_, 1);
lean_inc(v_snd_2467_);
lean_dec(v_val_2466_);
v_fst_2468_ = lean_ctor_get(v_snd_2467_, 0);
lean_inc(v_fst_2468_);
v_snd_2469_ = lean_ctor_get(v_snd_2467_, 1);
lean_inc_n(v_snd_2469_, 2);
lean_dec(v_snd_2467_);
lean_inc(v___y_2405_);
lean_inc_ref(v___y_2404_);
lean_inc(v___y_2403_);
lean_inc_ref(v___y_2402_);
v___x_2470_ = lean_whnf(v_snd_2469_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2470_) == 0)
{
lean_object* v_a_2471_; uint8_t v___x_2472_; 
v_a_2471_ = lean_ctor_get(v___x_2470_, 0);
lean_inc(v_a_2471_);
lean_dec_ref_known(v___x_2470_, 1);
v___x_2472_ = l_Lean_Expr_isFVar(v_a_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
lean_dec(v_a_2471_);
lean_inc(v___y_2405_);
lean_inc_ref(v___y_2404_);
lean_inc(v___y_2403_);
lean_inc_ref(v___y_2402_);
lean_inc(v_fst_2468_);
v___x_2473_ = lean_whnf(v_fst_2468_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; uint8_t v___x_2475_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v___x_2475_ = l_Lean_Expr_isFVar(v_a_2474_);
if (v___x_2475_ == 0)
{
lean_dec(v_a_2474_);
lean_dec(v_snd_2469_);
lean_dec(v_fst_2468_);
lean_dec(v_fvarSubst_2401_);
lean_dec(v_fst_2398_);
v___y_2452_ = v___y_2402_;
v___y_2453_ = v___y_2403_;
v___y_2454_ = v___y_2404_;
v___y_2455_ = v___y_2405_;
goto v___jp_2451_;
}
else
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_expr_eqv(v_fst_2468_, v_a_2474_);
lean_dec(v_fst_2468_);
if (v___x_2476_ == 0)
{
lean_object* v___x_2477_; 
v___x_2477_ = l_Lean_Meta_mkEq(v_a_2474_, v_snd_2469_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2477_) == 0)
{
lean_object* v_a_2478_; 
v_a_2478_ = lean_ctor_get(v___x_2477_, 0);
lean_inc(v_a_2478_);
lean_dec_ref_known(v___x_2477_, 1);
v_newType_2410_ = v_a_2478_;
v_symm_2411_ = v___x_2472_;
v___y_2412_ = v___y_2402_;
v___y_2413_ = v___y_2403_;
v___y_2414_ = v___y_2404_;
v___y_2415_ = v___y_2405_;
goto v___jp_2409_;
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_a_2408_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v_fvarSubst_2401_);
lean_dec(v_snd_2399_);
lean_dec(v_fst_2398_);
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
else
{
lean_object* v___x_2487_; 
lean_dec(v_a_2474_);
lean_dec(v_snd_2469_);
lean_dec(v_a_2408_);
v___x_2487_ = l_Lean_Meta_substCore(v_snd_2399_, v_fst_2398_, v___x_2472_, v_fvarSubst_2401_, v___x_2400_, v___x_2400_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v___x_2487_;
}
}
}
else
{
lean_object* v_a_2488_; lean_object* v___x_2490_; uint8_t v_isShared_2491_; uint8_t v_isSharedCheck_2495_; 
lean_dec(v_snd_2469_);
lean_dec(v_fst_2468_);
lean_dec(v_a_2408_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v_fvarSubst_2401_);
lean_dec(v_snd_2399_);
lean_dec(v_fst_2398_);
v_a_2488_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2495_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2495_ == 0)
{
v___x_2490_ = v___x_2473_;
v_isShared_2491_ = v_isSharedCheck_2495_;
goto v_resetjp_2489_;
}
else
{
lean_inc(v_a_2488_);
lean_dec(v___x_2473_);
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
uint8_t v___x_2496_; 
v___x_2496_ = lean_expr_eqv(v_snd_2469_, v_a_2471_);
lean_dec(v_snd_2469_);
if (v___x_2496_ == 0)
{
lean_object* v___x_2497_; 
v___x_2497_ = l_Lean_Meta_mkEq(v_fst_2468_, v_a_2471_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v_a_2498_; 
v_a_2498_ = lean_ctor_get(v___x_2497_, 0);
lean_inc(v_a_2498_);
lean_dec_ref_known(v___x_2497_, 1);
v_newType_2410_ = v_a_2498_;
v_symm_2411_ = v___x_2400_;
v___y_2412_ = v___y_2402_;
v___y_2413_ = v___y_2403_;
v___y_2414_ = v___y_2404_;
v___y_2415_ = v___y_2405_;
goto v___jp_2409_;
}
else
{
lean_object* v_a_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2506_; 
lean_dec(v_a_2408_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v_fvarSubst_2401_);
lean_dec(v_snd_2399_);
lean_dec(v_fst_2398_);
v_a_2499_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2506_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2506_ == 0)
{
v___x_2501_ = v___x_2497_;
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_a_2499_);
lean_dec(v___x_2497_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2506_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v___x_2504_; 
if (v_isShared_2502_ == 0)
{
v___x_2504_ = v___x_2501_;
goto v_reusejp_2503_;
}
else
{
lean_object* v_reuseFailAlloc_2505_; 
v_reuseFailAlloc_2505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2505_, 0, v_a_2499_);
v___x_2504_ = v_reuseFailAlloc_2505_;
goto v_reusejp_2503_;
}
v_reusejp_2503_:
{
return v___x_2504_;
}
}
}
}
else
{
lean_object* v___x_2507_; 
lean_dec(v_a_2471_);
lean_dec(v_fst_2468_);
lean_dec(v_a_2408_);
v___x_2507_ = l_Lean_Meta_substCore(v_snd_2399_, v_fst_2398_, v___x_2400_, v_fvarSubst_2401_, v___x_2400_, v___x_2400_, v___y_2402_, v___y_2403_, v___y_2404_, v___y_2405_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
return v___x_2507_;
}
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_snd_2469_);
lean_dec(v_fst_2468_);
lean_dec(v_a_2408_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v_fvarSubst_2401_);
lean_dec(v_snd_2399_);
lean_dec(v_fst_2398_);
v_a_2508_ = lean_ctor_get(v___x_2470_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2470_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2470_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2470_);
v___x_2510_ = lean_box(0);
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
v_resetjp_2509_:
{
lean_object* v___x_2513_; 
if (v_isShared_2511_ == 0)
{
v___x_2513_ = v___x_2510_;
goto v_reusejp_2512_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_a_2508_);
v___x_2513_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2512_;
}
v_reusejp_2512_:
{
return v___x_2513_;
}
}
}
}
else
{
lean_dec(v_a_2465_);
lean_dec(v_fvarSubst_2401_);
lean_dec(v_fst_2398_);
v___y_2452_ = v___y_2402_;
v___y_2453_ = v___y_2403_;
v___y_2454_ = v___y_2404_;
v___y_2455_ = v___y_2405_;
goto v___jp_2451_;
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v_a_2408_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v_fvarSubst_2401_);
lean_dec(v_snd_2399_);
lean_dec(v_fst_2398_);
v_a_2516_ = lean_ctor_get(v___x_2464_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2464_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2464_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2464_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_a_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
v___jp_2409_:
{
lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2416_ = l_Lean_LocalDecl_userName(v_a_2408_);
lean_dec(v_a_2408_);
lean_inc(v_fst_2398_);
v___x_2417_ = l_Lean_mkFVar(v_fst_2398_);
v___x_2418_ = l_Lean_MVarId_assert(v_snd_2399_, v___x_2416_, v_newType_2410_, v___x_2417_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2418_) == 0)
{
lean_object* v_a_2419_; lean_object* v___x_2420_; 
v_a_2419_ = lean_ctor_get(v___x_2418_, 0);
lean_inc(v_a_2419_);
lean_dec_ref_known(v___x_2418_, 1);
v___x_2420_ = l_Lean_Meta_intro1Core(v_a_2419_, v___x_2400_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v_fst_2422_; lean_object* v_snd_2423_; lean_object* v___x_2424_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___x_2420_, 1);
v_fst_2422_ = lean_ctor_get(v_a_2421_, 0);
lean_inc(v_fst_2422_);
v_snd_2423_ = lean_ctor_get(v_a_2421_, 1);
lean_inc(v_snd_2423_);
lean_dec(v_a_2421_);
v___x_2424_ = l_Lean_MVarId_clear(v_snd_2423_, v_fst_2398_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2426_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2426_ = l_Lean_Meta_substCore(v_a_2425_, v_fst_2422_, v_symm_2411_, v_fvarSubst_2401_, v___x_2400_, v___x_2400_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
return v___x_2426_;
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_dec(v_fst_2422_);
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v_fvarSubst_2401_);
v_a_2427_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2424_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2424_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
else
{
lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2442_; 
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v_fvarSubst_2401_);
lean_dec(v_fst_2398_);
v_a_2435_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2442_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2442_ == 0)
{
v___x_2437_ = v___x_2420_;
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2420_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2442_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2440_; 
if (v_isShared_2438_ == 0)
{
v___x_2440_ = v___x_2437_;
goto v_reusejp_2439_;
}
else
{
lean_object* v_reuseFailAlloc_2441_; 
v_reuseFailAlloc_2441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2441_, 0, v_a_2435_);
v___x_2440_ = v_reuseFailAlloc_2441_;
goto v_reusejp_2439_;
}
v_reusejp_2439_:
{
return v___x_2440_;
}
}
}
}
else
{
lean_object* v_a_2443_; lean_object* v___x_2445_; uint8_t v_isShared_2446_; uint8_t v_isSharedCheck_2450_; 
lean_dec(v___y_2415_);
lean_dec_ref(v___y_2414_);
lean_dec(v___y_2413_);
lean_dec_ref(v___y_2412_);
lean_dec(v_fvarSubst_2401_);
lean_dec(v_fst_2398_);
v_a_2443_ = lean_ctor_get(v___x_2418_, 0);
v_isSharedCheck_2450_ = !lean_is_exclusive(v___x_2418_);
if (v_isSharedCheck_2450_ == 0)
{
v___x_2445_ = v___x_2418_;
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
else
{
lean_inc(v_a_2443_);
lean_dec(v___x_2418_);
v___x_2445_ = lean_box(0);
v_isShared_2446_ = v_isSharedCheck_2450_;
goto v_resetjp_2444_;
}
v_resetjp_2444_:
{
lean_object* v___x_2448_; 
if (v_isShared_2446_ == 0)
{
v___x_2448_ = v___x_2445_;
goto v_reusejp_2447_;
}
else
{
lean_object* v_reuseFailAlloc_2449_; 
v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
v___x_2448_ = v_reuseFailAlloc_2449_;
goto v_reusejp_2447_;
}
v_reusejp_2447_:
{
return v___x_2448_;
}
}
}
}
v___jp_2451_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v___x_2456_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2457_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2458_ = l_Lean_LocalDecl_type(v_a_2408_);
lean_dec(v_a_2408_);
v___x_2459_ = l_Lean_indentExpr(v___x_2458_);
v___x_2460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2457_);
lean_ctor_set(v___x_2460_, 1, v___x_2459_);
v___x_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2461_, 0, v___x_2460_);
v___x_2462_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2456_, v_snd_2399_, v___x_2461_, v___y_2452_, v___y_2453_, v___y_2454_, v___y_2455_);
lean_dec(v___y_2455_);
lean_dec_ref(v___y_2454_);
lean_dec(v___y_2453_);
lean_dec_ref(v___y_2452_);
return v___x_2462_;
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v_fvarSubst_2401_);
lean_dec(v_snd_2399_);
lean_dec(v_fst_2398_);
v_a_2524_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2407_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2407_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2532_, lean_object* v_snd_2533_, lean_object* v___x_2534_, lean_object* v_fvarSubst_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_){
_start:
{
uint8_t v___x_1462__boxed_2541_; lean_object* v_res_2542_; 
v___x_1462__boxed_2541_ = lean_unbox(v___x_2534_);
v_res_2542_ = l_Lean_Meta_substEq___lam__0(v_fst_2532_, v_snd_2533_, v___x_1462__boxed_2541_, v_fvarSubst_2535_, v___y_2536_, v___y_2537_, v___y_2538_, v___y_2539_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2543_, lean_object* v_hFVarId_2544_, lean_object* v_fvarSubst_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_){
_start:
{
uint8_t v___x_2551_; lean_object* v___x_2552_; 
v___x_2551_ = 1;
v___x_2552_ = l_Lean_Meta_heqToEq(v_mvarId_2543_, v_hFVarId_2544_, v___x_2551_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
if (lean_obj_tag(v___x_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v_fst_2554_; lean_object* v_snd_2555_; lean_object* v___x_2556_; lean_object* v___f_2557_; lean_object* v___x_2558_; 
v_a_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v_fst_2554_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_fst_2554_);
v_snd_2555_ = lean_ctor_get(v_a_2553_, 1);
lean_inc_n(v_snd_2555_, 2);
lean_dec(v_a_2553_);
v___x_2556_ = lean_box(v___x_2551_);
v___f_2557_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2557_, 0, v_fst_2554_);
lean_closure_set(v___f_2557_, 1, v_snd_2555_);
lean_closure_set(v___f_2557_, 2, v___x_2556_);
lean_closure_set(v___f_2557_, 3, v_fvarSubst_2545_);
v___x_2558_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_snd_2555_, v___f_2557_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
return v___x_2558_;
}
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_dec(v_fvarSubst_2545_);
v_a_2559_ = lean_ctor_get(v___x_2552_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2552_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2552_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2552_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2567_, lean_object* v_hFVarId_2568_, lean_object* v_fvarSubst_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_){
_start:
{
lean_object* v_res_2575_; 
v_res_2575_ = l_Lean_Meta_substEq(v_mvarId_2567_, v_hFVarId_2568_, v_fvarSubst_2569_, v_a_2570_, v_a_2571_, v_a_2572_, v_a_2573_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
lean_dec(v_a_2571_);
lean_dec_ref(v_a_2570_);
return v_res_2575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2576_, lean_object* v_mvarId_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_){
_start:
{
lean_object* v___x_2583_; 
lean_inc(v_h_2576_);
v___x_2583_ = l_Lean_FVarId_getType___redArg(v_h_2576_, v___y_2578_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v___x_2585_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc_n(v_a_2584_, 2);
lean_dec_ref_known(v___x_2583_, 1);
v___x_2585_ = l_Lean_Meta_matchEq_x3f(v_a_2584_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
if (lean_obj_tag(v_a_2586_) == 0)
{
lean_object* v___x_2587_; 
v___x_2587_ = l_Lean_Meta_matchHEq_x3f(v_a_2584_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2587_) == 0)
{
lean_object* v_a_2588_; 
v_a_2588_ = lean_ctor_get(v___x_2587_, 0);
lean_inc(v_a_2588_);
lean_dec_ref_known(v___x_2587_, 1);
if (lean_obj_tag(v_a_2588_) == 0)
{
lean_object* v___x_2589_; 
v___x_2589_ = l_Lean_Meta_substVar(v_mvarId_2577_, v_h_2576_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2589_;
}
else
{
uint8_t v___x_2590_; lean_object* v___x_2591_; 
lean_dec_ref_known(v_a_2588_, 1);
v___x_2590_ = 1;
lean_inc(v_h_2576_);
lean_inc(v_mvarId_2577_);
v___x_2591_ = l_Lean_Meta_heqToEq(v_mvarId_2577_, v_h_2576_, v___x_2590_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v_fst_2593_; lean_object* v_snd_2594_; uint8_t v___x_2595_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
lean_inc(v_a_2592_);
lean_dec_ref_known(v___x_2591_, 1);
v_fst_2593_ = lean_ctor_get(v_a_2592_, 0);
lean_inc(v_fst_2593_);
v_snd_2594_ = lean_ctor_get(v_a_2592_, 1);
lean_inc(v_snd_2594_);
lean_dec(v_a_2592_);
v___x_2595_ = l_Lean_instBEqMVarId_beq(v_mvarId_2577_, v_snd_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; 
lean_dec(v_mvarId_2577_);
lean_dec(v_h_2576_);
v___x_2596_ = l_Lean_Meta_subst(v_snd_2594_, v_fst_2593_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2596_;
}
else
{
lean_object* v___x_2597_; 
lean_dec(v_snd_2594_);
lean_dec(v_fst_2593_);
v___x_2597_ = l_Lean_Meta_substVar(v_mvarId_2577_, v_h_2576_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
return v___x_2597_;
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_mvarId_2577_);
lean_dec(v_h_2576_);
v_a_2598_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2591_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2591_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v___x_2603_; 
if (v_isShared_2601_ == 0)
{
v___x_2603_ = v___x_2600_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2604_; 
v_reuseFailAlloc_2604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2604_, 0, v_a_2598_);
v___x_2603_ = v_reuseFailAlloc_2604_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
return v___x_2603_;
}
}
}
}
}
else
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v_mvarId_2577_);
lean_dec(v_h_2576_);
v_a_2606_ = lean_ctor_get(v___x_2587_, 0);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2587_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2587_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2587_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; 
lean_dec_ref_known(v_a_2586_, 1);
lean_dec(v_a_2584_);
v___x_2614_ = lean_box(0);
v___x_2615_ = l_Lean_Meta_substEq(v_mvarId_2577_, v_h_2576_, v___x_2614_, v___y_2578_, v___y_2579_, v___y_2580_, v___y_2581_);
if (lean_obj_tag(v___x_2615_) == 0)
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2624_; 
v_a_2616_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2618_ = v___x_2615_;
v_isShared_2619_ = v_isSharedCheck_2624_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2615_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2624_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v_snd_2620_; lean_object* v___x_2622_; 
v_snd_2620_ = lean_ctor_get(v_a_2616_, 1);
lean_inc(v_snd_2620_);
lean_dec(v_a_2616_);
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 0, v_snd_2620_);
v___x_2622_ = v___x_2618_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_snd_2620_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
v_a_2625_ = lean_ctor_get(v___x_2615_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2615_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2615_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2615_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_a_2584_);
lean_dec(v_mvarId_2577_);
lean_dec(v_h_2576_);
v_a_2633_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2585_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2585_);
v___x_2635_ = lean_box(0);
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
v_resetjp_2634_:
{
lean_object* v___x_2638_; 
if (v_isShared_2636_ == 0)
{
v___x_2638_ = v___x_2635_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2639_; 
v_reuseFailAlloc_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_a_2633_);
v___x_2638_ = v_reuseFailAlloc_2639_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
return v___x_2638_;
}
}
}
}
else
{
lean_object* v_a_2641_; lean_object* v___x_2643_; uint8_t v_isShared_2644_; uint8_t v_isSharedCheck_2648_; 
lean_dec(v_mvarId_2577_);
lean_dec(v_h_2576_);
v_a_2641_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2648_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2643_ = v___x_2583_;
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
else
{
lean_inc(v_a_2641_);
lean_dec(v___x_2583_);
v___x_2643_ = lean_box(0);
v_isShared_2644_ = v_isSharedCheck_2648_;
goto v_resetjp_2642_;
}
v_resetjp_2642_:
{
lean_object* v___x_2646_; 
if (v_isShared_2644_ == 0)
{
v___x_2646_ = v___x_2643_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_a_2641_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2649_, lean_object* v_mvarId_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_Lean_Meta_subst___lam__0(v_h_2649_, v_mvarId_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v___y_2652_);
lean_dec_ref(v___y_2651_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2657_, lean_object* v_h_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v___f_2664_; lean_object* v___x_2665_; 
lean_inc(v_mvarId_2657_);
v___f_2664_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2664_, 0, v_h_2658_);
lean_closure_set(v___f_2664_, 1, v_mvarId_2657_);
v___x_2665_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2657_, v___f_2664_, v_a_2659_, v_a_2660_, v_a_2661_, v_a_2662_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2666_, lean_object* v_h_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_, lean_object* v_a_2672_){
_start:
{
lean_object* v_res_2673_; 
v_res_2673_ = l_Lean_Meta_subst(v_mvarId_2666_, v_h_2667_, v_a_2668_, v_a_2669_, v_a_2670_, v_a_2671_);
lean_dec(v_a_2671_);
lean_dec_ref(v_a_2670_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
return v_res_2673_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v___x_2680_; 
v___x_2680_ = l_Lean_Meta_saveState___redArg(v___y_2676_, v___y_2678_);
if (lean_obj_tag(v___x_2680_) == 0)
{
lean_object* v_a_2681_; lean_object* v___x_2682_; 
v_a_2681_ = lean_ctor_get(v___x_2680_, 0);
lean_inc(v_a_2681_);
lean_dec_ref_known(v___x_2680_, 1);
lean_inc(v___y_2678_);
lean_inc_ref(v___y_2677_);
lean_inc(v___y_2676_);
lean_inc_ref(v___y_2675_);
v___x_2682_ = lean_apply_5(v_x_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_, lean_box(0));
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_dec(v_a_2681_);
return v___x_2682_;
}
else
{
lean_object* v_a_2683_; uint8_t v___x_2684_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
v___x_2684_ = l_Lean_Exception_isInterrupt(v_a_2683_);
if (v___x_2684_ == 0)
{
uint8_t v___x_2685_; 
lean_inc(v_a_2683_);
v___x_2685_ = l_Lean_Exception_isRuntime(v_a_2683_);
if (v___x_2685_ == 0)
{
lean_object* v___x_2686_; 
lean_dec_ref_known(v___x_2682_, 1);
v___x_2686_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2681_, v___y_2676_, v___y_2678_);
if (lean_obj_tag(v___x_2686_) == 0)
{
lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2693_; 
v_isSharedCheck_2693_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2693_ == 0)
{
lean_object* v_unused_2694_; 
v_unused_2694_ = lean_ctor_get(v___x_2686_, 0);
lean_dec(v_unused_2694_);
v___x_2688_ = v___x_2686_;
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v___x_2686_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2693_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2691_; 
if (v_isShared_2689_ == 0)
{
lean_ctor_set_tag(v___x_2688_, 1);
lean_ctor_set(v___x_2688_, 0, v_a_2683_);
v___x_2691_ = v___x_2688_;
goto v_reusejp_2690_;
}
else
{
lean_object* v_reuseFailAlloc_2692_; 
v_reuseFailAlloc_2692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2692_, 0, v_a_2683_);
v___x_2691_ = v_reuseFailAlloc_2692_;
goto v_reusejp_2690_;
}
v_reusejp_2690_:
{
return v___x_2691_;
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec(v_a_2683_);
v_a_2695_ = lean_ctor_get(v___x_2686_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2686_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2686_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2686_);
v___x_2697_ = lean_box(0);
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
v_resetjp_2696_:
{
lean_object* v___x_2700_; 
if (v_isShared_2698_ == 0)
{
v___x_2700_ = v___x_2697_;
goto v_reusejp_2699_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v_a_2695_);
v___x_2700_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2699_;
}
v_reusejp_2699_:
{
return v___x_2700_;
}
}
}
}
else
{
lean_dec(v_a_2683_);
lean_dec(v_a_2681_);
return v___x_2682_;
}
}
else
{
lean_dec(v_a_2683_);
lean_dec(v_a_2681_);
return v___x_2682_;
}
}
}
else
{
lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2710_; 
lean_dec_ref(v_x_2674_);
v_a_2703_ = lean_ctor_get(v___x_2680_, 0);
v_isSharedCheck_2710_ = !lean_is_exclusive(v___x_2680_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2705_ = v___x_2680_;
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_dec(v___x_2680_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2710_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2708_; 
if (v_isShared_2706_ == 0)
{
v___x_2708_ = v___x_2705_;
goto v_reusejp_2707_;
}
else
{
lean_object* v_reuseFailAlloc_2709_; 
v_reuseFailAlloc_2709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2709_, 0, v_a_2703_);
v___x_2708_ = v_reuseFailAlloc_2709_;
goto v_reusejp_2707_;
}
v_reusejp_2707_:
{
return v___x_2708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
lean_dec(v___y_2713_);
lean_dec_ref(v___y_2712_);
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2718_, lean_object* v_x_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
lean_object* v___x_2725_; 
v___x_2725_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
return v___x_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2726_, lean_object* v_x_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_res_2733_; 
v_res_2733_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2726_, v_x_2727_, v___y_2728_, v___y_2729_, v___y_2730_, v___y_2731_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
lean_dec(v___y_2729_);
lean_dec_ref(v___y_2728_);
return v_res_2733_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_, lean_object* v___y_2738_){
_start:
{
lean_object* v_ref_2740_; lean_object* v___x_2741_; lean_object* v_a_2742_; lean_object* v___x_2744_; uint8_t v_isShared_2745_; uint8_t v_isSharedCheck_2750_; 
v_ref_2740_ = lean_ctor_get(v___y_2737_, 2);
v___x_2741_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msg_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_);
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_isSharedCheck_2750_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2750_ == 0)
{
v___x_2744_ = v___x_2741_;
v_isShared_2745_ = v_isSharedCheck_2750_;
goto v_resetjp_2743_;
}
else
{
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2744_ = lean_box(0);
v_isShared_2745_ = v_isSharedCheck_2750_;
goto v_resetjp_2743_;
}
v_resetjp_2743_:
{
lean_object* v___x_2746_; lean_object* v___x_2748_; 
lean_inc(v_ref_2740_);
v___x_2746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2746_, 0, v_ref_2740_);
lean_ctor_set(v___x_2746_, 1, v_a_2742_);
if (v_isShared_2745_ == 0)
{
lean_ctor_set_tag(v___x_2744_, 1);
lean_ctor_set(v___x_2744_, 0, v___x_2746_);
v___x_2748_ = v___x_2744_;
goto v_reusejp_2747_;
}
else
{
lean_object* v_reuseFailAlloc_2749_; 
v_reuseFailAlloc_2749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2749_, 0, v___x_2746_);
v___x_2748_ = v_reuseFailAlloc_2749_;
goto v_reusejp_2747_;
}
v_reusejp_2747_:
{
return v___x_2748_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
return v_res_2757_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; 
v___x_2768_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2769_ = l_Lean_stringToMessageData(v___x_2768_);
return v___x_2769_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2786_ = l_Lean_stringToMessageData(v___x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2795_, uint8_t v_substLHS_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_, lean_object* v___y_2800_){
_start:
{
lean_object* v___x_2802_; 
lean_inc(v_mvarId_2795_);
v___x_2802_ = l_Lean_MVarId_getType_x27(v_mvarId_2795_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_2802_) == 0)
{
lean_object* v_a_2803_; 
v_a_2803_ = lean_ctor_get(v___x_2802_, 0);
lean_inc(v_a_2803_);
lean_dec_ref_known(v___x_2802_, 1);
if (lean_obj_tag(v_a_2803_) == 7)
{
lean_object* v_binderType_2807_; lean_object* v_body_2808_; uint8_t v___x_2809_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2821_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v___y_2904_; lean_object* v_fst_2944_; lean_object* v_fst_2945_; lean_object* v_fst_2946_; lean_object* v_snd_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2951_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; lean_object* v___y_2967_; 
v_binderType_2807_ = lean_ctor_get(v_a_2803_, 1);
lean_inc_ref(v_binderType_2807_);
v_body_2808_ = lean_ctor_get(v_a_2803_, 2);
lean_inc_ref(v_body_2808_);
lean_dec_ref_known(v_a_2803_, 3);
v___x_2809_ = l_Lean_Expr_hasLooseBVars(v_body_2808_);
if (v___x_2809_ == 0)
{
lean_object* v___x_2978_; 
v___x_2978_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2807_, v___y_2798_);
if (lean_obj_tag(v___x_2978_) == 0)
{
lean_object* v_a_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_a_2979_ = lean_ctor_get(v___x_2978_, 0);
lean_inc(v_a_2979_);
lean_dec_ref_known(v___x_2978_, 1);
v___x_2980_ = l_Lean_Expr_cleanupAnnotations(v_a_2979_);
v___x_2981_ = l_Lean_Expr_isApp(v___x_2980_);
if (v___x_2981_ == 0)
{
lean_dec_ref(v___x_2980_);
lean_dec_ref(v_body_2808_);
lean_dec(v_mvarId_2795_);
v___y_2964_ = v___y_2797_;
v___y_2965_ = v___y_2798_;
v___y_2966_ = v___y_2799_;
v___y_2967_ = v___y_2800_;
goto v___jp_2963_;
}
else
{
lean_object* v_arg_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; 
v_arg_2982_ = lean_ctor_get(v___x_2980_, 1);
lean_inc_ref(v_arg_2982_);
v___x_2983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2980_);
v___x_2984_ = l_Lean_Expr_isApp(v___x_2983_);
if (v___x_2984_ == 0)
{
lean_dec_ref(v___x_2983_);
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_body_2808_);
lean_dec(v_mvarId_2795_);
v___y_2964_ = v___y_2797_;
v___y_2965_ = v___y_2798_;
v___y_2966_ = v___y_2799_;
v___y_2967_ = v___y_2800_;
goto v___jp_2963_;
}
else
{
lean_object* v_arg_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; 
v_arg_2985_ = lean_ctor_get(v___x_2983_, 1);
lean_inc_ref(v_arg_2985_);
v___x_2986_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2983_);
v___x_2987_ = l_Lean_Expr_isApp(v___x_2986_);
if (v___x_2987_ == 0)
{
lean_dec_ref(v___x_2986_);
lean_dec_ref(v_arg_2985_);
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_body_2808_);
lean_dec(v_mvarId_2795_);
v___y_2964_ = v___y_2797_;
v___y_2965_ = v___y_2798_;
v___y_2966_ = v___y_2799_;
v___y_2967_ = v___y_2800_;
goto v___jp_2963_;
}
else
{
lean_object* v_arg_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v_arg_2988_ = lean_ctor_get(v___x_2986_, 1);
lean_inc_ref(v_arg_2988_);
v___x_2989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2986_);
v___x_2990_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_2991_ = l_Lean_Expr_isConstOf(v___x_2989_, v___x_2990_);
if (v___x_2991_ == 0)
{
uint8_t v___x_2992_; 
v___x_2992_ = l_Lean_Expr_isApp(v___x_2989_);
if (v___x_2992_ == 0)
{
lean_dec_ref(v___x_2989_);
lean_dec_ref(v_arg_2988_);
lean_dec_ref(v_arg_2985_);
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_body_2808_);
lean_dec(v_mvarId_2795_);
v___y_2964_ = v___y_2797_;
v___y_2965_ = v___y_2798_;
v___y_2966_ = v___y_2799_;
v___y_2967_ = v___y_2800_;
goto v___jp_2963_;
}
else
{
lean_object* v_arg_2993_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v_arg_2993_ = lean_ctor_get(v___x_2989_, 1);
lean_inc_ref(v_arg_2993_);
v___x_3001_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2989_);
v___x_3002_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_3003_ = l_Lean_Expr_isConstOf(v___x_3001_, v___x_3002_);
lean_dec_ref(v___x_3001_);
if (v___x_3003_ == 0)
{
lean_dec_ref(v_arg_2993_);
lean_dec_ref(v_arg_2988_);
lean_dec_ref(v_arg_2985_);
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_body_2808_);
lean_dec(v_mvarId_2795_);
v___y_2964_ = v___y_2797_;
v___y_2965_ = v___y_2798_;
v___y_2966_ = v___y_2799_;
v___y_2967_ = v___y_2800_;
goto v___jp_2963_;
}
else
{
lean_object* v___x_3004_; 
lean_inc_ref(v_arg_2993_);
v___x_3004_ = l_Lean_Meta_isExprDefEq(v_arg_2993_, v_arg_2985_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
if (lean_obj_tag(v___x_3004_) == 0)
{
lean_object* v_a_3005_; uint8_t v___x_3006_; 
v_a_3005_ = lean_ctor_get(v___x_3004_, 0);
lean_inc(v_a_3005_);
lean_dec_ref_known(v___x_3004_, 1);
v___x_3006_ = lean_unbox(v_a_3005_);
lean_dec(v_a_3005_);
if (v___x_3006_ == 0)
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v_arg_2993_);
lean_dec_ref(v_arg_2988_);
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_body_2808_);
lean_dec(v_mvarId_2795_);
v___x_3007_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_3008_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3007_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
v_a_3009_ = lean_ctor_get(v___x_3008_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_3008_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_3008_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_3008_);
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
else
{
v___y_2995_ = v___y_2797_;
v___y_2996_ = v___y_2798_;
v___y_2997_ = v___y_2799_;
v___y_2998_ = v___y_2800_;
goto v___jp_2994_;
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec_ref(v_arg_2993_);
lean_dec_ref(v_arg_2988_);
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_body_2808_);
lean_dec(v_mvarId_2795_);
v_a_3017_ = lean_ctor_get(v___x_3004_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_3004_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_3004_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_3004_);
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
v___jp_2994_:
{
if (v_substLHS_2796_ == 0)
{
lean_object* v___x_2999_; 
v___x_2999_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2944_ = v_arg_2993_;
v_fst_2945_ = v_arg_2988_;
v_fst_2946_ = v_arg_2982_;
v_snd_2947_ = v___x_2999_;
v___y_2948_ = v___y_2995_;
v___y_2949_ = v___y_2996_;
v___y_2950_ = v___y_2997_;
v___y_2951_ = v___y_2998_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_3000_; 
v___x_3000_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2944_ = v_arg_2993_;
v_fst_2945_ = v_arg_2982_;
v_fst_2946_ = v_arg_2988_;
v_snd_2947_ = v___x_3000_;
v___y_2948_ = v___y_2995_;
v___y_2949_ = v___y_2996_;
v___y_2950_ = v___y_2997_;
v___y_2951_ = v___y_2998_;
goto v___jp_2943_;
}
}
}
}
else
{
lean_dec_ref(v___x_2989_);
if (v_substLHS_2796_ == 0)
{
lean_object* v___x_3025_; 
v___x_3025_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2944_ = v_arg_2988_;
v_fst_2945_ = v_arg_2985_;
v_fst_2946_ = v_arg_2982_;
v_snd_2947_ = v___x_3025_;
v___y_2948_ = v___y_2797_;
v___y_2949_ = v___y_2798_;
v___y_2950_ = v___y_2799_;
v___y_2951_ = v___y_2800_;
goto v___jp_2943_;
}
else
{
lean_object* v___x_3026_; 
v___x_3026_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2944_ = v_arg_2988_;
v_fst_2945_ = v_arg_2982_;
v_fst_2946_ = v_arg_2985_;
v_snd_2947_ = v___x_3026_;
v___y_2948_ = v___y_2797_;
v___y_2949_ = v___y_2798_;
v___y_2950_ = v___y_2799_;
v___y_2951_ = v___y_2800_;
goto v___jp_2943_;
}
}
}
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec_ref(v_body_2808_);
lean_dec(v_mvarId_2795_);
v_a_3027_ = lean_ctor_get(v___x_2978_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2978_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2978_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2978_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
else
{
lean_dec_ref(v_body_2808_);
lean_dec_ref(v_binderType_2807_);
lean_dec(v_mvarId_2795_);
goto v___jp_2804_;
}
v___jp_2810_:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; uint8_t v___x_2825_; lean_object* v___x_2826_; 
v___x_2822_ = lean_mk_empty_array_with_capacity(v___y_2812_);
lean_inc_ref(v___x_2822_);
v___x_2823_ = lean_array_push(v___x_2822_, v___y_2813_);
v___x_2824_ = 1;
v___x_2825_ = 1;
v___x_2826_ = l_Lean_Meta_mkLambdaFVars(v___x_2823_, v_body_2808_, v___x_2809_, v___x_2824_, v___x_2809_, v___x_2824_, v___x_2825_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
lean_dec_ref(v___x_2823_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc_n(v_a_2827_, 2);
lean_dec_ref_known(v___x_2826_, 1);
lean_inc_ref(v___y_2815_);
v___x_2828_ = lean_array_push(v___x_2822_, v___y_2815_);
v___x_2829_ = l_Lean_Expr_beta(v_a_2827_, v___x_2828_);
lean_inc(v___y_2816_);
v___x_2830_ = l_Lean_MVarId_getTag(v___y_2816_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
lean_inc_ref(v___x_2829_);
v___x_2832_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2829_, v_a_2831_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2834_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
v___x_2834_ = l_Lean_Meta_getLevel(v___x_2829_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2834_) == 0)
{
lean_object* v_a_2835_; lean_object* v___x_2836_; 
v_a_2835_ = lean_ctor_get(v___x_2834_, 0);
lean_inc(v_a_2835_);
lean_dec_ref_known(v___x_2834_, 1);
lean_inc_ref(v___y_2817_);
v___x_2836_ = l_Lean_Meta_getLevel(v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_, v___y_2821_);
if (lean_obj_tag(v___x_2836_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2854_; 
v_a_2837_ = lean_ctor_get(v___x_2836_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v___x_2836_, 1);
v___x_2838_ = lean_box(0);
v___x_2839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2839_, 0, v_a_2837_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
v___x_2840_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2840_, 0, v_a_2835_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
lean_inc(v___y_2811_);
v___x_2841_ = l_Lean_mkConst(v___y_2811_, v___x_2840_);
lean_inc(v_a_2833_);
lean_inc_ref(v___y_2815_);
v___x_2842_ = l_Lean_mkApp4(v___x_2841_, v___y_2817_, v___y_2815_, v_a_2827_, v_a_2833_);
v___x_2843_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v___y_2816_, v___x_2842_, v___y_2819_);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2854_ == 0)
{
lean_object* v_unused_2855_; 
v_unused_2855_ = lean_ctor_get(v___x_2843_, 0);
lean_dec(v_unused_2855_);
v___x_2845_ = v___x_2843_;
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
else
{
lean_dec(v___x_2843_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2854_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2852_; 
v___x_2847_ = l_Lean_Meta_FVarSubst_empty;
v___x_2848_ = l_Lean_Meta_FVarSubst_insert(v___x_2847_, v___y_2814_, v___y_2815_);
v___x_2849_ = l_Lean_Expr_mvarId_x21(v_a_2833_);
lean_dec(v_a_2833_);
v___x_2850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2850_, 0, v___x_2848_);
lean_ctor_set(v___x_2850_, 1, v___x_2849_);
if (v_isShared_2846_ == 0)
{
lean_ctor_set(v___x_2845_, 0, v___x_2850_);
v___x_2852_ = v___x_2845_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v___x_2850_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_a_2835_);
lean_dec(v_a_2833_);
lean_dec(v_a_2827_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
v_a_2856_ = lean_ctor_get(v___x_2836_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2836_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2836_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2836_);
v___x_2858_ = lean_box(0);
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
v_resetjp_2857_:
{
lean_object* v___x_2861_; 
if (v_isShared_2859_ == 0)
{
v___x_2861_ = v___x_2858_;
goto v_reusejp_2860_;
}
else
{
lean_object* v_reuseFailAlloc_2862_; 
v_reuseFailAlloc_2862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_a_2856_);
v___x_2861_ = v_reuseFailAlloc_2862_;
goto v_reusejp_2860_;
}
v_reusejp_2860_:
{
return v___x_2861_;
}
}
}
}
else
{
lean_object* v_a_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2871_; 
lean_dec(v_a_2833_);
lean_dec(v_a_2827_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
v_a_2864_ = lean_ctor_get(v___x_2834_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2834_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2834_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2834_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2869_; 
if (v_isShared_2867_ == 0)
{
v___x_2869_ = v___x_2866_;
goto v_reusejp_2868_;
}
else
{
lean_object* v_reuseFailAlloc_2870_; 
v_reuseFailAlloc_2870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_a_2864_);
v___x_2869_ = v_reuseFailAlloc_2870_;
goto v_reusejp_2868_;
}
v_reusejp_2868_:
{
return v___x_2869_;
}
}
}
}
else
{
lean_object* v_a_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2879_; 
lean_dec_ref(v___x_2829_);
lean_dec(v_a_2827_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
v_a_2872_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2832_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2832_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2877_; 
if (v_isShared_2875_ == 0)
{
v___x_2877_ = v___x_2874_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v___x_2882_; uint8_t v_isShared_2883_; uint8_t v_isSharedCheck_2887_; 
lean_dec_ref(v___x_2829_);
lean_dec(v_a_2827_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
v_a_2880_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2830_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2830_);
v___x_2882_ = lean_box(0);
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
v_resetjp_2881_:
{
lean_object* v___x_2885_; 
if (v_isShared_2883_ == 0)
{
v___x_2885_ = v___x_2882_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_a_2880_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
}
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v___x_2822_);
lean_dec_ref(v___y_2817_);
lean_dec(v___y_2816_);
lean_dec_ref(v___y_2815_);
lean_dec(v___y_2814_);
v_a_2888_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2826_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2826_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
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
v___jp_2896_:
{
lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; 
v___x_2905_ = l_Lean_Expr_fvarId_x21(v___y_2898_);
v___x_2906_ = lean_unsigned_to_nat(1u);
v___x_2907_ = lean_mk_empty_array_with_capacity(v___x_2906_);
lean_inc(v___x_2905_);
v___x_2908_ = lean_array_push(v___x_2907_, v___x_2905_);
v___x_2909_ = l_Lean_MVarId_revert(v_mvarId_2795_, v___x_2908_, v___x_2809_, v___x_2809_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
if (lean_obj_tag(v___x_2909_) == 0)
{
lean_object* v_a_2910_; lean_object* v_fst_2911_; lean_object* v_snd_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2934_; 
v_a_2910_ = lean_ctor_get(v___x_2909_, 0);
lean_inc(v_a_2910_);
lean_dec_ref_known(v___x_2909_, 1);
v_fst_2911_ = lean_ctor_get(v_a_2910_, 0);
v_snd_2912_ = lean_ctor_get(v_a_2910_, 1);
v_isSharedCheck_2934_ = !lean_is_exclusive(v_a_2910_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2914_ = v_a_2910_;
v_isShared_2915_ = v_isSharedCheck_2934_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_snd_2912_);
lean_inc(v_fst_2911_);
lean_dec(v_a_2910_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2934_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = lean_array_get_size(v_fst_2911_);
lean_dec(v_fst_2911_);
v___x_2917_ = lean_nat_dec_eq(v___x_2916_, v___x_2906_);
if (v___x_2917_ == 0)
{
lean_object* v___x_2918_; lean_object* v___x_2919_; lean_object* v___x_2921_; 
lean_dec(v_snd_2912_);
lean_dec(v___x_2905_);
lean_dec_ref(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec_ref(v_body_2808_);
v___x_2918_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2919_ = l_Lean_MessageData_ofExpr(v___y_2898_);
if (v_isShared_2915_ == 0)
{
lean_ctor_set_tag(v___x_2914_, 7);
lean_ctor_set(v___x_2914_, 1, v___x_2919_);
lean_ctor_set(v___x_2914_, 0, v___x_2918_);
v___x_2921_ = v___x_2914_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2918_);
lean_ctor_set(v_reuseFailAlloc_2933_, 1, v___x_2919_);
v___x_2921_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
v___x_2922_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2921_);
lean_ctor_set(v___x_2923_, 1, v___x_2922_);
v___x_2924_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2923_, v___y_2901_, v___y_2902_, v___y_2903_, v___y_2904_);
v_a_2925_ = lean_ctor_get(v___x_2924_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2924_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2924_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2924_);
v___x_2927_ = lean_box(0);
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
v_resetjp_2926_:
{
lean_object* v___x_2930_; 
if (v_isShared_2928_ == 0)
{
v___x_2930_ = v___x_2927_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
v___x_2930_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
return v___x_2930_;
}
}
}
}
else
{
lean_del_object(v___x_2914_);
v___y_2811_ = v___y_2897_;
v___y_2812_ = v___x_2906_;
v___y_2813_ = v___y_2898_;
v___y_2814_ = v___x_2905_;
v___y_2815_ = v___y_2899_;
v___y_2816_ = v_snd_2912_;
v___y_2817_ = v___y_2900_;
v___y_2818_ = v___y_2901_;
v___y_2819_ = v___y_2902_;
v___y_2820_ = v___y_2903_;
v___y_2821_ = v___y_2904_;
goto v___jp_2810_;
}
}
}
else
{
lean_object* v_a_2935_; lean_object* v___x_2937_; uint8_t v_isShared_2938_; uint8_t v_isSharedCheck_2942_; 
lean_dec(v___x_2905_);
lean_dec_ref(v___y_2900_);
lean_dec_ref(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec_ref(v_body_2808_);
v_a_2935_ = lean_ctor_get(v___x_2909_, 0);
v_isSharedCheck_2942_ = !lean_is_exclusive(v___x_2909_);
if (v_isSharedCheck_2942_ == 0)
{
v___x_2937_ = v___x_2909_;
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
else
{
lean_inc(v_a_2935_);
lean_dec(v___x_2909_);
v___x_2937_ = lean_box(0);
v_isShared_2938_ = v_isSharedCheck_2942_;
goto v_resetjp_2936_;
}
v_resetjp_2936_:
{
lean_object* v___x_2940_; 
if (v_isShared_2938_ == 0)
{
v___x_2940_ = v___x_2937_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
v___x_2940_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
return v___x_2940_;
}
}
}
}
v___jp_2943_:
{
uint8_t v___x_2952_; 
v___x_2952_ = l_Lean_Expr_isFVar(v_fst_2946_);
if (v___x_2952_ == 0)
{
lean_object* v___x_2953_; lean_object* v___x_2954_; lean_object* v_a_2955_; lean_object* v___x_2957_; uint8_t v_isShared_2958_; uint8_t v_isSharedCheck_2962_; 
lean_dec_ref(v_fst_2946_);
lean_dec_ref(v_fst_2945_);
lean_dec_ref(v_fst_2944_);
lean_dec_ref(v_body_2808_);
lean_dec(v_mvarId_2795_);
v___x_2953_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2954_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2953_, v___y_2948_, v___y_2949_, v___y_2950_, v___y_2951_);
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2957_ = v___x_2954_;
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
else
{
lean_inc(v_a_2955_);
lean_dec(v___x_2954_);
v___x_2957_ = lean_box(0);
v_isShared_2958_ = v_isSharedCheck_2962_;
goto v_resetjp_2956_;
}
v_resetjp_2956_:
{
lean_object* v___x_2960_; 
if (v_isShared_2958_ == 0)
{
v___x_2960_ = v___x_2957_;
goto v_reusejp_2959_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v_a_2955_);
v___x_2960_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2959_;
}
v_reusejp_2959_:
{
return v___x_2960_;
}
}
}
else
{
v___y_2897_ = v_snd_2947_;
v___y_2898_ = v_fst_2946_;
v___y_2899_ = v_fst_2945_;
v___y_2900_ = v_fst_2944_;
v___y_2901_ = v___y_2948_;
v___y_2902_ = v___y_2949_;
v___y_2903_ = v___y_2950_;
v___y_2904_ = v___y_2951_;
goto v___jp_2896_;
}
}
v___jp_2963_:
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
v___x_2968_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_2969_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2968_, v___y_2964_, v___y_2965_, v___y_2966_, v___y_2967_);
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2969_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_dec(v_a_2803_);
lean_dec(v_mvarId_2795_);
goto v___jp_2804_;
}
v___jp_2804_:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2805_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2806_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2805_, v___y_2797_, v___y_2798_, v___y_2799_, v___y_2800_);
return v___x_2806_;
}
}
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_mvarId_2795_);
v_a_3035_ = lean_ctor_get(v___x_2802_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_2802_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_2802_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_2802_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object* v_mvarId_3043_, lean_object* v_substLHS_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_, lean_object* v___y_3049_){
_start:
{
uint8_t v_substLHS_boxed_3050_; lean_object* v_res_3051_; 
v_substLHS_boxed_3050_ = lean_unbox(v_substLHS_3044_);
v_res_3051_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_3043_, v_substLHS_boxed_3050_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_);
lean_dec(v___y_3048_);
lean_dec_ref(v___y_3047_);
lean_dec(v___y_3046_);
lean_dec_ref(v___y_3045_);
return v_res_3051_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3052_, lean_object* v_i_3053_, lean_object* v_k_3054_){
_start:
{
lean_object* v___x_3055_; uint8_t v___x_3056_; 
v___x_3055_ = lean_array_get_size(v_keys_3052_);
v___x_3056_ = lean_nat_dec_lt(v_i_3053_, v___x_3055_);
if (v___x_3056_ == 0)
{
lean_dec(v_i_3053_);
return v___x_3056_;
}
else
{
lean_object* v_k_x27_3057_; uint8_t v___x_3058_; 
v_k_x27_3057_ = lean_array_fget_borrowed(v_keys_3052_, v_i_3053_);
v___x_3058_ = l_Lean_instBEqMVarId_beq(v_k_3054_, v_k_x27_3057_);
if (v___x_3058_ == 0)
{
lean_object* v___x_3059_; lean_object* v___x_3060_; 
v___x_3059_ = lean_unsigned_to_nat(1u);
v___x_3060_ = lean_nat_add(v_i_3053_, v___x_3059_);
lean_dec(v_i_3053_);
v_i_3053_ = v___x_3060_;
goto _start;
}
else
{
lean_dec(v_i_3053_);
return v___x_3056_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3062_, lean_object* v_i_3063_, lean_object* v_k_3064_){
_start:
{
uint8_t v_res_3065_; lean_object* v_r_3066_; 
v_res_3065_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3062_, v_i_3063_, v_k_3064_);
lean_dec(v_k_3064_);
lean_dec_ref(v_keys_3062_);
v_r_3066_ = lean_box(v_res_3065_);
return v_r_3066_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3067_, size_t v_x_3068_, lean_object* v_x_3069_){
_start:
{
if (lean_obj_tag(v_x_3067_) == 0)
{
lean_object* v_es_3070_; lean_object* v___x_3071_; size_t v___x_3072_; size_t v___x_3073_; lean_object* v_j_3074_; lean_object* v___x_3075_; 
v_es_3070_ = lean_ctor_get(v_x_3067_, 0);
v___x_3071_ = lean_box(2);
v___x_3072_ = ((size_t)31ULL);
v___x_3073_ = lean_usize_land(v_x_3068_, v___x_3072_);
v_j_3074_ = lean_usize_to_nat(v___x_3073_);
v___x_3075_ = lean_array_get_borrowed(v___x_3071_, v_es_3070_, v_j_3074_);
lean_dec(v_j_3074_);
switch(lean_obj_tag(v___x_3075_))
{
case 0:
{
lean_object* v_key_3076_; uint8_t v___x_3077_; 
v_key_3076_ = lean_ctor_get(v___x_3075_, 0);
v___x_3077_ = l_Lean_instBEqMVarId_beq(v_x_3069_, v_key_3076_);
return v___x_3077_;
}
case 1:
{
lean_object* v_node_3078_; size_t v___x_3079_; size_t v___x_3080_; 
v_node_3078_ = lean_ctor_get(v___x_3075_, 0);
v___x_3079_ = ((size_t)5ULL);
v___x_3080_ = lean_usize_shift_right(v_x_3068_, v___x_3079_);
v_x_3067_ = v_node_3078_;
v_x_3068_ = v___x_3080_;
goto _start;
}
default: 
{
uint8_t v___x_3082_; 
v___x_3082_ = 0;
return v___x_3082_;
}
}
}
else
{
lean_object* v_ks_3083_; lean_object* v___x_3084_; uint8_t v___x_3085_; 
v_ks_3083_ = lean_ctor_get(v_x_3067_, 0);
v___x_3084_ = lean_unsigned_to_nat(0u);
v___x_3085_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3083_, v___x_3084_, v_x_3069_);
return v___x_3085_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3086_, lean_object* v_x_3087_, lean_object* v_x_3088_){
_start:
{
size_t v_x_10584__boxed_3089_; uint8_t v_res_3090_; lean_object* v_r_3091_; 
v_x_10584__boxed_3089_ = lean_unbox_usize(v_x_3087_);
lean_dec(v_x_3087_);
v_res_3090_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3086_, v_x_10584__boxed_3089_, v_x_3088_);
lean_dec(v_x_3088_);
lean_dec_ref(v_x_3086_);
v_r_3091_ = lean_box(v_res_3090_);
return v_r_3091_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3092_, lean_object* v_x_3093_){
_start:
{
uint64_t v___x_3094_; size_t v___x_3095_; uint8_t v___x_3096_; 
v___x_3094_ = l_Lean_instHashableMVarId_hash(v_x_3093_);
v___x_3095_ = lean_uint64_to_usize(v___x_3094_);
v___x_3096_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3092_, v___x_3095_, v_x_3093_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3097_, lean_object* v_x_3098_){
_start:
{
uint8_t v_res_3099_; lean_object* v_r_3100_; 
v_res_3099_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3097_, v_x_3098_);
lean_dec(v_x_3098_);
lean_dec_ref(v_x_3097_);
v_r_3100_ = lean_box(v_res_3099_);
return v_r_3100_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___x_3104_; lean_object* v_mctx_3105_; lean_object* v_eAssignment_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v___x_3104_ = lean_st_ref_get(v___y_3102_);
v_mctx_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc_ref(v_mctx_3105_);
lean_dec(v___x_3104_);
v_eAssignment_3106_ = lean_ctor_get(v_mctx_3105_, 8);
lean_inc_ref(v_eAssignment_3106_);
lean_dec_ref(v_mctx_3105_);
v___x_3107_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3106_, v_mvarId_3101_);
lean_dec_ref(v_eAssignment_3106_);
v___x_3108_ = lean_box(v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_){
_start:
{
lean_object* v_res_3113_; 
v_res_3113_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3110_, v___y_3111_);
lean_dec(v___y_3111_);
lean_dec(v_mvarId_3110_);
return v_res_3113_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3115_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3116_ = l_Lean_stringToMessageData(v___x_3115_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3117_, uint8_t v___x_3118_, lean_object* v_____r_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_, lean_object* v___y_3123_){
_start:
{
lean_object* v___x_3157_; lean_object* v_a_3158_; uint8_t v___x_3159_; 
v___x_3157_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3117_, v___y_3121_);
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3158_);
lean_dec_ref(v___x_3157_);
v___x_3159_ = lean_unbox(v_a_3158_);
lean_dec(v_a_3158_);
if (v___x_3159_ == 0)
{
goto v___jp_3125_;
}
else
{
lean_object* v___x_3160_; lean_object* v___x_3161_; lean_object* v_a_3162_; lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3169_; 
lean_dec(v_mvarId_3117_);
v___x_3160_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3161_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3160_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
v_a_3162_ = lean_ctor_get(v___x_3161_, 0);
v_isSharedCheck_3169_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3169_ == 0)
{
v___x_3164_ = v___x_3161_;
v_isShared_3165_ = v_isSharedCheck_3169_;
goto v_resetjp_3163_;
}
else
{
lean_inc(v_a_3162_);
lean_dec(v___x_3161_);
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
v___jp_3125_:
{
lean_object* v___x_3126_; 
v___x_3126_ = l_Lean_Meta_intro1Core(v_mvarId_3117_, v___x_3118_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
if (lean_obj_tag(v___x_3126_) == 0)
{
lean_object* v_a_3127_; lean_object* v_fst_3128_; lean_object* v_snd_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; 
v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
lean_inc(v_a_3127_);
lean_dec_ref_known(v___x_3126_, 1);
v_fst_3128_ = lean_ctor_get(v_a_3127_, 0);
lean_inc(v_fst_3128_);
v_snd_3129_ = lean_ctor_get(v_a_3127_, 1);
lean_inc(v_snd_3129_);
lean_dec(v_a_3127_);
v___x_3130_ = lean_box(0);
v___x_3131_ = l_Lean_Meta_substEq(v_snd_3129_, v_fst_3128_, v___x_3130_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
if (lean_obj_tag(v___x_3131_) == 0)
{
lean_object* v_a_3132_; lean_object* v___x_3134_; uint8_t v_isShared_3135_; uint8_t v_isSharedCheck_3140_; 
v_a_3132_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3134_ = v___x_3131_;
v_isShared_3135_ = v_isSharedCheck_3140_;
goto v_resetjp_3133_;
}
else
{
lean_inc(v_a_3132_);
lean_dec(v___x_3131_);
v___x_3134_ = lean_box(0);
v_isShared_3135_ = v_isSharedCheck_3140_;
goto v_resetjp_3133_;
}
v_resetjp_3133_:
{
lean_object* v___x_3136_; lean_object* v___x_3138_; 
v___x_3136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3136_, 0, v_a_3132_);
if (v_isShared_3135_ == 0)
{
lean_ctor_set(v___x_3134_, 0, v___x_3136_);
v___x_3138_ = v___x_3134_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v___x_3136_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_a_3141_ = lean_ctor_get(v___x_3131_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3131_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3131_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3131_);
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
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
v_a_3149_ = lean_ctor_get(v___x_3126_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3126_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3126_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3126_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3170_, lean_object* v___x_3171_, lean_object* v_____r_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_, lean_object* v___y_3177_){
_start:
{
uint8_t v___x_10656__boxed_3178_; lean_object* v_res_3179_; 
v___x_10656__boxed_3178_ = lean_unbox(v___x_3171_);
v_res_3179_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3170_, v___x_10656__boxed_3178_, v_____r_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
lean_dec(v___y_3176_);
lean_dec_ref(v___y_3175_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
return v_res_3179_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__2(void){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3183_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3184_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
v___x_3185_ = l_Lean_Name_append(v___x_3184_, v___x_3183_);
return v___x_3185_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__4(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3187_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__3));
v___x_3188_ = l_Lean_stringToMessageData(v___x_3187_);
return v___x_3188_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__6(void){
_start:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__5));
v___x_3191_ = l_Lean_stringToMessageData(v___x_3190_);
return v___x_3191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3192_, uint8_t v_substLHS_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_){
_start:
{
lean_object* v___y_3200_; lean_object* v___x_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3218_ = lean_box(v_substLHS_3193_);
lean_inc_n(v_mvarId_3192_, 2);
v___f_3219_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3219_, 0, v_mvarId_3192_);
lean_closure_set(v___f_3219_, 1, v___x_3218_);
v___x_3220_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
v___x_3221_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3192_, v___x_3220_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
lean_dec_ref_known(v___x_3221_, 1);
lean_inc(v_mvarId_3192_);
v___x_3222_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed), 8, 3);
lean_closure_set(v___x_3222_, 0, lean_box(0));
lean_closure_set(v___x_3222_, 1, v_mvarId_3192_);
lean_closure_set(v___x_3222_, 2, v___f_3219_);
v___x_3223_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3222_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_dec(v_mvarId_3192_);
return v___x_3223_;
}
else
{
lean_object* v_a_3224_; uint8_t v___x_3225_; 
v_a_3224_ = lean_ctor_get(v___x_3223_, 0);
v___x_3225_ = l_Lean_Exception_isInterrupt(v_a_3224_);
if (v___x_3225_ == 0)
{
uint8_t v___x_3226_; 
lean_inc(v_a_3224_);
v___x_3226_ = l_Lean_Exception_isRuntime(v_a_3224_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3260_; 
lean_inc(v_a_3224_);
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3260_ == 0)
{
lean_object* v_unused_3261_; 
v_unused_3261_ = lean_ctor_get(v___x_3223_, 0);
lean_dec(v_unused_3261_);
v___x_3228_ = v___x_3223_;
v_isShared_3229_ = v_isSharedCheck_3260_;
goto v_resetjp_3227_;
}
else
{
lean_dec(v___x_3223_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3260_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_toCold_3230_; lean_object* v_options_3231_; lean_object* v_inheritedTraceOptions_3232_; uint8_t v_hasTrace_3233_; 
v_toCold_3230_ = lean_ctor_get(v_a_3196_, 0);
v_options_3231_ = lean_ctor_get(v_toCold_3230_, 2);
v_inheritedTraceOptions_3232_ = lean_ctor_get(v_toCold_3230_, 11);
v_hasTrace_3233_ = lean_ctor_get_uint8(v_options_3231_, sizeof(void*)*1);
if (v_hasTrace_3233_ == 0)
{
lean_del_object(v___x_3228_);
lean_dec(v_a_3224_);
goto v___jp_3234_;
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3237_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3238_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__2, &l_Lean_Meta_introSubstEq___closed__2_once, _init_l_Lean_Meta_introSubstEq___closed__2);
v___x_3239_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3232_, v_options_3231_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_del_object(v___x_3228_);
lean_dec(v_a_3224_);
goto v___jp_3234_;
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
v___x_3240_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__4, &l_Lean_Meta_introSubstEq___closed__4_once, _init_l_Lean_Meta_introSubstEq___closed__4);
v___x_3241_ = l_Lean_Exception_toMessageData(v_a_3224_);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__6, &l_Lean_Meta_introSubstEq___closed__6_once, _init_l_Lean_Meta_introSubstEq___closed__6);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
lean_inc(v_mvarId_3192_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v_mvarId_3192_);
v___x_3246_ = v___x_3228_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_mvarId_3192_);
v___x_3246_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3244_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_3237_, v___x_3247_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
v___x_3250_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3192_, v___x_3226_, v_a_3249_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
v___y_3200_ = v___x_3250_;
goto v___jp_3199_;
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v_mvarId_3192_);
v_a_3251_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3258_ == 0)
{
v___x_3253_ = v___x_3248_;
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_a_3251_);
lean_dec(v___x_3248_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3258_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v___x_3256_; 
if (v_isShared_3254_ == 0)
{
v___x_3256_ = v___x_3253_;
goto v_reusejp_3255_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_a_3251_);
v___x_3256_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3255_;
}
v_reusejp_3255_:
{
return v___x_3256_;
}
}
}
}
}
}
v___jp_3234_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; 
v___x_3235_ = lean_box(0);
v___x_3236_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3192_, v___x_3226_, v___x_3235_, v_a_3194_, v_a_3195_, v_a_3196_, v_a_3197_);
v___y_3200_ = v___x_3236_;
goto v___jp_3199_;
}
}
}
else
{
lean_dec(v_mvarId_3192_);
return v___x_3223_;
}
}
else
{
lean_dec(v_mvarId_3192_);
return v___x_3223_;
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec_ref(v___f_3219_);
lean_dec(v_mvarId_3192_);
v_a_3262_ = lean_ctor_get(v___x_3221_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3221_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3221_);
v___x_3264_ = lean_box(0);
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
v_resetjp_3263_:
{
lean_object* v___x_3267_; 
if (v_isShared_3265_ == 0)
{
v___x_3267_ = v___x_3264_;
goto v_reusejp_3266_;
}
else
{
lean_object* v_reuseFailAlloc_3268_; 
v_reuseFailAlloc_3268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3268_, 0, v_a_3262_);
v___x_3267_ = v_reuseFailAlloc_3268_;
goto v_reusejp_3266_;
}
v_reusejp_3266_:
{
return v___x_3267_;
}
}
}
v___jp_3199_:
{
if (lean_obj_tag(v___y_3200_) == 0)
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3209_; 
v_a_3201_ = lean_ctor_get(v___y_3200_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___y_3200_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3203_ = v___y_3200_;
v_isShared_3204_ = v_isSharedCheck_3209_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___y_3200_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3209_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v_a_3205_; lean_object* v___x_3207_; 
v_a_3205_ = lean_ctor_get(v_a_3201_, 0);
lean_inc(v_a_3205_);
lean_dec(v_a_3201_);
if (v_isShared_3204_ == 0)
{
lean_ctor_set(v___x_3203_, 0, v_a_3205_);
v___x_3207_ = v___x_3203_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3205_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
v_a_3210_ = lean_ctor_get(v___y_3200_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___y_3200_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___y_3200_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___y_3200_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object* v_mvarId_3270_, lean_object* v_substLHS_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_){
_start:
{
uint8_t v_substLHS_boxed_3277_; lean_object* v_res_3278_; 
v_substLHS_boxed_3277_ = lean_unbox(v_substLHS_3271_);
v_res_3278_ = l_Lean_Meta_introSubstEq(v_mvarId_3270_, v_substLHS_boxed_3277_, v_a_3272_, v_a_3273_, v_a_3274_, v_a_3275_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
return v_res_3278_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object* v_00_u03b1_3279_, lean_object* v_msg_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___x_3286_; 
v___x_3286_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_3280_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
return v___x_3286_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object* v_00_u03b1_3287_, lean_object* v_msg_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v_res_3294_; 
v_res_3294_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(v_00_u03b1_3287_, v_msg_3288_, v___y_3289_, v___y_3290_, v___y_3291_, v___y_3292_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
return v_res_3294_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object* v_mvarId_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_){
_start:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3295_, v___y_3297_);
return v___x_3301_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object* v_mvarId_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
lean_object* v_res_3308_; 
v_res_3308_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v_mvarId_3302_);
return v_res_3308_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object* v_00_u03b2_3309_, lean_object* v_x_3310_, lean_object* v_x_3311_){
_start:
{
uint8_t v___x_3312_; 
v___x_3312_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3310_, v_x_3311_);
return v___x_3312_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3313_, lean_object* v_x_3314_, lean_object* v_x_3315_){
_start:
{
uint8_t v_res_3316_; lean_object* v_r_3317_; 
v_res_3316_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(v_00_u03b2_3313_, v_x_3314_, v_x_3315_);
lean_dec(v_x_3315_);
lean_dec_ref(v_x_3314_);
v_r_3317_ = lean_box(v_res_3316_);
return v_r_3317_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_3318_, lean_object* v_x_3319_, size_t v_x_3320_, lean_object* v_x_3321_){
_start:
{
uint8_t v___x_3322_; 
v___x_3322_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3319_, v_x_3320_, v_x_3321_);
return v___x_3322_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3323_, lean_object* v_x_3324_, lean_object* v_x_3325_, lean_object* v_x_3326_){
_start:
{
size_t v_x_11002__boxed_3327_; uint8_t v_res_3328_; lean_object* v_r_3329_; 
v_x_11002__boxed_3327_ = lean_unbox_usize(v_x_3325_);
lean_dec(v_x_3325_);
v_res_3328_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3323_, v_x_3324_, v_x_11002__boxed_3327_, v_x_3326_);
lean_dec(v_x_3326_);
lean_dec_ref(v_x_3324_);
v_r_3329_ = lean_box(v_res_3328_);
return v_r_3329_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3330_, lean_object* v_keys_3331_, lean_object* v_vals_3332_, lean_object* v_heq_3333_, lean_object* v_i_3334_, lean_object* v_k_3335_){
_start:
{
uint8_t v___x_3336_; 
v___x_3336_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3331_, v_i_3334_, v_k_3335_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3337_, lean_object* v_keys_3338_, lean_object* v_vals_3339_, lean_object* v_heq_3340_, lean_object* v_i_3341_, lean_object* v_k_3342_){
_start:
{
uint8_t v_res_3343_; lean_object* v_r_3344_; 
v_res_3343_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(v_00_u03b2_3337_, v_keys_3338_, v_vals_3339_, v_heq_3340_, v_i_3341_, v_k_3342_);
lean_dec(v_k_3342_);
lean_dec_ref(v_vals_3339_);
lean_dec_ref(v_keys_3338_);
v_r_3344_ = lean_box(v_res_3343_);
return v_r_3344_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* v_x_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v___x_3351_; 
v___x_3351_ = l_Lean_Meta_saveState___redArg(v___y_3347_, v___y_3349_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3353_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v___x_3351_, 1);
lean_inc(v___y_3349_);
lean_inc_ref(v___y_3348_);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
v___x_3353_ = lean_apply_5(v_x_3345_, v___y_3346_, v___y_3347_, v___y_3348_, v___y_3349_, lean_box(0));
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3356_; uint8_t v_isShared_3357_; uint8_t v_isSharedCheck_3362_; 
lean_dec(v_a_3352_);
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3362_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3362_ == 0)
{
v___x_3356_ = v___x_3353_;
v_isShared_3357_ = v_isSharedCheck_3362_;
goto v_resetjp_3355_;
}
else
{
lean_inc(v_a_3354_);
lean_dec(v___x_3353_);
v___x_3356_ = lean_box(0);
v_isShared_3357_ = v_isSharedCheck_3362_;
goto v_resetjp_3355_;
}
v_resetjp_3355_:
{
lean_object* v___x_3358_; lean_object* v___x_3360_; 
v___x_3358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3358_, 0, v_a_3354_);
if (v_isShared_3357_ == 0)
{
lean_ctor_set(v___x_3356_, 0, v___x_3358_);
v___x_3360_ = v___x_3356_;
goto v_reusejp_3359_;
}
else
{
lean_object* v_reuseFailAlloc_3361_; 
v_reuseFailAlloc_3361_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3361_, 0, v___x_3358_);
v___x_3360_ = v_reuseFailAlloc_3361_;
goto v_reusejp_3359_;
}
v_reusejp_3359_:
{
return v___x_3360_;
}
}
}
else
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3393_; 
v_a_3363_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3393_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3393_ == 0)
{
v___x_3365_ = v___x_3353_;
v_isShared_3366_ = v_isSharedCheck_3393_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3353_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3393_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
uint8_t v___x_3367_; 
v___x_3367_ = l_Lean_Exception_isInterrupt(v_a_3363_);
if (v___x_3367_ == 0)
{
uint8_t v___x_3368_; 
lean_inc(v_a_3363_);
v___x_3368_ = l_Lean_Exception_isRuntime(v_a_3363_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; 
lean_del_object(v___x_3365_);
lean_dec(v_a_3363_);
v___x_3369_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3352_, v___y_3347_, v___y_3349_);
if (lean_obj_tag(v___x_3369_) == 0)
{
lean_object* v___x_3371_; uint8_t v_isShared_3372_; uint8_t v_isSharedCheck_3377_; 
v_isSharedCheck_3377_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3377_ == 0)
{
lean_object* v_unused_3378_; 
v_unused_3378_ = lean_ctor_get(v___x_3369_, 0);
lean_dec(v_unused_3378_);
v___x_3371_ = v___x_3369_;
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
else
{
lean_dec(v___x_3369_);
v___x_3371_ = lean_box(0);
v_isShared_3372_ = v_isSharedCheck_3377_;
goto v_resetjp_3370_;
}
v_resetjp_3370_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = lean_box(0);
if (v_isShared_3372_ == 0)
{
lean_ctor_set(v___x_3371_, 0, v___x_3373_);
v___x_3375_ = v___x_3371_;
goto v_reusejp_3374_;
}
else
{
lean_object* v_reuseFailAlloc_3376_; 
v_reuseFailAlloc_3376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3376_, 0, v___x_3373_);
v___x_3375_ = v_reuseFailAlloc_3376_;
goto v_reusejp_3374_;
}
v_reusejp_3374_:
{
return v___x_3375_;
}
}
}
else
{
lean_object* v_a_3379_; lean_object* v___x_3381_; uint8_t v_isShared_3382_; uint8_t v_isSharedCheck_3386_; 
v_a_3379_ = lean_ctor_get(v___x_3369_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3369_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3381_ = v___x_3369_;
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
else
{
lean_inc(v_a_3379_);
lean_dec(v___x_3369_);
v___x_3381_ = lean_box(0);
v_isShared_3382_ = v_isSharedCheck_3386_;
goto v_resetjp_3380_;
}
v_resetjp_3380_:
{
lean_object* v___x_3384_; 
if (v_isShared_3382_ == 0)
{
v___x_3384_ = v___x_3381_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3379_);
v___x_3384_ = v_reuseFailAlloc_3385_;
goto v_reusejp_3383_;
}
v_reusejp_3383_:
{
return v___x_3384_;
}
}
}
}
else
{
lean_object* v___x_3388_; 
lean_dec(v_a_3352_);
if (v_isShared_3366_ == 0)
{
v___x_3388_ = v___x_3365_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3389_; 
v_reuseFailAlloc_3389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3389_, 0, v_a_3363_);
v___x_3388_ = v_reuseFailAlloc_3389_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
return v___x_3388_;
}
}
}
else
{
lean_object* v___x_3391_; 
lean_dec(v_a_3352_);
if (v_isShared_3366_ == 0)
{
v___x_3391_ = v___x_3365_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v_a_3363_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
return v___x_3391_;
}
}
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_dec_ref(v_x_3345_);
v_a_3394_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3351_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3351_);
v___x_3396_ = lean_box(0);
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
v_resetjp_3395_:
{
lean_object* v___x_3399_; 
if (v_isShared_3397_ == 0)
{
v___x_3399_ = v___x_3396_;
goto v_reusejp_3398_;
}
else
{
lean_object* v_reuseFailAlloc_3400_; 
v_reuseFailAlloc_3400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3400_, 0, v_a_3394_);
v___x_3399_ = v_reuseFailAlloc_3400_;
goto v_reusejp_3398_;
}
v_reusejp_3398_:
{
return v___x_3399_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object* v_x_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3402_, v___y_3403_, v___y_3404_, v___y_3405_, v___y_3406_);
lean_dec(v___y_3406_);
lean_dec_ref(v___y_3405_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object* v_00_u03b1_3409_, lean_object* v_x_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_){
_start:
{
lean_object* v___x_3416_; 
v___x_3416_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3410_, v___y_3411_, v___y_3412_, v___y_3413_, v___y_3414_);
return v___x_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object* v_00_u03b1_3417_, lean_object* v_x_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_){
_start:
{
lean_object* v_res_3424_; 
v_res_3424_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(v_00_u03b1_3417_, v_x_3418_, v___y_3419_, v___y_3420_, v___y_3421_, v___y_3422_);
lean_dec(v___y_3422_);
lean_dec_ref(v___y_3421_);
lean_dec(v___y_3420_);
lean_dec_ref(v___y_3419_);
return v_res_3424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* v_mvarId_3425_, lean_object* v_hFVarId_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_){
_start:
{
lean_object* v___x_3432_; lean_object* v___x_3433_; 
v___x_3432_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___boxed), 7, 2);
lean_closure_set(v___x_3432_, 0, v_mvarId_3425_);
lean_closure_set(v___x_3432_, 1, v_hFVarId_3426_);
v___x_3433_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3432_, v_a_3427_, v_a_3428_, v_a_3429_, v_a_3430_);
return v___x_3433_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object* v_mvarId_3434_, lean_object* v_hFVarId_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v_res_3441_; 
v_res_3441_ = l_Lean_Meta_substVar_x3f(v_mvarId_3434_, v_hFVarId_3435_, v_a_3436_, v_a_3437_, v_a_3438_, v_a_3439_);
lean_dec(v_a_3439_);
lean_dec_ref(v_a_3438_);
lean_dec(v_a_3437_);
lean_dec_ref(v_a_3436_);
return v_res_3441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* v_mvarId_3442_, lean_object* v_hFVarId_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_){
_start:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; 
v___x_3449_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 7, 2);
lean_closure_set(v___x_3449_, 0, v_mvarId_3442_);
lean_closure_set(v___x_3449_, 1, v_hFVarId_3443_);
v___x_3450_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3449_, v_a_3444_, v_a_3445_, v_a_3446_, v_a_3447_);
return v___x_3450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object* v_mvarId_3451_, lean_object* v_hFVarId_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_){
_start:
{
lean_object* v_res_3458_; 
v_res_3458_ = l_Lean_Meta_subst_x3f(v_mvarId_3451_, v_hFVarId_3452_, v_a_3453_, v_a_3454_, v_a_3455_, v_a_3456_);
lean_dec(v_a_3456_);
lean_dec_ref(v_a_3455_);
lean_dec(v_a_3454_);
lean_dec_ref(v_a_3453_);
return v_res_3458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* v_mvarId_3459_, lean_object* v_hFVarId_3460_, uint8_t v_symm_3461_, lean_object* v_fvarSubst_3462_, uint8_t v_clearH_3463_, uint8_t v_tryToSkip_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_){
_start:
{
lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; 
v___x_3470_ = lean_box(v_symm_3461_);
v___x_3471_ = lean_box(v_clearH_3463_);
v___x_3472_ = lean_box(v_tryToSkip_3464_);
v___x_3473_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_3473_, 0, v_mvarId_3459_);
lean_closure_set(v___x_3473_, 1, v_hFVarId_3460_);
lean_closure_set(v___x_3473_, 2, v___x_3470_);
lean_closure_set(v___x_3473_, 3, v_fvarSubst_3462_);
lean_closure_set(v___x_3473_, 4, v___x_3471_);
lean_closure_set(v___x_3473_, 5, v___x_3472_);
v___x_3474_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3473_, v_a_3465_, v_a_3466_, v_a_3467_, v_a_3468_);
return v___x_3474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* v_mvarId_3475_, lean_object* v_hFVarId_3476_, lean_object* v_symm_3477_, lean_object* v_fvarSubst_3478_, lean_object* v_clearH_3479_, lean_object* v_tryToSkip_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_){
_start:
{
uint8_t v_symm_boxed_3486_; uint8_t v_clearH_boxed_3487_; uint8_t v_tryToSkip_boxed_3488_; lean_object* v_res_3489_; 
v_symm_boxed_3486_ = lean_unbox(v_symm_3477_);
v_clearH_boxed_3487_ = lean_unbox(v_clearH_3479_);
v_tryToSkip_boxed_3488_ = lean_unbox(v_tryToSkip_3480_);
v_res_3489_ = l_Lean_Meta_substCore_x3f(v_mvarId_3475_, v_hFVarId_3476_, v_symm_boxed_3486_, v_fvarSubst_3478_, v_clearH_boxed_3487_, v_tryToSkip_boxed_3488_, v_a_3481_, v_a_3482_, v_a_3483_, v_a_3484_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
lean_dec(v_a_3482_);
lean_dec_ref(v_a_3481_);
return v_res_3489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* v_mvarId_3490_, lean_object* v_hFVarId_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_){
_start:
{
lean_object* v___x_3497_; 
lean_inc(v_mvarId_3490_);
v___x_3497_ = l_Lean_Meta_substVar_x3f(v_mvarId_3490_, v_hFVarId_3491_, v_a_3492_, v_a_3493_, v_a_3494_, v_a_3495_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3509_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3509_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3509_ == 0)
{
v___x_3500_ = v___x_3497_;
v_isShared_3501_ = v_isSharedCheck_3509_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3497_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3509_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
if (lean_obj_tag(v_a_3498_) == 0)
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v_mvarId_3490_);
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_mvarId_3490_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
else
{
lean_object* v_val_3505_; lean_object* v___x_3507_; 
lean_dec(v_mvarId_3490_);
v_val_3505_ = lean_ctor_get(v_a_3498_, 0);
lean_inc(v_val_3505_);
lean_dec_ref_known(v_a_3498_, 1);
if (v_isShared_3501_ == 0)
{
lean_ctor_set(v___x_3500_, 0, v_val_3505_);
v___x_3507_ = v___x_3500_;
goto v_reusejp_3506_;
}
else
{
lean_object* v_reuseFailAlloc_3508_; 
v_reuseFailAlloc_3508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_val_3505_);
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
lean_dec(v_mvarId_3490_);
v_a_3510_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3517_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3517_ == 0)
{
v___x_3512_ = v___x_3497_;
v_isShared_3513_ = v_isSharedCheck_3517_;
goto v_resetjp_3511_;
}
else
{
lean_inc(v_a_3510_);
lean_dec(v___x_3497_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object* v_mvarId_3518_, lean_object* v_hFVarId_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v_res_3525_; 
v_res_3525_ = l_Lean_Meta_trySubstVar(v_mvarId_3518_, v_hFVarId_3519_, v_a_3520_, v_a_3521_, v_a_3522_, v_a_3523_);
lean_dec(v_a_3523_);
lean_dec_ref(v_a_3522_);
lean_dec(v_a_3521_);
lean_dec_ref(v_a_3520_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* v_mvarId_3526_, lean_object* v_hFVarId_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v___x_3533_; 
lean_inc(v_mvarId_3526_);
v___x_3533_ = l_Lean_Meta_subst_x3f(v_mvarId_3526_, v_hFVarId_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
if (lean_obj_tag(v___x_3533_) == 0)
{
lean_object* v_a_3534_; lean_object* v___x_3536_; uint8_t v_isShared_3537_; uint8_t v_isSharedCheck_3545_; 
v_a_3534_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3536_ = v___x_3533_;
v_isShared_3537_ = v_isSharedCheck_3545_;
goto v_resetjp_3535_;
}
else
{
lean_inc(v_a_3534_);
lean_dec(v___x_3533_);
v___x_3536_ = lean_box(0);
v_isShared_3537_ = v_isSharedCheck_3545_;
goto v_resetjp_3535_;
}
v_resetjp_3535_:
{
if (lean_obj_tag(v_a_3534_) == 0)
{
lean_object* v___x_3539_; 
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v_mvarId_3526_);
v___x_3539_ = v___x_3536_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3540_; 
v_reuseFailAlloc_3540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_mvarId_3526_);
v___x_3539_ = v_reuseFailAlloc_3540_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
return v___x_3539_;
}
}
else
{
lean_object* v_val_3541_; lean_object* v___x_3543_; 
lean_dec(v_mvarId_3526_);
v_val_3541_ = lean_ctor_get(v_a_3534_, 0);
lean_inc(v_val_3541_);
lean_dec_ref_known(v_a_3534_, 1);
if (v_isShared_3537_ == 0)
{
lean_ctor_set(v___x_3536_, 0, v_val_3541_);
v___x_3543_ = v___x_3536_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_val_3541_);
v___x_3543_ = v_reuseFailAlloc_3544_;
goto v_reusejp_3542_;
}
v_reusejp_3542_:
{
return v___x_3543_;
}
}
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec(v_mvarId_3526_);
v_a_3546_ = lean_ctor_get(v___x_3533_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3533_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3533_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3533_);
v___x_3548_ = lean_box(0);
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
v_resetjp_3547_:
{
lean_object* v___x_3551_; 
if (v_isShared_3549_ == 0)
{
v___x_3551_ = v___x_3548_;
goto v_reusejp_3550_;
}
else
{
lean_object* v_reuseFailAlloc_3552_; 
v_reuseFailAlloc_3552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3552_, 0, v_a_3546_);
v___x_3551_ = v_reuseFailAlloc_3552_;
goto v_reusejp_3550_;
}
v_reusejp_3550_:
{
return v___x_3551_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object* v_mvarId_3554_, lean_object* v_hFVarId_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_Meta_trySubst(v_mvarId_3554_, v_hFVarId_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_mvarId_3565_, lean_object* v_as_3566_, size_t v_sz_3567_, size_t v_i_3568_, lean_object* v_b_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_){
_start:
{
uint8_t v___x_3575_; 
v___x_3575_ = lean_usize_dec_lt(v_i_3568_, v_sz_3567_);
if (v___x_3575_ == 0)
{
lean_object* v___x_3576_; 
lean_dec(v_mvarId_3565_);
v___x_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3576_, 0, v_b_3569_);
return v___x_3576_;
}
else
{
lean_object* v_snd_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3630_; 
v_snd_3577_ = lean_ctor_get(v_b_3569_, 1);
v_isSharedCheck_3630_ = !lean_is_exclusive(v_b_3569_);
if (v_isSharedCheck_3630_ == 0)
{
lean_object* v_unused_3631_; 
v_unused_3631_ = lean_ctor_get(v_b_3569_, 0);
lean_dec(v_unused_3631_);
v___x_3579_ = v_b_3569_;
v_isShared_3580_ = v_isSharedCheck_3630_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_snd_3577_);
lean_dec(v_b_3569_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3630_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3581_; lean_object* v_a_3583_; lean_object* v_a_3590_; 
v___x_3581_ = lean_box(0);
v_a_3590_ = lean_array_uget(v_as_3566_, v_i_3568_);
if (lean_obj_tag(v_a_3590_) == 0)
{
v_a_3583_ = v_snd_3577_;
goto v___jp_3582_;
}
else
{
lean_object* v_val_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3629_; 
v_val_3591_ = lean_ctor_get(v_a_3590_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_a_3590_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3593_ = v_a_3590_;
v_isShared_3594_ = v_isSharedCheck_3629_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_val_3591_);
lean_dec(v_a_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3629_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3595_ = lean_box(0);
v___x_3596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3597_ = l_Lean_LocalDecl_fvarId(v_val_3591_);
lean_dec(v_val_3591_);
lean_inc(v_mvarId_3565_);
v___x_3598_ = l_Lean_Meta_subst_x3f(v_mvarId_3565_, v___x_3597_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
if (lean_obj_tag(v___x_3598_) == 0)
{
lean_object* v_a_3599_; lean_object* v___x_3601_; uint8_t v_isShared_3602_; uint8_t v_isSharedCheck_3620_; 
v_a_3599_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3620_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3620_ == 0)
{
v___x_3601_ = v___x_3598_;
v_isShared_3602_ = v_isSharedCheck_3620_;
goto v_resetjp_3600_;
}
else
{
lean_inc(v_a_3599_);
lean_dec(v___x_3598_);
v___x_3601_ = lean_box(0);
v_isShared_3602_ = v_isSharedCheck_3620_;
goto v_resetjp_3600_;
}
v_resetjp_3600_:
{
if (lean_obj_tag(v_a_3599_) == 1)
{
lean_object* v___x_3604_; 
lean_del_object(v___x_3579_);
lean_dec(v_mvarId_3565_);
lean_inc_ref(v_a_3599_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v_a_3599_);
v___x_3604_ = v___x_3593_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3599_);
v___x_3604_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3617_; 
v_isSharedCheck_3617_ = !lean_is_exclusive(v_a_3599_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; 
v_unused_3618_ = lean_ctor_get(v_a_3599_, 0);
lean_dec(v_unused_3618_);
v___x_3606_ = v_a_3599_;
v_isShared_3607_ = v_isSharedCheck_3617_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v_a_3599_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3617_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3604_);
lean_ctor_set(v___x_3608_, 1, v___x_3595_);
if (v_isShared_3607_ == 0)
{
lean_ctor_set_tag(v___x_3606_, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3608_);
v___x_3610_ = v___x_3606_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3614_; 
v___x_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
v___x_3612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3611_);
lean_ctor_set(v___x_3612_, 1, v_snd_3577_);
if (v_isShared_3602_ == 0)
{
lean_ctor_set(v___x_3601_, 0, v___x_3612_);
v___x_3614_ = v___x_3601_;
goto v_reusejp_3613_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3612_);
v___x_3614_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3613_;
}
v_reusejp_3613_:
{
return v___x_3614_;
}
}
}
}
}
else
{
lean_del_object(v___x_3601_);
lean_dec(v_a_3599_);
lean_del_object(v___x_3593_);
lean_dec(v_snd_3577_);
v_a_3583_ = v___x_3596_;
goto v___jp_3582_;
}
}
}
else
{
lean_object* v_a_3621_; lean_object* v___x_3623_; uint8_t v_isShared_3624_; uint8_t v_isSharedCheck_3628_; 
lean_del_object(v___x_3593_);
lean_del_object(v___x_3579_);
lean_dec(v_snd_3577_);
lean_dec(v_mvarId_3565_);
v_a_3621_ = lean_ctor_get(v___x_3598_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v___x_3598_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3623_ = v___x_3598_;
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
else
{
lean_inc(v_a_3621_);
lean_dec(v___x_3598_);
v___x_3623_ = lean_box(0);
v_isShared_3624_ = v_isSharedCheck_3628_;
goto v_resetjp_3622_;
}
v_resetjp_3622_:
{
lean_object* v___x_3626_; 
if (v_isShared_3624_ == 0)
{
v___x_3626_ = v___x_3623_;
goto v_reusejp_3625_;
}
else
{
lean_object* v_reuseFailAlloc_3627_; 
v_reuseFailAlloc_3627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3627_, 0, v_a_3621_);
v___x_3626_ = v_reuseFailAlloc_3627_;
goto v_reusejp_3625_;
}
v_reusejp_3625_:
{
return v___x_3626_;
}
}
}
}
}
v___jp_3582_:
{
lean_object* v___x_3585_; 
if (v_isShared_3580_ == 0)
{
lean_ctor_set(v___x_3579_, 1, v_a_3583_);
lean_ctor_set(v___x_3579_, 0, v___x_3581_);
v___x_3585_ = v___x_3579_;
goto v_reusejp_3584_;
}
else
{
lean_object* v_reuseFailAlloc_3589_; 
v_reuseFailAlloc_3589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3589_, 0, v___x_3581_);
lean_ctor_set(v_reuseFailAlloc_3589_, 1, v_a_3583_);
v___x_3585_ = v_reuseFailAlloc_3589_;
goto v_reusejp_3584_;
}
v_reusejp_3584_:
{
size_t v___x_3586_; size_t v___x_3587_; 
v___x_3586_ = ((size_t)1ULL);
v___x_3587_ = lean_usize_add(v_i_3568_, v___x_3586_);
v_i_3568_ = v___x_3587_;
v_b_3569_ = v___x_3585_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_mvarId_3632_, lean_object* v_as_3633_, lean_object* v_sz_3634_, lean_object* v_i_3635_, lean_object* v_b_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_){
_start:
{
size_t v_sz_boxed_3642_; size_t v_i_boxed_3643_; lean_object* v_res_3644_; 
v_sz_boxed_3642_ = lean_unbox_usize(v_sz_3634_);
lean_dec(v_sz_3634_);
v_i_boxed_3643_ = lean_unbox_usize(v_i_3635_);
lean_dec(v_i_3635_);
v_res_3644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3632_, v_as_3633_, v_sz_boxed_3642_, v_i_boxed_3643_, v_b_3636_, v___y_3637_, v___y_3638_, v___y_3639_, v___y_3640_);
lean_dec(v___y_3640_);
lean_dec_ref(v___y_3639_);
lean_dec(v___y_3638_);
lean_dec_ref(v___y_3637_);
lean_dec_ref(v_as_3633_);
return v_res_3644_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object* v_mvarId_3645_, lean_object* v_as_3646_, size_t v_sz_3647_, size_t v_i_3648_, lean_object* v_b_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_){
_start:
{
uint8_t v___x_3655_; 
v___x_3655_ = lean_usize_dec_lt(v_i_3648_, v_sz_3647_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; 
lean_dec(v_mvarId_3645_);
v___x_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3656_, 0, v_b_3649_);
return v___x_3656_;
}
else
{
lean_object* v_snd_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3710_; 
v_snd_3657_ = lean_ctor_get(v_b_3649_, 1);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_b_3649_);
if (v_isSharedCheck_3710_ == 0)
{
lean_object* v_unused_3711_; 
v_unused_3711_ = lean_ctor_get(v_b_3649_, 0);
lean_dec(v_unused_3711_);
v___x_3659_ = v_b_3649_;
v_isShared_3660_ = v_isSharedCheck_3710_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_snd_3657_);
lean_dec(v_b_3649_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3710_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; lean_object* v_a_3663_; lean_object* v_a_3670_; 
v___x_3661_ = lean_box(0);
v_a_3670_ = lean_array_uget(v_as_3646_, v_i_3648_);
if (lean_obj_tag(v_a_3670_) == 0)
{
v_a_3663_ = v_snd_3657_;
goto v___jp_3662_;
}
else
{
lean_object* v_val_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3709_; 
v_val_3671_ = lean_ctor_get(v_a_3670_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_a_3670_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3673_ = v_a_3670_;
v_isShared_3674_ = v_isSharedCheck_3709_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_val_3671_);
lean_dec(v_a_3670_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3709_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; 
v___x_3675_ = lean_box(0);
v___x_3676_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3677_ = l_Lean_LocalDecl_fvarId(v_val_3671_);
lean_dec(v_val_3671_);
lean_inc(v_mvarId_3645_);
v___x_3678_ = l_Lean_Meta_subst_x3f(v_mvarId_3645_, v___x_3677_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3700_; 
v_a_3679_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3700_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3700_ == 0)
{
v___x_3681_ = v___x_3678_;
v_isShared_3682_ = v_isSharedCheck_3700_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3678_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3700_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
if (lean_obj_tag(v_a_3679_) == 1)
{
lean_object* v___x_3684_; 
lean_del_object(v___x_3659_);
lean_dec(v_mvarId_3645_);
lean_inc_ref(v_a_3679_);
if (v_isShared_3674_ == 0)
{
lean_ctor_set(v___x_3673_, 0, v_a_3679_);
v___x_3684_ = v___x_3673_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3697_; 
v_isSharedCheck_3697_ = !lean_is_exclusive(v_a_3679_);
if (v_isSharedCheck_3697_ == 0)
{
lean_object* v_unused_3698_; 
v_unused_3698_ = lean_ctor_get(v_a_3679_, 0);
lean_dec(v_unused_3698_);
v___x_3686_ = v_a_3679_;
v_isShared_3687_ = v_isSharedCheck_3697_;
goto v_resetjp_3685_;
}
else
{
lean_dec(v_a_3679_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3697_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3684_);
lean_ctor_set(v___x_3688_, 1, v___x_3675_);
if (v_isShared_3687_ == 0)
{
lean_ctor_set_tag(v___x_3686_, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3688_);
v___x_3690_ = v___x_3686_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3696_; 
v_reuseFailAlloc_3696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3696_, 0, v___x_3688_);
v___x_3690_ = v_reuseFailAlloc_3696_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; lean_object* v___x_3692_; lean_object* v___x_3694_; 
v___x_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
v___x_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
lean_ctor_set(v___x_3692_, 1, v_snd_3657_);
if (v_isShared_3682_ == 0)
{
lean_ctor_set(v___x_3681_, 0, v___x_3692_);
v___x_3694_ = v___x_3681_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3692_);
v___x_3694_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3693_;
}
v_reusejp_3693_:
{
return v___x_3694_;
}
}
}
}
}
else
{
lean_del_object(v___x_3681_);
lean_dec(v_a_3679_);
lean_del_object(v___x_3673_);
lean_dec(v_snd_3657_);
v_a_3663_ = v___x_3676_;
goto v___jp_3662_;
}
}
}
else
{
lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3708_; 
lean_del_object(v___x_3673_);
lean_del_object(v___x_3659_);
lean_dec(v_snd_3657_);
lean_dec(v_mvarId_3645_);
v_a_3701_ = lean_ctor_get(v___x_3678_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v___x_3678_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3703_ = v___x_3678_;
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_dec(v___x_3678_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3708_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3706_; 
if (v_isShared_3704_ == 0)
{
v___x_3706_ = v___x_3703_;
goto v_reusejp_3705_;
}
else
{
lean_object* v_reuseFailAlloc_3707_; 
v_reuseFailAlloc_3707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3707_, 0, v_a_3701_);
v___x_3706_ = v_reuseFailAlloc_3707_;
goto v_reusejp_3705_;
}
v_reusejp_3705_:
{
return v___x_3706_;
}
}
}
}
}
v___jp_3662_:
{
lean_object* v___x_3665_; 
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 1, v_a_3663_);
lean_ctor_set(v___x_3659_, 0, v___x_3661_);
v___x_3665_ = v___x_3659_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3661_);
lean_ctor_set(v_reuseFailAlloc_3669_, 1, v_a_3663_);
v___x_3665_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
size_t v___x_3666_; size_t v___x_3667_; lean_object* v___x_3668_; 
v___x_3666_ = ((size_t)1ULL);
v___x_3667_ = lean_usize_add(v_i_3648_, v___x_3666_);
v___x_3668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3645_, v_as_3646_, v_sz_3647_, v___x_3667_, v___x_3665_, v___y_3650_, v___y_3651_, v___y_3652_, v___y_3653_);
return v___x_3668_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_3712_, lean_object* v_as_3713_, lean_object* v_sz_3714_, lean_object* v_i_3715_, lean_object* v_b_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_){
_start:
{
size_t v_sz_boxed_3722_; size_t v_i_boxed_3723_; lean_object* v_res_3724_; 
v_sz_boxed_3722_ = lean_unbox_usize(v_sz_3714_);
lean_dec(v_sz_3714_);
v_i_boxed_3723_ = lean_unbox_usize(v_i_3715_);
lean_dec(v_i_3715_);
v_res_3724_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3712_, v_as_3713_, v_sz_boxed_3722_, v_i_boxed_3723_, v_b_3716_, v___y_3717_, v___y_3718_, v___y_3719_, v___y_3720_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec(v___y_3718_);
lean_dec_ref(v___y_3717_);
lean_dec_ref(v_as_3713_);
return v_res_3724_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* v_init_3725_, lean_object* v_mvarId_3726_, lean_object* v_n_3727_, lean_object* v_b_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
if (lean_obj_tag(v_n_3727_) == 0)
{
lean_object* v_cs_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; size_t v_sz_3737_; size_t v___x_3738_; lean_object* v___x_3739_; 
v_cs_3734_ = lean_ctor_get(v_n_3727_, 0);
v___x_3735_ = lean_box(0);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3735_);
lean_ctor_set(v___x_3736_, 1, v_b_3728_);
v_sz_3737_ = lean_array_size(v_cs_3734_);
v___x_3738_ = ((size_t)0ULL);
v___x_3739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3725_, v_mvarId_3726_, v_cs_3734_, v_sz_3737_, v___x_3738_, v___x_3736_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3754_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3754_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3754_ == 0)
{
v___x_3742_ = v___x_3739_;
v_isShared_3743_ = v_isSharedCheck_3754_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_a_3740_);
lean_dec(v___x_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3754_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v_fst_3744_; 
v_fst_3744_ = lean_ctor_get(v_a_3740_, 0);
if (lean_obj_tag(v_fst_3744_) == 0)
{
lean_object* v_snd_3745_; lean_object* v___x_3746_; lean_object* v___x_3748_; 
v_snd_3745_ = lean_ctor_get(v_a_3740_, 1);
lean_inc(v_snd_3745_);
lean_dec(v_a_3740_);
v___x_3746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3746_, 0, v_snd_3745_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v___x_3746_);
v___x_3748_ = v___x_3742_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v___x_3746_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
else
{
lean_object* v_val_3750_; lean_object* v___x_3752_; 
lean_inc_ref(v_fst_3744_);
lean_dec(v_a_3740_);
v_val_3750_ = lean_ctor_get(v_fst_3744_, 0);
lean_inc(v_val_3750_);
lean_dec_ref_known(v_fst_3744_, 1);
if (v_isShared_3743_ == 0)
{
lean_ctor_set(v___x_3742_, 0, v_val_3750_);
v___x_3752_ = v___x_3742_;
goto v_reusejp_3751_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_val_3750_);
v___x_3752_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3751_;
}
v_reusejp_3751_:
{
return v___x_3752_;
}
}
}
}
else
{
lean_object* v_a_3755_; lean_object* v___x_3757_; uint8_t v_isShared_3758_; uint8_t v_isSharedCheck_3762_; 
v_a_3755_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3762_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3762_ == 0)
{
v___x_3757_ = v___x_3739_;
v_isShared_3758_ = v_isSharedCheck_3762_;
goto v_resetjp_3756_;
}
else
{
lean_inc(v_a_3755_);
lean_dec(v___x_3739_);
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
lean_object* v_vs_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; size_t v_sz_3766_; size_t v___x_3767_; lean_object* v___x_3768_; 
v_vs_3763_ = lean_ctor_get(v_n_3727_, 0);
v___x_3764_ = lean_box(0);
v___x_3765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3764_);
lean_ctor_set(v___x_3765_, 1, v_b_3728_);
v_sz_3766_ = lean_array_size(v_vs_3763_);
v___x_3767_ = ((size_t)0ULL);
v___x_3768_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3726_, v_vs_3763_, v_sz_3766_, v___x_3767_, v___x_3765_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3768_) == 0)
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3783_; 
v_a_3769_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3771_ = v___x_3768_;
v_isShared_3772_ = v_isSharedCheck_3783_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3768_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3783_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v_fst_3773_; 
v_fst_3773_ = lean_ctor_get(v_a_3769_, 0);
if (lean_obj_tag(v_fst_3773_) == 0)
{
lean_object* v_snd_3774_; lean_object* v___x_3775_; lean_object* v___x_3777_; 
v_snd_3774_ = lean_ctor_get(v_a_3769_, 1);
lean_inc(v_snd_3774_);
lean_dec(v_a_3769_);
v___x_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3775_, 0, v_snd_3774_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 0, v___x_3775_);
v___x_3777_ = v___x_3771_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v___x_3775_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
else
{
lean_object* v_val_3779_; lean_object* v___x_3781_; 
lean_inc_ref(v_fst_3773_);
lean_dec(v_a_3769_);
v_val_3779_ = lean_ctor_get(v_fst_3773_, 0);
lean_inc(v_val_3779_);
lean_dec_ref_known(v_fst_3773_, 1);
if (v_isShared_3772_ == 0)
{
lean_ctor_set(v___x_3771_, 0, v_val_3779_);
v___x_3781_ = v___x_3771_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_val_3779_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
else
{
lean_object* v_a_3784_; lean_object* v___x_3786_; uint8_t v_isShared_3787_; uint8_t v_isSharedCheck_3791_; 
v_a_3784_ = lean_ctor_get(v___x_3768_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v___x_3768_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3786_ = v___x_3768_;
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
else
{
lean_inc(v_a_3784_);
lean_dec(v___x_3768_);
v___x_3786_ = lean_box(0);
v_isShared_3787_ = v_isSharedCheck_3791_;
goto v_resetjp_3785_;
}
v_resetjp_3785_:
{
lean_object* v___x_3789_; 
if (v_isShared_3787_ == 0)
{
v___x_3789_ = v___x_3786_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v_a_3784_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_init_3792_, lean_object* v_mvarId_3793_, lean_object* v_as_3794_, size_t v_sz_3795_, size_t v_i_3796_, lean_object* v_b_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
uint8_t v___x_3803_; 
v___x_3803_ = lean_usize_dec_lt(v_i_3796_, v_sz_3795_);
if (v___x_3803_ == 0)
{
lean_object* v___x_3804_; 
lean_dec(v_mvarId_3793_);
v___x_3804_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3804_, 0, v_b_3797_);
return v___x_3804_;
}
else
{
lean_object* v_snd_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3839_; 
v_snd_3805_ = lean_ctor_get(v_b_3797_, 1);
v_isSharedCheck_3839_ = !lean_is_exclusive(v_b_3797_);
if (v_isSharedCheck_3839_ == 0)
{
lean_object* v_unused_3840_; 
v_unused_3840_ = lean_ctor_get(v_b_3797_, 0);
lean_dec(v_unused_3840_);
v___x_3807_ = v_b_3797_;
v_isShared_3808_ = v_isSharedCheck_3839_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_snd_3805_);
lean_dec(v_b_3797_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3839_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v___x_3809_; lean_object* v_a_3810_; lean_object* v___x_3811_; 
v___x_3809_ = lean_box(0);
v_a_3810_ = lean_array_uget_borrowed(v_as_3794_, v_i_3796_);
lean_inc(v_snd_3805_);
lean_inc(v_mvarId_3793_);
v___x_3811_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3792_, v_mvarId_3793_, v_a_3810_, v_snd_3805_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3830_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3814_ = v___x_3811_;
v_isShared_3815_ = v_isSharedCheck_3830_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3811_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3830_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
if (lean_obj_tag(v_a_3812_) == 0)
{
lean_object* v___x_3816_; lean_object* v___x_3818_; 
lean_dec(v_mvarId_3793_);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v_a_3812_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3816_);
v___x_3818_ = v___x_3807_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_snd_3805_);
v___x_3818_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
lean_object* v___x_3820_; 
if (v_isShared_3815_ == 0)
{
lean_ctor_set(v___x_3814_, 0, v___x_3818_);
v___x_3820_ = v___x_3814_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3818_);
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
lean_object* v_a_3823_; lean_object* v___x_3825_; 
lean_del_object(v___x_3814_);
lean_dec(v_snd_3805_);
v_a_3823_ = lean_ctor_get(v_a_3812_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v_a_3812_, 1);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 1, v_a_3823_);
lean_ctor_set(v___x_3807_, 0, v___x_3809_);
v___x_3825_ = v___x_3807_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v___x_3809_);
lean_ctor_set(v_reuseFailAlloc_3829_, 1, v_a_3823_);
v___x_3825_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
size_t v___x_3826_; size_t v___x_3827_; 
v___x_3826_ = ((size_t)1ULL);
v___x_3827_ = lean_usize_add(v_i_3796_, v___x_3826_);
v_i_3796_ = v___x_3827_;
v_b_3797_ = v___x_3825_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3831_; lean_object* v___x_3833_; uint8_t v_isShared_3834_; uint8_t v_isSharedCheck_3838_; 
lean_del_object(v___x_3807_);
lean_dec(v_snd_3805_);
lean_dec(v_mvarId_3793_);
v_a_3831_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3838_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3838_ == 0)
{
v___x_3833_ = v___x_3811_;
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
else
{
lean_inc(v_a_3831_);
lean_dec(v___x_3811_);
v___x_3833_ = lean_box(0);
v_isShared_3834_ = v_isSharedCheck_3838_;
goto v_resetjp_3832_;
}
v_resetjp_3832_:
{
lean_object* v___x_3836_; 
if (v_isShared_3834_ == 0)
{
v___x_3836_ = v___x_3833_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3837_; 
v_reuseFailAlloc_3837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3837_, 0, v_a_3831_);
v___x_3836_ = v_reuseFailAlloc_3837_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
return v___x_3836_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3841_, lean_object* v_mvarId_3842_, lean_object* v_as_3843_, lean_object* v_sz_3844_, lean_object* v_i_3845_, lean_object* v_b_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_){
_start:
{
size_t v_sz_boxed_3852_; size_t v_i_boxed_3853_; lean_object* v_res_3854_; 
v_sz_boxed_3852_ = lean_unbox_usize(v_sz_3844_);
lean_dec(v_sz_3844_);
v_i_boxed_3853_ = lean_unbox_usize(v_i_3845_);
lean_dec(v_i_3845_);
v_res_3854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3841_, v_mvarId_3842_, v_as_3843_, v_sz_boxed_3852_, v_i_boxed_3853_, v_b_3846_, v___y_3847_, v___y_3848_, v___y_3849_, v___y_3850_);
lean_dec(v___y_3850_);
lean_dec_ref(v___y_3849_);
lean_dec(v___y_3848_);
lean_dec_ref(v___y_3847_);
lean_dec_ref(v_as_3843_);
lean_dec_ref(v_init_3841_);
return v_res_3854_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_init_3855_, lean_object* v_mvarId_3856_, lean_object* v_n_3857_, lean_object* v_b_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3855_, v_mvarId_3856_, v_n_3857_, v_b_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec(v___y_3860_);
lean_dec_ref(v___y_3859_);
lean_dec_ref(v_n_3857_);
lean_dec_ref(v_init_3855_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3868_, lean_object* v_as_3869_, size_t v_sz_3870_, size_t v_i_3871_, lean_object* v_b_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_){
_start:
{
uint8_t v___x_3878_; 
v___x_3878_ = lean_usize_dec_lt(v_i_3871_, v_sz_3870_);
if (v___x_3878_ == 0)
{
lean_object* v___x_3879_; 
lean_dec(v_mvarId_3868_);
v___x_3879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3879_, 0, v_b_3872_);
return v___x_3879_;
}
else
{
lean_object* v_snd_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3932_; 
v_snd_3880_ = lean_ctor_get(v_b_3872_, 1);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_b_3872_);
if (v_isSharedCheck_3932_ == 0)
{
lean_object* v_unused_3933_; 
v_unused_3933_ = lean_ctor_get(v_b_3872_, 0);
lean_dec(v_unused_3933_);
v___x_3882_ = v_b_3872_;
v_isShared_3883_ = v_isSharedCheck_3932_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_snd_3880_);
lean_dec(v_b_3872_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3932_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; lean_object* v_a_3886_; lean_object* v_a_3893_; 
v___x_3884_ = lean_box(0);
v_a_3893_ = lean_array_uget(v_as_3869_, v_i_3871_);
if (lean_obj_tag(v_a_3893_) == 0)
{
v_a_3886_ = v_snd_3880_;
goto v___jp_3885_;
}
else
{
lean_object* v_val_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3931_; 
v_val_3894_ = lean_ctor_get(v_a_3893_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_a_3893_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3896_ = v_a_3893_;
v_isShared_3897_ = v_isSharedCheck_3931_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_val_3894_);
lean_dec(v_a_3893_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3931_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3898_ = lean_box(0);
v___x_3899_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v___x_3900_ = l_Lean_LocalDecl_fvarId(v_val_3894_);
lean_dec(v_val_3894_);
lean_inc(v_mvarId_3868_);
v___x_3901_ = l_Lean_Meta_subst_x3f(v_mvarId_3868_, v___x_3900_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; lean_object* v___x_3904_; uint8_t v_isShared_3905_; uint8_t v_isSharedCheck_3922_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3922_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3922_ == 0)
{
v___x_3904_ = v___x_3901_;
v_isShared_3905_ = v_isSharedCheck_3922_;
goto v_resetjp_3903_;
}
else
{
lean_inc(v_a_3902_);
lean_dec(v___x_3901_);
v___x_3904_ = lean_box(0);
v_isShared_3905_ = v_isSharedCheck_3922_;
goto v_resetjp_3903_;
}
v_resetjp_3903_:
{
if (lean_obj_tag(v_a_3902_) == 1)
{
lean_object* v___x_3907_; 
lean_del_object(v___x_3882_);
lean_dec(v_mvarId_3868_);
lean_inc_ref(v_a_3902_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v_a_3902_);
v___x_3907_ = v___x_3896_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3902_);
v___x_3907_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3919_; 
v_isSharedCheck_3919_ = !lean_is_exclusive(v_a_3902_);
if (v_isSharedCheck_3919_ == 0)
{
lean_object* v_unused_3920_; 
v_unused_3920_ = lean_ctor_get(v_a_3902_, 0);
lean_dec(v_unused_3920_);
v___x_3909_ = v_a_3902_;
v_isShared_3910_ = v_isSharedCheck_3919_;
goto v_resetjp_3908_;
}
else
{
lean_dec(v_a_3902_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3919_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3907_);
lean_ctor_set(v___x_3911_, 1, v___x_3898_);
if (v_isShared_3910_ == 0)
{
lean_ctor_set(v___x_3909_, 0, v___x_3911_);
v___x_3913_ = v___x_3909_;
goto v_reusejp_3912_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v___x_3911_);
v___x_3913_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3912_;
}
v_reusejp_3912_:
{
lean_object* v___x_3914_; lean_object* v___x_3916_; 
v___x_3914_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
lean_ctor_set(v___x_3914_, 1, v_snd_3880_);
if (v_isShared_3905_ == 0)
{
lean_ctor_set(v___x_3904_, 0, v___x_3914_);
v___x_3916_ = v___x_3904_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3914_);
v___x_3916_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
return v___x_3916_;
}
}
}
}
}
else
{
lean_del_object(v___x_3904_);
lean_dec(v_a_3902_);
lean_del_object(v___x_3896_);
lean_dec(v_snd_3880_);
v_a_3886_ = v___x_3899_;
goto v___jp_3885_;
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_del_object(v___x_3896_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_mvarId_3868_);
v_a_3923_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3901_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3901_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
}
v___jp_3885_:
{
lean_object* v___x_3888_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v_a_3886_);
lean_ctor_set(v___x_3882_, 0, v___x_3884_);
v___x_3888_ = v___x_3882_;
goto v_reusejp_3887_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v___x_3884_);
lean_ctor_set(v_reuseFailAlloc_3892_, 1, v_a_3886_);
v___x_3888_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3887_;
}
v_reusejp_3887_:
{
size_t v___x_3889_; size_t v___x_3890_; 
v___x_3889_ = ((size_t)1ULL);
v___x_3890_ = lean_usize_add(v_i_3871_, v___x_3889_);
v_i_3871_ = v___x_3890_;
v_b_3872_ = v___x_3888_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3934_, lean_object* v_as_3935_, lean_object* v_sz_3936_, lean_object* v_i_3937_, lean_object* v_b_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_){
_start:
{
size_t v_sz_boxed_3944_; size_t v_i_boxed_3945_; lean_object* v_res_3946_; 
v_sz_boxed_3944_ = lean_unbox_usize(v_sz_3936_);
lean_dec(v_sz_3936_);
v_i_boxed_3945_ = lean_unbox_usize(v_i_3937_);
lean_dec(v_i_3937_);
v_res_3946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3934_, v_as_3935_, v_sz_boxed_3944_, v_i_boxed_3945_, v_b_3938_, v___y_3939_, v___y_3940_, v___y_3941_, v___y_3942_);
lean_dec(v___y_3942_);
lean_dec_ref(v___y_3941_);
lean_dec(v___y_3940_);
lean_dec_ref(v___y_3939_);
lean_dec_ref(v_as_3935_);
return v_res_3946_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_3947_, lean_object* v_as_3948_, size_t v_sz_3949_, size_t v_i_3950_, lean_object* v_b_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_){
_start:
{
uint8_t v___x_3957_; 
v___x_3957_ = lean_usize_dec_lt(v_i_3950_, v_sz_3949_);
if (v___x_3957_ == 0)
{
lean_object* v___x_3958_; 
lean_dec(v_mvarId_3947_);
v___x_3958_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3958_, 0, v_b_3951_);
return v___x_3958_;
}
else
{
lean_object* v_snd_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_4011_; 
v_snd_3959_ = lean_ctor_get(v_b_3951_, 1);
v_isSharedCheck_4011_ = !lean_is_exclusive(v_b_3951_);
if (v_isSharedCheck_4011_ == 0)
{
lean_object* v_unused_4012_; 
v_unused_4012_ = lean_ctor_get(v_b_3951_, 0);
lean_dec(v_unused_4012_);
v___x_3961_ = v_b_3951_;
v_isShared_3962_ = v_isSharedCheck_4011_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_snd_3959_);
lean_dec(v_b_3951_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_4011_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3963_; lean_object* v_a_3965_; lean_object* v_a_3972_; 
v___x_3963_ = lean_box(0);
v_a_3972_ = lean_array_uget(v_as_3948_, v_i_3950_);
if (lean_obj_tag(v_a_3972_) == 0)
{
v_a_3965_ = v_snd_3959_;
goto v___jp_3964_;
}
else
{
lean_object* v_val_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_4010_; 
v_val_3973_ = lean_ctor_get(v_a_3972_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_a_3972_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_3975_ = v_a_3972_;
v_isShared_3976_ = v_isSharedCheck_4010_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_val_3973_);
lean_dec(v_a_3972_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_4010_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; lean_object* v___x_3980_; 
v___x_3977_ = lean_box(0);
v___x_3978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v___x_3979_ = l_Lean_LocalDecl_fvarId(v_val_3973_);
lean_dec(v_val_3973_);
lean_inc(v_mvarId_3947_);
v___x_3980_ = l_Lean_Meta_subst_x3f(v_mvarId_3947_, v___x_3979_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
if (lean_obj_tag(v___x_3980_) == 0)
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_4001_; 
v_a_3981_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_4001_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_4001_ == 0)
{
v___x_3983_ = v___x_3980_;
v_isShared_3984_ = v_isSharedCheck_4001_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3980_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_4001_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
if (lean_obj_tag(v_a_3981_) == 1)
{
lean_object* v___x_3986_; 
lean_del_object(v___x_3961_);
lean_dec(v_mvarId_3947_);
lean_inc_ref(v_a_3981_);
if (v_isShared_3976_ == 0)
{
lean_ctor_set(v___x_3975_, 0, v_a_3981_);
v___x_3986_ = v___x_3975_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3998_; 
v_isSharedCheck_3998_ = !lean_is_exclusive(v_a_3981_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; 
v_unused_3999_ = lean_ctor_get(v_a_3981_, 0);
lean_dec(v_unused_3999_);
v___x_3988_ = v_a_3981_;
v_isShared_3989_ = v_isSharedCheck_3998_;
goto v_resetjp_3987_;
}
else
{
lean_dec(v_a_3981_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3998_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3986_);
lean_ctor_set(v___x_3990_, 1, v___x_3977_);
if (v_isShared_3989_ == 0)
{
lean_ctor_set(v___x_3988_, 0, v___x_3990_);
v___x_3992_ = v___x_3988_;
goto v_reusejp_3991_;
}
else
{
lean_object* v_reuseFailAlloc_3997_; 
v_reuseFailAlloc_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3997_, 0, v___x_3990_);
v___x_3992_ = v_reuseFailAlloc_3997_;
goto v_reusejp_3991_;
}
v_reusejp_3991_:
{
lean_object* v___x_3993_; lean_object* v___x_3995_; 
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
lean_ctor_set(v___x_3993_, 1, v_snd_3959_);
if (v_isShared_3984_ == 0)
{
lean_ctor_set(v___x_3983_, 0, v___x_3993_);
v___x_3995_ = v___x_3983_;
goto v_reusejp_3994_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3993_);
v___x_3995_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3994_;
}
v_reusejp_3994_:
{
return v___x_3995_;
}
}
}
}
}
else
{
lean_del_object(v___x_3983_);
lean_dec(v_a_3981_);
lean_del_object(v___x_3975_);
lean_dec(v_snd_3959_);
v_a_3965_ = v___x_3978_;
goto v___jp_3964_;
}
}
}
else
{
lean_object* v_a_4002_; lean_object* v___x_4004_; uint8_t v_isShared_4005_; uint8_t v_isSharedCheck_4009_; 
lean_del_object(v___x_3975_);
lean_del_object(v___x_3961_);
lean_dec(v_snd_3959_);
lean_dec(v_mvarId_3947_);
v_a_4002_ = lean_ctor_get(v___x_3980_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v___x_3980_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_4004_ = v___x_3980_;
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
else
{
lean_inc(v_a_4002_);
lean_dec(v___x_3980_);
v___x_4004_ = lean_box(0);
v_isShared_4005_ = v_isSharedCheck_4009_;
goto v_resetjp_4003_;
}
v_resetjp_4003_:
{
lean_object* v___x_4007_; 
if (v_isShared_4005_ == 0)
{
v___x_4007_ = v___x_4004_;
goto v_reusejp_4006_;
}
else
{
lean_object* v_reuseFailAlloc_4008_; 
v_reuseFailAlloc_4008_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4008_, 0, v_a_4002_);
v___x_4007_ = v_reuseFailAlloc_4008_;
goto v_reusejp_4006_;
}
v_reusejp_4006_:
{
return v___x_4007_;
}
}
}
}
}
v___jp_3964_:
{
lean_object* v___x_3967_; 
if (v_isShared_3962_ == 0)
{
lean_ctor_set(v___x_3961_, 1, v_a_3965_);
lean_ctor_set(v___x_3961_, 0, v___x_3963_);
v___x_3967_ = v___x_3961_;
goto v_reusejp_3966_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v___x_3963_);
lean_ctor_set(v_reuseFailAlloc_3971_, 1, v_a_3965_);
v___x_3967_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3966_;
}
v_reusejp_3966_:
{
size_t v___x_3968_; size_t v___x_3969_; lean_object* v___x_3970_; 
v___x_3968_ = ((size_t)1ULL);
v___x_3969_ = lean_usize_add(v_i_3950_, v___x_3968_);
v___x_3970_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3947_, v_as_3948_, v_sz_3949_, v___x_3969_, v___x_3967_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3955_);
return v___x_3970_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_4013_, lean_object* v_as_4014_, lean_object* v_sz_4015_, lean_object* v_i_4016_, lean_object* v_b_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
size_t v_sz_boxed_4023_; size_t v_i_boxed_4024_; lean_object* v_res_4025_; 
v_sz_boxed_4023_ = lean_unbox_usize(v_sz_4015_);
lean_dec(v_sz_4015_);
v_i_boxed_4024_ = lean_unbox_usize(v_i_4016_);
lean_dec(v_i_4016_);
v_res_4025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4013_, v_as_4014_, v_sz_boxed_4023_, v_i_boxed_4024_, v_b_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_);
lean_dec(v___y_4021_);
lean_dec_ref(v___y_4020_);
lean_dec(v___y_4019_);
lean_dec_ref(v___y_4018_);
lean_dec_ref(v_as_4014_);
return v_res_4025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4026_, lean_object* v_t_4027_, lean_object* v_init_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_){
_start:
{
lean_object* v_root_4034_; lean_object* v_tail_4035_; lean_object* v___x_4036_; 
v_root_4034_ = lean_ctor_get(v_t_4027_, 0);
v_tail_4035_ = lean_ctor_get(v_t_4027_, 1);
lean_inc(v_mvarId_4026_);
lean_inc_ref(v_init_4028_);
v___x_4036_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_4028_, v_mvarId_4026_, v_root_4034_, v_init_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
lean_dec_ref(v_init_4028_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4073_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4039_ = v___x_4036_;
v_isShared_4040_ = v_isSharedCheck_4073_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4036_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4073_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
if (lean_obj_tag(v_a_4037_) == 0)
{
lean_object* v_a_4041_; lean_object* v___x_4043_; 
lean_dec(v_mvarId_4026_);
v_a_4041_ = lean_ctor_get(v_a_4037_, 0);
lean_inc(v_a_4041_);
lean_dec_ref_known(v_a_4037_, 1);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v_a_4041_);
v___x_4043_ = v___x_4039_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4041_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; size_t v_sz_4048_; size_t v___x_4049_; lean_object* v___x_4050_; 
lean_del_object(v___x_4039_);
v_a_4045_ = lean_ctor_get(v_a_4037_, 0);
lean_inc(v_a_4045_);
lean_dec_ref_known(v_a_4037_, 1);
v___x_4046_ = lean_box(0);
v___x_4047_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
lean_ctor_set(v___x_4047_, 1, v_a_4045_);
v_sz_4048_ = lean_array_size(v_tail_4035_);
v___x_4049_ = ((size_t)0ULL);
v___x_4050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4026_, v_tail_4035_, v_sz_4048_, v___x_4049_, v___x_4047_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
if (lean_obj_tag(v___x_4050_) == 0)
{
lean_object* v_a_4051_; lean_object* v___x_4053_; uint8_t v_isShared_4054_; uint8_t v_isSharedCheck_4064_; 
v_a_4051_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4064_ == 0)
{
v___x_4053_ = v___x_4050_;
v_isShared_4054_ = v_isSharedCheck_4064_;
goto v_resetjp_4052_;
}
else
{
lean_inc(v_a_4051_);
lean_dec(v___x_4050_);
v___x_4053_ = lean_box(0);
v_isShared_4054_ = v_isSharedCheck_4064_;
goto v_resetjp_4052_;
}
v_resetjp_4052_:
{
lean_object* v_fst_4055_; 
v_fst_4055_ = lean_ctor_get(v_a_4051_, 0);
if (lean_obj_tag(v_fst_4055_) == 0)
{
lean_object* v_snd_4056_; lean_object* v___x_4058_; 
v_snd_4056_ = lean_ctor_get(v_a_4051_, 1);
lean_inc(v_snd_4056_);
lean_dec(v_a_4051_);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v_snd_4056_);
v___x_4058_ = v___x_4053_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_snd_4056_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
else
{
lean_object* v_val_4060_; lean_object* v___x_4062_; 
lean_inc_ref(v_fst_4055_);
lean_dec(v_a_4051_);
v_val_4060_ = lean_ctor_get(v_fst_4055_, 0);
lean_inc(v_val_4060_);
lean_dec_ref_known(v_fst_4055_, 1);
if (v_isShared_4054_ == 0)
{
lean_ctor_set(v___x_4053_, 0, v_val_4060_);
v___x_4062_ = v___x_4053_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_val_4060_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
return v___x_4062_;
}
}
}
}
else
{
lean_object* v_a_4065_; lean_object* v___x_4067_; uint8_t v_isShared_4068_; uint8_t v_isSharedCheck_4072_; 
v_a_4065_ = lean_ctor_get(v___x_4050_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4050_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4067_ = v___x_4050_;
v_isShared_4068_ = v_isSharedCheck_4072_;
goto v_resetjp_4066_;
}
else
{
lean_inc(v_a_4065_);
lean_dec(v___x_4050_);
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
}
else
{
lean_object* v_a_4074_; lean_object* v___x_4076_; uint8_t v_isShared_4077_; uint8_t v_isSharedCheck_4081_; 
lean_dec(v_mvarId_4026_);
v_a_4074_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4081_ == 0)
{
v___x_4076_ = v___x_4036_;
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
else
{
lean_inc(v_a_4074_);
lean_dec(v___x_4036_);
v___x_4076_ = lean_box(0);
v_isShared_4077_ = v_isSharedCheck_4081_;
goto v_resetjp_4075_;
}
v_resetjp_4075_:
{
lean_object* v___x_4079_; 
if (v_isShared_4077_ == 0)
{
v___x_4079_ = v___x_4076_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4074_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4082_, lean_object* v_t_4083_, lean_object* v_init_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_res_4090_; 
v_res_4090_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4082_, v_t_4083_, v_init_4084_, v___y_4085_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
lean_dec_ref(v___y_4085_);
lean_dec_ref(v_t_4083_);
return v_res_4090_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_){
_start:
{
lean_object* v_lctx_4100_; lean_object* v_decls_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; 
v_lctx_4100_ = lean_ctor_get(v___y_4095_, 2);
v_decls_4101_ = lean_ctor_get(v_lctx_4100_, 1);
v___x_4102_ = lean_box(0);
v___x_4103_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4104_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4094_, v_decls_4101_, v___x_4103_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v_a_4105_; lean_object* v___x_4107_; uint8_t v_isShared_4108_; uint8_t v_isSharedCheck_4117_; 
v_a_4105_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4107_ = v___x_4104_;
v_isShared_4108_ = v_isSharedCheck_4117_;
goto v_resetjp_4106_;
}
else
{
lean_inc(v_a_4105_);
lean_dec(v___x_4104_);
v___x_4107_ = lean_box(0);
v_isShared_4108_ = v_isSharedCheck_4117_;
goto v_resetjp_4106_;
}
v_resetjp_4106_:
{
lean_object* v_fst_4109_; 
v_fst_4109_ = lean_ctor_get(v_a_4105_, 0);
lean_inc(v_fst_4109_);
lean_dec(v_a_4105_);
if (lean_obj_tag(v_fst_4109_) == 0)
{
lean_object* v___x_4111_; 
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 0, v___x_4102_);
v___x_4111_ = v___x_4107_;
goto v_reusejp_4110_;
}
else
{
lean_object* v_reuseFailAlloc_4112_; 
v_reuseFailAlloc_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4112_, 0, v___x_4102_);
v___x_4111_ = v_reuseFailAlloc_4112_;
goto v_reusejp_4110_;
}
v_reusejp_4110_:
{
return v___x_4111_;
}
}
else
{
lean_object* v_val_4113_; lean_object* v___x_4115_; 
v_val_4113_ = lean_ctor_get(v_fst_4109_, 0);
lean_inc(v_val_4113_);
lean_dec_ref_known(v_fst_4109_, 1);
if (v_isShared_4108_ == 0)
{
lean_ctor_set(v___x_4107_, 0, v_val_4113_);
v___x_4115_ = v___x_4107_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_val_4113_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
}
}
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
v_a_4118_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4104_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4104_);
v___x_4120_ = lean_box(0);
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
v_resetjp_4119_:
{
lean_object* v___x_4123_; 
if (v_isShared_4121_ == 0)
{
v___x_4123_ = v___x_4120_;
goto v_reusejp_4122_;
}
else
{
lean_object* v_reuseFailAlloc_4124_; 
v_reuseFailAlloc_4124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4124_, 0, v_a_4118_);
v___x_4123_ = v_reuseFailAlloc_4124_;
goto v_reusejp_4122_;
}
v_reusejp_4122_:
{
return v___x_4123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_){
_start:
{
lean_object* v_res_4132_; 
v_res_4132_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4126_, v___y_4127_, v___y_4128_, v___y_4129_, v___y_4130_);
lean_dec(v___y_4130_);
lean_dec_ref(v___y_4129_);
lean_dec(v___y_4128_);
lean_dec_ref(v___y_4127_);
return v_res_4132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_){
_start:
{
lean_object* v___f_4139_; lean_object* v___x_4140_; 
lean_inc(v_mvarId_4133_);
v___f_4139_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4139_, 0, v_mvarId_4133_);
v___x_4140_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_4133_, v___f_4139_, v_a_4134_, v_a_4135_, v_a_4136_, v_a_4137_);
return v___x_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_){
_start:
{
lean_object* v_res_4147_; 
v_res_4147_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
lean_dec(v_a_4145_);
lean_dec_ref(v_a_4144_);
lean_dec(v_a_4143_);
lean_dec_ref(v_a_4142_);
return v_res_4147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_){
_start:
{
lean_object* v___x_4154_; 
lean_inc(v_mvarId_4148_);
v___x_4154_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4148_, v_a_4149_, v_a_4150_, v_a_4151_, v_a_4152_);
if (lean_obj_tag(v___x_4154_) == 0)
{
lean_object* v_a_4155_; lean_object* v___x_4157_; uint8_t v_isShared_4158_; uint8_t v_isSharedCheck_4164_; 
v_a_4155_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4164_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4164_ == 0)
{
v___x_4157_ = v___x_4154_;
v_isShared_4158_ = v_isSharedCheck_4164_;
goto v_resetjp_4156_;
}
else
{
lean_inc(v_a_4155_);
lean_dec(v___x_4154_);
v___x_4157_ = lean_box(0);
v_isShared_4158_ = v_isSharedCheck_4164_;
goto v_resetjp_4156_;
}
v_resetjp_4156_:
{
if (lean_obj_tag(v_a_4155_) == 1)
{
lean_object* v_val_4159_; 
lean_del_object(v___x_4157_);
lean_dec(v_mvarId_4148_);
v_val_4159_ = lean_ctor_get(v_a_4155_, 0);
lean_inc(v_val_4159_);
lean_dec_ref_known(v_a_4155_, 1);
v_mvarId_4148_ = v_val_4159_;
goto _start;
}
else
{
lean_object* v___x_4162_; 
lean_dec(v_a_4155_);
if (v_isShared_4158_ == 0)
{
lean_ctor_set(v___x_4157_, 0, v_mvarId_4148_);
v___x_4162_ = v___x_4157_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v_mvarId_4148_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
}
}
else
{
lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4172_; 
lean_dec(v_mvarId_4148_);
v_a_4165_ = lean_ctor_get(v___x_4154_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4154_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4167_ = v___x_4154_;
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4154_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4172_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4170_; 
if (v_isShared_4168_ == 0)
{
v___x_4170_ = v___x_4167_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v_a_4165_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_Meta_substVars(v_mvarId_4173_, v_a_4174_, v_a_4175_, v_a_4176_, v_a_4177_);
lean_dec(v_a_4177_);
lean_dec_ref(v_a_4176_);
lean_dec(v_a_4175_);
lean_dec_ref(v_a_4174_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4242_; uint8_t v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; 
v___x_4242_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_4243_ = 0;
v___x_4244_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4245_ = l_Lean_registerTraceClass(v___x_4242_, v___x_4243_, v___x_4244_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4246_){
_start:
{
lean_object* v_res_4247_; 
v_res_4247_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4247_;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_MatchUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Assert(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
