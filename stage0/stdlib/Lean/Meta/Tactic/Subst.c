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
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(lean_object* v_e_1_, lean_object* v___y_2_){
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
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_1_ = stack[0].m_obj;
lean_object* v___y_2_ = stack[1].m_obj;
lean_object* v_res_26_;
v_res_26_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_e_1_, v___y_2_);
stack->m_obj
 = v_res_26_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg___boxed(lean_object* v_e_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_e_27_, v___y_28_);
lean_dec(v___y_28_);
return v_res_30_;
}
}
lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT void l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_31_ = stack[0].m_obj;
lean_object* v___y_32_ = stack[1].m_obj;
lean_object* v___y_33_ = stack[2].m_obj;
lean_object* v___y_34_ = stack[3].m_obj;
lean_object* v___y_35_ = stack[4].m_obj;
lean_object* v_res_38_;
v_res_38_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0(v_e_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
stack->m_obj
 = v_res_38_;
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___boxed(lean_object* v_e_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_, lean_object* v___y_44_){
_start:
{
lean_object* v_res_45_; 
v_res_45_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0(v_e_39_, v___y_40_, v___y_41_, v___y_42_, v___y_43_);
lean_dec(v___y_43_);
lean_dec_ref(v___y_42_);
lean_dec(v___y_41_);
lean_dec_ref(v___y_40_);
return v_res_45_;
}
}
uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0(lean_object* v_x_46_){
_start:
{
uint8_t v___x_47_; 
v___x_47_ = 0;
return v___x_47_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_46_ = stack[0].m_obj;
uint8_t v_res_48_;
v_res_48_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0(v_x_46_);
stack->m_num = v_res_48_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0___boxed(lean_object* v_x_49_){
_start:
{
uint8_t v_res_50_; lean_object* v_r_51_; 
v_res_50_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__0(v_x_49_);
lean_dec(v_x_49_);
v_r_51_ = lean_box(v_res_50_);
return v_r_51_;
}
}
uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1(lean_object* v_fvarId_52_, lean_object* v_x_53_){
_start:
{
uint8_t v___x_54_; 
v___x_54_ = l_Lean_instBEqFVarId_beq(v_fvarId_52_, v_x_53_);
return v___x_54_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_52_ = stack[0].m_obj;
lean_object* v_x_53_ = stack[1].m_obj;
uint8_t v_res_55_;
v_res_55_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1(v_fvarId_52_, v_x_53_);
stack->m_num = v_res_55_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1___boxed(lean_object* v_fvarId_56_, lean_object* v_x_57_){
_start:
{
uint8_t v_res_58_; lean_object* v_r_59_; 
v_res_58_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1(v_fvarId_56_, v_x_57_);
lean_dec(v_x_57_);
lean_dec(v_fvarId_56_);
v_r_59_ = lean_box(v_res_58_);
return v_r_59_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_61_ = lean_box(0);
v___x_62_ = lean_unsigned_to_nat(16u);
v___x_63_ = lean_mk_array(v___x_62_, v___x_61_);
return v___x_63_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__1);
v___x_65_ = lean_unsigned_to_nat(0u);
v___x_66_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_65_);
lean_ctor_set(v___x_66_, 1, v___x_64_);
return v___x_66_;
}
}
lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(lean_object* v_e_67_, lean_object* v_fvarId_68_, lean_object* v___y_69_){
_start:
{
lean_object* v___f_71_; lean_object* v___f_72_; lean_object* v___x_73_; uint8_t v_fst_75_; lean_object* v_mctx_76_; lean_object* v___y_94_; lean_object* v_mctx_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___f_71_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__0));
v___f_72_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_72_, 0, v_fvarId_68_);
v___x_73_ = lean_st_ref_get(v___y_69_);
v_mctx_99_ = lean_ctor_get(v___x_73_, 0);
lean_inc_ref_n(v_mctx_99_, 2);
lean_dec(v___x_73_);
v___x_100_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___closed__2);
v___x_101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
lean_ctor_set(v___x_101_, 1, v_mctx_99_);
v___x_102_ = l_Lean_Expr_hasFVar(v_e_67_);
if (v___x_102_ == 0)
{
uint8_t v___x_103_; 
v___x_103_ = l_Lean_Expr_hasMVar(v_e_67_);
if (v___x_103_ == 0)
{
lean_dec_ref_known(v___x_101_, 2);
lean_dec_ref(v___f_72_);
lean_dec_ref(v_e_67_);
v_fst_75_ = v___x_103_;
v_mctx_76_ = v_mctx_99_;
goto v___jp_74_;
}
else
{
lean_object* v___x_104_; 
lean_dec_ref(v_mctx_99_);
v___x_104_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_72_, v___f_71_, v_e_67_, v___x_101_);
v___y_94_ = v___x_104_;
goto v___jp_93_;
}
}
else
{
lean_object* v___x_105_; 
lean_dec_ref(v_mctx_99_);
v___x_105_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_72_, v___f_71_, v_e_67_, v___x_101_);
v___y_94_ = v___x_105_;
goto v___jp_93_;
}
v___jp_74_:
{
lean_object* v___x_77_; lean_object* v_cache_78_; lean_object* v_zetaDeltaFVarIds_79_; lean_object* v_postponed_80_; lean_object* v_diag_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_91_; 
v___x_77_ = lean_st_ref_take(v___y_69_);
v_cache_78_ = lean_ctor_get(v___x_77_, 1);
v_zetaDeltaFVarIds_79_ = lean_ctor_get(v___x_77_, 2);
v_postponed_80_ = lean_ctor_get(v___x_77_, 3);
v_diag_81_ = lean_ctor_get(v___x_77_, 4);
v_isSharedCheck_91_ = !lean_is_exclusive(v___x_77_);
if (v_isSharedCheck_91_ == 0)
{
lean_object* v_unused_92_; 
v_unused_92_ = lean_ctor_get(v___x_77_, 0);
lean_dec(v_unused_92_);
v___x_83_ = v___x_77_;
v_isShared_84_ = v_isSharedCheck_91_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_diag_81_);
lean_inc(v_postponed_80_);
lean_inc(v_zetaDeltaFVarIds_79_);
lean_inc(v_cache_78_);
lean_dec(v___x_77_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_91_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v___x_86_; 
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v_mctx_76_);
v___x_86_ = v___x_83_;
goto v_reusejp_85_;
}
else
{
lean_object* v_reuseFailAlloc_90_; 
v_reuseFailAlloc_90_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_90_, 0, v_mctx_76_);
lean_ctor_set(v_reuseFailAlloc_90_, 1, v_cache_78_);
lean_ctor_set(v_reuseFailAlloc_90_, 2, v_zetaDeltaFVarIds_79_);
lean_ctor_set(v_reuseFailAlloc_90_, 3, v_postponed_80_);
lean_ctor_set(v_reuseFailAlloc_90_, 4, v_diag_81_);
v___x_86_ = v_reuseFailAlloc_90_;
goto v_reusejp_85_;
}
v_reusejp_85_:
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v___x_87_ = lean_st_ref_put(v___y_69_, v___x_86_);
v___x_88_ = lean_box(v_fst_75_);
v___x_89_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_89_, 0, v___x_88_);
return v___x_89_;
}
}
}
v___jp_93_:
{
lean_object* v_snd_95_; lean_object* v_fst_96_; lean_object* v_mctx_97_; uint8_t v___x_98_; 
v_snd_95_ = lean_ctor_get(v___y_94_, 1);
lean_inc(v_snd_95_);
v_fst_96_ = lean_ctor_get(v___y_94_, 0);
lean_inc(v_fst_96_);
lean_dec_ref(v___y_94_);
v_mctx_97_ = lean_ctor_get(v_snd_95_, 1);
lean_inc_ref(v_mctx_97_);
lean_dec(v_snd_95_);
v___x_98_ = lean_unbox(v_fst_96_);
lean_dec(v_fst_96_);
v_fst_75_ = v___x_98_;
v_mctx_76_ = v_mctx_97_;
goto v___jp_74_;
}
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_67_ = stack[0].m_obj;
lean_object* v_fvarId_68_ = stack[1].m_obj;
lean_object* v___y_69_ = stack[2].m_obj;
lean_object* v_res_106_;
v_res_106_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_e_67_, v_fvarId_68_, v___y_69_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg___boxed(lean_object* v_e_107_, lean_object* v_fvarId_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_e_107_, v_fvarId_108_, v___y_109_);
lean_dec(v___y_109_);
return v_res_111_;
}
}
lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3(lean_object* v_e_112_, lean_object* v_fvarId_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_e_112_, v_fvarId_113_, v___y_115_);
return v___x_119_;
}
}
LEAN_EXPORT void l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_e_112_ = stack[0].m_obj;
lean_object* v_fvarId_113_ = stack[1].m_obj;
lean_object* v___y_114_ = stack[2].m_obj;
lean_object* v___y_115_ = stack[3].m_obj;
lean_object* v___y_116_ = stack[4].m_obj;
lean_object* v___y_117_ = stack[5].m_obj;
lean_object* v_res_120_;
v_res_120_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3(v_e_112_, v_fvarId_113_, v___y_114_, v___y_115_, v___y_116_, v___y_117_);
stack->m_obj
 = v_res_120_;
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___boxed(lean_object* v_e_121_, lean_object* v_fvarId_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_, lean_object* v___y_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3(v_e_121_, v_fvarId_122_, v___y_123_, v___y_124_, v___y_125_, v___y_126_);
lean_dec(v___y_126_);
lean_dec_ref(v___y_125_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
return v_res_128_;
}
}
lean_object* l_panic___at___00Lean_Meta_substCore_spec__6(lean_object* v_msg_130_, lean_object* v___y_131_, lean_object* v___y_132_, lean_object* v___y_133_, lean_object* v___y_134_){
_start:
{
lean_object* v___f_136_; lean_object* v___x_24704__overap_137_; lean_object* v___x_138_; 
v___f_136_ = ((lean_object*)(l_panic___at___00Lean_Meta_substCore_spec__6___closed__0));
v___x_24704__overap_137_ = lean_panic_fn_borrowed(v___f_136_, v_msg_130_);
lean_inc(v___y_134_);
lean_inc_ref(v___y_133_);
lean_inc(v___y_132_);
lean_inc_ref(v___y_131_);
v___x_138_ = lean_apply_5(v___x_24704__overap_137_, v___y_131_, v___y_132_, v___y_133_, v___y_134_, lean_box(0));
return v___x_138_;
}
}
LEAN_EXPORT void l_panic___at___00Lean_Meta_substCore_spec__6_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_130_ = stack[0].m_obj;
lean_object* v___y_131_ = stack[1].m_obj;
lean_object* v___y_132_ = stack[2].m_obj;
lean_object* v___y_133_ = stack[3].m_obj;
lean_object* v___y_134_ = stack[4].m_obj;
lean_object* v_res_139_;
v_res_139_ = l_panic___at___00Lean_Meta_substCore_spec__6(v_msg_130_, v___y_131_, v___y_132_, v___y_133_, v___y_134_);
stack->m_obj
 = v_res_139_;
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__6___boxed(lean_object* v_msg_140_, lean_object* v___y_141_, lean_object* v___y_142_, lean_object* v___y_143_, lean_object* v___y_144_, lean_object* v___y_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_panic___at___00Lean_Meta_substCore_spec__6(v_msg_140_, v___y_141_, v___y_142_, v___y_143_, v___y_144_);
lean_dec(v___y_144_);
lean_dec_ref(v___y_143_);
lean_dec(v___y_142_);
lean_dec_ref(v___y_141_);
return v_res_146_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(lean_object* v_mvarId_147_, lean_object* v_x_148_, lean_object* v___y_149_, lean_object* v___y_150_, lean_object* v___y_151_, lean_object* v___y_152_){
_start:
{
lean_object* v___x_154_; 
v___x_154_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_147_, v_x_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
if (lean_obj_tag(v___x_154_) == 0)
{
lean_object* v_a_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_162_; 
v_a_155_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_162_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_162_ == 0)
{
v___x_157_ = v___x_154_;
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_a_155_);
lean_dec(v___x_154_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_162_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_160_; 
if (v_isShared_158_ == 0)
{
v___x_160_ = v___x_157_;
goto v_reusejp_159_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v_a_155_);
v___x_160_ = v_reuseFailAlloc_161_;
goto v_reusejp_159_;
}
v_reusejp_159_:
{
return v___x_160_;
}
}
}
else
{
lean_object* v_a_163_; lean_object* v___x_165_; uint8_t v_isShared_166_; uint8_t v_isSharedCheck_170_; 
v_a_163_ = lean_ctor_get(v___x_154_, 0);
v_isSharedCheck_170_ = !lean_is_exclusive(v___x_154_);
if (v_isSharedCheck_170_ == 0)
{
v___x_165_ = v___x_154_;
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
else
{
lean_inc(v_a_163_);
lean_dec(v___x_154_);
v___x_165_ = lean_box(0);
v_isShared_166_ = v_isSharedCheck_170_;
goto v_resetjp_164_;
}
v_resetjp_164_:
{
lean_object* v___x_168_; 
if (v_isShared_166_ == 0)
{
v___x_168_ = v___x_165_;
goto v_reusejp_167_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_163_);
v___x_168_ = v_reuseFailAlloc_169_;
goto v_reusejp_167_;
}
v_reusejp_167_:
{
return v___x_168_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_147_ = stack[0].m_obj;
lean_object* v_x_148_ = stack[1].m_obj;
lean_object* v___y_149_ = stack[2].m_obj;
lean_object* v___y_150_ = stack[3].m_obj;
lean_object* v___y_151_ = stack[4].m_obj;
lean_object* v___y_152_ = stack[5].m_obj;
lean_object* v_res_171_;
v_res_171_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_147_, v_x_148_, v___y_149_, v___y_150_, v___y_151_, v___y_152_);
stack->m_obj
 = v_res_171_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg___boxed(lean_object* v_mvarId_172_, lean_object* v_x_173_, lean_object* v___y_174_, lean_object* v___y_175_, lean_object* v___y_176_, lean_object* v___y_177_, lean_object* v___y_178_){
_start:
{
lean_object* v_res_179_; 
v_res_179_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_172_, v_x_173_, v___y_174_, v___y_175_, v___y_176_, v___y_177_);
lean_dec(v___y_177_);
lean_dec_ref(v___y_176_);
lean_dec(v___y_175_);
lean_dec_ref(v___y_174_);
return v_res_179_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(lean_object* v_00_u03b1_180_, lean_object* v_mvarId_181_, lean_object* v_x_182_, lean_object* v___y_183_, lean_object* v___y_184_, lean_object* v___y_185_, lean_object* v___y_186_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
return v___x_188_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_181_ = stack[1].m_obj;
lean_object* v_x_182_ = stack[2].m_obj;
lean_object* v___y_183_ = stack[3].m_obj;
lean_object* v___y_184_ = stack[4].m_obj;
lean_object* v___y_185_ = stack[5].m_obj;
lean_object* v___y_186_ = stack[6].m_obj;
lean_object* v_res_189_;
v_res_189_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(lean_box(0), v_mvarId_181_, v_x_182_, v___y_183_, v___y_184_, v___y_185_, v___y_186_);
stack->m_obj
 = v_res_189_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed(lean_object* v_00_u03b1_190_, lean_object* v_mvarId_191_, lean_object* v_x_192_, lean_object* v___y_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(v_00_u03b1_190_, v_mvarId_191_, v_x_192_, v___y_193_, v___y_194_, v___y_195_, v___y_196_);
lean_dec(v___y_196_);
lean_dec_ref(v___y_195_);
lean_dec(v___y_194_);
lean_dec_ref(v___y_193_);
return v_res_198_;
}
}
lean_object* l_Lean_Meta_substCore___lam__0(lean_object* v_type_199_, lean_object* v___x_200_, lean_object* v___x_201_, lean_object* v___x_202_, uint8_t v___x_203_, uint8_t v___x_204_, lean_object* v_hAux_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v___x_211_; 
lean_inc_ref(v_hAux_205_);
v___x_211_ = l_Lean_Meta_mkEqSymm(v_hAux_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; uint8_t v___x_217_; lean_object* v___x_218_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v___x_213_ = l_Lean_Expr_replaceFVar(v_type_199_, v___x_200_, v_a_212_);
lean_dec(v_a_212_);
v___x_214_ = lean_mk_empty_array_with_capacity(v___x_201_);
v___x_215_ = lean_array_push(v___x_214_, v___x_202_);
v___x_216_ = lean_array_push(v___x_215_, v_hAux_205_);
v___x_217_ = 1;
v___x_218_ = l_Lean_Meta_mkLambdaFVars(v___x_216_, v___x_213_, v___x_203_, v___x_204_, v___x_203_, v___x_204_, v___x_217_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
lean_dec_ref(v___x_216_);
return v___x_218_;
}
else
{
lean_dec_ref(v_hAux_205_);
lean_dec_ref(v___x_202_);
lean_dec_ref(v___x_200_);
return v___x_211_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_substCore___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_type_199_ = stack[0].m_obj;
lean_object* v___x_200_ = stack[1].m_obj;
lean_object* v___x_201_ = stack[2].m_obj;
lean_object* v___x_202_ = stack[3].m_obj;
uint8_t v___x_203_ = stack[4].m_num;
uint8_t v___x_204_ = stack[5].m_num;
lean_object* v_hAux_205_ = stack[6].m_obj;
lean_object* v___y_206_ = stack[7].m_obj;
lean_object* v___y_207_ = stack[8].m_obj;
lean_object* v___y_208_ = stack[9].m_obj;
lean_object* v___y_209_ = stack[10].m_obj;
lean_object* v_res_219_;
v_res_219_ = l_Lean_Meta_substCore___lam__0(v_type_199_, v___x_200_, v___x_201_, v___x_202_, v___x_203_, v___x_204_, v_hAux_205_, v___y_206_, v___y_207_, v___y_208_, v___y_209_);
stack->m_obj
 = v_res_219_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object* v_type_220_, lean_object* v___x_221_, lean_object* v___x_222_, lean_object* v___x_223_, lean_object* v___x_224_, lean_object* v___x_225_, lean_object* v_hAux_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_, lean_object* v___y_230_, lean_object* v___y_231_){
_start:
{
uint8_t v___x_27296__boxed_232_; uint8_t v___x_27297__boxed_233_; lean_object* v_res_234_; 
v___x_27296__boxed_232_ = lean_unbox(v___x_224_);
v___x_27297__boxed_233_ = lean_unbox(v___x_225_);
v_res_234_ = l_Lean_Meta_substCore___lam__0(v_type_220_, v___x_221_, v___x_222_, v___x_223_, v___x_27296__boxed_232_, v___x_27297__boxed_233_, v_hAux_226_, v___y_227_, v___y_228_, v___y_229_, v___y_230_);
lean_dec(v___y_230_);
lean_dec_ref(v___y_229_);
lean_dec(v___y_228_);
lean_dec_ref(v___y_227_);
lean_dec(v___x_222_);
lean_dec_ref(v_type_220_);
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14___redArg(lean_object* v_x_235_, lean_object* v_x_236_, lean_object* v_x_237_, lean_object* v_x_238_){
_start:
{
lean_object* v_ks_239_; lean_object* v_vs_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_264_; 
v_ks_239_ = lean_ctor_get(v_x_235_, 0);
v_vs_240_ = lean_ctor_get(v_x_235_, 1);
v_isSharedCheck_264_ = !lean_is_exclusive(v_x_235_);
if (v_isSharedCheck_264_ == 0)
{
v___x_242_ = v_x_235_;
v_isShared_243_ = v_isSharedCheck_264_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_vs_240_);
lean_inc(v_ks_239_);
lean_dec(v_x_235_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_264_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_244_; uint8_t v___x_245_; 
v___x_244_ = lean_array_get_size(v_ks_239_);
v___x_245_ = lean_nat_dec_lt(v_x_236_, v___x_244_);
if (v___x_245_ == 0)
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_249_; 
lean_dec(v_x_236_);
v___x_246_ = lean_array_push(v_ks_239_, v_x_237_);
v___x_247_ = lean_array_push(v_vs_240_, v_x_238_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_247_);
lean_ctor_set(v___x_242_, 0, v___x_246_);
v___x_249_ = v___x_242_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_247_);
v___x_249_ = v_reuseFailAlloc_250_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
return v___x_249_;
}
}
else
{
lean_object* v_k_x27_251_; uint8_t v___x_252_; 
v_k_x27_251_ = lean_array_fget_borrowed(v_ks_239_, v_x_236_);
v___x_252_ = l_Lean_instBEqMVarId_beq(v_x_237_, v_k_x27_251_);
if (v___x_252_ == 0)
{
lean_object* v___x_254_; 
if (v_isShared_243_ == 0)
{
v___x_254_ = v___x_242_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v_ks_239_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_vs_240_);
v___x_254_ = v_reuseFailAlloc_258_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_255_ = lean_unsigned_to_nat(1u);
v___x_256_ = lean_nat_add(v_x_236_, v___x_255_);
lean_dec(v_x_236_);
v_x_235_ = v___x_254_;
v_x_236_ = v___x_256_;
goto _start;
}
}
else
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_262_; 
v___x_259_ = lean_array_fset(v_ks_239_, v_x_236_, v_x_237_);
v___x_260_ = lean_array_fset(v_vs_240_, v_x_236_, v_x_238_);
lean_dec(v_x_236_);
if (v_isShared_243_ == 0)
{
lean_ctor_set(v___x_242_, 1, v___x_260_);
lean_ctor_set(v___x_242_, 0, v___x_259_);
v___x_262_ = v___x_242_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_259_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v___x_260_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13___redArg(lean_object* v_n_265_, lean_object* v_k_266_, lean_object* v_v_267_){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = lean_unsigned_to_nat(0u);
v___x_269_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14___redArg(v_n_265_, v___x_268_, v_k_266_, v_v_267_);
return v___x_269_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_270_; 
v___x_270_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_270_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(lean_object* v_x_271_, size_t v_x_272_, size_t v_x_273_, lean_object* v_x_274_, lean_object* v_x_275_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v_es_276_; size_t v___x_277_; size_t v___x_278_; lean_object* v_j_279_; lean_object* v___x_280_; uint8_t v___x_281_; 
v_es_276_ = lean_ctor_get(v_x_271_, 0);
v___x_277_ = ((size_t)31ULL);
v___x_278_ = lean_usize_land(v_x_272_, v___x_277_);
v_j_279_ = lean_usize_to_nat(v___x_278_);
v___x_280_ = lean_array_get_size(v_es_276_);
v___x_281_ = lean_nat_dec_lt(v_j_279_, v___x_280_);
if (v___x_281_ == 0)
{
lean_dec(v_j_279_);
lean_dec(v_x_275_);
lean_dec(v_x_274_);
return v_x_271_;
}
else
{
lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_320_; 
lean_inc_ref(v_es_276_);
v_isSharedCheck_320_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_320_ == 0)
{
lean_object* v_unused_321_; 
v_unused_321_ = lean_ctor_get(v_x_271_, 0);
lean_dec(v_unused_321_);
v___x_283_ = v_x_271_;
v_isShared_284_ = v_isSharedCheck_320_;
goto v_resetjp_282_;
}
else
{
lean_dec(v_x_271_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_320_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v_v_285_; lean_object* v___x_286_; lean_object* v_xs_x27_287_; lean_object* v___y_289_; 
v_v_285_ = lean_array_fget(v_es_276_, v_j_279_);
v___x_286_ = lean_box(0);
v_xs_x27_287_ = lean_array_fset(v_es_276_, v_j_279_, v___x_286_);
switch(lean_obj_tag(v_v_285_))
{
case 0:
{
lean_object* v_key_294_; lean_object* v_val_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_305_; 
v_key_294_ = lean_ctor_get(v_v_285_, 0);
v_val_295_ = lean_ctor_get(v_v_285_, 1);
v_isSharedCheck_305_ = !lean_is_exclusive(v_v_285_);
if (v_isSharedCheck_305_ == 0)
{
v___x_297_ = v_v_285_;
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_val_295_);
lean_inc(v_key_294_);
lean_dec(v_v_285_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_305_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
uint8_t v___x_299_; 
v___x_299_ = l_Lean_instBEqMVarId_beq(v_x_274_, v_key_294_);
if (v___x_299_ == 0)
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_del_object(v___x_297_);
v___x_300_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_294_, v_val_295_, v_x_274_, v_x_275_);
v___x_301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_301_, 0, v___x_300_);
v___y_289_ = v___x_301_;
goto v___jp_288_;
}
else
{
lean_object* v___x_303_; 
lean_dec(v_val_295_);
lean_dec(v_key_294_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 1, v_x_275_);
lean_ctor_set(v___x_297_, 0, v_x_274_);
v___x_303_ = v___x_297_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v_x_274_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_x_275_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
v___y_289_ = v___x_303_;
goto v___jp_288_;
}
}
}
}
case 1:
{
lean_object* v_node_306_; lean_object* v___x_308_; uint8_t v_isShared_309_; uint8_t v_isSharedCheck_318_; 
v_node_306_ = lean_ctor_get(v_v_285_, 0);
v_isSharedCheck_318_ = !lean_is_exclusive(v_v_285_);
if (v_isSharedCheck_318_ == 0)
{
v___x_308_ = v_v_285_;
v_isShared_309_ = v_isSharedCheck_318_;
goto v_resetjp_307_;
}
else
{
lean_inc(v_node_306_);
lean_dec(v_v_285_);
v___x_308_ = lean_box(0);
v_isShared_309_ = v_isSharedCheck_318_;
goto v_resetjp_307_;
}
v_resetjp_307_:
{
size_t v___x_310_; size_t v___x_311_; size_t v___x_312_; size_t v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
v___x_310_ = ((size_t)5ULL);
v___x_311_ = lean_usize_shift_right(v_x_272_, v___x_310_);
v___x_312_ = ((size_t)1ULL);
v___x_313_ = lean_usize_add(v_x_273_, v___x_312_);
v___x_314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_node_306_, v___x_311_, v___x_313_, v_x_274_, v_x_275_);
if (v_isShared_309_ == 0)
{
lean_ctor_set(v___x_308_, 0, v___x_314_);
v___x_316_ = v___x_308_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
v___y_289_ = v___x_316_;
goto v___jp_288_;
}
}
}
default: 
{
lean_object* v___x_319_; 
v___x_319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_319_, 0, v_x_274_);
lean_ctor_set(v___x_319_, 1, v_x_275_);
v___y_289_ = v___x_319_;
goto v___jp_288_;
}
}
v___jp_288_:
{
lean_object* v___x_290_; lean_object* v___x_292_; 
v___x_290_ = lean_array_fset(v_xs_x27_287_, v_j_279_, v___y_289_);
lean_dec(v_j_279_);
if (v_isShared_284_ == 0)
{
lean_ctor_set(v___x_283_, 0, v___x_290_);
v___x_292_ = v___x_283_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v___x_290_);
v___x_292_ = v_reuseFailAlloc_293_;
goto v_reusejp_291_;
}
v_reusejp_291_:
{
return v___x_292_;
}
}
}
}
}
else
{
lean_object* v_ks_322_; lean_object* v_vs_323_; lean_object* v___x_325_; uint8_t v_isShared_326_; uint8_t v_isSharedCheck_341_; 
v_ks_322_ = lean_ctor_get(v_x_271_, 0);
v_vs_323_ = lean_ctor_get(v_x_271_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_341_ == 0)
{
v___x_325_ = v_x_271_;
v_isShared_326_ = v_isSharedCheck_341_;
goto v_resetjp_324_;
}
else
{
lean_inc(v_vs_323_);
lean_inc(v_ks_322_);
lean_dec(v_x_271_);
v___x_325_ = lean_box(0);
v_isShared_326_ = v_isSharedCheck_341_;
goto v_resetjp_324_;
}
v_resetjp_324_:
{
lean_object* v___x_328_; 
if (v_isShared_326_ == 0)
{
v___x_328_ = v___x_325_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v_ks_322_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_vs_323_);
v___x_328_ = v_reuseFailAlloc_340_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
lean_object* v_newNode_329_; size_t v___x_330_; uint8_t v___x_331_; 
v_newNode_329_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13___redArg(v___x_328_, v_x_274_, v_x_275_);
v___x_330_ = ((size_t)7ULL);
v___x_331_ = lean_usize_dec_le(v___x_330_, v_x_273_);
if (v___x_331_ == 0)
{
lean_object* v___x_332_; lean_object* v___x_333_; uint8_t v___x_334_; 
v___x_332_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_329_);
v___x_333_ = lean_unsigned_to_nat(4u);
v___x_334_ = lean_nat_dec_lt(v___x_332_, v___x_333_);
lean_dec(v___x_332_);
if (v___x_334_ == 0)
{
lean_object* v_ks_335_; lean_object* v_vs_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_ks_335_ = lean_ctor_get(v_newNode_329_, 0);
lean_inc_ref(v_ks_335_);
v_vs_336_ = lean_ctor_get(v_newNode_329_, 1);
lean_inc_ref(v_vs_336_);
lean_dec_ref(v_newNode_329_);
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___closed__0);
v___x_339_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(v_x_273_, v_ks_335_, v_vs_336_, v___x_337_, v___x_338_);
lean_dec_ref(v_vs_336_);
lean_dec_ref(v_ks_335_);
return v___x_339_;
}
else
{
return v_newNode_329_;
}
}
else
{
return v_newNode_329_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_271_ = stack[0].m_obj;
size_t v_x_272_ = stack[1].m_num;
size_t v_x_273_ = stack[2].m_num;
lean_object* v_x_274_ = stack[3].m_obj;
lean_object* v_x_275_ = stack[4].m_obj;
lean_object* v_res_342_;
v_res_342_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_271_, v_x_272_, v_x_273_, v_x_274_, v_x_275_);
stack->m_obj
 = v_res_342_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(size_t v_depth_343_, lean_object* v_keys_344_, lean_object* v_vals_345_, lean_object* v_i_346_, lean_object* v_entries_347_){
_start:
{
lean_object* v___x_348_; uint8_t v___x_349_; 
v___x_348_ = lean_array_get_size(v_keys_344_);
v___x_349_ = lean_nat_dec_lt(v_i_346_, v___x_348_);
if (v___x_349_ == 0)
{
lean_dec(v_i_346_);
return v_entries_347_;
}
else
{
lean_object* v_k_350_; lean_object* v_v_351_; uint64_t v___x_352_; size_t v_h_353_; size_t v___x_354_; lean_object* v___x_355_; size_t v___x_356_; size_t v___x_357_; size_t v___x_358_; size_t v_h_359_; lean_object* v___x_360_; lean_object* v___x_361_; 
v_k_350_ = lean_array_fget_borrowed(v_keys_344_, v_i_346_);
v_v_351_ = lean_array_fget_borrowed(v_vals_345_, v_i_346_);
v___x_352_ = l_Lean_instHashableMVarId_hash(v_k_350_);
v_h_353_ = lean_uint64_to_usize(v___x_352_);
v___x_354_ = ((size_t)5ULL);
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = ((size_t)1ULL);
v___x_357_ = lean_usize_sub(v_depth_343_, v___x_356_);
v___x_358_ = lean_usize_mul(v___x_354_, v___x_357_);
v_h_359_ = lean_usize_shift_right(v_h_353_, v___x_358_);
v___x_360_ = lean_nat_add(v_i_346_, v___x_355_);
lean_dec(v_i_346_);
lean_inc(v_v_351_);
lean_inc(v_k_350_);
v___x_361_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_entries_347_, v_h_359_, v_depth_343_, v_k_350_, v_v_351_);
v_i_346_ = v___x_360_;
v_entries_347_ = v___x_361_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_343_ = stack[0].m_num;
lean_object* v_keys_344_ = stack[1].m_obj;
lean_object* v_vals_345_ = stack[2].m_obj;
lean_object* v_i_346_ = stack[3].m_obj;
lean_object* v_entries_347_ = stack[4].m_obj;
lean_object* v_res_363_;
v_res_363_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(v_depth_343_, v_keys_344_, v_vals_345_, v_i_346_, v_entries_347_);
stack->m_obj
 = v_res_363_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg___boxed(lean_object* v_depth_364_, lean_object* v_keys_365_, lean_object* v_vals_366_, lean_object* v_i_367_, lean_object* v_entries_368_){
_start:
{
size_t v_depth_boxed_369_; lean_object* v_res_370_; 
v_depth_boxed_369_ = lean_unbox_usize(v_depth_364_);
lean_dec(v_depth_364_);
v_res_370_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(v_depth_boxed_369_, v_keys_365_, v_vals_366_, v_i_367_, v_entries_368_);
lean_dec_ref(v_vals_366_);
lean_dec_ref(v_keys_365_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg___boxed(lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_x_373_, lean_object* v_x_374_, lean_object* v_x_375_){
_start:
{
size_t v_x_27476__boxed_376_; size_t v_x_27477__boxed_377_; lean_object* v_res_378_; 
v_x_27476__boxed_376_ = lean_unbox_usize(v_x_372_);
lean_dec(v_x_372_);
v_x_27477__boxed_377_ = lean_unbox_usize(v_x_373_);
lean_dec(v_x_373_);
v_res_378_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_371_, v_x_27476__boxed_376_, v_x_27477__boxed_377_, v_x_374_, v_x_375_);
return v_res_378_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5___redArg(lean_object* v_x_379_, lean_object* v_x_380_, lean_object* v_x_381_){
_start:
{
uint64_t v___x_382_; size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; 
v___x_382_ = l_Lean_instHashableMVarId_hash(v_x_380_);
v___x_383_ = lean_uint64_to_usize(v___x_382_);
v___x_384_ = ((size_t)1ULL);
v___x_385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_379_, v___x_383_, v___x_384_, v_x_380_, v_x_381_);
return v___x_385_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(lean_object* v_mvarId_386_, lean_object* v_val_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; lean_object* v_mctx_391_; lean_object* v_cache_392_; lean_object* v_zetaDeltaFVarIds_393_; lean_object* v_postponed_394_; lean_object* v_diag_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_425_; 
v___x_390_ = lean_st_ref_take(v___y_388_);
v_mctx_391_ = lean_ctor_get(v___x_390_, 0);
v_cache_392_ = lean_ctor_get(v___x_390_, 1);
v_zetaDeltaFVarIds_393_ = lean_ctor_get(v___x_390_, 2);
v_postponed_394_ = lean_ctor_get(v___x_390_, 3);
v_diag_395_ = lean_ctor_get(v___x_390_, 4);
v_isSharedCheck_425_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_425_ == 0)
{
v___x_397_ = v___x_390_;
v_isShared_398_ = v_isSharedCheck_425_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_diag_395_);
lean_inc(v_postponed_394_);
lean_inc(v_zetaDeltaFVarIds_393_);
lean_inc(v_cache_392_);
lean_inc(v_mctx_391_);
lean_dec(v___x_390_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_425_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v_depth_399_; lean_object* v_levelAssignDepth_400_; lean_object* v_lmvarCounter_401_; lean_object* v_mvarCounter_402_; lean_object* v_lDecls_403_; lean_object* v_decls_404_; lean_object* v_userNames_405_; lean_object* v_lAssignment_406_; lean_object* v_eAssignment_407_; lean_object* v_dAssignment_408_; lean_object* v_instanceTypedMVars_409_; lean_object* v_synthNormMemo_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_424_; 
v_depth_399_ = lean_ctor_get(v_mctx_391_, 0);
v_levelAssignDepth_400_ = lean_ctor_get(v_mctx_391_, 1);
v_lmvarCounter_401_ = lean_ctor_get(v_mctx_391_, 2);
v_mvarCounter_402_ = lean_ctor_get(v_mctx_391_, 3);
v_lDecls_403_ = lean_ctor_get(v_mctx_391_, 4);
v_decls_404_ = lean_ctor_get(v_mctx_391_, 5);
v_userNames_405_ = lean_ctor_get(v_mctx_391_, 6);
v_lAssignment_406_ = lean_ctor_get(v_mctx_391_, 7);
v_eAssignment_407_ = lean_ctor_get(v_mctx_391_, 8);
v_dAssignment_408_ = lean_ctor_get(v_mctx_391_, 9);
v_instanceTypedMVars_409_ = lean_ctor_get(v_mctx_391_, 10);
v_synthNormMemo_410_ = lean_ctor_get(v_mctx_391_, 11);
v_isSharedCheck_424_ = !lean_is_exclusive(v_mctx_391_);
if (v_isSharedCheck_424_ == 0)
{
v___x_412_ = v_mctx_391_;
v_isShared_413_ = v_isSharedCheck_424_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_synthNormMemo_410_);
lean_inc(v_instanceTypedMVars_409_);
lean_inc(v_dAssignment_408_);
lean_inc(v_eAssignment_407_);
lean_inc(v_lAssignment_406_);
lean_inc(v_userNames_405_);
lean_inc(v_decls_404_);
lean_inc(v_lDecls_403_);
lean_inc(v_mvarCounter_402_);
lean_inc(v_lmvarCounter_401_);
lean_inc(v_levelAssignDepth_400_);
lean_inc(v_depth_399_);
lean_dec(v_mctx_391_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_424_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_417_; 
v___x_414_ = lean_box(0);
v___x_415_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5___redArg(v_eAssignment_407_, v_mvarId_386_, v_val_387_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 8, v___x_415_);
v___x_417_ = v___x_412_;
goto v_reusejp_416_;
}
else
{
lean_object* v_reuseFailAlloc_423_; 
v_reuseFailAlloc_423_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_423_, 0, v_depth_399_);
lean_ctor_set(v_reuseFailAlloc_423_, 1, v_levelAssignDepth_400_);
lean_ctor_set(v_reuseFailAlloc_423_, 2, v_lmvarCounter_401_);
lean_ctor_set(v_reuseFailAlloc_423_, 3, v_mvarCounter_402_);
lean_ctor_set(v_reuseFailAlloc_423_, 4, v_lDecls_403_);
lean_ctor_set(v_reuseFailAlloc_423_, 5, v_decls_404_);
lean_ctor_set(v_reuseFailAlloc_423_, 6, v_userNames_405_);
lean_ctor_set(v_reuseFailAlloc_423_, 7, v_lAssignment_406_);
lean_ctor_set(v_reuseFailAlloc_423_, 8, v___x_415_);
lean_ctor_set(v_reuseFailAlloc_423_, 9, v_dAssignment_408_);
lean_ctor_set(v_reuseFailAlloc_423_, 10, v_instanceTypedMVars_409_);
lean_ctor_set(v_reuseFailAlloc_423_, 11, v_synthNormMemo_410_);
v___x_417_ = v_reuseFailAlloc_423_;
goto v_reusejp_416_;
}
v_reusejp_416_:
{
lean_object* v___x_419_; 
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_417_);
v___x_419_ = v___x_397_;
goto v_reusejp_418_;
}
else
{
lean_object* v_reuseFailAlloc_422_; 
v_reuseFailAlloc_422_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_422_, 0, v___x_417_);
lean_ctor_set(v_reuseFailAlloc_422_, 1, v_cache_392_);
lean_ctor_set(v_reuseFailAlloc_422_, 2, v_zetaDeltaFVarIds_393_);
lean_ctor_set(v_reuseFailAlloc_422_, 3, v_postponed_394_);
lean_ctor_set(v_reuseFailAlloc_422_, 4, v_diag_395_);
v___x_419_ = v_reuseFailAlloc_422_;
goto v_reusejp_418_;
}
v_reusejp_418_:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = lean_st_ref_put(v___y_388_, v___x_419_);
v___x_421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_421_, 0, v___x_414_);
return v___x_421_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_386_ = stack[0].m_obj;
lean_object* v_val_387_ = stack[1].m_obj;
lean_object* v___y_388_ = stack[2].m_obj;
lean_object* v_res_426_;
v_res_426_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_mvarId_386_, v_val_387_, v___y_388_);
stack->m_obj
 = v_res_426_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg___boxed(lean_object* v_mvarId_427_, lean_object* v_val_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_mvarId_427_, v_val_428_, v___y_429_);
lean_dec(v___y_429_);
return v_res_431_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(lean_object* v_fst_432_, lean_object* v_fst_433_, lean_object* v_n_434_, lean_object* v_i_435_, lean_object* v_a_436_){
_start:
{
lean_object* v_zero_438_; uint8_t v_isZero_439_; 
v_zero_438_ = lean_unsigned_to_nat(0u);
v_isZero_439_ = lean_nat_dec_eq(v_i_435_, v_zero_438_);
if (v_isZero_439_ == 1)
{
lean_object* v___x_440_; 
lean_dec(v_i_435_);
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_a_436_);
return v___x_440_;
}
else
{
lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v_one_443_; lean_object* v_n_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_441_ = lean_unsigned_to_nat(2u);
v___x_442_ = lean_box(0);
v_one_443_ = lean_unsigned_to_nat(1u);
v_n_444_ = lean_nat_sub(v_i_435_, v_one_443_);
lean_dec(v_i_435_);
v___x_445_ = lean_nat_sub(v_n_434_, v_n_444_);
v___x_446_ = lean_nat_sub(v___x_445_, v_one_443_);
lean_dec(v___x_445_);
v___x_447_ = lean_nat_add(v___x_446_, v___x_441_);
v___x_448_ = lean_array_get_borrowed(v___x_442_, v_fst_432_, v___x_447_);
lean_dec(v___x_447_);
v___x_449_ = lean_array_fget_borrowed(v_fst_433_, v___x_446_);
lean_dec(v___x_446_);
lean_inc(v___x_449_);
v___x_450_ = l_Lean_mkFVar(v___x_449_);
lean_inc(v___x_448_);
v___x_451_ = l_Lean_Meta_FVarSubst_insert(v_a_436_, v___x_448_, v___x_450_);
v_i_435_ = v_n_444_;
v_a_436_ = v___x_451_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_432_ = stack[0].m_obj;
lean_object* v_fst_433_ = stack[1].m_obj;
lean_object* v_n_434_ = stack[2].m_obj;
lean_object* v_i_435_ = stack[3].m_obj;
lean_object* v_a_436_ = stack[4].m_obj;
lean_object* v_res_453_;
v_res_453_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_432_, v_fst_433_, v_n_434_, v_i_435_, v_a_436_);
stack->m_obj
 = v_res_453_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg___boxed(lean_object* v_fst_454_, lean_object* v_fst_455_, lean_object* v_n_456_, lean_object* v_i_457_, lean_object* v_a_458_, lean_object* v___y_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_454_, v_fst_455_, v_n_456_, v_i_457_, v_a_458_);
lean_dec(v_n_456_);
lean_dec_ref(v_fst_455_);
lean_dec_ref(v_fst_454_);
return v_res_460_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0(lean_object* v_k_461_, lean_object* v_b_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
lean_inc(v___y_466_);
lean_inc_ref(v___y_465_);
lean_inc(v___y_464_);
lean_inc_ref(v___y_463_);
v___x_468_ = lean_apply_6(v_k_461_, v_b_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, lean_box(0));
return v___x_468_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_461_ = stack[0].m_obj;
lean_object* v_b_462_ = stack[1].m_obj;
lean_object* v___y_463_ = stack[2].m_obj;
lean_object* v___y_464_ = stack[3].m_obj;
lean_object* v___y_465_ = stack[4].m_obj;
lean_object* v___y_466_ = stack[5].m_obj;
lean_object* v_res_469_;
v_res_469_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0(v_k_461_, v_b_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
stack->m_obj
 = v_res_469_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_470_, lean_object* v_b_471_, lean_object* v___y_472_, lean_object* v___y_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_){
_start:
{
lean_object* v_res_477_; 
v_res_477_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0(v_k_470_, v_b_471_, v___y_472_, v___y_473_, v___y_474_, v___y_475_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
lean_dec(v___y_473_);
lean_dec_ref(v___y_472_);
return v_res_477_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(lean_object* v_name_478_, uint8_t v_bi_479_, lean_object* v_type_480_, lean_object* v_k_481_, uint8_t v_kind_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
lean_object* v___f_488_; lean_object* v___x_489_; 
v___f_488_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_488_, 0, v_k_481_);
v___x_489_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_478_, v_bi_479_, v_type_480_, v___f_488_, v_kind_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_489_) == 0)
{
lean_object* v_a_490_; lean_object* v___x_492_; uint8_t v_isShared_493_; uint8_t v_isSharedCheck_497_; 
v_a_490_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_497_ == 0)
{
v___x_492_ = v___x_489_;
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
else
{
lean_inc(v_a_490_);
lean_dec(v___x_489_);
v___x_492_ = lean_box(0);
v_isShared_493_ = v_isSharedCheck_497_;
goto v_resetjp_491_;
}
v_resetjp_491_:
{
lean_object* v___x_495_; 
if (v_isShared_493_ == 0)
{
v___x_495_ = v___x_492_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_a_490_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
else
{
lean_object* v_a_498_; lean_object* v___x_500_; uint8_t v_isShared_501_; uint8_t v_isSharedCheck_505_; 
v_a_498_ = lean_ctor_get(v___x_489_, 0);
v_isSharedCheck_505_ = !lean_is_exclusive(v___x_489_);
if (v_isSharedCheck_505_ == 0)
{
v___x_500_ = v___x_489_;
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
else
{
lean_inc(v_a_498_);
lean_dec(v___x_489_);
v___x_500_ = lean_box(0);
v_isShared_501_ = v_isSharedCheck_505_;
goto v_resetjp_499_;
}
v_resetjp_499_:
{
lean_object* v___x_503_; 
if (v_isShared_501_ == 0)
{
v___x_503_ = v___x_500_;
goto v_reusejp_502_;
}
else
{
lean_object* v_reuseFailAlloc_504_; 
v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_504_, 0, v_a_498_);
v___x_503_ = v_reuseFailAlloc_504_;
goto v_reusejp_502_;
}
v_reusejp_502_:
{
return v___x_503_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_478_ = stack[0].m_obj;
uint8_t v_bi_479_ = stack[1].m_num;
lean_object* v_type_480_ = stack[2].m_obj;
lean_object* v_k_481_ = stack[3].m_obj;
uint8_t v_kind_482_ = stack[4].m_num;
lean_object* v___y_483_ = stack[5].m_obj;
lean_object* v___y_484_ = stack[6].m_obj;
lean_object* v___y_485_ = stack[7].m_obj;
lean_object* v___y_486_ = stack[8].m_obj;
lean_object* v_res_506_;
v_res_506_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_478_, v_bi_479_, v_type_480_, v_k_481_, v_kind_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
stack->m_obj
 = v_res_506_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___boxed(lean_object* v_name_507_, lean_object* v_bi_508_, lean_object* v_type_509_, lean_object* v_k_510_, lean_object* v_kind_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
uint8_t v_bi_boxed_517_; uint8_t v_kind_boxed_518_; lean_object* v_res_519_; 
v_bi_boxed_517_ = lean_unbox(v_bi_508_);
v_kind_boxed_518_ = lean_unbox(v_kind_511_);
v_res_519_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_507_, v_bi_boxed_517_, v_type_509_, v_k_510_, v_kind_boxed_518_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
return v_res_519_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(lean_object* v_name_520_, lean_object* v_type_521_, lean_object* v_k_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_){
_start:
{
uint8_t v___x_528_; uint8_t v___x_529_; lean_object* v___x_530_; 
v___x_528_ = 0;
v___x_529_ = 0;
v___x_530_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_520_, v___x_528_, v_type_521_, v_k_522_, v___x_529_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
return v___x_530_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_520_ = stack[0].m_obj;
lean_object* v_type_521_ = stack[1].m_obj;
lean_object* v_k_522_ = stack[2].m_obj;
lean_object* v___y_523_ = stack[3].m_obj;
lean_object* v___y_524_ = stack[4].m_obj;
lean_object* v___y_525_ = stack[5].m_obj;
lean_object* v___y_526_ = stack[6].m_obj;
lean_object* v_res_531_;
v_res_531_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v_name_520_, v_type_521_, v_k_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_);
stack->m_obj
 = v_res_531_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object* v_name_532_, lean_object* v_type_533_, lean_object* v_k_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v_name_532_, v_type_533_, v_k_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
return v_res_540_;
}
}
lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(lean_object* v_msgData_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
lean_object* v___x_547_; lean_object* v_env_548_; uint8_t v___x_549_; lean_object* v_env_550_; lean_object* v___x_551_; lean_object* v_toCold_552_; lean_object* v_mctx_553_; lean_object* v_lctx_554_; lean_object* v_options_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_547_ = lean_st_ref_get(v___y_545_);
v_env_548_ = lean_ctor_get(v___x_547_, 0);
lean_inc_ref(v_env_548_);
lean_dec(v___x_547_);
v___x_549_ = 0;
v_env_550_ = l_Lean_Environment_setRecordingDeps(v_env_548_, v___x_549_);
v___x_551_ = lean_st_ref_get(v___y_543_);
v_toCold_552_ = lean_ctor_get(v___y_544_, 0);
v_mctx_553_ = lean_ctor_get(v___x_551_, 0);
lean_inc_ref(v_mctx_553_);
lean_dec(v___x_551_);
v_lctx_554_ = lean_ctor_get(v___y_542_, 2);
v_options_555_ = lean_ctor_get(v_toCold_552_, 2);
lean_inc_ref(v_options_555_);
lean_inc_ref(v_lctx_554_);
v___x_556_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_556_, 0, v_env_550_);
lean_ctor_set(v___x_556_, 1, v_mctx_553_);
lean_ctor_set(v___x_556_, 2, v_lctx_554_);
lean_ctor_set(v___x_556_, 3, v_options_555_);
v___x_557_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_557_, 0, v___x_556_);
lean_ctor_set(v___x_557_, 1, v_msgData_541_);
v___x_558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_558_, 0, v___x_557_);
return v___x_558_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_541_ = stack[0].m_obj;
lean_object* v___y_542_ = stack[1].m_obj;
lean_object* v___y_543_ = stack[2].m_obj;
lean_object* v___y_544_ = stack[3].m_obj;
lean_object* v___y_545_ = stack[4].m_obj;
lean_object* v_res_559_;
v_res_559_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msgData_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
stack->m_obj
 = v_res_559_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2___boxed(lean_object* v_msgData_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v_res_566_; 
v_res_566_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msgData_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_);
lean_dec(v___y_564_);
lean_dec_ref(v___y_563_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
return v_res_566_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0(void){
_start:
{
lean_object* v___x_567_; double v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = lean_float_of_nat(v___x_567_);
return v___x_568_;
}
}
lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(lean_object* v_cls_572_, lean_object* v_msg_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_){
_start:
{
lean_object* v_ref_579_; lean_object* v___x_580_; lean_object* v_a_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_626_; 
v_ref_579_ = lean_ctor_get(v___y_576_, 2);
v___x_580_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msg_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
v_a_581_ = lean_ctor_get(v___x_580_, 0);
v_isSharedCheck_626_ = !lean_is_exclusive(v___x_580_);
if (v_isSharedCheck_626_ == 0)
{
v___x_583_ = v___x_580_;
v_isShared_584_ = v_isSharedCheck_626_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_a_581_);
lean_dec(v___x_580_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_626_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v_traceState_586_; lean_object* v_env_587_; lean_object* v_nextMacroScope_588_; lean_object* v_ngen_589_; lean_object* v_auxDeclNGen_590_; lean_object* v_cache_591_; lean_object* v_recordedDeps_592_; lean_object* v_messages_593_; lean_object* v_infoState_594_; lean_object* v_snapshotTasks_595_; lean_object* v___x_597_; uint8_t v_isShared_598_; uint8_t v_isSharedCheck_625_; 
v___x_585_ = lean_st_ref_take(v___y_577_);
v_traceState_586_ = lean_ctor_get(v___x_585_, 4);
v_env_587_ = lean_ctor_get(v___x_585_, 0);
v_nextMacroScope_588_ = lean_ctor_get(v___x_585_, 1);
v_ngen_589_ = lean_ctor_get(v___x_585_, 2);
v_auxDeclNGen_590_ = lean_ctor_get(v___x_585_, 3);
v_cache_591_ = lean_ctor_get(v___x_585_, 5);
v_recordedDeps_592_ = lean_ctor_get(v___x_585_, 6);
v_messages_593_ = lean_ctor_get(v___x_585_, 7);
v_infoState_594_ = lean_ctor_get(v___x_585_, 8);
v_snapshotTasks_595_ = lean_ctor_get(v___x_585_, 9);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_585_);
if (v_isSharedCheck_625_ == 0)
{
v___x_597_ = v___x_585_;
v_isShared_598_ = v_isSharedCheck_625_;
goto v_resetjp_596_;
}
else
{
lean_inc(v_snapshotTasks_595_);
lean_inc(v_infoState_594_);
lean_inc(v_messages_593_);
lean_inc(v_recordedDeps_592_);
lean_inc(v_cache_591_);
lean_inc(v_traceState_586_);
lean_inc(v_auxDeclNGen_590_);
lean_inc(v_ngen_589_);
lean_inc(v_nextMacroScope_588_);
lean_inc(v_env_587_);
lean_dec(v___x_585_);
v___x_597_ = lean_box(0);
v_isShared_598_ = v_isSharedCheck_625_;
goto v_resetjp_596_;
}
v_resetjp_596_:
{
uint64_t v_tid_599_; lean_object* v_traces_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_624_; 
v_tid_599_ = lean_ctor_get_uint64(v_traceState_586_, sizeof(void*)*1);
v_traces_600_ = lean_ctor_get(v_traceState_586_, 0);
v_isSharedCheck_624_ = !lean_is_exclusive(v_traceState_586_);
if (v_isSharedCheck_624_ == 0)
{
v___x_602_ = v_traceState_586_;
v_isShared_603_ = v_isSharedCheck_624_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_traces_600_);
lean_dec(v_traceState_586_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_624_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; double v___x_606_; uint8_t v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_615_; 
v___x_604_ = lean_box(0);
v___x_605_ = lean_box(0);
v___x_606_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0);
v___x_607_ = 0;
v___x_608_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__1));
v___x_609_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_609_, 0, v_cls_572_);
lean_ctor_set(v___x_609_, 1, v___x_605_);
lean_ctor_set(v___x_609_, 2, v___x_608_);
lean_ctor_set_float(v___x_609_, sizeof(void*)*3, v___x_606_);
lean_ctor_set_float(v___x_609_, sizeof(void*)*3 + 8, v___x_606_);
lean_ctor_set_uint8(v___x_609_, sizeof(void*)*3 + 16, v___x_607_);
v___x_610_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__2));
v___x_611_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_611_, 0, v___x_609_);
lean_ctor_set(v___x_611_, 1, v_a_581_);
lean_ctor_set(v___x_611_, 2, v___x_610_);
lean_inc(v_ref_579_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v_ref_579_);
lean_ctor_set(v___x_612_, 1, v___x_611_);
v___x_613_ = l_Lean_PersistentArray_push___redArg(v_traces_600_, v___x_612_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_613_);
v___x_615_ = v___x_602_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_613_);
lean_ctor_set_uint64(v_reuseFailAlloc_623_, sizeof(void*)*1, v_tid_599_);
v___x_615_ = v_reuseFailAlloc_623_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
lean_object* v___x_617_; 
if (v_isShared_598_ == 0)
{
lean_ctor_set(v___x_597_, 4, v___x_615_);
v___x_617_ = v___x_597_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_env_587_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_nextMacroScope_588_);
lean_ctor_set(v_reuseFailAlloc_622_, 2, v_ngen_589_);
lean_ctor_set(v_reuseFailAlloc_622_, 3, v_auxDeclNGen_590_);
lean_ctor_set(v_reuseFailAlloc_622_, 4, v___x_615_);
lean_ctor_set(v_reuseFailAlloc_622_, 5, v_cache_591_);
lean_ctor_set(v_reuseFailAlloc_622_, 6, v_recordedDeps_592_);
lean_ctor_set(v_reuseFailAlloc_622_, 7, v_messages_593_);
lean_ctor_set(v_reuseFailAlloc_622_, 8, v_infoState_594_);
lean_ctor_set(v_reuseFailAlloc_622_, 9, v_snapshotTasks_595_);
v___x_617_ = v_reuseFailAlloc_622_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_618_; lean_object* v___x_620_; 
v___x_618_ = lean_st_ref_put(v___y_577_, v___x_617_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_604_);
v___x_620_ = v___x_583_;
goto v_reusejp_619_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_604_);
v___x_620_ = v_reuseFailAlloc_621_;
goto v_reusejp_619_;
}
v_reusejp_619_:
{
return v___x_620_;
}
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_cls_572_ = stack[0].m_obj;
lean_object* v_msg_573_ = stack[1].m_obj;
lean_object* v___y_574_ = stack[2].m_obj;
lean_object* v___y_575_ = stack[3].m_obj;
lean_object* v___y_576_ = stack[4].m_obj;
lean_object* v___y_577_ = stack[5].m_obj;
lean_object* v_res_627_;
v_res_627_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v_cls_572_, v_msg_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_);
stack->m_obj
 = v_res_627_;
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___boxed(lean_object* v_cls_628_, lean_object* v_msg_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v_cls_628_, v_msg_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
lean_dec(v___y_631_);
lean_dec_ref(v___y_630_);
return v_res_635_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__2));
v___x_641_ = l_Lean_stringToMessageData(v___x_640_);
return v___x_641_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__5(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__4));
v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__11(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_651_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__10));
v___x_652_ = lean_unsigned_to_nat(22u);
v___x_653_ = lean_unsigned_to_nat(64u);
v___x_654_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__9));
v___x_655_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__8));
v___x_656_ = l_mkPanicMessageWithDecl(v___x_655_, v___x_654_, v___x_653_, v___x_652_, v___x_651_);
return v___x_656_;
}
}
lean_object* l_Lean_Meta_substCore___lam__1(lean_object* v_fvarId_657_, lean_object* v_hFVarId_658_, lean_object* v___x_659_, lean_object* v_fst_660_, lean_object* v_fvarSubst_661_, uint8_t v_clearH_662_, lean_object* v___x_663_, lean_object* v___x_664_, lean_object* v___x_665_, uint8_t v_skip_666_, uint8_t v___x_667_, lean_object* v___x_668_, lean_object* v_snd_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v_a_672_, uint8_t v_symm_673_, uint8_t v___x_674_, lean_object* v___x_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_){
_start:
{
lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_698_; lean_object* v_mvarId_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v_newVal_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; uint8_t v___y_782_; lean_object* v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v_major_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; uint8_t v___y_823_; lean_object* v___y_824_; lean_object* v_motive_825_; lean_object* v_newType_826_; lean_object* v___x_837_; 
lean_inc(v_snd_669_);
v___x_837_ = l_Lean_MVarId_getDecl(v_snd_669_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; lean_object* v_type_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___f_842_; lean_object* v___x_843_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref_known(v___x_837_, 1);
v_type_839_ = lean_ctor_get(v_a_838_, 2);
lean_inc_ref_n(v_type_839_, 2);
lean_dec(v_a_838_);
v___x_840_ = lean_box(v___x_674_);
v___x_841_ = lean_box(v___x_667_);
lean_inc_ref(v___x_663_);
lean_inc(v___x_664_);
lean_inc_ref(v___x_659_);
v___f_842_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__0___boxed), 12, 6);
lean_closure_set(v___f_842_, 0, v_type_839_);
lean_closure_set(v___f_842_, 1, v___x_659_);
lean_closure_set(v___f_842_, 2, v___x_664_);
lean_closure_set(v___f_842_, 3, v___x_663_);
lean_closure_set(v___f_842_, 4, v___x_840_);
lean_closure_set(v___f_842_, 5, v___x_841_);
lean_inc(v___x_670_);
v___x_843_ = l_Lean_FVarId_getDecl___redArg(v___x_670_, v___y_676_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = l_Lean_LocalDecl_type(v_a_844_);
lean_dec(v_a_844_);
v___x_846_ = l_Lean_Meta_matchEq_x3f(v___x_845_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; lean_object* v___y_849_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
if (lean_obj_tag(v_a_847_) == 0)
{
lean_object* v___x_919_; lean_object* v___x_920_; 
lean_dec_ref(v___f_842_);
lean_dec_ref(v_type_839_);
lean_dec(v_a_672_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v___x_919_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__11, &l_Lean_Meta_substCore___lam__1___closed__11_once, _init_l_Lean_Meta_substCore___lam__1___closed__11);
v___x_920_ = l_panic___at___00Lean_Meta_substCore_spec__6(v___x_919_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
return v___x_920_;
}
else
{
lean_object* v_val_921_; lean_object* v_snd_922_; 
v_val_921_ = lean_ctor_get(v_a_847_, 0);
lean_inc(v_val_921_);
lean_dec_ref_known(v_a_847_, 1);
v_snd_922_ = lean_ctor_get(v_val_921_, 1);
lean_inc(v_snd_922_);
lean_dec(v_val_921_);
if (v_symm_673_ == 0)
{
lean_object* v_snd_923_; 
v_snd_923_ = lean_ctor_get(v_snd_922_, 1);
lean_inc(v_snd_923_);
lean_dec(v_snd_922_);
v___y_849_ = v_snd_923_;
goto v___jp_848_;
}
else
{
lean_object* v_fst_924_; 
v_fst_924_ = lean_ctor_get(v_snd_922_, 0);
lean_inc(v_fst_924_);
lean_dec(v_snd_922_);
v___y_849_ = v_fst_924_;
goto v___jp_848_;
}
}
v___jp_848_:
{
lean_object* v___x_850_; lean_object* v_a_851_; lean_object* v___x_852_; lean_object* v_a_853_; uint8_t v___x_854_; 
v___x_850_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_849_, v___y_677_);
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref(v___x_850_);
lean_inc(v___x_670_);
lean_inc_ref(v_type_839_);
v___x_852_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_type_839_, v___x_670_, v___y_677_);
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref(v___x_852_);
v___x_854_ = lean_unbox(v_a_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v___x_856_; uint8_t v___x_857_; lean_object* v___x_858_; 
lean_dec_ref(v___f_842_);
v___x_855_ = lean_mk_empty_array_with_capacity(v___x_675_);
lean_inc_ref(v___x_663_);
v___x_856_ = lean_array_push(v___x_855_, v___x_663_);
v___x_857_ = 1;
lean_inc_ref(v_type_839_);
v___x_858_ = l_Lean_Meta_mkLambdaFVars(v___x_856_, v_type_839_, v___x_674_, v___x_667_, v___x_674_, v___x_667_, v___x_857_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec_ref(v___x_856_);
if (lean_obj_tag(v___x_858_) == 0)
{
lean_object* v_a_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref_known(v___x_858_, 1);
lean_inc_ref(v___x_663_);
v___x_860_ = l_Lean_Expr_replaceFVar(v_type_839_, v___x_663_, v_a_851_);
lean_dec_ref(v_type_839_);
v___x_861_ = lean_unbox(v_a_853_);
lean_dec(v_a_853_);
v___y_823_ = v___x_861_;
v___y_824_ = v_a_851_;
v_motive_825_ = v_a_859_;
v_newType_826_ = v___x_860_;
goto v___jp_822_;
}
else
{
lean_object* v_a_862_; lean_object* v___x_864_; uint8_t v_isShared_865_; uint8_t v_isSharedCheck_869_; 
lean_dec(v_a_853_);
lean_dec(v_a_851_);
lean_dec_ref(v_type_839_);
lean_dec(v_a_672_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_862_ = lean_ctor_get(v___x_858_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_858_);
if (v_isSharedCheck_869_ == 0)
{
v___x_864_ = v___x_858_;
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
else
{
lean_inc(v_a_862_);
lean_dec(v___x_858_);
v___x_864_ = lean_box(0);
v_isShared_865_ = v_isSharedCheck_869_;
goto v_resetjp_863_;
}
v_resetjp_863_:
{
lean_object* v___x_867_; 
if (v_isShared_865_ == 0)
{
v___x_867_ = v___x_864_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_a_862_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_object* v___x_870_; lean_object* v___x_871_; 
lean_inc_ref(v___x_663_);
v___x_870_ = l_Lean_Expr_replaceFVar(v_type_839_, v___x_663_, v_a_851_);
lean_inc(v_a_851_);
v___x_871_ = l_Lean_Meta_mkEqRefl(v_a_851_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_871_) == 0)
{
lean_object* v_a_872_; lean_object* v___x_873_; 
v_a_872_ = lean_ctor_get(v___x_871_, 0);
lean_inc(v_a_872_);
lean_dec_ref_known(v___x_871_, 1);
lean_inc_ref(v___x_659_);
v___x_873_ = l_Lean_Expr_replaceFVar(v___x_870_, v___x_659_, v_a_872_);
lean_dec(v_a_872_);
lean_dec_ref(v___x_870_);
if (v_symm_673_ == 0)
{
lean_object* v___x_874_; 
lean_dec_ref(v_type_839_);
lean_inc_ref(v___x_663_);
lean_inc(v_a_851_);
v___x_874_ = l_Lean_Meta_mkEq(v_a_851_, v___x_663_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; lean_object* v___x_877_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref_known(v___x_874_, 1);
v___x_876_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__7));
v___x_877_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v___x_876_, v_a_875_, v___f_842_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_877_) == 0)
{
lean_object* v_a_878_; uint8_t v___x_879_; 
v_a_878_ = lean_ctor_get(v___x_877_, 0);
lean_inc(v_a_878_);
lean_dec_ref_known(v___x_877_, 1);
v___x_879_ = lean_unbox(v_a_853_);
lean_dec(v_a_853_);
v___y_823_ = v___x_879_;
v___y_824_ = v_a_851_;
v_motive_825_ = v_a_878_;
v_newType_826_ = v___x_873_;
goto v___jp_822_;
}
else
{
lean_object* v_a_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_887_; 
lean_dec_ref(v___x_873_);
lean_dec(v_a_853_);
lean_dec(v_a_851_);
lean_dec(v_a_672_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_880_ = lean_ctor_get(v___x_877_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v___x_877_);
if (v_isSharedCheck_887_ == 0)
{
v___x_882_ = v___x_877_;
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_a_880_);
lean_dec(v___x_877_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_887_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v___x_885_; 
if (v_isShared_883_ == 0)
{
v___x_885_ = v___x_882_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v_a_880_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v___x_873_);
lean_dec(v_a_853_);
lean_dec(v_a_851_);
lean_dec_ref(v___f_842_);
lean_dec(v_a_672_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_888_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_874_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_874_);
v___x_890_ = lean_box(0);
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
v_resetjp_889_:
{
lean_object* v___x_893_; 
if (v_isShared_891_ == 0)
{
v___x_893_ = v___x_890_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_a_888_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
}
}
else
{
lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; lean_object* v___x_900_; 
lean_dec_ref(v___f_842_);
v___x_896_ = lean_mk_empty_array_with_capacity(v___x_664_);
lean_inc_ref(v___x_663_);
v___x_897_ = lean_array_push(v___x_896_, v___x_663_);
lean_inc_ref(v___x_659_);
v___x_898_ = lean_array_push(v___x_897_, v___x_659_);
v___x_899_ = 1;
v___x_900_ = l_Lean_Meta_mkLambdaFVars(v___x_898_, v_type_839_, v___x_674_, v___x_667_, v___x_674_, v___x_667_, v___x_899_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
lean_dec_ref(v___x_898_);
if (lean_obj_tag(v___x_900_) == 0)
{
lean_object* v_a_901_; uint8_t v___x_902_; 
v_a_901_ = lean_ctor_get(v___x_900_, 0);
lean_inc(v_a_901_);
lean_dec_ref_known(v___x_900_, 1);
v___x_902_ = lean_unbox(v_a_853_);
lean_dec(v_a_853_);
v___y_823_ = v___x_902_;
v___y_824_ = v_a_851_;
v_motive_825_ = v_a_901_;
v_newType_826_ = v___x_873_;
goto v___jp_822_;
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v___x_873_);
lean_dec(v_a_853_);
lean_dec(v_a_851_);
lean_dec(v_a_672_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
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
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v___x_870_);
lean_dec(v_a_853_);
lean_dec(v_a_851_);
lean_dec_ref(v___f_842_);
lean_dec_ref(v_type_839_);
lean_dec(v_a_672_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_911_ = lean_ctor_get(v___x_871_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_871_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_871_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_871_);
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
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v___f_842_);
lean_dec_ref(v_type_839_);
lean_dec(v_a_672_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_925_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_846_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_846_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v___x_930_; 
if (v_isShared_928_ == 0)
{
v___x_930_ = v___x_927_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v_a_925_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec_ref(v___f_842_);
lean_dec_ref(v_type_839_);
lean_dec(v_a_672_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_933_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_843_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_843_);
v___x_935_ = lean_box(0);
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
v_resetjp_934_:
{
lean_object* v___x_938_; 
if (v_isShared_936_ == 0)
{
v___x_938_ = v___x_935_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v_a_933_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
}
else
{
lean_object* v_a_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_948_; 
lean_dec(v_a_672_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_941_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_837_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_837_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_946_; 
if (v_isShared_944_ == 0)
{
v___x_946_ = v___x_943_;
goto v_reusejp_945_;
}
else
{
lean_object* v_reuseFailAlloc_947_; 
v_reuseFailAlloc_947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_947_, 0, v_a_941_);
v___x_946_ = v_reuseFailAlloc_947_;
goto v_reusejp_945_;
}
v_reusejp_945_:
{
return v___x_946_;
}
}
}
v___jp_681_:
{
lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_685_ = l_Lean_Meta_FVarSubst_insert(v___y_682_, v_fvarId_657_, v___y_684_);
v___x_686_ = l_Lean_Meta_FVarSubst_insert(v___x_685_, v_hFVarId_658_, v___x_659_);
v___x_687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
lean_ctor_set(v___x_687_, 1, v___y_683_);
v___x_688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
return v___x_688_;
}
v___jp_689_:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = lean_array_get_size(v___y_691_);
v___x_694_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_660_, v___y_691_, v___x_693_, v___x_693_, v_fvarSubst_661_);
lean_dec_ref(v___y_691_);
if (v_clearH_662_ == 0)
{
lean_object* v_a_695_; 
lean_dec_ref(v___y_692_);
v_a_695_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_694_);
v___y_682_ = v_a_695_;
v___y_683_ = v___y_690_;
v___y_684_ = v___x_663_;
goto v___jp_681_;
}
else
{
lean_object* v_a_696_; 
lean_dec_ref(v___x_663_);
v_a_696_ = lean_ctor_get(v___x_694_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v___x_694_);
v___y_682_ = v_a_696_;
v___y_683_ = v___y_690_;
v___y_684_ = v___y_692_;
goto v___jp_681_;
}
}
v___jp_697_:
{
lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; 
v___x_704_ = lean_array_get_size(v_fst_660_);
v___x_705_ = lean_nat_sub(v___x_704_, v___x_664_);
lean_dec(v___x_664_);
lean_inc(v___x_705_);
v___x_706_ = l_Lean_Meta_introNCore(v_mvarId_699_, v___x_705_, v___x_665_, v_skip_666_, v___x_667_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v_toCold_708_; lean_object* v_options_709_; uint8_t v_hasTrace_710_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
lean_inc(v_a_707_);
lean_dec_ref_known(v___x_706_, 1);
v_toCold_708_ = lean_ctor_get(v___y_702_, 0);
v_options_709_ = lean_ctor_get(v_toCold_708_, 2);
v_hasTrace_710_ = lean_ctor_get_uint8(v_options_709_, sizeof(void*)*1);
if (v_hasTrace_710_ == 0)
{
lean_object* v_fst_711_; lean_object* v_snd_712_; 
lean_dec(v___x_705_);
lean_dec(v___x_668_);
v_fst_711_ = lean_ctor_get(v_a_707_, 0);
lean_inc(v_fst_711_);
v_snd_712_ = lean_ctor_get(v_a_707_, 1);
lean_inc(v_snd_712_);
lean_dec(v_a_707_);
v___y_690_ = v_snd_712_;
v___y_691_ = v_fst_711_;
v___y_692_ = v___y_698_;
goto v___jp_689_;
}
else
{
lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_742_; 
v_fst_713_ = lean_ctor_get(v_a_707_, 0);
v_snd_714_ = lean_ctor_get(v_a_707_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_a_707_);
if (v_isSharedCheck_742_ == 0)
{
v___x_716_ = v_a_707_;
v_isShared_717_ = v_isSharedCheck_742_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_inc(v_fst_713_);
lean_dec(v_a_707_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_742_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_inheritedTraceOptions_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_inheritedTraceOptions_718_ = lean_ctor_get(v_toCold_708_, 11);
v___x_719_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
lean_inc(v___x_668_);
v___x_720_ = l_Lean_Name_append(v___x_719_, v___x_668_);
v___x_721_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_718_, v_options_709_, v___x_720_);
lean_dec(v___x_720_);
if (v___x_721_ == 0)
{
lean_del_object(v___x_716_);
lean_dec(v___x_705_);
lean_dec(v___x_668_);
v___y_690_ = v_snd_714_;
v___y_691_ = v_fst_713_;
v___y_692_ = v___y_698_;
goto v___jp_689_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_722_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__3, &l_Lean_Meta_substCore___lam__1___closed__3_once, _init_l_Lean_Meta_substCore___lam__1___closed__3);
v___x_723_ = l_Nat_reprFast(v___x_705_);
v___x_724_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_724_, 0, v___x_723_);
v___x_725_ = l_Lean_MessageData_ofFormat(v___x_724_);
if (v_isShared_717_ == 0)
{
lean_ctor_set_tag(v___x_716_, 7);
lean_ctor_set(v___x_716_, 1, v___x_725_);
lean_ctor_set(v___x_716_, 0, v___x_722_);
v___x_727_ = v___x_716_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v___x_722_);
lean_ctor_set(v_reuseFailAlloc_741_, 1, v___x_725_);
v___x_727_ = v_reuseFailAlloc_741_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; 
v___x_728_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__5, &l_Lean_Meta_substCore___lam__1___closed__5_once, _init_l_Lean_Meta_substCore___lam__1___closed__5);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
lean_inc(v_snd_714_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_snd_714_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_668_, v___x_731_, v___y_700_, v___y_701_, v___y_702_, v___y_703_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_dec_ref_known(v___x_732_, 1);
v___y_690_ = v_snd_714_;
v___y_691_ = v_fst_713_;
v___y_692_ = v___y_698_;
goto v___jp_689_;
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v_snd_714_);
lean_dec(v_fst_713_);
lean_dec_ref(v___y_698_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_733_ = lean_ctor_get(v___x_732_, 0);
v_isSharedCheck_740_ = !lean_is_exclusive(v___x_732_);
if (v_isSharedCheck_740_ == 0)
{
v___x_735_ = v___x_732_;
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_a_733_);
lean_dec(v___x_732_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_740_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v___x_738_; 
if (v_isShared_736_ == 0)
{
v___x_738_ = v___x_735_;
goto v_reusejp_737_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v_a_733_);
v___x_738_ = v_reuseFailAlloc_739_;
goto v_reusejp_737_;
}
v_reusejp_737_:
{
return v___x_738_;
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
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec(v___x_705_);
lean_dec_ref(v___y_698_);
lean_dec(v___x_668_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_743_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_706_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_706_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
if (v_isShared_746_ == 0)
{
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_749_; 
v_reuseFailAlloc_749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
v___x_748_ = v_reuseFailAlloc_749_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
return v___x_748_;
}
}
}
}
v___jp_751_:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_snd_669_, v_newVal_754_, v___y_756_);
lean_dec_ref(v___x_759_);
v___x_760_ = l_Lean_Expr_mvarId_x21(v___y_753_);
lean_dec_ref(v___y_753_);
if (v_clearH_662_ == 0)
{
lean_dec(v___x_671_);
lean_dec(v___x_670_);
v___y_698_ = v___y_752_;
v_mvarId_699_ = v___x_760_;
v___y_700_ = v___y_755_;
v___y_701_ = v___y_756_;
v___y_702_ = v___y_757_;
v___y_703_ = v___y_758_;
goto v___jp_697_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_MVarId_clear(v___x_760_, v___x_670_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = l_Lean_MVarId_clear(v_a_762_, v___x_671_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___y_698_ = v___y_752_;
v_mvarId_699_ = v_a_764_;
v___y_700_ = v___y_755_;
v___y_701_ = v___y_756_;
v___y_702_ = v___y_757_;
v___y_703_ = v___y_758_;
goto v___jp_697_;
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v___y_752_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_765_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_772_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_772_ == 0)
{
v___x_767_ = v___x_763_;
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
else
{
lean_inc(v_a_765_);
lean_dec(v___x_763_);
v___x_767_ = lean_box(0);
v_isShared_768_ = v_isSharedCheck_772_;
goto v_resetjp_766_;
}
v_resetjp_766_:
{
lean_object* v___x_770_; 
if (v_isShared_768_ == 0)
{
v___x_770_ = v___x_767_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_a_765_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec_ref(v___y_752_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_773_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_761_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_761_);
v___x_775_ = lean_box(0);
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
v_resetjp_774_:
{
lean_object* v___x_778_; 
if (v_isShared_776_ == 0)
{
v___x_778_ = v___x_775_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v_a_773_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
v___jp_781_:
{
lean_object* v___x_791_; 
v___x_791_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_783_, v_a_672_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
if (v___y_782_ == 0)
{
lean_object* v_a_792_; lean_object* v___x_793_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc_n(v_a_792_, 2);
lean_dec_ref_known(v___x_791_, 1);
v___x_793_ = l_Lean_Meta_mkEqNDRec(v___y_784_, v_a_792_, v_major_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_793_) == 0)
{
lean_object* v_a_794_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc(v_a_794_);
lean_dec_ref_known(v___x_793_, 1);
v___y_752_ = v___y_785_;
v___y_753_ = v_a_792_;
v_newVal_754_ = v_a_794_;
v___y_755_ = v___y_787_;
v___y_756_ = v___y_788_;
v___y_757_ = v___y_789_;
v___y_758_ = v___y_790_;
goto v___jp_751_;
}
else
{
lean_object* v_a_795_; lean_object* v___x_797_; uint8_t v_isShared_798_; uint8_t v_isSharedCheck_802_; 
lean_dec(v_a_792_);
lean_dec_ref(v___y_785_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_795_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_802_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_802_ == 0)
{
v___x_797_ = v___x_793_;
v_isShared_798_ = v_isSharedCheck_802_;
goto v_resetjp_796_;
}
else
{
lean_inc(v_a_795_);
lean_dec(v___x_793_);
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
else
{
lean_object* v_a_803_; lean_object* v___x_804_; 
v_a_803_ = lean_ctor_get(v___x_791_, 0);
lean_inc_n(v_a_803_, 2);
lean_dec_ref_known(v___x_791_, 1);
v___x_804_ = l_Lean_Meta_mkEqRec(v___y_784_, v_a_803_, v_major_786_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_804_) == 0)
{
lean_object* v_a_805_; 
v_a_805_ = lean_ctor_get(v___x_804_, 0);
lean_inc(v_a_805_);
lean_dec_ref_known(v___x_804_, 1);
v___y_752_ = v___y_785_;
v___y_753_ = v_a_803_;
v_newVal_754_ = v_a_805_;
v___y_755_ = v___y_787_;
v___y_756_ = v___y_788_;
v___y_757_ = v___y_789_;
v___y_758_ = v___y_790_;
goto v___jp_751_;
}
else
{
lean_object* v_a_806_; lean_object* v___x_808_; uint8_t v_isShared_809_; uint8_t v_isSharedCheck_813_; 
lean_dec(v_a_803_);
lean_dec_ref(v___y_785_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_806_ = lean_ctor_get(v___x_804_, 0);
v_isSharedCheck_813_ = !lean_is_exclusive(v___x_804_);
if (v_isSharedCheck_813_ == 0)
{
v___x_808_ = v___x_804_;
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
else
{
lean_inc(v_a_806_);
lean_dec(v___x_804_);
v___x_808_ = lean_box(0);
v_isShared_809_ = v_isSharedCheck_813_;
goto v_resetjp_807_;
}
v_resetjp_807_:
{
lean_object* v___x_811_; 
if (v_isShared_809_ == 0)
{
v___x_811_ = v___x_808_;
goto v_reusejp_810_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_a_806_);
v___x_811_ = v_reuseFailAlloc_812_;
goto v_reusejp_810_;
}
v_reusejp_810_:
{
return v___x_811_;
}
}
}
}
}
else
{
lean_object* v_a_814_; lean_object* v___x_816_; uint8_t v_isShared_817_; uint8_t v_isSharedCheck_821_; 
lean_dec_ref(v_major_786_);
lean_dec_ref(v___y_785_);
lean_dec_ref(v___y_784_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_814_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_821_ == 0)
{
v___x_816_ = v___x_791_;
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
else
{
lean_inc(v_a_814_);
lean_dec(v___x_791_);
v___x_816_ = lean_box(0);
v_isShared_817_ = v_isSharedCheck_821_;
goto v_resetjp_815_;
}
v_resetjp_815_:
{
lean_object* v___x_819_; 
if (v_isShared_817_ == 0)
{
v___x_819_ = v___x_816_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v_a_814_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
v___jp_822_:
{
if (v_symm_673_ == 0)
{
lean_object* v___x_827_; 
lean_inc_ref(v___x_659_);
v___x_827_ = l_Lean_Meta_mkEqSymm(v___x_659_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
if (lean_obj_tag(v___x_827_) == 0)
{
lean_object* v_a_828_; 
v_a_828_ = lean_ctor_get(v___x_827_, 0);
lean_inc(v_a_828_);
lean_dec_ref_known(v___x_827_, 1);
v___y_782_ = v___y_823_;
v___y_783_ = v_newType_826_;
v___y_784_ = v_motive_825_;
v___y_785_ = v___y_824_;
v_major_786_ = v_a_828_;
v___y_787_ = v___y_676_;
v___y_788_ = v___y_677_;
v___y_789_ = v___y_678_;
v___y_790_ = v___y_679_;
goto v___jp_781_;
}
else
{
lean_object* v_a_829_; lean_object* v___x_831_; uint8_t v_isShared_832_; uint8_t v_isSharedCheck_836_; 
lean_dec_ref(v_newType_826_);
lean_dec_ref(v_motive_825_);
lean_dec_ref(v___y_824_);
lean_dec(v_a_672_);
lean_dec(v___x_671_);
lean_dec(v___x_670_);
lean_dec(v_snd_669_);
lean_dec(v___x_668_);
lean_dec(v___x_665_);
lean_dec(v___x_664_);
lean_dec_ref(v___x_663_);
lean_dec(v_fvarSubst_661_);
lean_dec_ref(v___x_659_);
lean_dec(v_hFVarId_658_);
lean_dec(v_fvarId_657_);
v_a_829_ = lean_ctor_get(v___x_827_, 0);
v_isSharedCheck_836_ = !lean_is_exclusive(v___x_827_);
if (v_isSharedCheck_836_ == 0)
{
v___x_831_ = v___x_827_;
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
else
{
lean_inc(v_a_829_);
lean_dec(v___x_827_);
v___x_831_ = lean_box(0);
v_isShared_832_ = v_isSharedCheck_836_;
goto v_resetjp_830_;
}
v_resetjp_830_:
{
lean_object* v___x_834_; 
if (v_isShared_832_ == 0)
{
v___x_834_ = v___x_831_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v_a_829_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
}
}
else
{
lean_inc_ref(v___x_659_);
v___y_782_ = v___y_823_;
v___y_783_ = v_newType_826_;
v___y_784_ = v_motive_825_;
v___y_785_ = v___y_824_;
v_major_786_ = v___x_659_;
v___y_787_ = v___y_676_;
v___y_788_ = v___y_677_;
v___y_789_ = v___y_678_;
v___y_790_ = v___y_679_;
goto v___jp_781_;
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_substCore___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_657_ = stack[0].m_obj;
lean_object* v_hFVarId_658_ = stack[1].m_obj;
lean_object* v___x_659_ = stack[2].m_obj;
lean_object* v_fst_660_ = stack[3].m_obj;
lean_object* v_fvarSubst_661_ = stack[4].m_obj;
uint8_t v_clearH_662_ = stack[5].m_num;
lean_object* v___x_663_ = stack[6].m_obj;
lean_object* v___x_664_ = stack[7].m_obj;
lean_object* v___x_665_ = stack[8].m_obj;
uint8_t v_skip_666_ = stack[9].m_num;
uint8_t v___x_667_ = stack[10].m_num;
lean_object* v___x_668_ = stack[11].m_obj;
lean_object* v_snd_669_ = stack[12].m_obj;
lean_object* v___x_670_ = stack[13].m_obj;
lean_object* v___x_671_ = stack[14].m_obj;
lean_object* v_a_672_ = stack[15].m_obj;
uint8_t v_symm_673_ = stack[16].m_num;
uint8_t v___x_674_ = stack[17].m_num;
lean_object* v___x_675_ = stack[18].m_obj;
lean_object* v___y_676_ = stack[19].m_obj;
lean_object* v___y_677_ = stack[20].m_obj;
lean_object* v___y_678_ = stack[21].m_obj;
lean_object* v___y_679_ = stack[22].m_obj;
lean_object* v_res_949_;
v_res_949_ = l_Lean_Meta_substCore___lam__1(v_fvarId_657_, v_hFVarId_658_, v___x_659_, v_fst_660_, v_fvarSubst_661_, v_clearH_662_, v___x_663_, v___x_664_, v___x_665_, v_skip_666_, v___x_667_, v___x_668_, v_snd_669_, v___x_670_, v___x_671_, v_a_672_, v_symm_673_, v___x_674_, v___x_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_);
stack->m_obj
 = v_res_949_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object** _args){
lean_object* v_fvarId_950_ = _args[0];
lean_object* v_hFVarId_951_ = _args[1];
lean_object* v___x_952_ = _args[2];
lean_object* v_fst_953_ = _args[3];
lean_object* v_fvarSubst_954_ = _args[4];
lean_object* v_clearH_955_ = _args[5];
lean_object* v___x_956_ = _args[6];
lean_object* v___x_957_ = _args[7];
lean_object* v___x_958_ = _args[8];
lean_object* v_skip_959_ = _args[9];
lean_object* v___x_960_ = _args[10];
lean_object* v___x_961_ = _args[11];
lean_object* v_snd_962_ = _args[12];
lean_object* v___x_963_ = _args[13];
lean_object* v___x_964_ = _args[14];
lean_object* v_a_965_ = _args[15];
lean_object* v_symm_966_ = _args[16];
lean_object* v___x_967_ = _args[17];
lean_object* v___x_968_ = _args[18];
lean_object* v___y_969_ = _args[19];
lean_object* v___y_970_ = _args[20];
lean_object* v___y_971_ = _args[21];
lean_object* v___y_972_ = _args[22];
lean_object* v___y_973_ = _args[23];
_start:
{
uint8_t v_clearH_boxed_974_; uint8_t v_skip_boxed_975_; uint8_t v___x_28238__boxed_976_; uint8_t v_symm_boxed_977_; uint8_t v___x_28244__boxed_978_; lean_object* v_res_979_; 
v_clearH_boxed_974_ = lean_unbox(v_clearH_955_);
v_skip_boxed_975_ = lean_unbox(v_skip_959_);
v___x_28238__boxed_976_ = lean_unbox(v___x_960_);
v_symm_boxed_977_ = lean_unbox(v_symm_966_);
v___x_28244__boxed_978_ = lean_unbox(v___x_967_);
v_res_979_ = l_Lean_Meta_substCore___lam__1(v_fvarId_950_, v_hFVarId_951_, v___x_952_, v_fst_953_, v_fvarSubst_954_, v_clearH_boxed_974_, v___x_956_, v___x_957_, v___x_958_, v_skip_boxed_975_, v___x_28238__boxed_976_, v___x_961_, v_snd_962_, v___x_963_, v___x_964_, v_a_965_, v_symm_boxed_977_, v___x_28244__boxed_978_, v___x_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_);
lean_dec(v___y_972_);
lean_dec_ref(v___y_971_);
lean_dec(v___y_970_);
lean_dec_ref(v___y_969_);
lean_dec(v___x_968_);
lean_dec_ref(v_fst_953_);
return v_res_979_;
}
}
lean_object* l_Lean_Meta_substCore___lam__2(lean_object* v___x_980_, lean_object* v___y_981_, lean_object* v___y_982_, lean_object* v___y_983_, lean_object* v___y_984_){
_start:
{
lean_object* v_toCold_986_; lean_object* v_options_987_; uint8_t v_hasTrace_988_; 
v_toCold_986_ = lean_ctor_get(v___y_983_, 0);
v_options_987_ = lean_ctor_get(v_toCold_986_, 2);
v_hasTrace_988_ = lean_ctor_get_uint8(v_options_987_, sizeof(void*)*1);
if (v_hasTrace_988_ == 0)
{
lean_object* v___x_989_; lean_object* v___x_990_; 
lean_dec(v___x_980_);
v___x_989_ = lean_box(v_hasTrace_988_);
v___x_990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_990_, 0, v___x_989_);
return v___x_990_;
}
else
{
lean_object* v_inheritedTraceOptions_991_; lean_object* v___x_992_; lean_object* v___x_993_; uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; 
v_inheritedTraceOptions_991_ = lean_ctor_get(v_toCold_986_, 11);
v___x_992_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
v___x_993_ = l_Lean_Name_append(v___x_992_, v___x_980_);
v___x_994_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_991_, v_options_987_, v___x_993_);
lean_dec(v___x_993_);
v___x_995_ = lean_box(v___x_994_);
v___x_996_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_996_, 0, v___x_995_);
return v___x_996_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_substCore___lam__2_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_980_ = stack[0].m_obj;
lean_object* v___y_981_ = stack[1].m_obj;
lean_object* v___y_982_ = stack[2].m_obj;
lean_object* v___y_983_ = stack[3].m_obj;
lean_object* v___y_984_ = stack[4].m_obj;
lean_object* v_res_997_;
v_res_997_ = l_Lean_Meta_substCore___lam__2(v___x_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
stack->m_obj
 = v_res_997_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object* v___x_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_, lean_object* v___y_1002_, lean_object* v___y_1003_){
_start:
{
lean_object* v_res_1004_; 
v_res_1004_ = l_Lean_Meta_substCore___lam__2(v___x_998_, v___y_999_, v___y_1000_, v___y_1001_, v___y_1002_);
lean_dec(v___y_1002_);
lean_dec_ref(v___y_1001_);
lean_dec(v___y_1000_);
lean_dec_ref(v___y_999_);
return v_res_1004_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(lean_object* v_a_1005_, lean_object* v_a_1006_){
_start:
{
if (lean_obj_tag(v_a_1005_) == 0)
{
lean_object* v___x_1007_; 
v___x_1007_ = l_List_reverse___redArg(v_a_1006_);
return v___x_1007_;
}
else
{
lean_object* v_head_1008_; lean_object* v_tail_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1018_; 
v_head_1008_ = lean_ctor_get(v_a_1005_, 0);
v_tail_1009_ = lean_ctor_get(v_a_1005_, 1);
v_isSharedCheck_1018_ = !lean_is_exclusive(v_a_1005_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1011_ = v_a_1005_;
v_isShared_1012_ = v_isSharedCheck_1018_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_tail_1009_);
lean_inc(v_head_1008_);
lean_dec(v_a_1005_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1018_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1013_; lean_object* v___x_1015_; 
v___x_1013_ = l_Lean_MessageData_ofName(v_head_1008_);
if (v_isShared_1012_ == 0)
{
lean_ctor_set(v___x_1011_, 1, v_a_1006_);
lean_ctor_set(v___x_1011_, 0, v___x_1013_);
v___x_1015_ = v___x_1011_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v___x_1013_);
lean_ctor_set(v_reuseFailAlloc_1017_, 1, v_a_1006_);
v___x_1015_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
v_a_1005_ = v_tail_1009_;
v_a_1006_ = v___x_1015_;
goto _start;
}
}
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(size_t v_sz_1019_, size_t v_i_1020_, lean_object* v_bs_1021_){
_start:
{
uint8_t v___x_1022_; 
v___x_1022_ = lean_usize_dec_lt(v_i_1020_, v_sz_1019_);
if (v___x_1022_ == 0)
{
return v_bs_1021_;
}
else
{
lean_object* v_v_1023_; lean_object* v___x_1024_; lean_object* v_bs_x27_1025_; size_t v___x_1026_; size_t v___x_1027_; lean_object* v___x_1028_; 
v_v_1023_ = lean_array_uget(v_bs_1021_, v_i_1020_);
v___x_1024_ = lean_unsigned_to_nat(0u);
v_bs_x27_1025_ = lean_array_uset(v_bs_1021_, v_i_1020_, v___x_1024_);
v___x_1026_ = ((size_t)1ULL);
v___x_1027_ = lean_usize_add(v_i_1020_, v___x_1026_);
v___x_1028_ = lean_array_uset(v_bs_x27_1025_, v_i_1020_, v_v_1023_);
v_i_1020_ = v___x_1027_;
v_bs_1021_ = v___x_1028_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8_0interp(lean_interpreter_value* stack)
{
size_t v_sz_1019_ = stack[0].m_num;
size_t v_i_1020_ = stack[1].m_num;
lean_object* v_bs_1021_ = stack[2].m_obj;
lean_object* v_res_1030_;
v_res_1030_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1019_, v_i_1020_, v_bs_1021_);
stack->m_obj
 = v_res_1030_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8___boxed(lean_object* v_sz_1031_, lean_object* v_i_1032_, lean_object* v_bs_1033_){
_start:
{
size_t v_sz_boxed_1034_; size_t v_i_boxed_1035_; lean_object* v_res_1036_; 
v_sz_boxed_1034_ = lean_unbox_usize(v_sz_1031_);
lean_dec(v_sz_1031_);
v_i_boxed_1035_ = lean_unbox_usize(v_i_1032_);
lean_dec(v_i_1032_);
v_res_1036_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_boxed_1034_, v_i_boxed_1035_, v_bs_1033_);
return v_res_1036_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__2));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__4));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__7));
v___x_1050_ = l_Lean_MessageData_ofFormat(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__9(void){
_start:
{
lean_object* v___x_1051_; lean_object* v___x_1052_; 
v___x_1051_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__8, &l_Lean_Meta_substCore___lam__3___closed__8_once, _init_l_Lean_Meta_substCore___lam__3___closed__8);
v___x_1052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1052_, 0, v___x_1051_);
return v___x_1052_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__11(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__10));
v___x_1055_ = l_Lean_stringToMessageData(v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__13(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__12));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__15(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__14));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__17(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__16));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__19(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__18));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__25(void){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__24));
v___x_1078_ = l_Lean_stringToMessageData(v___x_1077_);
return v___x_1078_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__27(void){
_start:
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1080_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__26));
v___x_1081_ = l_Lean_stringToMessageData(v___x_1080_);
return v___x_1081_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__29(void){
_start:
{
lean_object* v___x_1083_; lean_object* v___x_1084_; 
v___x_1083_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__28));
v___x_1084_ = l_Lean_stringToMessageData(v___x_1083_);
return v___x_1084_;
}
}
lean_object* l_Lean_Meta_substCore___lam__3(lean_object* v_mvarId_1087_, lean_object* v_hFVarId_1088_, lean_object* v___x_1089_, uint8_t v_clearH_1090_, lean_object* v_fvarSubst_1091_, uint8_t v_symm_1092_, uint8_t v_tryToSkip_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___y_1100_; lean_object* v___y_1101_; lean_object* v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1104_; lean_object* v___y_1105_; lean_object* v___y_1106_; lean_object* v___x_1137_; 
lean_inc(v_mvarId_1087_);
v___x_1137_ = l_Lean_MVarId_getTag(v_mvarId_1087_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v___x_1139_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
lean_inc(v_mvarId_1087_);
v___x_1140_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1087_, v___x_1139_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1141_; 
lean_dec_ref_known(v___x_1140_, 1);
lean_inc(v_hFVarId_1088_);
v___x_1141_ = l_Lean_FVarId_getDecl___redArg(v_hFVarId_1088_, v___y_1094_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; lean_object* v___x_1143_; lean_object* v___y_1145_; lean_object* v___y_1146_; lean_object* v___x_1158_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref_known(v___x_1141_, 1);
v___x_1143_ = l_Lean_LocalDecl_type(v_a_1142_);
lean_dec(v_a_1142_);
lean_inc_ref(v___x_1143_);
v___x_1158_ = l_Lean_Meta_matchEq_x3f(v___x_1143_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
lean_inc(v_a_1159_);
lean_dec_ref_known(v___x_1158_, 1);
if (lean_obj_tag(v_a_1159_) == 0)
{
lean_object* v___x_1160_; lean_object* v___x_1161_; 
lean_dec_ref(v___x_1143_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
v___x_1160_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__9, &l_Lean_Meta_substCore___lam__3___closed__9_once, _init_l_Lean_Meta_substCore___lam__3___closed__9);
v___x_1161_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1139_, v_mvarId_1087_, v___x_1160_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v___x_1161_;
}
else
{
lean_object* v_val_1162_; lean_object* v___x_1164_; uint8_t v_isShared_1165_; uint8_t v_isSharedCheck_1480_; 
v_val_1162_ = lean_ctor_get(v_a_1159_, 0);
v_isSharedCheck_1480_ = !lean_is_exclusive(v_a_1159_);
if (v_isSharedCheck_1480_ == 0)
{
v___x_1164_ = v_a_1159_;
v_isShared_1165_ = v_isSharedCheck_1480_;
goto v_resetjp_1163_;
}
else
{
lean_inc(v_val_1162_);
lean_dec(v_a_1159_);
v___x_1164_ = lean_box(0);
v_isShared_1165_ = v_isSharedCheck_1480_;
goto v_resetjp_1163_;
}
v_resetjp_1163_:
{
lean_object* v_snd_1166_; lean_object* v___x_1168_; uint8_t v_isShared_1169_; uint8_t v_isSharedCheck_1478_; 
v_snd_1166_ = lean_ctor_get(v_val_1162_, 1);
v_isSharedCheck_1478_ = !lean_is_exclusive(v_val_1162_);
if (v_isSharedCheck_1478_ == 0)
{
lean_object* v_unused_1479_; 
v_unused_1479_ = lean_ctor_get(v_val_1162_, 0);
lean_dec(v_unused_1479_);
v___x_1168_ = v_val_1162_;
v_isShared_1169_ = v_isSharedCheck_1478_;
goto v_resetjp_1167_;
}
else
{
lean_inc(v_snd_1166_);
lean_dec(v_val_1162_);
v___x_1168_ = lean_box(0);
v_isShared_1169_ = v_isSharedCheck_1478_;
goto v_resetjp_1167_;
}
v_resetjp_1167_:
{
lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1477_; 
v_fst_1170_ = lean_ctor_get(v_snd_1166_, 0);
v_snd_1171_ = lean_ctor_get(v_snd_1166_, 1);
v_isSharedCheck_1477_ = !lean_is_exclusive(v_snd_1166_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1173_ = v_snd_1166_;
v_isShared_1174_ = v_isSharedCheck_1477_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snd_1171_);
lean_inc(v_fst_1170_);
lean_dec(v_snd_1166_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1477_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
uint8_t v___x_1175_; uint8_t v___y_1177_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; uint8_t v_skip_1194_; uint8_t v___y_1203_; lean_object* v___y_1204_; lean_object* v___y_1205_; lean_object* v___y_1206_; lean_object* v___y_1207_; lean_object* v___y_1208_; lean_object* v___y_1209_; lean_object* v___y_1210_; lean_object* v___y_1211_; uint8_t v___y_1212_; lean_object* v___y_1213_; lean_object* v___y_1214_; lean_object* v___y_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v___y_1218_; uint8_t v___y_1244_; lean_object* v___y_1245_; lean_object* v___y_1246_; lean_object* v___y_1247_; lean_object* v___y_1248_; lean_object* v___y_1249_; lean_object* v___y_1250_; lean_object* v___y_1251_; lean_object* v___y_1252_; uint8_t v___y_1253_; lean_object* v___y_1254_; lean_object* v___y_1255_; lean_object* v___y_1256_; lean_object* v___y_1257_; lean_object* v___y_1258_; lean_object* v___y_1259_; lean_object* v___y_1260_; uint8_t v___y_1293_; lean_object* v___y_1294_; lean_object* v___y_1295_; lean_object* v___y_1296_; lean_object* v___y_1297_; lean_object* v___y_1298_; lean_object* v___y_1299_; uint8_t v___y_1300_; lean_object* v___y_1301_; lean_object* v___y_1302_; lean_object* v___y_1303_; lean_object* v___y_1304_; lean_object* v___y_1305_; lean_object* v___y_1306_; lean_object* v___y_1350_; lean_object* v___y_1351_; lean_object* v___y_1352_; lean_object* v___y_1353_; lean_object* v___y_1354_; lean_object* v___y_1355_; lean_object* v___y_1356_; lean_object* v___y_1357_; lean_object* v___y_1358_; lean_object* v___y_1406_; lean_object* v___y_1407_; lean_object* v___y_1408_; lean_object* v___y_1409_; lean_object* v___y_1410_; lean_object* v___y_1411_; lean_object* v___y_1412_; lean_object* v___y_1413_; lean_object* v___y_1414_; lean_object* v___y_1440_; lean_object* v___y_1441_; lean_object* v___y_1473_; 
v___x_1175_ = 1;
if (v_symm_1092_ == 0)
{
lean_inc(v_fst_1170_);
v___y_1473_ = v_fst_1170_;
goto v___jp_1472_;
}
else
{
lean_inc(v_snd_1171_);
v___y_1473_ = v_snd_1171_;
goto v___jp_1472_;
}
v___jp_1176_:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; 
v___x_1195_ = lean_box(v_clearH_1090_);
v___x_1196_ = lean_box(v_skip_1194_);
v___x_1197_ = lean_box(v___x_1175_);
v___x_1198_ = lean_box(v_symm_1092_);
v___x_1199_ = lean_box(v___y_1177_);
v___f_1200_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 24, 19);
lean_closure_set(v___f_1200_, 0, v___y_1178_);
lean_closure_set(v___f_1200_, 1, v_hFVarId_1088_);
lean_closure_set(v___f_1200_, 2, v___y_1186_);
lean_closure_set(v___f_1200_, 3, v___y_1179_);
lean_closure_set(v___f_1200_, 4, v_fvarSubst_1091_);
lean_closure_set(v___f_1200_, 5, v___x_1195_);
lean_closure_set(v___f_1200_, 6, v___y_1182_);
lean_closure_set(v___f_1200_, 7, v___y_1190_);
lean_closure_set(v___f_1200_, 8, v___y_1192_);
lean_closure_set(v___f_1200_, 9, v___x_1196_);
lean_closure_set(v___f_1200_, 10, v___x_1197_);
lean_closure_set(v___f_1200_, 11, v___y_1189_);
lean_closure_set(v___f_1200_, 12, v___y_1187_);
lean_closure_set(v___f_1200_, 13, v___y_1191_);
lean_closure_set(v___f_1200_, 14, v___y_1180_);
lean_closure_set(v___f_1200_, 15, v_a_1138_);
lean_closure_set(v___f_1200_, 16, v___x_1198_);
lean_closure_set(v___f_1200_, 17, v___x_1199_);
lean_closure_set(v___f_1200_, 18, v___y_1183_);
v___x_1201_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v___y_1184_, v___f_1200_, v___y_1185_, v___y_1193_, v___y_1188_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1188_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1185_);
return v___x_1201_;
}
v___jp_1202_:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_array_get(v___x_1089_, v___y_1210_, v___x_1219_);
lean_inc(v___x_1220_);
v___x_1221_ = l_Lean_mkFVar(v___x_1220_);
v___x_1222_ = lean_unsigned_to_nat(1u);
v___x_1223_ = lean_array_get(v___x_1089_, v___y_1210_, v___x_1222_);
lean_dec_ref(v___y_1210_);
lean_inc(v___x_1223_);
v___x_1224_ = l_Lean_mkFVar(v___x_1223_);
if (v_tryToSkip_1093_ == 0)
{
lean_dec_ref(v___y_1214_);
lean_dec(v___y_1213_);
v___y_1177_ = v___y_1203_;
v___y_1178_ = v___y_1205_;
v___y_1179_ = v___y_1206_;
v___y_1180_ = v___x_1220_;
v___y_1181_ = v___y_1218_;
v___y_1182_ = v___x_1221_;
v___y_1183_ = v___x_1222_;
v___y_1184_ = v___y_1211_;
v___y_1185_ = v___y_1215_;
v___y_1186_ = v___x_1224_;
v___y_1187_ = v___y_1209_;
v___y_1188_ = v___y_1217_;
v___y_1189_ = v___y_1204_;
v___y_1190_ = v___y_1207_;
v___y_1191_ = v___x_1223_;
v___y_1192_ = v___y_1208_;
v___y_1193_ = v___y_1216_;
v_skip_1194_ = v___y_1212_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1225_; uint8_t v___x_1226_; 
v___x_1225_ = lean_array_get_size(v___y_1214_);
lean_dec_ref(v___y_1214_);
v___x_1226_ = lean_nat_dec_eq(v___x_1225_, v___y_1213_);
lean_dec(v___y_1213_);
if (v___x_1226_ == 0)
{
v___y_1177_ = v___y_1203_;
v___y_1178_ = v___y_1205_;
v___y_1179_ = v___y_1206_;
v___y_1180_ = v___x_1220_;
v___y_1181_ = v___y_1218_;
v___y_1182_ = v___x_1221_;
v___y_1183_ = v___x_1222_;
v___y_1184_ = v___y_1211_;
v___y_1185_ = v___y_1215_;
v___y_1186_ = v___x_1224_;
v___y_1187_ = v___y_1209_;
v___y_1188_ = v___y_1217_;
v___y_1189_ = v___y_1204_;
v___y_1190_ = v___y_1207_;
v___y_1191_ = v___x_1223_;
v___y_1192_ = v___y_1208_;
v___y_1193_ = v___y_1216_;
v_skip_1194_ = v___y_1212_;
goto v___jp_1176_;
}
else
{
lean_object* v___x_1227_; 
lean_inc(v___y_1211_);
v___x_1227_ = l_Lean_MVarId_getType(v___y_1211_, v___y_1215_, v___y_1216_, v___y_1217_, v___y_1218_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v_a_1228_; lean_object* v___x_1229_; lean_object* v_a_1230_; uint8_t v___x_1231_; 
v_a_1228_ = lean_ctor_get(v___x_1227_, 0);
lean_inc_n(v_a_1228_, 2);
lean_dec_ref_known(v___x_1227_, 1);
lean_inc(v___x_1220_);
v___x_1229_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1228_, v___x_1220_, v___y_1216_);
v_a_1230_ = lean_ctor_get(v___x_1229_, 0);
lean_inc(v_a_1230_);
lean_dec_ref(v___x_1229_);
v___x_1231_ = lean_unbox(v_a_1230_);
lean_dec(v_a_1230_);
if (v___x_1231_ == 0)
{
lean_object* v___x_1232_; lean_object* v_a_1233_; uint8_t v___x_1234_; 
lean_inc(v___x_1223_);
v___x_1232_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1228_, v___x_1223_, v___y_1216_);
v_a_1233_ = lean_ctor_get(v___x_1232_, 0);
lean_inc(v_a_1233_);
lean_dec_ref(v___x_1232_);
v___x_1234_ = lean_unbox(v_a_1233_);
lean_dec(v_a_1233_);
if (v___x_1234_ == 0)
{
lean_dec_ref(v___x_1224_);
lean_dec_ref(v___x_1221_);
lean_dec(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec(v_a_1138_);
lean_dec(v_hFVarId_1088_);
v___y_1100_ = v___y_1217_;
v___y_1101_ = v___x_1220_;
v___y_1102_ = v___y_1218_;
v___y_1103_ = v___x_1223_;
v___y_1104_ = v___y_1211_;
v___y_1105_ = v___y_1215_;
v___y_1106_ = v___y_1216_;
goto v___jp_1099_;
}
else
{
v___y_1177_ = v___y_1203_;
v___y_1178_ = v___y_1205_;
v___y_1179_ = v___y_1206_;
v___y_1180_ = v___x_1220_;
v___y_1181_ = v___y_1218_;
v___y_1182_ = v___x_1221_;
v___y_1183_ = v___x_1222_;
v___y_1184_ = v___y_1211_;
v___y_1185_ = v___y_1215_;
v___y_1186_ = v___x_1224_;
v___y_1187_ = v___y_1209_;
v___y_1188_ = v___y_1217_;
v___y_1189_ = v___y_1204_;
v___y_1190_ = v___y_1207_;
v___y_1191_ = v___x_1223_;
v___y_1192_ = v___y_1208_;
v___y_1193_ = v___y_1216_;
v_skip_1194_ = v___y_1212_;
goto v___jp_1176_;
}
}
else
{
lean_dec(v_a_1228_);
v___y_1177_ = v___y_1203_;
v___y_1178_ = v___y_1205_;
v___y_1179_ = v___y_1206_;
v___y_1180_ = v___x_1220_;
v___y_1181_ = v___y_1218_;
v___y_1182_ = v___x_1221_;
v___y_1183_ = v___x_1222_;
v___y_1184_ = v___y_1211_;
v___y_1185_ = v___y_1215_;
v___y_1186_ = v___x_1224_;
v___y_1187_ = v___y_1209_;
v___y_1188_ = v___y_1217_;
v___y_1189_ = v___y_1204_;
v___y_1190_ = v___y_1207_;
v___y_1191_ = v___x_1223_;
v___y_1192_ = v___y_1208_;
v___y_1193_ = v___y_1216_;
v_skip_1194_ = v___y_1212_;
goto v___jp_1176_;
}
}
else
{
lean_object* v_a_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1242_; 
lean_dec_ref(v___x_1224_);
lean_dec(v___x_1223_);
lean_dec_ref(v___x_1221_);
lean_dec(v___x_1220_);
lean_dec(v___y_1218_);
lean_dec_ref(v___y_1217_);
lean_dec(v___y_1216_);
lean_dec_ref(v___y_1215_);
lean_dec(v___y_1211_);
lean_dec(v___y_1209_);
lean_dec(v___y_1208_);
lean_dec(v___y_1207_);
lean_dec_ref(v___y_1206_);
lean_dec(v___y_1205_);
lean_dec(v___y_1204_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
v_a_1235_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1242_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1237_ = v___x_1227_;
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_a_1235_);
lean_dec(v___x_1227_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1242_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1240_; 
if (v_isShared_1238_ == 0)
{
v___x_1240_ = v___x_1237_;
goto v_reusejp_1239_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_a_1235_);
v___x_1240_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1239_;
}
v_reusejp_1239_:
{
return v___x_1240_;
}
}
}
}
}
}
v___jp_1243_:
{
lean_object* v___x_1261_; 
lean_inc_ref(v___y_1255_);
lean_inc(v___y_1260_);
lean_inc_ref(v___y_1259_);
lean_inc(v___y_1258_);
lean_inc_ref(v___y_1257_);
v___x_1261_ = lean_apply_5(v___y_1255_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_, lean_box(0));
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v_a_1262_; uint8_t v___x_1263_; 
v_a_1262_ = lean_ctor_get(v___x_1261_, 0);
lean_inc(v_a_1262_);
lean_dec_ref_known(v___x_1261_, 1);
v___x_1263_ = lean_unbox(v_a_1262_);
lean_dec(v_a_1262_);
if (v___x_1263_ == 0)
{
lean_dec(v___y_1252_);
lean_del_object(v___x_1173_);
lean_inc(v___y_1251_);
v___y_1203_ = v___y_1244_;
v___y_1204_ = v___y_1246_;
v___y_1205_ = v___y_1245_;
v___y_1206_ = v___y_1247_;
v___y_1207_ = v___y_1248_;
v___y_1208_ = v___y_1250_;
v___y_1209_ = v___y_1251_;
v___y_1210_ = v___y_1249_;
v___y_1211_ = v___y_1251_;
v___y_1212_ = v___y_1253_;
v___y_1213_ = v___y_1254_;
v___y_1214_ = v___y_1256_;
v___y_1215_ = v___y_1257_;
v___y_1216_ = v___y_1258_;
v___y_1217_ = v___y_1259_;
v___y_1218_ = v___y_1260_;
goto v___jp_1202_;
}
else
{
lean_object* v___x_1264_; size_t v_sz_1265_; size_t v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1273_; 
v___x_1264_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__11, &l_Lean_Meta_substCore___lam__3___closed__11_once, _init_l_Lean_Meta_substCore___lam__3___closed__11);
v_sz_1265_ = lean_array_size(v___y_1256_);
v___x_1266_ = ((size_t)0ULL);
lean_inc_ref(v___y_1256_);
v___x_1267_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1265_, v___x_1266_, v___y_1256_);
v___x_1268_ = lean_array_to_list(v___x_1267_);
v___x_1269_ = lean_box(0);
v___x_1270_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(v___x_1268_, v___x_1269_);
v___x_1271_ = l_Lean_MessageData_ofList(v___x_1270_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set_tag(v___x_1173_, 7);
lean_ctor_set(v___x_1173_, 1, v___x_1271_);
lean_ctor_set(v___x_1173_, 0, v___x_1264_);
v___x_1273_ = v___x_1173_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1283_; 
v_reuseFailAlloc_1283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1283_, 0, v___x_1264_);
lean_ctor_set(v_reuseFailAlloc_1283_, 1, v___x_1271_);
v___x_1273_ = v_reuseFailAlloc_1283_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
lean_object* v___x_1274_; 
v___x_1274_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1252_, v___x_1273_, v___y_1257_, v___y_1258_, v___y_1259_, v___y_1260_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_dec_ref_known(v___x_1274_, 1);
lean_inc(v___y_1251_);
v___y_1203_ = v___y_1244_;
v___y_1204_ = v___y_1246_;
v___y_1205_ = v___y_1245_;
v___y_1206_ = v___y_1247_;
v___y_1207_ = v___y_1248_;
v___y_1208_ = v___y_1250_;
v___y_1209_ = v___y_1251_;
v___y_1210_ = v___y_1249_;
v___y_1211_ = v___y_1251_;
v___y_1212_ = v___y_1253_;
v___y_1213_ = v___y_1254_;
v___y_1214_ = v___y_1256_;
v___y_1215_ = v___y_1257_;
v___y_1216_ = v___y_1258_;
v___y_1217_ = v___y_1259_;
v___y_1218_ = v___y_1260_;
goto v___jp_1202_;
}
else
{
lean_object* v_a_1275_; lean_object* v___x_1277_; uint8_t v_isShared_1278_; uint8_t v_isSharedCheck_1282_; 
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1254_);
lean_dec(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1282_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1282_ == 0)
{
v___x_1277_ = v___x_1274_;
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
else
{
lean_inc(v_a_1275_);
lean_dec(v___x_1274_);
v___x_1277_ = lean_box(0);
v_isShared_1278_ = v_isSharedCheck_1282_;
goto v_resetjp_1276_;
}
v_resetjp_1276_:
{
lean_object* v___x_1280_; 
if (v_isShared_1278_ == 0)
{
v___x_1280_ = v___x_1277_;
goto v_reusejp_1279_;
}
else
{
lean_object* v_reuseFailAlloc_1281_; 
v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1281_, 0, v_a_1275_);
v___x_1280_ = v_reuseFailAlloc_1281_;
goto v_reusejp_1279_;
}
v_reusejp_1279_:
{
return v___x_1280_;
}
}
}
}
}
}
else
{
lean_object* v_a_1284_; lean_object* v___x_1286_; uint8_t v_isShared_1287_; uint8_t v_isSharedCheck_1291_; 
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec(v___y_1258_);
lean_dec_ref(v___y_1257_);
lean_dec_ref(v___y_1256_);
lean_dec(v___y_1254_);
lean_dec(v___y_1252_);
lean_dec(v___y_1251_);
lean_dec(v___y_1250_);
lean_dec_ref(v___y_1249_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec(v___y_1245_);
lean_del_object(v___x_1173_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
v_a_1284_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1291_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1291_ == 0)
{
v___x_1286_ = v___x_1261_;
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
else
{
lean_inc(v_a_1284_);
lean_dec(v___x_1261_);
v___x_1286_ = lean_box(0);
v_isShared_1287_ = v_isSharedCheck_1291_;
goto v_resetjp_1285_;
}
v_resetjp_1285_:
{
lean_object* v___x_1289_; 
if (v_isShared_1287_ == 0)
{
v___x_1289_ = v___x_1286_;
goto v_reusejp_1288_;
}
else
{
lean_object* v_reuseFailAlloc_1290_; 
v_reuseFailAlloc_1290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1290_, 0, v_a_1284_);
v___x_1289_ = v_reuseFailAlloc_1290_;
goto v_reusejp_1288_;
}
v_reusejp_1288_:
{
return v___x_1289_;
}
}
}
}
v___jp_1292_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_box(0);
lean_inc(v___y_1302_);
v___x_1308_ = l_Lean_Meta_introNCore(v___y_1296_, v___y_1302_, v___x_1307_, v___y_1300_, v___x_1175_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1308_) == 0)
{
lean_object* v_a_1309_; lean_object* v_fst_1310_; lean_object* v_snd_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1340_; 
v_a_1309_ = lean_ctor_get(v___x_1308_, 0);
lean_inc(v_a_1309_);
lean_dec_ref_known(v___x_1308_, 1);
v_fst_1310_ = lean_ctor_get(v_a_1309_, 0);
v_snd_1311_ = lean_ctor_get(v_a_1309_, 1);
v_isSharedCheck_1340_ = !lean_is_exclusive(v_a_1309_);
if (v_isSharedCheck_1340_ == 0)
{
v___x_1313_ = v_a_1309_;
v_isShared_1314_ = v_isSharedCheck_1340_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_snd_1311_);
lean_inc(v_fst_1310_);
lean_dec(v_a_1309_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1340_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1315_; 
lean_inc_ref(v___y_1301_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
v___x_1315_ = lean_apply_5(v___y_1301_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, lean_box(0));
if (lean_obj_tag(v___x_1315_) == 0)
{
lean_object* v_a_1316_; uint8_t v___x_1317_; 
v_a_1316_ = lean_ctor_get(v___x_1315_, 0);
lean_inc(v_a_1316_);
lean_dec_ref_known(v___x_1315_, 1);
v___x_1317_ = lean_unbox(v_a_1316_);
lean_dec(v_a_1316_);
if (v___x_1317_ == 0)
{
lean_del_object(v___x_1313_);
lean_inc_ref(v___y_1297_);
v___y_1244_ = v___y_1293_;
v___y_1245_ = v___y_1294_;
v___y_1246_ = v___y_1295_;
v___y_1247_ = v___y_1297_;
v___y_1248_ = v___y_1298_;
v___y_1249_ = v_fst_1310_;
v___y_1250_ = v___x_1307_;
v___y_1251_ = v_snd_1311_;
v___y_1252_ = v___y_1299_;
v___y_1253_ = v___y_1300_;
v___y_1254_ = v___y_1302_;
v___y_1255_ = v___y_1301_;
v___y_1256_ = v___y_1297_;
v___y_1257_ = v___y_1303_;
v___y_1258_ = v___y_1304_;
v___y_1259_ = v___y_1305_;
v___y_1260_ = v___y_1306_;
goto v___jp_1243_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1321_; 
v___x_1318_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__13, &l_Lean_Meta_substCore___lam__3___closed__13_once, _init_l_Lean_Meta_substCore___lam__3___closed__13);
lean_inc(v_snd_1311_);
v___x_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1319_, 0, v_snd_1311_);
if (v_isShared_1314_ == 0)
{
lean_ctor_set_tag(v___x_1313_, 7);
lean_ctor_set(v___x_1313_, 1, v___x_1319_);
lean_ctor_set(v___x_1313_, 0, v___x_1318_);
v___x_1321_ = v___x_1313_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1318_);
lean_ctor_set(v_reuseFailAlloc_1331_, 1, v___x_1319_);
v___x_1321_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
lean_object* v___x_1322_; 
lean_inc(v___y_1299_);
v___x_1322_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1299_, v___x_1321_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_);
if (lean_obj_tag(v___x_1322_) == 0)
{
lean_dec_ref_known(v___x_1322_, 1);
lean_inc_ref(v___y_1297_);
v___y_1244_ = v___y_1293_;
v___y_1245_ = v___y_1294_;
v___y_1246_ = v___y_1295_;
v___y_1247_ = v___y_1297_;
v___y_1248_ = v___y_1298_;
v___y_1249_ = v_fst_1310_;
v___y_1250_ = v___x_1307_;
v___y_1251_ = v_snd_1311_;
v___y_1252_ = v___y_1299_;
v___y_1253_ = v___y_1300_;
v___y_1254_ = v___y_1302_;
v___y_1255_ = v___y_1301_;
v___y_1256_ = v___y_1297_;
v___y_1257_ = v___y_1303_;
v___y_1258_ = v___y_1304_;
v___y_1259_ = v___y_1305_;
v___y_1260_ = v___y_1306_;
goto v___jp_1243_;
}
else
{
lean_object* v_a_1323_; lean_object* v___x_1325_; uint8_t v_isShared_1326_; uint8_t v_isSharedCheck_1330_; 
lean_dec(v_snd_1311_);
lean_dec(v_fst_1310_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1295_);
lean_dec(v___y_1294_);
lean_del_object(v___x_1173_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
v_a_1323_ = lean_ctor_get(v___x_1322_, 0);
v_isSharedCheck_1330_ = !lean_is_exclusive(v___x_1322_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1325_ = v___x_1322_;
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
else
{
lean_inc(v_a_1323_);
lean_dec(v___x_1322_);
v___x_1325_ = lean_box(0);
v_isShared_1326_ = v_isSharedCheck_1330_;
goto v_resetjp_1324_;
}
v_resetjp_1324_:
{
lean_object* v___x_1328_; 
if (v_isShared_1326_ == 0)
{
v___x_1328_ = v___x_1325_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_a_1323_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
else
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
lean_del_object(v___x_1313_);
lean_dec(v_snd_1311_);
lean_dec(v_fst_1310_);
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1295_);
lean_dec(v___y_1294_);
lean_del_object(v___x_1173_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
v_a_1332_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1315_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1315_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
}
}
else
{
lean_object* v_a_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1348_; 
lean_dec(v___y_1306_);
lean_dec_ref(v___y_1305_);
lean_dec(v___y_1304_);
lean_dec_ref(v___y_1303_);
lean_dec(v___y_1302_);
lean_dec(v___y_1299_);
lean_dec(v___y_1298_);
lean_dec_ref(v___y_1297_);
lean_dec(v___y_1295_);
lean_dec(v___y_1294_);
lean_del_object(v___x_1173_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
v_a_1341_ = lean_ctor_get(v___x_1308_, 0);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1308_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1343_ = v___x_1308_;
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_a_1341_);
lean_dec(v___x_1308_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1348_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v___x_1346_; 
if (v_isShared_1344_ == 0)
{
v___x_1346_ = v___x_1343_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_a_1341_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
v___jp_1349_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; 
v___x_1359_ = lean_unsigned_to_nat(2u);
v___x_1360_ = lean_mk_empty_array_with_capacity(v___x_1359_);
v___x_1361_ = lean_array_push(v___x_1360_, v___y_1353_);
lean_inc(v_hFVarId_1088_);
v___x_1362_ = lean_array_push(v___x_1361_, v_hFVarId_1088_);
v___x_1363_ = 0;
v___x_1364_ = l_Lean_MVarId_revert(v_mvarId_1087_, v___x_1362_, v___x_1175_, v___x_1363_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
if (lean_obj_tag(v___x_1364_) == 0)
{
lean_object* v_a_1365_; lean_object* v_fst_1366_; lean_object* v_snd_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1396_; 
v_a_1365_ = lean_ctor_get(v___x_1364_, 0);
lean_inc(v_a_1365_);
lean_dec_ref_known(v___x_1364_, 1);
v_fst_1366_ = lean_ctor_get(v_a_1365_, 0);
v_snd_1367_ = lean_ctor_get(v_a_1365_, 1);
v_isSharedCheck_1396_ = !lean_is_exclusive(v_a_1365_);
if (v_isSharedCheck_1396_ == 0)
{
v___x_1369_ = v_a_1365_;
v_isShared_1370_ = v_isSharedCheck_1396_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_snd_1367_);
lean_inc(v_fst_1366_);
lean_dec(v_a_1365_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1396_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1371_; 
lean_inc_ref(v___y_1354_);
lean_inc(v___y_1358_);
lean_inc_ref(v___y_1357_);
lean_inc(v___y_1356_);
lean_inc_ref(v___y_1355_);
v___x_1371_ = lean_apply_5(v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_, lean_box(0));
if (lean_obj_tag(v___x_1371_) == 0)
{
lean_object* v_a_1372_; uint8_t v___x_1373_; 
v_a_1372_ = lean_ctor_get(v___x_1371_, 0);
lean_inc(v_a_1372_);
lean_dec_ref_known(v___x_1371_, 1);
v___x_1373_ = lean_unbox(v_a_1372_);
lean_dec(v_a_1372_);
if (v___x_1373_ == 0)
{
lean_del_object(v___x_1369_);
v___y_1293_ = v___x_1363_;
v___y_1294_ = v___y_1351_;
v___y_1295_ = v___y_1350_;
v___y_1296_ = v_snd_1367_;
v___y_1297_ = v_fst_1366_;
v___y_1298_ = v___x_1359_;
v___y_1299_ = v___y_1352_;
v___y_1300_ = v___x_1363_;
v___y_1301_ = v___y_1354_;
v___y_1302_ = v___x_1359_;
v___y_1303_ = v___y_1355_;
v___y_1304_ = v___y_1356_;
v___y_1305_ = v___y_1357_;
v___y_1306_ = v___y_1358_;
goto v___jp_1292_;
}
else
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1374_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__15, &l_Lean_Meta_substCore___lam__3___closed__15_once, _init_l_Lean_Meta_substCore___lam__3___closed__15);
lean_inc(v_snd_1367_);
v___x_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1375_, 0, v_snd_1367_);
if (v_isShared_1370_ == 0)
{
lean_ctor_set_tag(v___x_1369_, 7);
lean_ctor_set(v___x_1369_, 1, v___x_1375_);
lean_ctor_set(v___x_1369_, 0, v___x_1374_);
v___x_1377_ = v___x_1369_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1387_; 
v_reuseFailAlloc_1387_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1387_, 0, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1387_, 1, v___x_1375_);
v___x_1377_ = v_reuseFailAlloc_1387_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
lean_object* v___x_1378_; 
lean_inc(v___y_1352_);
v___x_1378_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1352_, v___x_1377_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
if (lean_obj_tag(v___x_1378_) == 0)
{
lean_dec_ref_known(v___x_1378_, 1);
v___y_1293_ = v___x_1363_;
v___y_1294_ = v___y_1351_;
v___y_1295_ = v___y_1350_;
v___y_1296_ = v_snd_1367_;
v___y_1297_ = v_fst_1366_;
v___y_1298_ = v___x_1359_;
v___y_1299_ = v___y_1352_;
v___y_1300_ = v___x_1363_;
v___y_1301_ = v___y_1354_;
v___y_1302_ = v___x_1359_;
v___y_1303_ = v___y_1355_;
v___y_1304_ = v___y_1356_;
v___y_1305_ = v___y_1357_;
v___y_1306_ = v___y_1358_;
goto v___jp_1292_;
}
else
{
lean_object* v_a_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1386_; 
lean_dec(v_snd_1367_);
lean_dec(v_fst_1366_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
lean_del_object(v___x_1173_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
v_a_1379_ = lean_ctor_get(v___x_1378_, 0);
v_isSharedCheck_1386_ = !lean_is_exclusive(v___x_1378_);
if (v_isSharedCheck_1386_ == 0)
{
v___x_1381_ = v___x_1378_;
v_isShared_1382_ = v_isSharedCheck_1386_;
goto v_resetjp_1380_;
}
else
{
lean_inc(v_a_1379_);
lean_dec(v___x_1378_);
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
}
}
else
{
lean_object* v_a_1388_; lean_object* v___x_1390_; uint8_t v_isShared_1391_; uint8_t v_isSharedCheck_1395_; 
lean_del_object(v___x_1369_);
lean_dec(v_snd_1367_);
lean_dec(v_fst_1366_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
lean_del_object(v___x_1173_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
v_a_1388_ = lean_ctor_get(v___x_1371_, 0);
v_isSharedCheck_1395_ = !lean_is_exclusive(v___x_1371_);
if (v_isSharedCheck_1395_ == 0)
{
v___x_1390_ = v___x_1371_;
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
else
{
lean_inc(v_a_1388_);
lean_dec(v___x_1371_);
v___x_1390_ = lean_box(0);
v_isShared_1391_ = v_isSharedCheck_1395_;
goto v_resetjp_1389_;
}
v_resetjp_1389_:
{
lean_object* v___x_1393_; 
if (v_isShared_1391_ == 0)
{
v___x_1393_ = v___x_1390_;
goto v_reusejp_1392_;
}
else
{
lean_object* v_reuseFailAlloc_1394_; 
v_reuseFailAlloc_1394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1394_, 0, v_a_1388_);
v___x_1393_ = v_reuseFailAlloc_1394_;
goto v_reusejp_1392_;
}
v_reusejp_1392_:
{
return v___x_1393_;
}
}
}
}
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec(v___y_1350_);
lean_del_object(v___x_1173_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
v_a_1397_ = lean_ctor_get(v___x_1364_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1364_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1364_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1364_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
v___jp_1405_:
{
lean_object* v___x_1415_; lean_object* v_a_1416_; uint8_t v___x_1417_; 
lean_inc(v___y_1407_);
lean_inc_ref(v___y_1408_);
v___x_1415_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v___y_1408_, v___y_1407_, v___y_1412_);
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
lean_inc(v_a_1416_);
lean_dec_ref(v___x_1415_);
v___x_1417_ = lean_unbox(v_a_1416_);
lean_dec(v_a_1416_);
if (v___x_1417_ == 0)
{
lean_dec_ref(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_del_object(v___x_1168_);
lean_del_object(v___x_1164_);
lean_inc(v___y_1407_);
lean_inc(v___y_1406_);
v___y_1350_ = v___y_1406_;
v___y_1351_ = v___y_1407_;
v___y_1352_ = v___y_1406_;
v___y_1353_ = v___y_1407_;
v___y_1354_ = v___y_1410_;
v___y_1355_ = v___y_1411_;
v___y_1356_ = v___y_1412_;
v___y_1357_ = v___y_1413_;
v___y_1358_ = v___y_1414_;
goto v___jp_1349_;
}
else
{
lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1421_; 
v___x_1418_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_1419_ = l_Lean_MessageData_ofExpr(v___y_1409_);
if (v_isShared_1169_ == 0)
{
lean_ctor_set_tag(v___x_1168_, 7);
lean_ctor_set(v___x_1168_, 1, v___x_1419_);
lean_ctor_set(v___x_1168_, 0, v___x_1418_);
v___x_1421_ = v___x_1168_;
goto v_reusejp_1420_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1418_);
lean_ctor_set(v_reuseFailAlloc_1438_, 1, v___x_1419_);
v___x_1421_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1420_;
}
v_reusejp_1420_:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1422_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__19, &l_Lean_Meta_substCore___lam__3___closed__19_once, _init_l_Lean_Meta_substCore___lam__3___closed__19);
v___x_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1423_, 0, v___x_1421_);
lean_ctor_set(v___x_1423_, 1, v___x_1422_);
v___x_1424_ = l_Lean_indentExpr(v___y_1408_);
v___x_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1425_, 0, v___x_1423_);
lean_ctor_set(v___x_1425_, 1, v___x_1424_);
if (v_isShared_1165_ == 0)
{
lean_ctor_set(v___x_1164_, 0, v___x_1425_);
v___x_1427_ = v___x_1164_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
lean_object* v___x_1428_; 
lean_inc(v_mvarId_1087_);
v___x_1428_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1139_, v_mvarId_1087_, v___x_1427_, v___y_1411_, v___y_1412_, v___y_1413_, v___y_1414_);
if (lean_obj_tag(v___x_1428_) == 0)
{
lean_dec_ref_known(v___x_1428_, 1);
lean_inc(v___y_1407_);
lean_inc(v___y_1406_);
v___y_1350_ = v___y_1406_;
v___y_1351_ = v___y_1407_;
v___y_1352_ = v___y_1406_;
v___y_1353_ = v___y_1407_;
v___y_1354_ = v___y_1410_;
v___y_1355_ = v___y_1411_;
v___y_1356_ = v___y_1412_;
v___y_1357_ = v___y_1413_;
v___y_1358_ = v___y_1414_;
goto v___jp_1349_;
}
else
{
lean_object* v_a_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1436_; 
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
lean_dec(v___y_1412_);
lean_dec_ref(v___y_1411_);
lean_dec(v___y_1407_);
lean_dec(v___y_1406_);
lean_del_object(v___x_1173_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
lean_dec(v_mvarId_1087_);
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
v_isSharedCheck_1436_ = !lean_is_exclusive(v___x_1428_);
if (v_isSharedCheck_1436_ == 0)
{
v___x_1431_ = v___x_1428_;
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_a_1429_);
lean_dec(v___x_1428_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1436_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v___x_1434_; 
if (v_isShared_1432_ == 0)
{
v___x_1434_ = v___x_1431_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v_a_1429_);
v___x_1434_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
return v___x_1434_;
}
}
}
}
}
}
}
v___jp_1439_:
{
lean_object* v___x_1442_; 
v___x_1442_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1441_, v___y_1095_);
if (lean_obj_tag(v___y_1440_) == 1)
{
lean_object* v_a_1443_; lean_object* v_fvarId_1444_; lean_object* v___x_1445_; lean_object* v___f_1446_; lean_object* v___x_1447_; lean_object* v_a_1448_; uint8_t v___x_1449_; 
lean_dec_ref(v___x_1143_);
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
lean_inc(v_a_1443_);
lean_dec_ref(v___x_1442_);
v_fvarId_1444_ = lean_ctor_get(v___y_1440_, 0);
lean_inc(v_fvarId_1444_);
v___x_1445_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___f_1446_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__23));
v___x_1447_ = l_Lean_Meta_substCore___lam__2(v___x_1445_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
v_a_1448_ = lean_ctor_get(v___x_1447_, 0);
lean_inc(v_a_1448_);
lean_dec_ref(v___x_1447_);
v___x_1449_ = lean_unbox(v_a_1448_);
lean_dec(v_a_1448_);
if (v___x_1449_ == 0)
{
v___y_1406_ = v___x_1445_;
v___y_1407_ = v_fvarId_1444_;
v___y_1408_ = v_a_1443_;
v___y_1409_ = v___y_1440_;
v___y_1410_ = v___f_1446_;
v___y_1411_ = v___y_1094_;
v___y_1412_ = v___y_1095_;
v___y_1413_ = v___y_1096_;
v___y_1414_ = v___y_1097_;
goto v___jp_1405_;
}
else
{
lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; 
v___x_1450_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__25, &l_Lean_Meta_substCore___lam__3___closed__25_once, _init_l_Lean_Meta_substCore___lam__3___closed__25);
lean_inc_ref(v___y_1440_);
v___x_1451_ = l_Lean_MessageData_ofExpr(v___y_1440_);
v___x_1452_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1452_, 0, v___x_1450_);
lean_ctor_set(v___x_1452_, 1, v___x_1451_);
v___x_1453_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__27, &l_Lean_Meta_substCore___lam__3___closed__27_once, _init_l_Lean_Meta_substCore___lam__3___closed__27);
v___x_1454_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1454_, 0, v___x_1452_);
lean_ctor_set(v___x_1454_, 1, v___x_1453_);
lean_inc(v_fvarId_1444_);
v___x_1455_ = l_Lean_MessageData_ofName(v_fvarId_1444_);
v___x_1456_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1456_, 0, v___x_1454_);
lean_ctor_set(v___x_1456_, 1, v___x_1455_);
v___x_1457_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__29, &l_Lean_Meta_substCore___lam__3___closed__29_once, _init_l_Lean_Meta_substCore___lam__3___closed__29);
v___x_1458_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1458_, 0, v___x_1456_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
lean_inc(v_a_1443_);
v___x_1459_ = l_Lean_MessageData_ofExpr(v_a_1443_);
v___x_1460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1460_, 0, v___x_1458_);
lean_ctor_set(v___x_1460_, 1, v___x_1459_);
v___x_1461_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_1445_, v___x_1460_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_dec_ref_known(v___x_1461_, 1);
v___y_1406_ = v___x_1445_;
v___y_1407_ = v_fvarId_1444_;
v___y_1408_ = v_a_1443_;
v___y_1409_ = v___y_1440_;
v___y_1410_ = v___f_1446_;
v___y_1411_ = v___y_1094_;
v___y_1412_ = v___y_1095_;
v___y_1413_ = v___y_1096_;
v___y_1414_ = v___y_1097_;
goto v___jp_1405_;
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec(v_fvarId_1444_);
lean_dec(v_a_1443_);
lean_dec_ref_known(v___y_1440_, 1);
lean_del_object(v___x_1173_);
lean_del_object(v___x_1168_);
lean_del_object(v___x_1164_);
lean_dec(v_a_1138_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
lean_dec(v_mvarId_1087_);
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1461_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1461_);
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
lean_dec_ref(v___x_1442_);
lean_del_object(v___x_1173_);
lean_del_object(v___x_1168_);
lean_del_object(v___x_1164_);
lean_dec(v_a_1138_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
if (v_symm_1092_ == 0)
{
lean_object* v___x_1470_; 
v___x_1470_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__30));
v___y_1145_ = v___y_1440_;
v___y_1146_ = v___x_1470_;
goto v___jp_1144_;
}
else
{
lean_object* v___x_1471_; 
v___x_1471_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__31));
v___y_1145_ = v___y_1440_;
v___y_1146_ = v___x_1471_;
goto v___jp_1144_;
}
}
}
v___jp_1472_:
{
lean_object* v___x_1474_; 
v___x_1474_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1473_, v___y_1095_);
if (v_symm_1092_ == 0)
{
lean_object* v_a_1475_; 
lean_dec(v_fst_1170_);
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1475_);
lean_dec_ref(v___x_1474_);
v___y_1440_ = v_a_1475_;
v___y_1441_ = v_snd_1171_;
goto v___jp_1439_;
}
else
{
lean_object* v_a_1476_; 
lean_dec(v_snd_1171_);
v_a_1476_ = lean_ctor_get(v___x_1474_, 0);
lean_inc(v_a_1476_);
lean_dec_ref(v___x_1474_);
v___y_1440_ = v_a_1476_;
v___y_1441_ = v_fst_1170_;
goto v___jp_1439_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1488_; 
lean_dec_ref(v___x_1143_);
lean_dec(v_a_1138_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
lean_dec(v_mvarId_1087_);
v_a_1481_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1483_ = v___x_1158_;
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1158_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1488_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
lean_object* v___x_1486_; 
if (v_isShared_1484_ == 0)
{
v___x_1486_ = v___x_1483_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_a_1481_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
v___jp_1144_:
{
lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; 
v___x_1147_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__3, &l_Lean_Meta_substCore___lam__3___closed__3_once, _init_l_Lean_Meta_substCore___lam__3___closed__3);
lean_inc_ref(v___y_1146_);
v___x_1148_ = l_Lean_stringToMessageData(v___y_1146_);
v___x_1149_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1149_, 0, v___x_1147_);
lean_ctor_set(v___x_1149_, 1, v___x_1148_);
v___x_1150_ = l_Lean_indentExpr(v___x_1143_);
v___x_1151_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__5, &l_Lean_Meta_substCore___lam__3___closed__5_once, _init_l_Lean_Meta_substCore___lam__3___closed__5);
v___x_1153_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1152_);
v___x_1154_ = l_Lean_indentExpr(v___y_1145_);
v___x_1155_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
v___x_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
v___x_1157_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1139_, v_mvarId_1087_, v___x_1156_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
return v___x_1157_;
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_dec(v_a_1138_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
lean_dec(v_mvarId_1087_);
v_a_1489_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1141_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1141_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_dec(v_a_1138_);
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
lean_dec(v_mvarId_1087_);
v_a_1497_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1140_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1140_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_dec(v___y_1097_);
lean_dec_ref(v___y_1096_);
lean_dec(v___y_1095_);
lean_dec_ref(v___y_1094_);
lean_dec(v_fvarSubst_1091_);
lean_dec(v_hFVarId_1088_);
lean_dec(v_mvarId_1087_);
v_a_1505_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1137_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1137_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
v___jp_1099_:
{
if (v_clearH_1090_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1103_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
v___x_1107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1107_, 0, v_fvarSubst_1091_);
lean_ctor_set(v___x_1107_, 1, v___y_1104_);
v___x_1108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; 
v___x_1109_ = l_Lean_MVarId_clear(v___y_1104_, v___y_1103_, v___y_1105_, v___y_1106_, v___y_1100_, v___y_1102_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v___x_1111_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v___x_1111_ = l_Lean_MVarId_clear(v_a_1110_, v___y_1101_, v___y_1105_, v___y_1106_, v___y_1100_, v___y_1102_);
lean_dec(v___y_1102_);
lean_dec_ref(v___y_1100_);
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1120_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1120_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1114_ = v___x_1111_;
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1111_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1120_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1116_; lean_object* v___x_1118_; 
v___x_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1116_, 0, v_fvarSubst_1091_);
lean_ctor_set(v___x_1116_, 1, v_a_1112_);
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v___x_1116_);
v___x_1118_ = v___x_1114_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_fvarSubst_1091_);
v_a_1121_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1111_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1111_);
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
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v___y_1106_);
lean_dec_ref(v___y_1105_);
lean_dec(v___y_1102_);
lean_dec(v___y_1101_);
lean_dec_ref(v___y_1100_);
lean_dec(v_fvarSubst_1091_);
v_a_1129_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1109_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1109_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_substCore___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1087_ = stack[0].m_obj;
lean_object* v_hFVarId_1088_ = stack[1].m_obj;
lean_object* v___x_1089_ = stack[2].m_obj;
uint8_t v_clearH_1090_ = stack[3].m_num;
lean_object* v_fvarSubst_1091_ = stack[4].m_obj;
uint8_t v_symm_1092_ = stack[5].m_num;
uint8_t v_tryToSkip_1093_ = stack[6].m_num;
lean_object* v___y_1094_ = stack[7].m_obj;
lean_object* v___y_1095_ = stack[8].m_obj;
lean_object* v___y_1096_ = stack[9].m_obj;
lean_object* v___y_1097_ = stack[10].m_obj;
lean_object* v_res_1513_;
v_res_1513_ = l_Lean_Meta_substCore___lam__3(v_mvarId_1087_, v_hFVarId_1088_, v___x_1089_, v_clearH_1090_, v_fvarSubst_1091_, v_symm_1092_, v_tryToSkip_1093_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
stack->m_obj
 = v_res_1513_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3___boxed(lean_object* v_mvarId_1514_, lean_object* v_hFVarId_1515_, lean_object* v___x_1516_, lean_object* v_clearH_1517_, lean_object* v_fvarSubst_1518_, lean_object* v_symm_1519_, lean_object* v_tryToSkip_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_, lean_object* v___y_1524_, lean_object* v___y_1525_){
_start:
{
uint8_t v_clearH_boxed_1526_; uint8_t v_symm_boxed_1527_; uint8_t v_tryToSkip_boxed_1528_; lean_object* v_res_1529_; 
v_clearH_boxed_1526_ = lean_unbox(v_clearH_1517_);
v_symm_boxed_1527_ = lean_unbox(v_symm_1519_);
v_tryToSkip_boxed_1528_ = lean_unbox(v_tryToSkip_1520_);
v_res_1529_ = l_Lean_Meta_substCore___lam__3(v_mvarId_1514_, v_hFVarId_1515_, v___x_1516_, v_clearH_boxed_1526_, v_fvarSubst_1518_, v_symm_boxed_1527_, v_tryToSkip_boxed_1528_, v___y_1521_, v___y_1522_, v___y_1523_, v___y_1524_);
lean_dec(v___x_1516_);
return v_res_1529_;
}
}
lean_object* l_Lean_Meta_substCore(lean_object* v_mvarId_1530_, lean_object* v_hFVarId_1531_, uint8_t v_symm_1532_, lean_object* v_fvarSubst_1533_, uint8_t v_clearH_1534_, uint8_t v_tryToSkip_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___f_1545_; lean_object* v___x_1546_; 
v___x_1541_ = lean_box(0);
v___x_1542_ = lean_box(v_clearH_1534_);
v___x_1543_ = lean_box(v_symm_1532_);
v___x_1544_ = lean_box(v_tryToSkip_1535_);
lean_inc(v_mvarId_1530_);
v___f_1545_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__3___boxed), 12, 7);
lean_closure_set(v___f_1545_, 0, v_mvarId_1530_);
lean_closure_set(v___f_1545_, 1, v_hFVarId_1531_);
lean_closure_set(v___f_1545_, 2, v___x_1541_);
lean_closure_set(v___f_1545_, 3, v___x_1542_);
lean_closure_set(v___f_1545_, 4, v_fvarSubst_1533_);
lean_closure_set(v___f_1545_, 5, v___x_1543_);
lean_closure_set(v___f_1545_, 6, v___x_1544_);
v___x_1546_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1530_, v___f_1545_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
return v___x_1546_;
}
}
LEAN_EXPORT void l_Lean_Meta_substCore_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1530_ = stack[0].m_obj;
lean_object* v_hFVarId_1531_ = stack[1].m_obj;
uint8_t v_symm_1532_ = stack[2].m_num;
lean_object* v_fvarSubst_1533_ = stack[3].m_obj;
uint8_t v_clearH_1534_ = stack[4].m_num;
uint8_t v_tryToSkip_1535_ = stack[5].m_num;
lean_object* v_a_1536_ = stack[6].m_obj;
lean_object* v_a_1537_ = stack[7].m_obj;
lean_object* v_a_1538_ = stack[8].m_obj;
lean_object* v_a_1539_ = stack[9].m_obj;
lean_object* v_res_1547_;
v_res_1547_ = l_Lean_Meta_substCore(v_mvarId_1530_, v_hFVarId_1531_, v_symm_1532_, v_fvarSubst_1533_, v_clearH_1534_, v_tryToSkip_1535_, v_a_1536_, v_a_1537_, v_a_1538_, v_a_1539_);
stack->m_obj
 = v_res_1547_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* v_mvarId_1548_, lean_object* v_hFVarId_1549_, lean_object* v_symm_1550_, lean_object* v_fvarSubst_1551_, lean_object* v_clearH_1552_, lean_object* v_tryToSkip_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v_a_1558_){
_start:
{
uint8_t v_symm_boxed_1559_; uint8_t v_clearH_boxed_1560_; uint8_t v_tryToSkip_boxed_1561_; lean_object* v_res_1562_; 
v_symm_boxed_1559_ = lean_unbox(v_symm_1550_);
v_clearH_boxed_1560_ = lean_unbox(v_clearH_1552_);
v_tryToSkip_boxed_1561_ = lean_unbox(v_tryToSkip_1553_);
v_res_1562_ = l_Lean_Meta_substCore(v_mvarId_1548_, v_hFVarId_1549_, v_symm_boxed_1559_, v_fvarSubst_1551_, v_clearH_boxed_1560_, v_tryToSkip_boxed_1561_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_);
lean_dec(v_a_1557_);
lean_dec_ref(v_a_1556_);
lean_dec(v_a_1555_);
lean_dec_ref(v_a_1554_);
return v_res_1562_;
}
}
lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1(lean_object* v_fst_1563_, lean_object* v_fst_1564_, lean_object* v_n_1565_, lean_object* v_i_1566_, lean_object* v_a_1567_, lean_object* v_a_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_){
_start:
{
lean_object* v___x_1574_; 
v___x_1574_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_1563_, v_fst_1564_, v_n_1565_, v_i_1566_, v_a_1568_);
return v___x_1574_;
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1563_ = stack[0].m_obj;
lean_object* v_fst_1564_ = stack[1].m_obj;
lean_object* v_n_1565_ = stack[2].m_obj;
lean_object* v_i_1566_ = stack[3].m_obj;
lean_object* v_a_1568_ = stack[5].m_obj;
lean_object* v___y_1569_ = stack[6].m_obj;
lean_object* v___y_1570_ = stack[7].m_obj;
lean_object* v___y_1571_ = stack[8].m_obj;
lean_object* v___y_1572_ = stack[9].m_obj;
lean_object* v_res_1575_;
v_res_1575_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1(v_fst_1563_, v_fst_1564_, v_n_1565_, v_i_1566_, lean_box(0), v_a_1568_, v___y_1569_, v___y_1570_, v___y_1571_, v___y_1572_);
stack->m_obj
 = v_res_1575_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___boxed(lean_object* v_fst_1576_, lean_object* v_fst_1577_, lean_object* v_n_1578_, lean_object* v_i_1579_, lean_object* v_a_1580_, lean_object* v_a_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1(v_fst_1576_, v_fst_1577_, v_n_1578_, v_i_1579_, v_a_1580_, v_a_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v_n_1578_);
lean_dec_ref(v_fst_1577_);
lean_dec_ref(v_fst_1576_);
return v_res_1587_;
}
}
lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4(lean_object* v_mvarId_1588_, lean_object* v_val_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_mvarId_1588_, v_val_1589_, v___y_1591_);
return v___x_1595_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1588_ = stack[0].m_obj;
lean_object* v_val_1589_ = stack[1].m_obj;
lean_object* v___y_1590_ = stack[2].m_obj;
lean_object* v___y_1591_ = stack[3].m_obj;
lean_object* v___y_1592_ = stack[4].m_obj;
lean_object* v___y_1593_ = stack[5].m_obj;
lean_object* v_res_1596_;
v_res_1596_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4(v_mvarId_1588_, v_val_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
stack->m_obj
 = v_res_1596_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___boxed(lean_object* v_mvarId_1597_, lean_object* v_val_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4(v_mvarId_1597_, v_val_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1604_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7(lean_object* v_00_u03b1_1605_, lean_object* v_name_1606_, uint8_t v_bi_1607_, lean_object* v_type_1608_, lean_object* v_k_1609_, uint8_t v_kind_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; 
v___x_1616_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_1606_, v_bi_1607_, v_type_1608_, v_k_1609_, v_kind_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
return v___x_1616_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1606_ = stack[1].m_obj;
uint8_t v_bi_1607_ = stack[2].m_num;
lean_object* v_type_1608_ = stack[3].m_obj;
lean_object* v_k_1609_ = stack[4].m_obj;
uint8_t v_kind_1610_ = stack[5].m_num;
lean_object* v___y_1611_ = stack[6].m_obj;
lean_object* v___y_1612_ = stack[7].m_obj;
lean_object* v___y_1613_ = stack[8].m_obj;
lean_object* v___y_1614_ = stack[9].m_obj;
lean_object* v_res_1617_;
v_res_1617_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7(lean_box(0), v_name_1606_, v_bi_1607_, v_type_1608_, v_k_1609_, v_kind_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
stack->m_obj
 = v_res_1617_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1618_, lean_object* v_name_1619_, lean_object* v_bi_1620_, lean_object* v_type_1621_, lean_object* v_k_1622_, lean_object* v_kind_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
uint8_t v_bi_boxed_1629_; uint8_t v_kind_boxed_1630_; lean_object* v_res_1631_; 
v_bi_boxed_1629_ = lean_unbox(v_bi_1620_);
v_kind_boxed_1630_ = lean_unbox(v_kind_1623_);
v_res_1631_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7(v_00_u03b1_1618_, v_name_1619_, v_bi_boxed_1629_, v_type_1621_, v_k_1622_, v_kind_boxed_1630_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1631_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5(lean_object* v_00_u03b1_1632_, lean_object* v_name_1633_, lean_object* v_type_1634_, lean_object* v_k_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v_name_1633_, v_type_1634_, v_k_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
return v___x_1641_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1633_ = stack[1].m_obj;
lean_object* v_type_1634_ = stack[2].m_obj;
lean_object* v_k_1635_ = stack[3].m_obj;
lean_object* v___y_1636_ = stack[4].m_obj;
lean_object* v___y_1637_ = stack[5].m_obj;
lean_object* v___y_1638_ = stack[6].m_obj;
lean_object* v___y_1639_ = stack[7].m_obj;
lean_object* v_res_1642_;
v_res_1642_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5(lean_box(0), v_name_1633_, v_type_1634_, v_k_1635_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
stack->m_obj
 = v_res_1642_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___boxed(lean_object* v_00_u03b1_1643_, lean_object* v_name_1644_, lean_object* v_type_1645_, lean_object* v_k_1646_, lean_object* v___y_1647_, lean_object* v___y_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_){
_start:
{
lean_object* v_res_1652_; 
v_res_1652_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5(v_00_u03b1_1643_, v_name_1644_, v_type_1645_, v_k_1646_, v___y_1647_, v___y_1648_, v___y_1649_, v___y_1650_);
lean_dec(v___y_1650_);
lean_dec_ref(v___y_1649_);
lean_dec(v___y_1648_);
lean_dec_ref(v___y_1647_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5(lean_object* v_00_u03b2_1653_, lean_object* v_x_1654_, lean_object* v_x_1655_, lean_object* v_x_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5___redArg(v_x_1654_, v_x_1655_, v_x_1656_);
return v___x_1657_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_1658_, lean_object* v_x_1659_, size_t v_x_1660_, size_t v_x_1661_, lean_object* v_x_1662_, lean_object* v_x_1663_){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_1659_, v_x_1660_, v_x_1661_, v_x_1662_, v_x_1663_);
return v___x_1664_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1659_ = stack[1].m_obj;
size_t v_x_1660_ = stack[2].m_num;
size_t v_x_1661_ = stack[3].m_num;
lean_object* v_x_1662_ = stack[4].m_obj;
lean_object* v_x_1663_ = stack[5].m_obj;
lean_object* v_res_1665_;
v_res_1665_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8(lean_box(0), v_x_1659_, v_x_1660_, v_x_1661_, v_x_1662_, v_x_1663_);
stack->m_obj
 = v_res_1665_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_){
_start:
{
size_t v_x_30959__boxed_1672_; size_t v_x_30960__boxed_1673_; lean_object* v_res_1674_; 
v_x_30959__boxed_1672_ = lean_unbox_usize(v_x_1668_);
lean_dec(v_x_1668_);
v_x_30960__boxed_1673_ = lean_unbox_usize(v_x_1669_);
lean_dec(v_x_1669_);
v_res_1674_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8(v_00_u03b2_1666_, v_x_1667_, v_x_30959__boxed_1672_, v_x_30960__boxed_1673_, v_x_1670_, v_x_1671_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13(lean_object* v_00_u03b2_1675_, lean_object* v_n_1676_, lean_object* v_k_1677_, lean_object* v_v_1678_){
_start:
{
lean_object* v___x_1679_; 
v___x_1679_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13___redArg(v_n_1676_, v_k_1677_, v_v_1678_);
return v___x_1679_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1680_, size_t v_depth_1681_, lean_object* v_keys_1682_, lean_object* v_vals_1683_, lean_object* v_heq_1684_, lean_object* v_i_1685_, lean_object* v_entries_1686_){
_start:
{
lean_object* v___x_1687_; 
v___x_1687_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(v_depth_1681_, v_keys_1682_, v_vals_1683_, v_i_1685_, v_entries_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14_0interp(lean_interpreter_value* stack)
{
size_t v_depth_1681_ = stack[1].m_num;
lean_object* v_keys_1682_ = stack[2].m_obj;
lean_object* v_vals_1683_ = stack[3].m_obj;
lean_object* v_i_1685_ = stack[5].m_obj;
lean_object* v_entries_1686_ = stack[6].m_obj;
lean_object* v_res_1688_;
v_res_1688_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14(lean_box(0), v_depth_1681_, v_keys_1682_, v_vals_1683_, lean_box(0), v_i_1685_, v_entries_1686_);
stack->m_obj
 = v_res_1688_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1689_, lean_object* v_depth_1690_, lean_object* v_keys_1691_, lean_object* v_vals_1692_, lean_object* v_heq_1693_, lean_object* v_i_1694_, lean_object* v_entries_1695_){
_start:
{
size_t v_depth_boxed_1696_; lean_object* v_res_1697_; 
v_depth_boxed_1696_ = lean_unbox_usize(v_depth_1690_);
lean_dec(v_depth_1690_);
v_res_1697_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14(v_00_u03b2_1689_, v_depth_boxed_1696_, v_keys_1691_, v_vals_1692_, v_heq_1693_, v_i_1694_, v_entries_1695_);
lean_dec_ref(v_vals_1692_);
lean_dec_ref(v_keys_1691_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
lean_object* v___x_1703_; 
v___x_1703_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14___redArg(v_x_1699_, v_x_1700_, v_x_1701_, v_x_1702_);
return v___x_1703_;
}
}
lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* v_fvarId_1707_, lean_object* v_mvarId_1708_, uint8_t v_tryToClear_1709_, lean_object* v___y_1710_, lean_object* v___y_1711_, lean_object* v___y_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; 
lean_inc(v_fvarId_1707_);
v___x_1715_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1707_, v___y_1710_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v___x_1717_ = l_Lean_LocalDecl_type(v_a_1716_);
lean_inc(v___y_1713_);
lean_inc_ref(v___y_1712_);
lean_inc(v___y_1711_);
lean_inc_ref(v___y_1710_);
v___x_1718_ = lean_whnf(v___x_1717_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_a_1719_; lean_object* v___x_1721_; uint8_t v_isShared_1722_; uint8_t v_isSharedCheck_1803_; 
v_a_1719_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1803_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1803_ == 0)
{
v___x_1721_ = v___x_1718_;
v_isShared_1722_ = v_isSharedCheck_1803_;
goto v_resetjp_1720_;
}
else
{
lean_inc(v_a_1719_);
lean_dec(v___x_1718_);
v___x_1721_ = lean_box(0);
v_isShared_1722_ = v_isSharedCheck_1803_;
goto v_resetjp_1720_;
}
v_resetjp_1720_:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; uint8_t v___x_1725_; 
v___x_1723_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_1724_ = lean_unsigned_to_nat(4u);
v___x_1725_ = l_Lean_Expr_isAppOfArity(v_a_1719_, v___x_1723_, v___x_1724_);
if (v___x_1725_ == 0)
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
lean_dec(v_a_1719_);
lean_dec(v_a_1716_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
v___x_1726_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1726_, 0, v_fvarId_1707_);
lean_ctor_set(v___x_1726_, 1, v_mvarId_1708_);
if (v_isShared_1722_ == 0)
{
lean_ctor_set(v___x_1721_, 0, v___x_1726_);
v___x_1728_ = v___x_1721_;
goto v_reusejp_1727_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
v___x_1728_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1727_;
}
v_reusejp_1727_:
{
return v___x_1728_;
}
}
else
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_del_object(v___x_1721_);
v___x_1730_ = l_Lean_Expr_appFn_x21(v_a_1719_);
v___x_1731_ = l_Lean_Expr_appFn_x21(v___x_1730_);
v___x_1732_ = l_Lean_Expr_appFn_x21(v___x_1731_);
v___x_1733_ = l_Lean_Expr_appArg_x21(v___x_1732_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = l_Lean_Expr_appArg_x21(v___x_1731_);
lean_dec_ref(v___x_1731_);
v___x_1735_ = l_Lean_Expr_appArg_x21(v___x_1730_);
lean_dec_ref(v___x_1730_);
v___x_1736_ = l_Lean_Expr_appArg_x21(v_a_1719_);
lean_dec(v_a_1719_);
v___x_1737_ = l_Lean_Meta_isExprDefEq(v___x_1733_, v___x_1735_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1794_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1740_ = v___x_1737_;
v_isShared_1741_ = v_isSharedCheck_1794_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_a_1738_);
lean_dec(v___x_1737_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1794_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
uint8_t v___x_1742_; 
v___x_1742_ = lean_unbox(v_a_1738_);
if (v___x_1742_ == 0)
{
lean_object* v___x_1743_; lean_object* v___x_1745_; 
lean_dec(v_a_1738_);
lean_dec_ref(v___x_1736_);
lean_dec_ref(v___x_1734_);
lean_dec(v_a_1716_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
v___x_1743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1743_, 0, v_fvarId_1707_);
lean_ctor_set(v___x_1743_, 1, v_mvarId_1708_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 0, v___x_1743_);
v___x_1745_ = v___x_1740_;
goto v_reusejp_1744_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1743_);
v___x_1745_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1744_;
}
v_reusejp_1744_:
{
return v___x_1745_;
}
}
else
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_del_object(v___x_1740_);
lean_inc(v_fvarId_1707_);
v___x_1747_ = l_Lean_mkFVar(v_fvarId_1707_);
v___x_1748_ = l_Lean_Meta_mkEqOfHEq(v___x_1747_, v___x_1725_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1748_) == 0)
{
lean_object* v_a_1749_; lean_object* v___x_1750_; 
v_a_1749_ = lean_ctor_get(v___x_1748_, 0);
lean_inc(v_a_1749_);
lean_dec_ref_known(v___x_1748_, 1);
v___x_1750_ = l_Lean_Meta_mkEq(v___x_1734_, v___x_1736_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_a_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = l_Lean_LocalDecl_userName(v_a_1716_);
lean_dec(v_a_1716_);
v___x_1753_ = l_Lean_MVarId_assert(v_mvarId_1708_, v___x_1752_, v_a_1751_, v_a_1749_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1753_) == 0)
{
if (v_tryToClear_1709_ == 0)
{
lean_object* v_a_1754_; uint8_t v___x_1755_; lean_object* v___x_1756_; 
lean_dec(v_fvarId_1707_);
v_a_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1755_ = lean_unbox(v_a_1738_);
lean_dec(v_a_1738_);
v___x_1756_ = l_Lean_Meta_intro1Core(v_a_1754_, v___x_1755_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v___x_1756_;
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1758_; 
v_a_1757_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_a_1757_);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1758_ = l_Lean_MVarId_tryClear(v_a_1757_, v_fvarId_1707_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; uint8_t v___x_1760_; lean_object* v___x_1761_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1758_, 1);
v___x_1760_ = lean_unbox(v_a_1738_);
lean_dec(v_a_1738_);
v___x_1761_ = l_Lean_Meta_intro1Core(v_a_1759_, v___x_1760_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
return v___x_1761_;
}
else
{
lean_object* v_a_1762_; lean_object* v___x_1764_; uint8_t v_isShared_1765_; uint8_t v_isSharedCheck_1769_; 
lean_dec(v_a_1738_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
v_a_1762_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1758_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1758_);
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
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec(v_a_1738_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_fvarId_1707_);
v_a_1770_ = lean_ctor_get(v___x_1753_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1753_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1753_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1753_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v___x_1775_; 
if (v_isShared_1773_ == 0)
{
v___x_1775_ = v___x_1772_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_a_1770_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
}
}
else
{
lean_object* v_a_1778_; lean_object* v___x_1780_; uint8_t v_isShared_1781_; uint8_t v_isSharedCheck_1785_; 
lean_dec(v_a_1749_);
lean_dec(v_a_1738_);
lean_dec(v_a_1716_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_mvarId_1708_);
lean_dec(v_fvarId_1707_);
v_a_1778_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1785_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1785_ == 0)
{
v___x_1780_ = v___x_1750_;
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
else
{
lean_inc(v_a_1778_);
lean_dec(v___x_1750_);
v___x_1780_ = lean_box(0);
v_isShared_1781_ = v_isSharedCheck_1785_;
goto v_resetjp_1779_;
}
v_resetjp_1779_:
{
lean_object* v___x_1783_; 
if (v_isShared_1781_ == 0)
{
v___x_1783_ = v___x_1780_;
goto v_reusejp_1782_;
}
else
{
lean_object* v_reuseFailAlloc_1784_; 
v_reuseFailAlloc_1784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1784_, 0, v_a_1778_);
v___x_1783_ = v_reuseFailAlloc_1784_;
goto v_reusejp_1782_;
}
v_reusejp_1782_:
{
return v___x_1783_;
}
}
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
lean_dec(v_a_1738_);
lean_dec_ref(v___x_1736_);
lean_dec_ref(v___x_1734_);
lean_dec(v_a_1716_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_mvarId_1708_);
lean_dec(v_fvarId_1707_);
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
}
else
{
lean_object* v_a_1795_; lean_object* v___x_1797_; uint8_t v_isShared_1798_; uint8_t v_isSharedCheck_1802_; 
lean_dec_ref(v___x_1736_);
lean_dec_ref(v___x_1734_);
lean_dec(v_a_1716_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_mvarId_1708_);
lean_dec(v_fvarId_1707_);
v_a_1795_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1802_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1802_ == 0)
{
v___x_1797_ = v___x_1737_;
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
else
{
lean_inc(v_a_1795_);
lean_dec(v___x_1737_);
v___x_1797_ = lean_box(0);
v_isShared_1798_ = v_isSharedCheck_1802_;
goto v_resetjp_1796_;
}
v_resetjp_1796_:
{
lean_object* v___x_1800_; 
if (v_isShared_1798_ == 0)
{
v___x_1800_ = v___x_1797_;
goto v_reusejp_1799_;
}
else
{
lean_object* v_reuseFailAlloc_1801_; 
v_reuseFailAlloc_1801_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1801_, 0, v_a_1795_);
v___x_1800_ = v_reuseFailAlloc_1801_;
goto v_reusejp_1799_;
}
v_reusejp_1799_:
{
return v___x_1800_;
}
}
}
}
}
}
else
{
lean_object* v_a_1804_; lean_object* v___x_1806_; uint8_t v_isShared_1807_; uint8_t v_isSharedCheck_1811_; 
lean_dec(v_a_1716_);
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_mvarId_1708_);
lean_dec(v_fvarId_1707_);
v_a_1804_ = lean_ctor_get(v___x_1718_, 0);
v_isSharedCheck_1811_ = !lean_is_exclusive(v___x_1718_);
if (v_isSharedCheck_1811_ == 0)
{
v___x_1806_ = v___x_1718_;
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
else
{
lean_inc(v_a_1804_);
lean_dec(v___x_1718_);
v___x_1806_ = lean_box(0);
v_isShared_1807_ = v_isSharedCheck_1811_;
goto v_resetjp_1805_;
}
v_resetjp_1805_:
{
lean_object* v___x_1809_; 
if (v_isShared_1807_ == 0)
{
v___x_1809_ = v___x_1806_;
goto v_reusejp_1808_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_a_1804_);
v___x_1809_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1808_;
}
v_reusejp_1808_:
{
return v___x_1809_;
}
}
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
lean_dec(v___y_1713_);
lean_dec_ref(v___y_1712_);
lean_dec(v___y_1711_);
lean_dec_ref(v___y_1710_);
lean_dec(v_mvarId_1708_);
lean_dec(v_fvarId_1707_);
v_a_1812_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1715_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1715_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_heqToEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fvarId_1707_ = stack[0].m_obj;
lean_object* v_mvarId_1708_ = stack[1].m_obj;
uint8_t v_tryToClear_1709_ = stack[2].m_num;
lean_object* v___y_1710_ = stack[3].m_obj;
lean_object* v___y_1711_ = stack[4].m_obj;
lean_object* v___y_1712_ = stack[5].m_obj;
lean_object* v___y_1713_ = stack[6].m_obj;
lean_object* v_res_1820_;
v_res_1820_ = l_Lean_Meta_heqToEq___lam__0(v_fvarId_1707_, v_mvarId_1708_, v_tryToClear_1709_, v___y_1710_, v___y_1711_, v___y_1712_, v___y_1713_);
stack->m_obj
 = v_res_1820_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object* v_fvarId_1821_, lean_object* v_mvarId_1822_, lean_object* v_tryToClear_1823_, lean_object* v___y_1824_, lean_object* v___y_1825_, lean_object* v___y_1826_, lean_object* v___y_1827_, lean_object* v___y_1828_){
_start:
{
uint8_t v_tryToClear_boxed_1829_; lean_object* v_res_1830_; 
v_tryToClear_boxed_1829_ = lean_unbox(v_tryToClear_1823_);
v_res_1830_ = l_Lean_Meta_heqToEq___lam__0(v_fvarId_1821_, v_mvarId_1822_, v_tryToClear_boxed_1829_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_);
return v_res_1830_;
}
}
lean_object* l_Lean_Meta_heqToEq(lean_object* v_mvarId_1831_, lean_object* v_fvarId_1832_, uint8_t v_tryToClear_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v___x_1839_; lean_object* v___f_1840_; lean_object* v___x_1841_; 
v___x_1839_ = lean_box(v_tryToClear_1833_);
lean_inc(v_mvarId_1831_);
v___f_1840_ = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1840_, 0, v_fvarId_1832_);
lean_closure_set(v___f_1840_, 1, v_mvarId_1831_);
lean_closure_set(v___f_1840_, 2, v___x_1839_);
v___x_1841_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1831_, v___f_1840_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
return v___x_1841_;
}
}
LEAN_EXPORT void l_Lean_Meta_heqToEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1831_ = stack[0].m_obj;
lean_object* v_fvarId_1832_ = stack[1].m_obj;
uint8_t v_tryToClear_1833_ = stack[2].m_num;
lean_object* v_a_1834_ = stack[3].m_obj;
lean_object* v_a_1835_ = stack[4].m_obj;
lean_object* v_a_1836_ = stack[5].m_obj;
lean_object* v_a_1837_ = stack[6].m_obj;
lean_object* v_res_1842_;
v_res_1842_ = l_Lean_Meta_heqToEq(v_mvarId_1831_, v_fvarId_1832_, v_tryToClear_1833_, v_a_1834_, v_a_1835_, v_a_1836_, v_a_1837_);
stack->m_obj
 = v_res_1842_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* v_mvarId_1843_, lean_object* v_fvarId_1844_, lean_object* v_tryToClear_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_, lean_object* v_a_1849_, lean_object* v_a_1850_){
_start:
{
uint8_t v_tryToClear_boxed_1851_; lean_object* v_res_1852_; 
v_tryToClear_boxed_1851_ = lean_unbox(v_tryToClear_1845_);
v_res_1852_ = l_Lean_Meta_heqToEq(v_mvarId_1843_, v_fvarId_1844_, v_tryToClear_boxed_1851_, v_a_1846_, v_a_1847_, v_a_1848_, v_a_1849_);
lean_dec(v_a_1849_);
lean_dec_ref(v_a_1848_);
lean_dec(v_a_1847_);
lean_dec_ref(v_a_1846_);
return v_res_1852_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1856_, lean_object* v_as_1857_, size_t v_sz_1858_, size_t v_i_1859_, lean_object* v_b_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_a_1867_; uint8_t v___x_1871_; 
v___x_1871_ = lean_usize_dec_lt(v_i_1859_, v_sz_1858_);
if (v___x_1871_ == 0)
{
lean_object* v___x_1872_; 
lean_dec(v_x_1856_);
v___x_1872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1872_, 0, v_b_1860_);
return v___x_1872_;
}
else
{
lean_object* v___x_1873_; lean_object* v_a_1875_; lean_object* v___x_1879_; lean_object* v_a_1880_; 
lean_dec_ref(v_b_1860_);
v___x_1873_ = lean_box(0);
v___x_1879_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1880_ = lean_array_uget(v_as_1857_, v_i_1859_);
if (lean_obj_tag(v_a_1880_) == 0)
{
v_a_1867_ = v___x_1879_;
goto v___jp_1866_;
}
else
{
lean_object* v_val_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1968_; 
v_val_1881_ = lean_ctor_get(v_a_1880_, 0);
v_isSharedCheck_1968_ = !lean_is_exclusive(v_a_1880_);
if (v_isSharedCheck_1968_ == 0)
{
v___x_1883_ = v_a_1880_;
v_isShared_1884_ = v_isSharedCheck_1968_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_val_1881_);
lean_dec(v_a_1880_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1968_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
uint8_t v___x_1892_; 
v___x_1892_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1881_);
if (v___x_1892_ == 0)
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = l_Lean_LocalDecl_type(v_val_1881_);
v___x_1899_ = l_Lean_Meta_matchEq_x3f(v___x_1898_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
if (lean_obj_tag(v_a_1900_) == 1)
{
lean_object* v_val_1901_; lean_object* v_snd_1902_; lean_object* v_fst_1903_; lean_object* v_snd_1904_; lean_object* v___x_1905_; 
v_val_1901_ = lean_ctor_get(v_a_1900_, 0);
lean_inc(v_val_1901_);
lean_dec_ref_known(v_a_1900_, 1);
v_snd_1902_ = lean_ctor_get(v_val_1901_, 1);
lean_inc(v_snd_1902_);
lean_dec(v_val_1901_);
v_fst_1903_ = lean_ctor_get(v_snd_1902_, 0);
lean_inc(v_fst_1903_);
v_snd_1904_ = lean_ctor_get(v_snd_1902_, 1);
lean_inc(v_snd_1904_);
lean_dec(v_snd_1902_);
v___x_1905_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1903_, v___y_1862_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; lean_object* v___x_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref_known(v___x_1905_, 1);
v___x_1907_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1904_, v___y_1862_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; lean_object* v___y_1910_; uint8_t v___y_1911_; lean_object* v___y_1924_; uint8_t v___y_1929_; uint8_t v___x_1941_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref_known(v___x_1907_, 1);
v___x_1941_ = l_Lean_Expr_isFVar(v_a_1908_);
if (v___x_1941_ == 0)
{
v___y_1929_ = v___x_1892_;
goto v___jp_1928_;
}
else
{
lean_object* v___x_1942_; uint8_t v___x_1943_; 
v___x_1942_ = l_Lean_Expr_fvarId_x21(v_a_1908_);
v___x_1943_ = l_Lean_instBEqFVarId_beq(v___x_1942_, v_x_1856_);
lean_dec(v___x_1942_);
v___y_1929_ = v___x_1943_;
goto v___jp_1928_;
}
v___jp_1909_:
{
if (v___y_1911_ == 0)
{
lean_dec(v_a_1908_);
lean_dec(v_val_1881_);
v_a_1867_ = v___x_1879_;
goto v___jp_1866_;
}
else
{
lean_object* v___x_1912_; 
lean_inc(v_x_1856_);
v___x_1912_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1908_, v_x_1856_, v___y_1910_);
if (lean_obj_tag(v___x_1912_) == 0)
{
lean_object* v_a_1913_; uint8_t v___x_1914_; 
v_a_1913_ = lean_ctor_get(v___x_1912_, 0);
lean_inc(v_a_1913_);
lean_dec_ref_known(v___x_1912_, 1);
v___x_1914_ = lean_unbox(v_a_1913_);
lean_dec(v_a_1913_);
if (v___x_1914_ == 0)
{
lean_dec(v_x_1856_);
goto v___jp_1893_;
}
else
{
if (v___x_1892_ == 0)
{
lean_dec(v_val_1881_);
v_a_1867_ = v___x_1879_;
goto v___jp_1866_;
}
else
{
lean_dec(v_x_1856_);
goto v___jp_1893_;
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_val_1881_);
lean_dec(v_x_1856_);
v_a_1915_ = lean_ctor_get(v___x_1912_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1912_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1912_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1912_);
v___x_1917_ = lean_box(0);
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
v_resetjp_1916_:
{
lean_object* v___x_1920_; 
if (v_isShared_1918_ == 0)
{
v___x_1920_ = v___x_1917_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v_a_1915_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
return v___x_1920_;
}
}
}
}
}
v___jp_1923_:
{
uint8_t v___x_1925_; 
v___x_1925_ = l_Lean_Expr_isFVar(v_a_1906_);
if (v___x_1925_ == 0)
{
lean_dec(v_a_1906_);
v___y_1910_ = v___y_1924_;
v___y_1911_ = v___x_1892_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1926_; uint8_t v___x_1927_; 
v___x_1926_ = l_Lean_Expr_fvarId_x21(v_a_1906_);
lean_dec(v_a_1906_);
v___x_1927_ = l_Lean_instBEqFVarId_beq(v___x_1926_, v_x_1856_);
lean_dec(v___x_1926_);
v___y_1910_ = v___y_1924_;
v___y_1911_ = v___x_1927_;
goto v___jp_1909_;
}
}
v___jp_1928_:
{
if (v___y_1929_ == 0)
{
lean_del_object(v___x_1883_);
v___y_1924_ = v___y_1862_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1930_; 
lean_inc(v_x_1856_);
lean_inc(v_a_1906_);
v___x_1930_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1906_, v_x_1856_, v___y_1862_);
if (lean_obj_tag(v___x_1930_) == 0)
{
lean_object* v_a_1931_; uint8_t v___x_1932_; 
v_a_1931_ = lean_ctor_get(v___x_1930_, 0);
lean_inc(v_a_1931_);
lean_dec_ref_known(v___x_1930_, 1);
v___x_1932_ = lean_unbox(v_a_1931_);
lean_dec(v_a_1931_);
if (v___x_1932_ == 0)
{
lean_dec(v_a_1908_);
lean_dec(v_a_1906_);
lean_dec(v_x_1856_);
goto v___jp_1885_;
}
else
{
if (v___x_1892_ == 0)
{
lean_del_object(v___x_1883_);
v___y_1924_ = v___y_1862_;
goto v___jp_1923_;
}
else
{
lean_dec(v_a_1908_);
lean_dec(v_a_1906_);
lean_dec(v_x_1856_);
goto v___jp_1885_;
}
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_dec(v_a_1908_);
lean_dec(v_a_1906_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_dec(v_x_1856_);
v_a_1933_ = lean_ctor_get(v___x_1930_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1930_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1930_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1930_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1938_; 
if (v_isShared_1936_ == 0)
{
v___x_1938_ = v___x_1935_;
goto v_reusejp_1937_;
}
else
{
lean_object* v_reuseFailAlloc_1939_; 
v_reuseFailAlloc_1939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1939_, 0, v_a_1933_);
v___x_1938_ = v_reuseFailAlloc_1939_;
goto v_reusejp_1937_;
}
v_reusejp_1937_:
{
return v___x_1938_;
}
}
}
}
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v_a_1906_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_dec(v_x_1856_);
v_a_1944_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1907_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1907_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_snd_1904_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_dec(v_x_1856_);
v_a_1952_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1905_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1905_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
else
{
lean_dec(v_a_1900_);
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
v_a_1867_ = v___x_1879_;
goto v___jp_1866_;
}
}
else
{
lean_object* v_a_1960_; lean_object* v___x_1962_; uint8_t v_isShared_1963_; uint8_t v_isSharedCheck_1967_; 
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
lean_dec(v_x_1856_);
v_a_1960_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1967_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1967_ == 0)
{
v___x_1962_ = v___x_1899_;
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
else
{
lean_inc(v_a_1960_);
lean_dec(v___x_1899_);
v___x_1962_ = lean_box(0);
v_isShared_1963_ = v_isSharedCheck_1967_;
goto v_resetjp_1961_;
}
v_resetjp_1961_:
{
lean_object* v___x_1965_; 
if (v_isShared_1963_ == 0)
{
v___x_1965_ = v___x_1962_;
goto v_reusejp_1964_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_a_1960_);
v___x_1965_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1964_;
}
v_reusejp_1964_:
{
return v___x_1965_;
}
}
}
}
else
{
lean_del_object(v___x_1883_);
lean_dec(v_val_1881_);
v_a_1867_ = v___x_1879_;
goto v___jp_1866_;
}
v___jp_1885_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1890_; 
v___x_1886_ = l_Lean_LocalDecl_fvarId(v_val_1881_);
lean_dec(v_val_1881_);
v___x_1887_ = lean_box(v___x_1871_);
v___x_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1888_, 0, v___x_1886_);
lean_ctor_set(v___x_1888_, 1, v___x_1887_);
if (v_isShared_1884_ == 0)
{
lean_ctor_set(v___x_1883_, 0, v___x_1888_);
v___x_1890_ = v___x_1883_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
v_a_1875_ = v___x_1890_;
goto v___jp_1874_;
}
}
v___jp_1893_:
{
lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1894_ = l_Lean_LocalDecl_fvarId(v_val_1881_);
lean_dec(v_val_1881_);
v___x_1895_ = lean_box(v___x_1892_);
v___x_1896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1894_);
lean_ctor_set(v___x_1896_, 1, v___x_1895_);
v___x_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1897_, 0, v___x_1896_);
v_a_1875_ = v___x_1897_;
goto v___jp_1874_;
}
}
}
v___jp_1874_:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_a_1875_);
v___x_1877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1877_, 0, v___x_1876_);
lean_ctor_set(v___x_1877_, 1, v___x_1873_);
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v___x_1877_);
return v___x_1878_;
}
}
v___jp_1866_:
{
size_t v___x_1868_; size_t v___x_1869_; 
v___x_1868_ = ((size_t)1ULL);
v___x_1869_ = lean_usize_add(v_i_1859_, v___x_1868_);
lean_inc_ref(v_a_1867_);
v_i_1859_ = v___x_1869_;
v_b_1860_ = v_a_1867_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1856_ = stack[0].m_obj;
lean_object* v_as_1857_ = stack[1].m_obj;
size_t v_sz_1858_ = stack[2].m_num;
size_t v_i_1859_ = stack[3].m_num;
lean_object* v_b_1860_ = stack[4].m_obj;
lean_object* v___y_1861_ = stack[5].m_obj;
lean_object* v___y_1862_ = stack[6].m_obj;
lean_object* v___y_1863_ = stack[7].m_obj;
lean_object* v___y_1864_ = stack[8].m_obj;
lean_object* v_res_1969_;
v_res_1969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1856_, v_as_1857_, v_sz_1858_, v_i_1859_, v_b_1860_, v___y_1861_, v___y_1862_, v___y_1863_, v___y_1864_);
stack->m_obj
 = v_res_1969_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1970_, lean_object* v_as_1971_, lean_object* v_sz_1972_, lean_object* v_i_1973_, lean_object* v_b_1974_, lean_object* v___y_1975_, lean_object* v___y_1976_, lean_object* v___y_1977_, lean_object* v___y_1978_, lean_object* v___y_1979_){
_start:
{
size_t v_sz_boxed_1980_; size_t v_i_boxed_1981_; lean_object* v_res_1982_; 
v_sz_boxed_1980_ = lean_unbox_usize(v_sz_1972_);
lean_dec(v_sz_1972_);
v_i_boxed_1981_ = lean_unbox_usize(v_i_1973_);
lean_dec(v_i_1973_);
v_res_1982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1970_, v_as_1971_, v_sz_boxed_1980_, v_i_boxed_1981_, v_b_1974_, v___y_1975_, v___y_1976_, v___y_1977_, v___y_1978_);
lean_dec(v___y_1978_);
lean_dec_ref(v___y_1977_);
lean_dec(v___y_1976_);
lean_dec_ref(v___y_1975_);
lean_dec_ref(v_as_1971_);
return v_res_1982_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object* v_x_1983_, lean_object* v_as_1984_, size_t v_sz_1985_, size_t v_i_1986_, lean_object* v_b_1987_, lean_object* v___y_1988_, lean_object* v___y_1989_, lean_object* v___y_1990_, lean_object* v___y_1991_){
_start:
{
lean_object* v_a_1994_; uint8_t v___x_1998_; 
v___x_1998_ = lean_usize_dec_lt(v_i_1986_, v_sz_1985_);
if (v___x_1998_ == 0)
{
lean_object* v___x_1999_; 
lean_dec(v_x_1983_);
v___x_1999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1999_, 0, v_b_1987_);
return v___x_1999_;
}
else
{
lean_object* v___x_2000_; lean_object* v_a_2002_; lean_object* v___x_2006_; lean_object* v_a_2007_; 
lean_dec_ref(v_b_1987_);
v___x_2000_ = lean_box(0);
v___x_2006_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_2007_ = lean_array_uget(v_as_1984_, v_i_1986_);
if (lean_obj_tag(v_a_2007_) == 0)
{
v_a_1994_ = v___x_2006_;
goto v___jp_1993_;
}
else
{
lean_object* v_val_2008_; lean_object* v___x_2010_; uint8_t v_isShared_2011_; uint8_t v_isSharedCheck_2095_; 
v_val_2008_ = lean_ctor_get(v_a_2007_, 0);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_a_2007_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2010_ = v_a_2007_;
v_isShared_2011_ = v_isSharedCheck_2095_;
goto v_resetjp_2009_;
}
else
{
lean_inc(v_val_2008_);
lean_dec(v_a_2007_);
v___x_2010_ = lean_box(0);
v_isShared_2011_ = v_isSharedCheck_2095_;
goto v_resetjp_2009_;
}
v_resetjp_2009_:
{
uint8_t v___x_2019_; 
v___x_2019_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2008_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l_Lean_LocalDecl_type(v_val_2008_);
v___x_2026_ = l_Lean_Meta_matchEq_x3f(v___x_2025_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v_a_2027_; 
v_a_2027_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2027_);
lean_dec_ref_known(v___x_2026_, 1);
if (lean_obj_tag(v_a_2027_) == 1)
{
lean_object* v_val_2028_; lean_object* v_snd_2029_; lean_object* v_fst_2030_; lean_object* v_snd_2031_; lean_object* v___x_2032_; 
v_val_2028_ = lean_ctor_get(v_a_2027_, 0);
lean_inc(v_val_2028_);
lean_dec_ref_known(v_a_2027_, 1);
v_snd_2029_ = lean_ctor_get(v_val_2028_, 1);
lean_inc(v_snd_2029_);
lean_dec(v_val_2028_);
v_fst_2030_ = lean_ctor_get(v_snd_2029_, 0);
lean_inc(v_fst_2030_);
v_snd_2031_ = lean_ctor_get(v_snd_2029_, 1);
lean_inc(v_snd_2031_);
lean_dec(v_snd_2029_);
v___x_2032_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_2030_, v___y_1989_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2034_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_2031_, v___y_1989_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v_a_2035_; lean_object* v___y_2037_; uint8_t v___y_2038_; lean_object* v___y_2051_; uint8_t v___y_2056_; uint8_t v___x_2068_; 
v_a_2035_ = lean_ctor_get(v___x_2034_, 0);
lean_inc(v_a_2035_);
lean_dec_ref_known(v___x_2034_, 1);
v___x_2068_ = l_Lean_Expr_isFVar(v_a_2035_);
if (v___x_2068_ == 0)
{
v___y_2056_ = v___x_2019_;
goto v___jp_2055_;
}
else
{
lean_object* v___x_2069_; uint8_t v___x_2070_; 
v___x_2069_ = l_Lean_Expr_fvarId_x21(v_a_2035_);
v___x_2070_ = l_Lean_instBEqFVarId_beq(v___x_2069_, v_x_1983_);
lean_dec(v___x_2069_);
v___y_2056_ = v___x_2070_;
goto v___jp_2055_;
}
v___jp_2036_:
{
if (v___y_2038_ == 0)
{
lean_dec(v_a_2035_);
lean_dec(v_val_2008_);
v_a_1994_ = v___x_2006_;
goto v___jp_1993_;
}
else
{
lean_object* v___x_2039_; 
lean_inc(v_x_1983_);
v___x_2039_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_2035_, v_x_1983_, v___y_2037_);
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
lean_dec(v_x_1983_);
goto v___jp_2020_;
}
else
{
if (v___x_2019_ == 0)
{
lean_dec(v_val_2008_);
v_a_1994_ = v___x_2006_;
goto v___jp_1993_;
}
else
{
lean_dec(v_x_1983_);
goto v___jp_2020_;
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec(v_val_2008_);
lean_dec(v_x_1983_);
v_a_2042_ = lean_ctor_get(v___x_2039_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2039_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2039_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2039_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
}
v___jp_2050_:
{
uint8_t v___x_2052_; 
v___x_2052_ = l_Lean_Expr_isFVar(v_a_2033_);
if (v___x_2052_ == 0)
{
lean_dec(v_a_2033_);
v___y_2037_ = v___y_2051_;
v___y_2038_ = v___x_2019_;
goto v___jp_2036_;
}
else
{
lean_object* v___x_2053_; uint8_t v___x_2054_; 
v___x_2053_ = l_Lean_Expr_fvarId_x21(v_a_2033_);
lean_dec(v_a_2033_);
v___x_2054_ = l_Lean_instBEqFVarId_beq(v___x_2053_, v_x_1983_);
lean_dec(v___x_2053_);
v___y_2037_ = v___y_2051_;
v___y_2038_ = v___x_2054_;
goto v___jp_2036_;
}
}
v___jp_2055_:
{
if (v___y_2056_ == 0)
{
lean_del_object(v___x_2010_);
v___y_2051_ = v___y_1989_;
goto v___jp_2050_;
}
else
{
lean_object* v___x_2057_; 
lean_inc(v_x_1983_);
lean_inc(v_a_2033_);
v___x_2057_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_2033_, v_x_1983_, v___y_1989_);
if (lean_obj_tag(v___x_2057_) == 0)
{
lean_object* v_a_2058_; uint8_t v___x_2059_; 
v_a_2058_ = lean_ctor_get(v___x_2057_, 0);
lean_inc(v_a_2058_);
lean_dec_ref_known(v___x_2057_, 1);
v___x_2059_ = lean_unbox(v_a_2058_);
lean_dec(v_a_2058_);
if (v___x_2059_ == 0)
{
lean_dec(v_a_2035_);
lean_dec(v_a_2033_);
lean_dec(v_x_1983_);
goto v___jp_2012_;
}
else
{
if (v___x_2019_ == 0)
{
lean_del_object(v___x_2010_);
v___y_2051_ = v___y_1989_;
goto v___jp_2050_;
}
else
{
lean_dec(v_a_2035_);
lean_dec(v_a_2033_);
lean_dec(v_x_1983_);
goto v___jp_2012_;
}
}
}
else
{
lean_object* v_a_2060_; lean_object* v___x_2062_; uint8_t v_isShared_2063_; uint8_t v_isSharedCheck_2067_; 
lean_dec(v_a_2035_);
lean_dec(v_a_2033_);
lean_del_object(v___x_2010_);
lean_dec(v_val_2008_);
lean_dec(v_x_1983_);
v_a_2060_ = lean_ctor_get(v___x_2057_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v___x_2057_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_2062_ = v___x_2057_;
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
else
{
lean_inc(v_a_2060_);
lean_dec(v___x_2057_);
v___x_2062_ = lean_box(0);
v_isShared_2063_ = v_isSharedCheck_2067_;
goto v_resetjp_2061_;
}
v_resetjp_2061_:
{
lean_object* v___x_2065_; 
if (v_isShared_2063_ == 0)
{
v___x_2065_ = v___x_2062_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v_a_2060_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
return v___x_2065_;
}
}
}
}
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec(v_a_2033_);
lean_del_object(v___x_2010_);
lean_dec(v_val_2008_);
lean_dec(v_x_1983_);
v_a_2071_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2034_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2034_);
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
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
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
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_snd_2031_);
lean_del_object(v___x_2010_);
lean_dec(v_val_2008_);
lean_dec(v_x_1983_);
v_a_2079_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2032_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2032_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v___x_2084_; 
if (v_isShared_2082_ == 0)
{
v___x_2084_ = v___x_2081_;
goto v_reusejp_2083_;
}
else
{
lean_object* v_reuseFailAlloc_2085_; 
v_reuseFailAlloc_2085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2085_, 0, v_a_2079_);
v___x_2084_ = v_reuseFailAlloc_2085_;
goto v_reusejp_2083_;
}
v_reusejp_2083_:
{
return v___x_2084_;
}
}
}
}
else
{
lean_dec(v_a_2027_);
lean_del_object(v___x_2010_);
lean_dec(v_val_2008_);
v_a_1994_ = v___x_2006_;
goto v___jp_1993_;
}
}
else
{
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_del_object(v___x_2010_);
lean_dec(v_val_2008_);
lean_dec(v_x_1983_);
v_a_2087_ = lean_ctor_get(v___x_2026_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2026_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2026_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2092_; 
if (v_isShared_2090_ == 0)
{
v___x_2092_ = v___x_2089_;
goto v_reusejp_2091_;
}
else
{
lean_object* v_reuseFailAlloc_2093_; 
v_reuseFailAlloc_2093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2093_, 0, v_a_2087_);
v___x_2092_ = v_reuseFailAlloc_2093_;
goto v_reusejp_2091_;
}
v_reusejp_2091_:
{
return v___x_2092_;
}
}
}
}
else
{
lean_del_object(v___x_2010_);
lean_dec(v_val_2008_);
v_a_1994_ = v___x_2006_;
goto v___jp_1993_;
}
v___jp_2012_:
{
lean_object* v___x_2013_; lean_object* v___x_2014_; lean_object* v___x_2015_; lean_object* v___x_2017_; 
v___x_2013_ = l_Lean_LocalDecl_fvarId(v_val_2008_);
lean_dec(v_val_2008_);
v___x_2014_ = lean_box(v___x_1998_);
v___x_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2015_, 0, v___x_2013_);
lean_ctor_set(v___x_2015_, 1, v___x_2014_);
if (v_isShared_2011_ == 0)
{
lean_ctor_set(v___x_2010_, 0, v___x_2015_);
v___x_2017_ = v___x_2010_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v___x_2015_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
v_a_2002_ = v___x_2017_;
goto v___jp_2001_;
}
}
v___jp_2020_:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2021_ = l_Lean_LocalDecl_fvarId(v_val_2008_);
lean_dec(v_val_2008_);
v___x_2022_ = lean_box(v___x_2019_);
v___x_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2023_, 0, v___x_2021_);
lean_ctor_set(v___x_2023_, 1, v___x_2022_);
v___x_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2024_, 0, v___x_2023_);
v_a_2002_ = v___x_2024_;
goto v___jp_2001_;
}
}
}
v___jp_2001_:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2003_, 0, v_a_2002_);
v___x_2004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v___x_2000_);
v___x_2005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
return v___x_2005_;
}
}
v___jp_1993_:
{
size_t v___x_1995_; size_t v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((size_t)1ULL);
v___x_1996_ = lean_usize_add(v_i_1986_, v___x_1995_);
lean_inc_ref(v_a_1994_);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1983_, v_as_1984_, v_sz_1985_, v___x_1996_, v_a_1994_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
return v___x_1997_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1983_ = stack[0].m_obj;
lean_object* v_as_1984_ = stack[1].m_obj;
size_t v_sz_1985_ = stack[2].m_num;
size_t v_i_1986_ = stack[3].m_num;
lean_object* v_b_1987_ = stack[4].m_obj;
lean_object* v___y_1988_ = stack[5].m_obj;
lean_object* v___y_1989_ = stack[6].m_obj;
lean_object* v___y_1990_ = stack[7].m_obj;
lean_object* v___y_1991_ = stack[8].m_obj;
lean_object* v_res_2096_;
v_res_2096_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_1983_, v_as_1984_, v_sz_1985_, v_i_1986_, v_b_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
stack->m_obj
 = v_res_2096_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2097_, lean_object* v_as_2098_, lean_object* v_sz_2099_, lean_object* v_i_2100_, lean_object* v_b_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_){
_start:
{
size_t v_sz_boxed_2107_; size_t v_i_boxed_2108_; lean_object* v_res_2109_; 
v_sz_boxed_2107_ = lean_unbox_usize(v_sz_2099_);
lean_dec(v_sz_2099_);
v_i_boxed_2108_ = lean_unbox_usize(v_i_2100_);
lean_dec(v_i_2100_);
v_res_2109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2097_, v_as_2098_, v_sz_boxed_2107_, v_i_boxed_2108_, v_b_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_);
lean_dec(v___y_2105_);
lean_dec_ref(v___y_2104_);
lean_dec(v___y_2103_);
lean_dec_ref(v___y_2102_);
lean_dec_ref(v_as_2098_);
return v_res_2109_;
}
}
lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object* v_x_2110_, lean_object* v_x_2111_, lean_object* v___y_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_){
_start:
{
if (lean_obj_tag(v_x_2111_) == 0)
{
lean_object* v_cs_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; size_t v_sz_2120_; size_t v___x_2121_; lean_object* v___x_2122_; 
v_cs_2117_ = lean_ctor_get(v_x_2111_, 0);
v___x_2118_ = lean_box(0);
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2120_ = lean_array_size(v_cs_2117_);
v___x_2121_ = ((size_t)0ULL);
v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2110_, v_cs_2117_, v_sz_2120_, v___x_2121_, v___x_2119_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2135_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2125_ = v___x_2122_;
v_isShared_2126_ = v_isSharedCheck_2135_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2122_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2135_;
goto v_resetjp_2124_;
}
v_resetjp_2124_:
{
lean_object* v_fst_2127_; 
v_fst_2127_ = lean_ctor_get(v_a_2123_, 0);
lean_inc(v_fst_2127_);
lean_dec(v_a_2123_);
if (lean_obj_tag(v_fst_2127_) == 0)
{
lean_object* v___x_2129_; 
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v___x_2118_);
v___x_2129_ = v___x_2125_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2118_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
else
{
lean_object* v_val_2131_; lean_object* v___x_2133_; 
v_val_2131_ = lean_ctor_get(v_fst_2127_, 0);
lean_inc(v_val_2131_);
lean_dec_ref_known(v_fst_2127_, 1);
if (v_isShared_2126_ == 0)
{
lean_ctor_set(v___x_2125_, 0, v_val_2131_);
v___x_2133_ = v___x_2125_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_val_2131_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
v_a_2136_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2122_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2122_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_vs_2144_; lean_object* v___x_2145_; lean_object* v___x_2146_; size_t v_sz_2147_; size_t v___x_2148_; lean_object* v___x_2149_; 
v_vs_2144_ = lean_ctor_get(v_x_2111_, 0);
v___x_2145_ = lean_box(0);
v___x_2146_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2147_ = lean_array_size(v_vs_2144_);
v___x_2148_ = ((size_t)0ULL);
v___x_2149_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2110_, v_vs_2144_, v_sz_2147_, v___x_2148_, v___x_2146_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
if (lean_obj_tag(v___x_2149_) == 0)
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2162_; 
v_a_2150_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2152_ = v___x_2149_;
v_isShared_2153_ = v_isSharedCheck_2162_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2149_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2162_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v_fst_2154_; 
v_fst_2154_ = lean_ctor_get(v_a_2150_, 0);
lean_inc(v_fst_2154_);
lean_dec(v_a_2150_);
if (lean_obj_tag(v_fst_2154_) == 0)
{
lean_object* v___x_2156_; 
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2145_);
v___x_2156_ = v___x_2152_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v___x_2145_);
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
lean_object* v_val_2158_; lean_object* v___x_2160_; 
v_val_2158_ = lean_ctor_get(v_fst_2154_, 0);
lean_inc(v_val_2158_);
lean_dec_ref_known(v_fst_2154_, 1);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v_val_2158_);
v___x_2160_ = v___x_2152_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_val_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
v_a_2163_ = lean_ctor_get(v___x_2149_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2149_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2149_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2149_);
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
LEAN_EXPORT void l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2110_ = stack[0].m_obj;
lean_object* v_x_2111_ = stack[1].m_obj;
lean_object* v___y_2112_ = stack[2].m_obj;
lean_object* v___y_2113_ = stack[3].m_obj;
lean_object* v___y_2114_ = stack[4].m_obj;
lean_object* v___y_2115_ = stack[5].m_obj;
lean_object* v_res_2171_;
v_res_2171_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2110_, v_x_2111_, v___y_2112_, v___y_2113_, v___y_2114_, v___y_2115_);
stack->m_obj
 = v_res_2171_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2172_, lean_object* v_as_2173_, size_t v_sz_2174_, size_t v_i_2175_, lean_object* v_b_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_usize_dec_lt(v_i_2175_, v_sz_2174_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
lean_dec(v_x_2172_);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v_b_2176_);
return v___x_2183_;
}
else
{
lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v_a_2186_; lean_object* v___x_2187_; 
lean_dec_ref(v_b_2176_);
v___x_2184_ = lean_box(0);
v___x_2185_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_2186_ = lean_array_uget_borrowed(v_as_2173_, v_i_2175_);
lean_inc(v_x_2172_);
v___x_2187_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2172_, v_a_2186_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
if (lean_obj_tag(v___x_2187_) == 0)
{
lean_object* v_a_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2200_; 
v_a_2188_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2190_ = v___x_2187_;
v_isShared_2191_ = v_isSharedCheck_2200_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_a_2188_);
lean_dec(v___x_2187_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2200_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
if (lean_obj_tag(v_a_2188_) == 1)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2195_; 
lean_dec(v_x_2172_);
v___x_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2192_, 0, v_a_2188_);
v___x_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v___x_2184_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2193_);
v___x_2195_ = v___x_2190_;
goto v_reusejp_2194_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2193_);
v___x_2195_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2194_;
}
v_reusejp_2194_:
{
return v___x_2195_;
}
}
else
{
size_t v___x_2197_; size_t v___x_2198_; 
lean_del_object(v___x_2190_);
lean_dec(v_a_2188_);
v___x_2197_ = ((size_t)1ULL);
v___x_2198_ = lean_usize_add(v_i_2175_, v___x_2197_);
v_i_2175_ = v___x_2198_;
v_b_2176_ = v___x_2185_;
goto _start;
}
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec(v_x_2172_);
v_a_2201_ = lean_ctor_get(v___x_2187_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2187_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2187_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2187_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2172_ = stack[0].m_obj;
lean_object* v_as_2173_ = stack[1].m_obj;
size_t v_sz_2174_ = stack[2].m_num;
size_t v_i_2175_ = stack[3].m_num;
lean_object* v_b_2176_ = stack[4].m_obj;
lean_object* v___y_2177_ = stack[5].m_obj;
lean_object* v___y_2178_ = stack[6].m_obj;
lean_object* v___y_2179_ = stack[7].m_obj;
lean_object* v___y_2180_ = stack[8].m_obj;
lean_object* v_res_2209_;
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2172_, v_as_2173_, v_sz_2174_, v_i_2175_, v_b_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
stack->m_obj
 = v_res_2209_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2210_, lean_object* v_as_2211_, lean_object* v_sz_2212_, lean_object* v_i_2213_, lean_object* v_b_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_){
_start:
{
size_t v_sz_boxed_2220_; size_t v_i_boxed_2221_; lean_object* v_res_2222_; 
v_sz_boxed_2220_ = lean_unbox_usize(v_sz_2212_);
lean_dec(v_sz_2212_);
v_i_boxed_2221_ = lean_unbox_usize(v_i_2213_);
lean_dec(v_i_2213_);
v_res_2222_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2210_, v_as_2211_, v_sz_boxed_2220_, v_i_boxed_2221_, v_b_2214_, v___y_2215_, v___y_2216_, v___y_2217_, v___y_2218_);
lean_dec(v___y_2218_);
lean_dec_ref(v___y_2217_);
lean_dec(v___y_2216_);
lean_dec_ref(v___y_2215_);
lean_dec_ref(v_as_2211_);
return v_res_2222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2223_, lean_object* v_x_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2223_, v_x_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_);
lean_dec(v___y_2228_);
lean_dec_ref(v___y_2227_);
lean_dec(v___y_2226_);
lean_dec_ref(v___y_2225_);
lean_dec_ref(v_x_2224_);
return v_res_2230_;
}
}
lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object* v_x_2231_, lean_object* v_t_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v_root_2238_; lean_object* v_tail_2239_; lean_object* v___x_2240_; 
v_root_2238_ = lean_ctor_get(v_t_2232_, 0);
v_tail_2239_ = lean_ctor_get(v_t_2232_, 1);
lean_inc(v_x_2231_);
v___x_2240_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2231_, v_root_2238_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
if (lean_obj_tag(v_a_2241_) == 0)
{
lean_object* v___x_2242_; size_t v_sz_2243_; size_t v___x_2244_; lean_object* v___x_2245_; 
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v___x_2242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2243_ = lean_array_size(v_tail_2239_);
v___x_2244_ = ((size_t)0ULL);
v___x_2245_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2231_, v_tail_2239_, v_sz_2243_, v___x_2244_, v___x_2242_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
if (lean_obj_tag(v___x_2245_) == 0)
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2258_; 
v_a_2246_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2248_ = v___x_2245_;
v_isShared_2249_ = v_isSharedCheck_2258_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2245_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2258_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v_fst_2250_; 
v_fst_2250_ = lean_ctor_get(v_a_2246_, 0);
lean_inc(v_fst_2250_);
lean_dec(v_a_2246_);
if (lean_obj_tag(v_fst_2250_) == 0)
{
lean_object* v___x_2252_; 
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v_a_2241_);
v___x_2252_ = v___x_2248_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2241_);
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
lean_object* v_val_2254_; lean_object* v___x_2256_; 
v_val_2254_ = lean_ctor_get(v_fst_2250_, 0);
lean_inc(v_val_2254_);
lean_dec_ref_known(v_fst_2250_, 1);
if (v_isShared_2249_ == 0)
{
lean_ctor_set(v___x_2248_, 0, v_val_2254_);
v___x_2256_ = v___x_2248_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_val_2254_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
v_a_2259_ = lean_ctor_get(v___x_2245_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2245_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2245_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2245_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_dec(v_x_2231_);
return v___x_2240_;
}
}
else
{
lean_dec(v_x_2231_);
return v___x_2240_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2231_ = stack[0].m_obj;
lean_object* v_t_2232_ = stack[1].m_obj;
lean_object* v___y_2233_ = stack[2].m_obj;
lean_object* v___y_2234_ = stack[3].m_obj;
lean_object* v___y_2235_ = stack[4].m_obj;
lean_object* v___y_2236_ = stack[5].m_obj;
lean_object* v_res_2267_;
v_res_2267_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2231_, v_t_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
stack->m_obj
 = v_res_2267_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* v_x_2268_, lean_object* v_t_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_){
_start:
{
lean_object* v_res_2275_; 
v_res_2275_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2268_, v_t_2269_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
lean_dec(v___y_2273_);
lean_dec_ref(v___y_2272_);
lean_dec(v___y_2271_);
lean_dec_ref(v___y_2270_);
lean_dec_ref(v_t_2269_);
return v_res_2275_;
}
}
lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object* v_x_2276_, lean_object* v_lctx_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_){
_start:
{
lean_object* v_decls_2283_; lean_object* v___x_2284_; 
v_decls_2283_ = lean_ctor_get(v_lctx_2277_, 1);
v___x_2284_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2276_, v_decls_2283_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2284_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2276_ = stack[0].m_obj;
lean_object* v_lctx_2277_ = stack[1].m_obj;
lean_object* v___y_2278_ = stack[2].m_obj;
lean_object* v___y_2279_ = stack[3].m_obj;
lean_object* v___y_2280_ = stack[4].m_obj;
lean_object* v___y_2281_ = stack[5].m_obj;
lean_object* v_res_2285_;
v_res_2285_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2276_, v_lctx_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
stack->m_obj
 = v_res_2285_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object* v_x_2286_, lean_object* v_lctx_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_){
_start:
{
lean_object* v_res_2293_; 
v_res_2293_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2286_, v_lctx_2287_, v___y_2288_, v___y_2289_, v___y_2290_, v___y_2291_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec(v___y_2289_);
lean_dec_ref(v___y_2288_);
lean_dec_ref(v_lctx_2287_);
return v_res_2293_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2295_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__0));
v___x_2296_ = l_Lean_stringToMessageData(v___x_2295_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2298_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__2));
v___x_2299_ = l_Lean_stringToMessageData(v___x_2298_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2301_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__4));
v___x_2302_ = l_Lean_stringToMessageData(v___x_2301_);
return v___x_2302_;
}
}
lean_object* l_Lean_Meta_substVar___lam__0(lean_object* v_x_2303_, lean_object* v_mvarId_2304_, lean_object* v___y_2305_, lean_object* v___y_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_){
_start:
{
lean_object* v___x_2355_; 
lean_inc(v_x_2303_);
v___x_2355_ = l_Lean_FVarId_getDecl___redArg(v_x_2303_, v___y_2305_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2355_) == 0)
{
lean_object* v_a_2356_; uint8_t v___x_2357_; uint8_t v___x_2358_; 
v_a_2356_ = lean_ctor_get(v___x_2355_, 0);
lean_inc(v_a_2356_);
lean_dec_ref_known(v___x_2355_, 1);
v___x_2357_ = 0;
v___x_2358_ = l_Lean_LocalDecl_isLet(v_a_2356_, v___x_2357_);
lean_dec(v_a_2356_);
if (v___x_2358_ == 0)
{
goto v___jp_2310_;
}
else
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; 
v___x_2359_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2360_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2303_);
v___x_2361_ = l_Lean_mkFVar(v_x_2303_);
v___x_2362_ = l_Lean_MessageData_ofExpr(v___x_2361_);
v___x_2363_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2360_);
lean_ctor_set(v___x_2363_, 1, v___x_2362_);
v___x_2364_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2365_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2365_);
lean_inc(v_mvarId_2304_);
v___x_2367_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2359_, v_mvarId_2304_, v___x_2366_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2367_) == 0)
{
lean_dec_ref_known(v___x_2367_, 1);
goto v___jp_2310_;
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_mvarId_2304_);
lean_dec(v_x_2303_);
v_a_2368_ = lean_ctor_get(v___x_2367_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2367_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2367_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2367_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec(v_mvarId_2304_);
lean_dec(v_x_2303_);
v_a_2376_ = lean_ctor_get(v___x_2355_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2355_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2355_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2355_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
v___jp_2310_:
{
lean_object* v_lctx_2311_; lean_object* v___x_2312_; 
v_lctx_2311_ = lean_ctor_get(v___y_2305_, 2);
lean_inc(v_x_2303_);
v___x_2312_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2303_, v_lctx_2311_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2312_) == 0)
{
lean_object* v_a_2313_; 
v_a_2313_ = lean_ctor_get(v___x_2312_, 0);
lean_inc(v_a_2313_);
lean_dec_ref_known(v___x_2312_, 1);
if (lean_obj_tag(v_a_2313_) == 1)
{
lean_object* v_val_2314_; lean_object* v_fst_2315_; lean_object* v_snd_2316_; lean_object* v___x_2317_; uint8_t v___x_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; 
lean_dec(v_x_2303_);
v_val_2314_ = lean_ctor_get(v_a_2313_, 0);
lean_inc(v_val_2314_);
lean_dec_ref_known(v_a_2313_, 1);
v_fst_2315_ = lean_ctor_get(v_val_2314_, 0);
lean_inc(v_fst_2315_);
v_snd_2316_ = lean_ctor_get(v_val_2314_, 1);
lean_inc(v_snd_2316_);
lean_dec(v_val_2314_);
v___x_2317_ = lean_box(0);
v___x_2318_ = 1;
v___x_2319_ = lean_unbox(v_snd_2316_);
lean_dec(v_snd_2316_);
v___x_2320_ = l_Lean_Meta_substCore(v_mvarId_2304_, v_fst_2315_, v___x_2319_, v___x_2317_, v___x_2318_, v___x_2318_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2329_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2329_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2329_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v_snd_2325_; lean_object* v___x_2327_; 
v_snd_2325_ = lean_ctor_get(v_a_2321_, 1);
lean_inc(v_snd_2325_);
lean_dec(v_a_2321_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v_snd_2325_);
v___x_2327_ = v___x_2323_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_snd_2325_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
else
{
lean_object* v_a_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2337_; 
v_a_2330_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2337_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2337_ == 0)
{
v___x_2332_ = v___x_2320_;
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_a_2330_);
lean_dec(v___x_2320_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2337_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2335_; 
if (v_isShared_2333_ == 0)
{
v___x_2335_ = v___x_2332_;
goto v_reusejp_2334_;
}
else
{
lean_object* v_reuseFailAlloc_2336_; 
v_reuseFailAlloc_2336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2336_, 0, v_a_2330_);
v___x_2335_ = v_reuseFailAlloc_2336_;
goto v_reusejp_2334_;
}
v_reusejp_2334_:
{
return v___x_2335_;
}
}
}
}
else
{
lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_dec(v_a_2313_);
v___x_2338_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2339_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2340_ = l_Lean_mkFVar(v_x_2303_);
v___x_2341_ = l_Lean_MessageData_ofExpr(v___x_2340_);
v___x_2342_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2339_);
lean_ctor_set(v___x_2342_, 1, v___x_2341_);
v___x_2343_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_2344_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2342_);
lean_ctor_set(v___x_2344_, 1, v___x_2343_);
v___x_2345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
v___x_2346_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2338_, v_mvarId_2304_, v___x_2345_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
return v___x_2346_;
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec(v_mvarId_2304_);
lean_dec(v_x_2303_);
v_a_2347_ = lean_ctor_get(v___x_2312_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2312_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2312_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2312_);
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
LEAN_EXPORT void l_Lean_Meta_substVar___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2303_ = stack[0].m_obj;
lean_object* v_mvarId_2304_ = stack[1].m_obj;
lean_object* v___y_2305_ = stack[2].m_obj;
lean_object* v___y_2306_ = stack[3].m_obj;
lean_object* v___y_2307_ = stack[4].m_obj;
lean_object* v___y_2308_ = stack[5].m_obj;
lean_object* v_res_2384_;
v_res_2384_ = l_Lean_Meta_substVar___lam__0(v_x_2303_, v_mvarId_2304_, v___y_2305_, v___y_2306_, v___y_2307_, v___y_2308_);
stack->m_obj
 = v_res_2384_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2385_, lean_object* v_mvarId_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lean_Meta_substVar___lam__0(v_x_2385_, v_mvarId_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v_res_2392_;
}
}
lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2393_, lean_object* v_x_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v___f_2400_; lean_object* v___x_2401_; 
lean_inc(v_mvarId_2393_);
v___f_2400_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2400_, 0, v_x_2394_);
lean_closure_set(v___f_2400_, 1, v_mvarId_2393_);
v___x_2401_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2393_, v___f_2400_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
return v___x_2401_;
}
}
LEAN_EXPORT void l_Lean_Meta_substVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2393_ = stack[0].m_obj;
lean_object* v_x_2394_ = stack[1].m_obj;
lean_object* v_a_2395_ = stack[2].m_obj;
lean_object* v_a_2396_ = stack[3].m_obj;
lean_object* v_a_2397_ = stack[4].m_obj;
lean_object* v_a_2398_ = stack[5].m_obj;
lean_object* v_res_2402_;
v_res_2402_ = l_Lean_Meta_substVar(v_mvarId_2393_, v_x_2394_, v_a_2395_, v_a_2396_, v_a_2397_, v_a_2398_);
stack->m_obj
 = v_res_2402_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2403_, lean_object* v_x_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v_res_2410_; 
v_res_2410_ = l_Lean_Meta_substVar(v_mvarId_2403_, v_x_2404_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
lean_dec(v_a_2408_);
lean_dec_ref(v_a_2407_);
lean_dec(v_a_2406_);
lean_dec_ref(v_a_2405_);
return v_res_2410_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2412_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2413_ = l_Lean_stringToMessageData(v___x_2412_);
return v___x_2413_;
}
}
lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2414_, lean_object* v_snd_2415_, uint8_t v___x_2416_, lean_object* v_fvarSubst_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_){
_start:
{
lean_object* v___x_2423_; 
lean_inc(v_fst_2414_);
v___x_2423_ = l_Lean_FVarId_getDecl___redArg(v_fst_2414_, v___y_2418_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___y_2426_; lean_object* v___y_2427_; lean_object* v___y_2428_; lean_object* v___y_2429_; lean_object* v_newType_2438_; uint8_t v_symm_2439_; lean_object* v___y_2440_; lean_object* v___y_2441_; lean_object* v___y_2442_; lean_object* v___y_2443_; lean_object* v___x_2479_; lean_object* v___x_2480_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v___x_2479_ = l_Lean_LocalDecl_type(v_a_2424_);
v___x_2480_ = l_Lean_Meta_matchEq_x3f(v___x_2479_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2480_) == 0)
{
lean_object* v_a_2481_; 
v_a_2481_ = lean_ctor_get(v___x_2480_, 0);
lean_inc(v_a_2481_);
lean_dec_ref_known(v___x_2480_, 1);
if (lean_obj_tag(v_a_2481_) == 1)
{
lean_object* v_val_2482_; lean_object* v_snd_2483_; lean_object* v_fst_2484_; lean_object* v_snd_2485_; lean_object* v___x_2486_; 
v_val_2482_ = lean_ctor_get(v_a_2481_, 0);
lean_inc(v_val_2482_);
lean_dec_ref_known(v_a_2481_, 1);
v_snd_2483_ = lean_ctor_get(v_val_2482_, 1);
lean_inc(v_snd_2483_);
lean_dec(v_val_2482_);
v_fst_2484_ = lean_ctor_get(v_snd_2483_, 0);
lean_inc(v_fst_2484_);
v_snd_2485_ = lean_ctor_get(v_snd_2483_, 1);
lean_inc_n(v_snd_2485_, 2);
lean_dec(v_snd_2483_);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
v___x_2486_ = lean_whnf(v_snd_2485_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2486_) == 0)
{
lean_object* v_a_2487_; uint8_t v___x_2488_; 
v_a_2487_ = lean_ctor_get(v___x_2486_, 0);
lean_inc(v_a_2487_);
lean_dec_ref_known(v___x_2486_, 1);
v___x_2488_ = l_Lean_Expr_isFVar(v_a_2487_);
if (v___x_2488_ == 0)
{
lean_object* v___x_2489_; 
lean_dec(v_a_2487_);
lean_inc(v___y_2421_);
lean_inc_ref(v___y_2420_);
lean_inc(v___y_2419_);
lean_inc_ref(v___y_2418_);
lean_inc(v_fst_2484_);
v___x_2489_ = lean_whnf(v_fst_2484_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; uint8_t v___y_2492_; uint8_t v___x_2504_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2504_ = l_Lean_Expr_isFVar(v_a_2490_);
if (v___x_2504_ == 0)
{
lean_dec(v_a_2490_);
lean_dec(v_snd_2485_);
lean_dec(v_fst_2484_);
lean_dec(v_fvarSubst_2417_);
lean_dec(v_fst_2414_);
v___y_2426_ = v___y_2418_;
v___y_2427_ = v___y_2419_;
v___y_2428_ = v___y_2420_;
v___y_2429_ = v___y_2421_;
goto v___jp_2425_;
}
else
{
uint8_t v___x_2505_; 
v___x_2505_ = lean_expr_eqv(v_fst_2484_, v_a_2490_);
lean_dec(v_fst_2484_);
if (v___x_2505_ == 0)
{
v___y_2492_ = v___x_2504_;
goto v___jp_2491_;
}
else
{
v___y_2492_ = v___x_2488_;
goto v___jp_2491_;
}
}
v___jp_2491_:
{
if (v___y_2492_ == 0)
{
lean_object* v___x_2493_; 
lean_dec(v_a_2490_);
lean_dec(v_snd_2485_);
lean_dec(v_a_2424_);
v___x_2493_ = l_Lean_Meta_substCore(v_snd_2415_, v_fst_2414_, v___y_2492_, v_fvarSubst_2417_, v___x_2416_, v___x_2416_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
return v___x_2493_;
}
else
{
lean_object* v___x_2494_; 
v___x_2494_ = l_Lean_Meta_mkEq(v_a_2490_, v_snd_2485_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v_newType_2438_ = v_a_2495_;
v_symm_2439_ = v___x_2488_;
v___y_2440_ = v___y_2418_;
v___y_2441_ = v___y_2419_;
v___y_2442_ = v___y_2420_;
v___y_2443_ = v___y_2421_;
goto v___jp_2437_;
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_a_2424_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_fvarSubst_2417_);
lean_dec(v_snd_2415_);
lean_dec(v_fst_2414_);
v_a_2496_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2494_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2494_);
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
}
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_snd_2485_);
lean_dec(v_fst_2484_);
lean_dec(v_a_2424_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_fvarSubst_2417_);
lean_dec(v_snd_2415_);
lean_dec(v_fst_2414_);
v_a_2506_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2489_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2489_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
uint8_t v___x_2514_; 
v___x_2514_ = lean_expr_eqv(v_snd_2485_, v_a_2487_);
lean_dec(v_snd_2485_);
if (v___x_2514_ == 0)
{
if (v___x_2488_ == 0)
{
lean_object* v___x_2515_; 
lean_dec(v_a_2487_);
lean_dec(v_fst_2484_);
lean_dec(v_a_2424_);
v___x_2515_ = l_Lean_Meta_substCore(v_snd_2415_, v_fst_2414_, v___x_2416_, v_fvarSubst_2417_, v___x_2416_, v___x_2416_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
return v___x_2515_;
}
else
{
lean_object* v___x_2516_; 
v___x_2516_ = l_Lean_Meta_mkEq(v_fst_2484_, v_a_2487_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v_newType_2438_ = v_a_2517_;
v_symm_2439_ = v___x_2416_;
v___y_2440_ = v___y_2418_;
v___y_2441_ = v___y_2419_;
v___y_2442_ = v___y_2420_;
v___y_2443_ = v___y_2421_;
goto v___jp_2437_;
}
else
{
lean_object* v_a_2518_; lean_object* v___x_2520_; uint8_t v_isShared_2521_; uint8_t v_isSharedCheck_2525_; 
lean_dec(v_a_2424_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_fvarSubst_2417_);
lean_dec(v_snd_2415_);
lean_dec(v_fst_2414_);
v_a_2518_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2525_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2525_ == 0)
{
v___x_2520_ = v___x_2516_;
v_isShared_2521_ = v_isSharedCheck_2525_;
goto v_resetjp_2519_;
}
else
{
lean_inc(v_a_2518_);
lean_dec(v___x_2516_);
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
}
else
{
lean_object* v___x_2526_; 
lean_dec(v_a_2487_);
lean_dec(v_fst_2484_);
lean_dec(v_a_2424_);
v___x_2526_ = l_Lean_Meta_substCore(v_snd_2415_, v_fst_2414_, v___x_2416_, v_fvarSubst_2417_, v___x_2416_, v___x_2416_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
return v___x_2526_;
}
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v_snd_2485_);
lean_dec(v_fst_2484_);
lean_dec(v_a_2424_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_fvarSubst_2417_);
lean_dec(v_snd_2415_);
lean_dec(v_fst_2414_);
v_a_2527_ = lean_ctor_get(v___x_2486_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2486_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2486_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2486_);
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
}
else
{
lean_dec(v_a_2481_);
lean_dec(v_fvarSubst_2417_);
lean_dec(v_fst_2414_);
v___y_2426_ = v___y_2418_;
v___y_2427_ = v___y_2419_;
v___y_2428_ = v___y_2420_;
v___y_2429_ = v___y_2421_;
goto v___jp_2425_;
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_a_2424_);
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_fvarSubst_2417_);
lean_dec(v_snd_2415_);
lean_dec(v_fst_2414_);
v_a_2535_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2480_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2480_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v___x_2540_; 
if (v_isShared_2538_ == 0)
{
v___x_2540_ = v___x_2537_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2541_; 
v_reuseFailAlloc_2541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2541_, 0, v_a_2535_);
v___x_2540_ = v_reuseFailAlloc_2541_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
return v___x_2540_;
}
}
}
v___jp_2425_:
{
lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2430_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2431_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2432_ = l_Lean_LocalDecl_type(v_a_2424_);
lean_dec(v_a_2424_);
v___x_2433_ = l_Lean_indentExpr(v___x_2432_);
v___x_2434_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2434_, 0, v___x_2431_);
lean_ctor_set(v___x_2434_, 1, v___x_2433_);
v___x_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2434_);
v___x_2436_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2430_, v_snd_2415_, v___x_2435_, v___y_2426_, v___y_2427_, v___y_2428_, v___y_2429_);
lean_dec(v___y_2429_);
lean_dec_ref(v___y_2428_);
lean_dec(v___y_2427_);
lean_dec_ref(v___y_2426_);
return v___x_2436_;
}
v___jp_2437_:
{
lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v___x_2444_ = l_Lean_LocalDecl_userName(v_a_2424_);
lean_dec(v_a_2424_);
lean_inc(v_fst_2414_);
v___x_2445_ = l_Lean_mkFVar(v_fst_2414_);
v___x_2446_ = l_Lean_MVarId_assert(v_snd_2415_, v___x_2444_, v_newType_2438_, v___x_2445_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; lean_object* v___x_2448_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = l_Lean_Meta_intro1Core(v_a_2447_, v___x_2416_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2448_) == 0)
{
lean_object* v_a_2449_; lean_object* v_fst_2450_; lean_object* v_snd_2451_; lean_object* v___x_2452_; 
v_a_2449_ = lean_ctor_get(v___x_2448_, 0);
lean_inc(v_a_2449_);
lean_dec_ref_known(v___x_2448_, 1);
v_fst_2450_ = lean_ctor_get(v_a_2449_, 0);
lean_inc(v_fst_2450_);
v_snd_2451_ = lean_ctor_get(v_a_2449_, 1);
lean_inc(v_snd_2451_);
lean_dec(v_a_2449_);
v___x_2452_ = l_Lean_MVarId_clear(v_snd_2451_, v_fst_2414_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v_a_2453_; lean_object* v___x_2454_; 
v_a_2453_ = lean_ctor_get(v___x_2452_, 0);
lean_inc(v_a_2453_);
lean_dec_ref_known(v___x_2452_, 1);
v___x_2454_ = l_Lean_Meta_substCore(v_a_2453_, v_fst_2450_, v_symm_2439_, v_fvarSubst_2417_, v___x_2416_, v___x_2416_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v___x_2454_;
}
else
{
lean_object* v_a_2455_; lean_object* v___x_2457_; uint8_t v_isShared_2458_; uint8_t v_isSharedCheck_2462_; 
lean_dec(v_fst_2450_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v_fvarSubst_2417_);
v_a_2455_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2462_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2462_ == 0)
{
v___x_2457_ = v___x_2452_;
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
else
{
lean_inc(v_a_2455_);
lean_dec(v___x_2452_);
v___x_2457_ = lean_box(0);
v_isShared_2458_ = v_isSharedCheck_2462_;
goto v_resetjp_2456_;
}
v_resetjp_2456_:
{
lean_object* v___x_2460_; 
if (v_isShared_2458_ == 0)
{
v___x_2460_ = v___x_2457_;
goto v_reusejp_2459_;
}
else
{
lean_object* v_reuseFailAlloc_2461_; 
v_reuseFailAlloc_2461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2461_, 0, v_a_2455_);
v___x_2460_ = v_reuseFailAlloc_2461_;
goto v_reusejp_2459_;
}
v_reusejp_2459_:
{
return v___x_2460_;
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v_fvarSubst_2417_);
lean_dec(v_fst_2414_);
v_a_2463_ = lean_ctor_get(v___x_2448_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2448_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2448_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2448_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
lean_dec(v_fvarSubst_2417_);
lean_dec(v_fst_2414_);
v_a_2471_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2446_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2446_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec(v___y_2421_);
lean_dec_ref(v___y_2420_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v_fvarSubst_2417_);
lean_dec(v_snd_2415_);
lean_dec(v_fst_2414_);
v_a_2543_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2423_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2423_);
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
}
LEAN_EXPORT void l_Lean_Meta_substEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_2414_ = stack[0].m_obj;
lean_object* v_snd_2415_ = stack[1].m_obj;
uint8_t v___x_2416_ = stack[2].m_num;
lean_object* v_fvarSubst_2417_ = stack[3].m_obj;
lean_object* v___y_2418_ = stack[4].m_obj;
lean_object* v___y_2419_ = stack[5].m_obj;
lean_object* v___y_2420_ = stack[6].m_obj;
lean_object* v___y_2421_ = stack[7].m_obj;
lean_object* v_res_2551_;
v_res_2551_ = l_Lean_Meta_substEq___lam__0(v_fst_2414_, v_snd_2415_, v___x_2416_, v_fvarSubst_2417_, v___y_2418_, v___y_2419_, v___y_2420_, v___y_2421_);
stack->m_obj
 = v_res_2551_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2552_, lean_object* v_snd_2553_, lean_object* v___x_2554_, lean_object* v_fvarSubst_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
uint8_t v___x_1437__boxed_2561_; lean_object* v_res_2562_; 
v___x_1437__boxed_2561_ = lean_unbox(v___x_2554_);
v_res_2562_ = l_Lean_Meta_substEq___lam__0(v_fst_2552_, v_snd_2553_, v___x_1437__boxed_2561_, v_fvarSubst_2555_, v___y_2556_, v___y_2557_, v___y_2558_, v___y_2559_);
return v_res_2562_;
}
}
lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2563_, lean_object* v_hFVarId_2564_, lean_object* v_fvarSubst_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_){
_start:
{
uint8_t v___x_2571_; lean_object* v___x_2572_; 
v___x_2571_ = 1;
v___x_2572_ = l_Lean_Meta_heqToEq(v_mvarId_2563_, v_hFVarId_2564_, v___x_2571_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v_fst_2574_; lean_object* v_snd_2575_; lean_object* v___x_2576_; lean_object* v___f_2577_; lean_object* v___x_2578_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
v_fst_2574_ = lean_ctor_get(v_a_2573_, 0);
lean_inc(v_fst_2574_);
v_snd_2575_ = lean_ctor_get(v_a_2573_, 1);
lean_inc_n(v_snd_2575_, 2);
lean_dec(v_a_2573_);
v___x_2576_ = lean_box(v___x_2571_);
v___f_2577_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2577_, 0, v_fst_2574_);
lean_closure_set(v___f_2577_, 1, v_snd_2575_);
lean_closure_set(v___f_2577_, 2, v___x_2576_);
lean_closure_set(v___f_2577_, 3, v_fvarSubst_2565_);
v___x_2578_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_snd_2575_, v___f_2577_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
return v___x_2578_;
}
else
{
lean_object* v_a_2579_; lean_object* v___x_2581_; uint8_t v_isShared_2582_; uint8_t v_isSharedCheck_2586_; 
lean_dec(v_fvarSubst_2565_);
v_a_2579_ = lean_ctor_get(v___x_2572_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2572_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2581_ = v___x_2572_;
v_isShared_2582_ = v_isSharedCheck_2586_;
goto v_resetjp_2580_;
}
else
{
lean_inc(v_a_2579_);
lean_dec(v___x_2572_);
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
}
LEAN_EXPORT void l_Lean_Meta_substEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2563_ = stack[0].m_obj;
lean_object* v_hFVarId_2564_ = stack[1].m_obj;
lean_object* v_fvarSubst_2565_ = stack[2].m_obj;
lean_object* v_a_2566_ = stack[3].m_obj;
lean_object* v_a_2567_ = stack[4].m_obj;
lean_object* v_a_2568_ = stack[5].m_obj;
lean_object* v_a_2569_ = stack[6].m_obj;
lean_object* v_res_2587_;
v_res_2587_ = l_Lean_Meta_substEq(v_mvarId_2563_, v_hFVarId_2564_, v_fvarSubst_2565_, v_a_2566_, v_a_2567_, v_a_2568_, v_a_2569_);
stack->m_obj
 = v_res_2587_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2588_, lean_object* v_hFVarId_2589_, lean_object* v_fvarSubst_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_, lean_object* v_a_2594_, lean_object* v_a_2595_){
_start:
{
lean_object* v_res_2596_; 
v_res_2596_ = l_Lean_Meta_substEq(v_mvarId_2588_, v_hFVarId_2589_, v_fvarSubst_2590_, v_a_2591_, v_a_2592_, v_a_2593_, v_a_2594_);
lean_dec(v_a_2594_);
lean_dec_ref(v_a_2593_);
lean_dec(v_a_2592_);
lean_dec_ref(v_a_2591_);
return v_res_2596_;
}
}
lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2597_, lean_object* v_mvarId_2598_, lean_object* v___y_2599_, lean_object* v___y_2600_, lean_object* v___y_2601_, lean_object* v___y_2602_){
_start:
{
lean_object* v___x_2604_; 
lean_inc(v_h_2597_);
v___x_2604_ = l_Lean_FVarId_getType___redArg(v_h_2597_, v___y_2599_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; lean_object* v___x_2606_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc_n(v_a_2605_, 2);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = l_Lean_Meta_matchEq_x3f(v_a_2605_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
if (lean_obj_tag(v_a_2607_) == 0)
{
lean_object* v___x_2608_; 
v___x_2608_ = l_Lean_Meta_matchHEq_x3f(v_a_2605_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
if (lean_obj_tag(v_a_2609_) == 0)
{
lean_object* v___x_2610_; 
v___x_2610_ = l_Lean_Meta_substVar(v_mvarId_2598_, v_h_2597_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2610_;
}
else
{
uint8_t v___x_2611_; lean_object* v___x_2612_; 
lean_dec_ref_known(v_a_2609_, 1);
v___x_2611_ = 1;
lean_inc(v_h_2597_);
lean_inc(v_mvarId_2598_);
v___x_2612_ = l_Lean_Meta_heqToEq(v_mvarId_2598_, v_h_2597_, v___x_2611_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v_fst_2614_; lean_object* v_snd_2615_; uint8_t v___x_2616_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v_fst_2614_ = lean_ctor_get(v_a_2613_, 0);
lean_inc(v_fst_2614_);
v_snd_2615_ = lean_ctor_get(v_a_2613_, 1);
lean_inc(v_snd_2615_);
lean_dec(v_a_2613_);
v___x_2616_ = l_Lean_instBEqMVarId_beq(v_mvarId_2598_, v_snd_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
lean_dec(v_mvarId_2598_);
lean_dec(v_h_2597_);
v___x_2617_ = l_Lean_Meta_subst(v_snd_2615_, v_fst_2614_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2617_;
}
else
{
lean_object* v___x_2618_; 
lean_dec(v_snd_2615_);
lean_dec(v_fst_2614_);
v___x_2618_ = l_Lean_Meta_substVar(v_mvarId_2598_, v_h_2597_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
return v___x_2618_;
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_mvarId_2598_);
lean_dec(v_h_2597_);
v_a_2619_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2612_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2612_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2624_; 
if (v_isShared_2622_ == 0)
{
v___x_2624_ = v___x_2621_;
goto v_reusejp_2623_;
}
else
{
lean_object* v_reuseFailAlloc_2625_; 
v_reuseFailAlloc_2625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2625_, 0, v_a_2619_);
v___x_2624_ = v_reuseFailAlloc_2625_;
goto v_reusejp_2623_;
}
v_reusejp_2623_:
{
return v___x_2624_;
}
}
}
}
}
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v_mvarId_2598_);
lean_dec(v_h_2597_);
v_a_2627_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2608_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2608_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2632_; 
if (v_isShared_2630_ == 0)
{
v___x_2632_ = v___x_2629_;
goto v_reusejp_2631_;
}
else
{
lean_object* v_reuseFailAlloc_2633_; 
v_reuseFailAlloc_2633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2633_, 0, v_a_2627_);
v___x_2632_ = v_reuseFailAlloc_2633_;
goto v_reusejp_2631_;
}
v_reusejp_2631_:
{
return v___x_2632_;
}
}
}
}
else
{
lean_object* v___x_2635_; lean_object* v___x_2636_; 
lean_dec_ref_known(v_a_2607_, 1);
lean_dec(v_a_2605_);
v___x_2635_ = lean_box(0);
v___x_2636_ = l_Lean_Meta_substEq(v_mvarId_2598_, v_h_2597_, v___x_2635_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
if (lean_obj_tag(v___x_2636_) == 0)
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2645_; 
v_a_2637_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2639_ = v___x_2636_;
v_isShared_2640_ = v_isSharedCheck_2645_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2636_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2645_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v_snd_2641_; lean_object* v___x_2643_; 
v_snd_2641_ = lean_ctor_get(v_a_2637_, 1);
lean_inc(v_snd_2641_);
lean_dec(v_a_2637_);
if (v_isShared_2640_ == 0)
{
lean_ctor_set(v___x_2639_, 0, v_snd_2641_);
v___x_2643_ = v___x_2639_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_snd_2641_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
v_a_2646_ = lean_ctor_get(v___x_2636_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2636_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2636_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2636_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec(v_a_2605_);
lean_dec(v_mvarId_2598_);
lean_dec(v_h_2597_);
v_a_2654_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2606_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2606_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
else
{
lean_object* v_a_2662_; lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
lean_dec(v_mvarId_2598_);
lean_dec(v_h_2597_);
v_a_2662_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2669_ == 0)
{
v___x_2664_ = v___x_2604_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_inc(v_a_2662_);
lean_dec(v___x_2604_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2662_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_subst___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_h_2597_ = stack[0].m_obj;
lean_object* v_mvarId_2598_ = stack[1].m_obj;
lean_object* v___y_2599_ = stack[2].m_obj;
lean_object* v___y_2600_ = stack[3].m_obj;
lean_object* v___y_2601_ = stack[4].m_obj;
lean_object* v___y_2602_ = stack[5].m_obj;
lean_object* v_res_2670_;
v_res_2670_ = l_Lean_Meta_subst___lam__0(v_h_2597_, v_mvarId_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_);
stack->m_obj
 = v_res_2670_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2671_, lean_object* v_mvarId_2672_, lean_object* v___y_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l_Lean_Meta_subst___lam__0(v_h_2671_, v_mvarId_2672_, v___y_2673_, v___y_2674_, v___y_2675_, v___y_2676_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v___y_2674_);
lean_dec_ref(v___y_2673_);
return v_res_2678_;
}
}
lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2679_, lean_object* v_h_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v___f_2686_; lean_object* v___x_2687_; 
lean_inc(v_mvarId_2679_);
v___f_2686_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2686_, 0, v_h_2680_);
lean_closure_set(v___f_2686_, 1, v_mvarId_2679_);
v___x_2687_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2679_, v___f_2686_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
return v___x_2687_;
}
}
LEAN_EXPORT void l_Lean_Meta_subst_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2679_ = stack[0].m_obj;
lean_object* v_h_2680_ = stack[1].m_obj;
lean_object* v_a_2681_ = stack[2].m_obj;
lean_object* v_a_2682_ = stack[3].m_obj;
lean_object* v_a_2683_ = stack[4].m_obj;
lean_object* v_a_2684_ = stack[5].m_obj;
lean_object* v_res_2688_;
v_res_2688_ = l_Lean_Meta_subst(v_mvarId_2679_, v_h_2680_, v_a_2681_, v_a_2682_, v_a_2683_, v_a_2684_);
stack->m_obj
 = v_res_2688_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2689_, lean_object* v_h_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lean_Meta_subst(v_mvarId_2689_, v_h_2690_, v_a_2691_, v_a_2692_, v_a_2693_, v_a_2694_);
lean_dec(v_a_2694_);
lean_dec_ref(v_a_2693_);
lean_dec(v_a_2692_);
lean_dec_ref(v_a_2691_);
return v_res_2696_;
}
}
lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_Meta_saveState___redArg(v___y_2699_, v___y_2701_);
if (lean_obj_tag(v___x_2703_) == 0)
{
lean_object* v_a_2704_; lean_object* v___x_2705_; 
v_a_2704_ = lean_ctor_get(v___x_2703_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2703_, 1);
lean_inc(v___y_2701_);
lean_inc_ref(v___y_2700_);
lean_inc(v___y_2699_);
lean_inc_ref(v___y_2698_);
v___x_2705_ = lean_apply_5(v_x_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, lean_box(0));
if (lean_obj_tag(v___x_2705_) == 0)
{
lean_dec(v_a_2704_);
return v___x_2705_;
}
else
{
lean_object* v_a_2706_; uint8_t v___y_2708_; uint8_t v___x_2726_; 
v_a_2706_ = lean_ctor_get(v___x_2705_, 0);
lean_inc(v_a_2706_);
v___x_2726_ = l_Lean_Exception_isInterrupt(v_a_2706_);
if (v___x_2726_ == 0)
{
uint8_t v___x_2727_; 
lean_inc(v_a_2706_);
v___x_2727_ = l_Lean_Exception_isRuntime(v_a_2706_);
v___y_2708_ = v___x_2727_;
goto v___jp_2707_;
}
else
{
v___y_2708_ = v___x_2726_;
goto v___jp_2707_;
}
v___jp_2707_:
{
if (v___y_2708_ == 0)
{
lean_object* v___x_2709_; 
lean_dec_ref_known(v___x_2705_, 1);
v___x_2709_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2704_, v___y_2699_, v___y_2701_);
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2716_ == 0)
{
lean_object* v_unused_2717_; 
v_unused_2717_ = lean_ctor_get(v___x_2709_, 0);
lean_dec(v_unused_2717_);
v___x_2711_ = v___x_2709_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_dec(v___x_2709_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
lean_ctor_set_tag(v___x_2711_, 1);
lean_ctor_set(v___x_2711_, 0, v_a_2706_);
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2706_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
else
{
lean_object* v_a_2718_; lean_object* v___x_2720_; uint8_t v_isShared_2721_; uint8_t v_isSharedCheck_2725_; 
lean_dec(v_a_2706_);
v_a_2718_ = lean_ctor_get(v___x_2709_, 0);
v_isSharedCheck_2725_ = !lean_is_exclusive(v___x_2709_);
if (v_isSharedCheck_2725_ == 0)
{
v___x_2720_ = v___x_2709_;
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
else
{
lean_inc(v_a_2718_);
lean_dec(v___x_2709_);
v___x_2720_ = lean_box(0);
v_isShared_2721_ = v_isSharedCheck_2725_;
goto v_resetjp_2719_;
}
v_resetjp_2719_:
{
lean_object* v___x_2723_; 
if (v_isShared_2721_ == 0)
{
v___x_2723_ = v___x_2720_;
goto v_reusejp_2722_;
}
else
{
lean_object* v_reuseFailAlloc_2724_; 
v_reuseFailAlloc_2724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2724_, 0, v_a_2718_);
v___x_2723_ = v_reuseFailAlloc_2724_;
goto v_reusejp_2722_;
}
v_reusejp_2722_:
{
return v___x_2723_;
}
}
}
}
else
{
lean_dec(v_a_2706_);
lean_dec(v_a_2704_);
return v___x_2705_;
}
}
}
}
else
{
lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2735_; 
lean_dec_ref(v_x_2697_);
v_a_2728_ = lean_ctor_get(v___x_2703_, 0);
v_isSharedCheck_2735_ = !lean_is_exclusive(v___x_2703_);
if (v_isSharedCheck_2735_ == 0)
{
v___x_2730_ = v___x_2703_;
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2703_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2735_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2733_; 
if (v_isShared_2731_ == 0)
{
v___x_2733_ = v___x_2730_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_a_2728_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2697_ = stack[0].m_obj;
lean_object* v___y_2698_ = stack[1].m_obj;
lean_object* v___y_2699_ = stack[2].m_obj;
lean_object* v___y_2700_ = stack[3].m_obj;
lean_object* v___y_2701_ = stack[4].m_obj;
lean_object* v_res_2736_;
v_res_2736_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
stack->m_obj
 = v_res_2736_;
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
return v_res_2743_;
}
}
lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2744_, lean_object* v_x_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_){
_start:
{
lean_object* v___x_2751_; 
v___x_2751_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
return v___x_2751_;
}
}
LEAN_EXPORT void l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_2745_ = stack[1].m_obj;
lean_object* v___y_2746_ = stack[2].m_obj;
lean_object* v___y_2747_ = stack[3].m_obj;
lean_object* v___y_2748_ = stack[4].m_obj;
lean_object* v___y_2749_ = stack[5].m_obj;
lean_object* v_res_2752_;
v_res_2752_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_box(0), v_x_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
stack->m_obj
 = v_res_2752_;
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2753_, lean_object* v_x_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_){
_start:
{
lean_object* v_res_2760_; 
v_res_2760_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2753_, v_x_2754_, v___y_2755_, v___y_2756_, v___y_2757_, v___y_2758_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
lean_dec(v___y_2756_);
lean_dec_ref(v___y_2755_);
return v_res_2760_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_){
_start:
{
lean_object* v_ref_2767_; lean_object* v___x_2768_; lean_object* v_a_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2777_; 
v_ref_2767_ = lean_ctor_get(v___y_2764_, 2);
v___x_2768_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msg_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2771_ = v___x_2768_;
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_a_2769_);
lean_dec(v___x_2768_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2777_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
lean_object* v___x_2773_; lean_object* v___x_2775_; 
lean_inc(v_ref_2767_);
v___x_2773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2773_, 0, v_ref_2767_);
lean_ctor_set(v___x_2773_, 1, v_a_2769_);
if (v_isShared_2772_ == 0)
{
lean_ctor_set_tag(v___x_2771_, 1);
lean_ctor_set(v___x_2771_, 0, v___x_2773_);
v___x_2775_ = v___x_2771_;
goto v_reusejp_2774_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2773_);
v___x_2775_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2774_;
}
v_reusejp_2774_:
{
return v___x_2775_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_2761_ = stack[0].m_obj;
lean_object* v___y_2762_ = stack[1].m_obj;
lean_object* v___y_2763_ = stack[2].m_obj;
lean_object* v___y_2764_ = stack[3].m_obj;
lean_object* v___y_2765_ = stack[4].m_obj;
lean_object* v_res_2778_;
v_res_2778_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2761_, v___y_2762_, v___y_2763_, v___y_2764_, v___y_2765_);
stack->m_obj
 = v_res_2778_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2779_, lean_object* v___y_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_){
_start:
{
lean_object* v_res_2785_; 
v_res_2785_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2779_, v___y_2780_, v___y_2781_, v___y_2782_, v___y_2783_);
lean_dec(v___y_2783_);
lean_dec_ref(v___y_2782_);
lean_dec(v___y_2781_);
lean_dec_ref(v___y_2780_);
return v_res_2785_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2787_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2788_ = l_Lean_stringToMessageData(v___x_2787_);
return v___x_2788_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2790_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2791_ = l_Lean_stringToMessageData(v___x_2790_);
return v___x_2791_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2794_ = l_Lean_stringToMessageData(v___x_2793_);
return v___x_2794_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2796_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2797_ = l_Lean_stringToMessageData(v___x_2796_);
return v___x_2797_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2800_ = l_Lean_stringToMessageData(v___x_2799_);
return v___x_2800_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2813_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2814_ = l_Lean_stringToMessageData(v___x_2813_);
return v___x_2814_;
}
}
lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2823_, uint8_t v_substLHS_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_){
_start:
{
lean_object* v___x_2830_; 
lean_inc(v_mvarId_2823_);
v___x_2830_ = l_Lean_MVarId_getType_x27(v_mvarId_2823_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
if (lean_obj_tag(v_a_2831_) == 7)
{
lean_object* v_binderType_2835_; lean_object* v_body_2836_; uint8_t v___x_2837_; lean_object* v___y_2839_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v_fst_2972_; lean_object* v_fst_2973_; lean_object* v_fst_2974_; lean_object* v_snd_2975_; lean_object* v___y_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2992_; lean_object* v___y_2993_; lean_object* v___y_2994_; lean_object* v___y_2995_; 
v_binderType_2835_ = lean_ctor_get(v_a_2831_, 1);
lean_inc_ref(v_binderType_2835_);
v_body_2836_ = lean_ctor_get(v_a_2831_, 2);
lean_inc_ref(v_body_2836_);
lean_dec_ref_known(v_a_2831_, 3);
v___x_2837_ = l_Lean_Expr_hasLooseBVars(v_body_2836_);
if (v___x_2837_ == 0)
{
lean_object* v___x_3006_; 
v___x_3006_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2835_, v___y_2826_);
if (lean_obj_tag(v___x_3006_) == 0)
{
lean_object* v_a_3007_; lean_object* v___x_3008_; uint8_t v___x_3009_; 
v_a_3007_ = lean_ctor_get(v___x_3006_, 0);
lean_inc(v_a_3007_);
lean_dec_ref_known(v___x_3006_, 1);
v___x_3008_ = l_Lean_Expr_cleanupAnnotations(v_a_3007_);
v___x_3009_ = l_Lean_Expr_isApp(v___x_3008_);
if (v___x_3009_ == 0)
{
lean_dec_ref(v___x_3008_);
lean_dec_ref(v_body_2836_);
lean_dec(v_mvarId_2823_);
v___y_2992_ = v___y_2825_;
v___y_2993_ = v___y_2826_;
v___y_2994_ = v___y_2827_;
v___y_2995_ = v___y_2828_;
goto v___jp_2991_;
}
else
{
lean_object* v_arg_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v_arg_3010_ = lean_ctor_get(v___x_3008_, 1);
lean_inc_ref(v_arg_3010_);
v___x_3011_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3008_);
v___x_3012_ = l_Lean_Expr_isApp(v___x_3011_);
if (v___x_3012_ == 0)
{
lean_dec_ref(v___x_3011_);
lean_dec_ref(v_arg_3010_);
lean_dec_ref(v_body_2836_);
lean_dec(v_mvarId_2823_);
v___y_2992_ = v___y_2825_;
v___y_2993_ = v___y_2826_;
v___y_2994_ = v___y_2827_;
v___y_2995_ = v___y_2828_;
goto v___jp_2991_;
}
else
{
lean_object* v_arg_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_arg_3013_ = lean_ctor_get(v___x_3011_, 1);
lean_inc_ref(v_arg_3013_);
v___x_3014_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3011_);
v___x_3015_ = l_Lean_Expr_isApp(v___x_3014_);
if (v___x_3015_ == 0)
{
lean_dec_ref(v___x_3014_);
lean_dec_ref(v_arg_3013_);
lean_dec_ref(v_arg_3010_);
lean_dec_ref(v_body_2836_);
lean_dec(v_mvarId_2823_);
v___y_2992_ = v___y_2825_;
v___y_2993_ = v___y_2826_;
v___y_2994_ = v___y_2827_;
v___y_2995_ = v___y_2828_;
goto v___jp_2991_;
}
else
{
lean_object* v_arg_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; uint8_t v___x_3019_; 
v_arg_3016_ = lean_ctor_get(v___x_3014_, 1);
lean_inc_ref(v_arg_3016_);
v___x_3017_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3014_);
v___x_3018_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_3019_ = l_Lean_Expr_isConstOf(v___x_3017_, v___x_3018_);
if (v___x_3019_ == 0)
{
uint8_t v___x_3020_; 
v___x_3020_ = l_Lean_Expr_isApp(v___x_3017_);
if (v___x_3020_ == 0)
{
lean_dec_ref(v___x_3017_);
lean_dec_ref(v_arg_3016_);
lean_dec_ref(v_arg_3013_);
lean_dec_ref(v_arg_3010_);
lean_dec_ref(v_body_2836_);
lean_dec(v_mvarId_2823_);
v___y_2992_ = v___y_2825_;
v___y_2993_ = v___y_2826_;
v___y_2994_ = v___y_2827_;
v___y_2995_ = v___y_2828_;
goto v___jp_2991_;
}
else
{
lean_object* v_arg_3021_; lean_object* v___y_3023_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint8_t v___x_3031_; 
v_arg_3021_ = lean_ctor_get(v___x_3017_, 1);
lean_inc_ref(v_arg_3021_);
v___x_3029_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3017_);
v___x_3030_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_3031_ = l_Lean_Expr_isConstOf(v___x_3029_, v___x_3030_);
lean_dec_ref(v___x_3029_);
if (v___x_3031_ == 0)
{
lean_dec_ref(v_arg_3021_);
lean_dec_ref(v_arg_3016_);
lean_dec_ref(v_arg_3013_);
lean_dec_ref(v_arg_3010_);
lean_dec_ref(v_body_2836_);
lean_dec(v_mvarId_2823_);
v___y_2992_ = v___y_2825_;
v___y_2993_ = v___y_2826_;
v___y_2994_ = v___y_2827_;
v___y_2995_ = v___y_2828_;
goto v___jp_2991_;
}
else
{
lean_object* v___x_3032_; 
lean_inc_ref(v_arg_3021_);
v___x_3032_ = l_Lean_Meta_isExprDefEq(v_arg_3021_, v_arg_3013_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
if (lean_obj_tag(v___x_3032_) == 0)
{
lean_object* v_a_3033_; uint8_t v___x_3034_; 
v_a_3033_ = lean_ctor_get(v___x_3032_, 0);
lean_inc(v_a_3033_);
lean_dec_ref_known(v___x_3032_, 1);
v___x_3034_ = lean_unbox(v_a_3033_);
lean_dec(v_a_3033_);
if (v___x_3034_ == 0)
{
lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec_ref(v_arg_3021_);
lean_dec_ref(v_arg_3016_);
lean_dec_ref(v_arg_3010_);
lean_dec_ref(v_body_2836_);
lean_dec(v_mvarId_2823_);
v___x_3035_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_3036_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3035_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
v_a_3037_ = lean_ctor_get(v___x_3036_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3036_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3036_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3036_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3037_);
v___x_3042_ = v_reuseFailAlloc_3043_;
goto v_reusejp_3041_;
}
v_reusejp_3041_:
{
return v___x_3042_;
}
}
}
else
{
v___y_3023_ = v___y_2825_;
v___y_3024_ = v___y_2826_;
v___y_3025_ = v___y_2827_;
v___y_3026_ = v___y_2828_;
goto v___jp_3022_;
}
}
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec_ref(v_arg_3021_);
lean_dec_ref(v_arg_3016_);
lean_dec_ref(v_arg_3010_);
lean_dec_ref(v_body_2836_);
lean_dec(v_mvarId_2823_);
v_a_3045_ = lean_ctor_get(v___x_3032_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3032_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3032_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3032_);
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
v___jp_3022_:
{
if (v_substLHS_2824_ == 0)
{
lean_object* v___x_3027_; 
v___x_3027_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2972_ = v_arg_3021_;
v_fst_2973_ = v_arg_3016_;
v_fst_2974_ = v_arg_3010_;
v_snd_2975_ = v___x_3027_;
v___y_2976_ = v___y_3023_;
v___y_2977_ = v___y_3024_;
v___y_2978_ = v___y_3025_;
v___y_2979_ = v___y_3026_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_3028_; 
v___x_3028_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2972_ = v_arg_3021_;
v_fst_2973_ = v_arg_3010_;
v_fst_2974_ = v_arg_3016_;
v_snd_2975_ = v___x_3028_;
v___y_2976_ = v___y_3023_;
v___y_2977_ = v___y_3024_;
v___y_2978_ = v___y_3025_;
v___y_2979_ = v___y_3026_;
goto v___jp_2971_;
}
}
}
}
else
{
lean_dec_ref(v___x_3017_);
if (v_substLHS_2824_ == 0)
{
lean_object* v___x_3053_; 
v___x_3053_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2972_ = v_arg_3016_;
v_fst_2973_ = v_arg_3013_;
v_fst_2974_ = v_arg_3010_;
v_snd_2975_ = v___x_3053_;
v___y_2976_ = v___y_2825_;
v___y_2977_ = v___y_2826_;
v___y_2978_ = v___y_2827_;
v___y_2979_ = v___y_2828_;
goto v___jp_2971_;
}
else
{
lean_object* v___x_3054_; 
v___x_3054_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2972_ = v_arg_3016_;
v_fst_2973_ = v_arg_3010_;
v_fst_2974_ = v_arg_3013_;
v_snd_2975_ = v___x_3054_;
v___y_2976_ = v___y_2825_;
v___y_2977_ = v___y_2826_;
v___y_2978_ = v___y_2827_;
v___y_2979_ = v___y_2828_;
goto v___jp_2971_;
}
}
}
}
}
}
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_dec_ref(v_body_2836_);
lean_dec(v_mvarId_2823_);
v_a_3055_ = lean_ctor_get(v___x_3006_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3006_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3006_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3006_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
else
{
lean_dec_ref(v_body_2836_);
lean_dec_ref(v_binderType_2835_);
lean_dec(v_mvarId_2823_);
goto v___jp_2832_;
}
v___jp_2838_:
{
lean_object* v___x_2850_; lean_object* v___x_2851_; uint8_t v___x_2852_; uint8_t v___x_2853_; lean_object* v___x_2854_; 
v___x_2850_ = lean_mk_empty_array_with_capacity(v___y_2845_);
lean_inc_ref(v___x_2850_);
v___x_2851_ = lean_array_push(v___x_2850_, v___y_2844_);
v___x_2852_ = 1;
v___x_2853_ = 1;
v___x_2854_ = l_Lean_Meta_mkLambdaFVars(v___x_2851_, v_body_2836_, v___x_2837_, v___x_2852_, v___x_2837_, v___x_2852_, v___x_2853_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
lean_dec_ref(v___x_2851_);
if (lean_obj_tag(v___x_2854_) == 0)
{
lean_object* v_a_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v_a_2855_ = lean_ctor_get(v___x_2854_, 0);
lean_inc_n(v_a_2855_, 2);
lean_dec_ref_known(v___x_2854_, 1);
lean_inc_ref(v___y_2839_);
v___x_2856_ = lean_array_push(v___x_2850_, v___y_2839_);
v___x_2857_ = l_Lean_Expr_beta(v_a_2855_, v___x_2856_);
lean_inc(v___y_2843_);
v___x_2858_ = l_Lean_MVarId_getTag(v___y_2843_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
if (lean_obj_tag(v___x_2858_) == 0)
{
lean_object* v_a_2859_; lean_object* v___x_2860_; 
v_a_2859_ = lean_ctor_get(v___x_2858_, 0);
lean_inc(v_a_2859_);
lean_dec_ref_known(v___x_2858_, 1);
lean_inc_ref(v___x_2857_);
v___x_2860_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2857_, v_a_2859_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v_a_2861_; lean_object* v___x_2862_; 
v_a_2861_ = lean_ctor_get(v___x_2860_, 0);
lean_inc(v_a_2861_);
lean_dec_ref_known(v___x_2860_, 1);
v___x_2862_ = l_Lean_Meta_getLevel(v___x_2857_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
if (lean_obj_tag(v___x_2862_) == 0)
{
lean_object* v_a_2863_; lean_object* v___x_2864_; 
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
lean_inc(v_a_2863_);
lean_dec_ref_known(v___x_2862_, 1);
lean_inc_ref(v___y_2841_);
v___x_2864_ = l_Lean_Meta_getLevel(v___y_2841_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2882_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
v___x_2866_ = lean_box(0);
v___x_2867_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2867_, 0, v_a_2865_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
v___x_2868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2868_, 0, v_a_2863_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
lean_inc(v___y_2842_);
v___x_2869_ = l_Lean_mkConst(v___y_2842_, v___x_2868_);
lean_inc(v_a_2861_);
lean_inc_ref(v___y_2839_);
v___x_2870_ = l_Lean_mkApp4(v___x_2869_, v___y_2841_, v___y_2839_, v_a_2855_, v_a_2861_);
v___x_2871_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v___y_2843_, v___x_2870_, v___y_2847_);
v_isSharedCheck_2882_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2882_ == 0)
{
lean_object* v_unused_2883_; 
v_unused_2883_ = lean_ctor_get(v___x_2871_, 0);
lean_dec(v_unused_2883_);
v___x_2873_ = v___x_2871_;
v_isShared_2874_ = v_isSharedCheck_2882_;
goto v_resetjp_2872_;
}
else
{
lean_dec(v___x_2871_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2882_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2875_ = l_Lean_Meta_FVarSubst_empty;
v___x_2876_ = l_Lean_Meta_FVarSubst_insert(v___x_2875_, v___y_2840_, v___y_2839_);
v___x_2877_ = l_Lean_Expr_mvarId_x21(v_a_2861_);
lean_dec(v_a_2861_);
v___x_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2878_, 0, v___x_2876_);
lean_ctor_set(v___x_2878_, 1, v___x_2877_);
if (v_isShared_2874_ == 0)
{
lean_ctor_set(v___x_2873_, 0, v___x_2878_);
v___x_2880_ = v___x_2873_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2881_; 
v_reuseFailAlloc_2881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2881_, 0, v___x_2878_);
v___x_2880_ = v_reuseFailAlloc_2881_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
return v___x_2880_;
}
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_a_2863_);
lean_dec(v_a_2861_);
lean_dec(v_a_2855_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
v_a_2884_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2864_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2864_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_a_2861_);
lean_dec(v_a_2855_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
v_a_2892_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2862_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2862_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec_ref(v___x_2857_);
lean_dec(v_a_2855_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
v_a_2900_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2860_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2860_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
else
{
lean_object* v_a_2908_; lean_object* v___x_2910_; uint8_t v_isShared_2911_; uint8_t v_isSharedCheck_2915_; 
lean_dec_ref(v___x_2857_);
lean_dec(v_a_2855_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
v_a_2908_ = lean_ctor_get(v___x_2858_, 0);
v_isSharedCheck_2915_ = !lean_is_exclusive(v___x_2858_);
if (v_isSharedCheck_2915_ == 0)
{
v___x_2910_ = v___x_2858_;
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
else
{
lean_inc(v_a_2908_);
lean_dec(v___x_2858_);
v___x_2910_ = lean_box(0);
v_isShared_2911_ = v_isSharedCheck_2915_;
goto v_resetjp_2909_;
}
v_resetjp_2909_:
{
lean_object* v___x_2913_; 
if (v_isShared_2911_ == 0)
{
v___x_2913_ = v___x_2910_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2914_; 
v_reuseFailAlloc_2914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2914_, 0, v_a_2908_);
v___x_2913_ = v_reuseFailAlloc_2914_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
return v___x_2913_;
}
}
}
}
else
{
lean_object* v_a_2916_; lean_object* v___x_2918_; uint8_t v_isShared_2919_; uint8_t v_isSharedCheck_2923_; 
lean_dec_ref(v___x_2850_);
lean_dec(v___y_2843_);
lean_dec_ref(v___y_2841_);
lean_dec(v___y_2840_);
lean_dec_ref(v___y_2839_);
v_a_2916_ = lean_ctor_get(v___x_2854_, 0);
v_isSharedCheck_2923_ = !lean_is_exclusive(v___x_2854_);
if (v_isSharedCheck_2923_ == 0)
{
v___x_2918_ = v___x_2854_;
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
else
{
lean_inc(v_a_2916_);
lean_dec(v___x_2854_);
v___x_2918_ = lean_box(0);
v_isShared_2919_ = v_isSharedCheck_2923_;
goto v_resetjp_2917_;
}
v_resetjp_2917_:
{
lean_object* v___x_2921_; 
if (v_isShared_2919_ == 0)
{
v___x_2921_ = v___x_2918_;
goto v_reusejp_2920_;
}
else
{
lean_object* v_reuseFailAlloc_2922_; 
v_reuseFailAlloc_2922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2922_, 0, v_a_2916_);
v___x_2921_ = v_reuseFailAlloc_2922_;
goto v_reusejp_2920_;
}
v_reusejp_2920_:
{
return v___x_2921_;
}
}
}
}
v___jp_2924_:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2933_ = l_Lean_Expr_fvarId_x21(v___y_2928_);
v___x_2934_ = lean_unsigned_to_nat(1u);
v___x_2935_ = lean_mk_empty_array_with_capacity(v___x_2934_);
lean_inc(v___x_2933_);
v___x_2936_ = lean_array_push(v___x_2935_, v___x_2933_);
v___x_2937_ = l_Lean_MVarId_revert(v_mvarId_2823_, v___x_2936_, v___x_2837_, v___x_2837_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v_a_2938_; lean_object* v_fst_2939_; lean_object* v_snd_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2962_; 
v_a_2938_ = lean_ctor_get(v___x_2937_, 0);
lean_inc(v_a_2938_);
lean_dec_ref_known(v___x_2937_, 1);
v_fst_2939_ = lean_ctor_get(v_a_2938_, 0);
v_snd_2940_ = lean_ctor_get(v_a_2938_, 1);
v_isSharedCheck_2962_ = !lean_is_exclusive(v_a_2938_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2942_ = v_a_2938_;
v_isShared_2943_ = v_isSharedCheck_2962_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snd_2940_);
lean_inc(v_fst_2939_);
lean_dec(v_a_2938_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2962_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; uint8_t v___x_2945_; 
v___x_2944_ = lean_array_get_size(v_fst_2939_);
lean_dec(v_fst_2939_);
v___x_2945_ = lean_nat_dec_eq(v___x_2944_, v___x_2934_);
if (v___x_2945_ == 0)
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2949_; 
lean_dec(v_snd_2940_);
lean_dec(v___x_2933_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec_ref(v_body_2836_);
v___x_2946_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2947_ = l_Lean_MessageData_ofExpr(v___y_2928_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set_tag(v___x_2942_, 7);
lean_ctor_set(v___x_2942_, 1, v___x_2947_);
lean_ctor_set(v___x_2942_, 0, v___x_2946_);
v___x_2949_ = v___x_2942_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2961_; 
v_reuseFailAlloc_2961_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2961_, 0, v___x_2946_);
lean_ctor_set(v_reuseFailAlloc_2961_, 1, v___x_2947_);
v___x_2949_ = v_reuseFailAlloc_2961_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v_a_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2960_; 
v___x_2950_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2951_, 0, v___x_2949_);
lean_ctor_set(v___x_2951_, 1, v___x_2950_);
v___x_2952_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2951_, v___y_2929_, v___y_2930_, v___y_2931_, v___y_2932_);
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2952_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2955_ = v___x_2952_;
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
else
{
lean_inc(v_a_2953_);
lean_dec(v___x_2952_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2960_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2958_; 
if (v_isShared_2956_ == 0)
{
v___x_2958_ = v___x_2955_;
goto v_reusejp_2957_;
}
else
{
lean_object* v_reuseFailAlloc_2959_; 
v_reuseFailAlloc_2959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2959_, 0, v_a_2953_);
v___x_2958_ = v_reuseFailAlloc_2959_;
goto v_reusejp_2957_;
}
v_reusejp_2957_:
{
return v___x_2958_;
}
}
}
}
else
{
lean_del_object(v___x_2942_);
v___y_2839_ = v___y_2925_;
v___y_2840_ = v___x_2933_;
v___y_2841_ = v___y_2926_;
v___y_2842_ = v___y_2927_;
v___y_2843_ = v_snd_2940_;
v___y_2844_ = v___y_2928_;
v___y_2845_ = v___x_2934_;
v___y_2846_ = v___y_2929_;
v___y_2847_ = v___y_2930_;
v___y_2848_ = v___y_2931_;
v___y_2849_ = v___y_2932_;
goto v___jp_2838_;
}
}
}
else
{
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec(v___x_2933_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v___y_2925_);
lean_dec_ref(v_body_2836_);
v_a_2963_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2937_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2937_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
v___jp_2971_:
{
uint8_t v___x_2980_; 
v___x_2980_ = l_Lean_Expr_isFVar(v_fst_2974_);
if (v___x_2980_ == 0)
{
lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v_fst_2974_);
lean_dec_ref(v_fst_2973_);
lean_dec_ref(v_fst_2972_);
lean_dec_ref(v_body_2836_);
lean_dec(v_mvarId_2823_);
v___x_2981_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2982_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2981_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2982_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2982_);
v___x_2985_ = lean_box(0);
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
v_resetjp_2984_:
{
lean_object* v___x_2988_; 
if (v_isShared_2986_ == 0)
{
v___x_2988_ = v___x_2985_;
goto v_reusejp_2987_;
}
else
{
lean_object* v_reuseFailAlloc_2989_; 
v_reuseFailAlloc_2989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2989_, 0, v_a_2983_);
v___x_2988_ = v_reuseFailAlloc_2989_;
goto v_reusejp_2987_;
}
v_reusejp_2987_:
{
return v___x_2988_;
}
}
}
else
{
v___y_2925_ = v_fst_2973_;
v___y_2926_ = v_fst_2972_;
v___y_2927_ = v_snd_2975_;
v___y_2928_ = v_fst_2974_;
v___y_2929_ = v___y_2976_;
v___y_2930_ = v___y_2977_;
v___y_2931_ = v___y_2978_;
v___y_2932_ = v___y_2979_;
goto v___jp_2924_;
}
}
v___jp_2991_:
{
lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
v___x_2996_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_2997_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2996_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2997_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2997_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_dec(v_a_2831_);
lean_dec(v_mvarId_2823_);
goto v___jp_2832_;
}
v___jp_2832_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2834_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2833_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
return v___x_2834_;
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_dec(v_mvarId_2823_);
v_a_3063_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_2830_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_2830_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_introSubstEq___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_2823_ = stack[0].m_obj;
uint8_t v_substLHS_2824_ = stack[1].m_num;
lean_object* v___y_2825_ = stack[2].m_obj;
lean_object* v___y_2826_ = stack[3].m_obj;
lean_object* v___y_2827_ = stack[4].m_obj;
lean_object* v___y_2828_ = stack[5].m_obj;
lean_object* v_res_3071_;
v_res_3071_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_2823_, v_substLHS_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
stack->m_obj
 = v_res_3071_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object* v_mvarId_3072_, lean_object* v_substLHS_3073_, lean_object* v___y_3074_, lean_object* v___y_3075_, lean_object* v___y_3076_, lean_object* v___y_3077_, lean_object* v___y_3078_){
_start:
{
uint8_t v_substLHS_boxed_3079_; lean_object* v_res_3080_; 
v_substLHS_boxed_3079_ = lean_unbox(v_substLHS_3073_);
v_res_3080_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_3072_, v_substLHS_boxed_3079_, v___y_3074_, v___y_3075_, v___y_3076_, v___y_3077_);
lean_dec(v___y_3077_);
lean_dec_ref(v___y_3076_);
lean_dec(v___y_3075_);
lean_dec_ref(v___y_3074_);
return v_res_3080_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3081_, lean_object* v_i_3082_, lean_object* v_k_3083_){
_start:
{
lean_object* v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = lean_array_get_size(v_keys_3081_);
v___x_3085_ = lean_nat_dec_lt(v_i_3082_, v___x_3084_);
if (v___x_3085_ == 0)
{
lean_dec(v_i_3082_);
return v___x_3085_;
}
else
{
lean_object* v_k_x27_3086_; uint8_t v___x_3087_; 
v_k_x27_3086_ = lean_array_fget_borrowed(v_keys_3081_, v_i_3082_);
v___x_3087_ = l_Lean_instBEqMVarId_beq(v_k_3083_, v_k_x27_3086_);
if (v___x_3087_ == 0)
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
v___x_3088_ = lean_unsigned_to_nat(1u);
v___x_3089_ = lean_nat_add(v_i_3082_, v___x_3088_);
lean_dec(v_i_3082_);
v_i_3082_ = v___x_3089_;
goto _start;
}
else
{
lean_dec(v_i_3082_);
return v___x_3085_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3081_ = stack[0].m_obj;
lean_object* v_i_3082_ = stack[1].m_obj;
lean_object* v_k_3083_ = stack[2].m_obj;
uint8_t v_res_3091_;
v_res_3091_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3081_, v_i_3082_, v_k_3083_);
stack->m_num = v_res_3091_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3092_, lean_object* v_i_3093_, lean_object* v_k_3094_){
_start:
{
uint8_t v_res_3095_; lean_object* v_r_3096_; 
v_res_3095_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3092_, v_i_3093_, v_k_3094_);
lean_dec(v_k_3094_);
lean_dec_ref(v_keys_3092_);
v_r_3096_ = lean_box(v_res_3095_);
return v_r_3096_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3097_, size_t v_x_3098_, lean_object* v_x_3099_){
_start:
{
if (lean_obj_tag(v_x_3097_) == 0)
{
lean_object* v_es_3100_; lean_object* v___x_3101_; size_t v___x_3102_; size_t v___x_3103_; lean_object* v_j_3104_; lean_object* v___x_3105_; 
v_es_3100_ = lean_ctor_get(v_x_3097_, 0);
v___x_3101_ = lean_box(2);
v___x_3102_ = ((size_t)31ULL);
v___x_3103_ = lean_usize_land(v_x_3098_, v___x_3102_);
v_j_3104_ = lean_usize_to_nat(v___x_3103_);
v___x_3105_ = lean_array_get_borrowed(v___x_3101_, v_es_3100_, v_j_3104_);
lean_dec(v_j_3104_);
switch(lean_obj_tag(v___x_3105_))
{
case 0:
{
lean_object* v_key_3106_; uint8_t v___x_3107_; 
v_key_3106_ = lean_ctor_get(v___x_3105_, 0);
v___x_3107_ = l_Lean_instBEqMVarId_beq(v_x_3099_, v_key_3106_);
return v___x_3107_;
}
case 1:
{
lean_object* v_node_3108_; size_t v___x_3109_; size_t v___x_3110_; 
v_node_3108_ = lean_ctor_get(v___x_3105_, 0);
v___x_3109_ = ((size_t)5ULL);
v___x_3110_ = lean_usize_shift_right(v_x_3098_, v___x_3109_);
v_x_3097_ = v_node_3108_;
v_x_3098_ = v___x_3110_;
goto _start;
}
default: 
{
uint8_t v___x_3112_; 
v___x_3112_ = 0;
return v___x_3112_;
}
}
}
else
{
lean_object* v_ks_3113_; lean_object* v___x_3114_; uint8_t v___x_3115_; 
v_ks_3113_ = lean_ctor_get(v_x_3097_, 0);
v___x_3114_ = lean_unsigned_to_nat(0u);
v___x_3115_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3113_, v___x_3114_, v_x_3099_);
return v___x_3115_;
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3097_ = stack[0].m_obj;
size_t v_x_3098_ = stack[1].m_num;
lean_object* v_x_3099_ = stack[2].m_obj;
uint8_t v_res_3116_;
v_res_3116_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3097_, v_x_3098_, v_x_3099_);
stack->m_num = v_res_3116_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3117_, lean_object* v_x_3118_, lean_object* v_x_3119_){
_start:
{
size_t v_x_10983__boxed_3120_; uint8_t v_res_3121_; lean_object* v_r_3122_; 
v_x_10983__boxed_3120_ = lean_unbox_usize(v_x_3118_);
lean_dec(v_x_3118_);
v_res_3121_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3117_, v_x_10983__boxed_3120_, v_x_3119_);
lean_dec(v_x_3119_);
lean_dec_ref(v_x_3117_);
v_r_3122_ = lean_box(v_res_3121_);
return v_r_3122_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3123_, lean_object* v_x_3124_){
_start:
{
uint64_t v___x_3125_; size_t v___x_3126_; uint8_t v___x_3127_; 
v___x_3125_ = l_Lean_instHashableMVarId_hash(v_x_3124_);
v___x_3126_ = lean_uint64_to_usize(v___x_3125_);
v___x_3127_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3123_, v___x_3126_, v_x_3124_);
return v___x_3127_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3123_ = stack[0].m_obj;
lean_object* v_x_3124_ = stack[1].m_obj;
uint8_t v_res_3128_;
v_res_3128_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3123_, v_x_3124_);
stack->m_num = v_res_3128_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3129_, lean_object* v_x_3130_){
_start:
{
uint8_t v_res_3131_; lean_object* v_r_3132_; 
v_res_3131_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3129_, v_x_3130_);
lean_dec(v_x_3130_);
lean_dec_ref(v_x_3129_);
v_r_3132_ = lean_box(v_res_3131_);
return v_r_3132_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3133_, lean_object* v___y_3134_){
_start:
{
lean_object* v___x_3136_; lean_object* v_mctx_3137_; lean_object* v_eAssignment_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___x_3136_ = lean_st_ref_get(v___y_3134_);
v_mctx_3137_ = lean_ctor_get(v___x_3136_, 0);
lean_inc_ref(v_mctx_3137_);
lean_dec(v___x_3136_);
v_eAssignment_3138_ = lean_ctor_get(v_mctx_3137_, 8);
lean_inc_ref(v_eAssignment_3138_);
lean_dec_ref(v_mctx_3137_);
v___x_3139_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3138_, v_mvarId_3133_);
lean_dec_ref(v_eAssignment_3138_);
v___x_3140_ = lean_box(v___x_3139_);
v___x_3141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3141_, 0, v___x_3140_);
return v___x_3141_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3133_ = stack[0].m_obj;
lean_object* v___y_3134_ = stack[1].m_obj;
lean_object* v_res_3142_;
v_res_3142_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3133_, v___y_3134_);
stack->m_obj
 = v_res_3142_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_){
_start:
{
lean_object* v_res_3146_; 
v_res_3146_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3143_, v___y_3144_);
lean_dec(v___y_3144_);
lean_dec(v_mvarId_3143_);
return v_res_3146_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3148_; lean_object* v___x_3149_; 
v___x_3148_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3149_ = l_Lean_stringToMessageData(v___x_3148_);
return v___x_3149_;
}
}
lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3150_, uint8_t v___y_3151_, lean_object* v_____r_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_, lean_object* v___y_3156_){
_start:
{
lean_object* v___x_3190_; lean_object* v_a_3191_; uint8_t v___x_3192_; 
v___x_3190_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3150_, v___y_3154_);
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref(v___x_3190_);
v___x_3192_ = lean_unbox(v_a_3191_);
lean_dec(v_a_3191_);
if (v___x_3192_ == 0)
{
goto v___jp_3158_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_mvarId_3150_);
v___x_3193_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3194_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3193_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
v_isSharedCheck_3202_ = !lean_is_exclusive(v___x_3194_);
if (v_isSharedCheck_3202_ == 0)
{
v___x_3197_ = v___x_3194_;
v_isShared_3198_ = v_isSharedCheck_3202_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___x_3194_);
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
v___jp_3158_:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Lean_Meta_intro1Core(v_mvarId_3150_, v___y_3151_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v_fst_3161_; lean_object* v_snd_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v_a_3160_ = lean_ctor_get(v___x_3159_, 0);
lean_inc(v_a_3160_);
lean_dec_ref_known(v___x_3159_, 1);
v_fst_3161_ = lean_ctor_get(v_a_3160_, 0);
lean_inc(v_fst_3161_);
v_snd_3162_ = lean_ctor_get(v_a_3160_, 1);
lean_inc(v_snd_3162_);
lean_dec(v_a_3160_);
v___x_3163_ = lean_box(0);
v___x_3164_ = l_Lean_Meta_substEq(v_snd_3162_, v_fst_3161_, v___x_3163_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
if (lean_obj_tag(v___x_3164_) == 0)
{
lean_object* v_a_3165_; lean_object* v___x_3167_; uint8_t v_isShared_3168_; uint8_t v_isSharedCheck_3173_; 
v_a_3165_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3173_ == 0)
{
v___x_3167_ = v___x_3164_;
v_isShared_3168_ = v_isSharedCheck_3173_;
goto v_resetjp_3166_;
}
else
{
lean_inc(v_a_3165_);
lean_dec(v___x_3164_);
v___x_3167_ = lean_box(0);
v_isShared_3168_ = v_isSharedCheck_3173_;
goto v_resetjp_3166_;
}
v_resetjp_3166_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3169_, 0, v_a_3165_);
if (v_isShared_3168_ == 0)
{
lean_ctor_set(v___x_3167_, 0, v___x_3169_);
v___x_3171_ = v___x_3167_;
goto v_reusejp_3170_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3169_);
v___x_3171_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3170_;
}
v_reusejp_3170_:
{
return v___x_3171_;
}
}
}
else
{
lean_object* v_a_3174_; lean_object* v___x_3176_; uint8_t v_isShared_3177_; uint8_t v_isSharedCheck_3181_; 
v_a_3174_ = lean_ctor_get(v___x_3164_, 0);
v_isSharedCheck_3181_ = !lean_is_exclusive(v___x_3164_);
if (v_isSharedCheck_3181_ == 0)
{
v___x_3176_ = v___x_3164_;
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
else
{
lean_inc(v_a_3174_);
lean_dec(v___x_3164_);
v___x_3176_ = lean_box(0);
v_isShared_3177_ = v_isSharedCheck_3181_;
goto v_resetjp_3175_;
}
v_resetjp_3175_:
{
lean_object* v___x_3179_; 
if (v_isShared_3177_ == 0)
{
v___x_3179_ = v___x_3176_;
goto v_reusejp_3178_;
}
else
{
lean_object* v_reuseFailAlloc_3180_; 
v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
v___x_3179_ = v_reuseFailAlloc_3180_;
goto v_reusejp_3178_;
}
v_reusejp_3178_:
{
return v___x_3179_;
}
}
}
}
else
{
lean_object* v_a_3182_; lean_object* v___x_3184_; uint8_t v_isShared_3185_; uint8_t v_isSharedCheck_3189_; 
v_a_3182_ = lean_ctor_get(v___x_3159_, 0);
v_isSharedCheck_3189_ = !lean_is_exclusive(v___x_3159_);
if (v_isSharedCheck_3189_ == 0)
{
v___x_3184_ = v___x_3159_;
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
else
{
lean_inc(v_a_3182_);
lean_dec(v___x_3159_);
v___x_3184_ = lean_box(0);
v_isShared_3185_ = v_isSharedCheck_3189_;
goto v_resetjp_3183_;
}
v_resetjp_3183_:
{
lean_object* v___x_3187_; 
if (v_isShared_3185_ == 0)
{
v___x_3187_ = v___x_3184_;
goto v_reusejp_3186_;
}
else
{
lean_object* v_reuseFailAlloc_3188_; 
v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
v___x_3187_ = v_reuseFailAlloc_3188_;
goto v_reusejp_3186_;
}
v_reusejp_3186_:
{
return v___x_3187_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_introSubstEq___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3150_ = stack[0].m_obj;
uint8_t v___y_3151_ = stack[1].m_num;
lean_object* v_____r_3152_ = stack[2].m_obj;
lean_object* v___y_3153_ = stack[3].m_obj;
lean_object* v___y_3154_ = stack[4].m_obj;
lean_object* v___y_3155_ = stack[5].m_obj;
lean_object* v___y_3156_ = stack[6].m_obj;
lean_object* v_res_3203_;
v_res_3203_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3150_, v___y_3151_, v_____r_3152_, v___y_3153_, v___y_3154_, v___y_3155_, v___y_3156_);
stack->m_obj
 = v_res_3203_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3204_, lean_object* v___y_3205_, lean_object* v_____r_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
uint8_t v___y_11091__boxed_3212_; lean_object* v_res_3213_; 
v___y_11091__boxed_3212_ = lean_unbox(v___y_3205_);
v_res_3213_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3204_, v___y_11091__boxed_3212_, v_____r_3206_, v___y_3207_, v___y_3208_, v___y_3209_, v___y_3210_);
lean_dec(v___y_3210_);
lean_dec_ref(v___y_3209_);
lean_dec(v___y_3208_);
lean_dec_ref(v___y_3207_);
return v_res_3213_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__2(void){
_start:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3217_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3218_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
v___x_3219_ = l_Lean_Name_append(v___x_3218_, v___x_3217_);
return v___x_3219_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__4(void){
_start:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__3));
v___x_3222_ = l_Lean_stringToMessageData(v___x_3221_);
return v___x_3222_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__6(void){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__5));
v___x_3225_ = l_Lean_stringToMessageData(v___x_3224_);
return v___x_3225_;
}
}
lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3226_, uint8_t v_substLHS_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_, lean_object* v_a_3231_){
_start:
{
lean_object* v___y_3234_; lean_object* v___y_3253_; lean_object* v___x_3256_; lean_object* v___f_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3256_ = lean_box(v_substLHS_3227_);
lean_inc_n(v_mvarId_3226_, 2);
v___f_3257_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3257_, 0, v_mvarId_3226_);
lean_closure_set(v___f_3257_, 1, v___x_3256_);
v___x_3258_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
v___x_3259_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3226_, v___x_3258_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
lean_dec_ref_known(v___x_3259_, 1);
lean_inc(v_mvarId_3226_);
v___x_3260_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed), 8, 3);
lean_closure_set(v___x_3260_, 0, lean_box(0));
lean_closure_set(v___x_3260_, 1, v_mvarId_3226_);
lean_closure_set(v___x_3260_, 2, v___f_3257_);
v___x_3261_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3260_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3261_) == 0)
{
lean_dec(v_mvarId_3226_);
return v___x_3261_;
}
else
{
lean_object* v_a_3262_; uint8_t v___y_3264_; uint8_t v___x_3299_; 
v_a_3262_ = lean_ctor_get(v___x_3261_, 0);
v___x_3299_ = l_Lean_Exception_isInterrupt(v_a_3262_);
if (v___x_3299_ == 0)
{
uint8_t v___x_3300_; 
lean_inc(v_a_3262_);
v___x_3300_ = l_Lean_Exception_isRuntime(v_a_3262_);
v___y_3264_ = v___x_3300_;
goto v___jp_3263_;
}
else
{
v___y_3264_ = v___x_3299_;
goto v___jp_3263_;
}
v___jp_3263_:
{
if (v___y_3264_ == 0)
{
lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3297_; 
lean_inc(v_a_3262_);
v_isSharedCheck_3297_ = !lean_is_exclusive(v___x_3261_);
if (v_isSharedCheck_3297_ == 0)
{
lean_object* v_unused_3298_; 
v_unused_3298_ = lean_ctor_get(v___x_3261_, 0);
lean_dec(v_unused_3298_);
v___x_3266_ = v___x_3261_;
v_isShared_3267_ = v_isSharedCheck_3297_;
goto v_resetjp_3265_;
}
else
{
lean_dec(v___x_3261_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3297_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v_toCold_3268_; lean_object* v_options_3269_; lean_object* v_inheritedTraceOptions_3270_; uint8_t v_hasTrace_3271_; lean_object* v___x_3272_; lean_object* v___f_3273_; 
v_toCold_3268_ = lean_ctor_get(v_a_3230_, 0);
v_options_3269_ = lean_ctor_get(v_toCold_3268_, 2);
v_inheritedTraceOptions_3270_ = lean_ctor_get(v_toCold_3268_, 11);
v_hasTrace_3271_ = lean_ctor_get_uint8(v_options_3269_, sizeof(void*)*1);
v___x_3272_ = lean_box(v___y_3264_);
lean_inc(v_mvarId_3226_);
v___f_3273_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3273_, 0, v_mvarId_3226_);
lean_closure_set(v___f_3273_, 1, v___x_3272_);
if (v_hasTrace_3271_ == 0)
{
lean_del_object(v___x_3266_);
lean_dec(v_a_3262_);
lean_dec(v_mvarId_3226_);
v___y_3253_ = v___f_3273_;
goto v___jp_3252_;
}
else
{
lean_object* v___x_3274_; lean_object* v___x_3275_; uint8_t v___x_3276_; 
v___x_3274_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3275_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__2, &l_Lean_Meta_introSubstEq___closed__2_once, _init_l_Lean_Meta_introSubstEq___closed__2);
v___x_3276_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3270_, v_options_3269_, v___x_3275_);
if (v___x_3276_ == 0)
{
lean_del_object(v___x_3266_);
lean_dec(v_a_3262_);
lean_dec(v_mvarId_3226_);
v___y_3253_ = v___f_3273_;
goto v___jp_3252_;
}
else
{
lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3283_; 
lean_dec_ref(v___f_3273_);
v___x_3277_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__4, &l_Lean_Meta_introSubstEq___closed__4_once, _init_l_Lean_Meta_introSubstEq___closed__4);
v___x_3278_ = l_Lean_Exception_toMessageData(v_a_3262_);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
v___x_3280_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__6, &l_Lean_Meta_introSubstEq___closed__6_once, _init_l_Lean_Meta_introSubstEq___closed__6);
v___x_3281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3279_);
lean_ctor_set(v___x_3281_, 1, v___x_3280_);
lean_inc(v_mvarId_3226_);
if (v_isShared_3267_ == 0)
{
lean_ctor_set(v___x_3266_, 0, v_mvarId_3226_);
v___x_3283_ = v___x_3266_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3296_; 
v_reuseFailAlloc_3296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3296_, 0, v_mvarId_3226_);
v___x_3283_ = v_reuseFailAlloc_3296_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
lean_object* v___x_3284_; lean_object* v___x_3285_; 
v___x_3284_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3281_);
lean_ctor_set(v___x_3284_, 1, v___x_3283_);
v___x_3285_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_3274_, v___x_3284_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
if (lean_obj_tag(v___x_3285_) == 0)
{
lean_object* v_a_3286_; lean_object* v___x_3287_; 
v_a_3286_ = lean_ctor_get(v___x_3285_, 0);
lean_inc(v_a_3286_);
lean_dec_ref_known(v___x_3285_, 1);
v___x_3287_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3226_, v___y_3264_, v_a_3286_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
v___y_3234_ = v___x_3287_;
goto v___jp_3233_;
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_dec(v_mvarId_3226_);
v_a_3288_ = lean_ctor_get(v___x_3285_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3285_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3285_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3285_);
v___x_3290_ = lean_box(0);
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
v_resetjp_3289_:
{
lean_object* v___x_3293_; 
if (v_isShared_3291_ == 0)
{
v___x_3293_ = v___x_3290_;
goto v_reusejp_3292_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
v___x_3293_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3292_;
}
v_reusejp_3292_:
{
return v___x_3293_;
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
lean_dec(v_mvarId_3226_);
return v___x_3261_;
}
}
}
}
else
{
lean_object* v_a_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3308_; 
lean_dec_ref(v___f_3257_);
lean_dec(v_mvarId_3226_);
v_a_3301_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3303_ = v___x_3259_;
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_a_3301_);
lean_dec(v___x_3259_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3308_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3306_; 
if (v_isShared_3304_ == 0)
{
v___x_3306_ = v___x_3303_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v_a_3301_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
v___jp_3233_:
{
if (lean_obj_tag(v___y_3234_) == 0)
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3243_; 
v_a_3235_ = lean_ctor_get(v___y_3234_, 0);
v_isSharedCheck_3243_ = !lean_is_exclusive(v___y_3234_);
if (v_isSharedCheck_3243_ == 0)
{
v___x_3237_ = v___y_3234_;
v_isShared_3238_ = v_isSharedCheck_3243_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___y_3234_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3243_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v_a_3239_; lean_object* v___x_3241_; 
v_a_3239_ = lean_ctor_get(v_a_3235_, 0);
lean_inc(v_a_3239_);
lean_dec(v_a_3235_);
if (v_isShared_3238_ == 0)
{
lean_ctor_set(v___x_3237_, 0, v_a_3239_);
v___x_3241_ = v___x_3237_;
goto v_reusejp_3240_;
}
else
{
lean_object* v_reuseFailAlloc_3242_; 
v_reuseFailAlloc_3242_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3242_, 0, v_a_3239_);
v___x_3241_ = v_reuseFailAlloc_3242_;
goto v_reusejp_3240_;
}
v_reusejp_3240_:
{
return v___x_3241_;
}
}
}
else
{
lean_object* v_a_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3251_; 
v_a_3244_ = lean_ctor_get(v___y_3234_, 0);
v_isSharedCheck_3251_ = !lean_is_exclusive(v___y_3234_);
if (v_isSharedCheck_3251_ == 0)
{
v___x_3246_ = v___y_3234_;
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_a_3244_);
lean_dec(v___y_3234_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3251_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3249_; 
if (v_isShared_3247_ == 0)
{
v___x_3249_ = v___x_3246_;
goto v_reusejp_3248_;
}
else
{
lean_object* v_reuseFailAlloc_3250_; 
v_reuseFailAlloc_3250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3250_, 0, v_a_3244_);
v___x_3249_ = v_reuseFailAlloc_3250_;
goto v_reusejp_3248_;
}
v_reusejp_3248_:
{
return v___x_3249_;
}
}
}
}
v___jp_3252_:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = lean_box(0);
lean_inc(v_a_3231_);
lean_inc_ref(v_a_3230_);
lean_inc(v_a_3229_);
lean_inc_ref(v_a_3228_);
v___x_3255_ = lean_apply_6(v___y_3253_, v___x_3254_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_, lean_box(0));
v___y_3234_ = v___x_3255_;
goto v___jp_3233_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_introSubstEq_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3226_ = stack[0].m_obj;
uint8_t v_substLHS_3227_ = stack[1].m_num;
lean_object* v_a_3228_ = stack[2].m_obj;
lean_object* v_a_3229_ = stack[3].m_obj;
lean_object* v_a_3230_ = stack[4].m_obj;
lean_object* v_a_3231_ = stack[5].m_obj;
lean_object* v_res_3309_;
v_res_3309_ = l_Lean_Meta_introSubstEq(v_mvarId_3226_, v_substLHS_3227_, v_a_3228_, v_a_3229_, v_a_3230_, v_a_3231_);
stack->m_obj
 = v_res_3309_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object* v_mvarId_3310_, lean_object* v_substLHS_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_, lean_object* v_a_3314_, lean_object* v_a_3315_, lean_object* v_a_3316_){
_start:
{
uint8_t v_substLHS_boxed_3317_; lean_object* v_res_3318_; 
v_substLHS_boxed_3317_ = lean_unbox(v_substLHS_3311_);
v_res_3318_ = l_Lean_Meta_introSubstEq(v_mvarId_3310_, v_substLHS_boxed_3317_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_);
lean_dec(v_a_3315_);
lean_dec_ref(v_a_3314_);
lean_dec(v_a_3313_);
lean_dec_ref(v_a_3312_);
return v_res_3318_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object* v_00_u03b1_3319_, lean_object* v_msg_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_, lean_object* v___y_3324_){
_start:
{
lean_object* v___x_3326_; 
v___x_3326_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
return v___x_3326_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_3320_ = stack[1].m_obj;
lean_object* v___y_3321_ = stack[2].m_obj;
lean_object* v___y_3322_ = stack[3].m_obj;
lean_object* v___y_3323_ = stack[4].m_obj;
lean_object* v___y_3324_ = stack[5].m_obj;
lean_object* v_res_3327_;
v_res_3327_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_box(0), v_msg_3320_, v___y_3321_, v___y_3322_, v___y_3323_, v___y_3324_);
stack->m_obj
 = v_res_3327_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object* v_00_u03b1_3328_, lean_object* v_msg_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(v_00_u03b1_3328_, v_msg_3329_, v___y_3330_, v___y_3331_, v___y_3332_, v___y_3333_);
lean_dec(v___y_3333_);
lean_dec_ref(v___y_3332_);
lean_dec(v___y_3331_);
lean_dec_ref(v___y_3330_);
return v_res_3335_;
}
}
lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object* v_mvarId_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_, lean_object* v___y_3340_){
_start:
{
lean_object* v___x_3342_; 
v___x_3342_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3336_, v___y_3338_);
return v___x_3342_;
}
}
LEAN_EXPORT void l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3336_ = stack[0].m_obj;
lean_object* v___y_3337_ = stack[1].m_obj;
lean_object* v___y_3338_ = stack[2].m_obj;
lean_object* v___y_3339_ = stack[3].m_obj;
lean_object* v___y_3340_ = stack[4].m_obj;
lean_object* v_res_3343_;
v_res_3343_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3336_, v___y_3337_, v___y_3338_, v___y_3339_, v___y_3340_);
stack->m_obj
 = v_res_3343_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object* v_mvarId_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
lean_object* v_res_3350_; 
v_res_3350_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec(v_mvarId_3344_);
return v_res_3350_;
}
}
uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object* v_00_u03b2_3351_, lean_object* v_x_3352_, lean_object* v_x_3353_){
_start:
{
uint8_t v___x_3354_; 
v___x_3354_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3352_, v_x_3353_);
return v___x_3354_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3352_ = stack[1].m_obj;
lean_object* v_x_3353_ = stack[2].m_obj;
uint8_t v_res_3355_;
v_res_3355_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_box(0), v_x_3352_, v_x_3353_);
stack->m_num = v_res_3355_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3356_, lean_object* v_x_3357_, lean_object* v_x_3358_){
_start:
{
uint8_t v_res_3359_; lean_object* v_r_3360_; 
v_res_3359_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(v_00_u03b2_3356_, v_x_3357_, v_x_3358_);
lean_dec(v_x_3358_);
lean_dec_ref(v_x_3357_);
v_r_3360_ = lean_box(v_res_3359_);
return v_r_3360_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_3361_, lean_object* v_x_3362_, size_t v_x_3363_, lean_object* v_x_3364_){
_start:
{
uint8_t v___x_3365_; 
v___x_3365_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3362_, v_x_3363_, v_x_3364_);
return v___x_3365_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3362_ = stack[1].m_obj;
size_t v_x_3363_ = stack[2].m_num;
lean_object* v_x_3364_ = stack[3].m_obj;
uint8_t v_res_3366_;
v_res_3366_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_box(0), v_x_3362_, v_x_3363_, v_x_3364_);
stack->m_num = v_res_3366_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3367_, lean_object* v_x_3368_, lean_object* v_x_3369_, lean_object* v_x_3370_){
_start:
{
size_t v_x_11622__boxed_3371_; uint8_t v_res_3372_; lean_object* v_r_3373_; 
v_x_11622__boxed_3371_ = lean_unbox_usize(v_x_3369_);
lean_dec(v_x_3369_);
v_res_3372_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3367_, v_x_3368_, v_x_11622__boxed_3371_, v_x_3370_);
lean_dec(v_x_3370_);
lean_dec_ref(v_x_3368_);
v_r_3373_ = lean_box(v_res_3372_);
return v_r_3373_;
}
}
uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3374_, lean_object* v_keys_3375_, lean_object* v_vals_3376_, lean_object* v_heq_3377_, lean_object* v_i_3378_, lean_object* v_k_3379_){
_start:
{
uint8_t v___x_3380_; 
v___x_3380_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3375_, v_i_3378_, v_k_3379_);
return v___x_3380_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_keys_3375_ = stack[1].m_obj;
lean_object* v_vals_3376_ = stack[2].m_obj;
lean_object* v_i_3378_ = stack[4].m_obj;
lean_object* v_k_3379_ = stack[5].m_obj;
uint8_t v_res_3381_;
v_res_3381_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_box(0), v_keys_3375_, v_vals_3376_, lean_box(0), v_i_3378_, v_k_3379_);
stack->m_num = v_res_3381_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3382_, lean_object* v_keys_3383_, lean_object* v_vals_3384_, lean_object* v_heq_3385_, lean_object* v_i_3386_, lean_object* v_k_3387_){
_start:
{
uint8_t v_res_3388_; lean_object* v_r_3389_; 
v_res_3388_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(v_00_u03b2_3382_, v_keys_3383_, v_vals_3384_, v_heq_3385_, v_i_3386_, v_k_3387_);
lean_dec(v_k_3387_);
lean_dec_ref(v_vals_3384_);
lean_dec_ref(v_keys_3383_);
v_r_3389_ = lean_box(v_res_3388_);
return v_r_3389_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* v_x_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_){
_start:
{
lean_object* v___x_3396_; 
v___x_3396_ = l_Lean_Meta_saveState___redArg(v___y_3392_, v___y_3394_);
if (lean_obj_tag(v___x_3396_) == 0)
{
lean_object* v_a_3397_; lean_object* v___x_3398_; 
v_a_3397_ = lean_ctor_get(v___x_3396_, 0);
lean_inc(v_a_3397_);
lean_dec_ref_known(v___x_3396_, 1);
lean_inc(v___y_3394_);
lean_inc_ref(v___y_3393_);
lean_inc(v___y_3392_);
lean_inc_ref(v___y_3391_);
v___x_3398_ = lean_apply_5(v_x_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_, lean_box(0));
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v_a_3399_; lean_object* v___x_3401_; uint8_t v_isShared_3402_; uint8_t v_isSharedCheck_3407_; 
lean_dec(v_a_3397_);
v_a_3399_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3407_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3407_ == 0)
{
v___x_3401_ = v___x_3398_;
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
else
{
lean_inc(v_a_3399_);
lean_dec(v___x_3398_);
v___x_3401_ = lean_box(0);
v_isShared_3402_ = v_isSharedCheck_3407_;
goto v_resetjp_3400_;
}
v_resetjp_3400_:
{
lean_object* v___x_3403_; lean_object* v___x_3405_; 
v___x_3403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3403_, 0, v_a_3399_);
if (v_isShared_3402_ == 0)
{
lean_ctor_set(v___x_3401_, 0, v___x_3403_);
v___x_3405_ = v___x_3401_;
goto v_reusejp_3404_;
}
else
{
lean_object* v_reuseFailAlloc_3406_; 
v_reuseFailAlloc_3406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3406_, 0, v___x_3403_);
v___x_3405_ = v_reuseFailAlloc_3406_;
goto v_reusejp_3404_;
}
v_reusejp_3404_:
{
return v___x_3405_;
}
}
}
else
{
lean_object* v_a_3408_; lean_object* v___x_3410_; uint8_t v_isShared_3411_; uint8_t v_isSharedCheck_3437_; 
v_a_3408_ = lean_ctor_get(v___x_3398_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3398_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3410_ = v___x_3398_;
v_isShared_3411_ = v_isSharedCheck_3437_;
goto v_resetjp_3409_;
}
else
{
lean_inc(v_a_3408_);
lean_dec(v___x_3398_);
v___x_3410_ = lean_box(0);
v_isShared_3411_ = v_isSharedCheck_3437_;
goto v_resetjp_3409_;
}
v_resetjp_3409_:
{
uint8_t v___y_3413_; uint8_t v___x_3435_; 
v___x_3435_ = l_Lean_Exception_isInterrupt(v_a_3408_);
if (v___x_3435_ == 0)
{
uint8_t v___x_3436_; 
lean_inc(v_a_3408_);
v___x_3436_ = l_Lean_Exception_isRuntime(v_a_3408_);
v___y_3413_ = v___x_3436_;
goto v___jp_3412_;
}
else
{
v___y_3413_ = v___x_3435_;
goto v___jp_3412_;
}
v___jp_3412_:
{
if (v___y_3413_ == 0)
{
lean_object* v___x_3414_; 
lean_del_object(v___x_3410_);
lean_dec(v_a_3408_);
v___x_3414_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3397_, v___y_3392_, v___y_3394_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v___x_3416_; uint8_t v_isShared_3417_; uint8_t v_isSharedCheck_3422_; 
v_isSharedCheck_3422_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3422_ == 0)
{
lean_object* v_unused_3423_; 
v_unused_3423_ = lean_ctor_get(v___x_3414_, 0);
lean_dec(v_unused_3423_);
v___x_3416_ = v___x_3414_;
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
else
{
lean_dec(v___x_3414_);
v___x_3416_ = lean_box(0);
v_isShared_3417_ = v_isSharedCheck_3422_;
goto v_resetjp_3415_;
}
v_resetjp_3415_:
{
lean_object* v___x_3418_; lean_object* v___x_3420_; 
v___x_3418_ = lean_box(0);
if (v_isShared_3417_ == 0)
{
lean_ctor_set(v___x_3416_, 0, v___x_3418_);
v___x_3420_ = v___x_3416_;
goto v_reusejp_3419_;
}
else
{
lean_object* v_reuseFailAlloc_3421_; 
v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3418_);
v___x_3420_ = v_reuseFailAlloc_3421_;
goto v_reusejp_3419_;
}
v_reusejp_3419_:
{
return v___x_3420_;
}
}
}
else
{
lean_object* v_a_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3431_; 
v_a_3424_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3431_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3431_ == 0)
{
v___x_3426_ = v___x_3414_;
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_a_3424_);
lean_dec(v___x_3414_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3431_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3429_; 
if (v_isShared_3427_ == 0)
{
v___x_3429_ = v___x_3426_;
goto v_reusejp_3428_;
}
else
{
lean_object* v_reuseFailAlloc_3430_; 
v_reuseFailAlloc_3430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3430_, 0, v_a_3424_);
v___x_3429_ = v_reuseFailAlloc_3430_;
goto v_reusejp_3428_;
}
v_reusejp_3428_:
{
return v___x_3429_;
}
}
}
}
else
{
lean_object* v___x_3433_; 
lean_dec(v_a_3397_);
if (v_isShared_3411_ == 0)
{
v___x_3433_ = v___x_3410_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3408_);
v___x_3433_ = v_reuseFailAlloc_3434_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
return v___x_3433_;
}
}
}
}
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v_x_3390_);
v_a_3438_ = lean_ctor_get(v___x_3396_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3396_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3396_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3396_);
v___x_3440_ = lean_box(0);
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
v_resetjp_3439_:
{
lean_object* v___x_3443_; 
if (v_isShared_3441_ == 0)
{
v___x_3443_ = v___x_3440_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v_a_3438_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3390_ = stack[0].m_obj;
lean_object* v___y_3391_ = stack[1].m_obj;
lean_object* v___y_3392_ = stack[2].m_obj;
lean_object* v___y_3393_ = stack[3].m_obj;
lean_object* v___y_3394_ = stack[4].m_obj;
lean_object* v_res_3446_;
v_res_3446_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
stack->m_obj
 = v_res_3446_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object* v_x_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_, lean_object* v___y_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3447_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
lean_dec(v___y_3451_);
lean_dec_ref(v___y_3450_);
lean_dec(v___y_3449_);
lean_dec_ref(v___y_3448_);
return v_res_3453_;
}
}
lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object* v_00_u03b1_3454_, lean_object* v_x_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v___x_3461_; 
v___x_3461_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
return v___x_3461_;
}
}
LEAN_EXPORT void l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_3455_ = stack[1].m_obj;
lean_object* v___y_3456_ = stack[2].m_obj;
lean_object* v___y_3457_ = stack[3].m_obj;
lean_object* v___y_3458_ = stack[4].m_obj;
lean_object* v___y_3459_ = stack[5].m_obj;
lean_object* v_res_3462_;
v_res_3462_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_box(0), v_x_3455_, v___y_3456_, v___y_3457_, v___y_3458_, v___y_3459_);
stack->m_obj
 = v_res_3462_;
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object* v_00_u03b1_3463_, lean_object* v_x_3464_, lean_object* v___y_3465_, lean_object* v___y_3466_, lean_object* v___y_3467_, lean_object* v___y_3468_, lean_object* v___y_3469_){
_start:
{
lean_object* v_res_3470_; 
v_res_3470_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(v_00_u03b1_3463_, v_x_3464_, v___y_3465_, v___y_3466_, v___y_3467_, v___y_3468_);
lean_dec(v___y_3468_);
lean_dec_ref(v___y_3467_);
lean_dec(v___y_3466_);
lean_dec_ref(v___y_3465_);
return v_res_3470_;
}
}
lean_object* l_Lean_Meta_substVar_x3f(lean_object* v_mvarId_3471_, lean_object* v_hFVarId_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v___x_3478_; lean_object* v___x_3479_; 
v___x_3478_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___boxed), 7, 2);
lean_closure_set(v___x_3478_, 0, v_mvarId_3471_);
lean_closure_set(v___x_3478_, 1, v_hFVarId_3472_);
v___x_3479_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3478_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
return v___x_3479_;
}
}
LEAN_EXPORT void l_Lean_Meta_substVar_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3471_ = stack[0].m_obj;
lean_object* v_hFVarId_3472_ = stack[1].m_obj;
lean_object* v_a_3473_ = stack[2].m_obj;
lean_object* v_a_3474_ = stack[3].m_obj;
lean_object* v_a_3475_ = stack[4].m_obj;
lean_object* v_a_3476_ = stack[5].m_obj;
lean_object* v_res_3480_;
v_res_3480_ = l_Lean_Meta_substVar_x3f(v_mvarId_3471_, v_hFVarId_3472_, v_a_3473_, v_a_3474_, v_a_3475_, v_a_3476_);
stack->m_obj
 = v_res_3480_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object* v_mvarId_3481_, lean_object* v_hFVarId_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_){
_start:
{
lean_object* v_res_3488_; 
v_res_3488_ = l_Lean_Meta_substVar_x3f(v_mvarId_3481_, v_hFVarId_3482_, v_a_3483_, v_a_3484_, v_a_3485_, v_a_3486_);
lean_dec(v_a_3486_);
lean_dec_ref(v_a_3485_);
lean_dec(v_a_3484_);
lean_dec_ref(v_a_3483_);
return v_res_3488_;
}
}
lean_object* l_Lean_Meta_subst_x3f(lean_object* v_mvarId_3489_, lean_object* v_hFVarId_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; 
v___x_3496_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 7, 2);
lean_closure_set(v___x_3496_, 0, v_mvarId_3489_);
lean_closure_set(v___x_3496_, 1, v_hFVarId_3490_);
v___x_3497_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3496_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
return v___x_3497_;
}
}
LEAN_EXPORT void l_Lean_Meta_subst_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3489_ = stack[0].m_obj;
lean_object* v_hFVarId_3490_ = stack[1].m_obj;
lean_object* v_a_3491_ = stack[2].m_obj;
lean_object* v_a_3492_ = stack[3].m_obj;
lean_object* v_a_3493_ = stack[4].m_obj;
lean_object* v_a_3494_ = stack[5].m_obj;
lean_object* v_res_3498_;
v_res_3498_ = l_Lean_Meta_subst_x3f(v_mvarId_3489_, v_hFVarId_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
stack->m_obj
 = v_res_3498_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object* v_mvarId_3499_, lean_object* v_hFVarId_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_){
_start:
{
lean_object* v_res_3506_; 
v_res_3506_ = l_Lean_Meta_subst_x3f(v_mvarId_3499_, v_hFVarId_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
lean_dec(v_a_3504_);
lean_dec_ref(v_a_3503_);
lean_dec(v_a_3502_);
lean_dec_ref(v_a_3501_);
return v_res_3506_;
}
}
lean_object* l_Lean_Meta_substCore_x3f(lean_object* v_mvarId_3507_, lean_object* v_hFVarId_3508_, uint8_t v_symm_3509_, lean_object* v_fvarSubst_3510_, uint8_t v_clearH_3511_, uint8_t v_tryToSkip_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; 
v___x_3518_ = lean_box(v_symm_3509_);
v___x_3519_ = lean_box(v_clearH_3511_);
v___x_3520_ = lean_box(v_tryToSkip_3512_);
v___x_3521_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_3521_, 0, v_mvarId_3507_);
lean_closure_set(v___x_3521_, 1, v_hFVarId_3508_);
lean_closure_set(v___x_3521_, 2, v___x_3518_);
lean_closure_set(v___x_3521_, 3, v_fvarSubst_3510_);
lean_closure_set(v___x_3521_, 4, v___x_3519_);
lean_closure_set(v___x_3521_, 5, v___x_3520_);
v___x_3522_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3521_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
return v___x_3522_;
}
}
LEAN_EXPORT void l_Lean_Meta_substCore_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3507_ = stack[0].m_obj;
lean_object* v_hFVarId_3508_ = stack[1].m_obj;
uint8_t v_symm_3509_ = stack[2].m_num;
lean_object* v_fvarSubst_3510_ = stack[3].m_obj;
uint8_t v_clearH_3511_ = stack[4].m_num;
uint8_t v_tryToSkip_3512_ = stack[5].m_num;
lean_object* v_a_3513_ = stack[6].m_obj;
lean_object* v_a_3514_ = stack[7].m_obj;
lean_object* v_a_3515_ = stack[8].m_obj;
lean_object* v_a_3516_ = stack[9].m_obj;
lean_object* v_res_3523_;
v_res_3523_ = l_Lean_Meta_substCore_x3f(v_mvarId_3507_, v_hFVarId_3508_, v_symm_3509_, v_fvarSubst_3510_, v_clearH_3511_, v_tryToSkip_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
stack->m_obj
 = v_res_3523_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* v_mvarId_3524_, lean_object* v_hFVarId_3525_, lean_object* v_symm_3526_, lean_object* v_fvarSubst_3527_, lean_object* v_clearH_3528_, lean_object* v_tryToSkip_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_, lean_object* v_a_3533_, lean_object* v_a_3534_){
_start:
{
uint8_t v_symm_boxed_3535_; uint8_t v_clearH_boxed_3536_; uint8_t v_tryToSkip_boxed_3537_; lean_object* v_res_3538_; 
v_symm_boxed_3535_ = lean_unbox(v_symm_3526_);
v_clearH_boxed_3536_ = lean_unbox(v_clearH_3528_);
v_tryToSkip_boxed_3537_ = lean_unbox(v_tryToSkip_3529_);
v_res_3538_ = l_Lean_Meta_substCore_x3f(v_mvarId_3524_, v_hFVarId_3525_, v_symm_boxed_3535_, v_fvarSubst_3527_, v_clearH_boxed_3536_, v_tryToSkip_boxed_3537_, v_a_3530_, v_a_3531_, v_a_3532_, v_a_3533_);
lean_dec(v_a_3533_);
lean_dec_ref(v_a_3532_);
lean_dec(v_a_3531_);
lean_dec_ref(v_a_3530_);
return v_res_3538_;
}
}
lean_object* l_Lean_Meta_trySubstVar(lean_object* v_mvarId_3539_, lean_object* v_hFVarId_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_, lean_object* v_a_3543_, lean_object* v_a_3544_){
_start:
{
lean_object* v___x_3546_; 
lean_inc(v_mvarId_3539_);
v___x_3546_ = l_Lean_Meta_substVar_x3f(v_mvarId_3539_, v_hFVarId_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3558_; 
v_a_3547_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3558_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3558_ == 0)
{
v___x_3549_ = v___x_3546_;
v_isShared_3550_ = v_isSharedCheck_3558_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3546_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3558_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
if (lean_obj_tag(v_a_3547_) == 0)
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v_mvarId_3539_);
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_mvarId_3539_);
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
lean_object* v_val_3554_; lean_object* v___x_3556_; 
lean_dec(v_mvarId_3539_);
v_val_3554_ = lean_ctor_get(v_a_3547_, 0);
lean_inc(v_val_3554_);
lean_dec_ref_known(v_a_3547_, 1);
if (v_isShared_3550_ == 0)
{
lean_ctor_set(v___x_3549_, 0, v_val_3554_);
v___x_3556_ = v___x_3549_;
goto v_reusejp_3555_;
}
else
{
lean_object* v_reuseFailAlloc_3557_; 
v_reuseFailAlloc_3557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3557_, 0, v_val_3554_);
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
else
{
lean_object* v_a_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3566_; 
lean_dec(v_mvarId_3539_);
v_a_3559_ = lean_ctor_get(v___x_3546_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3546_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3561_ = v___x_3546_;
v_isShared_3562_ = v_isSharedCheck_3566_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_a_3559_);
lean_dec(v___x_3546_);
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
LEAN_EXPORT void l_Lean_Meta_trySubstVar_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3539_ = stack[0].m_obj;
lean_object* v_hFVarId_3540_ = stack[1].m_obj;
lean_object* v_a_3541_ = stack[2].m_obj;
lean_object* v_a_3542_ = stack[3].m_obj;
lean_object* v_a_3543_ = stack[4].m_obj;
lean_object* v_a_3544_ = stack[5].m_obj;
lean_object* v_res_3567_;
v_res_3567_ = l_Lean_Meta_trySubstVar(v_mvarId_3539_, v_hFVarId_3540_, v_a_3541_, v_a_3542_, v_a_3543_, v_a_3544_);
stack->m_obj
 = v_res_3567_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object* v_mvarId_3568_, lean_object* v_hFVarId_3569_, lean_object* v_a_3570_, lean_object* v_a_3571_, lean_object* v_a_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_Meta_trySubstVar(v_mvarId_3568_, v_hFVarId_3569_, v_a_3570_, v_a_3571_, v_a_3572_, v_a_3573_);
lean_dec(v_a_3573_);
lean_dec_ref(v_a_3572_);
lean_dec(v_a_3571_);
lean_dec_ref(v_a_3570_);
return v_res_3575_;
}
}
lean_object* l_Lean_Meta_trySubst(lean_object* v_mvarId_3576_, lean_object* v_hFVarId_3577_, lean_object* v_a_3578_, lean_object* v_a_3579_, lean_object* v_a_3580_, lean_object* v_a_3581_){
_start:
{
lean_object* v___x_3583_; 
lean_inc(v_mvarId_3576_);
v___x_3583_ = l_Lean_Meta_subst_x3f(v_mvarId_3576_, v_hFVarId_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3595_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3595_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3595_ == 0)
{
v___x_3586_ = v___x_3583_;
v_isShared_3587_ = v_isSharedCheck_3595_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3583_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3595_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
if (lean_obj_tag(v_a_3584_) == 0)
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v_mvarId_3576_);
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_mvarId_3576_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
else
{
lean_object* v_val_3591_; lean_object* v___x_3593_; 
lean_dec(v_mvarId_3576_);
v_val_3591_ = lean_ctor_get(v_a_3584_, 0);
lean_inc(v_val_3591_);
lean_dec_ref_known(v_a_3584_, 1);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v_val_3591_);
v___x_3593_ = v___x_3586_;
goto v_reusejp_3592_;
}
else
{
lean_object* v_reuseFailAlloc_3594_; 
v_reuseFailAlloc_3594_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3594_, 0, v_val_3591_);
v___x_3593_ = v_reuseFailAlloc_3594_;
goto v_reusejp_3592_;
}
v_reusejp_3592_:
{
return v___x_3593_;
}
}
}
}
else
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3603_; 
lean_dec(v_mvarId_3576_);
v_a_3596_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3603_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3603_ == 0)
{
v___x_3598_ = v___x_3583_;
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3583_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3603_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3601_; 
if (v_isShared_3599_ == 0)
{
v___x_3601_ = v___x_3598_;
goto v_reusejp_3600_;
}
else
{
lean_object* v_reuseFailAlloc_3602_; 
v_reuseFailAlloc_3602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3602_, 0, v_a_3596_);
v___x_3601_ = v_reuseFailAlloc_3602_;
goto v_reusejp_3600_;
}
v_reusejp_3600_:
{
return v___x_3601_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_trySubst_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3576_ = stack[0].m_obj;
lean_object* v_hFVarId_3577_ = stack[1].m_obj;
lean_object* v_a_3578_ = stack[2].m_obj;
lean_object* v_a_3579_ = stack[3].m_obj;
lean_object* v_a_3580_ = stack[4].m_obj;
lean_object* v_a_3581_ = stack[5].m_obj;
lean_object* v_res_3604_;
v_res_3604_ = l_Lean_Meta_trySubst(v_mvarId_3576_, v_hFVarId_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_);
stack->m_obj
 = v_res_3604_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object* v_mvarId_3605_, lean_object* v_hFVarId_3606_, lean_object* v_a_3607_, lean_object* v_a_3608_, lean_object* v_a_3609_, lean_object* v_a_3610_, lean_object* v_a_3611_){
_start:
{
lean_object* v_res_3612_; 
v_res_3612_ = l_Lean_Meta_trySubst(v_mvarId_3605_, v_hFVarId_3606_, v_a_3607_, v_a_3608_, v_a_3609_, v_a_3610_);
lean_dec(v_a_3610_);
lean_dec_ref(v_a_3609_);
lean_dec(v_a_3608_);
lean_dec_ref(v_a_3607_);
return v_res_3612_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_mvarId_3616_, lean_object* v_as_3617_, size_t v_sz_3618_, size_t v_i_3619_, lean_object* v_b_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_, lean_object* v___y_3624_){
_start:
{
uint8_t v___x_3626_; 
v___x_3626_ = lean_usize_dec_lt(v_i_3619_, v_sz_3618_);
if (v___x_3626_ == 0)
{
lean_object* v___x_3627_; 
lean_dec(v_mvarId_3616_);
v___x_3627_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3627_, 0, v_b_3620_);
return v___x_3627_;
}
else
{
lean_object* v_snd_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3681_; 
v_snd_3628_ = lean_ctor_get(v_b_3620_, 1);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_b_3620_);
if (v_isSharedCheck_3681_ == 0)
{
lean_object* v_unused_3682_; 
v_unused_3682_ = lean_ctor_get(v_b_3620_, 0);
lean_dec(v_unused_3682_);
v___x_3630_ = v_b_3620_;
v_isShared_3631_ = v_isSharedCheck_3681_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_snd_3628_);
lean_dec(v_b_3620_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3681_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v___x_3632_; lean_object* v_a_3634_; lean_object* v_a_3641_; 
v___x_3632_ = lean_box(0);
v_a_3641_ = lean_array_uget(v_as_3617_, v_i_3619_);
if (lean_obj_tag(v_a_3641_) == 0)
{
v_a_3634_ = v_snd_3628_;
goto v___jp_3633_;
}
else
{
lean_object* v_val_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3680_; 
v_val_3642_ = lean_ctor_get(v_a_3641_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_a_3641_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3644_ = v_a_3641_;
v_isShared_3645_ = v_isSharedCheck_3680_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_val_3642_);
lean_dec(v_a_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3680_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3649_; 
v___x_3646_ = lean_box(0);
v___x_3647_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3648_ = l_Lean_LocalDecl_fvarId(v_val_3642_);
lean_dec(v_val_3642_);
lean_inc(v_mvarId_3616_);
v___x_3649_ = l_Lean_Meta_subst_x3f(v_mvarId_3616_, v___x_3648_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3671_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3671_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3671_ == 0)
{
v___x_3652_ = v___x_3649_;
v_isShared_3653_ = v_isSharedCheck_3671_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_a_3650_);
lean_dec(v___x_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3671_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
if (lean_obj_tag(v_a_3650_) == 1)
{
lean_object* v___x_3655_; 
lean_del_object(v___x_3630_);
lean_dec(v_mvarId_3616_);
lean_inc_ref(v_a_3650_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set(v___x_3644_, 0, v_a_3650_);
v___x_3655_ = v___x_3644_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v_a_3650_);
v___x_3655_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3668_; 
v_isSharedCheck_3668_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_3668_ == 0)
{
lean_object* v_unused_3669_; 
v_unused_3669_ = lean_ctor_get(v_a_3650_, 0);
lean_dec(v_unused_3669_);
v___x_3657_ = v_a_3650_;
v_isShared_3658_ = v_isSharedCheck_3668_;
goto v_resetjp_3656_;
}
else
{
lean_dec(v_a_3650_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3668_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3655_);
lean_ctor_set(v___x_3659_, 1, v___x_3646_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set_tag(v___x_3657_, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3659_);
v___x_3661_ = v___x_3657_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3659_);
v___x_3661_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3665_; 
v___x_3662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3662_, 0, v___x_3661_);
v___x_3663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3663_, 0, v___x_3662_);
lean_ctor_set(v___x_3663_, 1, v_snd_3628_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3663_);
v___x_3665_ = v___x_3652_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3663_);
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
else
{
lean_del_object(v___x_3652_);
lean_dec(v_a_3650_);
lean_del_object(v___x_3644_);
lean_dec(v_snd_3628_);
v_a_3634_ = v___x_3647_;
goto v___jp_3633_;
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_del_object(v___x_3644_);
lean_del_object(v___x_3630_);
lean_dec(v_snd_3628_);
lean_dec(v_mvarId_3616_);
v_a_3672_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3649_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3649_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
}
v___jp_3633_:
{
lean_object* v___x_3636_; 
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 1, v_a_3634_);
lean_ctor_set(v___x_3630_, 0, v___x_3632_);
v___x_3636_ = v___x_3630_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3640_; 
v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3640_, 0, v___x_3632_);
lean_ctor_set(v_reuseFailAlloc_3640_, 1, v_a_3634_);
v___x_3636_ = v_reuseFailAlloc_3640_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
size_t v___x_3637_; size_t v___x_3638_; 
v___x_3637_ = ((size_t)1ULL);
v___x_3638_ = lean_usize_add(v_i_3619_, v___x_3637_);
v_i_3619_ = v___x_3638_;
v_b_3620_ = v___x_3636_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3616_ = stack[0].m_obj;
lean_object* v_as_3617_ = stack[1].m_obj;
size_t v_sz_3618_ = stack[2].m_num;
size_t v_i_3619_ = stack[3].m_num;
lean_object* v_b_3620_ = stack[4].m_obj;
lean_object* v___y_3621_ = stack[5].m_obj;
lean_object* v___y_3622_ = stack[6].m_obj;
lean_object* v___y_3623_ = stack[7].m_obj;
lean_object* v___y_3624_ = stack[8].m_obj;
lean_object* v_res_3683_;
v_res_3683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3616_, v_as_3617_, v_sz_3618_, v_i_3619_, v_b_3620_, v___y_3621_, v___y_3622_, v___y_3623_, v___y_3624_);
stack->m_obj
 = v_res_3683_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_mvarId_3684_, lean_object* v_as_3685_, lean_object* v_sz_3686_, lean_object* v_i_3687_, lean_object* v_b_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_){
_start:
{
size_t v_sz_boxed_3694_; size_t v_i_boxed_3695_; lean_object* v_res_3696_; 
v_sz_boxed_3694_ = lean_unbox_usize(v_sz_3686_);
lean_dec(v_sz_3686_);
v_i_boxed_3695_ = lean_unbox_usize(v_i_3687_);
lean_dec(v_i_3687_);
v_res_3696_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3684_, v_as_3685_, v_sz_boxed_3694_, v_i_boxed_3695_, v_b_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_);
lean_dec(v___y_3692_);
lean_dec_ref(v___y_3691_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec_ref(v_as_3685_);
return v_res_3696_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object* v_mvarId_3697_, lean_object* v_as_3698_, size_t v_sz_3699_, size_t v_i_3700_, lean_object* v_b_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_){
_start:
{
uint8_t v___x_3707_; 
v___x_3707_ = lean_usize_dec_lt(v_i_3700_, v_sz_3699_);
if (v___x_3707_ == 0)
{
lean_object* v___x_3708_; 
lean_dec(v_mvarId_3697_);
v___x_3708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3708_, 0, v_b_3701_);
return v___x_3708_;
}
else
{
lean_object* v_snd_3709_; lean_object* v___x_3711_; uint8_t v_isShared_3712_; uint8_t v_isSharedCheck_3762_; 
v_snd_3709_ = lean_ctor_get(v_b_3701_, 1);
v_isSharedCheck_3762_ = !lean_is_exclusive(v_b_3701_);
if (v_isSharedCheck_3762_ == 0)
{
lean_object* v_unused_3763_; 
v_unused_3763_ = lean_ctor_get(v_b_3701_, 0);
lean_dec(v_unused_3763_);
v___x_3711_ = v_b_3701_;
v_isShared_3712_ = v_isSharedCheck_3762_;
goto v_resetjp_3710_;
}
else
{
lean_inc(v_snd_3709_);
lean_dec(v_b_3701_);
v___x_3711_ = lean_box(0);
v_isShared_3712_ = v_isSharedCheck_3762_;
goto v_resetjp_3710_;
}
v_resetjp_3710_:
{
lean_object* v___x_3713_; lean_object* v_a_3715_; lean_object* v_a_3722_; 
v___x_3713_ = lean_box(0);
v_a_3722_ = lean_array_uget(v_as_3698_, v_i_3700_);
if (lean_obj_tag(v_a_3722_) == 0)
{
v_a_3715_ = v_snd_3709_;
goto v___jp_3714_;
}
else
{
lean_object* v_val_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3761_; 
v_val_3723_ = lean_ctor_get(v_a_3722_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v_a_3722_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3725_ = v_a_3722_;
v_isShared_3726_ = v_isSharedCheck_3761_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_val_3723_);
lean_dec(v_a_3722_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3761_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; lean_object* v___x_3730_; 
v___x_3727_ = lean_box(0);
v___x_3728_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3729_ = l_Lean_LocalDecl_fvarId(v_val_3723_);
lean_dec(v_val_3723_);
lean_inc(v_mvarId_3697_);
v___x_3730_ = l_Lean_Meta_subst_x3f(v_mvarId_3697_, v___x_3729_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
if (lean_obj_tag(v___x_3730_) == 0)
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3752_; 
v_a_3731_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3752_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3752_ == 0)
{
v___x_3733_ = v___x_3730_;
v_isShared_3734_ = v_isSharedCheck_3752_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3730_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3752_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
if (lean_obj_tag(v_a_3731_) == 1)
{
lean_object* v___x_3736_; 
lean_del_object(v___x_3711_);
lean_dec(v_mvarId_3697_);
lean_inc_ref(v_a_3731_);
if (v_isShared_3726_ == 0)
{
lean_ctor_set(v___x_3725_, 0, v_a_3731_);
v___x_3736_ = v___x_3725_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3751_; 
v_reuseFailAlloc_3751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3751_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3751_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
lean_object* v___x_3738_; uint8_t v_isShared_3739_; uint8_t v_isSharedCheck_3749_; 
v_isSharedCheck_3749_ = !lean_is_exclusive(v_a_3731_);
if (v_isSharedCheck_3749_ == 0)
{
lean_object* v_unused_3750_; 
v_unused_3750_ = lean_ctor_get(v_a_3731_, 0);
lean_dec(v_unused_3750_);
v___x_3738_ = v_a_3731_;
v_isShared_3739_ = v_isSharedCheck_3749_;
goto v_resetjp_3737_;
}
else
{
lean_dec(v_a_3731_);
v___x_3738_ = lean_box(0);
v_isShared_3739_ = v_isSharedCheck_3749_;
goto v_resetjp_3737_;
}
v_resetjp_3737_:
{
lean_object* v___x_3740_; lean_object* v___x_3742_; 
v___x_3740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3740_, 0, v___x_3736_);
lean_ctor_set(v___x_3740_, 1, v___x_3727_);
if (v_isShared_3739_ == 0)
{
lean_ctor_set_tag(v___x_3738_, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3740_);
v___x_3742_ = v___x_3738_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3740_);
v___x_3742_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3746_; 
v___x_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3742_);
v___x_3744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3744_, 0, v___x_3743_);
lean_ctor_set(v___x_3744_, 1, v_snd_3709_);
if (v_isShared_3734_ == 0)
{
lean_ctor_set(v___x_3733_, 0, v___x_3744_);
v___x_3746_ = v___x_3733_;
goto v_reusejp_3745_;
}
else
{
lean_object* v_reuseFailAlloc_3747_; 
v_reuseFailAlloc_3747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3747_, 0, v___x_3744_);
v___x_3746_ = v_reuseFailAlloc_3747_;
goto v_reusejp_3745_;
}
v_reusejp_3745_:
{
return v___x_3746_;
}
}
}
}
}
else
{
lean_del_object(v___x_3733_);
lean_dec(v_a_3731_);
lean_del_object(v___x_3725_);
lean_dec(v_snd_3709_);
v_a_3715_ = v___x_3728_;
goto v___jp_3714_;
}
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_del_object(v___x_3725_);
lean_del_object(v___x_3711_);
lean_dec(v_snd_3709_);
lean_dec(v_mvarId_3697_);
v_a_3753_ = lean_ctor_get(v___x_3730_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3730_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3730_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3730_);
v___x_3755_ = lean_box(0);
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
v_resetjp_3754_:
{
lean_object* v___x_3758_; 
if (v_isShared_3756_ == 0)
{
v___x_3758_ = v___x_3755_;
goto v_reusejp_3757_;
}
else
{
lean_object* v_reuseFailAlloc_3759_; 
v_reuseFailAlloc_3759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_a_3753_);
v___x_3758_ = v_reuseFailAlloc_3759_;
goto v_reusejp_3757_;
}
v_reusejp_3757_:
{
return v___x_3758_;
}
}
}
}
}
v___jp_3714_:
{
lean_object* v___x_3717_; 
if (v_isShared_3712_ == 0)
{
lean_ctor_set(v___x_3711_, 1, v_a_3715_);
lean_ctor_set(v___x_3711_, 0, v___x_3713_);
v___x_3717_ = v___x_3711_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3721_; 
v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3721_, 0, v___x_3713_);
lean_ctor_set(v_reuseFailAlloc_3721_, 1, v_a_3715_);
v___x_3717_ = v_reuseFailAlloc_3721_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
size_t v___x_3718_; size_t v___x_3719_; lean_object* v___x_3720_; 
v___x_3718_ = ((size_t)1ULL);
v___x_3719_ = lean_usize_add(v_i_3700_, v___x_3718_);
v___x_3720_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3697_, v_as_3698_, v_sz_3699_, v___x_3719_, v___x_3717_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
return v___x_3720_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3697_ = stack[0].m_obj;
lean_object* v_as_3698_ = stack[1].m_obj;
size_t v_sz_3699_ = stack[2].m_num;
size_t v_i_3700_ = stack[3].m_num;
lean_object* v_b_3701_ = stack[4].m_obj;
lean_object* v___y_3702_ = stack[5].m_obj;
lean_object* v___y_3703_ = stack[6].m_obj;
lean_object* v___y_3704_ = stack[7].m_obj;
lean_object* v___y_3705_ = stack[8].m_obj;
lean_object* v_res_3764_;
v_res_3764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3697_, v_as_3698_, v_sz_3699_, v_i_3700_, v_b_3701_, v___y_3702_, v___y_3703_, v___y_3704_, v___y_3705_);
stack->m_obj
 = v_res_3764_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_3765_, lean_object* v_as_3766_, lean_object* v_sz_3767_, lean_object* v_i_3768_, lean_object* v_b_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_, lean_object* v___y_3772_, lean_object* v___y_3773_, lean_object* v___y_3774_){
_start:
{
size_t v_sz_boxed_3775_; size_t v_i_boxed_3776_; lean_object* v_res_3777_; 
v_sz_boxed_3775_ = lean_unbox_usize(v_sz_3767_);
lean_dec(v_sz_3767_);
v_i_boxed_3776_ = lean_unbox_usize(v_i_3768_);
lean_dec(v_i_3768_);
v_res_3777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3765_, v_as_3766_, v_sz_boxed_3775_, v_i_boxed_3776_, v_b_3769_, v___y_3770_, v___y_3771_, v___y_3772_, v___y_3773_);
lean_dec(v___y_3773_);
lean_dec_ref(v___y_3772_);
lean_dec(v___y_3771_);
lean_dec_ref(v___y_3770_);
lean_dec_ref(v_as_3766_);
return v_res_3777_;
}
}
lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* v_init_3778_, lean_object* v_mvarId_3779_, lean_object* v_n_3780_, lean_object* v_b_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_, lean_object* v___y_3784_, lean_object* v___y_3785_){
_start:
{
if (lean_obj_tag(v_n_3780_) == 0)
{
lean_object* v_cs_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; size_t v_sz_3790_; size_t v___x_3791_; lean_object* v___x_3792_; 
v_cs_3787_ = lean_ctor_get(v_n_3780_, 0);
v___x_3788_ = lean_box(0);
v___x_3789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3788_);
lean_ctor_set(v___x_3789_, 1, v_b_3781_);
v_sz_3790_ = lean_array_size(v_cs_3787_);
v___x_3791_ = ((size_t)0ULL);
v___x_3792_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3778_, v_mvarId_3779_, v_cs_3787_, v_sz_3790_, v___x_3791_, v___x_3789_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
if (lean_obj_tag(v___x_3792_) == 0)
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3807_; 
v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3795_ = v___x_3792_;
v_isShared_3796_ = v_isSharedCheck_3807_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3792_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3807_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v_fst_3797_; 
v_fst_3797_ = lean_ctor_get(v_a_3793_, 0);
if (lean_obj_tag(v_fst_3797_) == 0)
{
lean_object* v_snd_3798_; lean_object* v___x_3799_; lean_object* v___x_3801_; 
v_snd_3798_ = lean_ctor_get(v_a_3793_, 1);
lean_inc(v_snd_3798_);
lean_dec(v_a_3793_);
v___x_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3799_, 0, v_snd_3798_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v___x_3799_);
v___x_3801_ = v___x_3795_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v___x_3799_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
else
{
lean_object* v_val_3803_; lean_object* v___x_3805_; 
lean_inc_ref(v_fst_3797_);
lean_dec(v_a_3793_);
v_val_3803_ = lean_ctor_get(v_fst_3797_, 0);
lean_inc(v_val_3803_);
lean_dec_ref_known(v_fst_3797_, 1);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v_val_3803_);
v___x_3805_ = v___x_3795_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_val_3803_);
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
else
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3815_; 
v_a_3808_ = lean_ctor_get(v___x_3792_, 0);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3792_);
if (v_isSharedCheck_3815_ == 0)
{
v___x_3810_ = v___x_3792_;
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3792_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3815_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
lean_object* v___x_3813_; 
if (v_isShared_3811_ == 0)
{
v___x_3813_ = v___x_3810_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v_a_3808_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
}
}
else
{
lean_object* v_vs_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; size_t v_sz_3819_; size_t v___x_3820_; lean_object* v___x_3821_; 
v_vs_3816_ = lean_ctor_get(v_n_3780_, 0);
v___x_3817_ = lean_box(0);
v___x_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3818_, 0, v___x_3817_);
lean_ctor_set(v___x_3818_, 1, v_b_3781_);
v_sz_3819_ = lean_array_size(v_vs_3816_);
v___x_3820_ = ((size_t)0ULL);
v___x_3821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3779_, v_vs_3816_, v_sz_3819_, v___x_3820_, v___x_3818_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3836_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3824_ = v___x_3821_;
v_isShared_3825_ = v_isSharedCheck_3836_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3821_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3836_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v_fst_3826_; 
v_fst_3826_ = lean_ctor_get(v_a_3822_, 0);
if (lean_obj_tag(v_fst_3826_) == 0)
{
lean_object* v_snd_3827_; lean_object* v___x_3828_; lean_object* v___x_3830_; 
v_snd_3827_ = lean_ctor_get(v_a_3822_, 1);
lean_inc(v_snd_3827_);
lean_dec(v_a_3822_);
v___x_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3828_, 0, v_snd_3827_);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v___x_3828_);
v___x_3830_ = v___x_3824_;
goto v_reusejp_3829_;
}
else
{
lean_object* v_reuseFailAlloc_3831_; 
v_reuseFailAlloc_3831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3831_, 0, v___x_3828_);
v___x_3830_ = v_reuseFailAlloc_3831_;
goto v_reusejp_3829_;
}
v_reusejp_3829_:
{
return v___x_3830_;
}
}
else
{
lean_object* v_val_3832_; lean_object* v___x_3834_; 
lean_inc_ref(v_fst_3826_);
lean_dec(v_a_3822_);
v_val_3832_ = lean_ctor_get(v_fst_3826_, 0);
lean_inc(v_val_3832_);
lean_dec_ref_known(v_fst_3826_, 1);
if (v_isShared_3825_ == 0)
{
lean_ctor_set(v___x_3824_, 0, v_val_3832_);
v___x_3834_ = v___x_3824_;
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
v_a_3837_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3821_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3821_);
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
}
LEAN_EXPORT void l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3778_ = stack[0].m_obj;
lean_object* v_mvarId_3779_ = stack[1].m_obj;
lean_object* v_n_3780_ = stack[2].m_obj;
lean_object* v_b_3781_ = stack[3].m_obj;
lean_object* v___y_3782_ = stack[4].m_obj;
lean_object* v___y_3783_ = stack[5].m_obj;
lean_object* v___y_3784_ = stack[6].m_obj;
lean_object* v___y_3785_ = stack[7].m_obj;
lean_object* v_res_3845_;
v_res_3845_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3778_, v_mvarId_3779_, v_n_3780_, v_b_3781_, v___y_3782_, v___y_3783_, v___y_3784_, v___y_3785_);
stack->m_obj
 = v_res_3845_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_init_3846_, lean_object* v_mvarId_3847_, lean_object* v_as_3848_, size_t v_sz_3849_, size_t v_i_3850_, lean_object* v_b_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_){
_start:
{
uint8_t v___x_3857_; 
v___x_3857_ = lean_usize_dec_lt(v_i_3850_, v_sz_3849_);
if (v___x_3857_ == 0)
{
lean_object* v___x_3858_; 
lean_dec(v_mvarId_3847_);
v___x_3858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3858_, 0, v_b_3851_);
return v___x_3858_;
}
else
{
lean_object* v_snd_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3893_; 
v_snd_3859_ = lean_ctor_get(v_b_3851_, 1);
v_isSharedCheck_3893_ = !lean_is_exclusive(v_b_3851_);
if (v_isSharedCheck_3893_ == 0)
{
lean_object* v_unused_3894_; 
v_unused_3894_ = lean_ctor_get(v_b_3851_, 0);
lean_dec(v_unused_3894_);
v___x_3861_ = v_b_3851_;
v_isShared_3862_ = v_isSharedCheck_3893_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_snd_3859_);
lean_dec(v_b_3851_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3893_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3863_; lean_object* v_a_3864_; lean_object* v___x_3865_; 
v___x_3863_ = lean_box(0);
v_a_3864_ = lean_array_uget_borrowed(v_as_3848_, v_i_3850_);
lean_inc(v_snd_3859_);
lean_inc(v_mvarId_3847_);
v___x_3865_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3846_, v_mvarId_3847_, v_a_3864_, v_snd_3859_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
if (lean_obj_tag(v___x_3865_) == 0)
{
lean_object* v_a_3866_; lean_object* v___x_3868_; uint8_t v_isShared_3869_; uint8_t v_isSharedCheck_3884_; 
v_a_3866_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3884_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3884_ == 0)
{
v___x_3868_ = v___x_3865_;
v_isShared_3869_ = v_isSharedCheck_3884_;
goto v_resetjp_3867_;
}
else
{
lean_inc(v_a_3866_);
lean_dec(v___x_3865_);
v___x_3868_ = lean_box(0);
v_isShared_3869_ = v_isSharedCheck_3884_;
goto v_resetjp_3867_;
}
v_resetjp_3867_:
{
if (lean_obj_tag(v_a_3866_) == 0)
{
lean_object* v___x_3870_; lean_object* v___x_3872_; 
lean_dec(v_mvarId_3847_);
v___x_3870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3870_, 0, v_a_3866_);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 0, v___x_3870_);
v___x_3872_ = v___x_3861_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3876_; 
v_reuseFailAlloc_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3876_, 0, v___x_3870_);
lean_ctor_set(v_reuseFailAlloc_3876_, 1, v_snd_3859_);
v___x_3872_ = v_reuseFailAlloc_3876_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
lean_object* v___x_3874_; 
if (v_isShared_3869_ == 0)
{
lean_ctor_set(v___x_3868_, 0, v___x_3872_);
v___x_3874_ = v___x_3868_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3875_; 
v_reuseFailAlloc_3875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3875_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3875_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
return v___x_3874_;
}
}
}
else
{
lean_object* v_a_3877_; lean_object* v___x_3879_; 
lean_del_object(v___x_3868_);
lean_dec(v_snd_3859_);
v_a_3877_ = lean_ctor_get(v_a_3866_, 0);
lean_inc(v_a_3877_);
lean_dec_ref_known(v_a_3866_, 1);
if (v_isShared_3862_ == 0)
{
lean_ctor_set(v___x_3861_, 1, v_a_3877_);
lean_ctor_set(v___x_3861_, 0, v___x_3863_);
v___x_3879_ = v___x_3861_;
goto v_reusejp_3878_;
}
else
{
lean_object* v_reuseFailAlloc_3883_; 
v_reuseFailAlloc_3883_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3883_, 0, v___x_3863_);
lean_ctor_set(v_reuseFailAlloc_3883_, 1, v_a_3877_);
v___x_3879_ = v_reuseFailAlloc_3883_;
goto v_reusejp_3878_;
}
v_reusejp_3878_:
{
size_t v___x_3880_; size_t v___x_3881_; 
v___x_3880_ = ((size_t)1ULL);
v___x_3881_ = lean_usize_add(v_i_3850_, v___x_3880_);
v_i_3850_ = v___x_3881_;
v_b_3851_ = v___x_3879_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_3892_; 
lean_del_object(v___x_3861_);
lean_dec(v_snd_3859_);
lean_dec(v_mvarId_3847_);
v_a_3885_ = lean_ctor_get(v___x_3865_, 0);
v_isSharedCheck_3892_ = !lean_is_exclusive(v___x_3865_);
if (v_isSharedCheck_3892_ == 0)
{
v___x_3887_ = v___x_3865_;
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_a_3885_);
lean_dec(v___x_3865_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_3892_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v___x_3890_; 
if (v_isShared_3888_ == 0)
{
v___x_3890_ = v___x_3887_;
goto v_reusejp_3889_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_a_3885_);
v___x_3890_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3889_;
}
v_reusejp_3889_:
{
return v___x_3890_;
}
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_init_3846_ = stack[0].m_obj;
lean_object* v_mvarId_3847_ = stack[1].m_obj;
lean_object* v_as_3848_ = stack[2].m_obj;
size_t v_sz_3849_ = stack[3].m_num;
size_t v_i_3850_ = stack[4].m_num;
lean_object* v_b_3851_ = stack[5].m_obj;
lean_object* v___y_3852_ = stack[6].m_obj;
lean_object* v___y_3853_ = stack[7].m_obj;
lean_object* v___y_3854_ = stack[8].m_obj;
lean_object* v___y_3855_ = stack[9].m_obj;
lean_object* v_res_3895_;
v_res_3895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3846_, v_mvarId_3847_, v_as_3848_, v_sz_3849_, v_i_3850_, v_b_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
stack->m_obj
 = v_res_3895_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3896_, lean_object* v_mvarId_3897_, lean_object* v_as_3898_, lean_object* v_sz_3899_, lean_object* v_i_3900_, lean_object* v_b_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_, lean_object* v___y_3906_){
_start:
{
size_t v_sz_boxed_3907_; size_t v_i_boxed_3908_; lean_object* v_res_3909_; 
v_sz_boxed_3907_ = lean_unbox_usize(v_sz_3899_);
lean_dec(v_sz_3899_);
v_i_boxed_3908_ = lean_unbox_usize(v_i_3900_);
lean_dec(v_i_3900_);
v_res_3909_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3896_, v_mvarId_3897_, v_as_3898_, v_sz_boxed_3907_, v_i_boxed_3908_, v_b_3901_, v___y_3902_, v___y_3903_, v___y_3904_, v___y_3905_);
lean_dec(v___y_3905_);
lean_dec_ref(v___y_3904_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec_ref(v_as_3898_);
lean_dec_ref(v_init_3896_);
return v_res_3909_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_init_3910_, lean_object* v_mvarId_3911_, lean_object* v_n_3912_, lean_object* v_b_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3910_, v_mvarId_3911_, v_n_3912_, v_b_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
lean_dec(v___y_3917_);
lean_dec_ref(v___y_3916_);
lean_dec(v___y_3915_);
lean_dec_ref(v___y_3914_);
lean_dec_ref(v_n_3912_);
lean_dec_ref(v_init_3910_);
return v_res_3919_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3923_, lean_object* v_as_3924_, size_t v_sz_3925_, size_t v_i_3926_, lean_object* v_b_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_){
_start:
{
uint8_t v___x_3933_; 
v___x_3933_ = lean_usize_dec_lt(v_i_3926_, v_sz_3925_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3934_; 
lean_dec(v_mvarId_3923_);
v___x_3934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3934_, 0, v_b_3927_);
return v___x_3934_;
}
else
{
lean_object* v_snd_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3987_; 
v_snd_3935_ = lean_ctor_get(v_b_3927_, 1);
v_isSharedCheck_3987_ = !lean_is_exclusive(v_b_3927_);
if (v_isSharedCheck_3987_ == 0)
{
lean_object* v_unused_3988_; 
v_unused_3988_ = lean_ctor_get(v_b_3927_, 0);
lean_dec(v_unused_3988_);
v___x_3937_ = v_b_3927_;
v_isShared_3938_ = v_isSharedCheck_3987_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_snd_3935_);
lean_dec(v_b_3927_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3987_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v_a_3941_; lean_object* v_a_3948_; 
v___x_3939_ = lean_box(0);
v_a_3948_ = lean_array_uget(v_as_3924_, v_i_3926_);
if (lean_obj_tag(v_a_3948_) == 0)
{
v_a_3941_ = v_snd_3935_;
goto v___jp_3940_;
}
else
{
lean_object* v_val_3949_; lean_object* v___x_3951_; uint8_t v_isShared_3952_; uint8_t v_isSharedCheck_3986_; 
v_val_3949_ = lean_ctor_get(v_a_3948_, 0);
v_isSharedCheck_3986_ = !lean_is_exclusive(v_a_3948_);
if (v_isSharedCheck_3986_ == 0)
{
v___x_3951_ = v_a_3948_;
v_isShared_3952_ = v_isSharedCheck_3986_;
goto v_resetjp_3950_;
}
else
{
lean_inc(v_val_3949_);
lean_dec(v_a_3948_);
v___x_3951_ = lean_box(0);
v_isShared_3952_ = v_isSharedCheck_3986_;
goto v_resetjp_3950_;
}
v_resetjp_3950_:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3953_ = lean_box(0);
v___x_3954_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v___x_3955_ = l_Lean_LocalDecl_fvarId(v_val_3949_);
lean_dec(v_val_3949_);
lean_inc(v_mvarId_3923_);
v___x_3956_ = l_Lean_Meta_subst_x3f(v_mvarId_3923_, v___x_3955_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
if (lean_obj_tag(v___x_3956_) == 0)
{
lean_object* v_a_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3977_; 
v_a_3957_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3959_ = v___x_3956_;
v_isShared_3960_ = v_isSharedCheck_3977_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_a_3957_);
lean_dec(v___x_3956_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3977_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
if (lean_obj_tag(v_a_3957_) == 1)
{
lean_object* v___x_3962_; 
lean_del_object(v___x_3937_);
lean_dec(v_mvarId_3923_);
lean_inc_ref(v_a_3957_);
if (v_isShared_3952_ == 0)
{
lean_ctor_set(v___x_3951_, 0, v_a_3957_);
v___x_3962_ = v___x_3951_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3957_);
v___x_3962_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
lean_object* v___x_3964_; uint8_t v_isShared_3965_; uint8_t v_isSharedCheck_3974_; 
v_isSharedCheck_3974_ = !lean_is_exclusive(v_a_3957_);
if (v_isSharedCheck_3974_ == 0)
{
lean_object* v_unused_3975_; 
v_unused_3975_ = lean_ctor_get(v_a_3957_, 0);
lean_dec(v_unused_3975_);
v___x_3964_ = v_a_3957_;
v_isShared_3965_ = v_isSharedCheck_3974_;
goto v_resetjp_3963_;
}
else
{
lean_dec(v_a_3957_);
v___x_3964_ = lean_box(0);
v_isShared_3965_ = v_isSharedCheck_3974_;
goto v_resetjp_3963_;
}
v_resetjp_3963_:
{
lean_object* v___x_3966_; lean_object* v___x_3968_; 
v___x_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3962_);
lean_ctor_set(v___x_3966_, 1, v___x_3953_);
if (v_isShared_3965_ == 0)
{
lean_ctor_set(v___x_3964_, 0, v___x_3966_);
v___x_3968_ = v___x_3964_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3973_; 
v_reuseFailAlloc_3973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3973_, 0, v___x_3966_);
v___x_3968_ = v_reuseFailAlloc_3973_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
lean_object* v___x_3969_; lean_object* v___x_3971_; 
v___x_3969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
lean_ctor_set(v___x_3969_, 1, v_snd_3935_);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 0, v___x_3969_);
v___x_3971_ = v___x_3959_;
goto v_reusejp_3970_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3969_);
v___x_3971_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3970_;
}
v_reusejp_3970_:
{
return v___x_3971_;
}
}
}
}
}
else
{
lean_del_object(v___x_3959_);
lean_dec(v_a_3957_);
lean_del_object(v___x_3951_);
lean_dec(v_snd_3935_);
v_a_3941_ = v___x_3954_;
goto v___jp_3940_;
}
}
}
else
{
lean_object* v_a_3978_; lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3985_; 
lean_del_object(v___x_3951_);
lean_del_object(v___x_3937_);
lean_dec(v_snd_3935_);
lean_dec(v_mvarId_3923_);
v_a_3978_ = lean_ctor_get(v___x_3956_, 0);
v_isSharedCheck_3985_ = !lean_is_exclusive(v___x_3956_);
if (v_isSharedCheck_3985_ == 0)
{
v___x_3980_ = v___x_3956_;
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
else
{
lean_inc(v_a_3978_);
lean_dec(v___x_3956_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3985_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3983_; 
if (v_isShared_3981_ == 0)
{
v___x_3983_ = v___x_3980_;
goto v_reusejp_3982_;
}
else
{
lean_object* v_reuseFailAlloc_3984_; 
v_reuseFailAlloc_3984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3984_, 0, v_a_3978_);
v___x_3983_ = v_reuseFailAlloc_3984_;
goto v_reusejp_3982_;
}
v_reusejp_3982_:
{
return v___x_3983_;
}
}
}
}
}
v___jp_3940_:
{
lean_object* v___x_3943_; 
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 1, v_a_3941_);
lean_ctor_set(v___x_3937_, 0, v___x_3939_);
v___x_3943_ = v___x_3937_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v_a_3941_);
v___x_3943_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
size_t v___x_3944_; size_t v___x_3945_; 
v___x_3944_ = ((size_t)1ULL);
v___x_3945_ = lean_usize_add(v_i_3926_, v___x_3944_);
v_i_3926_ = v___x_3945_;
v_b_3927_ = v___x_3943_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_3923_ = stack[0].m_obj;
lean_object* v_as_3924_ = stack[1].m_obj;
size_t v_sz_3925_ = stack[2].m_num;
size_t v_i_3926_ = stack[3].m_num;
lean_object* v_b_3927_ = stack[4].m_obj;
lean_object* v___y_3928_ = stack[5].m_obj;
lean_object* v___y_3929_ = stack[6].m_obj;
lean_object* v___y_3930_ = stack[7].m_obj;
lean_object* v___y_3931_ = stack[8].m_obj;
lean_object* v_res_3989_;
v_res_3989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3923_, v_as_3924_, v_sz_3925_, v_i_3926_, v_b_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
stack->m_obj
 = v_res_3989_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3990_, lean_object* v_as_3991_, lean_object* v_sz_3992_, lean_object* v_i_3993_, lean_object* v_b_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_){
_start:
{
size_t v_sz_boxed_4000_; size_t v_i_boxed_4001_; lean_object* v_res_4002_; 
v_sz_boxed_4000_ = lean_unbox_usize(v_sz_3992_);
lean_dec(v_sz_3992_);
v_i_boxed_4001_ = lean_unbox_usize(v_i_3993_);
lean_dec(v_i_3993_);
v_res_4002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3990_, v_as_3991_, v_sz_boxed_4000_, v_i_boxed_4001_, v_b_3994_, v___y_3995_, v___y_3996_, v___y_3997_, v___y_3998_);
lean_dec(v___y_3998_);
lean_dec_ref(v___y_3997_);
lean_dec(v___y_3996_);
lean_dec_ref(v___y_3995_);
lean_dec_ref(v_as_3991_);
return v_res_4002_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_4003_, lean_object* v_as_4004_, size_t v_sz_4005_, size_t v_i_4006_, lean_object* v_b_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
uint8_t v___x_4013_; 
v___x_4013_ = lean_usize_dec_lt(v_i_4006_, v_sz_4005_);
if (v___x_4013_ == 0)
{
lean_object* v___x_4014_; 
lean_dec(v_mvarId_4003_);
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v_b_4007_);
return v___x_4014_;
}
else
{
lean_object* v_snd_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4067_; 
v_snd_4015_ = lean_ctor_get(v_b_4007_, 1);
v_isSharedCheck_4067_ = !lean_is_exclusive(v_b_4007_);
if (v_isSharedCheck_4067_ == 0)
{
lean_object* v_unused_4068_; 
v_unused_4068_ = lean_ctor_get(v_b_4007_, 0);
lean_dec(v_unused_4068_);
v___x_4017_ = v_b_4007_;
v_isShared_4018_ = v_isSharedCheck_4067_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_snd_4015_);
lean_dec(v_b_4007_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4067_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4019_; lean_object* v_a_4021_; lean_object* v_a_4028_; 
v___x_4019_ = lean_box(0);
v_a_4028_ = lean_array_uget(v_as_4004_, v_i_4006_);
if (lean_obj_tag(v_a_4028_) == 0)
{
v_a_4021_ = v_snd_4015_;
goto v___jp_4020_;
}
else
{
lean_object* v_val_4029_; lean_object* v___x_4031_; uint8_t v_isShared_4032_; uint8_t v_isSharedCheck_4066_; 
v_val_4029_ = lean_ctor_get(v_a_4028_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v_a_4028_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4031_ = v_a_4028_;
v_isShared_4032_ = v_isSharedCheck_4066_;
goto v_resetjp_4030_;
}
else
{
lean_inc(v_val_4029_);
lean_dec(v_a_4028_);
v___x_4031_ = lean_box(0);
v_isShared_4032_ = v_isSharedCheck_4066_;
goto v_resetjp_4030_;
}
v_resetjp_4030_:
{
lean_object* v___x_4033_; lean_object* v___x_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v___x_4033_ = lean_box(0);
v___x_4034_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v___x_4035_ = l_Lean_LocalDecl_fvarId(v_val_4029_);
lean_dec(v_val_4029_);
lean_inc(v_mvarId_4003_);
v___x_4036_ = l_Lean_Meta_subst_x3f(v_mvarId_4003_, v___x_4035_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4057_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4039_ = v___x_4036_;
v_isShared_4040_ = v_isSharedCheck_4057_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4036_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4057_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
if (lean_obj_tag(v_a_4037_) == 1)
{
lean_object* v___x_4042_; 
lean_del_object(v___x_4017_);
lean_dec(v_mvarId_4003_);
lean_inc_ref(v_a_4037_);
if (v_isShared_4032_ == 0)
{
lean_ctor_set(v___x_4031_, 0, v_a_4037_);
v___x_4042_ = v___x_4031_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
lean_object* v___x_4044_; uint8_t v_isShared_4045_; uint8_t v_isSharedCheck_4054_; 
v_isSharedCheck_4054_ = !lean_is_exclusive(v_a_4037_);
if (v_isSharedCheck_4054_ == 0)
{
lean_object* v_unused_4055_; 
v_unused_4055_ = lean_ctor_get(v_a_4037_, 0);
lean_dec(v_unused_4055_);
v___x_4044_ = v_a_4037_;
v_isShared_4045_ = v_isSharedCheck_4054_;
goto v_resetjp_4043_;
}
else
{
lean_dec(v_a_4037_);
v___x_4044_ = lean_box(0);
v_isShared_4045_ = v_isSharedCheck_4054_;
goto v_resetjp_4043_;
}
v_resetjp_4043_:
{
lean_object* v___x_4046_; lean_object* v___x_4048_; 
v___x_4046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4042_);
lean_ctor_set(v___x_4046_, 1, v___x_4033_);
if (v_isShared_4045_ == 0)
{
lean_ctor_set(v___x_4044_, 0, v___x_4046_);
v___x_4048_ = v___x_4044_;
goto v_reusejp_4047_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v___x_4046_);
v___x_4048_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4047_;
}
v_reusejp_4047_:
{
lean_object* v___x_4049_; lean_object* v___x_4051_; 
v___x_4049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
lean_ctor_set(v___x_4049_, 1, v_snd_4015_);
if (v_isShared_4040_ == 0)
{
lean_ctor_set(v___x_4039_, 0, v___x_4049_);
v___x_4051_ = v___x_4039_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v___x_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
}
}
}
else
{
lean_del_object(v___x_4039_);
lean_dec(v_a_4037_);
lean_del_object(v___x_4031_);
lean_dec(v_snd_4015_);
v_a_4021_ = v___x_4034_;
goto v___jp_4020_;
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
lean_del_object(v___x_4031_);
lean_del_object(v___x_4017_);
lean_dec(v_snd_4015_);
lean_dec(v_mvarId_4003_);
v_a_4058_ = lean_ctor_get(v___x_4036_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4036_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4036_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4036_);
v___x_4060_ = lean_box(0);
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
v_resetjp_4059_:
{
lean_object* v___x_4063_; 
if (v_isShared_4061_ == 0)
{
v___x_4063_ = v___x_4060_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_a_4058_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
return v___x_4063_;
}
}
}
}
}
v___jp_4020_:
{
lean_object* v___x_4023_; 
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 1, v_a_4021_);
lean_ctor_set(v___x_4017_, 0, v___x_4019_);
v___x_4023_ = v___x_4017_;
goto v_reusejp_4022_;
}
else
{
lean_object* v_reuseFailAlloc_4027_; 
v_reuseFailAlloc_4027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4027_, 0, v___x_4019_);
lean_ctor_set(v_reuseFailAlloc_4027_, 1, v_a_4021_);
v___x_4023_ = v_reuseFailAlloc_4027_;
goto v_reusejp_4022_;
}
v_reusejp_4022_:
{
size_t v___x_4024_; size_t v___x_4025_; lean_object* v___x_4026_; 
v___x_4024_ = ((size_t)1ULL);
v___x_4025_ = lean_usize_add(v_i_4006_, v___x_4024_);
v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_4003_, v_as_4004_, v_sz_4005_, v___x_4025_, v___x_4023_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
return v___x_4026_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4003_ = stack[0].m_obj;
lean_object* v_as_4004_ = stack[1].m_obj;
size_t v_sz_4005_ = stack[2].m_num;
size_t v_i_4006_ = stack[3].m_num;
lean_object* v_b_4007_ = stack[4].m_obj;
lean_object* v___y_4008_ = stack[5].m_obj;
lean_object* v___y_4009_ = stack[6].m_obj;
lean_object* v___y_4010_ = stack[7].m_obj;
lean_object* v___y_4011_ = stack[8].m_obj;
lean_object* v_res_4069_;
v_res_4069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4003_, v_as_4004_, v_sz_4005_, v_i_4006_, v_b_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
stack->m_obj
 = v_res_4069_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_4070_, lean_object* v_as_4071_, lean_object* v_sz_4072_, lean_object* v_i_4073_, lean_object* v_b_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_){
_start:
{
size_t v_sz_boxed_4080_; size_t v_i_boxed_4081_; lean_object* v_res_4082_; 
v_sz_boxed_4080_ = lean_unbox_usize(v_sz_4072_);
lean_dec(v_sz_4072_);
v_i_boxed_4081_ = lean_unbox_usize(v_i_4073_);
lean_dec(v_i_4073_);
v_res_4082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4070_, v_as_4071_, v_sz_boxed_4080_, v_i_boxed_4081_, v_b_4074_, v___y_4075_, v___y_4076_, v___y_4077_, v___y_4078_);
lean_dec(v___y_4078_);
lean_dec_ref(v___y_4077_);
lean_dec(v___y_4076_);
lean_dec_ref(v___y_4075_);
lean_dec_ref(v_as_4071_);
return v_res_4082_;
}
}
lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4083_, lean_object* v_t_4084_, lean_object* v_init_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v_root_4091_; lean_object* v_tail_4092_; lean_object* v___x_4093_; 
v_root_4091_ = lean_ctor_get(v_t_4084_, 0);
v_tail_4092_ = lean_ctor_get(v_t_4084_, 1);
lean_inc(v_mvarId_4083_);
lean_inc_ref(v_init_4085_);
v___x_4093_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_4085_, v_mvarId_4083_, v_root_4091_, v_init_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec_ref(v_init_4085_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4130_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4130_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4130_ == 0)
{
v___x_4096_ = v___x_4093_;
v_isShared_4097_ = v_isSharedCheck_4130_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_a_4094_);
lean_dec(v___x_4093_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4130_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
if (lean_obj_tag(v_a_4094_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4100_; 
lean_dec(v_mvarId_4083_);
v_a_4098_ = lean_ctor_get(v_a_4094_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v_a_4094_, 1);
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v_a_4098_);
v___x_4100_ = v___x_4096_;
goto v_reusejp_4099_;
}
else
{
lean_object* v_reuseFailAlloc_4101_; 
v_reuseFailAlloc_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4098_);
v___x_4100_ = v_reuseFailAlloc_4101_;
goto v_reusejp_4099_;
}
v_reusejp_4099_:
{
return v___x_4100_;
}
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; size_t v_sz_4105_; size_t v___x_4106_; lean_object* v___x_4107_; 
lean_del_object(v___x_4096_);
v_a_4102_ = lean_ctor_get(v_a_4094_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v_a_4094_, 1);
v___x_4103_ = lean_box(0);
v___x_4104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4103_);
lean_ctor_set(v___x_4104_, 1, v_a_4102_);
v_sz_4105_ = lean_array_size(v_tail_4092_);
v___x_4106_ = ((size_t)0ULL);
v___x_4107_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4083_, v_tail_4092_, v_sz_4105_, v___x_4106_, v___x_4104_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
if (lean_obj_tag(v___x_4107_) == 0)
{
lean_object* v_a_4108_; lean_object* v___x_4110_; uint8_t v_isShared_4111_; uint8_t v_isSharedCheck_4121_; 
v_a_4108_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4121_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4121_ == 0)
{
v___x_4110_ = v___x_4107_;
v_isShared_4111_ = v_isSharedCheck_4121_;
goto v_resetjp_4109_;
}
else
{
lean_inc(v_a_4108_);
lean_dec(v___x_4107_);
v___x_4110_ = lean_box(0);
v_isShared_4111_ = v_isSharedCheck_4121_;
goto v_resetjp_4109_;
}
v_resetjp_4109_:
{
lean_object* v_fst_4112_; 
v_fst_4112_ = lean_ctor_get(v_a_4108_, 0);
if (lean_obj_tag(v_fst_4112_) == 0)
{
lean_object* v_snd_4113_; lean_object* v___x_4115_; 
v_snd_4113_ = lean_ctor_get(v_a_4108_, 1);
lean_inc(v_snd_4113_);
lean_dec(v_a_4108_);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v_snd_4113_);
v___x_4115_ = v___x_4110_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_snd_4113_);
v___x_4115_ = v_reuseFailAlloc_4116_;
goto v_reusejp_4114_;
}
v_reusejp_4114_:
{
return v___x_4115_;
}
}
else
{
lean_object* v_val_4117_; lean_object* v___x_4119_; 
lean_inc_ref(v_fst_4112_);
lean_dec(v_a_4108_);
v_val_4117_ = lean_ctor_get(v_fst_4112_, 0);
lean_inc(v_val_4117_);
lean_dec_ref_known(v_fst_4112_, 1);
if (v_isShared_4111_ == 0)
{
lean_ctor_set(v___x_4110_, 0, v_val_4117_);
v___x_4119_ = v___x_4110_;
goto v_reusejp_4118_;
}
else
{
lean_object* v_reuseFailAlloc_4120_; 
v_reuseFailAlloc_4120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4120_, 0, v_val_4117_);
v___x_4119_ = v_reuseFailAlloc_4120_;
goto v_reusejp_4118_;
}
v_reusejp_4118_:
{
return v___x_4119_;
}
}
}
}
else
{
lean_object* v_a_4122_; lean_object* v___x_4124_; uint8_t v_isShared_4125_; uint8_t v_isSharedCheck_4129_; 
v_a_4122_ = lean_ctor_get(v___x_4107_, 0);
v_isSharedCheck_4129_ = !lean_is_exclusive(v___x_4107_);
if (v_isSharedCheck_4129_ == 0)
{
v___x_4124_ = v___x_4107_;
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
else
{
lean_inc(v_a_4122_);
lean_dec(v___x_4107_);
v___x_4124_ = lean_box(0);
v_isShared_4125_ = v_isSharedCheck_4129_;
goto v_resetjp_4123_;
}
v_resetjp_4123_:
{
lean_object* v___x_4127_; 
if (v_isShared_4125_ == 0)
{
v___x_4127_ = v___x_4124_;
goto v_reusejp_4126_;
}
else
{
lean_object* v_reuseFailAlloc_4128_; 
v_reuseFailAlloc_4128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4128_, 0, v_a_4122_);
v___x_4127_ = v_reuseFailAlloc_4128_;
goto v_reusejp_4126_;
}
v_reusejp_4126_:
{
return v___x_4127_;
}
}
}
}
}
}
else
{
lean_object* v_a_4131_; lean_object* v___x_4133_; uint8_t v_isShared_4134_; uint8_t v_isSharedCheck_4138_; 
lean_dec(v_mvarId_4083_);
v_a_4131_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4138_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4138_ == 0)
{
v___x_4133_ = v___x_4093_;
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
else
{
lean_inc(v_a_4131_);
lean_dec(v___x_4093_);
v___x_4133_ = lean_box(0);
v_isShared_4134_ = v_isSharedCheck_4138_;
goto v_resetjp_4132_;
}
v_resetjp_4132_:
{
lean_object* v___x_4136_; 
if (v_isShared_4134_ == 0)
{
v___x_4136_ = v___x_4133_;
goto v_reusejp_4135_;
}
else
{
lean_object* v_reuseFailAlloc_4137_; 
v_reuseFailAlloc_4137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4137_, 0, v_a_4131_);
v___x_4136_ = v_reuseFailAlloc_4137_;
goto v_reusejp_4135_;
}
v_reusejp_4135_:
{
return v___x_4136_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4083_ = stack[0].m_obj;
lean_object* v_t_4084_ = stack[1].m_obj;
lean_object* v_init_4085_ = stack[2].m_obj;
lean_object* v___y_4086_ = stack[3].m_obj;
lean_object* v___y_4087_ = stack[4].m_obj;
lean_object* v___y_4088_ = stack[5].m_obj;
lean_object* v___y_4089_ = stack[6].m_obj;
lean_object* v_res_4139_;
v_res_4139_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4083_, v_t_4084_, v_init_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
stack->m_obj
 = v_res_4139_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4140_, lean_object* v_t_4141_, lean_object* v_init_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4140_, v_t_4141_, v_init_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
lean_dec_ref(v_t_4141_);
return v_res_4148_;
}
}
lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_){
_start:
{
lean_object* v_lctx_4158_; lean_object* v_decls_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; 
v_lctx_4158_ = lean_ctor_get(v___y_4153_, 2);
v_decls_4159_ = lean_ctor_get(v_lctx_4158_, 1);
v___x_4160_ = lean_box(0);
v___x_4161_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4162_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4152_, v_decls_4159_, v___x_4161_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
if (lean_obj_tag(v___x_4162_) == 0)
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4175_; 
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4165_ = v___x_4162_;
v_isShared_4166_ = v_isSharedCheck_4175_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4162_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4175_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v_fst_4167_; 
v_fst_4167_ = lean_ctor_get(v_a_4163_, 0);
lean_inc(v_fst_4167_);
lean_dec(v_a_4163_);
if (lean_obj_tag(v_fst_4167_) == 0)
{
lean_object* v___x_4169_; 
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4160_);
v___x_4169_ = v___x_4165_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4160_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
else
{
lean_object* v_val_4171_; lean_object* v___x_4173_; 
v_val_4171_ = lean_ctor_get(v_fst_4167_, 0);
lean_inc(v_val_4171_);
lean_dec_ref_known(v_fst_4167_, 1);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v_val_4171_);
v___x_4173_ = v___x_4165_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_val_4171_);
v___x_4173_ = v_reuseFailAlloc_4174_;
goto v_reusejp_4172_;
}
v_reusejp_4172_:
{
return v___x_4173_;
}
}
}
}
else
{
lean_object* v_a_4176_; lean_object* v___x_4178_; uint8_t v_isShared_4179_; uint8_t v_isSharedCheck_4183_; 
v_a_4176_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4162_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4162_);
v___x_4178_ = lean_box(0);
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
v_resetjp_4177_:
{
lean_object* v___x_4181_; 
if (v_isShared_4179_ == 0)
{
v___x_4181_ = v___x_4178_;
goto v_reusejp_4180_;
}
else
{
lean_object* v_reuseFailAlloc_4182_; 
v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
v___x_4181_ = v_reuseFailAlloc_4182_;
goto v_reusejp_4180_;
}
v_reusejp_4180_:
{
return v___x_4181_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_substSomeVar_x3f___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4152_ = stack[0].m_obj;
lean_object* v___y_4153_ = stack[1].m_obj;
lean_object* v___y_4154_ = stack[2].m_obj;
lean_object* v___y_4155_ = stack[3].m_obj;
lean_object* v___y_4156_ = stack[4].m_obj;
lean_object* v_res_4184_;
v_res_4184_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4152_, v___y_4153_, v___y_4154_, v___y_4155_, v___y_4156_);
stack->m_obj
 = v_res_4184_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_){
_start:
{
lean_object* v_res_4191_; 
v_res_4191_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4185_, v___y_4186_, v___y_4187_, v___y_4188_, v___y_4189_);
lean_dec(v___y_4189_);
lean_dec_ref(v___y_4188_);
lean_dec(v___y_4187_);
lean_dec_ref(v___y_4186_);
return v_res_4191_;
}
}
lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4192_, lean_object* v_a_4193_, lean_object* v_a_4194_, lean_object* v_a_4195_, lean_object* v_a_4196_){
_start:
{
lean_object* v___f_4198_; lean_object* v___x_4199_; 
lean_inc(v_mvarId_4192_);
v___f_4198_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4198_, 0, v_mvarId_4192_);
v___x_4199_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_4192_, v___f_4198_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_);
return v___x_4199_;
}
}
LEAN_EXPORT void l_Lean_Meta_substSomeVar_x3f_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4192_ = stack[0].m_obj;
lean_object* v_a_4193_ = stack[1].m_obj;
lean_object* v_a_4194_ = stack[2].m_obj;
lean_object* v_a_4195_ = stack[3].m_obj;
lean_object* v_a_4196_ = stack[4].m_obj;
lean_object* v_res_4200_;
v_res_4200_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_);
stack->m_obj
 = v_res_4200_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4201_, lean_object* v_a_4202_, lean_object* v_a_4203_, lean_object* v_a_4204_, lean_object* v_a_4205_, lean_object* v_a_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4201_, v_a_4202_, v_a_4203_, v_a_4204_, v_a_4205_);
lean_dec(v_a_4205_);
lean_dec_ref(v_a_4204_);
lean_dec(v_a_4203_);
lean_dec_ref(v_a_4202_);
return v_res_4207_;
}
}
lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4208_, lean_object* v_a_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_){
_start:
{
lean_object* v___x_4214_; 
lean_inc(v_mvarId_4208_);
v___x_4214_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
if (lean_obj_tag(v___x_4214_) == 0)
{
lean_object* v_a_4215_; lean_object* v___x_4217_; uint8_t v_isShared_4218_; uint8_t v_isSharedCheck_4224_; 
v_a_4215_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4217_ = v___x_4214_;
v_isShared_4218_ = v_isSharedCheck_4224_;
goto v_resetjp_4216_;
}
else
{
lean_inc(v_a_4215_);
lean_dec(v___x_4214_);
v___x_4217_ = lean_box(0);
v_isShared_4218_ = v_isSharedCheck_4224_;
goto v_resetjp_4216_;
}
v_resetjp_4216_:
{
if (lean_obj_tag(v_a_4215_) == 1)
{
lean_object* v_val_4219_; 
lean_del_object(v___x_4217_);
lean_dec(v_mvarId_4208_);
v_val_4219_ = lean_ctor_get(v_a_4215_, 0);
lean_inc(v_val_4219_);
lean_dec_ref_known(v_a_4215_, 1);
v_mvarId_4208_ = v_val_4219_;
goto _start;
}
else
{
lean_object* v___x_4222_; 
lean_dec(v_a_4215_);
if (v_isShared_4218_ == 0)
{
lean_ctor_set(v___x_4217_, 0, v_mvarId_4208_);
v___x_4222_ = v___x_4217_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_mvarId_4208_);
v___x_4222_ = v_reuseFailAlloc_4223_;
goto v_reusejp_4221_;
}
v_reusejp_4221_:
{
return v___x_4222_;
}
}
}
}
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
lean_dec(v_mvarId_4208_);
v_a_4225_ = lean_ctor_get(v___x_4214_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4214_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4214_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4214_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_substVars_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_4208_ = stack[0].m_obj;
lean_object* v_a_4209_ = stack[1].m_obj;
lean_object* v_a_4210_ = stack[2].m_obj;
lean_object* v_a_4211_ = stack[3].m_obj;
lean_object* v_a_4212_ = stack[4].m_obj;
lean_object* v_res_4233_;
v_res_4233_ = l_Lean_Meta_substVars(v_mvarId_4208_, v_a_4209_, v_a_4210_, v_a_4211_, v_a_4212_);
stack->m_obj
 = v_res_4233_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4234_, lean_object* v_a_4235_, lean_object* v_a_4236_, lean_object* v_a_4237_, lean_object* v_a_4238_, lean_object* v_a_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l_Lean_Meta_substVars(v_mvarId_4234_, v_a_4235_, v_a_4236_, v_a_4237_, v_a_4238_);
lean_dec(v_a_4238_);
lean_dec_ref(v_a_4237_);
lean_dec(v_a_4236_);
lean_dec_ref(v_a_4235_);
return v_res_4240_;
}
}
lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; lean_object* v___x_4306_; 
v___x_4303_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_4304_ = 0;
v___x_4305_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4306_ = l_Lean_registerTraceClass(v___x_4303_, v___x_4304_, v___x_4305_);
return v___x_4306_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_4307_;
v_res_4307_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
stack->m_obj
 = v_res_4307_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4308_){
_start:
{
lean_object* v_res_4309_; 
v_res_4309_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4309_;
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
