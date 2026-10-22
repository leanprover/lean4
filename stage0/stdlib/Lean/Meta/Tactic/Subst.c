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
lean_object* v___f_130_; lean_object* v___x_24700__overap_131_; lean_object* v___x_132_; 
v___f_130_ = ((lean_object*)(l_panic___at___00Lean_Meta_substCore_spec__6___closed__0));
v___x_24700__overap_131_ = lean_panic_fn_borrowed(v___f_130_, v_msg_124_);
lean_inc(v___y_128_);
lean_inc_ref(v___y_127_);
lean_inc(v___y_126_);
lean_inc_ref(v___y_125_);
v___x_132_ = lean_apply_5(v___x_24700__overap_131_, v___y_125_, v___y_126_, v___y_127_, v___y_128_, lean_box(0));
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
uint8_t v___x_27151__boxed_222_; uint8_t v___x_27152__boxed_223_; lean_object* v_res_224_; 
v___x_27151__boxed_222_ = lean_unbox(v___x_214_);
v___x_27152__boxed_223_ = lean_unbox(v___x_215_);
v_res_224_ = l_Lean_Meta_substCore___lam__0(v_type_210_, v___x_211_, v___x_212_, v___x_213_, v___x_27151__boxed_222_, v___x_27152__boxed_223_, v_hAux_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
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
size_t v_x_27272__boxed_364_; size_t v_x_27273__boxed_365_; lean_object* v_res_366_; 
v_x_27272__boxed_364_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_x_27273__boxed_365_ = lean_unbox_usize(v_x_361_);
lean_dec(v_x_361_);
v_res_366_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_359_, v_x_27272__boxed_364_, v_x_27273__boxed_365_, v_x_362_, v_x_363_);
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
lean_object* v___x_378_; lean_object* v_mctx_379_; lean_object* v_cache_380_; lean_object* v_zetaDeltaFVarIds_381_; lean_object* v_postponed_382_; lean_object* v_diag_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_412_; 
v___x_378_ = lean_st_ref_take(v___y_376_);
v_mctx_379_ = lean_ctor_get(v___x_378_, 0);
v_cache_380_ = lean_ctor_get(v___x_378_, 1);
v_zetaDeltaFVarIds_381_ = lean_ctor_get(v___x_378_, 2);
v_postponed_382_ = lean_ctor_get(v___x_378_, 3);
v_diag_383_ = lean_ctor_get(v___x_378_, 4);
v_isSharedCheck_412_ = !lean_is_exclusive(v___x_378_);
if (v_isSharedCheck_412_ == 0)
{
v___x_385_ = v___x_378_;
v_isShared_386_ = v_isSharedCheck_412_;
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
v_isShared_386_ = v_isSharedCheck_412_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v_depth_387_; lean_object* v_levelAssignDepth_388_; lean_object* v_lmvarCounter_389_; lean_object* v_mvarCounter_390_; lean_object* v_lDecls_391_; lean_object* v_decls_392_; lean_object* v_userNames_393_; lean_object* v_lAssignment_394_; lean_object* v_eAssignment_395_; lean_object* v_dAssignment_396_; lean_object* v_synthNormMemo_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_411_; 
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
v_synthNormMemo_397_ = lean_ctor_get(v_mctx_379_, 10);
v_isSharedCheck_411_ = !lean_is_exclusive(v_mctx_379_);
if (v_isSharedCheck_411_ == 0)
{
v___x_399_ = v_mctx_379_;
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_synthNormMemo_397_);
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
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_401_ = lean_box(0);
v___x_402_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5___redArg(v_eAssignment_395_, v_mvarId_374_, v_val_375_);
if (v_isShared_400_ == 0)
{
lean_ctor_set(v___x_399_, 8, v___x_402_);
v___x_404_ = v___x_399_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_410_; 
v_reuseFailAlloc_410_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_410_, 0, v_depth_387_);
lean_ctor_set(v_reuseFailAlloc_410_, 1, v_levelAssignDepth_388_);
lean_ctor_set(v_reuseFailAlloc_410_, 2, v_lmvarCounter_389_);
lean_ctor_set(v_reuseFailAlloc_410_, 3, v_mvarCounter_390_);
lean_ctor_set(v_reuseFailAlloc_410_, 4, v_lDecls_391_);
lean_ctor_set(v_reuseFailAlloc_410_, 5, v_decls_392_);
lean_ctor_set(v_reuseFailAlloc_410_, 6, v_userNames_393_);
lean_ctor_set(v_reuseFailAlloc_410_, 7, v_lAssignment_394_);
lean_ctor_set(v_reuseFailAlloc_410_, 8, v___x_402_);
lean_ctor_set(v_reuseFailAlloc_410_, 9, v_dAssignment_396_);
lean_ctor_set(v_reuseFailAlloc_410_, 10, v_synthNormMemo_397_);
v___x_404_ = v_reuseFailAlloc_410_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
lean_object* v___x_406_; 
if (v_isShared_386_ == 0)
{
lean_ctor_set(v___x_385_, 0, v___x_404_);
v___x_406_ = v___x_385_;
goto v_reusejp_405_;
}
else
{
lean_object* v_reuseFailAlloc_409_; 
v_reuseFailAlloc_409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_409_, 0, v___x_404_);
lean_ctor_set(v_reuseFailAlloc_409_, 1, v_cache_380_);
lean_ctor_set(v_reuseFailAlloc_409_, 2, v_zetaDeltaFVarIds_381_);
lean_ctor_set(v_reuseFailAlloc_409_, 3, v_postponed_382_);
lean_ctor_set(v_reuseFailAlloc_409_, 4, v_diag_383_);
v___x_406_ = v_reuseFailAlloc_409_;
goto v_reusejp_405_;
}
v_reusejp_405_:
{
lean_object* v___x_407_; lean_object* v___x_408_; 
v___x_407_ = lean_st_ref_put(v___y_376_, v___x_406_);
v___x_408_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_408_, 0, v___x_401_);
return v___x_408_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg___boxed(lean_object* v_mvarId_413_, lean_object* v_val_414_, lean_object* v___y_415_, lean_object* v___y_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_mvarId_413_, v_val_414_, v___y_415_);
lean_dec(v___y_415_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(lean_object* v_fst_418_, lean_object* v_fst_419_, lean_object* v_n_420_, lean_object* v_i_421_, lean_object* v_a_422_){
_start:
{
lean_object* v_zero_424_; uint8_t v_isZero_425_; 
v_zero_424_ = lean_unsigned_to_nat(0u);
v_isZero_425_ = lean_nat_dec_eq(v_i_421_, v_zero_424_);
if (v_isZero_425_ == 1)
{
lean_object* v___x_426_; 
lean_dec(v_i_421_);
v___x_426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_426_, 0, v_a_422_);
return v___x_426_;
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v_one_429_; lean_object* v_n_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_427_ = lean_unsigned_to_nat(2u);
v___x_428_ = lean_box(0);
v_one_429_ = lean_unsigned_to_nat(1u);
v_n_430_ = lean_nat_sub(v_i_421_, v_one_429_);
lean_dec(v_i_421_);
v___x_431_ = lean_nat_sub(v_n_420_, v_n_430_);
v___x_432_ = lean_nat_sub(v___x_431_, v_one_429_);
lean_dec(v___x_431_);
v___x_433_ = lean_nat_add(v___x_432_, v___x_427_);
v___x_434_ = lean_array_get_borrowed(v___x_428_, v_fst_418_, v___x_433_);
lean_dec(v___x_433_);
v___x_435_ = lean_array_fget_borrowed(v_fst_419_, v___x_432_);
lean_dec(v___x_432_);
lean_inc(v___x_435_);
v___x_436_ = l_Lean_mkFVar(v___x_435_);
lean_inc(v___x_434_);
v___x_437_ = l_Lean_Meta_FVarSubst_insert(v_a_422_, v___x_434_, v___x_436_);
v_i_421_ = v_n_430_;
v_a_422_ = v___x_437_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg___boxed(lean_object* v_fst_439_, lean_object* v_fst_440_, lean_object* v_n_441_, lean_object* v_i_442_, lean_object* v_a_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_439_, v_fst_440_, v_n_441_, v_i_442_, v_a_443_);
lean_dec(v_n_441_);
lean_dec_ref(v_fst_440_);
lean_dec_ref(v_fst_439_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0(lean_object* v_k_446_, lean_object* v_b_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; 
lean_inc(v___y_451_);
lean_inc_ref(v___y_450_);
lean_inc(v___y_449_);
lean_inc_ref(v___y_448_);
v___x_453_ = lean_apply_6(v_k_446_, v_b_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, lean_box(0));
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0___boxed(lean_object* v_k_454_, lean_object* v_b_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0(v_k_454_, v_b_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
lean_dec(v___y_457_);
lean_dec_ref(v___y_456_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(lean_object* v_name_462_, uint8_t v_bi_463_, lean_object* v_type_464_, lean_object* v_k_465_, uint8_t v_kind_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v___f_472_; lean_object* v___x_473_; 
v___f_472_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_472_, 0, v_k_465_);
v___x_473_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_462_, v_bi_463_, v_type_464_, v___f_472_, v_kind_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
if (lean_obj_tag(v___x_473_) == 0)
{
lean_object* v_a_474_; lean_object* v___x_476_; uint8_t v_isShared_477_; uint8_t v_isSharedCheck_481_; 
v_a_474_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_481_ == 0)
{
v___x_476_ = v___x_473_;
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
else
{
lean_inc(v_a_474_);
lean_dec(v___x_473_);
v___x_476_ = lean_box(0);
v_isShared_477_ = v_isSharedCheck_481_;
goto v_resetjp_475_;
}
v_resetjp_475_:
{
lean_object* v___x_479_; 
if (v_isShared_477_ == 0)
{
v___x_479_ = v___x_476_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v_a_474_);
v___x_479_ = v_reuseFailAlloc_480_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
return v___x_479_;
}
}
}
else
{
lean_object* v_a_482_; lean_object* v___x_484_; uint8_t v_isShared_485_; uint8_t v_isSharedCheck_489_; 
v_a_482_ = lean_ctor_get(v___x_473_, 0);
v_isSharedCheck_489_ = !lean_is_exclusive(v___x_473_);
if (v_isSharedCheck_489_ == 0)
{
v___x_484_ = v___x_473_;
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
else
{
lean_inc(v_a_482_);
lean_dec(v___x_473_);
v___x_484_ = lean_box(0);
v_isShared_485_ = v_isSharedCheck_489_;
goto v_resetjp_483_;
}
v_resetjp_483_:
{
lean_object* v___x_487_; 
if (v_isShared_485_ == 0)
{
v___x_487_ = v___x_484_;
goto v_reusejp_486_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_a_482_);
v___x_487_ = v_reuseFailAlloc_488_;
goto v_reusejp_486_;
}
v_reusejp_486_:
{
return v___x_487_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg___boxed(lean_object* v_name_490_, lean_object* v_bi_491_, lean_object* v_type_492_, lean_object* v_k_493_, lean_object* v_kind_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
uint8_t v_bi_boxed_500_; uint8_t v_kind_boxed_501_; lean_object* v_res_502_; 
v_bi_boxed_500_ = lean_unbox(v_bi_491_);
v_kind_boxed_501_ = lean_unbox(v_kind_494_);
v_res_502_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_490_, v_bi_boxed_500_, v_type_492_, v_k_493_, v_kind_boxed_501_, v___y_495_, v___y_496_, v___y_497_, v___y_498_);
lean_dec(v___y_498_);
lean_dec_ref(v___y_497_);
lean_dec(v___y_496_);
lean_dec_ref(v___y_495_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(lean_object* v_name_503_, lean_object* v_type_504_, lean_object* v_k_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
uint8_t v___x_511_; uint8_t v___x_512_; lean_object* v___x_513_; 
v___x_511_ = 0;
v___x_512_ = 0;
v___x_513_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_503_, v___x_511_, v_type_504_, v_k_505_, v___x_512_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object* v_name_514_, lean_object* v_type_515_, lean_object* v_k_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v_name_514_, v_type_515_, v_k_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_);
lean_dec(v___y_520_);
lean_dec_ref(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(lean_object* v_msgData_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_){
_start:
{
lean_object* v___x_529_; lean_object* v_env_530_; uint8_t v___x_531_; lean_object* v_env_532_; lean_object* v___x_533_; lean_object* v_toCold_534_; lean_object* v_mctx_535_; lean_object* v_lctx_536_; lean_object* v_options_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_529_ = lean_st_ref_get(v___y_527_);
v_env_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_ref(v_env_530_);
lean_dec(v___x_529_);
v___x_531_ = 0;
v_env_532_ = l_Lean_Environment_setRecordingDeps(v_env_530_, v___x_531_);
v___x_533_ = lean_st_ref_get(v___y_525_);
v_toCold_534_ = lean_ctor_get(v___y_526_, 0);
v_mctx_535_ = lean_ctor_get(v___x_533_, 0);
lean_inc_ref(v_mctx_535_);
lean_dec(v___x_533_);
v_lctx_536_ = lean_ctor_get(v___y_524_, 2);
v_options_537_ = lean_ctor_get(v_toCold_534_, 2);
lean_inc_ref(v_options_537_);
lean_inc_ref(v_lctx_536_);
v___x_538_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_538_, 0, v_env_532_);
lean_ctor_set(v___x_538_, 1, v_mctx_535_);
lean_ctor_set(v___x_538_, 2, v_lctx_536_);
lean_ctor_set(v___x_538_, 3, v_options_537_);
v___x_539_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_539_, 0, v___x_538_);
lean_ctor_set(v___x_539_, 1, v_msgData_523_);
v___x_540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_540_, 0, v___x_539_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2___boxed(lean_object* v_msgData_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msgData_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec(v___y_545_);
lean_dec_ref(v___y_544_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
return v_res_547_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0(void){
_start:
{
lean_object* v___x_548_; double v___x_549_; 
v___x_548_ = lean_unsigned_to_nat(0u);
v___x_549_ = lean_float_of_nat(v___x_548_);
return v___x_549_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(lean_object* v_cls_553_, lean_object* v_msg_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_ref_560_; lean_object* v___x_561_; lean_object* v_a_562_; lean_object* v___x_564_; uint8_t v_isShared_565_; uint8_t v_isSharedCheck_607_; 
v_ref_560_ = lean_ctor_get(v___y_557_, 2);
v___x_561_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msg_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
v_a_562_ = lean_ctor_get(v___x_561_, 0);
v_isSharedCheck_607_ = !lean_is_exclusive(v___x_561_);
if (v_isSharedCheck_607_ == 0)
{
v___x_564_ = v___x_561_;
v_isShared_565_ = v_isSharedCheck_607_;
goto v_resetjp_563_;
}
else
{
lean_inc(v_a_562_);
lean_dec(v___x_561_);
v___x_564_ = lean_box(0);
v_isShared_565_ = v_isSharedCheck_607_;
goto v_resetjp_563_;
}
v_resetjp_563_:
{
lean_object* v___x_566_; lean_object* v_traceState_567_; lean_object* v_env_568_; lean_object* v_nextMacroScope_569_; lean_object* v_ngen_570_; lean_object* v_auxDeclNGen_571_; lean_object* v_cache_572_; lean_object* v_recordedDeps_573_; lean_object* v_messages_574_; lean_object* v_infoState_575_; lean_object* v_snapshotTasks_576_; lean_object* v___x_578_; uint8_t v_isShared_579_; uint8_t v_isSharedCheck_606_; 
v___x_566_ = lean_st_ref_take(v___y_558_);
v_traceState_567_ = lean_ctor_get(v___x_566_, 4);
v_env_568_ = lean_ctor_get(v___x_566_, 0);
v_nextMacroScope_569_ = lean_ctor_get(v___x_566_, 1);
v_ngen_570_ = lean_ctor_get(v___x_566_, 2);
v_auxDeclNGen_571_ = lean_ctor_get(v___x_566_, 3);
v_cache_572_ = lean_ctor_get(v___x_566_, 5);
v_recordedDeps_573_ = lean_ctor_get(v___x_566_, 6);
v_messages_574_ = lean_ctor_get(v___x_566_, 7);
v_infoState_575_ = lean_ctor_get(v___x_566_, 8);
v_snapshotTasks_576_ = lean_ctor_get(v___x_566_, 9);
v_isSharedCheck_606_ = !lean_is_exclusive(v___x_566_);
if (v_isSharedCheck_606_ == 0)
{
v___x_578_ = v___x_566_;
v_isShared_579_ = v_isSharedCheck_606_;
goto v_resetjp_577_;
}
else
{
lean_inc(v_snapshotTasks_576_);
lean_inc(v_infoState_575_);
lean_inc(v_messages_574_);
lean_inc(v_recordedDeps_573_);
lean_inc(v_cache_572_);
lean_inc(v_traceState_567_);
lean_inc(v_auxDeclNGen_571_);
lean_inc(v_ngen_570_);
lean_inc(v_nextMacroScope_569_);
lean_inc(v_env_568_);
lean_dec(v___x_566_);
v___x_578_ = lean_box(0);
v_isShared_579_ = v_isSharedCheck_606_;
goto v_resetjp_577_;
}
v_resetjp_577_:
{
uint64_t v_tid_580_; lean_object* v_traces_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_605_; 
v_tid_580_ = lean_ctor_get_uint64(v_traceState_567_, sizeof(void*)*1);
v_traces_581_ = lean_ctor_get(v_traceState_567_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v_traceState_567_);
if (v_isSharedCheck_605_ == 0)
{
v___x_583_ = v_traceState_567_;
v_isShared_584_ = v_isSharedCheck_605_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_traces_581_);
lean_dec(v_traceState_567_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_605_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; lean_object* v___x_586_; double v___x_587_; uint8_t v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_596_; 
v___x_585_ = lean_box(0);
v___x_586_ = lean_box(0);
v___x_587_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0);
v___x_588_ = 0;
v___x_589_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__1));
v___x_590_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_590_, 0, v_cls_553_);
lean_ctor_set(v___x_590_, 1, v___x_586_);
lean_ctor_set(v___x_590_, 2, v___x_589_);
lean_ctor_set_float(v___x_590_, sizeof(void*)*3, v___x_587_);
lean_ctor_set_float(v___x_590_, sizeof(void*)*3 + 8, v___x_587_);
lean_ctor_set_uint8(v___x_590_, sizeof(void*)*3 + 16, v___x_588_);
v___x_591_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__2));
v___x_592_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_592_, 0, v___x_590_);
lean_ctor_set(v___x_592_, 1, v_a_562_);
lean_ctor_set(v___x_592_, 2, v___x_591_);
lean_inc(v_ref_560_);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_ref_560_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v___x_594_ = l_Lean_PersistentArray_push___redArg(v_traces_581_, v___x_593_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_594_);
v___x_596_ = v___x_583_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_604_; 
v_reuseFailAlloc_604_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_604_, 0, v___x_594_);
lean_ctor_set_uint64(v_reuseFailAlloc_604_, sizeof(void*)*1, v_tid_580_);
v___x_596_ = v_reuseFailAlloc_604_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_598_; 
if (v_isShared_579_ == 0)
{
lean_ctor_set(v___x_578_, 4, v___x_596_);
v___x_598_ = v___x_578_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_603_; 
v_reuseFailAlloc_603_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_603_, 0, v_env_568_);
lean_ctor_set(v_reuseFailAlloc_603_, 1, v_nextMacroScope_569_);
lean_ctor_set(v_reuseFailAlloc_603_, 2, v_ngen_570_);
lean_ctor_set(v_reuseFailAlloc_603_, 3, v_auxDeclNGen_571_);
lean_ctor_set(v_reuseFailAlloc_603_, 4, v___x_596_);
lean_ctor_set(v_reuseFailAlloc_603_, 5, v_cache_572_);
lean_ctor_set(v_reuseFailAlloc_603_, 6, v_recordedDeps_573_);
lean_ctor_set(v_reuseFailAlloc_603_, 7, v_messages_574_);
lean_ctor_set(v_reuseFailAlloc_603_, 8, v_infoState_575_);
lean_ctor_set(v_reuseFailAlloc_603_, 9, v_snapshotTasks_576_);
v___x_598_ = v_reuseFailAlloc_603_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; lean_object* v___x_601_; 
v___x_599_ = lean_st_ref_put(v___y_558_, v___x_598_);
if (v_isShared_565_ == 0)
{
lean_ctor_set(v___x_564_, 0, v___x_585_);
v___x_601_ = v___x_564_;
goto v_reusejp_600_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_585_);
v___x_601_ = v_reuseFailAlloc_602_;
goto v_reusejp_600_;
}
v_reusejp_600_:
{
return v___x_601_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___boxed(lean_object* v_cls_608_, lean_object* v_msg_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
lean_object* v_res_615_; 
v_res_615_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v_cls_608_, v_msg_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
return v_res_615_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_620_; lean_object* v___x_621_; 
v___x_620_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__2));
v___x_621_ = l_Lean_stringToMessageData(v___x_620_);
return v___x_621_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__5(void){
_start:
{
lean_object* v___x_623_; lean_object* v___x_624_; 
v___x_623_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__4));
v___x_624_ = l_Lean_stringToMessageData(v___x_623_);
return v___x_624_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__11(void){
_start:
{
lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_631_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__10));
v___x_632_ = lean_unsigned_to_nat(22u);
v___x_633_ = lean_unsigned_to_nat(64u);
v___x_634_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__9));
v___x_635_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__8));
v___x_636_ = l_mkPanicMessageWithDecl(v___x_635_, v___x_634_, v___x_633_, v___x_632_, v___x_631_);
return v___x_636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object* v_fvarId_637_, lean_object* v_hFVarId_638_, lean_object* v___x_639_, lean_object* v_fst_640_, lean_object* v_fvarSubst_641_, uint8_t v_clearH_642_, lean_object* v___x_643_, lean_object* v___x_644_, lean_object* v___x_645_, uint8_t v_skip_646_, uint8_t v___x_647_, lean_object* v___x_648_, lean_object* v_snd_649_, lean_object* v___x_650_, lean_object* v___x_651_, lean_object* v_a_652_, uint8_t v_symm_653_, uint8_t v___x_654_, lean_object* v___x_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v___y_662_; lean_object* v___y_663_; lean_object* v___y_664_; lean_object* v___y_670_; lean_object* v___y_671_; lean_object* v___y_672_; lean_object* v___y_678_; lean_object* v_mvarId_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_732_; lean_object* v___y_733_; lean_object* v_newVal_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v___y_765_; lean_object* v_major_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_803_; uint8_t v___y_804_; lean_object* v_motive_805_; lean_object* v_newType_806_; lean_object* v___x_817_; 
lean_inc(v_snd_649_);
v___x_817_ = l_Lean_MVarId_getDecl(v_snd_649_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_817_) == 0)
{
lean_object* v_a_818_; lean_object* v_type_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___f_822_; lean_object* v___x_823_; 
v_a_818_ = lean_ctor_get(v___x_817_, 0);
lean_inc(v_a_818_);
lean_dec_ref_known(v___x_817_, 1);
v_type_819_ = lean_ctor_get(v_a_818_, 2);
lean_inc_ref_n(v_type_819_, 2);
lean_dec(v_a_818_);
v___x_820_ = lean_box(v___x_654_);
v___x_821_ = lean_box(v___x_647_);
lean_inc_ref(v___x_643_);
lean_inc(v___x_644_);
lean_inc_ref(v___x_639_);
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__0___boxed), 12, 6);
lean_closure_set(v___f_822_, 0, v_type_819_);
lean_closure_set(v___f_822_, 1, v___x_639_);
lean_closure_set(v___f_822_, 2, v___x_644_);
lean_closure_set(v___f_822_, 3, v___x_643_);
lean_closure_set(v___f_822_, 4, v___x_820_);
lean_closure_set(v___f_822_, 5, v___x_821_);
lean_inc(v___x_650_);
v___x_823_ = l_Lean_FVarId_getDecl___redArg(v___x_650_, v___y_656_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_823_) == 0)
{
lean_object* v_a_824_; lean_object* v___x_825_; lean_object* v___x_826_; 
v_a_824_ = lean_ctor_get(v___x_823_, 0);
lean_inc(v_a_824_);
lean_dec_ref_known(v___x_823_, 1);
v___x_825_ = l_Lean_LocalDecl_type(v_a_824_);
lean_dec(v_a_824_);
v___x_826_ = l_Lean_Meta_matchEq_x3f(v___x_825_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_826_) == 0)
{
lean_object* v_a_827_; lean_object* v___y_829_; 
v_a_827_ = lean_ctor_get(v___x_826_, 0);
lean_inc(v_a_827_);
lean_dec_ref_known(v___x_826_, 1);
if (lean_obj_tag(v_a_827_) == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; 
lean_dec_ref(v___f_822_);
lean_dec_ref(v_type_819_);
lean_dec(v_a_652_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v___x_899_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__11, &l_Lean_Meta_substCore___lam__1___closed__11_once, _init_l_Lean_Meta_substCore___lam__1___closed__11);
v___x_900_ = l_panic___at___00Lean_Meta_substCore_spec__6(v___x_899_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
return v___x_900_;
}
else
{
lean_object* v_val_901_; lean_object* v_snd_902_; 
v_val_901_ = lean_ctor_get(v_a_827_, 0);
lean_inc(v_val_901_);
lean_dec_ref_known(v_a_827_, 1);
v_snd_902_ = lean_ctor_get(v_val_901_, 1);
lean_inc(v_snd_902_);
lean_dec(v_val_901_);
if (v_symm_653_ == 0)
{
lean_object* v_snd_903_; 
v_snd_903_ = lean_ctor_get(v_snd_902_, 1);
lean_inc(v_snd_903_);
lean_dec(v_snd_902_);
v___y_829_ = v_snd_903_;
goto v___jp_828_;
}
else
{
lean_object* v_fst_904_; 
v_fst_904_ = lean_ctor_get(v_snd_902_, 0);
lean_inc(v_fst_904_);
lean_dec(v_snd_902_);
v___y_829_ = v_fst_904_;
goto v___jp_828_;
}
}
v___jp_828_:
{
lean_object* v___x_830_; lean_object* v_a_831_; lean_object* v___x_832_; lean_object* v_a_833_; uint8_t v___x_834_; 
v___x_830_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_829_, v___y_657_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref(v___x_830_);
lean_inc(v___x_650_);
lean_inc_ref(v_type_819_);
v___x_832_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_type_819_, v___x_650_, v___y_657_);
v_a_833_ = lean_ctor_get(v___x_832_, 0);
lean_inc(v_a_833_);
lean_dec_ref(v___x_832_);
v___x_834_ = lean_unbox(v_a_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; lean_object* v___x_838_; 
lean_dec_ref(v___f_822_);
v___x_835_ = lean_mk_empty_array_with_capacity(v___x_655_);
lean_inc_ref(v___x_643_);
v___x_836_ = lean_array_push(v___x_835_, v___x_643_);
v___x_837_ = 1;
lean_inc_ref(v_type_819_);
v___x_838_ = l_Lean_Meta_mkLambdaFVars(v___x_836_, v_type_819_, v___x_654_, v___x_647_, v___x_654_, v___x_647_, v___x_837_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec_ref(v___x_836_);
if (lean_obj_tag(v___x_838_) == 0)
{
lean_object* v_a_839_; lean_object* v___x_840_; uint8_t v___x_841_; 
v_a_839_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_a_839_);
lean_dec_ref_known(v___x_838_, 1);
lean_inc_ref(v___x_643_);
v___x_840_ = l_Lean_Expr_replaceFVar(v_type_819_, v___x_643_, v_a_831_);
lean_dec_ref(v_type_819_);
v___x_841_ = lean_unbox(v_a_833_);
lean_dec(v_a_833_);
v___y_803_ = v_a_831_;
v___y_804_ = v___x_841_;
v_motive_805_ = v_a_839_;
v_newType_806_ = v___x_840_;
goto v___jp_802_;
}
else
{
lean_object* v_a_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_849_; 
lean_dec(v_a_833_);
lean_dec(v_a_831_);
lean_dec_ref(v_type_819_);
lean_dec(v_a_652_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_842_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_849_ == 0)
{
v___x_844_ = v___x_838_;
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_a_842_);
lean_dec(v___x_838_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_849_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_847_; 
if (v_isShared_845_ == 0)
{
v___x_847_ = v___x_844_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v_a_842_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
}
else
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_inc_ref(v___x_643_);
v___x_850_ = l_Lean_Expr_replaceFVar(v_type_819_, v___x_643_, v_a_831_);
lean_inc(v_a_831_);
v___x_851_ = l_Lean_Meta_mkEqRefl(v_a_831_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_851_) == 0)
{
lean_object* v_a_852_; lean_object* v___x_853_; 
v_a_852_ = lean_ctor_get(v___x_851_, 0);
lean_inc(v_a_852_);
lean_dec_ref_known(v___x_851_, 1);
lean_inc_ref(v___x_639_);
v___x_853_ = l_Lean_Expr_replaceFVar(v___x_850_, v___x_639_, v_a_852_);
lean_dec(v_a_852_);
lean_dec_ref(v___x_850_);
if (v_symm_653_ == 0)
{
lean_object* v___x_854_; 
lean_dec_ref(v_type_819_);
lean_inc_ref(v___x_643_);
lean_inc(v_a_831_);
v___x_854_ = l_Lean_Meta_mkEq(v_a_831_, v___x_643_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_854_) == 0)
{
lean_object* v_a_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v_a_855_ = lean_ctor_get(v___x_854_, 0);
lean_inc(v_a_855_);
lean_dec_ref_known(v___x_854_, 1);
v___x_856_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__7));
v___x_857_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v___x_856_, v_a_855_, v___f_822_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; uint8_t v___x_859_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
lean_inc(v_a_858_);
lean_dec_ref_known(v___x_857_, 1);
v___x_859_ = lean_unbox(v_a_833_);
lean_dec(v_a_833_);
v___y_803_ = v_a_831_;
v___y_804_ = v___x_859_;
v_motive_805_ = v_a_858_;
v_newType_806_ = v___x_853_;
goto v___jp_802_;
}
else
{
lean_object* v_a_860_; lean_object* v___x_862_; uint8_t v_isShared_863_; uint8_t v_isSharedCheck_867_; 
lean_dec_ref(v___x_853_);
lean_dec(v_a_833_);
lean_dec(v_a_831_);
lean_dec(v_a_652_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_860_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_867_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_867_ == 0)
{
v___x_862_ = v___x_857_;
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
else
{
lean_inc(v_a_860_);
lean_dec(v___x_857_);
v___x_862_ = lean_box(0);
v_isShared_863_ = v_isSharedCheck_867_;
goto v_resetjp_861_;
}
v_resetjp_861_:
{
lean_object* v___x_865_; 
if (v_isShared_863_ == 0)
{
v___x_865_ = v___x_862_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_860_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
else
{
lean_object* v_a_868_; lean_object* v___x_870_; uint8_t v_isShared_871_; uint8_t v_isSharedCheck_875_; 
lean_dec_ref(v___x_853_);
lean_dec(v_a_833_);
lean_dec(v_a_831_);
lean_dec_ref(v___f_822_);
lean_dec(v_a_652_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_868_ = lean_ctor_get(v___x_854_, 0);
v_isSharedCheck_875_ = !lean_is_exclusive(v___x_854_);
if (v_isSharedCheck_875_ == 0)
{
v___x_870_ = v___x_854_;
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
else
{
lean_inc(v_a_868_);
lean_dec(v___x_854_);
v___x_870_ = lean_box(0);
v_isShared_871_ = v_isSharedCheck_875_;
goto v_resetjp_869_;
}
v_resetjp_869_:
{
lean_object* v___x_873_; 
if (v_isShared_871_ == 0)
{
v___x_873_ = v___x_870_;
goto v_reusejp_872_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_a_868_);
v___x_873_ = v_reuseFailAlloc_874_;
goto v_reusejp_872_;
}
v_reusejp_872_:
{
return v___x_873_;
}
}
}
}
else
{
lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; uint8_t v___x_879_; lean_object* v___x_880_; 
lean_dec_ref(v___f_822_);
v___x_876_ = lean_mk_empty_array_with_capacity(v___x_644_);
lean_inc_ref(v___x_643_);
v___x_877_ = lean_array_push(v___x_876_, v___x_643_);
lean_inc_ref(v___x_639_);
v___x_878_ = lean_array_push(v___x_877_, v___x_639_);
v___x_879_ = 1;
v___x_880_ = l_Lean_Meta_mkLambdaFVars(v___x_878_, v_type_819_, v___x_654_, v___x_647_, v___x_654_, v___x_647_, v___x_879_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec_ref(v___x_878_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v_a_881_; uint8_t v___x_882_; 
v_a_881_ = lean_ctor_get(v___x_880_, 0);
lean_inc(v_a_881_);
lean_dec_ref_known(v___x_880_, 1);
v___x_882_ = lean_unbox(v_a_833_);
lean_dec(v_a_833_);
v___y_803_ = v_a_831_;
v___y_804_ = v___x_882_;
v_motive_805_ = v_a_881_;
v_newType_806_ = v___x_853_;
goto v___jp_802_;
}
else
{
lean_object* v_a_883_; lean_object* v___x_885_; uint8_t v_isShared_886_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v___x_853_);
lean_dec(v_a_833_);
lean_dec(v_a_831_);
lean_dec(v_a_652_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_883_ = lean_ctor_get(v___x_880_, 0);
v_isSharedCheck_890_ = !lean_is_exclusive(v___x_880_);
if (v_isSharedCheck_890_ == 0)
{
v___x_885_ = v___x_880_;
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
else
{
lean_inc(v_a_883_);
lean_dec(v___x_880_);
v___x_885_ = lean_box(0);
v_isShared_886_ = v_isSharedCheck_890_;
goto v_resetjp_884_;
}
v_resetjp_884_:
{
lean_object* v___x_888_; 
if (v_isShared_886_ == 0)
{
v___x_888_ = v___x_885_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_a_883_);
v___x_888_ = v_reuseFailAlloc_889_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
return v___x_888_;
}
}
}
}
}
else
{
lean_object* v_a_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_898_; 
lean_dec_ref(v___x_850_);
lean_dec(v_a_833_);
lean_dec(v_a_831_);
lean_dec_ref(v___f_822_);
lean_dec_ref(v_type_819_);
lean_dec(v_a_652_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_891_ = lean_ctor_get(v___x_851_, 0);
v_isSharedCheck_898_ = !lean_is_exclusive(v___x_851_);
if (v_isSharedCheck_898_ == 0)
{
v___x_893_ = v___x_851_;
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_a_891_);
lean_dec(v___x_851_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_898_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_896_; 
if (v_isShared_894_ == 0)
{
v___x_896_ = v___x_893_;
goto v_reusejp_895_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v_a_891_);
v___x_896_ = v_reuseFailAlloc_897_;
goto v_reusejp_895_;
}
v_reusejp_895_:
{
return v___x_896_;
}
}
}
}
}
}
else
{
lean_object* v_a_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_912_; 
lean_dec_ref(v___f_822_);
lean_dec_ref(v_type_819_);
lean_dec(v_a_652_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_905_ = lean_ctor_get(v___x_826_, 0);
v_isSharedCheck_912_ = !lean_is_exclusive(v___x_826_);
if (v_isSharedCheck_912_ == 0)
{
v___x_907_ = v___x_826_;
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_a_905_);
lean_dec(v___x_826_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_912_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_910_; 
if (v_isShared_908_ == 0)
{
v___x_910_ = v___x_907_;
goto v_reusejp_909_;
}
else
{
lean_object* v_reuseFailAlloc_911_; 
v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_911_, 0, v_a_905_);
v___x_910_ = v_reuseFailAlloc_911_;
goto v_reusejp_909_;
}
v_reusejp_909_:
{
return v___x_910_;
}
}
}
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v___f_822_);
lean_dec_ref(v_type_819_);
lean_dec(v_a_652_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_913_ = lean_ctor_get(v___x_823_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_823_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_823_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_823_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_918_; 
if (v_isShared_916_ == 0)
{
v___x_918_ = v___x_915_;
goto v_reusejp_917_;
}
else
{
lean_object* v_reuseFailAlloc_919_; 
v_reuseFailAlloc_919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_919_, 0, v_a_913_);
v___x_918_ = v_reuseFailAlloc_919_;
goto v_reusejp_917_;
}
v_reusejp_917_:
{
return v___x_918_;
}
}
}
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec(v_a_652_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_921_ = lean_ctor_get(v___x_817_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_817_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_817_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_817_);
v___x_923_ = lean_box(0);
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
v_resetjp_922_:
{
lean_object* v___x_926_; 
if (v_isShared_924_ == 0)
{
v___x_926_ = v___x_923_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_a_921_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
return v___x_926_;
}
}
}
v___jp_661_:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; 
v___x_665_ = l_Lean_Meta_FVarSubst_insert(v___y_662_, v_fvarId_637_, v___y_664_);
v___x_666_ = l_Lean_Meta_FVarSubst_insert(v___x_665_, v_hFVarId_638_, v___x_639_);
v___x_667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_667_, 0, v___x_666_);
lean_ctor_set(v___x_667_, 1, v___y_663_);
v___x_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_668_, 0, v___x_667_);
return v___x_668_;
}
v___jp_669_:
{
lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_673_ = lean_array_get_size(v___y_670_);
v___x_674_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_640_, v___y_670_, v___x_673_, v___x_673_, v_fvarSubst_641_);
lean_dec_ref(v___y_670_);
if (v_clearH_642_ == 0)
{
lean_object* v_a_675_; 
lean_dec_ref(v___y_671_);
v_a_675_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_675_);
lean_dec_ref(v___x_674_);
v___y_662_ = v_a_675_;
v___y_663_ = v___y_672_;
v___y_664_ = v___x_643_;
goto v___jp_661_;
}
else
{
lean_object* v_a_676_; 
lean_dec_ref(v___x_643_);
v_a_676_ = lean_ctor_get(v___x_674_, 0);
lean_inc(v_a_676_);
lean_dec_ref(v___x_674_);
v___y_662_ = v_a_676_;
v___y_663_ = v___y_672_;
v___y_664_ = v___y_671_;
goto v___jp_661_;
}
}
v___jp_677_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v___x_684_ = lean_array_get_size(v_fst_640_);
v___x_685_ = lean_nat_sub(v___x_684_, v___x_644_);
lean_dec(v___x_644_);
lean_inc(v___x_685_);
v___x_686_ = l_Lean_Meta_introNCore(v_mvarId_679_, v___x_685_, v___x_645_, v_skip_646_, v___x_647_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_686_) == 0)
{
lean_object* v_a_687_; lean_object* v_toCold_688_; lean_object* v_options_689_; uint8_t v_hasTrace_690_; 
v_a_687_ = lean_ctor_get(v___x_686_, 0);
lean_inc(v_a_687_);
lean_dec_ref_known(v___x_686_, 1);
v_toCold_688_ = lean_ctor_get(v___y_682_, 0);
v_options_689_ = lean_ctor_get(v_toCold_688_, 2);
v_hasTrace_690_ = lean_ctor_get_uint8(v_options_689_, sizeof(void*)*1);
if (v_hasTrace_690_ == 0)
{
lean_object* v_fst_691_; lean_object* v_snd_692_; 
lean_dec(v___x_685_);
lean_dec(v___x_648_);
v_fst_691_ = lean_ctor_get(v_a_687_, 0);
lean_inc(v_fst_691_);
v_snd_692_ = lean_ctor_get(v_a_687_, 1);
lean_inc(v_snd_692_);
lean_dec(v_a_687_);
v___y_670_ = v_fst_691_;
v___y_671_ = v___y_678_;
v___y_672_ = v_snd_692_;
goto v___jp_669_;
}
else
{
lean_object* v_fst_693_; lean_object* v_snd_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_722_; 
v_fst_693_ = lean_ctor_get(v_a_687_, 0);
v_snd_694_ = lean_ctor_get(v_a_687_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v_a_687_);
if (v_isSharedCheck_722_ == 0)
{
v___x_696_ = v_a_687_;
v_isShared_697_ = v_isSharedCheck_722_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_snd_694_);
lean_inc(v_fst_693_);
lean_dec(v_a_687_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_722_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v_inheritedTraceOptions_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; 
v_inheritedTraceOptions_698_ = lean_ctor_get(v_toCold_688_, 11);
v___x_699_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
lean_inc(v___x_648_);
v___x_700_ = l_Lean_Name_append(v___x_699_, v___x_648_);
v___x_701_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_698_, v_options_689_, v___x_700_);
lean_dec(v___x_700_);
if (v___x_701_ == 0)
{
lean_del_object(v___x_696_);
lean_dec(v___x_685_);
lean_dec(v___x_648_);
v___y_670_ = v_fst_693_;
v___y_671_ = v___y_678_;
v___y_672_ = v_snd_694_;
goto v___jp_669_;
}
else
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_707_; 
v___x_702_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__3, &l_Lean_Meta_substCore___lam__1___closed__3_once, _init_l_Lean_Meta_substCore___lam__1___closed__3);
v___x_703_ = l_Nat_reprFast(v___x_685_);
v___x_704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_704_, 0, v___x_703_);
v___x_705_ = l_Lean_MessageData_ofFormat(v___x_704_);
if (v_isShared_697_ == 0)
{
lean_ctor_set_tag(v___x_696_, 7);
lean_ctor_set(v___x_696_, 1, v___x_705_);
lean_ctor_set(v___x_696_, 0, v___x_702_);
v___x_707_ = v___x_696_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_702_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_705_);
v___x_707_ = v_reuseFailAlloc_721_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; 
v___x_708_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__5, &l_Lean_Meta_substCore___lam__1___closed__5_once, _init_l_Lean_Meta_substCore___lam__1___closed__5);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
lean_inc(v_snd_694_);
v___x_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_710_, 0, v_snd_694_);
v___x_711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_709_);
lean_ctor_set(v___x_711_, 1, v___x_710_);
v___x_712_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_648_, v___x_711_, v___y_680_, v___y_681_, v___y_682_, v___y_683_);
if (lean_obj_tag(v___x_712_) == 0)
{
lean_dec_ref_known(v___x_712_, 1);
v___y_670_ = v_fst_693_;
v___y_671_ = v___y_678_;
v___y_672_ = v_snd_694_;
goto v___jp_669_;
}
else
{
lean_object* v_a_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_720_; 
lean_dec(v_snd_694_);
lean_dec(v_fst_693_);
lean_dec_ref(v___y_678_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_713_ = lean_ctor_get(v___x_712_, 0);
v_isSharedCheck_720_ = !lean_is_exclusive(v___x_712_);
if (v_isSharedCheck_720_ == 0)
{
v___x_715_ = v___x_712_;
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_a_713_);
lean_dec(v___x_712_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_720_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_718_; 
if (v_isShared_716_ == 0)
{
v___x_718_ = v___x_715_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
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
lean_object* v_a_723_; lean_object* v___x_725_; uint8_t v_isShared_726_; uint8_t v_isSharedCheck_730_; 
lean_dec(v___x_685_);
lean_dec_ref(v___y_678_);
lean_dec(v___x_648_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_723_ = lean_ctor_get(v___x_686_, 0);
v_isSharedCheck_730_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_730_ == 0)
{
v___x_725_ = v___x_686_;
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
else
{
lean_inc(v_a_723_);
lean_dec(v___x_686_);
v___x_725_ = lean_box(0);
v_isShared_726_ = v_isSharedCheck_730_;
goto v_resetjp_724_;
}
v_resetjp_724_:
{
lean_object* v___x_728_; 
if (v_isShared_726_ == 0)
{
v___x_728_ = v___x_725_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v_a_723_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
v___jp_731_:
{
lean_object* v___x_739_; lean_object* v___x_740_; 
v___x_739_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_snd_649_, v_newVal_734_, v___y_736_);
lean_dec_ref(v___x_739_);
v___x_740_ = l_Lean_Expr_mvarId_x21(v___y_732_);
lean_dec_ref(v___y_732_);
if (v_clearH_642_ == 0)
{
lean_dec(v___x_651_);
lean_dec(v___x_650_);
v___y_678_ = v___y_733_;
v_mvarId_679_ = v___x_740_;
v___y_680_ = v___y_735_;
v___y_681_ = v___y_736_;
v___y_682_ = v___y_737_;
v___y_683_ = v___y_738_;
goto v___jp_677_;
}
else
{
lean_object* v___x_741_; 
v___x_741_ = l_Lean_MVarId_clear(v___x_740_, v___x_650_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; lean_object* v___x_743_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___x_743_ = l_Lean_MVarId_clear(v_a_742_, v___x_651_, v___y_735_, v___y_736_, v___y_737_, v___y_738_);
if (lean_obj_tag(v___x_743_) == 0)
{
lean_object* v_a_744_; 
v_a_744_ = lean_ctor_get(v___x_743_, 0);
lean_inc(v_a_744_);
lean_dec_ref_known(v___x_743_, 1);
v___y_678_ = v___y_733_;
v_mvarId_679_ = v_a_744_;
v___y_680_ = v___y_735_;
v___y_681_ = v___y_736_;
v___y_682_ = v___y_737_;
v___y_683_ = v___y_738_;
goto v___jp_677_;
}
else
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec_ref(v___y_733_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_745_ = lean_ctor_get(v___x_743_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_743_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_743_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_743_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_750_; 
if (v_isShared_748_ == 0)
{
v___x_750_ = v___x_747_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
else
{
lean_object* v_a_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_760_; 
lean_dec_ref(v___y_733_);
lean_dec(v___x_651_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_753_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_760_ == 0)
{
v___x_755_ = v___x_741_;
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_a_753_);
lean_dec(v___x_741_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_760_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
if (v_isShared_756_ == 0)
{
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v_a_753_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
v___jp_761_:
{
lean_object* v___x_771_; 
v___x_771_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_763_, v_a_652_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_771_) == 0)
{
if (v___y_765_ == 0)
{
lean_object* v_a_772_; lean_object* v___x_773_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc_n(v_a_772_, 2);
lean_dec_ref_known(v___x_771_, 1);
v___x_773_ = l_Lean_Meta_mkEqNDRec(v___y_762_, v_a_772_, v_major_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
lean_inc(v_a_774_);
lean_dec_ref_known(v___x_773_, 1);
v___y_732_ = v_a_772_;
v___y_733_ = v___y_764_;
v_newVal_734_ = v_a_774_;
v___y_735_ = v___y_767_;
v___y_736_ = v___y_768_;
v___y_737_ = v___y_769_;
v___y_738_ = v___y_770_;
goto v___jp_731_;
}
else
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_782_; 
lean_dec(v_a_772_);
lean_dec_ref(v___y_764_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_775_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_773_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_773_);
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
lean_object* v_a_783_; lean_object* v___x_784_; 
v_a_783_ = lean_ctor_get(v___x_771_, 0);
lean_inc_n(v_a_783_, 2);
lean_dec_ref_known(v___x_771_, 1);
v___x_784_ = l_Lean_Meta_mkEqRec(v___y_762_, v_a_783_, v_major_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
if (lean_obj_tag(v___x_784_) == 0)
{
lean_object* v_a_785_; 
v_a_785_ = lean_ctor_get(v___x_784_, 0);
lean_inc(v_a_785_);
lean_dec_ref_known(v___x_784_, 1);
v___y_732_ = v_a_783_;
v___y_733_ = v___y_764_;
v_newVal_734_ = v_a_785_;
v___y_735_ = v___y_767_;
v___y_736_ = v___y_768_;
v___y_737_ = v___y_769_;
v___y_738_ = v___y_770_;
goto v___jp_731_;
}
else
{
lean_object* v_a_786_; lean_object* v___x_788_; uint8_t v_isShared_789_; uint8_t v_isSharedCheck_793_; 
lean_dec(v_a_783_);
lean_dec_ref(v___y_764_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_786_ = lean_ctor_get(v___x_784_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_784_);
if (v_isSharedCheck_793_ == 0)
{
v___x_788_ = v___x_784_;
v_isShared_789_ = v_isSharedCheck_793_;
goto v_resetjp_787_;
}
else
{
lean_inc(v_a_786_);
lean_dec(v___x_784_);
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
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
lean_dec_ref(v_major_766_);
lean_dec_ref(v___y_764_);
lean_dec_ref(v___y_762_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_794_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_771_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_771_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
v___jp_802_:
{
if (v_symm_653_ == 0)
{
lean_object* v___x_807_; 
lean_inc_ref(v___x_639_);
v___x_807_ = l_Lean_Meta_mkEqSymm(v___x_639_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
if (lean_obj_tag(v___x_807_) == 0)
{
lean_object* v_a_808_; 
v_a_808_ = lean_ctor_get(v___x_807_, 0);
lean_inc(v_a_808_);
lean_dec_ref_known(v___x_807_, 1);
v___y_762_ = v_motive_805_;
v___y_763_ = v_newType_806_;
v___y_764_ = v___y_803_;
v___y_765_ = v___y_804_;
v_major_766_ = v_a_808_;
v___y_767_ = v___y_656_;
v___y_768_ = v___y_657_;
v___y_769_ = v___y_658_;
v___y_770_ = v___y_659_;
goto v___jp_761_;
}
else
{
lean_object* v_a_809_; lean_object* v___x_811_; uint8_t v_isShared_812_; uint8_t v_isSharedCheck_816_; 
lean_dec_ref(v_newType_806_);
lean_dec_ref(v_motive_805_);
lean_dec_ref(v___y_803_);
lean_dec(v_a_652_);
lean_dec(v___x_651_);
lean_dec(v___x_650_);
lean_dec(v_snd_649_);
lean_dec(v___x_648_);
lean_dec(v___x_645_);
lean_dec(v___x_644_);
lean_dec_ref(v___x_643_);
lean_dec(v_fvarSubst_641_);
lean_dec_ref(v___x_639_);
lean_dec(v_hFVarId_638_);
lean_dec(v_fvarId_637_);
v_a_809_ = lean_ctor_get(v___x_807_, 0);
v_isSharedCheck_816_ = !lean_is_exclusive(v___x_807_);
if (v_isSharedCheck_816_ == 0)
{
v___x_811_ = v___x_807_;
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
else
{
lean_inc(v_a_809_);
lean_dec(v___x_807_);
v___x_811_ = lean_box(0);
v_isShared_812_ = v_isSharedCheck_816_;
goto v_resetjp_810_;
}
v_resetjp_810_:
{
lean_object* v___x_814_; 
if (v_isShared_812_ == 0)
{
v___x_814_ = v___x_811_;
goto v_reusejp_813_;
}
else
{
lean_object* v_reuseFailAlloc_815_; 
v_reuseFailAlloc_815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_815_, 0, v_a_809_);
v___x_814_ = v_reuseFailAlloc_815_;
goto v_reusejp_813_;
}
v_reusejp_813_:
{
return v___x_814_;
}
}
}
}
else
{
lean_inc_ref(v___x_639_);
v___y_762_ = v_motive_805_;
v___y_763_ = v_newType_806_;
v___y_764_ = v___y_803_;
v___y_765_ = v___y_804_;
v_major_766_ = v___x_639_;
v___y_767_ = v___y_656_;
v___y_768_ = v___y_657_;
v___y_769_ = v___y_658_;
v___y_770_ = v___y_659_;
goto v___jp_761_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object** _args){
lean_object* v_fvarId_929_ = _args[0];
lean_object* v_hFVarId_930_ = _args[1];
lean_object* v___x_931_ = _args[2];
lean_object* v_fst_932_ = _args[3];
lean_object* v_fvarSubst_933_ = _args[4];
lean_object* v_clearH_934_ = _args[5];
lean_object* v___x_935_ = _args[6];
lean_object* v___x_936_ = _args[7];
lean_object* v___x_937_ = _args[8];
lean_object* v_skip_938_ = _args[9];
lean_object* v___x_939_ = _args[10];
lean_object* v___x_940_ = _args[11];
lean_object* v_snd_941_ = _args[12];
lean_object* v___x_942_ = _args[13];
lean_object* v___x_943_ = _args[14];
lean_object* v_a_944_ = _args[15];
lean_object* v_symm_945_ = _args[16];
lean_object* v___x_946_ = _args[17];
lean_object* v___x_947_ = _args[18];
lean_object* v___y_948_ = _args[19];
lean_object* v___y_949_ = _args[20];
lean_object* v___y_950_ = _args[21];
lean_object* v___y_951_ = _args[22];
lean_object* v___y_952_ = _args[23];
_start:
{
uint8_t v_clearH_boxed_953_; uint8_t v_skip_boxed_954_; uint8_t v___x_27782__boxed_955_; uint8_t v_symm_boxed_956_; uint8_t v___x_27788__boxed_957_; lean_object* v_res_958_; 
v_clearH_boxed_953_ = lean_unbox(v_clearH_934_);
v_skip_boxed_954_ = lean_unbox(v_skip_938_);
v___x_27782__boxed_955_ = lean_unbox(v___x_939_);
v_symm_boxed_956_ = lean_unbox(v_symm_945_);
v___x_27788__boxed_957_ = lean_unbox(v___x_946_);
v_res_958_ = l_Lean_Meta_substCore___lam__1(v_fvarId_929_, v_hFVarId_930_, v___x_931_, v_fst_932_, v_fvarSubst_933_, v_clearH_boxed_953_, v___x_935_, v___x_936_, v___x_937_, v_skip_boxed_954_, v___x_27782__boxed_955_, v___x_940_, v_snd_941_, v___x_942_, v___x_943_, v_a_944_, v_symm_boxed_956_, v___x_27788__boxed_957_, v___x_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_);
lean_dec(v___y_951_);
lean_dec_ref(v___y_950_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___x_947_);
lean_dec_ref(v_fst_932_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object* v___x_959_, lean_object* v___y_960_, lean_object* v___y_961_, lean_object* v___y_962_, lean_object* v___y_963_){
_start:
{
lean_object* v_toCold_965_; lean_object* v_options_966_; uint8_t v_hasTrace_967_; 
v_toCold_965_ = lean_ctor_get(v___y_962_, 0);
v_options_966_ = lean_ctor_get(v_toCold_965_, 2);
v_hasTrace_967_ = lean_ctor_get_uint8(v_options_966_, sizeof(void*)*1);
if (v_hasTrace_967_ == 0)
{
lean_object* v___x_968_; lean_object* v___x_969_; 
lean_dec(v___x_959_);
v___x_968_ = lean_box(v_hasTrace_967_);
v___x_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
return v___x_969_;
}
else
{
lean_object* v_inheritedTraceOptions_970_; lean_object* v___x_971_; lean_object* v___x_972_; uint8_t v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; 
v_inheritedTraceOptions_970_ = lean_ctor_get(v_toCold_965_, 11);
v___x_971_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
v___x_972_ = l_Lean_Name_append(v___x_971_, v___x_959_);
v___x_973_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_970_, v_options_966_, v___x_972_);
lean_dec(v___x_972_);
v___x_974_ = lean_box(v___x_973_);
v___x_975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_975_, 0, v___x_974_);
return v___x_975_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object* v___x_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_, lean_object* v___y_980_, lean_object* v___y_981_){
_start:
{
lean_object* v_res_982_; 
v_res_982_ = l_Lean_Meta_substCore___lam__2(v___x_976_, v___y_977_, v___y_978_, v___y_979_, v___y_980_);
lean_dec(v___y_980_);
lean_dec_ref(v___y_979_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(lean_object* v_a_983_, lean_object* v_a_984_){
_start:
{
if (lean_obj_tag(v_a_983_) == 0)
{
lean_object* v___x_985_; 
v___x_985_ = l_List_reverse___redArg(v_a_984_);
return v___x_985_;
}
else
{
lean_object* v_head_986_; lean_object* v_tail_987_; lean_object* v___x_989_; uint8_t v_isShared_990_; uint8_t v_isSharedCheck_996_; 
v_head_986_ = lean_ctor_get(v_a_983_, 0);
v_tail_987_ = lean_ctor_get(v_a_983_, 1);
v_isSharedCheck_996_ = !lean_is_exclusive(v_a_983_);
if (v_isSharedCheck_996_ == 0)
{
v___x_989_ = v_a_983_;
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
else
{
lean_inc(v_tail_987_);
lean_inc(v_head_986_);
lean_dec(v_a_983_);
v___x_989_ = lean_box(0);
v_isShared_990_ = v_isSharedCheck_996_;
goto v_resetjp_988_;
}
v_resetjp_988_:
{
lean_object* v___x_991_; lean_object* v___x_993_; 
v___x_991_ = l_Lean_MessageData_ofName(v_head_986_);
if (v_isShared_990_ == 0)
{
lean_ctor_set(v___x_989_, 1, v_a_984_);
lean_ctor_set(v___x_989_, 0, v___x_991_);
v___x_993_ = v___x_989_;
goto v_reusejp_992_;
}
else
{
lean_object* v_reuseFailAlloc_995_; 
v_reuseFailAlloc_995_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_995_, 0, v___x_991_);
lean_ctor_set(v_reuseFailAlloc_995_, 1, v_a_984_);
v___x_993_ = v_reuseFailAlloc_995_;
goto v_reusejp_992_;
}
v_reusejp_992_:
{
v_a_983_ = v_tail_987_;
v_a_984_ = v___x_993_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(size_t v_sz_997_, size_t v_i_998_, lean_object* v_bs_999_){
_start:
{
uint8_t v___x_1000_; 
v___x_1000_ = lean_usize_dec_lt(v_i_998_, v_sz_997_);
if (v___x_1000_ == 0)
{
return v_bs_999_;
}
else
{
lean_object* v_v_1001_; lean_object* v___x_1002_; lean_object* v_bs_x27_1003_; size_t v___x_1004_; size_t v___x_1005_; lean_object* v___x_1006_; 
v_v_1001_ = lean_array_uget(v_bs_999_, v_i_998_);
v___x_1002_ = lean_unsigned_to_nat(0u);
v_bs_x27_1003_ = lean_array_uset(v_bs_999_, v_i_998_, v___x_1002_);
v___x_1004_ = ((size_t)1ULL);
v___x_1005_ = lean_usize_add(v_i_998_, v___x_1004_);
v___x_1006_ = lean_array_uset(v_bs_x27_1003_, v_i_998_, v_v_1001_);
v_i_998_ = v___x_1005_;
v_bs_999_ = v___x_1006_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8___boxed(lean_object* v_sz_1008_, lean_object* v_i_1009_, lean_object* v_bs_1010_){
_start:
{
size_t v_sz_boxed_1011_; size_t v_i_boxed_1012_; lean_object* v_res_1013_; 
v_sz_boxed_1011_ = lean_unbox_usize(v_sz_1008_);
lean_dec(v_sz_1008_);
v_i_boxed_1012_ = lean_unbox_usize(v_i_1009_);
lean_dec(v_i_1009_);
v_res_1013_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_boxed_1011_, v_i_boxed_1012_, v_bs_1010_);
return v_res_1013_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
v___x_1018_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__2));
v___x_1019_ = l_Lean_stringToMessageData(v___x_1018_);
return v___x_1019_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1021_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__4));
v___x_1022_ = l_Lean_stringToMessageData(v___x_1021_);
return v___x_1022_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__7));
v___x_1027_ = l_Lean_MessageData_ofFormat(v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__9(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__8, &l_Lean_Meta_substCore___lam__3___closed__8_once, _init_l_Lean_Meta_substCore___lam__3___closed__8);
v___x_1029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1029_, 0, v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__11(void){
_start:
{
lean_object* v___x_1031_; lean_object* v___x_1032_; 
v___x_1031_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__10));
v___x_1032_ = l_Lean_stringToMessageData(v___x_1031_);
return v___x_1032_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__13(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__12));
v___x_1035_ = l_Lean_stringToMessageData(v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__15(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__14));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__17(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__16));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__19(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__18));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__25(void){
_start:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; 
v___x_1054_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__24));
v___x_1055_ = l_Lean_stringToMessageData(v___x_1054_);
return v___x_1055_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__27(void){
_start:
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
v___x_1057_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__26));
v___x_1058_ = l_Lean_stringToMessageData(v___x_1057_);
return v___x_1058_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__29(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__28));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3(lean_object* v_mvarId_1064_, lean_object* v_hFVarId_1065_, lean_object* v___x_1066_, uint8_t v_clearH_1067_, lean_object* v_fvarSubst_1068_, uint8_t v_symm_1069_, uint8_t v_tryToSkip_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_){
_start:
{
lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___x_1114_; 
lean_inc(v_mvarId_1064_);
v___x_1114_ = l_Lean_MVarId_getTag(v_mvarId_1064_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v_a_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; 
v_a_1115_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v___x_1114_, 1);
v___x_1116_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
lean_inc(v_mvarId_1064_);
v___x_1117_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1064_, v___x_1116_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref_known(v___x_1117_, 1);
lean_inc(v_hFVarId_1065_);
v___x_1118_ = l_Lean_FVarId_getDecl___redArg(v_hFVarId_1065_, v___y_1071_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___x_1135_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref_known(v___x_1118_, 1);
v___x_1120_ = l_Lean_LocalDecl_type(v_a_1119_);
lean_dec(v_a_1119_);
lean_inc_ref(v___x_1120_);
v___x_1135_ = l_Lean_Meta_matchEq_x3f(v___x_1120_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1135_) == 0)
{
lean_object* v_a_1136_; 
v_a_1136_ = lean_ctor_get(v___x_1135_, 0);
lean_inc(v_a_1136_);
lean_dec_ref_known(v___x_1135_, 1);
if (lean_obj_tag(v_a_1136_) == 0)
{
lean_object* v___x_1137_; lean_object* v___x_1138_; 
lean_dec_ref(v___x_1120_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v___x_1137_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__9, &l_Lean_Meta_substCore___lam__3___closed__9_once, _init_l_Lean_Meta_substCore___lam__3___closed__9);
v___x_1138_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1116_, v_mvarId_1064_, v___x_1137_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v___x_1138_;
}
else
{
lean_object* v_val_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1457_; 
v_val_1139_ = lean_ctor_get(v_a_1136_, 0);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_a_1136_);
if (v_isSharedCheck_1457_ == 0)
{
v___x_1141_ = v_a_1136_;
v_isShared_1142_ = v_isSharedCheck_1457_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_val_1139_);
lean_dec(v_a_1136_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1457_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_snd_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1455_; 
v_snd_1143_ = lean_ctor_get(v_val_1139_, 1);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_val_1139_);
if (v_isSharedCheck_1455_ == 0)
{
lean_object* v_unused_1456_; 
v_unused_1456_ = lean_ctor_get(v_val_1139_, 0);
lean_dec(v_unused_1456_);
v___x_1145_ = v_val_1139_;
v_isShared_1146_ = v_isSharedCheck_1455_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_snd_1143_);
lean_dec(v_val_1139_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1455_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_fst_1147_; lean_object* v_snd_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1454_; 
v_fst_1147_ = lean_ctor_get(v_snd_1143_, 0);
v_snd_1148_ = lean_ctor_get(v_snd_1143_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_snd_1143_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1150_ = v_snd_1143_;
v_isShared_1151_ = v_isSharedCheck_1454_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_snd_1148_);
lean_inc(v_fst_1147_);
lean_dec(v_snd_1143_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1454_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
uint8_t v___x_1152_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; uint8_t v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; uint8_t v_skip_1171_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; uint8_t v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; uint8_t v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; uint8_t v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; uint8_t v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; uint8_t v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; uint8_t v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1417_; lean_object* v___y_1418_; lean_object* v___y_1450_; 
v___x_1152_ = 1;
if (v_symm_1069_ == 0)
{
lean_inc(v_fst_1147_);
v___y_1450_ = v_fst_1147_;
goto v___jp_1449_;
}
else
{
lean_inc(v_snd_1148_);
v___y_1450_ = v_snd_1148_;
goto v___jp_1449_;
}
v___jp_1153_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___f_1177_; lean_object* v___x_1178_; 
v___x_1172_ = lean_box(v_clearH_1067_);
v___x_1173_ = lean_box(v_skip_1171_);
v___x_1174_ = lean_box(v___x_1152_);
v___x_1175_ = lean_box(v_symm_1069_);
v___x_1176_ = lean_box(v___y_1167_);
v___f_1177_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 24, 19);
lean_closure_set(v___f_1177_, 0, v___y_1158_);
lean_closure_set(v___f_1177_, 1, v_hFVarId_1065_);
lean_closure_set(v___f_1177_, 2, v___y_1159_);
lean_closure_set(v___f_1177_, 3, v___y_1164_);
lean_closure_set(v___f_1177_, 4, v_fvarSubst_1068_);
lean_closure_set(v___f_1177_, 5, v___x_1172_);
lean_closure_set(v___f_1177_, 6, v___y_1154_);
lean_closure_set(v___f_1177_, 7, v___y_1160_);
lean_closure_set(v___f_1177_, 8, v___y_1155_);
lean_closure_set(v___f_1177_, 9, v___x_1173_);
lean_closure_set(v___f_1177_, 10, v___x_1174_);
lean_closure_set(v___f_1177_, 11, v___y_1166_);
lean_closure_set(v___f_1177_, 12, v___y_1156_);
lean_closure_set(v___f_1177_, 13, v___y_1162_);
lean_closure_set(v___f_1177_, 14, v___y_1168_);
lean_closure_set(v___f_1177_, 15, v_a_1115_);
lean_closure_set(v___f_1177_, 16, v___x_1175_);
lean_closure_set(v___f_1177_, 17, v___x_1176_);
lean_closure_set(v___f_1177_, 18, v___y_1169_);
v___x_1178_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v___y_1161_, v___f_1177_, v___y_1157_, v___y_1165_, v___y_1170_, v___y_1163_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1165_);
lean_dec_ref(v___y_1157_);
return v___x_1178_;
}
v___jp_1179_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_array_get(v___x_1066_, v___y_1190_, v___x_1196_);
lean_inc(v___x_1197_);
v___x_1198_ = l_Lean_mkFVar(v___x_1197_);
v___x_1199_ = lean_unsigned_to_nat(1u);
v___x_1200_ = lean_array_get(v___x_1066_, v___y_1190_, v___x_1199_);
lean_dec_ref(v___y_1190_);
lean_inc(v___x_1200_);
v___x_1201_ = l_Lean_mkFVar(v___x_1200_);
if (v_tryToSkip_1070_ == 0)
{
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1187_);
v___y_1154_ = v___x_1198_;
v___y_1155_ = v___y_1181_;
v___y_1156_ = v___y_1180_;
v___y_1157_ = v___y_1192_;
v___y_1158_ = v___y_1182_;
v___y_1159_ = v___x_1201_;
v___y_1160_ = v___y_1183_;
v___y_1161_ = v___y_1189_;
v___y_1162_ = v___x_1200_;
v___y_1163_ = v___y_1195_;
v___y_1164_ = v___y_1184_;
v___y_1165_ = v___y_1193_;
v___y_1166_ = v___y_1186_;
v___y_1167_ = v___y_1185_;
v___y_1168_ = v___x_1197_;
v___y_1169_ = v___x_1199_;
v___y_1170_ = v___y_1194_;
v_skip_1171_ = v___y_1188_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = lean_array_get_size(v___y_1191_);
lean_dec_ref(v___y_1191_);
v___x_1203_ = lean_nat_dec_eq(v___x_1202_, v___y_1187_);
lean_dec(v___y_1187_);
if (v___x_1203_ == 0)
{
v___y_1154_ = v___x_1198_;
v___y_1155_ = v___y_1181_;
v___y_1156_ = v___y_1180_;
v___y_1157_ = v___y_1192_;
v___y_1158_ = v___y_1182_;
v___y_1159_ = v___x_1201_;
v___y_1160_ = v___y_1183_;
v___y_1161_ = v___y_1189_;
v___y_1162_ = v___x_1200_;
v___y_1163_ = v___y_1195_;
v___y_1164_ = v___y_1184_;
v___y_1165_ = v___y_1193_;
v___y_1166_ = v___y_1186_;
v___y_1167_ = v___y_1185_;
v___y_1168_ = v___x_1197_;
v___y_1169_ = v___x_1199_;
v___y_1170_ = v___y_1194_;
v_skip_1171_ = v___y_1188_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1204_; 
lean_inc(v___y_1189_);
v___x_1204_ = l_Lean_MVarId_getType(v___y_1189_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1206_; lean_object* v_a_1207_; uint8_t v___x_1208_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc_n(v_a_1205_, 2);
lean_dec_ref_known(v___x_1204_, 1);
lean_inc(v___x_1197_);
v___x_1206_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1205_, v___x_1197_, v___y_1193_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1206_);
v___x_1208_ = lean_unbox(v_a_1207_);
lean_dec(v_a_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v_a_1210_; uint8_t v___x_1211_; 
lean_inc(v___x_1200_);
v___x_1209_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1205_, v___x_1200_, v___y_1193_);
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref(v___x_1209_);
v___x_1211_ = lean_unbox(v_a_1210_);
lean_dec(v_a_1210_);
if (v___x_1211_ == 0)
{
lean_dec_ref(v___x_1201_);
lean_dec_ref(v___x_1198_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec(v_a_1115_);
lean_dec(v_hFVarId_1065_);
v___y_1077_ = v___y_1192_;
v___y_1078_ = v___y_1189_;
v___y_1079_ = v___x_1197_;
v___y_1080_ = v___x_1200_;
v___y_1081_ = v___y_1195_;
v___y_1082_ = v___y_1194_;
v___y_1083_ = v___y_1193_;
goto v___jp_1076_;
}
else
{
v___y_1154_ = v___x_1198_;
v___y_1155_ = v___y_1181_;
v___y_1156_ = v___y_1180_;
v___y_1157_ = v___y_1192_;
v___y_1158_ = v___y_1182_;
v___y_1159_ = v___x_1201_;
v___y_1160_ = v___y_1183_;
v___y_1161_ = v___y_1189_;
v___y_1162_ = v___x_1200_;
v___y_1163_ = v___y_1195_;
v___y_1164_ = v___y_1184_;
v___y_1165_ = v___y_1193_;
v___y_1166_ = v___y_1186_;
v___y_1167_ = v___y_1185_;
v___y_1168_ = v___x_1197_;
v___y_1169_ = v___x_1199_;
v___y_1170_ = v___y_1194_;
v_skip_1171_ = v___y_1188_;
goto v___jp_1153_;
}
}
else
{
lean_dec(v_a_1205_);
v___y_1154_ = v___x_1198_;
v___y_1155_ = v___y_1181_;
v___y_1156_ = v___y_1180_;
v___y_1157_ = v___y_1192_;
v___y_1158_ = v___y_1182_;
v___y_1159_ = v___x_1201_;
v___y_1160_ = v___y_1183_;
v___y_1161_ = v___y_1189_;
v___y_1162_ = v___x_1200_;
v___y_1163_ = v___y_1195_;
v___y_1164_ = v___y_1184_;
v___y_1165_ = v___y_1193_;
v___y_1166_ = v___y_1186_;
v___y_1167_ = v___y_1185_;
v___y_1168_ = v___x_1197_;
v___y_1169_ = v___x_1199_;
v___y_1170_ = v___y_1194_;
v_skip_1171_ = v___y_1188_;
goto v___jp_1153_;
}
}
else
{
lean_object* v_a_1212_; lean_object* v___x_1214_; uint8_t v_isShared_1215_; uint8_t v_isSharedCheck_1219_; 
lean_dec_ref(v___x_1201_);
lean_dec(v___x_1200_);
lean_dec_ref(v___x_1198_);
lean_dec(v___x_1197_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1189_);
lean_dec(v___y_1186_);
lean_dec_ref(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1212_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1219_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1219_ == 0)
{
v___x_1214_ = v___x_1204_;
v_isShared_1215_ = v_isSharedCheck_1219_;
goto v_resetjp_1213_;
}
else
{
lean_inc(v_a_1212_);
lean_dec(v___x_1204_);
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
}
}
v___jp_1220_:
{
lean_object* v___x_1238_; 
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1237_);
lean_inc_ref(v___y_1236_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
v___x_1238_ = lean_apply_5(v___y_1230_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_, lean_box(0));
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; uint8_t v___x_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
lean_dec_ref_known(v___x_1238_, 1);
v___x_1240_ = lean_unbox(v_a_1239_);
lean_dec(v_a_1239_);
if (v___x_1240_ == 0)
{
lean_dec(v___y_1232_);
lean_del_object(v___x_1150_);
lean_inc(v___y_1223_);
v___y_1180_ = v___y_1223_;
v___y_1181_ = v___y_1222_;
v___y_1182_ = v___y_1224_;
v___y_1183_ = v___y_1225_;
v___y_1184_ = v___y_1226_;
v___y_1185_ = v___y_1228_;
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1229_;
v___y_1188_ = v___y_1231_;
v___y_1189_ = v___y_1223_;
v___y_1190_ = v___y_1221_;
v___y_1191_ = v___y_1233_;
v___y_1192_ = v___y_1234_;
v___y_1193_ = v___y_1235_;
v___y_1194_ = v___y_1236_;
v___y_1195_ = v___y_1237_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1241_; size_t v_sz_1242_; size_t v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1250_; 
v___x_1241_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__11, &l_Lean_Meta_substCore___lam__3___closed__11_once, _init_l_Lean_Meta_substCore___lam__3___closed__11);
v_sz_1242_ = lean_array_size(v___y_1233_);
v___x_1243_ = ((size_t)0ULL);
lean_inc_ref(v___y_1233_);
v___x_1244_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1242_, v___x_1243_, v___y_1233_);
v___x_1245_ = lean_array_to_list(v___x_1244_);
v___x_1246_ = lean_box(0);
v___x_1247_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(v___x_1245_, v___x_1246_);
v___x_1248_ = l_Lean_MessageData_ofList(v___x_1247_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 7);
lean_ctor_set(v___x_1150_, 1, v___x_1248_);
lean_ctor_set(v___x_1150_, 0, v___x_1241_);
v___x_1250_ = v___x_1150_;
goto v_reusejp_1249_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v___x_1241_);
lean_ctor_set(v_reuseFailAlloc_1260_, 1, v___x_1248_);
v___x_1250_ = v_reuseFailAlloc_1260_;
goto v_reusejp_1249_;
}
v_reusejp_1249_:
{
lean_object* v___x_1251_; 
v___x_1251_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1232_, v___x_1250_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1251_) == 0)
{
lean_dec_ref_known(v___x_1251_, 1);
lean_inc(v___y_1223_);
v___y_1180_ = v___y_1223_;
v___y_1181_ = v___y_1222_;
v___y_1182_ = v___y_1224_;
v___y_1183_ = v___y_1225_;
v___y_1184_ = v___y_1226_;
v___y_1185_ = v___y_1228_;
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1229_;
v___y_1188_ = v___y_1231_;
v___y_1189_ = v___y_1223_;
v___y_1190_ = v___y_1221_;
v___y_1191_ = v___y_1233_;
v___y_1192_ = v___y_1234_;
v___y_1193_ = v___y_1235_;
v___y_1194_ = v___y_1236_;
v___y_1195_ = v___y_1237_;
goto v___jp_1179_;
}
else
{
lean_object* v_a_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1259_; 
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1229_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1252_ = lean_ctor_get(v___x_1251_, 0);
v_isSharedCheck_1259_ = !lean_is_exclusive(v___x_1251_);
if (v_isSharedCheck_1259_ == 0)
{
v___x_1254_ = v___x_1251_;
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_a_1252_);
lean_dec(v___x_1251_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1259_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v___x_1257_; 
if (v_isShared_1255_ == 0)
{
v___x_1257_ = v___x_1254_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v_a_1252_);
v___x_1257_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
return v___x_1257_;
}
}
}
}
}
}
else
{
lean_object* v_a_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1268_; 
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec(v___y_1229_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1261_ = lean_ctor_get(v___x_1238_, 0);
v_isSharedCheck_1268_ = !lean_is_exclusive(v___x_1238_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1263_ = v___x_1238_;
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_a_1261_);
lean_dec(v___x_1238_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1268_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1266_; 
if (v_isShared_1264_ == 0)
{
v___x_1266_ = v___x_1263_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v_a_1261_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
v___jp_1269_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_box(0);
lean_inc(v___y_1276_);
v___x_1285_ = l_Lean_Meta_introNCore(v___y_1270_, v___y_1276_, v___x_1284_, v___y_1278_, v___x_1152_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1285_) == 0)
{
lean_object* v_a_1286_; lean_object* v_fst_1287_; lean_object* v_snd_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1317_; 
v_a_1286_ = lean_ctor_get(v___x_1285_, 0);
lean_inc(v_a_1286_);
lean_dec_ref_known(v___x_1285_, 1);
v_fst_1287_ = lean_ctor_get(v_a_1286_, 0);
v_snd_1288_ = lean_ctor_get(v_a_1286_, 1);
v_isSharedCheck_1317_ = !lean_is_exclusive(v_a_1286_);
if (v_isSharedCheck_1317_ == 0)
{
v___x_1290_ = v_a_1286_;
v_isShared_1291_ = v_isSharedCheck_1317_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_snd_1288_);
lean_inc(v_fst_1287_);
lean_dec(v_a_1286_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1317_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; 
lean_inc_ref(v___y_1277_);
lean_inc(v___y_1283_);
lean_inc_ref(v___y_1282_);
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
v___x_1292_ = lean_apply_5(v___y_1277_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, lean_box(0));
if (lean_obj_tag(v___x_1292_) == 0)
{
lean_object* v_a_1293_; uint8_t v___x_1294_; 
v_a_1293_ = lean_ctor_get(v___x_1292_, 0);
lean_inc(v_a_1293_);
lean_dec_ref_known(v___x_1292_, 1);
v___x_1294_ = lean_unbox(v_a_1293_);
lean_dec(v_a_1293_);
if (v___x_1294_ == 0)
{
lean_del_object(v___x_1290_);
lean_inc_ref(v___y_1273_);
v___y_1221_ = v_fst_1287_;
v___y_1222_ = v___x_1284_;
v___y_1223_ = v_snd_1288_;
v___y_1224_ = v___y_1271_;
v___y_1225_ = v___y_1272_;
v___y_1226_ = v___y_1273_;
v___y_1227_ = v___y_1274_;
v___y_1228_ = v___y_1275_;
v___y_1229_ = v___y_1276_;
v___y_1230_ = v___y_1277_;
v___y_1231_ = v___y_1278_;
v___y_1232_ = v___y_1279_;
v___y_1233_ = v___y_1273_;
v___y_1234_ = v___y_1280_;
v___y_1235_ = v___y_1281_;
v___y_1236_ = v___y_1282_;
v___y_1237_ = v___y_1283_;
goto v___jp_1220_;
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1295_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__13, &l_Lean_Meta_substCore___lam__3___closed__13_once, _init_l_Lean_Meta_substCore___lam__3___closed__13);
lean_inc(v_snd_1288_);
v___x_1296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1296_, 0, v_snd_1288_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set_tag(v___x_1290_, 7);
lean_ctor_set(v___x_1290_, 1, v___x_1296_);
lean_ctor_set(v___x_1290_, 0, v___x_1295_);
v___x_1298_ = v___x_1290_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v___x_1295_);
lean_ctor_set(v_reuseFailAlloc_1308_, 1, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
lean_object* v___x_1299_; 
lean_inc(v___y_1279_);
v___x_1299_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1279_, v___x_1298_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_dec_ref_known(v___x_1299_, 1);
lean_inc_ref(v___y_1273_);
v___y_1221_ = v_fst_1287_;
v___y_1222_ = v___x_1284_;
v___y_1223_ = v_snd_1288_;
v___y_1224_ = v___y_1271_;
v___y_1225_ = v___y_1272_;
v___y_1226_ = v___y_1273_;
v___y_1227_ = v___y_1274_;
v___y_1228_ = v___y_1275_;
v___y_1229_ = v___y_1276_;
v___y_1230_ = v___y_1277_;
v___y_1231_ = v___y_1278_;
v___y_1232_ = v___y_1279_;
v___y_1233_ = v___y_1273_;
v___y_1234_ = v___y_1280_;
v___y_1235_ = v___y_1281_;
v___y_1236_ = v___y_1282_;
v___y_1237_ = v___y_1283_;
goto v___jp_1220_;
}
else
{
lean_object* v_a_1300_; lean_object* v___x_1302_; uint8_t v_isShared_1303_; uint8_t v_isSharedCheck_1307_; 
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v___y_1276_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1300_ = lean_ctor_get(v___x_1299_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1299_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1302_ = v___x_1299_;
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
else
{
lean_inc(v_a_1300_);
lean_dec(v___x_1299_);
v___x_1302_ = lean_box(0);
v_isShared_1303_ = v_isSharedCheck_1307_;
goto v_resetjp_1301_;
}
v_resetjp_1301_:
{
lean_object* v___x_1305_; 
if (v_isShared_1303_ == 0)
{
v___x_1305_ = v___x_1302_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v_a_1300_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
}
}
else
{
lean_object* v_a_1309_; lean_object* v___x_1311_; uint8_t v_isShared_1312_; uint8_t v_isSharedCheck_1316_; 
lean_del_object(v___x_1290_);
lean_dec(v_snd_1288_);
lean_dec(v_fst_1287_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v___y_1276_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1309_ = lean_ctor_get(v___x_1292_, 0);
v_isSharedCheck_1316_ = !lean_is_exclusive(v___x_1292_);
if (v_isSharedCheck_1316_ == 0)
{
v___x_1311_ = v___x_1292_;
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
else
{
lean_inc(v_a_1309_);
lean_dec(v___x_1292_);
v___x_1311_ = lean_box(0);
v_isShared_1312_ = v_isSharedCheck_1316_;
goto v_resetjp_1310_;
}
v_resetjp_1310_:
{
lean_object* v___x_1314_; 
if (v_isShared_1312_ == 0)
{
v___x_1314_ = v___x_1311_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1315_; 
v_reuseFailAlloc_1315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1315_, 0, v_a_1309_);
v___x_1314_ = v_reuseFailAlloc_1315_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
return v___x_1314_;
}
}
}
}
}
else
{
lean_object* v_a_1318_; lean_object* v___x_1320_; uint8_t v_isShared_1321_; uint8_t v_isSharedCheck_1325_; 
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v___y_1276_);
lean_dec(v___y_1274_);
lean_dec_ref(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1318_ = lean_ctor_get(v___x_1285_, 0);
v_isSharedCheck_1325_ = !lean_is_exclusive(v___x_1285_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1320_ = v___x_1285_;
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
else
{
lean_inc(v_a_1318_);
lean_dec(v___x_1285_);
v___x_1320_ = lean_box(0);
v_isShared_1321_ = v_isSharedCheck_1325_;
goto v_resetjp_1319_;
}
v_resetjp_1319_:
{
lean_object* v___x_1323_; 
if (v_isShared_1321_ == 0)
{
v___x_1323_ = v___x_1320_;
goto v_reusejp_1322_;
}
else
{
lean_object* v_reuseFailAlloc_1324_; 
v_reuseFailAlloc_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1324_, 0, v_a_1318_);
v___x_1323_ = v_reuseFailAlloc_1324_;
goto v_reusejp_1322_;
}
v_reusejp_1322_:
{
return v___x_1323_;
}
}
}
}
v___jp_1326_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; 
v___x_1336_ = lean_unsigned_to_nat(2u);
v___x_1337_ = lean_mk_empty_array_with_capacity(v___x_1336_);
v___x_1338_ = lean_array_push(v___x_1337_, v___y_1329_);
lean_inc(v_hFVarId_1065_);
v___x_1339_ = lean_array_push(v___x_1338_, v_hFVarId_1065_);
v___x_1340_ = 0;
v___x_1341_ = l_Lean_MVarId_revert(v_mvarId_1064_, v___x_1339_, v___x_1152_, v___x_1340_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1341_) == 0)
{
lean_object* v_a_1342_; lean_object* v_fst_1343_; lean_object* v_snd_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1373_; 
v_a_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_a_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v_fst_1343_ = lean_ctor_get(v_a_1342_, 0);
v_snd_1344_ = lean_ctor_get(v_a_1342_, 1);
v_isSharedCheck_1373_ = !lean_is_exclusive(v_a_1342_);
if (v_isSharedCheck_1373_ == 0)
{
v___x_1346_ = v_a_1342_;
v_isShared_1347_ = v_isSharedCheck_1373_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_snd_1344_);
lean_inc(v_fst_1343_);
lean_dec(v_a_1342_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1373_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; 
lean_inc_ref(v___y_1330_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
v___x_1348_ = lean_apply_5(v___y_1330_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_, lean_box(0));
if (lean_obj_tag(v___x_1348_) == 0)
{
lean_object* v_a_1349_; uint8_t v___x_1350_; 
v_a_1349_ = lean_ctor_get(v___x_1348_, 0);
lean_inc(v_a_1349_);
lean_dec_ref_known(v___x_1348_, 1);
v___x_1350_ = lean_unbox(v_a_1349_);
lean_dec(v_a_1349_);
if (v___x_1350_ == 0)
{
lean_del_object(v___x_1346_);
v___y_1270_ = v_snd_1344_;
v___y_1271_ = v___y_1327_;
v___y_1272_ = v___x_1336_;
v___y_1273_ = v_fst_1343_;
v___y_1274_ = v___y_1328_;
v___y_1275_ = v___x_1340_;
v___y_1276_ = v___x_1336_;
v___y_1277_ = v___y_1330_;
v___y_1278_ = v___x_1340_;
v___y_1279_ = v___y_1331_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___y_1333_;
v___y_1282_ = v___y_1334_;
v___y_1283_ = v___y_1335_;
goto v___jp_1269_;
}
else
{
lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1351_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__15, &l_Lean_Meta_substCore___lam__3___closed__15_once, _init_l_Lean_Meta_substCore___lam__3___closed__15);
lean_inc(v_snd_1344_);
v___x_1352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1352_, 0, v_snd_1344_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set_tag(v___x_1346_, 7);
lean_ctor_set(v___x_1346_, 1, v___x_1352_);
lean_ctor_set(v___x_1346_, 0, v___x_1351_);
v___x_1354_ = v___x_1346_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1364_, 1, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1355_; 
lean_inc(v___y_1331_);
v___x_1355_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1331_, v___x_1354_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_dec_ref_known(v___x_1355_, 1);
v___y_1270_ = v_snd_1344_;
v___y_1271_ = v___y_1327_;
v___y_1272_ = v___x_1336_;
v___y_1273_ = v_fst_1343_;
v___y_1274_ = v___y_1328_;
v___y_1275_ = v___x_1340_;
v___y_1276_ = v___x_1336_;
v___y_1277_ = v___y_1330_;
v___y_1278_ = v___x_1340_;
v___y_1279_ = v___y_1331_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___y_1333_;
v___y_1282_ = v___y_1334_;
v___y_1283_ = v___y_1335_;
goto v___jp_1269_;
}
else
{
lean_object* v_a_1356_; lean_object* v___x_1358_; uint8_t v_isShared_1359_; uint8_t v_isSharedCheck_1363_; 
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec(v___y_1328_);
lean_dec(v___y_1327_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1356_ = lean_ctor_get(v___x_1355_, 0);
v_isSharedCheck_1363_ = !lean_is_exclusive(v___x_1355_);
if (v_isSharedCheck_1363_ == 0)
{
v___x_1358_ = v___x_1355_;
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
else
{
lean_inc(v_a_1356_);
lean_dec(v___x_1355_);
v___x_1358_ = lean_box(0);
v_isShared_1359_ = v_isSharedCheck_1363_;
goto v_resetjp_1357_;
}
v_resetjp_1357_:
{
lean_object* v___x_1361_; 
if (v_isShared_1359_ == 0)
{
v___x_1361_ = v___x_1358_;
goto v_reusejp_1360_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v_a_1356_);
v___x_1361_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1360_;
}
v_reusejp_1360_:
{
return v___x_1361_;
}
}
}
}
}
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
lean_del_object(v___x_1346_);
lean_dec(v_snd_1344_);
lean_dec(v_fst_1343_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec(v___y_1328_);
lean_dec(v___y_1327_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1365_ = lean_ctor_get(v___x_1348_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1348_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1348_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1348_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
else
{
lean_object* v_a_1374_; lean_object* v___x_1376_; uint8_t v_isShared_1377_; uint8_t v_isSharedCheck_1381_; 
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec(v___y_1328_);
lean_dec(v___y_1327_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1374_ = lean_ctor_get(v___x_1341_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1341_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1376_ = v___x_1341_;
v_isShared_1377_ = v_isSharedCheck_1381_;
goto v_resetjp_1375_;
}
else
{
lean_inc(v_a_1374_);
lean_dec(v___x_1341_);
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
v___jp_1382_:
{
lean_object* v___x_1392_; lean_object* v_a_1393_; uint8_t v___x_1394_; 
lean_inc(v___y_1383_);
lean_inc_ref(v___y_1386_);
v___x_1392_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v___y_1386_, v___y_1383_, v___y_1389_);
v_a_1393_ = lean_ctor_get(v___x_1392_, 0);
lean_inc(v_a_1393_);
lean_dec_ref(v___x_1392_);
v___x_1394_ = lean_unbox(v_a_1393_);
lean_dec(v_a_1393_);
if (v___x_1394_ == 0)
{
lean_dec_ref(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1141_);
lean_inc(v___y_1384_);
lean_inc(v___y_1383_);
v___y_1327_ = v___y_1383_;
v___y_1328_ = v___y_1384_;
v___y_1329_ = v___y_1383_;
v___y_1330_ = v___y_1385_;
v___y_1331_ = v___y_1384_;
v___y_1332_ = v___y_1388_;
v___y_1333_ = v___y_1389_;
v___y_1334_ = v___y_1390_;
v___y_1335_ = v___y_1391_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1398_; 
v___x_1395_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_1396_ = l_Lean_MessageData_ofExpr(v___y_1387_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 7);
lean_ctor_set(v___x_1145_, 1, v___x_1396_);
lean_ctor_set(v___x_1145_, 0, v___x_1395_);
v___x_1398_ = v___x_1145_;
goto v_reusejp_1397_;
}
else
{
lean_object* v_reuseFailAlloc_1415_; 
v_reuseFailAlloc_1415_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1415_, 0, v___x_1395_);
lean_ctor_set(v_reuseFailAlloc_1415_, 1, v___x_1396_);
v___x_1398_ = v_reuseFailAlloc_1415_;
goto v_reusejp_1397_;
}
v_reusejp_1397_:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1399_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__19, &l_Lean_Meta_substCore___lam__3___closed__19_once, _init_l_Lean_Meta_substCore___lam__3___closed__19);
v___x_1400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
v___x_1401_ = l_Lean_indentExpr(v___y_1386_);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1402_);
v___x_1404_ = v___x_1141_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; 
lean_inc(v_mvarId_1064_);
v___x_1405_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1116_, v_mvarId_1064_, v___x_1404_, v___y_1388_, v___y_1389_, v___y_1390_, v___y_1391_);
if (lean_obj_tag(v___x_1405_) == 0)
{
lean_dec_ref_known(v___x_1405_, 1);
lean_inc(v___y_1384_);
lean_inc(v___y_1383_);
v___y_1327_ = v___y_1383_;
v___y_1328_ = v___y_1384_;
v___y_1329_ = v___y_1383_;
v___y_1330_ = v___y_1385_;
v___y_1331_ = v___y_1384_;
v___y_1332_ = v___y_1388_;
v___y_1333_ = v___y_1389_;
v___y_1334_ = v___y_1390_;
v___y_1335_ = v___y_1391_;
goto v___jp_1326_;
}
else
{
lean_object* v_a_1406_; lean_object* v___x_1408_; uint8_t v_isShared_1409_; uint8_t v_isSharedCheck_1413_; 
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1384_);
lean_dec(v___y_1383_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1406_ = lean_ctor_get(v___x_1405_, 0);
v_isSharedCheck_1413_ = !lean_is_exclusive(v___x_1405_);
if (v_isSharedCheck_1413_ == 0)
{
v___x_1408_ = v___x_1405_;
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
else
{
lean_inc(v_a_1406_);
lean_dec(v___x_1405_);
v___x_1408_ = lean_box(0);
v_isShared_1409_ = v_isSharedCheck_1413_;
goto v_resetjp_1407_;
}
v_resetjp_1407_:
{
lean_object* v___x_1411_; 
if (v_isShared_1409_ == 0)
{
v___x_1411_ = v___x_1408_;
goto v_reusejp_1410_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v_a_1406_);
v___x_1411_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1410_;
}
v_reusejp_1410_:
{
return v___x_1411_;
}
}
}
}
}
}
}
v___jp_1416_:
{
lean_object* v___x_1419_; 
v___x_1419_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1418_, v___y_1072_);
if (lean_obj_tag(v___y_1417_) == 1)
{
lean_object* v_a_1420_; lean_object* v_fvarId_1421_; lean_object* v___x_1422_; lean_object* v___f_1423_; lean_object* v___x_1424_; lean_object* v_a_1425_; uint8_t v___x_1426_; 
lean_dec_ref(v___x_1120_);
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref(v___x_1419_);
v_fvarId_1421_ = lean_ctor_get(v___y_1417_, 0);
lean_inc(v_fvarId_1421_);
v___x_1422_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___f_1423_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__23));
v___x_1424_ = l_Lean_Meta_substCore___lam__2(v___x_1422_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
v_a_1425_ = lean_ctor_get(v___x_1424_, 0);
lean_inc(v_a_1425_);
lean_dec_ref(v___x_1424_);
v___x_1426_ = lean_unbox(v_a_1425_);
lean_dec(v_a_1425_);
if (v___x_1426_ == 0)
{
v___y_1383_ = v_fvarId_1421_;
v___y_1384_ = v___x_1422_;
v___y_1385_ = v___f_1423_;
v___y_1386_ = v_a_1420_;
v___y_1387_ = v___y_1417_;
v___y_1388_ = v___y_1071_;
v___y_1389_ = v___y_1072_;
v___y_1390_ = v___y_1073_;
v___y_1391_ = v___y_1074_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; 
v___x_1427_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__25, &l_Lean_Meta_substCore___lam__3___closed__25_once, _init_l_Lean_Meta_substCore___lam__3___closed__25);
lean_inc_ref(v___y_1417_);
v___x_1428_ = l_Lean_MessageData_ofExpr(v___y_1417_);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
v___x_1430_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__27, &l_Lean_Meta_substCore___lam__3___closed__27_once, _init_l_Lean_Meta_substCore___lam__3___closed__27);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
lean_inc(v_fvarId_1421_);
v___x_1432_ = l_Lean_MessageData_ofName(v_fvarId_1421_);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__29, &l_Lean_Meta_substCore___lam__3___closed__29_once, _init_l_Lean_Meta_substCore___lam__3___closed__29);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
lean_inc(v_a_1420_);
v___x_1436_ = l_Lean_MessageData_ofExpr(v_a_1420_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_1422_, v___x_1437_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1438_) == 0)
{
lean_dec_ref_known(v___x_1438_, 1);
v___y_1383_ = v_fvarId_1421_;
v___y_1384_ = v___x_1422_;
v___y_1385_ = v___f_1423_;
v___y_1386_ = v_a_1420_;
v___y_1387_ = v___y_1417_;
v___y_1388_ = v___y_1071_;
v___y_1389_ = v___y_1072_;
v___y_1390_ = v___y_1073_;
v___y_1391_ = v___y_1074_;
goto v___jp_1382_;
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_dec(v_fvarId_1421_);
lean_dec(v_a_1420_);
lean_dec_ref_known(v___y_1417_, 1);
lean_del_object(v___x_1150_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1115_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1439_ = lean_ctor_get(v___x_1438_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1438_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1438_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1438_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1419_);
lean_del_object(v___x_1150_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
if (v_symm_1069_ == 0)
{
lean_object* v___x_1447_; 
v___x_1447_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__30));
v___y_1122_ = v___y_1417_;
v___y_1123_ = v___x_1447_;
goto v___jp_1121_;
}
else
{
lean_object* v___x_1448_; 
v___x_1448_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__31));
v___y_1122_ = v___y_1417_;
v___y_1123_ = v___x_1448_;
goto v___jp_1121_;
}
}
}
v___jp_1449_:
{
lean_object* v___x_1451_; 
v___x_1451_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1450_, v___y_1072_);
if (v_symm_1069_ == 0)
{
lean_object* v_a_1452_; 
lean_dec(v_fst_1147_);
v_a_1452_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1452_);
lean_dec_ref(v___x_1451_);
v___y_1417_ = v_a_1452_;
v___y_1418_ = v_snd_1148_;
goto v___jp_1416_;
}
else
{
lean_object* v_a_1453_; 
lean_dec(v_snd_1148_);
v_a_1453_ = lean_ctor_get(v___x_1451_, 0);
lean_inc(v_a_1453_);
lean_dec_ref(v___x_1451_);
v___y_1417_ = v_a_1453_;
v___y_1418_ = v_fst_1147_;
goto v___jp_1416_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1458_; lean_object* v___x_1460_; uint8_t v_isShared_1461_; uint8_t v_isSharedCheck_1465_; 
lean_dec_ref(v___x_1120_);
lean_dec(v_a_1115_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1458_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1460_ = v___x_1135_;
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
else
{
lean_inc(v_a_1458_);
lean_dec(v___x_1135_);
v___x_1460_ = lean_box(0);
v_isShared_1461_ = v_isSharedCheck_1465_;
goto v_resetjp_1459_;
}
v_resetjp_1459_:
{
lean_object* v___x_1463_; 
if (v_isShared_1461_ == 0)
{
v___x_1463_ = v___x_1460_;
goto v_reusejp_1462_;
}
else
{
lean_object* v_reuseFailAlloc_1464_; 
v_reuseFailAlloc_1464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1464_, 0, v_a_1458_);
v___x_1463_ = v_reuseFailAlloc_1464_;
goto v_reusejp_1462_;
}
v_reusejp_1462_:
{
return v___x_1463_;
}
}
}
v___jp_1121_:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1124_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__3, &l_Lean_Meta_substCore___lam__3___closed__3_once, _init_l_Lean_Meta_substCore___lam__3___closed__3);
lean_inc_ref(v___y_1123_);
v___x_1125_ = l_Lean_stringToMessageData(v___y_1123_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = l_Lean_indentExpr(v___x_1120_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__5, &l_Lean_Meta_substCore___lam__3___closed__5_once, _init_l_Lean_Meta_substCore___lam__3___closed__5);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = l_Lean_indentExpr(v___y_1122_);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1132_);
v___x_1134_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1116_, v_mvarId_1064_, v___x_1133_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
return v___x_1134_;
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec(v_a_1115_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1466_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1118_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1118_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1471_; 
if (v_isShared_1469_ == 0)
{
v___x_1471_ = v___x_1468_;
goto v_reusejp_1470_;
}
else
{
lean_object* v_reuseFailAlloc_1472_; 
v_reuseFailAlloc_1472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1472_, 0, v_a_1466_);
v___x_1471_ = v_reuseFailAlloc_1472_;
goto v_reusejp_1470_;
}
v_reusejp_1470_:
{
return v___x_1471_;
}
}
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec(v_a_1115_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1474_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1117_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1117_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1479_; 
if (v_isShared_1477_ == 0)
{
v___x_1479_ = v___x_1476_;
goto v_reusejp_1478_;
}
else
{
lean_object* v_reuseFailAlloc_1480_; 
v_reuseFailAlloc_1480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1480_, 0, v_a_1474_);
v___x_1479_ = v_reuseFailAlloc_1480_;
goto v_reusejp_1478_;
}
v_reusejp_1478_:
{
return v___x_1479_;
}
}
}
}
else
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1482_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1114_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1114_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
v___jp_1076_:
{
if (v_clearH_1067_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1077_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_fvarSubst_1068_);
lean_ctor_set(v___x_1084_, 1, v___y_1078_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_MVarId_clear(v___y_1078_, v___y_1080_, v___y_1077_, v___y_1083_, v___y_1082_, v___y_1081_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = l_Lean_MVarId_clear(v_a_1087_, v___y_1079_, v___y_1077_, v___y_1083_, v___y_1082_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1077_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1091_; uint8_t v_isShared_1092_; uint8_t v_isSharedCheck_1097_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1097_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1097_ == 0)
{
v___x_1091_ = v___x_1088_;
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
else
{
lean_inc(v_a_1089_);
lean_dec(v___x_1088_);
v___x_1091_ = lean_box(0);
v_isShared_1092_ = v_isSharedCheck_1097_;
goto v_resetjp_1090_;
}
v_resetjp_1090_:
{
lean_object* v___x_1093_; lean_object* v___x_1095_; 
v___x_1093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1093_, 0, v_fvarSubst_1068_);
lean_ctor_set(v___x_1093_, 1, v_a_1089_);
if (v_isShared_1092_ == 0)
{
lean_ctor_set(v___x_1091_, 0, v___x_1093_);
v___x_1095_ = v___x_1091_;
goto v_reusejp_1094_;
}
else
{
lean_object* v_reuseFailAlloc_1096_; 
v_reuseFailAlloc_1096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1096_, 0, v___x_1093_);
v___x_1095_ = v_reuseFailAlloc_1096_;
goto v_reusejp_1094_;
}
v_reusejp_1094_:
{
return v___x_1095_;
}
}
}
else
{
lean_object* v_a_1098_; lean_object* v___x_1100_; uint8_t v_isShared_1101_; uint8_t v_isSharedCheck_1105_; 
lean_dec(v_fvarSubst_1068_);
v_a_1098_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1105_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1105_ == 0)
{
v___x_1100_ = v___x_1088_;
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
else
{
lean_inc(v_a_1098_);
lean_dec(v___x_1088_);
v___x_1100_ = lean_box(0);
v_isShared_1101_ = v_isSharedCheck_1105_;
goto v_resetjp_1099_;
}
v_resetjp_1099_:
{
lean_object* v___x_1103_; 
if (v_isShared_1101_ == 0)
{
v___x_1103_ = v___x_1100_;
goto v_reusejp_1102_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_a_1098_);
v___x_1103_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1102_;
}
v_reusejp_1102_:
{
return v___x_1103_;
}
}
}
}
else
{
lean_object* v_a_1106_; lean_object* v___x_1108_; uint8_t v_isShared_1109_; uint8_t v_isSharedCheck_1113_; 
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1077_);
lean_dec(v_fvarSubst_1068_);
v_a_1106_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1113_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1113_ == 0)
{
v___x_1108_ = v___x_1086_;
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
else
{
lean_inc(v_a_1106_);
lean_dec(v___x_1086_);
v___x_1108_ = lean_box(0);
v_isShared_1109_ = v_isSharedCheck_1113_;
goto v_resetjp_1107_;
}
v_resetjp_1107_:
{
lean_object* v___x_1111_; 
if (v_isShared_1109_ == 0)
{
v___x_1111_ = v___x_1108_;
goto v_reusejp_1110_;
}
else
{
lean_object* v_reuseFailAlloc_1112_; 
v_reuseFailAlloc_1112_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_a_1106_);
v___x_1111_ = v_reuseFailAlloc_1112_;
goto v_reusejp_1110_;
}
v_reusejp_1110_:
{
return v___x_1111_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3___boxed(lean_object* v_mvarId_1490_, lean_object* v_hFVarId_1491_, lean_object* v___x_1492_, lean_object* v_clearH_1493_, lean_object* v_fvarSubst_1494_, lean_object* v_symm_1495_, lean_object* v_tryToSkip_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_){
_start:
{
uint8_t v_clearH_boxed_1502_; uint8_t v_symm_boxed_1503_; uint8_t v_tryToSkip_boxed_1504_; lean_object* v_res_1505_; 
v_clearH_boxed_1502_ = lean_unbox(v_clearH_1493_);
v_symm_boxed_1503_ = lean_unbox(v_symm_1495_);
v_tryToSkip_boxed_1504_ = lean_unbox(v_tryToSkip_1496_);
v_res_1505_ = l_Lean_Meta_substCore___lam__3(v_mvarId_1490_, v_hFVarId_1491_, v___x_1492_, v_clearH_boxed_1502_, v_fvarSubst_1494_, v_symm_boxed_1503_, v_tryToSkip_boxed_1504_, v___y_1497_, v___y_1498_, v___y_1499_, v___y_1500_);
lean_dec(v___x_1492_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object* v_mvarId_1506_, lean_object* v_hFVarId_1507_, uint8_t v_symm_1508_, lean_object* v_fvarSubst_1509_, uint8_t v_clearH_1510_, uint8_t v_tryToSkip_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_){
_start:
{
lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___f_1521_; lean_object* v___x_1522_; 
v___x_1517_ = lean_box(0);
v___x_1518_ = lean_box(v_clearH_1510_);
v___x_1519_ = lean_box(v_symm_1508_);
v___x_1520_ = lean_box(v_tryToSkip_1511_);
lean_inc(v_mvarId_1506_);
v___f_1521_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__3___boxed), 12, 7);
lean_closure_set(v___f_1521_, 0, v_mvarId_1506_);
lean_closure_set(v___f_1521_, 1, v_hFVarId_1507_);
lean_closure_set(v___f_1521_, 2, v___x_1517_);
lean_closure_set(v___f_1521_, 3, v___x_1518_);
lean_closure_set(v___f_1521_, 4, v_fvarSubst_1509_);
lean_closure_set(v___f_1521_, 5, v___x_1519_);
lean_closure_set(v___f_1521_, 6, v___x_1520_);
v___x_1522_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1506_, v___f_1521_, v_a_1512_, v_a_1513_, v_a_1514_, v_a_1515_);
return v___x_1522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* v_mvarId_1523_, lean_object* v_hFVarId_1524_, lean_object* v_symm_1525_, lean_object* v_fvarSubst_1526_, lean_object* v_clearH_1527_, lean_object* v_tryToSkip_1528_, lean_object* v_a_1529_, lean_object* v_a_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_){
_start:
{
uint8_t v_symm_boxed_1534_; uint8_t v_clearH_boxed_1535_; uint8_t v_tryToSkip_boxed_1536_; lean_object* v_res_1537_; 
v_symm_boxed_1534_ = lean_unbox(v_symm_1525_);
v_clearH_boxed_1535_ = lean_unbox(v_clearH_1527_);
v_tryToSkip_boxed_1536_ = lean_unbox(v_tryToSkip_1528_);
v_res_1537_ = l_Lean_Meta_substCore(v_mvarId_1523_, v_hFVarId_1524_, v_symm_boxed_1534_, v_fvarSubst_1526_, v_clearH_boxed_1535_, v_tryToSkip_boxed_1536_, v_a_1529_, v_a_1530_, v_a_1531_, v_a_1532_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
return v_res_1537_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1(lean_object* v_fst_1538_, lean_object* v_fst_1539_, lean_object* v_n_1540_, lean_object* v_i_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_){
_start:
{
lean_object* v___x_1549_; 
v___x_1549_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_1538_, v_fst_1539_, v_n_1540_, v_i_1541_, v_a_1543_);
return v___x_1549_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___boxed(lean_object* v_fst_1550_, lean_object* v_fst_1551_, lean_object* v_n_1552_, lean_object* v_i_1553_, lean_object* v_a_1554_, lean_object* v_a_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_){
_start:
{
lean_object* v_res_1561_; 
v_res_1561_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1(v_fst_1550_, v_fst_1551_, v_n_1552_, v_i_1553_, v_a_1554_, v_a_1555_, v___y_1556_, v___y_1557_, v___y_1558_, v___y_1559_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v___y_1557_);
lean_dec_ref(v___y_1556_);
lean_dec(v_n_1552_);
lean_dec_ref(v_fst_1551_);
lean_dec_ref(v_fst_1550_);
return v_res_1561_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4(lean_object* v_mvarId_1562_, lean_object* v_val_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_){
_start:
{
lean_object* v___x_1569_; 
v___x_1569_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_mvarId_1562_, v_val_1563_, v___y_1565_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___boxed(lean_object* v_mvarId_1570_, lean_object* v_val_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_){
_start:
{
lean_object* v_res_1577_; 
v_res_1577_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4(v_mvarId_1570_, v_val_1571_, v___y_1572_, v___y_1573_, v___y_1574_, v___y_1575_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
return v_res_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7(lean_object* v_00_u03b1_1578_, lean_object* v_name_1579_, uint8_t v_bi_1580_, lean_object* v_type_1581_, lean_object* v_k_1582_, uint8_t v_kind_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_){
_start:
{
lean_object* v___x_1589_; 
v___x_1589_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_1579_, v_bi_1580_, v_type_1581_, v_k_1582_, v_kind_1583_, v___y_1584_, v___y_1585_, v___y_1586_, v___y_1587_);
return v___x_1589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1590_, lean_object* v_name_1591_, lean_object* v_bi_1592_, lean_object* v_type_1593_, lean_object* v_k_1594_, lean_object* v_kind_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_){
_start:
{
uint8_t v_bi_boxed_1601_; uint8_t v_kind_boxed_1602_; lean_object* v_res_1603_; 
v_bi_boxed_1601_ = lean_unbox(v_bi_1592_);
v_kind_boxed_1602_ = lean_unbox(v_kind_1595_);
v_res_1603_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7(v_00_u03b1_1590_, v_name_1591_, v_bi_boxed_1601_, v_type_1593_, v_k_1594_, v_kind_boxed_1602_, v___y_1596_, v___y_1597_, v___y_1598_, v___y_1599_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
return v_res_1603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5(lean_object* v_00_u03b1_1604_, lean_object* v_name_1605_, lean_object* v_type_1606_, lean_object* v_k_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_){
_start:
{
lean_object* v___x_1613_; 
v___x_1613_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v_name_1605_, v_type_1606_, v_k_1607_, v___y_1608_, v___y_1609_, v___y_1610_, v___y_1611_);
return v___x_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___boxed(lean_object* v_00_u03b1_1614_, lean_object* v_name_1615_, lean_object* v_type_1616_, lean_object* v_k_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_){
_start:
{
lean_object* v_res_1623_; 
v_res_1623_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5(v_00_u03b1_1614_, v_name_1615_, v_type_1616_, v_k_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
return v_res_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5(lean_object* v_00_u03b2_1624_, lean_object* v_x_1625_, lean_object* v_x_1626_, lean_object* v_x_1627_){
_start:
{
lean_object* v___x_1628_; 
v___x_1628_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5___redArg(v_x_1625_, v_x_1626_, v_x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_1629_, lean_object* v_x_1630_, size_t v_x_1631_, size_t v_x_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_){
_start:
{
lean_object* v___x_1635_; 
v___x_1635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_1630_, v_x_1631_, v_x_1632_, v_x_1633_, v_x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_){
_start:
{
size_t v_x_29609__boxed_1642_; size_t v_x_29610__boxed_1643_; lean_object* v_res_1644_; 
v_x_29609__boxed_1642_ = lean_unbox_usize(v_x_1638_);
lean_dec(v_x_1638_);
v_x_29610__boxed_1643_ = lean_unbox_usize(v_x_1639_);
lean_dec(v_x_1639_);
v_res_1644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8(v_00_u03b2_1636_, v_x_1637_, v_x_29609__boxed_1642_, v_x_29610__boxed_1643_, v_x_1640_, v_x_1641_);
return v_res_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13(lean_object* v_00_u03b2_1645_, lean_object* v_n_1646_, lean_object* v_k_1647_, lean_object* v_v_1648_){
_start:
{
lean_object* v___x_1649_; 
v___x_1649_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13___redArg(v_n_1646_, v_k_1647_, v_v_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1650_, size_t v_depth_1651_, lean_object* v_keys_1652_, lean_object* v_vals_1653_, lean_object* v_heq_1654_, lean_object* v_i_1655_, lean_object* v_entries_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(v_depth_1651_, v_keys_1652_, v_vals_1653_, v_i_1655_, v_entries_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1658_, lean_object* v_depth_1659_, lean_object* v_keys_1660_, lean_object* v_vals_1661_, lean_object* v_heq_1662_, lean_object* v_i_1663_, lean_object* v_entries_1664_){
_start:
{
size_t v_depth_boxed_1665_; lean_object* v_res_1666_; 
v_depth_boxed_1665_ = lean_unbox_usize(v_depth_1659_);
lean_dec(v_depth_1659_);
v_res_1666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14(v_00_u03b2_1658_, v_depth_boxed_1665_, v_keys_1660_, v_vals_1661_, v_heq_1662_, v_i_1663_, v_entries_1664_);
lean_dec_ref(v_vals_1661_);
lean_dec_ref(v_keys_1660_);
return v_res_1666_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_){
_start:
{
lean_object* v___x_1672_; 
v___x_1672_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14___redArg(v_x_1668_, v_x_1669_, v_x_1670_, v_x_1671_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* v_fvarId_1676_, lean_object* v_mvarId_1677_, uint8_t v_tryToClear_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_){
_start:
{
lean_object* v___x_1684_; 
lean_inc(v_fvarId_1676_);
v___x_1684_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1676_, v___y_1679_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1684_) == 0)
{
lean_object* v_a_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_a_1685_ = lean_ctor_get(v___x_1684_, 0);
lean_inc(v_a_1685_);
lean_dec_ref_known(v___x_1684_, 1);
v___x_1686_ = l_Lean_LocalDecl_type(v_a_1685_);
lean_inc(v___y_1682_);
lean_inc_ref(v___y_1681_);
lean_inc(v___y_1680_);
lean_inc_ref(v___y_1679_);
v___x_1687_ = lean_whnf(v___x_1686_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1687_) == 0)
{
lean_object* v_a_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1772_; 
v_a_1688_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1690_ = v___x_1687_;
v_isShared_1691_ = v_isSharedCheck_1772_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_a_1688_);
lean_dec(v___x_1687_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1772_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1692_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_1693_ = lean_unsigned_to_nat(4u);
v___x_1694_ = l_Lean_Expr_isAppOfArity(v_a_1688_, v___x_1692_, v___x_1693_);
if (v___x_1694_ == 0)
{
lean_object* v___x_1695_; lean_object* v___x_1697_; 
lean_dec(v_a_1688_);
lean_dec(v_a_1685_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
v___x_1695_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1695_, 0, v_fvarId_1676_);
lean_ctor_set(v___x_1695_, 1, v_mvarId_1677_);
if (v_isShared_1691_ == 0)
{
lean_ctor_set(v___x_1690_, 0, v___x_1695_);
v___x_1697_ = v___x_1690_;
goto v_reusejp_1696_;
}
else
{
lean_object* v_reuseFailAlloc_1698_; 
v_reuseFailAlloc_1698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1698_, 0, v___x_1695_);
v___x_1697_ = v_reuseFailAlloc_1698_;
goto v_reusejp_1696_;
}
v_reusejp_1696_:
{
return v___x_1697_;
}
}
else
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_del_object(v___x_1690_);
v___x_1699_ = l_Lean_Expr_appFn_x21(v_a_1688_);
v___x_1700_ = l_Lean_Expr_appFn_x21(v___x_1699_);
v___x_1701_ = l_Lean_Expr_appFn_x21(v___x_1700_);
v___x_1702_ = l_Lean_Expr_appArg_x21(v___x_1701_);
lean_dec_ref(v___x_1701_);
v___x_1703_ = l_Lean_Expr_appArg_x21(v___x_1700_);
lean_dec_ref(v___x_1700_);
v___x_1704_ = l_Lean_Expr_appArg_x21(v___x_1699_);
lean_dec_ref(v___x_1699_);
v___x_1705_ = l_Lean_Expr_appArg_x21(v_a_1688_);
lean_dec(v_a_1688_);
v___x_1706_ = l_Lean_Meta_isExprDefEq(v___x_1702_, v___x_1704_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1763_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1763_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1763_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1763_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1763_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
uint8_t v___x_1711_; 
v___x_1711_ = lean_unbox(v_a_1707_);
if (v___x_1711_ == 0)
{
lean_object* v___x_1712_; lean_object* v___x_1714_; 
lean_dec(v_a_1707_);
lean_dec_ref(v___x_1705_);
lean_dec_ref(v___x_1703_);
lean_dec(v_a_1685_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_fvarId_1676_);
lean_ctor_set(v___x_1712_, 1, v_mvarId_1677_);
if (v_isShared_1710_ == 0)
{
lean_ctor_set(v___x_1709_, 0, v___x_1712_);
v___x_1714_ = v___x_1709_;
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
else
{
lean_object* v___x_1716_; lean_object* v___x_1717_; 
lean_del_object(v___x_1709_);
lean_inc(v_fvarId_1676_);
v___x_1716_ = l_Lean_mkFVar(v_fvarId_1676_);
v___x_1717_ = l_Lean_Meta_mkEqOfHEq(v___x_1716_, v___x_1694_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = l_Lean_Meta_mkEq(v___x_1703_, v___x_1705_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = l_Lean_LocalDecl_userName(v_a_1685_);
lean_dec(v_a_1685_);
v___x_1722_ = l_Lean_MVarId_assert(v_mvarId_1677_, v___x_1721_, v_a_1720_, v_a_1718_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1722_) == 0)
{
if (v_tryToClear_1678_ == 0)
{
lean_object* v_a_1723_; uint8_t v___x_1724_; lean_object* v___x_1725_; 
lean_dec(v_fvarId_1676_);
v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1723_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1724_ = lean_unbox(v_a_1707_);
lean_dec(v_a_1707_);
v___x_1725_ = l_Lean_Meta_intro1Core(v_a_1723_, v___x_1724_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
return v___x_1725_;
}
else
{
lean_object* v_a_1726_; lean_object* v___x_1727_; 
v_a_1726_ = lean_ctor_get(v___x_1722_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1722_, 1);
v___x_1727_ = l_Lean_MVarId_tryClear(v_a_1726_, v_fvarId_1676_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; uint8_t v___x_1729_; lean_object* v___x_1730_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1727_, 1);
v___x_1729_ = lean_unbox(v_a_1707_);
lean_dec(v_a_1707_);
v___x_1730_ = l_Lean_Meta_intro1Core(v_a_1728_, v___x_1729_, v___y_1679_, v___y_1680_, v___y_1681_, v___y_1682_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
return v___x_1730_;
}
else
{
lean_object* v_a_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1738_; 
lean_dec(v_a_1707_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
v_a_1731_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1738_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1738_ == 0)
{
v___x_1733_ = v___x_1727_;
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_a_1731_);
lean_dec(v___x_1727_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1738_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
lean_object* v___x_1736_; 
if (v_isShared_1734_ == 0)
{
v___x_1736_ = v___x_1733_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1737_; 
v_reuseFailAlloc_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1737_, 0, v_a_1731_);
v___x_1736_ = v_reuseFailAlloc_1737_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
return v___x_1736_;
}
}
}
}
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_a_1707_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_fvarId_1676_);
v_a_1739_ = lean_ctor_get(v___x_1722_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1722_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1722_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1722_);
v___x_1741_ = lean_box(0);
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
v_resetjp_1740_:
{
lean_object* v___x_1744_; 
if (v_isShared_1742_ == 0)
{
v___x_1744_ = v___x_1741_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v_a_1739_);
v___x_1744_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
return v___x_1744_;
}
}
}
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_a_1718_);
lean_dec(v_a_1707_);
lean_dec(v_a_1685_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_mvarId_1677_);
lean_dec(v_fvarId_1676_);
v_a_1747_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1719_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1719_);
v___x_1749_ = lean_box(0);
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
v_resetjp_1748_:
{
lean_object* v___x_1752_; 
if (v_isShared_1750_ == 0)
{
v___x_1752_ = v___x_1749_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v_a_1747_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
return v___x_1752_;
}
}
}
}
else
{
lean_object* v_a_1755_; lean_object* v___x_1757_; uint8_t v_isShared_1758_; uint8_t v_isSharedCheck_1762_; 
lean_dec(v_a_1707_);
lean_dec_ref(v___x_1705_);
lean_dec_ref(v___x_1703_);
lean_dec(v_a_1685_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_mvarId_1677_);
lean_dec(v_fvarId_1676_);
v_a_1755_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1717_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1717_);
v___x_1757_ = lean_box(0);
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
v_resetjp_1756_:
{
lean_object* v___x_1760_; 
if (v_isShared_1758_ == 0)
{
v___x_1760_ = v___x_1757_;
goto v_reusejp_1759_;
}
else
{
lean_object* v_reuseFailAlloc_1761_; 
v_reuseFailAlloc_1761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1761_, 0, v_a_1755_);
v___x_1760_ = v_reuseFailAlloc_1761_;
goto v_reusejp_1759_;
}
v_reusejp_1759_:
{
return v___x_1760_;
}
}
}
}
}
}
else
{
lean_object* v_a_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1771_; 
lean_dec_ref(v___x_1705_);
lean_dec_ref(v___x_1703_);
lean_dec(v_a_1685_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_mvarId_1677_);
lean_dec(v_fvarId_1676_);
v_a_1764_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1766_ = v___x_1706_;
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
else
{
lean_inc(v_a_1764_);
lean_dec(v___x_1706_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1771_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1769_; 
if (v_isShared_1767_ == 0)
{
v___x_1769_ = v___x_1766_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v_a_1764_);
v___x_1769_ = v_reuseFailAlloc_1770_;
goto v_reusejp_1768_;
}
v_reusejp_1768_:
{
return v___x_1769_;
}
}
}
}
}
}
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_a_1685_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_mvarId_1677_);
lean_dec(v_fvarId_1676_);
v_a_1773_ = lean_ctor_get(v___x_1687_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1687_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1687_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1687_);
v___x_1775_ = lean_box(0);
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
v_resetjp_1774_:
{
lean_object* v___x_1778_; 
if (v_isShared_1776_ == 0)
{
v___x_1778_ = v___x_1775_;
goto v_reusejp_1777_;
}
else
{
lean_object* v_reuseFailAlloc_1779_; 
v_reuseFailAlloc_1779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1779_, 0, v_a_1773_);
v___x_1778_ = v_reuseFailAlloc_1779_;
goto v_reusejp_1777_;
}
v_reusejp_1777_:
{
return v___x_1778_;
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v_mvarId_1677_);
lean_dec(v_fvarId_1676_);
v_a_1781_ = lean_ctor_get(v___x_1684_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1684_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1684_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1684_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object* v_fvarId_1789_, lean_object* v_mvarId_1790_, lean_object* v_tryToClear_1791_, lean_object* v___y_1792_, lean_object* v___y_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_){
_start:
{
uint8_t v_tryToClear_boxed_1797_; lean_object* v_res_1798_; 
v_tryToClear_boxed_1797_ = lean_unbox(v_tryToClear_1791_);
v_res_1798_ = l_Lean_Meta_heqToEq___lam__0(v_fvarId_1789_, v_mvarId_1790_, v_tryToClear_boxed_1797_, v___y_1792_, v___y_1793_, v___y_1794_, v___y_1795_);
return v_res_1798_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object* v_mvarId_1799_, lean_object* v_fvarId_1800_, uint8_t v_tryToClear_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_){
_start:
{
lean_object* v___x_1807_; lean_object* v___f_1808_; lean_object* v___x_1809_; 
v___x_1807_ = lean_box(v_tryToClear_1801_);
lean_inc(v_mvarId_1799_);
v___f_1808_ = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1808_, 0, v_fvarId_1800_);
lean_closure_set(v___f_1808_, 1, v_mvarId_1799_);
lean_closure_set(v___f_1808_, 2, v___x_1807_);
v___x_1809_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1799_, v___f_1808_, v_a_1802_, v_a_1803_, v_a_1804_, v_a_1805_);
return v___x_1809_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* v_mvarId_1810_, lean_object* v_fvarId_1811_, lean_object* v_tryToClear_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_){
_start:
{
uint8_t v_tryToClear_boxed_1818_; lean_object* v_res_1819_; 
v_tryToClear_boxed_1818_ = lean_unbox(v_tryToClear_1812_);
v_res_1819_ = l_Lean_Meta_heqToEq(v_mvarId_1810_, v_fvarId_1811_, v_tryToClear_boxed_1818_, v_a_1813_, v_a_1814_, v_a_1815_, v_a_1816_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1823_, lean_object* v_as_1824_, size_t v_sz_1825_, size_t v_i_1826_, lean_object* v_b_1827_, lean_object* v___y_1828_, lean_object* v___y_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_){
_start:
{
lean_object* v_a_1834_; uint8_t v___x_1838_; 
v___x_1838_ = lean_usize_dec_lt(v_i_1826_, v_sz_1825_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; 
lean_dec(v_x_1823_);
v___x_1839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1839_, 0, v_b_1827_);
return v___x_1839_;
}
else
{
lean_object* v___x_1840_; lean_object* v_a_1842_; lean_object* v___x_1846_; lean_object* v_a_1847_; 
lean_dec_ref(v_b_1827_);
v___x_1840_ = lean_box(0);
v___x_1846_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1847_ = lean_array_uget(v_as_1824_, v_i_1826_);
if (lean_obj_tag(v_a_1847_) == 0)
{
v_a_1834_ = v___x_1846_;
goto v___jp_1833_;
}
else
{
lean_object* v_val_1848_; lean_object* v___x_1850_; uint8_t v_isShared_1851_; uint8_t v_isSharedCheck_1947_; 
v_val_1848_ = lean_ctor_get(v_a_1847_, 0);
v_isSharedCheck_1947_ = !lean_is_exclusive(v_a_1847_);
if (v_isSharedCheck_1947_ == 0)
{
v___x_1850_ = v_a_1847_;
v_isShared_1851_ = v_isSharedCheck_1947_;
goto v_resetjp_1849_;
}
else
{
lean_inc(v_val_1848_);
lean_dec(v_a_1847_);
v___x_1850_ = lean_box(0);
v_isShared_1851_ = v_isSharedCheck_1947_;
goto v_resetjp_1849_;
}
v_resetjp_1849_:
{
uint8_t v___x_1852_; 
v___x_1852_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1848_);
if (v___x_1852_ == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = l_Lean_LocalDecl_type(v_val_1848_);
v___x_1854_ = l_Lean_Meta_matchEq_x3f(v___x_1853_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
if (lean_obj_tag(v_a_1855_) == 1)
{
lean_object* v_val_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1938_; 
v_val_1856_ = lean_ctor_get(v_a_1855_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v_a_1855_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1858_ = v_a_1855_;
v_isShared_1859_ = v_isSharedCheck_1938_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_val_1856_);
lean_dec(v_a_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1938_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v_snd_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1936_; 
v_snd_1860_ = lean_ctor_get(v_val_1856_, 1);
v_isSharedCheck_1936_ = !lean_is_exclusive(v_val_1856_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v_val_1856_, 0);
lean_dec(v_unused_1937_);
v___x_1862_ = v_val_1856_;
v_isShared_1863_ = v_isSharedCheck_1936_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_snd_1860_);
lean_dec(v_val_1856_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1936_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v_fst_1864_; lean_object* v_snd_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1935_; 
v_fst_1864_ = lean_ctor_get(v_snd_1860_, 0);
v_snd_1865_ = lean_ctor_get(v_snd_1860_, 1);
v_isSharedCheck_1935_ = !lean_is_exclusive(v_snd_1860_);
if (v_isSharedCheck_1935_ == 0)
{
v___x_1867_ = v_snd_1860_;
v_isShared_1868_ = v_isSharedCheck_1935_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_snd_1865_);
lean_inc(v_fst_1864_);
lean_dec(v_snd_1860_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1935_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1864_, v___y_1829_);
if (lean_obj_tag(v___x_1869_) == 0)
{
lean_object* v_a_1870_; lean_object* v___x_1871_; 
v_a_1870_ = lean_ctor_get(v___x_1869_, 0);
lean_inc(v_a_1870_);
lean_dec_ref_known(v___x_1869_, 1);
v___x_1871_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1865_, v___y_1829_);
if (lean_obj_tag(v___x_1871_) == 0)
{
lean_object* v_a_1872_; lean_object* v___y_1874_; uint8_t v___x_1897_; 
v_a_1872_ = lean_ctor_get(v___x_1871_, 0);
lean_inc(v_a_1872_);
lean_dec_ref_known(v___x_1871_, 1);
v___x_1897_ = l_Lean_Expr_isFVar(v_a_1872_);
if (v___x_1897_ == 0)
{
lean_del_object(v___x_1862_);
lean_del_object(v___x_1850_);
v___y_1874_ = v___y_1829_;
goto v___jp_1873_;
}
else
{
lean_object* v___x_1898_; uint8_t v___x_1899_; 
v___x_1898_ = l_Lean_Expr_fvarId_x21(v_a_1872_);
v___x_1899_ = l_Lean_instBEqFVarId_beq(v___x_1898_, v_x_1823_);
lean_dec(v___x_1898_);
if (v___x_1899_ == 0)
{
lean_del_object(v___x_1862_);
lean_del_object(v___x_1850_);
v___y_1874_ = v___y_1829_;
goto v___jp_1873_;
}
else
{
lean_object* v___x_1900_; 
lean_inc(v_x_1823_);
lean_inc(v_a_1870_);
v___x_1900_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1870_, v_x_1823_, v___y_1829_);
if (lean_obj_tag(v___x_1900_) == 0)
{
lean_object* v_a_1901_; uint8_t v___x_1902_; 
v_a_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_a_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v___x_1902_ = lean_unbox(v_a_1901_);
lean_dec(v_a_1901_);
if (v___x_1902_ == 0)
{
lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1906_; 
lean_dec(v_a_1872_);
lean_dec(v_a_1870_);
lean_del_object(v___x_1867_);
lean_del_object(v___x_1858_);
lean_dec(v_x_1823_);
v___x_1903_ = l_Lean_LocalDecl_fvarId(v_val_1848_);
lean_dec(v_val_1848_);
v___x_1904_ = lean_box(v___x_1838_);
if (v_isShared_1863_ == 0)
{
lean_ctor_set(v___x_1862_, 1, v___x_1904_);
lean_ctor_set(v___x_1862_, 0, v___x_1903_);
v___x_1906_ = v___x_1862_;
goto v_reusejp_1905_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1903_);
lean_ctor_set(v_reuseFailAlloc_1910_, 1, v___x_1904_);
v___x_1906_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1905_;
}
v_reusejp_1905_:
{
lean_object* v___x_1908_; 
if (v_isShared_1851_ == 0)
{
lean_ctor_set(v___x_1850_, 0, v___x_1906_);
v___x_1908_ = v___x_1850_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v___x_1906_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
v_a_1842_ = v___x_1908_;
goto v___jp_1841_;
}
}
}
else
{
lean_del_object(v___x_1862_);
lean_del_object(v___x_1850_);
v___y_1874_ = v___y_1829_;
goto v___jp_1873_;
}
}
else
{
lean_object* v_a_1911_; lean_object* v___x_1913_; uint8_t v_isShared_1914_; uint8_t v_isSharedCheck_1918_; 
lean_dec(v_a_1872_);
lean_dec(v_a_1870_);
lean_del_object(v___x_1867_);
lean_del_object(v___x_1862_);
lean_del_object(v___x_1858_);
lean_del_object(v___x_1850_);
lean_dec(v_val_1848_);
lean_dec(v_x_1823_);
v_a_1911_ = lean_ctor_get(v___x_1900_, 0);
v_isSharedCheck_1918_ = !lean_is_exclusive(v___x_1900_);
if (v_isSharedCheck_1918_ == 0)
{
v___x_1913_ = v___x_1900_;
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
else
{
lean_inc(v_a_1911_);
lean_dec(v___x_1900_);
v___x_1913_ = lean_box(0);
v_isShared_1914_ = v_isSharedCheck_1918_;
goto v_resetjp_1912_;
}
v_resetjp_1912_:
{
lean_object* v___x_1916_; 
if (v_isShared_1914_ == 0)
{
v___x_1916_ = v___x_1913_;
goto v_reusejp_1915_;
}
else
{
lean_object* v_reuseFailAlloc_1917_; 
v_reuseFailAlloc_1917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1917_, 0, v_a_1911_);
v___x_1916_ = v_reuseFailAlloc_1917_;
goto v_reusejp_1915_;
}
v_reusejp_1915_:
{
return v___x_1916_;
}
}
}
}
}
v___jp_1873_:
{
uint8_t v___x_1875_; 
v___x_1875_ = l_Lean_Expr_isFVar(v_a_1870_);
if (v___x_1875_ == 0)
{
lean_dec(v_a_1872_);
lean_dec(v_a_1870_);
lean_del_object(v___x_1867_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1848_);
v_a_1834_ = v___x_1846_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1876_; uint8_t v___x_1877_; 
v___x_1876_ = l_Lean_Expr_fvarId_x21(v_a_1870_);
lean_dec(v_a_1870_);
v___x_1877_ = l_Lean_instBEqFVarId_beq(v___x_1876_, v_x_1823_);
lean_dec(v___x_1876_);
if (v___x_1877_ == 0)
{
lean_dec(v_a_1872_);
lean_del_object(v___x_1867_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1848_);
v_a_1834_ = v___x_1846_;
goto v___jp_1833_;
}
else
{
lean_object* v___x_1878_; 
lean_inc(v_x_1823_);
v___x_1878_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1872_, v_x_1823_, v___y_1874_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; uint8_t v___x_1880_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
v___x_1880_ = lean_unbox(v_a_1879_);
lean_dec(v_a_1879_);
if (v___x_1880_ == 0)
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1884_; 
lean_dec(v_x_1823_);
v___x_1881_ = l_Lean_LocalDecl_fvarId(v_val_1848_);
lean_dec(v_val_1848_);
v___x_1882_ = lean_box(v___x_1852_);
if (v_isShared_1868_ == 0)
{
lean_ctor_set(v___x_1867_, 1, v___x_1882_);
lean_ctor_set(v___x_1867_, 0, v___x_1881_);
v___x_1884_ = v___x_1867_;
goto v_reusejp_1883_;
}
else
{
lean_object* v_reuseFailAlloc_1888_; 
v_reuseFailAlloc_1888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1881_);
lean_ctor_set(v_reuseFailAlloc_1888_, 1, v___x_1882_);
v___x_1884_ = v_reuseFailAlloc_1888_;
goto v_reusejp_1883_;
}
v_reusejp_1883_:
{
lean_object* v___x_1886_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1884_);
v___x_1886_ = v___x_1858_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v___x_1884_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
v_a_1842_ = v___x_1886_;
goto v___jp_1841_;
}
}
}
else
{
lean_del_object(v___x_1867_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1848_);
v_a_1834_ = v___x_1846_;
goto v___jp_1833_;
}
}
else
{
lean_object* v_a_1889_; lean_object* v___x_1891_; uint8_t v_isShared_1892_; uint8_t v_isSharedCheck_1896_; 
lean_del_object(v___x_1867_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1848_);
lean_dec(v_x_1823_);
v_a_1889_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1896_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1896_ == 0)
{
v___x_1891_ = v___x_1878_;
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
else
{
lean_inc(v_a_1889_);
lean_dec(v___x_1878_);
v___x_1891_ = lean_box(0);
v_isShared_1892_ = v_isSharedCheck_1896_;
goto v_resetjp_1890_;
}
v_resetjp_1890_:
{
lean_object* v___x_1894_; 
if (v_isShared_1892_ == 0)
{
v___x_1894_ = v___x_1891_;
goto v_reusejp_1893_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v_a_1889_);
v___x_1894_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1893_;
}
v_reusejp_1893_:
{
return v___x_1894_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v_a_1870_);
lean_del_object(v___x_1867_);
lean_del_object(v___x_1862_);
lean_del_object(v___x_1858_);
lean_del_object(v___x_1850_);
lean_dec(v_val_1848_);
lean_dec(v_x_1823_);
v_a_1919_ = lean_ctor_get(v___x_1871_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1871_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1871_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1871_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1924_; 
if (v_isShared_1922_ == 0)
{
v___x_1924_ = v___x_1921_;
goto v_reusejp_1923_;
}
else
{
lean_object* v_reuseFailAlloc_1925_; 
v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1919_);
v___x_1924_ = v_reuseFailAlloc_1925_;
goto v_reusejp_1923_;
}
v_reusejp_1923_:
{
return v___x_1924_;
}
}
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
lean_del_object(v___x_1867_);
lean_dec(v_snd_1865_);
lean_del_object(v___x_1862_);
lean_del_object(v___x_1858_);
lean_del_object(v___x_1850_);
lean_dec(v_val_1848_);
lean_dec(v_x_1823_);
v_a_1927_ = lean_ctor_get(v___x_1869_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1869_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1869_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1869_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1855_);
lean_del_object(v___x_1850_);
lean_dec(v_val_1848_);
v_a_1834_ = v___x_1846_;
goto v___jp_1833_;
}
}
else
{
lean_object* v_a_1939_; lean_object* v___x_1941_; uint8_t v_isShared_1942_; uint8_t v_isSharedCheck_1946_; 
lean_del_object(v___x_1850_);
lean_dec(v_val_1848_);
lean_dec(v_x_1823_);
v_a_1939_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1946_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1946_ == 0)
{
v___x_1941_ = v___x_1854_;
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
else
{
lean_inc(v_a_1939_);
lean_dec(v___x_1854_);
v___x_1941_ = lean_box(0);
v_isShared_1942_ = v_isSharedCheck_1946_;
goto v_resetjp_1940_;
}
v_resetjp_1940_:
{
lean_object* v___x_1944_; 
if (v_isShared_1942_ == 0)
{
v___x_1944_ = v___x_1941_;
goto v_reusejp_1943_;
}
else
{
lean_object* v_reuseFailAlloc_1945_; 
v_reuseFailAlloc_1945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1945_, 0, v_a_1939_);
v___x_1944_ = v_reuseFailAlloc_1945_;
goto v_reusejp_1943_;
}
v_reusejp_1943_:
{
return v___x_1944_;
}
}
}
}
else
{
lean_del_object(v___x_1850_);
lean_dec(v_val_1848_);
v_a_1834_ = v___x_1846_;
goto v___jp_1833_;
}
}
}
v___jp_1841_:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_a_1842_);
v___x_1844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v___x_1840_);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
return v___x_1845_;
}
}
v___jp_1833_:
{
size_t v___x_1835_; size_t v___x_1836_; 
v___x_1835_ = ((size_t)1ULL);
v___x_1836_ = lean_usize_add(v_i_1826_, v___x_1835_);
lean_inc_ref(v_a_1834_);
v_i_1826_ = v___x_1836_;
v_b_1827_ = v_a_1834_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1948_, lean_object* v_as_1949_, lean_object* v_sz_1950_, lean_object* v_i_1951_, lean_object* v_b_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_){
_start:
{
size_t v_sz_boxed_1958_; size_t v_i_boxed_1959_; lean_object* v_res_1960_; 
v_sz_boxed_1958_ = lean_unbox_usize(v_sz_1950_);
lean_dec(v_sz_1950_);
v_i_boxed_1959_ = lean_unbox_usize(v_i_1951_);
lean_dec(v_i_1951_);
v_res_1960_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1948_, v_as_1949_, v_sz_boxed_1958_, v_i_boxed_1959_, v_b_1952_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
lean_dec(v___y_1956_);
lean_dec_ref(v___y_1955_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec_ref(v_as_1949_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object* v_x_1961_, lean_object* v_as_1962_, size_t v_sz_1963_, size_t v_i_1964_, lean_object* v_b_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_){
_start:
{
lean_object* v_a_1972_; uint8_t v___x_1976_; 
v___x_1976_ = lean_usize_dec_lt(v_i_1964_, v_sz_1963_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; 
lean_dec(v_x_1961_);
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_b_1965_);
return v___x_1977_;
}
else
{
lean_object* v___x_1978_; lean_object* v_a_1980_; lean_object* v___x_1984_; lean_object* v_a_1985_; 
lean_dec_ref(v_b_1965_);
v___x_1978_ = lean_box(0);
v___x_1984_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1985_ = lean_array_uget(v_as_1962_, v_i_1964_);
if (lean_obj_tag(v_a_1985_) == 0)
{
v_a_1972_ = v___x_1984_;
goto v___jp_1971_;
}
else
{
lean_object* v_val_1986_; lean_object* v___x_1988_; uint8_t v_isShared_1989_; uint8_t v_isSharedCheck_2085_; 
v_val_1986_ = lean_ctor_get(v_a_1985_, 0);
v_isSharedCheck_2085_ = !lean_is_exclusive(v_a_1985_);
if (v_isSharedCheck_2085_ == 0)
{
v___x_1988_ = v_a_1985_;
v_isShared_1989_ = v_isSharedCheck_2085_;
goto v_resetjp_1987_;
}
else
{
lean_inc(v_val_1986_);
lean_dec(v_a_1985_);
v___x_1988_ = lean_box(0);
v_isShared_1989_ = v_isSharedCheck_2085_;
goto v_resetjp_1987_;
}
v_resetjp_1987_:
{
uint8_t v___x_1990_; 
v___x_1990_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1986_);
if (v___x_1990_ == 0)
{
lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1991_ = l_Lean_LocalDecl_type(v_val_1986_);
v___x_1992_ = l_Lean_Meta_matchEq_x3f(v___x_1991_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
if (lean_obj_tag(v___x_1992_) == 0)
{
lean_object* v_a_1993_; 
v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
lean_inc(v_a_1993_);
lean_dec_ref_known(v___x_1992_, 1);
if (lean_obj_tag(v_a_1993_) == 1)
{
lean_object* v_val_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2076_; 
v_val_1994_ = lean_ctor_get(v_a_1993_, 0);
v_isSharedCheck_2076_ = !lean_is_exclusive(v_a_1993_);
if (v_isSharedCheck_2076_ == 0)
{
v___x_1996_ = v_a_1993_;
v_isShared_1997_ = v_isSharedCheck_2076_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_val_1994_);
lean_dec(v_a_1993_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2076_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v_snd_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2074_; 
v_snd_1998_ = lean_ctor_get(v_val_1994_, 1);
v_isSharedCheck_2074_ = !lean_is_exclusive(v_val_1994_);
if (v_isSharedCheck_2074_ == 0)
{
lean_object* v_unused_2075_; 
v_unused_2075_ = lean_ctor_get(v_val_1994_, 0);
lean_dec(v_unused_2075_);
v___x_2000_ = v_val_1994_;
v_isShared_2001_ = v_isSharedCheck_2074_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_snd_1998_);
lean_dec(v_val_1994_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2074_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2005_; uint8_t v_isShared_2006_; uint8_t v_isSharedCheck_2073_; 
v_fst_2002_ = lean_ctor_get(v_snd_1998_, 0);
v_snd_2003_ = lean_ctor_get(v_snd_1998_, 1);
v_isSharedCheck_2073_ = !lean_is_exclusive(v_snd_1998_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2005_ = v_snd_1998_;
v_isShared_2006_ = v_isSharedCheck_2073_;
goto v_resetjp_2004_;
}
else
{
lean_inc(v_snd_2003_);
lean_inc(v_fst_2002_);
lean_dec(v_snd_1998_);
v___x_2005_ = lean_box(0);
v_isShared_2006_ = v_isSharedCheck_2073_;
goto v_resetjp_2004_;
}
v_resetjp_2004_:
{
lean_object* v___x_2007_; 
v___x_2007_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_2002_, v___y_1967_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_2003_, v___y_1967_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___y_2012_; uint8_t v___x_2035_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2035_ = l_Lean_Expr_isFVar(v_a_2010_);
if (v___x_2035_ == 0)
{
lean_del_object(v___x_2000_);
lean_del_object(v___x_1988_);
v___y_2012_ = v___y_1967_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = l_Lean_Expr_fvarId_x21(v_a_2010_);
v___x_2037_ = l_Lean_instBEqFVarId_beq(v___x_2036_, v_x_1961_);
lean_dec(v___x_2036_);
if (v___x_2037_ == 0)
{
lean_del_object(v___x_2000_);
lean_del_object(v___x_1988_);
v___y_2012_ = v___y_1967_;
goto v___jp_2011_;
}
else
{
lean_object* v___x_2038_; 
lean_inc(v_x_1961_);
lean_inc(v_a_2008_);
v___x_2038_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_2008_, v_x_1961_, v___y_1967_);
if (lean_obj_tag(v___x_2038_) == 0)
{
lean_object* v_a_2039_; uint8_t v___x_2040_; 
v_a_2039_ = lean_ctor_get(v___x_2038_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2038_, 1);
v___x_2040_ = lean_unbox(v_a_2039_);
lean_dec(v_a_2039_);
if (v___x_2040_ == 0)
{
lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2044_; 
lean_dec(v_a_2010_);
lean_dec(v_a_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1996_);
lean_dec(v_x_1961_);
v___x_2041_ = l_Lean_LocalDecl_fvarId(v_val_1986_);
lean_dec(v_val_1986_);
v___x_2042_ = lean_box(v___x_1976_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v___x_2042_);
lean_ctor_set(v___x_2000_, 0, v___x_2041_);
v___x_2044_ = v___x_2000_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2048_, 1, v___x_2042_);
v___x_2044_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2046_; 
if (v_isShared_1989_ == 0)
{
lean_ctor_set(v___x_1988_, 0, v___x_2044_);
v___x_2046_ = v___x_1988_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v___x_2044_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
v_a_1980_ = v___x_2046_;
goto v___jp_1979_;
}
}
}
else
{
lean_del_object(v___x_2000_);
lean_del_object(v___x_1988_);
v___y_2012_ = v___y_1967_;
goto v___jp_2011_;
}
}
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_a_2010_);
lean_dec(v_a_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_2000_);
lean_del_object(v___x_1996_);
lean_del_object(v___x_1988_);
lean_dec(v_val_1986_);
lean_dec(v_x_1961_);
v_a_2049_ = lean_ctor_get(v___x_2038_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2038_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2038_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2038_);
v___x_2051_ = lean_box(0);
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
v_resetjp_2050_:
{
lean_object* v___x_2054_; 
if (v_isShared_2052_ == 0)
{
v___x_2054_ = v___x_2051_;
goto v_reusejp_2053_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_a_2049_);
v___x_2054_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2053_;
}
v_reusejp_2053_:
{
return v___x_2054_;
}
}
}
}
}
v___jp_2011_:
{
uint8_t v___x_2013_; 
v___x_2013_ = l_Lean_Expr_isFVar(v_a_2008_);
if (v___x_2013_ == 0)
{
lean_dec(v_a_2010_);
lean_dec(v_a_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1996_);
lean_dec(v_val_1986_);
v_a_1972_ = v___x_1984_;
goto v___jp_1971_;
}
else
{
lean_object* v___x_2014_; uint8_t v___x_2015_; 
v___x_2014_ = l_Lean_Expr_fvarId_x21(v_a_2008_);
lean_dec(v_a_2008_);
v___x_2015_ = l_Lean_instBEqFVarId_beq(v___x_2014_, v_x_1961_);
lean_dec(v___x_2014_);
if (v___x_2015_ == 0)
{
lean_dec(v_a_2010_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_1996_);
lean_dec(v_val_1986_);
v_a_1972_ = v___x_1984_;
goto v___jp_1971_;
}
else
{
lean_object* v___x_2016_; 
lean_inc(v_x_1961_);
v___x_2016_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_2010_, v_x_1961_, v___y_2012_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; uint8_t v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
v___x_2018_ = lean_unbox(v_a_2017_);
lean_dec(v_a_2017_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2022_; 
lean_dec(v_x_1961_);
v___x_2019_ = l_Lean_LocalDecl_fvarId(v_val_1986_);
lean_dec(v_val_1986_);
v___x_2020_ = lean_box(v___x_1990_);
if (v_isShared_2006_ == 0)
{
lean_ctor_set(v___x_2005_, 1, v___x_2020_);
lean_ctor_set(v___x_2005_, 0, v___x_2019_);
v___x_2022_ = v___x_2005_;
goto v_reusejp_2021_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2019_);
lean_ctor_set(v_reuseFailAlloc_2026_, 1, v___x_2020_);
v___x_2022_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2021_;
}
v_reusejp_2021_:
{
lean_object* v___x_2024_; 
if (v_isShared_1997_ == 0)
{
lean_ctor_set(v___x_1996_, 0, v___x_2022_);
v___x_2024_ = v___x_1996_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2025_; 
v_reuseFailAlloc_2025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2025_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2025_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
v_a_1980_ = v___x_2024_;
goto v___jp_1979_;
}
}
}
else
{
lean_del_object(v___x_2005_);
lean_del_object(v___x_1996_);
lean_dec(v_val_1986_);
v_a_1972_ = v___x_1984_;
goto v___jp_1971_;
}
}
else
{
lean_object* v_a_2027_; lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2034_; 
lean_del_object(v___x_2005_);
lean_del_object(v___x_1996_);
lean_dec(v_val_1986_);
lean_dec(v_x_1961_);
v_a_2027_ = lean_ctor_get(v___x_2016_, 0);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2016_);
if (v_isSharedCheck_2034_ == 0)
{
v___x_2029_ = v___x_2016_;
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
else
{
lean_inc(v_a_2027_);
lean_dec(v___x_2016_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2034_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2032_; 
if (v_isShared_2030_ == 0)
{
v___x_2032_ = v___x_2029_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_a_2027_);
v___x_2032_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
return v___x_2032_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_dec(v_a_2008_);
lean_del_object(v___x_2005_);
lean_del_object(v___x_2000_);
lean_del_object(v___x_1996_);
lean_del_object(v___x_1988_);
lean_dec(v_val_1986_);
lean_dec(v_x_1961_);
v_a_2057_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_2009_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_2009_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2060_ == 0)
{
v___x_2062_ = v___x_2059_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2063_; 
v_reuseFailAlloc_2063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_a_2057_);
v___x_2062_ = v_reuseFailAlloc_2063_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
return v___x_2062_;
}
}
}
}
else
{
lean_object* v_a_2065_; lean_object* v___x_2067_; uint8_t v_isShared_2068_; uint8_t v_isSharedCheck_2072_; 
lean_del_object(v___x_2005_);
lean_dec(v_snd_2003_);
lean_del_object(v___x_2000_);
lean_del_object(v___x_1996_);
lean_del_object(v___x_1988_);
lean_dec(v_val_1986_);
lean_dec(v_x_1961_);
v_a_2065_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2067_ = v___x_2007_;
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
else
{
lean_inc(v_a_2065_);
lean_dec(v___x_2007_);
v___x_2067_ = lean_box(0);
v_isShared_2068_ = v_isSharedCheck_2072_;
goto v_resetjp_2066_;
}
v_resetjp_2066_:
{
lean_object* v___x_2070_; 
if (v_isShared_2068_ == 0)
{
v___x_2070_ = v___x_2067_;
goto v_reusejp_2069_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
v___x_2070_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2069_;
}
v_reusejp_2069_:
{
return v___x_2070_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1993_);
lean_del_object(v___x_1988_);
lean_dec(v_val_1986_);
v_a_1972_ = v___x_1984_;
goto v___jp_1971_;
}
}
else
{
lean_object* v_a_2077_; lean_object* v___x_2079_; uint8_t v_isShared_2080_; uint8_t v_isSharedCheck_2084_; 
lean_del_object(v___x_1988_);
lean_dec(v_val_1986_);
lean_dec(v_x_1961_);
v_a_2077_ = lean_ctor_get(v___x_1992_, 0);
v_isSharedCheck_2084_ = !lean_is_exclusive(v___x_1992_);
if (v_isSharedCheck_2084_ == 0)
{
v___x_2079_ = v___x_1992_;
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
else
{
lean_inc(v_a_2077_);
lean_dec(v___x_1992_);
v___x_2079_ = lean_box(0);
v_isShared_2080_ = v_isSharedCheck_2084_;
goto v_resetjp_2078_;
}
v_resetjp_2078_:
{
lean_object* v___x_2082_; 
if (v_isShared_2080_ == 0)
{
v___x_2082_ = v___x_2079_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2083_; 
v_reuseFailAlloc_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2083_, 0, v_a_2077_);
v___x_2082_ = v_reuseFailAlloc_2083_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
return v___x_2082_;
}
}
}
}
else
{
lean_del_object(v___x_1988_);
lean_dec(v_val_1986_);
v_a_1972_ = v___x_1984_;
goto v___jp_1971_;
}
}
}
v___jp_1979_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1981_, 0, v_a_1980_);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1981_);
lean_ctor_set(v___x_1982_, 1, v___x_1978_);
v___x_1983_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1982_);
return v___x_1983_;
}
}
v___jp_1971_:
{
size_t v___x_1973_; size_t v___x_1974_; lean_object* v___x_1975_; 
v___x_1973_ = ((size_t)1ULL);
v___x_1974_ = lean_usize_add(v_i_1964_, v___x_1973_);
lean_inc_ref(v_a_1972_);
v___x_1975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1961_, v_as_1962_, v_sz_1963_, v___x_1974_, v_a_1972_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_);
return v___x_1975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2086_, lean_object* v_as_2087_, lean_object* v_sz_2088_, lean_object* v_i_2089_, lean_object* v_b_2090_, lean_object* v___y_2091_, lean_object* v___y_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_){
_start:
{
size_t v_sz_boxed_2096_; size_t v_i_boxed_2097_; lean_object* v_res_2098_; 
v_sz_boxed_2096_ = lean_unbox_usize(v_sz_2088_);
lean_dec(v_sz_2088_);
v_i_boxed_2097_ = lean_unbox_usize(v_i_2089_);
lean_dec(v_i_2089_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2086_, v_as_2087_, v_sz_boxed_2096_, v_i_boxed_2097_, v_b_2090_, v___y_2091_, v___y_2092_, v___y_2093_, v___y_2094_);
lean_dec(v___y_2094_);
lean_dec_ref(v___y_2093_);
lean_dec(v___y_2092_);
lean_dec_ref(v___y_2091_);
lean_dec_ref(v_as_2087_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object* v_x_2099_, lean_object* v_x_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_, lean_object* v___y_2103_, lean_object* v___y_2104_){
_start:
{
if (lean_obj_tag(v_x_2100_) == 0)
{
lean_object* v_cs_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; size_t v_sz_2109_; size_t v___x_2110_; lean_object* v___x_2111_; 
v_cs_2106_ = lean_ctor_get(v_x_2100_, 0);
v___x_2107_ = lean_box(0);
v___x_2108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2109_ = lean_array_size(v_cs_2106_);
v___x_2110_ = ((size_t)0ULL);
v___x_2111_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2099_, v_cs_2106_, v_sz_2109_, v___x_2110_, v___x_2108_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2124_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2124_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2124_ == 0)
{
v___x_2114_ = v___x_2111_;
v_isShared_2115_ = v_isSharedCheck_2124_;
goto v_resetjp_2113_;
}
else
{
lean_inc(v_a_2112_);
lean_dec(v___x_2111_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2124_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v_fst_2116_; 
v_fst_2116_ = lean_ctor_get(v_a_2112_, 0);
lean_inc(v_fst_2116_);
lean_dec(v_a_2112_);
if (lean_obj_tag(v_fst_2116_) == 0)
{
lean_object* v___x_2118_; 
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2107_);
v___x_2118_ = v___x_2114_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2107_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
else
{
lean_object* v_val_2120_; lean_object* v___x_2122_; 
v_val_2120_ = lean_ctor_get(v_fst_2116_, 0);
lean_inc(v_val_2120_);
lean_dec_ref_known(v_fst_2116_, 1);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v_val_2120_);
v___x_2122_ = v___x_2114_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2123_; 
v_reuseFailAlloc_2123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2123_, 0, v_val_2120_);
v___x_2122_ = v_reuseFailAlloc_2123_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
return v___x_2122_;
}
}
}
}
else
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2132_; 
v_a_2125_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2132_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2132_ == 0)
{
v___x_2127_ = v___x_2111_;
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2111_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2132_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v___x_2130_; 
if (v_isShared_2128_ == 0)
{
v___x_2130_ = v___x_2127_;
goto v_reusejp_2129_;
}
else
{
lean_object* v_reuseFailAlloc_2131_; 
v_reuseFailAlloc_2131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2131_, 0, v_a_2125_);
v___x_2130_ = v_reuseFailAlloc_2131_;
goto v_reusejp_2129_;
}
v_reusejp_2129_:
{
return v___x_2130_;
}
}
}
}
else
{
lean_object* v_vs_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; size_t v_sz_2136_; size_t v___x_2137_; lean_object* v___x_2138_; 
v_vs_2133_ = lean_ctor_get(v_x_2100_, 0);
v___x_2134_ = lean_box(0);
v___x_2135_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2136_ = lean_array_size(v_vs_2133_);
v___x_2137_ = ((size_t)0ULL);
v___x_2138_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2099_, v_vs_2133_, v_sz_2136_, v___x_2137_, v___x_2135_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_);
if (lean_obj_tag(v___x_2138_) == 0)
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2151_; 
v_a_2139_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2141_ = v___x_2138_;
v_isShared_2142_ = v_isSharedCheck_2151_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2138_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2151_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v_fst_2143_; 
v_fst_2143_ = lean_ctor_get(v_a_2139_, 0);
lean_inc(v_fst_2143_);
lean_dec(v_a_2139_);
if (lean_obj_tag(v_fst_2143_) == 0)
{
lean_object* v___x_2145_; 
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v___x_2134_);
v___x_2145_ = v___x_2141_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v___x_2134_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
else
{
lean_object* v_val_2147_; lean_object* v___x_2149_; 
v_val_2147_ = lean_ctor_get(v_fst_2143_, 0);
lean_inc(v_val_2147_);
lean_dec_ref_known(v_fst_2143_, 1);
if (v_isShared_2142_ == 0)
{
lean_ctor_set(v___x_2141_, 0, v_val_2147_);
v___x_2149_ = v___x_2141_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_val_2147_);
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
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
v_a_2152_ = lean_ctor_get(v___x_2138_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2138_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2138_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2138_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2160_, lean_object* v_as_2161_, size_t v_sz_2162_, size_t v_i_2163_, lean_object* v_b_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_, lean_object* v___y_2168_){
_start:
{
uint8_t v___x_2170_; 
v___x_2170_ = lean_usize_dec_lt(v_i_2163_, v_sz_2162_);
if (v___x_2170_ == 0)
{
lean_object* v___x_2171_; 
lean_dec(v_x_2160_);
v___x_2171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2171_, 0, v_b_2164_);
return v___x_2171_;
}
else
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v_a_2174_; lean_object* v___x_2175_; 
lean_dec_ref(v_b_2164_);
v___x_2172_ = lean_box(0);
v___x_2173_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_2174_ = lean_array_uget_borrowed(v_as_2161_, v_i_2163_);
lean_inc(v_x_2160_);
v___x_2175_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2160_, v_a_2174_, v___y_2165_, v___y_2166_, v___y_2167_, v___y_2168_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2188_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2188_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2188_ == 0)
{
v___x_2178_ = v___x_2175_;
v_isShared_2179_ = v_isSharedCheck_2188_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_a_2176_);
lean_dec(v___x_2175_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2188_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
if (lean_obj_tag(v_a_2176_) == 1)
{
lean_object* v___x_2180_; lean_object* v___x_2181_; lean_object* v___x_2183_; 
lean_dec(v_x_2160_);
v___x_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2180_, 0, v_a_2176_);
v___x_2181_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2181_, 0, v___x_2180_);
lean_ctor_set(v___x_2181_, 1, v___x_2172_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2181_);
v___x_2183_ = v___x_2178_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
else
{
size_t v___x_2185_; size_t v___x_2186_; 
lean_del_object(v___x_2178_);
lean_dec(v_a_2176_);
v___x_2185_ = ((size_t)1ULL);
v___x_2186_ = lean_usize_add(v_i_2163_, v___x_2185_);
v_i_2163_ = v___x_2186_;
v_b_2164_ = v___x_2173_;
goto _start;
}
}
}
else
{
lean_object* v_a_2189_; lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2196_; 
lean_dec(v_x_2160_);
v_a_2189_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2196_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2196_ == 0)
{
v___x_2191_ = v___x_2175_;
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
else
{
lean_inc(v_a_2189_);
lean_dec(v___x_2175_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2196_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2194_; 
if (v_isShared_2192_ == 0)
{
v___x_2194_ = v___x_2191_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2195_; 
v_reuseFailAlloc_2195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2195_, 0, v_a_2189_);
v___x_2194_ = v_reuseFailAlloc_2195_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
return v___x_2194_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2197_, lean_object* v_as_2198_, lean_object* v_sz_2199_, lean_object* v_i_2200_, lean_object* v_b_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_){
_start:
{
size_t v_sz_boxed_2207_; size_t v_i_boxed_2208_; lean_object* v_res_2209_; 
v_sz_boxed_2207_ = lean_unbox_usize(v_sz_2199_);
lean_dec(v_sz_2199_);
v_i_boxed_2208_ = lean_unbox_usize(v_i_2200_);
lean_dec(v_i_2200_);
v_res_2209_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2197_, v_as_2198_, v_sz_boxed_2207_, v_i_boxed_2208_, v_b_2201_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
lean_dec(v___y_2205_);
lean_dec_ref(v___y_2204_);
lean_dec(v___y_2203_);
lean_dec_ref(v___y_2202_);
lean_dec_ref(v_as_2198_);
return v_res_2209_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2210_, lean_object* v_x_2211_, lean_object* v___y_2212_, lean_object* v___y_2213_, lean_object* v___y_2214_, lean_object* v___y_2215_, lean_object* v___y_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2210_, v_x_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_);
lean_dec(v___y_2215_);
lean_dec_ref(v___y_2214_);
lean_dec(v___y_2213_);
lean_dec_ref(v___y_2212_);
lean_dec_ref(v_x_2211_);
return v_res_2217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object* v_x_2218_, lean_object* v_t_2219_, lean_object* v___y_2220_, lean_object* v___y_2221_, lean_object* v___y_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_root_2225_; lean_object* v_tail_2226_; lean_object* v___x_2227_; 
v_root_2225_ = lean_ctor_get(v_t_2219_, 0);
v_tail_2226_ = lean_ctor_get(v_t_2219_, 1);
lean_inc(v_x_2218_);
v___x_2227_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2218_, v_root_2225_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
if (lean_obj_tag(v_a_2228_) == 0)
{
lean_object* v___x_2229_; size_t v_sz_2230_; size_t v___x_2231_; lean_object* v___x_2232_; 
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v___x_2229_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2230_ = lean_array_size(v_tail_2226_);
v___x_2231_ = ((size_t)0ULL);
v___x_2232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2218_, v_tail_2226_, v_sz_2230_, v___x_2231_, v___x_2229_, v___y_2220_, v___y_2221_, v___y_2222_, v___y_2223_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2235_; uint8_t v_isShared_2236_; uint8_t v_isSharedCheck_2245_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2235_ = v___x_2232_;
v_isShared_2236_ = v_isSharedCheck_2245_;
goto v_resetjp_2234_;
}
else
{
lean_inc(v_a_2233_);
lean_dec(v___x_2232_);
v___x_2235_ = lean_box(0);
v_isShared_2236_ = v_isSharedCheck_2245_;
goto v_resetjp_2234_;
}
v_resetjp_2234_:
{
lean_object* v_fst_2237_; 
v_fst_2237_ = lean_ctor_get(v_a_2233_, 0);
lean_inc(v_fst_2237_);
lean_dec(v_a_2233_);
if (lean_obj_tag(v_fst_2237_) == 0)
{
lean_object* v___x_2239_; 
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v_a_2228_);
v___x_2239_ = v___x_2235_;
goto v_reusejp_2238_;
}
else
{
lean_object* v_reuseFailAlloc_2240_; 
v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2240_, 0, v_a_2228_);
v___x_2239_ = v_reuseFailAlloc_2240_;
goto v_reusejp_2238_;
}
v_reusejp_2238_:
{
return v___x_2239_;
}
}
else
{
lean_object* v_val_2241_; lean_object* v___x_2243_; 
v_val_2241_ = lean_ctor_get(v_fst_2237_, 0);
lean_inc(v_val_2241_);
lean_dec_ref_known(v_fst_2237_, 1);
if (v_isShared_2236_ == 0)
{
lean_ctor_set(v___x_2235_, 0, v_val_2241_);
v___x_2243_ = v___x_2235_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_val_2241_);
v___x_2243_ = v_reuseFailAlloc_2244_;
goto v_reusejp_2242_;
}
v_reusejp_2242_:
{
return v___x_2243_;
}
}
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
v_a_2246_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2232_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2232_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
else
{
lean_dec(v_x_2218_);
return v___x_2227_;
}
}
else
{
lean_dec(v_x_2218_);
return v___x_2227_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* v_x_2254_, lean_object* v_t_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_){
_start:
{
lean_object* v_res_2261_; 
v_res_2261_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2254_, v_t_2255_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
lean_dec(v___y_2259_);
lean_dec_ref(v___y_2258_);
lean_dec(v___y_2257_);
lean_dec_ref(v___y_2256_);
lean_dec_ref(v_t_2255_);
return v_res_2261_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object* v_x_2262_, lean_object* v_lctx_2263_, lean_object* v___y_2264_, lean_object* v___y_2265_, lean_object* v___y_2266_, lean_object* v___y_2267_){
_start:
{
lean_object* v_decls_2269_; lean_object* v___x_2270_; 
v_decls_2269_ = lean_ctor_get(v_lctx_2263_, 1);
v___x_2270_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2262_, v_decls_2269_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2270_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object* v_x_2271_, lean_object* v_lctx_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_res_2278_; 
v_res_2278_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2271_, v_lctx_2272_, v___y_2273_, v___y_2274_, v___y_2275_, v___y_2276_);
lean_dec(v___y_2276_);
lean_dec_ref(v___y_2275_);
lean_dec(v___y_2274_);
lean_dec_ref(v___y_2273_);
lean_dec_ref(v_lctx_2272_);
return v_res_2278_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2280_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__0));
v___x_2281_ = l_Lean_stringToMessageData(v___x_2280_);
return v___x_2281_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__2));
v___x_2284_ = l_Lean_stringToMessageData(v___x_2283_);
return v___x_2284_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__4));
v___x_2287_ = l_Lean_stringToMessageData(v___x_2286_);
return v___x_2287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object* v_x_2288_, lean_object* v_mvarId_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_){
_start:
{
lean_object* v___x_2340_; 
lean_inc(v_x_2288_);
v___x_2340_ = l_Lean_FVarId_getDecl___redArg(v_x_2288_, v___y_2290_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; uint8_t v___x_2342_; uint8_t v___x_2343_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2342_ = 0;
v___x_2343_ = l_Lean_LocalDecl_isLet(v_a_2341_, v___x_2342_);
lean_dec(v_a_2341_);
if (v___x_2343_ == 0)
{
goto v___jp_2295_;
}
else
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2344_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2345_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2288_);
v___x_2346_ = l_Lean_mkFVar(v_x_2288_);
v___x_2347_ = l_Lean_MessageData_ofExpr(v___x_2346_);
v___x_2348_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2348_, 0, v___x_2345_);
lean_ctor_set(v___x_2348_, 1, v___x_2347_);
v___x_2349_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2350_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2348_);
lean_ctor_set(v___x_2350_, 1, v___x_2349_);
v___x_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2351_, 0, v___x_2350_);
lean_inc(v_mvarId_2289_);
v___x_2352_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2344_, v_mvarId_2289_, v___x_2351_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2352_) == 0)
{
lean_dec_ref_known(v___x_2352_, 1);
goto v___jp_2295_;
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_dec(v_mvarId_2289_);
lean_dec(v_x_2288_);
v_a_2353_ = lean_ctor_get(v___x_2352_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2352_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2352_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2352_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_dec(v_mvarId_2289_);
lean_dec(v_x_2288_);
v_a_2361_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2340_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2340_);
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
v___jp_2295_:
{
lean_object* v_lctx_2296_; lean_object* v___x_2297_; 
v_lctx_2296_ = lean_ctor_get(v___y_2290_, 2);
lean_inc(v_x_2288_);
v___x_2297_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2288_, v_lctx_2296_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2297_) == 0)
{
lean_object* v_a_2298_; 
v_a_2298_ = lean_ctor_get(v___x_2297_, 0);
lean_inc(v_a_2298_);
lean_dec_ref_known(v___x_2297_, 1);
if (lean_obj_tag(v_a_2298_) == 1)
{
lean_object* v_val_2299_; lean_object* v_fst_2300_; lean_object* v_snd_2301_; lean_object* v___x_2302_; uint8_t v___x_2303_; uint8_t v___x_2304_; lean_object* v___x_2305_; 
lean_dec(v_x_2288_);
v_val_2299_ = lean_ctor_get(v_a_2298_, 0);
lean_inc(v_val_2299_);
lean_dec_ref_known(v_a_2298_, 1);
v_fst_2300_ = lean_ctor_get(v_val_2299_, 0);
lean_inc(v_fst_2300_);
v_snd_2301_ = lean_ctor_get(v_val_2299_, 1);
lean_inc(v_snd_2301_);
lean_dec(v_val_2299_);
v___x_2302_ = lean_box(0);
v___x_2303_ = 1;
v___x_2304_ = lean_unbox(v_snd_2301_);
lean_dec(v_snd_2301_);
v___x_2305_ = l_Lean_Meta_substCore(v_mvarId_2289_, v_fst_2300_, v___x_2304_, v___x_2302_, v___x_2303_, v___x_2303_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
if (lean_obj_tag(v___x_2305_) == 0)
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2314_; 
v_a_2306_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2314_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2314_ == 0)
{
v___x_2308_ = v___x_2305_;
v_isShared_2309_ = v_isSharedCheck_2314_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2305_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2314_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v_snd_2310_; lean_object* v___x_2312_; 
v_snd_2310_ = lean_ctor_get(v_a_2306_, 1);
lean_inc(v_snd_2310_);
lean_dec(v_a_2306_);
if (v_isShared_2309_ == 0)
{
lean_ctor_set(v___x_2308_, 0, v_snd_2310_);
v___x_2312_ = v___x_2308_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2313_; 
v_reuseFailAlloc_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2313_, 0, v_snd_2310_);
v___x_2312_ = v_reuseFailAlloc_2313_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
return v___x_2312_;
}
}
}
else
{
lean_object* v_a_2315_; lean_object* v___x_2317_; uint8_t v_isShared_2318_; uint8_t v_isSharedCheck_2322_; 
v_a_2315_ = lean_ctor_get(v___x_2305_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v___x_2305_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2317_ = v___x_2305_;
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
else
{
lean_inc(v_a_2315_);
lean_dec(v___x_2305_);
v___x_2317_ = lean_box(0);
v_isShared_2318_ = v_isSharedCheck_2322_;
goto v_resetjp_2316_;
}
v_resetjp_2316_:
{
lean_object* v___x_2320_; 
if (v_isShared_2318_ == 0)
{
v___x_2320_ = v___x_2317_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2321_; 
v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_a_2315_);
v___x_2320_ = v_reuseFailAlloc_2321_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
return v___x_2320_;
}
}
}
}
else
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
lean_dec(v_a_2298_);
v___x_2323_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2324_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2325_ = l_Lean_mkFVar(v_x_2288_);
v___x_2326_ = l_Lean_MessageData_ofExpr(v___x_2325_);
v___x_2327_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2324_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_2329_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2327_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2329_);
v___x_2331_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2323_, v_mvarId_2289_, v___x_2330_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
return v___x_2331_;
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_dec(v_mvarId_2289_);
lean_dec(v_x_2288_);
v_a_2332_ = lean_ctor_get(v___x_2297_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2297_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2297_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2297_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v___x_2337_; 
if (v_isShared_2335_ == 0)
{
v___x_2337_ = v___x_2334_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v_a_2332_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2369_, lean_object* v_mvarId_2370_, lean_object* v___y_2371_, lean_object* v___y_2372_, lean_object* v___y_2373_, lean_object* v___y_2374_, lean_object* v___y_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l_Lean_Meta_substVar___lam__0(v_x_2369_, v_mvarId_2370_, v___y_2371_, v___y_2372_, v___y_2373_, v___y_2374_);
lean_dec(v___y_2374_);
lean_dec_ref(v___y_2373_);
lean_dec(v___y_2372_);
lean_dec_ref(v___y_2371_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2377_, lean_object* v_x_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v___f_2384_; lean_object* v___x_2385_; 
lean_inc(v_mvarId_2377_);
v___f_2384_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2384_, 0, v_x_2378_);
lean_closure_set(v___f_2384_, 1, v_mvarId_2377_);
v___x_2385_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2377_, v___f_2384_, v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
return v___x_2385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2386_, lean_object* v_x_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v_res_2393_; 
v_res_2393_ = l_Lean_Meta_substVar(v_mvarId_2386_, v_x_2387_, v_a_2388_, v_a_2389_, v_a_2390_, v_a_2391_);
lean_dec(v_a_2391_);
lean_dec_ref(v_a_2390_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
return v_res_2393_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2395_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2396_ = l_Lean_stringToMessageData(v___x_2395_);
return v___x_2396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2397_, lean_object* v_snd_2398_, uint8_t v___x_2399_, lean_object* v_fvarSubst_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; 
lean_inc(v_fst_2397_);
v___x_2406_ = l_Lean_FVarId_getDecl___redArg(v_fst_2397_, v___y_2401_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v_a_2407_; lean_object* v_newType_2409_; uint8_t v_symm_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2451_; lean_object* v___y_2452_; lean_object* v___y_2453_; lean_object* v___y_2454_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_a_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc(v_a_2407_);
lean_dec_ref_known(v___x_2406_, 1);
v___x_2462_ = l_Lean_LocalDecl_type(v_a_2407_);
v___x_2463_ = l_Lean_Meta_matchEq_x3f(v___x_2462_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
if (lean_obj_tag(v_a_2464_) == 1)
{
lean_object* v_val_2465_; lean_object* v_snd_2466_; lean_object* v_fst_2467_; lean_object* v_snd_2468_; lean_object* v___x_2469_; 
v_val_2465_ = lean_ctor_get(v_a_2464_, 0);
lean_inc(v_val_2465_);
lean_dec_ref_known(v_a_2464_, 1);
v_snd_2466_ = lean_ctor_get(v_val_2465_, 1);
lean_inc(v_snd_2466_);
lean_dec(v_val_2465_);
v_fst_2467_ = lean_ctor_get(v_snd_2466_, 0);
lean_inc(v_fst_2467_);
v_snd_2468_ = lean_ctor_get(v_snd_2466_, 1);
lean_inc_n(v_snd_2468_, 2);
lean_dec(v_snd_2466_);
lean_inc(v___y_2404_);
lean_inc_ref(v___y_2403_);
lean_inc(v___y_2402_);
lean_inc_ref(v___y_2401_);
v___x_2469_ = lean_whnf(v_snd_2468_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; uint8_t v___x_2471_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v___x_2471_ = l_Lean_Expr_isFVar(v_a_2470_);
if (v___x_2471_ == 0)
{
lean_object* v___x_2472_; 
lean_dec(v_a_2470_);
lean_inc(v___y_2404_);
lean_inc_ref(v___y_2403_);
lean_inc(v___y_2402_);
lean_inc_ref(v___y_2401_);
lean_inc(v_fst_2467_);
v___x_2472_ = lean_whnf(v_fst_2467_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2472_) == 0)
{
lean_object* v_a_2473_; uint8_t v___x_2474_; 
v_a_2473_ = lean_ctor_get(v___x_2472_, 0);
lean_inc(v_a_2473_);
lean_dec_ref_known(v___x_2472_, 1);
v___x_2474_ = l_Lean_Expr_isFVar(v_a_2473_);
if (v___x_2474_ == 0)
{
lean_dec(v_a_2473_);
lean_dec(v_snd_2468_);
lean_dec(v_fst_2467_);
lean_dec(v_fvarSubst_2400_);
lean_dec(v_fst_2397_);
v___y_2451_ = v___y_2401_;
v___y_2452_ = v___y_2402_;
v___y_2453_ = v___y_2403_;
v___y_2454_ = v___y_2404_;
goto v___jp_2450_;
}
else
{
uint8_t v___x_2475_; 
v___x_2475_ = lean_expr_eqv(v_fst_2467_, v_a_2473_);
lean_dec(v_fst_2467_);
if (v___x_2475_ == 0)
{
lean_object* v___x_2476_; 
v___x_2476_ = l_Lean_Meta_mkEq(v_a_2473_, v_snd_2468_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2476_) == 0)
{
lean_object* v_a_2477_; 
v_a_2477_ = lean_ctor_get(v___x_2476_, 0);
lean_inc(v_a_2477_);
lean_dec_ref_known(v___x_2476_, 1);
v_newType_2409_ = v_a_2477_;
v_symm_2410_ = v___x_2471_;
v___y_2411_ = v___y_2401_;
v___y_2412_ = v___y_2402_;
v___y_2413_ = v___y_2403_;
v___y_2414_ = v___y_2404_;
goto v___jp_2408_;
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec(v_a_2407_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_fvarSubst_2400_);
lean_dec(v_snd_2398_);
lean_dec(v_fst_2397_);
v_a_2478_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2476_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2476_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v___x_2486_; 
lean_dec(v_a_2473_);
lean_dec(v_snd_2468_);
lean_dec(v_a_2407_);
v___x_2486_ = l_Lean_Meta_substCore(v_snd_2398_, v_fst_2397_, v___x_2471_, v_fvarSubst_2400_, v___x_2399_, v___x_2399_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v___x_2486_;
}
}
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_snd_2468_);
lean_dec(v_fst_2467_);
lean_dec(v_a_2407_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_fvarSubst_2400_);
lean_dec(v_snd_2398_);
lean_dec(v_fst_2397_);
v_a_2487_ = lean_ctor_get(v___x_2472_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2472_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2472_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2472_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
else
{
uint8_t v___x_2495_; 
v___x_2495_ = lean_expr_eqv(v_snd_2468_, v_a_2470_);
lean_dec(v_snd_2468_);
if (v___x_2495_ == 0)
{
lean_object* v___x_2496_; 
v___x_2496_ = l_Lean_Meta_mkEq(v_fst_2467_, v_a_2470_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
if (lean_obj_tag(v___x_2496_) == 0)
{
lean_object* v_a_2497_; 
v_a_2497_ = lean_ctor_get(v___x_2496_, 0);
lean_inc(v_a_2497_);
lean_dec_ref_known(v___x_2496_, 1);
v_newType_2409_ = v_a_2497_;
v_symm_2410_ = v___x_2399_;
v___y_2411_ = v___y_2401_;
v___y_2412_ = v___y_2402_;
v___y_2413_ = v___y_2403_;
v___y_2414_ = v___y_2404_;
goto v___jp_2408_;
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_a_2407_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_fvarSubst_2400_);
lean_dec(v_snd_2398_);
lean_dec(v_fst_2397_);
v_a_2498_ = lean_ctor_get(v___x_2496_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2496_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2496_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2496_);
v___x_2500_ = lean_box(0);
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
v_resetjp_2499_:
{
lean_object* v___x_2503_; 
if (v_isShared_2501_ == 0)
{
v___x_2503_ = v___x_2500_;
goto v_reusejp_2502_;
}
else
{
lean_object* v_reuseFailAlloc_2504_; 
v_reuseFailAlloc_2504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2504_, 0, v_a_2498_);
v___x_2503_ = v_reuseFailAlloc_2504_;
goto v_reusejp_2502_;
}
v_reusejp_2502_:
{
return v___x_2503_;
}
}
}
}
else
{
lean_object* v___x_2506_; 
lean_dec(v_a_2470_);
lean_dec(v_fst_2467_);
lean_dec(v_a_2407_);
v___x_2506_ = l_Lean_Meta_substCore(v_snd_2398_, v_fst_2397_, v___x_2399_, v_fvarSubst_2400_, v___x_2399_, v___x_2399_, v___y_2401_, v___y_2402_, v___y_2403_, v___y_2404_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
return v___x_2506_;
}
}
}
else
{
lean_object* v_a_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2514_; 
lean_dec(v_snd_2468_);
lean_dec(v_fst_2467_);
lean_dec(v_a_2407_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_fvarSubst_2400_);
lean_dec(v_snd_2398_);
lean_dec(v_fst_2397_);
v_a_2507_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2514_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2514_ == 0)
{
v___x_2509_ = v___x_2469_;
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_a_2507_);
lean_dec(v___x_2469_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2514_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v___x_2512_; 
if (v_isShared_2510_ == 0)
{
v___x_2512_ = v___x_2509_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v_a_2507_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
else
{
lean_dec(v_a_2464_);
lean_dec(v_fvarSubst_2400_);
lean_dec(v_fst_2397_);
v___y_2451_ = v___y_2401_;
v___y_2452_ = v___y_2402_;
v___y_2453_ = v___y_2403_;
v___y_2454_ = v___y_2404_;
goto v___jp_2450_;
}
}
else
{
lean_object* v_a_2515_; lean_object* v___x_2517_; uint8_t v_isShared_2518_; uint8_t v_isSharedCheck_2522_; 
lean_dec(v_a_2407_);
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_fvarSubst_2400_);
lean_dec(v_snd_2398_);
lean_dec(v_fst_2397_);
v_a_2515_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2522_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2522_ == 0)
{
v___x_2517_ = v___x_2463_;
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
else
{
lean_inc(v_a_2515_);
lean_dec(v___x_2463_);
v___x_2517_ = lean_box(0);
v_isShared_2518_ = v_isSharedCheck_2522_;
goto v_resetjp_2516_;
}
v_resetjp_2516_:
{
lean_object* v___x_2520_; 
if (v_isShared_2518_ == 0)
{
v___x_2520_ = v___x_2517_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_a_2515_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
v___jp_2408_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = l_Lean_LocalDecl_userName(v_a_2407_);
lean_dec(v_a_2407_);
lean_inc(v_fst_2397_);
v___x_2416_ = l_Lean_mkFVar(v_fst_2397_);
v___x_2417_ = l_Lean_MVarId_assert(v_snd_2398_, v___x_2415_, v_newType_2409_, v___x_2416_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2419_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2419_ = l_Lean_Meta_intro1Core(v_a_2418_, v___x_2399_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v_fst_2421_; lean_object* v_snd_2422_; lean_object* v___x_2423_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v_fst_2421_ = lean_ctor_get(v_a_2420_, 0);
lean_inc(v_fst_2421_);
v_snd_2422_ = lean_ctor_get(v_a_2420_, 1);
lean_inc(v_snd_2422_);
lean_dec(v_a_2420_);
v___x_2423_ = l_Lean_MVarId_clear(v_snd_2422_, v_fst_2397_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2425_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref_known(v___x_2423_, 1);
v___x_2425_ = l_Lean_Meta_substCore(v_a_2424_, v_fst_2421_, v_symm_2410_, v_fvarSubst_2400_, v___x_2399_, v___x_2399_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
return v___x_2425_;
}
else
{
lean_object* v_a_2426_; lean_object* v___x_2428_; uint8_t v_isShared_2429_; uint8_t v_isSharedCheck_2433_; 
lean_dec(v_fst_2421_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v_fvarSubst_2400_);
v_a_2426_ = lean_ctor_get(v___x_2423_, 0);
v_isSharedCheck_2433_ = !lean_is_exclusive(v___x_2423_);
if (v_isSharedCheck_2433_ == 0)
{
v___x_2428_ = v___x_2423_;
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
else
{
lean_inc(v_a_2426_);
lean_dec(v___x_2423_);
v___x_2428_ = lean_box(0);
v_isShared_2429_ = v_isSharedCheck_2433_;
goto v_resetjp_2427_;
}
v_resetjp_2427_:
{
lean_object* v___x_2431_; 
if (v_isShared_2429_ == 0)
{
v___x_2431_ = v___x_2428_;
goto v_reusejp_2430_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v_a_2426_);
v___x_2431_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2430_;
}
v_reusejp_2430_:
{
return v___x_2431_;
}
}
}
}
else
{
lean_object* v_a_2434_; lean_object* v___x_2436_; uint8_t v_isShared_2437_; uint8_t v_isSharedCheck_2441_; 
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v_fvarSubst_2400_);
lean_dec(v_fst_2397_);
v_a_2434_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2441_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2441_ == 0)
{
v___x_2436_ = v___x_2419_;
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
else
{
lean_inc(v_a_2434_);
lean_dec(v___x_2419_);
v___x_2436_ = lean_box(0);
v_isShared_2437_ = v_isSharedCheck_2441_;
goto v_resetjp_2435_;
}
v_resetjp_2435_:
{
lean_object* v___x_2439_; 
if (v_isShared_2437_ == 0)
{
v___x_2439_ = v___x_2436_;
goto v_reusejp_2438_;
}
else
{
lean_object* v_reuseFailAlloc_2440_; 
v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
v___x_2439_ = v_reuseFailAlloc_2440_;
goto v_reusejp_2438_;
}
v_reusejp_2438_:
{
return v___x_2439_;
}
}
}
}
else
{
lean_object* v_a_2442_; lean_object* v___x_2444_; uint8_t v_isShared_2445_; uint8_t v_isSharedCheck_2449_; 
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v_fvarSubst_2400_);
lean_dec(v_fst_2397_);
v_a_2442_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2449_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2449_ == 0)
{
v___x_2444_ = v___x_2417_;
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
else
{
lean_inc(v_a_2442_);
lean_dec(v___x_2417_);
v___x_2444_ = lean_box(0);
v_isShared_2445_ = v_isSharedCheck_2449_;
goto v_resetjp_2443_;
}
v_resetjp_2443_:
{
lean_object* v___x_2447_; 
if (v_isShared_2445_ == 0)
{
v___x_2447_ = v___x_2444_;
goto v_reusejp_2446_;
}
else
{
lean_object* v_reuseFailAlloc_2448_; 
v_reuseFailAlloc_2448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2448_, 0, v_a_2442_);
v___x_2447_ = v_reuseFailAlloc_2448_;
goto v_reusejp_2446_;
}
v_reusejp_2446_:
{
return v___x_2447_;
}
}
}
}
v___jp_2450_:
{
lean_object* v___x_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; 
v___x_2455_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2456_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2457_ = l_Lean_LocalDecl_type(v_a_2407_);
lean_dec(v_a_2407_);
v___x_2458_ = l_Lean_indentExpr(v___x_2457_);
v___x_2459_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2456_);
lean_ctor_set(v___x_2459_, 1, v___x_2458_);
v___x_2460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2460_, 0, v___x_2459_);
v___x_2461_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2455_, v_snd_2398_, v___x_2460_, v___y_2451_, v___y_2452_, v___y_2453_, v___y_2454_);
lean_dec(v___y_2454_);
lean_dec_ref(v___y_2453_);
lean_dec(v___y_2452_);
lean_dec_ref(v___y_2451_);
return v___x_2461_;
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_dec(v___y_2404_);
lean_dec_ref(v___y_2403_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v_fvarSubst_2400_);
lean_dec(v_snd_2398_);
lean_dec(v_fst_2397_);
v_a_2523_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2406_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2406_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2528_; 
if (v_isShared_2526_ == 0)
{
v___x_2528_ = v___x_2525_;
goto v_reusejp_2527_;
}
else
{
lean_object* v_reuseFailAlloc_2529_; 
v_reuseFailAlloc_2529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2529_, 0, v_a_2523_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2531_, lean_object* v_snd_2532_, lean_object* v___x_2533_, lean_object* v_fvarSubst_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_){
_start:
{
uint8_t v___x_1462__boxed_2540_; lean_object* v_res_2541_; 
v___x_1462__boxed_2540_ = lean_unbox(v___x_2533_);
v_res_2541_ = l_Lean_Meta_substEq___lam__0(v_fst_2531_, v_snd_2532_, v___x_1462__boxed_2540_, v_fvarSubst_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
return v_res_2541_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2542_, lean_object* v_hFVarId_2543_, lean_object* v_fvarSubst_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
uint8_t v___x_2550_; lean_object* v___x_2551_; 
v___x_2550_ = 1;
v___x_2551_ = l_Lean_Meta_heqToEq(v_mvarId_2542_, v_hFVarId_2543_, v___x_2550_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
if (lean_obj_tag(v___x_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v_fst_2553_; lean_object* v_snd_2554_; lean_object* v___x_2555_; lean_object* v___f_2556_; lean_object* v___x_2557_; 
v_a_2552_ = lean_ctor_get(v___x_2551_, 0);
lean_inc(v_a_2552_);
lean_dec_ref_known(v___x_2551_, 1);
v_fst_2553_ = lean_ctor_get(v_a_2552_, 0);
lean_inc(v_fst_2553_);
v_snd_2554_ = lean_ctor_get(v_a_2552_, 1);
lean_inc_n(v_snd_2554_, 2);
lean_dec(v_a_2552_);
v___x_2555_ = lean_box(v___x_2550_);
v___f_2556_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2556_, 0, v_fst_2553_);
lean_closure_set(v___f_2556_, 1, v_snd_2554_);
lean_closure_set(v___f_2556_, 2, v___x_2555_);
lean_closure_set(v___f_2556_, 3, v_fvarSubst_2544_);
v___x_2557_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_snd_2554_, v___f_2556_, v_a_2545_, v_a_2546_, v_a_2547_, v_a_2548_);
return v___x_2557_;
}
else
{
lean_object* v_a_2558_; lean_object* v___x_2560_; uint8_t v_isShared_2561_; uint8_t v_isSharedCheck_2565_; 
lean_dec(v_fvarSubst_2544_);
v_a_2558_ = lean_ctor_get(v___x_2551_, 0);
v_isSharedCheck_2565_ = !lean_is_exclusive(v___x_2551_);
if (v_isSharedCheck_2565_ == 0)
{
v___x_2560_ = v___x_2551_;
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
else
{
lean_inc(v_a_2558_);
lean_dec(v___x_2551_);
v___x_2560_ = lean_box(0);
v_isShared_2561_ = v_isSharedCheck_2565_;
goto v_resetjp_2559_;
}
v_resetjp_2559_:
{
lean_object* v___x_2563_; 
if (v_isShared_2561_ == 0)
{
v___x_2563_ = v___x_2560_;
goto v_reusejp_2562_;
}
else
{
lean_object* v_reuseFailAlloc_2564_; 
v_reuseFailAlloc_2564_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2564_, 0, v_a_2558_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2566_, lean_object* v_hFVarId_2567_, lean_object* v_fvarSubst_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_Lean_Meta_substEq(v_mvarId_2566_, v_hFVarId_2567_, v_fvarSubst_2568_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
lean_dec(v_a_2572_);
lean_dec_ref(v_a_2571_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2575_, lean_object* v_mvarId_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_){
_start:
{
lean_object* v___x_2582_; 
lean_inc(v_h_2575_);
v___x_2582_ = l_Lean_FVarId_getType___redArg(v_h_2575_, v___y_2577_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2582_) == 0)
{
lean_object* v_a_2583_; lean_object* v___x_2584_; 
v_a_2583_ = lean_ctor_get(v___x_2582_, 0);
lean_inc_n(v_a_2583_, 2);
lean_dec_ref_known(v___x_2582_, 1);
v___x_2584_ = l_Lean_Meta_matchEq_x3f(v_a_2583_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
if (lean_obj_tag(v_a_2585_) == 0)
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lean_Meta_matchHEq_x3f(v_a_2583_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2586_) == 0)
{
lean_object* v_a_2587_; 
v_a_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_a_2587_);
lean_dec_ref_known(v___x_2586_, 1);
if (lean_obj_tag(v_a_2587_) == 0)
{
lean_object* v___x_2588_; 
v___x_2588_ = l_Lean_Meta_substVar(v_mvarId_2576_, v_h_2575_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2588_;
}
else
{
uint8_t v___x_2589_; lean_object* v___x_2590_; 
lean_dec_ref_known(v_a_2587_, 1);
v___x_2589_ = 1;
lean_inc(v_h_2575_);
lean_inc(v_mvarId_2576_);
v___x_2590_ = l_Lean_Meta_heqToEq(v_mvarId_2576_, v_h_2575_, v___x_2589_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2590_) == 0)
{
lean_object* v_a_2591_; lean_object* v_fst_2592_; lean_object* v_snd_2593_; uint8_t v___x_2594_; 
v_a_2591_ = lean_ctor_get(v___x_2590_, 0);
lean_inc(v_a_2591_);
lean_dec_ref_known(v___x_2590_, 1);
v_fst_2592_ = lean_ctor_get(v_a_2591_, 0);
lean_inc(v_fst_2592_);
v_snd_2593_ = lean_ctor_get(v_a_2591_, 1);
lean_inc(v_snd_2593_);
lean_dec(v_a_2591_);
v___x_2594_ = l_Lean_instBEqMVarId_beq(v_mvarId_2576_, v_snd_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; 
lean_dec(v_mvarId_2576_);
lean_dec(v_h_2575_);
v___x_2595_ = l_Lean_Meta_subst(v_snd_2593_, v_fst_2592_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2595_;
}
else
{
lean_object* v___x_2596_; 
lean_dec(v_snd_2593_);
lean_dec(v_fst_2592_);
v___x_2596_ = l_Lean_Meta_substVar(v_mvarId_2576_, v_h_2575_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
return v___x_2596_;
}
}
else
{
lean_object* v_a_2597_; lean_object* v___x_2599_; uint8_t v_isShared_2600_; uint8_t v_isSharedCheck_2604_; 
lean_dec(v_mvarId_2576_);
lean_dec(v_h_2575_);
v_a_2597_ = lean_ctor_get(v___x_2590_, 0);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2590_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2599_ = v___x_2590_;
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
else
{
lean_inc(v_a_2597_);
lean_dec(v___x_2590_);
v___x_2599_ = lean_box(0);
v_isShared_2600_ = v_isSharedCheck_2604_;
goto v_resetjp_2598_;
}
v_resetjp_2598_:
{
lean_object* v___x_2602_; 
if (v_isShared_2600_ == 0)
{
v___x_2602_ = v___x_2599_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v_a_2597_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2612_; 
lean_dec(v_mvarId_2576_);
lean_dec(v_h_2575_);
v_a_2605_ = lean_ctor_get(v___x_2586_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2586_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2607_ = v___x_2586_;
v_isShared_2608_ = v_isSharedCheck_2612_;
goto v_resetjp_2606_;
}
else
{
lean_inc(v_a_2605_);
lean_dec(v___x_2586_);
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
else
{
lean_object* v___x_2613_; lean_object* v___x_2614_; 
lean_dec_ref_known(v_a_2585_, 1);
lean_dec(v_a_2583_);
v___x_2613_ = lean_box(0);
v___x_2614_ = l_Lean_Meta_substEq(v_mvarId_2576_, v_h_2575_, v___x_2613_, v___y_2577_, v___y_2578_, v___y_2579_, v___y_2580_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2623_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2617_ = v___x_2614_;
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2614_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v_snd_2619_; lean_object* v___x_2621_; 
v_snd_2619_ = lean_ctor_get(v_a_2615_, 1);
lean_inc(v_snd_2619_);
lean_dec(v_a_2615_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 0, v_snd_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_snd_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
v_a_2624_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2614_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2614_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_a_2583_);
lean_dec(v_mvarId_2576_);
lean_dec(v_h_2575_);
v_a_2632_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2584_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2584_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
else
{
lean_object* v_a_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2647_; 
lean_dec(v_mvarId_2576_);
lean_dec(v_h_2575_);
v_a_2640_ = lean_ctor_get(v___x_2582_, 0);
v_isSharedCheck_2647_ = !lean_is_exclusive(v___x_2582_);
if (v_isSharedCheck_2647_ == 0)
{
v___x_2642_ = v___x_2582_;
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
else
{
lean_inc(v_a_2640_);
lean_dec(v___x_2582_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2647_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2645_; 
if (v_isShared_2643_ == 0)
{
v___x_2645_ = v___x_2642_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2646_; 
v_reuseFailAlloc_2646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_a_2640_);
v___x_2645_ = v_reuseFailAlloc_2646_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
return v___x_2645_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2648_, lean_object* v_mvarId_2649_, lean_object* v___y_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v_res_2655_; 
v_res_2655_ = l_Lean_Meta_subst___lam__0(v_h_2648_, v_mvarId_2649_, v___y_2650_, v___y_2651_, v___y_2652_, v___y_2653_);
lean_dec(v___y_2653_);
lean_dec_ref(v___y_2652_);
lean_dec(v___y_2651_);
lean_dec_ref(v___y_2650_);
return v_res_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2656_, lean_object* v_h_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
lean_object* v___f_2663_; lean_object* v___x_2664_; 
lean_inc(v_mvarId_2656_);
v___f_2663_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2663_, 0, v_h_2657_);
lean_closure_set(v___f_2663_, 1, v_mvarId_2656_);
v___x_2664_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2656_, v___f_2663_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
return v___x_2664_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2665_, lean_object* v_h_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v_res_2672_; 
v_res_2672_ = l_Lean_Meta_subst(v_mvarId_2665_, v_h_2666_, v_a_2667_, v_a_2668_, v_a_2669_, v_a_2670_);
lean_dec(v_a_2670_);
lean_dec_ref(v_a_2669_);
lean_dec(v_a_2668_);
lean_dec_ref(v_a_2667_);
return v_res_2672_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_){
_start:
{
lean_object* v___x_2679_; 
v___x_2679_ = l_Lean_Meta_saveState___redArg(v___y_2675_, v___y_2677_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v___x_2681_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
lean_inc(v___y_2677_);
lean_inc_ref(v___y_2676_);
lean_inc(v___y_2675_);
lean_inc_ref(v___y_2674_);
v___x_2681_ = lean_apply_5(v_x_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_, lean_box(0));
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_dec(v_a_2680_);
return v___x_2681_;
}
else
{
lean_object* v_a_2682_; uint8_t v___x_2683_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
v___x_2683_ = l_Lean_Exception_isInterrupt(v_a_2682_);
if (v___x_2683_ == 0)
{
uint8_t v___x_2684_; 
lean_inc(v_a_2682_);
v___x_2684_ = l_Lean_Exception_isRuntime(v_a_2682_);
if (v___x_2684_ == 0)
{
lean_object* v___x_2685_; 
lean_dec_ref_known(v___x_2681_, 1);
v___x_2685_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2680_, v___y_2675_, v___y_2677_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2692_ == 0)
{
lean_object* v_unused_2693_; 
v_unused_2693_ = lean_ctor_get(v___x_2685_, 0);
lean_dec(v_unused_2693_);
v___x_2687_ = v___x_2685_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_dec(v___x_2685_);
v___x_2687_ = lean_box(0);
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
v_resetjp_2686_:
{
lean_object* v___x_2690_; 
if (v_isShared_2688_ == 0)
{
lean_ctor_set_tag(v___x_2687_, 1);
lean_ctor_set(v___x_2687_, 0, v_a_2682_);
v___x_2690_ = v___x_2687_;
goto v_reusejp_2689_;
}
else
{
lean_object* v_reuseFailAlloc_2691_; 
v_reuseFailAlloc_2691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2691_, 0, v_a_2682_);
v___x_2690_ = v_reuseFailAlloc_2691_;
goto v_reusejp_2689_;
}
v_reusejp_2689_:
{
return v___x_2690_;
}
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v_a_2682_);
v_a_2694_ = lean_ctor_get(v___x_2685_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2685_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2685_);
v___x_2696_ = lean_box(0);
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
v_resetjp_2695_:
{
lean_object* v___x_2699_; 
if (v_isShared_2697_ == 0)
{
v___x_2699_ = v___x_2696_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v_a_2694_);
v___x_2699_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
return v___x_2699_;
}
}
}
}
else
{
lean_dec(v_a_2682_);
lean_dec(v_a_2680_);
return v___x_2681_;
}
}
else
{
lean_dec(v_a_2682_);
lean_dec(v_a_2680_);
return v___x_2681_;
}
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_dec_ref(v_x_2673_);
v_a_2702_ = lean_ctor_get(v___x_2679_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2679_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2679_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2679_);
v___x_2704_ = lean_box(0);
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
v_resetjp_2703_:
{
lean_object* v___x_2707_; 
if (v_isShared_2705_ == 0)
{
v___x_2707_ = v___x_2704_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_a_2702_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2710_, v___y_2711_, v___y_2712_, v___y_2713_, v___y_2714_);
lean_dec(v___y_2714_);
lean_dec_ref(v___y_2713_);
lean_dec(v___y_2712_);
lean_dec_ref(v___y_2711_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2717_, lean_object* v_x_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v___x_2724_; 
v___x_2724_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
return v___x_2724_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2725_, lean_object* v_x_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_){
_start:
{
lean_object* v_res_2732_; 
v_res_2732_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2725_, v_x_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
lean_dec(v___y_2730_);
lean_dec_ref(v___y_2729_);
lean_dec(v___y_2728_);
lean_dec_ref(v___y_2727_);
return v_res_2732_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
lean_object* v_ref_2739_; lean_object* v___x_2740_; lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2749_; 
v_ref_2739_ = lean_ctor_get(v___y_2736_, 2);
v___x_2740_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msg_2733_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
v_a_2741_ = lean_ctor_get(v___x_2740_, 0);
v_isSharedCheck_2749_ = !lean_is_exclusive(v___x_2740_);
if (v_isSharedCheck_2749_ == 0)
{
v___x_2743_ = v___x_2740_;
v_isShared_2744_ = v_isSharedCheck_2749_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2740_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2749_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2745_; lean_object* v___x_2747_; 
lean_inc(v_ref_2739_);
v___x_2745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2745_, 0, v_ref_2739_);
lean_ctor_set(v___x_2745_, 1, v_a_2741_);
if (v_isShared_2744_ == 0)
{
lean_ctor_set_tag(v___x_2743_, 1);
lean_ctor_set(v___x_2743_, 0, v___x_2745_);
v___x_2747_ = v___x_2743_;
goto v_reusejp_2746_;
}
else
{
lean_object* v_reuseFailAlloc_2748_; 
v_reuseFailAlloc_2748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2748_, 0, v___x_2745_);
v___x_2747_ = v_reuseFailAlloc_2748_;
goto v_reusejp_2746_;
}
v_reusejp_2746_:
{
return v___x_2747_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_res_2756_; 
v_res_2756_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
lean_dec(v___y_2754_);
lean_dec_ref(v___y_2753_);
lean_dec(v___y_2752_);
lean_dec_ref(v___y_2751_);
return v_res_2756_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2759_ = l_Lean_stringToMessageData(v___x_2758_);
return v___x_2759_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2762_ = l_Lean_stringToMessageData(v___x_2761_);
return v___x_2762_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2764_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2765_ = l_Lean_stringToMessageData(v___x_2764_);
return v___x_2765_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2767_; lean_object* v___x_2768_; 
v___x_2767_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2768_ = l_Lean_stringToMessageData(v___x_2767_);
return v___x_2768_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2770_; lean_object* v___x_2771_; 
v___x_2770_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2771_ = l_Lean_stringToMessageData(v___x_2770_);
return v___x_2771_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2784_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2785_ = l_Lean_stringToMessageData(v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2794_, uint8_t v_substLHS_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_, lean_object* v___y_2799_){
_start:
{
lean_object* v___x_2801_; 
lean_inc(v_mvarId_2794_);
v___x_2801_ = l_Lean_MVarId_getType_x27(v_mvarId_2794_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2801_) == 0)
{
lean_object* v_a_2802_; 
v_a_2802_ = lean_ctor_get(v___x_2801_, 0);
lean_inc(v_a_2802_);
lean_dec_ref_known(v___x_2801_, 1);
if (lean_obj_tag(v_a_2802_) == 7)
{
lean_object* v_binderType_2806_; lean_object* v_body_2807_; uint8_t v___x_2808_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2816_; lean_object* v___y_2817_; lean_object* v___y_2818_; lean_object* v___y_2819_; lean_object* v___y_2820_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v___y_2899_; lean_object* v___y_2900_; lean_object* v___y_2901_; lean_object* v___y_2902_; lean_object* v___y_2903_; lean_object* v_fst_2943_; lean_object* v_fst_2944_; lean_object* v_fst_2945_; lean_object* v_snd_2946_; lean_object* v___y_2947_; lean_object* v___y_2948_; lean_object* v___y_2949_; lean_object* v___y_2950_; lean_object* v___y_2963_; lean_object* v___y_2964_; lean_object* v___y_2965_; lean_object* v___y_2966_; 
v_binderType_2806_ = lean_ctor_get(v_a_2802_, 1);
lean_inc_ref(v_binderType_2806_);
v_body_2807_ = lean_ctor_get(v_a_2802_, 2);
lean_inc_ref(v_body_2807_);
lean_dec_ref_known(v_a_2802_, 3);
v___x_2808_ = l_Lean_Expr_hasLooseBVars(v_body_2807_);
if (v___x_2808_ == 0)
{
lean_object* v___x_2977_; 
v___x_2977_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2806_, v___y_2797_);
if (lean_obj_tag(v___x_2977_) == 0)
{
lean_object* v_a_2978_; lean_object* v___x_2979_; uint8_t v___x_2980_; 
v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2977_, 1);
v___x_2979_ = l_Lean_Expr_cleanupAnnotations(v_a_2978_);
v___x_2980_ = l_Lean_Expr_isApp(v___x_2979_);
if (v___x_2980_ == 0)
{
lean_dec_ref(v___x_2979_);
lean_dec_ref(v_body_2807_);
lean_dec(v_mvarId_2794_);
v___y_2963_ = v___y_2796_;
v___y_2964_ = v___y_2797_;
v___y_2965_ = v___y_2798_;
v___y_2966_ = v___y_2799_;
goto v___jp_2962_;
}
else
{
lean_object* v_arg_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; 
v_arg_2981_ = lean_ctor_get(v___x_2979_, 1);
lean_inc_ref(v_arg_2981_);
v___x_2982_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2979_);
v___x_2983_ = l_Lean_Expr_isApp(v___x_2982_);
if (v___x_2983_ == 0)
{
lean_dec_ref(v___x_2982_);
lean_dec_ref(v_arg_2981_);
lean_dec_ref(v_body_2807_);
lean_dec(v_mvarId_2794_);
v___y_2963_ = v___y_2796_;
v___y_2964_ = v___y_2797_;
v___y_2965_ = v___y_2798_;
v___y_2966_ = v___y_2799_;
goto v___jp_2962_;
}
else
{
lean_object* v_arg_2984_; lean_object* v___x_2985_; uint8_t v___x_2986_; 
v_arg_2984_ = lean_ctor_get(v___x_2982_, 1);
lean_inc_ref(v_arg_2984_);
v___x_2985_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2982_);
v___x_2986_ = l_Lean_Expr_isApp(v___x_2985_);
if (v___x_2986_ == 0)
{
lean_dec_ref(v___x_2985_);
lean_dec_ref(v_arg_2984_);
lean_dec_ref(v_arg_2981_);
lean_dec_ref(v_body_2807_);
lean_dec(v_mvarId_2794_);
v___y_2963_ = v___y_2796_;
v___y_2964_ = v___y_2797_;
v___y_2965_ = v___y_2798_;
v___y_2966_ = v___y_2799_;
goto v___jp_2962_;
}
else
{
lean_object* v_arg_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; uint8_t v___x_2990_; 
v_arg_2987_ = lean_ctor_get(v___x_2985_, 1);
lean_inc_ref(v_arg_2987_);
v___x_2988_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2985_);
v___x_2989_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_2990_ = l_Lean_Expr_isConstOf(v___x_2988_, v___x_2989_);
if (v___x_2990_ == 0)
{
uint8_t v___x_2991_; 
v___x_2991_ = l_Lean_Expr_isApp(v___x_2988_);
if (v___x_2991_ == 0)
{
lean_dec_ref(v___x_2988_);
lean_dec_ref(v_arg_2987_);
lean_dec_ref(v_arg_2984_);
lean_dec_ref(v_arg_2981_);
lean_dec_ref(v_body_2807_);
lean_dec(v_mvarId_2794_);
v___y_2963_ = v___y_2796_;
v___y_2964_ = v___y_2797_;
v___y_2965_ = v___y_2798_;
v___y_2966_ = v___y_2799_;
goto v___jp_2962_;
}
else
{
lean_object* v_arg_2992_; lean_object* v___y_2994_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___x_3000_; lean_object* v___x_3001_; uint8_t v___x_3002_; 
v_arg_2992_ = lean_ctor_get(v___x_2988_, 1);
lean_inc_ref(v_arg_2992_);
v___x_3000_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2988_);
v___x_3001_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_3002_ = l_Lean_Expr_isConstOf(v___x_3000_, v___x_3001_);
lean_dec_ref(v___x_3000_);
if (v___x_3002_ == 0)
{
lean_dec_ref(v_arg_2992_);
lean_dec_ref(v_arg_2987_);
lean_dec_ref(v_arg_2984_);
lean_dec_ref(v_arg_2981_);
lean_dec_ref(v_body_2807_);
lean_dec(v_mvarId_2794_);
v___y_2963_ = v___y_2796_;
v___y_2964_ = v___y_2797_;
v___y_2965_ = v___y_2798_;
v___y_2966_ = v___y_2799_;
goto v___jp_2962_;
}
else
{
lean_object* v___x_3003_; 
lean_inc_ref(v_arg_2992_);
v___x_3003_ = l_Lean_Meta_isExprDefEq(v_arg_2992_, v_arg_2984_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_3003_) == 0)
{
lean_object* v_a_3004_; uint8_t v___x_3005_; 
v_a_3004_ = lean_ctor_get(v___x_3003_, 0);
lean_inc(v_a_3004_);
lean_dec_ref_known(v___x_3003_, 1);
v___x_3005_ = lean_unbox(v_a_3004_);
lean_dec(v_a_3004_);
if (v___x_3005_ == 0)
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v_a_3008_; lean_object* v___x_3010_; uint8_t v_isShared_3011_; uint8_t v_isSharedCheck_3015_; 
lean_dec_ref(v_arg_2992_);
lean_dec_ref(v_arg_2987_);
lean_dec_ref(v_arg_2981_);
lean_dec_ref(v_body_2807_);
lean_dec(v_mvarId_2794_);
v___x_3006_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_3007_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3006_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3015_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3015_ == 0)
{
v___x_3010_ = v___x_3007_;
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
else
{
lean_inc(v_a_3008_);
lean_dec(v___x_3007_);
v___x_3010_ = lean_box(0);
v_isShared_3011_ = v_isSharedCheck_3015_;
goto v_resetjp_3009_;
}
v_resetjp_3009_:
{
lean_object* v___x_3013_; 
if (v_isShared_3011_ == 0)
{
v___x_3013_ = v___x_3010_;
goto v_reusejp_3012_;
}
else
{
lean_object* v_reuseFailAlloc_3014_; 
v_reuseFailAlloc_3014_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3014_, 0, v_a_3008_);
v___x_3013_ = v_reuseFailAlloc_3014_;
goto v_reusejp_3012_;
}
v_reusejp_3012_:
{
return v___x_3013_;
}
}
}
else
{
v___y_2994_ = v___y_2796_;
v___y_2995_ = v___y_2797_;
v___y_2996_ = v___y_2798_;
v___y_2997_ = v___y_2799_;
goto v___jp_2993_;
}
}
else
{
lean_object* v_a_3016_; lean_object* v___x_3018_; uint8_t v_isShared_3019_; uint8_t v_isSharedCheck_3023_; 
lean_dec_ref(v_arg_2992_);
lean_dec_ref(v_arg_2987_);
lean_dec_ref(v_arg_2981_);
lean_dec_ref(v_body_2807_);
lean_dec(v_mvarId_2794_);
v_a_3016_ = lean_ctor_get(v___x_3003_, 0);
v_isSharedCheck_3023_ = !lean_is_exclusive(v___x_3003_);
if (v_isSharedCheck_3023_ == 0)
{
v___x_3018_ = v___x_3003_;
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
else
{
lean_inc(v_a_3016_);
lean_dec(v___x_3003_);
v___x_3018_ = lean_box(0);
v_isShared_3019_ = v_isSharedCheck_3023_;
goto v_resetjp_3017_;
}
v_resetjp_3017_:
{
lean_object* v___x_3021_; 
if (v_isShared_3019_ == 0)
{
v___x_3021_ = v___x_3018_;
goto v_reusejp_3020_;
}
else
{
lean_object* v_reuseFailAlloc_3022_; 
v_reuseFailAlloc_3022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3022_, 0, v_a_3016_);
v___x_3021_ = v_reuseFailAlloc_3022_;
goto v_reusejp_3020_;
}
v_reusejp_3020_:
{
return v___x_3021_;
}
}
}
}
v___jp_2993_:
{
if (v_substLHS_2795_ == 0)
{
lean_object* v___x_2998_; 
v___x_2998_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2943_ = v_arg_2992_;
v_fst_2944_ = v_arg_2987_;
v_fst_2945_ = v_arg_2981_;
v_snd_2946_ = v___x_2998_;
v___y_2947_ = v___y_2994_;
v___y_2948_ = v___y_2995_;
v___y_2949_ = v___y_2996_;
v___y_2950_ = v___y_2997_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_2999_; 
v___x_2999_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2943_ = v_arg_2992_;
v_fst_2944_ = v_arg_2981_;
v_fst_2945_ = v_arg_2987_;
v_snd_2946_ = v___x_2999_;
v___y_2947_ = v___y_2994_;
v___y_2948_ = v___y_2995_;
v___y_2949_ = v___y_2996_;
v___y_2950_ = v___y_2997_;
goto v___jp_2942_;
}
}
}
}
else
{
lean_dec_ref(v___x_2988_);
if (v_substLHS_2795_ == 0)
{
lean_object* v___x_3024_; 
v___x_3024_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2943_ = v_arg_2987_;
v_fst_2944_ = v_arg_2984_;
v_fst_2945_ = v_arg_2981_;
v_snd_2946_ = v___x_3024_;
v___y_2947_ = v___y_2796_;
v___y_2948_ = v___y_2797_;
v___y_2949_ = v___y_2798_;
v___y_2950_ = v___y_2799_;
goto v___jp_2942_;
}
else
{
lean_object* v___x_3025_; 
v___x_3025_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2943_ = v_arg_2987_;
v_fst_2944_ = v_arg_2981_;
v_fst_2945_ = v_arg_2984_;
v_snd_2946_ = v___x_3025_;
v___y_2947_ = v___y_2796_;
v___y_2948_ = v___y_2797_;
v___y_2949_ = v___y_2798_;
v___y_2950_ = v___y_2799_;
goto v___jp_2942_;
}
}
}
}
}
}
else
{
lean_object* v_a_3026_; lean_object* v___x_3028_; uint8_t v_isShared_3029_; uint8_t v_isSharedCheck_3033_; 
lean_dec_ref(v_body_2807_);
lean_dec(v_mvarId_2794_);
v_a_3026_ = lean_ctor_get(v___x_2977_, 0);
v_isSharedCheck_3033_ = !lean_is_exclusive(v___x_2977_);
if (v_isSharedCheck_3033_ == 0)
{
v___x_3028_ = v___x_2977_;
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
else
{
lean_inc(v_a_3026_);
lean_dec(v___x_2977_);
v___x_3028_ = lean_box(0);
v_isShared_3029_ = v_isSharedCheck_3033_;
goto v_resetjp_3027_;
}
v_resetjp_3027_:
{
lean_object* v___x_3031_; 
if (v_isShared_3029_ == 0)
{
v___x_3031_ = v___x_3028_;
goto v_reusejp_3030_;
}
else
{
lean_object* v_reuseFailAlloc_3032_; 
v_reuseFailAlloc_3032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3032_, 0, v_a_3026_);
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
lean_dec_ref(v_body_2807_);
lean_dec_ref(v_binderType_2806_);
lean_dec(v_mvarId_2794_);
goto v___jp_2803_;
}
v___jp_2809_:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; uint8_t v___x_2823_; uint8_t v___x_2824_; lean_object* v___x_2825_; 
v___x_2821_ = lean_mk_empty_array_with_capacity(v___y_2811_);
lean_inc_ref(v___x_2821_);
v___x_2822_ = lean_array_push(v___x_2821_, v___y_2812_);
v___x_2823_ = 1;
v___x_2824_ = 1;
v___x_2825_ = l_Lean_Meta_mkLambdaFVars(v___x_2822_, v_body_2807_, v___x_2808_, v___x_2823_, v___x_2808_, v___x_2823_, v___x_2824_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
lean_dec_ref(v___x_2822_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v_a_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v_a_2826_ = lean_ctor_get(v___x_2825_, 0);
lean_inc_n(v_a_2826_, 2);
lean_dec_ref_known(v___x_2825_, 1);
lean_inc_ref(v___y_2814_);
v___x_2827_ = lean_array_push(v___x_2821_, v___y_2814_);
v___x_2828_ = l_Lean_Expr_beta(v_a_2826_, v___x_2827_);
lean_inc(v___y_2815_);
v___x_2829_ = l_Lean_MVarId_getTag(v___y_2815_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v___x_2831_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
lean_inc(v_a_2830_);
lean_dec_ref_known(v___x_2829_, 1);
lean_inc_ref(v___x_2828_);
v___x_2831_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2828_, v_a_2830_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; lean_object* v___x_2833_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
v___x_2833_ = l_Lean_Meta_getLevel(v___x_2828_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2833_) == 0)
{
lean_object* v_a_2834_; lean_object* v___x_2835_; 
v_a_2834_ = lean_ctor_get(v___x_2833_, 0);
lean_inc(v_a_2834_);
lean_dec_ref_known(v___x_2833_, 1);
lean_inc_ref(v___y_2816_);
v___x_2835_ = l_Lean_Meta_getLevel(v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_, v___y_2820_);
if (lean_obj_tag(v___x_2835_) == 0)
{
lean_object* v_a_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2853_; 
v_a_2836_ = lean_ctor_get(v___x_2835_, 0);
lean_inc(v_a_2836_);
lean_dec_ref_known(v___x_2835_, 1);
v___x_2837_ = lean_box(0);
v___x_2838_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2838_, 0, v_a_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2839_, 0, v_a_2834_);
lean_ctor_set(v___x_2839_, 1, v___x_2838_);
lean_inc(v___y_2810_);
v___x_2840_ = l_Lean_mkConst(v___y_2810_, v___x_2839_);
lean_inc(v_a_2832_);
lean_inc_ref(v___y_2814_);
v___x_2841_ = l_Lean_mkApp4(v___x_2840_, v___y_2816_, v___y_2814_, v_a_2826_, v_a_2832_);
v___x_2842_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v___y_2815_, v___x_2841_, v___y_2818_);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2853_ == 0)
{
lean_object* v_unused_2854_; 
v_unused_2854_ = lean_ctor_get(v___x_2842_, 0);
lean_dec(v_unused_2854_);
v___x_2844_ = v___x_2842_;
v_isShared_2845_ = v_isSharedCheck_2853_;
goto v_resetjp_2843_;
}
else
{
lean_dec(v___x_2842_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2853_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; 
v___x_2846_ = l_Lean_Meta_FVarSubst_empty;
v___x_2847_ = l_Lean_Meta_FVarSubst_insert(v___x_2846_, v___y_2813_, v___y_2814_);
v___x_2848_ = l_Lean_Expr_mvarId_x21(v_a_2832_);
lean_dec(v_a_2832_);
v___x_2849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2849_, 0, v___x_2847_);
lean_ctor_set(v___x_2849_, 1, v___x_2848_);
if (v_isShared_2845_ == 0)
{
lean_ctor_set(v___x_2844_, 0, v___x_2849_);
v___x_2851_ = v___x_2844_;
goto v_reusejp_2850_;
}
else
{
lean_object* v_reuseFailAlloc_2852_; 
v_reuseFailAlloc_2852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2852_, 0, v___x_2849_);
v___x_2851_ = v_reuseFailAlloc_2852_;
goto v_reusejp_2850_;
}
v_reusejp_2850_:
{
return v___x_2851_;
}
}
}
else
{
lean_object* v_a_2855_; lean_object* v___x_2857_; uint8_t v_isShared_2858_; uint8_t v_isSharedCheck_2862_; 
lean_dec(v_a_2834_);
lean_dec(v_a_2832_);
lean_dec(v_a_2826_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
v_a_2855_ = lean_ctor_get(v___x_2835_, 0);
v_isSharedCheck_2862_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2862_ == 0)
{
v___x_2857_ = v___x_2835_;
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
else
{
lean_inc(v_a_2855_);
lean_dec(v___x_2835_);
v___x_2857_ = lean_box(0);
v_isShared_2858_ = v_isSharedCheck_2862_;
goto v_resetjp_2856_;
}
v_resetjp_2856_:
{
lean_object* v___x_2860_; 
if (v_isShared_2858_ == 0)
{
v___x_2860_ = v___x_2857_;
goto v_reusejp_2859_;
}
else
{
lean_object* v_reuseFailAlloc_2861_; 
v_reuseFailAlloc_2861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2861_, 0, v_a_2855_);
v___x_2860_ = v_reuseFailAlloc_2861_;
goto v_reusejp_2859_;
}
v_reusejp_2859_:
{
return v___x_2860_;
}
}
}
}
else
{
lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2870_; 
lean_dec(v_a_2832_);
lean_dec(v_a_2826_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
v_a_2863_ = lean_ctor_get(v___x_2833_, 0);
v_isSharedCheck_2870_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2870_ == 0)
{
v___x_2865_ = v___x_2833_;
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2833_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2870_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2868_; 
if (v_isShared_2866_ == 0)
{
v___x_2868_ = v___x_2865_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v_a_2863_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
}
}
else
{
lean_object* v_a_2871_; lean_object* v___x_2873_; uint8_t v_isShared_2874_; uint8_t v_isSharedCheck_2878_; 
lean_dec_ref(v___x_2828_);
lean_dec(v_a_2826_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
v_a_2871_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2878_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2878_ == 0)
{
v___x_2873_ = v___x_2831_;
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
else
{
lean_inc(v_a_2871_);
lean_dec(v___x_2831_);
v___x_2873_ = lean_box(0);
v_isShared_2874_ = v_isSharedCheck_2878_;
goto v_resetjp_2872_;
}
v_resetjp_2872_:
{
lean_object* v___x_2876_; 
if (v_isShared_2874_ == 0)
{
v___x_2876_ = v___x_2873_;
goto v_reusejp_2875_;
}
else
{
lean_object* v_reuseFailAlloc_2877_; 
v_reuseFailAlloc_2877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2877_, 0, v_a_2871_);
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
else
{
lean_object* v_a_2879_; lean_object* v___x_2881_; uint8_t v_isShared_2882_; uint8_t v_isSharedCheck_2886_; 
lean_dec_ref(v___x_2828_);
lean_dec(v_a_2826_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
v_a_2879_ = lean_ctor_get(v___x_2829_, 0);
v_isSharedCheck_2886_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2886_ == 0)
{
v___x_2881_ = v___x_2829_;
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
else
{
lean_inc(v_a_2879_);
lean_dec(v___x_2829_);
v___x_2881_ = lean_box(0);
v_isShared_2882_ = v_isSharedCheck_2886_;
goto v_resetjp_2880_;
}
v_resetjp_2880_:
{
lean_object* v___x_2884_; 
if (v_isShared_2882_ == 0)
{
v___x_2884_ = v___x_2881_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v_a_2879_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
return v___x_2884_;
}
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_dec_ref(v___x_2821_);
lean_dec_ref(v___y_2816_);
lean_dec(v___y_2815_);
lean_dec_ref(v___y_2814_);
lean_dec(v___y_2813_);
v_a_2887_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2825_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2825_);
v___x_2889_ = lean_box(0);
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
v_resetjp_2888_:
{
lean_object* v___x_2892_; 
if (v_isShared_2890_ == 0)
{
v___x_2892_ = v___x_2889_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_a_2887_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
}
}
v___jp_2895_:
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; 
v___x_2904_ = l_Lean_Expr_fvarId_x21(v___y_2897_);
v___x_2905_ = lean_unsigned_to_nat(1u);
v___x_2906_ = lean_mk_empty_array_with_capacity(v___x_2905_);
lean_inc(v___x_2904_);
v___x_2907_ = lean_array_push(v___x_2906_, v___x_2904_);
v___x_2908_ = l_Lean_MVarId_revert(v_mvarId_2794_, v___x_2907_, v___x_2808_, v___x_2808_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
if (lean_obj_tag(v___x_2908_) == 0)
{
lean_object* v_a_2909_; lean_object* v_fst_2910_; lean_object* v_snd_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2933_; 
v_a_2909_ = lean_ctor_get(v___x_2908_, 0);
lean_inc(v_a_2909_);
lean_dec_ref_known(v___x_2908_, 1);
v_fst_2910_ = lean_ctor_get(v_a_2909_, 0);
v_snd_2911_ = lean_ctor_get(v_a_2909_, 1);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_a_2909_);
if (v_isSharedCheck_2933_ == 0)
{
v___x_2913_ = v_a_2909_;
v_isShared_2914_ = v_isSharedCheck_2933_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_snd_2911_);
lean_inc(v_fst_2910_);
lean_dec(v_a_2909_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2933_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2915_; uint8_t v___x_2916_; 
v___x_2915_ = lean_array_get_size(v_fst_2910_);
lean_dec(v_fst_2910_);
v___x_2916_ = lean_nat_dec_eq(v___x_2915_, v___x_2905_);
if (v___x_2916_ == 0)
{
lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v___x_2920_; 
lean_dec(v_snd_2911_);
lean_dec(v___x_2904_);
lean_dec_ref(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec_ref(v_body_2807_);
v___x_2917_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2918_ = l_Lean_MessageData_ofExpr(v___y_2897_);
if (v_isShared_2914_ == 0)
{
lean_ctor_set_tag(v___x_2913_, 7);
lean_ctor_set(v___x_2913_, 1, v___x_2918_);
lean_ctor_set(v___x_2913_, 0, v___x_2917_);
v___x_2920_ = v___x_2913_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v___x_2917_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v___x_2918_);
v___x_2920_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
lean_object* v___x_2921_; lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2931_; 
v___x_2921_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2922_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2922_, 0, v___x_2920_);
lean_ctor_set(v___x_2922_, 1, v___x_2921_);
v___x_2923_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2922_, v___y_2900_, v___y_2901_, v___y_2902_, v___y_2903_);
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2931_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2931_ == 0)
{
v___x_2926_ = v___x_2923_;
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2931_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
lean_object* v___x_2929_; 
if (v_isShared_2927_ == 0)
{
v___x_2929_ = v___x_2926_;
goto v_reusejp_2928_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2924_);
v___x_2929_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2928_;
}
v_reusejp_2928_:
{
return v___x_2929_;
}
}
}
}
else
{
lean_del_object(v___x_2913_);
v___y_2810_ = v___y_2896_;
v___y_2811_ = v___x_2905_;
v___y_2812_ = v___y_2897_;
v___y_2813_ = v___x_2904_;
v___y_2814_ = v___y_2898_;
v___y_2815_ = v_snd_2911_;
v___y_2816_ = v___y_2899_;
v___y_2817_ = v___y_2900_;
v___y_2818_ = v___y_2901_;
v___y_2819_ = v___y_2902_;
v___y_2820_ = v___y_2903_;
goto v___jp_2809_;
}
}
}
else
{
lean_object* v_a_2934_; lean_object* v___x_2936_; uint8_t v_isShared_2937_; uint8_t v_isSharedCheck_2941_; 
lean_dec(v___x_2904_);
lean_dec_ref(v___y_2899_);
lean_dec_ref(v___y_2898_);
lean_dec_ref(v___y_2897_);
lean_dec_ref(v_body_2807_);
v_a_2934_ = lean_ctor_get(v___x_2908_, 0);
v_isSharedCheck_2941_ = !lean_is_exclusive(v___x_2908_);
if (v_isSharedCheck_2941_ == 0)
{
v___x_2936_ = v___x_2908_;
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
else
{
lean_inc(v_a_2934_);
lean_dec(v___x_2908_);
v___x_2936_ = lean_box(0);
v_isShared_2937_ = v_isSharedCheck_2941_;
goto v_resetjp_2935_;
}
v_resetjp_2935_:
{
lean_object* v___x_2939_; 
if (v_isShared_2937_ == 0)
{
v___x_2939_ = v___x_2936_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2940_; 
v_reuseFailAlloc_2940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
v___x_2939_ = v_reuseFailAlloc_2940_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
return v___x_2939_;
}
}
}
}
v___jp_2942_:
{
uint8_t v___x_2951_; 
v___x_2951_ = l_Lean_Expr_isFVar(v_fst_2945_);
if (v___x_2951_ == 0)
{
lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
lean_dec_ref(v_fst_2945_);
lean_dec_ref(v_fst_2944_);
lean_dec_ref(v_fst_2943_);
lean_dec_ref(v_body_2807_);
lean_dec(v_mvarId_2794_);
v___x_2952_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2953_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2952_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
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
else
{
v___y_2896_ = v_snd_2946_;
v___y_2897_ = v_fst_2945_;
v___y_2898_ = v_fst_2944_;
v___y_2899_ = v_fst_2943_;
v___y_2900_ = v___y_2947_;
v___y_2901_ = v___y_2948_;
v___y_2902_ = v___y_2949_;
v___y_2903_ = v___y_2950_;
goto v___jp_2895_;
}
}
v___jp_2962_:
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
v___x_2967_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_2968_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2967_, v___y_2963_, v___y_2964_, v___y_2965_, v___y_2966_);
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
else
{
lean_dec(v_a_2802_);
lean_dec(v_mvarId_2794_);
goto v___jp_2803_;
}
v___jp_2803_:
{
lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2804_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2805_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2804_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
return v___x_2805_;
}
}
else
{
lean_object* v_a_3034_; lean_object* v___x_3036_; uint8_t v_isShared_3037_; uint8_t v_isSharedCheck_3041_; 
lean_dec(v_mvarId_2794_);
v_a_3034_ = lean_ctor_get(v___x_2801_, 0);
v_isSharedCheck_3041_ = !lean_is_exclusive(v___x_2801_);
if (v_isSharedCheck_3041_ == 0)
{
v___x_3036_ = v___x_2801_;
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
else
{
lean_inc(v_a_3034_);
lean_dec(v___x_2801_);
v___x_3036_ = lean_box(0);
v_isShared_3037_ = v_isSharedCheck_3041_;
goto v_resetjp_3035_;
}
v_resetjp_3035_:
{
lean_object* v___x_3039_; 
if (v_isShared_3037_ == 0)
{
v___x_3039_ = v___x_3036_;
goto v_reusejp_3038_;
}
else
{
lean_object* v_reuseFailAlloc_3040_; 
v_reuseFailAlloc_3040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3040_, 0, v_a_3034_);
v___x_3039_ = v_reuseFailAlloc_3040_;
goto v_reusejp_3038_;
}
v_reusejp_3038_:
{
return v___x_3039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object* v_mvarId_3042_, lean_object* v_substLHS_3043_, lean_object* v___y_3044_, lean_object* v___y_3045_, lean_object* v___y_3046_, lean_object* v___y_3047_, lean_object* v___y_3048_){
_start:
{
uint8_t v_substLHS_boxed_3049_; lean_object* v_res_3050_; 
v_substLHS_boxed_3049_ = lean_unbox(v_substLHS_3043_);
v_res_3050_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_3042_, v_substLHS_boxed_3049_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_);
lean_dec(v___y_3047_);
lean_dec_ref(v___y_3046_);
lean_dec(v___y_3045_);
lean_dec_ref(v___y_3044_);
return v_res_3050_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3051_, lean_object* v_i_3052_, lean_object* v_k_3053_){
_start:
{
lean_object* v___x_3054_; uint8_t v___x_3055_; 
v___x_3054_ = lean_array_get_size(v_keys_3051_);
v___x_3055_ = lean_nat_dec_lt(v_i_3052_, v___x_3054_);
if (v___x_3055_ == 0)
{
lean_dec(v_i_3052_);
return v___x_3055_;
}
else
{
lean_object* v_k_x27_3056_; uint8_t v___x_3057_; 
v_k_x27_3056_ = lean_array_fget_borrowed(v_keys_3051_, v_i_3052_);
v___x_3057_ = l_Lean_instBEqMVarId_beq(v_k_3053_, v_k_x27_3056_);
if (v___x_3057_ == 0)
{
lean_object* v___x_3058_; lean_object* v___x_3059_; 
v___x_3058_ = lean_unsigned_to_nat(1u);
v___x_3059_ = lean_nat_add(v_i_3052_, v___x_3058_);
lean_dec(v_i_3052_);
v_i_3052_ = v___x_3059_;
goto _start;
}
else
{
lean_dec(v_i_3052_);
return v___x_3055_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3061_, lean_object* v_i_3062_, lean_object* v_k_3063_){
_start:
{
uint8_t v_res_3064_; lean_object* v_r_3065_; 
v_res_3064_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3061_, v_i_3062_, v_k_3063_);
lean_dec(v_k_3063_);
lean_dec_ref(v_keys_3061_);
v_r_3065_ = lean_box(v_res_3064_);
return v_r_3065_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3066_, size_t v_x_3067_, lean_object* v_x_3068_){
_start:
{
if (lean_obj_tag(v_x_3066_) == 0)
{
lean_object* v_es_3069_; lean_object* v___x_3070_; size_t v___x_3071_; size_t v___x_3072_; lean_object* v_j_3073_; lean_object* v___x_3074_; 
v_es_3069_ = lean_ctor_get(v_x_3066_, 0);
v___x_3070_ = lean_box(2);
v___x_3071_ = ((size_t)31ULL);
v___x_3072_ = lean_usize_land(v_x_3067_, v___x_3071_);
v_j_3073_ = lean_usize_to_nat(v___x_3072_);
v___x_3074_ = lean_array_get_borrowed(v___x_3070_, v_es_3069_, v_j_3073_);
lean_dec(v_j_3073_);
switch(lean_obj_tag(v___x_3074_))
{
case 0:
{
lean_object* v_key_3075_; uint8_t v___x_3076_; 
v_key_3075_ = lean_ctor_get(v___x_3074_, 0);
v___x_3076_ = l_Lean_instBEqMVarId_beq(v_x_3068_, v_key_3075_);
return v___x_3076_;
}
case 1:
{
lean_object* v_node_3077_; size_t v___x_3078_; size_t v___x_3079_; 
v_node_3077_ = lean_ctor_get(v___x_3074_, 0);
v___x_3078_ = ((size_t)5ULL);
v___x_3079_ = lean_usize_shift_right(v_x_3067_, v___x_3078_);
v_x_3066_ = v_node_3077_;
v_x_3067_ = v___x_3079_;
goto _start;
}
default: 
{
uint8_t v___x_3081_; 
v___x_3081_ = 0;
return v___x_3081_;
}
}
}
else
{
lean_object* v_ks_3082_; lean_object* v___x_3083_; uint8_t v___x_3084_; 
v_ks_3082_ = lean_ctor_get(v_x_3066_, 0);
v___x_3083_ = lean_unsigned_to_nat(0u);
v___x_3084_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3082_, v___x_3083_, v_x_3068_);
return v___x_3084_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3085_, lean_object* v_x_3086_, lean_object* v_x_3087_){
_start:
{
size_t v_x_10584__boxed_3088_; uint8_t v_res_3089_; lean_object* v_r_3090_; 
v_x_10584__boxed_3088_ = lean_unbox_usize(v_x_3086_);
lean_dec(v_x_3086_);
v_res_3089_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3085_, v_x_10584__boxed_3088_, v_x_3087_);
lean_dec(v_x_3087_);
lean_dec_ref(v_x_3085_);
v_r_3090_ = lean_box(v_res_3089_);
return v_r_3090_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
uint64_t v___x_3093_; size_t v___x_3094_; uint8_t v___x_3095_; 
v___x_3093_ = l_Lean_instHashableMVarId_hash(v_x_3092_);
v___x_3094_ = lean_uint64_to_usize(v___x_3093_);
v___x_3095_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3091_, v___x_3094_, v_x_3092_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3096_, lean_object* v_x_3097_){
_start:
{
uint8_t v_res_3098_; lean_object* v_r_3099_; 
v_res_3098_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3096_, v_x_3097_);
lean_dec(v_x_3097_);
lean_dec_ref(v_x_3096_);
v_r_3099_ = lean_box(v_res_3098_);
return v_r_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; lean_object* v_mctx_3104_; lean_object* v_eAssignment_3105_; uint8_t v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3103_ = lean_st_ref_get(v___y_3101_);
v_mctx_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc_ref(v_mctx_3104_);
lean_dec(v___x_3103_);
v_eAssignment_3105_ = lean_ctor_get(v_mctx_3104_, 8);
lean_inc_ref(v_eAssignment_3105_);
lean_dec_ref(v_mctx_3104_);
v___x_3106_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3105_, v_mvarId_3100_);
lean_dec_ref(v_eAssignment_3105_);
v___x_3107_ = lean_box(v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v_res_3112_; 
v_res_3112_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3109_, v___y_3110_);
lean_dec(v___y_3110_);
lean_dec(v_mvarId_3109_);
return v_res_3112_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3114_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3115_ = l_Lean_stringToMessageData(v___x_3114_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3116_, uint8_t v___x_3117_, lean_object* v_____r_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___x_3156_; lean_object* v_a_3157_; uint8_t v___x_3158_; 
v___x_3156_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3116_, v___y_3120_);
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3157_);
lean_dec_ref(v___x_3156_);
v___x_3158_ = lean_unbox(v_a_3157_);
lean_dec(v_a_3157_);
if (v___x_3158_ == 0)
{
goto v___jp_3124_;
}
else
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v_a_3161_; lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3168_; 
lean_dec(v_mvarId_3116_);
v___x_3159_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3160_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3159_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
v_a_3161_ = lean_ctor_get(v___x_3160_, 0);
v_isSharedCheck_3168_ = !lean_is_exclusive(v___x_3160_);
if (v_isSharedCheck_3168_ == 0)
{
v___x_3163_ = v___x_3160_;
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
else
{
lean_inc(v_a_3161_);
lean_dec(v___x_3160_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3168_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3166_; 
if (v_isShared_3164_ == 0)
{
v___x_3166_ = v___x_3163_;
goto v_reusejp_3165_;
}
else
{
lean_object* v_reuseFailAlloc_3167_; 
v_reuseFailAlloc_3167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3167_, 0, v_a_3161_);
v___x_3166_ = v_reuseFailAlloc_3167_;
goto v_reusejp_3165_;
}
v_reusejp_3165_:
{
return v___x_3166_;
}
}
}
v___jp_3124_:
{
lean_object* v___x_3125_; 
v___x_3125_ = l_Lean_Meta_intro1Core(v_mvarId_3116_, v___x_3117_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v_fst_3127_; lean_object* v_snd_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
lean_inc(v_a_3126_);
lean_dec_ref_known(v___x_3125_, 1);
v_fst_3127_ = lean_ctor_get(v_a_3126_, 0);
lean_inc(v_fst_3127_);
v_snd_3128_ = lean_ctor_get(v_a_3126_, 1);
lean_inc(v_snd_3128_);
lean_dec(v_a_3126_);
v___x_3129_ = lean_box(0);
v___x_3130_ = l_Lean_Meta_substEq(v_snd_3128_, v_fst_3127_, v___x_3129_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
if (lean_obj_tag(v___x_3130_) == 0)
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3139_; 
v_a_3131_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3139_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3139_ == 0)
{
v___x_3133_ = v___x_3130_;
v_isShared_3134_ = v_isSharedCheck_3139_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3130_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3139_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3135_; lean_object* v___x_3137_; 
v___x_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3135_, 0, v_a_3131_);
if (v_isShared_3134_ == 0)
{
lean_ctor_set(v___x_3133_, 0, v___x_3135_);
v___x_3137_ = v___x_3133_;
goto v_reusejp_3136_;
}
else
{
lean_object* v_reuseFailAlloc_3138_; 
v_reuseFailAlloc_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3138_, 0, v___x_3135_);
v___x_3137_ = v_reuseFailAlloc_3138_;
goto v_reusejp_3136_;
}
v_reusejp_3136_:
{
return v___x_3137_;
}
}
}
else
{
lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
v_a_3140_ = lean_ctor_get(v___x_3130_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3130_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3130_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3130_);
v___x_3142_ = lean_box(0);
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
v_resetjp_3141_:
{
lean_object* v___x_3145_; 
if (v_isShared_3143_ == 0)
{
v___x_3145_ = v___x_3142_;
goto v_reusejp_3144_;
}
else
{
lean_object* v_reuseFailAlloc_3146_; 
v_reuseFailAlloc_3146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3146_, 0, v_a_3140_);
v___x_3145_ = v_reuseFailAlloc_3146_;
goto v_reusejp_3144_;
}
v_reusejp_3144_:
{
return v___x_3145_;
}
}
}
}
else
{
lean_object* v_a_3148_; lean_object* v___x_3150_; uint8_t v_isShared_3151_; uint8_t v_isSharedCheck_3155_; 
v_a_3148_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3155_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3155_ == 0)
{
v___x_3150_ = v___x_3125_;
v_isShared_3151_ = v_isSharedCheck_3155_;
goto v_resetjp_3149_;
}
else
{
lean_inc(v_a_3148_);
lean_dec(v___x_3125_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3169_, lean_object* v___x_3170_, lean_object* v_____r_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
uint8_t v___x_10656__boxed_3177_; lean_object* v_res_3178_; 
v___x_10656__boxed_3177_ = lean_unbox(v___x_3170_);
v_res_3178_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3169_, v___x_10656__boxed_3177_, v_____r_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
lean_dec(v___y_3175_);
lean_dec_ref(v___y_3174_);
lean_dec(v___y_3173_);
lean_dec_ref(v___y_3172_);
return v_res_3178_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__2(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3182_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3183_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
v___x_3184_ = l_Lean_Name_append(v___x_3183_, v___x_3182_);
return v___x_3184_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__4(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__3));
v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
return v___x_3187_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__6(void){
_start:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__5));
v___x_3190_ = l_Lean_stringToMessageData(v___x_3189_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3191_, uint8_t v_substLHS_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_, lean_object* v_a_3196_){
_start:
{
lean_object* v___y_3199_; lean_object* v___x_3217_; lean_object* v___f_3218_; lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3217_ = lean_box(v_substLHS_3192_);
lean_inc_n(v_mvarId_3191_, 2);
v___f_3218_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3218_, 0, v_mvarId_3191_);
lean_closure_set(v___f_3218_, 1, v___x_3217_);
v___x_3219_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
v___x_3220_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3191_, v___x_3219_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
lean_dec_ref_known(v___x_3220_, 1);
lean_inc(v_mvarId_3191_);
v___x_3221_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed), 8, 3);
lean_closure_set(v___x_3221_, 0, lean_box(0));
lean_closure_set(v___x_3221_, 1, v_mvarId_3191_);
lean_closure_set(v___x_3221_, 2, v___f_3218_);
v___x_3222_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3221_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
if (lean_obj_tag(v___x_3222_) == 0)
{
lean_dec(v_mvarId_3191_);
return v___x_3222_;
}
else
{
lean_object* v_a_3223_; uint8_t v___x_3224_; 
v_a_3223_ = lean_ctor_get(v___x_3222_, 0);
v___x_3224_ = l_Lean_Exception_isInterrupt(v_a_3223_);
if (v___x_3224_ == 0)
{
uint8_t v___x_3225_; 
lean_inc(v_a_3223_);
v___x_3225_ = l_Lean_Exception_isRuntime(v_a_3223_);
if (v___x_3225_ == 0)
{
lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3259_; 
lean_inc(v_a_3223_);
v_isSharedCheck_3259_ = !lean_is_exclusive(v___x_3222_);
if (v_isSharedCheck_3259_ == 0)
{
lean_object* v_unused_3260_; 
v_unused_3260_ = lean_ctor_get(v___x_3222_, 0);
lean_dec(v_unused_3260_);
v___x_3227_ = v___x_3222_;
v_isShared_3228_ = v_isSharedCheck_3259_;
goto v_resetjp_3226_;
}
else
{
lean_dec(v___x_3222_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3259_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v_toCold_3229_; lean_object* v_options_3230_; lean_object* v_inheritedTraceOptions_3231_; uint8_t v_hasTrace_3232_; 
v_toCold_3229_ = lean_ctor_get(v_a_3195_, 0);
v_options_3230_ = lean_ctor_get(v_toCold_3229_, 2);
v_inheritedTraceOptions_3231_ = lean_ctor_get(v_toCold_3229_, 11);
v_hasTrace_3232_ = lean_ctor_get_uint8(v_options_3230_, sizeof(void*)*1);
if (v_hasTrace_3232_ == 0)
{
lean_del_object(v___x_3227_);
lean_dec(v_a_3223_);
goto v___jp_3233_;
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; uint8_t v___x_3238_; 
v___x_3236_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3237_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__2, &l_Lean_Meta_introSubstEq___closed__2_once, _init_l_Lean_Meta_introSubstEq___closed__2);
v___x_3238_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3231_, v_options_3230_, v___x_3237_);
if (v___x_3238_ == 0)
{
lean_del_object(v___x_3227_);
lean_dec(v_a_3223_);
goto v___jp_3233_;
}
else
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3239_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__4, &l_Lean_Meta_introSubstEq___closed__4_once, _init_l_Lean_Meta_introSubstEq___closed__4);
v___x_3240_ = l_Lean_Exception_toMessageData(v_a_3223_);
v___x_3241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3239_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__6, &l_Lean_Meta_introSubstEq___closed__6_once, _init_l_Lean_Meta_introSubstEq___closed__6);
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3241_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
lean_inc(v_mvarId_3191_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v_mvarId_3191_);
v___x_3245_ = v___x_3227_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3258_; 
v_reuseFailAlloc_3258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_mvarId_3191_);
v___x_3245_ = v_reuseFailAlloc_3258_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; lean_object* v___x_3247_; 
v___x_3246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3243_);
lean_ctor_set(v___x_3246_, 1, v___x_3245_);
v___x_3247_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_3236_, v___x_3246_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v_a_3248_; lean_object* v___x_3249_; 
v_a_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_a_3248_);
lean_dec_ref_known(v___x_3247_, 1);
v___x_3249_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3191_, v___x_3225_, v_a_3248_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
v___y_3199_ = v___x_3249_;
goto v___jp_3198_;
}
else
{
lean_object* v_a_3250_; lean_object* v___x_3252_; uint8_t v_isShared_3253_; uint8_t v_isSharedCheck_3257_; 
lean_dec(v_mvarId_3191_);
v_a_3250_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3252_ = v___x_3247_;
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
else
{
lean_inc(v_a_3250_);
lean_dec(v___x_3247_);
v___x_3252_ = lean_box(0);
v_isShared_3253_ = v_isSharedCheck_3257_;
goto v_resetjp_3251_;
}
v_resetjp_3251_:
{
lean_object* v___x_3255_; 
if (v_isShared_3253_ == 0)
{
v___x_3255_ = v___x_3252_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v_a_3250_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
}
v___jp_3233_:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = lean_box(0);
v___x_3235_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3191_, v___x_3225_, v___x_3234_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
v___y_3199_ = v___x_3235_;
goto v___jp_3198_;
}
}
}
else
{
lean_dec(v_mvarId_3191_);
return v___x_3222_;
}
}
else
{
lean_dec(v_mvarId_3191_);
return v___x_3222_;
}
}
}
else
{
lean_object* v_a_3261_; lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3268_; 
lean_dec_ref(v___f_3218_);
lean_dec(v_mvarId_3191_);
v_a_3261_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3268_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3268_ == 0)
{
v___x_3263_ = v___x_3220_;
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
else
{
lean_inc(v_a_3261_);
lean_dec(v___x_3220_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3268_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3266_; 
if (v_isShared_3264_ == 0)
{
v___x_3266_ = v___x_3263_;
goto v_reusejp_3265_;
}
else
{
lean_object* v_reuseFailAlloc_3267_; 
v_reuseFailAlloc_3267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3267_, 0, v_a_3261_);
v___x_3266_ = v_reuseFailAlloc_3267_;
goto v_reusejp_3265_;
}
v_reusejp_3265_:
{
return v___x_3266_;
}
}
}
v___jp_3198_:
{
if (lean_obj_tag(v___y_3199_) == 0)
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3208_; 
v_a_3200_ = lean_ctor_get(v___y_3199_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___y_3199_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3202_ = v___y_3199_;
v_isShared_3203_ = v_isSharedCheck_3208_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___y_3199_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3208_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v_a_3204_; lean_object* v___x_3206_; 
v_a_3204_ = lean_ctor_get(v_a_3200_, 0);
lean_inc(v_a_3204_);
lean_dec(v_a_3200_);
if (v_isShared_3203_ == 0)
{
lean_ctor_set(v___x_3202_, 0, v_a_3204_);
v___x_3206_ = v___x_3202_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3204_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
v_a_3209_ = lean_ctor_get(v___y_3199_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___y_3199_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___y_3199_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___y_3199_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object* v_mvarId_3269_, lean_object* v_substLHS_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_){
_start:
{
uint8_t v_substLHS_boxed_3276_; lean_object* v_res_3277_; 
v_substLHS_boxed_3276_ = lean_unbox(v_substLHS_3270_);
v_res_3277_ = l_Lean_Meta_introSubstEq(v_mvarId_3269_, v_substLHS_boxed_3276_, v_a_3271_, v_a_3272_, v_a_3273_, v_a_3274_);
lean_dec(v_a_3274_);
lean_dec_ref(v_a_3273_);
lean_dec(v_a_3272_);
lean_dec_ref(v_a_3271_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object* v_00_u03b1_3278_, lean_object* v_msg_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_){
_start:
{
lean_object* v___x_3285_; 
v___x_3285_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_3279_, v___y_3280_, v___y_3281_, v___y_3282_, v___y_3283_);
return v___x_3285_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object* v_00_u03b1_3286_, lean_object* v_msg_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
lean_object* v_res_3293_; 
v_res_3293_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(v_00_u03b1_3286_, v_msg_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
return v_res_3293_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object* v_mvarId_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_){
_start:
{
lean_object* v___x_3300_; 
v___x_3300_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3294_, v___y_3296_);
return v___x_3300_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object* v_mvarId_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
lean_dec(v___y_3303_);
lean_dec_ref(v___y_3302_);
lean_dec(v_mvarId_3301_);
return v_res_3307_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object* v_00_u03b2_3308_, lean_object* v_x_3309_, lean_object* v_x_3310_){
_start:
{
uint8_t v___x_3311_; 
v___x_3311_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3309_, v_x_3310_);
return v___x_3311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3312_, lean_object* v_x_3313_, lean_object* v_x_3314_){
_start:
{
uint8_t v_res_3315_; lean_object* v_r_3316_; 
v_res_3315_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(v_00_u03b2_3312_, v_x_3313_, v_x_3314_);
lean_dec(v_x_3314_);
lean_dec_ref(v_x_3313_);
v_r_3316_ = lean_box(v_res_3315_);
return v_r_3316_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_3317_, lean_object* v_x_3318_, size_t v_x_3319_, lean_object* v_x_3320_){
_start:
{
uint8_t v___x_3321_; 
v___x_3321_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3318_, v_x_3319_, v_x_3320_);
return v___x_3321_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3322_, lean_object* v_x_3323_, lean_object* v_x_3324_, lean_object* v_x_3325_){
_start:
{
size_t v_x_11002__boxed_3326_; uint8_t v_res_3327_; lean_object* v_r_3328_; 
v_x_11002__boxed_3326_ = lean_unbox_usize(v_x_3324_);
lean_dec(v_x_3324_);
v_res_3327_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3322_, v_x_3323_, v_x_11002__boxed_3326_, v_x_3325_);
lean_dec(v_x_3325_);
lean_dec_ref(v_x_3323_);
v_r_3328_ = lean_box(v_res_3327_);
return v_r_3328_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3329_, lean_object* v_keys_3330_, lean_object* v_vals_3331_, lean_object* v_heq_3332_, lean_object* v_i_3333_, lean_object* v_k_3334_){
_start:
{
uint8_t v___x_3335_; 
v___x_3335_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3330_, v_i_3333_, v_k_3334_);
return v___x_3335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3336_, lean_object* v_keys_3337_, lean_object* v_vals_3338_, lean_object* v_heq_3339_, lean_object* v_i_3340_, lean_object* v_k_3341_){
_start:
{
uint8_t v_res_3342_; lean_object* v_r_3343_; 
v_res_3342_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(v_00_u03b2_3336_, v_keys_3337_, v_vals_3338_, v_heq_3339_, v_i_3340_, v_k_3341_);
lean_dec(v_k_3341_);
lean_dec_ref(v_vals_3338_);
lean_dec_ref(v_keys_3337_);
v_r_3343_ = lean_box(v_res_3342_);
return v_r_3343_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* v_x_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
lean_object* v___x_3350_; 
v___x_3350_ = l_Lean_Meta_saveState___redArg(v___y_3346_, v___y_3348_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v___x_3352_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
lean_inc(v___y_3348_);
lean_inc_ref(v___y_3347_);
lean_inc(v___y_3346_);
lean_inc_ref(v___y_3345_);
v___x_3352_ = lean_apply_5(v_x_3344_, v___y_3345_, v___y_3346_, v___y_3347_, v___y_3348_, lean_box(0));
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; lean_object* v___x_3355_; uint8_t v_isShared_3356_; uint8_t v_isSharedCheck_3361_; 
lean_dec(v_a_3351_);
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3361_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3361_ == 0)
{
v___x_3355_ = v___x_3352_;
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
else
{
lean_inc(v_a_3353_);
lean_dec(v___x_3352_);
v___x_3355_ = lean_box(0);
v_isShared_3356_ = v_isSharedCheck_3361_;
goto v_resetjp_3354_;
}
v_resetjp_3354_:
{
lean_object* v___x_3357_; lean_object* v___x_3359_; 
v___x_3357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3357_, 0, v_a_3353_);
if (v_isShared_3356_ == 0)
{
lean_ctor_set(v___x_3355_, 0, v___x_3357_);
v___x_3359_ = v___x_3355_;
goto v_reusejp_3358_;
}
else
{
lean_object* v_reuseFailAlloc_3360_; 
v_reuseFailAlloc_3360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3360_, 0, v___x_3357_);
v___x_3359_ = v_reuseFailAlloc_3360_;
goto v_reusejp_3358_;
}
v_reusejp_3358_:
{
return v___x_3359_;
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3392_; 
v_a_3362_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3364_ = v___x_3352_;
v_isShared_3365_ = v_isSharedCheck_3392_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3352_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3392_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
uint8_t v___x_3366_; 
v___x_3366_ = l_Lean_Exception_isInterrupt(v_a_3362_);
if (v___x_3366_ == 0)
{
uint8_t v___x_3367_; 
lean_inc(v_a_3362_);
v___x_3367_ = l_Lean_Exception_isRuntime(v_a_3362_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; 
lean_del_object(v___x_3364_);
lean_dec(v_a_3362_);
v___x_3368_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3351_, v___y_3346_, v___y_3348_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3376_; 
v_isSharedCheck_3376_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3376_ == 0)
{
lean_object* v_unused_3377_; 
v_unused_3377_ = lean_ctor_get(v___x_3368_, 0);
lean_dec(v_unused_3377_);
v___x_3370_ = v___x_3368_;
v_isShared_3371_ = v_isSharedCheck_3376_;
goto v_resetjp_3369_;
}
else
{
lean_dec(v___x_3368_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3376_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3372_ = lean_box(0);
if (v_isShared_3371_ == 0)
{
lean_ctor_set(v___x_3370_, 0, v___x_3372_);
v___x_3374_ = v___x_3370_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3375_; 
v_reuseFailAlloc_3375_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3375_, 0, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3375_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
return v___x_3374_;
}
}
}
else
{
lean_object* v_a_3378_; lean_object* v___x_3380_; uint8_t v_isShared_3381_; uint8_t v_isSharedCheck_3385_; 
v_a_3378_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3385_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3385_ == 0)
{
v___x_3380_ = v___x_3368_;
v_isShared_3381_ = v_isSharedCheck_3385_;
goto v_resetjp_3379_;
}
else
{
lean_inc(v_a_3378_);
lean_dec(v___x_3368_);
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
else
{
lean_object* v___x_3387_; 
lean_dec(v_a_3351_);
if (v_isShared_3365_ == 0)
{
v___x_3387_ = v___x_3364_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3362_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
else
{
lean_object* v___x_3390_; 
lean_dec(v_a_3351_);
if (v_isShared_3365_ == 0)
{
v___x_3390_ = v___x_3364_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3362_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
return v___x_3390_;
}
}
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec_ref(v_x_3344_);
v_a_3393_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3350_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3350_);
v___x_3395_ = lean_box(0);
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
v_resetjp_3394_:
{
lean_object* v___x_3398_; 
if (v_isShared_3396_ == 0)
{
v___x_3398_ = v___x_3395_;
goto v_reusejp_3397_;
}
else
{
lean_object* v_reuseFailAlloc_3399_; 
v_reuseFailAlloc_3399_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3399_, 0, v_a_3393_);
v___x_3398_ = v_reuseFailAlloc_3399_;
goto v_reusejp_3397_;
}
v_reusejp_3397_:
{
return v___x_3398_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object* v_x_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_){
_start:
{
lean_object* v_res_3407_; 
v_res_3407_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3401_, v___y_3402_, v___y_3403_, v___y_3404_, v___y_3405_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
return v_res_3407_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object* v_00_u03b1_3408_, lean_object* v_x_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
lean_object* v___x_3415_; 
v___x_3415_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3409_, v___y_3410_, v___y_3411_, v___y_3412_, v___y_3413_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object* v_00_u03b1_3416_, lean_object* v_x_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(v_00_u03b1_3416_, v_x_3417_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* v_mvarId_3424_, lean_object* v_hFVarId_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___boxed), 7, 2);
lean_closure_set(v___x_3431_, 0, v_mvarId_3424_);
lean_closure_set(v___x_3431_, 1, v_hFVarId_3425_);
v___x_3432_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3431_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object* v_mvarId_3433_, lean_object* v_hFVarId_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Meta_substVar_x3f(v_mvarId_3433_, v_hFVarId_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* v_mvarId_3441_, lean_object* v_hFVarId_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_){
_start:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; 
v___x_3448_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 7, 2);
lean_closure_set(v___x_3448_, 0, v_mvarId_3441_);
lean_closure_set(v___x_3448_, 1, v_hFVarId_3442_);
v___x_3449_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3448_, v_a_3443_, v_a_3444_, v_a_3445_, v_a_3446_);
return v___x_3449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object* v_mvarId_3450_, lean_object* v_hFVarId_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_){
_start:
{
lean_object* v_res_3457_; 
v_res_3457_ = l_Lean_Meta_subst_x3f(v_mvarId_3450_, v_hFVarId_3451_, v_a_3452_, v_a_3453_, v_a_3454_, v_a_3455_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
return v_res_3457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* v_mvarId_3458_, lean_object* v_hFVarId_3459_, uint8_t v_symm_3460_, lean_object* v_fvarSubst_3461_, uint8_t v_clearH_3462_, uint8_t v_tryToSkip_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; 
v___x_3469_ = lean_box(v_symm_3460_);
v___x_3470_ = lean_box(v_clearH_3462_);
v___x_3471_ = lean_box(v_tryToSkip_3463_);
v___x_3472_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_3472_, 0, v_mvarId_3458_);
lean_closure_set(v___x_3472_, 1, v_hFVarId_3459_);
lean_closure_set(v___x_3472_, 2, v___x_3469_);
lean_closure_set(v___x_3472_, 3, v_fvarSubst_3461_);
lean_closure_set(v___x_3472_, 4, v___x_3470_);
lean_closure_set(v___x_3472_, 5, v___x_3471_);
v___x_3473_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3472_, v_a_3464_, v_a_3465_, v_a_3466_, v_a_3467_);
return v___x_3473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* v_mvarId_3474_, lean_object* v_hFVarId_3475_, lean_object* v_symm_3476_, lean_object* v_fvarSubst_3477_, lean_object* v_clearH_3478_, lean_object* v_tryToSkip_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_){
_start:
{
uint8_t v_symm_boxed_3485_; uint8_t v_clearH_boxed_3486_; uint8_t v_tryToSkip_boxed_3487_; lean_object* v_res_3488_; 
v_symm_boxed_3485_ = lean_unbox(v_symm_3476_);
v_clearH_boxed_3486_ = lean_unbox(v_clearH_3478_);
v_tryToSkip_boxed_3487_ = lean_unbox(v_tryToSkip_3479_);
v_res_3488_ = l_Lean_Meta_substCore_x3f(v_mvarId_3474_, v_hFVarId_3475_, v_symm_boxed_3485_, v_fvarSubst_3477_, v_clearH_boxed_3486_, v_tryToSkip_boxed_3487_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
return v_res_3488_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* v_mvarId_3489_, lean_object* v_hFVarId_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_){
_start:
{
lean_object* v___x_3496_; 
lean_inc(v_mvarId_3489_);
v___x_3496_ = l_Lean_Meta_substVar_x3f(v_mvarId_3489_, v_hFVarId_3490_, v_a_3491_, v_a_3492_, v_a_3493_, v_a_3494_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3508_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3508_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3508_ == 0)
{
v___x_3499_ = v___x_3496_;
v_isShared_3500_ = v_isSharedCheck_3508_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3496_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3508_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
if (lean_obj_tag(v_a_3497_) == 0)
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v_mvarId_3489_);
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_mvarId_3489_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
else
{
lean_object* v_val_3504_; lean_object* v___x_3506_; 
lean_dec(v_mvarId_3489_);
v_val_3504_ = lean_ctor_get(v_a_3497_, 0);
lean_inc(v_val_3504_);
lean_dec_ref_known(v_a_3497_, 1);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v_val_3504_);
v___x_3506_ = v___x_3499_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3507_; 
v_reuseFailAlloc_3507_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3507_, 0, v_val_3504_);
v___x_3506_ = v_reuseFailAlloc_3507_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
return v___x_3506_;
}
}
}
}
else
{
lean_object* v_a_3509_; lean_object* v___x_3511_; uint8_t v_isShared_3512_; uint8_t v_isSharedCheck_3516_; 
lean_dec(v_mvarId_3489_);
v_a_3509_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3516_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3516_ == 0)
{
v___x_3511_ = v___x_3496_;
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
else
{
lean_inc(v_a_3509_);
lean_dec(v___x_3496_);
v___x_3511_ = lean_box(0);
v_isShared_3512_ = v_isSharedCheck_3516_;
goto v_resetjp_3510_;
}
v_resetjp_3510_:
{
lean_object* v___x_3514_; 
if (v_isShared_3512_ == 0)
{
v___x_3514_ = v___x_3511_;
goto v_reusejp_3513_;
}
else
{
lean_object* v_reuseFailAlloc_3515_; 
v_reuseFailAlloc_3515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3515_, 0, v_a_3509_);
v___x_3514_ = v_reuseFailAlloc_3515_;
goto v_reusejp_3513_;
}
v_reusejp_3513_:
{
return v___x_3514_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object* v_mvarId_3517_, lean_object* v_hFVarId_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_){
_start:
{
lean_object* v_res_3524_; 
v_res_3524_ = l_Lean_Meta_trySubstVar(v_mvarId_3517_, v_hFVarId_3518_, v_a_3519_, v_a_3520_, v_a_3521_, v_a_3522_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
return v_res_3524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* v_mvarId_3525_, lean_object* v_hFVarId_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_){
_start:
{
lean_object* v___x_3532_; 
lean_inc(v_mvarId_3525_);
v___x_3532_ = l_Lean_Meta_subst_x3f(v_mvarId_3525_, v_hFVarId_3526_, v_a_3527_, v_a_3528_, v_a_3529_, v_a_3530_);
if (lean_obj_tag(v___x_3532_) == 0)
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3544_; 
v_a_3533_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3535_ = v___x_3532_;
v_isShared_3536_ = v_isSharedCheck_3544_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3532_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3544_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
if (lean_obj_tag(v_a_3533_) == 0)
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v_mvarId_3525_);
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_mvarId_3525_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
else
{
lean_object* v_val_3540_; lean_object* v___x_3542_; 
lean_dec(v_mvarId_3525_);
v_val_3540_ = lean_ctor_get(v_a_3533_, 0);
lean_inc(v_val_3540_);
lean_dec_ref_known(v_a_3533_, 1);
if (v_isShared_3536_ == 0)
{
lean_ctor_set(v___x_3535_, 0, v_val_3540_);
v___x_3542_ = v___x_3535_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_val_3540_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
lean_object* v_a_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3552_; 
lean_dec(v_mvarId_3525_);
v_a_3545_ = lean_ctor_get(v___x_3532_, 0);
v_isSharedCheck_3552_ = !lean_is_exclusive(v___x_3532_);
if (v_isSharedCheck_3552_ == 0)
{
v___x_3547_ = v___x_3532_;
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_a_3545_);
lean_dec(v___x_3532_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3552_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3550_; 
if (v_isShared_3548_ == 0)
{
v___x_3550_ = v___x_3547_;
goto v_reusejp_3549_;
}
else
{
lean_object* v_reuseFailAlloc_3551_; 
v_reuseFailAlloc_3551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3551_, 0, v_a_3545_);
v___x_3550_ = v_reuseFailAlloc_3551_;
goto v_reusejp_3549_;
}
v_reusejp_3549_:
{
return v___x_3550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object* v_mvarId_3553_, lean_object* v_hFVarId_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_){
_start:
{
lean_object* v_res_3560_; 
v_res_3560_ = l_Lean_Meta_trySubst(v_mvarId_3553_, v_hFVarId_3554_, v_a_3555_, v_a_3556_, v_a_3557_, v_a_3558_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_mvarId_3564_, lean_object* v_as_3565_, size_t v_sz_3566_, size_t v_i_3567_, lean_object* v_b_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_){
_start:
{
uint8_t v___x_3574_; 
v___x_3574_ = lean_usize_dec_lt(v_i_3567_, v_sz_3566_);
if (v___x_3574_ == 0)
{
lean_object* v___x_3575_; 
lean_dec(v_mvarId_3564_);
v___x_3575_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3575_, 0, v_b_3568_);
return v___x_3575_;
}
else
{
lean_object* v_snd_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3629_; 
v_snd_3576_ = lean_ctor_get(v_b_3568_, 1);
v_isSharedCheck_3629_ = !lean_is_exclusive(v_b_3568_);
if (v_isSharedCheck_3629_ == 0)
{
lean_object* v_unused_3630_; 
v_unused_3630_ = lean_ctor_get(v_b_3568_, 0);
lean_dec(v_unused_3630_);
v___x_3578_ = v_b_3568_;
v_isShared_3579_ = v_isSharedCheck_3629_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_snd_3576_);
lean_dec(v_b_3568_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3629_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3580_; lean_object* v_a_3582_; lean_object* v_a_3589_; 
v___x_3580_ = lean_box(0);
v_a_3589_ = lean_array_uget(v_as_3565_, v_i_3567_);
if (lean_obj_tag(v_a_3589_) == 0)
{
v_a_3582_ = v_snd_3576_;
goto v___jp_3581_;
}
else
{
lean_object* v_val_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3628_; 
v_val_3590_ = lean_ctor_get(v_a_3589_, 0);
v_isSharedCheck_3628_ = !lean_is_exclusive(v_a_3589_);
if (v_isSharedCheck_3628_ == 0)
{
v___x_3592_ = v_a_3589_;
v_isShared_3593_ = v_isSharedCheck_3628_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_val_3590_);
lean_dec(v_a_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3628_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3594_ = lean_box(0);
v___x_3595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3596_ = l_Lean_LocalDecl_fvarId(v_val_3590_);
lean_dec(v_val_3590_);
lean_inc(v_mvarId_3564_);
v___x_3597_ = l_Lean_Meta_subst_x3f(v_mvarId_3564_, v___x_3596_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3619_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3619_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3619_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
if (lean_obj_tag(v_a_3598_) == 1)
{
lean_object* v___x_3603_; 
lean_del_object(v___x_3578_);
lean_dec(v_mvarId_3564_);
lean_inc_ref(v_a_3598_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v_a_3598_);
v___x_3603_ = v___x_3592_;
goto v_reusejp_3602_;
}
else
{
lean_object* v_reuseFailAlloc_3618_; 
v_reuseFailAlloc_3618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3618_, 0, v_a_3598_);
v___x_3603_ = v_reuseFailAlloc_3618_;
goto v_reusejp_3602_;
}
v_reusejp_3602_:
{
lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3616_; 
v_isSharedCheck_3616_ = !lean_is_exclusive(v_a_3598_);
if (v_isSharedCheck_3616_ == 0)
{
lean_object* v_unused_3617_; 
v_unused_3617_ = lean_ctor_get(v_a_3598_, 0);
lean_dec(v_unused_3617_);
v___x_3605_ = v_a_3598_;
v_isShared_3606_ = v_isSharedCheck_3616_;
goto v_resetjp_3604_;
}
else
{
lean_dec(v_a_3598_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3616_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3607_; lean_object* v___x_3609_; 
v___x_3607_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3603_);
lean_ctor_set(v___x_3607_, 1, v___x_3594_);
if (v_isShared_3606_ == 0)
{
lean_ctor_set_tag(v___x_3605_, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3607_);
v___x_3609_ = v___x_3605_;
goto v_reusejp_3608_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v___x_3607_);
v___x_3609_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3608_;
}
v_reusejp_3608_:
{
lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3613_; 
v___x_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
v___x_3611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3610_);
lean_ctor_set(v___x_3611_, 1, v_snd_3576_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3611_);
v___x_3613_ = v___x_3600_;
goto v_reusejp_3612_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3611_);
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
else
{
lean_del_object(v___x_3600_);
lean_dec(v_a_3598_);
lean_del_object(v___x_3592_);
lean_dec(v_snd_3576_);
v_a_3582_ = v___x_3595_;
goto v___jp_3581_;
}
}
}
else
{
lean_object* v_a_3620_; lean_object* v___x_3622_; uint8_t v_isShared_3623_; uint8_t v_isSharedCheck_3627_; 
lean_del_object(v___x_3592_);
lean_del_object(v___x_3578_);
lean_dec(v_snd_3576_);
lean_dec(v_mvarId_3564_);
v_a_3620_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3597_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3597_);
v___x_3622_ = lean_box(0);
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
v_resetjp_3621_:
{
lean_object* v___x_3625_; 
if (v_isShared_3623_ == 0)
{
v___x_3625_ = v___x_3622_;
goto v_reusejp_3624_;
}
else
{
lean_object* v_reuseFailAlloc_3626_; 
v_reuseFailAlloc_3626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3626_, 0, v_a_3620_);
v___x_3625_ = v_reuseFailAlloc_3626_;
goto v_reusejp_3624_;
}
v_reusejp_3624_:
{
return v___x_3625_;
}
}
}
}
}
v___jp_3581_:
{
lean_object* v___x_3584_; 
if (v_isShared_3579_ == 0)
{
lean_ctor_set(v___x_3578_, 1, v_a_3582_);
lean_ctor_set(v___x_3578_, 0, v___x_3580_);
v___x_3584_ = v___x_3578_;
goto v_reusejp_3583_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v___x_3580_);
lean_ctor_set(v_reuseFailAlloc_3588_, 1, v_a_3582_);
v___x_3584_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3583_;
}
v_reusejp_3583_:
{
size_t v___x_3585_; size_t v___x_3586_; 
v___x_3585_ = ((size_t)1ULL);
v___x_3586_ = lean_usize_add(v_i_3567_, v___x_3585_);
v_i_3567_ = v___x_3586_;
v_b_3568_ = v___x_3584_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_mvarId_3631_, lean_object* v_as_3632_, lean_object* v_sz_3633_, lean_object* v_i_3634_, lean_object* v_b_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_){
_start:
{
size_t v_sz_boxed_3641_; size_t v_i_boxed_3642_; lean_object* v_res_3643_; 
v_sz_boxed_3641_ = lean_unbox_usize(v_sz_3633_);
lean_dec(v_sz_3633_);
v_i_boxed_3642_ = lean_unbox_usize(v_i_3634_);
lean_dec(v_i_3634_);
v_res_3643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3631_, v_as_3632_, v_sz_boxed_3641_, v_i_boxed_3642_, v_b_3635_, v___y_3636_, v___y_3637_, v___y_3638_, v___y_3639_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec_ref(v_as_3632_);
return v_res_3643_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object* v_mvarId_3644_, lean_object* v_as_3645_, size_t v_sz_3646_, size_t v_i_3647_, lean_object* v_b_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_){
_start:
{
uint8_t v___x_3654_; 
v___x_3654_ = lean_usize_dec_lt(v_i_3647_, v_sz_3646_);
if (v___x_3654_ == 0)
{
lean_object* v___x_3655_; 
lean_dec(v_mvarId_3644_);
v___x_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3655_, 0, v_b_3648_);
return v___x_3655_;
}
else
{
lean_object* v_snd_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3709_; 
v_snd_3656_ = lean_ctor_get(v_b_3648_, 1);
v_isSharedCheck_3709_ = !lean_is_exclusive(v_b_3648_);
if (v_isSharedCheck_3709_ == 0)
{
lean_object* v_unused_3710_; 
v_unused_3710_ = lean_ctor_get(v_b_3648_, 0);
lean_dec(v_unused_3710_);
v___x_3658_ = v_b_3648_;
v_isShared_3659_ = v_isSharedCheck_3709_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_snd_3656_);
lean_dec(v_b_3648_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3709_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; lean_object* v_a_3662_; lean_object* v_a_3669_; 
v___x_3660_ = lean_box(0);
v_a_3669_ = lean_array_uget(v_as_3645_, v_i_3647_);
if (lean_obj_tag(v_a_3669_) == 0)
{
v_a_3662_ = v_snd_3656_;
goto v___jp_3661_;
}
else
{
lean_object* v_val_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3708_; 
v_val_3670_ = lean_ctor_get(v_a_3669_, 0);
v_isSharedCheck_3708_ = !lean_is_exclusive(v_a_3669_);
if (v_isSharedCheck_3708_ == 0)
{
v___x_3672_ = v_a_3669_;
v_isShared_3673_ = v_isSharedCheck_3708_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_val_3670_);
lean_dec(v_a_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3708_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3674_ = lean_box(0);
v___x_3675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3676_ = l_Lean_LocalDecl_fvarId(v_val_3670_);
lean_dec(v_val_3670_);
lean_inc(v_mvarId_3644_);
v___x_3677_ = l_Lean_Meta_subst_x3f(v_mvarId_3644_, v___x_3676_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3699_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3680_ = v___x_3677_;
v_isShared_3681_ = v_isSharedCheck_3699_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3699_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
if (lean_obj_tag(v_a_3678_) == 1)
{
lean_object* v___x_3683_; 
lean_del_object(v___x_3658_);
lean_dec(v_mvarId_3644_);
lean_inc_ref(v_a_3678_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v_a_3678_);
v___x_3683_ = v___x_3672_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3696_; 
v_isSharedCheck_3696_ = !lean_is_exclusive(v_a_3678_);
if (v_isSharedCheck_3696_ == 0)
{
lean_object* v_unused_3697_; 
v_unused_3697_ = lean_ctor_get(v_a_3678_, 0);
lean_dec(v_unused_3697_);
v___x_3685_ = v_a_3678_;
v_isShared_3686_ = v_isSharedCheck_3696_;
goto v_resetjp_3684_;
}
else
{
lean_dec(v_a_3678_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3696_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3687_; lean_object* v___x_3689_; 
v___x_3687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3683_);
lean_ctor_set(v___x_3687_, 1, v___x_3674_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set_tag(v___x_3685_, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3687_);
v___x_3689_ = v___x_3685_;
goto v_reusejp_3688_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v___x_3687_);
v___x_3689_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3688_;
}
v_reusejp_3688_:
{
lean_object* v___x_3690_; lean_object* v___x_3691_; lean_object* v___x_3693_; 
v___x_3690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
v___x_3691_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
lean_ctor_set(v___x_3691_, 1, v_snd_3656_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3691_);
v___x_3693_ = v___x_3680_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3691_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
}
else
{
lean_del_object(v___x_3680_);
lean_dec(v_a_3678_);
lean_del_object(v___x_3672_);
lean_dec(v_snd_3656_);
v_a_3662_ = v___x_3675_;
goto v___jp_3661_;
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
lean_del_object(v___x_3672_);
lean_del_object(v___x_3658_);
lean_dec(v_snd_3656_);
lean_dec(v_mvarId_3644_);
v_a_3700_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3677_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3677_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
}
v___jp_3661_:
{
lean_object* v___x_3664_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 1, v_a_3662_);
lean_ctor_set(v___x_3658_, 0, v___x_3660_);
v___x_3664_ = v___x_3658_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v___x_3660_);
lean_ctor_set(v_reuseFailAlloc_3668_, 1, v_a_3662_);
v___x_3664_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
size_t v___x_3665_; size_t v___x_3666_; lean_object* v___x_3667_; 
v___x_3665_ = ((size_t)1ULL);
v___x_3666_ = lean_usize_add(v_i_3647_, v___x_3665_);
v___x_3667_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3644_, v_as_3645_, v_sz_3646_, v___x_3666_, v___x_3664_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
return v___x_3667_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_3711_, lean_object* v_as_3712_, lean_object* v_sz_3713_, lean_object* v_i_3714_, lean_object* v_b_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_){
_start:
{
size_t v_sz_boxed_3721_; size_t v_i_boxed_3722_; lean_object* v_res_3723_; 
v_sz_boxed_3721_ = lean_unbox_usize(v_sz_3713_);
lean_dec(v_sz_3713_);
v_i_boxed_3722_ = lean_unbox_usize(v_i_3714_);
lean_dec(v_i_3714_);
v_res_3723_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3711_, v_as_3712_, v_sz_boxed_3721_, v_i_boxed_3722_, v_b_3715_, v___y_3716_, v___y_3717_, v___y_3718_, v___y_3719_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec_ref(v_as_3712_);
return v_res_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* v_init_3724_, lean_object* v_mvarId_3725_, lean_object* v_n_3726_, lean_object* v_b_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_){
_start:
{
if (lean_obj_tag(v_n_3726_) == 0)
{
lean_object* v_cs_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; size_t v_sz_3736_; size_t v___x_3737_; lean_object* v___x_3738_; 
v_cs_3733_ = lean_ctor_get(v_n_3726_, 0);
v___x_3734_ = lean_box(0);
v___x_3735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3735_, 0, v___x_3734_);
lean_ctor_set(v___x_3735_, 1, v_b_3727_);
v_sz_3736_ = lean_array_size(v_cs_3733_);
v___x_3737_ = ((size_t)0ULL);
v___x_3738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3724_, v_mvarId_3725_, v_cs_3733_, v_sz_3736_, v___x_3737_, v___x_3735_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3753_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3753_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3753_ == 0)
{
v___x_3741_ = v___x_3738_;
v_isShared_3742_ = v_isSharedCheck_3753_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_a_3739_);
lean_dec(v___x_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3753_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v_fst_3743_; 
v_fst_3743_ = lean_ctor_get(v_a_3739_, 0);
if (lean_obj_tag(v_fst_3743_) == 0)
{
lean_object* v_snd_3744_; lean_object* v___x_3745_; lean_object* v___x_3747_; 
v_snd_3744_ = lean_ctor_get(v_a_3739_, 1);
lean_inc(v_snd_3744_);
lean_dec(v_a_3739_);
v___x_3745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3745_, 0, v_snd_3744_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v___x_3745_);
v___x_3747_ = v___x_3741_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v___x_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
else
{
lean_object* v_val_3749_; lean_object* v___x_3751_; 
lean_inc_ref(v_fst_3743_);
lean_dec(v_a_3739_);
v_val_3749_ = lean_ctor_get(v_fst_3743_, 0);
lean_inc(v_val_3749_);
lean_dec_ref_known(v_fst_3743_, 1);
if (v_isShared_3742_ == 0)
{
lean_ctor_set(v___x_3741_, 0, v_val_3749_);
v___x_3751_ = v___x_3741_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v_val_3749_);
v___x_3751_ = v_reuseFailAlloc_3752_;
goto v_reusejp_3750_;
}
v_reusejp_3750_:
{
return v___x_3751_;
}
}
}
}
else
{
lean_object* v_a_3754_; lean_object* v___x_3756_; uint8_t v_isShared_3757_; uint8_t v_isSharedCheck_3761_; 
v_a_3754_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3761_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3761_ == 0)
{
v___x_3756_ = v___x_3738_;
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
else
{
lean_inc(v_a_3754_);
lean_dec(v___x_3738_);
v___x_3756_ = lean_box(0);
v_isShared_3757_ = v_isSharedCheck_3761_;
goto v_resetjp_3755_;
}
v_resetjp_3755_:
{
lean_object* v___x_3759_; 
if (v_isShared_3757_ == 0)
{
v___x_3759_ = v___x_3756_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v_a_3754_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
}
}
else
{
lean_object* v_vs_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; size_t v_sz_3765_; size_t v___x_3766_; lean_object* v___x_3767_; 
v_vs_3762_ = lean_ctor_get(v_n_3726_, 0);
v___x_3763_ = lean_box(0);
v___x_3764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3764_, 0, v___x_3763_);
lean_ctor_set(v___x_3764_, 1, v_b_3727_);
v_sz_3765_ = lean_array_size(v_vs_3762_);
v___x_3766_ = ((size_t)0ULL);
v___x_3767_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3725_, v_vs_3762_, v_sz_3765_, v___x_3766_, v___x_3764_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
if (lean_obj_tag(v___x_3767_) == 0)
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3782_; 
v_a_3768_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3770_ = v___x_3767_;
v_isShared_3771_ = v_isSharedCheck_3782_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3767_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3782_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v_fst_3772_; 
v_fst_3772_ = lean_ctor_get(v_a_3768_, 0);
if (lean_obj_tag(v_fst_3772_) == 0)
{
lean_object* v_snd_3773_; lean_object* v___x_3774_; lean_object* v___x_3776_; 
v_snd_3773_ = lean_ctor_get(v_a_3768_, 1);
lean_inc(v_snd_3773_);
lean_dec(v_a_3768_);
v___x_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3774_, 0, v_snd_3773_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 0, v___x_3774_);
v___x_3776_ = v___x_3770_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v___x_3774_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
else
{
lean_object* v_val_3778_; lean_object* v___x_3780_; 
lean_inc_ref(v_fst_3772_);
lean_dec(v_a_3768_);
v_val_3778_ = lean_ctor_get(v_fst_3772_, 0);
lean_inc(v_val_3778_);
lean_dec_ref_known(v_fst_3772_, 1);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 0, v_val_3778_);
v___x_3780_ = v___x_3770_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_val_3778_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
v_a_3783_ = lean_ctor_get(v___x_3767_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3767_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3767_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3767_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_init_3791_, lean_object* v_mvarId_3792_, lean_object* v_as_3793_, size_t v_sz_3794_, size_t v_i_3795_, lean_object* v_b_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
uint8_t v___x_3802_; 
v___x_3802_ = lean_usize_dec_lt(v_i_3795_, v_sz_3794_);
if (v___x_3802_ == 0)
{
lean_object* v___x_3803_; 
lean_dec(v_mvarId_3792_);
v___x_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3803_, 0, v_b_3796_);
return v___x_3803_;
}
else
{
lean_object* v_snd_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3838_; 
v_snd_3804_ = lean_ctor_get(v_b_3796_, 1);
v_isSharedCheck_3838_ = !lean_is_exclusive(v_b_3796_);
if (v_isSharedCheck_3838_ == 0)
{
lean_object* v_unused_3839_; 
v_unused_3839_ = lean_ctor_get(v_b_3796_, 0);
lean_dec(v_unused_3839_);
v___x_3806_ = v_b_3796_;
v_isShared_3807_ = v_isSharedCheck_3838_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_snd_3804_);
lean_dec(v_b_3796_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3838_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v_a_3809_; lean_object* v___x_3810_; 
v___x_3808_ = lean_box(0);
v_a_3809_ = lean_array_uget_borrowed(v_as_3793_, v_i_3795_);
lean_inc(v_snd_3804_);
lean_inc(v_mvarId_3792_);
v___x_3810_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3791_, v_mvarId_3792_, v_a_3809_, v_snd_3804_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
if (lean_obj_tag(v___x_3810_) == 0)
{
lean_object* v_a_3811_; lean_object* v___x_3813_; uint8_t v_isShared_3814_; uint8_t v_isSharedCheck_3829_; 
v_a_3811_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3813_ = v___x_3810_;
v_isShared_3814_ = v_isSharedCheck_3829_;
goto v_resetjp_3812_;
}
else
{
lean_inc(v_a_3811_);
lean_dec(v___x_3810_);
v___x_3813_ = lean_box(0);
v_isShared_3814_ = v_isSharedCheck_3829_;
goto v_resetjp_3812_;
}
v_resetjp_3812_:
{
if (lean_obj_tag(v_a_3811_) == 0)
{
lean_object* v___x_3815_; lean_object* v___x_3817_; 
lean_dec(v_mvarId_3792_);
v___x_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3815_, 0, v_a_3811_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v___x_3815_);
v___x_3817_ = v___x_3806_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3815_);
lean_ctor_set(v_reuseFailAlloc_3821_, 1, v_snd_3804_);
v___x_3817_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3816_;
}
v_reusejp_3816_:
{
lean_object* v___x_3819_; 
if (v_isShared_3814_ == 0)
{
lean_ctor_set(v___x_3813_, 0, v___x_3817_);
v___x_3819_ = v___x_3813_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3817_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; 
lean_del_object(v___x_3813_);
lean_dec(v_snd_3804_);
v_a_3822_ = lean_ctor_get(v_a_3811_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v_a_3811_, 1);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 1, v_a_3822_);
lean_ctor_set(v___x_3806_, 0, v___x_3808_);
v___x_3824_ = v___x_3806_;
goto v_reusejp_3823_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3828_, 1, v_a_3822_);
v___x_3824_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3823_;
}
v_reusejp_3823_:
{
size_t v___x_3825_; size_t v___x_3826_; 
v___x_3825_ = ((size_t)1ULL);
v___x_3826_ = lean_usize_add(v_i_3795_, v___x_3825_);
v_i_3795_ = v___x_3826_;
v_b_3796_ = v___x_3824_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3830_; lean_object* v___x_3832_; uint8_t v_isShared_3833_; uint8_t v_isSharedCheck_3837_; 
lean_del_object(v___x_3806_);
lean_dec(v_snd_3804_);
lean_dec(v_mvarId_3792_);
v_a_3830_ = lean_ctor_get(v___x_3810_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v___x_3810_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3832_ = v___x_3810_;
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
else
{
lean_inc(v_a_3830_);
lean_dec(v___x_3810_);
v___x_3832_ = lean_box(0);
v_isShared_3833_ = v_isSharedCheck_3837_;
goto v_resetjp_3831_;
}
v_resetjp_3831_:
{
lean_object* v___x_3835_; 
if (v_isShared_3833_ == 0)
{
v___x_3835_ = v___x_3832_;
goto v_reusejp_3834_;
}
else
{
lean_object* v_reuseFailAlloc_3836_; 
v_reuseFailAlloc_3836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3836_, 0, v_a_3830_);
v___x_3835_ = v_reuseFailAlloc_3836_;
goto v_reusejp_3834_;
}
v_reusejp_3834_:
{
return v___x_3835_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3840_, lean_object* v_mvarId_3841_, lean_object* v_as_3842_, lean_object* v_sz_3843_, lean_object* v_i_3844_, lean_object* v_b_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_){
_start:
{
size_t v_sz_boxed_3851_; size_t v_i_boxed_3852_; lean_object* v_res_3853_; 
v_sz_boxed_3851_ = lean_unbox_usize(v_sz_3843_);
lean_dec(v_sz_3843_);
v_i_boxed_3852_ = lean_unbox_usize(v_i_3844_);
lean_dec(v_i_3844_);
v_res_3853_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3840_, v_mvarId_3841_, v_as_3842_, v_sz_boxed_3851_, v_i_boxed_3852_, v_b_3845_, v___y_3846_, v___y_3847_, v___y_3848_, v___y_3849_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec_ref(v_as_3842_);
lean_dec_ref(v_init_3840_);
return v_res_3853_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_init_3854_, lean_object* v_mvarId_3855_, lean_object* v_n_3856_, lean_object* v_b_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3854_, v_mvarId_3855_, v_n_3856_, v_b_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec_ref(v_n_3856_);
lean_dec_ref(v_init_3854_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3867_, lean_object* v_as_3868_, size_t v_sz_3869_, size_t v_i_3870_, lean_object* v_b_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_){
_start:
{
uint8_t v___x_3877_; 
v___x_3877_ = lean_usize_dec_lt(v_i_3870_, v_sz_3869_);
if (v___x_3877_ == 0)
{
lean_object* v___x_3878_; 
lean_dec(v_mvarId_3867_);
v___x_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3878_, 0, v_b_3871_);
return v___x_3878_;
}
else
{
lean_object* v_snd_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3931_; 
v_snd_3879_ = lean_ctor_get(v_b_3871_, 1);
v_isSharedCheck_3931_ = !lean_is_exclusive(v_b_3871_);
if (v_isSharedCheck_3931_ == 0)
{
lean_object* v_unused_3932_; 
v_unused_3932_ = lean_ctor_get(v_b_3871_, 0);
lean_dec(v_unused_3932_);
v___x_3881_ = v_b_3871_;
v_isShared_3882_ = v_isSharedCheck_3931_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_snd_3879_);
lean_dec(v_b_3871_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3931_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3883_; lean_object* v_a_3885_; lean_object* v_a_3892_; 
v___x_3883_ = lean_box(0);
v_a_3892_ = lean_array_uget(v_as_3868_, v_i_3870_);
if (lean_obj_tag(v_a_3892_) == 0)
{
v_a_3885_ = v_snd_3879_;
goto v___jp_3884_;
}
else
{
lean_object* v_val_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3930_; 
v_val_3893_ = lean_ctor_get(v_a_3892_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v_a_3892_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3895_ = v_a_3892_;
v_isShared_3896_ = v_isSharedCheck_3930_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_val_3893_);
lean_dec(v_a_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3930_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3897_; lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3897_ = lean_box(0);
v___x_3898_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v___x_3899_ = l_Lean_LocalDecl_fvarId(v_val_3893_);
lean_dec(v_val_3893_);
lean_inc(v_mvarId_3867_);
v___x_3900_ = l_Lean_Meta_subst_x3f(v_mvarId_3867_, v___x_3899_, v___y_3872_, v___y_3873_, v___y_3874_, v___y_3875_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3921_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3921_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3921_ == 0)
{
v___x_3903_ = v___x_3900_;
v_isShared_3904_ = v_isSharedCheck_3921_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3900_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3921_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
if (lean_obj_tag(v_a_3901_) == 1)
{
lean_object* v___x_3906_; 
lean_del_object(v___x_3881_);
lean_dec(v_mvarId_3867_);
lean_inc_ref(v_a_3901_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v_a_3901_);
v___x_3906_ = v___x_3895_;
goto v_reusejp_3905_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v_a_3901_);
v___x_3906_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3905_;
}
v_reusejp_3905_:
{
lean_object* v___x_3908_; uint8_t v_isShared_3909_; uint8_t v_isSharedCheck_3918_; 
v_isSharedCheck_3918_ = !lean_is_exclusive(v_a_3901_);
if (v_isSharedCheck_3918_ == 0)
{
lean_object* v_unused_3919_; 
v_unused_3919_ = lean_ctor_get(v_a_3901_, 0);
lean_dec(v_unused_3919_);
v___x_3908_ = v_a_3901_;
v_isShared_3909_ = v_isSharedCheck_3918_;
goto v_resetjp_3907_;
}
else
{
lean_dec(v_a_3901_);
v___x_3908_ = lean_box(0);
v_isShared_3909_ = v_isSharedCheck_3918_;
goto v_resetjp_3907_;
}
v_resetjp_3907_:
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3906_);
lean_ctor_set(v___x_3910_, 1, v___x_3897_);
if (v_isShared_3909_ == 0)
{
lean_ctor_set(v___x_3908_, 0, v___x_3910_);
v___x_3912_ = v___x_3908_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
v___x_3913_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3913_, 0, v___x_3912_);
lean_ctor_set(v___x_3913_, 1, v_snd_3879_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 0, v___x_3913_);
v___x_3915_ = v___x_3903_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3916_; 
v_reuseFailAlloc_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3916_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3916_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
return v___x_3915_;
}
}
}
}
}
else
{
lean_del_object(v___x_3903_);
lean_dec(v_a_3901_);
lean_del_object(v___x_3895_);
lean_dec(v_snd_3879_);
v_a_3885_ = v___x_3898_;
goto v___jp_3884_;
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_del_object(v___x_3895_);
lean_del_object(v___x_3881_);
lean_dec(v_snd_3879_);
lean_dec(v_mvarId_3867_);
v_a_3922_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3900_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3900_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3927_; 
if (v_isShared_3925_ == 0)
{
v___x_3927_ = v___x_3924_;
goto v_reusejp_3926_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v_a_3922_);
v___x_3927_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3926_;
}
v_reusejp_3926_:
{
return v___x_3927_;
}
}
}
}
}
v___jp_3884_:
{
lean_object* v___x_3887_; 
if (v_isShared_3882_ == 0)
{
lean_ctor_set(v___x_3881_, 1, v_a_3885_);
lean_ctor_set(v___x_3881_, 0, v___x_3883_);
v___x_3887_ = v___x_3881_;
goto v_reusejp_3886_;
}
else
{
lean_object* v_reuseFailAlloc_3891_; 
v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3891_, 0, v___x_3883_);
lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_a_3885_);
v___x_3887_ = v_reuseFailAlloc_3891_;
goto v_reusejp_3886_;
}
v_reusejp_3886_:
{
size_t v___x_3888_; size_t v___x_3889_; 
v___x_3888_ = ((size_t)1ULL);
v___x_3889_ = lean_usize_add(v_i_3870_, v___x_3888_);
v_i_3870_ = v___x_3889_;
v_b_3871_ = v___x_3887_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3933_, lean_object* v_as_3934_, lean_object* v_sz_3935_, lean_object* v_i_3936_, lean_object* v_b_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
size_t v_sz_boxed_3943_; size_t v_i_boxed_3944_; lean_object* v_res_3945_; 
v_sz_boxed_3943_ = lean_unbox_usize(v_sz_3935_);
lean_dec(v_sz_3935_);
v_i_boxed_3944_ = lean_unbox_usize(v_i_3936_);
lean_dec(v_i_3936_);
v_res_3945_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3933_, v_as_3934_, v_sz_boxed_3943_, v_i_boxed_3944_, v_b_3937_, v___y_3938_, v___y_3939_, v___y_3940_, v___y_3941_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec_ref(v_as_3934_);
return v_res_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_3946_, lean_object* v_as_3947_, size_t v_sz_3948_, size_t v_i_3949_, lean_object* v_b_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
uint8_t v___x_3956_; 
v___x_3956_ = lean_usize_dec_lt(v_i_3949_, v_sz_3948_);
if (v___x_3956_ == 0)
{
lean_object* v___x_3957_; 
lean_dec(v_mvarId_3946_);
v___x_3957_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3957_, 0, v_b_3950_);
return v___x_3957_;
}
else
{
lean_object* v_snd_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_4010_; 
v_snd_3958_ = lean_ctor_get(v_b_3950_, 1);
v_isSharedCheck_4010_ = !lean_is_exclusive(v_b_3950_);
if (v_isSharedCheck_4010_ == 0)
{
lean_object* v_unused_4011_; 
v_unused_4011_ = lean_ctor_get(v_b_3950_, 0);
lean_dec(v_unused_4011_);
v___x_3960_ = v_b_3950_;
v_isShared_3961_ = v_isSharedCheck_4010_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_snd_3958_);
lean_dec(v_b_3950_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_4010_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3962_; lean_object* v_a_3964_; lean_object* v_a_3971_; 
v___x_3962_ = lean_box(0);
v_a_3971_ = lean_array_uget(v_as_3947_, v_i_3949_);
if (lean_obj_tag(v_a_3971_) == 0)
{
v_a_3964_ = v_snd_3958_;
goto v___jp_3963_;
}
else
{
lean_object* v_val_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_4009_; 
v_val_3972_ = lean_ctor_get(v_a_3971_, 0);
v_isSharedCheck_4009_ = !lean_is_exclusive(v_a_3971_);
if (v_isSharedCheck_4009_ == 0)
{
v___x_3974_ = v_a_3971_;
v_isShared_3975_ = v_isSharedCheck_4009_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_val_3972_);
lean_dec(v_a_3971_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_4009_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3976_ = lean_box(0);
v___x_3977_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v___x_3978_ = l_Lean_LocalDecl_fvarId(v_val_3972_);
lean_dec(v_val_3972_);
lean_inc(v_mvarId_3946_);
v___x_3979_ = l_Lean_Meta_subst_x3f(v_mvarId_3946_, v___x_3978_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4000_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4000_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4000_ == 0)
{
v___x_3982_ = v___x_3979_;
v_isShared_3983_ = v_isSharedCheck_4000_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3979_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4000_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
if (lean_obj_tag(v_a_3980_) == 1)
{
lean_object* v___x_3985_; 
lean_del_object(v___x_3960_);
lean_dec(v_mvarId_3946_);
lean_inc_ref(v_a_3980_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v_a_3980_);
v___x_3985_ = v___x_3974_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3999_; 
v_reuseFailAlloc_3999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3999_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3999_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
lean_object* v___x_3987_; uint8_t v_isShared_3988_; uint8_t v_isSharedCheck_3997_; 
v_isSharedCheck_3997_ = !lean_is_exclusive(v_a_3980_);
if (v_isSharedCheck_3997_ == 0)
{
lean_object* v_unused_3998_; 
v_unused_3998_ = lean_ctor_get(v_a_3980_, 0);
lean_dec(v_unused_3998_);
v___x_3987_ = v_a_3980_;
v_isShared_3988_ = v_isSharedCheck_3997_;
goto v_resetjp_3986_;
}
else
{
lean_dec(v_a_3980_);
v___x_3987_ = lean_box(0);
v_isShared_3988_ = v_isSharedCheck_3997_;
goto v_resetjp_3986_;
}
v_resetjp_3986_:
{
lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3985_);
lean_ctor_set(v___x_3989_, 1, v___x_3976_);
if (v_isShared_3988_ == 0)
{
lean_ctor_set(v___x_3987_, 0, v___x_3989_);
v___x_3991_ = v___x_3987_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
lean_ctor_set(v___x_3992_, 1, v_snd_3958_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_3992_);
v___x_3994_ = v___x_3982_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3995_; 
v_reuseFailAlloc_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3995_, 0, v___x_3992_);
v___x_3994_ = v_reuseFailAlloc_3995_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
return v___x_3994_;
}
}
}
}
}
else
{
lean_del_object(v___x_3982_);
lean_dec(v_a_3980_);
lean_del_object(v___x_3974_);
lean_dec(v_snd_3958_);
v_a_3964_ = v___x_3977_;
goto v___jp_3963_;
}
}
}
else
{
lean_object* v_a_4001_; lean_object* v___x_4003_; uint8_t v_isShared_4004_; uint8_t v_isSharedCheck_4008_; 
lean_del_object(v___x_3974_);
lean_del_object(v___x_3960_);
lean_dec(v_snd_3958_);
lean_dec(v_mvarId_3946_);
v_a_4001_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4008_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4008_ == 0)
{
v___x_4003_ = v___x_3979_;
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
else
{
lean_inc(v_a_4001_);
lean_dec(v___x_3979_);
v___x_4003_ = lean_box(0);
v_isShared_4004_ = v_isSharedCheck_4008_;
goto v_resetjp_4002_;
}
v_resetjp_4002_:
{
lean_object* v___x_4006_; 
if (v_isShared_4004_ == 0)
{
v___x_4006_ = v___x_4003_;
goto v_reusejp_4005_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v_a_4001_);
v___x_4006_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4005_;
}
v_reusejp_4005_:
{
return v___x_4006_;
}
}
}
}
}
v___jp_3963_:
{
lean_object* v___x_3966_; 
if (v_isShared_3961_ == 0)
{
lean_ctor_set(v___x_3960_, 1, v_a_3964_);
lean_ctor_set(v___x_3960_, 0, v___x_3962_);
v___x_3966_ = v___x_3960_;
goto v_reusejp_3965_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v___x_3962_);
lean_ctor_set(v_reuseFailAlloc_3970_, 1, v_a_3964_);
v___x_3966_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3965_;
}
v_reusejp_3965_:
{
size_t v___x_3967_; size_t v___x_3968_; lean_object* v___x_3969_; 
v___x_3967_ = ((size_t)1ULL);
v___x_3968_ = lean_usize_add(v_i_3949_, v___x_3967_);
v___x_3969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3946_, v_as_3947_, v_sz_3948_, v___x_3968_, v___x_3966_, v___y_3951_, v___y_3952_, v___y_3953_, v___y_3954_);
return v___x_3969_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_4012_, lean_object* v_as_4013_, lean_object* v_sz_4014_, lean_object* v_i_4015_, lean_object* v_b_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
size_t v_sz_boxed_4022_; size_t v_i_boxed_4023_; lean_object* v_res_4024_; 
v_sz_boxed_4022_ = lean_unbox_usize(v_sz_4014_);
lean_dec(v_sz_4014_);
v_i_boxed_4023_ = lean_unbox_usize(v_i_4015_);
lean_dec(v_i_4015_);
v_res_4024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4012_, v_as_4013_, v_sz_boxed_4022_, v_i_boxed_4023_, v_b_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec_ref(v_as_4013_);
return v_res_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4025_, lean_object* v_t_4026_, lean_object* v_init_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v_root_4033_; lean_object* v_tail_4034_; lean_object* v___x_4035_; 
v_root_4033_ = lean_ctor_get(v_t_4026_, 0);
v_tail_4034_ = lean_ctor_get(v_t_4026_, 1);
lean_inc(v_mvarId_4025_);
lean_inc_ref(v_init_4027_);
v___x_4035_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_4027_, v_mvarId_4025_, v_root_4033_, v_init_4027_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
lean_dec_ref(v_init_4027_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4072_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4072_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4072_ == 0)
{
v___x_4038_ = v___x_4035_;
v_isShared_4039_ = v_isSharedCheck_4072_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4035_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4072_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
if (lean_obj_tag(v_a_4036_) == 0)
{
lean_object* v_a_4040_; lean_object* v___x_4042_; 
lean_dec(v_mvarId_4025_);
v_a_4040_ = lean_ctor_get(v_a_4036_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v_a_4036_, 1);
if (v_isShared_4039_ == 0)
{
lean_ctor_set(v___x_4038_, 0, v_a_4040_);
v___x_4042_ = v___x_4038_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4040_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; size_t v_sz_4047_; size_t v___x_4048_; lean_object* v___x_4049_; 
lean_del_object(v___x_4038_);
v_a_4044_ = lean_ctor_get(v_a_4036_, 0);
lean_inc(v_a_4044_);
lean_dec_ref_known(v_a_4036_, 1);
v___x_4045_ = lean_box(0);
v___x_4046_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4046_, 0, v___x_4045_);
lean_ctor_set(v___x_4046_, 1, v_a_4044_);
v_sz_4047_ = lean_array_size(v_tail_4034_);
v___x_4048_ = ((size_t)0ULL);
v___x_4049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4025_, v_tail_4034_, v_sz_4047_, v___x_4048_, v___x_4046_, v___y_4028_, v___y_4029_, v___y_4030_, v___y_4031_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4063_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4063_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4063_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v_fst_4054_; 
v_fst_4054_ = lean_ctor_get(v_a_4050_, 0);
if (lean_obj_tag(v_fst_4054_) == 0)
{
lean_object* v_snd_4055_; lean_object* v___x_4057_; 
v_snd_4055_ = lean_ctor_get(v_a_4050_, 1);
lean_inc(v_snd_4055_);
lean_dec(v_a_4050_);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v_snd_4055_);
v___x_4057_ = v___x_4052_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_snd_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
else
{
lean_object* v_val_4059_; lean_object* v___x_4061_; 
lean_inc_ref(v_fst_4054_);
lean_dec(v_a_4050_);
v_val_4059_ = lean_ctor_get(v_fst_4054_, 0);
lean_inc(v_val_4059_);
lean_dec_ref_known(v_fst_4054_, 1);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v_val_4059_);
v___x_4061_ = v___x_4052_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v_val_4059_);
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
else
{
lean_object* v_a_4064_; lean_object* v___x_4066_; uint8_t v_isShared_4067_; uint8_t v_isSharedCheck_4071_; 
v_a_4064_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4071_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4071_ == 0)
{
v___x_4066_ = v___x_4049_;
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
else
{
lean_inc(v_a_4064_);
lean_dec(v___x_4049_);
v___x_4066_ = lean_box(0);
v_isShared_4067_ = v_isSharedCheck_4071_;
goto v_resetjp_4065_;
}
v_resetjp_4065_:
{
lean_object* v___x_4069_; 
if (v_isShared_4067_ == 0)
{
v___x_4069_ = v___x_4066_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_a_4064_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
}
}
}
}
else
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4080_; 
lean_dec(v_mvarId_4025_);
v_a_4073_ = lean_ctor_get(v___x_4035_, 0);
v_isSharedCheck_4080_ = !lean_is_exclusive(v___x_4035_);
if (v_isSharedCheck_4080_ == 0)
{
v___x_4075_ = v___x_4035_;
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4035_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4080_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4078_; 
if (v_isShared_4076_ == 0)
{
v___x_4078_ = v___x_4075_;
goto v_reusejp_4077_;
}
else
{
lean_object* v_reuseFailAlloc_4079_; 
v_reuseFailAlloc_4079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4079_, 0, v_a_4073_);
v___x_4078_ = v_reuseFailAlloc_4079_;
goto v_reusejp_4077_;
}
v_reusejp_4077_:
{
return v___x_4078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4081_, lean_object* v_t_4082_, lean_object* v_init_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v_res_4089_; 
v_res_4089_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4081_, v_t_4082_, v_init_4083_, v___y_4084_, v___y_4085_, v___y_4086_, v___y_4087_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec_ref(v_t_4082_);
return v_res_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_){
_start:
{
lean_object* v_lctx_4099_; lean_object* v_decls_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v_lctx_4099_ = lean_ctor_get(v___y_4094_, 2);
v_decls_4100_ = lean_ctor_get(v_lctx_4099_, 1);
v___x_4101_ = lean_box(0);
v___x_4102_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4103_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4093_, v_decls_4100_, v___x_4102_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4116_; 
v_a_4104_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4106_ = v___x_4103_;
v_isShared_4107_ = v_isSharedCheck_4116_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4103_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4116_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v_fst_4108_; 
v_fst_4108_ = lean_ctor_get(v_a_4104_, 0);
lean_inc(v_fst_4108_);
lean_dec(v_a_4104_);
if (lean_obj_tag(v_fst_4108_) == 0)
{
lean_object* v___x_4110_; 
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v___x_4101_);
v___x_4110_ = v___x_4106_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v___x_4101_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
else
{
lean_object* v_val_4112_; lean_object* v___x_4114_; 
v_val_4112_ = lean_ctor_get(v_fst_4108_, 0);
lean_inc(v_val_4112_);
lean_dec_ref_known(v_fst_4108_, 1);
if (v_isShared_4107_ == 0)
{
lean_ctor_set(v___x_4106_, 0, v_val_4112_);
v___x_4114_ = v___x_4106_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v_val_4112_);
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
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
v_a_4117_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4103_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4103_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_){
_start:
{
lean_object* v_res_4131_; 
v_res_4131_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4125_, v___y_4126_, v___y_4127_, v___y_4128_, v___y_4129_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
return v_res_4131_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_){
_start:
{
lean_object* v___f_4138_; lean_object* v___x_4139_; 
lean_inc(v_mvarId_4132_);
v___f_4138_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4138_, 0, v_mvarId_4132_);
v___x_4139_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_4132_, v___f_4138_, v_a_4133_, v_a_4134_, v_a_4135_, v_a_4136_);
return v___x_4139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v_res_4146_; 
v_res_4146_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4140_, v_a_4141_, v_a_4142_, v_a_4143_, v_a_4144_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
return v_res_4146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_){
_start:
{
lean_object* v___x_4153_; 
lean_inc(v_mvarId_4147_);
v___x_4153_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4147_, v_a_4148_, v_a_4149_, v_a_4150_, v_a_4151_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4163_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4163_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4163_ == 0)
{
v___x_4156_ = v___x_4153_;
v_isShared_4157_ = v_isSharedCheck_4163_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4153_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4163_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
if (lean_obj_tag(v_a_4154_) == 1)
{
lean_object* v_val_4158_; 
lean_del_object(v___x_4156_);
lean_dec(v_mvarId_4147_);
v_val_4158_ = lean_ctor_get(v_a_4154_, 0);
lean_inc(v_val_4158_);
lean_dec_ref_known(v_a_4154_, 1);
v_mvarId_4147_ = v_val_4158_;
goto _start;
}
else
{
lean_object* v___x_4161_; 
lean_dec(v_a_4154_);
if (v_isShared_4157_ == 0)
{
lean_ctor_set(v___x_4156_, 0, v_mvarId_4147_);
v___x_4161_ = v___x_4156_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4162_; 
v_reuseFailAlloc_4162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4162_, 0, v_mvarId_4147_);
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
else
{
lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4171_; 
lean_dec(v_mvarId_4147_);
v_a_4164_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4166_ = v___x_4153_;
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4153_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4171_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4169_; 
if (v_isShared_4167_ == 0)
{
v___x_4169_ = v___x_4166_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v_a_4164_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_Meta_substVars(v_mvarId_4172_, v_a_4173_, v_a_4174_, v_a_4175_, v_a_4176_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4241_; uint8_t v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4241_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_4242_ = 0;
v___x_4243_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4244_ = l_Lean_registerTraceClass(v___x_4241_, v___x_4242_, v___x_4243_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4245_){
_start:
{
lean_object* v_res_4246_; 
v_res_4246_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4246_;
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
