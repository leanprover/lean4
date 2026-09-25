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
uint8_t v___x_27145__boxed_222_; uint8_t v___x_27146__boxed_223_; lean_object* v_res_224_; 
v___x_27145__boxed_222_ = lean_unbox(v___x_214_);
v___x_27146__boxed_223_ = lean_unbox(v___x_215_);
v_res_224_ = l_Lean_Meta_substCore___lam__0(v_type_210_, v___x_211_, v___x_212_, v___x_213_, v___x_27145__boxed_222_, v___x_27146__boxed_223_, v_hAux_216_, v___y_217_, v___y_218_, v___y_219_, v___y_220_);
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
size_t v_x_27266__boxed_364_; size_t v_x_27267__boxed_365_; lean_object* v_res_366_; 
v_x_27266__boxed_364_ = lean_unbox_usize(v_x_360_);
lean_dec(v_x_360_);
v_x_27267__boxed_365_ = lean_unbox_usize(v_x_361_);
lean_dec(v_x_361_);
v_res_366_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_359_, v_x_27266__boxed_364_, v_x_27267__boxed_365_, v_x_362_, v_x_363_);
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
lean_object* v_depth_387_; lean_object* v_levelAssignDepth_388_; lean_object* v_lmvarCounter_389_; lean_object* v_mvarCounter_390_; lean_object* v_lDecls_391_; lean_object* v_decls_392_; lean_object* v_userNames_393_; lean_object* v_lAssignment_394_; lean_object* v_eAssignment_395_; lean_object* v_dAssignment_396_; lean_object* v_instanceTypedMVars_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_411_; 
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
v_isSharedCheck_411_ = !lean_is_exclusive(v_mctx_379_);
if (v_isSharedCheck_411_ == 0)
{
v___x_399_ = v_mctx_379_;
v_isShared_400_ = v_isSharedCheck_411_;
goto v_resetjp_398_;
}
else
{
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
lean_ctor_set(v_reuseFailAlloc_410_, 10, v_instanceTypedMVars_397_);
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
lean_object* v___x_529_; lean_object* v_env_530_; lean_object* v___x_531_; lean_object* v_toCold_532_; lean_object* v_mctx_533_; lean_object* v_lctx_534_; lean_object* v_options_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_529_ = lean_st_ref_get(v___y_527_);
v_env_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc_ref(v_env_530_);
lean_dec(v___x_529_);
v___x_531_ = lean_st_ref_get(v___y_525_);
v_toCold_532_ = lean_ctor_get(v___y_526_, 0);
v_mctx_533_ = lean_ctor_get(v___x_531_, 0);
lean_inc_ref(v_mctx_533_);
lean_dec(v___x_531_);
v_lctx_534_ = lean_ctor_get(v___y_524_, 2);
v_options_535_ = lean_ctor_get(v_toCold_532_, 2);
lean_inc_ref(v_options_535_);
lean_inc_ref(v_lctx_534_);
v___x_536_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_536_, 0, v_env_530_);
lean_ctor_set(v___x_536_, 1, v_mctx_533_);
lean_ctor_set(v___x_536_, 2, v_lctx_534_);
lean_ctor_set(v___x_536_, 3, v_options_535_);
v___x_537_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_537_, 0, v___x_536_);
lean_ctor_set(v___x_537_, 1, v_msgData_523_);
v___x_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_538_, 0, v___x_537_);
return v___x_538_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2___boxed(lean_object* v_msgData_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msgData_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_);
lean_dec(v___y_543_);
lean_dec_ref(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_545_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0(void){
_start:
{
lean_object* v___x_546_; double v___x_547_; 
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_float_of_nat(v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(lean_object* v_cls_551_, lean_object* v_msg_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_ref_558_; lean_object* v___x_559_; lean_object* v_a_560_; lean_object* v___x_562_; uint8_t v_isShared_563_; uint8_t v_isSharedCheck_605_; 
v_ref_558_ = lean_ctor_get(v___y_555_, 2);
v___x_559_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msg_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
v_a_560_ = lean_ctor_get(v___x_559_, 0);
v_isSharedCheck_605_ = !lean_is_exclusive(v___x_559_);
if (v_isSharedCheck_605_ == 0)
{
v___x_562_ = v___x_559_;
v_isShared_563_ = v_isSharedCheck_605_;
goto v_resetjp_561_;
}
else
{
lean_inc(v_a_560_);
lean_dec(v___x_559_);
v___x_562_ = lean_box(0);
v_isShared_563_ = v_isSharedCheck_605_;
goto v_resetjp_561_;
}
v_resetjp_561_:
{
lean_object* v___x_564_; lean_object* v_traceState_565_; lean_object* v_env_566_; lean_object* v_nextMacroScope_567_; lean_object* v_ngen_568_; lean_object* v_auxDeclNGen_569_; lean_object* v_cache_570_; lean_object* v_recordedDeps_571_; lean_object* v_messages_572_; lean_object* v_infoState_573_; lean_object* v_snapshotTasks_574_; lean_object* v___x_576_; uint8_t v_isShared_577_; uint8_t v_isSharedCheck_604_; 
v___x_564_ = lean_st_ref_take(v___y_556_);
v_traceState_565_ = lean_ctor_get(v___x_564_, 4);
v_env_566_ = lean_ctor_get(v___x_564_, 0);
v_nextMacroScope_567_ = lean_ctor_get(v___x_564_, 1);
v_ngen_568_ = lean_ctor_get(v___x_564_, 2);
v_auxDeclNGen_569_ = lean_ctor_get(v___x_564_, 3);
v_cache_570_ = lean_ctor_get(v___x_564_, 5);
v_recordedDeps_571_ = lean_ctor_get(v___x_564_, 6);
v_messages_572_ = lean_ctor_get(v___x_564_, 7);
v_infoState_573_ = lean_ctor_get(v___x_564_, 8);
v_snapshotTasks_574_ = lean_ctor_get(v___x_564_, 9);
v_isSharedCheck_604_ = !lean_is_exclusive(v___x_564_);
if (v_isSharedCheck_604_ == 0)
{
v___x_576_ = v___x_564_;
v_isShared_577_ = v_isSharedCheck_604_;
goto v_resetjp_575_;
}
else
{
lean_inc(v_snapshotTasks_574_);
lean_inc(v_infoState_573_);
lean_inc(v_messages_572_);
lean_inc(v_recordedDeps_571_);
lean_inc(v_cache_570_);
lean_inc(v_traceState_565_);
lean_inc(v_auxDeclNGen_569_);
lean_inc(v_ngen_568_);
lean_inc(v_nextMacroScope_567_);
lean_inc(v_env_566_);
lean_dec(v___x_564_);
v___x_576_ = lean_box(0);
v_isShared_577_ = v_isSharedCheck_604_;
goto v_resetjp_575_;
}
v_resetjp_575_:
{
uint64_t v_tid_578_; lean_object* v_traces_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_603_; 
v_tid_578_ = lean_ctor_get_uint64(v_traceState_565_, sizeof(void*)*1);
v_traces_579_ = lean_ctor_get(v_traceState_565_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v_traceState_565_);
if (v_isSharedCheck_603_ == 0)
{
v___x_581_ = v_traceState_565_;
v_isShared_582_ = v_isSharedCheck_603_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_traces_579_);
lean_dec(v_traceState_565_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_603_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; lean_object* v___x_584_; double v___x_585_; uint8_t v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_594_; 
v___x_583_ = lean_box(0);
v___x_584_ = lean_box(0);
v___x_585_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0, &l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__0);
v___x_586_ = 0;
v___x_587_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__1));
v___x_588_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_588_, 0, v_cls_551_);
lean_ctor_set(v___x_588_, 1, v___x_584_);
lean_ctor_set(v___x_588_, 2, v___x_587_);
lean_ctor_set_float(v___x_588_, sizeof(void*)*3, v___x_585_);
lean_ctor_set_float(v___x_588_, sizeof(void*)*3 + 8, v___x_585_);
lean_ctor_set_uint8(v___x_588_, sizeof(void*)*3 + 16, v___x_586_);
v___x_589_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___closed__2));
v___x_590_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_590_, 0, v___x_588_);
lean_ctor_set(v___x_590_, 1, v_a_560_);
lean_ctor_set(v___x_590_, 2, v___x_589_);
lean_inc(v_ref_558_);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_ref_558_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v___x_592_ = l_Lean_PersistentArray_push___redArg(v_traces_579_, v___x_591_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_592_);
v___x_594_ = v___x_581_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_602_; 
v_reuseFailAlloc_602_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_602_, 0, v___x_592_);
lean_ctor_set_uint64(v_reuseFailAlloc_602_, sizeof(void*)*1, v_tid_578_);
v___x_594_ = v_reuseFailAlloc_602_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_596_; 
if (v_isShared_577_ == 0)
{
lean_ctor_set(v___x_576_, 4, v___x_594_);
v___x_596_ = v___x_576_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_env_566_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_nextMacroScope_567_);
lean_ctor_set(v_reuseFailAlloc_601_, 2, v_ngen_568_);
lean_ctor_set(v_reuseFailAlloc_601_, 3, v_auxDeclNGen_569_);
lean_ctor_set(v_reuseFailAlloc_601_, 4, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_601_, 5, v_cache_570_);
lean_ctor_set(v_reuseFailAlloc_601_, 6, v_recordedDeps_571_);
lean_ctor_set(v_reuseFailAlloc_601_, 7, v_messages_572_);
lean_ctor_set(v_reuseFailAlloc_601_, 8, v_infoState_573_);
lean_ctor_set(v_reuseFailAlloc_601_, 9, v_snapshotTasks_574_);
v___x_596_ = v_reuseFailAlloc_601_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_597_; lean_object* v___x_599_; 
v___x_597_ = lean_st_ref_put(v___y_556_, v___x_596_);
if (v_isShared_563_ == 0)
{
lean_ctor_set(v___x_562_, 0, v___x_583_);
v___x_599_ = v___x_562_;
goto v_reusejp_598_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_583_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2___boxed(lean_object* v_cls_606_, lean_object* v_msg_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v_cls_606_, v_msg_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_613_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__3(void){
_start:
{
lean_object* v___x_618_; lean_object* v___x_619_; 
v___x_618_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__2));
v___x_619_ = l_Lean_stringToMessageData(v___x_618_);
return v___x_619_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__5(void){
_start:
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__4));
v___x_622_ = l_Lean_stringToMessageData(v___x_621_);
return v___x_622_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__1___closed__11(void){
_start:
{
lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_629_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__10));
v___x_630_ = lean_unsigned_to_nat(22u);
v___x_631_ = lean_unsigned_to_nat(64u);
v___x_632_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__9));
v___x_633_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__8));
v___x_634_ = l_mkPanicMessageWithDecl(v___x_633_, v___x_632_, v___x_631_, v___x_630_, v___x_629_);
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object* v_fvarId_635_, lean_object* v_hFVarId_636_, lean_object* v___x_637_, lean_object* v_fst_638_, lean_object* v_fvarSubst_639_, uint8_t v_clearH_640_, lean_object* v___x_641_, lean_object* v___x_642_, lean_object* v___x_643_, uint8_t v_skip_644_, uint8_t v___x_645_, lean_object* v___x_646_, lean_object* v_snd_647_, lean_object* v___x_648_, lean_object* v___x_649_, lean_object* v_a_650_, uint8_t v_symm_651_, uint8_t v___x_652_, lean_object* v___x_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v___y_660_; lean_object* v___y_661_; lean_object* v___y_662_; lean_object* v___y_668_; lean_object* v___y_669_; lean_object* v___y_670_; lean_object* v___y_676_; lean_object* v_mvarId_677_; lean_object* v___y_678_; lean_object* v___y_679_; lean_object* v___y_680_; lean_object* v___y_681_; lean_object* v___y_730_; lean_object* v___y_731_; lean_object* v_newVal_732_; lean_object* v___y_733_; lean_object* v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_760_; uint8_t v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v_major_764_; lean_object* v___y_765_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_801_; uint8_t v___y_802_; lean_object* v_motive_803_; lean_object* v_newType_804_; lean_object* v___x_815_; 
lean_inc(v_snd_647_);
v___x_815_ = l_Lean_MVarId_getDecl(v_snd_647_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_object* v_a_816_; lean_object* v_type_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___f_820_; lean_object* v___x_821_; 
v_a_816_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_a_816_);
lean_dec_ref_known(v___x_815_, 1);
v_type_817_ = lean_ctor_get(v_a_816_, 2);
lean_inc_ref_n(v_type_817_, 2);
lean_dec(v_a_816_);
v___x_818_ = lean_box(v___x_652_);
v___x_819_ = lean_box(v___x_645_);
lean_inc_ref(v___x_641_);
lean_inc(v___x_642_);
lean_inc_ref(v___x_637_);
v___f_820_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__0___boxed), 12, 6);
lean_closure_set(v___f_820_, 0, v_type_817_);
lean_closure_set(v___f_820_, 1, v___x_637_);
lean_closure_set(v___f_820_, 2, v___x_642_);
lean_closure_set(v___f_820_, 3, v___x_641_);
lean_closure_set(v___f_820_, 4, v___x_818_);
lean_closure_set(v___f_820_, 5, v___x_819_);
lean_inc(v___x_648_);
v___x_821_ = l_Lean_FVarId_getDecl___redArg(v___x_648_, v___y_654_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_821_) == 0)
{
lean_object* v_a_822_; lean_object* v___x_823_; lean_object* v___x_824_; 
v_a_822_ = lean_ctor_get(v___x_821_, 0);
lean_inc(v_a_822_);
lean_dec_ref_known(v___x_821_, 1);
v___x_823_ = l_Lean_LocalDecl_type(v_a_822_);
lean_dec(v_a_822_);
v___x_824_ = l_Lean_Meta_matchEq_x3f(v___x_823_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_824_) == 0)
{
lean_object* v_a_825_; lean_object* v___y_827_; 
v_a_825_ = lean_ctor_get(v___x_824_, 0);
lean_inc(v_a_825_);
lean_dec_ref_known(v___x_824_, 1);
if (lean_obj_tag(v_a_825_) == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; 
lean_dec_ref(v___f_820_);
lean_dec_ref(v_type_817_);
lean_dec(v_a_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v___x_897_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__11, &l_Lean_Meta_substCore___lam__1___closed__11_once, _init_l_Lean_Meta_substCore___lam__1___closed__11);
v___x_898_ = l_panic___at___00Lean_Meta_substCore_spec__6(v___x_897_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
return v___x_898_;
}
else
{
lean_object* v_val_899_; lean_object* v_snd_900_; 
v_val_899_ = lean_ctor_get(v_a_825_, 0);
lean_inc(v_val_899_);
lean_dec_ref_known(v_a_825_, 1);
v_snd_900_ = lean_ctor_get(v_val_899_, 1);
lean_inc(v_snd_900_);
lean_dec(v_val_899_);
if (v_symm_651_ == 0)
{
lean_object* v_snd_901_; 
v_snd_901_ = lean_ctor_get(v_snd_900_, 1);
lean_inc(v_snd_901_);
lean_dec(v_snd_900_);
v___y_827_ = v_snd_901_;
goto v___jp_826_;
}
else
{
lean_object* v_fst_902_; 
v_fst_902_ = lean_ctor_get(v_snd_900_, 0);
lean_inc(v_fst_902_);
lean_dec(v_snd_900_);
v___y_827_ = v_fst_902_;
goto v___jp_826_;
}
}
v___jp_826_:
{
lean_object* v___x_828_; lean_object* v_a_829_; lean_object* v___x_830_; lean_object* v_a_831_; uint8_t v___x_832_; 
v___x_828_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_827_, v___y_655_);
v_a_829_ = lean_ctor_get(v___x_828_, 0);
lean_inc(v_a_829_);
lean_dec_ref(v___x_828_);
lean_inc(v___x_648_);
lean_inc_ref(v_type_817_);
v___x_830_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_type_817_, v___x_648_, v___y_655_);
v_a_831_ = lean_ctor_get(v___x_830_, 0);
lean_inc(v_a_831_);
lean_dec_ref(v___x_830_);
v___x_832_ = lean_unbox(v_a_831_);
if (v___x_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; lean_object* v___x_836_; 
lean_dec_ref(v___f_820_);
v___x_833_ = lean_mk_empty_array_with_capacity(v___x_653_);
lean_inc_ref(v___x_641_);
v___x_834_ = lean_array_push(v___x_833_, v___x_641_);
v___x_835_ = 1;
lean_inc_ref(v_type_817_);
v___x_836_ = l_Lean_Meta_mkLambdaFVars(v___x_834_, v_type_817_, v___x_652_, v___x_645_, v___x_652_, v___x_645_, v___x_835_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec_ref(v___x_834_);
if (lean_obj_tag(v___x_836_) == 0)
{
lean_object* v_a_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_a_837_ = lean_ctor_get(v___x_836_, 0);
lean_inc(v_a_837_);
lean_dec_ref_known(v___x_836_, 1);
lean_inc_ref(v___x_641_);
v___x_838_ = l_Lean_Expr_replaceFVar(v_type_817_, v___x_641_, v_a_829_);
lean_dec_ref(v_type_817_);
v___x_839_ = lean_unbox(v_a_831_);
lean_dec(v_a_831_);
v___y_801_ = v_a_829_;
v___y_802_ = v___x_839_;
v_motive_803_ = v_a_837_;
v_newType_804_ = v___x_838_;
goto v___jp_800_;
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
lean_dec(v_a_831_);
lean_dec(v_a_829_);
lean_dec_ref(v_type_817_);
lean_dec(v_a_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_840_ = lean_ctor_get(v___x_836_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_836_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_836_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_836_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_inc_ref(v___x_641_);
v___x_848_ = l_Lean_Expr_replaceFVar(v_type_817_, v___x_641_, v_a_829_);
lean_inc(v_a_829_);
v___x_849_ = l_Lean_Meta_mkEqRefl(v_a_829_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_851_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref_known(v___x_849_, 1);
lean_inc_ref(v___x_637_);
v___x_851_ = l_Lean_Expr_replaceFVar(v___x_848_, v___x_637_, v_a_850_);
lean_dec(v_a_850_);
lean_dec_ref(v___x_848_);
if (v_symm_651_ == 0)
{
lean_object* v___x_852_; 
lean_dec_ref(v_type_817_);
lean_inc_ref(v___x_641_);
lean_inc(v_a_829_);
v___x_852_ = l_Lean_Meta_mkEq(v_a_829_, v___x_641_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref_known(v___x_852_, 1);
v___x_854_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__7));
v___x_855_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v___x_854_, v_a_853_, v___f_820_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_855_) == 0)
{
lean_object* v_a_856_; uint8_t v___x_857_; 
v_a_856_ = lean_ctor_get(v___x_855_, 0);
lean_inc(v_a_856_);
lean_dec_ref_known(v___x_855_, 1);
v___x_857_ = lean_unbox(v_a_831_);
lean_dec(v_a_831_);
v___y_801_ = v_a_829_;
v___y_802_ = v___x_857_;
v_motive_803_ = v_a_856_;
v_newType_804_ = v___x_851_;
goto v___jp_800_;
}
else
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_865_; 
lean_dec_ref(v___x_851_);
lean_dec(v_a_831_);
lean_dec(v_a_829_);
lean_dec(v_a_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_858_ = lean_ctor_get(v___x_855_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_855_);
if (v_isSharedCheck_865_ == 0)
{
v___x_860_ = v___x_855_;
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_855_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_865_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v___x_863_; 
if (v_isShared_861_ == 0)
{
v___x_863_ = v___x_860_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_858_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
else
{
lean_object* v_a_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_873_; 
lean_dec_ref(v___x_851_);
lean_dec(v_a_831_);
lean_dec(v_a_829_);
lean_dec_ref(v___f_820_);
lean_dec(v_a_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_866_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_873_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_873_ == 0)
{
v___x_868_ = v___x_852_;
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_a_866_);
lean_dec(v___x_852_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_873_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v___x_871_; 
if (v_isShared_869_ == 0)
{
v___x_871_ = v___x_868_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_a_866_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
else
{
lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; uint8_t v___x_877_; lean_object* v___x_878_; 
lean_dec_ref(v___f_820_);
v___x_874_ = lean_mk_empty_array_with_capacity(v___x_642_);
lean_inc_ref(v___x_641_);
v___x_875_ = lean_array_push(v___x_874_, v___x_641_);
lean_inc_ref(v___x_637_);
v___x_876_ = lean_array_push(v___x_875_, v___x_637_);
v___x_877_ = 1;
v___x_878_ = l_Lean_Meta_mkLambdaFVars(v___x_876_, v_type_817_, v___x_652_, v___x_645_, v___x_652_, v___x_645_, v___x_877_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
lean_dec_ref(v___x_876_);
if (lean_obj_tag(v___x_878_) == 0)
{
lean_object* v_a_879_; uint8_t v___x_880_; 
v_a_879_ = lean_ctor_get(v___x_878_, 0);
lean_inc(v_a_879_);
lean_dec_ref_known(v___x_878_, 1);
v___x_880_ = lean_unbox(v_a_831_);
lean_dec(v_a_831_);
v___y_801_ = v_a_829_;
v___y_802_ = v___x_880_;
v_motive_803_ = v_a_879_;
v_newType_804_ = v___x_851_;
goto v___jp_800_;
}
else
{
lean_object* v_a_881_; lean_object* v___x_883_; uint8_t v_isShared_884_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v___x_851_);
lean_dec(v_a_831_);
lean_dec(v_a_829_);
lean_dec(v_a_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_881_ = lean_ctor_get(v___x_878_, 0);
v_isSharedCheck_888_ = !lean_is_exclusive(v___x_878_);
if (v_isSharedCheck_888_ == 0)
{
v___x_883_ = v___x_878_;
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
else
{
lean_inc(v_a_881_);
lean_dec(v___x_878_);
v___x_883_ = lean_box(0);
v_isShared_884_ = v_isSharedCheck_888_;
goto v_resetjp_882_;
}
v_resetjp_882_:
{
lean_object* v___x_886_; 
if (v_isShared_884_ == 0)
{
v___x_886_ = v___x_883_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_a_881_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
else
{
lean_object* v_a_889_; lean_object* v___x_891_; uint8_t v_isShared_892_; uint8_t v_isSharedCheck_896_; 
lean_dec_ref(v___x_848_);
lean_dec(v_a_831_);
lean_dec(v_a_829_);
lean_dec_ref(v___f_820_);
lean_dec_ref(v_type_817_);
lean_dec(v_a_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_889_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_896_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_896_ == 0)
{
v___x_891_ = v___x_849_;
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
else
{
lean_inc(v_a_889_);
lean_dec(v___x_849_);
v___x_891_ = lean_box(0);
v_isShared_892_ = v_isSharedCheck_896_;
goto v_resetjp_890_;
}
v_resetjp_890_:
{
lean_object* v___x_894_; 
if (v_isShared_892_ == 0)
{
v___x_894_ = v___x_891_;
goto v_reusejp_893_;
}
else
{
lean_object* v_reuseFailAlloc_895_; 
v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_895_, 0, v_a_889_);
v___x_894_ = v_reuseFailAlloc_895_;
goto v_reusejp_893_;
}
v_reusejp_893_:
{
return v___x_894_;
}
}
}
}
}
}
else
{
lean_object* v_a_903_; lean_object* v___x_905_; uint8_t v_isShared_906_; uint8_t v_isSharedCheck_910_; 
lean_dec_ref(v___f_820_);
lean_dec_ref(v_type_817_);
lean_dec(v_a_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_903_ = lean_ctor_get(v___x_824_, 0);
v_isSharedCheck_910_ = !lean_is_exclusive(v___x_824_);
if (v_isSharedCheck_910_ == 0)
{
v___x_905_ = v___x_824_;
v_isShared_906_ = v_isSharedCheck_910_;
goto v_resetjp_904_;
}
else
{
lean_inc(v_a_903_);
lean_dec(v___x_824_);
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
lean_dec_ref(v___f_820_);
lean_dec_ref(v_type_817_);
lean_dec(v_a_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_911_ = lean_ctor_get(v___x_821_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_821_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_821_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_821_);
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
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec(v_a_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_919_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_815_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_815_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v___x_924_; 
if (v_isShared_922_ == 0)
{
v___x_924_ = v___x_921_;
goto v_reusejp_923_;
}
else
{
lean_object* v_reuseFailAlloc_925_; 
v_reuseFailAlloc_925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_925_, 0, v_a_919_);
v___x_924_ = v_reuseFailAlloc_925_;
goto v_reusejp_923_;
}
v_reusejp_923_:
{
return v___x_924_;
}
}
}
v___jp_659_:
{
lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_663_ = l_Lean_Meta_FVarSubst_insert(v___y_660_, v_fvarId_635_, v___y_662_);
v___x_664_ = l_Lean_Meta_FVarSubst_insert(v___x_663_, v_hFVarId_636_, v___x_637_);
v___x_665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_665_, 0, v___x_664_);
lean_ctor_set(v___x_665_, 1, v___y_661_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_665_);
return v___x_666_;
}
v___jp_667_:
{
lean_object* v___x_671_; lean_object* v___x_672_; 
v___x_671_ = lean_array_get_size(v___y_669_);
v___x_672_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_638_, v___y_669_, v___x_671_, v___x_671_, v_fvarSubst_639_);
lean_dec_ref(v___y_669_);
if (v_clearH_640_ == 0)
{
lean_object* v_a_673_; 
lean_dec_ref(v___y_668_);
v_a_673_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_673_);
lean_dec_ref(v___x_672_);
v___y_660_ = v_a_673_;
v___y_661_ = v___y_670_;
v___y_662_ = v___x_641_;
goto v___jp_659_;
}
else
{
lean_object* v_a_674_; 
lean_dec_ref(v___x_641_);
v_a_674_ = lean_ctor_get(v___x_672_, 0);
lean_inc(v_a_674_);
lean_dec_ref(v___x_672_);
v___y_660_ = v_a_674_;
v___y_661_ = v___y_670_;
v___y_662_ = v___y_668_;
goto v___jp_659_;
}
}
v___jp_675_:
{
lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; 
v___x_682_ = lean_array_get_size(v_fst_638_);
v___x_683_ = lean_nat_sub(v___x_682_, v___x_642_);
lean_dec(v___x_642_);
lean_inc(v___x_683_);
v___x_684_ = l_Lean_Meta_introNCore(v_mvarId_677_, v___x_683_, v___x_643_, v_skip_644_, v___x_645_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_684_) == 0)
{
lean_object* v_a_685_; lean_object* v_toCold_686_; lean_object* v_options_687_; uint8_t v_hasTrace_688_; 
v_a_685_ = lean_ctor_get(v___x_684_, 0);
lean_inc(v_a_685_);
lean_dec_ref_known(v___x_684_, 1);
v_toCold_686_ = lean_ctor_get(v___y_680_, 0);
v_options_687_ = lean_ctor_get(v_toCold_686_, 2);
v_hasTrace_688_ = lean_ctor_get_uint8(v_options_687_, sizeof(void*)*1);
if (v_hasTrace_688_ == 0)
{
lean_object* v_fst_689_; lean_object* v_snd_690_; 
lean_dec(v___x_683_);
lean_dec(v___x_646_);
v_fst_689_ = lean_ctor_get(v_a_685_, 0);
lean_inc(v_fst_689_);
v_snd_690_ = lean_ctor_get(v_a_685_, 1);
lean_inc(v_snd_690_);
lean_dec(v_a_685_);
v___y_668_ = v___y_676_;
v___y_669_ = v_fst_689_;
v___y_670_ = v_snd_690_;
goto v___jp_667_;
}
else
{
lean_object* v_fst_691_; lean_object* v_snd_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_720_; 
v_fst_691_ = lean_ctor_get(v_a_685_, 0);
v_snd_692_ = lean_ctor_get(v_a_685_, 1);
v_isSharedCheck_720_ = !lean_is_exclusive(v_a_685_);
if (v_isSharedCheck_720_ == 0)
{
v___x_694_ = v_a_685_;
v_isShared_695_ = v_isSharedCheck_720_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_snd_692_);
lean_inc(v_fst_691_);
lean_dec(v_a_685_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_720_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_inheritedTraceOptions_696_; lean_object* v___x_697_; lean_object* v___x_698_; uint8_t v___x_699_; 
v_inheritedTraceOptions_696_ = lean_ctor_get(v_toCold_686_, 11);
v___x_697_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
lean_inc(v___x_646_);
v___x_698_ = l_Lean_Name_append(v___x_697_, v___x_646_);
v___x_699_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_696_, v_options_687_, v___x_698_);
lean_dec(v___x_698_);
if (v___x_699_ == 0)
{
lean_del_object(v___x_694_);
lean_dec(v___x_683_);
lean_dec(v___x_646_);
v___y_668_ = v___y_676_;
v___y_669_ = v_fst_691_;
v___y_670_ = v_snd_692_;
goto v___jp_667_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_705_; 
v___x_700_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__3, &l_Lean_Meta_substCore___lam__1___closed__3_once, _init_l_Lean_Meta_substCore___lam__1___closed__3);
v___x_701_ = l_Nat_reprFast(v___x_683_);
v___x_702_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_702_, 0, v___x_701_);
v___x_703_ = l_Lean_MessageData_ofFormat(v___x_702_);
if (v_isShared_695_ == 0)
{
lean_ctor_set_tag(v___x_694_, 7);
lean_ctor_set(v___x_694_, 1, v___x_703_);
lean_ctor_set(v___x_694_, 0, v___x_700_);
v___x_705_ = v___x_694_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_703_);
v___x_705_ = v_reuseFailAlloc_719_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_706_ = lean_obj_once(&l_Lean_Meta_substCore___lam__1___closed__5, &l_Lean_Meta_substCore___lam__1___closed__5_once, _init_l_Lean_Meta_substCore___lam__1___closed__5);
v___x_707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_707_, 0, v___x_705_);
lean_ctor_set(v___x_707_, 1, v___x_706_);
lean_inc(v_snd_692_);
v___x_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_708_, 0, v_snd_692_);
v___x_709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_709_, 0, v___x_707_);
lean_ctor_set(v___x_709_, 1, v___x_708_);
v___x_710_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_646_, v___x_709_, v___y_678_, v___y_679_, v___y_680_, v___y_681_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_dec_ref_known(v___x_710_, 1);
v___y_668_ = v___y_676_;
v___y_669_ = v_fst_691_;
v___y_670_ = v_snd_692_;
goto v___jp_667_;
}
else
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_718_; 
lean_dec(v_snd_692_);
lean_dec(v_fst_691_);
lean_dec_ref(v___y_676_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_718_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_718_ == 0)
{
v___x_713_ = v___x_710_;
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_718_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
lean_object* v___x_716_; 
if (v_isShared_714_ == 0)
{
v___x_716_ = v___x_713_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_717_; 
v_reuseFailAlloc_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_717_, 0, v_a_711_);
v___x_716_ = v_reuseFailAlloc_717_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
return v___x_716_;
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
lean_object* v_a_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec(v___x_683_);
lean_dec_ref(v___y_676_);
lean_dec(v___x_646_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_721_ = lean_ctor_get(v___x_684_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v___x_684_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_a_721_);
lean_dec(v___x_684_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_a_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
return v___x_726_;
}
}
}
}
v___jp_729_:
{
lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_737_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_snd_647_, v_newVal_732_, v___y_734_);
lean_dec_ref(v___x_737_);
v___x_738_ = l_Lean_Expr_mvarId_x21(v___y_731_);
lean_dec_ref(v___y_731_);
if (v_clearH_640_ == 0)
{
lean_dec(v___x_649_);
lean_dec(v___x_648_);
v___y_676_ = v___y_730_;
v_mvarId_677_ = v___x_738_;
v___y_678_ = v___y_733_;
v___y_679_ = v___y_734_;
v___y_680_ = v___y_735_;
v___y_681_ = v___y_736_;
goto v___jp_675_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = l_Lean_MVarId_clear(v___x_738_, v___x_648_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_object* v_a_740_; lean_object* v___x_741_; 
v_a_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_a_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = l_Lean_MVarId_clear(v_a_740_, v___x_649_, v___y_733_, v___y_734_, v___y_735_, v___y_736_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v_a_742_; 
v_a_742_ = lean_ctor_get(v___x_741_, 0);
lean_inc(v_a_742_);
lean_dec_ref_known(v___x_741_, 1);
v___y_676_ = v___y_730_;
v_mvarId_677_ = v_a_742_;
v___y_678_ = v___y_733_;
v___y_679_ = v___y_734_;
v___y_680_ = v___y_735_;
v___y_681_ = v___y_736_;
goto v___jp_675_;
}
else
{
lean_object* v_a_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_750_; 
lean_dec_ref(v___y_730_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_743_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_741_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_741_);
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
else
{
lean_object* v_a_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_758_; 
lean_dec_ref(v___y_730_);
lean_dec(v___x_649_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_751_ = lean_ctor_get(v___x_739_, 0);
v_isSharedCheck_758_ = !lean_is_exclusive(v___x_739_);
if (v_isSharedCheck_758_ == 0)
{
v___x_753_ = v___x_739_;
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_a_751_);
lean_dec(v___x_739_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_758_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
if (v_isShared_754_ == 0)
{
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v_a_751_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
}
v___jp_759_:
{
lean_object* v___x_769_; 
v___x_769_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_762_, v_a_650_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_769_) == 0)
{
if (v___y_761_ == 0)
{
lean_object* v_a_770_; lean_object* v___x_771_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc_n(v_a_770_, 2);
lean_dec_ref_known(v___x_769_, 1);
v___x_771_ = l_Lean_Meta_mkEqNDRec(v___y_763_, v_a_770_, v_major_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_771_) == 0)
{
lean_object* v_a_772_; 
v_a_772_ = lean_ctor_get(v___x_771_, 0);
lean_inc(v_a_772_);
lean_dec_ref_known(v___x_771_, 1);
v___y_730_ = v___y_760_;
v___y_731_ = v_a_770_;
v_newVal_732_ = v_a_772_;
v___y_733_ = v___y_765_;
v___y_734_ = v___y_766_;
v___y_735_ = v___y_767_;
v___y_736_ = v___y_768_;
goto v___jp_729_;
}
else
{
lean_object* v_a_773_; lean_object* v___x_775_; uint8_t v_isShared_776_; uint8_t v_isSharedCheck_780_; 
lean_dec(v_a_770_);
lean_dec_ref(v___y_760_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_773_ = lean_ctor_get(v___x_771_, 0);
v_isSharedCheck_780_ = !lean_is_exclusive(v___x_771_);
if (v_isSharedCheck_780_ == 0)
{
v___x_775_ = v___x_771_;
v_isShared_776_ = v_isSharedCheck_780_;
goto v_resetjp_774_;
}
else
{
lean_inc(v_a_773_);
lean_dec(v___x_771_);
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
else
{
lean_object* v_a_781_; lean_object* v___x_782_; 
v_a_781_ = lean_ctor_get(v___x_769_, 0);
lean_inc_n(v_a_781_, 2);
lean_dec_ref_known(v___x_769_, 1);
v___x_782_ = l_Lean_Meta_mkEqRec(v___y_763_, v_a_781_, v_major_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
if (lean_obj_tag(v___x_782_) == 0)
{
lean_object* v_a_783_; 
v_a_783_ = lean_ctor_get(v___x_782_, 0);
lean_inc(v_a_783_);
lean_dec_ref_known(v___x_782_, 1);
v___y_730_ = v___y_760_;
v___y_731_ = v_a_781_;
v_newVal_732_ = v_a_783_;
v___y_733_ = v___y_765_;
v___y_734_ = v___y_766_;
v___y_735_ = v___y_767_;
v___y_736_ = v___y_768_;
goto v___jp_729_;
}
else
{
lean_object* v_a_784_; lean_object* v___x_786_; uint8_t v_isShared_787_; uint8_t v_isSharedCheck_791_; 
lean_dec(v_a_781_);
lean_dec_ref(v___y_760_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_784_ = lean_ctor_get(v___x_782_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_782_);
if (v_isSharedCheck_791_ == 0)
{
v___x_786_ = v___x_782_;
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
else
{
lean_inc(v_a_784_);
lean_dec(v___x_782_);
v___x_786_ = lean_box(0);
v_isShared_787_ = v_isSharedCheck_791_;
goto v_resetjp_785_;
}
v_resetjp_785_:
{
lean_object* v___x_789_; 
if (v_isShared_787_ == 0)
{
v___x_789_ = v___x_786_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
v___x_789_ = v_reuseFailAlloc_790_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
return v___x_789_;
}
}
}
}
}
else
{
lean_object* v_a_792_; lean_object* v___x_794_; uint8_t v_isShared_795_; uint8_t v_isSharedCheck_799_; 
lean_dec_ref(v_major_764_);
lean_dec_ref(v___y_763_);
lean_dec_ref(v___y_760_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_792_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_799_ == 0)
{
v___x_794_ = v___x_769_;
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
else
{
lean_inc(v_a_792_);
lean_dec(v___x_769_);
v___x_794_ = lean_box(0);
v_isShared_795_ = v_isSharedCheck_799_;
goto v_resetjp_793_;
}
v_resetjp_793_:
{
lean_object* v___x_797_; 
if (v_isShared_795_ == 0)
{
v___x_797_ = v___x_794_;
goto v_reusejp_796_;
}
else
{
lean_object* v_reuseFailAlloc_798_; 
v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
v___x_797_ = v_reuseFailAlloc_798_;
goto v_reusejp_796_;
}
v_reusejp_796_:
{
return v___x_797_;
}
}
}
}
v___jp_800_:
{
if (v_symm_651_ == 0)
{
lean_object* v___x_805_; 
lean_inc_ref(v___x_637_);
v___x_805_ = l_Lean_Meta_mkEqSymm(v___x_637_, v___y_654_, v___y_655_, v___y_656_, v___y_657_);
if (lean_obj_tag(v___x_805_) == 0)
{
lean_object* v_a_806_; 
v_a_806_ = lean_ctor_get(v___x_805_, 0);
lean_inc(v_a_806_);
lean_dec_ref_known(v___x_805_, 1);
v___y_760_ = v___y_801_;
v___y_761_ = v___y_802_;
v___y_762_ = v_newType_804_;
v___y_763_ = v_motive_803_;
v_major_764_ = v_a_806_;
v___y_765_ = v___y_654_;
v___y_766_ = v___y_655_;
v___y_767_ = v___y_656_;
v___y_768_ = v___y_657_;
goto v___jp_759_;
}
else
{
lean_object* v_a_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_814_; 
lean_dec_ref(v_newType_804_);
lean_dec_ref(v_motive_803_);
lean_dec_ref(v___y_801_);
lean_dec(v_a_650_);
lean_dec(v___x_649_);
lean_dec(v___x_648_);
lean_dec(v_snd_647_);
lean_dec(v___x_646_);
lean_dec(v___x_643_);
lean_dec(v___x_642_);
lean_dec_ref(v___x_641_);
lean_dec(v_fvarSubst_639_);
lean_dec_ref(v___x_637_);
lean_dec(v_hFVarId_636_);
lean_dec(v_fvarId_635_);
v_a_807_ = lean_ctor_get(v___x_805_, 0);
v_isSharedCheck_814_ = !lean_is_exclusive(v___x_805_);
if (v_isSharedCheck_814_ == 0)
{
v___x_809_ = v___x_805_;
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_a_807_);
lean_dec(v___x_805_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_814_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_812_; 
if (v_isShared_810_ == 0)
{
v___x_812_ = v___x_809_;
goto v_reusejp_811_;
}
else
{
lean_object* v_reuseFailAlloc_813_; 
v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_813_, 0, v_a_807_);
v___x_812_ = v_reuseFailAlloc_813_;
goto v_reusejp_811_;
}
v_reusejp_811_:
{
return v___x_812_;
}
}
}
}
else
{
lean_inc_ref(v___x_637_);
v___y_760_ = v___y_801_;
v___y_761_ = v___y_802_;
v___y_762_ = v_newType_804_;
v___y_763_ = v_motive_803_;
v_major_764_ = v___x_637_;
v___y_765_ = v___y_654_;
v___y_766_ = v___y_655_;
v___y_767_ = v___y_656_;
v___y_768_ = v___y_657_;
goto v___jp_759_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object** _args){
lean_object* v_fvarId_927_ = _args[0];
lean_object* v_hFVarId_928_ = _args[1];
lean_object* v___x_929_ = _args[2];
lean_object* v_fst_930_ = _args[3];
lean_object* v_fvarSubst_931_ = _args[4];
lean_object* v_clearH_932_ = _args[5];
lean_object* v___x_933_ = _args[6];
lean_object* v___x_934_ = _args[7];
lean_object* v___x_935_ = _args[8];
lean_object* v_skip_936_ = _args[9];
lean_object* v___x_937_ = _args[10];
lean_object* v___x_938_ = _args[11];
lean_object* v_snd_939_ = _args[12];
lean_object* v___x_940_ = _args[13];
lean_object* v___x_941_ = _args[14];
lean_object* v_a_942_ = _args[15];
lean_object* v_symm_943_ = _args[16];
lean_object* v___x_944_ = _args[17];
lean_object* v___x_945_ = _args[18];
lean_object* v___y_946_ = _args[19];
lean_object* v___y_947_ = _args[20];
lean_object* v___y_948_ = _args[21];
lean_object* v___y_949_ = _args[22];
lean_object* v___y_950_ = _args[23];
_start:
{
uint8_t v_clearH_boxed_951_; uint8_t v_skip_boxed_952_; uint8_t v___x_27774__boxed_953_; uint8_t v_symm_boxed_954_; uint8_t v___x_27780__boxed_955_; lean_object* v_res_956_; 
v_clearH_boxed_951_ = lean_unbox(v_clearH_932_);
v_skip_boxed_952_ = lean_unbox(v_skip_936_);
v___x_27774__boxed_953_ = lean_unbox(v___x_937_);
v_symm_boxed_954_ = lean_unbox(v_symm_943_);
v___x_27780__boxed_955_ = lean_unbox(v___x_944_);
v_res_956_ = l_Lean_Meta_substCore___lam__1(v_fvarId_927_, v_hFVarId_928_, v___x_929_, v_fst_930_, v_fvarSubst_931_, v_clearH_boxed_951_, v___x_933_, v___x_934_, v___x_935_, v_skip_boxed_952_, v___x_27774__boxed_953_, v___x_938_, v_snd_939_, v___x_940_, v___x_941_, v_a_942_, v_symm_boxed_954_, v___x_27780__boxed_955_, v___x_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_);
lean_dec(v___y_949_);
lean_dec_ref(v___y_948_);
lean_dec(v___y_947_);
lean_dec_ref(v___y_946_);
lean_dec(v___x_945_);
lean_dec_ref(v_fst_930_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object* v___x_957_, lean_object* v___y_958_, lean_object* v___y_959_, lean_object* v___y_960_, lean_object* v___y_961_){
_start:
{
lean_object* v_toCold_963_; lean_object* v_options_964_; uint8_t v_hasTrace_965_; 
v_toCold_963_ = lean_ctor_get(v___y_960_, 0);
v_options_964_ = lean_ctor_get(v_toCold_963_, 2);
v_hasTrace_965_ = lean_ctor_get_uint8(v_options_964_, sizeof(void*)*1);
if (v_hasTrace_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; 
lean_dec(v___x_957_);
v___x_966_ = lean_box(v_hasTrace_965_);
v___x_967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
return v___x_967_;
}
else
{
lean_object* v_inheritedTraceOptions_968_; lean_object* v___x_969_; lean_object* v___x_970_; uint8_t v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; 
v_inheritedTraceOptions_968_ = lean_ctor_get(v_toCold_963_, 11);
v___x_969_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
v___x_970_ = l_Lean_Name_append(v___x_969_, v___x_957_);
v___x_971_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_968_, v_options_964_, v___x_970_);
lean_dec(v___x_970_);
v___x_972_ = lean_box(v___x_971_);
v___x_973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_973_, 0, v___x_972_);
return v___x_973_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object* v___x_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_, lean_object* v___y_979_){
_start:
{
lean_object* v_res_980_; 
v_res_980_ = l_Lean_Meta_substCore___lam__2(v___x_974_, v___y_975_, v___y_976_, v___y_977_, v___y_978_);
lean_dec(v___y_978_);
lean_dec_ref(v___y_977_);
lean_dec(v___y_976_);
lean_dec_ref(v___y_975_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(lean_object* v_a_981_, lean_object* v_a_982_){
_start:
{
if (lean_obj_tag(v_a_981_) == 0)
{
lean_object* v___x_983_; 
v___x_983_ = l_List_reverse___redArg(v_a_982_);
return v___x_983_;
}
else
{
lean_object* v_head_984_; lean_object* v_tail_985_; lean_object* v___x_987_; uint8_t v_isShared_988_; uint8_t v_isSharedCheck_994_; 
v_head_984_ = lean_ctor_get(v_a_981_, 0);
v_tail_985_ = lean_ctor_get(v_a_981_, 1);
v_isSharedCheck_994_ = !lean_is_exclusive(v_a_981_);
if (v_isSharedCheck_994_ == 0)
{
v___x_987_ = v_a_981_;
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
else
{
lean_inc(v_tail_985_);
lean_inc(v_head_984_);
lean_dec(v_a_981_);
v___x_987_ = lean_box(0);
v_isShared_988_ = v_isSharedCheck_994_;
goto v_resetjp_986_;
}
v_resetjp_986_:
{
lean_object* v___x_989_; lean_object* v___x_991_; 
v___x_989_ = l_Lean_MessageData_ofName(v_head_984_);
if (v_isShared_988_ == 0)
{
lean_ctor_set(v___x_987_, 1, v_a_982_);
lean_ctor_set(v___x_987_, 0, v___x_989_);
v___x_991_ = v___x_987_;
goto v_reusejp_990_;
}
else
{
lean_object* v_reuseFailAlloc_993_; 
v_reuseFailAlloc_993_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_993_, 0, v___x_989_);
lean_ctor_set(v_reuseFailAlloc_993_, 1, v_a_982_);
v___x_991_ = v_reuseFailAlloc_993_;
goto v_reusejp_990_;
}
v_reusejp_990_:
{
v_a_981_ = v_tail_985_;
v_a_982_ = v___x_991_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(size_t v_sz_995_, size_t v_i_996_, lean_object* v_bs_997_){
_start:
{
uint8_t v___x_998_; 
v___x_998_ = lean_usize_dec_lt(v_i_996_, v_sz_995_);
if (v___x_998_ == 0)
{
return v_bs_997_;
}
else
{
lean_object* v_v_999_; lean_object* v___x_1000_; lean_object* v_bs_x27_1001_; size_t v___x_1002_; size_t v___x_1003_; lean_object* v___x_1004_; 
v_v_999_ = lean_array_uget(v_bs_997_, v_i_996_);
v___x_1000_ = lean_unsigned_to_nat(0u);
v_bs_x27_1001_ = lean_array_uset(v_bs_997_, v_i_996_, v___x_1000_);
v___x_1002_ = ((size_t)1ULL);
v___x_1003_ = lean_usize_add(v_i_996_, v___x_1002_);
v___x_1004_ = lean_array_uset(v_bs_x27_1001_, v_i_996_, v_v_999_);
v_i_996_ = v___x_1003_;
v_bs_997_ = v___x_1004_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8___boxed(lean_object* v_sz_1006_, lean_object* v_i_1007_, lean_object* v_bs_1008_){
_start:
{
size_t v_sz_boxed_1009_; size_t v_i_boxed_1010_; lean_object* v_res_1011_; 
v_sz_boxed_1009_ = lean_unbox_usize(v_sz_1006_);
lean_dec(v_sz_1006_);
v_i_boxed_1010_ = lean_unbox_usize(v_i_1007_);
lean_dec(v_i_1007_);
v_res_1011_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_boxed_1009_, v_i_boxed_1010_, v_bs_1008_);
return v_res_1011_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1016_; lean_object* v___x_1017_; 
v___x_1016_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__2));
v___x_1017_ = l_Lean_stringToMessageData(v___x_1016_);
return v___x_1017_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__4));
v___x_1020_ = l_Lean_stringToMessageData(v___x_1019_);
return v___x_1020_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__7));
v___x_1025_ = l_Lean_MessageData_ofFormat(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__9(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__8, &l_Lean_Meta_substCore___lam__3___closed__8_once, _init_l_Lean_Meta_substCore___lam__3___closed__8);
v___x_1027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1026_);
return v___x_1027_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__11(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; 
v___x_1029_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__10));
v___x_1030_ = l_Lean_stringToMessageData(v___x_1029_);
return v___x_1030_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__13(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__12));
v___x_1033_ = l_Lean_stringToMessageData(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__15(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__14));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__17(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__16));
v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__19(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__18));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__25(void){
_start:
{
lean_object* v___x_1052_; lean_object* v___x_1053_; 
v___x_1052_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__24));
v___x_1053_ = l_Lean_stringToMessageData(v___x_1052_);
return v___x_1053_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__27(void){
_start:
{
lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1055_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__26));
v___x_1056_ = l_Lean_stringToMessageData(v___x_1055_);
return v___x_1056_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__29(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__28));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3(lean_object* v_mvarId_1062_, lean_object* v_hFVarId_1063_, lean_object* v___x_1064_, uint8_t v_clearH_1065_, lean_object* v_fvarSubst_1066_, uint8_t v_symm_1067_, uint8_t v_tryToSkip_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v___y_1075_; lean_object* v___y_1076_; lean_object* v___y_1077_; lean_object* v___y_1078_; lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___x_1112_; 
lean_inc(v_mvarId_1062_);
v___x_1112_ = l_Lean_MVarId_getTag(v_mvarId_1062_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; 
v_a_1113_ = lean_ctor_get(v___x_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v___x_1112_, 1);
v___x_1114_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
lean_inc(v_mvarId_1062_);
v___x_1115_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1062_, v___x_1114_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; 
lean_dec_ref_known(v___x_1115_, 1);
lean_inc(v_hFVarId_1063_);
v___x_1116_ = l_Lean_FVarId_getDecl___redArg(v_hFVarId_1063_, v___y_1069_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___x_1133_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = l_Lean_LocalDecl_type(v_a_1117_);
lean_dec(v_a_1117_);
lean_inc_ref(v___x_1118_);
v___x_1133_ = l_Lean_Meta_matchEq_x3f(v___x_1118_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
if (lean_obj_tag(v_a_1134_) == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; 
lean_dec_ref(v___x_1118_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v___x_1135_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__9, &l_Lean_Meta_substCore___lam__3___closed__9_once, _init_l_Lean_Meta_substCore___lam__3___closed__9);
v___x_1136_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1114_, v_mvarId_1062_, v___x_1135_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v___x_1136_;
}
else
{
lean_object* v_val_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1455_; 
v_val_1137_ = lean_ctor_get(v_a_1134_, 0);
v_isSharedCheck_1455_ = !lean_is_exclusive(v_a_1134_);
if (v_isSharedCheck_1455_ == 0)
{
v___x_1139_ = v_a_1134_;
v_isShared_1140_ = v_isSharedCheck_1455_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_val_1137_);
lean_dec(v_a_1134_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1455_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1453_; 
v_snd_1141_ = lean_ctor_get(v_val_1137_, 1);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_val_1137_);
if (v_isSharedCheck_1453_ == 0)
{
lean_object* v_unused_1454_; 
v_unused_1454_ = lean_ctor_get(v_val_1137_, 0);
lean_dec(v_unused_1454_);
v___x_1143_ = v_val_1137_;
v_isShared_1144_ = v_isSharedCheck_1453_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_dec(v_val_1137_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1453_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_fst_1145_; lean_object* v_snd_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1452_; 
v_fst_1145_ = lean_ctor_get(v_snd_1141_, 0);
v_snd_1146_ = lean_ctor_get(v_snd_1141_, 1);
v_isSharedCheck_1452_ = !lean_is_exclusive(v_snd_1141_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1148_ = v_snd_1141_;
v_isShared_1149_ = v_isSharedCheck_1452_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_snd_1146_);
lean_inc(v_fst_1145_);
lean_dec(v_snd_1141_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1452_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
uint8_t v___x_1150_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; uint8_t v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; uint8_t v_skip_1169_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; lean_object* v___y_1181_; uint8_t v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; uint8_t v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; lean_object* v___y_1222_; uint8_t v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; uint8_t v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1268_; lean_object* v___y_1269_; lean_object* v___y_1270_; uint8_t v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; uint8_t v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1325_; lean_object* v___y_1326_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1381_; lean_object* v___y_1382_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1415_; lean_object* v___y_1416_; lean_object* v___y_1448_; 
v___x_1150_ = 1;
if (v_symm_1067_ == 0)
{
lean_inc(v_fst_1145_);
v___y_1448_ = v_fst_1145_;
goto v___jp_1447_;
}
else
{
lean_inc(v_snd_1146_);
v___y_1448_ = v_snd_1146_;
goto v___jp_1447_;
}
v___jp_1151_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; 
v___x_1170_ = lean_box(v_clearH_1065_);
v___x_1171_ = lean_box(v_skip_1169_);
v___x_1172_ = lean_box(v___x_1150_);
v___x_1173_ = lean_box(v_symm_1067_);
v___x_1174_ = lean_box(v___y_1157_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 24, 19);
lean_closure_set(v___f_1175_, 0, v___y_1168_);
lean_closure_set(v___f_1175_, 1, v_hFVarId_1063_);
lean_closure_set(v___f_1175_, 2, v___y_1162_);
lean_closure_set(v___f_1175_, 3, v___y_1156_);
lean_closure_set(v___f_1175_, 4, v_fvarSubst_1066_);
lean_closure_set(v___f_1175_, 5, v___x_1170_);
lean_closure_set(v___f_1175_, 6, v___y_1166_);
lean_closure_set(v___f_1175_, 7, v___y_1159_);
lean_closure_set(v___f_1175_, 8, v___y_1155_);
lean_closure_set(v___f_1175_, 9, v___x_1171_);
lean_closure_set(v___f_1175_, 10, v___x_1172_);
lean_closure_set(v___f_1175_, 11, v___y_1153_);
lean_closure_set(v___f_1175_, 12, v___y_1154_);
lean_closure_set(v___f_1175_, 13, v___y_1161_);
lean_closure_set(v___f_1175_, 14, v___y_1158_);
lean_closure_set(v___f_1175_, 15, v_a_1113_);
lean_closure_set(v___f_1175_, 16, v___x_1173_);
lean_closure_set(v___f_1175_, 17, v___x_1174_);
lean_closure_set(v___f_1175_, 18, v___y_1160_);
v___x_1176_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v___y_1164_, v___f_1175_, v___y_1165_, v___y_1163_, v___y_1152_, v___y_1167_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1152_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1165_);
return v___x_1176_;
}
v___jp_1177_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_array_get(v___x_1064_, v___y_1186_, v___x_1194_);
lean_inc(v___x_1195_);
v___x_1196_ = l_Lean_mkFVar(v___x_1195_);
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_array_get(v___x_1064_, v___y_1186_, v___x_1197_);
lean_dec_ref(v___y_1186_);
lean_inc(v___x_1198_);
v___x_1199_ = l_Lean_mkFVar(v___x_1198_);
if (v_tryToSkip_1068_ == 0)
{
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1185_);
v___y_1152_ = v___y_1192_;
v___y_1153_ = v___y_1178_;
v___y_1154_ = v___y_1179_;
v___y_1155_ = v___y_1180_;
v___y_1156_ = v___y_1181_;
v___y_1157_ = v___y_1182_;
v___y_1158_ = v___x_1195_;
v___y_1159_ = v___y_1183_;
v___y_1160_ = v___x_1197_;
v___y_1161_ = v___x_1198_;
v___y_1162_ = v___x_1199_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1187_;
v___y_1165_ = v___y_1190_;
v___y_1166_ = v___x_1196_;
v___y_1167_ = v___y_1193_;
v___y_1168_ = v___y_1184_;
v_skip_1169_ = v___y_1188_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = lean_array_get_size(v___y_1185_);
lean_dec_ref(v___y_1185_);
v___x_1201_ = lean_nat_dec_eq(v___x_1200_, v___y_1189_);
lean_dec(v___y_1189_);
if (v___x_1201_ == 0)
{
v___y_1152_ = v___y_1192_;
v___y_1153_ = v___y_1178_;
v___y_1154_ = v___y_1179_;
v___y_1155_ = v___y_1180_;
v___y_1156_ = v___y_1181_;
v___y_1157_ = v___y_1182_;
v___y_1158_ = v___x_1195_;
v___y_1159_ = v___y_1183_;
v___y_1160_ = v___x_1197_;
v___y_1161_ = v___x_1198_;
v___y_1162_ = v___x_1199_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1187_;
v___y_1165_ = v___y_1190_;
v___y_1166_ = v___x_1196_;
v___y_1167_ = v___y_1193_;
v___y_1168_ = v___y_1184_;
v_skip_1169_ = v___y_1188_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1202_; 
lean_inc(v___y_1187_);
v___x_1202_ = l_Lean_MVarId_getType(v___y_1187_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; lean_object* v_a_1205_; uint8_t v___x_1206_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc_n(v_a_1203_, 2);
lean_dec_ref_known(v___x_1202_, 1);
lean_inc(v___x_1195_);
v___x_1204_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1203_, v___x_1195_, v___y_1191_);
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref(v___x_1204_);
v___x_1206_ = lean_unbox(v_a_1205_);
lean_dec(v_a_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v_a_1208_; uint8_t v___x_1209_; 
lean_inc(v___x_1198_);
v___x_1207_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1203_, v___x_1198_, v___y_1191_);
v_a_1208_ = lean_ctor_get(v___x_1207_, 0);
lean_inc(v_a_1208_);
lean_dec_ref(v___x_1207_);
v___x_1209_ = lean_unbox(v_a_1208_);
lean_dec(v_a_1208_);
if (v___x_1209_ == 0)
{
lean_dec_ref(v___x_1199_);
lean_dec_ref(v___x_1196_);
lean_dec(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec(v_a_1113_);
lean_dec(v_hFVarId_1063_);
v___y_1075_ = v___y_1192_;
v___y_1076_ = v___y_1191_;
v___y_1077_ = v___y_1187_;
v___y_1078_ = v___y_1190_;
v___y_1079_ = v___y_1193_;
v___y_1080_ = v___x_1195_;
v___y_1081_ = v___x_1198_;
goto v___jp_1074_;
}
else
{
v___y_1152_ = v___y_1192_;
v___y_1153_ = v___y_1178_;
v___y_1154_ = v___y_1179_;
v___y_1155_ = v___y_1180_;
v___y_1156_ = v___y_1181_;
v___y_1157_ = v___y_1182_;
v___y_1158_ = v___x_1195_;
v___y_1159_ = v___y_1183_;
v___y_1160_ = v___x_1197_;
v___y_1161_ = v___x_1198_;
v___y_1162_ = v___x_1199_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1187_;
v___y_1165_ = v___y_1190_;
v___y_1166_ = v___x_1196_;
v___y_1167_ = v___y_1193_;
v___y_1168_ = v___y_1184_;
v_skip_1169_ = v___y_1188_;
goto v___jp_1151_;
}
}
else
{
lean_dec(v_a_1203_);
v___y_1152_ = v___y_1192_;
v___y_1153_ = v___y_1178_;
v___y_1154_ = v___y_1179_;
v___y_1155_ = v___y_1180_;
v___y_1156_ = v___y_1181_;
v___y_1157_ = v___y_1182_;
v___y_1158_ = v___x_1195_;
v___y_1159_ = v___y_1183_;
v___y_1160_ = v___x_1197_;
v___y_1161_ = v___x_1198_;
v___y_1162_ = v___x_1199_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1187_;
v___y_1165_ = v___y_1190_;
v___y_1166_ = v___x_1196_;
v___y_1167_ = v___y_1193_;
v___y_1168_ = v___y_1184_;
v_skip_1169_ = v___y_1188_;
goto v___jp_1151_;
}
}
else
{
lean_object* v_a_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1217_; 
lean_dec_ref(v___x_1199_);
lean_dec(v___x_1198_);
lean_dec_ref(v___x_1196_);
lean_dec(v___x_1195_);
lean_dec(v___y_1193_);
lean_dec_ref(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1187_);
lean_dec(v___y_1184_);
lean_dec(v___y_1183_);
lean_dec_ref(v___y_1181_);
lean_dec(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1210_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1212_ = v___x_1202_;
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_a_1210_);
lean_dec(v___x_1202_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1217_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1215_; 
if (v_isShared_1213_ == 0)
{
v___x_1215_ = v___x_1212_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_a_1210_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
}
v___jp_1218_:
{
lean_object* v___x_1236_; 
lean_inc_ref(v___y_1229_);
lean_inc(v___y_1235_);
lean_inc_ref(v___y_1234_);
lean_inc(v___y_1233_);
lean_inc_ref(v___y_1232_);
v___x_1236_ = lean_apply_5(v___y_1229_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_, lean_box(0));
if (lean_obj_tag(v___x_1236_) == 0)
{
lean_object* v_a_1237_; uint8_t v___x_1238_; 
v_a_1237_ = lean_ctor_get(v___x_1236_, 0);
lean_inc(v_a_1237_);
lean_dec_ref_known(v___x_1236_, 1);
v___x_1238_ = lean_unbox(v_a_1237_);
lean_dec(v_a_1237_);
if (v___x_1238_ == 0)
{
lean_dec(v___y_1227_);
lean_del_object(v___x_1148_);
lean_inc(v___y_1220_);
v___y_1178_ = v___y_1219_;
v___y_1179_ = v___y_1220_;
v___y_1180_ = v___y_1221_;
v___y_1181_ = v___y_1222_;
v___y_1182_ = v___y_1223_;
v___y_1183_ = v___y_1224_;
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1228_;
v___y_1186_ = v___y_1226_;
v___y_1187_ = v___y_1220_;
v___y_1188_ = v___y_1230_;
v___y_1189_ = v___y_1231_;
v___y_1190_ = v___y_1232_;
v___y_1191_ = v___y_1233_;
v___y_1192_ = v___y_1234_;
v___y_1193_ = v___y_1235_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1239_; size_t v_sz_1240_; size_t v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1248_; 
v___x_1239_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__11, &l_Lean_Meta_substCore___lam__3___closed__11_once, _init_l_Lean_Meta_substCore___lam__3___closed__11);
v_sz_1240_ = lean_array_size(v___y_1228_);
v___x_1241_ = ((size_t)0ULL);
lean_inc_ref(v___y_1228_);
v___x_1242_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1240_, v___x_1241_, v___y_1228_);
v___x_1243_ = lean_array_to_list(v___x_1242_);
v___x_1244_ = lean_box(0);
v___x_1245_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(v___x_1243_, v___x_1244_);
v___x_1246_ = l_Lean_MessageData_ofList(v___x_1245_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 7);
lean_ctor_set(v___x_1148_, 1, v___x_1246_);
lean_ctor_set(v___x_1148_, 0, v___x_1239_);
v___x_1248_ = v___x_1148_;
goto v_reusejp_1247_;
}
else
{
lean_object* v_reuseFailAlloc_1258_; 
v_reuseFailAlloc_1258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1258_, 0, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1258_, 1, v___x_1246_);
v___x_1248_ = v_reuseFailAlloc_1258_;
goto v_reusejp_1247_;
}
v_reusejp_1247_:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1227_, v___x_1248_, v___y_1232_, v___y_1233_, v___y_1234_, v___y_1235_);
if (lean_obj_tag(v___x_1249_) == 0)
{
lean_dec_ref_known(v___x_1249_, 1);
lean_inc(v___y_1220_);
v___y_1178_ = v___y_1219_;
v___y_1179_ = v___y_1220_;
v___y_1180_ = v___y_1221_;
v___y_1181_ = v___y_1222_;
v___y_1182_ = v___y_1223_;
v___y_1183_ = v___y_1224_;
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1228_;
v___y_1186_ = v___y_1226_;
v___y_1187_ = v___y_1220_;
v___y_1188_ = v___y_1230_;
v___y_1189_ = v___y_1231_;
v___y_1190_ = v___y_1232_;
v___y_1191_ = v___y_1233_;
v___y_1192_ = v___y_1234_;
v___y_1193_ = v___y_1235_;
goto v___jp_1177_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1228_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1250_ = lean_ctor_get(v___x_1249_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1249_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1249_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1249_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec_ref(v___y_1222_);
lean_dec(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec(v___y_1219_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1259_ = lean_ctor_get(v___x_1236_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1236_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1236_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1236_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
v___jp_1267_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_box(0);
lean_inc(v___y_1277_);
v___x_1283_ = l_Lean_Meta_introNCore(v___y_1269_, v___y_1277_, v___x_1282_, v___y_1276_, v___x_1150_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v_fst_1285_; lean_object* v_snd_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1315_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v_fst_1285_ = lean_ctor_get(v_a_1284_, 0);
v_snd_1286_ = lean_ctor_get(v_a_1284_, 1);
v_isSharedCheck_1315_ = !lean_is_exclusive(v_a_1284_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1288_ = v_a_1284_;
v_isShared_1289_ = v_isSharedCheck_1315_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_snd_1286_);
lean_inc(v_fst_1285_);
lean_dec(v_a_1284_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1315_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; 
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
lean_inc(v___y_1279_);
lean_inc_ref(v___y_1278_);
v___x_1290_ = lean_apply_5(v___y_1275_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_, lean_box(0));
if (lean_obj_tag(v___x_1290_) == 0)
{
lean_object* v_a_1291_; uint8_t v___x_1292_; 
v_a_1291_ = lean_ctor_get(v___x_1290_, 0);
lean_inc(v_a_1291_);
lean_dec_ref_known(v___x_1290_, 1);
v___x_1292_ = lean_unbox(v_a_1291_);
lean_dec(v_a_1291_);
if (v___x_1292_ == 0)
{
lean_del_object(v___x_1288_);
lean_inc_ref(v___y_1270_);
v___y_1219_ = v___y_1268_;
v___y_1220_ = v_snd_1286_;
v___y_1221_ = v___x_1282_;
v___y_1222_ = v___y_1270_;
v___y_1223_ = v___y_1271_;
v___y_1224_ = v___y_1272_;
v___y_1225_ = v___y_1273_;
v___y_1226_ = v_fst_1285_;
v___y_1227_ = v___y_1274_;
v___y_1228_ = v___y_1270_;
v___y_1229_ = v___y_1275_;
v___y_1230_ = v___y_1276_;
v___y_1231_ = v___y_1277_;
v___y_1232_ = v___y_1278_;
v___y_1233_ = v___y_1279_;
v___y_1234_ = v___y_1280_;
v___y_1235_ = v___y_1281_;
goto v___jp_1218_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; lean_object* v___x_1296_; 
v___x_1293_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__13, &l_Lean_Meta_substCore___lam__3___closed__13_once, _init_l_Lean_Meta_substCore___lam__3___closed__13);
lean_inc(v_snd_1286_);
v___x_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1294_, 0, v_snd_1286_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set_tag(v___x_1288_, 7);
lean_ctor_set(v___x_1288_, 1, v___x_1294_);
lean_ctor_set(v___x_1288_, 0, v___x_1293_);
v___x_1296_ = v___x_1288_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___x_1293_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v___x_1294_);
v___x_1296_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
lean_object* v___x_1297_; 
lean_inc(v___y_1274_);
v___x_1297_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1274_, v___x_1296_, v___y_1278_, v___y_1279_, v___y_1280_, v___y_1281_);
if (lean_obj_tag(v___x_1297_) == 0)
{
lean_dec_ref_known(v___x_1297_, 1);
lean_inc_ref(v___y_1270_);
v___y_1219_ = v___y_1268_;
v___y_1220_ = v_snd_1286_;
v___y_1221_ = v___x_1282_;
v___y_1222_ = v___y_1270_;
v___y_1223_ = v___y_1271_;
v___y_1224_ = v___y_1272_;
v___y_1225_ = v___y_1273_;
v___y_1226_ = v_fst_1285_;
v___y_1227_ = v___y_1274_;
v___y_1228_ = v___y_1270_;
v___y_1229_ = v___y_1275_;
v___y_1230_ = v___y_1276_;
v___y_1231_ = v___y_1277_;
v___y_1232_ = v___y_1278_;
v___y_1233_ = v___y_1279_;
v___y_1234_ = v___y_1280_;
v___y_1235_ = v___y_1281_;
goto v___jp_1218_;
}
else
{
lean_object* v_a_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1305_; 
lean_dec(v_snd_1286_);
lean_dec(v_fst_1285_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1268_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1298_ = lean_ctor_get(v___x_1297_, 0);
v_isSharedCheck_1305_ = !lean_is_exclusive(v___x_1297_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1300_ = v___x_1297_;
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_a_1298_);
lean_dec(v___x_1297_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1305_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___x_1303_; 
if (v_isShared_1301_ == 0)
{
v___x_1303_ = v___x_1300_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_a_1298_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
}
else
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
lean_del_object(v___x_1288_);
lean_dec(v_snd_1286_);
lean_dec(v_fst_1285_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1268_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1307_ = lean_ctor_get(v___x_1290_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1290_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1290_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1290_);
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
else
{
lean_object* v_a_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1323_; 
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1270_);
lean_dec(v___y_1268_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1316_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1323_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1318_ = v___x_1283_;
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_a_1316_);
lean_dec(v___x_1283_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1323_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1321_; 
if (v_isShared_1319_ == 0)
{
v___x_1321_ = v___x_1318_;
goto v_reusejp_1320_;
}
else
{
lean_object* v_reuseFailAlloc_1322_; 
v_reuseFailAlloc_1322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1322_, 0, v_a_1316_);
v___x_1321_ = v_reuseFailAlloc_1322_;
goto v_reusejp_1320_;
}
v_reusejp_1320_:
{
return v___x_1321_;
}
}
}
}
v___jp_1324_:
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; uint8_t v___x_1338_; lean_object* v___x_1339_; 
v___x_1334_ = lean_unsigned_to_nat(2u);
v___x_1335_ = lean_mk_empty_array_with_capacity(v___x_1334_);
v___x_1336_ = lean_array_push(v___x_1335_, v___y_1329_);
lean_inc(v_hFVarId_1063_);
v___x_1337_ = lean_array_push(v___x_1336_, v_hFVarId_1063_);
v___x_1338_ = 0;
v___x_1339_ = l_Lean_MVarId_revert(v_mvarId_1062_, v___x_1337_, v___x_1150_, v___x_1338_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v_a_1340_; lean_object* v_fst_1341_; lean_object* v_snd_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1371_; 
v_a_1340_ = lean_ctor_get(v___x_1339_, 0);
lean_inc(v_a_1340_);
lean_dec_ref_known(v___x_1339_, 1);
v_fst_1341_ = lean_ctor_get(v_a_1340_, 0);
v_snd_1342_ = lean_ctor_get(v_a_1340_, 1);
v_isSharedCheck_1371_ = !lean_is_exclusive(v_a_1340_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1344_ = v_a_1340_;
v_isShared_1345_ = v_isSharedCheck_1371_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_snd_1342_);
lean_inc(v_fst_1341_);
lean_dec(v_a_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1371_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v___x_1346_; 
lean_inc_ref(v___y_1328_);
lean_inc(v___y_1333_);
lean_inc_ref(v___y_1332_);
lean_inc(v___y_1331_);
lean_inc_ref(v___y_1330_);
v___x_1346_ = lean_apply_5(v___y_1328_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_, lean_box(0));
if (lean_obj_tag(v___x_1346_) == 0)
{
lean_object* v_a_1347_; uint8_t v___x_1348_; 
v_a_1347_ = lean_ctor_get(v___x_1346_, 0);
lean_inc(v_a_1347_);
lean_dec_ref_known(v___x_1346_, 1);
v___x_1348_ = lean_unbox(v_a_1347_);
lean_dec(v_a_1347_);
if (v___x_1348_ == 0)
{
lean_del_object(v___x_1344_);
v___y_1268_ = v___y_1325_;
v___y_1269_ = v_snd_1342_;
v___y_1270_ = v_fst_1341_;
v___y_1271_ = v___x_1338_;
v___y_1272_ = v___x_1334_;
v___y_1273_ = v___y_1326_;
v___y_1274_ = v___y_1327_;
v___y_1275_ = v___y_1328_;
v___y_1276_ = v___x_1338_;
v___y_1277_ = v___x_1334_;
v___y_1278_ = v___y_1330_;
v___y_1279_ = v___y_1331_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___y_1333_;
goto v___jp_1267_;
}
else
{
lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1349_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__15, &l_Lean_Meta_substCore___lam__3___closed__15_once, _init_l_Lean_Meta_substCore___lam__3___closed__15);
lean_inc(v_snd_1342_);
v___x_1350_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1350_, 0, v_snd_1342_);
if (v_isShared_1345_ == 0)
{
lean_ctor_set_tag(v___x_1344_, 7);
lean_ctor_set(v___x_1344_, 1, v___x_1350_);
lean_ctor_set(v___x_1344_, 0, v___x_1349_);
v___x_1352_ = v___x_1344_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1362_; 
v_reuseFailAlloc_1362_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1362_, 0, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1362_, 1, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1362_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1353_; 
lean_inc(v___y_1327_);
v___x_1353_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___y_1327_, v___x_1352_, v___y_1330_, v___y_1331_, v___y_1332_, v___y_1333_);
if (lean_obj_tag(v___x_1353_) == 0)
{
lean_dec_ref_known(v___x_1353_, 1);
v___y_1268_ = v___y_1325_;
v___y_1269_ = v_snd_1342_;
v___y_1270_ = v_fst_1341_;
v___y_1271_ = v___x_1338_;
v___y_1272_ = v___x_1334_;
v___y_1273_ = v___y_1326_;
v___y_1274_ = v___y_1327_;
v___y_1275_ = v___y_1328_;
v___y_1276_ = v___x_1338_;
v___y_1277_ = v___x_1334_;
v___y_1278_ = v___y_1330_;
v___y_1279_ = v___y_1331_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___y_1333_;
goto v___jp_1267_;
}
else
{
lean_object* v_a_1354_; lean_object* v___x_1356_; uint8_t v_isShared_1357_; uint8_t v_isSharedCheck_1361_; 
lean_dec(v_snd_1342_);
lean_dec(v_fst_1341_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec(v___y_1325_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1354_ = lean_ctor_get(v___x_1353_, 0);
v_isSharedCheck_1361_ = !lean_is_exclusive(v___x_1353_);
if (v_isSharedCheck_1361_ == 0)
{
v___x_1356_ = v___x_1353_;
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
else
{
lean_inc(v_a_1354_);
lean_dec(v___x_1353_);
v___x_1356_ = lean_box(0);
v_isShared_1357_ = v_isSharedCheck_1361_;
goto v_resetjp_1355_;
}
v_resetjp_1355_:
{
lean_object* v___x_1359_; 
if (v_isShared_1357_ == 0)
{
v___x_1359_ = v___x_1356_;
goto v_reusejp_1358_;
}
else
{
lean_object* v_reuseFailAlloc_1360_; 
v_reuseFailAlloc_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1360_, 0, v_a_1354_);
v___x_1359_ = v_reuseFailAlloc_1360_;
goto v_reusejp_1358_;
}
v_reusejp_1358_:
{
return v___x_1359_;
}
}
}
}
}
}
else
{
lean_object* v_a_1363_; lean_object* v___x_1365_; uint8_t v_isShared_1366_; uint8_t v_isSharedCheck_1370_; 
lean_del_object(v___x_1344_);
lean_dec(v_snd_1342_);
lean_dec(v_fst_1341_);
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec(v___y_1325_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1363_ = lean_ctor_get(v___x_1346_, 0);
v_isSharedCheck_1370_ = !lean_is_exclusive(v___x_1346_);
if (v_isSharedCheck_1370_ == 0)
{
v___x_1365_ = v___x_1346_;
v_isShared_1366_ = v_isSharedCheck_1370_;
goto v_resetjp_1364_;
}
else
{
lean_inc(v_a_1363_);
lean_dec(v___x_1346_);
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
}
else
{
lean_object* v_a_1372_; lean_object* v___x_1374_; uint8_t v_isShared_1375_; uint8_t v_isSharedCheck_1379_; 
lean_dec(v___y_1333_);
lean_dec_ref(v___y_1332_);
lean_dec(v___y_1331_);
lean_dec_ref(v___y_1330_);
lean_dec(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec(v___y_1325_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1372_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1379_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1374_ = v___x_1339_;
v_isShared_1375_ = v_isSharedCheck_1379_;
goto v_resetjp_1373_;
}
else
{
lean_inc(v_a_1372_);
lean_dec(v___x_1339_);
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
lean_object* v___x_1390_; lean_object* v_a_1391_; uint8_t v___x_1392_; 
lean_inc(v___y_1382_);
lean_inc_ref(v___y_1384_);
v___x_1390_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v___y_1384_, v___y_1382_, v___y_1387_);
v_a_1391_ = lean_ctor_get(v___x_1390_, 0);
lean_inc(v_a_1391_);
lean_dec_ref(v___x_1390_);
v___x_1392_ = lean_unbox(v_a_1391_);
lean_dec(v_a_1391_);
if (v___x_1392_ == 0)
{
lean_dec_ref(v___y_1385_);
lean_dec_ref(v___y_1384_);
lean_del_object(v___x_1143_);
lean_del_object(v___x_1139_);
lean_inc(v___y_1382_);
lean_inc(v___y_1381_);
v___y_1325_ = v___y_1381_;
v___y_1326_ = v___y_1382_;
v___y_1327_ = v___y_1381_;
v___y_1328_ = v___y_1383_;
v___y_1329_ = v___y_1382_;
v___y_1330_ = v___y_1386_;
v___y_1331_ = v___y_1387_;
v___y_1332_ = v___y_1388_;
v___y_1333_ = v___y_1389_;
goto v___jp_1324_;
}
else
{
lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1396_; 
v___x_1393_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_1394_ = l_Lean_MessageData_ofExpr(v___y_1385_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 7);
lean_ctor_set(v___x_1143_, 1, v___x_1394_);
lean_ctor_set(v___x_1143_, 0, v___x_1393_);
v___x_1396_ = v___x_1143_;
goto v_reusejp_1395_;
}
else
{
lean_object* v_reuseFailAlloc_1413_; 
v_reuseFailAlloc_1413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1413_, 0, v___x_1393_);
lean_ctor_set(v_reuseFailAlloc_1413_, 1, v___x_1394_);
v___x_1396_ = v_reuseFailAlloc_1413_;
goto v_reusejp_1395_;
}
v_reusejp_1395_:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1397_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__19, &l_Lean_Meta_substCore___lam__3___closed__19_once, _init_l_Lean_Meta_substCore___lam__3___closed__19);
v___x_1398_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1396_);
lean_ctor_set(v___x_1398_, 1, v___x_1397_);
v___x_1399_ = l_Lean_indentExpr(v___y_1384_);
v___x_1400_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1398_);
lean_ctor_set(v___x_1400_, 1, v___x_1399_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1400_);
v___x_1402_ = v___x_1139_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1412_; 
v_reuseFailAlloc_1412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1412_, 0, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1412_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; 
lean_inc(v_mvarId_1062_);
v___x_1403_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1114_, v_mvarId_1062_, v___x_1402_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
if (lean_obj_tag(v___x_1403_) == 0)
{
lean_dec_ref_known(v___x_1403_, 1);
lean_inc(v___y_1382_);
lean_inc(v___y_1381_);
v___y_1325_ = v___y_1381_;
v___y_1326_ = v___y_1382_;
v___y_1327_ = v___y_1381_;
v___y_1328_ = v___y_1383_;
v___y_1329_ = v___y_1382_;
v___y_1330_ = v___y_1386_;
v___y_1331_ = v___y_1387_;
v___y_1332_ = v___y_1388_;
v___y_1333_ = v___y_1389_;
goto v___jp_1324_;
}
else
{
lean_object* v_a_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1411_; 
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
lean_dec(v___y_1382_);
lean_dec(v___y_1381_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
v_a_1404_ = lean_ctor_get(v___x_1403_, 0);
v_isSharedCheck_1411_ = !lean_is_exclusive(v___x_1403_);
if (v_isSharedCheck_1411_ == 0)
{
v___x_1406_ = v___x_1403_;
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_a_1404_);
lean_dec(v___x_1403_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1411_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
lean_object* v___x_1409_; 
if (v_isShared_1407_ == 0)
{
v___x_1409_ = v___x_1406_;
goto v_reusejp_1408_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_a_1404_);
v___x_1409_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1408_;
}
v_reusejp_1408_:
{
return v___x_1409_;
}
}
}
}
}
}
}
v___jp_1414_:
{
lean_object* v___x_1417_; 
v___x_1417_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1416_, v___y_1070_);
if (lean_obj_tag(v___y_1415_) == 1)
{
lean_object* v_a_1418_; lean_object* v_fvarId_1419_; lean_object* v___x_1420_; lean_object* v___f_1421_; lean_object* v___x_1422_; lean_object* v_a_1423_; uint8_t v___x_1424_; 
lean_dec_ref(v___x_1118_);
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref(v___x_1417_);
v_fvarId_1419_ = lean_ctor_get(v___y_1415_, 0);
lean_inc(v_fvarId_1419_);
v___x_1420_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___f_1421_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__23));
v___x_1422_ = l_Lean_Meta_substCore___lam__2(v___x_1420_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref(v___x_1422_);
v___x_1424_ = lean_unbox(v_a_1423_);
lean_dec(v_a_1423_);
if (v___x_1424_ == 0)
{
v___y_1381_ = v___x_1420_;
v___y_1382_ = v_fvarId_1419_;
v___y_1383_ = v___f_1421_;
v___y_1384_ = v_a_1418_;
v___y_1385_ = v___y_1415_;
v___y_1386_ = v___y_1069_;
v___y_1387_ = v___y_1070_;
v___y_1388_ = v___y_1071_;
v___y_1389_ = v___y_1072_;
goto v___jp_1380_;
}
else
{
lean_object* v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1425_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__25, &l_Lean_Meta_substCore___lam__3___closed__25_once, _init_l_Lean_Meta_substCore___lam__3___closed__25);
lean_inc_ref(v___y_1415_);
v___x_1426_ = l_Lean_MessageData_ofExpr(v___y_1415_);
v___x_1427_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1427_, 0, v___x_1425_);
lean_ctor_set(v___x_1427_, 1, v___x_1426_);
v___x_1428_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__27, &l_Lean_Meta_substCore___lam__3___closed__27_once, _init_l_Lean_Meta_substCore___lam__3___closed__27);
v___x_1429_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1429_, 0, v___x_1427_);
lean_ctor_set(v___x_1429_, 1, v___x_1428_);
lean_inc(v_fvarId_1419_);
v___x_1430_ = l_Lean_MessageData_ofName(v_fvarId_1419_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__29, &l_Lean_Meta_substCore___lam__3___closed__29_once, _init_l_Lean_Meta_substCore___lam__3___closed__29);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
lean_inc(v_a_1418_);
v___x_1434_ = l_Lean_MessageData_ofExpr(v_a_1418_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_1420_, v___x_1435_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1436_) == 0)
{
lean_dec_ref_known(v___x_1436_, 1);
v___y_1381_ = v___x_1420_;
v___y_1382_ = v_fvarId_1419_;
v___y_1383_ = v___f_1421_;
v___y_1384_ = v_a_1418_;
v___y_1385_ = v___y_1415_;
v___y_1386_ = v___y_1069_;
v___y_1387_ = v___y_1070_;
v___y_1388_ = v___y_1071_;
v___y_1389_ = v___y_1072_;
goto v___jp_1380_;
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_dec(v_fvarId_1419_);
lean_dec(v_a_1418_);
lean_dec_ref_known(v___y_1415_, 1);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1143_);
lean_del_object(v___x_1139_);
lean_dec(v_a_1113_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
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
lean_dec_ref(v___x_1417_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1143_);
lean_del_object(v___x_1139_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
if (v_symm_1067_ == 0)
{
lean_object* v___x_1445_; 
v___x_1445_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__30));
v___y_1120_ = v___y_1415_;
v___y_1121_ = v___x_1445_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1446_; 
v___x_1446_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__31));
v___y_1120_ = v___y_1415_;
v___y_1121_ = v___x_1446_;
goto v___jp_1119_;
}
}
}
v___jp_1447_:
{
lean_object* v___x_1449_; 
v___x_1449_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1448_, v___y_1070_);
if (v_symm_1067_ == 0)
{
lean_object* v_a_1450_; 
lean_dec(v_fst_1145_);
v_a_1450_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1450_);
lean_dec_ref(v___x_1449_);
v___y_1415_ = v_a_1450_;
v___y_1416_ = v_snd_1146_;
goto v___jp_1414_;
}
else
{
lean_object* v_a_1451_; 
lean_dec(v_snd_1146_);
v_a_1451_ = lean_ctor_get(v___x_1449_, 0);
lean_inc(v_a_1451_);
lean_dec_ref(v___x_1449_);
v___y_1415_ = v_a_1451_;
v___y_1416_ = v_fst_1145_;
goto v___jp_1414_;
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
lean_dec_ref(v___x_1118_);
lean_dec(v_a_1113_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
v_a_1456_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1458_ = v___x_1133_;
v_isShared_1459_ = v_isSharedCheck_1463_;
goto v_resetjp_1457_;
}
else
{
lean_inc(v_a_1456_);
lean_dec(v___x_1133_);
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
v___jp_1119_:
{
lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; 
v___x_1122_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__3, &l_Lean_Meta_substCore___lam__3___closed__3_once, _init_l_Lean_Meta_substCore___lam__3___closed__3);
lean_inc_ref(v___y_1121_);
v___x_1123_ = l_Lean_stringToMessageData(v___y_1121_);
v___x_1124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1124_, 0, v___x_1122_);
lean_ctor_set(v___x_1124_, 1, v___x_1123_);
v___x_1125_ = l_Lean_indentExpr(v___x_1118_);
v___x_1126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1126_, 0, v___x_1124_);
lean_ctor_set(v___x_1126_, 1, v___x_1125_);
v___x_1127_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__5, &l_Lean_Meta_substCore___lam__3___closed__5_once, _init_l_Lean_Meta_substCore___lam__3___closed__5);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_indentExpr(v___y_1120_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1130_);
v___x_1132_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1114_, v_mvarId_1062_, v___x_1131_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
return v___x_1132_;
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec(v_a_1113_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
v_a_1464_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1116_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1116_);
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
lean_dec(v_a_1113_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
v_a_1472_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1115_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1115_);
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
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
v_a_1480_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1112_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1112_);
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
v___jp_1074_:
{
if (v_clearH_1065_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_fvarSubst_1066_);
lean_ctor_set(v___x_1082_, 1, v___y_1077_);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_MVarId_clear(v___y_1077_, v___y_1081_, v___y_1078_, v___y_1076_, v___y_1075_, v___y_1079_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = l_Lean_MVarId_clear(v_a_1085_, v___y_1080_, v___y_1078_, v___y_1076_, v___y_1075_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1078_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1095_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1095_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1095_ == 0)
{
v___x_1089_ = v___x_1086_;
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
else
{
lean_inc(v_a_1087_);
lean_dec(v___x_1086_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1095_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1091_; lean_object* v___x_1093_; 
v___x_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1091_, 0, v_fvarSubst_1066_);
lean_ctor_set(v___x_1091_, 1, v_a_1087_);
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
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec(v_fvarSubst_1066_);
v_a_1096_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1086_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1086_);
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
lean_dec(v___y_1080_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v_fvarSubst_1066_);
v_a_1104_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1084_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1084_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3___boxed(lean_object* v_mvarId_1488_, lean_object* v_hFVarId_1489_, lean_object* v___x_1490_, lean_object* v_clearH_1491_, lean_object* v_fvarSubst_1492_, lean_object* v_symm_1493_, lean_object* v_tryToSkip_1494_, lean_object* v___y_1495_, lean_object* v___y_1496_, lean_object* v___y_1497_, lean_object* v___y_1498_, lean_object* v___y_1499_){
_start:
{
uint8_t v_clearH_boxed_1500_; uint8_t v_symm_boxed_1501_; uint8_t v_tryToSkip_boxed_1502_; lean_object* v_res_1503_; 
v_clearH_boxed_1500_ = lean_unbox(v_clearH_1491_);
v_symm_boxed_1501_ = lean_unbox(v_symm_1493_);
v_tryToSkip_boxed_1502_ = lean_unbox(v_tryToSkip_1494_);
v_res_1503_ = l_Lean_Meta_substCore___lam__3(v_mvarId_1488_, v_hFVarId_1489_, v___x_1490_, v_clearH_boxed_1500_, v_fvarSubst_1492_, v_symm_boxed_1501_, v_tryToSkip_boxed_1502_, v___y_1495_, v___y_1496_, v___y_1497_, v___y_1498_);
lean_dec(v___x_1490_);
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
v___f_1519_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__3___boxed), 12, 7);
lean_closure_set(v___f_1519_, 0, v_mvarId_1504_);
lean_closure_set(v___f_1519_, 1, v_hFVarId_1505_);
lean_closure_set(v___f_1519_, 2, v___x_1515_);
lean_closure_set(v___f_1519_, 3, v___x_1516_);
lean_closure_set(v___f_1519_, 4, v_fvarSubst_1507_);
lean_closure_set(v___f_1519_, 5, v___x_1517_);
lean_closure_set(v___f_1519_, 6, v___x_1518_);
v___x_1520_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1504_, v___f_1519_, v_a_1510_, v_a_1511_, v_a_1512_, v_a_1513_);
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
lean_dec(v_a_1530_);
lean_dec_ref(v_a_1529_);
lean_dec(v_a_1528_);
lean_dec_ref(v_a_1527_);
return v_res_1535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1(lean_object* v_fst_1536_, lean_object* v_fst_1537_, lean_object* v_n_1538_, lean_object* v_i_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v___y_1542_, lean_object* v___y_1543_, lean_object* v___y_1544_, lean_object* v___y_1545_){
_start:
{
lean_object* v___x_1547_; 
v___x_1547_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___redArg(v_fst_1536_, v_fst_1537_, v_n_1538_, v_i_1539_, v_a_1541_);
return v___x_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1___boxed(lean_object* v_fst_1548_, lean_object* v_fst_1549_, lean_object* v_n_1550_, lean_object* v_i_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_, lean_object* v___y_1558_){
_start:
{
lean_object* v_res_1559_; 
v_res_1559_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__1(v_fst_1548_, v_fst_1549_, v_n_1550_, v_i_1551_, v_a_1552_, v_a_1553_, v___y_1554_, v___y_1555_, v___y_1556_, v___y_1557_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4(lean_object* v_mvarId_1560_, lean_object* v_val_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_){
_start:
{
lean_object* v___x_1567_; 
v___x_1567_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v_mvarId_1560_, v_val_1561_, v___y_1563_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___boxed(lean_object* v_mvarId_1568_, lean_object* v_val_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_){
_start:
{
lean_object* v_res_1575_; 
v_res_1575_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4(v_mvarId_1568_, v_val_1569_, v___y_1570_, v___y_1571_, v___y_1572_, v___y_1573_);
lean_dec(v___y_1573_);
lean_dec_ref(v___y_1572_);
lean_dec(v___y_1571_);
lean_dec_ref(v___y_1570_);
return v_res_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7(lean_object* v_00_u03b1_1576_, lean_object* v_name_1577_, uint8_t v_bi_1578_, lean_object* v_type_1579_, lean_object* v_k_1580_, uint8_t v_kind_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_){
_start:
{
lean_object* v___x_1587_; 
v___x_1587_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___redArg(v_name_1577_, v_bi_1578_, v_type_1579_, v_k_1580_, v_kind_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
return v___x_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7___boxed(lean_object* v_00_u03b1_1588_, lean_object* v_name_1589_, lean_object* v_bi_1590_, lean_object* v_type_1591_, lean_object* v_k_1592_, lean_object* v_kind_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_){
_start:
{
uint8_t v_bi_boxed_1599_; uint8_t v_kind_boxed_1600_; lean_object* v_res_1601_; 
v_bi_boxed_1599_ = lean_unbox(v_bi_1590_);
v_kind_boxed_1600_ = lean_unbox(v_kind_1593_);
v_res_1601_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5_spec__7(v_00_u03b1_1588_, v_name_1589_, v_bi_boxed_1599_, v_type_1591_, v_k_1592_, v_kind_boxed_1600_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
lean_dec(v___y_1597_);
lean_dec_ref(v___y_1596_);
lean_dec(v___y_1595_);
lean_dec_ref(v___y_1594_);
return v_res_1601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5(lean_object* v_00_u03b1_1602_, lean_object* v_name_1603_, lean_object* v_type_1604_, lean_object* v_k_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
lean_object* v___x_1611_; 
v___x_1611_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___redArg(v_name_1603_, v_type_1604_, v_k_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
return v___x_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5___boxed(lean_object* v_00_u03b1_1612_, lean_object* v_name_1613_, lean_object* v_type_1614_, lean_object* v_k_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__5(v_00_u03b1_1612_, v_name_1613_, v_type_1614_, v_k_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
lean_dec(v___y_1619_);
lean_dec_ref(v___y_1618_);
lean_dec(v___y_1617_);
lean_dec_ref(v___y_1616_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5(lean_object* v_00_u03b2_1622_, lean_object* v_x_1623_, lean_object* v_x_1624_, lean_object* v_x_1625_){
_start:
{
lean_object* v___x_1626_; 
v___x_1626_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5___redArg(v_x_1623_, v_x_1624_, v_x_1625_);
return v___x_1626_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8(lean_object* v_00_u03b2_1627_, lean_object* v_x_1628_, size_t v_x_1629_, size_t v_x_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_){
_start:
{
lean_object* v___x_1633_; 
v___x_1633_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___redArg(v_x_1628_, v_x_1629_, v_x_1630_, v_x_1631_, v_x_1632_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8___boxed(lean_object* v_00_u03b2_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_, lean_object* v_x_1639_){
_start:
{
size_t v_x_29601__boxed_1640_; size_t v_x_29602__boxed_1641_; lean_object* v_res_1642_; 
v_x_29601__boxed_1640_ = lean_unbox_usize(v_x_1636_);
lean_dec(v_x_1636_);
v_x_29602__boxed_1641_ = lean_unbox_usize(v_x_1637_);
lean_dec(v_x_1637_);
v_res_1642_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8(v_00_u03b2_1634_, v_x_1635_, v_x_29601__boxed_1640_, v_x_29602__boxed_1641_, v_x_1638_, v_x_1639_);
return v_res_1642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13(lean_object* v_00_u03b2_1643_, lean_object* v_n_1644_, lean_object* v_k_1645_, lean_object* v_v_1646_){
_start:
{
lean_object* v___x_1647_; 
v___x_1647_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13___redArg(v_n_1644_, v_k_1645_, v_v_1646_);
return v___x_1647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14(lean_object* v_00_u03b2_1648_, size_t v_depth_1649_, lean_object* v_keys_1650_, lean_object* v_vals_1651_, lean_object* v_heq_1652_, lean_object* v_i_1653_, lean_object* v_entries_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___redArg(v_depth_1649_, v_keys_1650_, v_vals_1651_, v_i_1653_, v_entries_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1656_, lean_object* v_depth_1657_, lean_object* v_keys_1658_, lean_object* v_vals_1659_, lean_object* v_heq_1660_, lean_object* v_i_1661_, lean_object* v_entries_1662_){
_start:
{
size_t v_depth_boxed_1663_; lean_object* v_res_1664_; 
v_depth_boxed_1663_ = lean_unbox_usize(v_depth_1657_);
lean_dec(v_depth_1657_);
v_res_1664_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__14(v_00_u03b2_1656_, v_depth_boxed_1663_, v_keys_1658_, v_vals_1659_, v_heq_1660_, v_i_1661_, v_entries_1662_);
lean_dec_ref(v_vals_1659_);
lean_dec_ref(v_keys_1658_);
return v_res_1664_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_1665_, lean_object* v_x_1666_, lean_object* v_x_1667_, lean_object* v_x_1668_, lean_object* v_x_1669_){
_start:
{
lean_object* v___x_1670_; 
v___x_1670_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4_spec__5_spec__8_spec__13_spec__14___redArg(v_x_1666_, v_x_1667_, v_x_1668_, v_x_1669_);
return v___x_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* v_fvarId_1674_, lean_object* v_mvarId_1675_, uint8_t v_tryToClear_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_, lean_object* v___y_1679_, lean_object* v___y_1680_){
_start:
{
lean_object* v___x_1682_; 
lean_inc(v_fvarId_1674_);
v___x_1682_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1674_, v___y_1677_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1682_) == 0)
{
lean_object* v_a_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; 
v_a_1683_ = lean_ctor_get(v___x_1682_, 0);
lean_inc(v_a_1683_);
lean_dec_ref_known(v___x_1682_, 1);
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
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_del_object(v___x_1688_);
v___x_1697_ = l_Lean_Expr_appFn_x21(v_a_1686_);
v___x_1698_ = l_Lean_Expr_appFn_x21(v___x_1697_);
v___x_1699_ = l_Lean_Expr_appFn_x21(v___x_1698_);
v___x_1700_ = l_Lean_Expr_appArg_x21(v___x_1699_);
lean_dec_ref(v___x_1699_);
v___x_1701_ = l_Lean_Expr_appArg_x21(v___x_1698_);
lean_dec_ref(v___x_1698_);
v___x_1702_ = l_Lean_Expr_appArg_x21(v___x_1697_);
lean_dec_ref(v___x_1697_);
v___x_1703_ = l_Lean_Expr_appArg_x21(v_a_1686_);
lean_dec(v_a_1686_);
v___x_1704_ = l_Lean_Meta_isExprDefEq(v___x_1700_, v___x_1702_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1704_) == 0)
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1761_; 
v_a_1705_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1761_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1761_ == 0)
{
v___x_1707_ = v___x_1704_;
v_isShared_1708_ = v_isSharedCheck_1761_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1704_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1761_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
uint8_t v___x_1709_; 
v___x_1709_ = lean_unbox(v_a_1705_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; lean_object* v___x_1712_; 
lean_dec(v_a_1705_);
lean_dec_ref(v___x_1703_);
lean_dec_ref(v___x_1701_);
lean_dec(v_a_1683_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_fvarId_1674_);
lean_ctor_set(v___x_1710_, 1, v_mvarId_1675_);
if (v_isShared_1708_ == 0)
{
lean_ctor_set(v___x_1707_, 0, v___x_1710_);
v___x_1712_ = v___x_1707_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1710_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
lean_del_object(v___x_1707_);
lean_inc(v_fvarId_1674_);
v___x_1714_ = l_Lean_mkFVar(v_fvarId_1674_);
v___x_1715_ = l_Lean_Meta_mkEqOfHEq(v___x_1714_, v___x_1692_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1715_) == 0)
{
lean_object* v_a_1716_; lean_object* v___x_1717_; 
v_a_1716_ = lean_ctor_get(v___x_1715_, 0);
lean_inc(v_a_1716_);
lean_dec_ref_known(v___x_1715_, 1);
v___x_1717_ = l_Lean_Meta_mkEq(v___x_1701_, v___x_1703_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = l_Lean_LocalDecl_userName(v_a_1683_);
lean_dec(v_a_1683_);
v___x_1720_ = l_Lean_MVarId_assert(v_mvarId_1675_, v___x_1719_, v_a_1718_, v_a_1716_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1720_) == 0)
{
if (v_tryToClear_1676_ == 0)
{
lean_object* v_a_1721_; uint8_t v___x_1722_; lean_object* v___x_1723_; 
lean_dec(v_fvarId_1674_);
v_a_1721_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1721_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1722_ = lean_unbox(v_a_1705_);
lean_dec(v_a_1705_);
v___x_1723_ = l_Lean_Meta_intro1Core(v_a_1721_, v___x_1722_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v___x_1723_;
}
else
{
lean_object* v_a_1724_; lean_object* v___x_1725_; 
v_a_1724_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1720_, 1);
v___x_1725_ = l_Lean_MVarId_tryClear(v_a_1724_, v_fvarId_1674_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; uint8_t v___x_1727_; lean_object* v___x_1728_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = lean_unbox(v_a_1705_);
lean_dec(v_a_1705_);
v___x_1728_ = l_Lean_Meta_intro1Core(v_a_1726_, v___x_1727_, v___y_1677_, v___y_1678_, v___y_1679_, v___y_1680_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
return v___x_1728_;
}
else
{
lean_object* v_a_1729_; lean_object* v___x_1731_; uint8_t v_isShared_1732_; uint8_t v_isSharedCheck_1736_; 
lean_dec(v_a_1705_);
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
lean_dec(v_a_1705_);
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
lean_dec(v_a_1716_);
lean_dec(v_a_1705_);
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
lean_dec(v_a_1705_);
lean_dec_ref(v___x_1703_);
lean_dec_ref(v___x_1701_);
lean_dec(v_a_1683_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_mvarId_1675_);
lean_dec(v_fvarId_1674_);
v_a_1753_ = lean_ctor_get(v___x_1715_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1715_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1715_);
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
lean_dec_ref(v___x_1703_);
lean_dec_ref(v___x_1701_);
lean_dec(v_a_1683_);
lean_dec(v___y_1680_);
lean_dec_ref(v___y_1679_);
lean_dec(v___y_1678_);
lean_dec_ref(v___y_1677_);
lean_dec(v_mvarId_1675_);
lean_dec(v_fvarId_1674_);
v_a_1762_ = lean_ctor_get(v___x_1704_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1704_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1764_ = v___x_1704_;
v_isShared_1765_ = v_isSharedCheck_1769_;
goto v_resetjp_1763_;
}
else
{
lean_inc(v_a_1762_);
lean_dec(v___x_1704_);
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
v___x_1807_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1797_, v___f_1806_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* v_mvarId_1808_, lean_object* v_fvarId_1809_, lean_object* v_tryToClear_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
uint8_t v_tryToClear_boxed_1816_; lean_object* v_res_1817_; 
v_tryToClear_boxed_1816_ = lean_unbox(v_tryToClear_1810_);
v_res_1817_ = l_Lean_Meta_heqToEq(v_mvarId_1808_, v_fvarId_1809_, v_tryToClear_boxed_1816_, v_a_1811_, v_a_1812_, v_a_1813_, v_a_1814_);
lean_dec(v_a_1814_);
lean_dec_ref(v_a_1813_);
lean_dec(v_a_1812_);
lean_dec_ref(v_a_1811_);
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
v___x_1864_ = l_Lean_Meta_matchEq_x3f(v___x_1863_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_);
if (lean_obj_tag(v___x_1864_) == 0)
{
lean_object* v_a_1865_; 
v_a_1865_ = lean_ctor_get(v___x_1864_, 0);
lean_inc(v_a_1865_);
lean_dec_ref_known(v___x_1864_, 1);
if (lean_obj_tag(v_a_1865_) == 1)
{
lean_object* v_val_1866_; lean_object* v_snd_1867_; lean_object* v_fst_1868_; lean_object* v_snd_1869_; lean_object* v___x_1870_; 
v_val_1866_ = lean_ctor_get(v_a_1865_, 0);
lean_inc(v_val_1866_);
lean_dec_ref_known(v_a_1865_, 1);
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
lean_dec_ref_known(v___x_1870_, 1);
v___x_1872_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1869_, v___y_1827_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; lean_object* v___y_1875_; uint8_t v___y_1876_; lean_object* v___y_1889_; uint8_t v___y_1894_; uint8_t v___x_1906_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
v___x_1906_ = l_Lean_Expr_isFVar(v_a_1873_);
if (v___x_1906_ == 0)
{
v___y_1894_ = v___x_1857_;
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
lean_dec(v_a_1873_);
lean_dec(v_val_1846_);
v_a_1832_ = v___x_1844_;
goto v___jp_1831_;
}
else
{
lean_object* v___x_1877_; 
lean_inc(v_x_1821_);
v___x_1877_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1873_, v_x_1821_, v___y_1875_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; uint8_t v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = lean_unbox(v_a_1878_);
lean_dec(v_a_1878_);
if (v___x_1879_ == 0)
{
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
lean_dec(v_x_1821_);
goto v___jp_1858_;
}
}
}
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_dec(v_val_1846_);
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
v___y_1876_ = v___x_1857_;
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
v___y_1889_ = v___y_1827_;
goto v___jp_1888_;
}
else
{
lean_object* v___x_1895_; 
lean_inc(v_x_1821_);
lean_inc(v_a_1871_);
v___x_1895_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1871_, v_x_1821_, v___y_1827_);
if (lean_obj_tag(v___x_1895_) == 0)
{
lean_object* v_a_1896_; uint8_t v___x_1897_; 
v_a_1896_ = lean_ctor_get(v___x_1895_, 0);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1895_, 1);
v___x_1897_ = lean_unbox(v_a_1896_);
lean_dec(v_a_1896_);
if (v___x_1897_ == 0)
{
lean_dec(v_a_1873_);
lean_dec(v_a_1871_);
lean_dec(v_x_1821_);
goto v___jp_1850_;
}
else
{
if (v___x_1857_ == 0)
{
lean_del_object(v___x_1848_);
v___y_1889_ = v___y_1827_;
goto v___jp_1888_;
}
else
{
lean_dec(v_a_1873_);
lean_dec(v_a_1871_);
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
lean_inc_ref(v_a_1832_);
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
lean_dec(v___y_1942_);
lean_dec_ref(v___y_1941_);
lean_dec(v___y_1940_);
lean_dec_ref(v___y_1939_);
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
v___x_1990_ = l_Lean_Meta_matchEq_x3f(v___x_1989_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_1991_);
lean_dec_ref_known(v___x_1990_, 1);
if (lean_obj_tag(v_a_1991_) == 1)
{
lean_object* v_val_1992_; lean_object* v_snd_1993_; lean_object* v_fst_1994_; lean_object* v_snd_1995_; lean_object* v___x_1996_; 
v_val_1992_ = lean_ctor_get(v_a_1991_, 0);
lean_inc(v_val_1992_);
lean_dec_ref_known(v_a_1991_, 1);
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
lean_dec_ref_known(v___x_1996_, 1);
v___x_1998_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1995_, v___y_1953_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___y_2001_; uint8_t v___y_2002_; lean_object* v___y_2015_; uint8_t v___y_2020_; uint8_t v___x_2032_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
v___x_2032_ = l_Lean_Expr_isFVar(v_a_1999_);
if (v___x_2032_ == 0)
{
v___y_2020_ = v___x_1983_;
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
lean_dec(v_a_1999_);
lean_dec(v_val_1972_);
v_a_1958_ = v___x_1970_;
goto v___jp_1957_;
}
else
{
lean_object* v___x_2003_; 
lean_inc(v_x_1947_);
v___x_2003_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1999_, v_x_1947_, v___y_2001_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; uint8_t v___x_2005_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = lean_unbox(v_a_2004_);
lean_dec(v_a_2004_);
if (v___x_2005_ == 0)
{
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
lean_dec(v_x_1947_);
goto v___jp_1984_;
}
}
}
else
{
lean_object* v_a_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2013_; 
lean_dec(v_val_1972_);
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
v___y_2002_ = v___x_1983_;
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
v___y_2015_ = v___y_1953_;
goto v___jp_2014_;
}
else
{
lean_object* v___x_2021_; 
lean_inc(v_x_1947_);
lean_inc(v_a_1997_);
v___x_2021_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__3___redArg(v_a_1997_, v_x_1947_, v___y_1953_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; uint8_t v___x_2023_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
lean_inc(v_a_2022_);
lean_dec_ref_known(v___x_2021_, 1);
v___x_2023_ = lean_unbox(v_a_2022_);
lean_dec(v_a_2022_);
if (v___x_2023_ == 0)
{
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
lean_dec(v_x_1947_);
goto v___jp_1976_;
}
else
{
if (v___x_1983_ == 0)
{
lean_del_object(v___x_1974_);
v___y_2015_ = v___y_1953_;
goto v___jp_2014_;
}
else
{
lean_dec(v_a_1999_);
lean_dec(v_a_1997_);
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
lean_inc_ref(v_a_1958_);
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
lean_dec(v___y_2068_);
lean_dec_ref(v___y_2067_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
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
lean_dec_ref_known(v_fst_2090_, 1);
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
lean_dec(v_x_2134_);
v___x_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2145_, 0, v_b_2138_);
return v___x_2145_;
}
else
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v_a_2148_; lean_object* v___x_2149_; 
lean_dec_ref(v_b_2138_);
v___x_2146_ = lean_box(0);
v___x_2147_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_2148_ = lean_array_uget_borrowed(v_as_2135_, v_i_2137_);
lean_inc(v_x_2134_);
v___x_2149_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2134_, v_a_2148_, v___y_2139_, v___y_2140_, v___y_2141_, v___y_2142_);
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
if (lean_obj_tag(v_a_2150_) == 1)
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2157_; 
lean_dec(v_x_2134_);
v___x_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2154_, 0, v_a_2150_);
v___x_2155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2155_, 0, v___x_2154_);
lean_ctor_set(v___x_2155_, 1, v___x_2146_);
if (v_isShared_2153_ == 0)
{
lean_ctor_set(v___x_2152_, 0, v___x_2155_);
v___x_2157_ = v___x_2152_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v___x_2155_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
else
{
size_t v___x_2159_; size_t v___x_2160_; 
lean_del_object(v___x_2152_);
lean_dec(v_a_2150_);
v___x_2159_ = ((size_t)1ULL);
v___x_2160_ = lean_usize_add(v_i_2137_, v___x_2159_);
v_i_2137_ = v___x_2160_;
v_b_2138_ = v___x_2147_;
goto _start;
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_x_2134_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2171_, lean_object* v_as_2172_, lean_object* v_sz_2173_, lean_object* v_i_2174_, lean_object* v_b_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_, lean_object* v___y_2179_, lean_object* v___y_2180_){
_start:
{
size_t v_sz_boxed_2181_; size_t v_i_boxed_2182_; lean_object* v_res_2183_; 
v_sz_boxed_2181_ = lean_unbox_usize(v_sz_2173_);
lean_dec(v_sz_2173_);
v_i_boxed_2182_ = lean_unbox_usize(v_i_2174_);
lean_dec(v_i_2174_);
v_res_2183_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2171_, v_as_2172_, v_sz_boxed_2181_, v_i_boxed_2182_, v_b_2175_, v___y_2176_, v___y_2177_, v___y_2178_, v___y_2179_);
lean_dec(v___y_2179_);
lean_dec_ref(v___y_2178_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec_ref(v_as_2172_);
return v_res_2183_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2184_, lean_object* v_x_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2184_, v_x_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
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
lean_dec_ref_known(v___x_2201_, 1);
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
lean_dec_ref_known(v_fst_2211_, 1);
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
lean_dec_ref_known(v_a_2202_, 1);
lean_dec(v_x_2192_);
return v___x_2201_;
}
}
else
{
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
lean_dec(v___y_2233_);
lean_dec_ref(v___y_2232_);
lean_dec(v___y_2231_);
lean_dec_ref(v___y_2230_);
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
lean_dec(v___y_2250_);
lean_dec_ref(v___y_2249_);
lean_dec(v___y_2248_);
lean_dec_ref(v___y_2247_);
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
lean_object* v___x_2314_; 
lean_inc(v_x_2262_);
v___x_2314_ = l_Lean_FVarId_getDecl___redArg(v_x_2262_, v___y_2264_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; uint8_t v___x_2316_; uint8_t v___x_2317_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = 0;
v___x_2317_ = l_Lean_LocalDecl_isLet(v_a_2315_, v___x_2316_);
lean_dec(v_a_2315_);
if (v___x_2317_ == 0)
{
goto v___jp_2269_;
}
else
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; 
v___x_2318_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2319_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2262_);
v___x_2320_ = l_Lean_mkFVar(v_x_2262_);
v___x_2321_ = l_Lean_MessageData_ofExpr(v___x_2320_);
v___x_2322_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2322_, 0, v___x_2319_);
lean_ctor_set(v___x_2322_, 1, v___x_2321_);
v___x_2323_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2324_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2324_, 0, v___x_2322_);
lean_ctor_set(v___x_2324_, 1, v___x_2323_);
v___x_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2325_, 0, v___x_2324_);
lean_inc(v_mvarId_2263_);
v___x_2326_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2318_, v_mvarId_2263_, v___x_2325_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_dec_ref_known(v___x_2326_, 1);
goto v___jp_2269_;
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec(v_mvarId_2263_);
lean_dec(v_x_2262_);
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2332_; 
if (v_isShared_2330_ == 0)
{
v___x_2332_ = v___x_2329_;
goto v_reusejp_2331_;
}
else
{
lean_object* v_reuseFailAlloc_2333_; 
v_reuseFailAlloc_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2333_, 0, v_a_2327_);
v___x_2332_ = v_reuseFailAlloc_2333_;
goto v_reusejp_2331_;
}
v_reusejp_2331_:
{
return v___x_2332_;
}
}
}
}
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_mvarId_2263_);
lean_dec(v_x_2262_);
v_a_2335_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2314_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2314_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2340_; 
if (v_isShared_2338_ == 0)
{
v___x_2340_ = v___x_2337_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v_a_2335_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
v___jp_2269_:
{
lean_object* v_lctx_2270_; lean_object* v___x_2271_; 
v_lctx_2270_ = lean_ctor_get(v___y_2264_, 2);
lean_inc(v_x_2262_);
v___x_2271_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2262_, v_lctx_2270_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v_a_2272_; 
v_a_2272_ = lean_ctor_get(v___x_2271_, 0);
lean_inc(v_a_2272_);
lean_dec_ref_known(v___x_2271_, 1);
if (lean_obj_tag(v_a_2272_) == 1)
{
lean_object* v_val_2273_; lean_object* v_fst_2274_; lean_object* v_snd_2275_; lean_object* v___x_2276_; uint8_t v___x_2277_; uint8_t v___x_2278_; lean_object* v___x_2279_; 
lean_dec(v_x_2262_);
v_val_2273_ = lean_ctor_get(v_a_2272_, 0);
lean_inc(v_val_2273_);
lean_dec_ref_known(v_a_2272_, 1);
v_fst_2274_ = lean_ctor_get(v_val_2273_, 0);
lean_inc(v_fst_2274_);
v_snd_2275_ = lean_ctor_get(v_val_2273_, 1);
lean_inc(v_snd_2275_);
lean_dec(v_val_2273_);
v___x_2276_ = lean_box(0);
v___x_2277_ = 1;
v___x_2278_ = lean_unbox(v_snd_2275_);
lean_dec(v_snd_2275_);
v___x_2279_ = l_Lean_Meta_substCore(v_mvarId_2263_, v_fst_2274_, v___x_2278_, v___x_2276_, v___x_2277_, v___x_2277_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2288_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2282_ = v___x_2279_;
v_isShared_2283_ = v_isSharedCheck_2288_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2279_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2288_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v_snd_2284_; lean_object* v___x_2286_; 
v_snd_2284_ = lean_ctor_get(v_a_2280_, 1);
lean_inc(v_snd_2284_);
lean_dec(v_a_2280_);
if (v_isShared_2283_ == 0)
{
lean_ctor_set(v___x_2282_, 0, v_snd_2284_);
v___x_2286_ = v___x_2282_;
goto v_reusejp_2285_;
}
else
{
lean_object* v_reuseFailAlloc_2287_; 
v_reuseFailAlloc_2287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_snd_2284_);
v___x_2286_ = v_reuseFailAlloc_2287_;
goto v_reusejp_2285_;
}
v_reusejp_2285_:
{
return v___x_2286_;
}
}
}
else
{
lean_object* v_a_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2296_; 
v_a_2289_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2279_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2279_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2294_; 
if (v_isShared_2292_ == 0)
{
v___x_2294_ = v___x_2291_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_a_2289_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
}
else
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
lean_dec(v_a_2272_);
v___x_2297_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2298_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2299_ = l_Lean_mkFVar(v_x_2262_);
v___x_2300_ = l_Lean_MessageData_ofExpr(v___x_2299_);
v___x_2301_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2298_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_2303_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2301_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
v___x_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2304_, 0, v___x_2303_);
v___x_2305_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2297_, v_mvarId_2263_, v___x_2304_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
return v___x_2305_;
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_dec(v_mvarId_2263_);
lean_dec(v_x_2262_);
v_a_2306_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2271_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2271_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2343_, lean_object* v_mvarId_2344_, lean_object* v___y_2345_, lean_object* v___y_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_){
_start:
{
lean_object* v_res_2350_; 
v_res_2350_ = l_Lean_Meta_substVar___lam__0(v_x_2343_, v_mvarId_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec(v___y_2346_);
lean_dec_ref(v___y_2345_);
return v_res_2350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2351_, lean_object* v_x_2352_, lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_){
_start:
{
lean_object* v___f_2358_; lean_object* v___x_2359_; 
lean_inc(v_mvarId_2351_);
v___f_2358_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2358_, 0, v_x_2352_);
lean_closure_set(v___f_2358_, 1, v_mvarId_2351_);
v___x_2359_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2351_, v___f_2358_, v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
return v___x_2359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2360_, lean_object* v_x_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lean_Meta_substVar(v_mvarId_2360_, v_x_2361_, v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
return v_res_2367_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2369_; lean_object* v___x_2370_; 
v___x_2369_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2370_ = l_Lean_stringToMessageData(v___x_2369_);
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2371_, lean_object* v_snd_2372_, uint8_t v___x_2373_, lean_object* v_fvarSubst_2374_, lean_object* v___y_2375_, lean_object* v___y_2376_, lean_object* v___y_2377_, lean_object* v___y_2378_){
_start:
{
lean_object* v___x_2380_; 
lean_inc(v_fst_2371_);
v___x_2380_ = l_Lean_FVarId_getDecl___redArg(v_fst_2371_, v___y_2375_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2380_) == 0)
{
lean_object* v_a_2381_; lean_object* v___y_2383_; lean_object* v___y_2384_; lean_object* v___y_2385_; lean_object* v___y_2386_; lean_object* v_newType_2395_; uint8_t v_symm_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___x_2436_; lean_object* v___x_2437_; 
v_a_2381_ = lean_ctor_get(v___x_2380_, 0);
lean_inc(v_a_2381_);
lean_dec_ref_known(v___x_2380_, 1);
v___x_2436_ = l_Lean_LocalDecl_type(v_a_2381_);
v___x_2437_ = l_Lean_Meta_matchEq_x3f(v___x_2436_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v_a_2438_; 
v_a_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc(v_a_2438_);
lean_dec_ref_known(v___x_2437_, 1);
if (lean_obj_tag(v_a_2438_) == 1)
{
lean_object* v_val_2439_; lean_object* v_snd_2440_; lean_object* v_fst_2441_; lean_object* v_snd_2442_; lean_object* v___x_2443_; 
v_val_2439_ = lean_ctor_get(v_a_2438_, 0);
lean_inc(v_val_2439_);
lean_dec_ref_known(v_a_2438_, 1);
v_snd_2440_ = lean_ctor_get(v_val_2439_, 1);
lean_inc(v_snd_2440_);
lean_dec(v_val_2439_);
v_fst_2441_ = lean_ctor_get(v_snd_2440_, 0);
lean_inc(v_fst_2441_);
v_snd_2442_ = lean_ctor_get(v_snd_2440_, 1);
lean_inc_n(v_snd_2442_, 2);
lean_dec(v_snd_2440_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
v___x_2443_ = lean_whnf(v_snd_2442_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; uint8_t v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = l_Lean_Expr_isFVar(v_a_2444_);
if (v___x_2445_ == 0)
{
lean_object* v___x_2446_; 
lean_dec(v_a_2444_);
lean_inc(v___y_2378_);
lean_inc_ref(v___y_2377_);
lean_inc(v___y_2376_);
lean_inc_ref(v___y_2375_);
lean_inc(v_fst_2441_);
v___x_2446_ = lean_whnf(v_fst_2441_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_object* v_a_2447_; uint8_t v___y_2449_; uint8_t v___x_2461_; 
v_a_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_a_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2461_ = l_Lean_Expr_isFVar(v_a_2447_);
if (v___x_2461_ == 0)
{
lean_dec(v_a_2447_);
lean_dec(v_snd_2442_);
lean_dec(v_fst_2441_);
lean_dec(v_fvarSubst_2374_);
lean_dec(v_fst_2371_);
v___y_2383_ = v___y_2375_;
v___y_2384_ = v___y_2376_;
v___y_2385_ = v___y_2377_;
v___y_2386_ = v___y_2378_;
goto v___jp_2382_;
}
else
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_expr_eqv(v_fst_2441_, v_a_2447_);
lean_dec(v_fst_2441_);
if (v___x_2462_ == 0)
{
v___y_2449_ = v___x_2461_;
goto v___jp_2448_;
}
else
{
v___y_2449_ = v___x_2445_;
goto v___jp_2448_;
}
}
v___jp_2448_:
{
if (v___y_2449_ == 0)
{
lean_object* v___x_2450_; 
lean_dec(v_a_2447_);
lean_dec(v_snd_2442_);
lean_dec(v_a_2381_);
v___x_2450_ = l_Lean_Meta_substCore(v_snd_2372_, v_fst_2371_, v___y_2449_, v_fvarSubst_2374_, v___x_2373_, v___x_2373_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v___x_2450_;
}
else
{
lean_object* v___x_2451_; 
v___x_2451_ = l_Lean_Meta_mkEq(v_a_2447_, v_snd_2442_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v_newType_2395_ = v_a_2452_;
v_symm_2396_ = v___x_2445_;
v___y_2397_ = v___y_2375_;
v___y_2398_ = v___y_2376_;
v___y_2399_ = v___y_2377_;
v___y_2400_ = v___y_2378_;
goto v___jp_2394_;
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
lean_dec(v_a_2381_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v_fvarSubst_2374_);
lean_dec(v_snd_2372_);
lean_dec(v_fst_2371_);
v_a_2453_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2451_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2451_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_snd_2442_);
lean_dec(v_fst_2441_);
lean_dec(v_a_2381_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v_fvarSubst_2374_);
lean_dec(v_snd_2372_);
lean_dec(v_fst_2371_);
v_a_2463_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2446_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2446_);
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
uint8_t v___x_2471_; 
v___x_2471_ = lean_expr_eqv(v_snd_2442_, v_a_2444_);
lean_dec(v_snd_2442_);
if (v___x_2471_ == 0)
{
if (v___x_2445_ == 0)
{
lean_object* v___x_2472_; 
lean_dec(v_a_2444_);
lean_dec(v_fst_2441_);
lean_dec(v_a_2381_);
v___x_2472_ = l_Lean_Meta_substCore(v_snd_2372_, v_fst_2371_, v___x_2373_, v_fvarSubst_2374_, v___x_2373_, v___x_2373_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v___x_2472_;
}
else
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lean_Meta_mkEq(v_fst_2441_, v_a_2444_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
if (lean_obj_tag(v___x_2473_) == 0)
{
lean_object* v_a_2474_; 
v_a_2474_ = lean_ctor_get(v___x_2473_, 0);
lean_inc(v_a_2474_);
lean_dec_ref_known(v___x_2473_, 1);
v_newType_2395_ = v_a_2474_;
v_symm_2396_ = v___x_2373_;
v___y_2397_ = v___y_2375_;
v___y_2398_ = v___y_2376_;
v___y_2399_ = v___y_2377_;
v___y_2400_ = v___y_2378_;
goto v___jp_2394_;
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v_a_2381_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v_fvarSubst_2374_);
lean_dec(v_snd_2372_);
lean_dec(v_fst_2371_);
v_a_2475_ = lean_ctor_get(v___x_2473_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2473_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2473_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2473_);
v___x_2477_ = lean_box(0);
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
v_resetjp_2476_:
{
lean_object* v___x_2480_; 
if (v_isShared_2478_ == 0)
{
v___x_2480_ = v___x_2477_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2481_; 
v_reuseFailAlloc_2481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2481_, 0, v_a_2475_);
v___x_2480_ = v_reuseFailAlloc_2481_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
return v___x_2480_;
}
}
}
}
}
else
{
lean_object* v___x_2483_; 
lean_dec(v_a_2444_);
lean_dec(v_fst_2441_);
lean_dec(v_a_2381_);
v___x_2483_ = l_Lean_Meta_substCore(v_snd_2372_, v_fst_2371_, v___x_2373_, v_fvarSubst_2374_, v___x_2373_, v___x_2373_, v___y_2375_, v___y_2376_, v___y_2377_, v___y_2378_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
return v___x_2483_;
}
}
}
else
{
lean_object* v_a_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2491_; 
lean_dec(v_snd_2442_);
lean_dec(v_fst_2441_);
lean_dec(v_a_2381_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v_fvarSubst_2374_);
lean_dec(v_snd_2372_);
lean_dec(v_fst_2371_);
v_a_2484_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2491_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2491_ == 0)
{
v___x_2486_ = v___x_2443_;
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_a_2484_);
lean_dec(v___x_2443_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2491_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v___x_2489_; 
if (v_isShared_2487_ == 0)
{
v___x_2489_ = v___x_2486_;
goto v_reusejp_2488_;
}
else
{
lean_object* v_reuseFailAlloc_2490_; 
v_reuseFailAlloc_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2490_, 0, v_a_2484_);
v___x_2489_ = v_reuseFailAlloc_2490_;
goto v_reusejp_2488_;
}
v_reusejp_2488_:
{
return v___x_2489_;
}
}
}
}
else
{
lean_dec(v_a_2438_);
lean_dec(v_fvarSubst_2374_);
lean_dec(v_fst_2371_);
v___y_2383_ = v___y_2375_;
v___y_2384_ = v___y_2376_;
v___y_2385_ = v___y_2377_;
v___y_2386_ = v___y_2378_;
goto v___jp_2382_;
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_a_2381_);
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v_fvarSubst_2374_);
lean_dec(v_snd_2372_);
lean_dec(v_fst_2371_);
v_a_2492_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2437_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2437_);
v___x_2494_ = lean_box(0);
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
v_resetjp_2493_:
{
lean_object* v___x_2497_; 
if (v_isShared_2495_ == 0)
{
v___x_2497_ = v___x_2494_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_a_2492_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
v___jp_2382_:
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2387_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2388_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2389_ = l_Lean_LocalDecl_type(v_a_2381_);
lean_dec(v_a_2381_);
v___x_2390_ = l_Lean_indentExpr(v___x_2389_);
v___x_2391_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2391_, 0, v___x_2388_);
lean_ctor_set(v___x_2391_, 1, v___x_2390_);
v___x_2392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2392_, 0, v___x_2391_);
v___x_2393_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2387_, v_snd_2372_, v___x_2392_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v___x_2393_;
}
v___jp_2394_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2401_ = l_Lean_LocalDecl_userName(v_a_2381_);
lean_dec(v_a_2381_);
lean_inc(v_fst_2371_);
v___x_2402_ = l_Lean_mkFVar(v_fst_2371_);
v___x_2403_ = l_Lean_MVarId_assert(v_snd_2372_, v___x_2401_, v_newType_2395_, v___x_2402_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2405_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = l_Lean_Meta_intro1Core(v_a_2404_, v___x_2373_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v_fst_2407_; lean_object* v_snd_2408_; lean_object* v___x_2409_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v_fst_2407_ = lean_ctor_get(v_a_2406_, 0);
lean_inc(v_fst_2407_);
v_snd_2408_ = lean_ctor_get(v_a_2406_, 1);
lean_inc(v_snd_2408_);
lean_dec(v_a_2406_);
v___x_2409_ = l_Lean_MVarId_clear(v_snd_2408_, v_fst_2371_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
if (lean_obj_tag(v___x_2409_) == 0)
{
lean_object* v_a_2410_; lean_object* v___x_2411_; 
v_a_2410_ = lean_ctor_get(v___x_2409_, 0);
lean_inc(v_a_2410_);
lean_dec_ref_known(v___x_2409_, 1);
v___x_2411_ = l_Lean_Meta_substCore(v_a_2410_, v_fst_2407_, v_symm_2396_, v_fvarSubst_2374_, v___x_2373_, v___x_2373_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v___x_2411_;
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_dec(v_fst_2407_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v_fvarSubst_2374_);
v_a_2412_ = lean_ctor_get(v___x_2409_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2409_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2409_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2409_);
v___x_2414_ = lean_box(0);
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
v_resetjp_2413_:
{
lean_object* v___x_2417_; 
if (v_isShared_2415_ == 0)
{
v___x_2417_ = v___x_2414_;
goto v_reusejp_2416_;
}
else
{
lean_object* v_reuseFailAlloc_2418_; 
v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2418_, 0, v_a_2412_);
v___x_2417_ = v_reuseFailAlloc_2418_;
goto v_reusejp_2416_;
}
v_reusejp_2416_:
{
return v___x_2417_;
}
}
}
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v_fvarSubst_2374_);
lean_dec(v_fst_2371_);
v_a_2420_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2405_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2405_);
v___x_2422_ = lean_box(0);
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
v_resetjp_2421_:
{
lean_object* v___x_2425_; 
if (v_isShared_2423_ == 0)
{
v___x_2425_ = v___x_2422_;
goto v_reusejp_2424_;
}
else
{
lean_object* v_reuseFailAlloc_2426_; 
v_reuseFailAlloc_2426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_a_2420_);
v___x_2425_ = v_reuseFailAlloc_2426_;
goto v_reusejp_2424_;
}
v_reusejp_2424_:
{
return v___x_2425_;
}
}
}
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v_fvarSubst_2374_);
lean_dec(v_fst_2371_);
v_a_2428_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2403_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2403_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v___x_2433_; 
if (v_isShared_2431_ == 0)
{
v___x_2433_ = v___x_2430_;
goto v_reusejp_2432_;
}
else
{
lean_object* v_reuseFailAlloc_2434_; 
v_reuseFailAlloc_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2434_, 0, v_a_2428_);
v___x_2433_ = v_reuseFailAlloc_2434_;
goto v_reusejp_2432_;
}
v_reusejp_2432_:
{
return v___x_2433_;
}
}
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v___y_2378_);
lean_dec_ref(v___y_2377_);
lean_dec(v___y_2376_);
lean_dec_ref(v___y_2375_);
lean_dec(v_fvarSubst_2374_);
lean_dec(v_snd_2372_);
lean_dec(v_fst_2371_);
v_a_2500_ = lean_ctor_get(v___x_2380_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2380_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2380_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2380_);
v___x_2502_ = lean_box(0);
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
v_resetjp_2501_:
{
lean_object* v___x_2505_; 
if (v_isShared_2503_ == 0)
{
v___x_2505_ = v___x_2502_;
goto v_reusejp_2504_;
}
else
{
lean_object* v_reuseFailAlloc_2506_; 
v_reuseFailAlloc_2506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2506_, 0, v_a_2500_);
v___x_2505_ = v_reuseFailAlloc_2506_;
goto v_reusejp_2504_;
}
v_reusejp_2504_:
{
return v___x_2505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2508_, lean_object* v_snd_2509_, lean_object* v___x_2510_, lean_object* v_fvarSubst_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_){
_start:
{
uint8_t v___x_1437__boxed_2517_; lean_object* v_res_2518_; 
v___x_1437__boxed_2517_ = lean_unbox(v___x_2510_);
v_res_2518_ = l_Lean_Meta_substEq___lam__0(v_fst_2508_, v_snd_2509_, v___x_1437__boxed_2517_, v_fvarSubst_2511_, v___y_2512_, v___y_2513_, v___y_2514_, v___y_2515_);
return v_res_2518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2519_, lean_object* v_hFVarId_2520_, lean_object* v_fvarSubst_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
uint8_t v___x_2527_; lean_object* v___x_2528_; 
v___x_2527_ = 1;
v___x_2528_ = l_Lean_Meta_heqToEq(v_mvarId_2519_, v_hFVarId_2520_, v___x_2527_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v_fst_2530_; lean_object* v_snd_2531_; lean_object* v___x_2532_; lean_object* v___f_2533_; lean_object* v___x_2534_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v_fst_2530_ = lean_ctor_get(v_a_2529_, 0);
lean_inc(v_fst_2530_);
v_snd_2531_ = lean_ctor_get(v_a_2529_, 1);
lean_inc_n(v_snd_2531_, 2);
lean_dec(v_a_2529_);
v___x_2532_ = lean_box(v___x_2527_);
v___f_2533_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2533_, 0, v_fst_2530_);
lean_closure_set(v___f_2533_, 1, v_snd_2531_);
lean_closure_set(v___f_2533_, 2, v___x_2532_);
lean_closure_set(v___f_2533_, 3, v_fvarSubst_2521_);
v___x_2534_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_snd_2531_, v___f_2533_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
return v___x_2534_;
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_fvarSubst_2521_);
v_a_2535_ = lean_ctor_get(v___x_2528_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2528_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2528_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2528_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2543_, lean_object* v_hFVarId_2544_, lean_object* v_fvarSubst_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lean_Meta_substEq(v_mvarId_2543_, v_hFVarId_2544_, v_fvarSubst_2545_, v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2552_, lean_object* v_mvarId_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_, lean_object* v___y_2557_){
_start:
{
lean_object* v___x_2559_; 
lean_inc(v_h_2552_);
v___x_2559_ = l_Lean_FVarId_getType___redArg(v_h_2552_, v___y_2554_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v_a_2560_; lean_object* v___x_2561_; 
v_a_2560_ = lean_ctor_get(v___x_2559_, 0);
lean_inc_n(v_a_2560_, 2);
lean_dec_ref_known(v___x_2559_, 1);
v___x_2561_ = l_Lean_Meta_matchEq_x3f(v_a_2560_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2561_) == 0)
{
lean_object* v_a_2562_; 
v_a_2562_ = lean_ctor_get(v___x_2561_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v___x_2561_, 1);
if (lean_obj_tag(v_a_2562_) == 0)
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lean_Meta_matchHEq_x3f(v_a_2560_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2563_) == 0)
{
lean_object* v_a_2564_; 
v_a_2564_ = lean_ctor_get(v___x_2563_, 0);
lean_inc(v_a_2564_);
lean_dec_ref_known(v___x_2563_, 1);
if (lean_obj_tag(v_a_2564_) == 0)
{
lean_object* v___x_2565_; 
v___x_2565_ = l_Lean_Meta_substVar(v_mvarId_2553_, v_h_2552_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
return v___x_2565_;
}
else
{
uint8_t v___x_2566_; lean_object* v___x_2567_; 
lean_dec_ref_known(v_a_2564_, 1);
v___x_2566_ = 1;
lean_inc(v_h_2552_);
lean_inc(v_mvarId_2553_);
v___x_2567_ = l_Lean_Meta_heqToEq(v_mvarId_2553_, v_h_2552_, v___x_2566_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v_fst_2569_; lean_object* v_snd_2570_; uint8_t v___x_2571_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc(v_a_2568_);
lean_dec_ref_known(v___x_2567_, 1);
v_fst_2569_ = lean_ctor_get(v_a_2568_, 0);
lean_inc(v_fst_2569_);
v_snd_2570_ = lean_ctor_get(v_a_2568_, 1);
lean_inc(v_snd_2570_);
lean_dec(v_a_2568_);
v___x_2571_ = l_Lean_instBEqMVarId_beq(v_mvarId_2553_, v_snd_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; 
lean_dec(v_mvarId_2553_);
lean_dec(v_h_2552_);
v___x_2572_ = l_Lean_Meta_subst(v_snd_2570_, v_fst_2569_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
return v___x_2572_;
}
else
{
lean_object* v___x_2573_; 
lean_dec(v_snd_2570_);
lean_dec(v_fst_2569_);
v___x_2573_ = l_Lean_Meta_substVar(v_mvarId_2553_, v_h_2552_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
return v___x_2573_;
}
}
else
{
lean_object* v_a_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2581_; 
lean_dec(v_mvarId_2553_);
lean_dec(v_h_2552_);
v_a_2574_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2581_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2581_ == 0)
{
v___x_2576_ = v___x_2567_;
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_a_2574_);
lean_dec(v___x_2567_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2581_;
goto v_resetjp_2575_;
}
v_resetjp_2575_:
{
lean_object* v___x_2579_; 
if (v_isShared_2577_ == 0)
{
v___x_2579_ = v___x_2576_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2580_; 
v_reuseFailAlloc_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2580_, 0, v_a_2574_);
v___x_2579_ = v_reuseFailAlloc_2580_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
return v___x_2579_;
}
}
}
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec(v_mvarId_2553_);
lean_dec(v_h_2552_);
v_a_2582_ = lean_ctor_get(v___x_2563_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2563_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2563_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2563_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2587_; 
if (v_isShared_2585_ == 0)
{
v___x_2587_ = v___x_2584_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_a_2582_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
else
{
lean_object* v___x_2590_; lean_object* v___x_2591_; 
lean_dec_ref_known(v_a_2562_, 1);
lean_dec(v_a_2560_);
v___x_2590_ = lean_box(0);
v___x_2591_ = l_Lean_Meta_substEq(v_mvarId_2553_, v_h_2552_, v___x_2590_, v___y_2554_, v___y_2555_, v___y_2556_, v___y_2557_);
if (lean_obj_tag(v___x_2591_) == 0)
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2600_; 
v_a_2592_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2594_ = v___x_2591_;
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2591_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2600_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v_snd_2596_; lean_object* v___x_2598_; 
v_snd_2596_ = lean_ctor_get(v_a_2592_, 1);
lean_inc(v_snd_2596_);
lean_dec(v_a_2592_);
if (v_isShared_2595_ == 0)
{
lean_ctor_set(v___x_2594_, 0, v_snd_2596_);
v___x_2598_ = v___x_2594_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_snd_2596_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
else
{
lean_object* v_a_2601_; lean_object* v___x_2603_; uint8_t v_isShared_2604_; uint8_t v_isSharedCheck_2608_; 
v_a_2601_ = lean_ctor_get(v___x_2591_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2591_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2603_ = v___x_2591_;
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
else
{
lean_inc(v_a_2601_);
lean_dec(v___x_2591_);
v___x_2603_ = lean_box(0);
v_isShared_2604_ = v_isSharedCheck_2608_;
goto v_resetjp_2602_;
}
v_resetjp_2602_:
{
lean_object* v___x_2606_; 
if (v_isShared_2604_ == 0)
{
v___x_2606_ = v___x_2603_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_a_2601_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
lean_dec(v_a_2560_);
lean_dec(v_mvarId_2553_);
lean_dec(v_h_2552_);
v_a_2609_ = lean_ctor_get(v___x_2561_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2561_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2561_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2561_);
v___x_2611_ = lean_box(0);
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
v_resetjp_2610_:
{
lean_object* v___x_2614_; 
if (v_isShared_2612_ == 0)
{
v___x_2614_ = v___x_2611_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_a_2609_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v_mvarId_2553_);
lean_dec(v_h_2552_);
v_a_2617_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2559_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2559_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2622_; 
if (v_isShared_2620_ == 0)
{
v___x_2622_ = v___x_2619_;
goto v_reusejp_2621_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_a_2617_);
v___x_2622_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2621_;
}
v_reusejp_2621_:
{
return v___x_2622_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2625_, lean_object* v_mvarId_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l_Lean_Meta_subst___lam__0(v_h_2625_, v_mvarId_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2633_, lean_object* v_h_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v___f_2640_; lean_object* v___x_2641_; 
lean_inc(v_mvarId_2633_);
v___f_2640_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2640_, 0, v_h_2634_);
lean_closure_set(v___f_2640_, 1, v_mvarId_2633_);
v___x_2641_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2633_, v___f_2640_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
return v___x_2641_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2642_, lean_object* v_h_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v_res_2649_; 
v_res_2649_ = l_Lean_Meta_subst(v_mvarId_2642_, v_h_2643_, v_a_2644_, v_a_2645_, v_a_2646_, v_a_2647_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
lean_dec(v_a_2645_);
lean_dec_ref(v_a_2644_);
return v_res_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2650_, lean_object* v___y_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_){
_start:
{
lean_object* v___x_2656_; 
v___x_2656_ = l_Lean_Meta_saveState___redArg(v___y_2652_, v___y_2654_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v___x_2658_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2657_);
lean_dec_ref_known(v___x_2656_, 1);
lean_inc(v___y_2654_);
lean_inc_ref(v___y_2653_);
lean_inc(v___y_2652_);
lean_inc_ref(v___y_2651_);
v___x_2658_ = lean_apply_5(v_x_2650_, v___y_2651_, v___y_2652_, v___y_2653_, v___y_2654_, lean_box(0));
if (lean_obj_tag(v___x_2658_) == 0)
{
lean_dec(v_a_2657_);
return v___x_2658_;
}
else
{
lean_object* v_a_2659_; uint8_t v___y_2661_; uint8_t v___x_2679_; 
v_a_2659_ = lean_ctor_get(v___x_2658_, 0);
lean_inc(v_a_2659_);
v___x_2679_ = l_Lean_Exception_isInterrupt(v_a_2659_);
if (v___x_2679_ == 0)
{
uint8_t v___x_2680_; 
lean_inc(v_a_2659_);
v___x_2680_ = l_Lean_Exception_isRuntime(v_a_2659_);
v___y_2661_ = v___x_2680_;
goto v___jp_2660_;
}
else
{
v___y_2661_ = v___x_2679_;
goto v___jp_2660_;
}
v___jp_2660_:
{
if (v___y_2661_ == 0)
{
lean_object* v___x_2662_; 
lean_dec_ref_known(v___x_2658_, 1);
v___x_2662_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2657_, v___y_2652_, v___y_2654_);
lean_dec(v_a_2657_);
if (lean_obj_tag(v___x_2662_) == 0)
{
lean_object* v___x_2664_; uint8_t v_isShared_2665_; uint8_t v_isSharedCheck_2669_; 
v_isSharedCheck_2669_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; 
v_unused_2670_ = lean_ctor_get(v___x_2662_, 0);
lean_dec(v_unused_2670_);
v___x_2664_ = v___x_2662_;
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
else
{
lean_dec(v___x_2662_);
v___x_2664_ = lean_box(0);
v_isShared_2665_ = v_isSharedCheck_2669_;
goto v_resetjp_2663_;
}
v_resetjp_2663_:
{
lean_object* v___x_2667_; 
if (v_isShared_2665_ == 0)
{
lean_ctor_set_tag(v___x_2664_, 1);
lean_ctor_set(v___x_2664_, 0, v_a_2659_);
v___x_2667_ = v___x_2664_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2659_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec(v_a_2659_);
v_a_2671_ = lean_ctor_get(v___x_2662_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2662_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2662_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2662_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
else
{
lean_dec(v_a_2659_);
lean_dec(v_a_2657_);
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec_ref(v_x_2650_);
v_a_2681_ = lean_ctor_get(v___x_2656_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2656_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2656_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2656_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2686_; 
if (v_isShared_2684_ == 0)
{
v___x_2686_ = v___x_2683_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v_a_2681_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2689_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
lean_dec(v___y_2693_);
lean_dec_ref(v___y_2692_);
lean_dec(v___y_2691_);
lean_dec_ref(v___y_2690_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2696_, lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_){
_start:
{
lean_object* v___x_2703_; 
v___x_2703_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2704_, lean_object* v_x_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2704_, v_x_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_){
_start:
{
lean_object* v_ref_2718_; lean_object* v___x_2719_; lean_object* v_a_2720_; lean_object* v___x_2722_; uint8_t v_isShared_2723_; uint8_t v_isSharedCheck_2728_; 
v_ref_2718_ = lean_ctor_get(v___y_2715_, 2);
v___x_2719_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__2_spec__2(v_msg_2712_, v___y_2713_, v___y_2714_, v___y_2715_, v___y_2716_);
v_a_2720_ = lean_ctor_get(v___x_2719_, 0);
v_isSharedCheck_2728_ = !lean_is_exclusive(v___x_2719_);
if (v_isSharedCheck_2728_ == 0)
{
v___x_2722_ = v___x_2719_;
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
else
{
lean_inc(v_a_2720_);
lean_dec(v___x_2719_);
v___x_2722_ = lean_box(0);
v_isShared_2723_ = v_isSharedCheck_2728_;
goto v_resetjp_2721_;
}
v_resetjp_2721_:
{
lean_object* v___x_2724_; lean_object* v___x_2726_; 
lean_inc(v_ref_2718_);
v___x_2724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2724_, 0, v_ref_2718_);
lean_ctor_set(v___x_2724_, 1, v_a_2720_);
if (v_isShared_2723_ == 0)
{
lean_ctor_set_tag(v___x_2722_, 1);
lean_ctor_set(v___x_2722_, 0, v___x_2724_);
v___x_2726_ = v___x_2722_;
goto v_reusejp_2725_;
}
else
{
lean_object* v_reuseFailAlloc_2727_; 
v_reuseFailAlloc_2727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2724_);
v___x_2726_ = v_reuseFailAlloc_2727_;
goto v_reusejp_2725_;
}
v_reusejp_2725_:
{
return v___x_2726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_, lean_object* v___y_2733_, lean_object* v___y_2734_){
_start:
{
lean_object* v_res_2735_; 
v_res_2735_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
lean_dec(v___y_2733_);
lean_dec_ref(v___y_2732_);
lean_dec(v___y_2731_);
lean_dec_ref(v___y_2730_);
return v_res_2735_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2737_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2738_ = l_Lean_stringToMessageData(v___x_2737_);
return v___x_2738_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; 
v___x_2740_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2741_ = l_Lean_stringToMessageData(v___x_2740_);
return v___x_2741_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2743_; lean_object* v___x_2744_; 
v___x_2743_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2744_ = l_Lean_stringToMessageData(v___x_2743_);
return v___x_2744_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; 
v___x_2746_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2747_ = l_Lean_stringToMessageData(v___x_2746_);
return v___x_2747_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2750_ = l_Lean_stringToMessageData(v___x_2749_);
return v___x_2750_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2764_ = l_Lean_stringToMessageData(v___x_2763_);
return v___x_2764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2773_, uint8_t v_substLHS_2774_, lean_object* v___y_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_){
_start:
{
lean_object* v___x_2780_; 
lean_inc(v_mvarId_2773_);
v___x_2780_ = l_Lean_MVarId_getType_x27(v_mvarId_2773_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
if (lean_obj_tag(v_a_2781_) == 7)
{
lean_object* v_binderType_2785_; lean_object* v_body_2786_; uint8_t v___x_2787_; lean_object* v___y_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2795_; lean_object* v___y_2796_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v___y_2882_; lean_object* v_fst_2922_; lean_object* v_fst_2923_; lean_object* v_fst_2924_; lean_object* v_snd_2925_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; 
v_binderType_2785_ = lean_ctor_get(v_a_2781_, 1);
lean_inc_ref(v_binderType_2785_);
v_body_2786_ = lean_ctor_get(v_a_2781_, 2);
lean_inc_ref(v_body_2786_);
lean_dec_ref_known(v_a_2781_, 3);
v___x_2787_ = l_Lean_Expr_hasLooseBVars(v_body_2786_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2956_; 
v___x_2956_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2785_, v___y_2776_);
if (lean_obj_tag(v___x_2956_) == 0)
{
lean_object* v_a_2957_; lean_object* v___x_2958_; uint8_t v___x_2959_; 
v_a_2957_ = lean_ctor_get(v___x_2956_, 0);
lean_inc(v_a_2957_);
lean_dec_ref_known(v___x_2956_, 1);
v___x_2958_ = l_Lean_Expr_cleanupAnnotations(v_a_2957_);
v___x_2959_ = l_Lean_Expr_isApp(v___x_2958_);
if (v___x_2959_ == 0)
{
lean_dec_ref(v___x_2958_);
lean_dec_ref(v_body_2786_);
lean_dec(v_mvarId_2773_);
v___y_2942_ = v___y_2775_;
v___y_2943_ = v___y_2776_;
v___y_2944_ = v___y_2777_;
v___y_2945_ = v___y_2778_;
goto v___jp_2941_;
}
else
{
lean_object* v_arg_2960_; lean_object* v___x_2961_; uint8_t v___x_2962_; 
v_arg_2960_ = lean_ctor_get(v___x_2958_, 1);
lean_inc_ref(v_arg_2960_);
v___x_2961_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2958_);
v___x_2962_ = l_Lean_Expr_isApp(v___x_2961_);
if (v___x_2962_ == 0)
{
lean_dec_ref(v___x_2961_);
lean_dec_ref(v_arg_2960_);
lean_dec_ref(v_body_2786_);
lean_dec(v_mvarId_2773_);
v___y_2942_ = v___y_2775_;
v___y_2943_ = v___y_2776_;
v___y_2944_ = v___y_2777_;
v___y_2945_ = v___y_2778_;
goto v___jp_2941_;
}
else
{
lean_object* v_arg_2963_; lean_object* v___x_2964_; uint8_t v___x_2965_; 
v_arg_2963_ = lean_ctor_get(v___x_2961_, 1);
lean_inc_ref(v_arg_2963_);
v___x_2964_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2961_);
v___x_2965_ = l_Lean_Expr_isApp(v___x_2964_);
if (v___x_2965_ == 0)
{
lean_dec_ref(v___x_2964_);
lean_dec_ref(v_arg_2963_);
lean_dec_ref(v_arg_2960_);
lean_dec_ref(v_body_2786_);
lean_dec(v_mvarId_2773_);
v___y_2942_ = v___y_2775_;
v___y_2943_ = v___y_2776_;
v___y_2944_ = v___y_2777_;
v___y_2945_ = v___y_2778_;
goto v___jp_2941_;
}
else
{
lean_object* v_arg_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v_arg_2966_ = lean_ctor_get(v___x_2964_, 1);
lean_inc_ref(v_arg_2966_);
v___x_2967_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2964_);
v___x_2968_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_2969_ = l_Lean_Expr_isConstOf(v___x_2967_, v___x_2968_);
if (v___x_2969_ == 0)
{
uint8_t v___x_2970_; 
v___x_2970_ = l_Lean_Expr_isApp(v___x_2967_);
if (v___x_2970_ == 0)
{
lean_dec_ref(v___x_2967_);
lean_dec_ref(v_arg_2966_);
lean_dec_ref(v_arg_2963_);
lean_dec_ref(v_arg_2960_);
lean_dec_ref(v_body_2786_);
lean_dec(v_mvarId_2773_);
v___y_2942_ = v___y_2775_;
v___y_2943_ = v___y_2776_;
v___y_2944_ = v___y_2777_;
v___y_2945_ = v___y_2778_;
goto v___jp_2941_;
}
else
{
lean_object* v_arg_2971_; lean_object* v___y_2973_; lean_object* v___y_2974_; lean_object* v___y_2975_; lean_object* v___y_2976_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_arg_2971_ = lean_ctor_get(v___x_2967_, 1);
lean_inc_ref(v_arg_2971_);
v___x_2979_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2967_);
v___x_2980_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_2981_ = l_Lean_Expr_isConstOf(v___x_2979_, v___x_2980_);
lean_dec_ref(v___x_2979_);
if (v___x_2981_ == 0)
{
lean_dec_ref(v_arg_2971_);
lean_dec_ref(v_arg_2966_);
lean_dec_ref(v_arg_2963_);
lean_dec_ref(v_arg_2960_);
lean_dec_ref(v_body_2786_);
lean_dec(v_mvarId_2773_);
v___y_2942_ = v___y_2775_;
v___y_2943_ = v___y_2776_;
v___y_2944_ = v___y_2777_;
v___y_2945_ = v___y_2778_;
goto v___jp_2941_;
}
else
{
lean_object* v___x_2982_; 
lean_inc_ref(v_arg_2971_);
v___x_2982_ = l_Lean_Meta_isExprDefEq(v_arg_2971_, v_arg_2963_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; uint8_t v___x_2984_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = lean_unbox(v_a_2983_);
lean_dec(v_a_2983_);
if (v___x_2984_ == 0)
{
lean_object* v___x_2985_; lean_object* v___x_2986_; lean_object* v_a_2987_; lean_object* v___x_2989_; uint8_t v_isShared_2990_; uint8_t v_isSharedCheck_2994_; 
lean_dec_ref(v_arg_2971_);
lean_dec_ref(v_arg_2966_);
lean_dec_ref(v_arg_2960_);
lean_dec_ref(v_body_2786_);
lean_dec(v_mvarId_2773_);
v___x_2985_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_2986_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2985_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_2994_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_2994_ == 0)
{
v___x_2989_ = v___x_2986_;
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
else
{
lean_inc(v_a_2987_);
lean_dec(v___x_2986_);
v___x_2989_ = lean_box(0);
v_isShared_2990_ = v_isSharedCheck_2994_;
goto v_resetjp_2988_;
}
v_resetjp_2988_:
{
lean_object* v___x_2992_; 
if (v_isShared_2990_ == 0)
{
v___x_2992_ = v___x_2989_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2993_; 
v_reuseFailAlloc_2993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2993_, 0, v_a_2987_);
v___x_2992_ = v_reuseFailAlloc_2993_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
return v___x_2992_;
}
}
}
else
{
v___y_2973_ = v___y_2775_;
v___y_2974_ = v___y_2776_;
v___y_2975_ = v___y_2777_;
v___y_2976_ = v___y_2778_;
goto v___jp_2972_;
}
}
else
{
lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec_ref(v_arg_2971_);
lean_dec_ref(v_arg_2966_);
lean_dec_ref(v_arg_2960_);
lean_dec_ref(v_body_2786_);
lean_dec(v_mvarId_2773_);
v_a_2995_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2982_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2982_);
v___x_2997_ = lean_box(0);
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
v_resetjp_2996_:
{
lean_object* v___x_3000_; 
if (v_isShared_2998_ == 0)
{
v___x_3000_ = v___x_2997_;
goto v_reusejp_2999_;
}
else
{
lean_object* v_reuseFailAlloc_3001_; 
v_reuseFailAlloc_3001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3001_, 0, v_a_2995_);
v___x_3000_ = v_reuseFailAlloc_3001_;
goto v_reusejp_2999_;
}
v_reusejp_2999_:
{
return v___x_3000_;
}
}
}
}
v___jp_2972_:
{
if (v_substLHS_2774_ == 0)
{
lean_object* v___x_2977_; 
v___x_2977_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2922_ = v_arg_2971_;
v_fst_2923_ = v_arg_2966_;
v_fst_2924_ = v_arg_2960_;
v_snd_2925_ = v___x_2977_;
v___y_2926_ = v___y_2973_;
v___y_2927_ = v___y_2974_;
v___y_2928_ = v___y_2975_;
v___y_2929_ = v___y_2976_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_2978_; 
v___x_2978_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2922_ = v_arg_2971_;
v_fst_2923_ = v_arg_2960_;
v_fst_2924_ = v_arg_2966_;
v_snd_2925_ = v___x_2978_;
v___y_2926_ = v___y_2973_;
v___y_2927_ = v___y_2974_;
v___y_2928_ = v___y_2975_;
v___y_2929_ = v___y_2976_;
goto v___jp_2921_;
}
}
}
}
else
{
lean_dec_ref(v___x_2967_);
if (v_substLHS_2774_ == 0)
{
lean_object* v___x_3003_; 
v___x_3003_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2922_ = v_arg_2966_;
v_fst_2923_ = v_arg_2963_;
v_fst_2924_ = v_arg_2960_;
v_snd_2925_ = v___x_3003_;
v___y_2926_ = v___y_2775_;
v___y_2927_ = v___y_2776_;
v___y_2928_ = v___y_2777_;
v___y_2929_ = v___y_2778_;
goto v___jp_2921_;
}
else
{
lean_object* v___x_3004_; 
v___x_3004_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2922_ = v_arg_2966_;
v_fst_2923_ = v_arg_2960_;
v_fst_2924_ = v_arg_2963_;
v_snd_2925_ = v___x_3004_;
v___y_2926_ = v___y_2775_;
v___y_2927_ = v___y_2776_;
v___y_2928_ = v___y_2777_;
v___y_2929_ = v___y_2778_;
goto v___jp_2921_;
}
}
}
}
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref(v_body_2786_);
lean_dec(v_mvarId_2773_);
v_a_3005_ = lean_ctor_get(v___x_2956_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2956_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2956_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2956_);
v___x_3007_ = lean_box(0);
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
v_resetjp_3006_:
{
lean_object* v___x_3010_; 
if (v_isShared_3008_ == 0)
{
v___x_3010_ = v___x_3007_;
goto v_reusejp_3009_;
}
else
{
lean_object* v_reuseFailAlloc_3011_; 
v_reuseFailAlloc_3011_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3011_, 0, v_a_3005_);
v___x_3010_ = v_reuseFailAlloc_3011_;
goto v_reusejp_3009_;
}
v_reusejp_3009_:
{
return v___x_3010_;
}
}
}
}
else
{
lean_dec_ref(v_body_2786_);
lean_dec_ref(v_binderType_2785_);
lean_dec(v_mvarId_2773_);
goto v___jp_2782_;
}
v___jp_2788_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; uint8_t v___x_2802_; uint8_t v___x_2803_; lean_object* v___x_2804_; 
v___x_2800_ = lean_mk_empty_array_with_capacity(v___y_2790_);
lean_inc_ref(v___x_2800_);
v___x_2801_ = lean_array_push(v___x_2800_, v___y_2791_);
v___x_2802_ = 1;
v___x_2803_ = 1;
v___x_2804_ = l_Lean_Meta_mkLambdaFVars(v___x_2801_, v_body_2786_, v___x_2787_, v___x_2802_, v___x_2787_, v___x_2802_, v___x_2803_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
lean_dec_ref(v___x_2801_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc_n(v_a_2805_, 2);
lean_dec_ref_known(v___x_2804_, 1);
lean_inc_ref(v___y_2793_);
v___x_2806_ = lean_array_push(v___x_2800_, v___y_2793_);
v___x_2807_ = l_Lean_Expr_beta(v_a_2805_, v___x_2806_);
lean_inc(v___y_2792_);
v___x_2808_ = l_Lean_MVarId_getTag(v___y_2792_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
lean_inc_ref(v___x_2807_);
v___x_2810_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2807_, v_a_2809_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___x_2812_ = l_Lean_Meta_getLevel(v___x_2807_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
lean_inc_ref(v___y_2794_);
v___x_2814_ = l_Lean_Meta_getLevel(v___y_2794_, v___y_2796_, v___y_2797_, v___y_2798_, v___y_2799_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2823_; uint8_t v_isShared_2824_; uint8_t v_isSharedCheck_2832_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
v___x_2816_ = lean_box(0);
v___x_2817_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2817_, 0, v_a_2815_);
lean_ctor_set(v___x_2817_, 1, v___x_2816_);
v___x_2818_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2818_, 0, v_a_2813_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
lean_inc(v___y_2789_);
v___x_2819_ = l_Lean_mkConst(v___y_2789_, v___x_2818_);
lean_inc(v_a_2811_);
lean_inc_ref(v___y_2793_);
v___x_2820_ = l_Lean_mkApp4(v___x_2819_, v___y_2794_, v___y_2793_, v_a_2805_, v_a_2811_);
v___x_2821_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__4___redArg(v___y_2792_, v___x_2820_, v___y_2797_);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2832_ == 0)
{
lean_object* v_unused_2833_; 
v_unused_2833_ = lean_ctor_get(v___x_2821_, 0);
lean_dec(v_unused_2833_);
v___x_2823_ = v___x_2821_;
v_isShared_2824_ = v_isSharedCheck_2832_;
goto v_resetjp_2822_;
}
else
{
lean_dec(v___x_2821_);
v___x_2823_ = lean_box(0);
v_isShared_2824_ = v_isSharedCheck_2832_;
goto v_resetjp_2822_;
}
v_resetjp_2822_:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2830_; 
v___x_2825_ = l_Lean_Meta_FVarSubst_empty;
v___x_2826_ = l_Lean_Meta_FVarSubst_insert(v___x_2825_, v___y_2795_, v___y_2793_);
v___x_2827_ = l_Lean_Expr_mvarId_x21(v_a_2811_);
lean_dec(v_a_2811_);
v___x_2828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2828_, 0, v___x_2826_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
if (v_isShared_2824_ == 0)
{
lean_ctor_set(v___x_2823_, 0, v___x_2828_);
v___x_2830_ = v___x_2823_;
goto v_reusejp_2829_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2828_);
v___x_2830_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2829_;
}
v_reusejp_2829_:
{
return v___x_2830_;
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2813_);
lean_dec(v_a_2811_);
lean_dec(v_a_2805_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
v_a_2834_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2814_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2814_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v_a_2811_);
lean_dec(v_a_2805_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
v_a_2842_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2812_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2812_);
v___x_2844_ = lean_box(0);
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
v_resetjp_2843_:
{
lean_object* v___x_2847_; 
if (v_isShared_2845_ == 0)
{
v___x_2847_ = v___x_2844_;
goto v_reusejp_2846_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v_a_2842_);
v___x_2847_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2846_;
}
v_reusejp_2846_:
{
return v___x_2847_;
}
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v___x_2807_);
lean_dec(v_a_2805_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
v_a_2850_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2810_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2810_);
v___x_2852_ = lean_box(0);
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
v_resetjp_2851_:
{
lean_object* v___x_2855_; 
if (v_isShared_2853_ == 0)
{
v___x_2855_ = v___x_2852_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_a_2850_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec_ref(v___x_2807_);
lean_dec(v_a_2805_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
v_a_2858_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2808_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2808_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v___x_2800_);
lean_dec(v___y_2795_);
lean_dec_ref(v___y_2794_);
lean_dec_ref(v___y_2793_);
lean_dec(v___y_2792_);
v_a_2866_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2804_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2804_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v___x_2871_; 
if (v_isShared_2869_ == 0)
{
v___x_2871_ = v___x_2868_;
goto v_reusejp_2870_;
}
else
{
lean_object* v_reuseFailAlloc_2872_; 
v_reuseFailAlloc_2872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2872_, 0, v_a_2866_);
v___x_2871_ = v_reuseFailAlloc_2872_;
goto v_reusejp_2870_;
}
v_reusejp_2870_:
{
return v___x_2871_;
}
}
}
}
v___jp_2874_:
{
lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; 
v___x_2883_ = l_Lean_Expr_fvarId_x21(v___y_2876_);
v___x_2884_ = lean_unsigned_to_nat(1u);
v___x_2885_ = lean_mk_empty_array_with_capacity(v___x_2884_);
lean_inc(v___x_2883_);
v___x_2886_ = lean_array_push(v___x_2885_, v___x_2883_);
v___x_2887_ = l_Lean_MVarId_revert(v_mvarId_2773_, v___x_2886_, v___x_2787_, v___x_2787_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; lean_object* v_fst_2889_; lean_object* v_snd_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2912_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
v_fst_2889_ = lean_ctor_get(v_a_2888_, 0);
v_snd_2890_ = lean_ctor_get(v_a_2888_, 1);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_a_2888_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2892_ = v_a_2888_;
v_isShared_2893_ = v_isSharedCheck_2912_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_snd_2890_);
lean_inc(v_fst_2889_);
lean_dec(v_a_2888_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2912_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2894_; uint8_t v___x_2895_; 
v___x_2894_ = lean_array_get_size(v_fst_2889_);
lean_dec(v_fst_2889_);
v___x_2895_ = lean_nat_dec_eq(v___x_2894_, v___x_2884_);
if (v___x_2895_ == 0)
{
lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
lean_dec(v_snd_2890_);
lean_dec(v___x_2883_);
lean_dec_ref(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v_body_2786_);
v___x_2896_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2897_ = l_Lean_MessageData_ofExpr(v___y_2876_);
if (v_isShared_2893_ == 0)
{
lean_ctor_set_tag(v___x_2892_, 7);
lean_ctor_set(v___x_2892_, 1, v___x_2897_);
lean_ctor_set(v___x_2892_, 0, v___x_2896_);
v___x_2899_ = v___x_2892_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2911_, 1, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
v___x_2900_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
v___x_2902_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2901_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2882_);
v_a_2903_ = lean_ctor_get(v___x_2902_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2902_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2902_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2902_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___x_2908_; 
if (v_isShared_2906_ == 0)
{
v___x_2908_ = v___x_2905_;
goto v_reusejp_2907_;
}
else
{
lean_object* v_reuseFailAlloc_2909_; 
v_reuseFailAlloc_2909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2909_, 0, v_a_2903_);
v___x_2908_ = v_reuseFailAlloc_2909_;
goto v_reusejp_2907_;
}
v_reusejp_2907_:
{
return v___x_2908_;
}
}
}
}
else
{
lean_del_object(v___x_2892_);
v___y_2789_ = v___y_2875_;
v___y_2790_ = v___x_2884_;
v___y_2791_ = v___y_2876_;
v___y_2792_ = v_snd_2890_;
v___y_2793_ = v___y_2877_;
v___y_2794_ = v___y_2878_;
v___y_2795_ = v___x_2883_;
v___y_2796_ = v___y_2879_;
v___y_2797_ = v___y_2880_;
v___y_2798_ = v___y_2881_;
v___y_2799_ = v___y_2882_;
goto v___jp_2788_;
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec(v___x_2883_);
lean_dec_ref(v___y_2878_);
lean_dec_ref(v___y_2877_);
lean_dec_ref(v___y_2876_);
lean_dec_ref(v_body_2786_);
v_a_2913_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2887_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2887_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
}
v___jp_2921_:
{
uint8_t v___x_2930_; 
v___x_2930_ = l_Lean_Expr_isFVar(v_fst_2924_);
if (v___x_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v_a_2933_; lean_object* v___x_2935_; uint8_t v_isShared_2936_; uint8_t v_isSharedCheck_2940_; 
lean_dec_ref(v_fst_2924_);
lean_dec_ref(v_fst_2923_);
lean_dec_ref(v_fst_2922_);
lean_dec_ref(v_body_2786_);
lean_dec(v_mvarId_2773_);
v___x_2931_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2932_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2931_, v___y_2926_, v___y_2927_, v___y_2928_, v___y_2929_);
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2940_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2940_ == 0)
{
v___x_2935_ = v___x_2932_;
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
else
{
lean_inc(v_a_2933_);
lean_dec(v___x_2932_);
v___x_2935_ = lean_box(0);
v_isShared_2936_ = v_isSharedCheck_2940_;
goto v_resetjp_2934_;
}
v_resetjp_2934_:
{
lean_object* v___x_2938_; 
if (v_isShared_2936_ == 0)
{
v___x_2938_ = v___x_2935_;
goto v_reusejp_2937_;
}
else
{
lean_object* v_reuseFailAlloc_2939_; 
v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
v___x_2938_ = v_reuseFailAlloc_2939_;
goto v_reusejp_2937_;
}
v_reusejp_2937_:
{
return v___x_2938_;
}
}
}
else
{
v___y_2875_ = v_snd_2925_;
v___y_2876_ = v_fst_2924_;
v___y_2877_ = v_fst_2923_;
v___y_2878_ = v_fst_2922_;
v___y_2879_ = v___y_2926_;
v___y_2880_ = v___y_2927_;
v___y_2881_ = v___y_2928_;
v___y_2882_ = v___y_2929_;
goto v___jp_2874_;
}
}
v___jp_2941_:
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
v___x_2946_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_2947_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2946_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2947_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_dec(v___x_2947_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
else
{
lean_dec(v_a_2781_);
lean_dec(v_mvarId_2773_);
goto v___jp_2782_;
}
v___jp_2782_:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; 
v___x_2783_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2784_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2783_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
return v___x_2784_;
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec(v_mvarId_2773_);
v_a_3013_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2780_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2780_);
v___x_3015_ = lean_box(0);
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
v_resetjp_3014_:
{
lean_object* v___x_3018_; 
if (v_isShared_3016_ == 0)
{
v___x_3018_ = v___x_3015_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3019_; 
v_reuseFailAlloc_3019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3019_, 0, v_a_3013_);
v___x_3018_ = v_reuseFailAlloc_3019_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
return v___x_3018_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object* v_mvarId_3021_, lean_object* v_substLHS_3022_, lean_object* v___y_3023_, lean_object* v___y_3024_, lean_object* v___y_3025_, lean_object* v___y_3026_, lean_object* v___y_3027_){
_start:
{
uint8_t v_substLHS_boxed_3028_; lean_object* v_res_3029_; 
v_substLHS_boxed_3028_ = lean_unbox(v_substLHS_3022_);
v_res_3029_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_3021_, v_substLHS_boxed_3028_, v___y_3023_, v___y_3024_, v___y_3025_, v___y_3026_);
lean_dec(v___y_3026_);
lean_dec_ref(v___y_3025_);
lean_dec(v___y_3024_);
lean_dec_ref(v___y_3023_);
return v_res_3029_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3030_, lean_object* v_i_3031_, lean_object* v_k_3032_){
_start:
{
lean_object* v___x_3033_; uint8_t v___x_3034_; 
v___x_3033_ = lean_array_get_size(v_keys_3030_);
v___x_3034_ = lean_nat_dec_lt(v_i_3031_, v___x_3033_);
if (v___x_3034_ == 0)
{
lean_dec(v_i_3031_);
return v___x_3034_;
}
else
{
lean_object* v_k_x27_3035_; uint8_t v___x_3036_; 
v_k_x27_3035_ = lean_array_fget_borrowed(v_keys_3030_, v_i_3031_);
v___x_3036_ = l_Lean_instBEqMVarId_beq(v_k_3032_, v_k_x27_3035_);
if (v___x_3036_ == 0)
{
lean_object* v___x_3037_; lean_object* v___x_3038_; 
v___x_3037_ = lean_unsigned_to_nat(1u);
v___x_3038_ = lean_nat_add(v_i_3031_, v___x_3037_);
lean_dec(v_i_3031_);
v_i_3031_ = v___x_3038_;
goto _start;
}
else
{
lean_dec(v_i_3031_);
return v___x_3034_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3040_, lean_object* v_i_3041_, lean_object* v_k_3042_){
_start:
{
uint8_t v_res_3043_; lean_object* v_r_3044_; 
v_res_3043_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3040_, v_i_3041_, v_k_3042_);
lean_dec(v_k_3042_);
lean_dec_ref(v_keys_3040_);
v_r_3044_ = lean_box(v_res_3043_);
return v_r_3044_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3045_, size_t v_x_3046_, lean_object* v_x_3047_){
_start:
{
if (lean_obj_tag(v_x_3045_) == 0)
{
lean_object* v_es_3048_; lean_object* v___x_3049_; size_t v___x_3050_; size_t v___x_3051_; lean_object* v_j_3052_; lean_object* v___x_3053_; 
v_es_3048_ = lean_ctor_get(v_x_3045_, 0);
v___x_3049_ = lean_box(2);
v___x_3050_ = ((size_t)31ULL);
v___x_3051_ = lean_usize_land(v_x_3046_, v___x_3050_);
v_j_3052_ = lean_usize_to_nat(v___x_3051_);
v___x_3053_ = lean_array_get_borrowed(v___x_3049_, v_es_3048_, v_j_3052_);
lean_dec(v_j_3052_);
switch(lean_obj_tag(v___x_3053_))
{
case 0:
{
lean_object* v_key_3054_; uint8_t v___x_3055_; 
v_key_3054_ = lean_ctor_get(v___x_3053_, 0);
v___x_3055_ = l_Lean_instBEqMVarId_beq(v_x_3047_, v_key_3054_);
return v___x_3055_;
}
case 1:
{
lean_object* v_node_3056_; size_t v___x_3057_; size_t v___x_3058_; 
v_node_3056_ = lean_ctor_get(v___x_3053_, 0);
v___x_3057_ = ((size_t)5ULL);
v___x_3058_ = lean_usize_shift_right(v_x_3046_, v___x_3057_);
v_x_3045_ = v_node_3056_;
v_x_3046_ = v___x_3058_;
goto _start;
}
default: 
{
uint8_t v___x_3060_; 
v___x_3060_ = 0;
return v___x_3060_;
}
}
}
else
{
lean_object* v_ks_3061_; lean_object* v___x_3062_; uint8_t v___x_3063_; 
v_ks_3061_ = lean_ctor_get(v_x_3045_, 0);
v___x_3062_ = lean_unsigned_to_nat(0u);
v___x_3063_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3061_, v___x_3062_, v_x_3047_);
return v___x_3063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3064_, lean_object* v_x_3065_, lean_object* v_x_3066_){
_start:
{
size_t v_x_10615__boxed_3067_; uint8_t v_res_3068_; lean_object* v_r_3069_; 
v_x_10615__boxed_3067_ = lean_unbox_usize(v_x_3065_);
lean_dec(v_x_3065_);
v_res_3068_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3064_, v_x_10615__boxed_3067_, v_x_3066_);
lean_dec(v_x_3066_);
lean_dec_ref(v_x_3064_);
v_r_3069_ = lean_box(v_res_3068_);
return v_r_3069_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3070_, lean_object* v_x_3071_){
_start:
{
uint64_t v___x_3072_; size_t v___x_3073_; uint8_t v___x_3074_; 
v___x_3072_ = l_Lean_instHashableMVarId_hash(v_x_3071_);
v___x_3073_ = lean_uint64_to_usize(v___x_3072_);
v___x_3074_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3070_, v___x_3073_, v_x_3071_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3075_, lean_object* v_x_3076_){
_start:
{
uint8_t v_res_3077_; lean_object* v_r_3078_; 
v_res_3077_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3075_, v_x_3076_);
lean_dec(v_x_3076_);
lean_dec_ref(v_x_3075_);
v_r_3078_ = lean_box(v_res_3077_);
return v_r_3078_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3079_, lean_object* v___y_3080_){
_start:
{
lean_object* v___x_3082_; lean_object* v_mctx_3083_; lean_object* v_eAssignment_3084_; uint8_t v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
v___x_3082_ = lean_st_ref_get(v___y_3080_);
v_mctx_3083_ = lean_ctor_get(v___x_3082_, 0);
lean_inc_ref(v_mctx_3083_);
lean_dec(v___x_3082_);
v_eAssignment_3084_ = lean_ctor_get(v_mctx_3083_, 8);
lean_inc_ref(v_eAssignment_3084_);
lean_dec_ref(v_mctx_3083_);
v___x_3085_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3084_, v_mvarId_3079_);
lean_dec_ref(v_eAssignment_3084_);
v___x_3086_ = lean_box(v___x_3085_);
v___x_3087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
return v___x_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v_res_3091_; 
v_res_3091_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3088_, v___y_3089_);
lean_dec(v___y_3089_);
lean_dec(v_mvarId_3088_);
return v_res_3091_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3093_; lean_object* v___x_3094_; 
v___x_3093_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3094_ = l_Lean_stringToMessageData(v___x_3093_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3095_, uint8_t v___y_3096_, lean_object* v_____r_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3135_; lean_object* v_a_3136_; uint8_t v___x_3137_; 
v___x_3135_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3095_, v___y_3099_);
v_a_3136_ = lean_ctor_get(v___x_3135_, 0);
lean_inc(v_a_3136_);
lean_dec_ref(v___x_3135_);
v___x_3137_ = lean_unbox(v_a_3136_);
lean_dec(v_a_3136_);
if (v___x_3137_ == 0)
{
goto v___jp_3103_;
}
else
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v_a_3140_; lean_object* v___x_3142_; uint8_t v_isShared_3143_; uint8_t v_isSharedCheck_3147_; 
lean_dec(v_mvarId_3095_);
v___x_3138_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3139_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3138_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
v_isSharedCheck_3147_ = !lean_is_exclusive(v___x_3139_);
if (v_isSharedCheck_3147_ == 0)
{
v___x_3142_ = v___x_3139_;
v_isShared_3143_ = v_isSharedCheck_3147_;
goto v_resetjp_3141_;
}
else
{
lean_inc(v_a_3140_);
lean_dec(v___x_3139_);
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
v___jp_3103_:
{
lean_object* v___x_3104_; 
v___x_3104_ = l_Lean_Meta_intro1Core(v_mvarId_3095_, v___y_3096_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v_fst_3106_; lean_object* v_snd_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
v_fst_3106_ = lean_ctor_get(v_a_3105_, 0);
lean_inc(v_fst_3106_);
v_snd_3107_ = lean_ctor_get(v_a_3105_, 1);
lean_inc(v_snd_3107_);
lean_dec(v_a_3105_);
v___x_3108_ = lean_box(0);
v___x_3109_ = l_Lean_Meta_substEq(v_snd_3107_, v_fst_3106_, v___x_3108_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3109_) == 0)
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3118_; 
v_a_3110_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3112_ = v___x_3109_;
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3109_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3118_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3114_; lean_object* v___x_3116_; 
v___x_3114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3114_, 0, v_a_3110_);
if (v_isShared_3113_ == 0)
{
lean_ctor_set(v___x_3112_, 0, v___x_3114_);
v___x_3116_ = v___x_3112_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v___x_3114_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
v_a_3119_ = lean_ctor_get(v___x_3109_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3109_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3109_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3109_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
v_a_3127_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3104_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3104_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3148_, lean_object* v___y_3149_, lean_object* v_____r_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_, lean_object* v___y_3155_){
_start:
{
uint8_t v___y_10687__boxed_3156_; lean_object* v_res_3157_; 
v___y_10687__boxed_3156_ = lean_unbox(v___y_3149_);
v_res_3157_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3148_, v___y_10687__boxed_3156_, v_____r_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
lean_dec(v___y_3154_);
lean_dec_ref(v___y_3153_);
lean_dec(v___y_3152_);
lean_dec_ref(v___y_3151_);
return v_res_3157_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__2(void){
_start:
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3161_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3162_ = ((lean_object*)(l_Lean_Meta_substCore___lam__1___closed__1));
v___x_3163_ = l_Lean_Name_append(v___x_3162_, v___x_3161_);
return v___x_3163_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__4(void){
_start:
{
lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3165_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__3));
v___x_3166_ = l_Lean_stringToMessageData(v___x_3165_);
return v___x_3166_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__6(void){
_start:
{
lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3168_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__5));
v___x_3169_ = l_Lean_stringToMessageData(v___x_3168_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3170_, uint8_t v_substLHS_3171_, lean_object* v_a_3172_, lean_object* v_a_3173_, lean_object* v_a_3174_, lean_object* v_a_3175_){
_start:
{
lean_object* v___y_3178_; lean_object* v___y_3197_; lean_object* v___x_3200_; lean_object* v___f_3201_; lean_object* v___x_3202_; lean_object* v___x_3203_; 
v___x_3200_ = lean_box(v_substLHS_3171_);
lean_inc_n(v_mvarId_3170_, 2);
v___f_3201_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3201_, 0, v_mvarId_3170_);
lean_closure_set(v___f_3201_, 1, v___x_3200_);
v___x_3202_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
v___x_3203_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3170_, v___x_3202_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
if (lean_obj_tag(v___x_3203_) == 0)
{
lean_object* v___x_3204_; lean_object* v___x_3205_; 
lean_dec_ref_known(v___x_3203_, 1);
lean_inc(v_mvarId_3170_);
v___x_3204_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed), 8, 3);
lean_closure_set(v___x_3204_, 0, lean_box(0));
lean_closure_set(v___x_3204_, 1, v_mvarId_3170_);
lean_closure_set(v___x_3204_, 2, v___f_3201_);
v___x_3205_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3204_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
if (lean_obj_tag(v___x_3205_) == 0)
{
lean_dec(v_mvarId_3170_);
return v___x_3205_;
}
else
{
lean_object* v_a_3206_; uint8_t v___y_3208_; uint8_t v___x_3243_; 
v_a_3206_ = lean_ctor_get(v___x_3205_, 0);
lean_inc(v_a_3206_);
v___x_3243_ = l_Lean_Exception_isInterrupt(v_a_3206_);
if (v___x_3243_ == 0)
{
uint8_t v___x_3244_; 
lean_inc(v_a_3206_);
v___x_3244_ = l_Lean_Exception_isRuntime(v_a_3206_);
v___y_3208_ = v___x_3244_;
goto v___jp_3207_;
}
else
{
v___y_3208_ = v___x_3243_;
goto v___jp_3207_;
}
v___jp_3207_:
{
if (v___y_3208_ == 0)
{
lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3241_; 
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3205_);
if (v_isSharedCheck_3241_ == 0)
{
lean_object* v_unused_3242_; 
v_unused_3242_ = lean_ctor_get(v___x_3205_, 0);
lean_dec(v_unused_3242_);
v___x_3210_ = v___x_3205_;
v_isShared_3211_ = v_isSharedCheck_3241_;
goto v_resetjp_3209_;
}
else
{
lean_dec(v___x_3205_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3241_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v_toCold_3212_; lean_object* v_options_3213_; lean_object* v_inheritedTraceOptions_3214_; uint8_t v_hasTrace_3215_; lean_object* v___x_3216_; lean_object* v___f_3217_; 
v_toCold_3212_ = lean_ctor_get(v_a_3174_, 0);
v_options_3213_ = lean_ctor_get(v_toCold_3212_, 2);
v_inheritedTraceOptions_3214_ = lean_ctor_get(v_toCold_3212_, 11);
v_hasTrace_3215_ = lean_ctor_get_uint8(v_options_3213_, sizeof(void*)*1);
v___x_3216_ = lean_box(v___y_3208_);
lean_inc(v_mvarId_3170_);
v___f_3217_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3217_, 0, v_mvarId_3170_);
lean_closure_set(v___f_3217_, 1, v___x_3216_);
if (v_hasTrace_3215_ == 0)
{
lean_del_object(v___x_3210_);
lean_dec(v_a_3206_);
lean_dec(v_mvarId_3170_);
v___y_3197_ = v___f_3217_;
goto v___jp_3196_;
}
else
{
lean_object* v___x_3218_; lean_object* v___x_3219_; uint8_t v___x_3220_; 
v___x_3218_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3219_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__2, &l_Lean_Meta_introSubstEq___closed__2_once, _init_l_Lean_Meta_introSubstEq___closed__2);
v___x_3220_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3214_, v_options_3213_, v___x_3219_);
if (v___x_3220_ == 0)
{
lean_del_object(v___x_3210_);
lean_dec(v_a_3206_);
lean_dec(v_mvarId_3170_);
v___y_3197_ = v___f_3217_;
goto v___jp_3196_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3227_; 
lean_dec_ref(v___f_3217_);
v___x_3221_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__4, &l_Lean_Meta_introSubstEq___closed__4_once, _init_l_Lean_Meta_introSubstEq___closed__4);
v___x_3222_ = l_Lean_Exception_toMessageData(v_a_3206_);
v___x_3223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3221_);
lean_ctor_set(v___x_3223_, 1, v___x_3222_);
v___x_3224_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__6, &l_Lean_Meta_introSubstEq___closed__6_once, _init_l_Lean_Meta_introSubstEq___closed__6);
v___x_3225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3223_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
lean_inc(v_mvarId_3170_);
if (v_isShared_3211_ == 0)
{
lean_ctor_set(v___x_3210_, 0, v_mvarId_3170_);
v___x_3227_ = v___x_3210_;
goto v_reusejp_3226_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_mvarId_3170_);
v___x_3227_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3226_;
}
v_reusejp_3226_:
{
lean_object* v___x_3228_; lean_object* v___x_3229_; 
v___x_3228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3225_);
lean_ctor_set(v___x_3228_, 1, v___x_3227_);
v___x_3229_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__2(v___x_3218_, v___x_3228_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
if (lean_obj_tag(v___x_3229_) == 0)
{
lean_object* v_a_3230_; lean_object* v___x_3231_; 
v_a_3230_ = lean_ctor_get(v___x_3229_, 0);
lean_inc(v_a_3230_);
lean_dec_ref_known(v___x_3229_, 1);
v___x_3231_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3170_, v___y_3208_, v_a_3230_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_);
v___y_3178_ = v___x_3231_;
goto v___jp_3177_;
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_dec(v_mvarId_3170_);
v_a_3232_ = lean_ctor_get(v___x_3229_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3229_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3229_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3229_);
v___x_3234_ = lean_box(0);
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
v_resetjp_3233_:
{
lean_object* v___x_3237_; 
if (v_isShared_3235_ == 0)
{
v___x_3237_ = v___x_3234_;
goto v_reusejp_3236_;
}
else
{
lean_object* v_reuseFailAlloc_3238_; 
v_reuseFailAlloc_3238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3238_, 0, v_a_3232_);
v___x_3237_ = v_reuseFailAlloc_3238_;
goto v_reusejp_3236_;
}
v_reusejp_3236_:
{
return v___x_3237_;
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
lean_dec(v_a_3206_);
lean_dec(v_mvarId_3170_);
return v___x_3205_;
}
}
}
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec_ref(v___f_3201_);
lean_dec(v_mvarId_3170_);
v_a_3245_ = lean_ctor_get(v___x_3203_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3203_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3203_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3203_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3250_; 
if (v_isShared_3248_ == 0)
{
v___x_3250_ = v___x_3247_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_a_3245_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
v___jp_3177_:
{
if (lean_obj_tag(v___y_3178_) == 0)
{
lean_object* v_a_3179_; lean_object* v___x_3181_; uint8_t v_isShared_3182_; uint8_t v_isSharedCheck_3187_; 
v_a_3179_ = lean_ctor_get(v___y_3178_, 0);
v_isSharedCheck_3187_ = !lean_is_exclusive(v___y_3178_);
if (v_isSharedCheck_3187_ == 0)
{
v___x_3181_ = v___y_3178_;
v_isShared_3182_ = v_isSharedCheck_3187_;
goto v_resetjp_3180_;
}
else
{
lean_inc(v_a_3179_);
lean_dec(v___y_3178_);
v___x_3181_ = lean_box(0);
v_isShared_3182_ = v_isSharedCheck_3187_;
goto v_resetjp_3180_;
}
v_resetjp_3180_:
{
lean_object* v_a_3183_; lean_object* v___x_3185_; 
v_a_3183_ = lean_ctor_get(v_a_3179_, 0);
lean_inc(v_a_3183_);
lean_dec(v_a_3179_);
if (v_isShared_3182_ == 0)
{
lean_ctor_set(v___x_3181_, 0, v_a_3183_);
v___x_3185_ = v___x_3181_;
goto v_reusejp_3184_;
}
else
{
lean_object* v_reuseFailAlloc_3186_; 
v_reuseFailAlloc_3186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3186_, 0, v_a_3183_);
v___x_3185_ = v_reuseFailAlloc_3186_;
goto v_reusejp_3184_;
}
v_reusejp_3184_:
{
return v___x_3185_;
}
}
}
else
{
lean_object* v_a_3188_; lean_object* v___x_3190_; uint8_t v_isShared_3191_; uint8_t v_isSharedCheck_3195_; 
v_a_3188_ = lean_ctor_get(v___y_3178_, 0);
v_isSharedCheck_3195_ = !lean_is_exclusive(v___y_3178_);
if (v_isSharedCheck_3195_ == 0)
{
v___x_3190_ = v___y_3178_;
v_isShared_3191_ = v_isSharedCheck_3195_;
goto v_resetjp_3189_;
}
else
{
lean_inc(v_a_3188_);
lean_dec(v___y_3178_);
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
v___jp_3196_:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = lean_box(0);
lean_inc(v_a_3175_);
lean_inc_ref(v_a_3174_);
lean_inc(v_a_3173_);
lean_inc_ref(v_a_3172_);
v___x_3199_ = lean_apply_6(v___y_3197_, v___x_3198_, v_a_3172_, v_a_3173_, v_a_3174_, v_a_3175_, lean_box(0));
v___y_3178_ = v___x_3199_;
goto v___jp_3177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object* v_mvarId_3253_, lean_object* v_substLHS_3254_, lean_object* v_a_3255_, lean_object* v_a_3256_, lean_object* v_a_3257_, lean_object* v_a_3258_, lean_object* v_a_3259_){
_start:
{
uint8_t v_substLHS_boxed_3260_; lean_object* v_res_3261_; 
v_substLHS_boxed_3260_ = lean_unbox(v_substLHS_3254_);
v_res_3261_ = l_Lean_Meta_introSubstEq(v_mvarId_3253_, v_substLHS_boxed_3260_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
lean_dec(v_a_3258_);
lean_dec_ref(v_a_3257_);
lean_dec(v_a_3256_);
lean_dec_ref(v_a_3255_);
return v_res_3261_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object* v_00_u03b1_3262_, lean_object* v_msg_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_3263_, v___y_3264_, v___y_3265_, v___y_3266_, v___y_3267_);
return v___x_3269_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object* v_00_u03b1_3270_, lean_object* v_msg_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_){
_start:
{
lean_object* v_res_3277_; 
v_res_3277_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(v_00_u03b1_3270_, v_msg_3271_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_);
lean_dec(v___y_3275_);
lean_dec_ref(v___y_3274_);
lean_dec(v___y_3273_);
lean_dec_ref(v___y_3272_);
return v_res_3277_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object* v_mvarId_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3278_, v___y_3280_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object* v_mvarId_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_){
_start:
{
lean_object* v_res_3291_; 
v_res_3291_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3285_, v___y_3286_, v___y_3287_, v___y_3288_, v___y_3289_);
lean_dec(v___y_3289_);
lean_dec_ref(v___y_3288_);
lean_dec(v___y_3287_);
lean_dec_ref(v___y_3286_);
lean_dec(v_mvarId_3285_);
return v_res_3291_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object* v_00_u03b2_3292_, lean_object* v_x_3293_, lean_object* v_x_3294_){
_start:
{
uint8_t v___x_3295_; 
v___x_3295_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3293_, v_x_3294_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3296_, lean_object* v_x_3297_, lean_object* v_x_3298_){
_start:
{
uint8_t v_res_3299_; lean_object* v_r_3300_; 
v_res_3299_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(v_00_u03b2_3296_, v_x_3297_, v_x_3298_);
lean_dec(v_x_3298_);
lean_dec_ref(v_x_3297_);
v_r_3300_ = lean_box(v_res_3299_);
return v_r_3300_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_3301_, lean_object* v_x_3302_, size_t v_x_3303_, lean_object* v_x_3304_){
_start:
{
uint8_t v___x_3305_; 
v___x_3305_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3302_, v_x_3303_, v_x_3304_);
return v___x_3305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3306_, lean_object* v_x_3307_, lean_object* v_x_3308_, lean_object* v_x_3309_){
_start:
{
size_t v_x_11043__boxed_3310_; uint8_t v_res_3311_; lean_object* v_r_3312_; 
v_x_11043__boxed_3310_ = lean_unbox_usize(v_x_3308_);
lean_dec(v_x_3308_);
v_res_3311_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3306_, v_x_3307_, v_x_11043__boxed_3310_, v_x_3309_);
lean_dec(v_x_3309_);
lean_dec_ref(v_x_3307_);
v_r_3312_ = lean_box(v_res_3311_);
return v_r_3312_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3313_, lean_object* v_keys_3314_, lean_object* v_vals_3315_, lean_object* v_heq_3316_, lean_object* v_i_3317_, lean_object* v_k_3318_){
_start:
{
uint8_t v___x_3319_; 
v___x_3319_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3314_, v_i_3317_, v_k_3318_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3320_, lean_object* v_keys_3321_, lean_object* v_vals_3322_, lean_object* v_heq_3323_, lean_object* v_i_3324_, lean_object* v_k_3325_){
_start:
{
uint8_t v_res_3326_; lean_object* v_r_3327_; 
v_res_3326_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(v_00_u03b2_3320_, v_keys_3321_, v_vals_3322_, v_heq_3323_, v_i_3324_, v_k_3325_);
lean_dec(v_k_3325_);
lean_dec_ref(v_vals_3322_);
lean_dec_ref(v_keys_3321_);
v_r_3327_ = lean_box(v_res_3326_);
return v_r_3327_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* v_x_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_, lean_object* v___y_3331_, lean_object* v___y_3332_){
_start:
{
lean_object* v___x_3334_; 
v___x_3334_ = l_Lean_Meta_saveState___redArg(v___y_3330_, v___y_3332_);
if (lean_obj_tag(v___x_3334_) == 0)
{
lean_object* v_a_3335_; lean_object* v___x_3336_; 
v_a_3335_ = lean_ctor_get(v___x_3334_, 0);
lean_inc(v_a_3335_);
lean_dec_ref_known(v___x_3334_, 1);
lean_inc(v___y_3332_);
lean_inc_ref(v___y_3331_);
lean_inc(v___y_3330_);
lean_inc_ref(v___y_3329_);
v___x_3336_ = lean_apply_5(v_x_3328_, v___y_3329_, v___y_3330_, v___y_3331_, v___y_3332_, lean_box(0));
if (lean_obj_tag(v___x_3336_) == 0)
{
lean_object* v_a_3337_; lean_object* v___x_3339_; uint8_t v_isShared_3340_; uint8_t v_isSharedCheck_3345_; 
lean_dec(v_a_3335_);
v_a_3337_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3345_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3345_ == 0)
{
v___x_3339_ = v___x_3336_;
v_isShared_3340_ = v_isSharedCheck_3345_;
goto v_resetjp_3338_;
}
else
{
lean_inc(v_a_3337_);
lean_dec(v___x_3336_);
v___x_3339_ = lean_box(0);
v_isShared_3340_ = v_isSharedCheck_3345_;
goto v_resetjp_3338_;
}
v_resetjp_3338_:
{
lean_object* v___x_3341_; lean_object* v___x_3343_; 
v___x_3341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3341_, 0, v_a_3337_);
if (v_isShared_3340_ == 0)
{
lean_ctor_set(v___x_3339_, 0, v___x_3341_);
v___x_3343_ = v___x_3339_;
goto v_reusejp_3342_;
}
else
{
lean_object* v_reuseFailAlloc_3344_; 
v_reuseFailAlloc_3344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3344_, 0, v___x_3341_);
v___x_3343_ = v_reuseFailAlloc_3344_;
goto v_reusejp_3342_;
}
v_reusejp_3342_:
{
return v___x_3343_;
}
}
}
else
{
lean_object* v_a_3346_; lean_object* v___x_3348_; uint8_t v_isShared_3349_; uint8_t v_isSharedCheck_3375_; 
v_a_3346_ = lean_ctor_get(v___x_3336_, 0);
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3336_);
if (v_isSharedCheck_3375_ == 0)
{
v___x_3348_ = v___x_3336_;
v_isShared_3349_ = v_isSharedCheck_3375_;
goto v_resetjp_3347_;
}
else
{
lean_inc(v_a_3346_);
lean_dec(v___x_3336_);
v___x_3348_ = lean_box(0);
v_isShared_3349_ = v_isSharedCheck_3375_;
goto v_resetjp_3347_;
}
v_resetjp_3347_:
{
uint8_t v___y_3351_; uint8_t v___x_3373_; 
v___x_3373_ = l_Lean_Exception_isInterrupt(v_a_3346_);
if (v___x_3373_ == 0)
{
uint8_t v___x_3374_; 
lean_inc(v_a_3346_);
v___x_3374_ = l_Lean_Exception_isRuntime(v_a_3346_);
v___y_3351_ = v___x_3374_;
goto v___jp_3350_;
}
else
{
v___y_3351_ = v___x_3373_;
goto v___jp_3350_;
}
v___jp_3350_:
{
if (v___y_3351_ == 0)
{
lean_object* v___x_3352_; 
lean_del_object(v___x_3348_);
lean_dec(v_a_3346_);
v___x_3352_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3335_, v___y_3330_, v___y_3332_);
lean_dec(v_a_3335_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3360_; 
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3360_ == 0)
{
lean_object* v_unused_3361_; 
v_unused_3361_ = lean_ctor_get(v___x_3352_, 0);
lean_dec(v_unused_3361_);
v___x_3354_ = v___x_3352_;
v_isShared_3355_ = v_isSharedCheck_3360_;
goto v_resetjp_3353_;
}
else
{
lean_dec(v___x_3352_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3360_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3356_ = lean_box(0);
if (v_isShared_3355_ == 0)
{
lean_ctor_set(v___x_3354_, 0, v___x_3356_);
v___x_3358_ = v___x_3354_;
goto v_reusejp_3357_;
}
else
{
lean_object* v_reuseFailAlloc_3359_; 
v_reuseFailAlloc_3359_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3359_, 0, v___x_3356_);
v___x_3358_ = v_reuseFailAlloc_3359_;
goto v_reusejp_3357_;
}
v_reusejp_3357_:
{
return v___x_3358_;
}
}
}
else
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3369_; 
v_a_3362_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3369_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3369_ == 0)
{
v___x_3364_ = v___x_3352_;
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3352_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3369_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3367_; 
if (v_isShared_3365_ == 0)
{
v___x_3367_ = v___x_3364_;
goto v_reusejp_3366_;
}
else
{
lean_object* v_reuseFailAlloc_3368_; 
v_reuseFailAlloc_3368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3368_, 0, v_a_3362_);
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
else
{
lean_object* v___x_3371_; 
lean_dec(v_a_3335_);
if (v_isShared_3349_ == 0)
{
v___x_3371_ = v___x_3348_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v_a_3346_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
}
}
}
else
{
lean_object* v_a_3376_; lean_object* v___x_3378_; uint8_t v_isShared_3379_; uint8_t v_isSharedCheck_3383_; 
lean_dec_ref(v_x_3328_);
v_a_3376_ = lean_ctor_get(v___x_3334_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3334_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3378_ = v___x_3334_;
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
else
{
lean_inc(v_a_3376_);
lean_dec(v___x_3334_);
v___x_3378_ = lean_box(0);
v_isShared_3379_ = v_isSharedCheck_3383_;
goto v_resetjp_3377_;
}
v_resetjp_3377_:
{
lean_object* v___x_3381_; 
if (v_isShared_3379_ == 0)
{
v___x_3381_ = v___x_3378_;
goto v_reusejp_3380_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v_a_3376_);
v___x_3381_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3380_;
}
v_reusejp_3380_:
{
return v___x_3381_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object* v_x_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_, lean_object* v___y_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_);
lean_dec(v___y_3388_);
lean_dec_ref(v___y_3387_);
lean_dec(v___y_3386_);
lean_dec_ref(v___y_3385_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object* v_00_u03b1_3391_, lean_object* v_x_3392_, lean_object* v___y_3393_, lean_object* v___y_3394_, lean_object* v___y_3395_, lean_object* v___y_3396_){
_start:
{
lean_object* v___x_3398_; 
v___x_3398_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3392_, v___y_3393_, v___y_3394_, v___y_3395_, v___y_3396_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object* v_00_u03b1_3399_, lean_object* v_x_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
lean_object* v_res_3406_; 
v_res_3406_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(v_00_u03b1_3399_, v_x_3400_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
return v_res_3406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* v_mvarId_3407_, lean_object* v_hFVarId_3408_, lean_object* v_a_3409_, lean_object* v_a_3410_, lean_object* v_a_3411_, lean_object* v_a_3412_){
_start:
{
lean_object* v___x_3414_; lean_object* v___x_3415_; 
v___x_3414_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___boxed), 7, 2);
lean_closure_set(v___x_3414_, 0, v_mvarId_3407_);
lean_closure_set(v___x_3414_, 1, v_hFVarId_3408_);
v___x_3415_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3414_, v_a_3409_, v_a_3410_, v_a_3411_, v_a_3412_);
return v___x_3415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object* v_mvarId_3416_, lean_object* v_hFVarId_3417_, lean_object* v_a_3418_, lean_object* v_a_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_){
_start:
{
lean_object* v_res_3423_; 
v_res_3423_ = l_Lean_Meta_substVar_x3f(v_mvarId_3416_, v_hFVarId_3417_, v_a_3418_, v_a_3419_, v_a_3420_, v_a_3421_);
lean_dec(v_a_3421_);
lean_dec_ref(v_a_3420_);
lean_dec(v_a_3419_);
lean_dec_ref(v_a_3418_);
return v_res_3423_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* v_mvarId_3424_, lean_object* v_hFVarId_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_){
_start:
{
lean_object* v___x_3431_; lean_object* v___x_3432_; 
v___x_3431_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 7, 2);
lean_closure_set(v___x_3431_, 0, v_mvarId_3424_);
lean_closure_set(v___x_3431_, 1, v_hFVarId_3425_);
v___x_3432_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3431_, v_a_3426_, v_a_3427_, v_a_3428_, v_a_3429_);
return v___x_3432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object* v_mvarId_3433_, lean_object* v_hFVarId_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_){
_start:
{
lean_object* v_res_3440_; 
v_res_3440_ = l_Lean_Meta_subst_x3f(v_mvarId_3433_, v_hFVarId_3434_, v_a_3435_, v_a_3436_, v_a_3437_, v_a_3438_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
return v_res_3440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* v_mvarId_3441_, lean_object* v_hFVarId_3442_, uint8_t v_symm_3443_, lean_object* v_fvarSubst_3444_, uint8_t v_clearH_3445_, uint8_t v_tryToSkip_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___x_3452_ = lean_box(v_symm_3443_);
v___x_3453_ = lean_box(v_clearH_3445_);
v___x_3454_ = lean_box(v_tryToSkip_3446_);
v___x_3455_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_3455_, 0, v_mvarId_3441_);
lean_closure_set(v___x_3455_, 1, v_hFVarId_3442_);
lean_closure_set(v___x_3455_, 2, v___x_3452_);
lean_closure_set(v___x_3455_, 3, v_fvarSubst_3444_);
lean_closure_set(v___x_3455_, 4, v___x_3453_);
lean_closure_set(v___x_3455_, 5, v___x_3454_);
v___x_3456_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3455_, v_a_3447_, v_a_3448_, v_a_3449_, v_a_3450_);
return v___x_3456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* v_mvarId_3457_, lean_object* v_hFVarId_3458_, lean_object* v_symm_3459_, lean_object* v_fvarSubst_3460_, lean_object* v_clearH_3461_, lean_object* v_tryToSkip_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_){
_start:
{
uint8_t v_symm_boxed_3468_; uint8_t v_clearH_boxed_3469_; uint8_t v_tryToSkip_boxed_3470_; lean_object* v_res_3471_; 
v_symm_boxed_3468_ = lean_unbox(v_symm_3459_);
v_clearH_boxed_3469_ = lean_unbox(v_clearH_3461_);
v_tryToSkip_boxed_3470_ = lean_unbox(v_tryToSkip_3462_);
v_res_3471_ = l_Lean_Meta_substCore_x3f(v_mvarId_3457_, v_hFVarId_3458_, v_symm_boxed_3468_, v_fvarSubst_3460_, v_clearH_boxed_3469_, v_tryToSkip_boxed_3470_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
lean_dec(v_a_3466_);
lean_dec_ref(v_a_3465_);
lean_dec(v_a_3464_);
lean_dec_ref(v_a_3463_);
return v_res_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* v_mvarId_3472_, lean_object* v_hFVarId_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_){
_start:
{
lean_object* v___x_3479_; 
lean_inc(v_mvarId_3472_);
v___x_3479_ = l_Lean_Meta_substVar_x3f(v_mvarId_3472_, v_hFVarId_3473_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
if (lean_obj_tag(v___x_3479_) == 0)
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3491_; 
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3482_ = v___x_3479_;
v_isShared_3483_ = v_isSharedCheck_3491_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3491_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
if (lean_obj_tag(v_a_3480_) == 0)
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v_mvarId_3472_);
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_mvarId_3472_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
else
{
lean_object* v_val_3487_; lean_object* v___x_3489_; 
lean_dec(v_mvarId_3472_);
v_val_3487_ = lean_ctor_get(v_a_3480_, 0);
lean_inc(v_val_3487_);
lean_dec_ref_known(v_a_3480_, 1);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v_val_3487_);
v___x_3489_ = v___x_3482_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_val_3487_);
v___x_3489_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3488_;
}
v_reusejp_3488_:
{
return v___x_3489_;
}
}
}
}
else
{
lean_object* v_a_3492_; lean_object* v___x_3494_; uint8_t v_isShared_3495_; uint8_t v_isSharedCheck_3499_; 
lean_dec(v_mvarId_3472_);
v_a_3492_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3499_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3499_ == 0)
{
v___x_3494_ = v___x_3479_;
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
else
{
lean_inc(v_a_3492_);
lean_dec(v___x_3479_);
v___x_3494_ = lean_box(0);
v_isShared_3495_ = v_isSharedCheck_3499_;
goto v_resetjp_3493_;
}
v_resetjp_3493_:
{
lean_object* v___x_3497_; 
if (v_isShared_3495_ == 0)
{
v___x_3497_ = v___x_3494_;
goto v_reusejp_3496_;
}
else
{
lean_object* v_reuseFailAlloc_3498_; 
v_reuseFailAlloc_3498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3498_, 0, v_a_3492_);
v___x_3497_ = v_reuseFailAlloc_3498_;
goto v_reusejp_3496_;
}
v_reusejp_3496_:
{
return v___x_3497_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object* v_mvarId_3500_, lean_object* v_hFVarId_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_, lean_object* v_a_3505_, lean_object* v_a_3506_){
_start:
{
lean_object* v_res_3507_; 
v_res_3507_ = l_Lean_Meta_trySubstVar(v_mvarId_3500_, v_hFVarId_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
lean_dec(v_a_3505_);
lean_dec_ref(v_a_3504_);
lean_dec(v_a_3503_);
lean_dec_ref(v_a_3502_);
return v_res_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* v_mvarId_3508_, lean_object* v_hFVarId_3509_, lean_object* v_a_3510_, lean_object* v_a_3511_, lean_object* v_a_3512_, lean_object* v_a_3513_){
_start:
{
lean_object* v___x_3515_; 
lean_inc(v_mvarId_3508_);
v___x_3515_ = l_Lean_Meta_subst_x3f(v_mvarId_3508_, v_hFVarId_3509_, v_a_3510_, v_a_3511_, v_a_3512_, v_a_3513_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v_a_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3527_; 
v_a_3516_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3518_ = v___x_3515_;
v_isShared_3519_ = v_isSharedCheck_3527_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_a_3516_);
lean_dec(v___x_3515_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3527_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
if (lean_obj_tag(v_a_3516_) == 0)
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v_mvarId_3508_);
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v_mvarId_3508_);
v___x_3521_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
return v___x_3521_;
}
}
else
{
lean_object* v_val_3523_; lean_object* v___x_3525_; 
lean_dec(v_mvarId_3508_);
v_val_3523_ = lean_ctor_get(v_a_3516_, 0);
lean_inc(v_val_3523_);
lean_dec_ref_known(v_a_3516_, 1);
if (v_isShared_3519_ == 0)
{
lean_ctor_set(v___x_3518_, 0, v_val_3523_);
v___x_3525_ = v___x_3518_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_val_3523_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec(v_mvarId_3508_);
v_a_3528_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3515_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3515_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object* v_mvarId_3536_, lean_object* v_hFVarId_3537_, lean_object* v_a_3538_, lean_object* v_a_3539_, lean_object* v_a_3540_, lean_object* v_a_3541_, lean_object* v_a_3542_){
_start:
{
lean_object* v_res_3543_; 
v_res_3543_ = l_Lean_Meta_trySubst(v_mvarId_3536_, v_hFVarId_3537_, v_a_3538_, v_a_3539_, v_a_3540_, v_a_3541_);
lean_dec(v_a_3541_);
lean_dec_ref(v_a_3540_);
lean_dec(v_a_3539_);
lean_dec_ref(v_a_3538_);
return v_res_3543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_mvarId_3547_, lean_object* v_as_3548_, size_t v_sz_3549_, size_t v_i_3550_, lean_object* v_b_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_){
_start:
{
uint8_t v___x_3557_; 
v___x_3557_ = lean_usize_dec_lt(v_i_3550_, v_sz_3549_);
if (v___x_3557_ == 0)
{
lean_object* v___x_3558_; 
lean_dec(v_mvarId_3547_);
v___x_3558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3558_, 0, v_b_3551_);
return v___x_3558_;
}
else
{
lean_object* v_snd_3559_; lean_object* v___x_3561_; uint8_t v_isShared_3562_; uint8_t v_isSharedCheck_3612_; 
v_snd_3559_ = lean_ctor_get(v_b_3551_, 1);
v_isSharedCheck_3612_ = !lean_is_exclusive(v_b_3551_);
if (v_isSharedCheck_3612_ == 0)
{
lean_object* v_unused_3613_; 
v_unused_3613_ = lean_ctor_get(v_b_3551_, 0);
lean_dec(v_unused_3613_);
v___x_3561_ = v_b_3551_;
v_isShared_3562_ = v_isSharedCheck_3612_;
goto v_resetjp_3560_;
}
else
{
lean_inc(v_snd_3559_);
lean_dec(v_b_3551_);
v___x_3561_ = lean_box(0);
v_isShared_3562_ = v_isSharedCheck_3612_;
goto v_resetjp_3560_;
}
v_resetjp_3560_:
{
lean_object* v___x_3563_; lean_object* v_a_3565_; lean_object* v_a_3572_; 
v___x_3563_ = lean_box(0);
v_a_3572_ = lean_array_uget(v_as_3548_, v_i_3550_);
if (lean_obj_tag(v_a_3572_) == 0)
{
v_a_3565_ = v_snd_3559_;
goto v___jp_3564_;
}
else
{
lean_object* v_val_3573_; lean_object* v___x_3575_; uint8_t v_isShared_3576_; uint8_t v_isSharedCheck_3611_; 
v_val_3573_ = lean_ctor_get(v_a_3572_, 0);
v_isSharedCheck_3611_ = !lean_is_exclusive(v_a_3572_);
if (v_isSharedCheck_3611_ == 0)
{
v___x_3575_ = v_a_3572_;
v_isShared_3576_ = v_isSharedCheck_3611_;
goto v_resetjp_3574_;
}
else
{
lean_inc(v_val_3573_);
lean_dec(v_a_3572_);
v___x_3575_ = lean_box(0);
v_isShared_3576_ = v_isSharedCheck_3611_;
goto v_resetjp_3574_;
}
v_resetjp_3574_:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3577_ = lean_box(0);
v___x_3578_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3579_ = l_Lean_LocalDecl_fvarId(v_val_3573_);
lean_dec(v_val_3573_);
lean_inc(v_mvarId_3547_);
v___x_3580_ = l_Lean_Meta_subst_x3f(v_mvarId_3547_, v___x_3579_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
if (lean_obj_tag(v___x_3580_) == 0)
{
lean_object* v_a_3581_; lean_object* v___x_3583_; uint8_t v_isShared_3584_; uint8_t v_isSharedCheck_3602_; 
v_a_3581_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3602_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3602_ == 0)
{
v___x_3583_ = v___x_3580_;
v_isShared_3584_ = v_isSharedCheck_3602_;
goto v_resetjp_3582_;
}
else
{
lean_inc(v_a_3581_);
lean_dec(v___x_3580_);
v___x_3583_ = lean_box(0);
v_isShared_3584_ = v_isSharedCheck_3602_;
goto v_resetjp_3582_;
}
v_resetjp_3582_:
{
if (lean_obj_tag(v_a_3581_) == 1)
{
lean_object* v___x_3586_; 
lean_del_object(v___x_3561_);
lean_dec(v_mvarId_3547_);
lean_inc_ref(v_a_3581_);
if (v_isShared_3576_ == 0)
{
lean_ctor_set(v___x_3575_, 0, v_a_3581_);
v___x_3586_ = v___x_3575_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3601_; 
v_reuseFailAlloc_3601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3601_, 0, v_a_3581_);
v___x_3586_ = v_reuseFailAlloc_3601_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3599_; 
v_isSharedCheck_3599_ = !lean_is_exclusive(v_a_3581_);
if (v_isSharedCheck_3599_ == 0)
{
lean_object* v_unused_3600_; 
v_unused_3600_ = lean_ctor_get(v_a_3581_, 0);
lean_dec(v_unused_3600_);
v___x_3588_ = v_a_3581_;
v_isShared_3589_ = v_isSharedCheck_3599_;
goto v_resetjp_3587_;
}
else
{
lean_dec(v_a_3581_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3599_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v___x_3592_; 
v___x_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3590_, 0, v___x_3586_);
lean_ctor_set(v___x_3590_, 1, v___x_3577_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set_tag(v___x_3588_, 0);
lean_ctor_set(v___x_3588_, 0, v___x_3590_);
v___x_3592_ = v___x_3588_;
goto v_reusejp_3591_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v___x_3590_);
v___x_3592_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3591_;
}
v_reusejp_3591_:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3596_; 
v___x_3593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3593_, 0, v___x_3592_);
v___x_3594_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set(v___x_3594_, 1, v_snd_3559_);
if (v_isShared_3584_ == 0)
{
lean_ctor_set(v___x_3583_, 0, v___x_3594_);
v___x_3596_ = v___x_3583_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3597_; 
v_reuseFailAlloc_3597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3597_, 0, v___x_3594_);
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
}
else
{
lean_del_object(v___x_3583_);
lean_dec(v_a_3581_);
lean_del_object(v___x_3575_);
lean_dec(v_snd_3559_);
v_a_3565_ = v___x_3578_;
goto v___jp_3564_;
}
}
}
else
{
lean_object* v_a_3603_; lean_object* v___x_3605_; uint8_t v_isShared_3606_; uint8_t v_isSharedCheck_3610_; 
lean_del_object(v___x_3575_);
lean_del_object(v___x_3561_);
lean_dec(v_snd_3559_);
lean_dec(v_mvarId_3547_);
v_a_3603_ = lean_ctor_get(v___x_3580_, 0);
v_isSharedCheck_3610_ = !lean_is_exclusive(v___x_3580_);
if (v_isSharedCheck_3610_ == 0)
{
v___x_3605_ = v___x_3580_;
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
else
{
lean_inc(v_a_3603_);
lean_dec(v___x_3580_);
v___x_3605_ = lean_box(0);
v_isShared_3606_ = v_isSharedCheck_3610_;
goto v_resetjp_3604_;
}
v_resetjp_3604_:
{
lean_object* v___x_3608_; 
if (v_isShared_3606_ == 0)
{
v___x_3608_ = v___x_3605_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v_a_3603_);
v___x_3608_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
return v___x_3608_;
}
}
}
}
}
v___jp_3564_:
{
lean_object* v___x_3567_; 
if (v_isShared_3562_ == 0)
{
lean_ctor_set(v___x_3561_, 1, v_a_3565_);
lean_ctor_set(v___x_3561_, 0, v___x_3563_);
v___x_3567_ = v___x_3561_;
goto v_reusejp_3566_;
}
else
{
lean_object* v_reuseFailAlloc_3571_; 
v_reuseFailAlloc_3571_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3571_, 0, v___x_3563_);
lean_ctor_set(v_reuseFailAlloc_3571_, 1, v_a_3565_);
v___x_3567_ = v_reuseFailAlloc_3571_;
goto v_reusejp_3566_;
}
v_reusejp_3566_:
{
size_t v___x_3568_; size_t v___x_3569_; 
v___x_3568_ = ((size_t)1ULL);
v___x_3569_ = lean_usize_add(v_i_3550_, v___x_3568_);
v_i_3550_ = v___x_3569_;
v_b_3551_ = v___x_3567_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_mvarId_3614_, lean_object* v_as_3615_, lean_object* v_sz_3616_, lean_object* v_i_3617_, lean_object* v_b_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
size_t v_sz_boxed_3624_; size_t v_i_boxed_3625_; lean_object* v_res_3626_; 
v_sz_boxed_3624_ = lean_unbox_usize(v_sz_3616_);
lean_dec(v_sz_3616_);
v_i_boxed_3625_ = lean_unbox_usize(v_i_3617_);
lean_dec(v_i_3617_);
v_res_3626_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3614_, v_as_3615_, v_sz_boxed_3624_, v_i_boxed_3625_, v_b_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
lean_dec_ref(v_as_3615_);
return v_res_3626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object* v_mvarId_3627_, lean_object* v_as_3628_, size_t v_sz_3629_, size_t v_i_3630_, lean_object* v_b_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_){
_start:
{
uint8_t v___x_3637_; 
v___x_3637_ = lean_usize_dec_lt(v_i_3630_, v_sz_3629_);
if (v___x_3637_ == 0)
{
lean_object* v___x_3638_; 
lean_dec(v_mvarId_3627_);
v___x_3638_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3638_, 0, v_b_3631_);
return v___x_3638_;
}
else
{
lean_object* v_snd_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3692_; 
v_snd_3639_ = lean_ctor_get(v_b_3631_, 1);
v_isSharedCheck_3692_ = !lean_is_exclusive(v_b_3631_);
if (v_isSharedCheck_3692_ == 0)
{
lean_object* v_unused_3693_; 
v_unused_3693_ = lean_ctor_get(v_b_3631_, 0);
lean_dec(v_unused_3693_);
v___x_3641_ = v_b_3631_;
v_isShared_3642_ = v_isSharedCheck_3692_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_snd_3639_);
lean_dec(v_b_3631_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3692_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; lean_object* v_a_3645_; lean_object* v_a_3652_; 
v___x_3643_ = lean_box(0);
v_a_3652_ = lean_array_uget(v_as_3628_, v_i_3630_);
if (lean_obj_tag(v_a_3652_) == 0)
{
v_a_3645_ = v_snd_3639_;
goto v___jp_3644_;
}
else
{
lean_object* v_val_3653_; lean_object* v___x_3655_; uint8_t v_isShared_3656_; uint8_t v_isSharedCheck_3691_; 
v_val_3653_ = lean_ctor_get(v_a_3652_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v_a_3652_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3655_ = v_a_3652_;
v_isShared_3656_ = v_isSharedCheck_3691_;
goto v_resetjp_3654_;
}
else
{
lean_inc(v_val_3653_);
lean_dec(v_a_3652_);
v___x_3655_ = lean_box(0);
v_isShared_3656_ = v_isSharedCheck_3691_;
goto v_resetjp_3654_;
}
v_resetjp_3654_:
{
lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; 
v___x_3657_ = lean_box(0);
v___x_3658_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3659_ = l_Lean_LocalDecl_fvarId(v_val_3653_);
lean_dec(v_val_3653_);
lean_inc(v_mvarId_3627_);
v___x_3660_ = l_Lean_Meta_subst_x3f(v_mvarId_3627_, v___x_3659_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3682_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3682_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3682_ == 0)
{
v___x_3663_ = v___x_3660_;
v_isShared_3664_ = v_isSharedCheck_3682_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3660_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3682_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
if (lean_obj_tag(v_a_3661_) == 1)
{
lean_object* v___x_3666_; 
lean_del_object(v___x_3641_);
lean_dec(v_mvarId_3627_);
lean_inc_ref(v_a_3661_);
if (v_isShared_3656_ == 0)
{
lean_ctor_set(v___x_3655_, 0, v_a_3661_);
v___x_3666_ = v___x_3655_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3681_; 
v_reuseFailAlloc_3681_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3681_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3681_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3679_; 
v_isSharedCheck_3679_ = !lean_is_exclusive(v_a_3661_);
if (v_isSharedCheck_3679_ == 0)
{
lean_object* v_unused_3680_; 
v_unused_3680_ = lean_ctor_get(v_a_3661_, 0);
lean_dec(v_unused_3680_);
v___x_3668_ = v_a_3661_;
v_isShared_3669_ = v_isSharedCheck_3679_;
goto v_resetjp_3667_;
}
else
{
lean_dec(v_a_3661_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3679_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; lean_object* v___x_3672_; 
v___x_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3666_);
lean_ctor_set(v___x_3670_, 1, v___x_3657_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set_tag(v___x_3668_, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3670_);
v___x_3672_ = v___x_3668_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3670_);
v___x_3672_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3676_; 
v___x_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3673_, 0, v___x_3672_);
v___x_3674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3673_);
lean_ctor_set(v___x_3674_, 1, v_snd_3639_);
if (v_isShared_3664_ == 0)
{
lean_ctor_set(v___x_3663_, 0, v___x_3674_);
v___x_3676_ = v___x_3663_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3674_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
}
else
{
lean_del_object(v___x_3663_);
lean_dec(v_a_3661_);
lean_del_object(v___x_3655_);
lean_dec(v_snd_3639_);
v_a_3645_ = v___x_3658_;
goto v___jp_3644_;
}
}
}
else
{
lean_object* v_a_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_3690_; 
lean_del_object(v___x_3655_);
lean_del_object(v___x_3641_);
lean_dec(v_snd_3639_);
lean_dec(v_mvarId_3627_);
v_a_3683_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3690_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3690_ == 0)
{
v___x_3685_ = v___x_3660_;
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_a_3683_);
lean_dec(v___x_3660_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_3690_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v___x_3688_; 
if (v_isShared_3686_ == 0)
{
v___x_3688_ = v___x_3685_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v_a_3683_);
v___x_3688_ = v_reuseFailAlloc_3689_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
return v___x_3688_;
}
}
}
}
}
v___jp_3644_:
{
lean_object* v___x_3647_; 
if (v_isShared_3642_ == 0)
{
lean_ctor_set(v___x_3641_, 1, v_a_3645_);
lean_ctor_set(v___x_3641_, 0, v___x_3643_);
v___x_3647_ = v___x_3641_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_a_3645_);
v___x_3647_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
size_t v___x_3648_; size_t v___x_3649_; lean_object* v___x_3650_; 
v___x_3648_ = ((size_t)1ULL);
v___x_3649_ = lean_usize_add(v_i_3630_, v___x_3648_);
v___x_3650_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3627_, v_as_3628_, v_sz_3629_, v___x_3649_, v___x_3647_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
return v___x_3650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_3694_, lean_object* v_as_3695_, lean_object* v_sz_3696_, lean_object* v_i_3697_, lean_object* v_b_3698_, lean_object* v___y_3699_, lean_object* v___y_3700_, lean_object* v___y_3701_, lean_object* v___y_3702_, lean_object* v___y_3703_){
_start:
{
size_t v_sz_boxed_3704_; size_t v_i_boxed_3705_; lean_object* v_res_3706_; 
v_sz_boxed_3704_ = lean_unbox_usize(v_sz_3696_);
lean_dec(v_sz_3696_);
v_i_boxed_3705_ = lean_unbox_usize(v_i_3697_);
lean_dec(v_i_3697_);
v_res_3706_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3694_, v_as_3695_, v_sz_boxed_3704_, v_i_boxed_3705_, v_b_3698_, v___y_3699_, v___y_3700_, v___y_3701_, v___y_3702_);
lean_dec(v___y_3702_);
lean_dec_ref(v___y_3701_);
lean_dec(v___y_3700_);
lean_dec_ref(v___y_3699_);
lean_dec_ref(v_as_3695_);
return v_res_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* v_init_3707_, lean_object* v_mvarId_3708_, lean_object* v_n_3709_, lean_object* v_b_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
if (lean_obj_tag(v_n_3709_) == 0)
{
lean_object* v_cs_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; size_t v_sz_3719_; size_t v___x_3720_; lean_object* v___x_3721_; 
v_cs_3716_ = lean_ctor_get(v_n_3709_, 0);
v___x_3717_ = lean_box(0);
v___x_3718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
lean_ctor_set(v___x_3718_, 1, v_b_3710_);
v_sz_3719_ = lean_array_size(v_cs_3716_);
v___x_3720_ = ((size_t)0ULL);
v___x_3721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3707_, v_mvarId_3708_, v_cs_3716_, v_sz_3719_, v___x_3720_, v___x_3718_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3721_) == 0)
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3736_; 
v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3724_ = v___x_3721_;
v_isShared_3725_ = v_isSharedCheck_3736_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3721_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3736_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v_fst_3726_; 
v_fst_3726_ = lean_ctor_get(v_a_3722_, 0);
if (lean_obj_tag(v_fst_3726_) == 0)
{
lean_object* v_snd_3727_; lean_object* v___x_3728_; lean_object* v___x_3730_; 
v_snd_3727_ = lean_ctor_get(v_a_3722_, 1);
lean_inc(v_snd_3727_);
lean_dec(v_a_3722_);
v___x_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3728_, 0, v_snd_3727_);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v___x_3728_);
v___x_3730_ = v___x_3724_;
goto v_reusejp_3729_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3728_);
v___x_3730_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3729_;
}
v_reusejp_3729_:
{
return v___x_3730_;
}
}
else
{
lean_object* v_val_3732_; lean_object* v___x_3734_; 
lean_inc_ref(v_fst_3726_);
lean_dec(v_a_3722_);
v_val_3732_ = lean_ctor_get(v_fst_3726_, 0);
lean_inc(v_val_3732_);
lean_dec_ref_known(v_fst_3726_, 1);
if (v_isShared_3725_ == 0)
{
lean_ctor_set(v___x_3724_, 0, v_val_3732_);
v___x_3734_ = v___x_3724_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_val_3732_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
v_a_3737_ = lean_ctor_get(v___x_3721_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3721_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3721_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3721_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v___x_3742_; 
if (v_isShared_3740_ == 0)
{
v___x_3742_ = v___x_3739_;
goto v_reusejp_3741_;
}
else
{
lean_object* v_reuseFailAlloc_3743_; 
v_reuseFailAlloc_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3743_, 0, v_a_3737_);
v___x_3742_ = v_reuseFailAlloc_3743_;
goto v_reusejp_3741_;
}
v_reusejp_3741_:
{
return v___x_3742_;
}
}
}
}
else
{
lean_object* v_vs_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; size_t v_sz_3748_; size_t v___x_3749_; lean_object* v___x_3750_; 
v_vs_3745_ = lean_ctor_get(v_n_3709_, 0);
v___x_3746_ = lean_box(0);
v___x_3747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3746_);
lean_ctor_set(v___x_3747_, 1, v_b_3710_);
v_sz_3748_ = lean_array_size(v_vs_3745_);
v___x_3749_ = ((size_t)0ULL);
v___x_3750_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3708_, v_vs_3745_, v_sz_3748_, v___x_3749_, v___x_3747_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3765_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3753_ = v___x_3750_;
v_isShared_3754_ = v_isSharedCheck_3765_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3750_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3765_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v_fst_3755_; 
v_fst_3755_ = lean_ctor_get(v_a_3751_, 0);
if (lean_obj_tag(v_fst_3755_) == 0)
{
lean_object* v_snd_3756_; lean_object* v___x_3757_; lean_object* v___x_3759_; 
v_snd_3756_ = lean_ctor_get(v_a_3751_, 1);
lean_inc(v_snd_3756_);
lean_dec(v_a_3751_);
v___x_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3757_, 0, v_snd_3756_);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v___x_3757_);
v___x_3759_ = v___x_3753_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3760_; 
v_reuseFailAlloc_3760_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3760_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3760_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
return v___x_3759_;
}
}
else
{
lean_object* v_val_3761_; lean_object* v___x_3763_; 
lean_inc_ref(v_fst_3755_);
lean_dec(v_a_3751_);
v_val_3761_ = lean_ctor_get(v_fst_3755_, 0);
lean_inc(v_val_3761_);
lean_dec_ref_known(v_fst_3755_, 1);
if (v_isShared_3754_ == 0)
{
lean_ctor_set(v___x_3753_, 0, v_val_3761_);
v___x_3763_ = v___x_3753_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_val_3761_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
v_a_3766_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3750_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3750_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v___x_3771_; 
if (v_isShared_3769_ == 0)
{
v___x_3771_ = v___x_3768_;
goto v_reusejp_3770_;
}
else
{
lean_object* v_reuseFailAlloc_3772_; 
v_reuseFailAlloc_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3772_, 0, v_a_3766_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_init_3774_, lean_object* v_mvarId_3775_, lean_object* v_as_3776_, size_t v_sz_3777_, size_t v_i_3778_, lean_object* v_b_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
uint8_t v___x_3785_; 
v___x_3785_ = lean_usize_dec_lt(v_i_3778_, v_sz_3777_);
if (v___x_3785_ == 0)
{
lean_object* v___x_3786_; 
lean_dec(v_mvarId_3775_);
v___x_3786_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3786_, 0, v_b_3779_);
return v___x_3786_;
}
else
{
lean_object* v_snd_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3821_; 
v_snd_3787_ = lean_ctor_get(v_b_3779_, 1);
v_isSharedCheck_3821_ = !lean_is_exclusive(v_b_3779_);
if (v_isSharedCheck_3821_ == 0)
{
lean_object* v_unused_3822_; 
v_unused_3822_ = lean_ctor_get(v_b_3779_, 0);
lean_dec(v_unused_3822_);
v___x_3789_ = v_b_3779_;
v_isShared_3790_ = v_isSharedCheck_3821_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_snd_3787_);
lean_dec(v_b_3779_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3821_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3791_; lean_object* v_a_3792_; lean_object* v___x_3793_; 
v___x_3791_ = lean_box(0);
v_a_3792_ = lean_array_uget_borrowed(v_as_3776_, v_i_3778_);
lean_inc(v_snd_3787_);
lean_inc(v_mvarId_3775_);
v___x_3793_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3774_, v_mvarId_3775_, v_a_3792_, v_snd_3787_, v___y_3780_, v___y_3781_, v___y_3782_, v___y_3783_);
if (lean_obj_tag(v___x_3793_) == 0)
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3812_; 
v_a_3794_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3812_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3812_ == 0)
{
v___x_3796_ = v___x_3793_;
v_isShared_3797_ = v_isSharedCheck_3812_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3793_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3812_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
if (lean_obj_tag(v_a_3794_) == 0)
{
lean_object* v___x_3798_; lean_object* v___x_3800_; 
lean_dec(v_mvarId_3775_);
v___x_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3798_, 0, v_a_3794_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 0, v___x_3798_);
v___x_3800_ = v___x_3789_;
goto v_reusejp_3799_;
}
else
{
lean_object* v_reuseFailAlloc_3804_; 
v_reuseFailAlloc_3804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3804_, 0, v___x_3798_);
lean_ctor_set(v_reuseFailAlloc_3804_, 1, v_snd_3787_);
v___x_3800_ = v_reuseFailAlloc_3804_;
goto v_reusejp_3799_;
}
v_reusejp_3799_:
{
lean_object* v___x_3802_; 
if (v_isShared_3797_ == 0)
{
lean_ctor_set(v___x_3796_, 0, v___x_3800_);
v___x_3802_ = v___x_3796_;
goto v_reusejp_3801_;
}
else
{
lean_object* v_reuseFailAlloc_3803_; 
v_reuseFailAlloc_3803_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3803_, 0, v___x_3800_);
v___x_3802_ = v_reuseFailAlloc_3803_;
goto v_reusejp_3801_;
}
v_reusejp_3801_:
{
return v___x_3802_;
}
}
}
else
{
lean_object* v_a_3805_; lean_object* v___x_3807_; 
lean_del_object(v___x_3796_);
lean_dec(v_snd_3787_);
v_a_3805_ = lean_ctor_get(v_a_3794_, 0);
lean_inc(v_a_3805_);
lean_dec_ref_known(v_a_3794_, 1);
if (v_isShared_3790_ == 0)
{
lean_ctor_set(v___x_3789_, 1, v_a_3805_);
lean_ctor_set(v___x_3789_, 0, v___x_3791_);
v___x_3807_ = v___x_3789_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3791_);
lean_ctor_set(v_reuseFailAlloc_3811_, 1, v_a_3805_);
v___x_3807_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
size_t v___x_3808_; size_t v___x_3809_; 
v___x_3808_ = ((size_t)1ULL);
v___x_3809_ = lean_usize_add(v_i_3778_, v___x_3808_);
v_i_3778_ = v___x_3809_;
v_b_3779_ = v___x_3807_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_del_object(v___x_3789_);
lean_dec(v_snd_3787_);
lean_dec(v_mvarId_3775_);
v_a_3813_ = lean_ctor_get(v___x_3793_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3793_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3793_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3793_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3823_, lean_object* v_mvarId_3824_, lean_object* v_as_3825_, lean_object* v_sz_3826_, lean_object* v_i_3827_, lean_object* v_b_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
size_t v_sz_boxed_3834_; size_t v_i_boxed_3835_; lean_object* v_res_3836_; 
v_sz_boxed_3834_ = lean_unbox_usize(v_sz_3826_);
lean_dec(v_sz_3826_);
v_i_boxed_3835_ = lean_unbox_usize(v_i_3827_);
lean_dec(v_i_3827_);
v_res_3836_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3823_, v_mvarId_3824_, v_as_3825_, v_sz_boxed_3834_, v_i_boxed_3835_, v_b_3828_, v___y_3829_, v___y_3830_, v___y_3831_, v___y_3832_);
lean_dec(v___y_3832_);
lean_dec_ref(v___y_3831_);
lean_dec(v___y_3830_);
lean_dec_ref(v___y_3829_);
lean_dec_ref(v_as_3825_);
lean_dec_ref(v_init_3823_);
return v_res_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_init_3837_, lean_object* v_mvarId_3838_, lean_object* v_n_3839_, lean_object* v_b_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_){
_start:
{
lean_object* v_res_3846_; 
v_res_3846_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3837_, v_mvarId_3838_, v_n_3839_, v_b_3840_, v___y_3841_, v___y_3842_, v___y_3843_, v___y_3844_);
lean_dec(v___y_3844_);
lean_dec_ref(v___y_3843_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec_ref(v_n_3839_);
lean_dec_ref(v_init_3837_);
return v_res_3846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3850_, lean_object* v_as_3851_, size_t v_sz_3852_, size_t v_i_3853_, lean_object* v_b_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
uint8_t v___x_3860_; 
v___x_3860_ = lean_usize_dec_lt(v_i_3853_, v_sz_3852_);
if (v___x_3860_ == 0)
{
lean_object* v___x_3861_; 
lean_dec(v_mvarId_3850_);
v___x_3861_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3861_, 0, v_b_3854_);
return v___x_3861_;
}
else
{
lean_object* v_snd_3862_; lean_object* v___x_3864_; uint8_t v_isShared_3865_; uint8_t v_isSharedCheck_3914_; 
v_snd_3862_ = lean_ctor_get(v_b_3854_, 1);
v_isSharedCheck_3914_ = !lean_is_exclusive(v_b_3854_);
if (v_isSharedCheck_3914_ == 0)
{
lean_object* v_unused_3915_; 
v_unused_3915_ = lean_ctor_get(v_b_3854_, 0);
lean_dec(v_unused_3915_);
v___x_3864_ = v_b_3854_;
v_isShared_3865_ = v_isSharedCheck_3914_;
goto v_resetjp_3863_;
}
else
{
lean_inc(v_snd_3862_);
lean_dec(v_b_3854_);
v___x_3864_ = lean_box(0);
v_isShared_3865_ = v_isSharedCheck_3914_;
goto v_resetjp_3863_;
}
v_resetjp_3863_:
{
lean_object* v___x_3866_; lean_object* v_a_3868_; lean_object* v_a_3875_; 
v___x_3866_ = lean_box(0);
v_a_3875_ = lean_array_uget(v_as_3851_, v_i_3853_);
if (lean_obj_tag(v_a_3875_) == 0)
{
v_a_3868_ = v_snd_3862_;
goto v___jp_3867_;
}
else
{
lean_object* v_val_3876_; lean_object* v___x_3878_; uint8_t v_isShared_3879_; uint8_t v_isSharedCheck_3913_; 
v_val_3876_ = lean_ctor_get(v_a_3875_, 0);
v_isSharedCheck_3913_ = !lean_is_exclusive(v_a_3875_);
if (v_isSharedCheck_3913_ == 0)
{
v___x_3878_ = v_a_3875_;
v_isShared_3879_ = v_isSharedCheck_3913_;
goto v_resetjp_3877_;
}
else
{
lean_inc(v_val_3876_);
lean_dec(v_a_3875_);
v___x_3878_ = lean_box(0);
v_isShared_3879_ = v_isSharedCheck_3913_;
goto v_resetjp_3877_;
}
v_resetjp_3877_:
{
lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3880_ = lean_box(0);
v___x_3881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v___x_3882_ = l_Lean_LocalDecl_fvarId(v_val_3876_);
lean_dec(v_val_3876_);
lean_inc(v_mvarId_3850_);
v___x_3883_ = l_Lean_Meta_subst_x3f(v_mvarId_3850_, v___x_3882_, v___y_3855_, v___y_3856_, v___y_3857_, v___y_3858_);
if (lean_obj_tag(v___x_3883_) == 0)
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3904_; 
v_a_3884_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3904_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3904_ == 0)
{
v___x_3886_ = v___x_3883_;
v_isShared_3887_ = v_isSharedCheck_3904_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3883_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3904_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
if (lean_obj_tag(v_a_3884_) == 1)
{
lean_object* v___x_3889_; 
lean_del_object(v___x_3864_);
lean_dec(v_mvarId_3850_);
lean_inc_ref(v_a_3884_);
if (v_isShared_3879_ == 0)
{
lean_ctor_set(v___x_3878_, 0, v_a_3884_);
v___x_3889_ = v___x_3878_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v_a_3884_);
v___x_3889_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3901_; 
v_isSharedCheck_3901_ = !lean_is_exclusive(v_a_3884_);
if (v_isSharedCheck_3901_ == 0)
{
lean_object* v_unused_3902_; 
v_unused_3902_ = lean_ctor_get(v_a_3884_, 0);
lean_dec(v_unused_3902_);
v___x_3891_ = v_a_3884_;
v_isShared_3892_ = v_isSharedCheck_3901_;
goto v_resetjp_3890_;
}
else
{
lean_dec(v_a_3884_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3901_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3895_; 
v___x_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3889_);
lean_ctor_set(v___x_3893_, 1, v___x_3880_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 0, v___x_3893_);
v___x_3895_ = v___x_3891_;
goto v_reusejp_3894_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v___x_3893_);
v___x_3895_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3894_;
}
v_reusejp_3894_:
{
lean_object* v___x_3896_; lean_object* v___x_3898_; 
v___x_3896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3896_, 0, v___x_3895_);
lean_ctor_set(v___x_3896_, 1, v_snd_3862_);
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 0, v___x_3896_);
v___x_3898_ = v___x_3886_;
goto v_reusejp_3897_;
}
else
{
lean_object* v_reuseFailAlloc_3899_; 
v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3899_, 0, v___x_3896_);
v___x_3898_ = v_reuseFailAlloc_3899_;
goto v_reusejp_3897_;
}
v_reusejp_3897_:
{
return v___x_3898_;
}
}
}
}
}
else
{
lean_del_object(v___x_3886_);
lean_dec(v_a_3884_);
lean_del_object(v___x_3878_);
lean_dec(v_snd_3862_);
v_a_3868_ = v___x_3881_;
goto v___jp_3867_;
}
}
}
else
{
lean_object* v_a_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3912_; 
lean_del_object(v___x_3878_);
lean_del_object(v___x_3864_);
lean_dec(v_snd_3862_);
lean_dec(v_mvarId_3850_);
v_a_3905_ = lean_ctor_get(v___x_3883_, 0);
v_isSharedCheck_3912_ = !lean_is_exclusive(v___x_3883_);
if (v_isSharedCheck_3912_ == 0)
{
v___x_3907_ = v___x_3883_;
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_a_3905_);
lean_dec(v___x_3883_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3912_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3910_; 
if (v_isShared_3908_ == 0)
{
v___x_3910_ = v___x_3907_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v_a_3905_);
v___x_3910_ = v_reuseFailAlloc_3911_;
goto v_reusejp_3909_;
}
v_reusejp_3909_:
{
return v___x_3910_;
}
}
}
}
}
v___jp_3867_:
{
lean_object* v___x_3870_; 
if (v_isShared_3865_ == 0)
{
lean_ctor_set(v___x_3864_, 1, v_a_3868_);
lean_ctor_set(v___x_3864_, 0, v___x_3866_);
v___x_3870_ = v___x_3864_;
goto v_reusejp_3869_;
}
else
{
lean_object* v_reuseFailAlloc_3874_; 
v_reuseFailAlloc_3874_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3874_, 0, v___x_3866_);
lean_ctor_set(v_reuseFailAlloc_3874_, 1, v_a_3868_);
v___x_3870_ = v_reuseFailAlloc_3874_;
goto v_reusejp_3869_;
}
v_reusejp_3869_:
{
size_t v___x_3871_; size_t v___x_3872_; 
v___x_3871_ = ((size_t)1ULL);
v___x_3872_ = lean_usize_add(v_i_3853_, v___x_3871_);
v_i_3853_ = v___x_3872_;
v_b_3854_ = v___x_3870_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3916_, lean_object* v_as_3917_, lean_object* v_sz_3918_, lean_object* v_i_3919_, lean_object* v_b_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_, lean_object* v___y_3925_){
_start:
{
size_t v_sz_boxed_3926_; size_t v_i_boxed_3927_; lean_object* v_res_3928_; 
v_sz_boxed_3926_ = lean_unbox_usize(v_sz_3918_);
lean_dec(v_sz_3918_);
v_i_boxed_3927_ = lean_unbox_usize(v_i_3919_);
lean_dec(v_i_3919_);
v_res_3928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3916_, v_as_3917_, v_sz_boxed_3926_, v_i_boxed_3927_, v_b_3920_, v___y_3921_, v___y_3922_, v___y_3923_, v___y_3924_);
lean_dec(v___y_3924_);
lean_dec_ref(v___y_3923_);
lean_dec(v___y_3922_);
lean_dec_ref(v___y_3921_);
lean_dec_ref(v_as_3917_);
return v_res_3928_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_3929_, lean_object* v_as_3930_, size_t v_sz_3931_, size_t v_i_3932_, lean_object* v_b_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_){
_start:
{
uint8_t v___x_3939_; 
v___x_3939_ = lean_usize_dec_lt(v_i_3932_, v_sz_3931_);
if (v___x_3939_ == 0)
{
lean_object* v___x_3940_; 
lean_dec(v_mvarId_3929_);
v___x_3940_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3940_, 0, v_b_3933_);
return v___x_3940_;
}
else
{
lean_object* v_snd_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3993_; 
v_snd_3941_ = lean_ctor_get(v_b_3933_, 1);
v_isSharedCheck_3993_ = !lean_is_exclusive(v_b_3933_);
if (v_isSharedCheck_3993_ == 0)
{
lean_object* v_unused_3994_; 
v_unused_3994_ = lean_ctor_get(v_b_3933_, 0);
lean_dec(v_unused_3994_);
v___x_3943_ = v_b_3933_;
v_isShared_3944_ = v_isSharedCheck_3993_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_snd_3941_);
lean_dec(v_b_3933_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3993_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3945_; lean_object* v_a_3947_; lean_object* v_a_3954_; 
v___x_3945_ = lean_box(0);
v_a_3954_ = lean_array_uget(v_as_3930_, v_i_3932_);
if (lean_obj_tag(v_a_3954_) == 0)
{
v_a_3947_ = v_snd_3941_;
goto v___jp_3946_;
}
else
{
lean_object* v_val_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3992_; 
v_val_3955_ = lean_ctor_get(v_a_3954_, 0);
v_isSharedCheck_3992_ = !lean_is_exclusive(v_a_3954_);
if (v_isSharedCheck_3992_ == 0)
{
v___x_3957_ = v_a_3954_;
v_isShared_3958_ = v_isSharedCheck_3992_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_val_3955_);
lean_dec(v_a_3954_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3992_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; 
v___x_3959_ = lean_box(0);
v___x_3960_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v___x_3961_ = l_Lean_LocalDecl_fvarId(v_val_3955_);
lean_dec(v_val_3955_);
lean_inc(v_mvarId_3929_);
v___x_3962_ = l_Lean_Meta_subst_x3f(v_mvarId_3929_, v___x_3961_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3983_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3983_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3983_ == 0)
{
v___x_3965_ = v___x_3962_;
v_isShared_3966_ = v_isSharedCheck_3983_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3962_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3983_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
if (lean_obj_tag(v_a_3963_) == 1)
{
lean_object* v___x_3968_; 
lean_del_object(v___x_3943_);
lean_dec(v_mvarId_3929_);
lean_inc_ref(v_a_3963_);
if (v_isShared_3958_ == 0)
{
lean_ctor_set(v___x_3957_, 0, v_a_3963_);
v___x_3968_ = v___x_3957_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3980_; 
v_isSharedCheck_3980_ = !lean_is_exclusive(v_a_3963_);
if (v_isSharedCheck_3980_ == 0)
{
lean_object* v_unused_3981_; 
v_unused_3981_ = lean_ctor_get(v_a_3963_, 0);
lean_dec(v_unused_3981_);
v___x_3970_ = v_a_3963_;
v_isShared_3971_ = v_isSharedCheck_3980_;
goto v_resetjp_3969_;
}
else
{
lean_dec(v_a_3963_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3980_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; lean_object* v___x_3974_; 
v___x_3972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3968_);
lean_ctor_set(v___x_3972_, 1, v___x_3959_);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v___x_3972_);
v___x_3974_ = v___x_3970_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___x_3972_);
v___x_3974_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
lean_object* v___x_3975_; lean_object* v___x_3977_; 
v___x_3975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3975_, 0, v___x_3974_);
lean_ctor_set(v___x_3975_, 1, v_snd_3941_);
if (v_isShared_3966_ == 0)
{
lean_ctor_set(v___x_3965_, 0, v___x_3975_);
v___x_3977_ = v___x_3965_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v___x_3975_);
v___x_3977_ = v_reuseFailAlloc_3978_;
goto v_reusejp_3976_;
}
v_reusejp_3976_:
{
return v___x_3977_;
}
}
}
}
}
else
{
lean_del_object(v___x_3965_);
lean_dec(v_a_3963_);
lean_del_object(v___x_3957_);
lean_dec(v_snd_3941_);
v_a_3947_ = v___x_3960_;
goto v___jp_3946_;
}
}
}
else
{
lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_del_object(v___x_3957_);
lean_del_object(v___x_3943_);
lean_dec(v_snd_3941_);
lean_dec(v_mvarId_3929_);
v_a_3984_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3962_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_dec(v___x_3962_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
}
}
}
}
}
v___jp_3946_:
{
lean_object* v___x_3949_; 
if (v_isShared_3944_ == 0)
{
lean_ctor_set(v___x_3943_, 1, v_a_3947_);
lean_ctor_set(v___x_3943_, 0, v___x_3945_);
v___x_3949_ = v___x_3943_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3945_);
lean_ctor_set(v_reuseFailAlloc_3953_, 1, v_a_3947_);
v___x_3949_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
size_t v___x_3950_; size_t v___x_3951_; lean_object* v___x_3952_; 
v___x_3950_ = ((size_t)1ULL);
v___x_3951_ = lean_usize_add(v_i_3932_, v___x_3950_);
v___x_3952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3929_, v_as_3930_, v_sz_3931_, v___x_3951_, v___x_3949_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
return v___x_3952_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_3995_, lean_object* v_as_3996_, lean_object* v_sz_3997_, lean_object* v_i_3998_, lean_object* v_b_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
size_t v_sz_boxed_4005_; size_t v_i_boxed_4006_; lean_object* v_res_4007_; 
v_sz_boxed_4005_ = lean_unbox_usize(v_sz_3997_);
lean_dec(v_sz_3997_);
v_i_boxed_4006_ = lean_unbox_usize(v_i_3998_);
lean_dec(v_i_3998_);
v_res_4007_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_3995_, v_as_3996_, v_sz_boxed_4005_, v_i_boxed_4006_, v_b_3999_, v___y_4000_, v___y_4001_, v___y_4002_, v___y_4003_);
lean_dec(v___y_4003_);
lean_dec_ref(v___y_4002_);
lean_dec(v___y_4001_);
lean_dec_ref(v___y_4000_);
lean_dec_ref(v_as_3996_);
return v_res_4007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4008_, lean_object* v_t_4009_, lean_object* v_init_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_root_4016_; lean_object* v_tail_4017_; lean_object* v___x_4018_; 
v_root_4016_ = lean_ctor_get(v_t_4009_, 0);
v_tail_4017_ = lean_ctor_get(v_t_4009_, 1);
lean_inc(v_mvarId_4008_);
lean_inc_ref(v_init_4010_);
v___x_4018_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_4010_, v_mvarId_4008_, v_root_4016_, v_init_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
lean_dec_ref(v_init_4010_);
if (lean_obj_tag(v___x_4018_) == 0)
{
lean_object* v_a_4019_; lean_object* v___x_4021_; uint8_t v_isShared_4022_; uint8_t v_isSharedCheck_4055_; 
v_a_4019_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4021_ = v___x_4018_;
v_isShared_4022_ = v_isSharedCheck_4055_;
goto v_resetjp_4020_;
}
else
{
lean_inc(v_a_4019_);
lean_dec(v___x_4018_);
v___x_4021_ = lean_box(0);
v_isShared_4022_ = v_isSharedCheck_4055_;
goto v_resetjp_4020_;
}
v_resetjp_4020_:
{
if (lean_obj_tag(v_a_4019_) == 0)
{
lean_object* v_a_4023_; lean_object* v___x_4025_; 
lean_dec(v_mvarId_4008_);
v_a_4023_ = lean_ctor_get(v_a_4019_, 0);
lean_inc(v_a_4023_);
lean_dec_ref_known(v_a_4019_, 1);
if (v_isShared_4022_ == 0)
{
lean_ctor_set(v___x_4021_, 0, v_a_4023_);
v___x_4025_ = v___x_4021_;
goto v_reusejp_4024_;
}
else
{
lean_object* v_reuseFailAlloc_4026_; 
v_reuseFailAlloc_4026_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4026_, 0, v_a_4023_);
v___x_4025_ = v_reuseFailAlloc_4026_;
goto v_reusejp_4024_;
}
v_reusejp_4024_:
{
return v___x_4025_;
}
}
else
{
lean_object* v_a_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; size_t v_sz_4030_; size_t v___x_4031_; lean_object* v___x_4032_; 
lean_del_object(v___x_4021_);
v_a_4027_ = lean_ctor_get(v_a_4019_, 0);
lean_inc(v_a_4027_);
lean_dec_ref_known(v_a_4019_, 1);
v___x_4028_ = lean_box(0);
v___x_4029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
lean_ctor_set(v___x_4029_, 1, v_a_4027_);
v_sz_4030_ = lean_array_size(v_tail_4017_);
v___x_4031_ = ((size_t)0ULL);
v___x_4032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4008_, v_tail_4017_, v_sz_4030_, v___x_4031_, v___x_4029_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
if (lean_obj_tag(v___x_4032_) == 0)
{
lean_object* v_a_4033_; lean_object* v___x_4035_; uint8_t v_isShared_4036_; uint8_t v_isSharedCheck_4046_; 
v_a_4033_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4035_ = v___x_4032_;
v_isShared_4036_ = v_isSharedCheck_4046_;
goto v_resetjp_4034_;
}
else
{
lean_inc(v_a_4033_);
lean_dec(v___x_4032_);
v___x_4035_ = lean_box(0);
v_isShared_4036_ = v_isSharedCheck_4046_;
goto v_resetjp_4034_;
}
v_resetjp_4034_:
{
lean_object* v_fst_4037_; 
v_fst_4037_ = lean_ctor_get(v_a_4033_, 0);
if (lean_obj_tag(v_fst_4037_) == 0)
{
lean_object* v_snd_4038_; lean_object* v___x_4040_; 
v_snd_4038_ = lean_ctor_get(v_a_4033_, 1);
lean_inc(v_snd_4038_);
lean_dec(v_a_4033_);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v_snd_4038_);
v___x_4040_ = v___x_4035_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_snd_4038_);
v___x_4040_ = v_reuseFailAlloc_4041_;
goto v_reusejp_4039_;
}
v_reusejp_4039_:
{
return v___x_4040_;
}
}
else
{
lean_object* v_val_4042_; lean_object* v___x_4044_; 
lean_inc_ref(v_fst_4037_);
lean_dec(v_a_4033_);
v_val_4042_ = lean_ctor_get(v_fst_4037_, 0);
lean_inc(v_val_4042_);
lean_dec_ref_known(v_fst_4037_, 1);
if (v_isShared_4036_ == 0)
{
lean_ctor_set(v___x_4035_, 0, v_val_4042_);
v___x_4044_ = v___x_4035_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_val_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
else
{
lean_object* v_a_4047_; lean_object* v___x_4049_; uint8_t v_isShared_4050_; uint8_t v_isSharedCheck_4054_; 
v_a_4047_ = lean_ctor_get(v___x_4032_, 0);
v_isSharedCheck_4054_ = !lean_is_exclusive(v___x_4032_);
if (v_isSharedCheck_4054_ == 0)
{
v___x_4049_ = v___x_4032_;
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
else
{
lean_inc(v_a_4047_);
lean_dec(v___x_4032_);
v___x_4049_ = lean_box(0);
v_isShared_4050_ = v_isSharedCheck_4054_;
goto v_resetjp_4048_;
}
v_resetjp_4048_:
{
lean_object* v___x_4052_; 
if (v_isShared_4050_ == 0)
{
v___x_4052_ = v___x_4049_;
goto v_reusejp_4051_;
}
else
{
lean_object* v_reuseFailAlloc_4053_; 
v_reuseFailAlloc_4053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4053_, 0, v_a_4047_);
v___x_4052_ = v_reuseFailAlloc_4053_;
goto v_reusejp_4051_;
}
v_reusejp_4051_:
{
return v___x_4052_;
}
}
}
}
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4058_; uint8_t v_isShared_4059_; uint8_t v_isSharedCheck_4063_; 
lean_dec(v_mvarId_4008_);
v_a_4056_ = lean_ctor_get(v___x_4018_, 0);
v_isSharedCheck_4063_ = !lean_is_exclusive(v___x_4018_);
if (v_isSharedCheck_4063_ == 0)
{
v___x_4058_ = v___x_4018_;
v_isShared_4059_ = v_isSharedCheck_4063_;
goto v_resetjp_4057_;
}
else
{
lean_inc(v_a_4056_);
lean_dec(v___x_4018_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4064_, lean_object* v_t_4065_, lean_object* v_init_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_){
_start:
{
lean_object* v_res_4072_; 
v_res_4072_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4064_, v_t_4065_, v_init_4066_, v___y_4067_, v___y_4068_, v___y_4069_, v___y_4070_);
lean_dec(v___y_4070_);
lean_dec_ref(v___y_4069_);
lean_dec(v___y_4068_);
lean_dec_ref(v___y_4067_);
lean_dec_ref(v_t_4065_);
return v_res_4072_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4076_, lean_object* v___y_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_){
_start:
{
lean_object* v_lctx_4082_; lean_object* v_decls_4083_; lean_object* v___x_4084_; lean_object* v___x_4085_; lean_object* v___x_4086_; 
v_lctx_4082_ = lean_ctor_get(v___y_4077_, 2);
v_decls_4083_ = lean_ctor_get(v_lctx_4082_, 1);
v___x_4084_ = lean_box(0);
v___x_4085_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4086_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4076_, v_decls_4083_, v___x_4085_, v___y_4077_, v___y_4078_, v___y_4079_, v___y_4080_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4099_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4089_ = v___x_4086_;
v_isShared_4090_ = v_isSharedCheck_4099_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4086_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4099_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v_fst_4091_; 
v_fst_4091_ = lean_ctor_get(v_a_4087_, 0);
lean_inc(v_fst_4091_);
lean_dec(v_a_4087_);
if (lean_obj_tag(v_fst_4091_) == 0)
{
lean_object* v___x_4093_; 
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v___x_4084_);
v___x_4093_ = v___x_4089_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4084_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
return v___x_4093_;
}
}
else
{
lean_object* v_val_4095_; lean_object* v___x_4097_; 
v_val_4095_ = lean_ctor_get(v_fst_4091_, 0);
lean_inc(v_val_4095_);
lean_dec_ref_known(v_fst_4091_, 1);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v_val_4095_);
v___x_4097_ = v___x_4089_;
goto v_reusejp_4096_;
}
else
{
lean_object* v_reuseFailAlloc_4098_; 
v_reuseFailAlloc_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4098_, 0, v_val_4095_);
v___x_4097_ = v_reuseFailAlloc_4098_;
goto v_reusejp_4096_;
}
v_reusejp_4096_:
{
return v___x_4097_;
}
}
}
}
else
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4107_; 
v_a_4100_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4107_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4107_ == 0)
{
v___x_4102_ = v___x_4086_;
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4086_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4107_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v___x_4105_; 
if (v_isShared_4103_ == 0)
{
v___x_4105_ = v___x_4102_;
goto v_reusejp_4104_;
}
else
{
lean_object* v_reuseFailAlloc_4106_; 
v_reuseFailAlloc_4106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4106_, 0, v_a_4100_);
v___x_4105_ = v_reuseFailAlloc_4106_;
goto v_reusejp_4104_;
}
v_reusejp_4104_:
{
return v___x_4105_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4108_, lean_object* v___y_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_){
_start:
{
lean_object* v_res_4114_; 
v_res_4114_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4108_, v___y_4109_, v___y_4110_, v___y_4111_, v___y_4112_);
lean_dec(v___y_4112_);
lean_dec_ref(v___y_4111_);
lean_dec(v___y_4110_);
lean_dec_ref(v___y_4109_);
return v_res_4114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4115_, lean_object* v_a_4116_, lean_object* v_a_4117_, lean_object* v_a_4118_, lean_object* v_a_4119_){
_start:
{
lean_object* v___f_4121_; lean_object* v___x_4122_; 
lean_inc(v_mvarId_4115_);
v___f_4121_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4121_, 0, v_mvarId_4115_);
v___x_4122_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_4115_, v___f_4121_, v_a_4116_, v_a_4117_, v_a_4118_, v_a_4119_);
return v___x_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4123_, lean_object* v_a_4124_, lean_object* v_a_4125_, lean_object* v_a_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4123_, v_a_4124_, v_a_4125_, v_a_4126_, v_a_4127_);
lean_dec(v_a_4127_);
lean_dec_ref(v_a_4126_);
lean_dec(v_a_4125_);
lean_dec_ref(v_a_4124_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v___x_4136_; 
lean_inc(v_mvarId_4130_);
v___x_4136_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4130_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4146_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4139_ = v___x_4136_;
v_isShared_4140_ = v_isSharedCheck_4146_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_a_4137_);
lean_dec(v___x_4136_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4146_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
if (lean_obj_tag(v_a_4137_) == 1)
{
lean_object* v_val_4141_; 
lean_del_object(v___x_4139_);
lean_dec(v_mvarId_4130_);
v_val_4141_ = lean_ctor_get(v_a_4137_, 0);
lean_inc(v_val_4141_);
lean_dec_ref_known(v_a_4137_, 1);
v_mvarId_4130_ = v_val_4141_;
goto _start;
}
else
{
lean_object* v___x_4144_; 
lean_dec(v_a_4137_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v_mvarId_4130_);
v___x_4144_ = v___x_4139_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v_mvarId_4130_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
else
{
lean_object* v_a_4147_; lean_object* v___x_4149_; uint8_t v_isShared_4150_; uint8_t v_isSharedCheck_4154_; 
lean_dec(v_mvarId_4130_);
v_a_4147_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4154_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4154_ == 0)
{
v___x_4149_ = v___x_4136_;
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
else
{
lean_inc(v_a_4147_);
lean_dec(v___x_4136_);
v___x_4149_ = lean_box(0);
v_isShared_4150_ = v_isSharedCheck_4154_;
goto v_resetjp_4148_;
}
v_resetjp_4148_:
{
lean_object* v___x_4152_; 
if (v_isShared_4150_ == 0)
{
v___x_4152_ = v___x_4149_;
goto v_reusejp_4151_;
}
else
{
lean_object* v_reuseFailAlloc_4153_; 
v_reuseFailAlloc_4153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4153_, 0, v_a_4147_);
v___x_4152_ = v_reuseFailAlloc_4153_;
goto v_reusejp_4151_;
}
v_reusejp_4151_:
{
return v___x_4152_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_, lean_object* v_a_4159_, lean_object* v_a_4160_){
_start:
{
lean_object* v_res_4161_; 
v_res_4161_ = l_Lean_Meta_substVars(v_mvarId_4155_, v_a_4156_, v_a_4157_, v_a_4158_, v_a_4159_);
lean_dec(v_a_4159_);
lean_dec_ref(v_a_4158_);
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
return v_res_4161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4224_; uint8_t v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; 
v___x_4224_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_4225_ = 0;
v___x_4226_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4227_ = l_Lean_registerTraceClass(v___x_4224_, v___x_4225_, v___x_4226_);
return v___x_4227_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4229_;
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
