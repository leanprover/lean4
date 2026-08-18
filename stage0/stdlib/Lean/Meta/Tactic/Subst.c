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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__0 = (const lean_object*)&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__0_value;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2;
static lean_once_cell_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_substCore___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_substCore___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_substCore___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_substCore___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_substCore___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_substCore___lam__0___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "after intro rest "};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__0 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__0_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__1;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__2 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__2_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__3;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Lean.Meta.Tactic.Subst"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__4 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__4_value;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.substCore"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__5 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__5_value;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__6 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__6_value;
static lean_once_cell_t l_Lean_Meta_substCore___lam__2___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_substCore___lam__2___closed__7;
static const lean_string_object l_Lean_Meta_substCore___lam__2___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_h"};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__8 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__8_value;
static const lean_ctor_object l_Lean_Meta_substCore___lam__2___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_substCore___lam__2___closed__8_value),LEAN_SCALAR_PTR_LITERAL(32, 79, 207, 54, 208, 114, 216, 130)}};
static const lean_object* l_Lean_Meta_substCore___lam__2___closed__9 = (const lean_object*)&l_Lean_Meta_substCore___lam__2___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object**);
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
static const lean_closure_object l_Lean_Meta_substCore___lam__3___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_substCore___lam__0___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Meta_substCore___lam__3___closed__22_value)} };
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
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__1(lean_object* v_msg_45_, lean_object* v___y_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_){
_start:
{
lean_object* v___f_51_; lean_object* v___x_28777__overap_52_; lean_object* v___x_53_; 
v___f_51_ = ((lean_object*)(l_panic___at___00Lean_Meta_substCore_spec__1___closed__0));
v___x_28777__overap_52_ = lean_panic_fn_borrowed(v___f_51_, v_msg_45_);
lean_inc(v___y_49_);
lean_inc_ref(v___y_48_);
lean_inc(v___y_47_);
lean_inc_ref(v___y_46_);
v___x_53_ = lean_apply_5(v___x_28777__overap_52_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, lean_box(0));
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__1___boxed(lean_object* v_msg_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_panic___at___00Lean_Meta_substCore_spec__1(v_msg_54_, v___y_55_, v___y_56_, v___y_57_, v___y_58_);
lean_dec(v___y_58_);
lean_dec_ref(v___y_57_);
lean_dec(v___y_56_);
lean_dec_ref(v___y_55_);
return v_res_60_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__0(lean_object* v_x_61_){
_start:
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_63_){
_start:
{
uint8_t v_res_64_; lean_object* v_r_65_; 
v_res_64_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__0(v_x_63_);
lean_dec(v_x_63_);
v_r_65_ = lean_box(v_res_64_);
return v_r_65_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1(lean_object* v_fvarId_66_, lean_object* v_x_67_){
_start:
{
uint8_t v___x_68_; 
v___x_68_ = l_Lean_instBEqFVarId_beq(v_fvarId_66_, v_x_67_);
return v___x_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1___boxed(lean_object* v_fvarId_69_, lean_object* v_x_70_){
_start:
{
uint8_t v_res_71_; lean_object* v_r_72_; 
v_res_71_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1(v_fvarId_69_, v_x_70_);
lean_dec(v_x_70_);
lean_dec(v_fvarId_69_);
v_r_72_ = lean_box(v_res_71_);
return v_r_72_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v_cellCount_74_; lean_object* v___x_75_; 
v_cellCount_74_ = lean_unsigned_to_nat(16u);
v___x_75_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_74_);
return v___x_75_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v_cellCount_76_; lean_object* v___x_77_; 
v_cellCount_76_ = lean_unsigned_to_nat(16u);
v___x_77_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__3(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_78_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2);
v___x_79_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1);
v___x_80_ = lean_unsigned_to_nat(0u);
v___x_81_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
lean_ctor_set(v___x_81_, 1, v___x_79_);
lean_ctor_set(v___x_81_, 2, v___x_78_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(lean_object* v_e_82_, lean_object* v_fvarId_83_, lean_object* v___y_84_){
_start:
{
lean_object* v___x_86_; uint8_t v_fst_88_; lean_object* v_mctx_89_; lean_object* v___y_107_; lean_object* v_mctx_112_; lean_object* v___f_113_; lean_object* v___f_114_; lean_object* v___x_115_; lean_object* v___x_116_; uint8_t v___x_117_; 
v___x_86_ = lean_st_ref_get(v___y_84_);
v_mctx_112_ = lean_ctor_get(v___x_86_, 0);
lean_inc_ref_n(v_mctx_112_, 2);
lean_dec(v___x_86_);
v___f_113_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__0));
v___f_114_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_114_, 0, v_fvarId_83_);
v___x_115_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__3, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__3_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__3);
v___x_116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_116_, 0, v___x_115_);
lean_ctor_set(v___x_116_, 1, v_mctx_112_);
v___x_117_ = l_Lean_Expr_hasFVar(v_e_82_);
if (v___x_117_ == 0)
{
uint8_t v___x_118_; 
v___x_118_ = l_Lean_Expr_hasMVar(v_e_82_);
if (v___x_118_ == 0)
{
lean_dec_ref_known(v___x_116_, 2);
lean_dec_ref(v___f_114_);
lean_dec_ref(v_e_82_);
v_fst_88_ = v___x_118_;
v_mctx_89_ = v_mctx_112_;
goto v___jp_87_;
}
else
{
lean_object* v___x_119_; 
lean_dec_ref(v_mctx_112_);
v___x_119_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_114_, v___f_113_, v_e_82_, v___x_116_);
v___y_107_ = v___x_119_;
goto v___jp_106_;
}
}
else
{
lean_object* v___x_120_; 
lean_dec_ref(v_mctx_112_);
v___x_120_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_114_, v___f_113_, v_e_82_, v___x_116_);
v___y_107_ = v___x_120_;
goto v___jp_106_;
}
v___jp_87_:
{
lean_object* v___x_90_; lean_object* v_cache_91_; lean_object* v_zetaDeltaFVarIds_92_; lean_object* v_postponed_93_; lean_object* v_diag_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_104_; 
v___x_90_ = lean_st_ref_take(v___y_84_);
v_cache_91_ = lean_ctor_get(v___x_90_, 1);
v_zetaDeltaFVarIds_92_ = lean_ctor_get(v___x_90_, 2);
v_postponed_93_ = lean_ctor_get(v___x_90_, 3);
v_diag_94_ = lean_ctor_get(v___x_90_, 4);
v_isSharedCheck_104_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v___x_90_, 0);
lean_dec(v_unused_105_);
v___x_96_ = v___x_90_;
v_isShared_97_ = v_isSharedCheck_104_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_diag_94_);
lean_inc(v_postponed_93_);
lean_inc(v_zetaDeltaFVarIds_92_);
lean_inc(v_cache_91_);
lean_dec(v___x_90_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_104_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v_mctx_89_);
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_mctx_89_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_cache_91_);
lean_ctor_set(v_reuseFailAlloc_103_, 2, v_zetaDeltaFVarIds_92_);
lean_ctor_set(v_reuseFailAlloc_103_, 3, v_postponed_93_);
lean_ctor_set(v_reuseFailAlloc_103_, 4, v_diag_94_);
v___x_99_ = v_reuseFailAlloc_103_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_100_ = lean_st_ref_put(v___y_84_, v___x_99_);
v___x_101_ = lean_box(v_fst_88_);
v___x_102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
return v___x_102_;
}
}
}
v___jp_106_:
{
lean_object* v_snd_108_; lean_object* v_fst_109_; lean_object* v_mctx_110_; uint8_t v___x_111_; 
v_snd_108_ = lean_ctor_get(v___y_107_, 1);
lean_inc(v_snd_108_);
v_fst_109_ = lean_ctor_get(v___y_107_, 0);
lean_inc(v_fst_109_);
lean_dec_ref(v___y_107_);
v_mctx_110_ = lean_ctor_get(v_snd_108_, 1);
lean_inc_ref(v_mctx_110_);
lean_dec(v_snd_108_);
v___x_111_ = lean_unbox(v_fst_109_);
lean_dec(v_fst_109_);
v_fst_88_ = v___x_111_;
v_mctx_89_ = v_mctx_110_;
goto v___jp_87_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___boxed(lean_object* v_e_121_, lean_object* v_fvarId_122_, lean_object* v___y_123_, lean_object* v___y_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_e_121_, v_fvarId_122_, v___y_123_);
lean_dec(v___y_123_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4(lean_object* v_e_126_, lean_object* v_fvarId_127_, lean_object* v___y_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_){
_start:
{
lean_object* v___x_133_; 
v___x_133_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_e_126_, v_fvarId_127_, v___y_129_);
return v___x_133_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___boxed(lean_object* v_e_134_, lean_object* v_fvarId_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_){
_start:
{
lean_object* v_res_141_; 
v_res_141_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4(v_e_134_, v_fvarId_135_, v___y_136_, v___y_137_, v___y_138_, v___y_139_);
lean_dec(v___y_139_);
lean_dec_ref(v___y_138_);
lean_dec(v___y_137_);
lean_dec_ref(v___y_136_);
return v_res_141_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(lean_object* v_mvarId_142_, lean_object* v_x_143_, lean_object* v___y_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_){
_start:
{
lean_object* v___x_149_; 
v___x_149_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_142_, v_x_143_, v___y_144_, v___y_145_, v___y_146_, v___y_147_);
if (lean_obj_tag(v___x_149_) == 0)
{
lean_object* v_a_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_157_; 
v_a_150_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_157_ == 0)
{
v___x_152_ = v___x_149_;
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_a_150_);
lean_dec(v___x_149_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_157_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_155_; 
if (v_isShared_153_ == 0)
{
v___x_155_ = v___x_152_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v_a_150_);
v___x_155_ = v_reuseFailAlloc_156_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
return v___x_155_;
}
}
}
else
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_165_; 
v_a_158_ = lean_ctor_get(v___x_149_, 0);
v_isSharedCheck_165_ = !lean_is_exclusive(v___x_149_);
if (v_isSharedCheck_165_ == 0)
{
v___x_160_ = v___x_149_;
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_149_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_165_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_163_; 
if (v_isShared_161_ == 0)
{
v___x_163_ = v___x_160_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
v___x_163_ = v_reuseFailAlloc_164_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
return v___x_163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg___boxed(lean_object* v_mvarId_166_, lean_object* v_x_167_, lean_object* v___y_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v_res_173_; 
v_res_173_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_166_, v_x_167_, v___y_168_, v___y_169_, v___y_170_, v___y_171_);
lean_dec(v___y_171_);
lean_dec_ref(v___y_170_);
lean_dec(v___y_169_);
lean_dec_ref(v___y_168_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(lean_object* v_00_u03b1_174_, lean_object* v_mvarId_175_, lean_object* v_x_176_, lean_object* v___y_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_175_, v_x_176_, v___y_177_, v___y_178_, v___y_179_, v___y_180_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed(lean_object* v_00_u03b1_183_, lean_object* v_mvarId_184_, lean_object* v_x_185_, lean_object* v___y_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(v_00_u03b1_183_, v_mvarId_184_, v_x_185_, v___y_186_, v___y_187_, v___y_188_, v___y_189_);
lean_dec(v___y_189_);
lean_dec_ref(v___y_188_);
lean_dec(v___y_187_);
lean_dec_ref(v___y_186_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0(lean_object* v___x_195_, lean_object* v___y_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_options_201_; uint8_t v_hasTrace_202_; 
v_options_201_ = lean_ctor_get(v___y_198_, 2);
v_hasTrace_202_ = lean_ctor_get_uint8(v_options_201_, sizeof(void*)*1);
if (v_hasTrace_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v___x_195_);
v___x_203_ = lean_box(v_hasTrace_202_);
v___x_204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
return v___x_204_;
}
else
{
lean_object* v_inheritedTraceOptions_205_; lean_object* v___x_206_; lean_object* v___x_207_; uint8_t v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; 
v_inheritedTraceOptions_205_ = lean_ctor_get(v___y_198_, 13);
v___x_206_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
v___x_207_ = l_Lean_Name_append(v___x_206_, v___x_195_);
v___x_208_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_205_, v_options_201_, v___x_207_);
lean_dec(v___x_207_);
v___x_209_ = lean_box(v___x_208_);
v___x_210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
return v___x_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object* v___x_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_Lean_Meta_substCore___lam__0(v___x_211_, v___y_212_, v___y_213_, v___y_214_, v___y_215_);
lean_dec(v___y_215_);
lean_dec_ref(v___y_214_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object* v_type_218_, lean_object* v___x_219_, lean_object* v___x_220_, lean_object* v___x_221_, uint8_t v___x_222_, uint8_t v___x_223_, lean_object* v_hAux_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v___x_230_; 
lean_inc_ref(v_hAux_224_);
v___x_230_ = l_Lean_Meta_mkEqSymm(v_hAux_224_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
if (lean_obj_tag(v___x_230_) == 0)
{
lean_object* v_a_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; uint8_t v___x_236_; lean_object* v___x_237_; 
v_a_231_ = lean_ctor_get(v___x_230_, 0);
lean_inc(v_a_231_);
lean_dec_ref_known(v___x_230_, 1);
v___x_232_ = l_Lean_Expr_replaceFVar(v_type_218_, v___x_219_, v_a_231_);
lean_dec(v_a_231_);
v___x_233_ = lean_mk_empty_array_with_capacity(v___x_220_);
v___x_234_ = lean_array_push(v___x_233_, v___x_221_);
v___x_235_ = lean_array_push(v___x_234_, v_hAux_224_);
v___x_236_ = 1;
v___x_237_ = l_Lean_Meta_mkLambdaFVars(v___x_235_, v___x_232_, v___x_222_, v___x_223_, v___x_222_, v___x_223_, v___x_236_, v___y_225_, v___y_226_, v___y_227_, v___y_228_);
lean_dec_ref(v___x_235_);
return v___x_237_;
}
else
{
lean_dec_ref(v_hAux_224_);
lean_dec_ref(v___x_221_);
lean_dec_ref(v___x_219_);
return v___x_230_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object* v_type_238_, lean_object* v___x_239_, lean_object* v___x_240_, lean_object* v___x_241_, lean_object* v___x_242_, lean_object* v___x_243_, lean_object* v_hAux_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_){
_start:
{
uint8_t v___x_33174__boxed_250_; uint8_t v___x_33175__boxed_251_; lean_object* v_res_252_; 
v___x_33174__boxed_250_ = lean_unbox(v___x_242_);
v___x_33175__boxed_251_ = lean_unbox(v___x_243_);
v_res_252_ = l_Lean_Meta_substCore___lam__1(v_type_238_, v___x_239_, v___x_240_, v___x_241_, v___x_33174__boxed_250_, v___x_33175__boxed_251_, v_hAux_244_, v___y_245_, v___y_246_, v___y_247_, v___y_248_);
lean_dec(v___y_248_);
lean_dec_ref(v___y_247_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___x_240_);
lean_dec_ref(v_type_238_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0(lean_object* v_k_253_, lean_object* v_b_254_, lean_object* v___y_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_){
_start:
{
lean_object* v___x_260_; 
lean_inc(v___y_258_);
lean_inc_ref(v___y_257_);
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
v___x_260_ = lean_apply_6(v_k_253_, v_b_254_, v___y_255_, v___y_256_, v___y_257_, v___y_258_, lean_box(0));
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_261_, lean_object* v_b_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0(v_k_261_, v_b_262_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(lean_object* v_name_269_, uint8_t v_bi_270_, lean_object* v_type_271_, lean_object* v_k_272_, uint8_t v_kind_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
lean_object* v___f_279_; lean_object* v___x_280_; 
v___f_279_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_279_, 0, v_k_272_);
v___x_280_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_269_, v_bi_270_, v_type_271_, v___f_279_, v_kind_273_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
if (lean_obj_tag(v___x_280_) == 0)
{
lean_object* v_a_281_; lean_object* v___x_283_; uint8_t v_isShared_284_; uint8_t v_isSharedCheck_288_; 
v_a_281_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_288_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_288_ == 0)
{
v___x_283_ = v___x_280_;
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
else
{
lean_inc(v_a_281_);
lean_dec(v___x_280_);
v___x_283_ = lean_box(0);
v_isShared_284_ = v_isSharedCheck_288_;
goto v_resetjp_282_;
}
v_resetjp_282_:
{
lean_object* v___x_286_; 
if (v_isShared_284_ == 0)
{
v___x_286_ = v___x_283_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_287_; 
v_reuseFailAlloc_287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_287_, 0, v_a_281_);
v___x_286_ = v_reuseFailAlloc_287_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
return v___x_286_;
}
}
}
else
{
lean_object* v_a_289_; lean_object* v___x_291_; uint8_t v_isShared_292_; uint8_t v_isSharedCheck_296_; 
v_a_289_ = lean_ctor_get(v___x_280_, 0);
v_isSharedCheck_296_ = !lean_is_exclusive(v___x_280_);
if (v_isSharedCheck_296_ == 0)
{
v___x_291_ = v___x_280_;
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
else
{
lean_inc(v_a_289_);
lean_dec(v___x_280_);
v___x_291_ = lean_box(0);
v_isShared_292_ = v_isSharedCheck_296_;
goto v_resetjp_290_;
}
v_resetjp_290_:
{
lean_object* v___x_294_; 
if (v_isShared_292_ == 0)
{
v___x_294_ = v___x_291_;
goto v_reusejp_293_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v_a_289_);
v___x_294_ = v_reuseFailAlloc_295_;
goto v_reusejp_293_;
}
v_reusejp_293_:
{
return v___x_294_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___boxed(lean_object* v_name_297_, lean_object* v_bi_298_, lean_object* v_type_299_, lean_object* v_k_300_, lean_object* v_kind_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_){
_start:
{
uint8_t v_bi_boxed_307_; uint8_t v_kind_boxed_308_; lean_object* v_res_309_; 
v_bi_boxed_307_ = lean_unbox(v_bi_298_);
v_kind_boxed_308_ = lean_unbox(v_kind_301_);
v_res_309_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_297_, v_bi_boxed_307_, v_type_299_, v_k_300_, v_kind_boxed_308_, v___y_302_, v___y_303_, v___y_304_, v___y_305_);
lean_dec(v___y_305_);
lean_dec_ref(v___y_304_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
return v_res_309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(lean_object* v_name_310_, lean_object* v_type_311_, lean_object* v_k_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
uint8_t v___x_318_; uint8_t v___x_319_; lean_object* v___x_320_; 
v___x_318_ = 0;
v___x_319_ = 0;
v___x_320_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_310_, v___x_318_, v_type_311_, v_k_312_, v___x_319_, v___y_313_, v___y_314_, v___y_315_, v___y_316_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg___boxed(lean_object* v_name_321_, lean_object* v_type_322_, lean_object* v_k_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v_name_321_, v_type_322_, v_k_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_);
lean_dec(v___y_327_);
lean_dec_ref(v___y_326_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
return v_res_329_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(lean_object* v_fst_330_, lean_object* v_fst_331_, lean_object* v_n_332_, lean_object* v_i_333_, lean_object* v_a_334_){
_start:
{
lean_object* v_zero_336_; uint8_t v_isZero_337_; 
v_zero_336_ = lean_unsigned_to_nat(0u);
v_isZero_337_ = lean_nat_dec_eq(v_i_333_, v_zero_336_);
if (v_isZero_337_ == 1)
{
lean_object* v___x_338_; 
lean_dec(v_i_333_);
v___x_338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_338_, 0, v_a_334_);
return v___x_338_;
}
else
{
lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v_one_341_; lean_object* v_n_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_339_ = lean_unsigned_to_nat(2u);
v___x_340_ = lean_box(0);
v_one_341_ = lean_unsigned_to_nat(1u);
v_n_342_ = lean_nat_sub(v_i_333_, v_one_341_);
lean_dec(v_i_333_);
v___x_343_ = lean_nat_sub(v_n_332_, v_n_342_);
v___x_344_ = lean_nat_sub(v___x_343_, v_one_341_);
lean_dec(v___x_343_);
v___x_345_ = lean_nat_add(v___x_344_, v___x_339_);
v___x_346_ = lean_array_get_borrowed(v___x_340_, v_fst_330_, v___x_345_);
lean_dec(v___x_345_);
v___x_347_ = lean_array_fget_borrowed(v_fst_331_, v___x_344_);
lean_dec(v___x_344_);
lean_inc(v___x_347_);
v___x_348_ = l_Lean_mkFVar(v___x_347_);
lean_inc(v___x_346_);
v___x_349_ = l_Lean_Meta_FVarSubst_insert(v_a_334_, v___x_346_, v___x_348_);
v_i_333_ = v_n_342_;
v_a_334_ = v___x_349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg___boxed(lean_object* v_fst_351_, lean_object* v_fst_352_, lean_object* v_n_353_, lean_object* v_i_354_, lean_object* v_a_355_, lean_object* v___y_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_351_, v_fst_352_, v_n_353_, v_i_354_, v_a_355_);
lean_dec(v_n_353_);
lean_dec_ref(v_fst_352_);
lean_dec_ref(v_fst_351_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(lean_object* v_msgData_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_){
_start:
{
lean_object* v___x_364_; lean_object* v_env_365_; lean_object* v___x_366_; lean_object* v_mctx_367_; lean_object* v_lctx_368_; lean_object* v_options_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; 
v___x_364_ = lean_st_ref_get(v___y_362_);
v_env_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_env_365_);
lean_dec(v___x_364_);
v___x_366_ = lean_st_ref_get(v___y_360_);
v_mctx_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc_ref(v_mctx_367_);
lean_dec(v___x_366_);
v_lctx_368_ = lean_ctor_get(v___y_359_, 2);
v_options_369_ = lean_ctor_get(v___y_361_, 2);
lean_inc_ref(v_options_369_);
lean_inc_ref(v_lctx_368_);
v___x_370_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_370_, 0, v_env_365_);
lean_ctor_set(v___x_370_, 1, v_mctx_367_);
lean_ctor_set(v___x_370_, 2, v_lctx_368_);
lean_ctor_set(v___x_370_, 3, v_options_369_);
v___x_371_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_371_, 0, v___x_370_);
lean_ctor_set(v___x_371_, 1, v_msgData_358_);
v___x_372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3___boxed(lean_object* v_msgData_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msgData_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
return v_res_379_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0(void){
_start:
{
lean_object* v___x_380_; double v___x_381_; 
v___x_380_ = lean_unsigned_to_nat(0u);
v___x_381_ = lean_float_of_nat(v___x_380_);
return v___x_381_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(lean_object* v_cls_385_, lean_object* v_msg_386_, lean_object* v___y_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_){
_start:
{
lean_object* v_ref_392_; lean_object* v___x_393_; lean_object* v_a_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_438_; 
v_ref_392_ = lean_ctor_get(v___y_389_, 5);
v___x_393_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msg_386_, v___y_387_, v___y_388_, v___y_389_, v___y_390_);
v_a_394_ = lean_ctor_get(v___x_393_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_393_);
if (v_isSharedCheck_438_ == 0)
{
v___x_396_ = v___x_393_;
v_isShared_397_ = v_isSharedCheck_438_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_a_394_);
lean_dec(v___x_393_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_438_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v_traceState_399_; lean_object* v_env_400_; lean_object* v_nextMacroScope_401_; lean_object* v_ngen_402_; lean_object* v_auxDeclNGen_403_; lean_object* v_cache_404_; lean_object* v_messages_405_; lean_object* v_infoState_406_; lean_object* v_snapshotTasks_407_; lean_object* v___x_409_; uint8_t v_isShared_410_; uint8_t v_isSharedCheck_437_; 
v___x_398_ = lean_st_ref_take(v___y_390_);
v_traceState_399_ = lean_ctor_get(v___x_398_, 4);
v_env_400_ = lean_ctor_get(v___x_398_, 0);
v_nextMacroScope_401_ = lean_ctor_get(v___x_398_, 1);
v_ngen_402_ = lean_ctor_get(v___x_398_, 2);
v_auxDeclNGen_403_ = lean_ctor_get(v___x_398_, 3);
v_cache_404_ = lean_ctor_get(v___x_398_, 5);
v_messages_405_ = lean_ctor_get(v___x_398_, 6);
v_infoState_406_ = lean_ctor_get(v___x_398_, 7);
v_snapshotTasks_407_ = lean_ctor_get(v___x_398_, 8);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_398_);
if (v_isSharedCheck_437_ == 0)
{
v___x_409_ = v___x_398_;
v_isShared_410_ = v_isSharedCheck_437_;
goto v_resetjp_408_;
}
else
{
lean_inc(v_snapshotTasks_407_);
lean_inc(v_infoState_406_);
lean_inc(v_messages_405_);
lean_inc(v_cache_404_);
lean_inc(v_traceState_399_);
lean_inc(v_auxDeclNGen_403_);
lean_inc(v_ngen_402_);
lean_inc(v_nextMacroScope_401_);
lean_inc(v_env_400_);
lean_dec(v___x_398_);
v___x_409_ = lean_box(0);
v_isShared_410_ = v_isSharedCheck_437_;
goto v_resetjp_408_;
}
v_resetjp_408_:
{
uint64_t v_tid_411_; lean_object* v_traces_412_; lean_object* v___x_414_; uint8_t v_isShared_415_; uint8_t v_isSharedCheck_436_; 
v_tid_411_ = lean_ctor_get_uint64(v_traceState_399_, sizeof(void*)*1);
v_traces_412_ = lean_ctor_get(v_traceState_399_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v_traceState_399_);
if (v_isSharedCheck_436_ == 0)
{
v___x_414_ = v_traceState_399_;
v_isShared_415_ = v_isSharedCheck_436_;
goto v_resetjp_413_;
}
else
{
lean_inc(v_traces_412_);
lean_dec(v_traceState_399_);
v___x_414_ = lean_box(0);
v_isShared_415_ = v_isSharedCheck_436_;
goto v_resetjp_413_;
}
v_resetjp_413_:
{
lean_object* v___x_416_; double v___x_417_; uint8_t v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_426_; 
v___x_416_ = lean_box(0);
v___x_417_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0);
v___x_418_ = 0;
v___x_419_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__1));
v___x_420_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_420_, 0, v_cls_385_);
lean_ctor_set(v___x_420_, 1, v___x_416_);
lean_ctor_set(v___x_420_, 2, v___x_419_);
lean_ctor_set_float(v___x_420_, sizeof(void*)*3, v___x_417_);
lean_ctor_set_float(v___x_420_, sizeof(void*)*3 + 8, v___x_417_);
lean_ctor_set_uint8(v___x_420_, sizeof(void*)*3 + 16, v___x_418_);
v___x_421_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__2));
v___x_422_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_422_, 0, v___x_420_);
lean_ctor_set(v___x_422_, 1, v_a_394_);
lean_ctor_set(v___x_422_, 2, v___x_421_);
lean_inc(v_ref_392_);
v___x_423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_423_, 0, v_ref_392_);
lean_ctor_set(v___x_423_, 1, v___x_422_);
v___x_424_ = l_Lean_PersistentArray_push___redArg(v_traces_412_, v___x_423_);
if (v_isShared_415_ == 0)
{
lean_ctor_set(v___x_414_, 0, v___x_424_);
v___x_426_ = v___x_414_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v___x_424_);
lean_ctor_set_uint64(v_reuseFailAlloc_435_, sizeof(void*)*1, v_tid_411_);
v___x_426_ = v_reuseFailAlloc_435_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_428_; 
if (v_isShared_410_ == 0)
{
lean_ctor_set(v___x_409_, 4, v___x_426_);
v___x_428_ = v___x_409_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v_env_400_);
lean_ctor_set(v_reuseFailAlloc_434_, 1, v_nextMacroScope_401_);
lean_ctor_set(v_reuseFailAlloc_434_, 2, v_ngen_402_);
lean_ctor_set(v_reuseFailAlloc_434_, 3, v_auxDeclNGen_403_);
lean_ctor_set(v_reuseFailAlloc_434_, 4, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_434_, 5, v_cache_404_);
lean_ctor_set(v_reuseFailAlloc_434_, 6, v_messages_405_);
lean_ctor_set(v_reuseFailAlloc_434_, 7, v_infoState_406_);
lean_ctor_set(v_reuseFailAlloc_434_, 8, v_snapshotTasks_407_);
v___x_428_ = v_reuseFailAlloc_434_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_432_; 
v___x_429_ = lean_st_ref_put(v___y_390_, v___x_428_);
v___x_430_ = lean_box(0);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 0, v___x_430_);
v___x_432_ = v___x_396_;
goto v_reusejp_431_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_430_);
v___x_432_ = v_reuseFailAlloc_433_;
goto v_reusejp_431_;
}
v_reusejp_431_:
{
return v___x_432_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___boxed(lean_object* v_cls_439_, lean_object* v_msg_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v_cls_439_, v_msg_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_444_);
lean_dec_ref(v___y_443_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_){
_start:
{
lean_object* v_ks_451_; lean_object* v_vs_452_; lean_object* v___x_454_; uint8_t v_isShared_455_; uint8_t v_isSharedCheck_476_; 
v_ks_451_ = lean_ctor_get(v_x_447_, 0);
v_vs_452_ = lean_ctor_get(v_x_447_, 1);
v_isSharedCheck_476_ = !lean_is_exclusive(v_x_447_);
if (v_isSharedCheck_476_ == 0)
{
v___x_454_ = v_x_447_;
v_isShared_455_ = v_isSharedCheck_476_;
goto v_resetjp_453_;
}
else
{
lean_inc(v_vs_452_);
lean_inc(v_ks_451_);
lean_dec(v_x_447_);
v___x_454_ = lean_box(0);
v_isShared_455_ = v_isSharedCheck_476_;
goto v_resetjp_453_;
}
v_resetjp_453_:
{
lean_object* v___x_456_; uint8_t v___x_457_; 
v___x_456_ = lean_array_get_size(v_ks_451_);
v___x_457_ = lean_nat_dec_lt(v_x_448_, v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_461_; 
lean_dec(v_x_448_);
v___x_458_ = lean_array_push(v_ks_451_, v_x_449_);
v___x_459_ = lean_array_push(v_vs_452_, v_x_450_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_459_);
lean_ctor_set(v___x_454_, 0, v___x_458_);
v___x_461_ = v___x_454_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v___x_458_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v___x_459_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
else
{
lean_object* v_k_x27_463_; uint8_t v___x_464_; 
v_k_x27_463_ = lean_array_fget_borrowed(v_ks_451_, v_x_448_);
v___x_464_ = l_Lean_instBEqMVarId_beq(v_x_449_, v_k_x27_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_466_; 
if (v_isShared_455_ == 0)
{
v___x_466_ = v___x_454_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v_ks_451_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v_vs_452_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; lean_object* v___x_468_; 
v___x_467_ = lean_unsigned_to_nat(1u);
v___x_468_ = lean_nat_add(v_x_448_, v___x_467_);
lean_dec(v_x_448_);
v_x_447_ = v___x_466_;
v_x_448_ = v___x_468_;
goto _start;
}
}
else
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_474_; 
v___x_471_ = lean_array_fset(v_ks_451_, v_x_448_, v_x_449_);
v___x_472_ = lean_array_fset(v_vs_452_, v_x_448_, v_x_450_);
lean_dec(v_x_448_);
if (v_isShared_455_ == 0)
{
lean_ctor_set(v___x_454_, 1, v___x_472_);
lean_ctor_set(v___x_454_, 0, v___x_471_);
v___x_474_ = v___x_454_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_475_, 1, v___x_472_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(lean_object* v_n_477_, lean_object* v_k_478_, lean_object* v_v_479_){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(0u);
v___x_481_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(v_n_477_, v___x_480_, v_k_478_, v_v_479_);
return v___x_481_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(lean_object* v_x_483_, size_t v_x_484_, size_t v_x_485_, lean_object* v_x_486_, lean_object* v_x_487_){
_start:
{
if (lean_obj_tag(v_x_483_) == 0)
{
lean_object* v_es_488_; size_t v___x_489_; size_t v___x_490_; lean_object* v_j_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v_es_488_ = lean_ctor_get(v_x_483_, 0);
v___x_489_ = ((size_t)31ULL);
v___x_490_ = lean_usize_land(v_x_484_, v___x_489_);
v_j_491_ = lean_usize_to_nat(v___x_490_);
v___x_492_ = lean_array_get_size(v_es_488_);
v___x_493_ = lean_nat_dec_lt(v_j_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_dec(v_j_491_);
lean_dec(v_x_487_);
lean_dec(v_x_486_);
return v_x_483_;
}
else
{
lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_532_; 
lean_inc_ref(v_es_488_);
v_isSharedCheck_532_ = !lean_is_exclusive(v_x_483_);
if (v_isSharedCheck_532_ == 0)
{
lean_object* v_unused_533_; 
v_unused_533_ = lean_ctor_get(v_x_483_, 0);
lean_dec(v_unused_533_);
v___x_495_ = v_x_483_;
v_isShared_496_ = v_isSharedCheck_532_;
goto v_resetjp_494_;
}
else
{
lean_dec(v_x_483_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_532_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v_v_497_; lean_object* v___x_498_; lean_object* v_xs_x27_499_; lean_object* v___y_501_; 
v_v_497_ = lean_array_fget(v_es_488_, v_j_491_);
v___x_498_ = lean_box(0);
v_xs_x27_499_ = lean_array_fset(v_es_488_, v_j_491_, v___x_498_);
switch(lean_obj_tag(v_v_497_))
{
case 0:
{
lean_object* v_key_506_; lean_object* v_val_507_; lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_517_; 
v_key_506_ = lean_ctor_get(v_v_497_, 0);
v_val_507_ = lean_ctor_get(v_v_497_, 1);
v_isSharedCheck_517_ = !lean_is_exclusive(v_v_497_);
if (v_isSharedCheck_517_ == 0)
{
v___x_509_ = v_v_497_;
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
else
{
lean_inc(v_val_507_);
lean_inc(v_key_506_);
lean_dec(v_v_497_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_517_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
uint8_t v___x_511_; 
v___x_511_ = l_Lean_instBEqMVarId_beq(v_x_486_, v_key_506_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_del_object(v___x_509_);
v___x_512_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_506_, v_val_507_, v_x_486_, v_x_487_);
v___x_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
v___y_501_ = v___x_513_;
goto v___jp_500_;
}
else
{
lean_object* v___x_515_; 
lean_dec(v_val_507_);
lean_dec(v_key_506_);
if (v_isShared_510_ == 0)
{
lean_ctor_set(v___x_509_, 1, v_x_487_);
lean_ctor_set(v___x_509_, 0, v_x_486_);
v___x_515_ = v___x_509_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_516_; 
v_reuseFailAlloc_516_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_516_, 0, v_x_486_);
lean_ctor_set(v_reuseFailAlloc_516_, 1, v_x_487_);
v___x_515_ = v_reuseFailAlloc_516_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
v___y_501_ = v___x_515_;
goto v___jp_500_;
}
}
}
}
case 1:
{
lean_object* v_node_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_530_; 
v_node_518_ = lean_ctor_get(v_v_497_, 0);
v_isSharedCheck_530_ = !lean_is_exclusive(v_v_497_);
if (v_isSharedCheck_530_ == 0)
{
v___x_520_ = v_v_497_;
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_node_518_);
lean_dec(v_v_497_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_530_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
size_t v___x_522_; size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; lean_object* v___x_526_; lean_object* v___x_528_; 
v___x_522_ = ((size_t)5ULL);
v___x_523_ = lean_usize_shift_right(v_x_484_, v___x_522_);
v___x_524_ = ((size_t)1ULL);
v___x_525_ = lean_usize_add(v_x_485_, v___x_524_);
v___x_526_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_node_518_, v___x_523_, v___x_525_, v_x_486_, v_x_487_);
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v___x_526_);
v___x_528_ = v___x_520_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_529_; 
v_reuseFailAlloc_529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_529_, 0, v___x_526_);
v___x_528_ = v_reuseFailAlloc_529_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
v___y_501_ = v___x_528_;
goto v___jp_500_;
}
}
}
default: 
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_x_486_);
lean_ctor_set(v___x_531_, 1, v_x_487_);
v___y_501_ = v___x_531_;
goto v___jp_500_;
}
}
v___jp_500_:
{
lean_object* v___x_502_; lean_object* v___x_504_; 
v___x_502_ = lean_array_fset(v_xs_x27_499_, v_j_491_, v___y_501_);
lean_dec(v_j_491_);
if (v_isShared_496_ == 0)
{
lean_ctor_set(v___x_495_, 0, v___x_502_);
v___x_504_ = v___x_495_;
goto v_reusejp_503_;
}
else
{
lean_object* v_reuseFailAlloc_505_; 
v_reuseFailAlloc_505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_505_, 0, v___x_502_);
v___x_504_ = v_reuseFailAlloc_505_;
goto v_reusejp_503_;
}
v_reusejp_503_:
{
return v___x_504_;
}
}
}
}
}
else
{
lean_object* v_ks_534_; lean_object* v_vs_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_555_; 
v_ks_534_ = lean_ctor_get(v_x_483_, 0);
v_vs_535_ = lean_ctor_get(v_x_483_, 1);
v_isSharedCheck_555_ = !lean_is_exclusive(v_x_483_);
if (v_isSharedCheck_555_ == 0)
{
v___x_537_ = v_x_483_;
v_isShared_538_ = v_isSharedCheck_555_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_vs_535_);
lean_inc(v_ks_534_);
lean_dec(v_x_483_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_555_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_ks_534_);
lean_ctor_set(v_reuseFailAlloc_554_, 1, v_vs_535_);
v___x_540_ = v_reuseFailAlloc_554_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
lean_object* v_newNode_541_; uint8_t v___y_543_; size_t v___x_549_; uint8_t v___x_550_; 
v_newNode_541_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v___x_540_, v_x_486_, v_x_487_);
v___x_549_ = ((size_t)7ULL);
v___x_550_ = lean_usize_dec_le(v___x_549_, v_x_485_);
if (v___x_550_ == 0)
{
lean_object* v___x_551_; lean_object* v___x_552_; uint8_t v___x_553_; 
v___x_551_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_541_);
v___x_552_ = lean_unsigned_to_nat(4u);
v___x_553_ = lean_nat_dec_lt(v___x_551_, v___x_552_);
lean_dec(v___x_551_);
v___y_543_ = v___x_553_;
goto v___jp_542_;
}
else
{
v___y_543_ = v___x_550_;
goto v___jp_542_;
}
v___jp_542_:
{
if (v___y_543_ == 0)
{
lean_object* v_ks_544_; lean_object* v_vs_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; 
v_ks_544_ = lean_ctor_get(v_newNode_541_, 0);
lean_inc_ref(v_ks_544_);
v_vs_545_ = lean_ctor_get(v_newNode_541_, 1);
lean_inc_ref(v_vs_545_);
lean_dec_ref(v_newNode_541_);
v___x_546_ = lean_unsigned_to_nat(0u);
v___x_547_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0);
v___x_548_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_x_485_, v_ks_544_, v_vs_545_, v___x_546_, v___x_547_);
lean_dec_ref(v_vs_545_);
lean_dec_ref(v_ks_544_);
return v___x_548_;
}
else
{
return v_newNode_541_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(size_t v_depth_556_, lean_object* v_keys_557_, lean_object* v_vals_558_, lean_object* v_i_559_, lean_object* v_entries_560_){
_start:
{
lean_object* v___x_561_; uint8_t v___x_562_; 
v___x_561_ = lean_array_get_size(v_keys_557_);
v___x_562_ = lean_nat_dec_lt(v_i_559_, v___x_561_);
if (v___x_562_ == 0)
{
lean_dec(v_i_559_);
return v_entries_560_;
}
else
{
lean_object* v_k_563_; lean_object* v_v_564_; uint64_t v___x_565_; size_t v_h_566_; size_t v___x_567_; lean_object* v___x_568_; size_t v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v_h_572_; lean_object* v___x_573_; lean_object* v___x_574_; 
v_k_563_ = lean_array_fget_borrowed(v_keys_557_, v_i_559_);
v_v_564_ = lean_array_fget_borrowed(v_vals_558_, v_i_559_);
v___x_565_ = l_Lean_instHashableMVarId_hash(v_k_563_);
v_h_566_ = lean_uint64_to_usize(v___x_565_);
v___x_567_ = ((size_t)5ULL);
v___x_568_ = lean_unsigned_to_nat(1u);
v___x_569_ = ((size_t)1ULL);
v___x_570_ = lean_usize_sub(v_depth_556_, v___x_569_);
v___x_571_ = lean_usize_mul(v___x_567_, v___x_570_);
v_h_572_ = lean_usize_shift_right(v_h_566_, v___x_571_);
v___x_573_ = lean_nat_add(v_i_559_, v___x_568_);
lean_dec(v_i_559_);
lean_inc(v_v_564_);
lean_inc(v_k_563_);
v___x_574_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_entries_560_, v_h_572_, v_depth_556_, v_k_563_, v_v_564_);
v_i_559_ = v___x_573_;
v_entries_560_ = v___x_574_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_depth_576_, lean_object* v_keys_577_, lean_object* v_vals_578_, lean_object* v_i_579_, lean_object* v_entries_580_){
_start:
{
size_t v_depth_boxed_581_; lean_object* v_res_582_; 
v_depth_boxed_581_ = lean_unbox_usize(v_depth_576_);
lean_dec(v_depth_576_);
v_res_582_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_boxed_581_, v_keys_577_, v_vals_578_, v_i_579_, v_entries_580_);
lean_dec_ref(v_vals_578_);
lean_dec_ref(v_keys_577_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_){
_start:
{
size_t v_x_33546__boxed_588_; size_t v_x_33547__boxed_589_; lean_object* v_res_590_; 
v_x_33546__boxed_588_ = lean_unbox_usize(v_x_584_);
lean_dec(v_x_584_);
v_x_33547__boxed_589_ = lean_unbox_usize(v_x_585_);
lean_dec(v_x_585_);
v_res_590_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_583_, v_x_33546__boxed_588_, v_x_33547__boxed_589_, v_x_586_, v_x_587_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(lean_object* v_x_591_, lean_object* v_x_592_, lean_object* v_x_593_){
_start:
{
uint64_t v___x_594_; size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
v___x_594_ = l_Lean_instHashableMVarId_hash(v_x_592_);
v___x_595_ = lean_uint64_to_usize(v___x_594_);
v___x_596_ = ((size_t)1ULL);
v___x_597_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_591_, v___x_595_, v___x_596_, v_x_592_, v_x_593_);
return v___x_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(lean_object* v_mvarId_598_, lean_object* v_val_599_, lean_object* v___y_600_){
_start:
{
lean_object* v___x_602_; lean_object* v_mctx_603_; lean_object* v_cache_604_; lean_object* v_zetaDeltaFVarIds_605_; lean_object* v_postponed_606_; lean_object* v_diag_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_636_; 
v___x_602_ = lean_st_ref_take(v___y_600_);
v_mctx_603_ = lean_ctor_get(v___x_602_, 0);
v_cache_604_ = lean_ctor_get(v___x_602_, 1);
v_zetaDeltaFVarIds_605_ = lean_ctor_get(v___x_602_, 2);
v_postponed_606_ = lean_ctor_get(v___x_602_, 3);
v_diag_607_ = lean_ctor_get(v___x_602_, 4);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_636_ == 0)
{
v___x_609_ = v___x_602_;
v_isShared_610_ = v_isSharedCheck_636_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_diag_607_);
lean_inc(v_postponed_606_);
lean_inc(v_zetaDeltaFVarIds_605_);
lean_inc(v_cache_604_);
lean_inc(v_mctx_603_);
lean_dec(v___x_602_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_636_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v_depth_611_; lean_object* v_levelAssignDepth_612_; lean_object* v_lmvarCounter_613_; lean_object* v_mvarCounter_614_; lean_object* v_lDecls_615_; lean_object* v_decls_616_; lean_object* v_userNames_617_; lean_object* v_lAssignment_618_; lean_object* v_eAssignment_619_; lean_object* v_dAssignment_620_; lean_object* v_instanceTypedMVars_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_635_; 
v_depth_611_ = lean_ctor_get(v_mctx_603_, 0);
v_levelAssignDepth_612_ = lean_ctor_get(v_mctx_603_, 1);
v_lmvarCounter_613_ = lean_ctor_get(v_mctx_603_, 2);
v_mvarCounter_614_ = lean_ctor_get(v_mctx_603_, 3);
v_lDecls_615_ = lean_ctor_get(v_mctx_603_, 4);
v_decls_616_ = lean_ctor_get(v_mctx_603_, 5);
v_userNames_617_ = lean_ctor_get(v_mctx_603_, 6);
v_lAssignment_618_ = lean_ctor_get(v_mctx_603_, 7);
v_eAssignment_619_ = lean_ctor_get(v_mctx_603_, 8);
v_dAssignment_620_ = lean_ctor_get(v_mctx_603_, 9);
v_instanceTypedMVars_621_ = lean_ctor_get(v_mctx_603_, 10);
v_isSharedCheck_635_ = !lean_is_exclusive(v_mctx_603_);
if (v_isSharedCheck_635_ == 0)
{
v___x_623_ = v_mctx_603_;
v_isShared_624_ = v_isSharedCheck_635_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_instanceTypedMVars_621_);
lean_inc(v_dAssignment_620_);
lean_inc(v_eAssignment_619_);
lean_inc(v_lAssignment_618_);
lean_inc(v_userNames_617_);
lean_inc(v_decls_616_);
lean_inc(v_lDecls_615_);
lean_inc(v_mvarCounter_614_);
lean_inc(v_lmvarCounter_613_);
lean_inc(v_levelAssignDepth_612_);
lean_inc(v_depth_611_);
lean_dec(v_mctx_603_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_635_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_625_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_eAssignment_619_, v_mvarId_598_, v_val_599_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 8, v___x_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_depth_611_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_levelAssignDepth_612_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_lmvarCounter_613_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_mvarCounter_614_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v_lDecls_615_);
lean_ctor_set(v_reuseFailAlloc_634_, 5, v_decls_616_);
lean_ctor_set(v_reuseFailAlloc_634_, 6, v_userNames_617_);
lean_ctor_set(v_reuseFailAlloc_634_, 7, v_lAssignment_618_);
lean_ctor_set(v_reuseFailAlloc_634_, 8, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_634_, 9, v_dAssignment_620_);
lean_ctor_set(v_reuseFailAlloc_634_, 10, v_instanceTypedMVars_621_);
v___x_627_ = v_reuseFailAlloc_634_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_610_ == 0)
{
lean_ctor_set(v___x_609_, 0, v___x_627_);
v___x_629_ = v___x_609_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_cache_604_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_zetaDeltaFVarIds_605_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_postponed_606_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v_diag_607_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = lean_st_ref_put(v___y_600_, v___x_629_);
v___x_631_ = lean_box(0);
v___x_632_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_632_, 0, v___x_631_);
return v___x_632_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object* v_mvarId_637_, lean_object* v_val_638_, lean_object* v___y_639_, lean_object* v___y_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_mvarId_637_, v_val_638_, v___y_639_);
lean_dec(v___y_639_);
return v_res_641_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__1(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__0));
v___x_644_ = l_Lean_stringToMessageData(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__3(void){
_start:
{
lean_object* v___x_646_; lean_object* v___x_647_; 
v___x_646_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__2));
v___x_647_ = l_Lean_stringToMessageData(v___x_646_);
return v___x_647_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__7(void){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v___x_651_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__6));
v___x_652_ = lean_unsigned_to_nat(22u);
v___x_653_ = lean_unsigned_to_nat(64u);
v___x_654_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__5));
v___x_655_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__4));
v___x_656_ = l_mkPanicMessageWithDecl(v___x_655_, v___x_654_, v___x_653_, v___x_652_, v___x_651_);
return v___x_656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object* v_snd_660_, lean_object* v___x_661_, lean_object* v_fvarId_662_, lean_object* v_hFVarId_663_, lean_object* v___x_664_, lean_object* v_fst_665_, lean_object* v_fvarSubst_666_, uint8_t v_clearH_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v___x_670_, uint8_t v_skip_671_, uint8_t v___x_672_, lean_object* v___x_673_, lean_object* v___x_674_, lean_object* v_a_675_, uint8_t v_symm_676_, uint8_t v___x_677_, lean_object* v___x_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_){
_start:
{
lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_701_; lean_object* v_mvarId_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v_newVal_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; uint8_t v___y_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v_major_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; uint8_t v___y_825_; lean_object* v___y_826_; lean_object* v_motive_827_; lean_object* v_newType_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___x_843_; 
lean_inc(v_snd_660_);
v___x_843_ = l_Lean_MVarId_getDecl(v_snd_660_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
lean_inc(v___x_661_);
v___x_845_ = l_Lean_FVarId_getDecl___redArg(v___x_661_, v___y_679_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref_known(v___x_845_, 1);
v___x_847_ = l_Lean_LocalDecl_type(v_a_846_);
lean_dec(v_a_846_);
v___x_848_ = l_Lean_Meta_matchEq_x3f(v___x_847_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_848_) == 0)
{
lean_object* v_a_849_; 
v_a_849_ = lean_ctor_get(v___x_848_, 0);
lean_inc(v_a_849_);
lean_dec_ref_known(v___x_848_, 1);
if (lean_obj_tag(v_a_849_) == 0)
{
lean_object* v___x_850_; lean_object* v___x_851_; 
lean_dec(v_a_844_);
lean_dec(v_a_675_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v___x_850_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__7, &l_Lean_Meta_substCore___lam__2___closed__7_once, _init_l_Lean_Meta_substCore___lam__2___closed__7);
v___x_851_ = l_panic___at___00Lean_Meta_substCore_spec__1(v___x_850_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
return v___x_851_;
}
else
{
lean_object* v_val_852_; lean_object* v_snd_853_; lean_object* v_fst_854_; lean_object* v_snd_855_; lean_object* v_type_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___f_859_; lean_object* v___y_861_; 
v_val_852_ = lean_ctor_get(v_a_849_, 0);
lean_inc(v_val_852_);
lean_dec_ref_known(v_a_849_, 1);
v_snd_853_ = lean_ctor_get(v_val_852_, 1);
lean_inc(v_snd_853_);
lean_dec(v_val_852_);
v_fst_854_ = lean_ctor_get(v_snd_853_, 0);
lean_inc(v_fst_854_);
v_snd_855_ = lean_ctor_get(v_snd_853_, 1);
lean_inc(v_snd_855_);
lean_dec(v_snd_853_);
v_type_856_ = lean_ctor_get(v_a_844_, 2);
lean_inc_ref_n(v_type_856_, 2);
lean_dec(v_a_844_);
v___x_857_ = lean_box(v___x_677_);
v___x_858_ = lean_box(v___x_672_);
lean_inc_ref(v___x_668_);
lean_inc(v___x_669_);
lean_inc_ref(v___x_664_);
v___f_859_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 12, 6);
lean_closure_set(v___f_859_, 0, v_type_856_);
lean_closure_set(v___f_859_, 1, v___x_664_);
lean_closure_set(v___f_859_, 2, v___x_669_);
lean_closure_set(v___f_859_, 3, v___x_668_);
lean_closure_set(v___f_859_, 4, v___x_857_);
lean_closure_set(v___f_859_, 5, v___x_858_);
if (v_symm_676_ == 0)
{
lean_dec(v_fst_854_);
v___y_861_ = v_snd_855_;
goto v___jp_860_;
}
else
{
lean_dec(v_snd_855_);
v___y_861_ = v_fst_854_;
goto v___jp_860_;
}
v___jp_860_:
{
lean_object* v___x_862_; lean_object* v_a_863_; lean_object* v___x_864_; lean_object* v_a_865_; uint8_t v___x_866_; 
v___x_862_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_861_, v___y_680_);
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
lean_inc(v___x_661_);
lean_inc_ref(v_type_856_);
v___x_864_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_type_856_, v___x_661_, v___y_680_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v___x_864_);
v___x_866_ = lean_unbox(v_a_865_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; lean_object* v___x_868_; uint8_t v___x_869_; lean_object* v___x_870_; 
lean_dec_ref(v___f_859_);
v___x_867_ = lean_mk_empty_array_with_capacity(v___x_678_);
lean_inc_ref(v___x_668_);
v___x_868_ = lean_array_push(v___x_867_, v___x_668_);
v___x_869_ = 1;
lean_inc_ref(v_type_856_);
v___x_870_ = l_Lean_Meta_mkLambdaFVars(v___x_868_, v_type_856_, v___x_677_, v___x_672_, v___x_677_, v___x_672_, v___x_869_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v___x_868_);
if (lean_obj_tag(v___x_870_) == 0)
{
lean_object* v_a_871_; lean_object* v___x_872_; uint8_t v___x_873_; 
v_a_871_ = lean_ctor_get(v___x_870_, 0);
lean_inc(v_a_871_);
lean_dec_ref_known(v___x_870_, 1);
lean_inc_ref(v___x_668_);
v___x_872_ = l_Lean_Expr_replaceFVar(v_type_856_, v___x_668_, v_a_863_);
lean_dec_ref(v_type_856_);
v___x_873_ = lean_unbox(v_a_865_);
lean_dec(v_a_865_);
v___y_825_ = v___x_873_;
v___y_826_ = v_a_863_;
v_motive_827_ = v_a_871_;
v_newType_828_ = v___x_872_;
v___y_829_ = v___y_679_;
v___y_830_ = v___y_680_;
v___y_831_ = v___y_681_;
v___y_832_ = v___y_682_;
goto v___jp_824_;
}
else
{
lean_object* v_a_874_; lean_object* v___x_876_; uint8_t v_isShared_877_; uint8_t v_isSharedCheck_881_; 
lean_dec(v_a_865_);
lean_dec(v_a_863_);
lean_dec_ref(v_type_856_);
lean_dec(v_a_675_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_874_ = lean_ctor_get(v___x_870_, 0);
v_isSharedCheck_881_ = !lean_is_exclusive(v___x_870_);
if (v_isSharedCheck_881_ == 0)
{
v___x_876_ = v___x_870_;
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
else
{
lean_inc(v_a_874_);
lean_dec(v___x_870_);
v___x_876_ = lean_box(0);
v_isShared_877_ = v_isSharedCheck_881_;
goto v_resetjp_875_;
}
v_resetjp_875_:
{
lean_object* v___x_879_; 
if (v_isShared_877_ == 0)
{
v___x_879_ = v___x_876_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_a_874_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
else
{
lean_object* v___x_882_; lean_object* v___x_883_; 
lean_inc_ref(v___x_668_);
v___x_882_ = l_Lean_Expr_replaceFVar(v_type_856_, v___x_668_, v_a_863_);
lean_inc(v_a_863_);
v___x_883_ = l_Lean_Meta_mkEqRefl(v_a_863_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
lean_inc_ref(v___x_664_);
v___x_885_ = l_Lean_Expr_replaceFVar(v___x_882_, v___x_664_, v_a_884_);
lean_dec(v_a_884_);
lean_dec_ref(v___x_882_);
if (v_symm_676_ == 0)
{
lean_object* v___x_886_; 
lean_dec_ref(v_type_856_);
lean_inc_ref(v___x_668_);
lean_inc(v_a_863_);
v___x_886_ = l_Lean_Meta_mkEq(v_a_863_, v___x_668_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_886_) == 0)
{
lean_object* v_a_887_; lean_object* v___x_888_; lean_object* v___x_889_; 
v_a_887_ = lean_ctor_get(v___x_886_, 0);
lean_inc(v_a_887_);
lean_dec_ref_known(v___x_886_, 1);
v___x_888_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__9));
v___x_889_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v___x_888_, v_a_887_, v___f_859_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; uint8_t v___x_891_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
v___x_891_ = lean_unbox(v_a_865_);
lean_dec(v_a_865_);
v___y_825_ = v___x_891_;
v___y_826_ = v_a_863_;
v_motive_827_ = v_a_890_;
v_newType_828_ = v___x_885_;
v___y_829_ = v___y_679_;
v___y_830_ = v___y_680_;
v___y_831_ = v___y_681_;
v___y_832_ = v___y_682_;
goto v___jp_824_;
}
else
{
lean_object* v_a_892_; lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_899_; 
lean_dec_ref(v___x_885_);
lean_dec(v_a_865_);
lean_dec(v_a_863_);
lean_dec(v_a_675_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_892_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_899_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_899_ == 0)
{
v___x_894_ = v___x_889_;
v_isShared_895_ = v_isSharedCheck_899_;
goto v_resetjp_893_;
}
else
{
lean_inc(v_a_892_);
lean_dec(v___x_889_);
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
else
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_907_; 
lean_dec_ref(v___x_885_);
lean_dec(v_a_865_);
lean_dec(v_a_863_);
lean_dec_ref(v___f_859_);
lean_dec(v_a_675_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_900_ = lean_ctor_get(v___x_886_, 0);
v_isSharedCheck_907_ = !lean_is_exclusive(v___x_886_);
if (v_isSharedCheck_907_ == 0)
{
v___x_902_ = v___x_886_;
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_886_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_907_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v___x_905_; 
if (v_isShared_903_ == 0)
{
v___x_905_ = v___x_902_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_a_900_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; uint8_t v___x_911_; lean_object* v___x_912_; 
lean_dec_ref(v___f_859_);
v___x_908_ = lean_mk_empty_array_with_capacity(v___x_669_);
lean_inc_ref(v___x_668_);
v___x_909_ = lean_array_push(v___x_908_, v___x_668_);
lean_inc_ref(v___x_664_);
v___x_910_ = lean_array_push(v___x_909_, v___x_664_);
v___x_911_ = 1;
v___x_912_ = l_Lean_Meta_mkLambdaFVars(v___x_910_, v_type_856_, v___x_677_, v___x_672_, v___x_677_, v___x_672_, v___x_911_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec_ref(v___x_910_);
if (lean_obj_tag(v___x_912_) == 0)
{
lean_object* v_a_913_; uint8_t v___x_914_; 
v_a_913_ = lean_ctor_get(v___x_912_, 0);
lean_inc(v_a_913_);
lean_dec_ref_known(v___x_912_, 1);
v___x_914_ = lean_unbox(v_a_865_);
lean_dec(v_a_865_);
v___y_825_ = v___x_914_;
v___y_826_ = v_a_863_;
v_motive_827_ = v_a_913_;
v_newType_828_ = v___x_885_;
v___y_829_ = v___y_679_;
v___y_830_ = v___y_680_;
v___y_831_ = v___y_681_;
v___y_832_ = v___y_682_;
goto v___jp_824_;
}
else
{
lean_object* v_a_915_; lean_object* v___x_917_; uint8_t v_isShared_918_; uint8_t v_isSharedCheck_922_; 
lean_dec_ref(v___x_885_);
lean_dec(v_a_865_);
lean_dec(v_a_863_);
lean_dec(v_a_675_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_915_ = lean_ctor_get(v___x_912_, 0);
v_isSharedCheck_922_ = !lean_is_exclusive(v___x_912_);
if (v_isSharedCheck_922_ == 0)
{
v___x_917_ = v___x_912_;
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
else
{
lean_inc(v_a_915_);
lean_dec(v___x_912_);
v___x_917_ = lean_box(0);
v_isShared_918_ = v_isSharedCheck_922_;
goto v_resetjp_916_;
}
v_resetjp_916_:
{
lean_object* v___x_920_; 
if (v_isShared_918_ == 0)
{
v___x_920_ = v___x_917_;
goto v_reusejp_919_;
}
else
{
lean_object* v_reuseFailAlloc_921_; 
v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_921_, 0, v_a_915_);
v___x_920_ = v_reuseFailAlloc_921_;
goto v_reusejp_919_;
}
v_reusejp_919_:
{
return v___x_920_;
}
}
}
}
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
lean_dec_ref(v___x_882_);
lean_dec(v_a_865_);
lean_dec(v_a_863_);
lean_dec_ref(v___f_859_);
lean_dec_ref(v_type_856_);
lean_dec(v_a_675_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_923_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_883_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_883_);
v___x_925_ = lean_box(0);
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
v_resetjp_924_:
{
lean_object* v___x_928_; 
if (v_isShared_926_ == 0)
{
v___x_928_ = v___x_925_;
goto v_reusejp_927_;
}
else
{
lean_object* v_reuseFailAlloc_929_; 
v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_929_, 0, v_a_923_);
v___x_928_ = v_reuseFailAlloc_929_;
goto v_reusejp_927_;
}
v_reusejp_927_:
{
return v___x_928_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_931_; lean_object* v___x_933_; uint8_t v_isShared_934_; uint8_t v_isSharedCheck_938_; 
lean_dec(v_a_844_);
lean_dec(v_a_675_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_931_ = lean_ctor_get(v___x_848_, 0);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_848_);
if (v_isSharedCheck_938_ == 0)
{
v___x_933_ = v___x_848_;
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
else
{
lean_inc(v_a_931_);
lean_dec(v___x_848_);
v___x_933_ = lean_box(0);
v_isShared_934_ = v_isSharedCheck_938_;
goto v_resetjp_932_;
}
v_resetjp_932_:
{
lean_object* v___x_936_; 
if (v_isShared_934_ == 0)
{
v___x_936_ = v___x_933_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v_a_931_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
}
else
{
lean_object* v_a_939_; lean_object* v___x_941_; uint8_t v_isShared_942_; uint8_t v_isSharedCheck_946_; 
lean_dec(v_a_844_);
lean_dec(v_a_675_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_939_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_946_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_946_ == 0)
{
v___x_941_ = v___x_845_;
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
else
{
lean_inc(v_a_939_);
lean_dec(v___x_845_);
v___x_941_ = lean_box(0);
v_isShared_942_ = v_isSharedCheck_946_;
goto v_resetjp_940_;
}
v_resetjp_940_:
{
lean_object* v___x_944_; 
if (v_isShared_942_ == 0)
{
v___x_944_ = v___x_941_;
goto v_reusejp_943_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_a_939_);
v___x_944_ = v_reuseFailAlloc_945_;
goto v_reusejp_943_;
}
v_reusejp_943_:
{
return v___x_944_;
}
}
}
}
else
{
lean_object* v_a_947_; lean_object* v___x_949_; uint8_t v_isShared_950_; uint8_t v_isSharedCheck_954_; 
lean_dec(v_a_675_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_947_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_954_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_954_ == 0)
{
v___x_949_ = v___x_843_;
v_isShared_950_ = v_isSharedCheck_954_;
goto v_resetjp_948_;
}
else
{
lean_inc(v_a_947_);
lean_dec(v___x_843_);
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
v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, 0);
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
v___jp_684_:
{
lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_688_ = l_Lean_Meta_FVarSubst_insert(v___y_686_, v_fvarId_662_, v___y_687_);
v___x_689_ = l_Lean_Meta_FVarSubst_insert(v___x_688_, v_hFVarId_663_, v___x_664_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___y_685_);
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v___x_690_);
return v___x_691_;
}
v___jp_692_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_array_get_size(v___y_695_);
v___x_697_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_665_, v___y_695_, v___x_696_, v___x_696_, v_fvarSubst_666_);
lean_dec_ref(v___y_695_);
if (v_clearH_667_ == 0)
{
lean_object* v_a_698_; 
lean_dec_ref(v___y_694_);
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v___x_697_);
v___y_685_ = v___y_693_;
v___y_686_ = v_a_698_;
v___y_687_ = v___x_668_;
goto v___jp_684_;
}
else
{
lean_object* v_a_699_; 
lean_dec_ref(v___x_668_);
v_a_699_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_699_);
lean_dec_ref(v___x_697_);
v___y_685_ = v___y_693_;
v___y_686_ = v_a_699_;
v___y_687_ = v___y_694_;
goto v___jp_684_;
}
}
v___jp_700_:
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = lean_array_get_size(v_fst_665_);
v___x_708_ = lean_nat_sub(v___x_707_, v___x_669_);
lean_dec(v___x_669_);
lean_inc(v___x_708_);
v___x_709_ = l_Lean_Meta_introNCore(v_mvarId_702_, v___x_708_, v___x_670_, v_skip_671_, v___x_672_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_709_) == 0)
{
lean_object* v_a_710_; lean_object* v_options_711_; uint8_t v_hasTrace_712_; 
v_a_710_ = lean_ctor_get(v___x_709_, 0);
lean_inc(v_a_710_);
lean_dec_ref_known(v___x_709_, 1);
v_options_711_ = lean_ctor_get(v___y_705_, 2);
v_hasTrace_712_ = lean_ctor_get_uint8(v_options_711_, sizeof(void*)*1);
if (v_hasTrace_712_ == 0)
{
lean_object* v_fst_713_; lean_object* v_snd_714_; 
lean_dec(v___x_708_);
lean_dec(v___x_673_);
v_fst_713_ = lean_ctor_get(v_a_710_, 0);
lean_inc(v_fst_713_);
v_snd_714_ = lean_ctor_get(v_a_710_, 1);
lean_inc(v_snd_714_);
lean_dec(v_a_710_);
v___y_693_ = v_snd_714_;
v___y_694_ = v___y_701_;
v___y_695_ = v_fst_713_;
goto v___jp_692_;
}
else
{
lean_object* v_fst_715_; lean_object* v_snd_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_744_; 
v_fst_715_ = lean_ctor_get(v_a_710_, 0);
v_snd_716_ = lean_ctor_get(v_a_710_, 1);
v_isSharedCheck_744_ = !lean_is_exclusive(v_a_710_);
if (v_isSharedCheck_744_ == 0)
{
v___x_718_ = v_a_710_;
v_isShared_719_ = v_isSharedCheck_744_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_snd_716_);
lean_inc(v_fst_715_);
lean_dec(v_a_710_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_744_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_inheritedTraceOptions_720_; lean_object* v___x_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_inheritedTraceOptions_720_ = lean_ctor_get(v___y_705_, 13);
v___x_721_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
lean_inc(v___x_673_);
v___x_722_ = l_Lean_Name_append(v___x_721_, v___x_673_);
v___x_723_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_720_, v_options_711_, v___x_722_);
lean_dec(v___x_722_);
if (v___x_723_ == 0)
{
lean_del_object(v___x_718_);
lean_dec(v___x_708_);
lean_dec(v___x_673_);
v___y_693_ = v_snd_716_;
v___y_694_ = v___y_701_;
v___y_695_ = v_fst_715_;
goto v___jp_692_;
}
else
{
lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_729_; 
v___x_724_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__1, &l_Lean_Meta_substCore___lam__2___closed__1_once, _init_l_Lean_Meta_substCore___lam__2___closed__1);
v___x_725_ = l_Nat_reprFast(v___x_708_);
v___x_726_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
v___x_727_ = l_Lean_MessageData_ofFormat(v___x_726_);
if (v_isShared_719_ == 0)
{
lean_ctor_set_tag(v___x_718_, 7);
lean_ctor_set(v___x_718_, 1, v___x_727_);
lean_ctor_set(v___x_718_, 0, v___x_724_);
v___x_729_ = v___x_718_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v___x_724_);
lean_ctor_set(v_reuseFailAlloc_743_, 1, v___x_727_);
v___x_729_ = v_reuseFailAlloc_743_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; 
v___x_730_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__3, &l_Lean_Meta_substCore___lam__2___closed__3_once, _init_l_Lean_Meta_substCore___lam__2___closed__3);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
lean_inc(v_snd_716_);
v___x_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_732_, 0, v_snd_716_);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
v___x_734_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_673_, v___x_733_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
if (lean_obj_tag(v___x_734_) == 0)
{
lean_dec_ref_known(v___x_734_, 1);
v___y_693_ = v_snd_716_;
v___y_694_ = v___y_701_;
v___y_695_ = v_fst_715_;
goto v___jp_692_;
}
else
{
lean_object* v_a_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_742_; 
lean_dec(v_snd_716_);
lean_dec(v_fst_715_);
lean_dec_ref(v___y_701_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
v_a_735_ = lean_ctor_get(v___x_734_, 0);
v_isSharedCheck_742_ = !lean_is_exclusive(v___x_734_);
if (v_isSharedCheck_742_ == 0)
{
v___x_737_ = v___x_734_;
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_a_735_);
lean_dec(v___x_734_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_742_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v___x_740_; 
if (v_isShared_738_ == 0)
{
v___x_740_ = v___x_737_;
goto v_reusejp_739_;
}
else
{
lean_object* v_reuseFailAlloc_741_; 
v_reuseFailAlloc_741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_741_, 0, v_a_735_);
v___x_740_ = v_reuseFailAlloc_741_;
goto v_reusejp_739_;
}
v_reusejp_739_:
{
return v___x_740_;
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
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_752_; 
lean_dec(v___x_708_);
lean_dec_ref(v___y_701_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
v_a_745_ = lean_ctor_get(v___x_709_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v___x_709_);
if (v_isSharedCheck_752_ == 0)
{
v___x_747_ = v___x_709_;
v_isShared_748_ = v_isSharedCheck_752_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_709_);
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
v___jp_753_:
{
lean_object* v___x_761_; lean_object* v___x_762_; 
v___x_761_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_snd_660_, v_newVal_756_, v___y_758_);
lean_dec_ref(v___x_761_);
v___x_762_ = l_Lean_Expr_mvarId_x21(v___y_755_);
lean_dec_ref(v___y_755_);
if (v_clearH_667_ == 0)
{
lean_dec(v___x_674_);
lean_dec(v___x_661_);
v___y_701_ = v___y_754_;
v_mvarId_702_ = v___x_762_;
v___y_703_ = v___y_757_;
v___y_704_ = v___y_758_;
v___y_705_ = v___y_759_;
v___y_706_ = v___y_760_;
goto v___jp_700_;
}
else
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_MVarId_clear(v___x_762_, v___x_661_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___x_765_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___x_765_ = l_Lean_MVarId_clear(v_a_764_, v___x_674_, v___y_757_, v___y_758_, v___y_759_, v___y_760_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v___y_701_ = v___y_754_;
v_mvarId_702_ = v_a_766_;
v___y_703_ = v___y_757_;
v___y_704_ = v___y_758_;
v___y_705_ = v___y_759_;
v___y_706_ = v___y_760_;
goto v___jp_700_;
}
else
{
lean_object* v_a_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_774_; 
lean_dec_ref(v___y_754_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
v_a_767_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_774_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_774_ == 0)
{
v___x_769_ = v___x_765_;
v_isShared_770_ = v_isSharedCheck_774_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_a_767_);
lean_dec(v___x_765_);
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
lean_dec_ref(v___y_754_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
v_a_775_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_782_ == 0)
{
v___x_777_ = v___x_763_;
v_isShared_778_ = v_isSharedCheck_782_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_763_);
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
}
v___jp_783_:
{
lean_object* v___x_793_; 
v___x_793_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_786_, v_a_675_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
if (v___y_784_ == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc_n(v_a_794_, 2);
lean_dec_ref_known(v___x_793_, 1);
v___x_795_ = l_Lean_Meta_mkEqNDRec(v___y_787_, v_a_794_, v_major_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
v___y_754_ = v___y_785_;
v___y_755_ = v_a_794_;
v_newVal_756_ = v_a_796_;
v___y_757_ = v___y_789_;
v___y_758_ = v___y_790_;
v___y_759_ = v___y_791_;
v___y_760_ = v___y_792_;
goto v___jp_753_;
}
else
{
lean_object* v_a_797_; lean_object* v___x_799_; uint8_t v_isShared_800_; uint8_t v_isSharedCheck_804_; 
lean_dec(v_a_794_);
lean_dec_ref(v___y_785_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_797_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_804_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_804_ == 0)
{
v___x_799_ = v___x_795_;
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
else
{
lean_inc(v_a_797_);
lean_dec(v___x_795_);
v___x_799_ = lean_box(0);
v_isShared_800_ = v_isSharedCheck_804_;
goto v_resetjp_798_;
}
v_resetjp_798_:
{
lean_object* v___x_802_; 
if (v_isShared_800_ == 0)
{
v___x_802_ = v___x_799_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_803_; 
v_reuseFailAlloc_803_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_803_, 0, v_a_797_);
v___x_802_ = v_reuseFailAlloc_803_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
return v___x_802_;
}
}
}
}
else
{
lean_object* v_a_805_; lean_object* v___x_806_; 
v_a_805_ = lean_ctor_get(v___x_793_, 0);
lean_inc_n(v_a_805_, 2);
lean_dec_ref_known(v___x_793_, 1);
v___x_806_ = l_Lean_Meta_mkEqRec(v___y_787_, v_a_805_, v_major_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
v___y_754_ = v___y_785_;
v___y_755_ = v_a_805_;
v_newVal_756_ = v_a_807_;
v___y_757_ = v___y_789_;
v___y_758_ = v___y_790_;
v___y_759_ = v___y_791_;
v___y_760_ = v___y_792_;
goto v___jp_753_;
}
else
{
lean_object* v_a_808_; lean_object* v___x_810_; uint8_t v_isShared_811_; uint8_t v_isSharedCheck_815_; 
lean_dec(v_a_805_);
lean_dec_ref(v___y_785_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
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
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec_ref(v_major_788_);
lean_dec_ref(v___y_787_);
lean_dec_ref(v___y_785_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_816_ = lean_ctor_get(v___x_793_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_793_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_793_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_793_);
v___x_818_ = lean_box(0);
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
v_resetjp_817_:
{
lean_object* v___x_821_; 
if (v_isShared_819_ == 0)
{
v___x_821_ = v___x_818_;
goto v_reusejp_820_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_a_816_);
v___x_821_ = v_reuseFailAlloc_822_;
goto v_reusejp_820_;
}
v_reusejp_820_:
{
return v___x_821_;
}
}
}
}
v___jp_824_:
{
if (v_symm_676_ == 0)
{
lean_object* v___x_833_; 
lean_inc_ref(v___x_664_);
v___x_833_ = l_Lean_Meta_mkEqSymm(v___x_664_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
if (lean_obj_tag(v___x_833_) == 0)
{
lean_object* v_a_834_; 
v_a_834_ = lean_ctor_get(v___x_833_, 0);
lean_inc(v_a_834_);
lean_dec_ref_known(v___x_833_, 1);
v___y_784_ = v___y_825_;
v___y_785_ = v___y_826_;
v___y_786_ = v_newType_828_;
v___y_787_ = v_motive_827_;
v_major_788_ = v_a_834_;
v___y_789_ = v___y_829_;
v___y_790_ = v___y_830_;
v___y_791_ = v___y_831_;
v___y_792_ = v___y_832_;
goto v___jp_783_;
}
else
{
lean_object* v_a_835_; lean_object* v___x_837_; uint8_t v_isShared_838_; uint8_t v_isSharedCheck_842_; 
lean_dec_ref(v_newType_828_);
lean_dec_ref(v_motive_827_);
lean_dec_ref(v___y_826_);
lean_dec(v_a_675_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_668_);
lean_dec(v_fvarSubst_666_);
lean_dec_ref(v___x_664_);
lean_dec(v_hFVarId_663_);
lean_dec(v_fvarId_662_);
lean_dec(v___x_661_);
lean_dec(v_snd_660_);
v_a_835_ = lean_ctor_get(v___x_833_, 0);
v_isSharedCheck_842_ = !lean_is_exclusive(v___x_833_);
if (v_isSharedCheck_842_ == 0)
{
v___x_837_ = v___x_833_;
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
else
{
lean_inc(v_a_835_);
lean_dec(v___x_833_);
v___x_837_ = lean_box(0);
v_isShared_838_ = v_isSharedCheck_842_;
goto v_resetjp_836_;
}
v_resetjp_836_:
{
lean_object* v___x_840_; 
if (v_isShared_838_ == 0)
{
v___x_840_ = v___x_837_;
goto v_reusejp_839_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_a_835_);
v___x_840_ = v_reuseFailAlloc_841_;
goto v_reusejp_839_;
}
v_reusejp_839_:
{
return v___x_840_;
}
}
}
}
else
{
lean_inc_ref(v___x_664_);
v___y_784_ = v___y_825_;
v___y_785_ = v___y_826_;
v___y_786_ = v_newType_828_;
v___y_787_ = v_motive_827_;
v_major_788_ = v___x_664_;
v___y_789_ = v___y_829_;
v___y_790_ = v___y_830_;
v___y_791_ = v___y_831_;
v___y_792_ = v___y_832_;
goto v___jp_783_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object** _args){
lean_object* v_snd_955_ = _args[0];
lean_object* v___x_956_ = _args[1];
lean_object* v_fvarId_957_ = _args[2];
lean_object* v_hFVarId_958_ = _args[3];
lean_object* v___x_959_ = _args[4];
lean_object* v_fst_960_ = _args[5];
lean_object* v_fvarSubst_961_ = _args[6];
lean_object* v_clearH_962_ = _args[7];
lean_object* v___x_963_ = _args[8];
lean_object* v___x_964_ = _args[9];
lean_object* v___x_965_ = _args[10];
lean_object* v_skip_966_ = _args[11];
lean_object* v___x_967_ = _args[12];
lean_object* v___x_968_ = _args[13];
lean_object* v___x_969_ = _args[14];
lean_object* v_a_970_ = _args[15];
lean_object* v_symm_971_ = _args[16];
lean_object* v___x_972_ = _args[17];
lean_object* v___x_973_ = _args[18];
lean_object* v___y_974_ = _args[19];
lean_object* v___y_975_ = _args[20];
lean_object* v___y_976_ = _args[21];
lean_object* v___y_977_ = _args[22];
lean_object* v___y_978_ = _args[23];
_start:
{
uint8_t v_clearH_boxed_979_; uint8_t v_skip_boxed_980_; uint8_t v___x_33806__boxed_981_; uint8_t v_symm_boxed_982_; uint8_t v___x_33810__boxed_983_; lean_object* v_res_984_; 
v_clearH_boxed_979_ = lean_unbox(v_clearH_962_);
v_skip_boxed_980_ = lean_unbox(v_skip_966_);
v___x_33806__boxed_981_ = lean_unbox(v___x_967_);
v_symm_boxed_982_ = lean_unbox(v_symm_971_);
v___x_33810__boxed_983_ = lean_unbox(v___x_972_);
v_res_984_ = l_Lean_Meta_substCore___lam__2(v_snd_955_, v___x_956_, v_fvarId_957_, v_hFVarId_958_, v___x_959_, v_fst_960_, v_fvarSubst_961_, v_clearH_boxed_979_, v___x_963_, v___x_964_, v___x_965_, v_skip_boxed_980_, v___x_33806__boxed_981_, v___x_968_, v___x_969_, v_a_970_, v_symm_boxed_982_, v___x_33810__boxed_983_, v___x_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___x_973_);
lean_dec_ref(v_fst_960_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(lean_object* v_a_985_, lean_object* v_a_986_){
_start:
{
if (lean_obj_tag(v_a_985_) == 0)
{
lean_object* v___x_987_; 
v___x_987_ = l_List_reverse___redArg(v_a_986_);
return v___x_987_;
}
else
{
lean_object* v_head_988_; lean_object* v_tail_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_998_; 
v_head_988_ = lean_ctor_get(v_a_985_, 0);
v_tail_989_ = lean_ctor_get(v_a_985_, 1);
v_isSharedCheck_998_ = !lean_is_exclusive(v_a_985_);
if (v_isSharedCheck_998_ == 0)
{
v___x_991_ = v_a_985_;
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_tail_989_);
lean_inc(v_head_988_);
lean_dec(v_a_985_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_998_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
v___x_993_ = l_Lean_MessageData_ofName(v_head_988_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v_a_986_);
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_997_; 
v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_997_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_997_, 1, v_a_986_);
v___x_995_ = v_reuseFailAlloc_997_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
v_a_985_ = v_tail_989_;
v_a_986_ = v___x_995_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(size_t v_sz_999_, size_t v_i_1000_, lean_object* v_bs_1001_){
_start:
{
uint8_t v___x_1002_; 
v___x_1002_ = lean_usize_dec_lt(v_i_1000_, v_sz_999_);
if (v___x_1002_ == 0)
{
return v_bs_1001_;
}
else
{
lean_object* v_v_1003_; lean_object* v___x_1004_; lean_object* v_bs_x27_1005_; size_t v___x_1006_; size_t v___x_1007_; lean_object* v___x_1008_; 
v_v_1003_ = lean_array_uget(v_bs_1001_, v_i_1000_);
v___x_1004_ = lean_unsigned_to_nat(0u);
v_bs_x27_1005_ = lean_array_uset(v_bs_1001_, v_i_1000_, v___x_1004_);
v___x_1006_ = ((size_t)1ULL);
v___x_1007_ = lean_usize_add(v_i_1000_, v___x_1006_);
v___x_1008_ = lean_array_uset(v_bs_x27_1005_, v_i_1000_, v_v_1003_);
v_i_1000_ = v___x_1007_;
v_bs_1001_ = v___x_1008_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8___boxed(lean_object* v_sz_1010_, lean_object* v_i_1011_, lean_object* v_bs_1012_){
_start:
{
size_t v_sz_boxed_1013_; size_t v_i_boxed_1014_; lean_object* v_res_1015_; 
v_sz_boxed_1013_ = lean_unbox_usize(v_sz_1010_);
lean_dec(v_sz_1010_);
v_i_boxed_1014_ = lean_unbox_usize(v_i_1011_);
lean_dec(v_i_1011_);
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_boxed_1013_, v_i_boxed_1014_, v_bs_1012_);
return v_res_1015_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; 
v___x_1020_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__2));
v___x_1021_ = l_Lean_stringToMessageData(v___x_1020_);
return v___x_1021_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; 
v___x_1023_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__4));
v___x_1024_ = l_Lean_stringToMessageData(v___x_1023_);
return v___x_1024_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1028_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__7));
v___x_1029_ = l_Lean_MessageData_ofFormat(v___x_1028_);
return v___x_1029_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__9(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__8, &l_Lean_Meta_substCore___lam__3___closed__8_once, _init_l_Lean_Meta_substCore___lam__3___closed__8);
v___x_1031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1031_, 0, v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__11(void){
_start:
{
lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1033_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__10));
v___x_1034_ = l_Lean_stringToMessageData(v___x_1033_);
return v___x_1034_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__13(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; 
v___x_1036_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__12));
v___x_1037_ = l_Lean_stringToMessageData(v___x_1036_);
return v___x_1037_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__15(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; 
v___x_1039_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__14));
v___x_1040_ = l_Lean_stringToMessageData(v___x_1039_);
return v___x_1040_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__17(void){
_start:
{
lean_object* v___x_1042_; lean_object* v___x_1043_; 
v___x_1042_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__16));
v___x_1043_ = l_Lean_stringToMessageData(v___x_1042_);
return v___x_1043_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__19(void){
_start:
{
lean_object* v___x_1045_; lean_object* v___x_1046_; 
v___x_1045_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__18));
v___x_1046_ = l_Lean_stringToMessageData(v___x_1045_);
return v___x_1046_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__25(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__24));
v___x_1057_ = l_Lean_stringToMessageData(v___x_1056_);
return v___x_1057_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__27(void){
_start:
{
lean_object* v___x_1059_; lean_object* v___x_1060_; 
v___x_1059_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__26));
v___x_1060_ = l_Lean_stringToMessageData(v___x_1059_);
return v___x_1060_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__29(void){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__28));
v___x_1063_ = l_Lean_stringToMessageData(v___x_1062_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3(lean_object* v_mvarId_1066_, lean_object* v_hFVarId_1067_, lean_object* v___x_1068_, uint8_t v_clearH_1069_, lean_object* v_fvarSubst_1070_, uint8_t v_symm_1071_, uint8_t v_tryToSkip_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___y_1079_; lean_object* v___y_1080_; lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___x_1116_; 
lean_inc(v_mvarId_1066_);
v___x_1116_ = l_Lean_MVarId_getTag(v_mvarId_1066_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
lean_dec_ref_known(v___x_1116_, 1);
v___x_1118_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
lean_inc(v_mvarId_1066_);
v___x_1119_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1066_, v___x_1118_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1120_; 
lean_dec_ref_known(v___x_1119_, 1);
lean_inc(v_hFVarId_1067_);
v___x_1120_ = l_Lean_FVarId_getDecl___redArg(v_hFVarId_1067_, v___y_1073_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; lean_object* v___y_1124_; lean_object* v___y_1125_; lean_object* v___x_1137_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref_known(v___x_1120_, 1);
v___x_1122_ = l_Lean_LocalDecl_type(v_a_1121_);
lean_dec(v_a_1121_);
lean_inc_ref(v___x_1122_);
v___x_1137_ = l_Lean_Meta_matchEq_x3f(v___x_1122_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
if (lean_obj_tag(v_a_1138_) == 0)
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_dec_ref(v___x_1122_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
v___x_1139_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__9, &l_Lean_Meta_substCore___lam__3___closed__9_once, _init_l_Lean_Meta_substCore___lam__3___closed__9);
v___x_1140_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1118_, v_mvarId_1066_, v___x_1139_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v___x_1140_;
}
else
{
lean_object* v_val_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1463_; 
v_val_1141_ = lean_ctor_get(v_a_1138_, 0);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_a_1138_);
if (v_isSharedCheck_1463_ == 0)
{
v___x_1143_ = v_a_1138_;
v_isShared_1144_ = v_isSharedCheck_1463_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_val_1141_);
lean_dec(v_a_1138_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1463_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_snd_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1461_; 
v_snd_1145_ = lean_ctor_get(v_val_1141_, 1);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_val_1141_);
if (v_isSharedCheck_1461_ == 0)
{
lean_object* v_unused_1462_; 
v_unused_1462_ = lean_ctor_get(v_val_1141_, 0);
lean_dec(v_unused_1462_);
v___x_1147_ = v_val_1141_;
v_isShared_1148_ = v_isSharedCheck_1461_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_snd_1145_);
lean_dec(v_val_1141_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1461_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_fst_1149_; lean_object* v_snd_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1460_; 
v_fst_1149_ = lean_ctor_get(v_snd_1145_, 0);
v_snd_1150_ = lean_ctor_get(v_snd_1145_, 1);
v_isSharedCheck_1460_ = !lean_is_exclusive(v_snd_1145_);
if (v_isSharedCheck_1460_ == 0)
{
v___x_1152_ = v_snd_1145_;
v_isShared_1153_ = v_isSharedCheck_1460_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snd_1150_);
lean_inc(v_fst_1149_);
lean_dec(v_snd_1145_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1460_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v___x_1154_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; uint8_t v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; uint8_t v_skip_1173_; uint8_t v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; uint8_t v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; uint8_t v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; uint8_t v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; uint8_t v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; uint8_t v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1456_; 
v___x_1154_ = 1;
if (v_symm_1071_ == 0)
{
lean_inc(v_fst_1149_);
v___y_1456_ = v_fst_1149_;
goto v___jp_1455_;
}
else
{
lean_inc(v_snd_1150_);
v___y_1456_ = v_snd_1150_;
goto v___jp_1455_;
}
v___jp_1155_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; 
v___x_1174_ = lean_box(v_clearH_1069_);
v___x_1175_ = lean_box(v_skip_1173_);
v___x_1176_ = lean_box(v___x_1154_);
v___x_1177_ = lean_box(v_symm_1071_);
v___x_1178_ = lean_box(v___y_1165_);
v___f_1179_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__2___boxed), 24, 19);
lean_closure_set(v___f_1179_, 0, v___y_1161_);
lean_closure_set(v___f_1179_, 1, v___y_1170_);
lean_closure_set(v___f_1179_, 2, v___y_1172_);
lean_closure_set(v___f_1179_, 3, v_hFVarId_1067_);
lean_closure_set(v___f_1179_, 4, v___y_1162_);
lean_closure_set(v___f_1179_, 5, v___y_1166_);
lean_closure_set(v___f_1179_, 6, v_fvarSubst_1070_);
lean_closure_set(v___f_1179_, 7, v___x_1174_);
lean_closure_set(v___f_1179_, 8, v___y_1156_);
lean_closure_set(v___f_1179_, 9, v___y_1171_);
lean_closure_set(v___f_1179_, 10, v___y_1168_);
lean_closure_set(v___f_1179_, 11, v___x_1175_);
lean_closure_set(v___f_1179_, 12, v___x_1176_);
lean_closure_set(v___f_1179_, 13, v___y_1158_);
lean_closure_set(v___f_1179_, 14, v___y_1159_);
lean_closure_set(v___f_1179_, 15, v_a_1117_);
lean_closure_set(v___f_1179_, 16, v___x_1177_);
lean_closure_set(v___f_1179_, 17, v___x_1178_);
lean_closure_set(v___f_1179_, 18, v___y_1164_);
v___x_1180_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v___y_1163_, v___f_1179_, v___y_1157_, v___y_1167_, v___y_1160_, v___y_1169_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1160_);
lean_dec(v___y_1167_);
lean_dec_ref(v___y_1157_);
return v___x_1180_;
}
v___jp_1181_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_array_get(v___x_1068_, v___y_1192_, v___x_1198_);
lean_inc(v___x_1199_);
v___x_1200_ = l_Lean_mkFVar(v___x_1199_);
v___x_1201_ = lean_unsigned_to_nat(1u);
v___x_1202_ = lean_array_get(v___x_1068_, v___y_1192_, v___x_1201_);
lean_dec_ref(v___y_1192_);
lean_inc(v___x_1202_);
v___x_1203_ = l_Lean_mkFVar(v___x_1202_);
if (v_tryToSkip_1072_ == 0)
{
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1189_);
v___y_1156_ = v___x_1200_;
v___y_1157_ = v___y_1194_;
v___y_1158_ = v___y_1184_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1196_;
v___y_1161_ = v___y_1186_;
v___y_1162_ = v___x_1203_;
v___y_1163_ = v___y_1190_;
v___y_1164_ = v___x_1201_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1183_;
v___y_1167_ = v___y_1195_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___y_1197_;
v___y_1170_ = v___x_1202_;
v___y_1171_ = v___y_1187_;
v___y_1172_ = v___y_1188_;
v_skip_1173_ = v___y_1193_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1204_; uint8_t v___x_1205_; 
v___x_1204_ = lean_array_get_size(v___y_1189_);
lean_dec_ref(v___y_1189_);
v___x_1205_ = lean_nat_dec_eq(v___x_1204_, v___y_1191_);
lean_dec(v___y_1191_);
if (v___x_1205_ == 0)
{
v___y_1156_ = v___x_1200_;
v___y_1157_ = v___y_1194_;
v___y_1158_ = v___y_1184_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1196_;
v___y_1161_ = v___y_1186_;
v___y_1162_ = v___x_1203_;
v___y_1163_ = v___y_1190_;
v___y_1164_ = v___x_1201_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1183_;
v___y_1167_ = v___y_1195_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___y_1197_;
v___y_1170_ = v___x_1202_;
v___y_1171_ = v___y_1187_;
v___y_1172_ = v___y_1188_;
v_skip_1173_ = v___y_1193_;
goto v___jp_1155_;
}
else
{
lean_object* v___x_1206_; 
lean_inc(v___y_1190_);
v___x_1206_ = l_Lean_MVarId_getType(v___y_1190_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1208_; lean_object* v_a_1209_; uint8_t v___x_1210_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc_n(v_a_1207_, 2);
lean_dec_ref_known(v___x_1206_, 1);
lean_inc(v___x_1199_);
v___x_1208_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1207_, v___x_1199_, v___y_1195_);
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc(v_a_1209_);
lean_dec_ref(v___x_1208_);
v___x_1210_ = lean_unbox(v_a_1209_);
lean_dec(v_a_1209_);
if (v___x_1210_ == 0)
{
lean_object* v___x_1211_; lean_object* v_a_1212_; uint8_t v___x_1213_; 
lean_inc(v___x_1202_);
v___x_1211_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1207_, v___x_1202_, v___y_1195_);
v_a_1212_ = lean_ctor_get(v___x_1211_, 0);
lean_inc(v_a_1212_);
lean_dec_ref(v___x_1211_);
v___x_1213_ = lean_unbox(v_a_1212_);
lean_dec(v_a_1212_);
if (v___x_1213_ == 0)
{
lean_dec_ref(v___x_1203_);
lean_dec_ref(v___x_1200_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v_a_1117_);
lean_dec(v_hFVarId_1067_);
v___y_1079_ = v___y_1194_;
v___y_1080_ = v___y_1195_;
v___y_1081_ = v___y_1197_;
v___y_1082_ = v___y_1196_;
v___y_1083_ = v___x_1202_;
v___y_1084_ = v___x_1199_;
v___y_1085_ = v___y_1190_;
goto v___jp_1078_;
}
else
{
v___y_1156_ = v___x_1200_;
v___y_1157_ = v___y_1194_;
v___y_1158_ = v___y_1184_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1196_;
v___y_1161_ = v___y_1186_;
v___y_1162_ = v___x_1203_;
v___y_1163_ = v___y_1190_;
v___y_1164_ = v___x_1201_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1183_;
v___y_1167_ = v___y_1195_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___y_1197_;
v___y_1170_ = v___x_1202_;
v___y_1171_ = v___y_1187_;
v___y_1172_ = v___y_1188_;
v_skip_1173_ = v___y_1193_;
goto v___jp_1155_;
}
}
else
{
lean_dec(v_a_1207_);
v___y_1156_ = v___x_1200_;
v___y_1157_ = v___y_1194_;
v___y_1158_ = v___y_1184_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1196_;
v___y_1161_ = v___y_1186_;
v___y_1162_ = v___x_1203_;
v___y_1163_ = v___y_1190_;
v___y_1164_ = v___x_1201_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1183_;
v___y_1167_ = v___y_1195_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___y_1197_;
v___y_1170_ = v___x_1202_;
v___y_1171_ = v___y_1187_;
v___y_1172_ = v___y_1188_;
v_skip_1173_ = v___y_1193_;
goto v___jp_1155_;
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec_ref(v___x_1203_);
lean_dec(v___x_1202_);
lean_dec_ref(v___x_1200_);
lean_dec(v___x_1199_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1190_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
v_a_1214_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1206_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1206_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1219_; 
if (v_isShared_1217_ == 0)
{
v___x_1219_ = v___x_1216_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1214_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
}
}
}
v___jp_1222_:
{
lean_object* v___x_1241_; 
lean_inc_ref(v___y_1233_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1238_);
lean_inc_ref(v___y_1237_);
v___x_1241_ = lean_apply_5(v___y_1233_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_, lean_box(0));
if (lean_obj_tag(v___x_1241_) == 0)
{
lean_object* v_a_1242_; uint8_t v___x_1243_; 
v_a_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc(v_a_1242_);
lean_dec_ref_known(v___x_1241_, 1);
v___x_1243_ = lean_unbox(v_a_1242_);
lean_dec(v_a_1242_);
if (v___x_1243_ == 0)
{
lean_dec(v___y_1232_);
lean_del_object(v___x_1152_);
v___y_1182_ = v___y_1223_;
v___y_1183_ = v___y_1224_;
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1226_;
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1229_;
v___y_1189_ = v___y_1230_;
v___y_1190_ = v___y_1231_;
v___y_1191_ = v___y_1234_;
v___y_1192_ = v___y_1235_;
v___y_1193_ = v___y_1236_;
v___y_1194_ = v___y_1237_;
v___y_1195_ = v___y_1238_;
v___y_1196_ = v___y_1239_;
v___y_1197_ = v___y_1240_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1244_; size_t v_sz_1245_; size_t v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1253_; 
v___x_1244_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__11, &l_Lean_Meta_substCore___lam__3___closed__11_once, _init_l_Lean_Meta_substCore___lam__3___closed__11);
v_sz_1245_ = lean_array_size(v___y_1230_);
v___x_1246_ = ((size_t)0ULL);
lean_inc_ref(v___y_1230_);
v___x_1247_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1245_, v___x_1246_, v___y_1230_);
v___x_1248_ = lean_array_to_list(v___x_1247_);
v___x_1249_ = lean_box(0);
v___x_1250_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(v___x_1248_, v___x_1249_);
v___x_1251_ = l_Lean_MessageData_ofList(v___x_1250_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 7);
lean_ctor_set(v___x_1152_, 1, v___x_1251_);
lean_ctor_set(v___x_1152_, 0, v___x_1244_);
v___x_1253_ = v___x_1152_;
goto v_reusejp_1252_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___x_1244_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1251_);
v___x_1253_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1252_;
}
v_reusejp_1252_:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1232_, v___x_1253_, v___y_1237_, v___y_1238_, v___y_1239_, v___y_1240_);
if (lean_obj_tag(v___x_1254_) == 0)
{
lean_dec_ref_known(v___x_1254_, 1);
v___y_1182_ = v___y_1223_;
v___y_1183_ = v___y_1224_;
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1226_;
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1229_;
v___y_1189_ = v___y_1230_;
v___y_1190_ = v___y_1231_;
v___y_1191_ = v___y_1234_;
v___y_1192_ = v___y_1235_;
v___y_1193_ = v___y_1236_;
v___y_1194_ = v___y_1237_;
v___y_1195_ = v___y_1238_;
v___y_1196_ = v___y_1239_;
v___y_1197_ = v___y_1240_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1262_; 
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
v_a_1255_ = lean_ctor_get(v___x_1254_, 0);
v_isSharedCheck_1262_ = !lean_is_exclusive(v___x_1254_);
if (v_isSharedCheck_1262_ == 0)
{
v___x_1257_ = v___x_1254_;
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_a_1255_);
lean_dec(v___x_1254_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1262_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___x_1260_; 
if (v_isShared_1258_ == 0)
{
v___x_1260_ = v___x_1257_;
goto v_reusejp_1259_;
}
else
{
lean_object* v_reuseFailAlloc_1261_; 
v_reuseFailAlloc_1261_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1261_, 0, v_a_1255_);
v___x_1260_ = v_reuseFailAlloc_1261_;
goto v_reusejp_1259_;
}
v_reusejp_1259_:
{
return v___x_1260_;
}
}
}
}
}
}
else
{
lean_object* v_a_1264_; lean_object* v___x_1266_; uint8_t v_isShared_1267_; uint8_t v_isSharedCheck_1271_; 
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec_ref(v___y_1224_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
v_a_1264_ = lean_ctor_get(v___x_1241_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1241_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1266_ = v___x_1241_;
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
else
{
lean_inc(v_a_1264_);
lean_dec(v___x_1241_);
v___x_1266_ = lean_box(0);
v_isShared_1267_ = v_isSharedCheck_1271_;
goto v_resetjp_1265_;
}
v_resetjp_1265_:
{
lean_object* v___x_1269_; 
if (v_isShared_1267_ == 0)
{
v___x_1269_ = v___x_1266_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_a_1264_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
v___jp_1272_:
{
lean_object* v___x_1288_; lean_object* v___x_1289_; 
v___x_1288_ = lean_box(0);
lean_inc(v___y_1281_);
v___x_1289_ = l_Lean_Meta_introNCore(v___y_1279_, v___y_1281_, v___x_1288_, v___y_1283_, v___x_1154_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1289_) == 0)
{
lean_object* v_a_1290_; lean_object* v_fst_1291_; lean_object* v_snd_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1321_; 
v_a_1290_ = lean_ctor_get(v___x_1289_, 0);
lean_inc(v_a_1290_);
lean_dec_ref_known(v___x_1289_, 1);
v_fst_1291_ = lean_ctor_get(v_a_1290_, 0);
v_snd_1292_ = lean_ctor_get(v_a_1290_, 1);
v_isSharedCheck_1321_ = !lean_is_exclusive(v_a_1290_);
if (v_isSharedCheck_1321_ == 0)
{
v___x_1294_ = v_a_1290_;
v_isShared_1295_ = v_isSharedCheck_1321_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_snd_1292_);
lean_inc(v_fst_1291_);
lean_dec(v_a_1290_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1321_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; 
lean_inc_ref(v___y_1282_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
v___x_1296_ = lean_apply_5(v___y_1282_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_, lean_box(0));
if (lean_obj_tag(v___x_1296_) == 0)
{
lean_object* v_a_1297_; uint8_t v___x_1298_; 
v_a_1297_ = lean_ctor_get(v___x_1296_, 0);
lean_inc(v_a_1297_);
lean_dec_ref_known(v___x_1296_, 1);
v___x_1298_ = lean_unbox(v_a_1297_);
lean_dec(v_a_1297_);
if (v___x_1298_ == 0)
{
lean_del_object(v___x_1294_);
lean_inc(v_snd_1292_);
v___y_1223_ = v___y_1273_;
v___y_1224_ = v___y_1274_;
v___y_1225_ = v___y_1275_;
v___y_1226_ = v___x_1288_;
v___y_1227_ = v_snd_1292_;
v___y_1228_ = v___y_1276_;
v___y_1229_ = v___y_1277_;
v___y_1230_ = v___y_1278_;
v___y_1231_ = v_snd_1292_;
v___y_1232_ = v___y_1280_;
v___y_1233_ = v___y_1282_;
v___y_1234_ = v___y_1281_;
v___y_1235_ = v_fst_1291_;
v___y_1236_ = v___y_1283_;
v___y_1237_ = v___y_1284_;
v___y_1238_ = v___y_1285_;
v___y_1239_ = v___y_1286_;
v___y_1240_ = v___y_1287_;
goto v___jp_1222_;
}
else
{
lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1302_; 
v___x_1299_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__13, &l_Lean_Meta_substCore___lam__3___closed__13_once, _init_l_Lean_Meta_substCore___lam__3___closed__13);
lean_inc(v_snd_1292_);
v___x_1300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1300_, 0, v_snd_1292_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set_tag(v___x_1294_, 7);
lean_ctor_set(v___x_1294_, 1, v___x_1300_);
lean_ctor_set(v___x_1294_, 0, v___x_1299_);
v___x_1302_ = v___x_1294_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1312_, 1, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
lean_object* v___x_1303_; 
lean_inc(v___y_1280_);
v___x_1303_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1280_, v___x_1302_, v___y_1284_, v___y_1285_, v___y_1286_, v___y_1287_);
if (lean_obj_tag(v___x_1303_) == 0)
{
lean_dec_ref_known(v___x_1303_, 1);
lean_inc(v_snd_1292_);
v___y_1223_ = v___y_1273_;
v___y_1224_ = v___y_1274_;
v___y_1225_ = v___y_1275_;
v___y_1226_ = v___x_1288_;
v___y_1227_ = v_snd_1292_;
v___y_1228_ = v___y_1276_;
v___y_1229_ = v___y_1277_;
v___y_1230_ = v___y_1278_;
v___y_1231_ = v_snd_1292_;
v___y_1232_ = v___y_1280_;
v___y_1233_ = v___y_1282_;
v___y_1234_ = v___y_1281_;
v___y_1235_ = v_fst_1291_;
v___y_1236_ = v___y_1283_;
v___y_1237_ = v___y_1284_;
v___y_1238_ = v___y_1285_;
v___y_1239_ = v___y_1286_;
v___y_1240_ = v___y_1287_;
goto v___jp_1222_;
}
else
{
lean_object* v_a_1304_; lean_object* v___x_1306_; uint8_t v_isShared_1307_; uint8_t v_isSharedCheck_1311_; 
lean_dec(v_snd_1292_);
lean_dec(v_fst_1291_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
v_a_1304_ = lean_ctor_get(v___x_1303_, 0);
v_isSharedCheck_1311_ = !lean_is_exclusive(v___x_1303_);
if (v_isSharedCheck_1311_ == 0)
{
v___x_1306_ = v___x_1303_;
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
else
{
lean_inc(v_a_1304_);
lean_dec(v___x_1303_);
v___x_1306_ = lean_box(0);
v_isShared_1307_ = v_isSharedCheck_1311_;
goto v_resetjp_1305_;
}
v_resetjp_1305_:
{
lean_object* v___x_1309_; 
if (v_isShared_1307_ == 0)
{
v___x_1309_ = v___x_1306_;
goto v_reusejp_1308_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v_a_1304_);
v___x_1309_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1308_;
}
v_reusejp_1308_:
{
return v___x_1309_;
}
}
}
}
}
}
else
{
lean_object* v_a_1313_; lean_object* v___x_1315_; uint8_t v_isShared_1316_; uint8_t v_isSharedCheck_1320_; 
lean_del_object(v___x_1294_);
lean_dec(v_snd_1292_);
lean_dec(v_fst_1291_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
v_a_1313_ = lean_ctor_get(v___x_1296_, 0);
v_isSharedCheck_1320_ = !lean_is_exclusive(v___x_1296_);
if (v_isSharedCheck_1320_ == 0)
{
v___x_1315_ = v___x_1296_;
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
else
{
lean_inc(v_a_1313_);
lean_dec(v___x_1296_);
v___x_1315_ = lean_box(0);
v_isShared_1316_ = v_isSharedCheck_1320_;
goto v_resetjp_1314_;
}
v_resetjp_1314_:
{
lean_object* v___x_1318_; 
if (v_isShared_1316_ == 0)
{
v___x_1318_ = v___x_1315_;
goto v_reusejp_1317_;
}
else
{
lean_object* v_reuseFailAlloc_1319_; 
v_reuseFailAlloc_1319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1319_, 0, v_a_1313_);
v___x_1318_ = v_reuseFailAlloc_1319_;
goto v_reusejp_1317_;
}
v_reusejp_1317_:
{
return v___x_1318_;
}
}
}
}
}
else
{
lean_object* v_a_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1329_; 
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec_ref(v___y_1278_);
lean_dec(v___y_1277_);
lean_dec(v___y_1276_);
lean_dec(v___y_1275_);
lean_dec_ref(v___y_1274_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
v_a_1322_ = lean_ctor_get(v___x_1289_, 0);
v_isSharedCheck_1329_ = !lean_is_exclusive(v___x_1289_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1324_ = v___x_1289_;
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_a_1322_);
lean_dec(v___x_1289_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1329_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1327_; 
if (v_isShared_1325_ == 0)
{
v___x_1327_ = v___x_1324_;
goto v_reusejp_1326_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_a_1322_);
v___x_1327_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1326_;
}
v_reusejp_1326_:
{
return v___x_1327_;
}
}
}
}
v___jp_1330_:
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; lean_object* v___x_1345_; 
v___x_1340_ = lean_unsigned_to_nat(2u);
v___x_1341_ = lean_mk_empty_array_with_capacity(v___x_1340_);
v___x_1342_ = lean_array_push(v___x_1341_, v___y_1335_);
lean_inc(v_hFVarId_1067_);
v___x_1343_ = lean_array_push(v___x_1342_, v_hFVarId_1067_);
v___x_1344_ = 0;
v___x_1345_ = l_Lean_MVarId_revert(v_mvarId_1066_, v___x_1343_, v___x_1154_, v___x_1344_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1345_) == 0)
{
lean_object* v_a_1346_; lean_object* v_fst_1347_; lean_object* v_snd_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1377_; 
v_a_1346_ = lean_ctor_get(v___x_1345_, 0);
lean_inc(v_a_1346_);
lean_dec_ref_known(v___x_1345_, 1);
v_fst_1347_ = lean_ctor_get(v_a_1346_, 0);
v_snd_1348_ = lean_ctor_get(v_a_1346_, 1);
v_isSharedCheck_1377_ = !lean_is_exclusive(v_a_1346_);
if (v_isSharedCheck_1377_ == 0)
{
v___x_1350_ = v_a_1346_;
v_isShared_1351_ = v_isSharedCheck_1377_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_snd_1348_);
lean_inc(v_fst_1347_);
lean_dec(v_a_1346_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1377_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; 
lean_inc_ref(v___y_1334_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
v___x_1352_ = lean_apply_5(v___y_1334_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_, lean_box(0));
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_object* v_a_1353_; uint8_t v___x_1354_; 
v_a_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_a_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = lean_unbox(v_a_1353_);
lean_dec(v_a_1353_);
if (v___x_1354_ == 0)
{
lean_del_object(v___x_1350_);
lean_inc(v_fst_1347_);
v___y_1273_ = v___x_1344_;
v___y_1274_ = v_fst_1347_;
v___y_1275_ = v___y_1331_;
v___y_1276_ = v___x_1340_;
v___y_1277_ = v___y_1332_;
v___y_1278_ = v_fst_1347_;
v___y_1279_ = v_snd_1348_;
v___y_1280_ = v___y_1333_;
v___y_1281_ = v___x_1340_;
v___y_1282_ = v___y_1334_;
v___y_1283_ = v___x_1344_;
v___y_1284_ = v___y_1336_;
v___y_1285_ = v___y_1337_;
v___y_1286_ = v___y_1338_;
v___y_1287_ = v___y_1339_;
goto v___jp_1272_;
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1358_; 
v___x_1355_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__15, &l_Lean_Meta_substCore___lam__3___closed__15_once, _init_l_Lean_Meta_substCore___lam__3___closed__15);
lean_inc(v_snd_1348_);
v___x_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1356_, 0, v_snd_1348_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set_tag(v___x_1350_, 7);
lean_ctor_set(v___x_1350_, 1, v___x_1356_);
lean_ctor_set(v___x_1350_, 0, v___x_1355_);
v___x_1358_ = v___x_1350_;
goto v_reusejp_1357_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v___x_1355_);
lean_ctor_set(v_reuseFailAlloc_1368_, 1, v___x_1356_);
v___x_1358_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1357_;
}
v_reusejp_1357_:
{
lean_object* v___x_1359_; 
lean_inc(v___y_1333_);
v___x_1359_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1333_, v___x_1358_, v___y_1336_, v___y_1337_, v___y_1338_, v___y_1339_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_dec_ref_known(v___x_1359_, 1);
lean_inc(v_fst_1347_);
v___y_1273_ = v___x_1344_;
v___y_1274_ = v_fst_1347_;
v___y_1275_ = v___y_1331_;
v___y_1276_ = v___x_1340_;
v___y_1277_ = v___y_1332_;
v___y_1278_ = v_fst_1347_;
v___y_1279_ = v_snd_1348_;
v___y_1280_ = v___y_1333_;
v___y_1281_ = v___x_1340_;
v___y_1282_ = v___y_1334_;
v___y_1283_ = v___x_1344_;
v___y_1284_ = v___y_1336_;
v___y_1285_ = v___y_1337_;
v___y_1286_ = v___y_1338_;
v___y_1287_ = v___y_1339_;
goto v___jp_1272_;
}
else
{
lean_object* v_a_1360_; lean_object* v___x_1362_; uint8_t v_isShared_1363_; uint8_t v_isSharedCheck_1367_; 
lean_dec(v_snd_1348_);
lean_dec(v_fst_1347_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec(v___y_1331_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
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
else
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
lean_del_object(v___x_1350_);
lean_dec(v_snd_1348_);
lean_dec(v_fst_1347_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec(v___y_1331_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
v_a_1369_ = lean_ctor_get(v___x_1352_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1352_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1352_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1352_);
v___x_1371_ = lean_box(0);
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
v_resetjp_1370_:
{
lean_object* v___x_1374_; 
if (v_isShared_1372_ == 0)
{
v___x_1374_ = v___x_1371_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1375_; 
v_reuseFailAlloc_1375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1375_, 0, v_a_1369_);
v___x_1374_ = v_reuseFailAlloc_1375_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
return v___x_1374_;
}
}
}
}
}
else
{
lean_object* v_a_1378_; lean_object* v___x_1380_; uint8_t v_isShared_1381_; uint8_t v_isSharedCheck_1385_; 
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1333_);
lean_dec(v___y_1332_);
lean_dec(v___y_1331_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
v_a_1378_ = lean_ctor_get(v___x_1345_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1345_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1380_ = v___x_1345_;
v_isShared_1381_ = v_isSharedCheck_1385_;
goto v_resetjp_1379_;
}
else
{
lean_inc(v_a_1378_);
lean_dec(v___x_1345_);
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
v___jp_1386_:
{
lean_object* v___x_1398_; lean_object* v_a_1399_; uint8_t v___x_1400_; 
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1393_);
v___x_1398_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v___y_1393_, v___y_1392_, v___y_1395_);
v_a_1399_ = lean_ctor_get(v___x_1398_, 0);
lean_inc(v_a_1399_);
lean_dec_ref(v___x_1398_);
v___x_1400_ = lean_unbox(v_a_1399_);
lean_dec(v_a_1399_);
if (v___x_1400_ == 0)
{
lean_dec_ref(v___y_1393_);
lean_dec_ref(v___y_1391_);
lean_del_object(v___x_1147_);
lean_del_object(v___x_1143_);
v___y_1331_ = v___y_1387_;
v___y_1332_ = v___y_1388_;
v___y_1333_ = v___y_1389_;
v___y_1334_ = v___y_1390_;
v___y_1335_ = v___y_1392_;
v___y_1336_ = v___y_1394_;
v___y_1337_ = v___y_1395_;
v___y_1338_ = v___y_1396_;
v___y_1339_ = v___y_1397_;
goto v___jp_1330_;
}
else
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1401_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_1402_ = l_Lean_MessageData_ofExpr(v___y_1391_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 7);
lean_ctor_set(v___x_1147_, 1, v___x_1402_);
lean_ctor_set(v___x_1147_, 0, v___x_1401_);
v___x_1404_ = v___x_1147_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1421_; 
v_reuseFailAlloc_1421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1421_, 0, v___x_1401_);
lean_ctor_set(v_reuseFailAlloc_1421_, 1, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1421_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1410_; 
v___x_1405_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__19, &l_Lean_Meta_substCore___lam__3___closed__19_once, _init_l_Lean_Meta_substCore___lam__3___closed__19);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
v___x_1407_ = l_Lean_indentExpr(v___y_1393_);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1408_);
v___x_1410_ = v___x_1143_;
goto v_reusejp_1409_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v___x_1408_);
v___x_1410_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1409_;
}
v_reusejp_1409_:
{
lean_object* v___x_1411_; 
lean_inc(v_mvarId_1066_);
v___x_1411_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1118_, v_mvarId_1066_, v___x_1410_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1411_) == 0)
{
lean_dec_ref_known(v___x_1411_, 1);
v___y_1331_ = v___y_1387_;
v___y_1332_ = v___y_1388_;
v___y_1333_ = v___y_1389_;
v___y_1334_ = v___y_1390_;
v___y_1335_ = v___y_1392_;
v___y_1336_ = v___y_1394_;
v___y_1337_ = v___y_1395_;
v___y_1338_ = v___y_1396_;
v___y_1339_ = v___y_1397_;
goto v___jp_1330_;
}
else
{
lean_object* v_a_1412_; lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1419_; 
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1392_);
lean_dec(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec(v___y_1387_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
v_a_1412_ = lean_ctor_get(v___x_1411_, 0);
v_isSharedCheck_1419_ = !lean_is_exclusive(v___x_1411_);
if (v_isSharedCheck_1419_ == 0)
{
v___x_1414_ = v___x_1411_;
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
else
{
lean_inc(v_a_1412_);
lean_dec(v___x_1411_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1419_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v___x_1417_; 
if (v_isShared_1415_ == 0)
{
v___x_1417_ = v___x_1414_;
goto v_reusejp_1416_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v_a_1412_);
v___x_1417_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1416_;
}
v_reusejp_1416_:
{
return v___x_1417_;
}
}
}
}
}
}
}
v___jp_1422_:
{
lean_object* v___x_1425_; 
v___x_1425_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1424_, v___y_1074_);
if (lean_obj_tag(v___y_1423_) == 1)
{
lean_object* v_a_1426_; lean_object* v_fvarId_1427_; lean_object* v___x_1428_; lean_object* v___f_1429_; lean_object* v___x_1430_; lean_object* v_a_1431_; uint8_t v___x_1432_; 
lean_dec_ref(v___x_1122_);
v_a_1426_ = lean_ctor_get(v___x_1425_, 0);
lean_inc(v_a_1426_);
lean_dec_ref(v___x_1425_);
v_fvarId_1427_ = lean_ctor_get(v___y_1423_, 0);
lean_inc(v_fvarId_1427_);
v___x_1428_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___f_1429_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__23));
v___x_1430_ = l_Lean_Meta_substCore___lam__0(v___x_1428_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
v_a_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc(v_a_1431_);
lean_dec_ref(v___x_1430_);
v___x_1432_ = lean_unbox(v_a_1431_);
lean_dec(v_a_1431_);
if (v___x_1432_ == 0)
{
lean_inc(v_fvarId_1427_);
v___y_1387_ = v___x_1428_;
v___y_1388_ = v_fvarId_1427_;
v___y_1389_ = v___x_1428_;
v___y_1390_ = v___f_1429_;
v___y_1391_ = v___y_1423_;
v___y_1392_ = v_fvarId_1427_;
v___y_1393_ = v_a_1426_;
v___y_1394_ = v___y_1073_;
v___y_1395_ = v___y_1074_;
v___y_1396_ = v___y_1075_;
v___y_1397_ = v___y_1076_;
goto v___jp_1386_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; 
v___x_1433_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__25, &l_Lean_Meta_substCore___lam__3___closed__25_once, _init_l_Lean_Meta_substCore___lam__3___closed__25);
lean_inc_ref(v___y_1423_);
v___x_1434_ = l_Lean_MessageData_ofExpr(v___y_1423_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__27, &l_Lean_Meta_substCore___lam__3___closed__27_once, _init_l_Lean_Meta_substCore___lam__3___closed__27);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
lean_inc(v_fvarId_1427_);
v___x_1438_ = l_Lean_MessageData_ofName(v_fvarId_1427_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__29, &l_Lean_Meta_substCore___lam__3___closed__29_once, _init_l_Lean_Meta_substCore___lam__3___closed__29);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_inc(v_a_1426_);
v___x_1442_ = l_Lean_MessageData_ofExpr(v_a_1426_);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_1428_, v___x_1443_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1444_) == 0)
{
lean_dec_ref_known(v___x_1444_, 1);
lean_inc(v_fvarId_1427_);
v___y_1387_ = v___x_1428_;
v___y_1388_ = v_fvarId_1427_;
v___y_1389_ = v___x_1428_;
v___y_1390_ = v___f_1429_;
v___y_1391_ = v___y_1423_;
v___y_1392_ = v_fvarId_1427_;
v___y_1393_ = v_a_1426_;
v___y_1394_ = v___y_1073_;
v___y_1395_ = v___y_1074_;
v___y_1396_ = v___y_1075_;
v___y_1397_ = v___y_1076_;
goto v___jp_1386_;
}
else
{
lean_object* v_a_1445_; lean_object* v___x_1447_; uint8_t v_isShared_1448_; uint8_t v_isSharedCheck_1452_; 
lean_dec(v_fvarId_1427_);
lean_dec_ref_known(v___y_1423_, 1);
lean_dec(v_a_1426_);
lean_del_object(v___x_1152_);
lean_del_object(v___x_1147_);
lean_del_object(v___x_1143_);
lean_dec(v_a_1117_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
v_a_1445_ = lean_ctor_get(v___x_1444_, 0);
v_isSharedCheck_1452_ = !lean_is_exclusive(v___x_1444_);
if (v_isSharedCheck_1452_ == 0)
{
v___x_1447_ = v___x_1444_;
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
else
{
lean_inc(v_a_1445_);
lean_dec(v___x_1444_);
v___x_1447_ = lean_box(0);
v_isShared_1448_ = v_isSharedCheck_1452_;
goto v_resetjp_1446_;
}
v_resetjp_1446_:
{
lean_object* v___x_1450_; 
if (v_isShared_1448_ == 0)
{
v___x_1450_ = v___x_1447_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1451_; 
v_reuseFailAlloc_1451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1451_, 0, v_a_1445_);
v___x_1450_ = v_reuseFailAlloc_1451_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
return v___x_1450_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1425_);
lean_del_object(v___x_1152_);
lean_del_object(v___x_1147_);
lean_del_object(v___x_1143_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
if (v_symm_1071_ == 0)
{
lean_object* v___x_1453_; 
v___x_1453_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__30));
v___y_1124_ = v___y_1423_;
v___y_1125_ = v___x_1453_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1454_; 
v___x_1454_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__31));
v___y_1124_ = v___y_1423_;
v___y_1125_ = v___x_1454_;
goto v___jp_1123_;
}
}
}
v___jp_1455_:
{
lean_object* v___x_1457_; 
v___x_1457_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1456_, v___y_1074_);
if (v_symm_1071_ == 0)
{
lean_object* v_a_1458_; 
lean_dec(v_fst_1149_);
v_a_1458_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1458_);
lean_dec_ref(v___x_1457_);
v___y_1423_ = v_a_1458_;
v___y_1424_ = v_snd_1150_;
goto v___jp_1422_;
}
else
{
lean_object* v_a_1459_; 
lean_dec(v_snd_1150_);
v_a_1459_ = lean_ctor_get(v___x_1457_, 0);
lean_inc(v_a_1459_);
lean_dec_ref(v___x_1457_);
v___y_1423_ = v_a_1459_;
v___y_1424_ = v_fst_1149_;
goto v___jp_1422_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1471_; 
lean_dec_ref(v___x_1122_);
lean_dec(v_a_1117_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
v_a_1464_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1471_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1471_ == 0)
{
v___x_1466_ = v___x_1137_;
v_isShared_1467_ = v_isSharedCheck_1471_;
goto v_resetjp_1465_;
}
else
{
lean_inc(v_a_1464_);
lean_dec(v___x_1137_);
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
v___jp_1123_:
{
lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; 
v___x_1126_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__3, &l_Lean_Meta_substCore___lam__3___closed__3_once, _init_l_Lean_Meta_substCore___lam__3___closed__3);
lean_inc_ref(v___y_1125_);
v___x_1127_ = l_Lean_stringToMessageData(v___y_1125_);
v___x_1128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1126_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_indentExpr(v___x_1122_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__5, &l_Lean_Meta_substCore___lam__3___closed__5_once, _init_l_Lean_Meta_substCore___lam__3___closed__5);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_indentExpr(v___y_1124_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1134_);
v___x_1136_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1118_, v_mvarId_1066_, v___x_1135_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
return v___x_1136_;
}
}
else
{
lean_object* v_a_1472_; lean_object* v___x_1474_; uint8_t v_isShared_1475_; uint8_t v_isSharedCheck_1479_; 
lean_dec(v_a_1117_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
v_a_1472_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1479_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1479_ == 0)
{
v___x_1474_ = v___x_1120_;
v_isShared_1475_ = v_isSharedCheck_1479_;
goto v_resetjp_1473_;
}
else
{
lean_inc(v_a_1472_);
lean_dec(v___x_1120_);
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
lean_dec(v_a_1117_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
v_a_1480_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1487_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1487_ == 0)
{
v___x_1482_ = v___x_1119_;
v_isShared_1483_ = v_isSharedCheck_1487_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1119_);
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
}
else
{
lean_object* v_a_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1495_; 
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
v_a_1488_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1495_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1495_ == 0)
{
v___x_1490_ = v___x_1116_;
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
else
{
lean_inc(v_a_1488_);
lean_dec(v___x_1116_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1495_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1493_; 
if (v_isShared_1491_ == 0)
{
v___x_1493_ = v___x_1490_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_a_1488_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
v___jp_1078_:
{
if (v_clearH_1069_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v___y_1084_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_fvarSubst_1070_);
lean_ctor_set(v___x_1086_, 1, v___y_1085_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_MVarId_clear(v___y_1085_, v___y_1083_, v___y_1079_, v___y_1080_, v___y_1082_, v___y_1081_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = l_Lean_MVarId_clear(v_a_1089_, v___y_1084_, v___y_1079_, v___y_1080_, v___y_1082_, v___y_1081_);
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1099_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1099_ == 0)
{
v___x_1093_ = v___x_1090_;
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
else
{
lean_inc(v_a_1091_);
lean_dec(v___x_1090_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1099_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1097_; 
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v_fvarSubst_1070_);
lean_ctor_set(v___x_1095_, 1, v_a_1091_);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 0, v___x_1095_);
v___x_1097_ = v___x_1093_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v___x_1095_);
v___x_1097_ = v_reuseFailAlloc_1098_;
goto v_reusejp_1096_;
}
v_reusejp_1096_:
{
return v___x_1097_;
}
}
}
else
{
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec(v_fvarSubst_1070_);
v_a_1100_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1090_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1090_);
v___x_1102_ = lean_box(0);
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
v_resetjp_1101_:
{
lean_object* v___x_1105_; 
if (v_isShared_1103_ == 0)
{
v___x_1105_ = v___x_1102_;
goto v_reusejp_1104_;
}
else
{
lean_object* v_reuseFailAlloc_1106_; 
v_reuseFailAlloc_1106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_a_1100_);
v___x_1105_ = v_reuseFailAlloc_1106_;
goto v_reusejp_1104_;
}
v_reusejp_1104_:
{
return v___x_1105_;
}
}
}
}
else
{
lean_object* v_a_1108_; lean_object* v___x_1110_; uint8_t v_isShared_1111_; uint8_t v_isSharedCheck_1115_; 
lean_dec(v___y_1084_);
lean_dec_ref(v___y_1082_);
lean_dec(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v_fvarSubst_1070_);
v_a_1108_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1115_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1115_ == 0)
{
v___x_1110_ = v___x_1088_;
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
else
{
lean_inc(v_a_1108_);
lean_dec(v___x_1088_);
v___x_1110_ = lean_box(0);
v_isShared_1111_ = v_isSharedCheck_1115_;
goto v_resetjp_1109_;
}
v_resetjp_1109_:
{
lean_object* v___x_1113_; 
if (v_isShared_1111_ == 0)
{
v___x_1113_ = v___x_1110_;
goto v_reusejp_1112_;
}
else
{
lean_object* v_reuseFailAlloc_1114_; 
v_reuseFailAlloc_1114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1114_, 0, v_a_1108_);
v___x_1113_ = v_reuseFailAlloc_1114_;
goto v_reusejp_1112_;
}
v_reusejp_1112_:
{
return v___x_1113_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3___boxed(lean_object* v_mvarId_1496_, lean_object* v_hFVarId_1497_, lean_object* v___x_1498_, lean_object* v_clearH_1499_, lean_object* v_fvarSubst_1500_, lean_object* v_symm_1501_, lean_object* v_tryToSkip_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_){
_start:
{
uint8_t v_clearH_boxed_1508_; uint8_t v_symm_boxed_1509_; uint8_t v_tryToSkip_boxed_1510_; lean_object* v_res_1511_; 
v_clearH_boxed_1508_ = lean_unbox(v_clearH_1499_);
v_symm_boxed_1509_ = lean_unbox(v_symm_1501_);
v_tryToSkip_boxed_1510_ = lean_unbox(v_tryToSkip_1502_);
v_res_1511_ = l_Lean_Meta_substCore___lam__3(v_mvarId_1496_, v_hFVarId_1497_, v___x_1498_, v_clearH_boxed_1508_, v_fvarSubst_1500_, v_symm_boxed_1509_, v_tryToSkip_boxed_1510_, v___y_1503_, v___y_1504_, v___y_1505_, v___y_1506_);
lean_dec(v___x_1498_);
return v_res_1511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object* v_mvarId_1512_, lean_object* v_hFVarId_1513_, uint8_t v_symm_1514_, lean_object* v_fvarSubst_1515_, uint8_t v_clearH_1516_, uint8_t v_tryToSkip_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___f_1527_; lean_object* v___x_1528_; 
v___x_1523_ = lean_box(0);
v___x_1524_ = lean_box(v_clearH_1516_);
v___x_1525_ = lean_box(v_symm_1514_);
v___x_1526_ = lean_box(v_tryToSkip_1517_);
lean_inc(v_mvarId_1512_);
v___f_1527_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__3___boxed), 12, 7);
lean_closure_set(v___f_1527_, 0, v_mvarId_1512_);
lean_closure_set(v___f_1527_, 1, v_hFVarId_1513_);
lean_closure_set(v___f_1527_, 2, v___x_1523_);
lean_closure_set(v___f_1527_, 3, v___x_1524_);
lean_closure_set(v___f_1527_, 4, v_fvarSubst_1515_);
lean_closure_set(v___f_1527_, 5, v___x_1525_);
lean_closure_set(v___f_1527_, 6, v___x_1526_);
v___x_1528_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1512_, v___f_1527_, v_a_1518_, v_a_1519_, v_a_1520_, v_a_1521_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* v_mvarId_1529_, lean_object* v_hFVarId_1530_, lean_object* v_symm_1531_, lean_object* v_fvarSubst_1532_, lean_object* v_clearH_1533_, lean_object* v_tryToSkip_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_){
_start:
{
uint8_t v_symm_boxed_1540_; uint8_t v_clearH_boxed_1541_; uint8_t v_tryToSkip_boxed_1542_; lean_object* v_res_1543_; 
v_symm_boxed_1540_ = lean_unbox(v_symm_1531_);
v_clearH_boxed_1541_ = lean_unbox(v_clearH_1533_);
v_tryToSkip_boxed_1542_ = lean_unbox(v_tryToSkip_1534_);
v_res_1543_ = l_Lean_Meta_substCore(v_mvarId_1529_, v_hFVarId_1530_, v_symm_boxed_1540_, v_fvarSubst_1532_, v_clearH_boxed_1541_, v_tryToSkip_boxed_1542_, v_a_1535_, v_a_1536_, v_a_1537_, v_a_1538_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(lean_object* v_fst_1544_, lean_object* v_fst_1545_, lean_object* v_n_1546_, lean_object* v_i_1547_, lean_object* v_a_1548_, lean_object* v_a_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_){
_start:
{
lean_object* v___x_1555_; 
v___x_1555_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_1544_, v_fst_1545_, v_n_1546_, v_i_1547_, v_a_1549_);
return v___x_1555_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___boxed(lean_object* v_fst_1556_, lean_object* v_fst_1557_, lean_object* v_n_1558_, lean_object* v_i_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_){
_start:
{
lean_object* v_res_1567_; 
v_res_1567_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(v_fst_1556_, v_fst_1557_, v_n_1558_, v_i_1559_, v_a_1560_, v_a_1561_, v___y_1562_, v___y_1563_, v___y_1564_, v___y_1565_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v_n_1558_);
lean_dec_ref(v_fst_1557_);
lean_dec_ref(v_fst_1556_);
return v_res_1567_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(lean_object* v_mvarId_1568_, lean_object* v_val_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_){
_start:
{
lean_object* v___x_1575_; 
v___x_1575_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_mvarId_1568_, v_val_1569_, v___y_1571_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___boxed(lean_object* v_mvarId_1576_, lean_object* v_val_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(v_mvarId_1576_, v_val_1577_, v___y_1578_, v___y_1579_, v___y_1580_, v___y_1581_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(lean_object* v_00_u03b1_1584_, lean_object* v_name_1585_, uint8_t v_bi_1586_, lean_object* v_type_1587_, lean_object* v_k_1588_, uint8_t v_kind_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_1585_, v_bi_1586_, v_type_1587_, v_k_1588_, v_kind_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1596_, lean_object* v_name_1597_, lean_object* v_bi_1598_, lean_object* v_type_1599_, lean_object* v_k_1600_, lean_object* v_kind_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_){
_start:
{
uint8_t v_bi_boxed_1607_; uint8_t v_kind_boxed_1608_; lean_object* v_res_1609_; 
v_bi_boxed_1607_ = lean_unbox(v_bi_1598_);
v_kind_boxed_1608_ = lean_unbox(v_kind_1601_);
v_res_1609_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(v_00_u03b1_1596_, v_name_1597_, v_bi_boxed_1607_, v_type_1599_, v_k_1600_, v_kind_boxed_1608_, v___y_1602_, v___y_1603_, v___y_1604_, v___y_1605_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
return v_res_1609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(lean_object* v_00_u03b1_1610_, lean_object* v_name_1611_, lean_object* v_type_1612_, lean_object* v_k_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_){
_start:
{
lean_object* v___x_1619_; 
v___x_1619_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v_name_1611_, v_type_1612_, v_k_1613_, v___y_1614_, v___y_1615_, v___y_1616_, v___y_1617_);
return v___x_1619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___boxed(lean_object* v_00_u03b1_1620_, lean_object* v_name_1621_, lean_object* v_type_1622_, lean_object* v_k_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_){
_start:
{
lean_object* v_res_1629_; 
v_res_1629_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(v_00_u03b1_1620_, v_name_1621_, v_type_1622_, v_k_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
return v_res_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6(lean_object* v_00_u03b2_1630_, lean_object* v_x_1631_, lean_object* v_x_1632_, lean_object* v_x_1633_){
_start:
{
lean_object* v___x_1634_; 
v___x_1634_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_x_1631_, v_x_1632_, v_x_1633_);
return v___x_1634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1635_, lean_object* v_x_1636_, size_t v_x_1637_, size_t v_x_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_1636_, v_x_1637_, v_x_1638_, v_x_1639_, v_x_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_){
_start:
{
size_t v_x_35606__boxed_1648_; size_t v_x_35607__boxed_1649_; lean_object* v_res_1650_; 
v_x_35606__boxed_1648_ = lean_unbox_usize(v_x_1644_);
lean_dec(v_x_1644_);
v_x_35607__boxed_1649_ = lean_unbox_usize(v_x_1645_);
lean_dec(v_x_1645_);
v_res_1650_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(v_00_u03b2_1642_, v_x_1643_, v_x_35606__boxed_1648_, v_x_35607__boxed_1649_, v_x_1646_, v_x_1647_);
return v_res_1650_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13(lean_object* v_00_u03b2_1651_, lean_object* v_n_1652_, lean_object* v_k_1653_, lean_object* v_v_1654_){
_start:
{
lean_object* v___x_1655_; 
v___x_1655_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v_n_1652_, v_k_1653_, v_v_1654_);
return v___x_1655_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1656_, size_t v_depth_1657_, lean_object* v_keys_1658_, lean_object* v_vals_1659_, lean_object* v_heq_1660_, lean_object* v_i_1661_, lean_object* v_entries_1662_){
_start:
{
lean_object* v___x_1663_; 
v___x_1663_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_1657_, v_keys_1658_, v_vals_1659_, v_i_1661_, v_entries_1662_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1664_, lean_object* v_depth_1665_, lean_object* v_keys_1666_, lean_object* v_vals_1667_, lean_object* v_heq_1668_, lean_object* v_i_1669_, lean_object* v_entries_1670_){
_start:
{
size_t v_depth_boxed_1671_; lean_object* v_res_1672_; 
v_depth_boxed_1671_ = lean_unbox_usize(v_depth_1665_);
lean_dec(v_depth_1665_);
v_res_1672_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(v_00_u03b2_1664_, v_depth_boxed_1671_, v_keys_1666_, v_vals_1667_, v_heq_1668_, v_i_1669_, v_entries_1670_);
lean_dec_ref(v_vals_1667_);
lean_dec_ref(v_keys_1666_);
return v_res_1672_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_){
_start:
{
lean_object* v___x_1678_; 
v___x_1678_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(v_x_1674_, v_x_1675_, v_x_1676_, v_x_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* v_fvarId_1682_, lean_object* v_mvarId_1683_, uint8_t v_tryToClear_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_){
_start:
{
lean_object* v___x_1690_; 
lean_inc(v_fvarId_1682_);
v___x_1690_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1682_, v___y_1685_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1690_) == 0)
{
lean_object* v_a_1691_; lean_object* v___x_1692_; lean_object* v___x_1693_; 
v_a_1691_ = lean_ctor_get(v___x_1690_, 0);
lean_inc(v_a_1691_);
lean_dec_ref_known(v___x_1690_, 1);
v___x_1692_ = l_Lean_LocalDecl_type(v_a_1691_);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
v___x_1693_ = lean_whnf(v___x_1692_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1693_) == 0)
{
lean_object* v_a_1694_; lean_object* v___x_1696_; uint8_t v_isShared_1697_; uint8_t v_isSharedCheck_1778_; 
v_a_1694_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1696_ = v___x_1693_;
v_isShared_1697_ = v_isSharedCheck_1778_;
goto v_resetjp_1695_;
}
else
{
lean_inc(v_a_1694_);
lean_dec(v___x_1693_);
v___x_1696_ = lean_box(0);
v_isShared_1697_ = v_isSharedCheck_1778_;
goto v_resetjp_1695_;
}
v_resetjp_1695_:
{
lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1698_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_1699_ = lean_unsigned_to_nat(4u);
v___x_1700_ = l_Lean_Expr_isAppOfArity(v_a_1694_, v___x_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; lean_object* v___x_1703_; 
lean_dec(v_a_1694_);
lean_dec(v_a_1691_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_fvarId_1682_);
lean_ctor_set(v___x_1701_, 1, v_mvarId_1683_);
if (v_isShared_1697_ == 0)
{
lean_ctor_set(v___x_1696_, 0, v___x_1701_);
v___x_1703_ = v___x_1696_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1701_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
else
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
lean_del_object(v___x_1696_);
v___x_1705_ = l_Lean_Expr_appFn_x21(v_a_1694_);
v___x_1706_ = l_Lean_Expr_appFn_x21(v___x_1705_);
v___x_1707_ = l_Lean_Expr_appFn_x21(v___x_1706_);
v___x_1708_ = l_Lean_Expr_appArg_x21(v___x_1707_);
lean_dec_ref(v___x_1707_);
v___x_1709_ = l_Lean_Expr_appArg_x21(v___x_1705_);
lean_dec_ref(v___x_1705_);
v___x_1710_ = l_Lean_Meta_isExprDefEq(v___x_1708_, v___x_1709_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_a_1711_; lean_object* v___x_1713_; uint8_t v_isShared_1714_; uint8_t v_isSharedCheck_1769_; 
v_a_1711_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1769_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1769_ == 0)
{
v___x_1713_ = v___x_1710_;
v_isShared_1714_ = v_isSharedCheck_1769_;
goto v_resetjp_1712_;
}
else
{
lean_inc(v_a_1711_);
lean_dec(v___x_1710_);
v___x_1713_ = lean_box(0);
v_isShared_1714_ = v_isSharedCheck_1769_;
goto v_resetjp_1712_;
}
v_resetjp_1712_:
{
uint8_t v___x_1715_; 
v___x_1715_ = lean_unbox(v_a_1711_);
if (v___x_1715_ == 0)
{
lean_object* v___x_1716_; lean_object* v___x_1718_; 
lean_dec(v_a_1711_);
lean_dec_ref(v___x_1706_);
lean_dec(v_a_1694_);
lean_dec(v_a_1691_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
v___x_1716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1716_, 0, v_fvarId_1682_);
lean_ctor_set(v___x_1716_, 1, v_mvarId_1683_);
if (v_isShared_1714_ == 0)
{
lean_ctor_set(v___x_1713_, 0, v___x_1716_);
v___x_1718_ = v___x_1713_;
goto v_reusejp_1717_;
}
else
{
lean_object* v_reuseFailAlloc_1719_; 
v_reuseFailAlloc_1719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1719_, 0, v___x_1716_);
v___x_1718_ = v_reuseFailAlloc_1719_;
goto v_reusejp_1717_;
}
v_reusejp_1717_:
{
return v___x_1718_;
}
}
else
{
lean_object* v___x_1720_; lean_object* v___x_1721_; 
lean_del_object(v___x_1713_);
lean_inc(v_fvarId_1682_);
v___x_1720_ = l_Lean_mkFVar(v_fvarId_1682_);
v___x_1721_ = l_Lean_Meta_mkEqOfHEq(v___x_1720_, v___x_1700_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = l_Lean_Expr_appArg_x21(v___x_1706_);
lean_dec_ref(v___x_1706_);
v___x_1724_ = l_Lean_Expr_appArg_x21(v_a_1694_);
lean_dec(v_a_1694_);
v___x_1725_ = l_Lean_Meta_mkEq(v___x_1723_, v___x_1724_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref_known(v___x_1725_, 1);
v___x_1727_ = l_Lean_LocalDecl_userName(v_a_1691_);
lean_dec(v_a_1691_);
v___x_1728_ = l_Lean_MVarId_assert(v_mvarId_1683_, v___x_1727_, v_a_1726_, v_a_1722_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1728_) == 0)
{
if (v_tryToClear_1684_ == 0)
{
lean_object* v_a_1729_; uint8_t v___x_1730_; lean_object* v___x_1731_; 
lean_dec(v_fvarId_1682_);
v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1729_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1730_ = lean_unbox(v_a_1711_);
lean_dec(v_a_1711_);
v___x_1731_ = l_Lean_Meta_intro1Core(v_a_1729_, v___x_1730_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
return v___x_1731_;
}
else
{
lean_object* v_a_1732_; lean_object* v___x_1733_; 
v_a_1732_ = lean_ctor_get(v___x_1728_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1728_, 1);
v___x_1733_ = l_Lean_MVarId_tryClear(v_a_1732_, v_fvarId_1682_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
if (lean_obj_tag(v___x_1733_) == 0)
{
lean_object* v_a_1734_; uint8_t v___x_1735_; lean_object* v___x_1736_; 
v_a_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_a_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v___x_1735_ = lean_unbox(v_a_1711_);
lean_dec(v_a_1711_);
v___x_1736_ = l_Lean_Meta_intro1Core(v_a_1734_, v___x_1735_, v___y_1685_, v___y_1686_, v___y_1687_, v___y_1688_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
return v___x_1736_;
}
else
{
lean_object* v_a_1737_; lean_object* v___x_1739_; uint8_t v_isShared_1740_; uint8_t v_isSharedCheck_1744_; 
lean_dec(v_a_1711_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
v_a_1737_ = lean_ctor_get(v___x_1733_, 0);
v_isSharedCheck_1744_ = !lean_is_exclusive(v___x_1733_);
if (v_isSharedCheck_1744_ == 0)
{
v___x_1739_ = v___x_1733_;
v_isShared_1740_ = v_isSharedCheck_1744_;
goto v_resetjp_1738_;
}
else
{
lean_inc(v_a_1737_);
lean_dec(v___x_1733_);
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
}
else
{
lean_object* v_a_1745_; lean_object* v___x_1747_; uint8_t v_isShared_1748_; uint8_t v_isSharedCheck_1752_; 
lean_dec(v_a_1711_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v_fvarId_1682_);
v_a_1745_ = lean_ctor_get(v___x_1728_, 0);
v_isSharedCheck_1752_ = !lean_is_exclusive(v___x_1728_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1747_ = v___x_1728_;
v_isShared_1748_ = v_isSharedCheck_1752_;
goto v_resetjp_1746_;
}
else
{
lean_inc(v_a_1745_);
lean_dec(v___x_1728_);
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
lean_dec(v_a_1722_);
lean_dec(v_a_1711_);
lean_dec(v_a_1691_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v_mvarId_1683_);
lean_dec(v_fvarId_1682_);
v_a_1753_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1760_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1760_ == 0)
{
v___x_1755_ = v___x_1725_;
v_isShared_1756_ = v_isSharedCheck_1760_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1725_);
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
else
{
lean_object* v_a_1761_; lean_object* v___x_1763_; uint8_t v_isShared_1764_; uint8_t v_isSharedCheck_1768_; 
lean_dec(v_a_1711_);
lean_dec_ref(v___x_1706_);
lean_dec(v_a_1694_);
lean_dec(v_a_1691_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v_mvarId_1683_);
lean_dec(v_fvarId_1682_);
v_a_1761_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1768_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1768_ == 0)
{
v___x_1763_ = v___x_1721_;
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
else
{
lean_inc(v_a_1761_);
lean_dec(v___x_1721_);
v___x_1763_ = lean_box(0);
v_isShared_1764_ = v_isSharedCheck_1768_;
goto v_resetjp_1762_;
}
v_resetjp_1762_:
{
lean_object* v___x_1766_; 
if (v_isShared_1764_ == 0)
{
v___x_1766_ = v___x_1763_;
goto v_reusejp_1765_;
}
else
{
lean_object* v_reuseFailAlloc_1767_; 
v_reuseFailAlloc_1767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1767_, 0, v_a_1761_);
v___x_1766_ = v_reuseFailAlloc_1767_;
goto v_reusejp_1765_;
}
v_reusejp_1765_:
{
return v___x_1766_;
}
}
}
}
}
}
else
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1777_; 
lean_dec_ref(v___x_1706_);
lean_dec(v_a_1694_);
lean_dec(v_a_1691_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v_mvarId_1683_);
lean_dec(v_fvarId_1682_);
v_a_1770_ = lean_ctor_get(v___x_1710_, 0);
v_isSharedCheck_1777_ = !lean_is_exclusive(v___x_1710_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1772_ = v___x_1710_;
v_isShared_1773_ = v_isSharedCheck_1777_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1710_);
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
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_a_1691_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v_mvarId_1683_);
lean_dec(v_fvarId_1682_);
v_a_1779_ = lean_ctor_get(v___x_1693_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1693_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1693_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1693_);
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
else
{
lean_object* v_a_1787_; lean_object* v___x_1789_; uint8_t v_isShared_1790_; uint8_t v_isSharedCheck_1794_; 
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v_mvarId_1683_);
lean_dec(v_fvarId_1682_);
v_a_1787_ = lean_ctor_get(v___x_1690_, 0);
v_isSharedCheck_1794_ = !lean_is_exclusive(v___x_1690_);
if (v_isSharedCheck_1794_ == 0)
{
v___x_1789_ = v___x_1690_;
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
else
{
lean_inc(v_a_1787_);
lean_dec(v___x_1690_);
v___x_1789_ = lean_box(0);
v_isShared_1790_ = v_isSharedCheck_1794_;
goto v_resetjp_1788_;
}
v_resetjp_1788_:
{
lean_object* v___x_1792_; 
if (v_isShared_1790_ == 0)
{
v___x_1792_ = v___x_1789_;
goto v_reusejp_1791_;
}
else
{
lean_object* v_reuseFailAlloc_1793_; 
v_reuseFailAlloc_1793_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1793_, 0, v_a_1787_);
v___x_1792_ = v_reuseFailAlloc_1793_;
goto v_reusejp_1791_;
}
v_reusejp_1791_:
{
return v___x_1792_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object* v_fvarId_1795_, lean_object* v_mvarId_1796_, lean_object* v_tryToClear_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_){
_start:
{
uint8_t v_tryToClear_boxed_1803_; lean_object* v_res_1804_; 
v_tryToClear_boxed_1803_ = lean_unbox(v_tryToClear_1797_);
v_res_1804_ = l_Lean_Meta_heqToEq___lam__0(v_fvarId_1795_, v_mvarId_1796_, v_tryToClear_boxed_1803_, v___y_1798_, v___y_1799_, v___y_1800_, v___y_1801_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object* v_mvarId_1805_, lean_object* v_fvarId_1806_, uint8_t v_tryToClear_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_){
_start:
{
lean_object* v___x_1813_; lean_object* v___f_1814_; lean_object* v___x_1815_; 
v___x_1813_ = lean_box(v_tryToClear_1807_);
lean_inc(v_mvarId_1805_);
v___f_1814_ = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1814_, 0, v_fvarId_1806_);
lean_closure_set(v___f_1814_, 1, v_mvarId_1805_);
lean_closure_set(v___f_1814_, 2, v___x_1813_);
v___x_1815_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1805_, v___f_1814_, v_a_1808_, v_a_1809_, v_a_1810_, v_a_1811_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* v_mvarId_1816_, lean_object* v_fvarId_1817_, lean_object* v_tryToClear_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
uint8_t v_tryToClear_boxed_1824_; lean_object* v_res_1825_; 
v_tryToClear_boxed_1824_ = lean_unbox(v_tryToClear_1818_);
v_res_1825_ = l_Lean_Meta_heqToEq(v_mvarId_1816_, v_fvarId_1817_, v_tryToClear_boxed_1824_, v_a_1819_, v_a_1820_, v_a_1821_, v_a_1822_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
return v_res_1825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1829_, lean_object* v_as_1830_, size_t v_sz_1831_, size_t v_i_1832_, lean_object* v_b_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_){
_start:
{
lean_object* v_a_1840_; uint8_t v___x_1844_; 
v___x_1844_ = lean_usize_dec_lt(v_i_1832_, v_sz_1831_);
if (v___x_1844_ == 0)
{
lean_object* v___x_1845_; 
lean_dec(v_x_1829_);
v___x_1845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_b_1833_);
return v___x_1845_;
}
else
{
lean_object* v___x_1846_; lean_object* v_a_1848_; lean_object* v___x_1852_; lean_object* v_a_1853_; 
lean_dec_ref(v_b_1833_);
v___x_1846_ = lean_box(0);
v___x_1852_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1853_ = lean_array_uget(v_as_1830_, v_i_1832_);
if (lean_obj_tag(v_a_1853_) == 0)
{
v_a_1840_ = v___x_1852_;
goto v___jp_1839_;
}
else
{
lean_object* v_val_1854_; lean_object* v___x_1856_; uint8_t v_isShared_1857_; uint8_t v_isSharedCheck_1941_; 
v_val_1854_ = lean_ctor_get(v_a_1853_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v_a_1853_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1856_ = v_a_1853_;
v_isShared_1857_ = v_isSharedCheck_1941_;
goto v_resetjp_1855_;
}
else
{
lean_inc(v_val_1854_);
lean_dec(v_a_1853_);
v___x_1856_ = lean_box(0);
v_isShared_1857_ = v_isSharedCheck_1941_;
goto v_resetjp_1855_;
}
v_resetjp_1855_:
{
uint8_t v___x_1865_; 
v___x_1865_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1854_);
if (v___x_1865_ == 0)
{
lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1871_ = l_Lean_LocalDecl_type(v_val_1854_);
v___x_1872_ = l_Lean_Meta_matchEq_x3f(v___x_1871_, v___y_1834_, v___y_1835_, v___y_1836_, v___y_1837_);
if (lean_obj_tag(v___x_1872_) == 0)
{
lean_object* v_a_1873_; 
v_a_1873_ = lean_ctor_get(v___x_1872_, 0);
lean_inc(v_a_1873_);
lean_dec_ref_known(v___x_1872_, 1);
if (lean_obj_tag(v_a_1873_) == 1)
{
lean_object* v_val_1874_; lean_object* v_snd_1875_; lean_object* v_fst_1876_; lean_object* v_snd_1877_; lean_object* v___x_1878_; 
v_val_1874_ = lean_ctor_get(v_a_1873_, 0);
lean_inc(v_val_1874_);
lean_dec_ref_known(v_a_1873_, 1);
v_snd_1875_ = lean_ctor_get(v_val_1874_, 1);
lean_inc(v_snd_1875_);
lean_dec(v_val_1874_);
v_fst_1876_ = lean_ctor_get(v_snd_1875_, 0);
lean_inc(v_fst_1876_);
v_snd_1877_ = lean_ctor_get(v_snd_1875_, 1);
lean_inc(v_snd_1877_);
lean_dec(v_snd_1875_);
v___x_1878_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1876_, v___y_1835_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___x_1880_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
v___x_1880_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1877_, v___y_1835_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___y_1883_; uint8_t v___y_1884_; lean_object* v___y_1897_; uint8_t v___y_1902_; uint8_t v___x_1914_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v___x_1914_ = l_Lean_Expr_isFVar(v_a_1881_);
if (v___x_1914_ == 0)
{
v___y_1902_ = v___x_1914_;
goto v___jp_1901_;
}
else
{
lean_object* v___x_1915_; uint8_t v___x_1916_; 
v___x_1915_ = l_Lean_Expr_fvarId_x21(v_a_1881_);
v___x_1916_ = l_Lean_instBEqFVarId_beq(v___x_1915_, v_x_1829_);
lean_dec(v___x_1915_);
v___y_1902_ = v___x_1916_;
goto v___jp_1901_;
}
v___jp_1882_:
{
if (v___y_1884_ == 0)
{
lean_dec(v_a_1881_);
lean_dec(v_val_1854_);
v_a_1840_ = v___x_1852_;
goto v___jp_1839_;
}
else
{
lean_object* v___x_1885_; 
lean_inc(v_x_1829_);
v___x_1885_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1881_, v_x_1829_, v___y_1883_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; uint8_t v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = lean_unbox(v_a_1886_);
lean_dec(v_a_1886_);
if (v___x_1887_ == 0)
{
lean_dec(v_x_1829_);
goto v___jp_1866_;
}
else
{
if (v___x_1865_ == 0)
{
lean_dec(v_val_1854_);
v_a_1840_ = v___x_1852_;
goto v___jp_1839_;
}
else
{
lean_dec(v_x_1829_);
goto v___jp_1866_;
}
}
}
else
{
lean_object* v_a_1888_; lean_object* v___x_1890_; uint8_t v_isShared_1891_; uint8_t v_isSharedCheck_1895_; 
lean_dec(v_val_1854_);
lean_dec(v_x_1829_);
v_a_1888_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1895_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1895_ == 0)
{
v___x_1890_ = v___x_1885_;
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
else
{
lean_inc(v_a_1888_);
lean_dec(v___x_1885_);
v___x_1890_ = lean_box(0);
v_isShared_1891_ = v_isSharedCheck_1895_;
goto v_resetjp_1889_;
}
v_resetjp_1889_:
{
lean_object* v___x_1893_; 
if (v_isShared_1891_ == 0)
{
v___x_1893_ = v___x_1890_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v_a_1888_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
return v___x_1893_;
}
}
}
}
}
v___jp_1896_:
{
uint8_t v___x_1898_; 
v___x_1898_ = l_Lean_Expr_isFVar(v_a_1879_);
if (v___x_1898_ == 0)
{
lean_dec(v_a_1879_);
v___y_1883_ = v___y_1897_;
v___y_1884_ = v___x_1898_;
goto v___jp_1882_;
}
else
{
lean_object* v___x_1899_; uint8_t v___x_1900_; 
v___x_1899_ = l_Lean_Expr_fvarId_x21(v_a_1879_);
lean_dec(v_a_1879_);
v___x_1900_ = l_Lean_instBEqFVarId_beq(v___x_1899_, v_x_1829_);
lean_dec(v___x_1899_);
v___y_1883_ = v___y_1897_;
v___y_1884_ = v___x_1900_;
goto v___jp_1882_;
}
}
v___jp_1901_:
{
if (v___y_1902_ == 0)
{
lean_del_object(v___x_1856_);
v___y_1897_ = v___y_1835_;
goto v___jp_1896_;
}
else
{
lean_object* v___x_1903_; 
lean_inc(v_x_1829_);
lean_inc(v_a_1879_);
v___x_1903_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1879_, v_x_1829_, v___y_1835_);
if (lean_obj_tag(v___x_1903_) == 0)
{
lean_object* v_a_1904_; uint8_t v___x_1905_; 
v_a_1904_ = lean_ctor_get(v___x_1903_, 0);
lean_inc(v_a_1904_);
lean_dec_ref_known(v___x_1903_, 1);
v___x_1905_ = lean_unbox(v_a_1904_);
lean_dec(v_a_1904_);
if (v___x_1905_ == 0)
{
lean_dec(v_a_1881_);
lean_dec(v_a_1879_);
lean_dec(v_x_1829_);
goto v___jp_1858_;
}
else
{
if (v___x_1865_ == 0)
{
lean_del_object(v___x_1856_);
v___y_1897_ = v___y_1835_;
goto v___jp_1896_;
}
else
{
lean_dec(v_a_1881_);
lean_dec(v_a_1879_);
lean_dec(v_x_1829_);
goto v___jp_1858_;
}
}
}
else
{
lean_object* v_a_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1913_; 
lean_dec(v_a_1881_);
lean_dec(v_a_1879_);
lean_del_object(v___x_1856_);
lean_dec(v_val_1854_);
lean_dec(v_x_1829_);
v_a_1906_ = lean_ctor_get(v___x_1903_, 0);
v_isSharedCheck_1913_ = !lean_is_exclusive(v___x_1903_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1908_ = v___x_1903_;
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_a_1906_);
lean_dec(v___x_1903_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1913_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
lean_object* v___x_1911_; 
if (v_isShared_1909_ == 0)
{
v___x_1911_ = v___x_1908_;
goto v_reusejp_1910_;
}
else
{
lean_object* v_reuseFailAlloc_1912_; 
v_reuseFailAlloc_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1912_, 0, v_a_1906_);
v___x_1911_ = v_reuseFailAlloc_1912_;
goto v_reusejp_1910_;
}
v_reusejp_1910_:
{
return v___x_1911_;
}
}
}
}
}
}
else
{
lean_object* v_a_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1924_; 
lean_dec(v_a_1879_);
lean_del_object(v___x_1856_);
lean_dec(v_val_1854_);
lean_dec(v_x_1829_);
v_a_1917_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1924_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1924_ == 0)
{
v___x_1919_ = v___x_1880_;
v_isShared_1920_ = v_isSharedCheck_1924_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_a_1917_);
lean_dec(v___x_1880_);
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
lean_object* v_a_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1932_; 
lean_dec(v_snd_1877_);
lean_del_object(v___x_1856_);
lean_dec(v_val_1854_);
lean_dec(v_x_1829_);
v_a_1925_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1932_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1932_ == 0)
{
v___x_1927_ = v___x_1878_;
v_isShared_1928_ = v_isSharedCheck_1932_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_a_1925_);
lean_dec(v___x_1878_);
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
lean_dec(v_a_1873_);
lean_del_object(v___x_1856_);
lean_dec(v_val_1854_);
v_a_1840_ = v___x_1852_;
goto v___jp_1839_;
}
}
else
{
lean_object* v_a_1933_; lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1940_; 
lean_del_object(v___x_1856_);
lean_dec(v_val_1854_);
lean_dec(v_x_1829_);
v_a_1933_ = lean_ctor_get(v___x_1872_, 0);
v_isSharedCheck_1940_ = !lean_is_exclusive(v___x_1872_);
if (v_isSharedCheck_1940_ == 0)
{
v___x_1935_ = v___x_1872_;
v_isShared_1936_ = v_isSharedCheck_1940_;
goto v_resetjp_1934_;
}
else
{
lean_inc(v_a_1933_);
lean_dec(v___x_1872_);
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
else
{
lean_del_object(v___x_1856_);
lean_dec(v_val_1854_);
v_a_1840_ = v___x_1852_;
goto v___jp_1839_;
}
v___jp_1858_:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1863_; 
v___x_1859_ = l_Lean_LocalDecl_fvarId(v_val_1854_);
lean_dec(v_val_1854_);
v___x_1860_ = lean_box(v___x_1844_);
v___x_1861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1859_);
lean_ctor_set(v___x_1861_, 1, v___x_1860_);
if (v_isShared_1857_ == 0)
{
lean_ctor_set(v___x_1856_, 0, v___x_1861_);
v___x_1863_ = v___x_1856_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1861_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
v_a_1848_ = v___x_1863_;
goto v___jp_1847_;
}
}
v___jp_1866_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1867_ = l_Lean_LocalDecl_fvarId(v_val_1854_);
lean_dec(v_val_1854_);
v___x_1868_ = lean_box(v___x_1865_);
v___x_1869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1869_, 0, v___x_1867_);
lean_ctor_set(v___x_1869_, 1, v___x_1868_);
v___x_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1870_, 0, v___x_1869_);
v_a_1848_ = v___x_1870_;
goto v___jp_1847_;
}
}
}
v___jp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1849_, 0, v_a_1848_);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v___x_1846_);
v___x_1851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1851_, 0, v___x_1850_);
return v___x_1851_;
}
}
v___jp_1839_:
{
size_t v___x_1841_; size_t v___x_1842_; 
v___x_1841_ = ((size_t)1ULL);
v___x_1842_ = lean_usize_add(v_i_1832_, v___x_1841_);
lean_inc_ref(v_a_1840_);
v_i_1832_ = v___x_1842_;
v_b_1833_ = v_a_1840_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1942_, lean_object* v_as_1943_, lean_object* v_sz_1944_, lean_object* v_i_1945_, lean_object* v_b_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_){
_start:
{
size_t v_sz_boxed_1952_; size_t v_i_boxed_1953_; lean_object* v_res_1954_; 
v_sz_boxed_1952_ = lean_unbox_usize(v_sz_1944_);
lean_dec(v_sz_1944_);
v_i_boxed_1953_ = lean_unbox_usize(v_i_1945_);
lean_dec(v_i_1945_);
v_res_1954_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1942_, v_as_1943_, v_sz_boxed_1952_, v_i_boxed_1953_, v_b_1946_, v___y_1947_, v___y_1948_, v___y_1949_, v___y_1950_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec_ref(v_as_1943_);
return v_res_1954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object* v_x_1955_, lean_object* v_as_1956_, size_t v_sz_1957_, size_t v_i_1958_, lean_object* v_b_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v_a_1966_; uint8_t v___x_1970_; 
v___x_1970_ = lean_usize_dec_lt(v_i_1958_, v_sz_1957_);
if (v___x_1970_ == 0)
{
lean_object* v___x_1971_; 
lean_dec(v_x_1955_);
v___x_1971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_b_1959_);
return v___x_1971_;
}
else
{
lean_object* v___x_1972_; lean_object* v_a_1974_; lean_object* v___x_1978_; lean_object* v_a_1979_; 
lean_dec_ref(v_b_1959_);
v___x_1972_ = lean_box(0);
v___x_1978_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1979_ = lean_array_uget(v_as_1956_, v_i_1958_);
if (lean_obj_tag(v_a_1979_) == 0)
{
v_a_1966_ = v___x_1978_;
goto v___jp_1965_;
}
else
{
lean_object* v_val_1980_; lean_object* v___x_1982_; uint8_t v_isShared_1983_; uint8_t v_isSharedCheck_2067_; 
v_val_1980_ = lean_ctor_get(v_a_1979_, 0);
v_isSharedCheck_2067_ = !lean_is_exclusive(v_a_1979_);
if (v_isSharedCheck_2067_ == 0)
{
v___x_1982_ = v_a_1979_;
v_isShared_1983_ = v_isSharedCheck_2067_;
goto v_resetjp_1981_;
}
else
{
lean_inc(v_val_1980_);
lean_dec(v_a_1979_);
v___x_1982_ = lean_box(0);
v_isShared_1983_ = v_isSharedCheck_2067_;
goto v_resetjp_1981_;
}
v_resetjp_1981_:
{
uint8_t v___x_1991_; 
v___x_1991_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1980_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1997_ = l_Lean_LocalDecl_type(v_val_1980_);
v___x_1998_ = l_Lean_Meta_matchEq_x3f(v___x_1997_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
if (lean_obj_tag(v_a_1999_) == 1)
{
lean_object* v_val_2000_; lean_object* v_snd_2001_; lean_object* v_fst_2002_; lean_object* v_snd_2003_; lean_object* v___x_2004_; 
v_val_2000_ = lean_ctor_get(v_a_1999_, 0);
lean_inc(v_val_2000_);
lean_dec_ref_known(v_a_1999_, 1);
v_snd_2001_ = lean_ctor_get(v_val_2000_, 1);
lean_inc(v_snd_2001_);
lean_dec(v_val_2000_);
v_fst_2002_ = lean_ctor_get(v_snd_2001_, 0);
lean_inc(v_fst_2002_);
v_snd_2003_ = lean_ctor_get(v_snd_2001_, 1);
lean_inc(v_snd_2003_);
lean_dec(v_snd_2001_);
v___x_2004_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_2002_, v___y_1961_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___x_2006_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2006_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_2003_, v___y_1961_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___y_2009_; uint8_t v___y_2010_; lean_object* v___y_2023_; uint8_t v___y_2028_; uint8_t v___x_2040_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2040_ = l_Lean_Expr_isFVar(v_a_2007_);
if (v___x_2040_ == 0)
{
v___y_2028_ = v___x_2040_;
goto v___jp_2027_;
}
else
{
lean_object* v___x_2041_; uint8_t v___x_2042_; 
v___x_2041_ = l_Lean_Expr_fvarId_x21(v_a_2007_);
v___x_2042_ = l_Lean_instBEqFVarId_beq(v___x_2041_, v_x_1955_);
lean_dec(v___x_2041_);
v___y_2028_ = v___x_2042_;
goto v___jp_2027_;
}
v___jp_2008_:
{
if (v___y_2010_ == 0)
{
lean_dec(v_a_2007_);
lean_dec(v_val_1980_);
v_a_1966_ = v___x_1978_;
goto v___jp_1965_;
}
else
{
lean_object* v___x_2011_; 
lean_inc(v_x_1955_);
v___x_2011_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2007_, v_x_1955_, v___y_2009_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; uint8_t v___x_2013_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v___x_2013_ = lean_unbox(v_a_2012_);
lean_dec(v_a_2012_);
if (v___x_2013_ == 0)
{
lean_dec(v_x_1955_);
goto v___jp_1992_;
}
else
{
if (v___x_1991_ == 0)
{
lean_dec(v_val_1980_);
v_a_1966_ = v___x_1978_;
goto v___jp_1965_;
}
else
{
lean_dec(v_x_1955_);
goto v___jp_1992_;
}
}
}
else
{
lean_object* v_a_2014_; lean_object* v___x_2016_; uint8_t v_isShared_2017_; uint8_t v_isSharedCheck_2021_; 
lean_dec(v_val_1980_);
lean_dec(v_x_1955_);
v_a_2014_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2021_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2021_ == 0)
{
v___x_2016_ = v___x_2011_;
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
else
{
lean_inc(v_a_2014_);
lean_dec(v___x_2011_);
v___x_2016_ = lean_box(0);
v_isShared_2017_ = v_isSharedCheck_2021_;
goto v_resetjp_2015_;
}
v_resetjp_2015_:
{
lean_object* v___x_2019_; 
if (v_isShared_2017_ == 0)
{
v___x_2019_ = v___x_2016_;
goto v_reusejp_2018_;
}
else
{
lean_object* v_reuseFailAlloc_2020_; 
v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2020_, 0, v_a_2014_);
v___x_2019_ = v_reuseFailAlloc_2020_;
goto v_reusejp_2018_;
}
v_reusejp_2018_:
{
return v___x_2019_;
}
}
}
}
}
v___jp_2022_:
{
uint8_t v___x_2024_; 
v___x_2024_ = l_Lean_Expr_isFVar(v_a_2005_);
if (v___x_2024_ == 0)
{
lean_dec(v_a_2005_);
v___y_2009_ = v___y_2023_;
v___y_2010_ = v___x_2024_;
goto v___jp_2008_;
}
else
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = l_Lean_Expr_fvarId_x21(v_a_2005_);
lean_dec(v_a_2005_);
v___x_2026_ = l_Lean_instBEqFVarId_beq(v___x_2025_, v_x_1955_);
lean_dec(v___x_2025_);
v___y_2009_ = v___y_2023_;
v___y_2010_ = v___x_2026_;
goto v___jp_2008_;
}
}
v___jp_2027_:
{
if (v___y_2028_ == 0)
{
lean_del_object(v___x_1982_);
v___y_2023_ = v___y_1961_;
goto v___jp_2022_;
}
else
{
lean_object* v___x_2029_; 
lean_inc(v_x_1955_);
lean_inc(v_a_2005_);
v___x_2029_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2005_, v_x_1955_, v___y_1961_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; uint8_t v___x_2031_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = lean_unbox(v_a_2030_);
lean_dec(v_a_2030_);
if (v___x_2031_ == 0)
{
lean_dec(v_a_2007_);
lean_dec(v_a_2005_);
lean_dec(v_x_1955_);
goto v___jp_1984_;
}
else
{
if (v___x_1991_ == 0)
{
lean_del_object(v___x_1982_);
v___y_2023_ = v___y_1961_;
goto v___jp_2022_;
}
else
{
lean_dec(v_a_2007_);
lean_dec(v_a_2005_);
lean_dec(v_x_1955_);
goto v___jp_1984_;
}
}
}
else
{
lean_object* v_a_2032_; lean_object* v___x_2034_; uint8_t v_isShared_2035_; uint8_t v_isSharedCheck_2039_; 
lean_dec(v_a_2007_);
lean_dec(v_a_2005_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_dec(v_x_1955_);
v_a_2032_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2039_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2039_ == 0)
{
v___x_2034_ = v___x_2029_;
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
else
{
lean_inc(v_a_2032_);
lean_dec(v___x_2029_);
v___x_2034_ = lean_box(0);
v_isShared_2035_ = v_isSharedCheck_2039_;
goto v_resetjp_2033_;
}
v_resetjp_2033_:
{
lean_object* v___x_2037_; 
if (v_isShared_2035_ == 0)
{
v___x_2037_ = v___x_2034_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2038_; 
v_reuseFailAlloc_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2038_, 0, v_a_2032_);
v___x_2037_ = v_reuseFailAlloc_2038_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
return v___x_2037_;
}
}
}
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec(v_a_2005_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_dec(v_x_1955_);
v_a_2043_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2006_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2006_);
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
lean_object* v_a_2051_; lean_object* v___x_2053_; uint8_t v_isShared_2054_; uint8_t v_isSharedCheck_2058_; 
lean_dec(v_snd_2003_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_dec(v_x_1955_);
v_a_2051_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2004_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2004_);
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
lean_dec(v_a_1999_);
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
v_a_1966_ = v___x_1978_;
goto v___jp_1965_;
}
}
else
{
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
lean_dec(v_x_1955_);
v_a_2059_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_1998_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_1998_);
v___x_2061_ = lean_box(0);
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
v_resetjp_2060_:
{
lean_object* v___x_2064_; 
if (v_isShared_2062_ == 0)
{
v___x_2064_ = v___x_2061_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2065_; 
v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
v___x_2064_ = v_reuseFailAlloc_2065_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
return v___x_2064_;
}
}
}
}
else
{
lean_del_object(v___x_1982_);
lean_dec(v_val_1980_);
v_a_1966_ = v___x_1978_;
goto v___jp_1965_;
}
v___jp_1984_:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1989_; 
v___x_1985_ = l_Lean_LocalDecl_fvarId(v_val_1980_);
lean_dec(v_val_1980_);
v___x_1986_ = lean_box(v___x_1970_);
v___x_1987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1987_, 0, v___x_1985_);
lean_ctor_set(v___x_1987_, 1, v___x_1986_);
if (v_isShared_1983_ == 0)
{
lean_ctor_set(v___x_1982_, 0, v___x_1987_);
v___x_1989_ = v___x_1982_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v___x_1987_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
v_a_1974_ = v___x_1989_;
goto v___jp_1973_;
}
}
v___jp_1992_:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1993_ = l_Lean_LocalDecl_fvarId(v_val_1980_);
lean_dec(v_val_1980_);
v___x_1994_ = lean_box(v___x_1991_);
v___x_1995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1995_, 0, v___x_1993_);
lean_ctor_set(v___x_1995_, 1, v___x_1994_);
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v___x_1995_);
v_a_1974_ = v___x_1996_;
goto v___jp_1973_;
}
}
}
v___jp_1973_:
{
lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1975_, 0, v_a_1974_);
v___x_1976_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1976_, 0, v___x_1975_);
lean_ctor_set(v___x_1976_, 1, v___x_1972_);
v___x_1977_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1976_);
return v___x_1977_;
}
}
v___jp_1965_:
{
size_t v___x_1967_; size_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1967_ = ((size_t)1ULL);
v___x_1968_ = lean_usize_add(v_i_1958_, v___x_1967_);
lean_inc_ref(v_a_1966_);
v___x_1969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1955_, v_as_1956_, v_sz_1957_, v___x_1968_, v_a_1966_, v___y_1960_, v___y_1961_, v___y_1962_, v___y_1963_);
return v___x_1969_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2068_, lean_object* v_as_2069_, lean_object* v_sz_2070_, lean_object* v_i_2071_, lean_object* v_b_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_){
_start:
{
size_t v_sz_boxed_2078_; size_t v_i_boxed_2079_; lean_object* v_res_2080_; 
v_sz_boxed_2078_ = lean_unbox_usize(v_sz_2070_);
lean_dec(v_sz_2070_);
v_i_boxed_2079_ = lean_unbox_usize(v_i_2071_);
lean_dec(v_i_2071_);
v_res_2080_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2068_, v_as_2069_, v_sz_boxed_2078_, v_i_boxed_2079_, v_b_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec_ref(v_as_2069_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object* v_x_2081_, lean_object* v_x_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_){
_start:
{
if (lean_obj_tag(v_x_2082_) == 0)
{
lean_object* v_cs_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; size_t v_sz_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v_cs_2088_ = lean_ctor_get(v_x_2082_, 0);
v___x_2089_ = lean_box(0);
v___x_2090_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2091_ = lean_array_size(v_cs_2088_);
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2081_, v_cs_2088_, v_sz_2091_, v___x_2092_, v___x_2090_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v_a_2094_; lean_object* v___x_2096_; uint8_t v_isShared_2097_; uint8_t v_isSharedCheck_2106_; 
v_a_2094_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2096_ = v___x_2093_;
v_isShared_2097_ = v_isSharedCheck_2106_;
goto v_resetjp_2095_;
}
else
{
lean_inc(v_a_2094_);
lean_dec(v___x_2093_);
v___x_2096_ = lean_box(0);
v_isShared_2097_ = v_isSharedCheck_2106_;
goto v_resetjp_2095_;
}
v_resetjp_2095_:
{
lean_object* v_fst_2098_; 
v_fst_2098_ = lean_ctor_get(v_a_2094_, 0);
lean_inc(v_fst_2098_);
lean_dec(v_a_2094_);
if (lean_obj_tag(v_fst_2098_) == 0)
{
lean_object* v___x_2100_; 
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v___x_2089_);
v___x_2100_ = v___x_2096_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v___x_2089_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
else
{
lean_object* v_val_2102_; lean_object* v___x_2104_; 
v_val_2102_ = lean_ctor_get(v_fst_2098_, 0);
lean_inc(v_val_2102_);
lean_dec_ref_known(v_fst_2098_, 1);
if (v_isShared_2097_ == 0)
{
lean_ctor_set(v___x_2096_, 0, v_val_2102_);
v___x_2104_ = v___x_2096_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_val_2102_);
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
lean_object* v_a_2107_; lean_object* v___x_2109_; uint8_t v_isShared_2110_; uint8_t v_isSharedCheck_2114_; 
v_a_2107_ = lean_ctor_get(v___x_2093_, 0);
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2114_ == 0)
{
v___x_2109_ = v___x_2093_;
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
else
{
lean_inc(v_a_2107_);
lean_dec(v___x_2093_);
v___x_2109_ = lean_box(0);
v_isShared_2110_ = v_isSharedCheck_2114_;
goto v_resetjp_2108_;
}
v_resetjp_2108_:
{
lean_object* v___x_2112_; 
if (v_isShared_2110_ == 0)
{
v___x_2112_ = v___x_2109_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_a_2107_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
}
else
{
lean_object* v_vs_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; size_t v_sz_2118_; size_t v___x_2119_; lean_object* v___x_2120_; 
v_vs_2115_ = lean_ctor_get(v_x_2082_, 0);
v___x_2116_ = lean_box(0);
v___x_2117_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2118_ = lean_array_size(v_vs_2115_);
v___x_2119_ = ((size_t)0ULL);
v___x_2120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2081_, v_vs_2115_, v_sz_2118_, v___x_2119_, v___x_2117_, v___y_2083_, v___y_2084_, v___y_2085_, v___y_2086_);
if (lean_obj_tag(v___x_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2133_; 
v_a_2121_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2133_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2133_ == 0)
{
v___x_2123_ = v___x_2120_;
v_isShared_2124_ = v_isSharedCheck_2133_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2120_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2133_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v_fst_2125_; 
v_fst_2125_ = lean_ctor_get(v_a_2121_, 0);
lean_inc(v_fst_2125_);
lean_dec(v_a_2121_);
if (lean_obj_tag(v_fst_2125_) == 0)
{
lean_object* v___x_2127_; 
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v___x_2116_);
v___x_2127_ = v___x_2123_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v___x_2116_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
else
{
lean_object* v_val_2129_; lean_object* v___x_2131_; 
v_val_2129_ = lean_ctor_get(v_fst_2125_, 0);
lean_inc(v_val_2129_);
lean_dec_ref_known(v_fst_2125_, 1);
if (v_isShared_2124_ == 0)
{
lean_ctor_set(v___x_2123_, 0, v_val_2129_);
v___x_2131_ = v___x_2123_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v_val_2129_);
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
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
v_a_2134_ = lean_ctor_get(v___x_2120_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2120_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2120_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2120_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v___x_2139_; 
if (v_isShared_2137_ == 0)
{
v___x_2139_ = v___x_2136_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2140_; 
v_reuseFailAlloc_2140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2140_, 0, v_a_2134_);
v___x_2139_ = v_reuseFailAlloc_2140_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
return v___x_2139_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2142_, lean_object* v_as_2143_, size_t v_sz_2144_, size_t v_i_2145_, lean_object* v_b_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_){
_start:
{
uint8_t v___x_2152_; 
v___x_2152_ = lean_usize_dec_lt(v_i_2145_, v_sz_2144_);
if (v___x_2152_ == 0)
{
lean_object* v___x_2153_; 
lean_dec(v_x_2142_);
v___x_2153_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2153_, 0, v_b_2146_);
return v___x_2153_;
}
else
{
lean_object* v_a_2154_; lean_object* v___x_2155_; 
lean_dec_ref(v_b_2146_);
v_a_2154_ = lean_array_uget_borrowed(v_as_2143_, v_i_2145_);
lean_inc(v_x_2142_);
v___x_2155_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2142_, v_a_2154_, v___y_2147_, v___y_2148_, v___y_2149_, v___y_2150_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2170_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2170_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2170_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2160_; 
v___x_2160_ = lean_box(0);
if (lean_obj_tag(v_a_2156_) == 1)
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2164_; 
lean_dec(v_x_2142_);
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v_a_2156_);
v___x_2162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2162_, 0, v___x_2161_);
lean_ctor_set(v___x_2162_, 1, v___x_2160_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2162_);
v___x_2164_ = v___x_2158_;
goto v_reusejp_2163_;
}
else
{
lean_object* v_reuseFailAlloc_2165_; 
v_reuseFailAlloc_2165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2165_, 0, v___x_2162_);
v___x_2164_ = v_reuseFailAlloc_2165_;
goto v_reusejp_2163_;
}
v_reusejp_2163_:
{
return v___x_2164_;
}
}
else
{
lean_object* v___x_2166_; size_t v___x_2167_; size_t v___x_2168_; 
lean_del_object(v___x_2158_);
lean_dec(v_a_2156_);
v___x_2166_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2167_ = ((size_t)1ULL);
v___x_2168_ = lean_usize_add(v_i_2145_, v___x_2167_);
v_i_2145_ = v___x_2168_;
v_b_2146_ = v___x_2166_;
goto _start;
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec(v_x_2142_);
v_a_2171_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2155_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2155_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2179_, lean_object* v_as_2180_, lean_object* v_sz_2181_, lean_object* v_i_2182_, lean_object* v_b_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_){
_start:
{
size_t v_sz_boxed_2189_; size_t v_i_boxed_2190_; lean_object* v_res_2191_; 
v_sz_boxed_2189_ = lean_unbox_usize(v_sz_2181_);
lean_dec(v_sz_2181_);
v_i_boxed_2190_ = lean_unbox_usize(v_i_2182_);
lean_dec(v_i_2182_);
v_res_2191_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2179_, v_as_2180_, v_sz_boxed_2189_, v_i_boxed_2190_, v_b_2183_, v___y_2184_, v___y_2185_, v___y_2186_, v___y_2187_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec_ref(v_as_2180_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2192_, lean_object* v_x_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2192_, v_x_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec_ref(v_x_2193_);
return v_res_2199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object* v_x_2200_, lean_object* v_t_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_){
_start:
{
lean_object* v_root_2207_; lean_object* v_tail_2208_; lean_object* v___x_2209_; 
v_root_2207_ = lean_ctor_get(v_t_2201_, 0);
v_tail_2208_ = lean_ctor_get(v_t_2201_, 1);
lean_inc(v_x_2200_);
v___x_2209_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2200_, v_root_2207_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2209_) == 0)
{
lean_object* v_a_2210_; 
v_a_2210_ = lean_ctor_get(v___x_2209_, 0);
lean_inc(v_a_2210_);
if (lean_obj_tag(v_a_2210_) == 0)
{
lean_object* v___x_2211_; size_t v_sz_2212_; size_t v___x_2213_; lean_object* v___x_2214_; 
lean_dec_ref_known(v___x_2209_, 1);
v___x_2211_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2212_ = lean_array_size(v_tail_2208_);
v___x_2213_ = ((size_t)0ULL);
v___x_2214_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2200_, v_tail_2208_, v_sz_2212_, v___x_2213_, v___x_2211_, v___y_2202_, v___y_2203_, v___y_2204_, v___y_2205_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2217_; uint8_t v_isShared_2218_; uint8_t v_isSharedCheck_2227_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2227_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2227_ == 0)
{
v___x_2217_ = v___x_2214_;
v_isShared_2218_ = v_isSharedCheck_2227_;
goto v_resetjp_2216_;
}
else
{
lean_inc(v_a_2215_);
lean_dec(v___x_2214_);
v___x_2217_ = lean_box(0);
v_isShared_2218_ = v_isSharedCheck_2227_;
goto v_resetjp_2216_;
}
v_resetjp_2216_:
{
lean_object* v_fst_2219_; 
v_fst_2219_ = lean_ctor_get(v_a_2215_, 0);
lean_inc(v_fst_2219_);
lean_dec(v_a_2215_);
if (lean_obj_tag(v_fst_2219_) == 0)
{
lean_object* v___x_2221_; 
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v_a_2210_);
v___x_2221_ = v___x_2217_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_a_2210_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
else
{
lean_object* v_val_2223_; lean_object* v___x_2225_; 
v_val_2223_ = lean_ctor_get(v_fst_2219_, 0);
lean_inc(v_val_2223_);
lean_dec_ref_known(v_fst_2219_, 1);
if (v_isShared_2218_ == 0)
{
lean_ctor_set(v___x_2217_, 0, v_val_2223_);
v___x_2225_ = v___x_2217_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_val_2223_);
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
lean_object* v_a_2228_; lean_object* v___x_2230_; uint8_t v_isShared_2231_; uint8_t v_isSharedCheck_2235_; 
v_a_2228_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2235_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2235_ == 0)
{
v___x_2230_ = v___x_2214_;
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
else
{
lean_inc(v_a_2228_);
lean_dec(v___x_2214_);
v___x_2230_ = lean_box(0);
v_isShared_2231_ = v_isSharedCheck_2235_;
goto v_resetjp_2229_;
}
v_resetjp_2229_:
{
lean_object* v___x_2233_; 
if (v_isShared_2231_ == 0)
{
v___x_2233_ = v___x_2230_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2234_; 
v_reuseFailAlloc_2234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
v___x_2233_ = v_reuseFailAlloc_2234_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
return v___x_2233_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2210_, 1);
lean_dec(v_x_2200_);
return v___x_2209_;
}
}
else
{
lean_dec(v_x_2200_);
return v___x_2209_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* v_x_2236_, lean_object* v_t_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v_res_2243_; 
v_res_2243_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2236_, v_t_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec_ref(v_t_2237_);
return v_res_2243_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object* v_x_2244_, lean_object* v_lctx_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v_decls_2251_; lean_object* v___x_2252_; 
v_decls_2251_ = lean_ctor_get(v_lctx_2245_, 1);
v___x_2252_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2244_, v_decls_2251_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object* v_x_2253_, lean_object* v_lctx_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_){
_start:
{
lean_object* v_res_2260_; 
v_res_2260_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2253_, v_lctx_2254_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec_ref(v_lctx_2254_);
return v_res_2260_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2262_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__0));
v___x_2263_ = l_Lean_stringToMessageData(v___x_2262_);
return v___x_2263_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2265_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__2));
v___x_2266_ = l_Lean_stringToMessageData(v___x_2265_);
return v___x_2266_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__4));
v___x_2269_ = l_Lean_stringToMessageData(v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object* v_x_2270_, lean_object* v_mvarId_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_){
_start:
{
lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___x_2326_; 
lean_inc(v_x_2270_);
v___x_2326_ = l_Lean_FVarId_getDecl___redArg(v_x_2270_, v___y_2272_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; uint8_t v___x_2328_; uint8_t v___x_2329_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v___x_2326_, 1);
v___x_2328_ = 0;
v___x_2329_ = l_Lean_LocalDecl_isLet(v_a_2327_, v___x_2328_);
lean_dec(v_a_2327_);
if (v___x_2329_ == 0)
{
v___y_2278_ = v___y_2272_;
v___y_2279_ = v___y_2273_;
v___y_2280_ = v___y_2274_;
v___y_2281_ = v___y_2275_;
goto v___jp_2277_;
}
else
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2330_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2331_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2270_);
v___x_2332_ = l_Lean_mkFVar(v_x_2270_);
v___x_2333_ = l_Lean_MessageData_ofExpr(v___x_2332_);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2331_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2334_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2336_);
lean_inc(v_mvarId_2271_);
v___x_2338_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2330_, v_mvarId_2271_, v___x_2337_, v___y_2272_, v___y_2273_, v___y_2274_, v___y_2275_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_dec_ref_known(v___x_2338_, 1);
v___y_2278_ = v___y_2272_;
v___y_2279_ = v___y_2273_;
v___y_2280_ = v___y_2274_;
v___y_2281_ = v___y_2275_;
goto v___jp_2277_;
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_dec(v_mvarId_2271_);
lean_dec(v_x_2270_);
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2338_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2338_);
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
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec(v_mvarId_2271_);
lean_dec(v_x_2270_);
v_a_2347_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2326_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2326_);
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
v___jp_2277_:
{
lean_object* v_lctx_2282_; lean_object* v___x_2283_; 
v_lctx_2282_ = lean_ctor_get(v___y_2278_, 2);
lean_inc(v_x_2270_);
v___x_2283_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2270_, v_lctx_2282_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2283_) == 0)
{
lean_object* v_a_2284_; 
v_a_2284_ = lean_ctor_get(v___x_2283_, 0);
lean_inc(v_a_2284_);
lean_dec_ref_known(v___x_2283_, 1);
if (lean_obj_tag(v_a_2284_) == 1)
{
lean_object* v_val_2285_; lean_object* v_fst_2286_; lean_object* v_snd_2287_; lean_object* v___x_2288_; uint8_t v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; 
lean_dec(v_x_2270_);
v_val_2285_ = lean_ctor_get(v_a_2284_, 0);
lean_inc(v_val_2285_);
lean_dec_ref_known(v_a_2284_, 1);
v_fst_2286_ = lean_ctor_get(v_val_2285_, 0);
lean_inc(v_fst_2286_);
v_snd_2287_ = lean_ctor_get(v_val_2285_, 1);
lean_inc(v_snd_2287_);
lean_dec(v_val_2285_);
v___x_2288_ = lean_box(0);
v___x_2289_ = 1;
v___x_2290_ = lean_unbox(v_snd_2287_);
lean_dec(v_snd_2287_);
v___x_2291_ = l_Lean_Meta_substCore(v_mvarId_2271_, v_fst_2286_, v___x_2290_, v___x_2288_, v___x_2289_, v___x_2289_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2300_; 
v_a_2292_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2294_ = v___x_2291_;
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2291_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2300_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v_snd_2296_; lean_object* v___x_2298_; 
v_snd_2296_ = lean_ctor_get(v_a_2292_, 1);
lean_inc(v_snd_2296_);
lean_dec(v_a_2292_);
if (v_isShared_2295_ == 0)
{
lean_ctor_set(v___x_2294_, 0, v_snd_2296_);
v___x_2298_ = v___x_2294_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_snd_2296_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
v_a_2301_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2291_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2291_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v___x_2306_; 
if (v_isShared_2304_ == 0)
{
v___x_2306_ = v___x_2303_;
goto v_reusejp_2305_;
}
else
{
lean_object* v_reuseFailAlloc_2307_; 
v_reuseFailAlloc_2307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2307_, 0, v_a_2301_);
v___x_2306_ = v_reuseFailAlloc_2307_;
goto v_reusejp_2305_;
}
v_reusejp_2305_:
{
return v___x_2306_;
}
}
}
}
else
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; 
lean_dec(v_a_2284_);
v___x_2309_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2310_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2311_ = l_Lean_mkFVar(v_x_2270_);
v___x_2312_ = l_Lean_MessageData_ofExpr(v___x_2311_);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2310_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2313_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2316_, 0, v___x_2315_);
v___x_2317_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2309_, v_mvarId_2271_, v___x_2316_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
return v___x_2317_;
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec(v_mvarId_2271_);
lean_dec(v_x_2270_);
v_a_2318_ = lean_ctor_get(v___x_2283_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2283_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2283_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2283_);
v___x_2320_ = lean_box(0);
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
v_resetjp_2319_:
{
lean_object* v___x_2323_; 
if (v_isShared_2321_ == 0)
{
v___x_2323_ = v___x_2320_;
goto v_reusejp_2322_;
}
else
{
lean_object* v_reuseFailAlloc_2324_; 
v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2324_, 0, v_a_2318_);
v___x_2323_ = v_reuseFailAlloc_2324_;
goto v_reusejp_2322_;
}
v_reusejp_2322_:
{
return v___x_2323_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2355_, lean_object* v_mvarId_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_){
_start:
{
lean_object* v_res_2362_; 
v_res_2362_ = l_Lean_Meta_substVar___lam__0(v_x_2355_, v_mvarId_2356_, v___y_2357_, v___y_2358_, v___y_2359_, v___y_2360_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
return v_res_2362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2363_, lean_object* v_x_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v___f_2370_; lean_object* v___x_2371_; 
lean_inc(v_mvarId_2363_);
v___f_2370_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2370_, 0, v_x_2364_);
lean_closure_set(v___f_2370_, 1, v_mvarId_2363_);
v___x_2371_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2363_, v___f_2370_, v_a_2365_, v_a_2366_, v_a_2367_, v_a_2368_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2372_, lean_object* v_x_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v_res_2379_; 
v_res_2379_ = l_Lean_Meta_substVar(v_mvarId_2372_, v_x_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
return v_res_2379_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2381_; lean_object* v___x_2382_; 
v___x_2381_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2382_ = l_Lean_stringToMessageData(v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2383_, lean_object* v_snd_2384_, uint8_t v___x_2385_, lean_object* v_fvarSubst_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_){
_start:
{
lean_object* v___x_2392_; 
lean_inc(v_fst_2383_);
v___x_2392_ = l_Lean_FVarId_getDecl___redArg(v_fst_2383_, v___y_2387_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v_newType_2407_; uint8_t v_symm_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___x_2448_; lean_object* v___x_2449_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
v___x_2448_ = l_Lean_LocalDecl_type(v_a_2393_);
v___x_2449_ = l_Lean_Meta_matchEq_x3f(v___x_2448_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
if (lean_obj_tag(v_a_2450_) == 1)
{
lean_object* v_val_2451_; lean_object* v_snd_2452_; lean_object* v_fst_2453_; lean_object* v_snd_2454_; lean_object* v___x_2455_; 
v_val_2451_ = lean_ctor_get(v_a_2450_, 0);
lean_inc(v_val_2451_);
lean_dec_ref_known(v_a_2450_, 1);
v_snd_2452_ = lean_ctor_get(v_val_2451_, 1);
lean_inc(v_snd_2452_);
lean_dec(v_val_2451_);
v_fst_2453_ = lean_ctor_get(v_snd_2452_, 0);
lean_inc(v_fst_2453_);
v_snd_2454_ = lean_ctor_get(v_snd_2452_, 1);
lean_inc_n(v_snd_2454_, 2);
lean_dec(v_snd_2452_);
lean_inc(v___y_2390_);
lean_inc_ref(v___y_2389_);
lean_inc(v___y_2388_);
lean_inc_ref(v___y_2387_);
v___x_2455_ = lean_whnf(v_snd_2454_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2455_) == 0)
{
lean_object* v_a_2456_; uint8_t v___x_2457_; 
v_a_2456_ = lean_ctor_get(v___x_2455_, 0);
lean_inc(v_a_2456_);
lean_dec_ref_known(v___x_2455_, 1);
v___x_2457_ = l_Lean_Expr_isFVar(v_a_2456_);
if (v___x_2457_ == 0)
{
lean_object* v___x_2458_; 
lean_dec(v_a_2456_);
lean_inc(v___y_2390_);
lean_inc_ref(v___y_2389_);
lean_inc(v___y_2388_);
lean_inc_ref(v___y_2387_);
lean_inc(v_fst_2453_);
v___x_2458_ = lean_whnf(v_fst_2453_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2458_) == 0)
{
lean_object* v_a_2459_; uint8_t v___y_2461_; uint8_t v___x_2473_; 
v_a_2459_ = lean_ctor_get(v___x_2458_, 0);
lean_inc(v_a_2459_);
lean_dec_ref_known(v___x_2458_, 1);
v___x_2473_ = l_Lean_Expr_isFVar(v_a_2459_);
if (v___x_2473_ == 0)
{
lean_dec(v_a_2459_);
lean_dec(v_snd_2454_);
lean_dec(v_fst_2453_);
lean_dec(v_fvarSubst_2386_);
lean_dec(v_fst_2383_);
v___y_2395_ = v___y_2387_;
v___y_2396_ = v___y_2388_;
v___y_2397_ = v___y_2389_;
v___y_2398_ = v___y_2390_;
goto v___jp_2394_;
}
else
{
uint8_t v___x_2474_; 
v___x_2474_ = lean_expr_eqv(v_fst_2453_, v_a_2459_);
lean_dec(v_fst_2453_);
if (v___x_2474_ == 0)
{
v___y_2461_ = v___x_2473_;
goto v___jp_2460_;
}
else
{
v___y_2461_ = v___x_2457_;
goto v___jp_2460_;
}
}
v___jp_2460_:
{
if (v___y_2461_ == 0)
{
lean_object* v___x_2462_; 
lean_dec(v_a_2459_);
lean_dec(v_snd_2454_);
lean_dec(v_a_2393_);
v___x_2462_ = l_Lean_Meta_substCore(v_snd_2384_, v_fst_2383_, v___y_2461_, v_fvarSubst_2386_, v___x_2385_, v___x_2385_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v___x_2462_;
}
else
{
lean_object* v___x_2463_; 
v___x_2463_ = l_Lean_Meta_mkEq(v_a_2459_, v_snd_2454_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v_newType_2407_ = v_a_2464_;
v_symm_2408_ = v___x_2457_;
v___y_2409_ = v___y_2387_;
v___y_2410_ = v___y_2388_;
v___y_2411_ = v___y_2389_;
v___y_2412_ = v___y_2390_;
goto v___jp_2406_;
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec(v_a_2393_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v_fvarSubst_2386_);
lean_dec(v_snd_2384_);
lean_dec(v_fst_2383_);
v_a_2465_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2463_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2463_);
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
}
}
else
{
lean_object* v_a_2475_; lean_object* v___x_2477_; uint8_t v_isShared_2478_; uint8_t v_isSharedCheck_2482_; 
lean_dec(v_snd_2454_);
lean_dec(v_fst_2453_);
lean_dec(v_a_2393_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v_fvarSubst_2386_);
lean_dec(v_snd_2384_);
lean_dec(v_fst_2383_);
v_a_2475_ = lean_ctor_get(v___x_2458_, 0);
v_isSharedCheck_2482_ = !lean_is_exclusive(v___x_2458_);
if (v_isSharedCheck_2482_ == 0)
{
v___x_2477_ = v___x_2458_;
v_isShared_2478_ = v_isSharedCheck_2482_;
goto v_resetjp_2476_;
}
else
{
lean_inc(v_a_2475_);
lean_dec(v___x_2458_);
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
else
{
uint8_t v___x_2483_; 
v___x_2483_ = lean_expr_eqv(v_snd_2454_, v_a_2456_);
lean_dec(v_snd_2454_);
if (v___x_2483_ == 0)
{
if (v___x_2457_ == 0)
{
lean_object* v___x_2484_; 
lean_dec(v_a_2456_);
lean_dec(v_fst_2453_);
lean_dec(v_a_2393_);
v___x_2484_ = l_Lean_Meta_substCore(v_snd_2384_, v_fst_2383_, v___x_2385_, v_fvarSubst_2386_, v___x_2385_, v___x_2385_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v___x_2484_;
}
else
{
lean_object* v___x_2485_; 
v___x_2485_ = l_Lean_Meta_mkEq(v_fst_2453_, v_a_2456_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
if (lean_obj_tag(v___x_2485_) == 0)
{
lean_object* v_a_2486_; 
v_a_2486_ = lean_ctor_get(v___x_2485_, 0);
lean_inc(v_a_2486_);
lean_dec_ref_known(v___x_2485_, 1);
v_newType_2407_ = v_a_2486_;
v_symm_2408_ = v___x_2385_;
v___y_2409_ = v___y_2387_;
v___y_2410_ = v___y_2388_;
v___y_2411_ = v___y_2389_;
v___y_2412_ = v___y_2390_;
goto v___jp_2406_;
}
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec(v_a_2393_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v_fvarSubst_2386_);
lean_dec(v_snd_2384_);
lean_dec(v_fst_2383_);
v_a_2487_ = lean_ctor_get(v___x_2485_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2485_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2485_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2485_);
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
}
else
{
lean_object* v___x_2495_; 
lean_dec(v_a_2456_);
lean_dec(v_fst_2453_);
lean_dec(v_a_2393_);
v___x_2495_ = l_Lean_Meta_substCore(v_snd_2384_, v_fst_2383_, v___x_2385_, v_fvarSubst_2386_, v___x_2385_, v___x_2385_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
return v___x_2495_;
}
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_dec(v_snd_2454_);
lean_dec(v_fst_2453_);
lean_dec(v_a_2393_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v_fvarSubst_2386_);
lean_dec(v_snd_2384_);
lean_dec(v_fst_2383_);
v_a_2496_ = lean_ctor_get(v___x_2455_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2455_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2455_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2455_);
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
else
{
lean_dec(v_a_2450_);
lean_dec(v_fvarSubst_2386_);
lean_dec(v_fst_2383_);
v___y_2395_ = v___y_2387_;
v___y_2396_ = v___y_2388_;
v___y_2397_ = v___y_2389_;
v___y_2398_ = v___y_2390_;
goto v___jp_2394_;
}
}
else
{
lean_object* v_a_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2511_; 
lean_dec(v_a_2393_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v_fvarSubst_2386_);
lean_dec(v_snd_2384_);
lean_dec(v_fst_2383_);
v_a_2504_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2511_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2511_ == 0)
{
v___x_2506_ = v___x_2449_;
v_isShared_2507_ = v_isSharedCheck_2511_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_a_2504_);
lean_dec(v___x_2449_);
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
v___jp_2394_:
{
lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v___x_2399_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2400_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2401_ = l_Lean_LocalDecl_type(v_a_2393_);
lean_dec(v_a_2393_);
v___x_2402_ = l_Lean_indentExpr(v___x_2401_);
v___x_2403_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2403_, 0, v___x_2400_);
lean_ctor_set(v___x_2403_, 1, v___x_2402_);
v___x_2404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2403_);
v___x_2405_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2399_, v_snd_2384_, v___x_2404_, v___y_2395_, v___y_2396_, v___y_2397_, v___y_2398_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
return v___x_2405_;
}
v___jp_2406_:
{
lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2413_ = l_Lean_LocalDecl_userName(v_a_2393_);
lean_dec(v_a_2393_);
lean_inc(v_fst_2383_);
v___x_2414_ = l_Lean_mkFVar(v_fst_2383_);
v___x_2415_ = l_Lean_MVarId_assert(v_snd_2384_, v___x_2413_, v_newType_2407_, v___x_2414_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v___x_2417_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v___x_2417_ = l_Lean_Meta_intro1Core(v_a_2416_, v___x_2385_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v_fst_2419_; lean_object* v_snd_2420_; lean_object* v___x_2421_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v_fst_2419_ = lean_ctor_get(v_a_2418_, 0);
lean_inc(v_fst_2419_);
v_snd_2420_ = lean_ctor_get(v_a_2418_, 1);
lean_inc(v_snd_2420_);
lean_dec(v_a_2418_);
v___x_2421_ = l_Lean_MVarId_clear(v_snd_2420_, v_fst_2383_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v___x_2423_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref_known(v___x_2421_, 1);
v___x_2423_ = l_Lean_Meta_substCore(v_a_2422_, v_fst_2419_, v_symm_2408_, v_fvarSubst_2386_, v___x_2385_, v___x_2385_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
return v___x_2423_;
}
else
{
lean_object* v_a_2424_; lean_object* v___x_2426_; uint8_t v_isShared_2427_; uint8_t v_isSharedCheck_2431_; 
lean_dec(v_fst_2419_);
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v_fvarSubst_2386_);
v_a_2424_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2426_ = v___x_2421_;
v_isShared_2427_ = v_isSharedCheck_2431_;
goto v_resetjp_2425_;
}
else
{
lean_inc(v_a_2424_);
lean_dec(v___x_2421_);
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
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v_fvarSubst_2386_);
lean_dec(v_fst_2383_);
v_a_2432_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2417_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2417_);
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
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_dec(v___y_2412_);
lean_dec_ref(v___y_2411_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v_fvarSubst_2386_);
lean_dec(v_fst_2383_);
v_a_2440_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2415_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2415_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
}
else
{
lean_object* v_a_2512_; lean_object* v___x_2514_; uint8_t v_isShared_2515_; uint8_t v_isSharedCheck_2519_; 
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v_fvarSubst_2386_);
lean_dec(v_snd_2384_);
lean_dec(v_fst_2383_);
v_a_2512_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2519_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2519_ == 0)
{
v___x_2514_ = v___x_2392_;
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
else
{
lean_inc(v_a_2512_);
lean_dec(v___x_2392_);
v___x_2514_ = lean_box(0);
v_isShared_2515_ = v_isSharedCheck_2519_;
goto v_resetjp_2513_;
}
v_resetjp_2513_:
{
lean_object* v___x_2517_; 
if (v_isShared_2515_ == 0)
{
v___x_2517_ = v___x_2514_;
goto v_reusejp_2516_;
}
else
{
lean_object* v_reuseFailAlloc_2518_; 
v_reuseFailAlloc_2518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2518_, 0, v_a_2512_);
v___x_2517_ = v_reuseFailAlloc_2518_;
goto v_reusejp_2516_;
}
v_reusejp_2516_:
{
return v___x_2517_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2520_, lean_object* v_snd_2521_, lean_object* v___x_2522_, lean_object* v_fvarSubst_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_){
_start:
{
uint8_t v___x_1937__boxed_2529_; lean_object* v_res_2530_; 
v___x_1937__boxed_2529_ = lean_unbox(v___x_2522_);
v_res_2530_ = l_Lean_Meta_substEq___lam__0(v_fst_2520_, v_snd_2521_, v___x_1937__boxed_2529_, v_fvarSubst_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2531_, lean_object* v_hFVarId_2532_, lean_object* v_fvarSubst_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
uint8_t v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = 1;
v___x_2540_ = l_Lean_Meta_heqToEq(v_mvarId_2531_, v_hFVarId_2532_, v___x_2539_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
if (lean_obj_tag(v___x_2540_) == 0)
{
lean_object* v_a_2541_; lean_object* v_fst_2542_; lean_object* v_snd_2543_; lean_object* v___x_2544_; lean_object* v___f_2545_; lean_object* v___x_2546_; 
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
lean_inc(v_a_2541_);
lean_dec_ref_known(v___x_2540_, 1);
v_fst_2542_ = lean_ctor_get(v_a_2541_, 0);
lean_inc(v_fst_2542_);
v_snd_2543_ = lean_ctor_get(v_a_2541_, 1);
lean_inc_n(v_snd_2543_, 2);
lean_dec(v_a_2541_);
v___x_2544_ = lean_box(v___x_2539_);
v___f_2545_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2545_, 0, v_fst_2542_);
lean_closure_set(v___f_2545_, 1, v_snd_2543_);
lean_closure_set(v___f_2545_, 2, v___x_2544_);
lean_closure_set(v___f_2545_, 3, v_fvarSubst_2533_);
v___x_2546_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_snd_2543_, v___f_2545_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
return v___x_2546_;
}
else
{
lean_object* v_a_2547_; lean_object* v___x_2549_; uint8_t v_isShared_2550_; uint8_t v_isSharedCheck_2554_; 
lean_dec(v_fvarSubst_2533_);
v_a_2547_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2554_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2554_ == 0)
{
v___x_2549_ = v___x_2540_;
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
else
{
lean_inc(v_a_2547_);
lean_dec(v___x_2540_);
v___x_2549_ = lean_box(0);
v_isShared_2550_ = v_isSharedCheck_2554_;
goto v_resetjp_2548_;
}
v_resetjp_2548_:
{
lean_object* v___x_2552_; 
if (v_isShared_2550_ == 0)
{
v___x_2552_ = v___x_2549_;
goto v_reusejp_2551_;
}
else
{
lean_object* v_reuseFailAlloc_2553_; 
v_reuseFailAlloc_2553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2553_, 0, v_a_2547_);
v___x_2552_ = v_reuseFailAlloc_2553_;
goto v_reusejp_2551_;
}
v_reusejp_2551_:
{
return v___x_2552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2555_, lean_object* v_hFVarId_2556_, lean_object* v_fvarSubst_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_Lean_Meta_substEq(v_mvarId_2555_, v_hFVarId_2556_, v_fvarSubst_2557_, v_a_2558_, v_a_2559_, v_a_2560_, v_a_2561_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2564_, lean_object* v_mvarId_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_){
_start:
{
lean_object* v___x_2571_; 
lean_inc(v_h_2564_);
v___x_2571_ = l_Lean_FVarId_getType___redArg(v_h_2564_, v___y_2566_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; lean_object* v___x_2573_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc_n(v_a_2572_, 2);
lean_dec_ref_known(v___x_2571_, 1);
v___x_2573_ = l_Lean_Meta_matchEq_x3f(v_a_2572_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
if (lean_obj_tag(v_a_2574_) == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_Meta_matchHEq_x3f(v_a_2572_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
if (lean_obj_tag(v_a_2576_) == 0)
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_Meta_substVar(v_mvarId_2565_, v_h_2564_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2577_;
}
else
{
uint8_t v___x_2578_; lean_object* v___x_2579_; 
lean_dec_ref_known(v_a_2576_, 1);
v___x_2578_ = 1;
lean_inc(v_h_2564_);
lean_inc(v_mvarId_2565_);
v___x_2579_ = l_Lean_Meta_heqToEq(v_mvarId_2565_, v_h_2564_, v___x_2578_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v_fst_2581_; lean_object* v_snd_2582_; uint8_t v___x_2583_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v_fst_2581_ = lean_ctor_get(v_a_2580_, 0);
lean_inc(v_fst_2581_);
v_snd_2582_ = lean_ctor_get(v_a_2580_, 1);
lean_inc(v_snd_2582_);
lean_dec(v_a_2580_);
v___x_2583_ = l_Lean_instBEqMVarId_beq(v_mvarId_2565_, v_snd_2582_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; 
lean_dec(v_mvarId_2565_);
lean_dec(v_h_2564_);
v___x_2584_ = l_Lean_Meta_subst(v_snd_2582_, v_fst_2581_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2584_;
}
else
{
lean_object* v___x_2585_; 
lean_dec(v_snd_2582_);
lean_dec(v_fst_2581_);
v___x_2585_ = l_Lean_Meta_substVar(v_mvarId_2565_, v_h_2564_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
return v___x_2585_;
}
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_mvarId_2565_);
lean_dec(v_h_2564_);
v_a_2586_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2593_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2593_ == 0)
{
v___x_2588_ = v___x_2579_;
v_isShared_2589_ = v_isSharedCheck_2593_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_a_2586_);
lean_dec(v___x_2579_);
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
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec(v_mvarId_2565_);
lean_dec(v_h_2564_);
v_a_2594_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2575_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2575_);
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
else
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
lean_dec_ref_known(v_a_2574_, 1);
lean_dec(v_a_2572_);
v___x_2602_ = lean_box(0);
v___x_2603_ = l_Lean_Meta_substEq(v_mvarId_2565_, v_h_2564_, v___x_2602_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
if (lean_obj_tag(v___x_2603_) == 0)
{
lean_object* v_a_2604_; lean_object* v___x_2606_; uint8_t v_isShared_2607_; uint8_t v_isSharedCheck_2612_; 
v_a_2604_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2606_ = v___x_2603_;
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
else
{
lean_inc(v_a_2604_);
lean_dec(v___x_2603_);
v___x_2606_ = lean_box(0);
v_isShared_2607_ = v_isSharedCheck_2612_;
goto v_resetjp_2605_;
}
v_resetjp_2605_:
{
lean_object* v_snd_2608_; lean_object* v___x_2610_; 
v_snd_2608_ = lean_ctor_get(v_a_2604_, 1);
lean_inc(v_snd_2608_);
lean_dec(v_a_2604_);
if (v_isShared_2607_ == 0)
{
lean_ctor_set(v___x_2606_, 0, v_snd_2608_);
v___x_2610_ = v___x_2606_;
goto v_reusejp_2609_;
}
else
{
lean_object* v_reuseFailAlloc_2611_; 
v_reuseFailAlloc_2611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2611_, 0, v_snd_2608_);
v___x_2610_ = v_reuseFailAlloc_2611_;
goto v_reusejp_2609_;
}
v_reusejp_2609_:
{
return v___x_2610_;
}
}
}
else
{
lean_object* v_a_2613_; lean_object* v___x_2615_; uint8_t v_isShared_2616_; uint8_t v_isSharedCheck_2620_; 
v_a_2613_ = lean_ctor_get(v___x_2603_, 0);
v_isSharedCheck_2620_ = !lean_is_exclusive(v___x_2603_);
if (v_isSharedCheck_2620_ == 0)
{
v___x_2615_ = v___x_2603_;
v_isShared_2616_ = v_isSharedCheck_2620_;
goto v_resetjp_2614_;
}
else
{
lean_inc(v_a_2613_);
lean_dec(v___x_2603_);
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
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec(v_a_2572_);
lean_dec(v_mvarId_2565_);
lean_dec(v_h_2564_);
v_a_2621_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2573_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2573_);
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
else
{
lean_object* v_a_2629_; lean_object* v___x_2631_; uint8_t v_isShared_2632_; uint8_t v_isSharedCheck_2636_; 
lean_dec(v_mvarId_2565_);
lean_dec(v_h_2564_);
v_a_2629_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2636_ == 0)
{
v___x_2631_ = v___x_2571_;
v_isShared_2632_ = v_isSharedCheck_2636_;
goto v_resetjp_2630_;
}
else
{
lean_inc(v_a_2629_);
lean_dec(v___x_2571_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2637_, lean_object* v_mvarId_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_Lean_Meta_subst___lam__0(v_h_2637_, v_mvarId_2638_, v___y_2639_, v___y_2640_, v___y_2641_, v___y_2642_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2645_, lean_object* v_h_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v___f_2652_; lean_object* v___x_2653_; 
lean_inc(v_mvarId_2645_);
v___f_2652_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2652_, 0, v_h_2646_);
lean_closure_set(v___f_2652_, 1, v_mvarId_2645_);
v___x_2653_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2645_, v___f_2652_, v_a_2647_, v_a_2648_, v_a_2649_, v_a_2650_);
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2654_, lean_object* v_h_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l_Lean_Meta_subst(v_mvarId_2654_, v_h_2655_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_){
_start:
{
lean_object* v___x_2668_; 
v___x_2668_ = l_Lean_Meta_saveState___redArg(v___y_2664_, v___y_2666_);
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_object* v_a_2669_; lean_object* v___x_2670_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v___x_2668_, 1);
lean_inc(v___y_2666_);
lean_inc_ref(v___y_2665_);
lean_inc(v___y_2664_);
lean_inc_ref(v___y_2663_);
v___x_2670_ = lean_apply_5(v_x_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, lean_box(0));
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_dec(v_a_2669_);
return v___x_2670_;
}
else
{
lean_object* v_a_2671_; uint8_t v___y_2673_; uint8_t v___x_2691_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
v___x_2691_ = l_Lean_Exception_isInterrupt(v_a_2671_);
if (v___x_2691_ == 0)
{
uint8_t v___x_2692_; 
lean_inc(v_a_2671_);
v___x_2692_ = l_Lean_Exception_isRuntime(v_a_2671_);
v___y_2673_ = v___x_2692_;
goto v___jp_2672_;
}
else
{
v___y_2673_ = v___x_2691_;
goto v___jp_2672_;
}
v___jp_2672_:
{
if (v___y_2673_ == 0)
{
lean_object* v___x_2674_; 
lean_dec_ref_known(v___x_2670_, 1);
v___x_2674_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2669_, v___y_2664_, v___y_2666_);
lean_dec(v_a_2669_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_object* v___x_2676_; uint8_t v_isShared_2677_; uint8_t v_isSharedCheck_2681_; 
v_isSharedCheck_2681_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2681_ == 0)
{
lean_object* v_unused_2682_; 
v_unused_2682_ = lean_ctor_get(v___x_2674_, 0);
lean_dec(v_unused_2682_);
v___x_2676_ = v___x_2674_;
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
else
{
lean_dec(v___x_2674_);
v___x_2676_ = lean_box(0);
v_isShared_2677_ = v_isSharedCheck_2681_;
goto v_resetjp_2675_;
}
v_resetjp_2675_:
{
lean_object* v___x_2679_; 
if (v_isShared_2677_ == 0)
{
lean_ctor_set_tag(v___x_2676_, 1);
lean_ctor_set(v___x_2676_, 0, v_a_2671_);
v___x_2679_ = v___x_2676_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_a_2671_);
v___x_2679_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
return v___x_2679_;
}
}
}
else
{
lean_object* v_a_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2690_; 
lean_dec(v_a_2671_);
v_a_2683_ = lean_ctor_get(v___x_2674_, 0);
v_isSharedCheck_2690_ = !lean_is_exclusive(v___x_2674_);
if (v_isSharedCheck_2690_ == 0)
{
v___x_2685_ = v___x_2674_;
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
else
{
lean_inc(v_a_2683_);
lean_dec(v___x_2674_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2690_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2688_; 
if (v_isShared_2686_ == 0)
{
v___x_2688_ = v___x_2685_;
goto v_reusejp_2687_;
}
else
{
lean_object* v_reuseFailAlloc_2689_; 
v_reuseFailAlloc_2689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2689_, 0, v_a_2683_);
v___x_2688_ = v_reuseFailAlloc_2689_;
goto v_reusejp_2687_;
}
v_reusejp_2687_:
{
return v___x_2688_;
}
}
}
}
else
{
lean_dec(v_a_2671_);
lean_dec(v_a_2669_);
return v___x_2670_;
}
}
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec_ref(v_x_2662_);
v_a_2693_ = lean_ctor_get(v___x_2668_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2668_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2668_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2668_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2698_; 
if (v_isShared_2696_ == 0)
{
v___x_2698_ = v___x_2695_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v_a_2693_);
v___x_2698_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
return v___x_2698_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_){
_start:
{
lean_object* v_res_2707_; 
v_res_2707_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
return v_res_2707_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2708_, lean_object* v_x_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_){
_start:
{
lean_object* v___x_2715_; 
v___x_2715_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2709_, v___y_2710_, v___y_2711_, v___y_2712_, v___y_2713_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2716_, lean_object* v_x_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_){
_start:
{
lean_object* v_res_2723_; 
v_res_2723_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2716_, v_x_2717_, v___y_2718_, v___y_2719_, v___y_2720_, v___y_2721_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
return v_res_2723_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_ref_2730_; lean_object* v___x_2731_; lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2740_; 
v_ref_2730_ = lean_ctor_get(v___y_2727_, 5);
v___x_2731_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msg_2724_, v___y_2725_, v___y_2726_, v___y_2727_, v___y_2728_);
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2740_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2740_ == 0)
{
v___x_2734_ = v___x_2731_;
v_isShared_2735_ = v_isSharedCheck_2740_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2731_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2740_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2736_; lean_object* v___x_2738_; 
lean_inc(v_ref_2730_);
v___x_2736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2736_, 0, v_ref_2730_);
lean_ctor_set(v___x_2736_, 1, v_a_2732_);
if (v_isShared_2735_ == 0)
{
lean_ctor_set_tag(v___x_2734_, 1);
lean_ctor_set(v___x_2734_, 0, v___x_2736_);
v___x_2738_ = v___x_2734_;
goto v_reusejp_2737_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2736_);
v___x_2738_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2737_;
}
v_reusejp_2737_:
{
return v___x_2738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2741_, v___y_2742_, v___y_2743_, v___y_2744_, v___y_2745_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
return v_res_2747_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; 
v___x_2749_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2750_ = l_Lean_stringToMessageData(v___x_2749_);
return v___x_2750_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2752_; lean_object* v___x_2753_; 
v___x_2752_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2753_ = l_Lean_stringToMessageData(v___x_2752_);
return v___x_2753_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2755_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2756_ = l_Lean_stringToMessageData(v___x_2755_);
return v___x_2756_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2758_; lean_object* v___x_2759_; 
v___x_2758_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2759_ = l_Lean_stringToMessageData(v___x_2758_);
return v___x_2759_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2761_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2762_ = l_Lean_stringToMessageData(v___x_2761_);
return v___x_2762_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2775_; lean_object* v___x_2776_; 
v___x_2775_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2776_ = l_Lean_stringToMessageData(v___x_2775_);
return v___x_2776_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2785_, uint8_t v_substLHS_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_){
_start:
{
lean_object* v___x_2792_; 
lean_inc(v_mvarId_2785_);
v___x_2792_ = l_Lean_MVarId_getType_x27(v_mvarId_2785_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2792_) == 0)
{
lean_object* v_a_2793_; 
v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
lean_inc(v_a_2793_);
lean_dec_ref_known(v___x_2792_, 1);
if (lean_obj_tag(v_a_2793_) == 7)
{
lean_object* v_binderType_2797_; lean_object* v_body_2798_; uint8_t v___x_2799_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v_fst_2934_; lean_object* v_fst_2935_; lean_object* v_fst_2936_; lean_object* v_snd_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; 
v_binderType_2797_ = lean_ctor_get(v_a_2793_, 1);
lean_inc_ref(v_binderType_2797_);
v_body_2798_ = lean_ctor_get(v_a_2793_, 2);
lean_inc_ref(v_body_2798_);
lean_dec_ref_known(v_a_2793_, 3);
v___x_2799_ = l_Lean_Expr_hasLooseBVars(v_body_2798_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2953_; 
v___x_2953_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2797_, v___y_2788_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2970_ = l_Lean_Expr_cleanupAnnotations(v_a_2954_);
v___x_2971_ = l_Lean_Expr_isApp(v___x_2970_);
if (v___x_2971_ == 0)
{
lean_dec_ref(v___x_2970_);
lean_dec_ref(v_body_2798_);
lean_dec(v_mvarId_2785_);
v___y_2956_ = v___y_2787_;
v___y_2957_ = v___y_2788_;
v___y_2958_ = v___y_2789_;
v___y_2959_ = v___y_2790_;
goto v___jp_2955_;
}
else
{
lean_object* v_arg_2972_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v_arg_2972_ = lean_ctor_get(v___x_2970_, 1);
lean_inc_ref(v_arg_2972_);
v___x_2973_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2970_);
v___x_2974_ = l_Lean_Expr_isApp(v___x_2973_);
if (v___x_2974_ == 0)
{
lean_dec_ref(v___x_2973_);
lean_dec_ref(v_arg_2972_);
lean_dec_ref(v_body_2798_);
lean_dec(v_mvarId_2785_);
v___y_2956_ = v___y_2787_;
v___y_2957_ = v___y_2788_;
v___y_2958_ = v___y_2789_;
v___y_2959_ = v___y_2790_;
goto v___jp_2955_;
}
else
{
lean_object* v_arg_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v_arg_2975_ = lean_ctor_get(v___x_2973_, 1);
lean_inc_ref(v_arg_2975_);
v___x_2976_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2973_);
v___x_2977_ = l_Lean_Expr_isApp(v___x_2976_);
if (v___x_2977_ == 0)
{
lean_dec_ref(v___x_2976_);
lean_dec_ref(v_arg_2975_);
lean_dec_ref(v_arg_2972_);
lean_dec_ref(v_body_2798_);
lean_dec(v_mvarId_2785_);
v___y_2956_ = v___y_2787_;
v___y_2957_ = v___y_2788_;
v___y_2958_ = v___y_2789_;
v___y_2959_ = v___y_2790_;
goto v___jp_2955_;
}
else
{
lean_object* v_arg_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_arg_2978_ = lean_ctor_get(v___x_2976_, 1);
lean_inc_ref(v_arg_2978_);
v___x_2979_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2976_);
v___x_2980_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_2981_ = l_Lean_Expr_isConstOf(v___x_2979_, v___x_2980_);
if (v___x_2981_ == 0)
{
uint8_t v___x_2982_; 
v___x_2982_ = l_Lean_Expr_isApp(v___x_2979_);
if (v___x_2982_ == 0)
{
lean_dec_ref(v___x_2979_);
lean_dec_ref(v_arg_2978_);
lean_dec_ref(v_arg_2975_);
lean_dec_ref(v_arg_2972_);
lean_dec_ref(v_body_2798_);
lean_dec(v_mvarId_2785_);
v___y_2956_ = v___y_2787_;
v___y_2957_ = v___y_2788_;
v___y_2958_ = v___y_2789_;
v___y_2959_ = v___y_2790_;
goto v___jp_2955_;
}
else
{
lean_object* v_arg_2983_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___x_2991_; lean_object* v___x_2992_; uint8_t v___x_2993_; 
v_arg_2983_ = lean_ctor_get(v___x_2979_, 1);
lean_inc_ref(v_arg_2983_);
v___x_2991_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2979_);
v___x_2992_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_2993_ = l_Lean_Expr_isConstOf(v___x_2991_, v___x_2992_);
lean_dec_ref(v___x_2991_);
if (v___x_2993_ == 0)
{
lean_dec_ref(v_arg_2983_);
lean_dec_ref(v_arg_2978_);
lean_dec_ref(v_arg_2975_);
lean_dec_ref(v_arg_2972_);
lean_dec_ref(v_body_2798_);
lean_dec(v_mvarId_2785_);
v___y_2956_ = v___y_2787_;
v___y_2957_ = v___y_2788_;
v___y_2958_ = v___y_2789_;
v___y_2959_ = v___y_2790_;
goto v___jp_2955_;
}
else
{
lean_object* v___x_2994_; 
lean_inc_ref(v_arg_2983_);
v___x_2994_ = l_Lean_Meta_isExprDefEq(v_arg_2983_, v_arg_2975_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
if (lean_obj_tag(v___x_2994_) == 0)
{
lean_object* v_a_2995_; uint8_t v___x_2996_; 
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_a_2995_);
lean_dec_ref_known(v___x_2994_, 1);
v___x_2996_ = lean_unbox(v_a_2995_);
lean_dec(v_a_2995_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2997_; lean_object* v___x_2998_; lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v_arg_2983_);
lean_dec_ref(v_arg_2978_);
lean_dec_ref(v_arg_2972_);
lean_dec_ref(v_body_2798_);
lean_dec(v_mvarId_2785_);
v___x_2997_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_2998_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2997_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2998_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2998_);
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
else
{
v___y_2985_ = v___y_2787_;
v___y_2986_ = v___y_2788_;
v___y_2987_ = v___y_2789_;
v___y_2988_ = v___y_2790_;
goto v___jp_2984_;
}
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_dec_ref(v_arg_2983_);
lean_dec_ref(v_arg_2978_);
lean_dec_ref(v_arg_2972_);
lean_dec_ref(v_body_2798_);
lean_dec(v_mvarId_2785_);
v_a_3007_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2994_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2994_);
v___x_3009_ = lean_box(0);
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
v_resetjp_3008_:
{
lean_object* v___x_3012_; 
if (v_isShared_3010_ == 0)
{
v___x_3012_ = v___x_3009_;
goto v_reusejp_3011_;
}
else
{
lean_object* v_reuseFailAlloc_3013_; 
v_reuseFailAlloc_3013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3013_, 0, v_a_3007_);
v___x_3012_ = v_reuseFailAlloc_3013_;
goto v_reusejp_3011_;
}
v_reusejp_3011_:
{
return v___x_3012_;
}
}
}
}
v___jp_2984_:
{
if (v_substLHS_2786_ == 0)
{
lean_object* v___x_2989_; 
v___x_2989_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2934_ = v_arg_2983_;
v_fst_2935_ = v_arg_2978_;
v_fst_2936_ = v_arg_2972_;
v_snd_2937_ = v___x_2989_;
v___y_2938_ = v___y_2985_;
v___y_2939_ = v___y_2986_;
v___y_2940_ = v___y_2987_;
v___y_2941_ = v___y_2988_;
goto v___jp_2933_;
}
else
{
lean_object* v___x_2990_; 
v___x_2990_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2934_ = v_arg_2983_;
v_fst_2935_ = v_arg_2972_;
v_fst_2936_ = v_arg_2978_;
v_snd_2937_ = v___x_2990_;
v___y_2938_ = v___y_2985_;
v___y_2939_ = v___y_2986_;
v___y_2940_ = v___y_2987_;
v___y_2941_ = v___y_2988_;
goto v___jp_2933_;
}
}
}
}
else
{
lean_dec_ref(v___x_2979_);
if (v_substLHS_2786_ == 0)
{
lean_object* v___x_3015_; 
v___x_3015_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2934_ = v_arg_2978_;
v_fst_2935_ = v_arg_2975_;
v_fst_2936_ = v_arg_2972_;
v_snd_2937_ = v___x_3015_;
v___y_2938_ = v___y_2787_;
v___y_2939_ = v___y_2788_;
v___y_2940_ = v___y_2789_;
v___y_2941_ = v___y_2790_;
goto v___jp_2933_;
}
else
{
lean_object* v___x_3016_; 
v___x_3016_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2934_ = v_arg_2978_;
v_fst_2935_ = v_arg_2972_;
v_fst_2936_ = v_arg_2975_;
v_snd_2937_ = v___x_3016_;
v___y_2938_ = v___y_2787_;
v___y_2939_ = v___y_2788_;
v___y_2940_ = v___y_2789_;
v___y_2941_ = v___y_2790_;
goto v___jp_2933_;
}
}
}
}
}
v___jp_2955_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
v___x_2960_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_2961_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2960_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
v_a_2962_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2961_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_3017_; lean_object* v___x_3019_; uint8_t v_isShared_3020_; uint8_t v_isSharedCheck_3024_; 
lean_dec_ref(v_body_2798_);
lean_dec(v_mvarId_2785_);
v_a_3017_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_3024_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_3024_ == 0)
{
v___x_3019_ = v___x_2953_;
v_isShared_3020_ = v_isSharedCheck_3024_;
goto v_resetjp_3018_;
}
else
{
lean_inc(v_a_3017_);
lean_dec(v___x_2953_);
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
else
{
lean_dec_ref(v_body_2798_);
lean_dec_ref(v_binderType_2797_);
lean_dec(v_mvarId_2785_);
goto v___jp_2794_;
}
v___jp_2800_:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; uint8_t v___x_2814_; uint8_t v___x_2815_; lean_object* v___x_2816_; 
v___x_2812_ = lean_mk_empty_array_with_capacity(v___y_2801_);
lean_inc_ref(v___x_2812_);
v___x_2813_ = lean_array_push(v___x_2812_, v___y_2805_);
v___x_2814_ = 1;
v___x_2815_ = 1;
v___x_2816_ = l_Lean_Meta_mkLambdaFVars(v___x_2813_, v_body_2798_, v___x_2799_, v___x_2814_, v___x_2799_, v___x_2814_, v___x_2815_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
lean_dec_ref(v___x_2813_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
lean_inc(v___y_2802_);
v___x_2818_ = l_Lean_MVarId_getTag(v___y_2802_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
lean_inc_ref(v___y_2806_);
v___x_2820_ = lean_array_push(v___x_2812_, v___y_2806_);
lean_inc(v_a_2817_);
v___x_2821_ = l_Lean_Expr_beta(v_a_2817_, v___x_2820_);
lean_inc_ref(v___x_2821_);
v___x_2822_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2821_, v_a_2819_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = l_Lean_Meta_getLevel(v___x_2821_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2826_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
lean_inc_ref(v___y_2804_);
v___x_2826_ = l_Lean_Meta_getLevel(v___y_2804_, v___y_2808_, v___y_2809_, v___y_2810_, v___y_2811_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2844_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref_known(v___x_2826_, 1);
v___x_2828_ = lean_box(0);
v___x_2829_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2829_, 0, v_a_2827_);
lean_ctor_set(v___x_2829_, 1, v___x_2828_);
v___x_2830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2830_, 0, v_a_2825_);
lean_ctor_set(v___x_2830_, 1, v___x_2829_);
lean_inc(v___y_2803_);
v___x_2831_ = l_Lean_mkConst(v___y_2803_, v___x_2830_);
lean_inc(v_a_2823_);
lean_inc_ref(v___y_2806_);
v___x_2832_ = l_Lean_mkApp4(v___x_2831_, v___y_2804_, v___y_2806_, v_a_2817_, v_a_2823_);
v___x_2833_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v___y_2802_, v___x_2832_, v___y_2809_);
v_isSharedCheck_2844_ = !lean_is_exclusive(v___x_2833_);
if (v_isSharedCheck_2844_ == 0)
{
lean_object* v_unused_2845_; 
v_unused_2845_ = lean_ctor_get(v___x_2833_, 0);
lean_dec(v_unused_2845_);
v___x_2835_ = v___x_2833_;
v_isShared_2836_ = v_isSharedCheck_2844_;
goto v_resetjp_2834_;
}
else
{
lean_dec(v___x_2833_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2844_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2842_; 
v___x_2837_ = l_Lean_Meta_FVarSubst_empty;
v___x_2838_ = l_Lean_Meta_FVarSubst_insert(v___x_2837_, v___y_2807_, v___y_2806_);
v___x_2839_ = l_Lean_Expr_mvarId_x21(v_a_2823_);
lean_dec(v_a_2823_);
v___x_2840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2838_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v___x_2840_);
v___x_2842_ = v___x_2835_;
goto v_reusejp_2841_;
}
else
{
lean_object* v_reuseFailAlloc_2843_; 
v_reuseFailAlloc_2843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2843_, 0, v___x_2840_);
v___x_2842_ = v_reuseFailAlloc_2843_;
goto v_reusejp_2841_;
}
v_reusejp_2841_:
{
return v___x_2842_;
}
}
}
else
{
lean_object* v_a_2846_; lean_object* v___x_2848_; uint8_t v_isShared_2849_; uint8_t v_isSharedCheck_2853_; 
lean_dec(v_a_2825_);
lean_dec(v_a_2823_);
lean_dec(v_a_2817_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2802_);
v_a_2846_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2853_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2853_ == 0)
{
v___x_2848_ = v___x_2826_;
v_isShared_2849_ = v_isSharedCheck_2853_;
goto v_resetjp_2847_;
}
else
{
lean_inc(v_a_2846_);
lean_dec(v___x_2826_);
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
lean_dec(v_a_2823_);
lean_dec(v_a_2817_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2802_);
v_a_2854_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2861_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2861_ == 0)
{
v___x_2856_ = v___x_2824_;
v_isShared_2857_ = v_isSharedCheck_2861_;
goto v_resetjp_2855_;
}
else
{
lean_inc(v_a_2854_);
lean_dec(v___x_2824_);
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
lean_dec_ref(v___x_2821_);
lean_dec(v_a_2817_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2802_);
v_a_2862_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2869_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2869_ == 0)
{
v___x_2864_ = v___x_2822_;
v_isShared_2865_ = v_isSharedCheck_2869_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2822_);
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
lean_dec(v_a_2817_);
lean_dec_ref(v___x_2812_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2802_);
v_a_2870_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2877_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2877_ == 0)
{
v___x_2872_ = v___x_2818_;
v_isShared_2873_ = v_isSharedCheck_2877_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2818_);
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
else
{
lean_object* v_a_2878_; lean_object* v___x_2880_; uint8_t v_isShared_2881_; uint8_t v_isSharedCheck_2885_; 
lean_dec_ref(v___x_2812_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2802_);
v_a_2878_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2885_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2885_ == 0)
{
v___x_2880_ = v___x_2816_;
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
else
{
lean_inc(v_a_2878_);
lean_dec(v___x_2816_);
v___x_2880_ = lean_box(0);
v_isShared_2881_ = v_isSharedCheck_2885_;
goto v_resetjp_2879_;
}
v_resetjp_2879_:
{
lean_object* v___x_2883_; 
if (v_isShared_2881_ == 0)
{
v___x_2883_ = v___x_2880_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
}
}
v___jp_2886_:
{
lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; 
v___x_2895_ = l_Lean_Expr_fvarId_x21(v___y_2889_);
v___x_2896_ = lean_unsigned_to_nat(1u);
v___x_2897_ = lean_mk_empty_array_with_capacity(v___x_2896_);
lean_inc(v___x_2895_);
v___x_2898_ = lean_array_push(v___x_2897_, v___x_2895_);
v___x_2899_ = l_Lean_MVarId_revert(v_mvarId_2785_, v___x_2898_, v___x_2799_, v___x_2799_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
if (lean_obj_tag(v___x_2899_) == 0)
{
lean_object* v_a_2900_; lean_object* v_fst_2901_; lean_object* v_snd_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2924_; 
v_a_2900_ = lean_ctor_get(v___x_2899_, 0);
lean_inc(v_a_2900_);
lean_dec_ref_known(v___x_2899_, 1);
v_fst_2901_ = lean_ctor_get(v_a_2900_, 0);
v_snd_2902_ = lean_ctor_get(v_a_2900_, 1);
v_isSharedCheck_2924_ = !lean_is_exclusive(v_a_2900_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2904_ = v_a_2900_;
v_isShared_2905_ = v_isSharedCheck_2924_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_snd_2902_);
lean_inc(v_fst_2901_);
lean_dec(v_a_2900_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2924_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2906_ = lean_array_get_size(v_fst_2901_);
lean_dec(v_fst_2901_);
v___x_2907_ = lean_nat_dec_eq(v___x_2906_, v___x_2896_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2911_; 
lean_dec(v_snd_2902_);
lean_dec(v___x_2895_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v_body_2798_);
v___x_2908_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2909_ = l_Lean_MessageData_ofExpr(v___y_2889_);
if (v_isShared_2905_ == 0)
{
lean_ctor_set_tag(v___x_2904_, 7);
lean_ctor_set(v___x_2904_, 1, v___x_2909_);
lean_ctor_set(v___x_2904_, 0, v___x_2908_);
v___x_2911_ = v___x_2904_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v___x_2908_);
lean_ctor_set(v_reuseFailAlloc_2923_, 1, v___x_2909_);
v___x_2911_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; lean_object* v_a_2915_; lean_object* v___x_2917_; uint8_t v_isShared_2918_; uint8_t v_isSharedCheck_2922_; 
v___x_2912_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2911_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2913_, v___y_2891_, v___y_2892_, v___y_2893_, v___y_2894_);
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2922_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2917_ = v___x_2914_;
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
else
{
lean_inc(v_a_2915_);
lean_dec(v___x_2914_);
v___x_2917_ = lean_box(0);
v_isShared_2918_ = v_isSharedCheck_2922_;
goto v_resetjp_2916_;
}
v_resetjp_2916_:
{
lean_object* v___x_2920_; 
if (v_isShared_2918_ == 0)
{
v___x_2920_ = v___x_2917_;
goto v_reusejp_2919_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v_a_2915_);
v___x_2920_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2919_;
}
v_reusejp_2919_:
{
return v___x_2920_;
}
}
}
}
else
{
lean_del_object(v___x_2904_);
v___y_2801_ = v___x_2896_;
v___y_2802_ = v_snd_2902_;
v___y_2803_ = v___y_2887_;
v___y_2804_ = v___y_2888_;
v___y_2805_ = v___y_2889_;
v___y_2806_ = v___y_2890_;
v___y_2807_ = v___x_2895_;
v___y_2808_ = v___y_2891_;
v___y_2809_ = v___y_2892_;
v___y_2810_ = v___y_2893_;
v___y_2811_ = v___y_2894_;
goto v___jp_2800_;
}
}
}
else
{
lean_object* v_a_2925_; lean_object* v___x_2927_; uint8_t v_isShared_2928_; uint8_t v_isSharedCheck_2932_; 
lean_dec(v___x_2895_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v_body_2798_);
v_a_2925_ = lean_ctor_get(v___x_2899_, 0);
v_isSharedCheck_2932_ = !lean_is_exclusive(v___x_2899_);
if (v_isSharedCheck_2932_ == 0)
{
v___x_2927_ = v___x_2899_;
v_isShared_2928_ = v_isSharedCheck_2932_;
goto v_resetjp_2926_;
}
else
{
lean_inc(v_a_2925_);
lean_dec(v___x_2899_);
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
v___jp_2933_:
{
uint8_t v___x_2942_; 
v___x_2942_ = l_Lean_Expr_isFVar(v_fst_2936_);
if (v___x_2942_ == 0)
{
lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v_a_2945_; lean_object* v___x_2947_; uint8_t v_isShared_2948_; uint8_t v_isSharedCheck_2952_; 
lean_dec_ref(v_fst_2936_);
lean_dec_ref(v_fst_2935_);
lean_dec_ref(v_fst_2934_);
lean_dec_ref(v_body_2798_);
lean_dec(v_mvarId_2785_);
v___x_2943_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2944_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2943_, v___y_2938_, v___y_2939_, v___y_2940_, v___y_2941_);
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_2952_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_2952_ == 0)
{
v___x_2947_ = v___x_2944_;
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
else
{
lean_inc(v_a_2945_);
lean_dec(v___x_2944_);
v___x_2947_ = lean_box(0);
v_isShared_2948_ = v_isSharedCheck_2952_;
goto v_resetjp_2946_;
}
v_resetjp_2946_:
{
lean_object* v___x_2950_; 
if (v_isShared_2948_ == 0)
{
v___x_2950_ = v___x_2947_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2951_; 
v_reuseFailAlloc_2951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2951_, 0, v_a_2945_);
v___x_2950_ = v_reuseFailAlloc_2951_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
return v___x_2950_;
}
}
}
else
{
v___y_2887_ = v_snd_2937_;
v___y_2888_ = v_fst_2934_;
v___y_2889_ = v_fst_2936_;
v___y_2890_ = v_fst_2935_;
v___y_2891_ = v___y_2938_;
v___y_2892_ = v___y_2939_;
v___y_2893_ = v___y_2940_;
v___y_2894_ = v___y_2941_;
goto v___jp_2886_;
}
}
}
else
{
lean_dec(v_a_2793_);
lean_dec(v_mvarId_2785_);
goto v___jp_2794_;
}
v___jp_2794_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2795_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2796_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2795_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_);
return v___x_2796_;
}
}
else
{
lean_object* v_a_3025_; lean_object* v___x_3027_; uint8_t v_isShared_3028_; uint8_t v_isSharedCheck_3032_; 
lean_dec(v_mvarId_2785_);
v_a_3025_ = lean_ctor_get(v___x_2792_, 0);
v_isSharedCheck_3032_ = !lean_is_exclusive(v___x_2792_);
if (v_isSharedCheck_3032_ == 0)
{
v___x_3027_ = v___x_2792_;
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
else
{
lean_inc(v_a_3025_);
lean_dec(v___x_2792_);
v___x_3027_ = lean_box(0);
v_isShared_3028_ = v_isSharedCheck_3032_;
goto v_resetjp_3026_;
}
v_resetjp_3026_:
{
lean_object* v___x_3030_; 
if (v_isShared_3028_ == 0)
{
v___x_3030_ = v___x_3027_;
goto v_reusejp_3029_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v_a_3025_);
v___x_3030_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3029_;
}
v_reusejp_3029_:
{
return v___x_3030_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object* v_mvarId_3033_, lean_object* v_substLHS_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_){
_start:
{
uint8_t v_substLHS_boxed_3040_; lean_object* v_res_3041_; 
v_substLHS_boxed_3040_ = lean_unbox(v_substLHS_3034_);
v_res_3041_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_3033_, v_substLHS_boxed_3040_, v___y_3035_, v___y_3036_, v___y_3037_, v___y_3038_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
return v_res_3041_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3042_, lean_object* v_i_3043_, lean_object* v_k_3044_){
_start:
{
lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3045_ = lean_array_get_size(v_keys_3042_);
v___x_3046_ = lean_nat_dec_lt(v_i_3043_, v___x_3045_);
if (v___x_3046_ == 0)
{
lean_dec(v_i_3043_);
return v___x_3046_;
}
else
{
lean_object* v_k_x27_3047_; uint8_t v___x_3048_; 
v_k_x27_3047_ = lean_array_fget_borrowed(v_keys_3042_, v_i_3043_);
v___x_3048_ = l_Lean_instBEqMVarId_beq(v_k_3044_, v_k_x27_3047_);
if (v___x_3048_ == 0)
{
lean_object* v___x_3049_; lean_object* v___x_3050_; 
v___x_3049_ = lean_unsigned_to_nat(1u);
v___x_3050_ = lean_nat_add(v_i_3043_, v___x_3049_);
lean_dec(v_i_3043_);
v_i_3043_ = v___x_3050_;
goto _start;
}
else
{
lean_dec(v_i_3043_);
return v___x_3048_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3052_, lean_object* v_i_3053_, lean_object* v_k_3054_){
_start:
{
uint8_t v_res_3055_; lean_object* v_r_3056_; 
v_res_3055_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3052_, v_i_3053_, v_k_3054_);
lean_dec(v_k_3054_);
lean_dec_ref(v_keys_3052_);
v_r_3056_ = lean_box(v_res_3055_);
return v_r_3056_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3057_, size_t v_x_3058_, lean_object* v_x_3059_){
_start:
{
if (lean_obj_tag(v_x_3057_) == 0)
{
lean_object* v_es_3060_; lean_object* v___x_3061_; size_t v___x_3062_; size_t v___x_3063_; lean_object* v_j_3064_; lean_object* v___x_3065_; 
v_es_3060_ = lean_ctor_get(v_x_3057_, 0);
v___x_3061_ = lean_box(2);
v___x_3062_ = ((size_t)31ULL);
v___x_3063_ = lean_usize_land(v_x_3058_, v___x_3062_);
v_j_3064_ = lean_usize_to_nat(v___x_3063_);
v___x_3065_ = lean_array_get_borrowed(v___x_3061_, v_es_3060_, v_j_3064_);
lean_dec(v_j_3064_);
switch(lean_obj_tag(v___x_3065_))
{
case 0:
{
lean_object* v_key_3066_; uint8_t v___x_3067_; 
v_key_3066_ = lean_ctor_get(v___x_3065_, 0);
v___x_3067_ = l_Lean_instBEqMVarId_beq(v_x_3059_, v_key_3066_);
return v___x_3067_;
}
case 1:
{
lean_object* v_node_3068_; size_t v___x_3069_; size_t v___x_3070_; 
v_node_3068_ = lean_ctor_get(v___x_3065_, 0);
v___x_3069_ = ((size_t)5ULL);
v___x_3070_ = lean_usize_shift_right(v_x_3058_, v___x_3069_);
v_x_3057_ = v_node_3068_;
v_x_3058_ = v___x_3070_;
goto _start;
}
default: 
{
uint8_t v___x_3072_; 
v___x_3072_ = 0;
return v___x_3072_;
}
}
}
else
{
lean_object* v_ks_3073_; lean_object* v___x_3074_; uint8_t v___x_3075_; 
v_ks_3073_ = lean_ctor_get(v_x_3057_, 0);
v___x_3074_ = lean_unsigned_to_nat(0u);
v___x_3075_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3073_, v___x_3074_, v_x_3059_);
return v___x_3075_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3076_, lean_object* v_x_3077_, lean_object* v_x_3078_){
_start:
{
size_t v_x_12601__boxed_3079_; uint8_t v_res_3080_; lean_object* v_r_3081_; 
v_x_12601__boxed_3079_ = lean_unbox_usize(v_x_3077_);
lean_dec(v_x_3077_);
v_res_3080_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3076_, v_x_12601__boxed_3079_, v_x_3078_);
lean_dec(v_x_3078_);
lean_dec_ref(v_x_3076_);
v_r_3081_ = lean_box(v_res_3080_);
return v_r_3081_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3082_, lean_object* v_x_3083_){
_start:
{
uint64_t v___x_3084_; size_t v___x_3085_; uint8_t v___x_3086_; 
v___x_3084_ = l_Lean_instHashableMVarId_hash(v_x_3083_);
v___x_3085_ = lean_uint64_to_usize(v___x_3084_);
v___x_3086_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3082_, v___x_3085_, v_x_3083_);
return v___x_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3087_, lean_object* v_x_3088_){
_start:
{
uint8_t v_res_3089_; lean_object* v_r_3090_; 
v_res_3089_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3087_, v_x_3088_);
lean_dec(v_x_3088_);
lean_dec_ref(v_x_3087_);
v_r_3090_ = lean_box(v_res_3089_);
return v_r_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v___x_3094_; lean_object* v_mctx_3095_; lean_object* v_eAssignment_3096_; uint8_t v___x_3097_; lean_object* v___x_3098_; lean_object* v___x_3099_; 
v___x_3094_ = lean_st_ref_get(v___y_3092_);
v_mctx_3095_ = lean_ctor_get(v___x_3094_, 0);
lean_inc_ref(v_mctx_3095_);
lean_dec(v___x_3094_);
v_eAssignment_3096_ = lean_ctor_get(v_mctx_3095_, 8);
lean_inc_ref(v_eAssignment_3096_);
lean_dec_ref(v_mctx_3095_);
v___x_3097_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3096_, v_mvarId_3091_);
lean_dec_ref(v_eAssignment_3096_);
v___x_3098_ = lean_box(v___x_3097_);
v___x_3099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
return v___x_3099_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3100_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec(v_mvarId_3100_);
return v_res_3103_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; 
v___x_3105_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3106_ = l_Lean_stringToMessageData(v___x_3105_);
return v___x_3106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3107_, uint8_t v___y_3108_, lean_object* v_____r_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___x_3151_; lean_object* v_a_3152_; uint8_t v___x_3153_; 
v___x_3151_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3107_, v___y_3111_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
lean_inc(v_a_3152_);
lean_dec_ref(v___x_3151_);
v___x_3153_ = lean_unbox(v_a_3152_);
lean_dec(v_a_3152_);
if (v___x_3153_ == 0)
{
v___y_3116_ = v___y_3110_;
v___y_3117_ = v___y_3111_;
v___y_3118_ = v___y_3112_;
v___y_3119_ = v___y_3113_;
goto v___jp_3115_;
}
else
{
lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v_a_3156_; lean_object* v___x_3158_; uint8_t v_isShared_3159_; uint8_t v_isSharedCheck_3163_; 
lean_dec(v_mvarId_3107_);
v___x_3154_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3155_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3154_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
v_isSharedCheck_3163_ = !lean_is_exclusive(v___x_3155_);
if (v_isSharedCheck_3163_ == 0)
{
v___x_3158_ = v___x_3155_;
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
else
{
lean_inc(v_a_3156_);
lean_dec(v___x_3155_);
v___x_3158_ = lean_box(0);
v_isShared_3159_ = v_isSharedCheck_3163_;
goto v_resetjp_3157_;
}
v_resetjp_3157_:
{
lean_object* v___x_3161_; 
if (v_isShared_3159_ == 0)
{
v___x_3161_ = v___x_3158_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v_a_3156_);
v___x_3161_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
return v___x_3161_;
}
}
}
v___jp_3115_:
{
lean_object* v___x_3120_; 
v___x_3120_ = l_Lean_Meta_intro1Core(v_mvarId_3107_, v___y_3108_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
if (lean_obj_tag(v___x_3120_) == 0)
{
lean_object* v_a_3121_; lean_object* v_fst_3122_; lean_object* v_snd_3123_; lean_object* v___x_3124_; lean_object* v___x_3125_; 
v_a_3121_ = lean_ctor_get(v___x_3120_, 0);
lean_inc(v_a_3121_);
lean_dec_ref_known(v___x_3120_, 1);
v_fst_3122_ = lean_ctor_get(v_a_3121_, 0);
lean_inc(v_fst_3122_);
v_snd_3123_ = lean_ctor_get(v_a_3121_, 1);
lean_inc(v_snd_3123_);
lean_dec(v_a_3121_);
v___x_3124_ = lean_box(0);
v___x_3125_ = l_Lean_Meta_substEq(v_snd_3123_, v_fst_3122_, v___x_3124_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_);
if (lean_obj_tag(v___x_3125_) == 0)
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3134_; 
v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3128_ = v___x_3125_;
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3125_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3134_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3130_; lean_object* v___x_3132_; 
v___x_3130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_a_3126_);
if (v_isShared_3129_ == 0)
{
lean_ctor_set(v___x_3128_, 0, v___x_3130_);
v___x_3132_ = v___x_3128_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v___x_3130_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
v_a_3135_ = lean_ctor_get(v___x_3125_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3125_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3125_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3125_);
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
else
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
v_a_3143_ = lean_ctor_get(v___x_3120_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3120_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3120_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3120_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3164_, lean_object* v___y_3165_, lean_object* v_____r_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_){
_start:
{
uint8_t v___y_12673__boxed_3172_; lean_object* v_res_3173_; 
v___y_12673__boxed_3172_ = lean_unbox(v___y_3165_);
v_res_3173_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3164_, v___y_12673__boxed_3172_, v_____r_3166_, v___y_3167_, v___y_3168_, v___y_3169_, v___y_3170_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
return v_res_3173_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__2(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3177_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3178_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
v___x_3179_ = l_Lean_Name_append(v___x_3178_, v___x_3177_);
return v___x_3179_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__4(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; 
v___x_3181_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__3));
v___x_3182_ = l_Lean_stringToMessageData(v___x_3181_);
return v___x_3182_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__6(void){
_start:
{
lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3184_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__5));
v___x_3185_ = l_Lean_stringToMessageData(v___x_3184_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3186_, uint8_t v_substLHS_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_){
_start:
{
lean_object* v___y_3194_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3212_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
lean_inc(v_mvarId_3186_);
v___x_3213_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3186_, v___x_3212_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_object* v___x_3214_; lean_object* v___f_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
lean_dec_ref_known(v___x_3213_, 1);
v___x_3214_ = lean_box(v_substLHS_3187_);
lean_inc_n(v_mvarId_3186_, 2);
v___f_3215_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3215_, 0, v_mvarId_3186_);
lean_closure_set(v___f_3215_, 1, v___x_3214_);
v___x_3216_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed), 8, 3);
lean_closure_set(v___x_3216_, 0, lean_box(0));
lean_closure_set(v___x_3216_, 1, v_mvarId_3186_);
lean_closure_set(v___x_3216_, 2, v___f_3215_);
v___x_3217_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3216_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_dec(v_mvarId_3186_);
return v___x_3217_;
}
else
{
lean_object* v_a_3218_; lean_object* v___y_3220_; uint8_t v___y_3224_; uint8_t v___x_3258_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
v___x_3258_ = l_Lean_Exception_isInterrupt(v_a_3218_);
if (v___x_3258_ == 0)
{
uint8_t v___x_3259_; 
lean_inc(v_a_3218_);
v___x_3259_ = l_Lean_Exception_isRuntime(v_a_3218_);
v___y_3224_ = v___x_3259_;
goto v___jp_3223_;
}
else
{
v___y_3224_ = v___x_3258_;
goto v___jp_3223_;
}
v___jp_3219_:
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_box(0);
lean_inc(v_a_3191_);
lean_inc_ref(v_a_3190_);
lean_inc(v_a_3189_);
lean_inc_ref(v_a_3188_);
v___x_3222_ = lean_apply_6(v___y_3220_, v___x_3221_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, lean_box(0));
v___y_3194_ = v___x_3222_;
goto v___jp_3193_;
}
v___jp_3223_:
{
if (v___y_3224_ == 0)
{
lean_object* v___x_3226_; uint8_t v_isShared_3227_; uint8_t v_isSharedCheck_3256_; 
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3256_ == 0)
{
lean_object* v_unused_3257_; 
v_unused_3257_ = lean_ctor_get(v___x_3217_, 0);
lean_dec(v_unused_3257_);
v___x_3226_ = v___x_3217_;
v_isShared_3227_ = v_isSharedCheck_3256_;
goto v_resetjp_3225_;
}
else
{
lean_dec(v___x_3217_);
v___x_3226_ = lean_box(0);
v_isShared_3227_ = v_isSharedCheck_3256_;
goto v_resetjp_3225_;
}
v_resetjp_3225_:
{
lean_object* v_options_3228_; lean_object* v_inheritedTraceOptions_3229_; uint8_t v_hasTrace_3230_; lean_object* v___x_3231_; lean_object* v___f_3232_; 
v_options_3228_ = lean_ctor_get(v_a_3190_, 2);
v_inheritedTraceOptions_3229_ = lean_ctor_get(v_a_3190_, 13);
v_hasTrace_3230_ = lean_ctor_get_uint8(v_options_3228_, sizeof(void*)*1);
v___x_3231_ = lean_box(v___y_3224_);
lean_inc(v_mvarId_3186_);
v___f_3232_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3232_, 0, v_mvarId_3186_);
lean_closure_set(v___f_3232_, 1, v___x_3231_);
if (v_hasTrace_3230_ == 0)
{
lean_del_object(v___x_3226_);
lean_dec(v_a_3218_);
lean_dec(v_mvarId_3186_);
v___y_3220_ = v___f_3232_;
goto v___jp_3219_;
}
else
{
lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; 
v___x_3233_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3234_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__2, &l_Lean_Meta_introSubstEq___closed__2_once, _init_l_Lean_Meta_introSubstEq___closed__2);
v___x_3235_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3229_, v_options_3228_, v___x_3234_);
if (v___x_3235_ == 0)
{
lean_del_object(v___x_3226_);
lean_dec(v_a_3218_);
lean_dec(v_mvarId_3186_);
v___y_3220_ = v___f_3232_;
goto v___jp_3219_;
}
else
{
lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3242_; 
lean_dec_ref(v___f_3232_);
v___x_3236_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__4, &l_Lean_Meta_introSubstEq___closed__4_once, _init_l_Lean_Meta_introSubstEq___closed__4);
v___x_3237_ = l_Lean_Exception_toMessageData(v_a_3218_);
v___x_3238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
v___x_3239_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__6, &l_Lean_Meta_introSubstEq___closed__6_once, _init_l_Lean_Meta_introSubstEq___closed__6);
v___x_3240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3238_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
lean_inc(v_mvarId_3186_);
if (v_isShared_3227_ == 0)
{
lean_ctor_set(v___x_3226_, 0, v_mvarId_3186_);
v___x_3242_ = v___x_3226_;
goto v_reusejp_3241_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_mvarId_3186_);
v___x_3242_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3241_;
}
v_reusejp_3241_:
{
lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3243_, 0, v___x_3240_);
lean_ctor_set(v___x_3243_, 1, v___x_3242_);
v___x_3244_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_3233_, v___x_3243_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
if (lean_obj_tag(v___x_3244_) == 0)
{
lean_object* v_a_3245_; lean_object* v___x_3246_; 
v_a_3245_ = lean_ctor_get(v___x_3244_, 0);
lean_inc(v_a_3245_);
lean_dec_ref_known(v___x_3244_, 1);
v___x_3246_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3186_, v___y_3224_, v_a_3245_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_);
v___y_3194_ = v___x_3246_;
goto v___jp_3193_;
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec(v_mvarId_3186_);
v_a_3247_ = lean_ctor_get(v___x_3244_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3244_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3244_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3244_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
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
lean_dec(v_a_3218_);
lean_dec(v_mvarId_3186_);
return v___x_3217_;
}
}
}
}
else
{
lean_object* v_a_3260_; lean_object* v___x_3262_; uint8_t v_isShared_3263_; uint8_t v_isSharedCheck_3267_; 
lean_dec(v_mvarId_3186_);
v_a_3260_ = lean_ctor_get(v___x_3213_, 0);
v_isSharedCheck_3267_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3267_ == 0)
{
v___x_3262_ = v___x_3213_;
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
else
{
lean_inc(v_a_3260_);
lean_dec(v___x_3213_);
v___x_3262_ = lean_box(0);
v_isShared_3263_ = v_isSharedCheck_3267_;
goto v_resetjp_3261_;
}
v_resetjp_3261_:
{
lean_object* v___x_3265_; 
if (v_isShared_3263_ == 0)
{
v___x_3265_ = v___x_3262_;
goto v_reusejp_3264_;
}
else
{
lean_object* v_reuseFailAlloc_3266_; 
v_reuseFailAlloc_3266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3266_, 0, v_a_3260_);
v___x_3265_ = v_reuseFailAlloc_3266_;
goto v_reusejp_3264_;
}
v_reusejp_3264_:
{
return v___x_3265_;
}
}
}
v___jp_3193_:
{
if (lean_obj_tag(v___y_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3203_; 
v_a_3195_ = lean_ctor_get(v___y_3194_, 0);
v_isSharedCheck_3203_ = !lean_is_exclusive(v___y_3194_);
if (v_isSharedCheck_3203_ == 0)
{
v___x_3197_ = v___y_3194_;
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
else
{
lean_inc(v_a_3195_);
lean_dec(v___y_3194_);
v___x_3197_ = lean_box(0);
v_isShared_3198_ = v_isSharedCheck_3203_;
goto v_resetjp_3196_;
}
v_resetjp_3196_:
{
lean_object* v_a_3199_; lean_object* v___x_3201_; 
v_a_3199_ = lean_ctor_get(v_a_3195_, 0);
lean_inc(v_a_3199_);
lean_dec(v_a_3195_);
if (v_isShared_3198_ == 0)
{
lean_ctor_set(v___x_3197_, 0, v_a_3199_);
v___x_3201_ = v___x_3197_;
goto v_reusejp_3200_;
}
else
{
lean_object* v_reuseFailAlloc_3202_; 
v_reuseFailAlloc_3202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3202_, 0, v_a_3199_);
v___x_3201_ = v_reuseFailAlloc_3202_;
goto v_reusejp_3200_;
}
v_reusejp_3200_:
{
return v___x_3201_;
}
}
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3211_; 
v_a_3204_ = lean_ctor_get(v___y_3194_, 0);
v_isSharedCheck_3211_ = !lean_is_exclusive(v___y_3194_);
if (v_isSharedCheck_3211_ == 0)
{
v___x_3206_ = v___y_3194_;
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_a_3204_);
lean_dec(v___y_3194_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3211_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3209_; 
if (v_isShared_3207_ == 0)
{
v___x_3209_ = v___x_3206_;
goto v_reusejp_3208_;
}
else
{
lean_object* v_reuseFailAlloc_3210_; 
v_reuseFailAlloc_3210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_a_3204_);
v___x_3209_ = v_reuseFailAlloc_3210_;
goto v_reusejp_3208_;
}
v_reusejp_3208_:
{
return v___x_3209_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object* v_mvarId_3268_, lean_object* v_substLHS_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_, lean_object* v_a_3273_, lean_object* v_a_3274_){
_start:
{
uint8_t v_substLHS_boxed_3275_; lean_object* v_res_3276_; 
v_substLHS_boxed_3275_ = lean_unbox(v_substLHS_3269_);
v_res_3276_ = l_Lean_Meta_introSubstEq(v_mvarId_3268_, v_substLHS_boxed_3275_, v_a_3270_, v_a_3271_, v_a_3272_, v_a_3273_);
lean_dec(v_a_3273_);
lean_dec_ref(v_a_3272_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3270_);
return v_res_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object* v_00_u03b1_3277_, lean_object* v_msg_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_){
_start:
{
lean_object* v___x_3284_; 
v___x_3284_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_3278_, v___y_3279_, v___y_3280_, v___y_3281_, v___y_3282_);
return v___x_3284_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object* v_00_u03b1_3285_, lean_object* v_msg_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_){
_start:
{
lean_object* v_res_3292_; 
v_res_3292_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(v_00_u03b1_3285_, v_msg_3286_, v___y_3287_, v___y_3288_, v___y_3289_, v___y_3290_);
lean_dec(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
return v_res_3292_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object* v_mvarId_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_, lean_object* v___y_3296_, lean_object* v___y_3297_){
_start:
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3293_, v___y_3295_);
return v___x_3299_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object* v_mvarId_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_){
_start:
{
lean_object* v_res_3306_; 
v_res_3306_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v_mvarId_3300_);
return v_res_3306_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object* v_00_u03b2_3307_, lean_object* v_x_3308_, lean_object* v_x_3309_){
_start:
{
uint8_t v___x_3310_; 
v___x_3310_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3308_, v_x_3309_);
return v___x_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3311_, lean_object* v_x_3312_, lean_object* v_x_3313_){
_start:
{
uint8_t v_res_3314_; lean_object* v_r_3315_; 
v_res_3314_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(v_00_u03b2_3311_, v_x_3312_, v_x_3313_);
lean_dec(v_x_3313_);
lean_dec_ref(v_x_3312_);
v_r_3315_ = lean_box(v_res_3314_);
return v_r_3315_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_3316_, lean_object* v_x_3317_, size_t v_x_3318_, lean_object* v_x_3319_){
_start:
{
uint8_t v___x_3320_; 
v___x_3320_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3317_, v_x_3318_, v_x_3319_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3321_, lean_object* v_x_3322_, lean_object* v_x_3323_, lean_object* v_x_3324_){
_start:
{
size_t v_x_13037__boxed_3325_; uint8_t v_res_3326_; lean_object* v_r_3327_; 
v_x_13037__boxed_3325_ = lean_unbox_usize(v_x_3323_);
lean_dec(v_x_3323_);
v_res_3326_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3321_, v_x_3322_, v_x_13037__boxed_3325_, v_x_3324_);
lean_dec(v_x_3324_);
lean_dec_ref(v_x_3322_);
v_r_3327_ = lean_box(v_res_3326_);
return v_r_3327_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3328_, lean_object* v_keys_3329_, lean_object* v_vals_3330_, lean_object* v_heq_3331_, lean_object* v_i_3332_, lean_object* v_k_3333_){
_start:
{
uint8_t v___x_3334_; 
v___x_3334_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3329_, v_i_3332_, v_k_3333_);
return v___x_3334_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3335_, lean_object* v_keys_3336_, lean_object* v_vals_3337_, lean_object* v_heq_3338_, lean_object* v_i_3339_, lean_object* v_k_3340_){
_start:
{
uint8_t v_res_3341_; lean_object* v_r_3342_; 
v_res_3341_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(v_00_u03b2_3335_, v_keys_3336_, v_vals_3337_, v_heq_3338_, v_i_3339_, v_k_3340_);
lean_dec(v_k_3340_);
lean_dec_ref(v_vals_3337_);
lean_dec_ref(v_keys_3336_);
v_r_3342_ = lean_box(v_res_3341_);
return v_r_3342_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* v_x_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_){
_start:
{
lean_object* v___x_3349_; 
v___x_3349_ = l_Lean_Meta_saveState___redArg(v___y_3345_, v___y_3347_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3351_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
lean_inc(v___y_3347_);
lean_inc_ref(v___y_3346_);
lean_inc(v___y_3345_);
lean_inc_ref(v___y_3344_);
v___x_3351_ = lean_apply_5(v_x_3343_, v___y_3344_, v___y_3345_, v___y_3346_, v___y_3347_, lean_box(0));
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v___x_3354_; uint8_t v_isShared_3355_; uint8_t v_isSharedCheck_3360_; 
lean_dec(v_a_3350_);
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3360_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3360_ == 0)
{
v___x_3354_ = v___x_3351_;
v_isShared_3355_ = v_isSharedCheck_3360_;
goto v_resetjp_3353_;
}
else
{
lean_inc(v_a_3352_);
lean_dec(v___x_3351_);
v___x_3354_ = lean_box(0);
v_isShared_3355_ = v_isSharedCheck_3360_;
goto v_resetjp_3353_;
}
v_resetjp_3353_:
{
lean_object* v___x_3356_; lean_object* v___x_3358_; 
v___x_3356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3356_, 0, v_a_3352_);
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
lean_object* v_a_3361_; lean_object* v___x_3363_; uint8_t v_isShared_3364_; uint8_t v_isSharedCheck_3390_; 
v_a_3361_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3390_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3390_ == 0)
{
v___x_3363_ = v___x_3351_;
v_isShared_3364_ = v_isSharedCheck_3390_;
goto v_resetjp_3362_;
}
else
{
lean_inc(v_a_3361_);
lean_dec(v___x_3351_);
v___x_3363_ = lean_box(0);
v_isShared_3364_ = v_isSharedCheck_3390_;
goto v_resetjp_3362_;
}
v_resetjp_3362_:
{
uint8_t v___y_3366_; uint8_t v___x_3388_; 
v___x_3388_ = l_Lean_Exception_isInterrupt(v_a_3361_);
if (v___x_3388_ == 0)
{
uint8_t v___x_3389_; 
lean_inc(v_a_3361_);
v___x_3389_ = l_Lean_Exception_isRuntime(v_a_3361_);
v___y_3366_ = v___x_3389_;
goto v___jp_3365_;
}
else
{
v___y_3366_ = v___x_3388_;
goto v___jp_3365_;
}
v___jp_3365_:
{
if (v___y_3366_ == 0)
{
lean_object* v___x_3367_; 
lean_del_object(v___x_3363_);
lean_dec(v_a_3361_);
v___x_3367_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3350_, v___y_3345_, v___y_3347_);
lean_dec(v_a_3350_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3375_; 
v_isSharedCheck_3375_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3375_ == 0)
{
lean_object* v_unused_3376_; 
v_unused_3376_ = lean_ctor_get(v___x_3367_, 0);
lean_dec(v_unused_3376_);
v___x_3369_ = v___x_3367_;
v_isShared_3370_ = v_isSharedCheck_3375_;
goto v_resetjp_3368_;
}
else
{
lean_dec(v___x_3367_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3375_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3371_ = lean_box(0);
if (v_isShared_3370_ == 0)
{
lean_ctor_set(v___x_3369_, 0, v___x_3371_);
v___x_3373_ = v___x_3369_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3374_; 
v_reuseFailAlloc_3374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3374_, 0, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3374_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
return v___x_3373_;
}
}
}
else
{
lean_object* v_a_3377_; lean_object* v___x_3379_; uint8_t v_isShared_3380_; uint8_t v_isSharedCheck_3384_; 
v_a_3377_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3384_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3384_ == 0)
{
v___x_3379_ = v___x_3367_;
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
else
{
lean_inc(v_a_3377_);
lean_dec(v___x_3367_);
v___x_3379_ = lean_box(0);
v_isShared_3380_ = v_isSharedCheck_3384_;
goto v_resetjp_3378_;
}
v_resetjp_3378_:
{
lean_object* v___x_3382_; 
if (v_isShared_3380_ == 0)
{
v___x_3382_ = v___x_3379_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3377_);
v___x_3382_ = v_reuseFailAlloc_3383_;
goto v_reusejp_3381_;
}
v_reusejp_3381_:
{
return v___x_3382_;
}
}
}
}
else
{
lean_object* v___x_3386_; 
lean_dec(v_a_3350_);
if (v_isShared_3364_ == 0)
{
v___x_3386_ = v___x_3363_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3361_);
v___x_3386_ = v_reuseFailAlloc_3387_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
return v___x_3386_;
}
}
}
}
}
}
else
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3398_; 
lean_dec_ref(v_x_3343_);
v_a_3391_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3398_ == 0)
{
v___x_3393_ = v___x_3349_;
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3349_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3398_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3396_; 
if (v_isShared_3394_ == 0)
{
v___x_3396_ = v___x_3393_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_a_3391_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
return v___x_3396_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object* v_x_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_){
_start:
{
lean_object* v_res_3405_; 
v_res_3405_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3399_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
lean_dec(v___y_3403_);
lean_dec_ref(v___y_3402_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
return v_res_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object* v_00_u03b1_3406_, lean_object* v_x_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_){
_start:
{
lean_object* v___x_3413_; 
v___x_3413_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
return v___x_3413_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object* v_00_u03b1_3414_, lean_object* v_x_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_){
_start:
{
lean_object* v_res_3421_; 
v_res_3421_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(v_00_u03b1_3414_, v_x_3415_, v___y_3416_, v___y_3417_, v___y_3418_, v___y_3419_);
lean_dec(v___y_3419_);
lean_dec_ref(v___y_3418_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
return v_res_3421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* v_mvarId_3422_, lean_object* v_hFVarId_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_, lean_object* v_a_3426_, lean_object* v_a_3427_){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; 
v___x_3429_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___boxed), 7, 2);
lean_closure_set(v___x_3429_, 0, v_mvarId_3422_);
lean_closure_set(v___x_3429_, 1, v_hFVarId_3423_);
v___x_3430_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3429_, v_a_3424_, v_a_3425_, v_a_3426_, v_a_3427_);
return v___x_3430_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object* v_mvarId_3431_, lean_object* v_hFVarId_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_, lean_object* v_a_3436_, lean_object* v_a_3437_){
_start:
{
lean_object* v_res_3438_; 
v_res_3438_ = l_Lean_Meta_substVar_x3f(v_mvarId_3431_, v_hFVarId_3432_, v_a_3433_, v_a_3434_, v_a_3435_, v_a_3436_);
lean_dec(v_a_3436_);
lean_dec_ref(v_a_3435_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
return v_res_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* v_mvarId_3439_, lean_object* v_hFVarId_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_, lean_object* v_a_3443_, lean_object* v_a_3444_){
_start:
{
lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3446_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 7, 2);
lean_closure_set(v___x_3446_, 0, v_mvarId_3439_);
lean_closure_set(v___x_3446_, 1, v_hFVarId_3440_);
v___x_3447_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3446_, v_a_3441_, v_a_3442_, v_a_3443_, v_a_3444_);
return v___x_3447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object* v_mvarId_3448_, lean_object* v_hFVarId_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_, lean_object* v_a_3453_, lean_object* v_a_3454_){
_start:
{
lean_object* v_res_3455_; 
v_res_3455_ = l_Lean_Meta_subst_x3f(v_mvarId_3448_, v_hFVarId_3449_, v_a_3450_, v_a_3451_, v_a_3452_, v_a_3453_);
lean_dec(v_a_3453_);
lean_dec_ref(v_a_3452_);
lean_dec(v_a_3451_);
lean_dec_ref(v_a_3450_);
return v_res_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* v_mvarId_3456_, lean_object* v_hFVarId_3457_, uint8_t v_symm_3458_, lean_object* v_fvarSubst_3459_, uint8_t v_clearH_3460_, uint8_t v_tryToSkip_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_){
_start:
{
lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; lean_object* v___x_3470_; lean_object* v___x_3471_; 
v___x_3467_ = lean_box(v_symm_3458_);
v___x_3468_ = lean_box(v_clearH_3460_);
v___x_3469_ = lean_box(v_tryToSkip_3461_);
v___x_3470_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_3470_, 0, v_mvarId_3456_);
lean_closure_set(v___x_3470_, 1, v_hFVarId_3457_);
lean_closure_set(v___x_3470_, 2, v___x_3467_);
lean_closure_set(v___x_3470_, 3, v_fvarSubst_3459_);
lean_closure_set(v___x_3470_, 4, v___x_3468_);
lean_closure_set(v___x_3470_, 5, v___x_3469_);
v___x_3471_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3470_, v_a_3462_, v_a_3463_, v_a_3464_, v_a_3465_);
return v___x_3471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* v_mvarId_3472_, lean_object* v_hFVarId_3473_, lean_object* v_symm_3474_, lean_object* v_fvarSubst_3475_, lean_object* v_clearH_3476_, lean_object* v_tryToSkip_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_){
_start:
{
uint8_t v_symm_boxed_3483_; uint8_t v_clearH_boxed_3484_; uint8_t v_tryToSkip_boxed_3485_; lean_object* v_res_3486_; 
v_symm_boxed_3483_ = lean_unbox(v_symm_3474_);
v_clearH_boxed_3484_ = lean_unbox(v_clearH_3476_);
v_tryToSkip_boxed_3485_ = lean_unbox(v_tryToSkip_3477_);
v_res_3486_ = l_Lean_Meta_substCore_x3f(v_mvarId_3472_, v_hFVarId_3473_, v_symm_boxed_3483_, v_fvarSubst_3475_, v_clearH_boxed_3484_, v_tryToSkip_boxed_3485_, v_a_3478_, v_a_3479_, v_a_3480_, v_a_3481_);
lean_dec(v_a_3481_);
lean_dec_ref(v_a_3480_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
return v_res_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* v_mvarId_3487_, lean_object* v_hFVarId_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_){
_start:
{
lean_object* v___x_3494_; 
lean_inc(v_mvarId_3487_);
v___x_3494_ = l_Lean_Meta_substVar_x3f(v_mvarId_3487_, v_hFVarId_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3506_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3506_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3506_ == 0)
{
v___x_3497_ = v___x_3494_;
v_isShared_3498_ = v_isSharedCheck_3506_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_a_3495_);
lean_dec(v___x_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3506_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
if (lean_obj_tag(v_a_3495_) == 0)
{
lean_object* v___x_3500_; 
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v_mvarId_3487_);
v___x_3500_ = v___x_3497_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_mvarId_3487_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
else
{
lean_object* v_val_3502_; lean_object* v___x_3504_; 
lean_dec(v_mvarId_3487_);
v_val_3502_ = lean_ctor_get(v_a_3495_, 0);
lean_inc(v_val_3502_);
lean_dec_ref_known(v_a_3495_, 1);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v_val_3502_);
v___x_3504_ = v___x_3497_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_val_3502_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
}
}
else
{
lean_object* v_a_3507_; lean_object* v___x_3509_; uint8_t v_isShared_3510_; uint8_t v_isSharedCheck_3514_; 
lean_dec(v_mvarId_3487_);
v_a_3507_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3514_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3514_ == 0)
{
v___x_3509_ = v___x_3494_;
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
else
{
lean_inc(v_a_3507_);
lean_dec(v___x_3494_);
v___x_3509_ = lean_box(0);
v_isShared_3510_ = v_isSharedCheck_3514_;
goto v_resetjp_3508_;
}
v_resetjp_3508_:
{
lean_object* v___x_3512_; 
if (v_isShared_3510_ == 0)
{
v___x_3512_ = v___x_3509_;
goto v_reusejp_3511_;
}
else
{
lean_object* v_reuseFailAlloc_3513_; 
v_reuseFailAlloc_3513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3513_, 0, v_a_3507_);
v___x_3512_ = v_reuseFailAlloc_3513_;
goto v_reusejp_3511_;
}
v_reusejp_3511_:
{
return v___x_3512_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object* v_mvarId_3515_, lean_object* v_hFVarId_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
lean_object* v_res_3522_; 
v_res_3522_ = l_Lean_Meta_trySubstVar(v_mvarId_3515_, v_hFVarId_3516_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
return v_res_3522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* v_mvarId_3523_, lean_object* v_hFVarId_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_, lean_object* v_a_3527_, lean_object* v_a_3528_){
_start:
{
lean_object* v___x_3530_; 
lean_inc(v_mvarId_3523_);
v___x_3530_ = l_Lean_Meta_subst_x3f(v_mvarId_3523_, v_hFVarId_3524_, v_a_3525_, v_a_3526_, v_a_3527_, v_a_3528_);
if (lean_obj_tag(v___x_3530_) == 0)
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3542_; 
v_a_3531_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3533_ = v___x_3530_;
v_isShared_3534_ = v_isSharedCheck_3542_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3530_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3542_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
if (lean_obj_tag(v_a_3531_) == 0)
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v_mvarId_3523_);
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_mvarId_3523_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
else
{
lean_object* v_val_3538_; lean_object* v___x_3540_; 
lean_dec(v_mvarId_3523_);
v_val_3538_ = lean_ctor_get(v_a_3531_, 0);
lean_inc(v_val_3538_);
lean_dec_ref_known(v_a_3531_, 1);
if (v_isShared_3534_ == 0)
{
lean_ctor_set(v___x_3533_, 0, v_val_3538_);
v___x_3540_ = v___x_3533_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_val_3538_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec(v_mvarId_3523_);
v_a_3543_ = lean_ctor_get(v___x_3530_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3530_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3530_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3530_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object* v_mvarId_3551_, lean_object* v_hFVarId_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_){
_start:
{
lean_object* v_res_3558_; 
v_res_3558_ = l_Lean_Meta_trySubst(v_mvarId_3551_, v_hFVarId_3552_, v_a_3553_, v_a_3554_, v_a_3555_, v_a_3556_);
lean_dec(v_a_3556_);
lean_dec_ref(v_a_3555_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
return v_res_3558_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_mvarId_3562_, lean_object* v_as_3563_, size_t v_sz_3564_, size_t v_i_3565_, lean_object* v_b_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_, lean_object* v___y_3569_, lean_object* v___y_3570_){
_start:
{
uint8_t v___x_3572_; 
v___x_3572_ = lean_usize_dec_lt(v_i_3565_, v_sz_3564_);
if (v___x_3572_ == 0)
{
lean_object* v___x_3573_; 
lean_dec(v_mvarId_3562_);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v_b_3566_);
return v___x_3573_;
}
else
{
lean_object* v_snd_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3627_; 
v_snd_3574_ = lean_ctor_get(v_b_3566_, 1);
v_isSharedCheck_3627_ = !lean_is_exclusive(v_b_3566_);
if (v_isSharedCheck_3627_ == 0)
{
lean_object* v_unused_3628_; 
v_unused_3628_ = lean_ctor_get(v_b_3566_, 0);
lean_dec(v_unused_3628_);
v___x_3576_ = v_b_3566_;
v_isShared_3577_ = v_isSharedCheck_3627_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_snd_3574_);
lean_dec(v_b_3566_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3627_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3578_; lean_object* v_a_3580_; lean_object* v_a_3587_; 
v___x_3578_ = lean_box(0);
v_a_3587_ = lean_array_uget(v_as_3563_, v_i_3565_);
if (lean_obj_tag(v_a_3587_) == 0)
{
v_a_3580_ = v_snd_3574_;
goto v___jp_3579_;
}
else
{
lean_object* v_val_3588_; lean_object* v___x_3590_; uint8_t v_isShared_3591_; uint8_t v_isSharedCheck_3626_; 
v_val_3588_ = lean_ctor_get(v_a_3587_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_a_3587_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3590_ = v_a_3587_;
v_isShared_3591_ = v_isSharedCheck_3626_;
goto v_resetjp_3589_;
}
else
{
lean_inc(v_val_3588_);
lean_dec(v_a_3587_);
v___x_3590_ = lean_box(0);
v_isShared_3591_ = v_isSharedCheck_3626_;
goto v_resetjp_3589_;
}
v_resetjp_3589_:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = l_Lean_LocalDecl_fvarId(v_val_3588_);
lean_dec(v_val_3588_);
lean_inc(v_mvarId_3562_);
v___x_3593_ = l_Lean_Meta_subst_x3f(v_mvarId_3562_, v___x_3592_, v___y_3567_, v___y_3568_, v___y_3569_, v___y_3570_);
if (lean_obj_tag(v___x_3593_) == 0)
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3617_; 
v_a_3594_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3596_ = v___x_3593_;
v_isShared_3597_ = v_isSharedCheck_3617_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3593_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3617_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3598_; 
v___x_3598_ = lean_box(0);
if (lean_obj_tag(v_a_3594_) == 1)
{
lean_object* v___x_3600_; 
lean_del_object(v___x_3576_);
lean_dec(v_mvarId_3562_);
lean_inc_ref(v_a_3594_);
if (v_isShared_3591_ == 0)
{
lean_ctor_set(v___x_3590_, 0, v_a_3594_);
v___x_3600_ = v___x_3590_;
goto v_reusejp_3599_;
}
else
{
lean_object* v_reuseFailAlloc_3615_; 
v_reuseFailAlloc_3615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3615_, 0, v_a_3594_);
v___x_3600_ = v_reuseFailAlloc_3615_;
goto v_reusejp_3599_;
}
v_reusejp_3599_:
{
lean_object* v___x_3602_; uint8_t v_isShared_3603_; uint8_t v_isSharedCheck_3613_; 
v_isSharedCheck_3613_ = !lean_is_exclusive(v_a_3594_);
if (v_isSharedCheck_3613_ == 0)
{
lean_object* v_unused_3614_; 
v_unused_3614_ = lean_ctor_get(v_a_3594_, 0);
lean_dec(v_unused_3614_);
v___x_3602_ = v_a_3594_;
v_isShared_3603_ = v_isSharedCheck_3613_;
goto v_resetjp_3601_;
}
else
{
lean_dec(v_a_3594_);
v___x_3602_ = lean_box(0);
v_isShared_3603_ = v_isSharedCheck_3613_;
goto v_resetjp_3601_;
}
v_resetjp_3601_:
{
lean_object* v___x_3604_; lean_object* v___x_3606_; 
v___x_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3600_);
lean_ctor_set(v___x_3604_, 1, v___x_3598_);
if (v_isShared_3603_ == 0)
{
lean_ctor_set_tag(v___x_3602_, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3604_);
v___x_3606_ = v___x_3602_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3612_; 
v_reuseFailAlloc_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3612_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3612_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v_snd_3574_);
if (v_isShared_3597_ == 0)
{
lean_ctor_set(v___x_3596_, 0, v___x_3608_);
v___x_3610_ = v___x_3596_;
goto v_reusejp_3609_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v___x_3608_);
v___x_3610_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3609_;
}
v_reusejp_3609_:
{
return v___x_3610_;
}
}
}
}
}
else
{
lean_object* v___x_3616_; 
lean_del_object(v___x_3596_);
lean_dec(v_a_3594_);
lean_del_object(v___x_3590_);
lean_dec(v_snd_3574_);
v___x_3616_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3580_ = v___x_3616_;
goto v___jp_3579_;
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_del_object(v___x_3590_);
lean_del_object(v___x_3576_);
lean_dec(v_snd_3574_);
lean_dec(v_mvarId_3562_);
v_a_3618_ = lean_ctor_get(v___x_3593_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3593_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3593_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3593_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v_a_3618_);
v___x_3623_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
return v___x_3623_;
}
}
}
}
}
v___jp_3579_:
{
lean_object* v___x_3582_; 
if (v_isShared_3577_ == 0)
{
lean_ctor_set(v___x_3576_, 1, v_a_3580_);
lean_ctor_set(v___x_3576_, 0, v___x_3578_);
v___x_3582_ = v___x_3576_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3586_; 
v_reuseFailAlloc_3586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3586_, 0, v___x_3578_);
lean_ctor_set(v_reuseFailAlloc_3586_, 1, v_a_3580_);
v___x_3582_ = v_reuseFailAlloc_3586_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
size_t v___x_3583_; size_t v___x_3584_; 
v___x_3583_ = ((size_t)1ULL);
v___x_3584_ = lean_usize_add(v_i_3565_, v___x_3583_);
v_i_3565_ = v___x_3584_;
v_b_3566_ = v___x_3582_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_mvarId_3629_, lean_object* v_as_3630_, lean_object* v_sz_3631_, lean_object* v_i_3632_, lean_object* v_b_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_, lean_object* v___y_3637_, lean_object* v___y_3638_){
_start:
{
size_t v_sz_boxed_3639_; size_t v_i_boxed_3640_; lean_object* v_res_3641_; 
v_sz_boxed_3639_ = lean_unbox_usize(v_sz_3631_);
lean_dec(v_sz_3631_);
v_i_boxed_3640_ = lean_unbox_usize(v_i_3632_);
lean_dec(v_i_3632_);
v_res_3641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3629_, v_as_3630_, v_sz_boxed_3639_, v_i_boxed_3640_, v_b_3633_, v___y_3634_, v___y_3635_, v___y_3636_, v___y_3637_);
lean_dec(v___y_3637_);
lean_dec_ref(v___y_3636_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec_ref(v_as_3630_);
return v_res_3641_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object* v_mvarId_3642_, lean_object* v_as_3643_, size_t v_sz_3644_, size_t v_i_3645_, lean_object* v_b_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_, lean_object* v___y_3649_, lean_object* v___y_3650_){
_start:
{
uint8_t v___x_3652_; 
v___x_3652_ = lean_usize_dec_lt(v_i_3645_, v_sz_3644_);
if (v___x_3652_ == 0)
{
lean_object* v___x_3653_; 
lean_dec(v_mvarId_3642_);
v___x_3653_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3653_, 0, v_b_3646_);
return v___x_3653_;
}
else
{
lean_object* v_snd_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3707_; 
v_snd_3654_ = lean_ctor_get(v_b_3646_, 1);
v_isSharedCheck_3707_ = !lean_is_exclusive(v_b_3646_);
if (v_isSharedCheck_3707_ == 0)
{
lean_object* v_unused_3708_; 
v_unused_3708_ = lean_ctor_get(v_b_3646_, 0);
lean_dec(v_unused_3708_);
v___x_3656_ = v_b_3646_;
v_isShared_3657_ = v_isSharedCheck_3707_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_snd_3654_);
lean_dec(v_b_3646_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3707_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3658_; lean_object* v_a_3660_; lean_object* v_a_3667_; 
v___x_3658_ = lean_box(0);
v_a_3667_ = lean_array_uget(v_as_3643_, v_i_3645_);
if (lean_obj_tag(v_a_3667_) == 0)
{
v_a_3660_ = v_snd_3654_;
goto v___jp_3659_;
}
else
{
lean_object* v_val_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3706_; 
v_val_3668_ = lean_ctor_get(v_a_3667_, 0);
v_isSharedCheck_3706_ = !lean_is_exclusive(v_a_3667_);
if (v_isSharedCheck_3706_ == 0)
{
v___x_3670_ = v_a_3667_;
v_isShared_3671_ = v_isSharedCheck_3706_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_val_3668_);
lean_dec(v_a_3667_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3706_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3672_; lean_object* v___x_3673_; 
v___x_3672_ = l_Lean_LocalDecl_fvarId(v_val_3668_);
lean_dec(v_val_3668_);
lean_inc(v_mvarId_3642_);
v___x_3673_ = l_Lean_Meta_subst_x3f(v_mvarId_3642_, v___x_3672_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
if (lean_obj_tag(v___x_3673_) == 0)
{
lean_object* v_a_3674_; lean_object* v___x_3676_; uint8_t v_isShared_3677_; uint8_t v_isSharedCheck_3697_; 
v_a_3674_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3697_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3697_ == 0)
{
v___x_3676_ = v___x_3673_;
v_isShared_3677_ = v_isSharedCheck_3697_;
goto v_resetjp_3675_;
}
else
{
lean_inc(v_a_3674_);
lean_dec(v___x_3673_);
v___x_3676_ = lean_box(0);
v_isShared_3677_ = v_isSharedCheck_3697_;
goto v_resetjp_3675_;
}
v_resetjp_3675_:
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_box(0);
if (lean_obj_tag(v_a_3674_) == 1)
{
lean_object* v___x_3680_; 
lean_del_object(v___x_3656_);
lean_dec(v_mvarId_3642_);
lean_inc_ref(v_a_3674_);
if (v_isShared_3671_ == 0)
{
lean_ctor_set(v___x_3670_, 0, v_a_3674_);
v___x_3680_ = v___x_3670_;
goto v_reusejp_3679_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3674_);
v___x_3680_ = v_reuseFailAlloc_3695_;
goto v_reusejp_3679_;
}
v_reusejp_3679_:
{
lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3693_; 
v_isSharedCheck_3693_ = !lean_is_exclusive(v_a_3674_);
if (v_isSharedCheck_3693_ == 0)
{
lean_object* v_unused_3694_; 
v_unused_3694_ = lean_ctor_get(v_a_3674_, 0);
lean_dec(v_unused_3694_);
v___x_3682_ = v_a_3674_;
v_isShared_3683_ = v_isSharedCheck_3693_;
goto v_resetjp_3681_;
}
else
{
lean_dec(v_a_3674_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3693_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3684_; lean_object* v___x_3686_; 
v___x_3684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3680_);
lean_ctor_set(v___x_3684_, 1, v___x_3678_);
if (v_isShared_3683_ == 0)
{
lean_ctor_set_tag(v___x_3682_, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3684_);
v___x_3686_ = v___x_3682_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3684_);
v___x_3686_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
lean_object* v___x_3687_; lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3687_, 0, v___x_3686_);
v___x_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3687_);
lean_ctor_set(v___x_3688_, 1, v_snd_3654_);
if (v_isShared_3677_ == 0)
{
lean_ctor_set(v___x_3676_, 0, v___x_3688_);
v___x_3690_ = v___x_3676_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v___x_3688_);
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
else
{
lean_object* v___x_3696_; 
lean_del_object(v___x_3676_);
lean_dec(v_a_3674_);
lean_del_object(v___x_3670_);
lean_dec(v_snd_3654_);
v___x_3696_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3660_ = v___x_3696_;
goto v___jp_3659_;
}
}
}
else
{
lean_object* v_a_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3705_; 
lean_del_object(v___x_3670_);
lean_del_object(v___x_3656_);
lean_dec(v_snd_3654_);
lean_dec(v_mvarId_3642_);
v_a_3698_ = lean_ctor_get(v___x_3673_, 0);
v_isSharedCheck_3705_ = !lean_is_exclusive(v___x_3673_);
if (v_isSharedCheck_3705_ == 0)
{
v___x_3700_ = v___x_3673_;
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_a_3698_);
lean_dec(v___x_3673_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3705_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v___x_3703_; 
if (v_isShared_3701_ == 0)
{
v___x_3703_ = v___x_3700_;
goto v_reusejp_3702_;
}
else
{
lean_object* v_reuseFailAlloc_3704_; 
v_reuseFailAlloc_3704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3704_, 0, v_a_3698_);
v___x_3703_ = v_reuseFailAlloc_3704_;
goto v_reusejp_3702_;
}
v_reusejp_3702_:
{
return v___x_3703_;
}
}
}
}
}
v___jp_3659_:
{
lean_object* v___x_3662_; 
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 1, v_a_3660_);
lean_ctor_set(v___x_3656_, 0, v___x_3658_);
v___x_3662_ = v___x_3656_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v_a_3660_);
v___x_3662_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
size_t v___x_3663_; size_t v___x_3664_; lean_object* v___x_3665_; 
v___x_3663_ = ((size_t)1ULL);
v___x_3664_ = lean_usize_add(v_i_3645_, v___x_3663_);
v___x_3665_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3642_, v_as_3643_, v_sz_3644_, v___x_3664_, v___x_3662_, v___y_3647_, v___y_3648_, v___y_3649_, v___y_3650_);
return v___x_3665_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_3709_, lean_object* v_as_3710_, lean_object* v_sz_3711_, lean_object* v_i_3712_, lean_object* v_b_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
size_t v_sz_boxed_3719_; size_t v_i_boxed_3720_; lean_object* v_res_3721_; 
v_sz_boxed_3719_ = lean_unbox_usize(v_sz_3711_);
lean_dec(v_sz_3711_);
v_i_boxed_3720_ = lean_unbox_usize(v_i_3712_);
lean_dec(v_i_3712_);
v_res_3721_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3709_, v_as_3710_, v_sz_boxed_3719_, v_i_boxed_3720_, v_b_3713_, v___y_3714_, v___y_3715_, v___y_3716_, v___y_3717_);
lean_dec(v___y_3717_);
lean_dec_ref(v___y_3716_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec_ref(v_as_3710_);
return v_res_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* v_init_3722_, lean_object* v_mvarId_3723_, lean_object* v_n_3724_, lean_object* v_b_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
if (lean_obj_tag(v_n_3724_) == 0)
{
lean_object* v_cs_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; size_t v_sz_3734_; size_t v___x_3735_; lean_object* v___x_3736_; 
v_cs_3731_ = lean_ctor_get(v_n_3724_, 0);
v___x_3732_ = lean_box(0);
v___x_3733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3733_, 0, v___x_3732_);
lean_ctor_set(v___x_3733_, 1, v_b_3725_);
v_sz_3734_ = lean_array_size(v_cs_3731_);
v___x_3735_ = ((size_t)0ULL);
v___x_3736_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3722_, v_mvarId_3723_, v_cs_3731_, v_sz_3734_, v___x_3735_, v___x_3733_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3736_) == 0)
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3751_; 
v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3751_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3751_ == 0)
{
v___x_3739_ = v___x_3736_;
v_isShared_3740_ = v_isSharedCheck_3751_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3736_);
v___x_3739_ = lean_box(0);
v_isShared_3740_ = v_isSharedCheck_3751_;
goto v_resetjp_3738_;
}
v_resetjp_3738_:
{
lean_object* v_fst_3741_; 
v_fst_3741_ = lean_ctor_get(v_a_3737_, 0);
if (lean_obj_tag(v_fst_3741_) == 0)
{
lean_object* v_snd_3742_; lean_object* v___x_3743_; lean_object* v___x_3745_; 
v_snd_3742_ = lean_ctor_get(v_a_3737_, 1);
lean_inc(v_snd_3742_);
lean_dec(v_a_3737_);
v___x_3743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3743_, 0, v_snd_3742_);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v___x_3743_);
v___x_3745_ = v___x_3739_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v___x_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
else
{
lean_object* v_val_3747_; lean_object* v___x_3749_; 
lean_inc_ref(v_fst_3741_);
lean_dec(v_a_3737_);
v_val_3747_ = lean_ctor_get(v_fst_3741_, 0);
lean_inc(v_val_3747_);
lean_dec_ref_known(v_fst_3741_, 1);
if (v_isShared_3740_ == 0)
{
lean_ctor_set(v___x_3739_, 0, v_val_3747_);
v___x_3749_ = v___x_3739_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v_val_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
v_a_3752_ = lean_ctor_get(v___x_3736_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3736_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3736_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3736_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3757_; 
if (v_isShared_3755_ == 0)
{
v___x_3757_ = v___x_3754_;
goto v_reusejp_3756_;
}
else
{
lean_object* v_reuseFailAlloc_3758_; 
v_reuseFailAlloc_3758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3758_, 0, v_a_3752_);
v___x_3757_ = v_reuseFailAlloc_3758_;
goto v_reusejp_3756_;
}
v_reusejp_3756_:
{
return v___x_3757_;
}
}
}
}
else
{
lean_object* v_vs_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; size_t v_sz_3763_; size_t v___x_3764_; lean_object* v___x_3765_; 
v_vs_3760_ = lean_ctor_get(v_n_3724_, 0);
v___x_3761_ = lean_box(0);
v___x_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v_b_3725_);
v_sz_3763_ = lean_array_size(v_vs_3760_);
v___x_3764_ = ((size_t)0ULL);
v___x_3765_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3723_, v_vs_3760_, v_sz_3763_, v___x_3764_, v___x_3762_, v___y_3726_, v___y_3727_, v___y_3728_, v___y_3729_);
if (lean_obj_tag(v___x_3765_) == 0)
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3780_; 
v_a_3766_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3768_ = v___x_3765_;
v_isShared_3769_ = v_isSharedCheck_3780_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3765_);
v___x_3768_ = lean_box(0);
v_isShared_3769_ = v_isSharedCheck_3780_;
goto v_resetjp_3767_;
}
v_resetjp_3767_:
{
lean_object* v_fst_3770_; 
v_fst_3770_ = lean_ctor_get(v_a_3766_, 0);
if (lean_obj_tag(v_fst_3770_) == 0)
{
lean_object* v_snd_3771_; lean_object* v___x_3772_; lean_object* v___x_3774_; 
v_snd_3771_ = lean_ctor_get(v_a_3766_, 1);
lean_inc(v_snd_3771_);
lean_dec(v_a_3766_);
v___x_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3772_, 0, v_snd_3771_);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v___x_3772_);
v___x_3774_ = v___x_3768_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v___x_3772_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
else
{
lean_object* v_val_3776_; lean_object* v___x_3778_; 
lean_inc_ref(v_fst_3770_);
lean_dec(v_a_3766_);
v_val_3776_ = lean_ctor_get(v_fst_3770_, 0);
lean_inc(v_val_3776_);
lean_dec_ref_known(v_fst_3770_, 1);
if (v_isShared_3769_ == 0)
{
lean_ctor_set(v___x_3768_, 0, v_val_3776_);
v___x_3778_ = v___x_3768_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_val_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
}
}
else
{
lean_object* v_a_3781_; lean_object* v___x_3783_; uint8_t v_isShared_3784_; uint8_t v_isSharedCheck_3788_; 
v_a_3781_ = lean_ctor_get(v___x_3765_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3765_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3765_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3765_);
v___x_3783_ = lean_box(0);
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
v_resetjp_3782_:
{
lean_object* v___x_3786_; 
if (v_isShared_3784_ == 0)
{
v___x_3786_ = v___x_3783_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v_a_3781_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_init_3789_, lean_object* v_mvarId_3790_, lean_object* v_as_3791_, size_t v_sz_3792_, size_t v_i_3793_, lean_object* v_b_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_){
_start:
{
uint8_t v___x_3800_; 
v___x_3800_ = lean_usize_dec_lt(v_i_3793_, v_sz_3792_);
if (v___x_3800_ == 0)
{
lean_object* v___x_3801_; 
lean_dec(v_mvarId_3790_);
v___x_3801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3801_, 0, v_b_3794_);
return v___x_3801_;
}
else
{
lean_object* v_snd_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3836_; 
v_snd_3802_ = lean_ctor_get(v_b_3794_, 1);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_b_3794_);
if (v_isSharedCheck_3836_ == 0)
{
lean_object* v_unused_3837_; 
v_unused_3837_ = lean_ctor_get(v_b_3794_, 0);
lean_dec(v_unused_3837_);
v___x_3804_ = v_b_3794_;
v_isShared_3805_ = v_isSharedCheck_3836_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_snd_3802_);
lean_dec(v_b_3794_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3836_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v_a_3806_; lean_object* v___x_3807_; 
v_a_3806_ = lean_array_uget_borrowed(v_as_3791_, v_i_3793_);
lean_inc(v_snd_3802_);
lean_inc(v_mvarId_3790_);
v___x_3807_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3789_, v_mvarId_3790_, v_a_3806_, v_snd_3802_, v___y_3795_, v___y_3796_, v___y_3797_, v___y_3798_);
if (lean_obj_tag(v___x_3807_) == 0)
{
lean_object* v_a_3808_; lean_object* v___x_3810_; uint8_t v_isShared_3811_; uint8_t v_isSharedCheck_3827_; 
v_a_3808_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3810_ = v___x_3807_;
v_isShared_3811_ = v_isSharedCheck_3827_;
goto v_resetjp_3809_;
}
else
{
lean_inc(v_a_3808_);
lean_dec(v___x_3807_);
v___x_3810_ = lean_box(0);
v_isShared_3811_ = v_isSharedCheck_3827_;
goto v_resetjp_3809_;
}
v_resetjp_3809_:
{
if (lean_obj_tag(v_a_3808_) == 0)
{
lean_object* v___x_3812_; lean_object* v___x_3814_; 
lean_dec(v_mvarId_3790_);
v___x_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3812_, 0, v_a_3808_);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3812_);
v___x_3814_ = v___x_3804_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v___x_3812_);
lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_snd_3802_);
v___x_3814_ = v_reuseFailAlloc_3818_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
lean_object* v___x_3816_; 
if (v_isShared_3811_ == 0)
{
lean_ctor_set(v___x_3810_, 0, v___x_3814_);
v___x_3816_ = v___x_3810_;
goto v_reusejp_3815_;
}
else
{
lean_object* v_reuseFailAlloc_3817_; 
v_reuseFailAlloc_3817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3817_, 0, v___x_3814_);
v___x_3816_ = v_reuseFailAlloc_3817_;
goto v_reusejp_3815_;
}
v_reusejp_3815_:
{
return v___x_3816_;
}
}
}
else
{
lean_object* v_a_3819_; lean_object* v___x_3820_; lean_object* v___x_3822_; 
lean_del_object(v___x_3810_);
lean_dec(v_snd_3802_);
v_a_3819_ = lean_ctor_get(v_a_3808_, 0);
lean_inc(v_a_3819_);
lean_dec_ref_known(v_a_3808_, 1);
v___x_3820_ = lean_box(0);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 1, v_a_3819_);
lean_ctor_set(v___x_3804_, 0, v___x_3820_);
v___x_3822_ = v___x_3804_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v___x_3820_);
lean_ctor_set(v_reuseFailAlloc_3826_, 1, v_a_3819_);
v___x_3822_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
size_t v___x_3823_; size_t v___x_3824_; 
v___x_3823_ = ((size_t)1ULL);
v___x_3824_ = lean_usize_add(v_i_3793_, v___x_3823_);
v_i_3793_ = v___x_3824_;
v_b_3794_ = v___x_3822_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_del_object(v___x_3804_);
lean_dec(v_snd_3802_);
lean_dec(v_mvarId_3790_);
v_a_3828_ = lean_ctor_get(v___x_3807_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3807_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3807_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3807_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3838_, lean_object* v_mvarId_3839_, lean_object* v_as_3840_, lean_object* v_sz_3841_, lean_object* v_i_3842_, lean_object* v_b_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_, lean_object* v___y_3847_, lean_object* v___y_3848_){
_start:
{
size_t v_sz_boxed_3849_; size_t v_i_boxed_3850_; lean_object* v_res_3851_; 
v_sz_boxed_3849_ = lean_unbox_usize(v_sz_3841_);
lean_dec(v_sz_3841_);
v_i_boxed_3850_ = lean_unbox_usize(v_i_3842_);
lean_dec(v_i_3842_);
v_res_3851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3838_, v_mvarId_3839_, v_as_3840_, v_sz_boxed_3849_, v_i_boxed_3850_, v_b_3843_, v___y_3844_, v___y_3845_, v___y_3846_, v___y_3847_);
lean_dec(v___y_3847_);
lean_dec_ref(v___y_3846_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec_ref(v_as_3840_);
lean_dec_ref(v_init_3838_);
return v_res_3851_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_init_3852_, lean_object* v_mvarId_3853_, lean_object* v_n_3854_, lean_object* v_b_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_){
_start:
{
lean_object* v_res_3861_; 
v_res_3861_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3852_, v_mvarId_3853_, v_n_3854_, v_b_3855_, v___y_3856_, v___y_3857_, v___y_3858_, v___y_3859_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec_ref(v_n_3854_);
lean_dec_ref(v_init_3852_);
return v_res_3861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3865_, lean_object* v_as_3866_, size_t v_sz_3867_, size_t v_i_3868_, lean_object* v_b_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_){
_start:
{
uint8_t v___x_3875_; 
v___x_3875_ = lean_usize_dec_lt(v_i_3868_, v_sz_3867_);
if (v___x_3875_ == 0)
{
lean_object* v___x_3876_; 
lean_dec(v_mvarId_3865_);
v___x_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3876_, 0, v_b_3869_);
return v___x_3876_;
}
else
{
lean_object* v_snd_3877_; lean_object* v___x_3879_; uint8_t v_isShared_3880_; uint8_t v_isSharedCheck_3929_; 
v_snd_3877_ = lean_ctor_get(v_b_3869_, 1);
v_isSharedCheck_3929_ = !lean_is_exclusive(v_b_3869_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; 
v_unused_3930_ = lean_ctor_get(v_b_3869_, 0);
lean_dec(v_unused_3930_);
v___x_3879_ = v_b_3869_;
v_isShared_3880_ = v_isSharedCheck_3929_;
goto v_resetjp_3878_;
}
else
{
lean_inc(v_snd_3877_);
lean_dec(v_b_3869_);
v___x_3879_ = lean_box(0);
v_isShared_3880_ = v_isSharedCheck_3929_;
goto v_resetjp_3878_;
}
v_resetjp_3878_:
{
lean_object* v___x_3881_; lean_object* v_a_3883_; lean_object* v_a_3890_; 
v___x_3881_ = lean_box(0);
v_a_3890_ = lean_array_uget(v_as_3866_, v_i_3868_);
if (lean_obj_tag(v_a_3890_) == 0)
{
v_a_3883_ = v_snd_3877_;
goto v___jp_3882_;
}
else
{
lean_object* v_val_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3928_; 
v_val_3891_ = lean_ctor_get(v_a_3890_, 0);
v_isSharedCheck_3928_ = !lean_is_exclusive(v_a_3890_);
if (v_isSharedCheck_3928_ == 0)
{
v___x_3893_ = v_a_3890_;
v_isShared_3894_ = v_isSharedCheck_3928_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_val_3891_);
lean_dec(v_a_3890_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3928_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3895_; lean_object* v___x_3896_; 
v___x_3895_ = l_Lean_LocalDecl_fvarId(v_val_3891_);
lean_dec(v_val_3891_);
lean_inc(v_mvarId_3865_);
v___x_3896_ = l_Lean_Meta_subst_x3f(v_mvarId_3865_, v___x_3895_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
if (lean_obj_tag(v___x_3896_) == 0)
{
lean_object* v_a_3897_; lean_object* v___x_3899_; uint8_t v_isShared_3900_; uint8_t v_isSharedCheck_3919_; 
v_a_3897_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3899_ = v___x_3896_;
v_isShared_3900_ = v_isSharedCheck_3919_;
goto v_resetjp_3898_;
}
else
{
lean_inc(v_a_3897_);
lean_dec(v___x_3896_);
v___x_3899_ = lean_box(0);
v_isShared_3900_ = v_isSharedCheck_3919_;
goto v_resetjp_3898_;
}
v_resetjp_3898_:
{
lean_object* v___x_3901_; 
v___x_3901_ = lean_box(0);
if (lean_obj_tag(v_a_3897_) == 1)
{
lean_object* v___x_3903_; 
lean_del_object(v___x_3879_);
lean_dec(v_mvarId_3865_);
lean_inc_ref(v_a_3897_);
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 0, v_a_3897_);
v___x_3903_ = v___x_3893_;
goto v_reusejp_3902_;
}
else
{
lean_object* v_reuseFailAlloc_3917_; 
v_reuseFailAlloc_3917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3917_, 0, v_a_3897_);
v___x_3903_ = v_reuseFailAlloc_3917_;
goto v_reusejp_3902_;
}
v_reusejp_3902_:
{
lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_3915_; 
v_isSharedCheck_3915_ = !lean_is_exclusive(v_a_3897_);
if (v_isSharedCheck_3915_ == 0)
{
lean_object* v_unused_3916_; 
v_unused_3916_ = lean_ctor_get(v_a_3897_, 0);
lean_dec(v_unused_3916_);
v___x_3905_ = v_a_3897_;
v_isShared_3906_ = v_isSharedCheck_3915_;
goto v_resetjp_3904_;
}
else
{
lean_dec(v_a_3897_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_3915_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3907_; lean_object* v___x_3909_; 
v___x_3907_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3903_);
lean_ctor_set(v___x_3907_, 1, v___x_3901_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3907_);
v___x_3909_ = v___x_3905_;
goto v_reusejp_3908_;
}
else
{
lean_object* v_reuseFailAlloc_3914_; 
v_reuseFailAlloc_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3914_, 0, v___x_3907_);
v___x_3909_ = v_reuseFailAlloc_3914_;
goto v_reusejp_3908_;
}
v_reusejp_3908_:
{
lean_object* v___x_3910_; lean_object* v___x_3912_; 
v___x_3910_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3910_, 0, v___x_3909_);
lean_ctor_set(v___x_3910_, 1, v_snd_3877_);
if (v_isShared_3900_ == 0)
{
lean_ctor_set(v___x_3899_, 0, v___x_3910_);
v___x_3912_ = v___x_3899_;
goto v_reusejp_3911_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v___x_3910_);
v___x_3912_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3911_;
}
v_reusejp_3911_:
{
return v___x_3912_;
}
}
}
}
}
else
{
lean_object* v___x_3918_; 
lean_del_object(v___x_3899_);
lean_dec(v_a_3897_);
lean_del_object(v___x_3893_);
lean_dec(v_snd_3877_);
v___x_3918_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3883_ = v___x_3918_;
goto v___jp_3882_;
}
}
}
else
{
lean_object* v_a_3920_; lean_object* v___x_3922_; uint8_t v_isShared_3923_; uint8_t v_isSharedCheck_3927_; 
lean_del_object(v___x_3893_);
lean_del_object(v___x_3879_);
lean_dec(v_snd_3877_);
lean_dec(v_mvarId_3865_);
v_a_3920_ = lean_ctor_get(v___x_3896_, 0);
v_isSharedCheck_3927_ = !lean_is_exclusive(v___x_3896_);
if (v_isSharedCheck_3927_ == 0)
{
v___x_3922_ = v___x_3896_;
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
else
{
lean_inc(v_a_3920_);
lean_dec(v___x_3896_);
v___x_3922_ = lean_box(0);
v_isShared_3923_ = v_isSharedCheck_3927_;
goto v_resetjp_3921_;
}
v_resetjp_3921_:
{
lean_object* v___x_3925_; 
if (v_isShared_3923_ == 0)
{
v___x_3925_ = v___x_3922_;
goto v_reusejp_3924_;
}
else
{
lean_object* v_reuseFailAlloc_3926_; 
v_reuseFailAlloc_3926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3926_, 0, v_a_3920_);
v___x_3925_ = v_reuseFailAlloc_3926_;
goto v_reusejp_3924_;
}
v_reusejp_3924_:
{
return v___x_3925_;
}
}
}
}
}
v___jp_3882_:
{
lean_object* v___x_3885_; 
if (v_isShared_3880_ == 0)
{
lean_ctor_set(v___x_3879_, 1, v_a_3883_);
lean_ctor_set(v___x_3879_, 0, v___x_3881_);
v___x_3885_ = v___x_3879_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3889_; 
v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3881_);
lean_ctor_set(v_reuseFailAlloc_3889_, 1, v_a_3883_);
v___x_3885_ = v_reuseFailAlloc_3889_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
size_t v___x_3886_; size_t v___x_3887_; 
v___x_3886_ = ((size_t)1ULL);
v___x_3887_ = lean_usize_add(v_i_3868_, v___x_3886_);
v_i_3868_ = v___x_3887_;
v_b_3869_ = v___x_3885_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3931_, lean_object* v_as_3932_, lean_object* v_sz_3933_, lean_object* v_i_3934_, lean_object* v_b_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_){
_start:
{
size_t v_sz_boxed_3941_; size_t v_i_boxed_3942_; lean_object* v_res_3943_; 
v_sz_boxed_3941_ = lean_unbox_usize(v_sz_3933_);
lean_dec(v_sz_3933_);
v_i_boxed_3942_ = lean_unbox_usize(v_i_3934_);
lean_dec(v_i_3934_);
v_res_3943_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3931_, v_as_3932_, v_sz_boxed_3941_, v_i_boxed_3942_, v_b_3935_, v___y_3936_, v___y_3937_, v___y_3938_, v___y_3939_);
lean_dec(v___y_3939_);
lean_dec_ref(v___y_3938_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec_ref(v_as_3932_);
return v_res_3943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_3944_, lean_object* v_as_3945_, size_t v_sz_3946_, size_t v_i_3947_, lean_object* v_b_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_){
_start:
{
uint8_t v___x_3954_; 
v___x_3954_ = lean_usize_dec_lt(v_i_3947_, v_sz_3946_);
if (v___x_3954_ == 0)
{
lean_object* v___x_3955_; 
lean_dec(v_mvarId_3944_);
v___x_3955_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3955_, 0, v_b_3948_);
return v___x_3955_;
}
else
{
lean_object* v_snd_3956_; lean_object* v___x_3958_; uint8_t v_isShared_3959_; uint8_t v_isSharedCheck_4008_; 
v_snd_3956_ = lean_ctor_get(v_b_3948_, 1);
v_isSharedCheck_4008_ = !lean_is_exclusive(v_b_3948_);
if (v_isSharedCheck_4008_ == 0)
{
lean_object* v_unused_4009_; 
v_unused_4009_ = lean_ctor_get(v_b_3948_, 0);
lean_dec(v_unused_4009_);
v___x_3958_ = v_b_3948_;
v_isShared_3959_ = v_isSharedCheck_4008_;
goto v_resetjp_3957_;
}
else
{
lean_inc(v_snd_3956_);
lean_dec(v_b_3948_);
v___x_3958_ = lean_box(0);
v_isShared_3959_ = v_isSharedCheck_4008_;
goto v_resetjp_3957_;
}
v_resetjp_3957_:
{
lean_object* v___x_3960_; lean_object* v_a_3962_; lean_object* v_a_3969_; 
v___x_3960_ = lean_box(0);
v_a_3969_ = lean_array_uget(v_as_3945_, v_i_3947_);
if (lean_obj_tag(v_a_3969_) == 0)
{
v_a_3962_ = v_snd_3956_;
goto v___jp_3961_;
}
else
{
lean_object* v_val_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_4007_; 
v_val_3970_ = lean_ctor_get(v_a_3969_, 0);
v_isSharedCheck_4007_ = !lean_is_exclusive(v_a_3969_);
if (v_isSharedCheck_4007_ == 0)
{
v___x_3972_ = v_a_3969_;
v_isShared_3973_ = v_isSharedCheck_4007_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_val_3970_);
lean_dec(v_a_3969_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_4007_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3975_; 
v___x_3974_ = l_Lean_LocalDecl_fvarId(v_val_3970_);
lean_dec(v_val_3970_);
lean_inc(v_mvarId_3944_);
v___x_3975_ = l_Lean_Meta_subst_x3f(v_mvarId_3944_, v___x_3974_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
if (lean_obj_tag(v___x_3975_) == 0)
{
lean_object* v_a_3976_; lean_object* v___x_3978_; uint8_t v_isShared_3979_; uint8_t v_isSharedCheck_3998_; 
v_a_3976_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_3998_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_3998_ == 0)
{
v___x_3978_ = v___x_3975_;
v_isShared_3979_ = v_isSharedCheck_3998_;
goto v_resetjp_3977_;
}
else
{
lean_inc(v_a_3976_);
lean_dec(v___x_3975_);
v___x_3978_ = lean_box(0);
v_isShared_3979_ = v_isSharedCheck_3998_;
goto v_resetjp_3977_;
}
v_resetjp_3977_:
{
lean_object* v___x_3980_; 
v___x_3980_ = lean_box(0);
if (lean_obj_tag(v_a_3976_) == 1)
{
lean_object* v___x_3982_; 
lean_del_object(v___x_3958_);
lean_dec(v_mvarId_3944_);
lean_inc_ref(v_a_3976_);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 0, v_a_3976_);
v___x_3982_ = v___x_3972_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_3996_; 
v_reuseFailAlloc_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3996_, 0, v_a_3976_);
v___x_3982_ = v_reuseFailAlloc_3996_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3994_; 
v_isSharedCheck_3994_ = !lean_is_exclusive(v_a_3976_);
if (v_isSharedCheck_3994_ == 0)
{
lean_object* v_unused_3995_; 
v_unused_3995_ = lean_ctor_get(v_a_3976_, 0);
lean_dec(v_unused_3995_);
v___x_3984_ = v_a_3976_;
v_isShared_3985_ = v_isSharedCheck_3994_;
goto v_resetjp_3983_;
}
else
{
lean_dec(v_a_3976_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3994_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3986_; lean_object* v___x_3988_; 
v___x_3986_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3986_, 0, v___x_3982_);
lean_ctor_set(v___x_3986_, 1, v___x_3980_);
if (v_isShared_3985_ == 0)
{
lean_ctor_set(v___x_3984_, 0, v___x_3986_);
v___x_3988_ = v___x_3984_;
goto v_reusejp_3987_;
}
else
{
lean_object* v_reuseFailAlloc_3993_; 
v_reuseFailAlloc_3993_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3993_, 0, v___x_3986_);
v___x_3988_ = v_reuseFailAlloc_3993_;
goto v_reusejp_3987_;
}
v_reusejp_3987_:
{
lean_object* v___x_3989_; lean_object* v___x_3991_; 
v___x_3989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3989_, 0, v___x_3988_);
lean_ctor_set(v___x_3989_, 1, v_snd_3956_);
if (v_isShared_3979_ == 0)
{
lean_ctor_set(v___x_3978_, 0, v___x_3989_);
v___x_3991_ = v___x_3978_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v___x_3989_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
}
else
{
lean_object* v___x_3997_; 
lean_del_object(v___x_3978_);
lean_dec(v_a_3976_);
lean_del_object(v___x_3972_);
lean_dec(v_snd_3956_);
v___x_3997_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3962_ = v___x_3997_;
goto v___jp_3961_;
}
}
}
else
{
lean_object* v_a_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4006_; 
lean_del_object(v___x_3972_);
lean_del_object(v___x_3958_);
lean_dec(v_snd_3956_);
lean_dec(v_mvarId_3944_);
v_a_3999_ = lean_ctor_get(v___x_3975_, 0);
v_isSharedCheck_4006_ = !lean_is_exclusive(v___x_3975_);
if (v_isSharedCheck_4006_ == 0)
{
v___x_4001_ = v___x_3975_;
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_a_3999_);
lean_dec(v___x_3975_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4006_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4004_; 
if (v_isShared_4002_ == 0)
{
v___x_4004_ = v___x_4001_;
goto v_reusejp_4003_;
}
else
{
lean_object* v_reuseFailAlloc_4005_; 
v_reuseFailAlloc_4005_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4005_, 0, v_a_3999_);
v___x_4004_ = v_reuseFailAlloc_4005_;
goto v_reusejp_4003_;
}
v_reusejp_4003_:
{
return v___x_4004_;
}
}
}
}
}
v___jp_3961_:
{
lean_object* v___x_3964_; 
if (v_isShared_3959_ == 0)
{
lean_ctor_set(v___x_3958_, 1, v_a_3962_);
lean_ctor_set(v___x_3958_, 0, v___x_3960_);
v___x_3964_ = v___x_3958_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3968_; 
v_reuseFailAlloc_3968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3968_, 0, v___x_3960_);
lean_ctor_set(v_reuseFailAlloc_3968_, 1, v_a_3962_);
v___x_3964_ = v_reuseFailAlloc_3968_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
size_t v___x_3965_; size_t v___x_3966_; lean_object* v___x_3967_; 
v___x_3965_ = ((size_t)1ULL);
v___x_3966_ = lean_usize_add(v_i_3947_, v___x_3965_);
v___x_3967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3944_, v_as_3945_, v_sz_3946_, v___x_3966_, v___x_3964_, v___y_3949_, v___y_3950_, v___y_3951_, v___y_3952_);
return v___x_3967_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_4010_, lean_object* v_as_4011_, lean_object* v_sz_4012_, lean_object* v_i_4013_, lean_object* v_b_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
size_t v_sz_boxed_4020_; size_t v_i_boxed_4021_; lean_object* v_res_4022_; 
v_sz_boxed_4020_ = lean_unbox_usize(v_sz_4012_);
lean_dec(v_sz_4012_);
v_i_boxed_4021_ = lean_unbox_usize(v_i_4013_);
lean_dec(v_i_4013_);
v_res_4022_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4010_, v_as_4011_, v_sz_boxed_4020_, v_i_boxed_4021_, v_b_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec_ref(v_as_4011_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4023_, lean_object* v_t_4024_, lean_object* v_init_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_){
_start:
{
lean_object* v_root_4031_; lean_object* v_tail_4032_; lean_object* v___x_4033_; 
v_root_4031_ = lean_ctor_get(v_t_4024_, 0);
v_tail_4032_ = lean_ctor_get(v_t_4024_, 1);
lean_inc(v_mvarId_4023_);
lean_inc_ref(v_init_4025_);
v___x_4033_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_4025_, v_mvarId_4023_, v_root_4031_, v_init_4025_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
lean_dec_ref(v_init_4025_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4036_; uint8_t v_isShared_4037_; uint8_t v_isSharedCheck_4070_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4036_ = v___x_4033_;
v_isShared_4037_ = v_isSharedCheck_4070_;
goto v_resetjp_4035_;
}
else
{
lean_inc(v_a_4034_);
lean_dec(v___x_4033_);
v___x_4036_ = lean_box(0);
v_isShared_4037_ = v_isSharedCheck_4070_;
goto v_resetjp_4035_;
}
v_resetjp_4035_:
{
if (lean_obj_tag(v_a_4034_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4040_; 
lean_dec(v_mvarId_4023_);
v_a_4038_ = lean_ctor_get(v_a_4034_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v_a_4034_, 1);
if (v_isShared_4037_ == 0)
{
lean_ctor_set(v___x_4036_, 0, v_a_4038_);
v___x_4040_ = v___x_4036_;
goto v_reusejp_4039_;
}
else
{
lean_object* v_reuseFailAlloc_4041_; 
v_reuseFailAlloc_4041_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4041_, 0, v_a_4038_);
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
lean_object* v_a_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; size_t v_sz_4045_; size_t v___x_4046_; lean_object* v___x_4047_; 
lean_del_object(v___x_4036_);
v_a_4042_ = lean_ctor_get(v_a_4034_, 0);
lean_inc(v_a_4042_);
lean_dec_ref_known(v_a_4034_, 1);
v___x_4043_ = lean_box(0);
v___x_4044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4044_, 0, v___x_4043_);
lean_ctor_set(v___x_4044_, 1, v_a_4042_);
v_sz_4045_ = lean_array_size(v_tail_4032_);
v___x_4046_ = ((size_t)0ULL);
v___x_4047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4023_, v_tail_4032_, v_sz_4045_, v___x_4046_, v___x_4044_, v___y_4026_, v___y_4027_, v___y_4028_, v___y_4029_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4061_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4050_ = v___x_4047_;
v_isShared_4051_ = v_isSharedCheck_4061_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4047_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4061_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v_fst_4052_; 
v_fst_4052_ = lean_ctor_get(v_a_4048_, 0);
if (lean_obj_tag(v_fst_4052_) == 0)
{
lean_object* v_snd_4053_; lean_object* v___x_4055_; 
v_snd_4053_ = lean_ctor_get(v_a_4048_, 1);
lean_inc(v_snd_4053_);
lean_dec(v_a_4048_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v_snd_4053_);
v___x_4055_ = v___x_4050_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_snd_4053_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
else
{
lean_object* v_val_4057_; lean_object* v___x_4059_; 
lean_inc_ref(v_fst_4052_);
lean_dec(v_a_4048_);
v_val_4057_ = lean_ctor_get(v_fst_4052_, 0);
lean_inc(v_val_4057_);
lean_dec_ref_known(v_fst_4052_, 1);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v_val_4057_);
v___x_4059_ = v___x_4050_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_val_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
v_a_4062_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4047_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4047_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v___x_4067_; 
if (v_isShared_4065_ == 0)
{
v___x_4067_ = v___x_4064_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4068_; 
v_reuseFailAlloc_4068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4068_, 0, v_a_4062_);
v___x_4067_ = v_reuseFailAlloc_4068_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
return v___x_4067_;
}
}
}
}
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_dec(v_mvarId_4023_);
v_a_4071_ = lean_ctor_get(v___x_4033_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4033_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4033_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4033_);
v___x_4073_ = lean_box(0);
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
v_resetjp_4072_:
{
lean_object* v___x_4076_; 
if (v_isShared_4074_ == 0)
{
v___x_4076_ = v___x_4073_;
goto v_reusejp_4075_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_a_4071_);
v___x_4076_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4075_;
}
v_reusejp_4075_:
{
return v___x_4076_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4079_, lean_object* v_t_4080_, lean_object* v_init_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_, lean_object* v___y_4085_, lean_object* v___y_4086_){
_start:
{
lean_object* v_res_4087_; 
v_res_4087_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4079_, v_t_4080_, v_init_4081_, v___y_4082_, v___y_4083_, v___y_4084_, v___y_4085_);
lean_dec(v___y_4085_);
lean_dec_ref(v___y_4084_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec_ref(v_t_4080_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v_lctx_4097_; lean_object* v_decls_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_lctx_4097_ = lean_ctor_get(v___y_4092_, 2);
v_decls_4098_ = lean_ctor_get(v_lctx_4097_, 1);
v___x_4099_ = lean_box(0);
v___x_4100_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4101_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4091_, v_decls_4098_, v___x_4100_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4114_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4114_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4114_ == 0)
{
v___x_4104_ = v___x_4101_;
v_isShared_4105_ = v_isSharedCheck_4114_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4101_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4114_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v_fst_4106_; 
v_fst_4106_ = lean_ctor_get(v_a_4102_, 0);
lean_inc(v_fst_4106_);
lean_dec(v_a_4102_);
if (lean_obj_tag(v_fst_4106_) == 0)
{
lean_object* v___x_4108_; 
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 0, v___x_4099_);
v___x_4108_ = v___x_4104_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4099_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
else
{
lean_object* v_val_4110_; lean_object* v___x_4112_; 
v_val_4110_ = lean_ctor_get(v_fst_4106_, 0);
lean_inc(v_val_4110_);
lean_dec_ref_known(v_fst_4106_, 1);
if (v_isShared_4105_ == 0)
{
lean_ctor_set(v___x_4104_, 0, v_val_4110_);
v___x_4112_ = v___x_4104_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v_val_4110_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
}
}
else
{
lean_object* v_a_4115_; lean_object* v___x_4117_; uint8_t v_isShared_4118_; uint8_t v_isSharedCheck_4122_; 
v_a_4115_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4122_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4122_ == 0)
{
v___x_4117_ = v___x_4101_;
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
else
{
lean_inc(v_a_4115_);
lean_dec(v___x_4101_);
v___x_4117_ = lean_box(0);
v_isShared_4118_ = v_isSharedCheck_4122_;
goto v_resetjp_4116_;
}
v_resetjp_4116_:
{
lean_object* v___x_4120_; 
if (v_isShared_4118_ == 0)
{
v___x_4120_ = v___x_4117_;
goto v_reusejp_4119_;
}
else
{
lean_object* v_reuseFailAlloc_4121_; 
v_reuseFailAlloc_4121_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4121_, 0, v_a_4115_);
v___x_4120_ = v_reuseFailAlloc_4121_;
goto v_reusejp_4119_;
}
v_reusejp_4119_:
{
return v___x_4120_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_, lean_object* v___y_4128_){
_start:
{
lean_object* v_res_4129_; 
v_res_4129_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4123_, v___y_4124_, v___y_4125_, v___y_4126_, v___y_4127_);
lean_dec(v___y_4127_);
lean_dec_ref(v___y_4126_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
return v_res_4129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_, lean_object* v_a_4133_, lean_object* v_a_4134_){
_start:
{
lean_object* v___f_4136_; lean_object* v___x_4137_; 
lean_inc(v_mvarId_4130_);
v___f_4136_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4136_, 0, v_mvarId_4130_);
v___x_4137_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_4130_, v___f_4136_, v_a_4131_, v_a_4132_, v_a_4133_, v_a_4134_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_){
_start:
{
lean_object* v_res_4144_; 
v_res_4144_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4138_, v_a_4139_, v_a_4140_, v_a_4141_, v_a_4142_);
lean_dec(v_a_4142_);
lean_dec_ref(v_a_4141_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
return v_res_4144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_, lean_object* v_a_4149_){
_start:
{
lean_object* v___x_4151_; 
lean_inc(v_mvarId_4145_);
v___x_4151_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4145_, v_a_4146_, v_a_4147_, v_a_4148_, v_a_4149_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4161_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4154_ = v___x_4151_;
v_isShared_4155_ = v_isSharedCheck_4161_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4151_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4161_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
if (lean_obj_tag(v_a_4152_) == 1)
{
lean_object* v_val_4156_; 
lean_del_object(v___x_4154_);
lean_dec(v_mvarId_4145_);
v_val_4156_ = lean_ctor_get(v_a_4152_, 0);
lean_inc(v_val_4156_);
lean_dec_ref_known(v_a_4152_, 1);
v_mvarId_4145_ = v_val_4156_;
goto _start;
}
else
{
lean_object* v___x_4159_; 
lean_dec(v_a_4152_);
if (v_isShared_4155_ == 0)
{
lean_ctor_set(v___x_4154_, 0, v_mvarId_4145_);
v___x_4159_ = v___x_4154_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_mvarId_4145_);
v___x_4159_ = v_reuseFailAlloc_4160_;
goto v_reusejp_4158_;
}
v_reusejp_4158_:
{
return v___x_4159_;
}
}
}
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
lean_dec(v_mvarId_4145_);
v_a_4162_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4151_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4151_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_, lean_object* v_a_4174_, lean_object* v_a_4175_){
_start:
{
lean_object* v_res_4176_; 
v_res_4176_ = l_Lean_Meta_substVars(v_mvarId_4170_, v_a_4171_, v_a_4172_, v_a_4173_, v_a_4174_);
lean_dec(v_a_4174_);
lean_dec_ref(v_a_4173_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
return v_res_4176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4239_; uint8_t v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v___x_4239_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_4240_ = 0;
v___x_4241_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4242_ = l_Lean_registerTraceClass(v___x_4239_, v___x_4240_, v___x_4241_);
return v___x_4242_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4243_){
_start:
{
lean_object* v_res_4244_; 
v_res_4244_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4244_;
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
