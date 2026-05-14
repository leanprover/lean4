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
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__2;
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
lean_object* v___f_51_; lean_object* v___x_28778__overap_52_; lean_object* v___x_53_; 
v___f_51_ = ((lean_object*)(l_panic___at___00Lean_Meta_substCore_spec__1___closed__0));
v___x_28778__overap_52_ = lean_panic_fn_borrowed(v___f_51_, v_msg_45_);
lean_inc(v___y_49_);
lean_inc_ref(v___y_48_);
lean_inc(v___y_47_);
lean_inc_ref(v___y_46_);
v___x_53_ = lean_apply_5(v___x_28778__overap_52_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, lean_box(0));
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
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_74_ = lean_box(0);
v___x_75_ = lean_unsigned_to_nat(16u);
v___x_76_ = lean_mk_array(v___x_75_, v___x_74_);
return v___x_76_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_77_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1);
v___x_78_ = lean_unsigned_to_nat(0u);
v___x_79_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_78_);
lean_ctor_set(v___x_79_, 1, v___x_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(lean_object* v_e_80_, lean_object* v_fvarId_81_, lean_object* v___y_82_){
_start:
{
lean_object* v___x_84_; uint8_t v_fst_86_; lean_object* v_mctx_87_; lean_object* v___y_105_; lean_object* v_mctx_110_; lean_object* v___f_111_; lean_object* v___f_112_; lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_84_ = lean_st_ref_get(v___y_82_);
v_mctx_110_ = lean_ctor_get(v___x_84_, 0);
lean_inc_ref_n(v_mctx_110_, 2);
lean_dec(v___x_84_);
v___f_111_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__0));
v___f_112_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_112_, 0, v_fvarId_81_);
v___x_113_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2);
v___x_114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_114_, 0, v___x_113_);
lean_ctor_set(v___x_114_, 1, v_mctx_110_);
v___x_115_ = l_Lean_Expr_hasFVar(v_e_80_);
if (v___x_115_ == 0)
{
uint8_t v___x_116_; 
v___x_116_ = l_Lean_Expr_hasMVar(v_e_80_);
if (v___x_116_ == 0)
{
lean_dec_ref(v___x_114_);
lean_dec_ref(v___f_112_);
lean_dec_ref(v_e_80_);
v_fst_86_ = v___x_116_;
v_mctx_87_ = v_mctx_110_;
goto v___jp_85_;
}
else
{
lean_object* v___x_117_; 
lean_dec_ref(v_mctx_110_);
v___x_117_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_112_, v___f_111_, v_e_80_, v___x_114_);
v___y_105_ = v___x_117_;
goto v___jp_104_;
}
}
else
{
lean_object* v___x_118_; 
lean_dec_ref(v_mctx_110_);
v___x_118_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_112_, v___f_111_, v_e_80_, v___x_114_);
v___y_105_ = v___x_118_;
goto v___jp_104_;
}
v___jp_85_:
{
lean_object* v___x_88_; lean_object* v_cache_89_; lean_object* v_zetaDeltaFVarIds_90_; lean_object* v_postponed_91_; lean_object* v_diag_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_102_; 
v___x_88_ = lean_st_ref_take(v___y_82_);
v_cache_89_ = lean_ctor_get(v___x_88_, 1);
v_zetaDeltaFVarIds_90_ = lean_ctor_get(v___x_88_, 2);
v_postponed_91_ = lean_ctor_get(v___x_88_, 3);
v_diag_92_ = lean_ctor_get(v___x_88_, 4);
v_isSharedCheck_102_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_102_ == 0)
{
lean_object* v_unused_103_; 
v_unused_103_ = lean_ctor_get(v___x_88_, 0);
lean_dec(v_unused_103_);
v___x_94_ = v___x_88_;
v_isShared_95_ = v_isSharedCheck_102_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_diag_92_);
lean_inc(v_postponed_91_);
lean_inc(v_zetaDeltaFVarIds_90_);
lean_inc(v_cache_89_);
lean_dec(v___x_88_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_102_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_97_; 
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v_mctx_87_);
v___x_97_ = v___x_94_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_mctx_87_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_cache_89_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_zetaDeltaFVarIds_90_);
lean_ctor_set(v_reuseFailAlloc_101_, 3, v_postponed_91_);
lean_ctor_set(v_reuseFailAlloc_101_, 4, v_diag_92_);
v___x_97_ = v_reuseFailAlloc_101_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v___x_98_ = lean_st_ref_set(v___y_82_, v___x_97_);
v___x_99_ = lean_box(v_fst_86_);
v___x_100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
return v___x_100_;
}
}
}
v___jp_104_:
{
lean_object* v_snd_106_; lean_object* v_fst_107_; lean_object* v_mctx_108_; uint8_t v___x_109_; 
v_snd_106_ = lean_ctor_get(v___y_105_, 1);
lean_inc(v_snd_106_);
v_fst_107_ = lean_ctor_get(v___y_105_, 0);
lean_inc(v_fst_107_);
lean_dec_ref(v___y_105_);
v_mctx_108_ = lean_ctor_get(v_snd_106_, 1);
lean_inc_ref(v_mctx_108_);
lean_dec(v_snd_106_);
v___x_109_ = lean_unbox(v_fst_107_);
lean_dec(v_fst_107_);
v_fst_86_ = v___x_109_;
v_mctx_87_ = v_mctx_108_;
goto v___jp_85_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___boxed(lean_object* v_e_119_, lean_object* v_fvarId_120_, lean_object* v___y_121_, lean_object* v___y_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_e_119_, v_fvarId_120_, v___y_121_);
lean_dec(v___y_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4(lean_object* v_e_124_, lean_object* v_fvarId_125_, lean_object* v___y_126_, lean_object* v___y_127_, lean_object* v___y_128_, lean_object* v___y_129_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_e_124_, v_fvarId_125_, v___y_127_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___boxed(lean_object* v_e_132_, lean_object* v_fvarId_133_, lean_object* v___y_134_, lean_object* v___y_135_, lean_object* v___y_136_, lean_object* v___y_137_, lean_object* v___y_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4(v_e_132_, v_fvarId_133_, v___y_134_, v___y_135_, v___y_136_, v___y_137_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0(lean_object* v___x_193_, lean_object* v___y_194_, lean_object* v___y_195_, lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_options_199_; uint8_t v_hasTrace_200_; 
v_options_199_ = lean_ctor_get(v___y_196_, 2);
v_hasTrace_200_ = lean_ctor_get_uint8(v_options_199_, sizeof(void*)*1);
if (v_hasTrace_200_ == 0)
{
lean_object* v___x_201_; lean_object* v___x_202_; 
lean_dec(v___x_193_);
v___x_201_ = lean_box(v_hasTrace_200_);
v___x_202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
return v___x_202_;
}
else
{
lean_object* v_inheritedTraceOptions_203_; lean_object* v___x_204_; lean_object* v___x_205_; uint8_t v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; 
v_inheritedTraceOptions_203_ = lean_ctor_get(v___y_196_, 13);
v___x_204_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
v___x_205_ = l_Lean_Name_append(v___x_204_, v___x_193_);
v___x_206_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_203_, v_options_199_, v___x_205_);
lean_dec(v___x_205_);
v___x_207_ = lean_box(v___x_206_);
v___x_208_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object* v___x_209_, lean_object* v___y_210_, lean_object* v___y_211_, lean_object* v___y_212_, lean_object* v___y_213_, lean_object* v___y_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l_Lean_Meta_substCore___lam__0(v___x_209_, v___y_210_, v___y_211_, v___y_212_, v___y_213_);
lean_dec(v___y_213_);
lean_dec_ref(v___y_212_);
lean_dec(v___y_211_);
lean_dec_ref(v___y_210_);
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object* v_type_216_, lean_object* v___x_217_, lean_object* v___x_218_, lean_object* v___x_219_, uint8_t v___x_220_, uint8_t v___x_221_, lean_object* v_hAux_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_){
_start:
{
lean_object* v___x_228_; 
lean_inc_ref(v_hAux_222_);
v___x_228_ = l_Lean_Meta_mkEqSymm(v_hAux_222_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; uint8_t v___x_234_; lean_object* v___x_235_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref(v___x_228_);
v___x_230_ = l_Lean_Expr_replaceFVar(v_type_216_, v___x_217_, v_a_229_);
lean_dec(v_a_229_);
v___x_231_ = lean_mk_empty_array_with_capacity(v___x_218_);
v___x_232_ = lean_array_push(v___x_231_, v___x_219_);
v___x_233_ = lean_array_push(v___x_232_, v_hAux_222_);
v___x_234_ = 1;
v___x_235_ = l_Lean_Meta_mkLambdaFVars(v___x_233_, v___x_230_, v___x_220_, v___x_221_, v___x_220_, v___x_221_, v___x_234_, v___y_223_, v___y_224_, v___y_225_, v___y_226_);
lean_dec_ref(v___x_233_);
return v___x_235_;
}
else
{
lean_dec_ref(v_hAux_222_);
lean_dec_ref(v___x_219_);
lean_dec_ref(v___x_217_);
return v___x_228_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object* v_type_236_, lean_object* v___x_237_, lean_object* v___x_238_, lean_object* v___x_239_, lean_object* v___x_240_, lean_object* v___x_241_, lean_object* v_hAux_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_, lean_object* v___y_246_, lean_object* v___y_247_){
_start:
{
uint8_t v___x_33188__boxed_248_; uint8_t v___x_33189__boxed_249_; lean_object* v_res_250_; 
v___x_33188__boxed_248_ = lean_unbox(v___x_240_);
v___x_33189__boxed_249_ = lean_unbox(v___x_241_);
v_res_250_ = l_Lean_Meta_substCore___lam__1(v_type_236_, v___x_237_, v___x_238_, v___x_239_, v___x_33188__boxed_248_, v___x_33189__boxed_249_, v_hAux_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
lean_dec(v___y_246_);
lean_dec_ref(v___y_245_);
lean_dec(v___y_244_);
lean_dec_ref(v___y_243_);
lean_dec(v___x_238_);
lean_dec_ref(v_type_236_);
return v_res_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0(lean_object* v_k_251_, lean_object* v_b_252_, lean_object* v___y_253_, lean_object* v___y_254_, lean_object* v___y_255_, lean_object* v___y_256_){
_start:
{
lean_object* v___x_258_; 
lean_inc(v___y_256_);
lean_inc_ref(v___y_255_);
lean_inc(v___y_254_);
lean_inc_ref(v___y_253_);
v___x_258_ = lean_apply_6(v_k_251_, v_b_252_, v___y_253_, v___y_254_, v___y_255_, v___y_256_, lean_box(0));
return v___x_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_259_, lean_object* v_b_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_){
_start:
{
lean_object* v_res_266_; 
v_res_266_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0(v_k_259_, v_b_260_, v___y_261_, v___y_262_, v___y_263_, v___y_264_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
lean_dec(v___y_262_);
lean_dec_ref(v___y_261_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(lean_object* v_name_267_, uint8_t v_bi_268_, lean_object* v_type_269_, lean_object* v_k_270_, uint8_t v_kind_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
lean_object* v___f_277_; lean_object* v___x_278_; 
v___f_277_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_277_, 0, v_k_270_);
v___x_278_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_267_, v_bi_268_, v_type_269_, v___f_277_, v_kind_271_, v___y_272_, v___y_273_, v___y_274_, v___y_275_);
if (lean_obj_tag(v___x_278_) == 0)
{
lean_object* v_a_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_286_; 
v_a_279_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_286_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_286_ == 0)
{
v___x_281_ = v___x_278_;
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_a_279_);
lean_dec(v___x_278_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_286_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_284_; 
if (v_isShared_282_ == 0)
{
v___x_284_ = v___x_281_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
else
{
lean_object* v_a_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_294_; 
v_a_287_ = lean_ctor_get(v___x_278_, 0);
v_isSharedCheck_294_ = !lean_is_exclusive(v___x_278_);
if (v_isSharedCheck_294_ == 0)
{
v___x_289_ = v___x_278_;
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_a_287_);
lean_dec(v___x_278_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_294_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_292_; 
if (v_isShared_290_ == 0)
{
v___x_292_ = v___x_289_;
goto v_reusejp_291_;
}
else
{
lean_object* v_reuseFailAlloc_293_; 
v_reuseFailAlloc_293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_293_, 0, v_a_287_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___boxed(lean_object* v_name_295_, lean_object* v_bi_296_, lean_object* v_type_297_, lean_object* v_k_298_, lean_object* v_kind_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_){
_start:
{
uint8_t v_bi_boxed_305_; uint8_t v_kind_boxed_306_; lean_object* v_res_307_; 
v_bi_boxed_305_ = lean_unbox(v_bi_296_);
v_kind_boxed_306_ = lean_unbox(v_kind_299_);
v_res_307_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_295_, v_bi_boxed_305_, v_type_297_, v_k_298_, v_kind_boxed_306_, v___y_300_, v___y_301_, v___y_302_, v___y_303_);
lean_dec(v___y_303_);
lean_dec_ref(v___y_302_);
lean_dec(v___y_301_);
lean_dec_ref(v___y_300_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(lean_object* v_name_308_, lean_object* v_type_309_, lean_object* v_k_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_){
_start:
{
uint8_t v___x_316_; uint8_t v___x_317_; lean_object* v___x_318_; 
v___x_316_ = 0;
v___x_317_ = 0;
v___x_318_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_308_, v___x_316_, v_type_309_, v_k_310_, v___x_317_, v___y_311_, v___y_312_, v___y_313_, v___y_314_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg___boxed(lean_object* v_name_319_, lean_object* v_type_320_, lean_object* v_k_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_){
_start:
{
lean_object* v_res_327_; 
v_res_327_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v_name_319_, v_type_320_, v_k_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_327_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(lean_object* v_fst_328_, lean_object* v_fst_329_, lean_object* v_n_330_, lean_object* v_i_331_, lean_object* v_a_332_){
_start:
{
lean_object* v_zero_334_; uint8_t v_isZero_335_; 
v_zero_334_ = lean_unsigned_to_nat(0u);
v_isZero_335_ = lean_nat_dec_eq(v_i_331_, v_zero_334_);
if (v_isZero_335_ == 1)
{
lean_object* v___x_336_; 
lean_dec(v_i_331_);
v___x_336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_336_, 0, v_a_332_);
return v___x_336_;
}
else
{
lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v_one_339_; lean_object* v_n_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_337_ = lean_unsigned_to_nat(2u);
v___x_338_ = lean_box(0);
v_one_339_ = lean_unsigned_to_nat(1u);
v_n_340_ = lean_nat_sub(v_i_331_, v_one_339_);
lean_dec(v_i_331_);
v___x_341_ = lean_nat_sub(v_n_330_, v_n_340_);
v___x_342_ = lean_nat_sub(v___x_341_, v_one_339_);
lean_dec(v___x_341_);
v___x_343_ = lean_nat_add(v___x_342_, v___x_337_);
v___x_344_ = lean_array_get_borrowed(v___x_338_, v_fst_328_, v___x_343_);
lean_dec(v___x_343_);
v___x_345_ = lean_array_fget_borrowed(v_fst_329_, v___x_342_);
lean_dec(v___x_342_);
lean_inc(v___x_345_);
v___x_346_ = l_Lean_mkFVar(v___x_345_);
lean_inc(v___x_344_);
v___x_347_ = l_Lean_Meta_FVarSubst_insert(v_a_332_, v___x_344_, v___x_346_);
v_i_331_ = v_n_340_;
v_a_332_ = v___x_347_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg___boxed(lean_object* v_fst_349_, lean_object* v_fst_350_, lean_object* v_n_351_, lean_object* v_i_352_, lean_object* v_a_353_, lean_object* v___y_354_){
_start:
{
lean_object* v_res_355_; 
v_res_355_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_349_, v_fst_350_, v_n_351_, v_i_352_, v_a_353_);
lean_dec(v_n_351_);
lean_dec_ref(v_fst_350_);
lean_dec_ref(v_fst_349_);
return v_res_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(lean_object* v_msgData_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_){
_start:
{
lean_object* v___x_362_; lean_object* v_env_363_; lean_object* v___x_364_; lean_object* v_mctx_365_; lean_object* v_lctx_366_; lean_object* v_options_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; 
v___x_362_ = lean_st_ref_get(v___y_360_);
v_env_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc_ref(v_env_363_);
lean_dec(v___x_362_);
v___x_364_ = lean_st_ref_get(v___y_358_);
v_mctx_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc_ref(v_mctx_365_);
lean_dec(v___x_364_);
v_lctx_366_ = lean_ctor_get(v___y_357_, 2);
v_options_367_ = lean_ctor_get(v___y_359_, 2);
lean_inc_ref(v_options_367_);
lean_inc_ref(v_lctx_366_);
v___x_368_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_368_, 0, v_env_363_);
lean_ctor_set(v___x_368_, 1, v_mctx_365_);
lean_ctor_set(v___x_368_, 2, v_lctx_366_);
lean_ctor_set(v___x_368_, 3, v_options_367_);
v___x_369_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set(v___x_369_, 1, v_msgData_356_);
v___x_370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
return v___x_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3___boxed(lean_object* v_msgData_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_){
_start:
{
lean_object* v_res_377_; 
v_res_377_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msgData_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
return v_res_377_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0(void){
_start:
{
lean_object* v___x_378_; double v___x_379_; 
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = lean_float_of_nat(v___x_378_);
return v___x_379_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(lean_object* v_cls_383_, lean_object* v_msg_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v_ref_390_; lean_object* v___x_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_437_; 
v_ref_390_ = lean_ctor_get(v___y_387_, 5);
v___x_391_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msg_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_437_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_437_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_437_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v_traceState_397_; lean_object* v_env_398_; lean_object* v_nextMacroScope_399_; lean_object* v_ngen_400_; lean_object* v_auxDeclNGen_401_; lean_object* v_cache_402_; lean_object* v_messages_403_; lean_object* v_infoState_404_; lean_object* v_snapshotTasks_405_; lean_object* v_newDecls_406_; lean_object* v___x_408_; uint8_t v_isShared_409_; uint8_t v_isSharedCheck_436_; 
v___x_396_ = lean_st_ref_take(v___y_388_);
v_traceState_397_ = lean_ctor_get(v___x_396_, 4);
v_env_398_ = lean_ctor_get(v___x_396_, 0);
v_nextMacroScope_399_ = lean_ctor_get(v___x_396_, 1);
v_ngen_400_ = lean_ctor_get(v___x_396_, 2);
v_auxDeclNGen_401_ = lean_ctor_get(v___x_396_, 3);
v_cache_402_ = lean_ctor_get(v___x_396_, 5);
v_messages_403_ = lean_ctor_get(v___x_396_, 6);
v_infoState_404_ = lean_ctor_get(v___x_396_, 7);
v_snapshotTasks_405_ = lean_ctor_get(v___x_396_, 8);
v_newDecls_406_ = lean_ctor_get(v___x_396_, 9);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_436_ == 0)
{
v___x_408_ = v___x_396_;
v_isShared_409_ = v_isSharedCheck_436_;
goto v_resetjp_407_;
}
else
{
lean_inc(v_newDecls_406_);
lean_inc(v_snapshotTasks_405_);
lean_inc(v_infoState_404_);
lean_inc(v_messages_403_);
lean_inc(v_cache_402_);
lean_inc(v_traceState_397_);
lean_inc(v_auxDeclNGen_401_);
lean_inc(v_ngen_400_);
lean_inc(v_nextMacroScope_399_);
lean_inc(v_env_398_);
lean_dec(v___x_396_);
v___x_408_ = lean_box(0);
v_isShared_409_ = v_isSharedCheck_436_;
goto v_resetjp_407_;
}
v_resetjp_407_:
{
uint64_t v_tid_410_; lean_object* v_traces_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_435_; 
v_tid_410_ = lean_ctor_get_uint64(v_traceState_397_, sizeof(void*)*1);
v_traces_411_ = lean_ctor_get(v_traceState_397_, 0);
v_isSharedCheck_435_ = !lean_is_exclusive(v_traceState_397_);
if (v_isSharedCheck_435_ == 0)
{
v___x_413_ = v_traceState_397_;
v_isShared_414_ = v_isSharedCheck_435_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_traces_411_);
lean_dec(v_traceState_397_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_435_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___x_415_; double v___x_416_; uint8_t v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_425_; 
v___x_415_ = lean_box(0);
v___x_416_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0);
v___x_417_ = 0;
v___x_418_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__1));
v___x_419_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_419_, 0, v_cls_383_);
lean_ctor_set(v___x_419_, 1, v___x_415_);
lean_ctor_set(v___x_419_, 2, v___x_418_);
lean_ctor_set_float(v___x_419_, sizeof(void*)*3, v___x_416_);
lean_ctor_set_float(v___x_419_, sizeof(void*)*3 + 8, v___x_416_);
lean_ctor_set_uint8(v___x_419_, sizeof(void*)*3 + 16, v___x_417_);
v___x_420_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__2));
v___x_421_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_421_, 0, v___x_419_);
lean_ctor_set(v___x_421_, 1, v_a_392_);
lean_ctor_set(v___x_421_, 2, v___x_420_);
lean_inc(v_ref_390_);
v___x_422_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_422_, 0, v_ref_390_);
lean_ctor_set(v___x_422_, 1, v___x_421_);
v___x_423_ = l_Lean_PersistentArray_push___redArg(v_traces_411_, v___x_422_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 0, v___x_423_);
v___x_425_ = v___x_413_;
goto v_reusejp_424_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_423_);
lean_ctor_set_uint64(v_reuseFailAlloc_434_, sizeof(void*)*1, v_tid_410_);
v___x_425_ = v_reuseFailAlloc_434_;
goto v_reusejp_424_;
}
v_reusejp_424_:
{
lean_object* v___x_427_; 
if (v_isShared_409_ == 0)
{
lean_ctor_set(v___x_408_, 4, v___x_425_);
v___x_427_ = v___x_408_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v_env_398_);
lean_ctor_set(v_reuseFailAlloc_433_, 1, v_nextMacroScope_399_);
lean_ctor_set(v_reuseFailAlloc_433_, 2, v_ngen_400_);
lean_ctor_set(v_reuseFailAlloc_433_, 3, v_auxDeclNGen_401_);
lean_ctor_set(v_reuseFailAlloc_433_, 4, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_433_, 5, v_cache_402_);
lean_ctor_set(v_reuseFailAlloc_433_, 6, v_messages_403_);
lean_ctor_set(v_reuseFailAlloc_433_, 7, v_infoState_404_);
lean_ctor_set(v_reuseFailAlloc_433_, 8, v_snapshotTasks_405_);
lean_ctor_set(v_reuseFailAlloc_433_, 9, v_newDecls_406_);
v___x_427_ = v_reuseFailAlloc_433_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_431_; 
v___x_428_ = lean_st_ref_set(v___y_388_, v___x_427_);
v___x_429_ = lean_box(0);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_429_);
v___x_431_ = v___x_394_;
goto v_reusejp_430_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v___x_429_);
v___x_431_ = v_reuseFailAlloc_432_;
goto v_reusejp_430_;
}
v_reusejp_430_:
{
return v___x_431_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___boxed(lean_object* v_cls_438_, lean_object* v_msg_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v_cls_438_, v_msg_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
lean_dec(v___y_441_);
lean_dec_ref(v___y_440_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v_ks_450_; lean_object* v_vs_451_; lean_object* v___x_453_; uint8_t v_isShared_454_; uint8_t v_isSharedCheck_475_; 
v_ks_450_ = lean_ctor_get(v_x_446_, 0);
v_vs_451_ = lean_ctor_get(v_x_446_, 1);
v_isSharedCheck_475_ = !lean_is_exclusive(v_x_446_);
if (v_isSharedCheck_475_ == 0)
{
v___x_453_ = v_x_446_;
v_isShared_454_ = v_isSharedCheck_475_;
goto v_resetjp_452_;
}
else
{
lean_inc(v_vs_451_);
lean_inc(v_ks_450_);
lean_dec(v_x_446_);
v___x_453_ = lean_box(0);
v_isShared_454_ = v_isSharedCheck_475_;
goto v_resetjp_452_;
}
v_resetjp_452_:
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_array_get_size(v_ks_450_);
v___x_456_ = lean_nat_dec_lt(v_x_447_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_460_; 
lean_dec(v_x_447_);
v___x_457_ = lean_array_push(v_ks_450_, v_x_448_);
v___x_458_ = lean_array_push(v_vs_451_, v_x_449_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v___x_458_);
lean_ctor_set(v___x_453_, 0, v___x_457_);
v___x_460_ = v___x_453_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v___x_457_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
else
{
lean_object* v_k_x27_462_; uint8_t v___x_463_; 
v_k_x27_462_ = lean_array_fget_borrowed(v_ks_450_, v_x_447_);
v___x_463_ = l_Lean_instBEqMVarId_beq(v_x_448_, v_k_x27_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_465_; 
if (v_isShared_454_ == 0)
{
v___x_465_ = v___x_453_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_ks_450_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_vs_451_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_466_; lean_object* v___x_467_; 
v___x_466_ = lean_unsigned_to_nat(1u);
v___x_467_ = lean_nat_add(v_x_447_, v___x_466_);
lean_dec(v_x_447_);
v_x_446_ = v___x_465_;
v_x_447_ = v___x_467_;
goto _start;
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_470_ = lean_array_fset(v_ks_450_, v_x_447_, v_x_448_);
v___x_471_ = lean_array_fset(v_vs_451_, v_x_447_, v_x_449_);
lean_dec(v_x_447_);
if (v_isShared_454_ == 0)
{
lean_ctor_set(v___x_453_, 1, v___x_471_);
lean_ctor_set(v___x_453_, 0, v___x_470_);
v___x_473_ = v___x_453_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_470_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v___x_471_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(lean_object* v_n_476_, lean_object* v_k_477_, lean_object* v_v_478_){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; 
v___x_479_ = lean_unsigned_to_nat(0u);
v___x_480_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(v_n_476_, v___x_479_, v_k_477_, v_v_478_);
return v___x_480_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_481_; size_t v___x_482_; size_t v___x_483_; 
v___x_481_ = ((size_t)5ULL);
v___x_482_ = ((size_t)1ULL);
v___x_483_ = lean_usize_shift_left(v___x_482_, v___x_481_);
return v___x_483_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_484_; size_t v___x_485_; size_t v___x_486_; 
v___x_484_ = ((size_t)1ULL);
v___x_485_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0);
v___x_486_ = lean_usize_sub(v___x_485_, v___x_484_);
return v___x_486_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(lean_object* v_x_488_, size_t v_x_489_, size_t v_x_490_, lean_object* v_x_491_, lean_object* v_x_492_){
_start:
{
if (lean_obj_tag(v_x_488_) == 0)
{
lean_object* v_es_493_; size_t v___x_494_; size_t v___x_495_; size_t v___x_496_; size_t v___x_497_; lean_object* v_j_498_; lean_object* v___x_499_; uint8_t v___x_500_; 
v_es_493_ = lean_ctor_get(v_x_488_, 0);
v___x_494_ = ((size_t)5ULL);
v___x_495_ = ((size_t)1ULL);
v___x_496_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1);
v___x_497_ = lean_usize_land(v_x_489_, v___x_496_);
v_j_498_ = lean_usize_to_nat(v___x_497_);
v___x_499_ = lean_array_get_size(v_es_493_);
v___x_500_ = lean_nat_dec_lt(v_j_498_, v___x_499_);
if (v___x_500_ == 0)
{
lean_dec(v_j_498_);
lean_dec(v_x_492_);
lean_dec(v_x_491_);
return v_x_488_;
}
else
{
lean_object* v___x_502_; uint8_t v_isShared_503_; uint8_t v_isSharedCheck_537_; 
lean_inc_ref(v_es_493_);
v_isSharedCheck_537_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v_x_488_, 0);
lean_dec(v_unused_538_);
v___x_502_ = v_x_488_;
v_isShared_503_ = v_isSharedCheck_537_;
goto v_resetjp_501_;
}
else
{
lean_dec(v_x_488_);
v___x_502_ = lean_box(0);
v_isShared_503_ = v_isSharedCheck_537_;
goto v_resetjp_501_;
}
v_resetjp_501_:
{
lean_object* v_v_504_; lean_object* v___x_505_; lean_object* v_xs_x27_506_; lean_object* v___y_508_; 
v_v_504_ = lean_array_fget(v_es_493_, v_j_498_);
v___x_505_ = lean_box(0);
v_xs_x27_506_ = lean_array_fset(v_es_493_, v_j_498_, v___x_505_);
switch(lean_obj_tag(v_v_504_))
{
case 0:
{
lean_object* v_key_513_; lean_object* v_val_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_524_; 
v_key_513_ = lean_ctor_get(v_v_504_, 0);
v_val_514_ = lean_ctor_get(v_v_504_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_v_504_);
if (v_isSharedCheck_524_ == 0)
{
v___x_516_ = v_v_504_;
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_val_514_);
lean_inc(v_key_513_);
lean_dec(v_v_504_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_524_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
uint8_t v___x_518_; 
v___x_518_ = l_Lean_instBEqMVarId_beq(v_x_491_, v_key_513_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; lean_object* v___x_520_; 
lean_del_object(v___x_516_);
v___x_519_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_513_, v_val_514_, v_x_491_, v_x_492_);
v___x_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_520_, 0, v___x_519_);
v___y_508_ = v___x_520_;
goto v___jp_507_;
}
else
{
lean_object* v___x_522_; 
lean_dec(v_val_514_);
lean_dec(v_key_513_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 1, v_x_492_);
lean_ctor_set(v___x_516_, 0, v_x_491_);
v___x_522_ = v___x_516_;
goto v_reusejp_521_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_x_491_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_x_492_);
v___x_522_ = v_reuseFailAlloc_523_;
goto v_reusejp_521_;
}
v_reusejp_521_:
{
v___y_508_ = v___x_522_;
goto v___jp_507_;
}
}
}
}
case 1:
{
lean_object* v_node_525_; lean_object* v___x_527_; uint8_t v_isShared_528_; uint8_t v_isSharedCheck_535_; 
v_node_525_ = lean_ctor_get(v_v_504_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v_v_504_);
if (v_isSharedCheck_535_ == 0)
{
v___x_527_ = v_v_504_;
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
else
{
lean_inc(v_node_525_);
lean_dec(v_v_504_);
v___x_527_ = lean_box(0);
v_isShared_528_ = v_isSharedCheck_535_;
goto v_resetjp_526_;
}
v_resetjp_526_:
{
size_t v___x_529_; size_t v___x_530_; lean_object* v___x_531_; lean_object* v___x_533_; 
v___x_529_ = lean_usize_shift_right(v_x_489_, v___x_494_);
v___x_530_ = lean_usize_add(v_x_490_, v___x_495_);
v___x_531_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_node_525_, v___x_529_, v___x_530_, v_x_491_, v_x_492_);
if (v_isShared_528_ == 0)
{
lean_ctor_set(v___x_527_, 0, v___x_531_);
v___x_533_ = v___x_527_;
goto v_reusejp_532_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v___x_531_);
v___x_533_ = v_reuseFailAlloc_534_;
goto v_reusejp_532_;
}
v_reusejp_532_:
{
v___y_508_ = v___x_533_;
goto v___jp_507_;
}
}
}
default: 
{
lean_object* v___x_536_; 
v___x_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_536_, 0, v_x_491_);
lean_ctor_set(v___x_536_, 1, v_x_492_);
v___y_508_ = v___x_536_;
goto v___jp_507_;
}
}
v___jp_507_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_array_fset(v_xs_x27_506_, v_j_498_, v___y_508_);
lean_dec(v_j_498_);
if (v_isShared_503_ == 0)
{
lean_ctor_set(v___x_502_, 0, v___x_509_);
v___x_511_ = v___x_502_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
}
else
{
lean_object* v_ks_539_; lean_object* v_vs_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_560_; 
v_ks_539_ = lean_ctor_get(v_x_488_, 0);
v_vs_540_ = lean_ctor_get(v_x_488_, 1);
v_isSharedCheck_560_ = !lean_is_exclusive(v_x_488_);
if (v_isSharedCheck_560_ == 0)
{
v___x_542_ = v_x_488_;
v_isShared_543_ = v_isSharedCheck_560_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_vs_540_);
lean_inc(v_ks_539_);
lean_dec(v_x_488_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_560_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_ks_539_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_vs_540_);
v___x_545_ = v_reuseFailAlloc_559_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v_newNode_546_; uint8_t v___y_548_; size_t v___x_554_; uint8_t v___x_555_; 
v_newNode_546_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v___x_545_, v_x_491_, v_x_492_);
v___x_554_ = ((size_t)7ULL);
v___x_555_ = lean_usize_dec_le(v___x_554_, v_x_490_);
if (v___x_555_ == 0)
{
lean_object* v___x_556_; lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_556_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_546_);
v___x_557_ = lean_unsigned_to_nat(4u);
v___x_558_ = lean_nat_dec_lt(v___x_556_, v___x_557_);
lean_dec(v___x_556_);
v___y_548_ = v___x_558_;
goto v___jp_547_;
}
else
{
v___y_548_ = v___x_555_;
goto v___jp_547_;
}
v___jp_547_:
{
if (v___y_548_ == 0)
{
lean_object* v_ks_549_; lean_object* v_vs_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; 
v_ks_549_ = lean_ctor_get(v_newNode_546_, 0);
lean_inc_ref(v_ks_549_);
v_vs_550_ = lean_ctor_get(v_newNode_546_, 1);
lean_inc_ref(v_vs_550_);
lean_dec_ref(v_newNode_546_);
v___x_551_ = lean_unsigned_to_nat(0u);
v___x_552_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__2);
v___x_553_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_x_490_, v_ks_549_, v_vs_550_, v___x_551_, v___x_552_);
lean_dec_ref(v_vs_550_);
lean_dec_ref(v_ks_549_);
return v___x_553_;
}
else
{
return v_newNode_546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(size_t v_depth_561_, lean_object* v_keys_562_, lean_object* v_vals_563_, lean_object* v_i_564_, lean_object* v_entries_565_){
_start:
{
lean_object* v___x_566_; uint8_t v___x_567_; 
v___x_566_ = lean_array_get_size(v_keys_562_);
v___x_567_ = lean_nat_dec_lt(v_i_564_, v___x_566_);
if (v___x_567_ == 0)
{
lean_dec(v_i_564_);
return v_entries_565_;
}
else
{
lean_object* v_k_568_; lean_object* v_v_569_; uint64_t v___x_570_; size_t v_h_571_; size_t v___x_572_; lean_object* v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v_h_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v_k_568_ = lean_array_fget_borrowed(v_keys_562_, v_i_564_);
v_v_569_ = lean_array_fget_borrowed(v_vals_563_, v_i_564_);
v___x_570_ = l_Lean_instHashableMVarId_hash(v_k_568_);
v_h_571_ = lean_uint64_to_usize(v___x_570_);
v___x_572_ = ((size_t)5ULL);
v___x_573_ = lean_unsigned_to_nat(1u);
v___x_574_ = ((size_t)1ULL);
v___x_575_ = lean_usize_sub(v_depth_561_, v___x_574_);
v___x_576_ = lean_usize_mul(v___x_572_, v___x_575_);
v_h_577_ = lean_usize_shift_right(v_h_571_, v___x_576_);
v___x_578_ = lean_nat_add(v_i_564_, v___x_573_);
lean_dec(v_i_564_);
lean_inc(v_v_569_);
lean_inc(v_k_568_);
v___x_579_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_entries_565_, v_h_577_, v_depth_561_, v_k_568_, v_v_569_);
v_i_564_ = v___x_578_;
v_entries_565_ = v___x_579_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_depth_581_, lean_object* v_keys_582_, lean_object* v_vals_583_, lean_object* v_i_584_, lean_object* v_entries_585_){
_start:
{
size_t v_depth_boxed_586_; lean_object* v_res_587_; 
v_depth_boxed_586_ = lean_unbox_usize(v_depth_581_);
lean_dec(v_depth_581_);
v_res_587_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_boxed_586_, v_keys_582_, v_vals_583_, v_i_584_, v_entries_585_);
lean_dec_ref(v_vals_583_);
lean_dec_ref(v_keys_582_);
return v_res_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_, lean_object* v_x_592_){
_start:
{
size_t v_x_33572__boxed_593_; size_t v_x_33573__boxed_594_; lean_object* v_res_595_; 
v_x_33572__boxed_593_ = lean_unbox_usize(v_x_589_);
lean_dec(v_x_589_);
v_x_33573__boxed_594_ = lean_unbox_usize(v_x_590_);
lean_dec(v_x_590_);
v_res_595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_588_, v_x_33572__boxed_593_, v_x_33573__boxed_594_, v_x_591_, v_x_592_);
return v_res_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(lean_object* v_x_596_, lean_object* v_x_597_, lean_object* v_x_598_){
_start:
{
uint64_t v___x_599_; size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
v___x_599_ = l_Lean_instHashableMVarId_hash(v_x_597_);
v___x_600_ = lean_uint64_to_usize(v___x_599_);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_596_, v___x_600_, v___x_601_, v_x_597_, v_x_598_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(lean_object* v_mvarId_603_, lean_object* v_val_604_, lean_object* v___y_605_){
_start:
{
lean_object* v___x_607_; lean_object* v_mctx_608_; lean_object* v_cache_609_; lean_object* v_zetaDeltaFVarIds_610_; lean_object* v_postponed_611_; lean_object* v_diag_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_640_; 
v___x_607_ = lean_st_ref_take(v___y_605_);
v_mctx_608_ = lean_ctor_get(v___x_607_, 0);
v_cache_609_ = lean_ctor_get(v___x_607_, 1);
v_zetaDeltaFVarIds_610_ = lean_ctor_get(v___x_607_, 2);
v_postponed_611_ = lean_ctor_get(v___x_607_, 3);
v_diag_612_ = lean_ctor_get(v___x_607_, 4);
v_isSharedCheck_640_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_640_ == 0)
{
v___x_614_ = v___x_607_;
v_isShared_615_ = v_isSharedCheck_640_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_diag_612_);
lean_inc(v_postponed_611_);
lean_inc(v_zetaDeltaFVarIds_610_);
lean_inc(v_cache_609_);
lean_inc(v_mctx_608_);
lean_dec(v___x_607_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_640_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v_depth_616_; lean_object* v_levelAssignDepth_617_; lean_object* v_lmvarCounter_618_; lean_object* v_mvarCounter_619_; lean_object* v_lDecls_620_; lean_object* v_decls_621_; lean_object* v_userNames_622_; lean_object* v_lAssignment_623_; lean_object* v_eAssignment_624_; lean_object* v_dAssignment_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_639_; 
v_depth_616_ = lean_ctor_get(v_mctx_608_, 0);
v_levelAssignDepth_617_ = lean_ctor_get(v_mctx_608_, 1);
v_lmvarCounter_618_ = lean_ctor_get(v_mctx_608_, 2);
v_mvarCounter_619_ = lean_ctor_get(v_mctx_608_, 3);
v_lDecls_620_ = lean_ctor_get(v_mctx_608_, 4);
v_decls_621_ = lean_ctor_get(v_mctx_608_, 5);
v_userNames_622_ = lean_ctor_get(v_mctx_608_, 6);
v_lAssignment_623_ = lean_ctor_get(v_mctx_608_, 7);
v_eAssignment_624_ = lean_ctor_get(v_mctx_608_, 8);
v_dAssignment_625_ = lean_ctor_get(v_mctx_608_, 9);
v_isSharedCheck_639_ = !lean_is_exclusive(v_mctx_608_);
if (v_isSharedCheck_639_ == 0)
{
v___x_627_ = v_mctx_608_;
v_isShared_628_ = v_isSharedCheck_639_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_dAssignment_625_);
lean_inc(v_eAssignment_624_);
lean_inc(v_lAssignment_623_);
lean_inc(v_userNames_622_);
lean_inc(v_decls_621_);
lean_inc(v_lDecls_620_);
lean_inc(v_mvarCounter_619_);
lean_inc(v_lmvarCounter_618_);
lean_inc(v_levelAssignDepth_617_);
lean_inc(v_depth_616_);
lean_dec(v_mctx_608_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_639_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v___x_629_; lean_object* v___x_631_; 
v___x_629_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_eAssignment_624_, v_mvarId_603_, v_val_604_);
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 8, v___x_629_);
v___x_631_ = v___x_627_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_638_; 
v_reuseFailAlloc_638_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_638_, 0, v_depth_616_);
lean_ctor_set(v_reuseFailAlloc_638_, 1, v_levelAssignDepth_617_);
lean_ctor_set(v_reuseFailAlloc_638_, 2, v_lmvarCounter_618_);
lean_ctor_set(v_reuseFailAlloc_638_, 3, v_mvarCounter_619_);
lean_ctor_set(v_reuseFailAlloc_638_, 4, v_lDecls_620_);
lean_ctor_set(v_reuseFailAlloc_638_, 5, v_decls_621_);
lean_ctor_set(v_reuseFailAlloc_638_, 6, v_userNames_622_);
lean_ctor_set(v_reuseFailAlloc_638_, 7, v_lAssignment_623_);
lean_ctor_set(v_reuseFailAlloc_638_, 8, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_638_, 9, v_dAssignment_625_);
v___x_631_ = v_reuseFailAlloc_638_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_633_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_631_);
v___x_633_ = v___x_614_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_637_; 
v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_637_, 0, v___x_631_);
lean_ctor_set(v_reuseFailAlloc_637_, 1, v_cache_609_);
lean_ctor_set(v_reuseFailAlloc_637_, 2, v_zetaDeltaFVarIds_610_);
lean_ctor_set(v_reuseFailAlloc_637_, 3, v_postponed_611_);
lean_ctor_set(v_reuseFailAlloc_637_, 4, v_diag_612_);
v___x_633_ = v_reuseFailAlloc_637_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_st_ref_set(v___y_605_, v___x_633_);
v___x_635_ = lean_box(0);
v___x_636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_636_, 0, v___x_635_);
return v___x_636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object* v_mvarId_641_, lean_object* v_val_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_mvarId_641_, v_val_642_, v___y_643_);
lean_dec(v___y_643_);
return v_res_645_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__1(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_647_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__0));
v___x_648_ = l_Lean_stringToMessageData(v___x_647_);
return v___x_648_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__3(void){
_start:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__2));
v___x_651_ = l_Lean_stringToMessageData(v___x_650_);
return v___x_651_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__7(void){
_start:
{
lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; 
v___x_655_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__6));
v___x_656_ = lean_unsigned_to_nat(22u);
v___x_657_ = lean_unsigned_to_nat(64u);
v___x_658_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__5));
v___x_659_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__4));
v___x_660_ = l_mkPanicMessageWithDecl(v___x_659_, v___x_658_, v___x_657_, v___x_656_, v___x_655_);
return v___x_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object* v_snd_664_, lean_object* v___x_665_, lean_object* v_fvarId_666_, lean_object* v_hFVarId_667_, lean_object* v___x_668_, lean_object* v_fst_669_, lean_object* v_fvarSubst_670_, uint8_t v_clearH_671_, lean_object* v___x_672_, lean_object* v___x_673_, lean_object* v___x_674_, uint8_t v_skip_675_, uint8_t v___x_676_, lean_object* v___x_677_, lean_object* v___x_678_, lean_object* v_a_679_, uint8_t v_symm_680_, uint8_t v___x_681_, lean_object* v___x_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_697_; lean_object* v___y_698_; lean_object* v___y_699_; lean_object* v___y_705_; lean_object* v_mvarId_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v_newVal_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_763_; lean_object* v___y_764_; uint8_t v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v_major_792_; lean_object* v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; uint8_t v___y_829_; lean_object* v___y_830_; lean_object* v_motive_831_; lean_object* v_newType_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___y_835_; lean_object* v___y_836_; lean_object* v___x_847_; 
lean_inc(v_snd_664_);
v___x_847_ = l_Lean_MVarId_getDecl(v_snd_664_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v___x_847_);
lean_inc(v___x_665_);
v___x_849_ = l_Lean_FVarId_getDecl___redArg(v___x_665_, v___y_683_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_849_) == 0)
{
lean_object* v_a_850_; lean_object* v___x_851_; lean_object* v___x_852_; 
v_a_850_ = lean_ctor_get(v___x_849_, 0);
lean_inc(v_a_850_);
lean_dec_ref(v___x_849_);
v___x_851_ = l_Lean_LocalDecl_type(v_a_850_);
lean_dec(v_a_850_);
v___x_852_ = l_Lean_Meta_matchEq_x3f(v___x_851_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_852_) == 0)
{
lean_object* v_a_853_; 
v_a_853_ = lean_ctor_get(v___x_852_, 0);
lean_inc(v_a_853_);
lean_dec_ref(v___x_852_);
if (lean_obj_tag(v_a_853_) == 0)
{
lean_object* v___x_854_; lean_object* v___x_855_; 
lean_dec(v_a_848_);
lean_dec(v_a_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v___x_854_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__7, &l_Lean_Meta_substCore___lam__2___closed__7_once, _init_l_Lean_Meta_substCore___lam__2___closed__7);
v___x_855_ = l_panic___at___00Lean_Meta_substCore_spec__1(v___x_854_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
return v___x_855_;
}
else
{
lean_object* v_val_856_; lean_object* v_snd_857_; lean_object* v_fst_858_; lean_object* v_snd_859_; lean_object* v_type_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___f_863_; lean_object* v___y_865_; 
v_val_856_ = lean_ctor_get(v_a_853_, 0);
lean_inc(v_val_856_);
lean_dec_ref(v_a_853_);
v_snd_857_ = lean_ctor_get(v_val_856_, 1);
lean_inc(v_snd_857_);
lean_dec(v_val_856_);
v_fst_858_ = lean_ctor_get(v_snd_857_, 0);
lean_inc(v_fst_858_);
v_snd_859_ = lean_ctor_get(v_snd_857_, 1);
lean_inc(v_snd_859_);
lean_dec(v_snd_857_);
v_type_860_ = lean_ctor_get(v_a_848_, 2);
lean_inc_ref_n(v_type_860_, 2);
lean_dec(v_a_848_);
v___x_861_ = lean_box(v___x_681_);
v___x_862_ = lean_box(v___x_676_);
lean_inc_ref(v___x_672_);
lean_inc(v___x_673_);
lean_inc_ref(v___x_668_);
v___f_863_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 12, 6);
lean_closure_set(v___f_863_, 0, v_type_860_);
lean_closure_set(v___f_863_, 1, v___x_668_);
lean_closure_set(v___f_863_, 2, v___x_673_);
lean_closure_set(v___f_863_, 3, v___x_672_);
lean_closure_set(v___f_863_, 4, v___x_861_);
lean_closure_set(v___f_863_, 5, v___x_862_);
if (v_symm_680_ == 0)
{
lean_dec(v_fst_858_);
v___y_865_ = v_snd_859_;
goto v___jp_864_;
}
else
{
lean_dec(v_snd_859_);
v___y_865_ = v_fst_858_;
goto v___jp_864_;
}
v___jp_864_:
{
lean_object* v___x_866_; lean_object* v_a_867_; lean_object* v___x_868_; lean_object* v_a_869_; uint8_t v___x_870_; 
v___x_866_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_865_, v___y_684_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
lean_inc(v___x_665_);
lean_inc_ref(v_type_860_);
v___x_868_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_type_860_, v___x_665_, v___y_684_);
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref(v___x_868_);
v___x_870_ = lean_unbox(v_a_869_);
if (v___x_870_ == 0)
{
lean_object* v___x_871_; lean_object* v___x_872_; uint8_t v___x_873_; lean_object* v___x_874_; 
lean_dec_ref(v___f_863_);
v___x_871_ = lean_mk_empty_array_with_capacity(v___x_682_);
lean_inc_ref(v___x_672_);
v___x_872_ = lean_array_push(v___x_871_, v___x_672_);
v___x_873_ = 1;
lean_inc_ref(v_type_860_);
v___x_874_ = l_Lean_Meta_mkLambdaFVars(v___x_872_, v_type_860_, v___x_681_, v___x_676_, v___x_681_, v___x_676_, v___x_873_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___x_872_);
if (lean_obj_tag(v___x_874_) == 0)
{
lean_object* v_a_875_; lean_object* v___x_876_; uint8_t v___x_877_; 
v_a_875_ = lean_ctor_get(v___x_874_, 0);
lean_inc(v_a_875_);
lean_dec_ref(v___x_874_);
lean_inc_ref(v___x_672_);
v___x_876_ = l_Lean_Expr_replaceFVar(v_type_860_, v___x_672_, v_a_867_);
lean_dec_ref(v_type_860_);
v___x_877_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
v___y_829_ = v___x_877_;
v___y_830_ = v_a_867_;
v_motive_831_ = v_a_875_;
v_newType_832_ = v___x_876_;
v___y_833_ = v___y_683_;
v___y_834_ = v___y_684_;
v___y_835_ = v___y_685_;
v___y_836_ = v___y_686_;
goto v___jp_828_;
}
else
{
lean_object* v_a_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_885_; 
lean_dec(v_a_869_);
lean_dec(v_a_867_);
lean_dec_ref(v_type_860_);
lean_dec(v_a_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_878_ = lean_ctor_get(v___x_874_, 0);
v_isSharedCheck_885_ = !lean_is_exclusive(v___x_874_);
if (v_isSharedCheck_885_ == 0)
{
v___x_880_ = v___x_874_;
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_a_878_);
lean_dec(v___x_874_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_885_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_883_; 
if (v_isShared_881_ == 0)
{
v___x_883_ = v___x_880_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v_a_878_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
else
{
lean_object* v___x_886_; lean_object* v___x_887_; 
lean_inc_ref(v___x_672_);
v___x_886_ = l_Lean_Expr_replaceFVar(v_type_860_, v___x_672_, v_a_867_);
lean_inc(v_a_867_);
v___x_887_ = l_Lean_Meta_mkEqRefl(v_a_867_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref(v___x_887_);
lean_inc_ref(v___x_668_);
v___x_889_ = l_Lean_Expr_replaceFVar(v___x_886_, v___x_668_, v_a_888_);
lean_dec(v_a_888_);
lean_dec_ref(v___x_886_);
if (v_symm_680_ == 0)
{
lean_object* v___x_890_; 
lean_dec_ref(v_type_860_);
lean_inc_ref(v___x_672_);
lean_inc(v_a_867_);
v___x_890_ = l_Lean_Meta_mkEq(v_a_867_, v___x_672_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_890_) == 0)
{
lean_object* v_a_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v_a_891_ = lean_ctor_get(v___x_890_, 0);
lean_inc(v_a_891_);
lean_dec_ref(v___x_890_);
v___x_892_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__9));
v___x_893_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v___x_892_, v_a_891_, v___f_863_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; uint8_t v___x_895_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref(v___x_893_);
v___x_895_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
v___y_829_ = v___x_895_;
v___y_830_ = v_a_867_;
v_motive_831_ = v_a_894_;
v_newType_832_ = v___x_889_;
v___y_833_ = v___y_683_;
v___y_834_ = v___y_684_;
v___y_835_ = v___y_685_;
v___y_836_ = v___y_686_;
goto v___jp_828_;
}
else
{
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v___x_889_);
lean_dec(v_a_869_);
lean_dec(v_a_867_);
lean_dec(v_a_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_896_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_893_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_893_);
v___x_898_ = lean_box(0);
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
v_resetjp_897_:
{
lean_object* v___x_901_; 
if (v_isShared_899_ == 0)
{
v___x_901_ = v___x_898_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_a_896_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
}
}
else
{
lean_object* v_a_904_; lean_object* v___x_906_; uint8_t v_isShared_907_; uint8_t v_isSharedCheck_911_; 
lean_dec_ref(v___x_889_);
lean_dec(v_a_869_);
lean_dec(v_a_867_);
lean_dec_ref(v___f_863_);
lean_dec(v_a_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_904_ = lean_ctor_get(v___x_890_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_890_);
if (v_isSharedCheck_911_ == 0)
{
v___x_906_ = v___x_890_;
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
else
{
lean_inc(v_a_904_);
lean_dec(v___x_890_);
v___x_906_ = lean_box(0);
v_isShared_907_ = v_isSharedCheck_911_;
goto v_resetjp_905_;
}
v_resetjp_905_:
{
lean_object* v___x_909_; 
if (v_isShared_907_ == 0)
{
v___x_909_ = v___x_906_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v_a_904_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
}
else
{
lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; lean_object* v___x_916_; 
lean_dec_ref(v___f_863_);
v___x_912_ = lean_mk_empty_array_with_capacity(v___x_673_);
lean_inc_ref(v___x_672_);
v___x_913_ = lean_array_push(v___x_912_, v___x_672_);
lean_inc_ref(v___x_668_);
v___x_914_ = lean_array_push(v___x_913_, v___x_668_);
v___x_915_ = 1;
v___x_916_ = l_Lean_Meta_mkLambdaFVars(v___x_914_, v_type_860_, v___x_681_, v___x_676_, v___x_681_, v___x_676_, v___x_915_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
lean_dec_ref(v___x_914_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_object* v_a_917_; uint8_t v___x_918_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
lean_inc(v_a_917_);
lean_dec_ref(v___x_916_);
v___x_918_ = lean_unbox(v_a_869_);
lean_dec(v_a_869_);
v___y_829_ = v___x_918_;
v___y_830_ = v_a_867_;
v_motive_831_ = v_a_917_;
v_newType_832_ = v___x_889_;
v___y_833_ = v___y_683_;
v___y_834_ = v___y_684_;
v___y_835_ = v___y_685_;
v___y_836_ = v___y_686_;
goto v___jp_828_;
}
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v___x_889_);
lean_dec(v_a_869_);
lean_dec(v_a_867_);
lean_dec(v_a_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_919_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_916_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_916_);
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
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec_ref(v___x_886_);
lean_dec(v_a_869_);
lean_dec(v_a_867_);
lean_dec_ref(v___f_863_);
lean_dec_ref(v_type_860_);
lean_dec(v_a_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_927_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_887_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_887_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v___x_932_; 
if (v_isShared_930_ == 0)
{
v___x_932_ = v___x_929_;
goto v_reusejp_931_;
}
else
{
lean_object* v_reuseFailAlloc_933_; 
v_reuseFailAlloc_933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_933_, 0, v_a_927_);
v___x_932_ = v_reuseFailAlloc_933_;
goto v_reusejp_931_;
}
v_reusejp_931_:
{
return v___x_932_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_a_848_);
lean_dec(v_a_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_935_ = lean_ctor_get(v___x_852_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_852_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_852_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_852_);
v___x_937_ = lean_box(0);
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
v_resetjp_936_:
{
lean_object* v___x_940_; 
if (v_isShared_938_ == 0)
{
v___x_940_ = v___x_937_;
goto v_reusejp_939_;
}
else
{
lean_object* v_reuseFailAlloc_941_; 
v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_941_, 0, v_a_935_);
v___x_940_ = v_reuseFailAlloc_941_;
goto v_reusejp_939_;
}
v_reusejp_939_:
{
return v___x_940_;
}
}
}
}
else
{
lean_object* v_a_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_950_; 
lean_dec(v_a_848_);
lean_dec(v_a_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_943_ = lean_ctor_get(v___x_849_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_849_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_849_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_849_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_948_; 
if (v_isShared_946_ == 0)
{
v___x_948_ = v___x_945_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v_a_943_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
}
}
else
{
lean_object* v_a_951_; lean_object* v___x_953_; uint8_t v_isShared_954_; uint8_t v_isSharedCheck_958_; 
lean_dec(v_a_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_951_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_958_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_958_ == 0)
{
v___x_953_ = v___x_847_;
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
else
{
lean_inc(v_a_951_);
lean_dec(v___x_847_);
v___x_953_ = lean_box(0);
v_isShared_954_ = v_isSharedCheck_958_;
goto v_resetjp_952_;
}
v_resetjp_952_:
{
lean_object* v___x_956_; 
if (v_isShared_954_ == 0)
{
v___x_956_ = v___x_953_;
goto v_reusejp_955_;
}
else
{
lean_object* v_reuseFailAlloc_957_; 
v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_957_, 0, v_a_951_);
v___x_956_ = v_reuseFailAlloc_957_;
goto v_reusejp_955_;
}
v_reusejp_955_:
{
return v___x_956_;
}
}
}
v___jp_688_:
{
lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_692_ = l_Lean_Meta_FVarSubst_insert(v___y_690_, v_fvarId_666_, v___y_691_);
v___x_693_ = l_Lean_Meta_FVarSubst_insert(v___x_692_, v_hFVarId_667_, v___x_668_);
v___x_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_694_, 0, v___x_693_);
lean_ctor_set(v___x_694_, 1, v___y_689_);
v___x_695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
return v___x_695_;
}
v___jp_696_:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_array_get_size(v___y_698_);
v___x_701_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_669_, v___y_698_, v___x_700_, v___x_700_, v_fvarSubst_670_);
lean_dec_ref(v___y_698_);
if (v_clearH_671_ == 0)
{
lean_object* v_a_702_; 
lean_dec_ref(v___y_699_);
v_a_702_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_702_);
lean_dec_ref(v___x_701_);
v___y_689_ = v___y_697_;
v___y_690_ = v_a_702_;
v___y_691_ = v___x_672_;
goto v___jp_688_;
}
else
{
lean_object* v_a_703_; 
lean_dec_ref(v___x_672_);
v_a_703_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_a_703_);
lean_dec_ref(v___x_701_);
v___y_689_ = v___y_697_;
v___y_690_ = v_a_703_;
v___y_691_ = v___y_699_;
goto v___jp_688_;
}
}
v___jp_704_:
{
lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; 
v___x_711_ = lean_array_get_size(v_fst_669_);
v___x_712_ = lean_nat_sub(v___x_711_, v___x_673_);
lean_dec(v___x_673_);
lean_inc(v___x_712_);
v___x_713_ = l_Lean_Meta_introNCore(v_mvarId_706_, v___x_712_, v___x_674_, v_skip_675_, v___x_676_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v_options_715_; uint8_t v_hasTrace_716_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
lean_inc(v_a_714_);
lean_dec_ref(v___x_713_);
v_options_715_ = lean_ctor_get(v___y_709_, 2);
v_hasTrace_716_ = lean_ctor_get_uint8(v_options_715_, sizeof(void*)*1);
if (v_hasTrace_716_ == 0)
{
lean_object* v_fst_717_; lean_object* v_snd_718_; 
lean_dec(v___x_712_);
lean_dec(v___x_677_);
v_fst_717_ = lean_ctor_get(v_a_714_, 0);
lean_inc(v_fst_717_);
v_snd_718_ = lean_ctor_get(v_a_714_, 1);
lean_inc(v_snd_718_);
lean_dec(v_a_714_);
v___y_697_ = v_snd_718_;
v___y_698_ = v_fst_717_;
v___y_699_ = v___y_705_;
goto v___jp_696_;
}
else
{
lean_object* v_fst_719_; lean_object* v_snd_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_748_; 
v_fst_719_ = lean_ctor_get(v_a_714_, 0);
v_snd_720_ = lean_ctor_get(v_a_714_, 1);
v_isSharedCheck_748_ = !lean_is_exclusive(v_a_714_);
if (v_isSharedCheck_748_ == 0)
{
v___x_722_ = v_a_714_;
v_isShared_723_ = v_isSharedCheck_748_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_snd_720_);
lean_inc(v_fst_719_);
lean_dec(v_a_714_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_748_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v_inheritedTraceOptions_724_; lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v_inheritedTraceOptions_724_ = lean_ctor_get(v___y_709_, 13);
v___x_725_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
lean_inc(v___x_677_);
v___x_726_ = l_Lean_Name_append(v___x_725_, v___x_677_);
v___x_727_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_724_, v_options_715_, v___x_726_);
lean_dec(v___x_726_);
if (v___x_727_ == 0)
{
lean_del_object(v___x_722_);
lean_dec(v___x_712_);
lean_dec(v___x_677_);
v___y_697_ = v_snd_720_;
v___y_698_ = v_fst_719_;
v___y_699_ = v___y_705_;
goto v___jp_696_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_733_; 
v___x_728_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__1, &l_Lean_Meta_substCore___lam__2___closed__1_once, _init_l_Lean_Meta_substCore___lam__2___closed__1);
v___x_729_ = l_Nat_reprFast(v___x_712_);
v___x_730_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
v___x_731_ = l_Lean_MessageData_ofFormat(v___x_730_);
if (v_isShared_723_ == 0)
{
lean_ctor_set_tag(v___x_722_, 7);
lean_ctor_set(v___x_722_, 1, v___x_731_);
lean_ctor_set(v___x_722_, 0, v___x_728_);
v___x_733_ = v___x_722_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_747_, 1, v___x_731_);
v___x_733_ = v_reuseFailAlloc_747_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; 
v___x_734_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__3, &l_Lean_Meta_substCore___lam__2___closed__3_once, _init_l_Lean_Meta_substCore___lam__2___closed__3);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
lean_inc(v_snd_720_);
v___x_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_736_, 0, v_snd_720_);
v___x_737_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_737_, 0, v___x_735_);
lean_ctor_set(v___x_737_, 1, v___x_736_);
v___x_738_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_677_, v___x_737_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
if (lean_obj_tag(v___x_738_) == 0)
{
lean_dec_ref(v___x_738_);
v___y_697_ = v_snd_720_;
v___y_698_ = v_fst_719_;
v___y_699_ = v___y_705_;
goto v___jp_696_;
}
else
{
lean_object* v_a_739_; lean_object* v___x_741_; uint8_t v_isShared_742_; uint8_t v_isSharedCheck_746_; 
lean_dec(v_snd_720_);
lean_dec(v_fst_719_);
lean_dec_ref(v___y_705_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
v_a_739_ = lean_ctor_get(v___x_738_, 0);
v_isSharedCheck_746_ = !lean_is_exclusive(v___x_738_);
if (v_isSharedCheck_746_ == 0)
{
v___x_741_ = v___x_738_;
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
else
{
lean_inc(v_a_739_);
lean_dec(v___x_738_);
v___x_741_ = lean_box(0);
v_isShared_742_ = v_isSharedCheck_746_;
goto v_resetjp_740_;
}
v_resetjp_740_:
{
lean_object* v___x_744_; 
if (v_isShared_742_ == 0)
{
v___x_744_ = v___x_741_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
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
lean_object* v_a_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_756_; 
lean_dec(v___x_712_);
lean_dec_ref(v___y_705_);
lean_dec(v___x_677_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
v_a_749_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_756_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_756_ == 0)
{
v___x_751_ = v___x_713_;
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_a_749_);
lean_dec(v___x_713_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_756_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_752_ == 0)
{
v___x_754_ = v___x_751_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_755_; 
v_reuseFailAlloc_755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_755_, 0, v_a_749_);
v___x_754_ = v_reuseFailAlloc_755_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
return v___x_754_;
}
}
}
}
v___jp_757_:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_snd_664_, v_newVal_760_, v___y_762_);
lean_dec_ref(v___x_765_);
v___x_766_ = l_Lean_Expr_mvarId_x21(v___y_759_);
lean_dec_ref(v___y_759_);
if (v_clearH_671_ == 0)
{
lean_dec(v___x_678_);
lean_dec(v___x_665_);
v___y_705_ = v___y_758_;
v_mvarId_706_ = v___x_766_;
v___y_707_ = v___y_761_;
v___y_708_ = v___y_762_;
v___y_709_ = v___y_763_;
v___y_710_ = v___y_764_;
goto v___jp_704_;
}
else
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_MVarId_clear(v___x_766_, v___x_665_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___x_769_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref(v___x_767_);
v___x_769_ = l_Lean_MVarId_clear(v_a_768_, v___x_678_, v___y_761_, v___y_762_, v___y_763_, v___y_764_);
if (lean_obj_tag(v___x_769_) == 0)
{
lean_object* v_a_770_; 
v_a_770_ = lean_ctor_get(v___x_769_, 0);
lean_inc(v_a_770_);
lean_dec_ref(v___x_769_);
v___y_705_ = v___y_758_;
v_mvarId_706_ = v_a_770_;
v___y_707_ = v___y_761_;
v___y_708_ = v___y_762_;
v___y_709_ = v___y_763_;
v___y_710_ = v___y_764_;
goto v___jp_704_;
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v___y_758_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
v_a_771_ = lean_ctor_get(v___x_769_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_769_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_769_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_769_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_776_; 
if (v_isShared_774_ == 0)
{
v___x_776_ = v___x_773_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_a_771_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
else
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_786_; 
lean_dec_ref(v___y_758_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
v_a_779_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_786_ == 0)
{
v___x_781_ = v___x_767_;
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_767_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_786_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_784_; 
if (v_isShared_782_ == 0)
{
v___x_784_ = v___x_781_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_a_779_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
}
}
}
v___jp_787_:
{
lean_object* v___x_797_; 
v___x_797_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_791_, v_a_679_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_797_) == 0)
{
if (v___y_788_ == 0)
{
lean_object* v_a_798_; lean_object* v___x_799_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc_n(v_a_798_, 2);
lean_dec_ref(v___x_797_);
v___x_799_ = l_Lean_Meta_mkEqNDRec(v___y_789_, v_a_798_, v_major_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_799_) == 0)
{
lean_object* v_a_800_; 
v_a_800_ = lean_ctor_get(v___x_799_, 0);
lean_inc(v_a_800_);
lean_dec_ref(v___x_799_);
v___y_758_ = v___y_790_;
v___y_759_ = v_a_798_;
v_newVal_760_ = v_a_800_;
v___y_761_ = v___y_793_;
v___y_762_ = v___y_794_;
v___y_763_ = v___y_795_;
v___y_764_ = v___y_796_;
goto v___jp_757_;
}
else
{
lean_object* v_a_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_808_; 
lean_dec(v_a_798_);
lean_dec_ref(v___y_790_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_801_ = lean_ctor_get(v___x_799_, 0);
v_isSharedCheck_808_ = !lean_is_exclusive(v___x_799_);
if (v_isSharedCheck_808_ == 0)
{
v___x_803_ = v___x_799_;
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_a_801_);
lean_dec(v___x_799_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_808_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_806_; 
if (v_isShared_804_ == 0)
{
v___x_806_ = v___x_803_;
goto v_reusejp_805_;
}
else
{
lean_object* v_reuseFailAlloc_807_; 
v_reuseFailAlloc_807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_807_, 0, v_a_801_);
v___x_806_ = v_reuseFailAlloc_807_;
goto v_reusejp_805_;
}
v_reusejp_805_:
{
return v___x_806_;
}
}
}
}
else
{
lean_object* v_a_809_; lean_object* v___x_810_; 
v_a_809_ = lean_ctor_get(v___x_797_, 0);
lean_inc_n(v_a_809_, 2);
lean_dec_ref(v___x_797_);
v___x_810_ = l_Lean_Meta_mkEqRec(v___y_789_, v_a_809_, v_major_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_object* v_a_811_; 
v_a_811_ = lean_ctor_get(v___x_810_, 0);
lean_inc(v_a_811_);
lean_dec_ref(v___x_810_);
v___y_758_ = v___y_790_;
v___y_759_ = v_a_809_;
v_newVal_760_ = v_a_811_;
v___y_761_ = v___y_793_;
v___y_762_ = v___y_794_;
v___y_763_ = v___y_795_;
v___y_764_ = v___y_796_;
goto v___jp_757_;
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_a_809_);
lean_dec_ref(v___y_790_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_812_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_810_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_810_);
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
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
lean_dec_ref(v_major_792_);
lean_dec_ref(v___y_790_);
lean_dec_ref(v___y_789_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_820_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_797_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_797_);
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
v___jp_828_:
{
if (v_symm_680_ == 0)
{
lean_object* v___x_837_; 
lean_inc_ref(v___x_668_);
v___x_837_ = l_Lean_Meta_mkEqSymm(v___x_668_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
if (lean_obj_tag(v___x_837_) == 0)
{
lean_object* v_a_838_; 
v_a_838_ = lean_ctor_get(v___x_837_, 0);
lean_inc(v_a_838_);
lean_dec_ref(v___x_837_);
v___y_788_ = v___y_829_;
v___y_789_ = v_motive_831_;
v___y_790_ = v___y_830_;
v___y_791_ = v_newType_832_;
v_major_792_ = v_a_838_;
v___y_793_ = v___y_833_;
v___y_794_ = v___y_834_;
v___y_795_ = v___y_835_;
v___y_796_ = v___y_836_;
goto v___jp_787_;
}
else
{
lean_object* v_a_839_; lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v_newType_832_);
lean_dec_ref(v_motive_831_);
lean_dec_ref(v___y_830_);
lean_dec(v_a_679_);
lean_dec(v___x_678_);
lean_dec(v___x_677_);
lean_dec(v___x_674_);
lean_dec(v___x_673_);
lean_dec_ref(v___x_672_);
lean_dec(v_fvarSubst_670_);
lean_dec_ref(v___x_668_);
lean_dec(v_hFVarId_667_);
lean_dec(v_fvarId_666_);
lean_dec(v___x_665_);
lean_dec(v_snd_664_);
v_a_839_ = lean_ctor_get(v___x_837_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_837_);
if (v_isSharedCheck_846_ == 0)
{
v___x_841_ = v___x_837_;
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
else
{
lean_inc(v_a_839_);
lean_dec(v___x_837_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_846_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_844_; 
if (v_isShared_842_ == 0)
{
v___x_844_ = v___x_841_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_a_839_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
else
{
lean_inc_ref(v___x_668_);
v___y_788_ = v___y_829_;
v___y_789_ = v_motive_831_;
v___y_790_ = v___y_830_;
v___y_791_ = v_newType_832_;
v_major_792_ = v___x_668_;
v___y_793_ = v___y_833_;
v___y_794_ = v___y_834_;
v___y_795_ = v___y_835_;
v___y_796_ = v___y_836_;
goto v___jp_787_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object** _args){
lean_object* v_snd_959_ = _args[0];
lean_object* v___x_960_ = _args[1];
lean_object* v_fvarId_961_ = _args[2];
lean_object* v_hFVarId_962_ = _args[3];
lean_object* v___x_963_ = _args[4];
lean_object* v_fst_964_ = _args[5];
lean_object* v_fvarSubst_965_ = _args[6];
lean_object* v_clearH_966_ = _args[7];
lean_object* v___x_967_ = _args[8];
lean_object* v___x_968_ = _args[9];
lean_object* v___x_969_ = _args[10];
lean_object* v_skip_970_ = _args[11];
lean_object* v___x_971_ = _args[12];
lean_object* v___x_972_ = _args[13];
lean_object* v___x_973_ = _args[14];
lean_object* v_a_974_ = _args[15];
lean_object* v_symm_975_ = _args[16];
lean_object* v___x_976_ = _args[17];
lean_object* v___x_977_ = _args[18];
lean_object* v___y_978_ = _args[19];
lean_object* v___y_979_ = _args[20];
lean_object* v___y_980_ = _args[21];
lean_object* v___y_981_ = _args[22];
lean_object* v___y_982_ = _args[23];
_start:
{
uint8_t v_clearH_boxed_983_; uint8_t v_skip_boxed_984_; uint8_t v___x_33838__boxed_985_; uint8_t v_symm_boxed_986_; uint8_t v___x_33842__boxed_987_; lean_object* v_res_988_; 
v_clearH_boxed_983_ = lean_unbox(v_clearH_966_);
v_skip_boxed_984_ = lean_unbox(v_skip_970_);
v___x_33838__boxed_985_ = lean_unbox(v___x_971_);
v_symm_boxed_986_ = lean_unbox(v_symm_975_);
v___x_33842__boxed_987_ = lean_unbox(v___x_976_);
v_res_988_ = l_Lean_Meta_substCore___lam__2(v_snd_959_, v___x_960_, v_fvarId_961_, v_hFVarId_962_, v___x_963_, v_fst_964_, v_fvarSubst_965_, v_clearH_boxed_983_, v___x_967_, v___x_968_, v___x_969_, v_skip_boxed_984_, v___x_33838__boxed_985_, v___x_972_, v___x_973_, v_a_974_, v_symm_boxed_986_, v___x_33842__boxed_987_, v___x_977_, v___y_978_, v___y_979_, v___y_980_, v___y_981_);
lean_dec(v___y_981_);
lean_dec_ref(v___y_980_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___x_977_);
lean_dec_ref(v_fst_964_);
return v_res_988_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
if (lean_obj_tag(v_a_989_) == 0)
{
lean_object* v___x_991_; 
v___x_991_ = l_List_reverse___redArg(v_a_990_);
return v___x_991_;
}
else
{
lean_object* v_head_992_; lean_object* v_tail_993_; lean_object* v___x_995_; uint8_t v_isShared_996_; uint8_t v_isSharedCheck_1002_; 
v_head_992_ = lean_ctor_get(v_a_989_, 0);
v_tail_993_ = lean_ctor_get(v_a_989_, 1);
v_isSharedCheck_1002_ = !lean_is_exclusive(v_a_989_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_995_ = v_a_989_;
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
else
{
lean_inc(v_tail_993_);
lean_inc(v_head_992_);
lean_dec(v_a_989_);
v___x_995_ = lean_box(0);
v_isShared_996_ = v_isSharedCheck_1002_;
goto v_resetjp_994_;
}
v_resetjp_994_:
{
lean_object* v___x_997_; lean_object* v___x_999_; 
v___x_997_ = l_Lean_MessageData_ofName(v_head_992_);
if (v_isShared_996_ == 0)
{
lean_ctor_set(v___x_995_, 1, v_a_990_);
lean_ctor_set(v___x_995_, 0, v___x_997_);
v___x_999_ = v___x_995_;
goto v_reusejp_998_;
}
else
{
lean_object* v_reuseFailAlloc_1001_; 
v_reuseFailAlloc_1001_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1001_, 0, v___x_997_);
lean_ctor_set(v_reuseFailAlloc_1001_, 1, v_a_990_);
v___x_999_ = v_reuseFailAlloc_1001_;
goto v_reusejp_998_;
}
v_reusejp_998_:
{
v_a_989_ = v_tail_993_;
v_a_990_ = v___x_999_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(size_t v_sz_1003_, size_t v_i_1004_, lean_object* v_bs_1005_){
_start:
{
uint8_t v___x_1006_; 
v___x_1006_ = lean_usize_dec_lt(v_i_1004_, v_sz_1003_);
if (v___x_1006_ == 0)
{
return v_bs_1005_;
}
else
{
lean_object* v_v_1007_; lean_object* v___x_1008_; lean_object* v_bs_x27_1009_; size_t v___x_1010_; size_t v___x_1011_; lean_object* v___x_1012_; 
v_v_1007_ = lean_array_uget(v_bs_1005_, v_i_1004_);
v___x_1008_ = lean_unsigned_to_nat(0u);
v_bs_x27_1009_ = lean_array_uset(v_bs_1005_, v_i_1004_, v___x_1008_);
v___x_1010_ = ((size_t)1ULL);
v___x_1011_ = lean_usize_add(v_i_1004_, v___x_1010_);
v___x_1012_ = lean_array_uset(v_bs_x27_1009_, v_i_1004_, v_v_1007_);
v_i_1004_ = v___x_1011_;
v_bs_1005_ = v___x_1012_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8___boxed(lean_object* v_sz_1014_, lean_object* v_i_1015_, lean_object* v_bs_1016_){
_start:
{
size_t v_sz_boxed_1017_; size_t v_i_boxed_1018_; lean_object* v_res_1019_; 
v_sz_boxed_1017_ = lean_unbox_usize(v_sz_1014_);
lean_dec(v_sz_1014_);
v_i_boxed_1018_ = lean_unbox_usize(v_i_1015_);
lean_dec(v_i_1015_);
v_res_1019_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_boxed_1017_, v_i_boxed_1018_, v_bs_1016_);
return v_res_1019_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__2));
v___x_1025_ = l_Lean_stringToMessageData(v___x_1024_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1027_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__4));
v___x_1028_ = l_Lean_stringToMessageData(v___x_1027_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__7));
v___x_1033_ = l_Lean_MessageData_ofFormat(v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__9(void){
_start:
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1034_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__8, &l_Lean_Meta_substCore___lam__3___closed__8_once, _init_l_Lean_Meta_substCore___lam__3___closed__8);
v___x_1035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__11(void){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1037_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__10));
v___x_1038_ = l_Lean_stringToMessageData(v___x_1037_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__13(void){
_start:
{
lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1040_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__12));
v___x_1041_ = l_Lean_stringToMessageData(v___x_1040_);
return v___x_1041_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__15(void){
_start:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__14));
v___x_1044_ = l_Lean_stringToMessageData(v___x_1043_);
return v___x_1044_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__17(void){
_start:
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
v___x_1046_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__16));
v___x_1047_ = l_Lean_stringToMessageData(v___x_1046_);
return v___x_1047_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__19(void){
_start:
{
lean_object* v___x_1049_; lean_object* v___x_1050_; 
v___x_1049_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__18));
v___x_1050_ = l_Lean_stringToMessageData(v___x_1049_);
return v___x_1050_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__25(void){
_start:
{
lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1060_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__24));
v___x_1061_ = l_Lean_stringToMessageData(v___x_1060_);
return v___x_1061_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__27(void){
_start:
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1063_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__26));
v___x_1064_ = l_Lean_stringToMessageData(v___x_1063_);
return v___x_1064_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__29(void){
_start:
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
v___x_1066_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__28));
v___x_1067_ = l_Lean_stringToMessageData(v___x_1066_);
return v___x_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3(lean_object* v_mvarId_1070_, lean_object* v_hFVarId_1071_, lean_object* v___x_1072_, uint8_t v_clearH_1073_, lean_object* v_fvarSubst_1074_, uint8_t v_symm_1075_, uint8_t v_tryToSkip_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___y_1088_; lean_object* v___y_1089_; lean_object* v___x_1120_; 
lean_inc(v_mvarId_1070_);
v___x_1120_ = l_Lean_MVarId_getTag(v_mvarId_1070_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1120_) == 0)
{
lean_object* v_a_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; 
v_a_1121_ = lean_ctor_get(v___x_1120_, 0);
lean_inc(v_a_1121_);
lean_dec_ref(v___x_1120_);
v___x_1122_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
lean_inc(v_mvarId_1070_);
v___x_1123_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1070_, v___x_1122_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1123_) == 0)
{
lean_object* v___x_1124_; 
lean_dec_ref(v___x_1123_);
lean_inc(v_hFVarId_1071_);
v___x_1124_ = l_Lean_FVarId_getDecl___redArg(v_hFVarId_1071_, v___y_1077_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1124_) == 0)
{
lean_object* v_a_1125_; lean_object* v___x_1126_; lean_object* v___y_1128_; lean_object* v___y_1129_; lean_object* v___x_1141_; 
v_a_1125_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_a_1125_);
lean_dec_ref(v___x_1124_);
v___x_1126_ = l_Lean_LocalDecl_type(v_a_1125_);
lean_dec(v_a_1125_);
lean_inc_ref(v___x_1126_);
v___x_1141_ = l_Lean_Meta_matchEq_x3f(v___x_1126_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1141_) == 0)
{
lean_object* v_a_1142_; 
v_a_1142_ = lean_ctor_get(v___x_1141_, 0);
lean_inc(v_a_1142_);
lean_dec_ref(v___x_1141_);
if (lean_obj_tag(v_a_1142_) == 0)
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_dec_ref(v___x_1126_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
v___x_1143_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__9, &l_Lean_Meta_substCore___lam__3___closed__9_once, _init_l_Lean_Meta_substCore___lam__3___closed__9);
v___x_1144_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1122_, v_mvarId_1070_, v___x_1143_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
return v___x_1144_;
}
else
{
lean_object* v_val_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1467_; 
v_val_1145_ = lean_ctor_get(v_a_1142_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v_a_1142_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1147_ = v_a_1142_;
v_isShared_1148_ = v_isSharedCheck_1467_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_val_1145_);
lean_dec(v_a_1142_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1467_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_snd_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1465_; 
v_snd_1149_ = lean_ctor_get(v_val_1145_, 1);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_val_1145_);
if (v_isSharedCheck_1465_ == 0)
{
lean_object* v_unused_1466_; 
v_unused_1466_ = lean_ctor_get(v_val_1145_, 0);
lean_dec(v_unused_1466_);
v___x_1151_ = v_val_1145_;
v_isShared_1152_ = v_isSharedCheck_1465_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_snd_1149_);
lean_dec(v_val_1145_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1465_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v_fst_1153_; lean_object* v_snd_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1464_; 
v_fst_1153_ = lean_ctor_get(v_snd_1149_, 0);
v_snd_1154_ = lean_ctor_get(v_snd_1149_, 1);
v_isSharedCheck_1464_ = !lean_is_exclusive(v_snd_1149_);
if (v_isSharedCheck_1464_ == 0)
{
v___x_1156_ = v_snd_1149_;
v_isShared_1157_ = v_isSharedCheck_1464_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_snd_1154_);
lean_inc(v_fst_1153_);
lean_dec(v_snd_1149_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1464_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
uint8_t v___x_1158_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; uint8_t v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; lean_object* v___y_1175_; lean_object* v___y_1176_; uint8_t v_skip_1177_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; uint8_t v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; uint8_t v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1200_; lean_object* v___y_1201_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; uint8_t v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; uint8_t v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1243_; lean_object* v___y_1244_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; uint8_t v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; uint8_t v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1290_; lean_object* v___y_1291_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1342_; lean_object* v___y_1343_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1400_; lean_object* v___y_1401_; lean_object* v___y_1427_; lean_object* v___y_1428_; lean_object* v___y_1460_; 
v___x_1158_ = 1;
if (v_symm_1075_ == 0)
{
lean_inc(v_fst_1153_);
v___y_1460_ = v_fst_1153_;
goto v___jp_1459_;
}
else
{
lean_inc(v_snd_1154_);
v___y_1460_ = v_snd_1154_;
goto v___jp_1459_;
}
v___jp_1159_:
{
lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; 
v___x_1178_ = lean_box(v_clearH_1073_);
v___x_1179_ = lean_box(v_skip_1177_);
v___x_1180_ = lean_box(v___x_1158_);
v___x_1181_ = lean_box(v_symm_1075_);
v___x_1182_ = lean_box(v___y_1171_);
v___f_1183_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__2___boxed), 24, 19);
lean_closure_set(v___f_1183_, 0, v___y_1163_);
lean_closure_set(v___f_1183_, 1, v___y_1160_);
lean_closure_set(v___f_1183_, 2, v___y_1167_);
lean_closure_set(v___f_1183_, 3, v_hFVarId_1071_);
lean_closure_set(v___f_1183_, 4, v___y_1169_);
lean_closure_set(v___f_1183_, 5, v___y_1161_);
lean_closure_set(v___f_1183_, 6, v_fvarSubst_1074_);
lean_closure_set(v___f_1183_, 7, v___x_1178_);
lean_closure_set(v___f_1183_, 8, v___y_1162_);
lean_closure_set(v___f_1183_, 9, v___y_1170_);
lean_closure_set(v___f_1183_, 10, v___y_1168_);
lean_closure_set(v___f_1183_, 11, v___x_1179_);
lean_closure_set(v___f_1183_, 12, v___x_1180_);
lean_closure_set(v___f_1183_, 13, v___y_1165_);
lean_closure_set(v___f_1183_, 14, v___y_1166_);
lean_closure_set(v___f_1183_, 15, v_a_1121_);
lean_closure_set(v___f_1183_, 16, v___x_1181_);
lean_closure_set(v___f_1183_, 17, v___x_1182_);
lean_closure_set(v___f_1183_, 18, v___y_1174_);
v___x_1184_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v___y_1175_, v___f_1183_, v___y_1173_, v___y_1164_, v___y_1172_, v___y_1176_);
lean_dec(v___y_1176_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1173_);
return v___x_1184_;
}
v___jp_1185_:
{
lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; 
v___x_1202_ = lean_unsigned_to_nat(0u);
v___x_1203_ = lean_array_get(v___x_1072_, v___y_1196_, v___x_1202_);
lean_inc(v___x_1203_);
v___x_1204_ = l_Lean_mkFVar(v___x_1203_);
v___x_1205_ = lean_unsigned_to_nat(1u);
v___x_1206_ = lean_array_get(v___x_1072_, v___y_1196_, v___x_1205_);
lean_dec_ref(v___y_1196_);
lean_inc(v___x_1206_);
v___x_1207_ = l_Lean_mkFVar(v___x_1206_);
if (v_tryToSkip_1076_ == 0)
{
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1193_);
v___y_1160_ = v___x_1206_;
v___y_1161_ = v___y_1189_;
v___y_1162_ = v___x_1204_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1199_;
v___y_1165_ = v___y_1192_;
v___y_1166_ = v___x_1203_;
v___y_1167_ = v___y_1186_;
v___y_1168_ = v___y_1187_;
v___y_1169_ = v___x_1207_;
v___y_1170_ = v___y_1188_;
v___y_1171_ = v___y_1190_;
v___y_1172_ = v___y_1200_;
v___y_1173_ = v___y_1198_;
v___y_1174_ = v___x_1205_;
v___y_1175_ = v___y_1195_;
v___y_1176_ = v___y_1201_;
v_skip_1177_ = v___y_1194_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = lean_array_get_size(v___y_1193_);
lean_dec_ref(v___y_1193_);
v___x_1209_ = lean_nat_dec_eq(v___x_1208_, v___y_1197_);
lean_dec(v___y_1197_);
if (v___x_1209_ == 0)
{
v___y_1160_ = v___x_1206_;
v___y_1161_ = v___y_1189_;
v___y_1162_ = v___x_1204_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1199_;
v___y_1165_ = v___y_1192_;
v___y_1166_ = v___x_1203_;
v___y_1167_ = v___y_1186_;
v___y_1168_ = v___y_1187_;
v___y_1169_ = v___x_1207_;
v___y_1170_ = v___y_1188_;
v___y_1171_ = v___y_1190_;
v___y_1172_ = v___y_1200_;
v___y_1173_ = v___y_1198_;
v___y_1174_ = v___x_1205_;
v___y_1175_ = v___y_1195_;
v___y_1176_ = v___y_1201_;
v_skip_1177_ = v___y_1194_;
goto v___jp_1159_;
}
else
{
lean_object* v___x_1210_; 
lean_inc(v___y_1195_);
v___x_1210_ = l_Lean_MVarId_getType(v___y_1195_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; lean_object* v_a_1213_; uint8_t v___x_1214_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc_n(v_a_1211_, 2);
lean_dec_ref(v___x_1210_);
lean_inc(v___x_1203_);
v___x_1212_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1211_, v___x_1203_, v___y_1199_);
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
lean_inc(v_a_1213_);
lean_dec_ref(v___x_1212_);
v___x_1214_ = lean_unbox(v_a_1213_);
lean_dec(v_a_1213_);
if (v___x_1214_ == 0)
{
lean_object* v___x_1215_; lean_object* v_a_1216_; uint8_t v___x_1217_; 
lean_inc(v___x_1206_);
v___x_1215_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1211_, v___x_1206_, v___y_1199_);
v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
lean_inc(v_a_1216_);
lean_dec_ref(v___x_1215_);
v___x_1217_ = lean_unbox(v_a_1216_);
lean_dec(v_a_1216_);
if (v___x_1217_ == 0)
{
lean_dec_ref(v___x_1207_);
lean_dec_ref(v___x_1204_);
lean_dec(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v_a_1121_);
lean_dec(v_hFVarId_1071_);
v___y_1083_ = v___x_1206_;
v___y_1084_ = v___y_1200_;
v___y_1085_ = v___y_1199_;
v___y_1086_ = v___y_1198_;
v___y_1087_ = v___x_1203_;
v___y_1088_ = v___y_1195_;
v___y_1089_ = v___y_1201_;
goto v___jp_1082_;
}
else
{
v___y_1160_ = v___x_1206_;
v___y_1161_ = v___y_1189_;
v___y_1162_ = v___x_1204_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1199_;
v___y_1165_ = v___y_1192_;
v___y_1166_ = v___x_1203_;
v___y_1167_ = v___y_1186_;
v___y_1168_ = v___y_1187_;
v___y_1169_ = v___x_1207_;
v___y_1170_ = v___y_1188_;
v___y_1171_ = v___y_1190_;
v___y_1172_ = v___y_1200_;
v___y_1173_ = v___y_1198_;
v___y_1174_ = v___x_1205_;
v___y_1175_ = v___y_1195_;
v___y_1176_ = v___y_1201_;
v_skip_1177_ = v___y_1194_;
goto v___jp_1159_;
}
}
else
{
lean_dec(v_a_1211_);
v___y_1160_ = v___x_1206_;
v___y_1161_ = v___y_1189_;
v___y_1162_ = v___x_1204_;
v___y_1163_ = v___y_1191_;
v___y_1164_ = v___y_1199_;
v___y_1165_ = v___y_1192_;
v___y_1166_ = v___x_1203_;
v___y_1167_ = v___y_1186_;
v___y_1168_ = v___y_1187_;
v___y_1169_ = v___x_1207_;
v___y_1170_ = v___y_1188_;
v___y_1171_ = v___y_1190_;
v___y_1172_ = v___y_1200_;
v___y_1173_ = v___y_1198_;
v___y_1174_ = v___x_1205_;
v___y_1175_ = v___y_1195_;
v___y_1176_ = v___y_1201_;
v_skip_1177_ = v___y_1194_;
goto v___jp_1159_;
}
}
else
{
lean_object* v_a_1218_; lean_object* v___x_1220_; uint8_t v_isShared_1221_; uint8_t v_isSharedCheck_1225_; 
lean_dec_ref(v___x_1207_);
lean_dec(v___x_1206_);
lean_dec_ref(v___x_1204_);
lean_dec(v___x_1203_);
lean_dec(v___y_1201_);
lean_dec_ref(v___y_1200_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1195_);
lean_dec(v___y_1192_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
v_a_1218_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1225_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1220_ = v___x_1210_;
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
else
{
lean_inc(v_a_1218_);
lean_dec(v___x_1210_);
v___x_1220_ = lean_box(0);
v_isShared_1221_ = v_isSharedCheck_1225_;
goto v_resetjp_1219_;
}
v_resetjp_1219_:
{
lean_object* v___x_1223_; 
if (v_isShared_1221_ == 0)
{
v___x_1223_ = v___x_1220_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v_a_1218_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
}
}
}
v___jp_1226_:
{
lean_object* v___x_1245_; 
lean_inc_ref(v___y_1239_);
lean_inc(v___y_1244_);
lean_inc_ref(v___y_1243_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
v___x_1245_ = lean_apply_5(v___y_1239_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_, lean_box(0));
if (lean_obj_tag(v___x_1245_) == 0)
{
lean_object* v_a_1246_; uint8_t v___x_1247_; 
v_a_1246_ = lean_ctor_get(v___x_1245_, 0);
lean_inc(v_a_1246_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = lean_unbox(v_a_1246_);
lean_dec(v_a_1246_);
if (v___x_1247_ == 0)
{
lean_dec(v___y_1234_);
lean_del_object(v___x_1156_);
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1229_;
v___y_1189_ = v___y_1230_;
v___y_1190_ = v___y_1231_;
v___y_1191_ = v___y_1232_;
v___y_1192_ = v___y_1233_;
v___y_1193_ = v___y_1236_;
v___y_1194_ = v___y_1235_;
v___y_1195_ = v___y_1238_;
v___y_1196_ = v___y_1237_;
v___y_1197_ = v___y_1240_;
v___y_1198_ = v___y_1241_;
v___y_1199_ = v___y_1242_;
v___y_1200_ = v___y_1243_;
v___y_1201_ = v___y_1244_;
goto v___jp_1185_;
}
else
{
lean_object* v___x_1248_; size_t v_sz_1249_; size_t v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1257_; 
v___x_1248_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__11, &l_Lean_Meta_substCore___lam__3___closed__11_once, _init_l_Lean_Meta_substCore___lam__3___closed__11);
v_sz_1249_ = lean_array_size(v___y_1236_);
v___x_1250_ = ((size_t)0ULL);
lean_inc_ref(v___y_1236_);
v___x_1251_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1249_, v___x_1250_, v___y_1236_);
v___x_1252_ = lean_array_to_list(v___x_1251_);
v___x_1253_ = lean_box(0);
v___x_1254_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(v___x_1252_, v___x_1253_);
v___x_1255_ = l_Lean_MessageData_ofList(v___x_1254_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set_tag(v___x_1156_, 7);
lean_ctor_set(v___x_1156_, 1, v___x_1255_);
lean_ctor_set(v___x_1156_, 0, v___x_1248_);
v___x_1257_ = v___x_1156_;
goto v_reusejp_1256_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___x_1248_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1255_);
v___x_1257_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1256_;
}
v_reusejp_1256_:
{
lean_object* v___x_1258_; 
v___x_1258_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1234_, v___x_1257_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1258_) == 0)
{
lean_dec_ref(v___x_1258_);
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1229_;
v___y_1189_ = v___y_1230_;
v___y_1190_ = v___y_1231_;
v___y_1191_ = v___y_1232_;
v___y_1192_ = v___y_1233_;
v___y_1193_ = v___y_1236_;
v___y_1194_ = v___y_1235_;
v___y_1195_ = v___y_1238_;
v___y_1196_ = v___y_1237_;
v___y_1197_ = v___y_1240_;
v___y_1198_ = v___y_1241_;
v___y_1199_ = v___y_1242_;
v___y_1200_ = v___y_1243_;
v___y_1201_ = v___y_1244_;
goto v___jp_1185_;
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
v_a_1259_ = lean_ctor_get(v___x_1258_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1258_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1258_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1258_);
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
}
}
else
{
lean_object* v_a_1268_; lean_object* v___x_1270_; uint8_t v_isShared_1271_; uint8_t v_isSharedCheck_1275_; 
lean_dec(v___y_1244_);
lean_dec_ref(v___y_1243_);
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_del_object(v___x_1156_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
v_a_1268_ = lean_ctor_get(v___x_1245_, 0);
v_isSharedCheck_1275_ = !lean_is_exclusive(v___x_1245_);
if (v_isSharedCheck_1275_ == 0)
{
v___x_1270_ = v___x_1245_;
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
else
{
lean_inc(v_a_1268_);
lean_dec(v___x_1245_);
v___x_1270_ = lean_box(0);
v_isShared_1271_ = v_isSharedCheck_1275_;
goto v_resetjp_1269_;
}
v_resetjp_1269_:
{
lean_object* v___x_1273_; 
if (v_isShared_1271_ == 0)
{
v___x_1273_ = v___x_1270_;
goto v_reusejp_1272_;
}
else
{
lean_object* v_reuseFailAlloc_1274_; 
v_reuseFailAlloc_1274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1274_, 0, v_a_1268_);
v___x_1273_ = v_reuseFailAlloc_1274_;
goto v_reusejp_1272_;
}
v_reusejp_1272_:
{
return v___x_1273_;
}
}
}
}
v___jp_1276_:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1292_ = lean_box(0);
lean_inc(v___y_1287_);
v___x_1293_ = l_Lean_Meta_introNCore(v___y_1286_, v___y_1287_, v___x_1292_, v___y_1284_, v___x_1158_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1293_) == 0)
{
lean_object* v_a_1294_; lean_object* v_fst_1295_; lean_object* v_snd_1296_; lean_object* v___x_1298_; uint8_t v_isShared_1299_; uint8_t v_isSharedCheck_1325_; 
v_a_1294_ = lean_ctor_get(v___x_1293_, 0);
lean_inc(v_a_1294_);
lean_dec_ref(v___x_1293_);
v_fst_1295_ = lean_ctor_get(v_a_1294_, 0);
v_snd_1296_ = lean_ctor_get(v_a_1294_, 1);
v_isSharedCheck_1325_ = !lean_is_exclusive(v_a_1294_);
if (v_isSharedCheck_1325_ == 0)
{
v___x_1298_ = v_a_1294_;
v_isShared_1299_ = v_isSharedCheck_1325_;
goto v_resetjp_1297_;
}
else
{
lean_inc(v_snd_1296_);
lean_inc(v_fst_1295_);
lean_dec(v_a_1294_);
v___x_1298_ = lean_box(0);
v_isShared_1299_ = v_isSharedCheck_1325_;
goto v_resetjp_1297_;
}
v_resetjp_1297_:
{
lean_object* v___x_1300_; 
lean_inc_ref(v___y_1285_);
lean_inc(v___y_1291_);
lean_inc_ref(v___y_1290_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
v___x_1300_ = lean_apply_5(v___y_1285_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_, lean_box(0));
if (lean_obj_tag(v___x_1300_) == 0)
{
lean_object* v_a_1301_; uint8_t v___x_1302_; 
v_a_1301_ = lean_ctor_get(v___x_1300_, 0);
lean_inc(v_a_1301_);
lean_dec_ref(v___x_1300_);
v___x_1302_ = lean_unbox(v_a_1301_);
lean_dec(v_a_1301_);
if (v___x_1302_ == 0)
{
lean_del_object(v___x_1298_);
lean_inc(v_snd_1296_);
v___y_1227_ = v___y_1277_;
v___y_1228_ = v___x_1292_;
v___y_1229_ = v___y_1278_;
v___y_1230_ = v___y_1279_;
v___y_1231_ = v___y_1280_;
v___y_1232_ = v_snd_1296_;
v___y_1233_ = v___y_1281_;
v___y_1234_ = v___y_1282_;
v___y_1235_ = v___y_1284_;
v___y_1236_ = v___y_1283_;
v___y_1237_ = v_fst_1295_;
v___y_1238_ = v_snd_1296_;
v___y_1239_ = v___y_1285_;
v___y_1240_ = v___y_1287_;
v___y_1241_ = v___y_1288_;
v___y_1242_ = v___y_1289_;
v___y_1243_ = v___y_1290_;
v___y_1244_ = v___y_1291_;
goto v___jp_1226_;
}
else
{
lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1306_; 
v___x_1303_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__13, &l_Lean_Meta_substCore___lam__3___closed__13_once, _init_l_Lean_Meta_substCore___lam__3___closed__13);
lean_inc(v_snd_1296_);
v___x_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1304_, 0, v_snd_1296_);
if (v_isShared_1299_ == 0)
{
lean_ctor_set_tag(v___x_1298_, 7);
lean_ctor_set(v___x_1298_, 1, v___x_1304_);
lean_ctor_set(v___x_1298_, 0, v___x_1303_);
v___x_1306_ = v___x_1298_;
goto v_reusejp_1305_;
}
else
{
lean_object* v_reuseFailAlloc_1316_; 
v_reuseFailAlloc_1316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1316_, 0, v___x_1303_);
lean_ctor_set(v_reuseFailAlloc_1316_, 1, v___x_1304_);
v___x_1306_ = v_reuseFailAlloc_1316_;
goto v_reusejp_1305_;
}
v_reusejp_1305_:
{
lean_object* v___x_1307_; 
lean_inc(v___y_1282_);
v___x_1307_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1282_, v___x_1306_, v___y_1288_, v___y_1289_, v___y_1290_, v___y_1291_);
if (lean_obj_tag(v___x_1307_) == 0)
{
lean_dec_ref(v___x_1307_);
lean_inc(v_snd_1296_);
v___y_1227_ = v___y_1277_;
v___y_1228_ = v___x_1292_;
v___y_1229_ = v___y_1278_;
v___y_1230_ = v___y_1279_;
v___y_1231_ = v___y_1280_;
v___y_1232_ = v_snd_1296_;
v___y_1233_ = v___y_1281_;
v___y_1234_ = v___y_1282_;
v___y_1235_ = v___y_1284_;
v___y_1236_ = v___y_1283_;
v___y_1237_ = v_fst_1295_;
v___y_1238_ = v_snd_1296_;
v___y_1239_ = v___y_1285_;
v___y_1240_ = v___y_1287_;
v___y_1241_ = v___y_1288_;
v___y_1242_ = v___y_1289_;
v___y_1243_ = v___y_1290_;
v___y_1244_ = v___y_1291_;
goto v___jp_1226_;
}
else
{
lean_object* v_a_1308_; lean_object* v___x_1310_; uint8_t v_isShared_1311_; uint8_t v_isSharedCheck_1315_; 
lean_dec(v_snd_1296_);
lean_dec(v_fst_1295_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
lean_del_object(v___x_1156_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
v_a_1308_ = lean_ctor_get(v___x_1307_, 0);
v_isSharedCheck_1315_ = !lean_is_exclusive(v___x_1307_);
if (v_isSharedCheck_1315_ == 0)
{
v___x_1310_ = v___x_1307_;
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
else
{
lean_inc(v_a_1308_);
lean_dec(v___x_1307_);
v___x_1310_ = lean_box(0);
v_isShared_1311_ = v_isSharedCheck_1315_;
goto v_resetjp_1309_;
}
v_resetjp_1309_:
{
lean_object* v___x_1313_; 
if (v_isShared_1311_ == 0)
{
v___x_1313_ = v___x_1310_;
goto v_reusejp_1312_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v_a_1308_);
v___x_1313_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1312_;
}
v_reusejp_1312_:
{
return v___x_1313_;
}
}
}
}
}
}
else
{
lean_object* v_a_1317_; lean_object* v___x_1319_; uint8_t v_isShared_1320_; uint8_t v_isSharedCheck_1324_; 
lean_del_object(v___x_1298_);
lean_dec(v_snd_1296_);
lean_dec(v_fst_1295_);
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
lean_del_object(v___x_1156_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
v_a_1317_ = lean_ctor_get(v___x_1300_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1300_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1319_ = v___x_1300_;
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
else
{
lean_inc(v_a_1317_);
lean_dec(v___x_1300_);
v___x_1319_ = lean_box(0);
v_isShared_1320_ = v_isSharedCheck_1324_;
goto v_resetjp_1318_;
}
v_resetjp_1318_:
{
lean_object* v___x_1322_; 
if (v_isShared_1320_ == 0)
{
v___x_1322_ = v___x_1319_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v_a_1317_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
else
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
lean_dec(v___y_1291_);
lean_dec_ref(v___y_1290_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1282_);
lean_dec(v___y_1281_);
lean_dec_ref(v___y_1279_);
lean_dec(v___y_1278_);
lean_dec(v___y_1277_);
lean_del_object(v___x_1156_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
v_a_1326_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1293_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1293_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
}
v___jp_1334_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; uint8_t v___x_1348_; lean_object* v___x_1349_; 
v___x_1344_ = lean_unsigned_to_nat(2u);
v___x_1345_ = lean_mk_empty_array_with_capacity(v___x_1344_);
v___x_1346_ = lean_array_push(v___x_1345_, v___y_1339_);
lean_inc(v_hFVarId_1071_);
v___x_1347_ = lean_array_push(v___x_1346_, v_hFVarId_1071_);
v___x_1348_ = 0;
v___x_1349_ = l_Lean_MVarId_revert(v_mvarId_1070_, v___x_1347_, v___x_1158_, v___x_1348_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1349_) == 0)
{
lean_object* v_a_1350_; lean_object* v_fst_1351_; lean_object* v_snd_1352_; lean_object* v___x_1354_; uint8_t v_isShared_1355_; uint8_t v_isSharedCheck_1381_; 
v_a_1350_ = lean_ctor_get(v___x_1349_, 0);
lean_inc(v_a_1350_);
lean_dec_ref(v___x_1349_);
v_fst_1351_ = lean_ctor_get(v_a_1350_, 0);
v_snd_1352_ = lean_ctor_get(v_a_1350_, 1);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_a_1350_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1354_ = v_a_1350_;
v_isShared_1355_ = v_isSharedCheck_1381_;
goto v_resetjp_1353_;
}
else
{
lean_inc(v_snd_1352_);
lean_inc(v_fst_1351_);
lean_dec(v_a_1350_);
v___x_1354_ = lean_box(0);
v_isShared_1355_ = v_isSharedCheck_1381_;
goto v_resetjp_1353_;
}
v_resetjp_1353_:
{
lean_object* v___x_1356_; 
lean_inc_ref(v___y_1338_);
lean_inc(v___y_1343_);
lean_inc_ref(v___y_1342_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
v___x_1356_ = lean_apply_5(v___y_1338_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_, lean_box(0));
if (lean_obj_tag(v___x_1356_) == 0)
{
lean_object* v_a_1357_; uint8_t v___x_1358_; 
v_a_1357_ = lean_ctor_get(v___x_1356_, 0);
lean_inc(v_a_1357_);
lean_dec_ref(v___x_1356_);
v___x_1358_ = lean_unbox(v_a_1357_);
lean_dec(v_a_1357_);
if (v___x_1358_ == 0)
{
lean_del_object(v___x_1354_);
lean_inc(v_fst_1351_);
v___y_1277_ = v___y_1335_;
v___y_1278_ = v___x_1344_;
v___y_1279_ = v_fst_1351_;
v___y_1280_ = v___x_1348_;
v___y_1281_ = v___y_1336_;
v___y_1282_ = v___y_1337_;
v___y_1283_ = v_fst_1351_;
v___y_1284_ = v___x_1348_;
v___y_1285_ = v___y_1338_;
v___y_1286_ = v_snd_1352_;
v___y_1287_ = v___x_1344_;
v___y_1288_ = v___y_1340_;
v___y_1289_ = v___y_1341_;
v___y_1290_ = v___y_1342_;
v___y_1291_ = v___y_1343_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1362_; 
v___x_1359_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__15, &l_Lean_Meta_substCore___lam__3___closed__15_once, _init_l_Lean_Meta_substCore___lam__3___closed__15);
lean_inc(v_snd_1352_);
v___x_1360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1360_, 0, v_snd_1352_);
if (v_isShared_1355_ == 0)
{
lean_ctor_set_tag(v___x_1354_, 7);
lean_ctor_set(v___x_1354_, 1, v___x_1360_);
lean_ctor_set(v___x_1354_, 0, v___x_1359_);
v___x_1362_ = v___x_1354_;
goto v_reusejp_1361_;
}
else
{
lean_object* v_reuseFailAlloc_1372_; 
v_reuseFailAlloc_1372_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1372_, 0, v___x_1359_);
lean_ctor_set(v_reuseFailAlloc_1372_, 1, v___x_1360_);
v___x_1362_ = v_reuseFailAlloc_1372_;
goto v_reusejp_1361_;
}
v_reusejp_1361_:
{
lean_object* v___x_1363_; 
lean_inc(v___y_1337_);
v___x_1363_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1337_, v___x_1362_, v___y_1340_, v___y_1341_, v___y_1342_, v___y_1343_);
if (lean_obj_tag(v___x_1363_) == 0)
{
lean_dec_ref(v___x_1363_);
lean_inc(v_fst_1351_);
v___y_1277_ = v___y_1335_;
v___y_1278_ = v___x_1344_;
v___y_1279_ = v_fst_1351_;
v___y_1280_ = v___x_1348_;
v___y_1281_ = v___y_1336_;
v___y_1282_ = v___y_1337_;
v___y_1283_ = v_fst_1351_;
v___y_1284_ = v___x_1348_;
v___y_1285_ = v___y_1338_;
v___y_1286_ = v_snd_1352_;
v___y_1287_ = v___x_1344_;
v___y_1288_ = v___y_1340_;
v___y_1289_ = v___y_1341_;
v___y_1290_ = v___y_1342_;
v___y_1291_ = v___y_1343_;
goto v___jp_1276_;
}
else
{
lean_object* v_a_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1371_; 
lean_dec(v_snd_1352_);
lean_dec(v_fst_1351_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
lean_del_object(v___x_1156_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
v_a_1364_ = lean_ctor_get(v___x_1363_, 0);
v_isSharedCheck_1371_ = !lean_is_exclusive(v___x_1363_);
if (v_isSharedCheck_1371_ == 0)
{
v___x_1366_ = v___x_1363_;
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_a_1364_);
lean_dec(v___x_1363_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1371_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v___x_1369_; 
if (v_isShared_1367_ == 0)
{
v___x_1369_ = v___x_1366_;
goto v_reusejp_1368_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v_a_1364_);
v___x_1369_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1368_;
}
v_reusejp_1368_:
{
return v___x_1369_;
}
}
}
}
}
}
else
{
lean_object* v_a_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1380_; 
lean_del_object(v___x_1354_);
lean_dec(v_snd_1352_);
lean_dec(v_fst_1351_);
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
lean_del_object(v___x_1156_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
v_a_1373_ = lean_ctor_get(v___x_1356_, 0);
v_isSharedCheck_1380_ = !lean_is_exclusive(v___x_1356_);
if (v_isSharedCheck_1380_ == 0)
{
v___x_1375_ = v___x_1356_;
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_a_1373_);
lean_dec(v___x_1356_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1380_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1378_; 
if (v_isShared_1376_ == 0)
{
v___x_1378_ = v___x_1375_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v_a_1373_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
else
{
lean_object* v_a_1382_; lean_object* v___x_1384_; uint8_t v_isShared_1385_; uint8_t v_isSharedCheck_1389_; 
lean_dec(v___y_1343_);
lean_dec_ref(v___y_1342_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1337_);
lean_dec(v___y_1336_);
lean_dec(v___y_1335_);
lean_del_object(v___x_1156_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
v_a_1382_ = lean_ctor_get(v___x_1349_, 0);
v_isSharedCheck_1389_ = !lean_is_exclusive(v___x_1349_);
if (v_isSharedCheck_1389_ == 0)
{
v___x_1384_ = v___x_1349_;
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
else
{
lean_inc(v_a_1382_);
lean_dec(v___x_1349_);
v___x_1384_ = lean_box(0);
v_isShared_1385_ = v_isSharedCheck_1389_;
goto v_resetjp_1383_;
}
v_resetjp_1383_:
{
lean_object* v___x_1387_; 
if (v_isShared_1385_ == 0)
{
v___x_1387_ = v___x_1384_;
goto v_reusejp_1386_;
}
else
{
lean_object* v_reuseFailAlloc_1388_; 
v_reuseFailAlloc_1388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1388_, 0, v_a_1382_);
v___x_1387_ = v_reuseFailAlloc_1388_;
goto v_reusejp_1386_;
}
v_reusejp_1386_:
{
return v___x_1387_;
}
}
}
}
v___jp_1390_:
{
lean_object* v___x_1402_; lean_object* v_a_1403_; uint8_t v___x_1404_; 
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1397_);
v___x_1402_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v___y_1397_, v___y_1395_, v___y_1399_);
v_a_1403_ = lean_ctor_get(v___x_1402_, 0);
lean_inc(v_a_1403_);
lean_dec_ref(v___x_1402_);
v___x_1404_ = lean_unbox(v_a_1403_);
lean_dec(v_a_1403_);
if (v___x_1404_ == 0)
{
lean_dec_ref(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_del_object(v___x_1151_);
lean_del_object(v___x_1147_);
v___y_1335_ = v___y_1391_;
v___y_1336_ = v___y_1392_;
v___y_1337_ = v___y_1393_;
v___y_1338_ = v___y_1394_;
v___y_1339_ = v___y_1395_;
v___y_1340_ = v___y_1398_;
v___y_1341_ = v___y_1399_;
v___y_1342_ = v___y_1400_;
v___y_1343_ = v___y_1401_;
goto v___jp_1334_;
}
else
{
lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1405_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_1406_ = l_Lean_MessageData_ofExpr(v___y_1396_);
if (v_isShared_1152_ == 0)
{
lean_ctor_set_tag(v___x_1151_, 7);
lean_ctor_set(v___x_1151_, 1, v___x_1406_);
lean_ctor_set(v___x_1151_, 0, v___x_1405_);
v___x_1408_ = v___x_1151_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1425_; 
v_reuseFailAlloc_1425_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1425_, 0, v___x_1405_);
lean_ctor_set(v_reuseFailAlloc_1425_, 1, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1425_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1414_; 
v___x_1409_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__19, &l_Lean_Meta_substCore___lam__3___closed__19_once, _init_l_Lean_Meta_substCore___lam__3___closed__19);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
v___x_1411_ = l_Lean_indentExpr(v___y_1397_);
v___x_1412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1410_);
lean_ctor_set(v___x_1412_, 1, v___x_1411_);
if (v_isShared_1148_ == 0)
{
lean_ctor_set(v___x_1147_, 0, v___x_1412_);
v___x_1414_ = v___x_1147_;
goto v_reusejp_1413_;
}
else
{
lean_object* v_reuseFailAlloc_1424_; 
v_reuseFailAlloc_1424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1412_);
v___x_1414_ = v_reuseFailAlloc_1424_;
goto v_reusejp_1413_;
}
v_reusejp_1413_:
{
lean_object* v___x_1415_; 
lean_inc(v_mvarId_1070_);
v___x_1415_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1122_, v_mvarId_1070_, v___x_1414_, v___y_1398_, v___y_1399_, v___y_1400_, v___y_1401_);
if (lean_obj_tag(v___x_1415_) == 0)
{
lean_dec_ref(v___x_1415_);
v___y_1335_ = v___y_1391_;
v___y_1336_ = v___y_1392_;
v___y_1337_ = v___y_1393_;
v___y_1338_ = v___y_1394_;
v___y_1339_ = v___y_1395_;
v___y_1340_ = v___y_1398_;
v___y_1341_ = v___y_1399_;
v___y_1342_ = v___y_1400_;
v___y_1343_ = v___y_1401_;
goto v___jp_1334_;
}
else
{
lean_object* v_a_1416_; lean_object* v___x_1418_; uint8_t v_isShared_1419_; uint8_t v_isSharedCheck_1423_; 
lean_dec(v___y_1401_);
lean_dec_ref(v___y_1400_);
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1395_);
lean_dec(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec(v___y_1391_);
lean_del_object(v___x_1156_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
lean_dec(v_mvarId_1070_);
v_a_1416_ = lean_ctor_get(v___x_1415_, 0);
v_isSharedCheck_1423_ = !lean_is_exclusive(v___x_1415_);
if (v_isSharedCheck_1423_ == 0)
{
v___x_1418_ = v___x_1415_;
v_isShared_1419_ = v_isSharedCheck_1423_;
goto v_resetjp_1417_;
}
else
{
lean_inc(v_a_1416_);
lean_dec(v___x_1415_);
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
}
}
v___jp_1426_:
{
lean_object* v___x_1429_; 
v___x_1429_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1428_, v___y_1078_);
if (lean_obj_tag(v___y_1427_) == 1)
{
lean_object* v_a_1430_; lean_object* v_fvarId_1431_; lean_object* v___x_1432_; lean_object* v___f_1433_; lean_object* v___x_1434_; lean_object* v_a_1435_; uint8_t v___x_1436_; 
lean_dec_ref(v___x_1126_);
v_a_1430_ = lean_ctor_get(v___x_1429_, 0);
lean_inc(v_a_1430_);
lean_dec_ref(v___x_1429_);
v_fvarId_1431_ = lean_ctor_get(v___y_1427_, 0);
lean_inc(v_fvarId_1431_);
v___x_1432_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___f_1433_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__23));
v___x_1434_ = l_Lean_Meta_substCore___lam__0(v___x_1432_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
v_a_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc(v_a_1435_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = lean_unbox(v_a_1435_);
lean_dec(v_a_1435_);
if (v___x_1436_ == 0)
{
lean_inc(v_fvarId_1431_);
v___y_1391_ = v_fvarId_1431_;
v___y_1392_ = v___x_1432_;
v___y_1393_ = v___x_1432_;
v___y_1394_ = v___f_1433_;
v___y_1395_ = v_fvarId_1431_;
v___y_1396_ = v___y_1427_;
v___y_1397_ = v_a_1430_;
v___y_1398_ = v___y_1077_;
v___y_1399_ = v___y_1078_;
v___y_1400_ = v___y_1079_;
v___y_1401_ = v___y_1080_;
goto v___jp_1390_;
}
else
{
lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; 
v___x_1437_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__25, &l_Lean_Meta_substCore___lam__3___closed__25_once, _init_l_Lean_Meta_substCore___lam__3___closed__25);
lean_inc_ref(v___y_1427_);
v___x_1438_ = l_Lean_MessageData_ofExpr(v___y_1427_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__27, &l_Lean_Meta_substCore___lam__3___closed__27_once, _init_l_Lean_Meta_substCore___lam__3___closed__27);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_inc(v_fvarId_1431_);
v___x_1442_ = l_Lean_MessageData_ofName(v_fvarId_1431_);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
v___x_1444_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__29, &l_Lean_Meta_substCore___lam__3___closed__29_once, _init_l_Lean_Meta_substCore___lam__3___closed__29);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
lean_inc(v_a_1430_);
v___x_1446_ = l_Lean_MessageData_ofExpr(v_a_1430_);
v___x_1447_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1447_, 0, v___x_1445_);
lean_ctor_set(v___x_1447_, 1, v___x_1446_);
v___x_1448_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_1432_, v___x_1447_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
if (lean_obj_tag(v___x_1448_) == 0)
{
lean_dec_ref(v___x_1448_);
lean_inc(v_fvarId_1431_);
v___y_1391_ = v_fvarId_1431_;
v___y_1392_ = v___x_1432_;
v___y_1393_ = v___x_1432_;
v___y_1394_ = v___f_1433_;
v___y_1395_ = v_fvarId_1431_;
v___y_1396_ = v___y_1427_;
v___y_1397_ = v_a_1430_;
v___y_1398_ = v___y_1077_;
v___y_1399_ = v___y_1078_;
v___y_1400_ = v___y_1079_;
v___y_1401_ = v___y_1080_;
goto v___jp_1390_;
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
lean_dec(v_fvarId_1431_);
lean_dec(v_a_1430_);
lean_dec_ref(v___y_1427_);
lean_del_object(v___x_1156_);
lean_del_object(v___x_1151_);
lean_del_object(v___x_1147_);
lean_dec(v_a_1121_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
lean_dec(v_mvarId_1070_);
v_a_1449_ = lean_ctor_get(v___x_1448_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1448_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1448_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1448_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1429_);
lean_del_object(v___x_1156_);
lean_del_object(v___x_1151_);
lean_del_object(v___x_1147_);
lean_dec(v_a_1121_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
if (v_symm_1075_ == 0)
{
lean_object* v___x_1457_; 
v___x_1457_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__30));
v___y_1128_ = v___y_1427_;
v___y_1129_ = v___x_1457_;
goto v___jp_1127_;
}
else
{
lean_object* v___x_1458_; 
v___x_1458_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__31));
v___y_1128_ = v___y_1427_;
v___y_1129_ = v___x_1458_;
goto v___jp_1127_;
}
}
}
v___jp_1459_:
{
lean_object* v___x_1461_; 
v___x_1461_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1460_, v___y_1078_);
if (v_symm_1075_ == 0)
{
lean_object* v_a_1462_; 
lean_dec(v_fst_1153_);
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref(v___x_1461_);
v___y_1427_ = v_a_1462_;
v___y_1428_ = v_snd_1154_;
goto v___jp_1426_;
}
else
{
lean_object* v_a_1463_; 
lean_dec(v_snd_1154_);
v_a_1463_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1463_);
lean_dec_ref(v___x_1461_);
v___y_1427_ = v_a_1463_;
v___y_1428_ = v_fst_1153_;
goto v___jp_1426_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec_ref(v___x_1126_);
lean_dec(v_a_1121_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
lean_dec(v_mvarId_1070_);
v_a_1468_ = lean_ctor_get(v___x_1141_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1141_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1141_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1141_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1473_; 
if (v_isShared_1471_ == 0)
{
v___x_1473_ = v___x_1470_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_a_1468_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
v___jp_1127_:
{
lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; 
v___x_1130_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__3, &l_Lean_Meta_substCore___lam__3___closed__3_once, _init_l_Lean_Meta_substCore___lam__3___closed__3);
lean_inc_ref(v___y_1129_);
v___x_1131_ = l_Lean_stringToMessageData(v___y_1129_);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = l_Lean_indentExpr(v___x_1126_);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__5, &l_Lean_Meta_substCore___lam__3___closed__5_once, _init_l_Lean_Meta_substCore___lam__3___closed__5);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = l_Lean_indentExpr(v___y_1128_);
v___x_1138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1136_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1138_);
v___x_1140_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1122_, v_mvarId_1070_, v___x_1139_, v___y_1077_, v___y_1078_, v___y_1079_, v___y_1080_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
return v___x_1140_;
}
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_a_1121_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
lean_dec(v_mvarId_1070_);
v_a_1476_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1124_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1124_);
v___x_1478_ = lean_box(0);
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
v_resetjp_1477_:
{
lean_object* v___x_1481_; 
if (v_isShared_1479_ == 0)
{
v___x_1481_ = v___x_1478_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1482_; 
v_reuseFailAlloc_1482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1482_, 0, v_a_1476_);
v___x_1481_ = v_reuseFailAlloc_1482_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
return v___x_1481_;
}
}
}
}
else
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1491_; 
lean_dec(v_a_1121_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
lean_dec(v_mvarId_1070_);
v_a_1484_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1123_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1123_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1489_; 
if (v_isShared_1487_ == 0)
{
v___x_1489_ = v___x_1486_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1490_; 
v_reuseFailAlloc_1490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1490_, 0, v_a_1484_);
v___x_1489_ = v_reuseFailAlloc_1490_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
return v___x_1489_;
}
}
}
}
else
{
lean_object* v_a_1492_; lean_object* v___x_1494_; uint8_t v_isShared_1495_; uint8_t v_isSharedCheck_1499_; 
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v_fvarSubst_1074_);
lean_dec(v_hFVarId_1071_);
lean_dec(v_mvarId_1070_);
v_a_1492_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1499_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1499_ == 0)
{
v___x_1494_ = v___x_1120_;
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
else
{
lean_inc(v_a_1492_);
lean_dec(v___x_1120_);
v___x_1494_ = lean_box(0);
v_isShared_1495_ = v_isSharedCheck_1499_;
goto v_resetjp_1493_;
}
v_resetjp_1493_:
{
lean_object* v___x_1497_; 
if (v_isShared_1495_ == 0)
{
v___x_1497_ = v___x_1494_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_a_1492_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
v___jp_1082_:
{
if (v_clearH_1073_ == 0)
{
lean_object* v___x_1090_; lean_object* v___x_1091_; 
lean_dec(v___y_1089_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1083_);
v___x_1090_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1090_, 0, v_fvarSubst_1074_);
lean_ctor_set(v___x_1090_, 1, v___y_1088_);
v___x_1091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1091_, 0, v___x_1090_);
return v___x_1091_;
}
else
{
lean_object* v___x_1092_; 
v___x_1092_ = l_Lean_MVarId_clear(v___y_1088_, v___y_1083_, v___y_1086_, v___y_1085_, v___y_1084_, v___y_1089_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1094_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
lean_inc(v_a_1093_);
lean_dec_ref(v___x_1092_);
v___x_1094_ = l_Lean_MVarId_clear(v_a_1093_, v___y_1087_, v___y_1086_, v___y_1085_, v___y_1084_, v___y_1089_);
lean_dec(v___y_1089_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1086_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1103_; 
v_a_1095_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1097_ = v___x_1094_;
v_isShared_1098_ = v_isSharedCheck_1103_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1094_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1103_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1099_; lean_object* v___x_1101_; 
v___x_1099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1099_, 0, v_fvarSubst_1074_);
lean_ctor_set(v___x_1099_, 1, v_a_1095_);
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1099_);
v___x_1101_ = v___x_1097_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1102_; 
v_reuseFailAlloc_1102_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1102_, 0, v___x_1099_);
v___x_1101_ = v_reuseFailAlloc_1102_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
return v___x_1101_;
}
}
}
else
{
lean_object* v_a_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1111_; 
lean_dec(v_fvarSubst_1074_);
v_a_1104_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1111_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1111_ == 0)
{
v___x_1106_ = v___x_1094_;
v_isShared_1107_ = v_isSharedCheck_1111_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_a_1104_);
lean_dec(v___x_1094_);
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
lean_dec(v___y_1089_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v_fvarSubst_1074_);
v_a_1112_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1119_ == 0)
{
v___x_1114_ = v___x_1092_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_inc(v_a_1112_);
lean_dec(v___x_1092_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3___boxed(lean_object* v_mvarId_1500_, lean_object* v_hFVarId_1501_, lean_object* v___x_1502_, lean_object* v_clearH_1503_, lean_object* v_fvarSubst_1504_, lean_object* v_symm_1505_, lean_object* v_tryToSkip_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_){
_start:
{
uint8_t v_clearH_boxed_1512_; uint8_t v_symm_boxed_1513_; uint8_t v_tryToSkip_boxed_1514_; lean_object* v_res_1515_; 
v_clearH_boxed_1512_ = lean_unbox(v_clearH_1503_);
v_symm_boxed_1513_ = lean_unbox(v_symm_1505_);
v_tryToSkip_boxed_1514_ = lean_unbox(v_tryToSkip_1506_);
v_res_1515_ = l_Lean_Meta_substCore___lam__3(v_mvarId_1500_, v_hFVarId_1501_, v___x_1502_, v_clearH_boxed_1512_, v_fvarSubst_1504_, v_symm_boxed_1513_, v_tryToSkip_boxed_1514_, v___y_1507_, v___y_1508_, v___y_1509_, v___y_1510_);
lean_dec(v___x_1502_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object* v_mvarId_1516_, lean_object* v_hFVarId_1517_, uint8_t v_symm_1518_, lean_object* v_fvarSubst_1519_, uint8_t v_clearH_1520_, uint8_t v_tryToSkip_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___f_1531_; lean_object* v___x_1532_; 
v___x_1527_ = lean_box(0);
v___x_1528_ = lean_box(v_clearH_1520_);
v___x_1529_ = lean_box(v_symm_1518_);
v___x_1530_ = lean_box(v_tryToSkip_1521_);
lean_inc(v_mvarId_1516_);
v___f_1531_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__3___boxed), 12, 7);
lean_closure_set(v___f_1531_, 0, v_mvarId_1516_);
lean_closure_set(v___f_1531_, 1, v_hFVarId_1517_);
lean_closure_set(v___f_1531_, 2, v___x_1527_);
lean_closure_set(v___f_1531_, 3, v___x_1528_);
lean_closure_set(v___f_1531_, 4, v_fvarSubst_1519_);
lean_closure_set(v___f_1531_, 5, v___x_1529_);
lean_closure_set(v___f_1531_, 6, v___x_1530_);
v___x_1532_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1516_, v___f_1531_, v_a_1522_, v_a_1523_, v_a_1524_, v_a_1525_);
return v___x_1532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* v_mvarId_1533_, lean_object* v_hFVarId_1534_, lean_object* v_symm_1535_, lean_object* v_fvarSubst_1536_, lean_object* v_clearH_1537_, lean_object* v_tryToSkip_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_){
_start:
{
uint8_t v_symm_boxed_1544_; uint8_t v_clearH_boxed_1545_; uint8_t v_tryToSkip_boxed_1546_; lean_object* v_res_1547_; 
v_symm_boxed_1544_ = lean_unbox(v_symm_1535_);
v_clearH_boxed_1545_ = lean_unbox(v_clearH_1537_);
v_tryToSkip_boxed_1546_ = lean_unbox(v_tryToSkip_1538_);
v_res_1547_ = l_Lean_Meta_substCore(v_mvarId_1533_, v_hFVarId_1534_, v_symm_boxed_1544_, v_fvarSubst_1536_, v_clearH_boxed_1545_, v_tryToSkip_boxed_1546_, v_a_1539_, v_a_1540_, v_a_1541_, v_a_1542_);
lean_dec(v_a_1542_);
lean_dec_ref(v_a_1541_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(lean_object* v_fst_1548_, lean_object* v_fst_1549_, lean_object* v_n_1550_, lean_object* v_i_1551_, lean_object* v_a_1552_, lean_object* v_a_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_, lean_object* v___y_1556_, lean_object* v___y_1557_){
_start:
{
lean_object* v___x_1559_; 
v___x_1559_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_1548_, v_fst_1549_, v_n_1550_, v_i_1551_, v_a_1553_);
return v___x_1559_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___boxed(lean_object* v_fst_1560_, lean_object* v_fst_1561_, lean_object* v_n_1562_, lean_object* v_i_1563_, lean_object* v_a_1564_, lean_object* v_a_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(v_fst_1560_, v_fst_1561_, v_n_1562_, v_i_1563_, v_a_1564_, v_a_1565_, v___y_1566_, v___y_1567_, v___y_1568_, v___y_1569_);
lean_dec(v___y_1569_);
lean_dec_ref(v___y_1568_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v_n_1562_);
lean_dec_ref(v_fst_1561_);
lean_dec_ref(v_fst_1560_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(lean_object* v_mvarId_1572_, lean_object* v_val_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_){
_start:
{
lean_object* v___x_1579_; 
v___x_1579_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_mvarId_1572_, v_val_1573_, v___y_1575_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___boxed(lean_object* v_mvarId_1580_, lean_object* v_val_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_, lean_object* v___y_1585_, lean_object* v___y_1586_){
_start:
{
lean_object* v_res_1587_; 
v_res_1587_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(v_mvarId_1580_, v_val_1581_, v___y_1582_, v___y_1583_, v___y_1584_, v___y_1585_);
lean_dec(v___y_1585_);
lean_dec_ref(v___y_1584_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
return v_res_1587_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(lean_object* v_00_u03b1_1588_, lean_object* v_name_1589_, uint8_t v_bi_1590_, lean_object* v_type_1591_, lean_object* v_k_1592_, uint8_t v_kind_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_, lean_object* v___y_1596_, lean_object* v___y_1597_){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_1589_, v_bi_1590_, v_type_1591_, v_k_1592_, v_kind_1593_, v___y_1594_, v___y_1595_, v___y_1596_, v___y_1597_);
return v___x_1599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1600_, lean_object* v_name_1601_, lean_object* v_bi_1602_, lean_object* v_type_1603_, lean_object* v_k_1604_, lean_object* v_kind_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
uint8_t v_bi_boxed_1611_; uint8_t v_kind_boxed_1612_; lean_object* v_res_1613_; 
v_bi_boxed_1611_ = lean_unbox(v_bi_1602_);
v_kind_boxed_1612_ = lean_unbox(v_kind_1605_);
v_res_1613_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(v_00_u03b1_1600_, v_name_1601_, v_bi_boxed_1611_, v_type_1603_, v_k_1604_, v_kind_boxed_1612_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(lean_object* v_00_u03b1_1614_, lean_object* v_name_1615_, lean_object* v_type_1616_, lean_object* v_k_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; 
v___x_1623_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v_name_1615_, v_type_1616_, v_k_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
return v___x_1623_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___boxed(lean_object* v_00_u03b1_1624_, lean_object* v_name_1625_, lean_object* v_type_1626_, lean_object* v_k_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_, lean_object* v___y_1631_, lean_object* v___y_1632_){
_start:
{
lean_object* v_res_1633_; 
v_res_1633_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(v_00_u03b1_1624_, v_name_1625_, v_type_1626_, v_k_1627_, v___y_1628_, v___y_1629_, v___y_1630_, v___y_1631_);
lean_dec(v___y_1631_);
lean_dec_ref(v___y_1630_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
return v_res_1633_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6(lean_object* v_00_u03b2_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_, lean_object* v_x_1637_){
_start:
{
lean_object* v___x_1638_; 
v___x_1638_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_x_1635_, v_x_1636_, v_x_1637_);
return v___x_1638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1639_, lean_object* v_x_1640_, size_t v_x_1641_, size_t v_x_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_){
_start:
{
lean_object* v___x_1645_; 
v___x_1645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_1640_, v_x_1641_, v_x_1642_, v_x_1643_, v_x_1644_);
return v___x_1645_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_, lean_object* v_x_1650_, lean_object* v_x_1651_){
_start:
{
size_t v_x_35638__boxed_1652_; size_t v_x_35639__boxed_1653_; lean_object* v_res_1654_; 
v_x_35638__boxed_1652_ = lean_unbox_usize(v_x_1648_);
lean_dec(v_x_1648_);
v_x_35639__boxed_1653_ = lean_unbox_usize(v_x_1649_);
lean_dec(v_x_1649_);
v_res_1654_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(v_00_u03b2_1646_, v_x_1647_, v_x_35638__boxed_1652_, v_x_35639__boxed_1653_, v_x_1650_, v_x_1651_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13(lean_object* v_00_u03b2_1655_, lean_object* v_n_1656_, lean_object* v_k_1657_, lean_object* v_v_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v_n_1656_, v_k_1657_, v_v_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1660_, size_t v_depth_1661_, lean_object* v_keys_1662_, lean_object* v_vals_1663_, lean_object* v_heq_1664_, lean_object* v_i_1665_, lean_object* v_entries_1666_){
_start:
{
lean_object* v___x_1667_; 
v___x_1667_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_1661_, v_keys_1662_, v_vals_1663_, v_i_1665_, v_entries_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1668_, lean_object* v_depth_1669_, lean_object* v_keys_1670_, lean_object* v_vals_1671_, lean_object* v_heq_1672_, lean_object* v_i_1673_, lean_object* v_entries_1674_){
_start:
{
size_t v_depth_boxed_1675_; lean_object* v_res_1676_; 
v_depth_boxed_1675_ = lean_unbox_usize(v_depth_1669_);
lean_dec(v_depth_1669_);
v_res_1676_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(v_00_u03b2_1668_, v_depth_boxed_1675_, v_keys_1670_, v_vals_1671_, v_heq_1672_, v_i_1673_, v_entries_1674_);
lean_dec_ref(v_vals_1671_);
lean_dec_ref(v_keys_1670_);
return v_res_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_, lean_object* v_x_1680_, lean_object* v_x_1681_){
_start:
{
lean_object* v___x_1682_; 
v___x_1682_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(v_x_1678_, v_x_1679_, v_x_1680_, v_x_1681_);
return v___x_1682_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* v_fvarId_1686_, lean_object* v_mvarId_1687_, uint8_t v_tryToClear_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_, lean_object* v___y_1691_, lean_object* v___y_1692_){
_start:
{
lean_object* v___x_1694_; 
lean_inc(v_fvarId_1686_);
v___x_1694_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1686_, v___y_1689_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_a_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; 
v_a_1695_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_a_1695_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = l_Lean_LocalDecl_type(v_a_1695_);
lean_inc(v___y_1692_);
lean_inc_ref(v___y_1691_);
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
v___x_1697_ = lean_whnf(v___x_1696_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1697_) == 0)
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1782_; 
v_a_1698_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1700_ = v___x_1697_;
v_isShared_1701_ = v_isSharedCheck_1782_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1697_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1782_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; uint8_t v___x_1704_; 
v___x_1702_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_1703_ = lean_unsigned_to_nat(4u);
v___x_1704_ = l_Lean_Expr_isAppOfArity(v_a_1698_, v___x_1702_, v___x_1703_);
if (v___x_1704_ == 0)
{
lean_object* v___x_1705_; lean_object* v___x_1707_; 
lean_dec(v_a_1698_);
lean_dec(v_a_1695_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
v___x_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1705_, 0, v_fvarId_1686_);
lean_ctor_set(v___x_1705_, 1, v_mvarId_1687_);
if (v_isShared_1701_ == 0)
{
lean_ctor_set(v___x_1700_, 0, v___x_1705_);
v___x_1707_ = v___x_1700_;
goto v_reusejp_1706_;
}
else
{
lean_object* v_reuseFailAlloc_1708_; 
v_reuseFailAlloc_1708_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1708_, 0, v___x_1705_);
v___x_1707_ = v_reuseFailAlloc_1708_;
goto v_reusejp_1706_;
}
v_reusejp_1706_:
{
return v___x_1707_;
}
}
else
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
lean_del_object(v___x_1700_);
v___x_1709_ = l_Lean_Expr_appFn_x21(v_a_1698_);
v___x_1710_ = l_Lean_Expr_appFn_x21(v___x_1709_);
v___x_1711_ = l_Lean_Expr_appFn_x21(v___x_1710_);
v___x_1712_ = l_Lean_Expr_appArg_x21(v___x_1711_);
lean_dec_ref(v___x_1711_);
v___x_1713_ = l_Lean_Expr_appArg_x21(v___x_1709_);
lean_dec_ref(v___x_1709_);
v___x_1714_ = l_Lean_Meta_isExprDefEq(v___x_1712_, v___x_1713_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1773_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1717_ = v___x_1714_;
v_isShared_1718_ = v_isSharedCheck_1773_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1714_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1773_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
uint8_t v___x_1719_; 
v___x_1719_ = lean_unbox(v_a_1715_);
if (v___x_1719_ == 0)
{
lean_object* v___x_1720_; lean_object* v___x_1722_; 
lean_dec(v_a_1715_);
lean_dec_ref(v___x_1710_);
lean_dec(v_a_1698_);
lean_dec(v_a_1695_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v_fvarId_1686_);
lean_ctor_set(v___x_1720_, 1, v_mvarId_1687_);
if (v_isShared_1718_ == 0)
{
lean_ctor_set(v___x_1717_, 0, v___x_1720_);
v___x_1722_ = v___x_1717_;
goto v_reusejp_1721_;
}
else
{
lean_object* v_reuseFailAlloc_1723_; 
v_reuseFailAlloc_1723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1723_, 0, v___x_1720_);
v___x_1722_ = v_reuseFailAlloc_1723_;
goto v_reusejp_1721_;
}
v_reusejp_1721_:
{
return v___x_1722_;
}
}
else
{
lean_object* v___x_1724_; lean_object* v___x_1725_; 
lean_del_object(v___x_1717_);
lean_inc(v_fvarId_1686_);
v___x_1724_ = l_Lean_mkFVar(v_fvarId_1686_);
v___x_1725_ = l_Lean_Meta_mkEqOfHEq(v___x_1724_, v___x_1704_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1725_) == 0)
{
lean_object* v_a_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; 
v_a_1726_ = lean_ctor_get(v___x_1725_, 0);
lean_inc(v_a_1726_);
lean_dec_ref(v___x_1725_);
v___x_1727_ = l_Lean_Expr_appArg_x21(v___x_1710_);
lean_dec_ref(v___x_1710_);
v___x_1728_ = l_Lean_Expr_appArg_x21(v_a_1698_);
lean_dec(v_a_1698_);
v___x_1729_ = l_Lean_Meta_mkEq(v___x_1727_, v___x_1728_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref(v___x_1729_);
v___x_1731_ = l_Lean_LocalDecl_userName(v_a_1695_);
lean_dec(v_a_1695_);
v___x_1732_ = l_Lean_MVarId_assert(v_mvarId_1687_, v___x_1731_, v_a_1730_, v_a_1726_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1732_) == 0)
{
if (v_tryToClear_1688_ == 0)
{
lean_object* v_a_1733_; uint8_t v___x_1734_; lean_object* v___x_1735_; 
lean_dec(v_fvarId_1686_);
v_a_1733_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1733_);
lean_dec_ref(v___x_1732_);
v___x_1734_ = lean_unbox(v_a_1715_);
lean_dec(v_a_1715_);
v___x_1735_ = l_Lean_Meta_intro1Core(v_a_1733_, v___x_1734_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v___x_1735_;
}
else
{
lean_object* v_a_1736_; lean_object* v___x_1737_; 
v_a_1736_ = lean_ctor_get(v___x_1732_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1732_);
v___x_1737_ = l_Lean_MVarId_tryClear(v_a_1736_, v_fvarId_1686_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
if (lean_obj_tag(v___x_1737_) == 0)
{
lean_object* v_a_1738_; uint8_t v___x_1739_; lean_object* v___x_1740_; 
v_a_1738_ = lean_ctor_get(v___x_1737_, 0);
lean_inc(v_a_1738_);
lean_dec_ref(v___x_1737_);
v___x_1739_ = lean_unbox(v_a_1715_);
lean_dec(v_a_1715_);
v___x_1740_ = l_Lean_Meta_intro1Core(v_a_1738_, v___x_1739_, v___y_1689_, v___y_1690_, v___y_1691_, v___y_1692_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
return v___x_1740_;
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_a_1715_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
v_a_1741_ = lean_ctor_get(v___x_1737_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1737_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1737_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1737_);
v___x_1743_ = lean_box(0);
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
v_resetjp_1742_:
{
lean_object* v___x_1746_; 
if (v_isShared_1744_ == 0)
{
v___x_1746_ = v___x_1743_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_a_1741_);
v___x_1746_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
return v___x_1746_;
}
}
}
}
}
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v_a_1715_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_fvarId_1686_);
v_a_1749_ = lean_ctor_get(v___x_1732_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1732_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1732_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1732_);
v___x_1751_ = lean_box(0);
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
v_resetjp_1750_:
{
lean_object* v___x_1754_; 
if (v_isShared_1752_ == 0)
{
v___x_1754_ = v___x_1751_;
goto v_reusejp_1753_;
}
else
{
lean_object* v_reuseFailAlloc_1755_; 
v_reuseFailAlloc_1755_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1755_, 0, v_a_1749_);
v___x_1754_ = v_reuseFailAlloc_1755_;
goto v_reusejp_1753_;
}
v_reusejp_1753_:
{
return v___x_1754_;
}
}
}
}
else
{
lean_object* v_a_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1764_; 
lean_dec(v_a_1726_);
lean_dec(v_a_1715_);
lean_dec(v_a_1695_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_mvarId_1687_);
lean_dec(v_fvarId_1686_);
v_a_1757_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1729_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1729_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1762_; 
if (v_isShared_1760_ == 0)
{
v___x_1762_ = v___x_1759_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v_a_1757_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
}
else
{
lean_object* v_a_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1772_; 
lean_dec(v_a_1715_);
lean_dec_ref(v___x_1710_);
lean_dec(v_a_1698_);
lean_dec(v_a_1695_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_mvarId_1687_);
lean_dec(v_fvarId_1686_);
v_a_1765_ = lean_ctor_get(v___x_1725_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1725_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1767_ = v___x_1725_;
v_isShared_1768_ = v_isSharedCheck_1772_;
goto v_resetjp_1766_;
}
else
{
lean_inc(v_a_1765_);
lean_dec(v___x_1725_);
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
lean_dec_ref(v___x_1710_);
lean_dec(v_a_1698_);
lean_dec(v_a_1695_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_mvarId_1687_);
lean_dec(v_fvarId_1686_);
v_a_1774_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1781_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1781_ == 0)
{
v___x_1776_ = v___x_1714_;
v_isShared_1777_ = v_isSharedCheck_1781_;
goto v_resetjp_1775_;
}
else
{
lean_inc(v_a_1774_);
lean_dec(v___x_1714_);
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
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v_a_1695_);
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_mvarId_1687_);
lean_dec(v_fvarId_1686_);
v_a_1783_ = lean_ctor_get(v___x_1697_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1697_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1697_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1697_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
else
{
lean_object* v_a_1791_; lean_object* v___x_1793_; uint8_t v_isShared_1794_; uint8_t v_isSharedCheck_1798_; 
lean_dec(v___y_1692_);
lean_dec_ref(v___y_1691_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v_mvarId_1687_);
lean_dec(v_fvarId_1686_);
v_a_1791_ = lean_ctor_get(v___x_1694_, 0);
v_isSharedCheck_1798_ = !lean_is_exclusive(v___x_1694_);
if (v_isSharedCheck_1798_ == 0)
{
v___x_1793_ = v___x_1694_;
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
else
{
lean_inc(v_a_1791_);
lean_dec(v___x_1694_);
v___x_1793_ = lean_box(0);
v_isShared_1794_ = v_isSharedCheck_1798_;
goto v_resetjp_1792_;
}
v_resetjp_1792_:
{
lean_object* v___x_1796_; 
if (v_isShared_1794_ == 0)
{
v___x_1796_ = v___x_1793_;
goto v_reusejp_1795_;
}
else
{
lean_object* v_reuseFailAlloc_1797_; 
v_reuseFailAlloc_1797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1797_, 0, v_a_1791_);
v___x_1796_ = v_reuseFailAlloc_1797_;
goto v_reusejp_1795_;
}
v_reusejp_1795_:
{
return v___x_1796_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object* v_fvarId_1799_, lean_object* v_mvarId_1800_, lean_object* v_tryToClear_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_, lean_object* v___y_1805_, lean_object* v___y_1806_){
_start:
{
uint8_t v_tryToClear_boxed_1807_; lean_object* v_res_1808_; 
v_tryToClear_boxed_1807_ = lean_unbox(v_tryToClear_1801_);
v_res_1808_ = l_Lean_Meta_heqToEq___lam__0(v_fvarId_1799_, v_mvarId_1800_, v_tryToClear_boxed_1807_, v___y_1802_, v___y_1803_, v___y_1804_, v___y_1805_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object* v_mvarId_1809_, lean_object* v_fvarId_1810_, uint8_t v_tryToClear_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_, lean_object* v_a_1814_, lean_object* v_a_1815_){
_start:
{
lean_object* v___x_1817_; lean_object* v___f_1818_; lean_object* v___x_1819_; 
v___x_1817_ = lean_box(v_tryToClear_1811_);
lean_inc(v_mvarId_1809_);
v___f_1818_ = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1818_, 0, v_fvarId_1810_);
lean_closure_set(v___f_1818_, 1, v_mvarId_1809_);
lean_closure_set(v___f_1818_, 2, v___x_1817_);
v___x_1819_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1809_, v___f_1818_, v_a_1812_, v_a_1813_, v_a_1814_, v_a_1815_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* v_mvarId_1820_, lean_object* v_fvarId_1821_, lean_object* v_tryToClear_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
uint8_t v_tryToClear_boxed_1828_; lean_object* v_res_1829_; 
v_tryToClear_boxed_1828_ = lean_unbox(v_tryToClear_1822_);
v_res_1829_ = l_Lean_Meta_heqToEq(v_mvarId_1820_, v_fvarId_1821_, v_tryToClear_boxed_1828_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1833_, lean_object* v_as_1834_, size_t v_sz_1835_, size_t v_i_1836_, lean_object* v_b_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_){
_start:
{
lean_object* v_a_1844_; uint8_t v___x_1848_; 
v___x_1848_ = lean_usize_dec_lt(v_i_1836_, v_sz_1835_);
if (v___x_1848_ == 0)
{
lean_object* v___x_1849_; 
lean_dec(v_x_1833_);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v_b_1837_);
return v___x_1849_;
}
else
{
lean_object* v___x_1850_; lean_object* v_a_1852_; lean_object* v___x_1856_; lean_object* v_a_1857_; 
lean_dec_ref(v_b_1837_);
v___x_1850_ = lean_box(0);
v___x_1856_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1857_ = lean_array_uget(v_as_1834_, v_i_1836_);
if (lean_obj_tag(v_a_1857_) == 0)
{
v_a_1844_ = v___x_1856_;
goto v___jp_1843_;
}
else
{
lean_object* v_val_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1945_; 
v_val_1858_ = lean_ctor_get(v_a_1857_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v_a_1857_);
if (v_isSharedCheck_1945_ == 0)
{
v___x_1860_ = v_a_1857_;
v_isShared_1861_ = v_isSharedCheck_1945_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_val_1858_);
lean_dec(v_a_1857_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1945_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
uint8_t v___x_1869_; 
v___x_1869_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1858_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1875_; lean_object* v___x_1876_; 
v___x_1875_ = l_Lean_LocalDecl_type(v_val_1858_);
v___x_1876_ = l_Lean_Meta_matchEq_x3f(v___x_1875_, v___y_1838_, v___y_1839_, v___y_1840_, v___y_1841_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref(v___x_1876_);
if (lean_obj_tag(v_a_1877_) == 1)
{
lean_object* v_val_1878_; lean_object* v_snd_1879_; lean_object* v_fst_1880_; lean_object* v_snd_1881_; lean_object* v___x_1882_; 
v_val_1878_ = lean_ctor_get(v_a_1877_, 0);
lean_inc(v_val_1878_);
lean_dec_ref(v_a_1877_);
v_snd_1879_ = lean_ctor_get(v_val_1878_, 1);
lean_inc(v_snd_1879_);
lean_dec(v_val_1878_);
v_fst_1880_ = lean_ctor_get(v_snd_1879_, 0);
lean_inc(v_fst_1880_);
v_snd_1881_ = lean_ctor_get(v_snd_1879_, 1);
lean_inc(v_snd_1881_);
lean_dec(v_snd_1879_);
v___x_1882_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1880_, v___y_1839_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___x_1884_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v___x_1884_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1881_, v___y_1839_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; lean_object* v___y_1887_; uint8_t v___y_1888_; lean_object* v___y_1901_; uint8_t v___y_1906_; uint8_t v___x_1918_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref(v___x_1884_);
v___x_1918_ = l_Lean_Expr_isFVar(v_a_1885_);
if (v___x_1918_ == 0)
{
v___y_1906_ = v___x_1918_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_1919_; uint8_t v___x_1920_; 
v___x_1919_ = l_Lean_Expr_fvarId_x21(v_a_1885_);
v___x_1920_ = l_Lean_instBEqFVarId_beq(v___x_1919_, v_x_1833_);
lean_dec(v___x_1919_);
v___y_1906_ = v___x_1920_;
goto v___jp_1905_;
}
v___jp_1886_:
{
if (v___y_1888_ == 0)
{
lean_dec(v_a_1885_);
lean_dec(v_val_1858_);
v_a_1844_ = v___x_1856_;
goto v___jp_1843_;
}
else
{
lean_object* v___x_1889_; 
lean_inc(v_x_1833_);
v___x_1889_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1885_, v_x_1833_, v___y_1887_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; uint8_t v___x_1891_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref(v___x_1889_);
v___x_1891_ = lean_unbox(v_a_1890_);
lean_dec(v_a_1890_);
if (v___x_1891_ == 0)
{
lean_dec(v_x_1833_);
goto v___jp_1870_;
}
else
{
if (v___x_1869_ == 0)
{
lean_dec(v_val_1858_);
v_a_1844_ = v___x_1856_;
goto v___jp_1843_;
}
else
{
lean_dec(v_x_1833_);
goto v___jp_1870_;
}
}
}
else
{
lean_object* v_a_1892_; lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1899_; 
lean_dec(v_val_1858_);
lean_dec(v_x_1833_);
v_a_1892_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1899_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1899_ == 0)
{
v___x_1894_ = v___x_1889_;
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
else
{
lean_inc(v_a_1892_);
lean_dec(v___x_1889_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1899_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v___x_1897_; 
if (v_isShared_1895_ == 0)
{
v___x_1897_ = v___x_1894_;
goto v_reusejp_1896_;
}
else
{
lean_object* v_reuseFailAlloc_1898_; 
v_reuseFailAlloc_1898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1898_, 0, v_a_1892_);
v___x_1897_ = v_reuseFailAlloc_1898_;
goto v_reusejp_1896_;
}
v_reusejp_1896_:
{
return v___x_1897_;
}
}
}
}
}
v___jp_1900_:
{
uint8_t v___x_1902_; 
v___x_1902_ = l_Lean_Expr_isFVar(v_a_1883_);
if (v___x_1902_ == 0)
{
lean_dec(v_a_1883_);
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___x_1902_;
goto v___jp_1886_;
}
else
{
lean_object* v___x_1903_; uint8_t v___x_1904_; 
v___x_1903_ = l_Lean_Expr_fvarId_x21(v_a_1883_);
lean_dec(v_a_1883_);
v___x_1904_ = l_Lean_instBEqFVarId_beq(v___x_1903_, v_x_1833_);
lean_dec(v___x_1903_);
v___y_1887_ = v___y_1901_;
v___y_1888_ = v___x_1904_;
goto v___jp_1886_;
}
}
v___jp_1905_:
{
if (v___y_1906_ == 0)
{
lean_del_object(v___x_1860_);
v___y_1901_ = v___y_1839_;
goto v___jp_1900_;
}
else
{
lean_object* v___x_1907_; 
lean_inc(v_x_1833_);
lean_inc(v_a_1883_);
v___x_1907_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1883_, v_x_1833_, v___y_1839_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v_a_1908_; uint8_t v___x_1909_; 
v_a_1908_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_a_1908_);
lean_dec_ref(v___x_1907_);
v___x_1909_ = lean_unbox(v_a_1908_);
lean_dec(v_a_1908_);
if (v___x_1909_ == 0)
{
lean_dec(v_a_1885_);
lean_dec(v_a_1883_);
lean_dec(v_x_1833_);
goto v___jp_1862_;
}
else
{
if (v___x_1869_ == 0)
{
lean_del_object(v___x_1860_);
v___y_1901_ = v___y_1839_;
goto v___jp_1900_;
}
else
{
lean_dec(v_a_1885_);
lean_dec(v_a_1883_);
lean_dec(v_x_1833_);
goto v___jp_1862_;
}
}
}
else
{
lean_object* v_a_1910_; lean_object* v___x_1912_; uint8_t v_isShared_1913_; uint8_t v_isSharedCheck_1917_; 
lean_dec(v_a_1885_);
lean_dec(v_a_1883_);
lean_del_object(v___x_1860_);
lean_dec(v_val_1858_);
lean_dec(v_x_1833_);
v_a_1910_ = lean_ctor_get(v___x_1907_, 0);
v_isSharedCheck_1917_ = !lean_is_exclusive(v___x_1907_);
if (v_isSharedCheck_1917_ == 0)
{
v___x_1912_ = v___x_1907_;
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
else
{
lean_inc(v_a_1910_);
lean_dec(v___x_1907_);
v___x_1912_ = lean_box(0);
v_isShared_1913_ = v_isSharedCheck_1917_;
goto v_resetjp_1911_;
}
v_resetjp_1911_:
{
lean_object* v___x_1915_; 
if (v_isShared_1913_ == 0)
{
v___x_1915_ = v___x_1912_;
goto v_reusejp_1914_;
}
else
{
lean_object* v_reuseFailAlloc_1916_; 
v_reuseFailAlloc_1916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1910_);
v___x_1915_ = v_reuseFailAlloc_1916_;
goto v_reusejp_1914_;
}
v_reusejp_1914_:
{
return v___x_1915_;
}
}
}
}
}
}
else
{
lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_a_1883_);
lean_del_object(v___x_1860_);
lean_dec(v_val_1858_);
lean_dec(v_x_1833_);
v_a_1921_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1884_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1884_);
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
lean_dec(v_snd_1881_);
lean_del_object(v___x_1860_);
lean_dec(v_val_1858_);
lean_dec(v_x_1833_);
v_a_1929_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1882_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1882_);
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
else
{
lean_dec(v_a_1877_);
lean_del_object(v___x_1860_);
lean_dec(v_val_1858_);
v_a_1844_ = v___x_1856_;
goto v___jp_1843_;
}
}
else
{
lean_object* v_a_1937_; lean_object* v___x_1939_; uint8_t v_isShared_1940_; uint8_t v_isSharedCheck_1944_; 
lean_del_object(v___x_1860_);
lean_dec(v_val_1858_);
lean_dec(v_x_1833_);
v_a_1937_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1944_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1944_ == 0)
{
v___x_1939_ = v___x_1876_;
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
else
{
lean_inc(v_a_1937_);
lean_dec(v___x_1876_);
v___x_1939_ = lean_box(0);
v_isShared_1940_ = v_isSharedCheck_1944_;
goto v_resetjp_1938_;
}
v_resetjp_1938_:
{
lean_object* v___x_1942_; 
if (v_isShared_1940_ == 0)
{
v___x_1942_ = v___x_1939_;
goto v_reusejp_1941_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_a_1937_);
v___x_1942_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1941_;
}
v_reusejp_1941_:
{
return v___x_1942_;
}
}
}
}
else
{
lean_del_object(v___x_1860_);
lean_dec(v_val_1858_);
v_a_1844_ = v___x_1856_;
goto v___jp_1843_;
}
v___jp_1862_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1867_; 
v___x_1863_ = l_Lean_LocalDecl_fvarId(v_val_1858_);
lean_dec(v_val_1858_);
v___x_1864_ = lean_box(v___x_1848_);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
if (v_isShared_1861_ == 0)
{
lean_ctor_set(v___x_1860_, 0, v___x_1865_);
v___x_1867_ = v___x_1860_;
goto v_reusejp_1866_;
}
else
{
lean_object* v_reuseFailAlloc_1868_; 
v_reuseFailAlloc_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1868_, 0, v___x_1865_);
v___x_1867_ = v_reuseFailAlloc_1868_;
goto v_reusejp_1866_;
}
v_reusejp_1866_:
{
v_a_1852_ = v___x_1867_;
goto v___jp_1851_;
}
}
v___jp_1870_:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1871_ = l_Lean_LocalDecl_fvarId(v_val_1858_);
lean_dec(v_val_1858_);
v___x_1872_ = lean_box(v___x_1869_);
v___x_1873_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1873_, 0, v___x_1871_);
lean_ctor_set(v___x_1873_, 1, v___x_1872_);
v___x_1874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1874_, 0, v___x_1873_);
v_a_1852_ = v___x_1874_;
goto v___jp_1851_;
}
}
}
v___jp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1853_, 0, v_a_1852_);
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1850_);
v___x_1855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
return v___x_1855_;
}
}
v___jp_1843_:
{
size_t v___x_1845_; size_t v___x_1846_; 
v___x_1845_ = ((size_t)1ULL);
v___x_1846_ = lean_usize_add(v_i_1836_, v___x_1845_);
lean_inc_ref(v_a_1844_);
v_i_1836_ = v___x_1846_;
v_b_1837_ = v_a_1844_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1946_, lean_object* v_as_1947_, lean_object* v_sz_1948_, lean_object* v_i_1949_, lean_object* v_b_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
size_t v_sz_boxed_1956_; size_t v_i_boxed_1957_; lean_object* v_res_1958_; 
v_sz_boxed_1956_ = lean_unbox_usize(v_sz_1948_);
lean_dec(v_sz_1948_);
v_i_boxed_1957_ = lean_unbox_usize(v_i_1949_);
lean_dec(v_i_1949_);
v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1946_, v_as_1947_, v_sz_boxed_1956_, v_i_boxed_1957_, v_b_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec_ref(v_as_1947_);
return v_res_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object* v_x_1959_, lean_object* v_as_1960_, size_t v_sz_1961_, size_t v_i_1962_, lean_object* v_b_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_, lean_object* v___y_1966_, lean_object* v___y_1967_){
_start:
{
lean_object* v_a_1970_; uint8_t v___x_1974_; 
v___x_1974_ = lean_usize_dec_lt(v_i_1962_, v_sz_1961_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; 
lean_dec(v_x_1959_);
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v_b_1963_);
return v___x_1975_;
}
else
{
lean_object* v___x_1976_; lean_object* v_a_1978_; lean_object* v___x_1982_; lean_object* v_a_1983_; 
lean_dec_ref(v_b_1963_);
v___x_1976_ = lean_box(0);
v___x_1982_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1983_ = lean_array_uget(v_as_1960_, v_i_1962_);
if (lean_obj_tag(v_a_1983_) == 0)
{
v_a_1970_ = v___x_1982_;
goto v___jp_1969_;
}
else
{
lean_object* v_val_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_2071_; 
v_val_1984_ = lean_ctor_get(v_a_1983_, 0);
v_isSharedCheck_2071_ = !lean_is_exclusive(v_a_1983_);
if (v_isSharedCheck_2071_ == 0)
{
v___x_1986_ = v_a_1983_;
v_isShared_1987_ = v_isSharedCheck_2071_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_val_1984_);
lean_dec(v_a_1983_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_2071_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
uint8_t v___x_1995_; 
v___x_1995_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1984_);
if (v___x_1995_ == 0)
{
lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2001_ = l_Lean_LocalDecl_type(v_val_1984_);
v___x_2002_ = l_Lean_Meta_matchEq_x3f(v___x_2001_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref(v___x_2002_);
if (lean_obj_tag(v_a_2003_) == 1)
{
lean_object* v_val_2004_; lean_object* v_snd_2005_; lean_object* v_fst_2006_; lean_object* v_snd_2007_; lean_object* v___x_2008_; 
v_val_2004_ = lean_ctor_get(v_a_2003_, 0);
lean_inc(v_val_2004_);
lean_dec_ref(v_a_2003_);
v_snd_2005_ = lean_ctor_get(v_val_2004_, 1);
lean_inc(v_snd_2005_);
lean_dec(v_val_2004_);
v_fst_2006_ = lean_ctor_get(v_snd_2005_, 0);
lean_inc(v_fst_2006_);
v_snd_2007_ = lean_ctor_get(v_snd_2005_, 1);
lean_inc(v_snd_2007_);
lean_dec(v_snd_2005_);
v___x_2008_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_2006_, v___y_1965_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___x_2010_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v___x_2008_);
v___x_2010_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_2007_, v___y_1965_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___y_2013_; uint8_t v___y_2014_; lean_object* v___y_2027_; uint8_t v___y_2032_; uint8_t v___x_2044_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref(v___x_2010_);
v___x_2044_ = l_Lean_Expr_isFVar(v_a_2011_);
if (v___x_2044_ == 0)
{
v___y_2032_ = v___x_2044_;
goto v___jp_2031_;
}
else
{
lean_object* v___x_2045_; uint8_t v___x_2046_; 
v___x_2045_ = l_Lean_Expr_fvarId_x21(v_a_2011_);
v___x_2046_ = l_Lean_instBEqFVarId_beq(v___x_2045_, v_x_1959_);
lean_dec(v___x_2045_);
v___y_2032_ = v___x_2046_;
goto v___jp_2031_;
}
v___jp_2012_:
{
if (v___y_2014_ == 0)
{
lean_dec(v_a_2011_);
lean_dec(v_val_1984_);
v_a_1970_ = v___x_1982_;
goto v___jp_1969_;
}
else
{
lean_object* v___x_2015_; 
lean_inc(v_x_1959_);
v___x_2015_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2011_, v_x_1959_, v___y_2013_);
if (lean_obj_tag(v___x_2015_) == 0)
{
lean_object* v_a_2016_; uint8_t v___x_2017_; 
v_a_2016_ = lean_ctor_get(v___x_2015_, 0);
lean_inc(v_a_2016_);
lean_dec_ref(v___x_2015_);
v___x_2017_ = lean_unbox(v_a_2016_);
lean_dec(v_a_2016_);
if (v___x_2017_ == 0)
{
lean_dec(v_x_1959_);
goto v___jp_1996_;
}
else
{
if (v___x_1995_ == 0)
{
lean_dec(v_val_1984_);
v_a_1970_ = v___x_1982_;
goto v___jp_1969_;
}
else
{
lean_dec(v_x_1959_);
goto v___jp_1996_;
}
}
}
else
{
lean_object* v_a_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2025_; 
lean_dec(v_val_1984_);
lean_dec(v_x_1959_);
v_a_2018_ = lean_ctor_get(v___x_2015_, 0);
v_isSharedCheck_2025_ = !lean_is_exclusive(v___x_2015_);
if (v_isSharedCheck_2025_ == 0)
{
v___x_2020_ = v___x_2015_;
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_a_2018_);
lean_dec(v___x_2015_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2025_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_2021_ == 0)
{
v___x_2023_ = v___x_2020_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2024_; 
v_reuseFailAlloc_2024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2024_, 0, v_a_2018_);
v___x_2023_ = v_reuseFailAlloc_2024_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
return v___x_2023_;
}
}
}
}
}
v___jp_2026_:
{
uint8_t v___x_2028_; 
v___x_2028_ = l_Lean_Expr_isFVar(v_a_2009_);
if (v___x_2028_ == 0)
{
lean_dec(v_a_2009_);
v___y_2013_ = v___y_2027_;
v___y_2014_ = v___x_2028_;
goto v___jp_2012_;
}
else
{
lean_object* v___x_2029_; uint8_t v___x_2030_; 
v___x_2029_ = l_Lean_Expr_fvarId_x21(v_a_2009_);
lean_dec(v_a_2009_);
v___x_2030_ = l_Lean_instBEqFVarId_beq(v___x_2029_, v_x_1959_);
lean_dec(v___x_2029_);
v___y_2013_ = v___y_2027_;
v___y_2014_ = v___x_2030_;
goto v___jp_2012_;
}
}
v___jp_2031_:
{
if (v___y_2032_ == 0)
{
lean_del_object(v___x_1986_);
v___y_2027_ = v___y_1965_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2033_; 
lean_inc(v_x_1959_);
lean_inc(v_a_2009_);
v___x_2033_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2009_, v_x_1959_, v___y_1965_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; uint8_t v___x_2035_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref(v___x_2033_);
v___x_2035_ = lean_unbox(v_a_2034_);
lean_dec(v_a_2034_);
if (v___x_2035_ == 0)
{
lean_dec(v_a_2011_);
lean_dec(v_a_2009_);
lean_dec(v_x_1959_);
goto v___jp_1988_;
}
else
{
if (v___x_1995_ == 0)
{
lean_del_object(v___x_1986_);
v___y_2027_ = v___y_1965_;
goto v___jp_2026_;
}
else
{
lean_dec(v_a_2011_);
lean_dec(v_a_2009_);
lean_dec(v_x_1959_);
goto v___jp_1988_;
}
}
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec(v_a_2011_);
lean_dec(v_a_2009_);
lean_del_object(v___x_1986_);
lean_dec(v_val_1984_);
lean_dec(v_x_1959_);
v_a_2036_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2033_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2033_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_a_2009_);
lean_del_object(v___x_1986_);
lean_dec(v_val_1984_);
lean_dec(v_x_1959_);
v_a_2047_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2010_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2010_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_dec(v_snd_2007_);
lean_del_object(v___x_1986_);
lean_dec(v_val_1984_);
lean_dec(v_x_1959_);
v_a_2055_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_2008_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_2008_);
v___x_2057_ = lean_box(0);
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
v_resetjp_2056_:
{
lean_object* v___x_2060_; 
if (v_isShared_2058_ == 0)
{
v___x_2060_ = v___x_2057_;
goto v_reusejp_2059_;
}
else
{
lean_object* v_reuseFailAlloc_2061_; 
v_reuseFailAlloc_2061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2061_, 0, v_a_2055_);
v___x_2060_ = v_reuseFailAlloc_2061_;
goto v_reusejp_2059_;
}
v_reusejp_2059_:
{
return v___x_2060_;
}
}
}
}
else
{
lean_dec(v_a_2003_);
lean_del_object(v___x_1986_);
lean_dec(v_val_1984_);
v_a_1970_ = v___x_1982_;
goto v___jp_1969_;
}
}
else
{
lean_object* v_a_2063_; lean_object* v___x_2065_; uint8_t v_isShared_2066_; uint8_t v_isSharedCheck_2070_; 
lean_del_object(v___x_1986_);
lean_dec(v_val_1984_);
lean_dec(v_x_1959_);
v_a_2063_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2070_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2070_ == 0)
{
v___x_2065_ = v___x_2002_;
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
else
{
lean_inc(v_a_2063_);
lean_dec(v___x_2002_);
v___x_2065_ = lean_box(0);
v_isShared_2066_ = v_isSharedCheck_2070_;
goto v_resetjp_2064_;
}
v_resetjp_2064_:
{
lean_object* v___x_2068_; 
if (v_isShared_2066_ == 0)
{
v___x_2068_ = v___x_2065_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2069_; 
v_reuseFailAlloc_2069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2069_, 0, v_a_2063_);
v___x_2068_ = v_reuseFailAlloc_2069_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
return v___x_2068_;
}
}
}
}
else
{
lean_del_object(v___x_1986_);
lean_dec(v_val_1984_);
v_a_1970_ = v___x_1982_;
goto v___jp_1969_;
}
v___jp_1988_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1993_; 
v___x_1989_ = l_Lean_LocalDecl_fvarId(v_val_1984_);
lean_dec(v_val_1984_);
v___x_1990_ = lean_box(v___x_1974_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
if (v_isShared_1987_ == 0)
{
lean_ctor_set(v___x_1986_, 0, v___x_1991_);
v___x_1993_ = v___x_1986_;
goto v_reusejp_1992_;
}
else
{
lean_object* v_reuseFailAlloc_1994_; 
v_reuseFailAlloc_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1994_, 0, v___x_1991_);
v___x_1993_ = v_reuseFailAlloc_1994_;
goto v_reusejp_1992_;
}
v_reusejp_1992_:
{
v_a_1978_ = v___x_1993_;
goto v___jp_1977_;
}
}
v___jp_1996_:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1997_ = l_Lean_LocalDecl_fvarId(v_val_1984_);
lean_dec(v_val_1984_);
v___x_1998_ = lean_box(v___x_1995_);
v___x_1999_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1997_);
lean_ctor_set(v___x_1999_, 1, v___x_1998_);
v___x_2000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2000_, 0, v___x_1999_);
v_a_1978_ = v___x_2000_;
goto v___jp_1977_;
}
}
}
v___jp_1977_:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v_a_1978_);
v___x_1980_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
lean_ctor_set(v___x_1980_, 1, v___x_1976_);
v___x_1981_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
return v___x_1981_;
}
}
v___jp_1969_:
{
size_t v___x_1971_; size_t v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = ((size_t)1ULL);
v___x_1972_ = lean_usize_add(v_i_1962_, v___x_1971_);
lean_inc_ref(v_a_1970_);
v___x_1973_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1959_, v_as_1960_, v_sz_1961_, v___x_1972_, v_a_1970_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
return v___x_1973_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2072_, lean_object* v_as_2073_, lean_object* v_sz_2074_, lean_object* v_i_2075_, lean_object* v_b_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_){
_start:
{
size_t v_sz_boxed_2082_; size_t v_i_boxed_2083_; lean_object* v_res_2084_; 
v_sz_boxed_2082_ = lean_unbox_usize(v_sz_2074_);
lean_dec(v_sz_2074_);
v_i_boxed_2083_ = lean_unbox_usize(v_i_2075_);
lean_dec(v_i_2075_);
v_res_2084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2072_, v_as_2073_, v_sz_boxed_2082_, v_i_boxed_2083_, v_b_2076_, v___y_2077_, v___y_2078_, v___y_2079_, v___y_2080_);
lean_dec(v___y_2080_);
lean_dec_ref(v___y_2079_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec_ref(v_as_2073_);
return v_res_2084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object* v_x_2085_, lean_object* v_x_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_, lean_object* v___y_2089_, lean_object* v___y_2090_){
_start:
{
if (lean_obj_tag(v_x_2086_) == 0)
{
lean_object* v_cs_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; size_t v_sz_2095_; size_t v___x_2096_; lean_object* v___x_2097_; 
v_cs_2092_ = lean_ctor_get(v_x_2086_, 0);
v___x_2093_ = lean_box(0);
v___x_2094_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2095_ = lean_array_size(v_cs_2092_);
v___x_2096_ = ((size_t)0ULL);
v___x_2097_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2085_, v_cs_2092_, v_sz_2095_, v___x_2096_, v___x_2094_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
if (lean_obj_tag(v___x_2097_) == 0)
{
lean_object* v_a_2098_; lean_object* v___x_2100_; uint8_t v_isShared_2101_; uint8_t v_isSharedCheck_2110_; 
v_a_2098_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2100_ = v___x_2097_;
v_isShared_2101_ = v_isSharedCheck_2110_;
goto v_resetjp_2099_;
}
else
{
lean_inc(v_a_2098_);
lean_dec(v___x_2097_);
v___x_2100_ = lean_box(0);
v_isShared_2101_ = v_isSharedCheck_2110_;
goto v_resetjp_2099_;
}
v_resetjp_2099_:
{
lean_object* v_fst_2102_; 
v_fst_2102_ = lean_ctor_get(v_a_2098_, 0);
lean_inc(v_fst_2102_);
lean_dec(v_a_2098_);
if (lean_obj_tag(v_fst_2102_) == 0)
{
lean_object* v___x_2104_; 
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v___x_2093_);
v___x_2104_ = v___x_2100_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v___x_2093_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
else
{
lean_object* v_val_2106_; lean_object* v___x_2108_; 
v_val_2106_ = lean_ctor_get(v_fst_2102_, 0);
lean_inc(v_val_2106_);
lean_dec_ref(v_fst_2102_);
if (v_isShared_2101_ == 0)
{
lean_ctor_set(v___x_2100_, 0, v_val_2106_);
v___x_2108_ = v___x_2100_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_val_2106_);
v___x_2108_ = v_reuseFailAlloc_2109_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
return v___x_2108_;
}
}
}
}
else
{
lean_object* v_a_2111_; lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2118_; 
v_a_2111_ = lean_ctor_get(v___x_2097_, 0);
v_isSharedCheck_2118_ = !lean_is_exclusive(v___x_2097_);
if (v_isSharedCheck_2118_ == 0)
{
v___x_2113_ = v___x_2097_;
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
else
{
lean_inc(v_a_2111_);
lean_dec(v___x_2097_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2118_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2116_; 
if (v_isShared_2114_ == 0)
{
v___x_2116_ = v___x_2113_;
goto v_reusejp_2115_;
}
else
{
lean_object* v_reuseFailAlloc_2117_; 
v_reuseFailAlloc_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_a_2111_);
v___x_2116_ = v_reuseFailAlloc_2117_;
goto v_reusejp_2115_;
}
v_reusejp_2115_:
{
return v___x_2116_;
}
}
}
}
else
{
lean_object* v_vs_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; size_t v_sz_2122_; size_t v___x_2123_; lean_object* v___x_2124_; 
v_vs_2119_ = lean_ctor_get(v_x_2086_, 0);
v___x_2120_ = lean_box(0);
v___x_2121_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2122_ = lean_array_size(v_vs_2119_);
v___x_2123_ = ((size_t)0ULL);
v___x_2124_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2085_, v_vs_2119_, v_sz_2122_, v___x_2123_, v___x_2121_, v___y_2087_, v___y_2088_, v___y_2089_, v___y_2090_);
if (lean_obj_tag(v___x_2124_) == 0)
{
lean_object* v_a_2125_; lean_object* v___x_2127_; uint8_t v_isShared_2128_; uint8_t v_isSharedCheck_2137_; 
v_a_2125_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2127_ = v___x_2124_;
v_isShared_2128_ = v_isSharedCheck_2137_;
goto v_resetjp_2126_;
}
else
{
lean_inc(v_a_2125_);
lean_dec(v___x_2124_);
v___x_2127_ = lean_box(0);
v_isShared_2128_ = v_isSharedCheck_2137_;
goto v_resetjp_2126_;
}
v_resetjp_2126_:
{
lean_object* v_fst_2129_; 
v_fst_2129_ = lean_ctor_get(v_a_2125_, 0);
lean_inc(v_fst_2129_);
lean_dec(v_a_2125_);
if (lean_obj_tag(v_fst_2129_) == 0)
{
lean_object* v___x_2131_; 
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v___x_2120_);
v___x_2131_ = v___x_2127_;
goto v_reusejp_2130_;
}
else
{
lean_object* v_reuseFailAlloc_2132_; 
v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2120_);
v___x_2131_ = v_reuseFailAlloc_2132_;
goto v_reusejp_2130_;
}
v_reusejp_2130_:
{
return v___x_2131_;
}
}
else
{
lean_object* v_val_2133_; lean_object* v___x_2135_; 
v_val_2133_ = lean_ctor_get(v_fst_2129_, 0);
lean_inc(v_val_2133_);
lean_dec_ref(v_fst_2129_);
if (v_isShared_2128_ == 0)
{
lean_ctor_set(v___x_2127_, 0, v_val_2133_);
v___x_2135_ = v___x_2127_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_val_2133_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
v_a_2138_ = lean_ctor_get(v___x_2124_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2124_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2124_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2124_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
v___x_2143_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2142_;
}
v_reusejp_2142_:
{
return v___x_2143_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2146_, lean_object* v_as_2147_, size_t v_sz_2148_, size_t v_i_2149_, lean_object* v_b_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_, lean_object* v___y_2153_, lean_object* v___y_2154_){
_start:
{
uint8_t v___x_2156_; 
v___x_2156_ = lean_usize_dec_lt(v_i_2149_, v_sz_2148_);
if (v___x_2156_ == 0)
{
lean_object* v___x_2157_; 
lean_dec(v_x_2146_);
v___x_2157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2157_, 0, v_b_2150_);
return v___x_2157_;
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2159_; 
lean_dec_ref(v_b_2150_);
v_a_2158_ = lean_array_uget_borrowed(v_as_2147_, v_i_2149_);
lean_inc(v_x_2146_);
v___x_2159_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2146_, v_a_2158_, v___y_2151_, v___y_2152_, v___y_2153_, v___y_2154_);
if (lean_obj_tag(v___x_2159_) == 0)
{
lean_object* v_a_2160_; lean_object* v___x_2162_; uint8_t v_isShared_2163_; uint8_t v_isSharedCheck_2174_; 
v_a_2160_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2162_ = v___x_2159_;
v_isShared_2163_ = v_isSharedCheck_2174_;
goto v_resetjp_2161_;
}
else
{
lean_inc(v_a_2160_);
lean_dec(v___x_2159_);
v___x_2162_ = lean_box(0);
v_isShared_2163_ = v_isSharedCheck_2174_;
goto v_resetjp_2161_;
}
v_resetjp_2161_:
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_box(0);
if (lean_obj_tag(v_a_2160_) == 1)
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2168_; 
lean_dec(v_x_2146_);
v___x_2165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2165_, 0, v_a_2160_);
v___x_2166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2166_, 0, v___x_2165_);
lean_ctor_set(v___x_2166_, 1, v___x_2164_);
if (v_isShared_2163_ == 0)
{
lean_ctor_set(v___x_2162_, 0, v___x_2166_);
v___x_2168_ = v___x_2162_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v___x_2166_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
else
{
lean_object* v___x_2170_; size_t v___x_2171_; size_t v___x_2172_; 
lean_del_object(v___x_2162_);
lean_dec(v_a_2160_);
v___x_2170_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2171_ = ((size_t)1ULL);
v___x_2172_ = lean_usize_add(v_i_2149_, v___x_2171_);
v_i_2149_ = v___x_2172_;
v_b_2150_ = v___x_2170_;
goto _start;
}
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_x_2146_);
v_a_2175_ = lean_ctor_get(v___x_2159_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2159_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2159_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2159_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v___x_2180_; 
if (v_isShared_2178_ == 0)
{
v___x_2180_ = v___x_2177_;
goto v_reusejp_2179_;
}
else
{
lean_object* v_reuseFailAlloc_2181_; 
v_reuseFailAlloc_2181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2181_, 0, v_a_2175_);
v___x_2180_ = v_reuseFailAlloc_2181_;
goto v_reusejp_2179_;
}
v_reusejp_2179_:
{
return v___x_2180_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2183_, lean_object* v_as_2184_, lean_object* v_sz_2185_, lean_object* v_i_2186_, lean_object* v_b_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_){
_start:
{
size_t v_sz_boxed_2193_; size_t v_i_boxed_2194_; lean_object* v_res_2195_; 
v_sz_boxed_2193_ = lean_unbox_usize(v_sz_2185_);
lean_dec(v_sz_2185_);
v_i_boxed_2194_ = lean_unbox_usize(v_i_2186_);
lean_dec(v_i_2186_);
v_res_2195_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2183_, v_as_2184_, v_sz_boxed_2193_, v_i_boxed_2194_, v_b_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec_ref(v_as_2184_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2196_, lean_object* v_x_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2196_, v_x_2197_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
lean_dec(v___y_2201_);
lean_dec_ref(v___y_2200_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec_ref(v_x_2197_);
return v_res_2203_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object* v_x_2204_, lean_object* v_t_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_, lean_object* v___y_2208_, lean_object* v___y_2209_){
_start:
{
lean_object* v_root_2211_; lean_object* v_tail_2212_; lean_object* v___x_2213_; 
v_root_2211_ = lean_ctor_get(v_t_2205_, 0);
v_tail_2212_ = lean_ctor_get(v_t_2205_, 1);
lean_inc(v_x_2204_);
v___x_2213_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2204_, v_root_2211_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
if (lean_obj_tag(v_a_2214_) == 0)
{
lean_object* v___x_2215_; size_t v_sz_2216_; size_t v___x_2217_; lean_object* v___x_2218_; 
lean_dec_ref(v___x_2213_);
v___x_2215_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2216_ = lean_array_size(v_tail_2212_);
v___x_2217_ = ((size_t)0ULL);
v___x_2218_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2204_, v_tail_2212_, v_sz_2216_, v___x_2217_, v___x_2215_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_);
if (lean_obj_tag(v___x_2218_) == 0)
{
lean_object* v_a_2219_; lean_object* v___x_2221_; uint8_t v_isShared_2222_; uint8_t v_isSharedCheck_2231_; 
v_a_2219_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2221_ = v___x_2218_;
v_isShared_2222_ = v_isSharedCheck_2231_;
goto v_resetjp_2220_;
}
else
{
lean_inc(v_a_2219_);
lean_dec(v___x_2218_);
v___x_2221_ = lean_box(0);
v_isShared_2222_ = v_isSharedCheck_2231_;
goto v_resetjp_2220_;
}
v_resetjp_2220_:
{
lean_object* v_fst_2223_; 
v_fst_2223_ = lean_ctor_get(v_a_2219_, 0);
lean_inc(v_fst_2223_);
lean_dec(v_a_2219_);
if (lean_obj_tag(v_fst_2223_) == 0)
{
lean_object* v___x_2225_; 
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v_a_2214_);
v___x_2225_ = v___x_2221_;
goto v_reusejp_2224_;
}
else
{
lean_object* v_reuseFailAlloc_2226_; 
v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2214_);
v___x_2225_ = v_reuseFailAlloc_2226_;
goto v_reusejp_2224_;
}
v_reusejp_2224_:
{
return v___x_2225_;
}
}
else
{
lean_object* v_val_2227_; lean_object* v___x_2229_; 
v_val_2227_ = lean_ctor_get(v_fst_2223_, 0);
lean_inc(v_val_2227_);
lean_dec_ref(v_fst_2223_);
if (v_isShared_2222_ == 0)
{
lean_ctor_set(v___x_2221_, 0, v_val_2227_);
v___x_2229_ = v___x_2221_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_val_2227_);
v___x_2229_ = v_reuseFailAlloc_2230_;
goto v_reusejp_2228_;
}
v_reusejp_2228_:
{
return v___x_2229_;
}
}
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
v_a_2232_ = lean_ctor_get(v___x_2218_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2218_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2218_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2218_);
v___x_2234_ = lean_box(0);
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
v_resetjp_2233_:
{
lean_object* v___x_2237_; 
if (v_isShared_2235_ == 0)
{
v___x_2237_ = v___x_2234_;
goto v_reusejp_2236_;
}
else
{
lean_object* v_reuseFailAlloc_2238_; 
v_reuseFailAlloc_2238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2238_, 0, v_a_2232_);
v___x_2237_ = v_reuseFailAlloc_2238_;
goto v_reusejp_2236_;
}
v_reusejp_2236_:
{
return v___x_2237_;
}
}
}
}
else
{
lean_dec_ref(v_a_2214_);
lean_dec(v_x_2204_);
return v___x_2213_;
}
}
else
{
lean_dec(v_x_2204_);
return v___x_2213_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* v_x_2240_, lean_object* v_t_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_){
_start:
{
lean_object* v_res_2247_; 
v_res_2247_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2240_, v_t_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
lean_dec(v___y_2245_);
lean_dec_ref(v___y_2244_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec_ref(v_t_2241_);
return v_res_2247_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object* v_x_2248_, lean_object* v_lctx_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_){
_start:
{
lean_object* v_decls_2255_; lean_object* v___x_2256_; 
v_decls_2255_ = lean_ctor_get(v_lctx_2249_, 1);
v___x_2256_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2248_, v_decls_2255_, v___y_2250_, v___y_2251_, v___y_2252_, v___y_2253_);
return v___x_2256_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object* v_x_2257_, lean_object* v_lctx_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_, lean_object* v___y_2262_, lean_object* v___y_2263_){
_start:
{
lean_object* v_res_2264_; 
v_res_2264_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2257_, v_lctx_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_);
lean_dec(v___y_2262_);
lean_dec_ref(v___y_2261_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec_ref(v_lctx_2258_);
return v_res_2264_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__0));
v___x_2267_ = l_Lean_stringToMessageData(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__2));
v___x_2270_ = l_Lean_stringToMessageData(v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__4));
v___x_2273_ = l_Lean_stringToMessageData(v___x_2272_);
return v___x_2273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object* v_x_2274_, lean_object* v_mvarId_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_){
_start:
{
lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___y_2284_; lean_object* v___y_2285_; lean_object* v___x_2330_; 
lean_inc(v_x_2274_);
v___x_2330_ = l_Lean_FVarId_getDecl___redArg(v_x_2274_, v___y_2276_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2330_) == 0)
{
lean_object* v_a_2331_; uint8_t v___x_2332_; uint8_t v___x_2333_; 
v_a_2331_ = lean_ctor_get(v___x_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref(v___x_2330_);
v___x_2332_ = 0;
v___x_2333_ = l_Lean_LocalDecl_isLet(v_a_2331_, v___x_2332_);
lean_dec(v_a_2331_);
if (v___x_2333_ == 0)
{
v___y_2282_ = v___y_2276_;
v___y_2283_ = v___y_2277_;
v___y_2284_ = v___y_2278_;
v___y_2285_ = v___y_2279_;
goto v___jp_2281_;
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2334_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2335_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2274_);
v___x_2336_ = l_Lean_mkFVar(v_x_2274_);
v___x_2337_ = l_Lean_MessageData_ofExpr(v___x_2336_);
v___x_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2335_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2340_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2338_);
lean_ctor_set(v___x_2340_, 1, v___x_2339_);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v___x_2340_);
lean_inc(v_mvarId_2275_);
v___x_2342_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2334_, v_mvarId_2275_, v___x_2341_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_dec_ref(v___x_2342_);
v___y_2282_ = v___y_2276_;
v___y_2283_ = v___y_2277_;
v___y_2284_ = v___y_2278_;
v___y_2285_ = v___y_2279_;
goto v___jp_2281_;
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_mvarId_2275_);
lean_dec(v_x_2274_);
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2342_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2342_);
v___x_2345_ = lean_box(0);
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
v_resetjp_2344_:
{
lean_object* v___x_2348_; 
if (v_isShared_2346_ == 0)
{
v___x_2348_ = v___x_2345_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_a_2343_);
v___x_2348_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
return v___x_2348_;
}
}
}
}
}
else
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2358_; 
lean_dec(v_mvarId_2275_);
lean_dec(v_x_2274_);
v_a_2351_ = lean_ctor_get(v___x_2330_, 0);
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2330_);
if (v_isSharedCheck_2358_ == 0)
{
v___x_2353_ = v___x_2330_;
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2330_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2358_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2356_; 
if (v_isShared_2354_ == 0)
{
v___x_2356_ = v___x_2353_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v_a_2351_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
v___jp_2281_:
{
lean_object* v_lctx_2286_; lean_object* v___x_2287_; 
v_lctx_2286_ = lean_ctor_get(v___y_2282_, 2);
lean_inc(v_x_2274_);
v___x_2287_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2274_, v_lctx_2286_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref(v___x_2287_);
if (lean_obj_tag(v_a_2288_) == 1)
{
lean_object* v_val_2289_; lean_object* v_fst_2290_; lean_object* v_snd_2291_; lean_object* v___x_2292_; uint8_t v___x_2293_; uint8_t v___x_2294_; lean_object* v___x_2295_; 
lean_dec(v_x_2274_);
v_val_2289_ = lean_ctor_get(v_a_2288_, 0);
lean_inc(v_val_2289_);
lean_dec_ref(v_a_2288_);
v_fst_2290_ = lean_ctor_get(v_val_2289_, 0);
lean_inc(v_fst_2290_);
v_snd_2291_ = lean_ctor_get(v_val_2289_, 1);
lean_inc(v_snd_2291_);
lean_dec(v_val_2289_);
v___x_2292_ = lean_box(0);
v___x_2293_ = 1;
v___x_2294_ = lean_unbox(v_snd_2291_);
lean_dec(v_snd_2291_);
v___x_2295_ = l_Lean_Meta_substCore(v_mvarId_2275_, v_fst_2290_, v___x_2294_, v___x_2292_, v___x_2293_, v___x_2293_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
if (lean_obj_tag(v___x_2295_) == 0)
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2304_; 
v_a_2296_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2298_ = v___x_2295_;
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2295_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2304_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v_snd_2300_; lean_object* v___x_2302_; 
v_snd_2300_ = lean_ctor_get(v_a_2296_, 1);
lean_inc(v_snd_2300_);
lean_dec(v_a_2296_);
if (v_isShared_2299_ == 0)
{
lean_ctor_set(v___x_2298_, 0, v_snd_2300_);
v___x_2302_ = v___x_2298_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_snd_2300_);
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
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
v_a_2305_ = lean_ctor_get(v___x_2295_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2295_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2295_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2295_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v___x_2310_; 
if (v_isShared_2308_ == 0)
{
v___x_2310_ = v___x_2307_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_a_2305_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
else
{
lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
lean_dec(v_a_2288_);
v___x_2313_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2314_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2315_ = l_Lean_mkFVar(v_x_2274_);
v___x_2316_ = l_Lean_MessageData_ofExpr(v___x_2315_);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2314_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_2319_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2319_, 0, v___x_2317_);
lean_ctor_set(v___x_2319_, 1, v___x_2318_);
v___x_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2319_);
v___x_2321_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2313_, v_mvarId_2275_, v___x_2320_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_);
return v___x_2321_;
}
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2324_; uint8_t v_isShared_2325_; uint8_t v_isSharedCheck_2329_; 
lean_dec(v_mvarId_2275_);
lean_dec(v_x_2274_);
v_a_2322_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2329_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2329_ == 0)
{
v___x_2324_ = v___x_2287_;
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
else
{
lean_inc(v_a_2322_);
lean_dec(v___x_2287_);
v___x_2324_ = lean_box(0);
v_isShared_2325_ = v_isSharedCheck_2329_;
goto v_resetjp_2323_;
}
v_resetjp_2323_:
{
lean_object* v___x_2327_; 
if (v_isShared_2325_ == 0)
{
v___x_2327_ = v___x_2324_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2328_; 
v_reuseFailAlloc_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2328_, 0, v_a_2322_);
v___x_2327_ = v_reuseFailAlloc_2328_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
return v___x_2327_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2359_, lean_object* v_mvarId_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_, lean_object* v___y_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_res_2366_; 
v_res_2366_ = l_Lean_Meta_substVar___lam__0(v_x_2359_, v_mvarId_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_);
lean_dec(v___y_2364_);
lean_dec_ref(v___y_2363_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
return v_res_2366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2367_, lean_object* v_x_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___f_2374_; lean_object* v___x_2375_; 
lean_inc(v_mvarId_2367_);
v___f_2374_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2374_, 0, v_x_2368_);
lean_closure_set(v___f_2374_, 1, v_mvarId_2367_);
v___x_2375_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2367_, v___f_2374_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
return v___x_2375_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2376_, lean_object* v_x_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_){
_start:
{
lean_object* v_res_2383_; 
v_res_2383_ = l_Lean_Meta_substVar(v_mvarId_2376_, v_x_2377_, v_a_2378_, v_a_2379_, v_a_2380_, v_a_2381_);
lean_dec(v_a_2381_);
lean_dec_ref(v_a_2380_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
return v_res_2383_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2385_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2386_ = l_Lean_stringToMessageData(v___x_2385_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2387_, lean_object* v_snd_2388_, uint8_t v___x_2389_, lean_object* v_fvarSubst_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_){
_start:
{
lean_object* v___x_2396_; 
lean_inc(v_fst_2387_);
v___x_2396_ = l_Lean_FVarId_getDecl___redArg(v_fst_2387_, v___y_2391_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2396_) == 0)
{
lean_object* v_a_2397_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v___y_2401_; lean_object* v___y_2402_; lean_object* v_newType_2411_; uint8_t v_symm_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___y_2415_; lean_object* v___y_2416_; lean_object* v___x_2452_; lean_object* v___x_2453_; 
v_a_2397_ = lean_ctor_get(v___x_2396_, 0);
lean_inc(v_a_2397_);
lean_dec_ref(v___x_2396_);
v___x_2452_ = l_Lean_LocalDecl_type(v_a_2397_);
v___x_2453_ = l_Lean_Meta_matchEq_x3f(v___x_2452_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref(v___x_2453_);
if (lean_obj_tag(v_a_2454_) == 1)
{
lean_object* v_val_2455_; lean_object* v_snd_2456_; lean_object* v_fst_2457_; lean_object* v_snd_2458_; lean_object* v___x_2459_; 
v_val_2455_ = lean_ctor_get(v_a_2454_, 0);
lean_inc(v_val_2455_);
lean_dec_ref(v_a_2454_);
v_snd_2456_ = lean_ctor_get(v_val_2455_, 1);
lean_inc(v_snd_2456_);
lean_dec(v_val_2455_);
v_fst_2457_ = lean_ctor_get(v_snd_2456_, 0);
lean_inc(v_fst_2457_);
v_snd_2458_ = lean_ctor_get(v_snd_2456_, 1);
lean_inc_n(v_snd_2458_, 2);
lean_dec(v_snd_2456_);
lean_inc(v___y_2394_);
lean_inc_ref(v___y_2393_);
lean_inc(v___y_2392_);
lean_inc_ref(v___y_2391_);
v___x_2459_ = lean_whnf(v_snd_2458_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; uint8_t v___x_2461_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref(v___x_2459_);
v___x_2461_ = l_Lean_Expr_isFVar(v_a_2460_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
lean_dec(v_a_2460_);
lean_inc(v___y_2394_);
lean_inc_ref(v___y_2393_);
lean_inc(v___y_2392_);
lean_inc_ref(v___y_2391_);
lean_inc(v_fst_2457_);
v___x_2462_ = lean_whnf(v_fst_2457_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; uint8_t v___y_2465_; uint8_t v___x_2477_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref(v___x_2462_);
v___x_2477_ = l_Lean_Expr_isFVar(v_a_2463_);
if (v___x_2477_ == 0)
{
lean_dec(v_a_2463_);
lean_dec(v_snd_2458_);
lean_dec(v_fst_2457_);
lean_dec(v_fvarSubst_2390_);
lean_dec(v_fst_2387_);
v___y_2399_ = v___y_2391_;
v___y_2400_ = v___y_2392_;
v___y_2401_ = v___y_2393_;
v___y_2402_ = v___y_2394_;
goto v___jp_2398_;
}
else
{
uint8_t v___x_2478_; 
v___x_2478_ = lean_expr_eqv(v_fst_2457_, v_a_2463_);
lean_dec(v_fst_2457_);
if (v___x_2478_ == 0)
{
v___y_2465_ = v___x_2477_;
goto v___jp_2464_;
}
else
{
v___y_2465_ = v___x_2461_;
goto v___jp_2464_;
}
}
v___jp_2464_:
{
if (v___y_2465_ == 0)
{
lean_object* v___x_2466_; 
lean_dec(v_a_2463_);
lean_dec(v_snd_2458_);
lean_dec(v_a_2397_);
v___x_2466_ = l_Lean_Meta_substCore(v_snd_2388_, v_fst_2387_, v___y_2465_, v_fvarSubst_2390_, v___x_2389_, v___x_2389_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
return v___x_2466_;
}
else
{
lean_object* v___x_2467_; 
v___x_2467_ = l_Lean_Meta_mkEq(v_a_2463_, v_snd_2458_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref(v___x_2467_);
v_newType_2411_ = v_a_2468_;
v_symm_2412_ = v___x_2461_;
v___y_2413_ = v___y_2391_;
v___y_2414_ = v___y_2392_;
v___y_2415_ = v___y_2393_;
v___y_2416_ = v___y_2394_;
goto v___jp_2410_;
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v_a_2397_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v_fvarSubst_2390_);
lean_dec(v_snd_2388_);
lean_dec(v_fst_2387_);
v_a_2469_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2467_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2467_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec(v_snd_2458_);
lean_dec(v_fst_2457_);
lean_dec(v_a_2397_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v_fvarSubst_2390_);
lean_dec(v_snd_2388_);
lean_dec(v_fst_2387_);
v_a_2479_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2462_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2462_);
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
uint8_t v___x_2487_; 
v___x_2487_ = lean_expr_eqv(v_snd_2458_, v_a_2460_);
lean_dec(v_snd_2458_);
if (v___x_2487_ == 0)
{
if (v___x_2461_ == 0)
{
lean_object* v___x_2488_; 
lean_dec(v_a_2460_);
lean_dec(v_fst_2457_);
lean_dec(v_a_2397_);
v___x_2488_ = l_Lean_Meta_substCore(v_snd_2388_, v_fst_2387_, v___x_2389_, v_fvarSubst_2390_, v___x_2389_, v___x_2389_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
return v___x_2488_;
}
else
{
lean_object* v___x_2489_; 
v___x_2489_ = l_Lean_Meta_mkEq(v_fst_2457_, v_a_2460_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref(v___x_2489_);
v_newType_2411_ = v_a_2490_;
v_symm_2412_ = v___x_2389_;
v___y_2413_ = v___y_2391_;
v___y_2414_ = v___y_2392_;
v___y_2415_ = v___y_2393_;
v___y_2416_ = v___y_2394_;
goto v___jp_2410_;
}
else
{
lean_object* v_a_2491_; lean_object* v___x_2493_; uint8_t v_isShared_2494_; uint8_t v_isSharedCheck_2498_; 
lean_dec(v_a_2397_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v_fvarSubst_2390_);
lean_dec(v_snd_2388_);
lean_dec(v_fst_2387_);
v_a_2491_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2498_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2498_ == 0)
{
v___x_2493_ = v___x_2489_;
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
else
{
lean_inc(v_a_2491_);
lean_dec(v___x_2489_);
v___x_2493_ = lean_box(0);
v_isShared_2494_ = v_isSharedCheck_2498_;
goto v_resetjp_2492_;
}
v_resetjp_2492_:
{
lean_object* v___x_2496_; 
if (v_isShared_2494_ == 0)
{
v___x_2496_ = v___x_2493_;
goto v_reusejp_2495_;
}
else
{
lean_object* v_reuseFailAlloc_2497_; 
v_reuseFailAlloc_2497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2497_, 0, v_a_2491_);
v___x_2496_ = v_reuseFailAlloc_2497_;
goto v_reusejp_2495_;
}
v_reusejp_2495_:
{
return v___x_2496_;
}
}
}
}
}
else
{
lean_object* v___x_2499_; 
lean_dec(v_a_2460_);
lean_dec(v_fst_2457_);
lean_dec(v_a_2397_);
v___x_2499_ = l_Lean_Meta_substCore(v_snd_2388_, v_fst_2387_, v___x_2389_, v_fvarSubst_2390_, v___x_2389_, v___x_2389_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
return v___x_2499_;
}
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_snd_2458_);
lean_dec(v_fst_2457_);
lean_dec(v_a_2397_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v_fvarSubst_2390_);
lean_dec(v_snd_2388_);
lean_dec(v_fst_2387_);
v_a_2500_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2459_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2459_);
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
else
{
lean_dec(v_a_2454_);
lean_dec(v_fvarSubst_2390_);
lean_dec(v_fst_2387_);
v___y_2399_ = v___y_2391_;
v___y_2400_ = v___y_2392_;
v___y_2401_ = v___y_2393_;
v___y_2402_ = v___y_2394_;
goto v___jp_2398_;
}
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v_a_2397_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v_fvarSubst_2390_);
lean_dec(v_snd_2388_);
lean_dec(v_fst_2387_);
v_a_2508_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2453_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2453_);
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
v___jp_2398_:
{
lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; 
v___x_2403_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2404_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2405_ = l_Lean_LocalDecl_type(v_a_2397_);
lean_dec(v_a_2397_);
v___x_2406_ = l_Lean_indentExpr(v___x_2405_);
v___x_2407_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2407_, 0, v___x_2404_);
lean_ctor_set(v___x_2407_, 1, v___x_2406_);
v___x_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2408_, 0, v___x_2407_);
v___x_2409_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2403_, v_snd_2388_, v___x_2408_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
return v___x_2409_;
}
v___jp_2410_:
{
lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2417_ = l_Lean_LocalDecl_userName(v_a_2397_);
lean_dec(v_a_2397_);
lean_inc(v_fst_2387_);
v___x_2418_ = l_Lean_mkFVar(v_fst_2387_);
v___x_2419_ = l_Lean_MVarId_assert(v_snd_2388_, v___x_2417_, v_newType_2411_, v___x_2418_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref(v___x_2419_);
v___x_2421_ = l_Lean_Meta_intro1Core(v_a_2420_, v___x_2389_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2421_) == 0)
{
lean_object* v_a_2422_; lean_object* v_fst_2423_; lean_object* v_snd_2424_; lean_object* v___x_2425_; 
v_a_2422_ = lean_ctor_get(v___x_2421_, 0);
lean_inc(v_a_2422_);
lean_dec_ref(v___x_2421_);
v_fst_2423_ = lean_ctor_get(v_a_2422_, 0);
lean_inc(v_fst_2423_);
v_snd_2424_ = lean_ctor_get(v_a_2422_, 1);
lean_inc(v_snd_2424_);
lean_dec(v_a_2422_);
v___x_2425_ = l_Lean_MVarId_clear(v_snd_2424_, v_fst_2387_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref(v___x_2425_);
v___x_2427_ = l_Lean_Meta_substCore(v_a_2426_, v_fst_2423_, v_symm_2412_, v_fvarSubst_2390_, v___x_2389_, v___x_2389_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
return v___x_2427_;
}
else
{
lean_object* v_a_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_2435_; 
lean_dec(v_fst_2423_);
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v_fvarSubst_2390_);
v_a_2428_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2425_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2425_);
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
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v_fvarSubst_2390_);
lean_dec(v_fst_2387_);
v_a_2436_ = lean_ctor_get(v___x_2421_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2421_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2421_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2421_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_a_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec(v___y_2416_);
lean_dec_ref(v___y_2415_);
lean_dec(v___y_2414_);
lean_dec_ref(v___y_2413_);
lean_dec(v_fvarSubst_2390_);
lean_dec(v_fst_2387_);
v_a_2444_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2419_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2419_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2449_; 
if (v_isShared_2447_ == 0)
{
v___x_2449_ = v___x_2446_;
goto v_reusejp_2448_;
}
else
{
lean_object* v_reuseFailAlloc_2450_; 
v_reuseFailAlloc_2450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2444_);
v___x_2449_ = v_reuseFailAlloc_2450_;
goto v_reusejp_2448_;
}
v_reusejp_2448_:
{
return v___x_2449_;
}
}
}
}
}
else
{
lean_object* v_a_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v_fvarSubst_2390_);
lean_dec(v_snd_2388_);
lean_dec(v_fst_2387_);
v_a_2516_ = lean_ctor_get(v___x_2396_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2396_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2396_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_a_2516_);
lean_dec(v___x_2396_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2524_, lean_object* v_snd_2525_, lean_object* v___x_2526_, lean_object* v_fvarSubst_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
uint8_t v___x_1937__boxed_2533_; lean_object* v_res_2534_; 
v___x_1937__boxed_2533_ = lean_unbox(v___x_2526_);
v_res_2534_ = l_Lean_Meta_substEq___lam__0(v_fst_2524_, v_snd_2525_, v___x_1937__boxed_2533_, v_fvarSubst_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2535_, lean_object* v_hFVarId_2536_, lean_object* v_fvarSubst_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
uint8_t v___x_2543_; lean_object* v___x_2544_; 
v___x_2543_ = 1;
v___x_2544_ = l_Lean_Meta_heqToEq(v_mvarId_2535_, v_hFVarId_2536_, v___x_2543_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v_a_2545_; lean_object* v_fst_2546_; lean_object* v_snd_2547_; lean_object* v___x_2548_; lean_object* v___f_2549_; lean_object* v___x_2550_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2545_);
lean_dec_ref(v___x_2544_);
v_fst_2546_ = lean_ctor_get(v_a_2545_, 0);
lean_inc(v_fst_2546_);
v_snd_2547_ = lean_ctor_get(v_a_2545_, 1);
lean_inc_n(v_snd_2547_, 2);
lean_dec(v_a_2545_);
v___x_2548_ = lean_box(v___x_2543_);
v___f_2549_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2549_, 0, v_fst_2546_);
lean_closure_set(v___f_2549_, 1, v_snd_2547_);
lean_closure_set(v___f_2549_, 2, v___x_2548_);
lean_closure_set(v___f_2549_, 3, v_fvarSubst_2537_);
v___x_2550_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_snd_2547_, v___f_2549_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
return v___x_2550_;
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec(v_fvarSubst_2537_);
v_a_2551_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2544_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2544_);
v___x_2553_ = lean_box(0);
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
v_resetjp_2552_:
{
lean_object* v___x_2556_; 
if (v_isShared_2554_ == 0)
{
v___x_2556_ = v___x_2553_;
goto v_reusejp_2555_;
}
else
{
lean_object* v_reuseFailAlloc_2557_; 
v_reuseFailAlloc_2557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2557_, 0, v_a_2551_);
v___x_2556_ = v_reuseFailAlloc_2557_;
goto v_reusejp_2555_;
}
v_reusejp_2555_:
{
return v___x_2556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2559_, lean_object* v_hFVarId_2560_, lean_object* v_fvarSubst_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l_Lean_Meta_substEq(v_mvarId_2559_, v_hFVarId_2560_, v_fvarSubst_2561_, v_a_2562_, v_a_2563_, v_a_2564_, v_a_2565_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2568_, lean_object* v_mvarId_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_, lean_object* v___y_2572_, lean_object* v___y_2573_){
_start:
{
lean_object* v___x_2575_; 
lean_inc(v_h_2568_);
v___x_2575_ = l_Lean_FVarId_getType___redArg(v_h_2568_, v___y_2570_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc_n(v_a_2576_, 2);
lean_dec_ref(v___x_2575_);
v___x_2577_ = l_Lean_Meta_matchEq_x3f(v_a_2576_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref(v___x_2577_);
if (lean_obj_tag(v_a_2578_) == 0)
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_Meta_matchHEq_x3f(v_a_2576_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref(v___x_2579_);
if (lean_obj_tag(v_a_2580_) == 0)
{
lean_object* v___x_2581_; 
v___x_2581_ = l_Lean_Meta_substVar(v_mvarId_2569_, v_h_2568_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
return v___x_2581_;
}
else
{
uint8_t v___x_2582_; lean_object* v___x_2583_; 
lean_dec_ref(v_a_2580_);
v___x_2582_ = 1;
lean_inc(v_h_2568_);
lean_inc(v_mvarId_2569_);
v___x_2583_ = l_Lean_Meta_heqToEq(v_mvarId_2569_, v_h_2568_, v___x_2582_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v_fst_2585_; lean_object* v_snd_2586_; uint8_t v___x_2587_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref(v___x_2583_);
v_fst_2585_ = lean_ctor_get(v_a_2584_, 0);
lean_inc(v_fst_2585_);
v_snd_2586_ = lean_ctor_get(v_a_2584_, 1);
lean_inc(v_snd_2586_);
lean_dec(v_a_2584_);
v___x_2587_ = l_Lean_instBEqMVarId_beq(v_mvarId_2569_, v_snd_2586_);
if (v___x_2587_ == 0)
{
lean_object* v___x_2588_; 
lean_dec(v_mvarId_2569_);
lean_dec(v_h_2568_);
v___x_2588_ = l_Lean_Meta_subst(v_snd_2586_, v_fst_2585_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
return v___x_2588_;
}
else
{
lean_object* v___x_2589_; 
lean_dec(v_snd_2586_);
lean_dec(v_fst_2585_);
v___x_2589_ = l_Lean_Meta_substVar(v_mvarId_2569_, v_h_2568_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
return v___x_2589_;
}
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_mvarId_2569_);
lean_dec(v_h_2568_);
v_a_2590_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2583_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2583_);
v___x_2592_ = lean_box(0);
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
v_resetjp_2591_:
{
lean_object* v___x_2595_; 
if (v_isShared_2593_ == 0)
{
v___x_2595_ = v___x_2592_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_a_2590_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
else
{
lean_object* v_a_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2605_; 
lean_dec(v_mvarId_2569_);
lean_dec(v_h_2568_);
v_a_2598_ = lean_ctor_get(v___x_2579_, 0);
v_isSharedCheck_2605_ = !lean_is_exclusive(v___x_2579_);
if (v_isSharedCheck_2605_ == 0)
{
v___x_2600_ = v___x_2579_;
v_isShared_2601_ = v_isSharedCheck_2605_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_a_2598_);
lean_dec(v___x_2579_);
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
else
{
lean_object* v___x_2606_; lean_object* v___x_2607_; 
lean_dec_ref(v_a_2578_);
lean_dec(v_a_2576_);
v___x_2606_ = lean_box(0);
v___x_2607_ = l_Lean_Meta_substEq(v_mvarId_2569_, v_h_2568_, v___x_2606_, v___y_2570_, v___y_2571_, v___y_2572_, v___y_2573_);
if (lean_obj_tag(v___x_2607_) == 0)
{
lean_object* v_a_2608_; lean_object* v___x_2610_; uint8_t v_isShared_2611_; uint8_t v_isSharedCheck_2616_; 
v_a_2608_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2610_ = v___x_2607_;
v_isShared_2611_ = v_isSharedCheck_2616_;
goto v_resetjp_2609_;
}
else
{
lean_inc(v_a_2608_);
lean_dec(v___x_2607_);
v___x_2610_ = lean_box(0);
v_isShared_2611_ = v_isSharedCheck_2616_;
goto v_resetjp_2609_;
}
v_resetjp_2609_:
{
lean_object* v_snd_2612_; lean_object* v___x_2614_; 
v_snd_2612_ = lean_ctor_get(v_a_2608_, 1);
lean_inc(v_snd_2612_);
lean_dec(v_a_2608_);
if (v_isShared_2611_ == 0)
{
lean_ctor_set(v___x_2610_, 0, v_snd_2612_);
v___x_2614_ = v___x_2610_;
goto v_reusejp_2613_;
}
else
{
lean_object* v_reuseFailAlloc_2615_; 
v_reuseFailAlloc_2615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2615_, 0, v_snd_2612_);
v___x_2614_ = v_reuseFailAlloc_2615_;
goto v_reusejp_2613_;
}
v_reusejp_2613_:
{
return v___x_2614_;
}
}
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
v_a_2617_ = lean_ctor_get(v___x_2607_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2607_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2607_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2607_);
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
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_a_2576_);
lean_dec(v_mvarId_2569_);
lean_dec(v_h_2568_);
v_a_2625_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2577_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2577_);
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
else
{
lean_object* v_a_2633_; lean_object* v___x_2635_; uint8_t v_isShared_2636_; uint8_t v_isSharedCheck_2640_; 
lean_dec(v_mvarId_2569_);
lean_dec(v_h_2568_);
v_a_2633_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2575_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2575_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2641_, lean_object* v_mvarId_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lean_Meta_subst___lam__0(v_h_2641_, v_mvarId_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v_res_2648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2649_, lean_object* v_h_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_){
_start:
{
lean_object* v___f_2656_; lean_object* v___x_2657_; 
lean_inc(v_mvarId_2649_);
v___f_2656_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2656_, 0, v_h_2650_);
lean_closure_set(v___f_2656_, 1, v_mvarId_2649_);
v___x_2657_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2649_, v___f_2656_, v_a_2651_, v_a_2652_, v_a_2653_, v_a_2654_);
return v___x_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2658_, lean_object* v_h_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v_res_2665_; 
v_res_2665_ = l_Lean_Meta_subst(v_mvarId_2658_, v_h_2659_, v_a_2660_, v_a_2661_, v_a_2662_, v_a_2663_);
lean_dec(v_a_2663_);
lean_dec_ref(v_a_2662_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
return v_res_2665_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_, lean_object* v___y_2670_){
_start:
{
lean_object* v___x_2672_; 
v___x_2672_ = l_Lean_Meta_saveState___redArg(v___y_2668_, v___y_2670_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref(v___x_2672_);
lean_inc(v___y_2670_);
lean_inc_ref(v___y_2669_);
lean_inc(v___y_2668_);
lean_inc_ref(v___y_2667_);
v___x_2674_ = lean_apply_5(v_x_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_, lean_box(0));
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_dec(v_a_2673_);
return v___x_2674_;
}
else
{
lean_object* v_a_2675_; uint8_t v___y_2677_; uint8_t v___x_2695_; 
v_a_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_a_2675_);
v___x_2695_ = l_Lean_Exception_isInterrupt(v_a_2675_);
if (v___x_2695_ == 0)
{
uint8_t v___x_2696_; 
lean_inc(v_a_2675_);
v___x_2696_ = l_Lean_Exception_isRuntime(v_a_2675_);
v___y_2677_ = v___x_2696_;
goto v___jp_2676_;
}
else
{
v___y_2677_ = v___x_2695_;
goto v___jp_2676_;
}
v___jp_2676_:
{
if (v___y_2677_ == 0)
{
lean_object* v___x_2678_; 
lean_dec_ref(v___x_2674_);
v___x_2678_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2673_, v___y_2668_, v___y_2670_);
lean_dec(v_a_2673_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v___x_2680_; uint8_t v_isShared_2681_; uint8_t v_isSharedCheck_2685_; 
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
lean_ctor_set_tag(v___x_2680_, 1);
lean_ctor_set(v___x_2680_, 0, v_a_2675_);
v___x_2683_ = v___x_2680_;
goto v_reusejp_2682_;
}
else
{
lean_object* v_reuseFailAlloc_2684_; 
v_reuseFailAlloc_2684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2684_, 0, v_a_2675_);
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
lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2694_; 
lean_dec(v_a_2675_);
v_a_2687_ = lean_ctor_get(v___x_2678_, 0);
v_isSharedCheck_2694_ = !lean_is_exclusive(v___x_2678_);
if (v_isSharedCheck_2694_ == 0)
{
v___x_2689_ = v___x_2678_;
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_dec(v___x_2678_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2694_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2692_; 
if (v_isShared_2690_ == 0)
{
v___x_2692_ = v___x_2689_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_a_2687_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
else
{
lean_dec(v_a_2675_);
lean_dec(v_a_2673_);
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2704_; 
lean_dec_ref(v_x_2666_);
v_a_2697_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2704_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2704_ == 0)
{
v___x_2699_ = v___x_2672_;
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_a_2697_);
lean_dec(v___x_2672_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2704_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2702_; 
if (v_isShared_2700_ == 0)
{
v___x_2702_ = v___x_2699_;
goto v_reusejp_2701_;
}
else
{
lean_object* v_reuseFailAlloc_2703_; 
v_reuseFailAlloc_2703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2697_);
v___x_2702_ = v_reuseFailAlloc_2703_;
goto v_reusejp_2701_;
}
v_reusejp_2701_:
{
return v___x_2702_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_res_2711_; 
v_res_2711_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
lean_dec(v___y_2709_);
lean_dec_ref(v___y_2708_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
return v_res_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2712_, lean_object* v_x_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2720_, lean_object* v_x_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_res_2727_; 
v_res_2727_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2720_, v_x_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
return v_res_2727_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_, lean_object* v___y_2731_, lean_object* v___y_2732_){
_start:
{
lean_object* v_ref_2734_; lean_object* v___x_2735_; lean_object* v_a_2736_; lean_object* v___x_2738_; uint8_t v_isShared_2739_; uint8_t v_isSharedCheck_2744_; 
v_ref_2734_ = lean_ctor_get(v___y_2731_, 5);
v___x_2735_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msg_2728_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_);
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2738_ = v___x_2735_;
v_isShared_2739_ = v_isSharedCheck_2744_;
goto v_resetjp_2737_;
}
else
{
lean_inc(v_a_2736_);
lean_dec(v___x_2735_);
v___x_2738_ = lean_box(0);
v_isShared_2739_ = v_isSharedCheck_2744_;
goto v_resetjp_2737_;
}
v_resetjp_2737_:
{
lean_object* v___x_2740_; lean_object* v___x_2742_; 
lean_inc(v_ref_2734_);
v___x_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2740_, 0, v_ref_2734_);
lean_ctor_set(v___x_2740_, 1, v_a_2736_);
if (v_isShared_2739_ == 0)
{
lean_ctor_set_tag(v___x_2738_, 1);
lean_ctor_set(v___x_2738_, 0, v___x_2740_);
v___x_2742_ = v___x_2738_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
v___x_2742_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
return v___x_2742_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
lean_dec(v___y_2749_);
lean_dec_ref(v___y_2748_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
return v_res_2751_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; 
v___x_2762_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2763_ = l_Lean_stringToMessageData(v___x_2762_);
return v___x_2763_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2765_; lean_object* v___x_2766_; 
v___x_2765_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2766_ = l_Lean_stringToMessageData(v___x_2765_);
return v___x_2766_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2780_ = l_Lean_stringToMessageData(v___x_2779_);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2789_, uint8_t v_substLHS_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_, lean_object* v___y_2793_, lean_object* v___y_2794_){
_start:
{
lean_object* v___x_2796_; 
lean_inc(v_mvarId_2789_);
v___x_2796_ = l_Lean_MVarId_getType_x27(v_mvarId_2789_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2796_) == 0)
{
lean_object* v_a_2797_; 
v_a_2797_ = lean_ctor_get(v___x_2796_, 0);
lean_inc(v_a_2797_);
lean_dec_ref(v___x_2796_);
if (lean_obj_tag(v_a_2797_) == 7)
{
lean_object* v_binderType_2801_; lean_object* v_body_2802_; uint8_t v___x_2803_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___y_2815_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v___y_2897_; lean_object* v___y_2898_; lean_object* v_fst_2938_; lean_object* v_fst_2939_; lean_object* v_fst_2940_; lean_object* v_snd_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; lean_object* v___y_2944_; lean_object* v___y_2945_; 
v_binderType_2801_ = lean_ctor_get(v_a_2797_, 1);
lean_inc_ref(v_binderType_2801_);
v_body_2802_ = lean_ctor_get(v_a_2797_, 2);
lean_inc_ref(v_body_2802_);
lean_dec_ref(v_a_2797_);
v___x_2803_ = l_Lean_Expr_hasLooseBVars(v_body_2802_);
if (v___x_2803_ == 0)
{
lean_object* v___x_2957_; 
v___x_2957_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2801_, v___y_2792_);
if (lean_obj_tag(v___x_2957_) == 0)
{
lean_object* v_a_2958_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___y_2962_; lean_object* v___y_2963_; lean_object* v___x_2974_; uint8_t v___x_2975_; 
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
lean_inc(v_a_2958_);
lean_dec_ref(v___x_2957_);
v___x_2974_ = l_Lean_Expr_cleanupAnnotations(v_a_2958_);
v___x_2975_ = l_Lean_Expr_isApp(v___x_2974_);
if (v___x_2975_ == 0)
{
lean_dec_ref(v___x_2974_);
lean_dec_ref(v_body_2802_);
lean_dec(v_mvarId_2789_);
v___y_2960_ = v___y_2791_;
v___y_2961_ = v___y_2792_;
v___y_2962_ = v___y_2793_;
v___y_2963_ = v___y_2794_;
goto v___jp_2959_;
}
else
{
lean_object* v_arg_2976_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v_arg_2976_ = lean_ctor_get(v___x_2974_, 1);
lean_inc_ref(v_arg_2976_);
v___x_2977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2974_);
v___x_2978_ = l_Lean_Expr_isApp(v___x_2977_);
if (v___x_2978_ == 0)
{
lean_dec_ref(v___x_2977_);
lean_dec_ref(v_arg_2976_);
lean_dec_ref(v_body_2802_);
lean_dec(v_mvarId_2789_);
v___y_2960_ = v___y_2791_;
v___y_2961_ = v___y_2792_;
v___y_2962_ = v___y_2793_;
v___y_2963_ = v___y_2794_;
goto v___jp_2959_;
}
else
{
lean_object* v_arg_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_arg_2979_ = lean_ctor_get(v___x_2977_, 1);
lean_inc_ref(v_arg_2979_);
v___x_2980_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2977_);
v___x_2981_ = l_Lean_Expr_isApp(v___x_2980_);
if (v___x_2981_ == 0)
{
lean_dec_ref(v___x_2980_);
lean_dec_ref(v_arg_2979_);
lean_dec_ref(v_arg_2976_);
lean_dec_ref(v_body_2802_);
lean_dec(v_mvarId_2789_);
v___y_2960_ = v___y_2791_;
v___y_2961_ = v___y_2792_;
v___y_2962_ = v___y_2793_;
v___y_2963_ = v___y_2794_;
goto v___jp_2959_;
}
else
{
lean_object* v_arg_2982_; lean_object* v___x_2983_; lean_object* v___x_2984_; uint8_t v___x_2985_; 
v_arg_2982_ = lean_ctor_get(v___x_2980_, 1);
lean_inc_ref(v_arg_2982_);
v___x_2983_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2980_);
v___x_2984_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_2985_ = l_Lean_Expr_isConstOf(v___x_2983_, v___x_2984_);
if (v___x_2985_ == 0)
{
uint8_t v___x_2986_; 
v___x_2986_ = l_Lean_Expr_isApp(v___x_2983_);
if (v___x_2986_ == 0)
{
lean_dec_ref(v___x_2983_);
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_arg_2979_);
lean_dec_ref(v_arg_2976_);
lean_dec_ref(v_body_2802_);
lean_dec(v_mvarId_2789_);
v___y_2960_ = v___y_2791_;
v___y_2961_ = v___y_2792_;
v___y_2962_ = v___y_2793_;
v___y_2963_ = v___y_2794_;
goto v___jp_2959_;
}
else
{
lean_object* v_arg_2987_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___y_2991_; lean_object* v___y_2992_; lean_object* v___x_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; 
v_arg_2987_ = lean_ctor_get(v___x_2983_, 1);
lean_inc_ref(v_arg_2987_);
v___x_2995_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2983_);
v___x_2996_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_2997_ = l_Lean_Expr_isConstOf(v___x_2995_, v___x_2996_);
lean_dec_ref(v___x_2995_);
if (v___x_2997_ == 0)
{
lean_dec_ref(v_arg_2987_);
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_arg_2979_);
lean_dec_ref(v_arg_2976_);
lean_dec_ref(v_body_2802_);
lean_dec(v_mvarId_2789_);
v___y_2960_ = v___y_2791_;
v___y_2961_ = v___y_2792_;
v___y_2962_ = v___y_2793_;
v___y_2963_ = v___y_2794_;
goto v___jp_2959_;
}
else
{
lean_object* v___x_2998_; 
lean_inc_ref(v_arg_2987_);
v___x_2998_ = l_Lean_Meta_isExprDefEq(v_arg_2987_, v_arg_2979_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
if (lean_obj_tag(v___x_2998_) == 0)
{
lean_object* v_a_2999_; uint8_t v___x_3000_; 
v_a_2999_ = lean_ctor_get(v___x_2998_, 0);
lean_inc(v_a_2999_);
lean_dec_ref(v___x_2998_);
v___x_3000_ = lean_unbox(v_a_2999_);
lean_dec(v_a_2999_);
if (v___x_3000_ == 0)
{
lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v_arg_2987_);
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_arg_2976_);
lean_dec_ref(v_body_2802_);
lean_dec(v_mvarId_2789_);
v___x_3001_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_3002_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3001_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_3002_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
else
{
v___y_2989_ = v___y_2791_;
v___y_2990_ = v___y_2792_;
v___y_2991_ = v___y_2793_;
v___y_2992_ = v___y_2794_;
goto v___jp_2988_;
}
}
else
{
lean_object* v_a_3011_; lean_object* v___x_3013_; uint8_t v_isShared_3014_; uint8_t v_isSharedCheck_3018_; 
lean_dec_ref(v_arg_2987_);
lean_dec_ref(v_arg_2982_);
lean_dec_ref(v_arg_2976_);
lean_dec_ref(v_body_2802_);
lean_dec(v_mvarId_2789_);
v_a_3011_ = lean_ctor_get(v___x_2998_, 0);
v_isSharedCheck_3018_ = !lean_is_exclusive(v___x_2998_);
if (v_isSharedCheck_3018_ == 0)
{
v___x_3013_ = v___x_2998_;
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
else
{
lean_inc(v_a_3011_);
lean_dec(v___x_2998_);
v___x_3013_ = lean_box(0);
v_isShared_3014_ = v_isSharedCheck_3018_;
goto v_resetjp_3012_;
}
v_resetjp_3012_:
{
lean_object* v___x_3016_; 
if (v_isShared_3014_ == 0)
{
v___x_3016_ = v___x_3013_;
goto v_reusejp_3015_;
}
else
{
lean_object* v_reuseFailAlloc_3017_; 
v_reuseFailAlloc_3017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3017_, 0, v_a_3011_);
v___x_3016_ = v_reuseFailAlloc_3017_;
goto v_reusejp_3015_;
}
v_reusejp_3015_:
{
return v___x_3016_;
}
}
}
}
v___jp_2988_:
{
if (v_substLHS_2790_ == 0)
{
lean_object* v___x_2993_; 
v___x_2993_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2938_ = v_arg_2987_;
v_fst_2939_ = v_arg_2982_;
v_fst_2940_ = v_arg_2976_;
v_snd_2941_ = v___x_2993_;
v___y_2942_ = v___y_2989_;
v___y_2943_ = v___y_2990_;
v___y_2944_ = v___y_2991_;
v___y_2945_ = v___y_2992_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_2994_; 
v___x_2994_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2938_ = v_arg_2987_;
v_fst_2939_ = v_arg_2976_;
v_fst_2940_ = v_arg_2982_;
v_snd_2941_ = v___x_2994_;
v___y_2942_ = v___y_2989_;
v___y_2943_ = v___y_2990_;
v___y_2944_ = v___y_2991_;
v___y_2945_ = v___y_2992_;
goto v___jp_2937_;
}
}
}
}
else
{
lean_dec_ref(v___x_2983_);
if (v_substLHS_2790_ == 0)
{
lean_object* v___x_3019_; 
v___x_3019_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2938_ = v_arg_2982_;
v_fst_2939_ = v_arg_2979_;
v_fst_2940_ = v_arg_2976_;
v_snd_2941_ = v___x_3019_;
v___y_2942_ = v___y_2791_;
v___y_2943_ = v___y_2792_;
v___y_2944_ = v___y_2793_;
v___y_2945_ = v___y_2794_;
goto v___jp_2937_;
}
else
{
lean_object* v___x_3020_; 
v___x_3020_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2938_ = v_arg_2982_;
v_fst_2939_ = v_arg_2976_;
v_fst_2940_ = v_arg_2979_;
v_snd_2941_ = v___x_3020_;
v___y_2942_ = v___y_2791_;
v___y_2943_ = v___y_2792_;
v___y_2944_ = v___y_2793_;
v___y_2945_ = v___y_2794_;
goto v___jp_2937_;
}
}
}
}
}
v___jp_2959_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
v___x_2964_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_2965_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2964_, v___y_2960_, v___y_2961_, v___y_2962_, v___y_2963_);
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2965_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2965_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec_ref(v_body_2802_);
lean_dec(v_mvarId_2789_);
v_a_3021_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2957_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2957_);
v___x_3023_ = lean_box(0);
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
v_resetjp_3022_:
{
lean_object* v___x_3026_; 
if (v_isShared_3024_ == 0)
{
v___x_3026_ = v___x_3023_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3027_; 
v_reuseFailAlloc_3027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3027_, 0, v_a_3021_);
v___x_3026_ = v_reuseFailAlloc_3027_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
return v___x_3026_;
}
}
}
}
else
{
lean_dec_ref(v_body_2802_);
lean_dec_ref(v_binderType_2801_);
lean_dec(v_mvarId_2789_);
goto v___jp_2798_;
}
v___jp_2804_:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; uint8_t v___x_2819_; lean_object* v___x_2820_; 
v___x_2816_ = lean_mk_empty_array_with_capacity(v___y_2809_);
lean_inc_ref(v___x_2816_);
v___x_2817_ = lean_array_push(v___x_2816_, v___y_2811_);
v___x_2818_ = 1;
v___x_2819_ = 1;
v___x_2820_ = l_Lean_Meta_mkLambdaFVars(v___x_2817_, v_body_2802_, v___x_2803_, v___x_2818_, v___x_2803_, v___x_2818_, v___x_2819_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
lean_dec_ref(v___x_2817_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref(v___x_2820_);
lean_inc(v___y_2810_);
v___x_2822_ = l_Lean_MVarId_getTag(v___y_2810_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref(v___x_2822_);
lean_inc_ref(v___y_2805_);
v___x_2824_ = lean_array_push(v___x_2816_, v___y_2805_);
lean_inc(v_a_2821_);
v___x_2825_ = l_Lean_Expr_beta(v_a_2821_, v___x_2824_);
lean_inc_ref(v___x_2825_);
v___x_2826_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2825_, v_a_2823_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___x_2826_);
v___x_2828_ = l_Lean_Meta_getLevel(v___x_2825_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref(v___x_2828_);
lean_inc_ref(v___y_2807_);
v___x_2830_ = l_Lean_Meta_getLevel(v___y_2807_, v___y_2812_, v___y_2813_, v___y_2814_, v___y_2815_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2848_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref(v___x_2830_);
v___x_2832_ = lean_box(0);
v___x_2833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2833_, 0, v_a_2831_);
lean_ctor_set(v___x_2833_, 1, v___x_2832_);
v___x_2834_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2834_, 0, v_a_2829_);
lean_ctor_set(v___x_2834_, 1, v___x_2833_);
lean_inc(v___y_2806_);
v___x_2835_ = l_Lean_mkConst(v___y_2806_, v___x_2834_);
lean_inc(v_a_2827_);
lean_inc_ref(v___y_2805_);
v___x_2836_ = l_Lean_mkApp4(v___x_2835_, v___y_2807_, v___y_2805_, v_a_2821_, v_a_2827_);
v___x_2837_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v___y_2810_, v___x_2836_, v___y_2813_);
v_isSharedCheck_2848_ = !lean_is_exclusive(v___x_2837_);
if (v_isSharedCheck_2848_ == 0)
{
lean_object* v_unused_2849_; 
v_unused_2849_ = lean_ctor_get(v___x_2837_, 0);
lean_dec(v_unused_2849_);
v___x_2839_ = v___x_2837_;
v_isShared_2840_ = v_isSharedCheck_2848_;
goto v_resetjp_2838_;
}
else
{
lean_dec(v___x_2837_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2848_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2841_ = l_Lean_Meta_FVarSubst_empty;
v___x_2842_ = l_Lean_Meta_FVarSubst_insert(v___x_2841_, v___y_2808_, v___y_2805_);
v___x_2843_ = l_Lean_Expr_mvarId_x21(v_a_2827_);
lean_dec(v_a_2827_);
v___x_2844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2842_);
lean_ctor_set(v___x_2844_, 1, v___x_2843_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 0, v___x_2844_);
v___x_2846_ = v___x_2839_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2844_);
v___x_2846_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
return v___x_2846_;
}
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v_a_2829_);
lean_dec(v_a_2827_);
lean_dec(v_a_2821_);
lean_dec(v___y_2810_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2805_);
v_a_2850_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2830_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2830_);
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
lean_dec(v_a_2827_);
lean_dec(v_a_2821_);
lean_dec(v___y_2810_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2805_);
v_a_2858_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2828_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2828_);
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
lean_dec_ref(v___x_2825_);
lean_dec(v_a_2821_);
lean_dec(v___y_2810_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2805_);
v_a_2866_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2826_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2826_);
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
else
{
lean_object* v_a_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2881_; 
lean_dec(v_a_2821_);
lean_dec_ref(v___x_2816_);
lean_dec(v___y_2810_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2805_);
v_a_2874_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2822_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2822_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___x_2879_; 
if (v_isShared_2877_ == 0)
{
v___x_2879_ = v___x_2876_;
goto v_reusejp_2878_;
}
else
{
lean_object* v_reuseFailAlloc_2880_; 
v_reuseFailAlloc_2880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2880_, 0, v_a_2874_);
v___x_2879_ = v_reuseFailAlloc_2880_;
goto v_reusejp_2878_;
}
v_reusejp_2878_:
{
return v___x_2879_;
}
}
}
}
else
{
lean_object* v_a_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2889_; 
lean_dec_ref(v___x_2816_);
lean_dec(v___y_2810_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec_ref(v___y_2805_);
v_a_2882_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2889_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2889_ == 0)
{
v___x_2884_ = v___x_2820_;
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_a_2882_);
lean_dec(v___x_2820_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2889_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2887_; 
if (v_isShared_2885_ == 0)
{
v___x_2887_ = v___x_2884_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_a_2882_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
}
}
v___jp_2890_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; 
v___x_2899_ = l_Lean_Expr_fvarId_x21(v___y_2894_);
v___x_2900_ = lean_unsigned_to_nat(1u);
v___x_2901_ = lean_mk_empty_array_with_capacity(v___x_2900_);
lean_inc(v___x_2899_);
v___x_2902_ = lean_array_push(v___x_2901_, v___x_2899_);
v___x_2903_ = l_Lean_MVarId_revert(v_mvarId_2789_, v___x_2902_, v___x_2803_, v___x_2803_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
if (lean_obj_tag(v___x_2903_) == 0)
{
lean_object* v_a_2904_; lean_object* v_fst_2905_; lean_object* v_snd_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2928_; 
v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
lean_inc(v_a_2904_);
lean_dec_ref(v___x_2903_);
v_fst_2905_ = lean_ctor_get(v_a_2904_, 0);
v_snd_2906_ = lean_ctor_get(v_a_2904_, 1);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_a_2904_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2908_ = v_a_2904_;
v_isShared_2909_ = v_isSharedCheck_2928_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_snd_2906_);
lean_inc(v_fst_2905_);
lean_dec(v_a_2904_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2928_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = lean_array_get_size(v_fst_2905_);
lean_dec(v_fst_2905_);
v___x_2911_ = lean_nat_dec_eq(v___x_2910_, v___x_2900_);
if (v___x_2911_ == 0)
{
lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2915_; 
lean_dec(v_snd_2906_);
lean_dec(v___x_2899_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec_ref(v_body_2802_);
v___x_2912_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2913_ = l_Lean_MessageData_ofExpr(v___y_2894_);
if (v_isShared_2909_ == 0)
{
lean_ctor_set_tag(v___x_2908_, 7);
lean_ctor_set(v___x_2908_, 1, v___x_2913_);
lean_ctor_set(v___x_2908_, 0, v___x_2912_);
v___x_2915_ = v___x_2908_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v___x_2912_);
lean_ctor_set(v_reuseFailAlloc_2927_, 1, v___x_2913_);
v___x_2915_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2918_; lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
v___x_2916_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2917_, 0, v___x_2915_);
lean_ctor_set(v___x_2917_, 1, v___x_2916_);
v___x_2918_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2917_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2918_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2918_);
v___x_2921_ = lean_box(0);
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
v_resetjp_2920_:
{
lean_object* v___x_2924_; 
if (v_isShared_2922_ == 0)
{
v___x_2924_ = v___x_2921_;
goto v_reusejp_2923_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
v___x_2924_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2923_;
}
v_reusejp_2923_:
{
return v___x_2924_;
}
}
}
}
else
{
lean_del_object(v___x_2908_);
v___y_2805_ = v___y_2891_;
v___y_2806_ = v___y_2893_;
v___y_2807_ = v___y_2892_;
v___y_2808_ = v___x_2899_;
v___y_2809_ = v___x_2900_;
v___y_2810_ = v_snd_2906_;
v___y_2811_ = v___y_2894_;
v___y_2812_ = v___y_2895_;
v___y_2813_ = v___y_2896_;
v___y_2814_ = v___y_2897_;
v___y_2815_ = v___y_2898_;
goto v___jp_2804_;
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec(v___x_2899_);
lean_dec_ref(v___y_2894_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2891_);
lean_dec_ref(v_body_2802_);
v_a_2929_ = lean_ctor_get(v___x_2903_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2903_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2903_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2903_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
}
}
}
}
v___jp_2937_:
{
uint8_t v___x_2946_; 
v___x_2946_ = l_Lean_Expr_isFVar(v_fst_2940_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_dec_ref(v_fst_2940_);
lean_dec_ref(v_fst_2939_);
lean_dec_ref(v_fst_2938_);
lean_dec_ref(v_body_2802_);
lean_dec(v_mvarId_2789_);
v___x_2947_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2948_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2947_, v___y_2942_, v___y_2943_, v___y_2944_, v___y_2945_);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
else
{
v___y_2891_ = v_fst_2939_;
v___y_2892_ = v_fst_2938_;
v___y_2893_ = v_snd_2941_;
v___y_2894_ = v_fst_2940_;
v___y_2895_ = v___y_2942_;
v___y_2896_ = v___y_2943_;
v___y_2897_ = v___y_2944_;
v___y_2898_ = v___y_2945_;
goto v___jp_2890_;
}
}
}
else
{
lean_dec(v_a_2797_);
lean_dec(v_mvarId_2789_);
goto v___jp_2798_;
}
v___jp_2798_:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; 
v___x_2799_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2800_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2799_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_);
return v___x_2800_;
}
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec(v_mvarId_2789_);
v_a_3029_ = lean_ctor_get(v___x_2796_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2796_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_2796_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_2796_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object* v_mvarId_3037_, lean_object* v_substLHS_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_, lean_object* v___y_3043_){
_start:
{
uint8_t v_substLHS_boxed_3044_; lean_object* v_res_3045_; 
v_substLHS_boxed_3044_ = lean_unbox(v_substLHS_3038_);
v_res_3045_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_3037_, v_substLHS_boxed_3044_, v___y_3039_, v___y_3040_, v___y_3041_, v___y_3042_);
lean_dec(v___y_3042_);
lean_dec_ref(v___y_3041_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
return v_res_3045_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3046_, lean_object* v_i_3047_, lean_object* v_k_3048_){
_start:
{
lean_object* v___x_3049_; uint8_t v___x_3050_; 
v___x_3049_ = lean_array_get_size(v_keys_3046_);
v___x_3050_ = lean_nat_dec_lt(v_i_3047_, v___x_3049_);
if (v___x_3050_ == 0)
{
lean_dec(v_i_3047_);
return v___x_3050_;
}
else
{
lean_object* v_k_x27_3051_; uint8_t v___x_3052_; 
v_k_x27_3051_ = lean_array_fget_borrowed(v_keys_3046_, v_i_3047_);
v___x_3052_ = l_Lean_instBEqMVarId_beq(v_k_3048_, v_k_x27_3051_);
if (v___x_3052_ == 0)
{
lean_object* v___x_3053_; lean_object* v___x_3054_; 
v___x_3053_ = lean_unsigned_to_nat(1u);
v___x_3054_ = lean_nat_add(v_i_3047_, v___x_3053_);
lean_dec(v_i_3047_);
v_i_3047_ = v___x_3054_;
goto _start;
}
else
{
lean_dec(v_i_3047_);
return v___x_3052_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3056_, lean_object* v_i_3057_, lean_object* v_k_3058_){
_start:
{
uint8_t v_res_3059_; lean_object* v_r_3060_; 
v_res_3059_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3056_, v_i_3057_, v_k_3058_);
lean_dec(v_k_3058_);
lean_dec_ref(v_keys_3056_);
v_r_3060_ = lean_box(v_res_3059_);
return v_r_3060_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3061_, size_t v_x_3062_, lean_object* v_x_3063_){
_start:
{
if (lean_obj_tag(v_x_3061_) == 0)
{
lean_object* v_es_3064_; lean_object* v___x_3065_; size_t v___x_3066_; size_t v___x_3067_; size_t v___x_3068_; lean_object* v_j_3069_; lean_object* v___x_3070_; 
v_es_3064_ = lean_ctor_get(v_x_3061_, 0);
v___x_3065_ = lean_box(2);
v___x_3066_ = ((size_t)5ULL);
v___x_3067_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1);
v___x_3068_ = lean_usize_land(v_x_3062_, v___x_3067_);
v_j_3069_ = lean_usize_to_nat(v___x_3068_);
v___x_3070_ = lean_array_get_borrowed(v___x_3065_, v_es_3064_, v_j_3069_);
lean_dec(v_j_3069_);
switch(lean_obj_tag(v___x_3070_))
{
case 0:
{
lean_object* v_key_3071_; uint8_t v___x_3072_; 
v_key_3071_ = lean_ctor_get(v___x_3070_, 0);
v___x_3072_ = l_Lean_instBEqMVarId_beq(v_x_3063_, v_key_3071_);
return v___x_3072_;
}
case 1:
{
lean_object* v_node_3073_; size_t v___x_3074_; 
v_node_3073_ = lean_ctor_get(v___x_3070_, 0);
v___x_3074_ = lean_usize_shift_right(v_x_3062_, v___x_3066_);
v_x_3061_ = v_node_3073_;
v_x_3062_ = v___x_3074_;
goto _start;
}
default: 
{
uint8_t v___x_3076_; 
v___x_3076_ = 0;
return v___x_3076_;
}
}
}
else
{
lean_object* v_ks_3077_; lean_object* v___x_3078_; uint8_t v___x_3079_; 
v_ks_3077_ = lean_ctor_get(v_x_3061_, 0);
v___x_3078_ = lean_unsigned_to_nat(0u);
v___x_3079_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3077_, v___x_3078_, v_x_3063_);
return v___x_3079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3080_, lean_object* v_x_3081_, lean_object* v_x_3082_){
_start:
{
size_t v_x_12612__boxed_3083_; uint8_t v_res_3084_; lean_object* v_r_3085_; 
v_x_12612__boxed_3083_ = lean_unbox_usize(v_x_3081_);
lean_dec(v_x_3081_);
v_res_3084_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3080_, v_x_12612__boxed_3083_, v_x_3082_);
lean_dec(v_x_3082_);
lean_dec_ref(v_x_3080_);
v_r_3085_ = lean_box(v_res_3084_);
return v_r_3085_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3086_, lean_object* v_x_3087_){
_start:
{
uint64_t v___x_3088_; size_t v___x_3089_; uint8_t v___x_3090_; 
v___x_3088_ = l_Lean_instHashableMVarId_hash(v_x_3087_);
v___x_3089_ = lean_uint64_to_usize(v___x_3088_);
v___x_3090_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3086_, v___x_3089_, v_x_3087_);
return v___x_3090_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3091_, lean_object* v_x_3092_){
_start:
{
uint8_t v_res_3093_; lean_object* v_r_3094_; 
v_res_3093_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3091_, v_x_3092_);
lean_dec(v_x_3092_);
lean_dec_ref(v_x_3091_);
v_r_3094_ = lean_box(v_res_3093_);
return v_r_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3095_, lean_object* v___y_3096_){
_start:
{
lean_object* v___x_3098_; lean_object* v_mctx_3099_; lean_object* v_eAssignment_3100_; uint8_t v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v___x_3098_ = lean_st_ref_get(v___y_3096_);
v_mctx_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc_ref(v_mctx_3099_);
lean_dec(v___x_3098_);
v_eAssignment_3100_ = lean_ctor_get(v_mctx_3099_, 8);
lean_inc_ref(v_eAssignment_3100_);
lean_dec_ref(v_mctx_3099_);
v___x_3101_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3100_, v_mvarId_3095_);
lean_dec_ref(v_eAssignment_3100_);
v___x_3102_ = lean_box(v___x_3101_);
v___x_3103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3103_, 0, v___x_3102_);
return v___x_3103_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_){
_start:
{
lean_object* v_res_3107_; 
v_res_3107_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3104_, v___y_3105_);
lean_dec(v___y_3105_);
lean_dec(v_mvarId_3104_);
return v_res_3107_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3110_ = l_Lean_stringToMessageData(v___x_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3111_, uint8_t v___y_3112_, lean_object* v_____r_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_, lean_object* v___y_3116_, lean_object* v___y_3117_){
_start:
{
lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; lean_object* v___y_3123_; lean_object* v___x_3155_; lean_object* v_a_3156_; uint8_t v___x_3157_; 
v___x_3155_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3111_, v___y_3115_);
v_a_3156_ = lean_ctor_get(v___x_3155_, 0);
lean_inc(v_a_3156_);
lean_dec_ref(v___x_3155_);
v___x_3157_ = lean_unbox(v_a_3156_);
lean_dec(v_a_3156_);
if (v___x_3157_ == 0)
{
v___y_3120_ = v___y_3114_;
v___y_3121_ = v___y_3115_;
v___y_3122_ = v___y_3116_;
v___y_3123_ = v___y_3117_;
goto v___jp_3119_;
}
else
{
lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
lean_dec(v_mvarId_3111_);
v___x_3158_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3159_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3158_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
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
v___jp_3119_:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_Lean_Meta_intro1Core(v_mvarId_3111_, v___y_3112_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; lean_object* v_fst_3126_; lean_object* v_snd_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref(v___x_3124_);
v_fst_3126_ = lean_ctor_get(v_a_3125_, 0);
lean_inc(v_fst_3126_);
v_snd_3127_ = lean_ctor_get(v_a_3125_, 1);
lean_inc(v_snd_3127_);
lean_dec(v_a_3125_);
v___x_3128_ = lean_box(0);
v___x_3129_ = l_Lean_Meta_substEq(v_snd_3127_, v_fst_3126_, v___x_3128_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_);
if (lean_obj_tag(v___x_3129_) == 0)
{
lean_object* v_a_3130_; lean_object* v___x_3132_; uint8_t v_isShared_3133_; uint8_t v_isSharedCheck_3138_; 
v_a_3130_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3132_ = v___x_3129_;
v_isShared_3133_ = v_isSharedCheck_3138_;
goto v_resetjp_3131_;
}
else
{
lean_inc(v_a_3130_);
lean_dec(v___x_3129_);
v___x_3132_ = lean_box(0);
v_isShared_3133_ = v_isSharedCheck_3138_;
goto v_resetjp_3131_;
}
v_resetjp_3131_:
{
lean_object* v___x_3134_; lean_object* v___x_3136_; 
v___x_3134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3134_, 0, v_a_3130_);
if (v_isShared_3133_ == 0)
{
lean_ctor_set(v___x_3132_, 0, v___x_3134_);
v___x_3136_ = v___x_3132_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v___x_3134_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
v_a_3139_ = lean_ctor_get(v___x_3129_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3129_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3129_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3129_);
v___x_3141_ = lean_box(0);
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
v_resetjp_3140_:
{
lean_object* v___x_3144_; 
if (v_isShared_3142_ == 0)
{
v___x_3144_ = v___x_3141_;
goto v_reusejp_3143_;
}
else
{
lean_object* v_reuseFailAlloc_3145_; 
v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
v___x_3144_ = v_reuseFailAlloc_3145_;
goto v_reusejp_3143_;
}
v_reusejp_3143_:
{
return v___x_3144_;
}
}
}
}
else
{
lean_object* v_a_3147_; lean_object* v___x_3149_; uint8_t v_isShared_3150_; uint8_t v_isSharedCheck_3154_; 
v_a_3147_ = lean_ctor_get(v___x_3124_, 0);
v_isSharedCheck_3154_ = !lean_is_exclusive(v___x_3124_);
if (v_isSharedCheck_3154_ == 0)
{
v___x_3149_ = v___x_3124_;
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
else
{
lean_inc(v_a_3147_);
lean_dec(v___x_3124_);
v___x_3149_ = lean_box(0);
v_isShared_3150_ = v_isSharedCheck_3154_;
goto v_resetjp_3148_;
}
v_resetjp_3148_:
{
lean_object* v___x_3152_; 
if (v_isShared_3150_ == 0)
{
v___x_3152_ = v___x_3149_;
goto v_reusejp_3151_;
}
else
{
lean_object* v_reuseFailAlloc_3153_; 
v_reuseFailAlloc_3153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3153_, 0, v_a_3147_);
v___x_3152_ = v_reuseFailAlloc_3153_;
goto v_reusejp_3151_;
}
v_reusejp_3151_:
{
return v___x_3152_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3168_, lean_object* v___y_3169_, lean_object* v_____r_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
uint8_t v___y_12686__boxed_3176_; lean_object* v_res_3177_; 
v___y_12686__boxed_3176_ = lean_unbox(v___y_3169_);
v_res_3177_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3168_, v___y_12686__boxed_3176_, v_____r_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
lean_dec(v___y_3174_);
lean_dec_ref(v___y_3173_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
return v_res_3177_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__2(void){
_start:
{
lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3181_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3182_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
v___x_3183_ = l_Lean_Name_append(v___x_3182_, v___x_3181_);
return v___x_3183_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__4(void){
_start:
{
lean_object* v___x_3185_; lean_object* v___x_3186_; 
v___x_3185_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__3));
v___x_3186_ = l_Lean_stringToMessageData(v___x_3185_);
return v___x_3186_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__6(void){
_start:
{
lean_object* v___x_3188_; lean_object* v___x_3189_; 
v___x_3188_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__5));
v___x_3189_ = l_Lean_stringToMessageData(v___x_3188_);
return v___x_3189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3190_, uint8_t v_substLHS_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_, lean_object* v_a_3194_, lean_object* v_a_3195_){
_start:
{
lean_object* v___y_3198_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v___x_3216_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
lean_inc(v_mvarId_3190_);
v___x_3217_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3190_, v___x_3216_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v___x_3218_; lean_object* v___f_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; 
lean_dec_ref(v___x_3217_);
v___x_3218_ = lean_box(v_substLHS_3191_);
lean_inc_n(v_mvarId_3190_, 2);
v___f_3219_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3219_, 0, v_mvarId_3190_);
lean_closure_set(v___f_3219_, 1, v___x_3218_);
v___x_3220_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed), 8, 3);
lean_closure_set(v___x_3220_, 0, lean_box(0));
lean_closure_set(v___x_3220_, 1, v_mvarId_3190_);
lean_closure_set(v___x_3220_, 2, v___f_3219_);
v___x_3221_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3220_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_);
if (lean_obj_tag(v___x_3221_) == 0)
{
lean_dec(v_mvarId_3190_);
return v___x_3221_;
}
else
{
lean_object* v_a_3222_; lean_object* v___y_3224_; uint8_t v___y_3228_; uint8_t v___x_3262_; 
v_a_3222_ = lean_ctor_get(v___x_3221_, 0);
lean_inc(v_a_3222_);
v___x_3262_ = l_Lean_Exception_isInterrupt(v_a_3222_);
if (v___x_3262_ == 0)
{
uint8_t v___x_3263_; 
lean_inc(v_a_3222_);
v___x_3263_ = l_Lean_Exception_isRuntime(v_a_3222_);
v___y_3228_ = v___x_3263_;
goto v___jp_3227_;
}
else
{
v___y_3228_ = v___x_3262_;
goto v___jp_3227_;
}
v___jp_3223_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; 
v___x_3225_ = lean_box(0);
lean_inc(v_a_3195_);
lean_inc_ref(v_a_3194_);
lean_inc(v_a_3193_);
lean_inc_ref(v_a_3192_);
v___x_3226_ = lean_apply_6(v___y_3224_, v___x_3225_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, lean_box(0));
v___y_3198_ = v___x_3226_;
goto v___jp_3197_;
}
v___jp_3227_:
{
if (v___y_3228_ == 0)
{
lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3260_; 
v_isSharedCheck_3260_ = !lean_is_exclusive(v___x_3221_);
if (v_isSharedCheck_3260_ == 0)
{
lean_object* v_unused_3261_; 
v_unused_3261_ = lean_ctor_get(v___x_3221_, 0);
lean_dec(v_unused_3261_);
v___x_3230_ = v___x_3221_;
v_isShared_3231_ = v_isSharedCheck_3260_;
goto v_resetjp_3229_;
}
else
{
lean_dec(v___x_3221_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3260_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v_options_3232_; lean_object* v_inheritedTraceOptions_3233_; uint8_t v_hasTrace_3234_; lean_object* v___x_3235_; lean_object* v___f_3236_; 
v_options_3232_ = lean_ctor_get(v_a_3194_, 2);
v_inheritedTraceOptions_3233_ = lean_ctor_get(v_a_3194_, 13);
v_hasTrace_3234_ = lean_ctor_get_uint8(v_options_3232_, sizeof(void*)*1);
v___x_3235_ = lean_box(v___y_3228_);
lean_inc(v_mvarId_3190_);
v___f_3236_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3236_, 0, v_mvarId_3190_);
lean_closure_set(v___f_3236_, 1, v___x_3235_);
if (v_hasTrace_3234_ == 0)
{
lean_del_object(v___x_3230_);
lean_dec(v_a_3222_);
lean_dec(v_mvarId_3190_);
v___y_3224_ = v___f_3236_;
goto v___jp_3223_;
}
else
{
lean_object* v___x_3237_; lean_object* v___x_3238_; uint8_t v___x_3239_; 
v___x_3237_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3238_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__2, &l_Lean_Meta_introSubstEq___closed__2_once, _init_l_Lean_Meta_introSubstEq___closed__2);
v___x_3239_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3233_, v_options_3232_, v___x_3238_);
if (v___x_3239_ == 0)
{
lean_del_object(v___x_3230_);
lean_dec(v_a_3222_);
lean_dec(v_mvarId_3190_);
v___y_3224_ = v___f_3236_;
goto v___jp_3223_;
}
else
{
lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; lean_object* v___x_3246_; 
lean_dec_ref(v___f_3236_);
v___x_3240_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__4, &l_Lean_Meta_introSubstEq___closed__4_once, _init_l_Lean_Meta_introSubstEq___closed__4);
v___x_3241_ = l_Lean_Exception_toMessageData(v_a_3222_);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
v___x_3243_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__6, &l_Lean_Meta_introSubstEq___closed__6_once, _init_l_Lean_Meta_introSubstEq___closed__6);
v___x_3244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3242_);
lean_ctor_set(v___x_3244_, 1, v___x_3243_);
lean_inc(v_mvarId_3190_);
if (v_isShared_3231_ == 0)
{
lean_ctor_set(v___x_3230_, 0, v_mvarId_3190_);
v___x_3246_ = v___x_3230_;
goto v_reusejp_3245_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_mvarId_3190_);
v___x_3246_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3245_;
}
v_reusejp_3245_:
{
lean_object* v___x_3247_; lean_object* v___x_3248_; 
v___x_3247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3244_);
lean_ctor_set(v___x_3247_, 1, v___x_3246_);
v___x_3248_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_3237_, v___x_3247_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; lean_object* v___x_3250_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref(v___x_3248_);
v___x_3250_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3190_, v___y_3228_, v_a_3249_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_);
v___y_3198_ = v___x_3250_;
goto v___jp_3197_;
}
else
{
lean_object* v_a_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3258_; 
lean_dec(v_mvarId_3190_);
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
}
}
else
{
lean_dec(v_a_3222_);
lean_dec(v_mvarId_3190_);
return v___x_3221_;
}
}
}
}
else
{
lean_object* v_a_3264_; lean_object* v___x_3266_; uint8_t v_isShared_3267_; uint8_t v_isSharedCheck_3271_; 
lean_dec(v_mvarId_3190_);
v_a_3264_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3271_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3271_ == 0)
{
v___x_3266_ = v___x_3217_;
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
else
{
lean_inc(v_a_3264_);
lean_dec(v___x_3217_);
v___x_3266_ = lean_box(0);
v_isShared_3267_ = v_isSharedCheck_3271_;
goto v_resetjp_3265_;
}
v_resetjp_3265_:
{
lean_object* v___x_3269_; 
if (v_isShared_3267_ == 0)
{
v___x_3269_ = v___x_3266_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3270_; 
v_reuseFailAlloc_3270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3270_, 0, v_a_3264_);
v___x_3269_ = v_reuseFailAlloc_3270_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
return v___x_3269_;
}
}
}
v___jp_3197_:
{
if (lean_obj_tag(v___y_3198_) == 0)
{
lean_object* v_a_3199_; lean_object* v___x_3201_; uint8_t v_isShared_3202_; uint8_t v_isSharedCheck_3207_; 
v_a_3199_ = lean_ctor_get(v___y_3198_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___y_3198_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3201_ = v___y_3198_;
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
else
{
lean_inc(v_a_3199_);
lean_dec(v___y_3198_);
v___x_3201_ = lean_box(0);
v_isShared_3202_ = v_isSharedCheck_3207_;
goto v_resetjp_3200_;
}
v_resetjp_3200_:
{
lean_object* v_a_3203_; lean_object* v___x_3205_; 
v_a_3203_ = lean_ctor_get(v_a_3199_, 0);
lean_inc(v_a_3203_);
lean_dec(v_a_3199_);
if (v_isShared_3202_ == 0)
{
lean_ctor_set(v___x_3201_, 0, v_a_3203_);
v___x_3205_ = v___x_3201_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3203_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
v_a_3208_ = lean_ctor_get(v___y_3198_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___y_3198_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___y_3198_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___y_3198_);
v___x_3210_ = lean_box(0);
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
v_resetjp_3209_:
{
lean_object* v___x_3213_; 
if (v_isShared_3211_ == 0)
{
v___x_3213_ = v___x_3210_;
goto v_reusejp_3212_;
}
else
{
lean_object* v_reuseFailAlloc_3214_; 
v_reuseFailAlloc_3214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3214_, 0, v_a_3208_);
v___x_3213_ = v_reuseFailAlloc_3214_;
goto v_reusejp_3212_;
}
v_reusejp_3212_:
{
return v___x_3213_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object* v_mvarId_3272_, lean_object* v_substLHS_3273_, lean_object* v_a_3274_, lean_object* v_a_3275_, lean_object* v_a_3276_, lean_object* v_a_3277_, lean_object* v_a_3278_){
_start:
{
uint8_t v_substLHS_boxed_3279_; lean_object* v_res_3280_; 
v_substLHS_boxed_3279_ = lean_unbox(v_substLHS_3273_);
v_res_3280_ = l_Lean_Meta_introSubstEq(v_mvarId_3272_, v_substLHS_boxed_3279_, v_a_3274_, v_a_3275_, v_a_3276_, v_a_3277_);
lean_dec(v_a_3277_);
lean_dec_ref(v_a_3276_);
lean_dec(v_a_3275_);
lean_dec_ref(v_a_3274_);
return v_res_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object* v_00_u03b1_3281_, lean_object* v_msg_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
return v___x_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object* v_00_u03b1_3289_, lean_object* v_msg_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v_res_3296_; 
v_res_3296_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(v_00_u03b1_3289_, v_msg_3290_, v___y_3291_, v___y_3292_, v___y_3293_, v___y_3294_);
lean_dec(v___y_3294_);
lean_dec_ref(v___y_3293_);
lean_dec(v___y_3292_);
lean_dec_ref(v___y_3291_);
return v_res_3296_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object* v_mvarId_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v___x_3303_; 
v___x_3303_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3297_, v___y_3299_);
return v___x_3303_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object* v_mvarId_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_, lean_object* v___y_3309_){
_start:
{
lean_object* v_res_3310_; 
v_res_3310_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_);
lean_dec(v___y_3308_);
lean_dec_ref(v___y_3307_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v_mvarId_3304_);
return v_res_3310_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object* v_00_u03b2_3311_, lean_object* v_x_3312_, lean_object* v_x_3313_){
_start:
{
uint8_t v___x_3314_; 
v___x_3314_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3312_, v_x_3313_);
return v___x_3314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3315_, lean_object* v_x_3316_, lean_object* v_x_3317_){
_start:
{
uint8_t v_res_3318_; lean_object* v_r_3319_; 
v_res_3318_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(v_00_u03b2_3315_, v_x_3316_, v_x_3317_);
lean_dec(v_x_3317_);
lean_dec_ref(v_x_3316_);
v_r_3319_ = lean_box(v_res_3318_);
return v_r_3319_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_3320_, lean_object* v_x_3321_, size_t v_x_3322_, lean_object* v_x_3323_){
_start:
{
uint8_t v___x_3324_; 
v___x_3324_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3321_, v_x_3322_, v_x_3323_);
return v___x_3324_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3325_, lean_object* v_x_3326_, lean_object* v_x_3327_, lean_object* v_x_3328_){
_start:
{
size_t v_x_13050__boxed_3329_; uint8_t v_res_3330_; lean_object* v_r_3331_; 
v_x_13050__boxed_3329_ = lean_unbox_usize(v_x_3327_);
lean_dec(v_x_3327_);
v_res_3330_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3325_, v_x_3326_, v_x_13050__boxed_3329_, v_x_3328_);
lean_dec(v_x_3328_);
lean_dec_ref(v_x_3326_);
v_r_3331_ = lean_box(v_res_3330_);
return v_r_3331_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3332_, lean_object* v_keys_3333_, lean_object* v_vals_3334_, lean_object* v_heq_3335_, lean_object* v_i_3336_, lean_object* v_k_3337_){
_start:
{
uint8_t v___x_3338_; 
v___x_3338_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3333_, v_i_3336_, v_k_3337_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3339_, lean_object* v_keys_3340_, lean_object* v_vals_3341_, lean_object* v_heq_3342_, lean_object* v_i_3343_, lean_object* v_k_3344_){
_start:
{
uint8_t v_res_3345_; lean_object* v_r_3346_; 
v_res_3345_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(v_00_u03b2_3339_, v_keys_3340_, v_vals_3341_, v_heq_3342_, v_i_3343_, v_k_3344_);
lean_dec(v_k_3344_);
lean_dec_ref(v_vals_3341_);
lean_dec_ref(v_keys_3340_);
v_r_3346_ = lean_box(v_res_3345_);
return v_r_3346_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* v_x_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_, lean_object* v___y_3351_){
_start:
{
lean_object* v___x_3353_; 
v___x_3353_ = l_Lean_Meta_saveState___redArg(v___y_3349_, v___y_3351_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; lean_object* v___x_3355_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref(v___x_3353_);
lean_inc(v___y_3351_);
lean_inc_ref(v___y_3350_);
lean_inc(v___y_3349_);
lean_inc_ref(v___y_3348_);
v___x_3355_ = lean_apply_5(v_x_3347_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_, lean_box(0));
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v___x_3358_; uint8_t v_isShared_3359_; uint8_t v_isSharedCheck_3364_; 
lean_dec(v_a_3354_);
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3358_ = v___x_3355_;
v_isShared_3359_ = v_isSharedCheck_3364_;
goto v_resetjp_3357_;
}
else
{
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3358_ = lean_box(0);
v_isShared_3359_ = v_isSharedCheck_3364_;
goto v_resetjp_3357_;
}
v_resetjp_3357_:
{
lean_object* v___x_3360_; lean_object* v___x_3362_; 
v___x_3360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3360_, 0, v_a_3356_);
if (v_isShared_3359_ == 0)
{
lean_ctor_set(v___x_3358_, 0, v___x_3360_);
v___x_3362_ = v___x_3358_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v___x_3360_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
else
{
lean_object* v_a_3365_; lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3394_; 
v_a_3365_ = lean_ctor_get(v___x_3355_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3367_ = v___x_3355_;
v_isShared_3368_ = v_isSharedCheck_3394_;
goto v_resetjp_3366_;
}
else
{
lean_inc(v_a_3365_);
lean_dec(v___x_3355_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3394_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
uint8_t v___y_3370_; uint8_t v___x_3392_; 
v___x_3392_ = l_Lean_Exception_isInterrupt(v_a_3365_);
if (v___x_3392_ == 0)
{
uint8_t v___x_3393_; 
lean_inc(v_a_3365_);
v___x_3393_ = l_Lean_Exception_isRuntime(v_a_3365_);
v___y_3370_ = v___x_3393_;
goto v___jp_3369_;
}
else
{
v___y_3370_ = v___x_3392_;
goto v___jp_3369_;
}
v___jp_3369_:
{
if (v___y_3370_ == 0)
{
lean_object* v___x_3371_; 
lean_del_object(v___x_3367_);
lean_dec(v_a_3365_);
v___x_3371_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3354_, v___y_3349_, v___y_3351_);
lean_dec(v_a_3354_);
if (lean_obj_tag(v___x_3371_) == 0)
{
lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3379_; 
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3379_ == 0)
{
lean_object* v_unused_3380_; 
v_unused_3380_ = lean_ctor_get(v___x_3371_, 0);
lean_dec(v_unused_3380_);
v___x_3373_ = v___x_3371_;
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
else
{
lean_dec(v___x_3371_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3379_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = lean_box(0);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3375_);
v___x_3377_ = v___x_3373_;
goto v_reusejp_3376_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3375_);
v___x_3377_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3376_;
}
v_reusejp_3376_:
{
return v___x_3377_;
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3388_; 
v_a_3381_ = lean_ctor_get(v___x_3371_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3371_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3383_ = v___x_3371_;
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3371_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3388_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3386_; 
if (v_isShared_3384_ == 0)
{
v___x_3386_ = v___x_3383_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3387_; 
v_reuseFailAlloc_3387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3387_, 0, v_a_3381_);
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
else
{
lean_object* v___x_3390_; 
lean_dec(v_a_3354_);
if (v_isShared_3368_ == 0)
{
v___x_3390_ = v___x_3367_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v_a_3365_);
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
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_dec_ref(v_x_3347_);
v_a_3395_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3353_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3353_);
v___x_3397_ = lean_box(0);
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
v_resetjp_3396_:
{
lean_object* v___x_3400_; 
if (v_isShared_3398_ == 0)
{
v___x_3400_ = v___x_3397_;
goto v_reusejp_3399_;
}
else
{
lean_object* v_reuseFailAlloc_3401_; 
v_reuseFailAlloc_3401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3401_, 0, v_a_3395_);
v___x_3400_ = v_reuseFailAlloc_3401_;
goto v_reusejp_3399_;
}
v_reusejp_3399_:
{
return v___x_3400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object* v_x_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
lean_dec(v___y_3407_);
lean_dec_ref(v___y_3406_);
lean_dec(v___y_3405_);
lean_dec_ref(v___y_3404_);
return v_res_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object* v_00_u03b1_3410_, lean_object* v_x_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v___x_3417_; 
v___x_3417_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object* v_00_u03b1_3418_, lean_object* v_x_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_){
_start:
{
lean_object* v_res_3425_; 
v_res_3425_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(v_00_u03b1_3418_, v_x_3419_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
lean_dec(v___y_3421_);
lean_dec_ref(v___y_3420_);
return v_res_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* v_mvarId_3426_, lean_object* v_hFVarId_3427_, lean_object* v_a_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_){
_start:
{
lean_object* v___x_3433_; lean_object* v___x_3434_; 
v___x_3433_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___boxed), 7, 2);
lean_closure_set(v___x_3433_, 0, v_mvarId_3426_);
lean_closure_set(v___x_3433_, 1, v_hFVarId_3427_);
v___x_3434_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3433_, v_a_3428_, v_a_3429_, v_a_3430_, v_a_3431_);
return v___x_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object* v_mvarId_3435_, lean_object* v_hFVarId_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_){
_start:
{
lean_object* v_res_3442_; 
v_res_3442_ = l_Lean_Meta_substVar_x3f(v_mvarId_3435_, v_hFVarId_3436_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
lean_dec(v_a_3440_);
lean_dec_ref(v_a_3439_);
lean_dec(v_a_3438_);
lean_dec_ref(v_a_3437_);
return v_res_3442_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* v_mvarId_3443_, lean_object* v_hFVarId_3444_, lean_object* v_a_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; 
v___x_3450_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 7, 2);
lean_closure_set(v___x_3450_, 0, v_mvarId_3443_);
lean_closure_set(v___x_3450_, 1, v_hFVarId_3444_);
v___x_3451_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3450_, v_a_3445_, v_a_3446_, v_a_3447_, v_a_3448_);
return v___x_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object* v_mvarId_3452_, lean_object* v_hFVarId_3453_, lean_object* v_a_3454_, lean_object* v_a_3455_, lean_object* v_a_3456_, lean_object* v_a_3457_, lean_object* v_a_3458_){
_start:
{
lean_object* v_res_3459_; 
v_res_3459_ = l_Lean_Meta_subst_x3f(v_mvarId_3452_, v_hFVarId_3453_, v_a_3454_, v_a_3455_, v_a_3456_, v_a_3457_);
lean_dec(v_a_3457_);
lean_dec_ref(v_a_3456_);
lean_dec(v_a_3455_);
lean_dec_ref(v_a_3454_);
return v_res_3459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* v_mvarId_3460_, lean_object* v_hFVarId_3461_, uint8_t v_symm_3462_, lean_object* v_fvarSubst_3463_, uint8_t v_clearH_3464_, uint8_t v_tryToSkip_3465_, lean_object* v_a_3466_, lean_object* v_a_3467_, lean_object* v_a_3468_, lean_object* v_a_3469_){
_start:
{
lean_object* v___x_3471_; lean_object* v___x_3472_; lean_object* v___x_3473_; lean_object* v___x_3474_; lean_object* v___x_3475_; 
v___x_3471_ = lean_box(v_symm_3462_);
v___x_3472_ = lean_box(v_clearH_3464_);
v___x_3473_ = lean_box(v_tryToSkip_3465_);
v___x_3474_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_3474_, 0, v_mvarId_3460_);
lean_closure_set(v___x_3474_, 1, v_hFVarId_3461_);
lean_closure_set(v___x_3474_, 2, v___x_3471_);
lean_closure_set(v___x_3474_, 3, v_fvarSubst_3463_);
lean_closure_set(v___x_3474_, 4, v___x_3472_);
lean_closure_set(v___x_3474_, 5, v___x_3473_);
v___x_3475_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3474_, v_a_3466_, v_a_3467_, v_a_3468_, v_a_3469_);
return v___x_3475_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* v_mvarId_3476_, lean_object* v_hFVarId_3477_, lean_object* v_symm_3478_, lean_object* v_fvarSubst_3479_, lean_object* v_clearH_3480_, lean_object* v_tryToSkip_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_, lean_object* v_a_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_){
_start:
{
uint8_t v_symm_boxed_3487_; uint8_t v_clearH_boxed_3488_; uint8_t v_tryToSkip_boxed_3489_; lean_object* v_res_3490_; 
v_symm_boxed_3487_ = lean_unbox(v_symm_3478_);
v_clearH_boxed_3488_ = lean_unbox(v_clearH_3480_);
v_tryToSkip_boxed_3489_ = lean_unbox(v_tryToSkip_3481_);
v_res_3490_ = l_Lean_Meta_substCore_x3f(v_mvarId_3476_, v_hFVarId_3477_, v_symm_boxed_3487_, v_fvarSubst_3479_, v_clearH_boxed_3488_, v_tryToSkip_boxed_3489_, v_a_3482_, v_a_3483_, v_a_3484_, v_a_3485_);
lean_dec(v_a_3485_);
lean_dec_ref(v_a_3484_);
lean_dec(v_a_3483_);
lean_dec_ref(v_a_3482_);
return v_res_3490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* v_mvarId_3491_, lean_object* v_hFVarId_3492_, lean_object* v_a_3493_, lean_object* v_a_3494_, lean_object* v_a_3495_, lean_object* v_a_3496_){
_start:
{
lean_object* v___x_3498_; 
lean_inc(v_mvarId_3491_);
v___x_3498_ = l_Lean_Meta_substVar_x3f(v_mvarId_3491_, v_hFVarId_3492_, v_a_3493_, v_a_3494_, v_a_3495_, v_a_3496_);
if (lean_obj_tag(v___x_3498_) == 0)
{
lean_object* v_a_3499_; lean_object* v___x_3501_; uint8_t v_isShared_3502_; uint8_t v_isSharedCheck_3510_; 
v_a_3499_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3501_ = v___x_3498_;
v_isShared_3502_ = v_isSharedCheck_3510_;
goto v_resetjp_3500_;
}
else
{
lean_inc(v_a_3499_);
lean_dec(v___x_3498_);
v___x_3501_ = lean_box(0);
v_isShared_3502_ = v_isSharedCheck_3510_;
goto v_resetjp_3500_;
}
v_resetjp_3500_:
{
if (lean_obj_tag(v_a_3499_) == 0)
{
lean_object* v___x_3504_; 
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 0, v_mvarId_3491_);
v___x_3504_ = v___x_3501_;
goto v_reusejp_3503_;
}
else
{
lean_object* v_reuseFailAlloc_3505_; 
v_reuseFailAlloc_3505_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3505_, 0, v_mvarId_3491_);
v___x_3504_ = v_reuseFailAlloc_3505_;
goto v_reusejp_3503_;
}
v_reusejp_3503_:
{
return v___x_3504_;
}
}
else
{
lean_object* v_val_3506_; lean_object* v___x_3508_; 
lean_dec(v_mvarId_3491_);
v_val_3506_ = lean_ctor_get(v_a_3499_, 0);
lean_inc(v_val_3506_);
lean_dec_ref(v_a_3499_);
if (v_isShared_3502_ == 0)
{
lean_ctor_set(v___x_3501_, 0, v_val_3506_);
v___x_3508_ = v___x_3501_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_val_3506_);
v___x_3508_ = v_reuseFailAlloc_3509_;
goto v_reusejp_3507_;
}
v_reusejp_3507_:
{
return v___x_3508_;
}
}
}
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_dec(v_mvarId_3491_);
v_a_3511_ = lean_ctor_get(v___x_3498_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3498_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3498_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3498_);
v___x_3513_ = lean_box(0);
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
v_resetjp_3512_:
{
lean_object* v___x_3516_; 
if (v_isShared_3514_ == 0)
{
v___x_3516_ = v___x_3513_;
goto v_reusejp_3515_;
}
else
{
lean_object* v_reuseFailAlloc_3517_; 
v_reuseFailAlloc_3517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3517_, 0, v_a_3511_);
v___x_3516_ = v_reuseFailAlloc_3517_;
goto v_reusejp_3515_;
}
v_reusejp_3515_:
{
return v___x_3516_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object* v_mvarId_3519_, lean_object* v_hFVarId_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_){
_start:
{
lean_object* v_res_3526_; 
v_res_3526_ = l_Lean_Meta_trySubstVar(v_mvarId_3519_, v_hFVarId_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
lean_dec(v_a_3524_);
lean_dec_ref(v_a_3523_);
lean_dec(v_a_3522_);
lean_dec_ref(v_a_3521_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* v_mvarId_3527_, lean_object* v_hFVarId_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_, lean_object* v_a_3532_){
_start:
{
lean_object* v___x_3534_; 
lean_inc(v_mvarId_3527_);
v___x_3534_ = l_Lean_Meta_subst_x3f(v_mvarId_3527_, v_hFVarId_3528_, v_a_3529_, v_a_3530_, v_a_3531_, v_a_3532_);
if (lean_obj_tag(v___x_3534_) == 0)
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3546_; 
v_a_3535_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3537_ = v___x_3534_;
v_isShared_3538_ = v_isSharedCheck_3546_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3534_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3546_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
if (lean_obj_tag(v_a_3535_) == 0)
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v_mvarId_3527_);
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_mvarId_3527_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
else
{
lean_object* v_val_3542_; lean_object* v___x_3544_; 
lean_dec(v_mvarId_3527_);
v_val_3542_ = lean_ctor_get(v_a_3535_, 0);
lean_inc(v_val_3542_);
lean_dec_ref(v_a_3535_);
if (v_isShared_3538_ == 0)
{
lean_ctor_set(v___x_3537_, 0, v_val_3542_);
v___x_3544_ = v___x_3537_;
goto v_reusejp_3543_;
}
else
{
lean_object* v_reuseFailAlloc_3545_; 
v_reuseFailAlloc_3545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3545_, 0, v_val_3542_);
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
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec(v_mvarId_3527_);
v_a_3547_ = lean_ctor_get(v___x_3534_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3534_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3534_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3534_);
v___x_3549_ = lean_box(0);
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
v_resetjp_3548_:
{
lean_object* v___x_3552_; 
if (v_isShared_3550_ == 0)
{
v___x_3552_ = v___x_3549_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3553_; 
v_reuseFailAlloc_3553_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3553_, 0, v_a_3547_);
v___x_3552_ = v_reuseFailAlloc_3553_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
return v___x_3552_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object* v_mvarId_3555_, lean_object* v_hFVarId_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_, lean_object* v_a_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_Meta_trySubst(v_mvarId_3555_, v_hFVarId_3556_, v_a_3557_, v_a_3558_, v_a_3559_, v_a_3560_);
lean_dec(v_a_3560_);
lean_dec_ref(v_a_3559_);
lean_dec(v_a_3558_);
lean_dec_ref(v_a_3557_);
return v_res_3562_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_mvarId_3566_, lean_object* v_as_3567_, size_t v_sz_3568_, size_t v_i_3569_, lean_object* v_b_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
uint8_t v___x_3576_; 
v___x_3576_ = lean_usize_dec_lt(v_i_3569_, v_sz_3568_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; 
lean_dec(v_mvarId_3566_);
v___x_3577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3577_, 0, v_b_3570_);
return v___x_3577_;
}
else
{
lean_object* v_snd_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3631_; 
v_snd_3578_ = lean_ctor_get(v_b_3570_, 1);
v_isSharedCheck_3631_ = !lean_is_exclusive(v_b_3570_);
if (v_isSharedCheck_3631_ == 0)
{
lean_object* v_unused_3632_; 
v_unused_3632_ = lean_ctor_get(v_b_3570_, 0);
lean_dec(v_unused_3632_);
v___x_3580_ = v_b_3570_;
v_isShared_3581_ = v_isSharedCheck_3631_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_snd_3578_);
lean_dec(v_b_3570_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3631_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3582_; lean_object* v_a_3584_; lean_object* v_a_3591_; 
v___x_3582_ = lean_box(0);
v_a_3591_ = lean_array_uget(v_as_3567_, v_i_3569_);
if (lean_obj_tag(v_a_3591_) == 0)
{
v_a_3584_ = v_snd_3578_;
goto v___jp_3583_;
}
else
{
lean_object* v_val_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3630_; 
v_val_3592_ = lean_ctor_get(v_a_3591_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v_a_3591_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3594_ = v_a_3591_;
v_isShared_3595_ = v_isSharedCheck_3630_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_val_3592_);
lean_dec(v_a_3591_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3630_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = l_Lean_LocalDecl_fvarId(v_val_3592_);
lean_dec(v_val_3592_);
lean_inc(v_mvarId_3566_);
v___x_3597_ = l_Lean_Meta_subst_x3f(v_mvarId_3566_, v___x_3596_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
if (lean_obj_tag(v___x_3597_) == 0)
{
lean_object* v_a_3598_; lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3621_; 
v_a_3598_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3600_ = v___x_3597_;
v_isShared_3601_ = v_isSharedCheck_3621_;
goto v_resetjp_3599_;
}
else
{
lean_inc(v_a_3598_);
lean_dec(v___x_3597_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3621_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; 
v___x_3602_ = lean_box(0);
if (lean_obj_tag(v_a_3598_) == 1)
{
lean_object* v___x_3604_; 
lean_del_object(v___x_3580_);
lean_dec(v_mvarId_3566_);
lean_inc_ref(v_a_3598_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 0, v_a_3598_);
v___x_3604_ = v___x_3594_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3619_; 
v_reuseFailAlloc_3619_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3619_, 0, v_a_3598_);
v___x_3604_ = v_reuseFailAlloc_3619_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3606_; uint8_t v_isShared_3607_; uint8_t v_isSharedCheck_3617_; 
v_isSharedCheck_3617_ = !lean_is_exclusive(v_a_3598_);
if (v_isSharedCheck_3617_ == 0)
{
lean_object* v_unused_3618_; 
v_unused_3618_ = lean_ctor_get(v_a_3598_, 0);
lean_dec(v_unused_3618_);
v___x_3606_ = v_a_3598_;
v_isShared_3607_ = v_isSharedCheck_3617_;
goto v_resetjp_3605_;
}
else
{
lean_dec(v_a_3598_);
v___x_3606_ = lean_box(0);
v_isShared_3607_ = v_isSharedCheck_3617_;
goto v_resetjp_3605_;
}
v_resetjp_3605_:
{
lean_object* v___x_3608_; lean_object* v___x_3610_; 
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3604_);
lean_ctor_set(v___x_3608_, 1, v___x_3602_);
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
lean_ctor_set(v___x_3612_, 1, v_snd_3578_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set(v___x_3600_, 0, v___x_3612_);
v___x_3614_ = v___x_3600_;
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
lean_object* v___x_3620_; 
lean_del_object(v___x_3600_);
lean_dec(v_a_3598_);
lean_del_object(v___x_3594_);
lean_dec(v_snd_3578_);
v___x_3620_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3584_ = v___x_3620_;
goto v___jp_3583_;
}
}
}
else
{
lean_object* v_a_3622_; lean_object* v___x_3624_; uint8_t v_isShared_3625_; uint8_t v_isSharedCheck_3629_; 
lean_del_object(v___x_3594_);
lean_del_object(v___x_3580_);
lean_dec(v_snd_3578_);
lean_dec(v_mvarId_3566_);
v_a_3622_ = lean_ctor_get(v___x_3597_, 0);
v_isSharedCheck_3629_ = !lean_is_exclusive(v___x_3597_);
if (v_isSharedCheck_3629_ == 0)
{
v___x_3624_ = v___x_3597_;
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
else
{
lean_inc(v_a_3622_);
lean_dec(v___x_3597_);
v___x_3624_ = lean_box(0);
v_isShared_3625_ = v_isSharedCheck_3629_;
goto v_resetjp_3623_;
}
v_resetjp_3623_:
{
lean_object* v___x_3627_; 
if (v_isShared_3625_ == 0)
{
v___x_3627_ = v___x_3624_;
goto v_reusejp_3626_;
}
else
{
lean_object* v_reuseFailAlloc_3628_; 
v_reuseFailAlloc_3628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3628_, 0, v_a_3622_);
v___x_3627_ = v_reuseFailAlloc_3628_;
goto v_reusejp_3626_;
}
v_reusejp_3626_:
{
return v___x_3627_;
}
}
}
}
}
v___jp_3583_:
{
lean_object* v___x_3586_; 
if (v_isShared_3581_ == 0)
{
lean_ctor_set(v___x_3580_, 1, v_a_3584_);
lean_ctor_set(v___x_3580_, 0, v___x_3582_);
v___x_3586_ = v___x_3580_;
goto v_reusejp_3585_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v___x_3582_);
lean_ctor_set(v_reuseFailAlloc_3590_, 1, v_a_3584_);
v___x_3586_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3585_;
}
v_reusejp_3585_:
{
size_t v___x_3587_; size_t v___x_3588_; 
v___x_3587_ = ((size_t)1ULL);
v___x_3588_ = lean_usize_add(v_i_3569_, v___x_3587_);
v_i_3569_ = v___x_3588_;
v_b_3570_ = v___x_3586_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_mvarId_3633_, lean_object* v_as_3634_, lean_object* v_sz_3635_, lean_object* v_i_3636_, lean_object* v_b_3637_, lean_object* v___y_3638_, lean_object* v___y_3639_, lean_object* v___y_3640_, lean_object* v___y_3641_, lean_object* v___y_3642_){
_start:
{
size_t v_sz_boxed_3643_; size_t v_i_boxed_3644_; lean_object* v_res_3645_; 
v_sz_boxed_3643_ = lean_unbox_usize(v_sz_3635_);
lean_dec(v_sz_3635_);
v_i_boxed_3644_ = lean_unbox_usize(v_i_3636_);
lean_dec(v_i_3636_);
v_res_3645_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3633_, v_as_3634_, v_sz_boxed_3643_, v_i_boxed_3644_, v_b_3637_, v___y_3638_, v___y_3639_, v___y_3640_, v___y_3641_);
lean_dec(v___y_3641_);
lean_dec_ref(v___y_3640_);
lean_dec(v___y_3639_);
lean_dec_ref(v___y_3638_);
lean_dec_ref(v_as_3634_);
return v_res_3645_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object* v_mvarId_3646_, lean_object* v_as_3647_, size_t v_sz_3648_, size_t v_i_3649_, lean_object* v_b_3650_, lean_object* v___y_3651_, lean_object* v___y_3652_, lean_object* v___y_3653_, lean_object* v___y_3654_){
_start:
{
uint8_t v___x_3656_; 
v___x_3656_ = lean_usize_dec_lt(v_i_3649_, v_sz_3648_);
if (v___x_3656_ == 0)
{
lean_object* v___x_3657_; 
lean_dec(v_mvarId_3646_);
v___x_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3657_, 0, v_b_3650_);
return v___x_3657_;
}
else
{
lean_object* v_snd_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3711_; 
v_snd_3658_ = lean_ctor_get(v_b_3650_, 1);
v_isSharedCheck_3711_ = !lean_is_exclusive(v_b_3650_);
if (v_isSharedCheck_3711_ == 0)
{
lean_object* v_unused_3712_; 
v_unused_3712_ = lean_ctor_get(v_b_3650_, 0);
lean_dec(v_unused_3712_);
v___x_3660_ = v_b_3650_;
v_isShared_3661_ = v_isSharedCheck_3711_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_snd_3658_);
lean_dec(v_b_3650_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3711_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v_a_3664_; lean_object* v_a_3671_; 
v___x_3662_ = lean_box(0);
v_a_3671_ = lean_array_uget(v_as_3647_, v_i_3649_);
if (lean_obj_tag(v_a_3671_) == 0)
{
v_a_3664_ = v_snd_3658_;
goto v___jp_3663_;
}
else
{
lean_object* v_val_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3710_; 
v_val_3672_ = lean_ctor_get(v_a_3671_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v_a_3671_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3674_ = v_a_3671_;
v_isShared_3675_ = v_isSharedCheck_3710_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_val_3672_);
lean_dec(v_a_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3710_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = l_Lean_LocalDecl_fvarId(v_val_3672_);
lean_dec(v_val_3672_);
lean_inc(v_mvarId_3646_);
v___x_3677_ = l_Lean_Meta_subst_x3f(v_mvarId_3646_, v___x_3676_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3701_; 
v_a_3678_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3680_ = v___x_3677_;
v_isShared_3681_ = v_isSharedCheck_3701_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3677_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3701_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; 
v___x_3682_ = lean_box(0);
if (lean_obj_tag(v_a_3678_) == 1)
{
lean_object* v___x_3684_; 
lean_del_object(v___x_3660_);
lean_dec(v_mvarId_3646_);
lean_inc_ref(v_a_3678_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v_a_3678_);
v___x_3684_ = v___x_3674_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3699_; 
v_reuseFailAlloc_3699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3678_);
v___x_3684_ = v_reuseFailAlloc_3699_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3686_; uint8_t v_isShared_3687_; uint8_t v_isSharedCheck_3697_; 
v_isSharedCheck_3697_ = !lean_is_exclusive(v_a_3678_);
if (v_isSharedCheck_3697_ == 0)
{
lean_object* v_unused_3698_; 
v_unused_3698_ = lean_ctor_get(v_a_3678_, 0);
lean_dec(v_unused_3698_);
v___x_3686_ = v_a_3678_;
v_isShared_3687_ = v_isSharedCheck_3697_;
goto v_resetjp_3685_;
}
else
{
lean_dec(v_a_3678_);
v___x_3686_ = lean_box(0);
v_isShared_3687_ = v_isSharedCheck_3697_;
goto v_resetjp_3685_;
}
v_resetjp_3685_:
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3688_, 0, v___x_3684_);
lean_ctor_set(v___x_3688_, 1, v___x_3682_);
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
lean_ctor_set(v___x_3692_, 1, v_snd_3658_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set(v___x_3680_, 0, v___x_3692_);
v___x_3694_ = v___x_3680_;
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
lean_object* v___x_3700_; 
lean_del_object(v___x_3680_);
lean_dec(v_a_3678_);
lean_del_object(v___x_3674_);
lean_dec(v_snd_3658_);
v___x_3700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3664_ = v___x_3700_;
goto v___jp_3663_;
}
}
}
else
{
lean_object* v_a_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_3709_; 
lean_del_object(v___x_3674_);
lean_del_object(v___x_3660_);
lean_dec(v_snd_3658_);
lean_dec(v_mvarId_3646_);
v_a_3702_ = lean_ctor_get(v___x_3677_, 0);
v_isSharedCheck_3709_ = !lean_is_exclusive(v___x_3677_);
if (v_isSharedCheck_3709_ == 0)
{
v___x_3704_ = v___x_3677_;
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_a_3702_);
lean_dec(v___x_3677_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_3709_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3707_; 
if (v_isShared_3705_ == 0)
{
v___x_3707_ = v___x_3704_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3708_; 
v_reuseFailAlloc_3708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3708_, 0, v_a_3702_);
v___x_3707_ = v_reuseFailAlloc_3708_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
return v___x_3707_;
}
}
}
}
}
v___jp_3663_:
{
lean_object* v___x_3666_; 
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 1, v_a_3664_);
lean_ctor_set(v___x_3660_, 0, v___x_3662_);
v___x_3666_ = v___x_3660_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3662_);
lean_ctor_set(v_reuseFailAlloc_3670_, 1, v_a_3664_);
v___x_3666_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
size_t v___x_3667_; size_t v___x_3668_; lean_object* v___x_3669_; 
v___x_3667_ = ((size_t)1ULL);
v___x_3668_ = lean_usize_add(v_i_3649_, v___x_3667_);
v___x_3669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3646_, v_as_3647_, v_sz_3648_, v___x_3668_, v___x_3666_, v___y_3651_, v___y_3652_, v___y_3653_, v___y_3654_);
return v___x_3669_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_3713_, lean_object* v_as_3714_, lean_object* v_sz_3715_, lean_object* v_i_3716_, lean_object* v_b_3717_, lean_object* v___y_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_){
_start:
{
size_t v_sz_boxed_3723_; size_t v_i_boxed_3724_; lean_object* v_res_3725_; 
v_sz_boxed_3723_ = lean_unbox_usize(v_sz_3715_);
lean_dec(v_sz_3715_);
v_i_boxed_3724_ = lean_unbox_usize(v_i_3716_);
lean_dec(v_i_3716_);
v_res_3725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3713_, v_as_3714_, v_sz_boxed_3723_, v_i_boxed_3724_, v_b_3717_, v___y_3718_, v___y_3719_, v___y_3720_, v___y_3721_);
lean_dec(v___y_3721_);
lean_dec_ref(v___y_3720_);
lean_dec(v___y_3719_);
lean_dec_ref(v___y_3718_);
lean_dec_ref(v_as_3714_);
return v_res_3725_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* v_init_3726_, lean_object* v_mvarId_3727_, lean_object* v_n_3728_, lean_object* v_b_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_, lean_object* v___y_3733_){
_start:
{
if (lean_obj_tag(v_n_3728_) == 0)
{
lean_object* v_cs_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; size_t v_sz_3738_; size_t v___x_3739_; lean_object* v___x_3740_; 
v_cs_3735_ = lean_ctor_get(v_n_3728_, 0);
v___x_3736_ = lean_box(0);
v___x_3737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3737_, 0, v___x_3736_);
lean_ctor_set(v___x_3737_, 1, v_b_3729_);
v_sz_3738_ = lean_array_size(v_cs_3735_);
v___x_3739_ = ((size_t)0ULL);
v___x_3740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3726_, v_mvarId_3727_, v_cs_3735_, v_sz_3738_, v___x_3739_, v___x_3737_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
if (lean_obj_tag(v___x_3740_) == 0)
{
lean_object* v_a_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3755_; 
v_a_3741_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3743_ = v___x_3740_;
v_isShared_3744_ = v_isSharedCheck_3755_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_a_3741_);
lean_dec(v___x_3740_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3755_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v_fst_3745_; 
v_fst_3745_ = lean_ctor_get(v_a_3741_, 0);
if (lean_obj_tag(v_fst_3745_) == 0)
{
lean_object* v_snd_3746_; lean_object* v___x_3747_; lean_object* v___x_3749_; 
v_snd_3746_ = lean_ctor_get(v_a_3741_, 1);
lean_inc(v_snd_3746_);
lean_dec(v_a_3741_);
v___x_3747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3747_, 0, v_snd_3746_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v___x_3747_);
v___x_3749_ = v___x_3743_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3750_; 
v_reuseFailAlloc_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3750_, 0, v___x_3747_);
v___x_3749_ = v_reuseFailAlloc_3750_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
return v___x_3749_;
}
}
else
{
lean_object* v_val_3751_; lean_object* v___x_3753_; 
lean_inc_ref(v_fst_3745_);
lean_dec(v_a_3741_);
v_val_3751_ = lean_ctor_get(v_fst_3745_, 0);
lean_inc(v_val_3751_);
lean_dec_ref(v_fst_3745_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set(v___x_3743_, 0, v_val_3751_);
v___x_3753_ = v___x_3743_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_val_3751_);
v___x_3753_ = v_reuseFailAlloc_3754_;
goto v_reusejp_3752_;
}
v_reusejp_3752_:
{
return v___x_3753_;
}
}
}
}
else
{
lean_object* v_a_3756_; lean_object* v___x_3758_; uint8_t v_isShared_3759_; uint8_t v_isSharedCheck_3763_; 
v_a_3756_ = lean_ctor_get(v___x_3740_, 0);
v_isSharedCheck_3763_ = !lean_is_exclusive(v___x_3740_);
if (v_isSharedCheck_3763_ == 0)
{
v___x_3758_ = v___x_3740_;
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
else
{
lean_inc(v_a_3756_);
lean_dec(v___x_3740_);
v___x_3758_ = lean_box(0);
v_isShared_3759_ = v_isSharedCheck_3763_;
goto v_resetjp_3757_;
}
v_resetjp_3757_:
{
lean_object* v___x_3761_; 
if (v_isShared_3759_ == 0)
{
v___x_3761_ = v___x_3758_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3762_; 
v_reuseFailAlloc_3762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3762_, 0, v_a_3756_);
v___x_3761_ = v_reuseFailAlloc_3762_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
return v___x_3761_;
}
}
}
}
else
{
lean_object* v_vs_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; size_t v_sz_3767_; size_t v___x_3768_; lean_object* v___x_3769_; 
v_vs_3764_ = lean_ctor_get(v_n_3728_, 0);
v___x_3765_ = lean_box(0);
v___x_3766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3765_);
lean_ctor_set(v___x_3766_, 1, v_b_3729_);
v_sz_3767_ = lean_array_size(v_vs_3764_);
v___x_3768_ = ((size_t)0ULL);
v___x_3769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3727_, v_vs_3764_, v_sz_3767_, v___x_3768_, v___x_3766_, v___y_3730_, v___y_3731_, v___y_3732_, v___y_3733_);
if (lean_obj_tag(v___x_3769_) == 0)
{
lean_object* v_a_3770_; lean_object* v___x_3772_; uint8_t v_isShared_3773_; uint8_t v_isSharedCheck_3784_; 
v_a_3770_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3772_ = v___x_3769_;
v_isShared_3773_ = v_isSharedCheck_3784_;
goto v_resetjp_3771_;
}
else
{
lean_inc(v_a_3770_);
lean_dec(v___x_3769_);
v___x_3772_ = lean_box(0);
v_isShared_3773_ = v_isSharedCheck_3784_;
goto v_resetjp_3771_;
}
v_resetjp_3771_:
{
lean_object* v_fst_3774_; 
v_fst_3774_ = lean_ctor_get(v_a_3770_, 0);
if (lean_obj_tag(v_fst_3774_) == 0)
{
lean_object* v_snd_3775_; lean_object* v___x_3776_; lean_object* v___x_3778_; 
v_snd_3775_ = lean_ctor_get(v_a_3770_, 1);
lean_inc(v_snd_3775_);
lean_dec(v_a_3770_);
v___x_3776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3776_, 0, v_snd_3775_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v___x_3776_);
v___x_3778_ = v___x_3772_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v___x_3776_);
v___x_3778_ = v_reuseFailAlloc_3779_;
goto v_reusejp_3777_;
}
v_reusejp_3777_:
{
return v___x_3778_;
}
}
else
{
lean_object* v_val_3780_; lean_object* v___x_3782_; 
lean_inc_ref(v_fst_3774_);
lean_dec(v_a_3770_);
v_val_3780_ = lean_ctor_get(v_fst_3774_, 0);
lean_inc(v_val_3780_);
lean_dec_ref(v_fst_3774_);
if (v_isShared_3773_ == 0)
{
lean_ctor_set(v___x_3772_, 0, v_val_3780_);
v___x_3782_ = v___x_3772_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_val_3780_);
v___x_3782_ = v_reuseFailAlloc_3783_;
goto v_reusejp_3781_;
}
v_reusejp_3781_:
{
return v___x_3782_;
}
}
}
}
else
{
lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3792_; 
v_a_3785_ = lean_ctor_get(v___x_3769_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3769_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3787_ = v___x_3769_;
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_dec(v___x_3769_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3792_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3790_; 
if (v_isShared_3788_ == 0)
{
v___x_3790_ = v___x_3787_;
goto v_reusejp_3789_;
}
else
{
lean_object* v_reuseFailAlloc_3791_; 
v_reuseFailAlloc_3791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3791_, 0, v_a_3785_);
v___x_3790_ = v_reuseFailAlloc_3791_;
goto v_reusejp_3789_;
}
v_reusejp_3789_:
{
return v___x_3790_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_init_3793_, lean_object* v_mvarId_3794_, lean_object* v_as_3795_, size_t v_sz_3796_, size_t v_i_3797_, lean_object* v_b_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
uint8_t v___x_3804_; 
v___x_3804_ = lean_usize_dec_lt(v_i_3797_, v_sz_3796_);
if (v___x_3804_ == 0)
{
lean_object* v___x_3805_; 
lean_dec(v_mvarId_3794_);
v___x_3805_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3805_, 0, v_b_3798_);
return v___x_3805_;
}
else
{
lean_object* v_snd_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3840_; 
v_snd_3806_ = lean_ctor_get(v_b_3798_, 1);
v_isSharedCheck_3840_ = !lean_is_exclusive(v_b_3798_);
if (v_isSharedCheck_3840_ == 0)
{
lean_object* v_unused_3841_; 
v_unused_3841_ = lean_ctor_get(v_b_3798_, 0);
lean_dec(v_unused_3841_);
v___x_3808_ = v_b_3798_;
v_isShared_3809_ = v_isSharedCheck_3840_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_snd_3806_);
lean_dec(v_b_3798_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3840_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
lean_object* v_a_3810_; lean_object* v___x_3811_; 
v_a_3810_ = lean_array_uget_borrowed(v_as_3795_, v_i_3797_);
lean_inc(v_snd_3806_);
lean_inc(v_mvarId_3794_);
v___x_3811_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3793_, v_mvarId_3794_, v_a_3810_, v_snd_3806_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
if (lean_obj_tag(v___x_3811_) == 0)
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3831_; 
v_a_3812_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3814_ = v___x_3811_;
v_isShared_3815_ = v_isSharedCheck_3831_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3811_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3831_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
if (lean_obj_tag(v_a_3812_) == 0)
{
lean_object* v___x_3816_; lean_object* v___x_3818_; 
lean_dec(v_mvarId_3794_);
v___x_3816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3816_, 0, v_a_3812_);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v___x_3816_);
v___x_3818_ = v___x_3808_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_snd_3806_);
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
lean_object* v_a_3823_; lean_object* v___x_3824_; lean_object* v___x_3826_; 
lean_del_object(v___x_3814_);
lean_dec(v_snd_3806_);
v_a_3823_ = lean_ctor_get(v_a_3812_, 0);
lean_inc(v_a_3823_);
lean_dec_ref(v_a_3812_);
v___x_3824_ = lean_box(0);
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 1, v_a_3823_);
lean_ctor_set(v___x_3808_, 0, v___x_3824_);
v___x_3826_ = v___x_3808_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v___x_3824_);
lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_a_3823_);
v___x_3826_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
size_t v___x_3827_; size_t v___x_3828_; 
v___x_3827_ = ((size_t)1ULL);
v___x_3828_ = lean_usize_add(v_i_3797_, v___x_3827_);
v_i_3797_ = v___x_3828_;
v_b_3798_ = v___x_3826_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3832_; lean_object* v___x_3834_; uint8_t v_isShared_3835_; uint8_t v_isSharedCheck_3839_; 
lean_del_object(v___x_3808_);
lean_dec(v_snd_3806_);
lean_dec(v_mvarId_3794_);
v_a_3832_ = lean_ctor_get(v___x_3811_, 0);
v_isSharedCheck_3839_ = !lean_is_exclusive(v___x_3811_);
if (v_isSharedCheck_3839_ == 0)
{
v___x_3834_ = v___x_3811_;
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
else
{
lean_inc(v_a_3832_);
lean_dec(v___x_3811_);
v___x_3834_ = lean_box(0);
v_isShared_3835_ = v_isSharedCheck_3839_;
goto v_resetjp_3833_;
}
v_resetjp_3833_:
{
lean_object* v___x_3837_; 
if (v_isShared_3835_ == 0)
{
v___x_3837_ = v___x_3834_;
goto v_reusejp_3836_;
}
else
{
lean_object* v_reuseFailAlloc_3838_; 
v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
v___x_3837_ = v_reuseFailAlloc_3838_;
goto v_reusejp_3836_;
}
v_reusejp_3836_:
{
return v___x_3837_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3842_, lean_object* v_mvarId_3843_, lean_object* v_as_3844_, lean_object* v_sz_3845_, lean_object* v_i_3846_, lean_object* v_b_3847_, lean_object* v___y_3848_, lean_object* v___y_3849_, lean_object* v___y_3850_, lean_object* v___y_3851_, lean_object* v___y_3852_){
_start:
{
size_t v_sz_boxed_3853_; size_t v_i_boxed_3854_; lean_object* v_res_3855_; 
v_sz_boxed_3853_ = lean_unbox_usize(v_sz_3845_);
lean_dec(v_sz_3845_);
v_i_boxed_3854_ = lean_unbox_usize(v_i_3846_);
lean_dec(v_i_3846_);
v_res_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3842_, v_mvarId_3843_, v_as_3844_, v_sz_boxed_3853_, v_i_boxed_3854_, v_b_3847_, v___y_3848_, v___y_3849_, v___y_3850_, v___y_3851_);
lean_dec(v___y_3851_);
lean_dec_ref(v___y_3850_);
lean_dec(v___y_3849_);
lean_dec_ref(v___y_3848_);
lean_dec_ref(v_as_3844_);
lean_dec_ref(v_init_3842_);
return v_res_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_init_3856_, lean_object* v_mvarId_3857_, lean_object* v_n_3858_, lean_object* v_b_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3856_, v_mvarId_3857_, v_n_3858_, v_b_3859_, v___y_3860_, v___y_3861_, v___y_3862_, v___y_3863_);
lean_dec(v___y_3863_);
lean_dec_ref(v___y_3862_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec_ref(v_n_3858_);
lean_dec_ref(v_init_3856_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3869_, lean_object* v_as_3870_, size_t v_sz_3871_, size_t v_i_3872_, lean_object* v_b_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_){
_start:
{
uint8_t v___x_3879_; 
v___x_3879_ = lean_usize_dec_lt(v_i_3872_, v_sz_3871_);
if (v___x_3879_ == 0)
{
lean_object* v___x_3880_; 
lean_dec(v_mvarId_3869_);
v___x_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3880_, 0, v_b_3873_);
return v___x_3880_;
}
else
{
lean_object* v_snd_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3933_; 
v_snd_3881_ = lean_ctor_get(v_b_3873_, 1);
v_isSharedCheck_3933_ = !lean_is_exclusive(v_b_3873_);
if (v_isSharedCheck_3933_ == 0)
{
lean_object* v_unused_3934_; 
v_unused_3934_ = lean_ctor_get(v_b_3873_, 0);
lean_dec(v_unused_3934_);
v___x_3883_ = v_b_3873_;
v_isShared_3884_ = v_isSharedCheck_3933_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_snd_3881_);
lean_dec(v_b_3873_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3933_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; lean_object* v_a_3887_; lean_object* v_a_3894_; 
v___x_3885_ = lean_box(0);
v_a_3894_ = lean_array_uget(v_as_3870_, v_i_3872_);
if (lean_obj_tag(v_a_3894_) == 0)
{
v_a_3887_ = v_snd_3881_;
goto v___jp_3886_;
}
else
{
lean_object* v_val_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3932_; 
v_val_3895_ = lean_ctor_get(v_a_3894_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v_a_3894_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3897_ = v_a_3894_;
v_isShared_3898_ = v_isSharedCheck_3932_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_val_3895_);
lean_dec(v_a_3894_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3932_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3899_; lean_object* v___x_3900_; 
v___x_3899_ = l_Lean_LocalDecl_fvarId(v_val_3895_);
lean_dec(v_val_3895_);
lean_inc(v_mvarId_3869_);
v___x_3900_ = l_Lean_Meta_subst_x3f(v_mvarId_3869_, v___x_3899_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
if (lean_obj_tag(v___x_3900_) == 0)
{
lean_object* v_a_3901_; lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3923_; 
v_a_3901_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3903_ = v___x_3900_;
v_isShared_3904_ = v_isSharedCheck_3923_;
goto v_resetjp_3902_;
}
else
{
lean_inc(v_a_3901_);
lean_dec(v___x_3900_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3923_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; 
v___x_3905_ = lean_box(0);
if (lean_obj_tag(v_a_3901_) == 1)
{
lean_object* v___x_3907_; 
lean_del_object(v___x_3883_);
lean_dec(v_mvarId_3869_);
lean_inc_ref(v_a_3901_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v_a_3901_);
v___x_3907_ = v___x_3897_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v_a_3901_);
v___x_3907_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3909_; uint8_t v_isShared_3910_; uint8_t v_isSharedCheck_3919_; 
v_isSharedCheck_3919_ = !lean_is_exclusive(v_a_3901_);
if (v_isSharedCheck_3919_ == 0)
{
lean_object* v_unused_3920_; 
v_unused_3920_ = lean_ctor_get(v_a_3901_, 0);
lean_dec(v_unused_3920_);
v___x_3909_ = v_a_3901_;
v_isShared_3910_ = v_isSharedCheck_3919_;
goto v_resetjp_3908_;
}
else
{
lean_dec(v_a_3901_);
v___x_3909_ = lean_box(0);
v_isShared_3910_ = v_isSharedCheck_3919_;
goto v_resetjp_3908_;
}
v_resetjp_3908_:
{
lean_object* v___x_3911_; lean_object* v___x_3913_; 
v___x_3911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3911_, 0, v___x_3907_);
lean_ctor_set(v___x_3911_, 1, v___x_3905_);
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
lean_ctor_set(v___x_3914_, 1, v_snd_3881_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 0, v___x_3914_);
v___x_3916_ = v___x_3903_;
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
lean_object* v___x_3922_; 
lean_del_object(v___x_3903_);
lean_dec(v_a_3901_);
lean_del_object(v___x_3897_);
lean_dec(v_snd_3881_);
v___x_3922_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3887_ = v___x_3922_;
goto v___jp_3886_;
}
}
}
else
{
lean_object* v_a_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3931_; 
lean_del_object(v___x_3897_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_mvarId_3869_);
v_a_3924_ = lean_ctor_get(v___x_3900_, 0);
v_isSharedCheck_3931_ = !lean_is_exclusive(v___x_3900_);
if (v_isSharedCheck_3931_ == 0)
{
v___x_3926_ = v___x_3900_;
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_a_3924_);
lean_dec(v___x_3900_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3931_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3929_; 
if (v_isShared_3927_ == 0)
{
v___x_3929_ = v___x_3926_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3930_; 
v_reuseFailAlloc_3930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3930_, 0, v_a_3924_);
v___x_3929_ = v_reuseFailAlloc_3930_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
return v___x_3929_;
}
}
}
}
}
v___jp_3886_:
{
lean_object* v___x_3889_; 
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 1, v_a_3887_);
lean_ctor_set(v___x_3883_, 0, v___x_3885_);
v___x_3889_ = v___x_3883_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v___x_3885_);
lean_ctor_set(v_reuseFailAlloc_3893_, 1, v_a_3887_);
v___x_3889_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3888_;
}
v_reusejp_3888_:
{
size_t v___x_3890_; size_t v___x_3891_; 
v___x_3890_ = ((size_t)1ULL);
v___x_3891_ = lean_usize_add(v_i_3872_, v___x_3890_);
v_i_3872_ = v___x_3891_;
v_b_3873_ = v___x_3889_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3935_, lean_object* v_as_3936_, lean_object* v_sz_3937_, lean_object* v_i_3938_, lean_object* v_b_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_, lean_object* v___y_3943_, lean_object* v___y_3944_){
_start:
{
size_t v_sz_boxed_3945_; size_t v_i_boxed_3946_; lean_object* v_res_3947_; 
v_sz_boxed_3945_ = lean_unbox_usize(v_sz_3937_);
lean_dec(v_sz_3937_);
v_i_boxed_3946_ = lean_unbox_usize(v_i_3938_);
lean_dec(v_i_3938_);
v_res_3947_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3935_, v_as_3936_, v_sz_boxed_3945_, v_i_boxed_3946_, v_b_3939_, v___y_3940_, v___y_3941_, v___y_3942_, v___y_3943_);
lean_dec(v___y_3943_);
lean_dec_ref(v___y_3942_);
lean_dec(v___y_3941_);
lean_dec_ref(v___y_3940_);
lean_dec_ref(v_as_3936_);
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_3948_, lean_object* v_as_3949_, size_t v_sz_3950_, size_t v_i_3951_, lean_object* v_b_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_){
_start:
{
uint8_t v___x_3958_; 
v___x_3958_ = lean_usize_dec_lt(v_i_3951_, v_sz_3950_);
if (v___x_3958_ == 0)
{
lean_object* v___x_3959_; 
lean_dec(v_mvarId_3948_);
v___x_3959_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3959_, 0, v_b_3952_);
return v___x_3959_;
}
else
{
lean_object* v_snd_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_4012_; 
v_snd_3960_ = lean_ctor_get(v_b_3952_, 1);
v_isSharedCheck_4012_ = !lean_is_exclusive(v_b_3952_);
if (v_isSharedCheck_4012_ == 0)
{
lean_object* v_unused_4013_; 
v_unused_4013_ = lean_ctor_get(v_b_3952_, 0);
lean_dec(v_unused_4013_);
v___x_3962_ = v_b_3952_;
v_isShared_3963_ = v_isSharedCheck_4012_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_snd_3960_);
lean_dec(v_b_3952_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_4012_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3964_; lean_object* v_a_3966_; lean_object* v_a_3973_; 
v___x_3964_ = lean_box(0);
v_a_3973_ = lean_array_uget(v_as_3949_, v_i_3951_);
if (lean_obj_tag(v_a_3973_) == 0)
{
v_a_3966_ = v_snd_3960_;
goto v___jp_3965_;
}
else
{
lean_object* v_val_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_4011_; 
v_val_3974_ = lean_ctor_get(v_a_3973_, 0);
v_isSharedCheck_4011_ = !lean_is_exclusive(v_a_3973_);
if (v_isSharedCheck_4011_ == 0)
{
v___x_3976_ = v_a_3973_;
v_isShared_3977_ = v_isSharedCheck_4011_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_val_3974_);
lean_dec(v_a_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_4011_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3978_ = l_Lean_LocalDecl_fvarId(v_val_3974_);
lean_dec(v_val_3974_);
lean_inc(v_mvarId_3948_);
v___x_3979_ = l_Lean_Meta_subst_x3f(v_mvarId_3948_, v___x_3978_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
if (lean_obj_tag(v___x_3979_) == 0)
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_4002_; 
v_a_3980_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3982_ = v___x_3979_;
v_isShared_3983_ = v_isSharedCheck_4002_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3979_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_4002_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; 
v___x_3984_ = lean_box(0);
if (lean_obj_tag(v_a_3980_) == 1)
{
lean_object* v___x_3986_; 
lean_del_object(v___x_3962_);
lean_dec(v_mvarId_3948_);
lean_inc_ref(v_a_3980_);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v_a_3980_);
v___x_3986_ = v___x_3976_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_4000_; 
v_reuseFailAlloc_4000_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4000_, 0, v_a_3980_);
v___x_3986_ = v_reuseFailAlloc_4000_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3998_; 
v_isSharedCheck_3998_ = !lean_is_exclusive(v_a_3980_);
if (v_isSharedCheck_3998_ == 0)
{
lean_object* v_unused_3999_; 
v_unused_3999_ = lean_ctor_get(v_a_3980_, 0);
lean_dec(v_unused_3999_);
v___x_3988_ = v_a_3980_;
v_isShared_3989_ = v_isSharedCheck_3998_;
goto v_resetjp_3987_;
}
else
{
lean_dec(v_a_3980_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3998_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3990_; lean_object* v___x_3992_; 
v___x_3990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3990_, 0, v___x_3986_);
lean_ctor_set(v___x_3990_, 1, v___x_3984_);
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
lean_ctor_set(v___x_3993_, 1, v_snd_3960_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_3993_);
v___x_3995_ = v___x_3982_;
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
lean_object* v___x_4001_; 
lean_del_object(v___x_3982_);
lean_dec(v_a_3980_);
lean_del_object(v___x_3976_);
lean_dec(v_snd_3960_);
v___x_4001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3966_ = v___x_4001_;
goto v___jp_3965_;
}
}
}
else
{
lean_object* v_a_4003_; lean_object* v___x_4005_; uint8_t v_isShared_4006_; uint8_t v_isSharedCheck_4010_; 
lean_del_object(v___x_3976_);
lean_del_object(v___x_3962_);
lean_dec(v_snd_3960_);
lean_dec(v_mvarId_3948_);
v_a_4003_ = lean_ctor_get(v___x_3979_, 0);
v_isSharedCheck_4010_ = !lean_is_exclusive(v___x_3979_);
if (v_isSharedCheck_4010_ == 0)
{
v___x_4005_ = v___x_3979_;
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
else
{
lean_inc(v_a_4003_);
lean_dec(v___x_3979_);
v___x_4005_ = lean_box(0);
v_isShared_4006_ = v_isSharedCheck_4010_;
goto v_resetjp_4004_;
}
v_resetjp_4004_:
{
lean_object* v___x_4008_; 
if (v_isShared_4006_ == 0)
{
v___x_4008_ = v___x_4005_;
goto v_reusejp_4007_;
}
else
{
lean_object* v_reuseFailAlloc_4009_; 
v_reuseFailAlloc_4009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4009_, 0, v_a_4003_);
v___x_4008_ = v_reuseFailAlloc_4009_;
goto v_reusejp_4007_;
}
v_reusejp_4007_:
{
return v___x_4008_;
}
}
}
}
}
v___jp_3965_:
{
lean_object* v___x_3968_; 
if (v_isShared_3963_ == 0)
{
lean_ctor_set(v___x_3962_, 1, v_a_3966_);
lean_ctor_set(v___x_3962_, 0, v___x_3964_);
v___x_3968_ = v___x_3962_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3972_; 
v_reuseFailAlloc_3972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3972_, 0, v___x_3964_);
lean_ctor_set(v_reuseFailAlloc_3972_, 1, v_a_3966_);
v___x_3968_ = v_reuseFailAlloc_3972_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
size_t v___x_3969_; size_t v___x_3970_; lean_object* v___x_3971_; 
v___x_3969_ = ((size_t)1ULL);
v___x_3970_ = lean_usize_add(v_i_3951_, v___x_3969_);
v___x_3971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3948_, v_as_3949_, v_sz_3950_, v___x_3970_, v___x_3968_, v___y_3953_, v___y_3954_, v___y_3955_, v___y_3956_);
return v___x_3971_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_4014_, lean_object* v_as_4015_, lean_object* v_sz_4016_, lean_object* v_i_4017_, lean_object* v_b_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_){
_start:
{
size_t v_sz_boxed_4024_; size_t v_i_boxed_4025_; lean_object* v_res_4026_; 
v_sz_boxed_4024_ = lean_unbox_usize(v_sz_4016_);
lean_dec(v_sz_4016_);
v_i_boxed_4025_ = lean_unbox_usize(v_i_4017_);
lean_dec(v_i_4017_);
v_res_4026_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4014_, v_as_4015_, v_sz_boxed_4024_, v_i_boxed_4025_, v_b_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
lean_dec(v___y_4022_);
lean_dec_ref(v___y_4021_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec_ref(v_as_4015_);
return v_res_4026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4027_, lean_object* v_t_4028_, lean_object* v_init_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v_root_4035_; lean_object* v_tail_4036_; lean_object* v___x_4037_; 
v_root_4035_ = lean_ctor_get(v_t_4028_, 0);
v_tail_4036_ = lean_ctor_get(v_t_4028_, 1);
lean_inc(v_mvarId_4027_);
lean_inc_ref(v_init_4029_);
v___x_4037_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_4029_, v_mvarId_4027_, v_root_4035_, v_init_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec_ref(v_init_4029_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4074_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4040_ = v___x_4037_;
v_isShared_4041_ = v_isSharedCheck_4074_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4037_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4074_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
if (lean_obj_tag(v_a_4038_) == 0)
{
lean_object* v_a_4042_; lean_object* v___x_4044_; 
lean_dec(v_mvarId_4027_);
v_a_4042_ = lean_ctor_get(v_a_4038_, 0);
lean_inc(v_a_4042_);
lean_dec_ref(v_a_4038_);
if (v_isShared_4041_ == 0)
{
lean_ctor_set(v___x_4040_, 0, v_a_4042_);
v___x_4044_ = v___x_4040_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4042_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
else
{
lean_object* v_a_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; size_t v_sz_4049_; size_t v___x_4050_; lean_object* v___x_4051_; 
lean_del_object(v___x_4040_);
v_a_4046_ = lean_ctor_get(v_a_4038_, 0);
lean_inc(v_a_4046_);
lean_dec_ref(v_a_4038_);
v___x_4047_ = lean_box(0);
v___x_4048_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
lean_ctor_set(v___x_4048_, 1, v_a_4046_);
v_sz_4049_ = lean_array_size(v_tail_4036_);
v___x_4050_ = ((size_t)0ULL);
v___x_4051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4027_, v_tail_4036_, v_sz_4049_, v___x_4050_, v___x_4048_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
if (lean_obj_tag(v___x_4051_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4065_; 
v_a_4052_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4054_ = v___x_4051_;
v_isShared_4055_ = v_isSharedCheck_4065_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4051_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4065_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v_fst_4056_; 
v_fst_4056_ = lean_ctor_get(v_a_4052_, 0);
if (lean_obj_tag(v_fst_4056_) == 0)
{
lean_object* v_snd_4057_; lean_object* v___x_4059_; 
v_snd_4057_ = lean_ctor_get(v_a_4052_, 1);
lean_inc(v_snd_4057_);
lean_dec(v_a_4052_);
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 0, v_snd_4057_);
v___x_4059_ = v___x_4054_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4060_; 
v_reuseFailAlloc_4060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_snd_4057_);
v___x_4059_ = v_reuseFailAlloc_4060_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
return v___x_4059_;
}
}
else
{
lean_object* v_val_4061_; lean_object* v___x_4063_; 
lean_inc_ref(v_fst_4056_);
lean_dec(v_a_4052_);
v_val_4061_ = lean_ctor_get(v_fst_4056_, 0);
lean_inc(v_val_4061_);
lean_dec_ref(v_fst_4056_);
if (v_isShared_4055_ == 0)
{
lean_ctor_set(v___x_4054_, 0, v_val_4061_);
v___x_4063_ = v___x_4054_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v_val_4061_);
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
else
{
lean_object* v_a_4066_; lean_object* v___x_4068_; uint8_t v_isShared_4069_; uint8_t v_isSharedCheck_4073_; 
v_a_4066_ = lean_ctor_get(v___x_4051_, 0);
v_isSharedCheck_4073_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4073_ == 0)
{
v___x_4068_ = v___x_4051_;
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
else
{
lean_inc(v_a_4066_);
lean_dec(v___x_4051_);
v___x_4068_ = lean_box(0);
v_isShared_4069_ = v_isSharedCheck_4073_;
goto v_resetjp_4067_;
}
v_resetjp_4067_:
{
lean_object* v___x_4071_; 
if (v_isShared_4069_ == 0)
{
v___x_4071_ = v___x_4068_;
goto v_reusejp_4070_;
}
else
{
lean_object* v_reuseFailAlloc_4072_; 
v_reuseFailAlloc_4072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4072_, 0, v_a_4066_);
v___x_4071_ = v_reuseFailAlloc_4072_;
goto v_reusejp_4070_;
}
v_reusejp_4070_:
{
return v___x_4071_;
}
}
}
}
}
}
else
{
lean_object* v_a_4075_; lean_object* v___x_4077_; uint8_t v_isShared_4078_; uint8_t v_isSharedCheck_4082_; 
lean_dec(v_mvarId_4027_);
v_a_4075_ = lean_ctor_get(v___x_4037_, 0);
v_isSharedCheck_4082_ = !lean_is_exclusive(v___x_4037_);
if (v_isSharedCheck_4082_ == 0)
{
v___x_4077_ = v___x_4037_;
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
else
{
lean_inc(v_a_4075_);
lean_dec(v___x_4037_);
v___x_4077_ = lean_box(0);
v_isShared_4078_ = v_isSharedCheck_4082_;
goto v_resetjp_4076_;
}
v_resetjp_4076_:
{
lean_object* v___x_4080_; 
if (v_isShared_4078_ == 0)
{
v___x_4080_ = v___x_4077_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4081_; 
v_reuseFailAlloc_4081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4081_, 0, v_a_4075_);
v___x_4080_ = v_reuseFailAlloc_4081_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
return v___x_4080_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4083_, lean_object* v_t_4084_, lean_object* v_init_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v_res_4091_; 
v_res_4091_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4083_, v_t_4084_, v_init_4085_, v___y_4086_, v___y_4087_, v___y_4088_, v___y_4089_);
lean_dec(v___y_4089_);
lean_dec_ref(v___y_4088_);
lean_dec(v___y_4087_);
lean_dec_ref(v___y_4086_);
lean_dec_ref(v_t_4084_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_){
_start:
{
lean_object* v_lctx_4101_; lean_object* v_decls_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; 
v_lctx_4101_ = lean_ctor_get(v___y_4096_, 2);
v_decls_4102_ = lean_ctor_get(v_lctx_4101_, 1);
v___x_4103_ = lean_box(0);
v___x_4104_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4105_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4095_, v_decls_4102_, v___x_4104_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v_a_4106_; lean_object* v___x_4108_; uint8_t v_isShared_4109_; uint8_t v_isSharedCheck_4118_; 
v_a_4106_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4108_ = v___x_4105_;
v_isShared_4109_ = v_isSharedCheck_4118_;
goto v_resetjp_4107_;
}
else
{
lean_inc(v_a_4106_);
lean_dec(v___x_4105_);
v___x_4108_ = lean_box(0);
v_isShared_4109_ = v_isSharedCheck_4118_;
goto v_resetjp_4107_;
}
v_resetjp_4107_:
{
lean_object* v_fst_4110_; 
v_fst_4110_ = lean_ctor_get(v_a_4106_, 0);
lean_inc(v_fst_4110_);
lean_dec(v_a_4106_);
if (lean_obj_tag(v_fst_4110_) == 0)
{
lean_object* v___x_4112_; 
if (v_isShared_4109_ == 0)
{
lean_ctor_set(v___x_4108_, 0, v___x_4103_);
v___x_4112_ = v___x_4108_;
goto v_reusejp_4111_;
}
else
{
lean_object* v_reuseFailAlloc_4113_; 
v_reuseFailAlloc_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4113_, 0, v___x_4103_);
v___x_4112_ = v_reuseFailAlloc_4113_;
goto v_reusejp_4111_;
}
v_reusejp_4111_:
{
return v___x_4112_;
}
}
else
{
lean_object* v_val_4114_; lean_object* v___x_4116_; 
v_val_4114_ = lean_ctor_get(v_fst_4110_, 0);
lean_inc(v_val_4114_);
lean_dec_ref(v_fst_4110_);
if (v_isShared_4109_ == 0)
{
lean_ctor_set(v___x_4108_, 0, v_val_4114_);
v___x_4116_ = v___x_4108_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_val_4114_);
v___x_4116_ = v_reuseFailAlloc_4117_;
goto v_reusejp_4115_;
}
v_reusejp_4115_:
{
return v___x_4116_;
}
}
}
}
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
v_a_4119_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4105_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4105_);
v___x_4121_ = lean_box(0);
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
v_resetjp_4120_:
{
lean_object* v___x_4124_; 
if (v_isShared_4122_ == 0)
{
v___x_4124_ = v___x_4121_;
goto v_reusejp_4123_;
}
else
{
lean_object* v_reuseFailAlloc_4125_; 
v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
v___x_4124_ = v_reuseFailAlloc_4125_;
goto v_reusejp_4123_;
}
v_reusejp_4123_:
{
return v___x_4124_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
lean_object* v___f_4140_; lean_object* v___x_4141_; 
lean_inc(v_mvarId_4134_);
v___f_4140_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4140_, 0, v_mvarId_4134_);
v___x_4141_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_4134_, v___f_4140_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4142_, v_a_4143_, v_a_4144_, v_a_4145_, v_a_4146_);
lean_dec(v_a_4146_);
lean_dec_ref(v_a_4145_);
lean_dec(v_a_4144_);
lean_dec_ref(v_a_4143_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4149_, lean_object* v_a_4150_, lean_object* v_a_4151_, lean_object* v_a_4152_, lean_object* v_a_4153_){
_start:
{
lean_object* v___x_4155_; 
lean_inc(v_mvarId_4149_);
v___x_4155_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4149_, v_a_4150_, v_a_4151_, v_a_4152_, v_a_4153_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4158_; uint8_t v_isShared_4159_; uint8_t v_isSharedCheck_4165_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4158_ = v___x_4155_;
v_isShared_4159_ = v_isSharedCheck_4165_;
goto v_resetjp_4157_;
}
else
{
lean_inc(v_a_4156_);
lean_dec(v___x_4155_);
v___x_4158_ = lean_box(0);
v_isShared_4159_ = v_isSharedCheck_4165_;
goto v_resetjp_4157_;
}
v_resetjp_4157_:
{
if (lean_obj_tag(v_a_4156_) == 1)
{
lean_object* v_val_4160_; 
lean_del_object(v___x_4158_);
lean_dec(v_mvarId_4149_);
v_val_4160_ = lean_ctor_get(v_a_4156_, 0);
lean_inc(v_val_4160_);
lean_dec_ref(v_a_4156_);
v_mvarId_4149_ = v_val_4160_;
goto _start;
}
else
{
lean_object* v___x_4163_; 
lean_dec(v_a_4156_);
if (v_isShared_4159_ == 0)
{
lean_ctor_set(v___x_4158_, 0, v_mvarId_4149_);
v___x_4163_ = v___x_4158_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_mvarId_4149_);
v___x_4163_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
return v___x_4163_;
}
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec(v_mvarId_4149_);
v_a_4166_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4155_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4155_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
lean_object* v___x_4171_; 
if (v_isShared_4169_ == 0)
{
v___x_4171_ = v___x_4168_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v_a_4166_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4174_, lean_object* v_a_4175_, lean_object* v_a_4176_, lean_object* v_a_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_Meta_substVars(v_mvarId_4174_, v_a_4175_, v_a_4176_, v_a_4177_, v_a_4178_);
lean_dec(v_a_4178_);
lean_dec_ref(v_a_4177_);
lean_dec(v_a_4176_);
lean_dec_ref(v_a_4175_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4243_; uint8_t v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4243_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_4244_ = 0;
v___x_4245_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4246_ = l_Lean_registerTraceClass(v___x_4243_, v___x_4244_, v___x_4245_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4247_){
_start:
{
lean_object* v_res_4248_; 
v_res_4248_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4248_;
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
