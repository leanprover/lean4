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
lean_object* v___f_51_; lean_object* v___x_28771__overap_52_; lean_object* v___x_53_; 
v___f_51_ = ((lean_object*)(l_panic___at___00Lean_Meta_substCore_spec__1___closed__0));
v___x_28771__overap_52_ = lean_panic_fn_borrowed(v___f_51_, v_msg_45_);
lean_inc(v___y_49_);
lean_inc_ref(v___y_48_);
lean_inc(v___y_47_);
lean_inc_ref(v___y_46_);
v___x_53_ = lean_apply_5(v___x_28771__overap_52_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, lean_box(0));
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
uint8_t v___x_33166__boxed_248_; uint8_t v___x_33167__boxed_249_; lean_object* v_res_250_; 
v___x_33166__boxed_248_ = lean_unbox(v___x_240_);
v___x_33167__boxed_249_ = lean_unbox(v___x_241_);
v_res_250_ = l_Lean_Meta_substCore___lam__1(v_type_236_, v___x_237_, v___x_238_, v___x_239_, v___x_33166__boxed_248_, v___x_33167__boxed_249_, v_hAux_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
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
lean_object* v_ref_390_; lean_object* v___x_391_; lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_436_; 
v_ref_390_ = lean_ctor_get(v___y_387_, 5);
v___x_391_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msg_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
v_a_392_ = lean_ctor_get(v___x_391_, 0);
v_isSharedCheck_436_ = !lean_is_exclusive(v___x_391_);
if (v_isSharedCheck_436_ == 0)
{
v___x_394_ = v___x_391_;
v_isShared_395_ = v_isSharedCheck_436_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_391_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_436_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_396_; lean_object* v_traceState_397_; lean_object* v_env_398_; lean_object* v_nextMacroScope_399_; lean_object* v_ngen_400_; lean_object* v_auxDeclNGen_401_; lean_object* v_cache_402_; lean_object* v_messages_403_; lean_object* v_infoState_404_; lean_object* v_snapshotTasks_405_; lean_object* v___x_407_; uint8_t v_isShared_408_; uint8_t v_isSharedCheck_435_; 
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
v_isSharedCheck_435_ = !lean_is_exclusive(v___x_396_);
if (v_isSharedCheck_435_ == 0)
{
v___x_407_ = v___x_396_;
v_isShared_408_ = v_isSharedCheck_435_;
goto v_resetjp_406_;
}
else
{
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
v___x_407_ = lean_box(0);
v_isShared_408_ = v_isSharedCheck_435_;
goto v_resetjp_406_;
}
v_resetjp_406_:
{
uint64_t v_tid_409_; lean_object* v_traces_410_; lean_object* v___x_412_; uint8_t v_isShared_413_; uint8_t v_isSharedCheck_434_; 
v_tid_409_ = lean_ctor_get_uint64(v_traceState_397_, sizeof(void*)*1);
v_traces_410_ = lean_ctor_get(v_traceState_397_, 0);
v_isSharedCheck_434_ = !lean_is_exclusive(v_traceState_397_);
if (v_isSharedCheck_434_ == 0)
{
v___x_412_ = v_traceState_397_;
v_isShared_413_ = v_isSharedCheck_434_;
goto v_resetjp_411_;
}
else
{
lean_inc(v_traces_410_);
lean_dec(v_traceState_397_);
v___x_412_ = lean_box(0);
v_isShared_413_ = v_isSharedCheck_434_;
goto v_resetjp_411_;
}
v_resetjp_411_:
{
lean_object* v___x_414_; double v___x_415_; uint8_t v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_414_ = lean_box(0);
v___x_415_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0);
v___x_416_ = 0;
v___x_417_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__1));
v___x_418_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_418_, 0, v_cls_383_);
lean_ctor_set(v___x_418_, 1, v___x_414_);
lean_ctor_set(v___x_418_, 2, v___x_417_);
lean_ctor_set_float(v___x_418_, sizeof(void*)*3, v___x_415_);
lean_ctor_set_float(v___x_418_, sizeof(void*)*3 + 8, v___x_415_);
lean_ctor_set_uint8(v___x_418_, sizeof(void*)*3 + 16, v___x_416_);
v___x_419_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__2));
v___x_420_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_420_, 0, v___x_418_);
lean_ctor_set(v___x_420_, 1, v_a_392_);
lean_ctor_set(v___x_420_, 2, v___x_419_);
lean_inc(v_ref_390_);
v___x_421_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_421_, 0, v_ref_390_);
lean_ctor_set(v___x_421_, 1, v___x_420_);
v___x_422_ = l_Lean_PersistentArray_push___redArg(v_traces_410_, v___x_421_);
if (v_isShared_413_ == 0)
{
lean_ctor_set(v___x_412_, 0, v___x_422_);
v___x_424_ = v___x_412_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_433_; 
v_reuseFailAlloc_433_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_433_, 0, v___x_422_);
lean_ctor_set_uint64(v_reuseFailAlloc_433_, sizeof(void*)*1, v_tid_409_);
v___x_424_ = v_reuseFailAlloc_433_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
lean_object* v___x_426_; 
if (v_isShared_408_ == 0)
{
lean_ctor_set(v___x_407_, 4, v___x_424_);
v___x_426_ = v___x_407_;
goto v_reusejp_425_;
}
else
{
lean_object* v_reuseFailAlloc_432_; 
v_reuseFailAlloc_432_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_432_, 0, v_env_398_);
lean_ctor_set(v_reuseFailAlloc_432_, 1, v_nextMacroScope_399_);
lean_ctor_set(v_reuseFailAlloc_432_, 2, v_ngen_400_);
lean_ctor_set(v_reuseFailAlloc_432_, 3, v_auxDeclNGen_401_);
lean_ctor_set(v_reuseFailAlloc_432_, 4, v___x_424_);
lean_ctor_set(v_reuseFailAlloc_432_, 5, v_cache_402_);
lean_ctor_set(v_reuseFailAlloc_432_, 6, v_messages_403_);
lean_ctor_set(v_reuseFailAlloc_432_, 7, v_infoState_404_);
lean_ctor_set(v_reuseFailAlloc_432_, 8, v_snapshotTasks_405_);
v___x_426_ = v_reuseFailAlloc_432_;
goto v_reusejp_425_;
}
v_reusejp_425_:
{
lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_427_ = lean_st_ref_set(v___y_388_, v___x_426_);
v___x_428_ = lean_box(0);
if (v_isShared_395_ == 0)
{
lean_ctor_set(v___x_394_, 0, v___x_428_);
v___x_430_ = v___x_394_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v___x_428_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___boxed(lean_object* v_cls_437_, lean_object* v_msg_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v_cls_437_, v_msg_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(lean_object* v_x_445_, lean_object* v_x_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v_ks_449_; lean_object* v_vs_450_; lean_object* v___x_452_; uint8_t v_isShared_453_; uint8_t v_isSharedCheck_474_; 
v_ks_449_ = lean_ctor_get(v_x_445_, 0);
v_vs_450_ = lean_ctor_get(v_x_445_, 1);
v_isSharedCheck_474_ = !lean_is_exclusive(v_x_445_);
if (v_isSharedCheck_474_ == 0)
{
v___x_452_ = v_x_445_;
v_isShared_453_ = v_isSharedCheck_474_;
goto v_resetjp_451_;
}
else
{
lean_inc(v_vs_450_);
lean_inc(v_ks_449_);
lean_dec(v_x_445_);
v___x_452_ = lean_box(0);
v_isShared_453_ = v_isSharedCheck_474_;
goto v_resetjp_451_;
}
v_resetjp_451_:
{
lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_454_ = lean_array_get_size(v_ks_449_);
v___x_455_ = lean_nat_dec_lt(v_x_446_, v___x_454_);
if (v___x_455_ == 0)
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_459_; 
lean_dec(v_x_446_);
v___x_456_ = lean_array_push(v_ks_449_, v_x_447_);
v___x_457_ = lean_array_push(v_vs_450_, v_x_448_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_457_);
lean_ctor_set(v___x_452_, 0, v___x_456_);
v___x_459_ = v___x_452_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_456_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
return v___x_459_;
}
}
else
{
lean_object* v_k_x27_461_; uint8_t v___x_462_; 
v_k_x27_461_ = lean_array_fget_borrowed(v_ks_449_, v_x_446_);
v___x_462_ = l_Lean_instBEqMVarId_beq(v_x_447_, v_k_x27_461_);
if (v___x_462_ == 0)
{
lean_object* v___x_464_; 
if (v_isShared_453_ == 0)
{
v___x_464_ = v___x_452_;
goto v_reusejp_463_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_ks_449_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_vs_450_);
v___x_464_ = v_reuseFailAlloc_468_;
goto v_reusejp_463_;
}
v_reusejp_463_:
{
lean_object* v___x_465_; lean_object* v___x_466_; 
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_add(v_x_446_, v___x_465_);
lean_dec(v_x_446_);
v_x_445_ = v___x_464_;
v_x_446_ = v___x_466_;
goto _start;
}
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_472_; 
v___x_469_ = lean_array_fset(v_ks_449_, v_x_446_, v_x_447_);
v___x_470_ = lean_array_fset(v_vs_450_, v_x_446_, v_x_448_);
lean_dec(v_x_446_);
if (v_isShared_453_ == 0)
{
lean_ctor_set(v___x_452_, 1, v___x_470_);
lean_ctor_set(v___x_452_, 0, v___x_469_);
v___x_472_ = v___x_452_;
goto v_reusejp_471_;
}
else
{
lean_object* v_reuseFailAlloc_473_; 
v_reuseFailAlloc_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_473_, 0, v___x_469_);
lean_ctor_set(v_reuseFailAlloc_473_, 1, v___x_470_);
v___x_472_ = v_reuseFailAlloc_473_;
goto v_reusejp_471_;
}
v_reusejp_471_:
{
return v___x_472_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(lean_object* v_n_475_, lean_object* v_k_476_, lean_object* v_v_477_){
_start:
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(0u);
v___x_479_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(v_n_475_, v___x_478_, v_k_476_, v_v_477_);
return v___x_479_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0(void){
_start:
{
size_t v___x_480_; size_t v___x_481_; size_t v___x_482_; 
v___x_480_ = ((size_t)5ULL);
v___x_481_ = ((size_t)1ULL);
v___x_482_ = lean_usize_shift_left(v___x_481_, v___x_480_);
return v___x_482_;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1(void){
_start:
{
size_t v___x_483_; size_t v___x_484_; size_t v___x_485_; 
v___x_483_ = ((size_t)1ULL);
v___x_484_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0);
v___x_485_ = lean_usize_sub(v___x_484_, v___x_483_);
return v___x_485_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__2(void){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(lean_object* v_x_487_, size_t v_x_488_, size_t v_x_489_, lean_object* v_x_490_, lean_object* v_x_491_){
_start:
{
if (lean_obj_tag(v_x_487_) == 0)
{
lean_object* v_es_492_; size_t v___x_493_; size_t v___x_494_; size_t v___x_495_; size_t v___x_496_; lean_object* v_j_497_; lean_object* v___x_498_; uint8_t v___x_499_; 
v_es_492_ = lean_ctor_get(v_x_487_, 0);
v___x_493_ = ((size_t)5ULL);
v___x_494_ = ((size_t)1ULL);
v___x_495_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1);
v___x_496_ = lean_usize_land(v_x_488_, v___x_495_);
v_j_497_ = lean_usize_to_nat(v___x_496_);
v___x_498_ = lean_array_get_size(v_es_492_);
v___x_499_ = lean_nat_dec_lt(v_j_497_, v___x_498_);
if (v___x_499_ == 0)
{
lean_dec(v_j_497_);
lean_dec(v_x_491_);
lean_dec(v_x_490_);
return v_x_487_;
}
else
{
lean_object* v___x_501_; uint8_t v_isShared_502_; uint8_t v_isSharedCheck_536_; 
lean_inc_ref(v_es_492_);
v_isSharedCheck_536_ = !lean_is_exclusive(v_x_487_);
if (v_isSharedCheck_536_ == 0)
{
lean_object* v_unused_537_; 
v_unused_537_ = lean_ctor_get(v_x_487_, 0);
lean_dec(v_unused_537_);
v___x_501_ = v_x_487_;
v_isShared_502_ = v_isSharedCheck_536_;
goto v_resetjp_500_;
}
else
{
lean_dec(v_x_487_);
v___x_501_ = lean_box(0);
v_isShared_502_ = v_isSharedCheck_536_;
goto v_resetjp_500_;
}
v_resetjp_500_:
{
lean_object* v_v_503_; lean_object* v___x_504_; lean_object* v_xs_x27_505_; lean_object* v___y_507_; 
v_v_503_ = lean_array_fget(v_es_492_, v_j_497_);
v___x_504_ = lean_box(0);
v_xs_x27_505_ = lean_array_fset(v_es_492_, v_j_497_, v___x_504_);
switch(lean_obj_tag(v_v_503_))
{
case 0:
{
lean_object* v_key_512_; lean_object* v_val_513_; lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_523_; 
v_key_512_ = lean_ctor_get(v_v_503_, 0);
v_val_513_ = lean_ctor_get(v_v_503_, 1);
v_isSharedCheck_523_ = !lean_is_exclusive(v_v_503_);
if (v_isSharedCheck_523_ == 0)
{
v___x_515_ = v_v_503_;
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
else
{
lean_inc(v_val_513_);
lean_inc(v_key_512_);
lean_dec(v_v_503_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_523_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
uint8_t v___x_517_; 
v___x_517_ = l_Lean_instBEqMVarId_beq(v_x_490_, v_key_512_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_del_object(v___x_515_);
v___x_518_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_512_, v_val_513_, v_x_490_, v_x_491_);
v___x_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_519_, 0, v___x_518_);
v___y_507_ = v___x_519_;
goto v___jp_506_;
}
else
{
lean_object* v___x_521_; 
lean_dec(v_val_513_);
lean_dec(v_key_512_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 1, v_x_491_);
lean_ctor_set(v___x_515_, 0, v_x_490_);
v___x_521_ = v___x_515_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_x_490_);
lean_ctor_set(v_reuseFailAlloc_522_, 1, v_x_491_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
v___y_507_ = v___x_521_;
goto v___jp_506_;
}
}
}
}
case 1:
{
lean_object* v_node_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_534_; 
v_node_524_ = lean_ctor_get(v_v_503_, 0);
v_isSharedCheck_534_ = !lean_is_exclusive(v_v_503_);
if (v_isSharedCheck_534_ == 0)
{
v___x_526_ = v_v_503_;
v_isShared_527_ = v_isSharedCheck_534_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_node_524_);
lean_dec(v_v_503_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_534_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
size_t v___x_528_; size_t v___x_529_; lean_object* v___x_530_; lean_object* v___x_532_; 
v___x_528_ = lean_usize_shift_right(v_x_488_, v___x_493_);
v___x_529_ = lean_usize_add(v_x_489_, v___x_494_);
v___x_530_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_node_524_, v___x_528_, v___x_529_, v_x_490_, v_x_491_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 0, v___x_530_);
v___x_532_ = v___x_526_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v___x_530_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v___y_507_ = v___x_532_;
goto v___jp_506_;
}
}
}
default: 
{
lean_object* v___x_535_; 
v___x_535_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_535_, 0, v_x_490_);
lean_ctor_set(v___x_535_, 1, v_x_491_);
v___y_507_ = v___x_535_;
goto v___jp_506_;
}
}
v___jp_506_:
{
lean_object* v___x_508_; lean_object* v___x_510_; 
v___x_508_ = lean_array_fset(v_xs_x27_505_, v_j_497_, v___y_507_);
lean_dec(v_j_497_);
if (v_isShared_502_ == 0)
{
lean_ctor_set(v___x_501_, 0, v___x_508_);
v___x_510_ = v___x_501_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___x_508_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
}
}
else
{
lean_object* v_ks_538_; lean_object* v_vs_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_559_; 
v_ks_538_ = lean_ctor_get(v_x_487_, 0);
v_vs_539_ = lean_ctor_get(v_x_487_, 1);
v_isSharedCheck_559_ = !lean_is_exclusive(v_x_487_);
if (v_isSharedCheck_559_ == 0)
{
v___x_541_ = v_x_487_;
v_isShared_542_ = v_isSharedCheck_559_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_vs_539_);
lean_inc(v_ks_538_);
lean_dec(v_x_487_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_559_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_558_; 
v_reuseFailAlloc_558_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_558_, 0, v_ks_538_);
lean_ctor_set(v_reuseFailAlloc_558_, 1, v_vs_539_);
v___x_544_ = v_reuseFailAlloc_558_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v_newNode_545_; uint8_t v___y_547_; size_t v___x_553_; uint8_t v___x_554_; 
v_newNode_545_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v___x_544_, v_x_490_, v_x_491_);
v___x_553_ = ((size_t)7ULL);
v___x_554_ = lean_usize_dec_le(v___x_553_, v_x_489_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; lean_object* v___x_556_; uint8_t v___x_557_; 
v___x_555_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_545_);
v___x_556_ = lean_unsigned_to_nat(4u);
v___x_557_ = lean_nat_dec_lt(v___x_555_, v___x_556_);
lean_dec(v___x_555_);
v___y_547_ = v___x_557_;
goto v___jp_546_;
}
else
{
v___y_547_ = v___x_554_;
goto v___jp_546_;
}
v___jp_546_:
{
if (v___y_547_ == 0)
{
lean_object* v_ks_548_; lean_object* v_vs_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
v_ks_548_ = lean_ctor_get(v_newNode_545_, 0);
lean_inc_ref(v_ks_548_);
v_vs_549_ = lean_ctor_get(v_newNode_545_, 1);
lean_inc_ref(v_vs_549_);
lean_dec_ref(v_newNode_545_);
v___x_550_ = lean_unsigned_to_nat(0u);
v___x_551_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__2);
v___x_552_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_x_489_, v_ks_548_, v_vs_549_, v___x_550_, v___x_551_);
lean_dec_ref(v_vs_549_);
lean_dec_ref(v_ks_548_);
return v___x_552_;
}
else
{
return v_newNode_545_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(size_t v_depth_560_, lean_object* v_keys_561_, lean_object* v_vals_562_, lean_object* v_i_563_, lean_object* v_entries_564_){
_start:
{
lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_565_ = lean_array_get_size(v_keys_561_);
v___x_566_ = lean_nat_dec_lt(v_i_563_, v___x_565_);
if (v___x_566_ == 0)
{
lean_dec(v_i_563_);
return v_entries_564_;
}
else
{
lean_object* v_k_567_; lean_object* v_v_568_; uint64_t v___x_569_; size_t v_h_570_; size_t v___x_571_; lean_object* v___x_572_; size_t v___x_573_; size_t v___x_574_; size_t v___x_575_; size_t v_h_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v_k_567_ = lean_array_fget_borrowed(v_keys_561_, v_i_563_);
v_v_568_ = lean_array_fget_borrowed(v_vals_562_, v_i_563_);
v___x_569_ = l_Lean_instHashableMVarId_hash(v_k_567_);
v_h_570_ = lean_uint64_to_usize(v___x_569_);
v___x_571_ = ((size_t)5ULL);
v___x_572_ = lean_unsigned_to_nat(1u);
v___x_573_ = ((size_t)1ULL);
v___x_574_ = lean_usize_sub(v_depth_560_, v___x_573_);
v___x_575_ = lean_usize_mul(v___x_571_, v___x_574_);
v_h_576_ = lean_usize_shift_right(v_h_570_, v___x_575_);
v___x_577_ = lean_nat_add(v_i_563_, v___x_572_);
lean_dec(v_i_563_);
lean_inc(v_v_568_);
lean_inc(v_k_567_);
v___x_578_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_entries_564_, v_h_576_, v_depth_560_, v_k_567_, v_v_568_);
v_i_563_ = v___x_577_;
v_entries_564_ = v___x_578_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_depth_580_, lean_object* v_keys_581_, lean_object* v_vals_582_, lean_object* v_i_583_, lean_object* v_entries_584_){
_start:
{
size_t v_depth_boxed_585_; lean_object* v_res_586_; 
v_depth_boxed_585_ = lean_unbox_usize(v_depth_580_);
lean_dec(v_depth_580_);
v_res_586_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_boxed_585_, v_keys_581_, v_vals_582_, v_i_583_, v_entries_584_);
lean_dec_ref(v_vals_582_);
lean_dec_ref(v_keys_581_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
size_t v_x_33550__boxed_592_; size_t v_x_33551__boxed_593_; lean_object* v_res_594_; 
v_x_33550__boxed_592_ = lean_unbox_usize(v_x_588_);
lean_dec(v_x_588_);
v_x_33551__boxed_593_ = lean_unbox_usize(v_x_589_);
lean_dec(v_x_589_);
v_res_594_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_587_, v_x_33550__boxed_592_, v_x_33551__boxed_593_, v_x_590_, v_x_591_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(lean_object* v_x_595_, lean_object* v_x_596_, lean_object* v_x_597_){
_start:
{
uint64_t v___x_598_; size_t v___x_599_; size_t v___x_600_; lean_object* v___x_601_; 
v___x_598_ = l_Lean_instHashableMVarId_hash(v_x_596_);
v___x_599_ = lean_uint64_to_usize(v___x_598_);
v___x_600_ = ((size_t)1ULL);
v___x_601_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_595_, v___x_599_, v___x_600_, v_x_596_, v_x_597_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(lean_object* v_mvarId_602_, lean_object* v_val_603_, lean_object* v___y_604_){
_start:
{
lean_object* v___x_606_; lean_object* v_mctx_607_; lean_object* v_cache_608_; lean_object* v_zetaDeltaFVarIds_609_; lean_object* v_postponed_610_; lean_object* v_diag_611_; lean_object* v___x_613_; uint8_t v_isShared_614_; uint8_t v_isSharedCheck_638_; 
v___x_606_ = lean_st_ref_take(v___y_604_);
v_mctx_607_ = lean_ctor_get(v___x_606_, 0);
v_cache_608_ = lean_ctor_get(v___x_606_, 1);
v_zetaDeltaFVarIds_609_ = lean_ctor_get(v___x_606_, 2);
v_postponed_610_ = lean_ctor_get(v___x_606_, 3);
v_diag_611_ = lean_ctor_get(v___x_606_, 4);
v_isSharedCheck_638_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_638_ == 0)
{
v___x_613_ = v___x_606_;
v_isShared_614_ = v_isSharedCheck_638_;
goto v_resetjp_612_;
}
else
{
lean_inc(v_diag_611_);
lean_inc(v_postponed_610_);
lean_inc(v_zetaDeltaFVarIds_609_);
lean_inc(v_cache_608_);
lean_inc(v_mctx_607_);
lean_dec(v___x_606_);
v___x_613_ = lean_box(0);
v_isShared_614_ = v_isSharedCheck_638_;
goto v_resetjp_612_;
}
v_resetjp_612_:
{
lean_object* v_depth_615_; lean_object* v_levelAssignDepth_616_; lean_object* v_mvarCounter_617_; lean_object* v_lDepth_618_; lean_object* v_decls_619_; lean_object* v_userNames_620_; lean_object* v_lAssignment_621_; lean_object* v_eAssignment_622_; lean_object* v_dAssignment_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_637_; 
v_depth_615_ = lean_ctor_get(v_mctx_607_, 0);
v_levelAssignDepth_616_ = lean_ctor_get(v_mctx_607_, 1);
v_mvarCounter_617_ = lean_ctor_get(v_mctx_607_, 2);
v_lDepth_618_ = lean_ctor_get(v_mctx_607_, 3);
v_decls_619_ = lean_ctor_get(v_mctx_607_, 4);
v_userNames_620_ = lean_ctor_get(v_mctx_607_, 5);
v_lAssignment_621_ = lean_ctor_get(v_mctx_607_, 6);
v_eAssignment_622_ = lean_ctor_get(v_mctx_607_, 7);
v_dAssignment_623_ = lean_ctor_get(v_mctx_607_, 8);
v_isSharedCheck_637_ = !lean_is_exclusive(v_mctx_607_);
if (v_isSharedCheck_637_ == 0)
{
v___x_625_ = v_mctx_607_;
v_isShared_626_ = v_isSharedCheck_637_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_dAssignment_623_);
lean_inc(v_eAssignment_622_);
lean_inc(v_lAssignment_621_);
lean_inc(v_userNames_620_);
lean_inc(v_decls_619_);
lean_inc(v_lDepth_618_);
lean_inc(v_mvarCounter_617_);
lean_inc(v_levelAssignDepth_616_);
lean_inc(v_depth_615_);
lean_dec(v_mctx_607_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_637_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_629_; 
v___x_627_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_eAssignment_622_, v_mvarId_602_, v_val_603_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 7, v___x_627_);
v___x_629_ = v___x_625_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_636_; 
v_reuseFailAlloc_636_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_636_, 0, v_depth_615_);
lean_ctor_set(v_reuseFailAlloc_636_, 1, v_levelAssignDepth_616_);
lean_ctor_set(v_reuseFailAlloc_636_, 2, v_mvarCounter_617_);
lean_ctor_set(v_reuseFailAlloc_636_, 3, v_lDepth_618_);
lean_ctor_set(v_reuseFailAlloc_636_, 4, v_decls_619_);
lean_ctor_set(v_reuseFailAlloc_636_, 5, v_userNames_620_);
lean_ctor_set(v_reuseFailAlloc_636_, 6, v_lAssignment_621_);
lean_ctor_set(v_reuseFailAlloc_636_, 7, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_636_, 8, v_dAssignment_623_);
v___x_629_ = v_reuseFailAlloc_636_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_631_; 
if (v_isShared_614_ == 0)
{
lean_ctor_set(v___x_613_, 0, v___x_629_);
v___x_631_ = v___x_613_;
goto v_reusejp_630_;
}
else
{
lean_object* v_reuseFailAlloc_635_; 
v_reuseFailAlloc_635_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_635_, 0, v___x_629_);
lean_ctor_set(v_reuseFailAlloc_635_, 1, v_cache_608_);
lean_ctor_set(v_reuseFailAlloc_635_, 2, v_zetaDeltaFVarIds_609_);
lean_ctor_set(v_reuseFailAlloc_635_, 3, v_postponed_610_);
lean_ctor_set(v_reuseFailAlloc_635_, 4, v_diag_611_);
v___x_631_ = v_reuseFailAlloc_635_;
goto v_reusejp_630_;
}
v_reusejp_630_:
{
lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; 
v___x_632_ = lean_st_ref_set(v___y_604_, v___x_631_);
v___x_633_ = lean_box(0);
v___x_634_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_634_, 0, v___x_633_);
return v___x_634_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object* v_mvarId_639_, lean_object* v_val_640_, lean_object* v___y_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_res_643_; 
v_res_643_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_mvarId_639_, v_val_640_, v___y_641_);
lean_dec(v___y_641_);
return v_res_643_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__1(void){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__0));
v___x_646_ = l_Lean_stringToMessageData(v___x_645_);
return v___x_646_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__3(void){
_start:
{
lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_648_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__2));
v___x_649_ = l_Lean_stringToMessageData(v___x_648_);
return v___x_649_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__7(void){
_start:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_653_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__6));
v___x_654_ = lean_unsigned_to_nat(22u);
v___x_655_ = lean_unsigned_to_nat(64u);
v___x_656_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__5));
v___x_657_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__4));
v___x_658_ = l_mkPanicMessageWithDecl(v___x_657_, v___x_656_, v___x_655_, v___x_654_, v___x_653_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object* v_snd_662_, lean_object* v___x_663_, lean_object* v_fvarId_664_, lean_object* v_hFVarId_665_, lean_object* v___x_666_, lean_object* v_fst_667_, lean_object* v_fvarSubst_668_, uint8_t v_clearH_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v___x_672_, uint8_t v_skip_673_, uint8_t v___x_674_, lean_object* v___x_675_, lean_object* v___x_676_, lean_object* v_a_677_, uint8_t v_symm_678_, uint8_t v___x_679_, lean_object* v___x_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_){
_start:
{
lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_703_; lean_object* v_mvarId_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v_newVal_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_761_; lean_object* v___y_762_; lean_object* v___y_786_; uint8_t v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v_major_790_; lean_object* v___y_791_; lean_object* v___y_792_; lean_object* v___y_793_; lean_object* v___y_794_; uint8_t v___y_827_; lean_object* v___y_828_; lean_object* v_motive_829_; lean_object* v_newType_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___y_833_; lean_object* v___y_834_; lean_object* v___x_845_; 
lean_inc(v_snd_662_);
v___x_845_ = l_Lean_MVarId_getDecl(v_snd_662_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v_a_846_; lean_object* v___x_847_; 
v_a_846_ = lean_ctor_get(v___x_845_, 0);
lean_inc(v_a_846_);
lean_dec_ref(v___x_845_);
lean_inc(v___x_663_);
v___x_847_ = l_Lean_FVarId_getDecl___redArg(v___x_663_, v___y_681_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_847_) == 0)
{
lean_object* v_a_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v_a_848_ = lean_ctor_get(v___x_847_, 0);
lean_inc(v_a_848_);
lean_dec_ref(v___x_847_);
v___x_849_ = l_Lean_LocalDecl_type(v_a_848_);
lean_dec(v_a_848_);
v___x_850_ = l_Lean_Meta_matchEq_x3f(v___x_849_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_850_) == 0)
{
lean_object* v_a_851_; 
v_a_851_ = lean_ctor_get(v___x_850_, 0);
lean_inc(v_a_851_);
lean_dec_ref(v___x_850_);
if (lean_obj_tag(v_a_851_) == 0)
{
lean_object* v___x_852_; lean_object* v___x_853_; 
lean_dec(v_a_846_);
lean_dec(v_a_677_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v___x_852_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__7, &l_Lean_Meta_substCore___lam__2___closed__7_once, _init_l_Lean_Meta_substCore___lam__2___closed__7);
v___x_853_ = l_panic___at___00Lean_Meta_substCore_spec__1(v___x_852_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
return v___x_853_;
}
else
{
lean_object* v_val_854_; lean_object* v_snd_855_; lean_object* v_fst_856_; lean_object* v_snd_857_; lean_object* v_type_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___f_861_; lean_object* v___y_863_; 
v_val_854_ = lean_ctor_get(v_a_851_, 0);
lean_inc(v_val_854_);
lean_dec_ref(v_a_851_);
v_snd_855_ = lean_ctor_get(v_val_854_, 1);
lean_inc(v_snd_855_);
lean_dec(v_val_854_);
v_fst_856_ = lean_ctor_get(v_snd_855_, 0);
lean_inc(v_fst_856_);
v_snd_857_ = lean_ctor_get(v_snd_855_, 1);
lean_inc(v_snd_857_);
lean_dec(v_snd_855_);
v_type_858_ = lean_ctor_get(v_a_846_, 2);
lean_inc_ref_n(v_type_858_, 2);
lean_dec(v_a_846_);
v___x_859_ = lean_box(v___x_679_);
v___x_860_ = lean_box(v___x_674_);
lean_inc_ref(v___x_670_);
lean_inc(v___x_671_);
lean_inc_ref(v___x_666_);
v___f_861_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 12, 6);
lean_closure_set(v___f_861_, 0, v_type_858_);
lean_closure_set(v___f_861_, 1, v___x_666_);
lean_closure_set(v___f_861_, 2, v___x_671_);
lean_closure_set(v___f_861_, 3, v___x_670_);
lean_closure_set(v___f_861_, 4, v___x_859_);
lean_closure_set(v___f_861_, 5, v___x_860_);
if (v_symm_678_ == 0)
{
lean_dec(v_fst_856_);
v___y_863_ = v_snd_857_;
goto v___jp_862_;
}
else
{
lean_dec(v_snd_857_);
v___y_863_ = v_fst_856_;
goto v___jp_862_;
}
v___jp_862_:
{
lean_object* v___x_864_; lean_object* v_a_865_; lean_object* v___x_866_; lean_object* v_a_867_; uint8_t v___x_868_; 
v___x_864_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_863_, v___y_682_);
v_a_865_ = lean_ctor_get(v___x_864_, 0);
lean_inc(v_a_865_);
lean_dec_ref(v___x_864_);
lean_inc(v___x_663_);
lean_inc_ref(v_type_858_);
v___x_866_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_type_858_, v___x_663_, v___y_682_);
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref(v___x_866_);
v___x_868_ = lean_unbox(v_a_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; lean_object* v___x_872_; 
lean_dec_ref(v___f_861_);
v___x_869_ = lean_mk_empty_array_with_capacity(v___x_680_);
lean_inc_ref(v___x_670_);
v___x_870_ = lean_array_push(v___x_869_, v___x_670_);
v___x_871_ = 1;
lean_inc_ref(v_type_858_);
v___x_872_ = l_Lean_Meta_mkLambdaFVars(v___x_870_, v_type_858_, v___x_679_, v___x_674_, v___x_679_, v___x_674_, v___x_871_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec_ref(v___x_870_);
if (lean_obj_tag(v___x_872_) == 0)
{
lean_object* v_a_873_; lean_object* v___x_874_; uint8_t v___x_875_; 
v_a_873_ = lean_ctor_get(v___x_872_, 0);
lean_inc(v_a_873_);
lean_dec_ref(v___x_872_);
lean_inc_ref(v___x_670_);
v___x_874_ = l_Lean_Expr_replaceFVar(v_type_858_, v___x_670_, v_a_865_);
lean_dec_ref(v_type_858_);
v___x_875_ = lean_unbox(v_a_867_);
lean_dec(v_a_867_);
v___y_827_ = v___x_875_;
v___y_828_ = v_a_865_;
v_motive_829_ = v_a_873_;
v_newType_830_ = v___x_874_;
v___y_831_ = v___y_681_;
v___y_832_ = v___y_682_;
v___y_833_ = v___y_683_;
v___y_834_ = v___y_684_;
goto v___jp_826_;
}
else
{
lean_object* v_a_876_; lean_object* v___x_878_; uint8_t v_isShared_879_; uint8_t v_isSharedCheck_883_; 
lean_dec(v_a_867_);
lean_dec(v_a_865_);
lean_dec_ref(v_type_858_);
lean_dec(v_a_677_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_876_ = lean_ctor_get(v___x_872_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v___x_872_);
if (v_isSharedCheck_883_ == 0)
{
v___x_878_ = v___x_872_;
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
else
{
lean_inc(v_a_876_);
lean_dec(v___x_872_);
v___x_878_ = lean_box(0);
v_isShared_879_ = v_isSharedCheck_883_;
goto v_resetjp_877_;
}
v_resetjp_877_:
{
lean_object* v___x_881_; 
if (v_isShared_879_ == 0)
{
v___x_881_ = v___x_878_;
goto v_reusejp_880_;
}
else
{
lean_object* v_reuseFailAlloc_882_; 
v_reuseFailAlloc_882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_882_, 0, v_a_876_);
v___x_881_ = v_reuseFailAlloc_882_;
goto v_reusejp_880_;
}
v_reusejp_880_:
{
return v___x_881_;
}
}
}
}
else
{
lean_object* v___x_884_; lean_object* v___x_885_; 
lean_inc_ref(v___x_670_);
v___x_884_ = l_Lean_Expr_replaceFVar(v_type_858_, v___x_670_, v_a_865_);
lean_inc(v_a_865_);
v___x_885_ = l_Lean_Meta_mkEqRefl(v_a_865_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref(v___x_885_);
lean_inc_ref(v___x_666_);
v___x_887_ = l_Lean_Expr_replaceFVar(v___x_884_, v___x_666_, v_a_886_);
lean_dec(v_a_886_);
lean_dec_ref(v___x_884_);
if (v_symm_678_ == 0)
{
lean_object* v___x_888_; 
lean_dec_ref(v_type_858_);
lean_inc_ref(v___x_670_);
lean_inc(v_a_865_);
v___x_888_ = l_Lean_Meta_mkEq(v_a_865_, v___x_670_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_888_) == 0)
{
lean_object* v_a_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v_a_889_ = lean_ctor_get(v___x_888_, 0);
lean_inc(v_a_889_);
lean_dec_ref(v___x_888_);
v___x_890_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__9));
v___x_891_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v___x_890_, v_a_889_, v___f_861_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; uint8_t v___x_893_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref(v___x_891_);
v___x_893_ = lean_unbox(v_a_867_);
lean_dec(v_a_867_);
v___y_827_ = v___x_893_;
v___y_828_ = v_a_865_;
v_motive_829_ = v_a_892_;
v_newType_830_ = v___x_887_;
v___y_831_ = v___y_681_;
v___y_832_ = v___y_682_;
v___y_833_ = v___y_683_;
v___y_834_ = v___y_684_;
goto v___jp_826_;
}
else
{
lean_object* v_a_894_; lean_object* v___x_896_; uint8_t v_isShared_897_; uint8_t v_isSharedCheck_901_; 
lean_dec_ref(v___x_887_);
lean_dec(v_a_867_);
lean_dec(v_a_865_);
lean_dec(v_a_677_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_894_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_901_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_901_ == 0)
{
v___x_896_ = v___x_891_;
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
else
{
lean_inc(v_a_894_);
lean_dec(v___x_891_);
v___x_896_ = lean_box(0);
v_isShared_897_ = v_isSharedCheck_901_;
goto v_resetjp_895_;
}
v_resetjp_895_:
{
lean_object* v___x_899_; 
if (v_isShared_897_ == 0)
{
v___x_899_ = v___x_896_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_a_894_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
else
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_909_; 
lean_dec_ref(v___x_887_);
lean_dec(v_a_867_);
lean_dec(v_a_865_);
lean_dec_ref(v___f_861_);
lean_dec(v_a_677_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_902_ = lean_ctor_get(v___x_888_, 0);
v_isSharedCheck_909_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_909_ == 0)
{
v___x_904_ = v___x_888_;
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_888_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_909_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v___x_907_; 
if (v_isShared_905_ == 0)
{
v___x_907_ = v___x_904_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_a_902_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; 
lean_dec_ref(v___f_861_);
v___x_910_ = lean_mk_empty_array_with_capacity(v___x_671_);
lean_inc_ref(v___x_670_);
v___x_911_ = lean_array_push(v___x_910_, v___x_670_);
lean_inc_ref(v___x_666_);
v___x_912_ = lean_array_push(v___x_911_, v___x_666_);
v___x_913_ = 1;
v___x_914_ = l_Lean_Meta_mkLambdaFVars(v___x_912_, v_type_858_, v___x_679_, v___x_674_, v___x_679_, v___x_674_, v___x_913_, v___y_681_, v___y_682_, v___y_683_, v___y_684_);
lean_dec_ref(v___x_912_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; uint8_t v___x_916_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref(v___x_914_);
v___x_916_ = lean_unbox(v_a_867_);
lean_dec(v_a_867_);
v___y_827_ = v___x_916_;
v___y_828_ = v_a_865_;
v_motive_829_ = v_a_915_;
v_newType_830_ = v___x_887_;
v___y_831_ = v___y_681_;
v___y_832_ = v___y_682_;
v___y_833_ = v___y_683_;
v___y_834_ = v___y_684_;
goto v___jp_826_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
lean_dec_ref(v___x_887_);
lean_dec(v_a_867_);
lean_dec(v_a_865_);
lean_dec(v_a_677_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_917_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_914_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_914_);
v___x_919_ = lean_box(0);
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
v_resetjp_918_:
{
lean_object* v___x_922_; 
if (v_isShared_920_ == 0)
{
v___x_922_ = v___x_919_;
goto v_reusejp_921_;
}
else
{
lean_object* v_reuseFailAlloc_923_; 
v_reuseFailAlloc_923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_923_, 0, v_a_917_);
v___x_922_ = v_reuseFailAlloc_923_;
goto v_reusejp_921_;
}
v_reusejp_921_:
{
return v___x_922_;
}
}
}
}
}
else
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_932_; 
lean_dec_ref(v___x_884_);
lean_dec(v_a_867_);
lean_dec(v_a_865_);
lean_dec_ref(v___f_861_);
lean_dec_ref(v_type_858_);
lean_dec(v_a_677_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_925_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_932_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_932_ == 0)
{
v___x_927_ = v___x_885_;
v_isShared_928_ = v_isSharedCheck_932_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_885_);
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
}
}
}
else
{
lean_object* v_a_933_; lean_object* v___x_935_; uint8_t v_isShared_936_; uint8_t v_isSharedCheck_940_; 
lean_dec(v_a_846_);
lean_dec(v_a_677_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_933_ = lean_ctor_get(v___x_850_, 0);
v_isSharedCheck_940_ = !lean_is_exclusive(v___x_850_);
if (v_isSharedCheck_940_ == 0)
{
v___x_935_ = v___x_850_;
v_isShared_936_ = v_isSharedCheck_940_;
goto v_resetjp_934_;
}
else
{
lean_inc(v_a_933_);
lean_dec(v___x_850_);
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
lean_dec(v_a_846_);
lean_dec(v_a_677_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_941_ = lean_ctor_get(v___x_847_, 0);
v_isSharedCheck_948_ = !lean_is_exclusive(v___x_847_);
if (v_isSharedCheck_948_ == 0)
{
v___x_943_ = v___x_847_;
v_isShared_944_ = v_isSharedCheck_948_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_a_941_);
lean_dec(v___x_847_);
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
}
else
{
lean_object* v_a_949_; lean_object* v___x_951_; uint8_t v_isShared_952_; uint8_t v_isSharedCheck_956_; 
lean_dec(v_a_677_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_949_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_956_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_956_ == 0)
{
v___x_951_ = v___x_845_;
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
else
{
lean_inc(v_a_949_);
lean_dec(v___x_845_);
v___x_951_ = lean_box(0);
v_isShared_952_ = v_isSharedCheck_956_;
goto v_resetjp_950_;
}
v_resetjp_950_:
{
lean_object* v___x_954_; 
if (v_isShared_952_ == 0)
{
v___x_954_ = v___x_951_;
goto v_reusejp_953_;
}
else
{
lean_object* v_reuseFailAlloc_955_; 
v_reuseFailAlloc_955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_955_, 0, v_a_949_);
v___x_954_ = v_reuseFailAlloc_955_;
goto v_reusejp_953_;
}
v_reusejp_953_:
{
return v___x_954_;
}
}
}
v___jp_686_:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_690_ = l_Lean_Meta_FVarSubst_insert(v___y_688_, v_fvarId_664_, v___y_689_);
v___x_691_ = l_Lean_Meta_FVarSubst_insert(v___x_690_, v_hFVarId_665_, v___x_666_);
v___x_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_692_, 0, v___x_691_);
lean_ctor_set(v___x_692_, 1, v___y_687_);
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v___x_692_);
return v___x_693_;
}
v___jp_694_:
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = lean_array_get_size(v___y_695_);
v___x_699_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_667_, v___y_695_, v___x_698_, v___x_698_, v_fvarSubst_668_);
lean_dec_ref(v___y_695_);
if (v_clearH_669_ == 0)
{
lean_object* v_a_700_; 
lean_dec_ref(v___y_697_);
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_700_);
lean_dec_ref(v___x_699_);
v___y_687_ = v___y_696_;
v___y_688_ = v_a_700_;
v___y_689_ = v___x_670_;
goto v___jp_686_;
}
else
{
lean_object* v_a_701_; 
lean_dec_ref(v___x_670_);
v_a_701_ = lean_ctor_get(v___x_699_, 0);
lean_inc(v_a_701_);
lean_dec_ref(v___x_699_);
v___y_687_ = v___y_696_;
v___y_688_ = v_a_701_;
v___y_689_ = v___y_697_;
goto v___jp_686_;
}
}
v___jp_702_:
{
lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_709_ = lean_array_get_size(v_fst_667_);
v___x_710_ = lean_nat_sub(v___x_709_, v___x_671_);
lean_dec(v___x_671_);
lean_inc(v___x_710_);
v___x_711_ = l_Lean_Meta_introNCore(v_mvarId_704_, v___x_710_, v___x_672_, v_skip_673_, v___x_674_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v_options_713_; uint8_t v_hasTrace_714_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
lean_inc(v_a_712_);
lean_dec_ref(v___x_711_);
v_options_713_ = lean_ctor_get(v___y_707_, 2);
v_hasTrace_714_ = lean_ctor_get_uint8(v_options_713_, sizeof(void*)*1);
if (v_hasTrace_714_ == 0)
{
lean_object* v_fst_715_; lean_object* v_snd_716_; 
lean_dec(v___x_710_);
lean_dec(v___x_675_);
v_fst_715_ = lean_ctor_get(v_a_712_, 0);
lean_inc(v_fst_715_);
v_snd_716_ = lean_ctor_get(v_a_712_, 1);
lean_inc(v_snd_716_);
lean_dec(v_a_712_);
v___y_695_ = v_fst_715_;
v___y_696_ = v_snd_716_;
v___y_697_ = v___y_703_;
goto v___jp_694_;
}
else
{
lean_object* v_fst_717_; lean_object* v_snd_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_746_; 
v_fst_717_ = lean_ctor_get(v_a_712_, 0);
v_snd_718_ = lean_ctor_get(v_a_712_, 1);
v_isSharedCheck_746_ = !lean_is_exclusive(v_a_712_);
if (v_isSharedCheck_746_ == 0)
{
v___x_720_ = v_a_712_;
v_isShared_721_ = v_isSharedCheck_746_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_snd_718_);
lean_inc(v_fst_717_);
lean_dec(v_a_712_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_746_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v_inheritedTraceOptions_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v_inheritedTraceOptions_722_ = lean_ctor_get(v___y_707_, 13);
v___x_723_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
lean_inc(v___x_675_);
v___x_724_ = l_Lean_Name_append(v___x_723_, v___x_675_);
v___x_725_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_722_, v_options_713_, v___x_724_);
lean_dec(v___x_724_);
if (v___x_725_ == 0)
{
lean_del_object(v___x_720_);
lean_dec(v___x_710_);
lean_dec(v___x_675_);
v___y_695_ = v_fst_717_;
v___y_696_ = v_snd_718_;
v___y_697_ = v___y_703_;
goto v___jp_694_;
}
else
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_731_; 
v___x_726_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__1, &l_Lean_Meta_substCore___lam__2___closed__1_once, _init_l_Lean_Meta_substCore___lam__2___closed__1);
v___x_727_ = l_Nat_reprFast(v___x_710_);
v___x_728_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_728_, 0, v___x_727_);
v___x_729_ = l_Lean_MessageData_ofFormat(v___x_728_);
if (v_isShared_721_ == 0)
{
lean_ctor_set_tag(v___x_720_, 7);
lean_ctor_set(v___x_720_, 1, v___x_729_);
lean_ctor_set(v___x_720_, 0, v___x_726_);
v___x_731_ = v___x_720_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_726_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v___x_729_);
v___x_731_ = v_reuseFailAlloc_745_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; 
v___x_732_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__3, &l_Lean_Meta_substCore___lam__2___closed__3_once, _init_l_Lean_Meta_substCore___lam__2___closed__3);
v___x_733_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_731_);
lean_ctor_set(v___x_733_, 1, v___x_732_);
lean_inc(v_snd_718_);
v___x_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_734_, 0, v_snd_718_);
v___x_735_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_735_, 0, v___x_733_);
lean_ctor_set(v___x_735_, 1, v___x_734_);
v___x_736_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_675_, v___x_735_, v___y_705_, v___y_706_, v___y_707_, v___y_708_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_dec_ref(v___x_736_);
v___y_695_ = v_fst_717_;
v___y_696_ = v_snd_718_;
v___y_697_ = v___y_703_;
goto v___jp_694_;
}
else
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_744_; 
lean_dec(v_snd_718_);
lean_dec(v_fst_717_);
lean_dec_ref(v___y_703_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_744_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_744_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_744_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_742_; 
if (v_isShared_740_ == 0)
{
v___x_742_ = v___x_739_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_743_; 
v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
v___x_742_ = v_reuseFailAlloc_743_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
return v___x_742_;
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
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_754_; 
lean_dec(v___x_710_);
lean_dec_ref(v___y_703_);
lean_dec(v___x_675_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
v_a_747_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_754_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_754_ == 0)
{
v___x_749_ = v___x_711_;
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_711_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_754_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v___x_752_; 
if (v_isShared_750_ == 0)
{
v___x_752_ = v___x_749_;
goto v_reusejp_751_;
}
else
{
lean_object* v_reuseFailAlloc_753_; 
v_reuseFailAlloc_753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_753_, 0, v_a_747_);
v___x_752_ = v_reuseFailAlloc_753_;
goto v_reusejp_751_;
}
v_reusejp_751_:
{
return v___x_752_;
}
}
}
}
v___jp_755_:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_snd_662_, v_newVal_758_, v___y_760_);
lean_dec_ref(v___x_763_);
v___x_764_ = l_Lean_Expr_mvarId_x21(v___y_756_);
lean_dec_ref(v___y_756_);
if (v_clearH_669_ == 0)
{
lean_dec(v___x_676_);
lean_dec(v___x_663_);
v___y_703_ = v___y_757_;
v_mvarId_704_ = v___x_764_;
v___y_705_ = v___y_759_;
v___y_706_ = v___y_760_;
v___y_707_ = v___y_761_;
v___y_708_ = v___y_762_;
goto v___jp_702_;
}
else
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_MVarId_clear(v___x_764_, v___x_663_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___x_767_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref(v___x_765_);
v___x_767_ = l_Lean_MVarId_clear(v_a_766_, v___x_676_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref(v___x_767_);
v___y_703_ = v___y_757_;
v_mvarId_704_ = v_a_768_;
v___y_705_ = v___y_759_;
v___y_706_ = v___y_760_;
v___y_707_ = v___y_761_;
v___y_708_ = v___y_762_;
goto v___jp_702_;
}
else
{
lean_object* v_a_769_; lean_object* v___x_771_; uint8_t v_isShared_772_; uint8_t v_isSharedCheck_776_; 
lean_dec_ref(v___y_757_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
v_a_769_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_776_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_776_ == 0)
{
v___x_771_ = v___x_767_;
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
else
{
lean_inc(v_a_769_);
lean_dec(v___x_767_);
v___x_771_ = lean_box(0);
v_isShared_772_ = v_isSharedCheck_776_;
goto v_resetjp_770_;
}
v_resetjp_770_:
{
lean_object* v___x_774_; 
if (v_isShared_772_ == 0)
{
v___x_774_ = v___x_771_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_a_769_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
else
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_784_; 
lean_dec_ref(v___y_757_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
v_a_777_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_784_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_784_ == 0)
{
v___x_779_ = v___x_765_;
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_765_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_784_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v___x_782_; 
if (v_isShared_780_ == 0)
{
v___x_782_ = v___x_779_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v_a_777_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
}
}
}
v___jp_785_:
{
lean_object* v___x_795_; 
v___x_795_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_789_, v_a_677_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_795_) == 0)
{
if (v___y_787_ == 0)
{
lean_object* v_a_796_; lean_object* v___x_797_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc_n(v_a_796_, 2);
lean_dec_ref(v___x_795_);
v___x_797_ = l_Lean_Meta_mkEqNDRec(v___y_786_, v_a_796_, v_major_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_797_) == 0)
{
lean_object* v_a_798_; 
v_a_798_ = lean_ctor_get(v___x_797_, 0);
lean_inc(v_a_798_);
lean_dec_ref(v___x_797_);
v___y_756_ = v_a_796_;
v___y_757_ = v___y_788_;
v_newVal_758_ = v_a_798_;
v___y_759_ = v___y_791_;
v___y_760_ = v___y_792_;
v___y_761_ = v___y_793_;
v___y_762_ = v___y_794_;
goto v___jp_755_;
}
else
{
lean_object* v_a_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_806_; 
lean_dec(v_a_796_);
lean_dec_ref(v___y_788_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_799_ = lean_ctor_get(v___x_797_, 0);
v_isSharedCheck_806_ = !lean_is_exclusive(v___x_797_);
if (v_isSharedCheck_806_ == 0)
{
v___x_801_ = v___x_797_;
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_a_799_);
lean_dec(v___x_797_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_806_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_804_; 
if (v_isShared_802_ == 0)
{
v___x_804_ = v___x_801_;
goto v_reusejp_803_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_a_799_);
v___x_804_ = v_reuseFailAlloc_805_;
goto v_reusejp_803_;
}
v_reusejp_803_:
{
return v___x_804_;
}
}
}
}
else
{
lean_object* v_a_807_; lean_object* v___x_808_; 
v_a_807_ = lean_ctor_get(v___x_795_, 0);
lean_inc_n(v_a_807_, 2);
lean_dec_ref(v___x_795_);
v___x_808_ = l_Lean_Meta_mkEqRec(v___y_786_, v_a_807_, v_major_790_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
if (lean_obj_tag(v___x_808_) == 0)
{
lean_object* v_a_809_; 
v_a_809_ = lean_ctor_get(v___x_808_, 0);
lean_inc(v_a_809_);
lean_dec_ref(v___x_808_);
v___y_756_ = v_a_807_;
v___y_757_ = v___y_788_;
v_newVal_758_ = v_a_809_;
v___y_759_ = v___y_791_;
v___y_760_ = v___y_792_;
v___y_761_ = v___y_793_;
v___y_762_ = v___y_794_;
goto v___jp_755_;
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_a_807_);
lean_dec_ref(v___y_788_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
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
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
lean_dec_ref(v_major_790_);
lean_dec_ref(v___y_788_);
lean_dec_ref(v___y_786_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_818_ = lean_ctor_get(v___x_795_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_795_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_795_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_795_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
v___jp_826_:
{
if (v_symm_678_ == 0)
{
lean_object* v___x_835_; 
lean_inc_ref(v___x_666_);
v___x_835_ = l_Lean_Meta_mkEqSymm(v___x_666_, v___y_831_, v___y_832_, v___y_833_, v___y_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v_a_836_; 
v_a_836_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_a_836_);
lean_dec_ref(v___x_835_);
v___y_786_ = v_motive_829_;
v___y_787_ = v___y_827_;
v___y_788_ = v___y_828_;
v___y_789_ = v_newType_830_;
v_major_790_ = v_a_836_;
v___y_791_ = v___y_831_;
v___y_792_ = v___y_832_;
v___y_793_ = v___y_833_;
v___y_794_ = v___y_834_;
goto v___jp_785_;
}
else
{
lean_object* v_a_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_844_; 
lean_dec_ref(v_newType_830_);
lean_dec_ref(v_motive_829_);
lean_dec_ref(v___y_828_);
lean_dec(v_a_677_);
lean_dec(v___x_676_);
lean_dec(v___x_675_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_670_);
lean_dec(v_fvarSubst_668_);
lean_dec_ref(v___x_666_);
lean_dec(v_hFVarId_665_);
lean_dec(v_fvarId_664_);
lean_dec(v___x_663_);
lean_dec(v_snd_662_);
v_a_837_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_844_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_844_ == 0)
{
v___x_839_ = v___x_835_;
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_a_837_);
lean_dec(v___x_835_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_844_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_840_ == 0)
{
v___x_842_ = v___x_839_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v_a_837_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
}
}
else
{
lean_inc_ref(v___x_666_);
v___y_786_ = v_motive_829_;
v___y_787_ = v___y_827_;
v___y_788_ = v___y_828_;
v___y_789_ = v_newType_830_;
v_major_790_ = v___x_666_;
v___y_791_ = v___y_831_;
v___y_792_ = v___y_832_;
v___y_793_ = v___y_833_;
v___y_794_ = v___y_834_;
goto v___jp_785_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object** _args){
lean_object* v_snd_957_ = _args[0];
lean_object* v___x_958_ = _args[1];
lean_object* v_fvarId_959_ = _args[2];
lean_object* v_hFVarId_960_ = _args[3];
lean_object* v___x_961_ = _args[4];
lean_object* v_fst_962_ = _args[5];
lean_object* v_fvarSubst_963_ = _args[6];
lean_object* v_clearH_964_ = _args[7];
lean_object* v___x_965_ = _args[8];
lean_object* v___x_966_ = _args[9];
lean_object* v___x_967_ = _args[10];
lean_object* v_skip_968_ = _args[11];
lean_object* v___x_969_ = _args[12];
lean_object* v___x_970_ = _args[13];
lean_object* v___x_971_ = _args[14];
lean_object* v_a_972_ = _args[15];
lean_object* v_symm_973_ = _args[16];
lean_object* v___x_974_ = _args[17];
lean_object* v___x_975_ = _args[18];
lean_object* v___y_976_ = _args[19];
lean_object* v___y_977_ = _args[20];
lean_object* v___y_978_ = _args[21];
lean_object* v___y_979_ = _args[22];
lean_object* v___y_980_ = _args[23];
_start:
{
uint8_t v_clearH_boxed_981_; uint8_t v_skip_boxed_982_; uint8_t v___x_33816__boxed_983_; uint8_t v_symm_boxed_984_; uint8_t v___x_33820__boxed_985_; lean_object* v_res_986_; 
v_clearH_boxed_981_ = lean_unbox(v_clearH_964_);
v_skip_boxed_982_ = lean_unbox(v_skip_968_);
v___x_33816__boxed_983_ = lean_unbox(v___x_969_);
v_symm_boxed_984_ = lean_unbox(v_symm_973_);
v___x_33820__boxed_985_ = lean_unbox(v___x_974_);
v_res_986_ = l_Lean_Meta_substCore___lam__2(v_snd_957_, v___x_958_, v_fvarId_959_, v_hFVarId_960_, v___x_961_, v_fst_962_, v_fvarSubst_963_, v_clearH_boxed_981_, v___x_965_, v___x_966_, v___x_967_, v_skip_boxed_982_, v___x_33816__boxed_983_, v___x_970_, v___x_971_, v_a_972_, v_symm_boxed_984_, v___x_33820__boxed_985_, v___x_975_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
lean_dec(v___y_979_);
lean_dec_ref(v___y_978_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___x_975_);
lean_dec_ref(v_fst_962_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(lean_object* v_a_987_, lean_object* v_a_988_){
_start:
{
if (lean_obj_tag(v_a_987_) == 0)
{
lean_object* v___x_989_; 
v___x_989_ = l_List_reverse___redArg(v_a_988_);
return v___x_989_;
}
else
{
lean_object* v_head_990_; lean_object* v_tail_991_; lean_object* v___x_993_; uint8_t v_isShared_994_; uint8_t v_isSharedCheck_1000_; 
v_head_990_ = lean_ctor_get(v_a_987_, 0);
v_tail_991_ = lean_ctor_get(v_a_987_, 1);
v_isSharedCheck_1000_ = !lean_is_exclusive(v_a_987_);
if (v_isSharedCheck_1000_ == 0)
{
v___x_993_ = v_a_987_;
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
else
{
lean_inc(v_tail_991_);
lean_inc(v_head_990_);
lean_dec(v_a_987_);
v___x_993_ = lean_box(0);
v_isShared_994_ = v_isSharedCheck_1000_;
goto v_resetjp_992_;
}
v_resetjp_992_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = l_Lean_MessageData_ofName(v_head_990_);
if (v_isShared_994_ == 0)
{
lean_ctor_set(v___x_993_, 1, v_a_988_);
lean_ctor_set(v___x_993_, 0, v___x_995_);
v___x_997_ = v___x_993_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v___x_995_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_a_988_);
v___x_997_ = v_reuseFailAlloc_999_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
v_a_987_ = v_tail_991_;
v_a_988_ = v___x_997_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(size_t v_sz_1001_, size_t v_i_1002_, lean_object* v_bs_1003_){
_start:
{
uint8_t v___x_1004_; 
v___x_1004_ = lean_usize_dec_lt(v_i_1002_, v_sz_1001_);
if (v___x_1004_ == 0)
{
return v_bs_1003_;
}
else
{
lean_object* v_v_1005_; lean_object* v___x_1006_; lean_object* v_bs_x27_1007_; size_t v___x_1008_; size_t v___x_1009_; lean_object* v___x_1010_; 
v_v_1005_ = lean_array_uget(v_bs_1003_, v_i_1002_);
v___x_1006_ = lean_unsigned_to_nat(0u);
v_bs_x27_1007_ = lean_array_uset(v_bs_1003_, v_i_1002_, v___x_1006_);
v___x_1008_ = ((size_t)1ULL);
v___x_1009_ = lean_usize_add(v_i_1002_, v___x_1008_);
v___x_1010_ = lean_array_uset(v_bs_x27_1007_, v_i_1002_, v_v_1005_);
v_i_1002_ = v___x_1009_;
v_bs_1003_ = v___x_1010_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8___boxed(lean_object* v_sz_1012_, lean_object* v_i_1013_, lean_object* v_bs_1014_){
_start:
{
size_t v_sz_boxed_1015_; size_t v_i_boxed_1016_; lean_object* v_res_1017_; 
v_sz_boxed_1015_ = lean_unbox_usize(v_sz_1012_);
lean_dec(v_sz_1012_);
v_i_boxed_1016_ = lean_unbox_usize(v_i_1013_);
lean_dec(v_i_1013_);
v_res_1017_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_boxed_1015_, v_i_boxed_1016_, v_bs_1014_);
return v_res_1017_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__3(void){
_start:
{
lean_object* v___x_1022_; lean_object* v___x_1023_; 
v___x_1022_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__2));
v___x_1023_ = l_Lean_stringToMessageData(v___x_1022_);
return v___x_1023_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__5(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__4));
v___x_1026_ = l_Lean_stringToMessageData(v___x_1025_);
return v___x_1026_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__8(void){
_start:
{
lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1030_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__7));
v___x_1031_ = l_Lean_MessageData_ofFormat(v___x_1030_);
return v___x_1031_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__9(void){
_start:
{
lean_object* v___x_1032_; lean_object* v___x_1033_; 
v___x_1032_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__8, &l_Lean_Meta_substCore___lam__3___closed__8_once, _init_l_Lean_Meta_substCore___lam__3___closed__8);
v___x_1033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1033_, 0, v___x_1032_);
return v___x_1033_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__11(void){
_start:
{
lean_object* v___x_1035_; lean_object* v___x_1036_; 
v___x_1035_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__10));
v___x_1036_ = l_Lean_stringToMessageData(v___x_1035_);
return v___x_1036_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__13(void){
_start:
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__12));
v___x_1039_ = l_Lean_stringToMessageData(v___x_1038_);
return v___x_1039_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__15(void){
_start:
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
v___x_1041_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__14));
v___x_1042_ = l_Lean_stringToMessageData(v___x_1041_);
return v___x_1042_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__17(void){
_start:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__16));
v___x_1045_ = l_Lean_stringToMessageData(v___x_1044_);
return v___x_1045_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__19(void){
_start:
{
lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1047_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__18));
v___x_1048_ = l_Lean_stringToMessageData(v___x_1047_);
return v___x_1048_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__25(void){
_start:
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
v___x_1058_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__24));
v___x_1059_ = l_Lean_stringToMessageData(v___x_1058_);
return v___x_1059_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__27(void){
_start:
{
lean_object* v___x_1061_; lean_object* v___x_1062_; 
v___x_1061_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__26));
v___x_1062_ = l_Lean_stringToMessageData(v___x_1061_);
return v___x_1062_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__3___closed__29(void){
_start:
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
v___x_1064_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__28));
v___x_1065_ = l_Lean_stringToMessageData(v___x_1064_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3(lean_object* v_mvarId_1068_, lean_object* v_hFVarId_1069_, lean_object* v___x_1070_, uint8_t v_clearH_1071_, lean_object* v_fvarSubst_1072_, uint8_t v_symm_1073_, uint8_t v_tryToSkip_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___y_1081_; lean_object* v___y_1082_; lean_object* v___y_1083_; lean_object* v___y_1084_; lean_object* v___y_1085_; lean_object* v___y_1086_; lean_object* v___y_1087_; lean_object* v___x_1118_; 
lean_inc(v_mvarId_1068_);
v___x_1118_ = l_Lean_MVarId_getTag(v_mvarId_1068_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v_a_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; 
v_a_1119_ = lean_ctor_get(v___x_1118_, 0);
lean_inc(v_a_1119_);
lean_dec_ref(v___x_1118_);
v___x_1120_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
lean_inc(v_mvarId_1068_);
v___x_1121_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_1068_, v___x_1120_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; 
lean_dec_ref(v___x_1121_);
lean_inc(v_hFVarId_1069_);
v___x_1122_ = l_Lean_FVarId_getDecl___redArg(v_hFVarId_1069_, v___y_1075_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1122_) == 0)
{
lean_object* v_a_1123_; lean_object* v___x_1124_; lean_object* v___y_1126_; lean_object* v___y_1127_; lean_object* v___x_1139_; 
v_a_1123_ = lean_ctor_get(v___x_1122_, 0);
lean_inc(v_a_1123_);
lean_dec_ref(v___x_1122_);
v___x_1124_ = l_Lean_LocalDecl_type(v_a_1123_);
lean_dec(v_a_1123_);
lean_inc_ref(v___x_1124_);
v___x_1139_ = l_Lean_Meta_matchEq_x3f(v___x_1124_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v_a_1140_; 
v_a_1140_ = lean_ctor_get(v___x_1139_, 0);
lean_inc(v_a_1140_);
lean_dec_ref(v___x_1139_);
if (lean_obj_tag(v_a_1140_) == 0)
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_dec_ref(v___x_1124_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
v___x_1141_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__9, &l_Lean_Meta_substCore___lam__3___closed__9_once, _init_l_Lean_Meta_substCore___lam__3___closed__9);
v___x_1142_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1120_, v_mvarId_1068_, v___x_1141_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v___x_1142_;
}
else
{
lean_object* v_val_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1465_; 
v_val_1143_ = lean_ctor_get(v_a_1140_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_a_1140_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1145_ = v_a_1140_;
v_isShared_1146_ = v_isSharedCheck_1465_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_val_1143_);
lean_dec(v_a_1140_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1465_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_snd_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1463_; 
v_snd_1147_ = lean_ctor_get(v_val_1143_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_val_1143_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_val_1143_, 0);
lean_dec(v_unused_1464_);
v___x_1149_ = v_val_1143_;
v_isShared_1150_ = v_isSharedCheck_1463_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_snd_1147_);
lean_dec(v_val_1143_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1463_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v_fst_1151_; lean_object* v_snd_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1462_; 
v_fst_1151_ = lean_ctor_get(v_snd_1147_, 0);
v_snd_1152_ = lean_ctor_get(v_snd_1147_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_snd_1147_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1154_ = v_snd_1147_;
v_isShared_1155_ = v_isSharedCheck_1462_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_snd_1152_);
lean_inc(v_fst_1151_);
lean_dec(v_snd_1147_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1462_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
uint8_t v___x_1156_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; uint8_t v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; lean_object* v___y_1173_; lean_object* v___y_1174_; uint8_t v_skip_1175_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; uint8_t v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; uint8_t v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1198_; lean_object* v___y_1199_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; uint8_t v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; uint8_t v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; uint8_t v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; uint8_t v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1458_; 
v___x_1156_ = 1;
if (v_symm_1073_ == 0)
{
lean_inc(v_fst_1151_);
v___y_1458_ = v_fst_1151_;
goto v___jp_1457_;
}
else
{
lean_inc(v_snd_1152_);
v___y_1458_ = v_snd_1152_;
goto v___jp_1457_;
}
v___jp_1157_:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___f_1181_; lean_object* v___x_1182_; 
v___x_1176_ = lean_box(v_clearH_1071_);
v___x_1177_ = lean_box(v_skip_1175_);
v___x_1178_ = lean_box(v___x_1156_);
v___x_1179_ = lean_box(v_symm_1073_);
v___x_1180_ = lean_box(v___y_1163_);
v___f_1181_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__2___boxed), 24, 19);
lean_closure_set(v___f_1181_, 0, v___y_1158_);
lean_closure_set(v___f_1181_, 1, v___y_1173_);
lean_closure_set(v___f_1181_, 2, v___y_1172_);
lean_closure_set(v___f_1181_, 3, v_hFVarId_1069_);
lean_closure_set(v___f_1181_, 4, v___y_1171_);
lean_closure_set(v___f_1181_, 5, v___y_1160_);
lean_closure_set(v___f_1181_, 6, v_fvarSubst_1072_);
lean_closure_set(v___f_1181_, 7, v___x_1176_);
lean_closure_set(v___f_1181_, 8, v___y_1162_);
lean_closure_set(v___f_1181_, 9, v___y_1168_);
lean_closure_set(v___f_1181_, 10, v___y_1166_);
lean_closure_set(v___f_1181_, 11, v___x_1177_);
lean_closure_set(v___f_1181_, 12, v___x_1178_);
lean_closure_set(v___f_1181_, 13, v___y_1174_);
lean_closure_set(v___f_1181_, 14, v___y_1169_);
lean_closure_set(v___f_1181_, 15, v_a_1119_);
lean_closure_set(v___f_1181_, 16, v___x_1179_);
lean_closure_set(v___f_1181_, 17, v___x_1180_);
lean_closure_set(v___f_1181_, 18, v___y_1165_);
v___x_1182_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v___y_1167_, v___f_1181_, v___y_1159_, v___y_1164_, v___y_1170_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1159_);
return v___x_1182_;
}
v___jp_1183_:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v___x_1200_ = lean_unsigned_to_nat(0u);
v___x_1201_ = lean_array_get(v___x_1070_, v___y_1191_, v___x_1200_);
lean_inc(v___x_1201_);
v___x_1202_ = l_Lean_mkFVar(v___x_1201_);
v___x_1203_ = lean_unsigned_to_nat(1u);
v___x_1204_ = lean_array_get(v___x_1070_, v___y_1191_, v___x_1203_);
lean_dec_ref(v___y_1191_);
lean_inc(v___x_1204_);
v___x_1205_ = l_Lean_mkFVar(v___x_1204_);
if (v_tryToSkip_1074_ == 0)
{
lean_dec_ref(v___y_1195_);
lean_dec(v___y_1193_);
v___y_1158_ = v___y_1186_;
v___y_1159_ = v___y_1196_;
v___y_1160_ = v___y_1187_;
v___y_1161_ = v___y_1199_;
v___y_1162_ = v___x_1202_;
v___y_1163_ = v___y_1189_;
v___y_1164_ = v___y_1197_;
v___y_1165_ = v___x_1203_;
v___y_1166_ = v___y_1184_;
v___y_1167_ = v___y_1194_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___x_1201_;
v___y_1170_ = v___y_1198_;
v___y_1171_ = v___x_1205_;
v___y_1172_ = v___y_1188_;
v___y_1173_ = v___x_1204_;
v___y_1174_ = v___y_1190_;
v_skip_1175_ = v___y_1192_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = lean_array_get_size(v___y_1195_);
lean_dec_ref(v___y_1195_);
v___x_1207_ = lean_nat_dec_eq(v___x_1206_, v___y_1193_);
lean_dec(v___y_1193_);
if (v___x_1207_ == 0)
{
v___y_1158_ = v___y_1186_;
v___y_1159_ = v___y_1196_;
v___y_1160_ = v___y_1187_;
v___y_1161_ = v___y_1199_;
v___y_1162_ = v___x_1202_;
v___y_1163_ = v___y_1189_;
v___y_1164_ = v___y_1197_;
v___y_1165_ = v___x_1203_;
v___y_1166_ = v___y_1184_;
v___y_1167_ = v___y_1194_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___x_1201_;
v___y_1170_ = v___y_1198_;
v___y_1171_ = v___x_1205_;
v___y_1172_ = v___y_1188_;
v___y_1173_ = v___x_1204_;
v___y_1174_ = v___y_1190_;
v_skip_1175_ = v___y_1192_;
goto v___jp_1157_;
}
else
{
lean_object* v___x_1208_; 
lean_inc(v___y_1194_);
v___x_1208_ = l_Lean_MVarId_getType(v___y_1194_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1210_; lean_object* v_a_1211_; uint8_t v___x_1212_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc_n(v_a_1209_, 2);
lean_dec_ref(v___x_1208_);
lean_inc(v___x_1201_);
v___x_1210_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1209_, v___x_1201_, v___y_1197_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = lean_unbox(v_a_1211_);
lean_dec(v_a_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v_a_1214_; uint8_t v___x_1215_; 
lean_inc(v___x_1204_);
v___x_1213_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1209_, v___x_1204_, v___y_1197_);
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref(v___x_1213_);
v___x_1215_ = lean_unbox(v_a_1214_);
lean_dec(v_a_1214_);
if (v___x_1215_ == 0)
{
lean_dec_ref(v___x_1205_);
lean_dec_ref(v___x_1202_);
lean_dec(v___y_1190_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec(v_a_1119_);
lean_dec(v_hFVarId_1069_);
v___y_1081_ = v___y_1194_;
v___y_1082_ = v___x_1201_;
v___y_1083_ = v___y_1198_;
v___y_1084_ = v___y_1196_;
v___y_1085_ = v___y_1199_;
v___y_1086_ = v___x_1204_;
v___y_1087_ = v___y_1197_;
goto v___jp_1080_;
}
else
{
v___y_1158_ = v___y_1186_;
v___y_1159_ = v___y_1196_;
v___y_1160_ = v___y_1187_;
v___y_1161_ = v___y_1199_;
v___y_1162_ = v___x_1202_;
v___y_1163_ = v___y_1189_;
v___y_1164_ = v___y_1197_;
v___y_1165_ = v___x_1203_;
v___y_1166_ = v___y_1184_;
v___y_1167_ = v___y_1194_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___x_1201_;
v___y_1170_ = v___y_1198_;
v___y_1171_ = v___x_1205_;
v___y_1172_ = v___y_1188_;
v___y_1173_ = v___x_1204_;
v___y_1174_ = v___y_1190_;
v_skip_1175_ = v___y_1192_;
goto v___jp_1157_;
}
}
else
{
lean_dec(v_a_1209_);
v___y_1158_ = v___y_1186_;
v___y_1159_ = v___y_1196_;
v___y_1160_ = v___y_1187_;
v___y_1161_ = v___y_1199_;
v___y_1162_ = v___x_1202_;
v___y_1163_ = v___y_1189_;
v___y_1164_ = v___y_1197_;
v___y_1165_ = v___x_1203_;
v___y_1166_ = v___y_1184_;
v___y_1167_ = v___y_1194_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___x_1201_;
v___y_1170_ = v___y_1198_;
v___y_1171_ = v___x_1205_;
v___y_1172_ = v___y_1188_;
v___y_1173_ = v___x_1204_;
v___y_1174_ = v___y_1190_;
v_skip_1175_ = v___y_1192_;
goto v___jp_1157_;
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v___x_1205_);
lean_dec(v___x_1204_);
lean_dec_ref(v___x_1202_);
lean_dec(v___x_1201_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1194_);
lean_dec(v___y_1190_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
v_a_1216_ = lean_ctor_get(v___x_1208_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1208_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1208_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1208_);
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
}
}
v___jp_1224_:
{
lean_object* v___x_1243_; 
lean_inc_ref(v___y_1232_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
v___x_1243_ = lean_apply_5(v___y_1232_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, lean_box(0));
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; uint8_t v___x_1245_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref(v___x_1243_);
v___x_1245_ = lean_unbox(v_a_1244_);
lean_dec(v_a_1244_);
if (v___x_1245_ == 0)
{
lean_dec(v___y_1235_);
lean_del_object(v___x_1154_);
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1226_;
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1229_;
v___y_1189_ = v___y_1230_;
v___y_1190_ = v___y_1231_;
v___y_1191_ = v___y_1233_;
v___y_1192_ = v___y_1234_;
v___y_1193_ = v___y_1236_;
v___y_1194_ = v___y_1237_;
v___y_1195_ = v___y_1238_;
v___y_1196_ = v___y_1239_;
v___y_1197_ = v___y_1240_;
v___y_1198_ = v___y_1241_;
v___y_1199_ = v___y_1242_;
goto v___jp_1183_;
}
else
{
lean_object* v___x_1246_; size_t v_sz_1247_; size_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1246_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__11, &l_Lean_Meta_substCore___lam__3___closed__11_once, _init_l_Lean_Meta_substCore___lam__3___closed__11);
v_sz_1247_ = lean_array_size(v___y_1238_);
v___x_1248_ = ((size_t)0ULL);
lean_inc_ref(v___y_1238_);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1247_, v___x_1248_, v___y_1238_);
v___x_1250_ = lean_array_to_list(v___x_1249_);
v___x_1251_ = lean_box(0);
v___x_1252_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(v___x_1250_, v___x_1251_);
v___x_1253_ = l_Lean_MessageData_ofList(v___x_1252_);
if (v_isShared_1155_ == 0)
{
lean_ctor_set_tag(v___x_1154_, 7);
lean_ctor_set(v___x_1154_, 1, v___x_1253_);
lean_ctor_set(v___x_1154_, 0, v___x_1246_);
v___x_1255_ = v___x_1154_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v___x_1246_);
lean_ctor_set(v_reuseFailAlloc_1265_, 1, v___x_1253_);
v___x_1255_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
lean_object* v___x_1256_; 
v___x_1256_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1235_, v___x_1255_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_dec_ref(v___x_1256_);
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1226_;
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1229_;
v___y_1189_ = v___y_1230_;
v___y_1190_ = v___y_1231_;
v___y_1191_ = v___y_1233_;
v___y_1192_ = v___y_1234_;
v___y_1193_ = v___y_1236_;
v___y_1194_ = v___y_1237_;
v___y_1195_ = v___y_1238_;
v___y_1196_ = v___y_1239_;
v___y_1197_ = v___y_1240_;
v___y_1198_ = v___y_1241_;
v___y_1199_ = v___y_1242_;
goto v___jp_1183_;
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1231_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
v_a_1257_ = lean_ctor_get(v___x_1256_, 0);
v_isSharedCheck_1264_ = !lean_is_exclusive(v___x_1256_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1259_ = v___x_1256_;
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_a_1257_);
lean_dec(v___x_1256_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1264_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v___x_1262_; 
if (v_isShared_1260_ == 0)
{
v___x_1262_ = v___x_1259_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_a_1257_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
}
else
{
lean_object* v_a_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1273_; 
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec_ref(v___y_1238_);
lean_dec(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1231_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
v_a_1266_ = lean_ctor_get(v___x_1243_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1243_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1268_ = v___x_1243_;
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_a_1266_);
lean_dec(v___x_1243_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1273_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1271_; 
if (v_isShared_1269_ == 0)
{
v___x_1271_ = v___x_1268_;
goto v_reusejp_1270_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_a_1266_);
v___x_1271_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1270_;
}
v_reusejp_1270_:
{
return v___x_1271_;
}
}
}
}
v___jp_1274_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_box(0);
lean_inc(v___y_1284_);
v___x_1291_ = l_Lean_Meta_introNCore(v___y_1280_, v___y_1284_, v___x_1290_, v___y_1282_, v___x_1156_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v_fst_1293_; lean_object* v_snd_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1323_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref(v___x_1291_);
v_fst_1293_ = lean_ctor_get(v_a_1292_, 0);
v_snd_1294_ = lean_ctor_get(v_a_1292_, 1);
v_isSharedCheck_1323_ = !lean_is_exclusive(v_a_1292_);
if (v_isSharedCheck_1323_ == 0)
{
v___x_1296_ = v_a_1292_;
v_isShared_1297_ = v_isSharedCheck_1323_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_snd_1294_);
lean_inc(v_fst_1293_);
lean_dec(v_a_1292_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1323_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; 
lean_inc_ref(v___y_1281_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1298_ = lean_apply_5(v___y_1281_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, lean_box(0));
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; uint8_t v___x_1300_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref(v___x_1298_);
v___x_1300_ = lean_unbox(v_a_1299_);
lean_dec(v_a_1299_);
if (v___x_1300_ == 0)
{
lean_del_object(v___x_1296_);
lean_inc(v_snd_1294_);
v___y_1225_ = v___x_1290_;
v___y_1226_ = v___y_1275_;
v___y_1227_ = v_snd_1294_;
v___y_1228_ = v___y_1276_;
v___y_1229_ = v___y_1277_;
v___y_1230_ = v___y_1278_;
v___y_1231_ = v___y_1279_;
v___y_1232_ = v___y_1281_;
v___y_1233_ = v_fst_1293_;
v___y_1234_ = v___y_1282_;
v___y_1235_ = v___y_1283_;
v___y_1236_ = v___y_1284_;
v___y_1237_ = v_snd_1294_;
v___y_1238_ = v___y_1285_;
v___y_1239_ = v___y_1286_;
v___y_1240_ = v___y_1287_;
v___y_1241_ = v___y_1288_;
v___y_1242_ = v___y_1289_;
goto v___jp_1224_;
}
else
{
lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; 
v___x_1301_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__13, &l_Lean_Meta_substCore___lam__3___closed__13_once, _init_l_Lean_Meta_substCore___lam__3___closed__13);
lean_inc(v_snd_1294_);
v___x_1302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1302_, 0, v_snd_1294_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set_tag(v___x_1296_, 7);
lean_ctor_set(v___x_1296_, 1, v___x_1302_);
lean_ctor_set(v___x_1296_, 0, v___x_1301_);
v___x_1304_ = v___x_1296_;
goto v_reusejp_1303_;
}
else
{
lean_object* v_reuseFailAlloc_1314_; 
v_reuseFailAlloc_1314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1301_);
lean_ctor_set(v_reuseFailAlloc_1314_, 1, v___x_1302_);
v___x_1304_ = v_reuseFailAlloc_1314_;
goto v_reusejp_1303_;
}
v_reusejp_1303_:
{
lean_object* v___x_1305_; 
lean_inc(v___y_1283_);
v___x_1305_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1283_, v___x_1304_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_dec_ref(v___x_1305_);
lean_inc(v_snd_1294_);
v___y_1225_ = v___x_1290_;
v___y_1226_ = v___y_1275_;
v___y_1227_ = v_snd_1294_;
v___y_1228_ = v___y_1276_;
v___y_1229_ = v___y_1277_;
v___y_1230_ = v___y_1278_;
v___y_1231_ = v___y_1279_;
v___y_1232_ = v___y_1281_;
v___y_1233_ = v_fst_1293_;
v___y_1234_ = v___y_1282_;
v___y_1235_ = v___y_1283_;
v___y_1236_ = v___y_1284_;
v___y_1237_ = v_snd_1294_;
v___y_1238_ = v___y_1285_;
v___y_1239_ = v___y_1286_;
v___y_1240_ = v___y_1287_;
v___y_1241_ = v___y_1288_;
v___y_1242_ = v___y_1289_;
goto v___jp_1224_;
}
else
{
lean_object* v_a_1306_; lean_object* v___x_1308_; uint8_t v_isShared_1309_; uint8_t v_isSharedCheck_1313_; 
lean_dec(v_snd_1294_);
lean_dec(v_fst_1293_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec(v___y_1279_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
v_a_1306_ = lean_ctor_get(v___x_1305_, 0);
v_isSharedCheck_1313_ = !lean_is_exclusive(v___x_1305_);
if (v_isSharedCheck_1313_ == 0)
{
v___x_1308_ = v___x_1305_;
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
else
{
lean_inc(v_a_1306_);
lean_dec(v___x_1305_);
v___x_1308_ = lean_box(0);
v_isShared_1309_ = v_isSharedCheck_1313_;
goto v_resetjp_1307_;
}
v_resetjp_1307_:
{
lean_object* v___x_1311_; 
if (v_isShared_1309_ == 0)
{
v___x_1311_ = v___x_1308_;
goto v_reusejp_1310_;
}
else
{
lean_object* v_reuseFailAlloc_1312_; 
v_reuseFailAlloc_1312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1312_, 0, v_a_1306_);
v___x_1311_ = v_reuseFailAlloc_1312_;
goto v_reusejp_1310_;
}
v_reusejp_1310_:
{
return v___x_1311_;
}
}
}
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
lean_del_object(v___x_1296_);
lean_dec(v_snd_1294_);
lean_dec(v_fst_1293_);
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec(v___y_1279_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
v_a_1315_ = lean_ctor_get(v___x_1298_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1298_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1298_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1298_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
else
{
lean_object* v_a_1324_; lean_object* v___x_1326_; uint8_t v_isShared_1327_; uint8_t v_isSharedCheck_1331_; 
lean_dec(v___y_1289_);
lean_dec_ref(v___y_1288_);
lean_dec(v___y_1287_);
lean_dec_ref(v___y_1286_);
lean_dec_ref(v___y_1285_);
lean_dec(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec(v___y_1279_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
v_a_1324_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1331_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1326_ = v___x_1291_;
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
else
{
lean_inc(v_a_1324_);
lean_dec(v___x_1291_);
v___x_1326_ = lean_box(0);
v_isShared_1327_ = v_isSharedCheck_1331_;
goto v_resetjp_1325_;
}
v_resetjp_1325_:
{
lean_object* v___x_1329_; 
if (v_isShared_1327_ == 0)
{
v___x_1329_ = v___x_1326_;
goto v_reusejp_1328_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_a_1324_);
v___x_1329_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1328_;
}
v_reusejp_1328_:
{
return v___x_1329_;
}
}
}
}
v___jp_1332_:
{
lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; uint8_t v___x_1346_; lean_object* v___x_1347_; 
v___x_1342_ = lean_unsigned_to_nat(2u);
v___x_1343_ = lean_mk_empty_array_with_capacity(v___x_1342_);
v___x_1344_ = lean_array_push(v___x_1343_, v___y_1336_);
lean_inc(v_hFVarId_1069_);
v___x_1345_ = lean_array_push(v___x_1344_, v_hFVarId_1069_);
v___x_1346_ = 0;
v___x_1347_ = l_Lean_MVarId_revert(v_mvarId_1068_, v___x_1345_, v___x_1156_, v___x_1346_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v_fst_1349_; lean_object* v_snd_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1379_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref(v___x_1347_);
v_fst_1349_ = lean_ctor_get(v_a_1348_, 0);
v_snd_1350_ = lean_ctor_get(v_a_1348_, 1);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_a_1348_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1352_ = v_a_1348_;
v_isShared_1353_ = v_isSharedCheck_1379_;
goto v_resetjp_1351_;
}
else
{
lean_inc(v_snd_1350_);
lean_inc(v_fst_1349_);
lean_dec(v_a_1348_);
v___x_1352_ = lean_box(0);
v_isShared_1353_ = v_isSharedCheck_1379_;
goto v_resetjp_1351_;
}
v_resetjp_1351_:
{
lean_object* v___x_1354_; 
lean_inc_ref(v___y_1335_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
v___x_1354_ = lean_apply_5(v___y_1335_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, lean_box(0));
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; uint8_t v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref(v___x_1354_);
v___x_1356_ = lean_unbox(v_a_1355_);
lean_dec(v_a_1355_);
if (v___x_1356_ == 0)
{
lean_del_object(v___x_1352_);
lean_inc(v_fst_1349_);
v___y_1275_ = v___x_1342_;
v___y_1276_ = v_fst_1349_;
v___y_1277_ = v___y_1333_;
v___y_1278_ = v___x_1346_;
v___y_1279_ = v___y_1334_;
v___y_1280_ = v_snd_1350_;
v___y_1281_ = v___y_1335_;
v___y_1282_ = v___x_1346_;
v___y_1283_ = v___y_1337_;
v___y_1284_ = v___x_1342_;
v___y_1285_ = v_fst_1349_;
v___y_1286_ = v___y_1338_;
v___y_1287_ = v___y_1339_;
v___y_1288_ = v___y_1340_;
v___y_1289_ = v___y_1341_;
goto v___jp_1274_;
}
else
{
lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1360_; 
v___x_1357_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__15, &l_Lean_Meta_substCore___lam__3___closed__15_once, _init_l_Lean_Meta_substCore___lam__3___closed__15);
lean_inc(v_snd_1350_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v_snd_1350_);
if (v_isShared_1353_ == 0)
{
lean_ctor_set_tag(v___x_1352_, 7);
lean_ctor_set(v___x_1352_, 1, v___x_1358_);
lean_ctor_set(v___x_1352_, 0, v___x_1357_);
v___x_1360_ = v___x_1352_;
goto v_reusejp_1359_;
}
else
{
lean_object* v_reuseFailAlloc_1370_; 
v_reuseFailAlloc_1370_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1370_, 0, v___x_1357_);
lean_ctor_set(v_reuseFailAlloc_1370_, 1, v___x_1358_);
v___x_1360_ = v_reuseFailAlloc_1370_;
goto v_reusejp_1359_;
}
v_reusejp_1359_:
{
lean_object* v___x_1361_; 
lean_inc(v___y_1337_);
v___x_1361_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1337_, v___x_1360_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_dec_ref(v___x_1361_);
lean_inc(v_fst_1349_);
v___y_1275_ = v___x_1342_;
v___y_1276_ = v_fst_1349_;
v___y_1277_ = v___y_1333_;
v___y_1278_ = v___x_1346_;
v___y_1279_ = v___y_1334_;
v___y_1280_ = v_snd_1350_;
v___y_1281_ = v___y_1335_;
v___y_1282_ = v___x_1346_;
v___y_1283_ = v___y_1337_;
v___y_1284_ = v___x_1342_;
v___y_1285_ = v_fst_1349_;
v___y_1286_ = v___y_1338_;
v___y_1287_ = v___y_1339_;
v___y_1288_ = v___y_1340_;
v___y_1289_ = v___y_1341_;
goto v___jp_1274_;
}
else
{
lean_object* v_a_1362_; lean_object* v___x_1364_; uint8_t v_isShared_1365_; uint8_t v_isSharedCheck_1369_; 
lean_dec(v_snd_1350_);
lean_dec(v_fst_1349_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1334_);
lean_dec(v___y_1333_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
v_a_1362_ = lean_ctor_get(v___x_1361_, 0);
v_isSharedCheck_1369_ = !lean_is_exclusive(v___x_1361_);
if (v_isSharedCheck_1369_ == 0)
{
v___x_1364_ = v___x_1361_;
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
else
{
lean_inc(v_a_1362_);
lean_dec(v___x_1361_);
v___x_1364_ = lean_box(0);
v_isShared_1365_ = v_isSharedCheck_1369_;
goto v_resetjp_1363_;
}
v_resetjp_1363_:
{
lean_object* v___x_1367_; 
if (v_isShared_1365_ == 0)
{
v___x_1367_ = v___x_1364_;
goto v_reusejp_1366_;
}
else
{
lean_object* v_reuseFailAlloc_1368_; 
v_reuseFailAlloc_1368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1368_, 0, v_a_1362_);
v___x_1367_ = v_reuseFailAlloc_1368_;
goto v_reusejp_1366_;
}
v_reusejp_1366_:
{
return v___x_1367_;
}
}
}
}
}
}
else
{
lean_object* v_a_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1378_; 
lean_del_object(v___x_1352_);
lean_dec(v_snd_1350_);
lean_dec(v_fst_1349_);
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1334_);
lean_dec(v___y_1333_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
v_a_1371_ = lean_ctor_get(v___x_1354_, 0);
v_isSharedCheck_1378_ = !lean_is_exclusive(v___x_1354_);
if (v_isSharedCheck_1378_ == 0)
{
v___x_1373_ = v___x_1354_;
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_a_1371_);
lean_dec(v___x_1354_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1378_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1376_; 
if (v_isShared_1374_ == 0)
{
v___x_1376_ = v___x_1373_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1377_; 
v_reuseFailAlloc_1377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1377_, 0, v_a_1371_);
v___x_1376_ = v_reuseFailAlloc_1377_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
return v___x_1376_;
}
}
}
}
}
else
{
lean_object* v_a_1380_; lean_object* v___x_1382_; uint8_t v_isShared_1383_; uint8_t v_isSharedCheck_1387_; 
lean_dec(v___y_1341_);
lean_dec_ref(v___y_1340_);
lean_dec(v___y_1339_);
lean_dec_ref(v___y_1338_);
lean_dec(v___y_1337_);
lean_dec(v___y_1334_);
lean_dec(v___y_1333_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
v_a_1380_ = lean_ctor_get(v___x_1347_, 0);
v_isSharedCheck_1387_ = !lean_is_exclusive(v___x_1347_);
if (v_isSharedCheck_1387_ == 0)
{
v___x_1382_ = v___x_1347_;
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
else
{
lean_inc(v_a_1380_);
lean_dec(v___x_1347_);
v___x_1382_ = lean_box(0);
v_isShared_1383_ = v_isSharedCheck_1387_;
goto v_resetjp_1381_;
}
v_resetjp_1381_:
{
lean_object* v___x_1385_; 
if (v_isShared_1383_ == 0)
{
v___x_1385_ = v___x_1382_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_a_1380_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
v___jp_1388_:
{
lean_object* v___x_1400_; lean_object* v_a_1401_; uint8_t v___x_1402_; 
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1394_);
v___x_1400_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v___y_1394_, v___y_1392_, v___y_1397_);
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = lean_unbox(v_a_1401_);
lean_dec(v_a_1401_);
if (v___x_1402_ == 0)
{
lean_dec_ref(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1145_);
v___y_1333_ = v___y_1389_;
v___y_1334_ = v___y_1390_;
v___y_1335_ = v___y_1391_;
v___y_1336_ = v___y_1392_;
v___y_1337_ = v___y_1393_;
v___y_1338_ = v___y_1396_;
v___y_1339_ = v___y_1397_;
v___y_1340_ = v___y_1398_;
v___y_1341_ = v___y_1399_;
goto v___jp_1332_;
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1403_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_1404_ = l_Lean_MessageData_ofExpr(v___y_1395_);
if (v_isShared_1150_ == 0)
{
lean_ctor_set_tag(v___x_1149_, 7);
lean_ctor_set(v___x_1149_, 1, v___x_1404_);
lean_ctor_set(v___x_1149_, 0, v___x_1403_);
v___x_1406_ = v___x_1149_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1423_; 
v_reuseFailAlloc_1423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1423_, 0, v___x_1403_);
lean_ctor_set(v_reuseFailAlloc_1423_, 1, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1423_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1412_; 
v___x_1407_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__19, &l_Lean_Meta_substCore___lam__3___closed__19_once, _init_l_Lean_Meta_substCore___lam__3___closed__19);
v___x_1408_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1406_);
lean_ctor_set(v___x_1408_, 1, v___x_1407_);
v___x_1409_ = l_Lean_indentExpr(v___y_1394_);
v___x_1410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1410_, 0, v___x_1408_);
lean_ctor_set(v___x_1410_, 1, v___x_1409_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 0, v___x_1410_);
v___x_1412_ = v___x_1145_;
goto v_reusejp_1411_;
}
else
{
lean_object* v_reuseFailAlloc_1422_; 
v_reuseFailAlloc_1422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1422_, 0, v___x_1410_);
v___x_1412_ = v_reuseFailAlloc_1422_;
goto v_reusejp_1411_;
}
v_reusejp_1411_:
{
lean_object* v___x_1413_; 
lean_inc(v_mvarId_1068_);
v___x_1413_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1120_, v_mvarId_1068_, v___x_1412_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_dec_ref(v___x_1413_);
v___y_1333_ = v___y_1389_;
v___y_1334_ = v___y_1390_;
v___y_1335_ = v___y_1391_;
v___y_1336_ = v___y_1392_;
v___y_1337_ = v___y_1393_;
v___y_1338_ = v___y_1396_;
v___y_1339_ = v___y_1397_;
v___y_1340_ = v___y_1398_;
v___y_1341_ = v___y_1399_;
goto v___jp_1332_;
}
else
{
lean_object* v_a_1414_; lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1421_; 
lean_dec(v___y_1399_);
lean_dec_ref(v___y_1398_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1393_);
lean_dec(v___y_1392_);
lean_dec(v___y_1390_);
lean_dec(v___y_1389_);
lean_del_object(v___x_1154_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
lean_dec(v_mvarId_1068_);
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1421_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1421_ == 0)
{
v___x_1416_ = v___x_1413_;
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
else
{
lean_inc(v_a_1414_);
lean_dec(v___x_1413_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1421_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v___x_1419_; 
if (v_isShared_1417_ == 0)
{
v___x_1419_ = v___x_1416_;
goto v_reusejp_1418_;
}
else
{
lean_object* v_reuseFailAlloc_1420_; 
v_reuseFailAlloc_1420_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1420_, 0, v_a_1414_);
v___x_1419_ = v_reuseFailAlloc_1420_;
goto v_reusejp_1418_;
}
v_reusejp_1418_:
{
return v___x_1419_;
}
}
}
}
}
}
}
v___jp_1424_:
{
lean_object* v___x_1427_; 
v___x_1427_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1426_, v___y_1076_);
if (lean_obj_tag(v___y_1425_) == 1)
{
lean_object* v_a_1428_; lean_object* v_fvarId_1429_; lean_object* v___x_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; lean_object* v_a_1433_; uint8_t v___x_1434_; 
lean_dec_ref(v___x_1124_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
v_fvarId_1429_ = lean_ctor_get(v___y_1425_, 0);
lean_inc(v_fvarId_1429_);
v___x_1430_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___f_1431_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__23));
v___x_1432_ = l_Lean_Meta_substCore___lam__0(v___x_1430_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
v_a_1433_ = lean_ctor_get(v___x_1432_, 0);
lean_inc(v_a_1433_);
lean_dec_ref(v___x_1432_);
v___x_1434_ = lean_unbox(v_a_1433_);
lean_dec(v_a_1433_);
if (v___x_1434_ == 0)
{
lean_inc(v_fvarId_1429_);
v___y_1389_ = v_fvarId_1429_;
v___y_1390_ = v___x_1430_;
v___y_1391_ = v___f_1431_;
v___y_1392_ = v_fvarId_1429_;
v___y_1393_ = v___x_1430_;
v___y_1394_ = v_a_1428_;
v___y_1395_ = v___y_1425_;
v___y_1396_ = v___y_1075_;
v___y_1397_ = v___y_1076_;
v___y_1398_ = v___y_1077_;
v___y_1399_ = v___y_1078_;
goto v___jp_1388_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1435_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__25, &l_Lean_Meta_substCore___lam__3___closed__25_once, _init_l_Lean_Meta_substCore___lam__3___closed__25);
lean_inc_ref(v___y_1425_);
v___x_1436_ = l_Lean_MessageData_ofExpr(v___y_1425_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__27, &l_Lean_Meta_substCore___lam__3___closed__27_once, _init_l_Lean_Meta_substCore___lam__3___closed__27);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
lean_inc(v_fvarId_1429_);
v___x_1440_ = l_Lean_MessageData_ofName(v_fvarId_1429_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__29, &l_Lean_Meta_substCore___lam__3___closed__29_once, _init_l_Lean_Meta_substCore___lam__3___closed__29);
v___x_1443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1441_);
lean_ctor_set(v___x_1443_, 1, v___x_1442_);
lean_inc(v_a_1428_);
v___x_1444_ = l_Lean_MessageData_ofExpr(v_a_1428_);
v___x_1445_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1445_, 0, v___x_1443_);
lean_ctor_set(v___x_1445_, 1, v___x_1444_);
v___x_1446_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_1430_, v___x_1445_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_dec_ref(v___x_1446_);
lean_inc(v_fvarId_1429_);
v___y_1389_ = v_fvarId_1429_;
v___y_1390_ = v___x_1430_;
v___y_1391_ = v___f_1431_;
v___y_1392_ = v_fvarId_1429_;
v___y_1393_ = v___x_1430_;
v___y_1394_ = v_a_1428_;
v___y_1395_ = v___y_1425_;
v___y_1396_ = v___y_1075_;
v___y_1397_ = v___y_1076_;
v___y_1398_ = v___y_1077_;
v___y_1399_ = v___y_1078_;
goto v___jp_1388_;
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_fvarId_1429_);
lean_dec_ref(v___y_1425_);
lean_dec(v_a_1428_);
lean_del_object(v___x_1154_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1145_);
lean_dec(v_a_1119_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
lean_dec(v_mvarId_1068_);
v_a_1447_ = lean_ctor_get(v___x_1446_, 0);
v_isSharedCheck_1454_ = !lean_is_exclusive(v___x_1446_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1449_ = v___x_1446_;
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
else
{
lean_inc(v_a_1447_);
lean_dec(v___x_1446_);
v___x_1449_ = lean_box(0);
v_isShared_1450_ = v_isSharedCheck_1454_;
goto v_resetjp_1448_;
}
v_resetjp_1448_:
{
lean_object* v___x_1452_; 
if (v_isShared_1450_ == 0)
{
v___x_1452_ = v___x_1449_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v_a_1447_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
return v___x_1452_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1427_);
lean_del_object(v___x_1154_);
lean_del_object(v___x_1149_);
lean_del_object(v___x_1145_);
lean_dec(v_a_1119_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
if (v_symm_1073_ == 0)
{
lean_object* v___x_1455_; 
v___x_1455_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__30));
v___y_1126_ = v___y_1425_;
v___y_1127_ = v___x_1455_;
goto v___jp_1125_;
}
else
{
lean_object* v___x_1456_; 
v___x_1456_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__31));
v___y_1126_ = v___y_1425_;
v___y_1127_ = v___x_1456_;
goto v___jp_1125_;
}
}
}
v___jp_1457_:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1458_, v___y_1076_);
if (v_symm_1073_ == 0)
{
lean_object* v_a_1460_; 
lean_dec(v_fst_1151_);
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1459_);
v___y_1425_ = v_a_1460_;
v___y_1426_ = v_snd_1152_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1461_; 
lean_dec(v_snd_1152_);
v_a_1461_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1461_);
lean_dec_ref(v___x_1459_);
v___y_1425_ = v_a_1461_;
v___y_1426_ = v_fst_1151_;
goto v___jp_1424_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1473_; 
lean_dec_ref(v___x_1124_);
lean_dec(v_a_1119_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
lean_dec(v_mvarId_1068_);
v_a_1466_ = lean_ctor_get(v___x_1139_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1139_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1139_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1139_);
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
v___jp_1125_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; 
v___x_1128_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__3, &l_Lean_Meta_substCore___lam__3___closed__3_once, _init_l_Lean_Meta_substCore___lam__3___closed__3);
lean_inc_ref(v___y_1127_);
v___x_1129_ = l_Lean_stringToMessageData(v___y_1127_);
v___x_1130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1128_);
lean_ctor_set(v___x_1130_, 1, v___x_1129_);
v___x_1131_ = l_Lean_indentExpr(v___x_1124_);
v___x_1132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1132_, 0, v___x_1130_);
lean_ctor_set(v___x_1132_, 1, v___x_1131_);
v___x_1133_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__5, &l_Lean_Meta_substCore___lam__3___closed__5_once, _init_l_Lean_Meta_substCore___lam__3___closed__5);
v___x_1134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
v___x_1135_ = l_Lean_indentExpr(v___y_1126_);
v___x_1136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1136_, 0, v___x_1134_);
lean_ctor_set(v___x_1136_, 1, v___x_1135_);
v___x_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
v___x_1138_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1120_, v_mvarId_1068_, v___x_1137_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
return v___x_1138_;
}
}
else
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec(v_a_1119_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
lean_dec(v_mvarId_1068_);
v_a_1474_ = lean_ctor_get(v___x_1122_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1122_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1122_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1122_);
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
lean_dec(v_a_1119_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
lean_dec(v_mvarId_1068_);
v_a_1482_ = lean_ctor_get(v___x_1121_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1121_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1121_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1121_);
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
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v_fvarSubst_1072_);
lean_dec(v_hFVarId_1069_);
lean_dec(v_mvarId_1068_);
v_a_1490_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1118_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1118_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
v___jp_1080_:
{
if (v_clearH_1071_ == 0)
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_dec(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
v___x_1088_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1088_, 0, v_fvarSubst_1072_);
lean_ctor_set(v___x_1088_, 1, v___y_1081_);
v___x_1089_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1089_, 0, v___x_1088_);
return v___x_1089_;
}
else
{
lean_object* v___x_1090_; 
v___x_1090_ = l_Lean_MVarId_clear(v___y_1081_, v___y_1086_, v___y_1084_, v___y_1087_, v___y_1083_, v___y_1085_);
if (lean_obj_tag(v___x_1090_) == 0)
{
lean_object* v_a_1091_; lean_object* v___x_1092_; 
v_a_1091_ = lean_ctor_get(v___x_1090_, 0);
lean_inc(v_a_1091_);
lean_dec_ref(v___x_1090_);
v___x_1092_ = l_Lean_MVarId_clear(v_a_1091_, v___y_1082_, v___y_1084_, v___y_1087_, v___y_1083_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1087_);
lean_dec_ref(v___y_1084_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v_a_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1101_; 
v_a_1093_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1095_ = v___x_1092_;
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_a_1093_);
lean_dec(v___x_1092_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v_fvarSubst_1072_);
lean_ctor_set(v___x_1097_, 1, v_a_1093_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 0, v___x_1097_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec(v_fvarSubst_1072_);
v_a_1102_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1092_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1092_);
v___x_1104_ = lean_box(0);
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
v_resetjp_1103_:
{
lean_object* v___x_1107_; 
if (v_isShared_1105_ == 0)
{
v___x_1107_ = v___x_1104_;
goto v_reusejp_1106_;
}
else
{
lean_object* v_reuseFailAlloc_1108_; 
v_reuseFailAlloc_1108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1108_, 0, v_a_1102_);
v___x_1107_ = v_reuseFailAlloc_1108_;
goto v_reusejp_1106_;
}
v_reusejp_1106_:
{
return v___x_1107_;
}
}
}
}
else
{
lean_object* v_a_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v___y_1087_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec_ref(v___y_1083_);
lean_dec(v___y_1082_);
lean_dec(v_fvarSubst_1072_);
v_a_1110_ = lean_ctor_get(v___x_1090_, 0);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1090_);
if (v_isSharedCheck_1117_ == 0)
{
v___x_1112_ = v___x_1090_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_a_1110_);
lean_dec(v___x_1090_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1110_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3___boxed(lean_object* v_mvarId_1498_, lean_object* v_hFVarId_1499_, lean_object* v___x_1500_, lean_object* v_clearH_1501_, lean_object* v_fvarSubst_1502_, lean_object* v_symm_1503_, lean_object* v_tryToSkip_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_){
_start:
{
uint8_t v_clearH_boxed_1510_; uint8_t v_symm_boxed_1511_; uint8_t v_tryToSkip_boxed_1512_; lean_object* v_res_1513_; 
v_clearH_boxed_1510_ = lean_unbox(v_clearH_1501_);
v_symm_boxed_1511_ = lean_unbox(v_symm_1503_);
v_tryToSkip_boxed_1512_ = lean_unbox(v_tryToSkip_1504_);
v_res_1513_ = l_Lean_Meta_substCore___lam__3(v_mvarId_1498_, v_hFVarId_1499_, v___x_1500_, v_clearH_boxed_1510_, v_fvarSubst_1502_, v_symm_boxed_1511_, v_tryToSkip_boxed_1512_, v___y_1505_, v___y_1506_, v___y_1507_, v___y_1508_);
lean_dec(v___x_1500_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object* v_mvarId_1514_, lean_object* v_hFVarId_1515_, uint8_t v_symm_1516_, lean_object* v_fvarSubst_1517_, uint8_t v_clearH_1518_, uint8_t v_tryToSkip_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___f_1529_; lean_object* v___x_1530_; 
v___x_1525_ = lean_box(0);
v___x_1526_ = lean_box(v_clearH_1518_);
v___x_1527_ = lean_box(v_symm_1516_);
v___x_1528_ = lean_box(v_tryToSkip_1519_);
lean_inc(v_mvarId_1514_);
v___f_1529_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__3___boxed), 12, 7);
lean_closure_set(v___f_1529_, 0, v_mvarId_1514_);
lean_closure_set(v___f_1529_, 1, v_hFVarId_1515_);
lean_closure_set(v___f_1529_, 2, v___x_1525_);
lean_closure_set(v___f_1529_, 3, v___x_1526_);
lean_closure_set(v___f_1529_, 4, v_fvarSubst_1517_);
lean_closure_set(v___f_1529_, 5, v___x_1527_);
lean_closure_set(v___f_1529_, 6, v___x_1528_);
v___x_1530_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1514_, v___f_1529_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1530_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* v_mvarId_1531_, lean_object* v_hFVarId_1532_, lean_object* v_symm_1533_, lean_object* v_fvarSubst_1534_, lean_object* v_clearH_1535_, lean_object* v_tryToSkip_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_){
_start:
{
uint8_t v_symm_boxed_1542_; uint8_t v_clearH_boxed_1543_; uint8_t v_tryToSkip_boxed_1544_; lean_object* v_res_1545_; 
v_symm_boxed_1542_ = lean_unbox(v_symm_1533_);
v_clearH_boxed_1543_ = lean_unbox(v_clearH_1535_);
v_tryToSkip_boxed_1544_ = lean_unbox(v_tryToSkip_1536_);
v_res_1545_ = l_Lean_Meta_substCore(v_mvarId_1531_, v_hFVarId_1532_, v_symm_boxed_1542_, v_fvarSubst_1534_, v_clearH_boxed_1543_, v_tryToSkip_boxed_1544_, v_a_1537_, v_a_1538_, v_a_1539_, v_a_1540_);
lean_dec(v_a_1540_);
lean_dec_ref(v_a_1539_);
lean_dec(v_a_1538_);
lean_dec_ref(v_a_1537_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(lean_object* v_fst_1546_, lean_object* v_fst_1547_, lean_object* v_n_1548_, lean_object* v_i_1549_, lean_object* v_a_1550_, lean_object* v_a_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
lean_object* v___x_1557_; 
v___x_1557_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_1546_, v_fst_1547_, v_n_1548_, v_i_1549_, v_a_1551_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___boxed(lean_object* v_fst_1558_, lean_object* v_fst_1559_, lean_object* v_n_1560_, lean_object* v_i_1561_, lean_object* v_a_1562_, lean_object* v_a_1563_, lean_object* v___y_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_){
_start:
{
lean_object* v_res_1569_; 
v_res_1569_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(v_fst_1558_, v_fst_1559_, v_n_1560_, v_i_1561_, v_a_1562_, v_a_1563_, v___y_1564_, v___y_1565_, v___y_1566_, v___y_1567_);
lean_dec(v___y_1567_);
lean_dec_ref(v___y_1566_);
lean_dec(v___y_1565_);
lean_dec_ref(v___y_1564_);
lean_dec(v_n_1560_);
lean_dec_ref(v_fst_1559_);
lean_dec_ref(v_fst_1558_);
return v_res_1569_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(lean_object* v_mvarId_1570_, lean_object* v_val_1571_, lean_object* v___y_1572_, lean_object* v___y_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_){
_start:
{
lean_object* v___x_1577_; 
v___x_1577_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_mvarId_1570_, v_val_1571_, v___y_1573_);
return v___x_1577_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___boxed(lean_object* v_mvarId_1578_, lean_object* v_val_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_, lean_object* v___y_1584_){
_start:
{
lean_object* v_res_1585_; 
v_res_1585_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(v_mvarId_1578_, v_val_1579_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
lean_dec(v___y_1583_);
lean_dec_ref(v___y_1582_);
lean_dec(v___y_1581_);
lean_dec_ref(v___y_1580_);
return v_res_1585_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(lean_object* v_00_u03b1_1586_, lean_object* v_name_1587_, uint8_t v_bi_1588_, lean_object* v_type_1589_, lean_object* v_k_1590_, uint8_t v_kind_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_, lean_object* v___y_1594_, lean_object* v___y_1595_){
_start:
{
lean_object* v___x_1597_; 
v___x_1597_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_1587_, v_bi_1588_, v_type_1589_, v_k_1590_, v_kind_1591_, v___y_1592_, v___y_1593_, v___y_1594_, v___y_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1598_, lean_object* v_name_1599_, lean_object* v_bi_1600_, lean_object* v_type_1601_, lean_object* v_k_1602_, lean_object* v_kind_1603_, lean_object* v___y_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_){
_start:
{
uint8_t v_bi_boxed_1609_; uint8_t v_kind_boxed_1610_; lean_object* v_res_1611_; 
v_bi_boxed_1609_ = lean_unbox(v_bi_1600_);
v_kind_boxed_1610_ = lean_unbox(v_kind_1603_);
v_res_1611_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(v_00_u03b1_1598_, v_name_1599_, v_bi_boxed_1609_, v_type_1601_, v_k_1602_, v_kind_boxed_1610_, v___y_1604_, v___y_1605_, v___y_1606_, v___y_1607_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec(v___y_1605_);
lean_dec_ref(v___y_1604_);
return v_res_1611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(lean_object* v_00_u03b1_1612_, lean_object* v_name_1613_, lean_object* v_type_1614_, lean_object* v_k_1615_, lean_object* v___y_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v_name_1613_, v_type_1614_, v_k_1615_, v___y_1616_, v___y_1617_, v___y_1618_, v___y_1619_);
return v___x_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___boxed(lean_object* v_00_u03b1_1622_, lean_object* v_name_1623_, lean_object* v_type_1624_, lean_object* v_k_1625_, lean_object* v___y_1626_, lean_object* v___y_1627_, lean_object* v___y_1628_, lean_object* v___y_1629_, lean_object* v___y_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(v_00_u03b1_1622_, v_name_1623_, v_type_1624_, v_k_1625_, v___y_1626_, v___y_1627_, v___y_1628_, v___y_1629_);
lean_dec(v___y_1629_);
lean_dec_ref(v___y_1628_);
lean_dec(v___y_1627_);
lean_dec_ref(v___y_1626_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6(lean_object* v_00_u03b2_1632_, lean_object* v_x_1633_, lean_object* v_x_1634_, lean_object* v_x_1635_){
_start:
{
lean_object* v___x_1636_; 
v___x_1636_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_x_1633_, v_x_1634_, v_x_1635_);
return v___x_1636_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1637_, lean_object* v_x_1638_, size_t v_x_1639_, size_t v_x_1640_, lean_object* v_x_1641_, lean_object* v_x_1642_){
_start:
{
lean_object* v___x_1643_; 
v___x_1643_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_1638_, v_x_1639_, v_x_1640_, v_x_1641_, v_x_1642_);
return v___x_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1644_, lean_object* v_x_1645_, lean_object* v_x_1646_, lean_object* v_x_1647_, lean_object* v_x_1648_, lean_object* v_x_1649_){
_start:
{
size_t v_x_35616__boxed_1650_; size_t v_x_35617__boxed_1651_; lean_object* v_res_1652_; 
v_x_35616__boxed_1650_ = lean_unbox_usize(v_x_1646_);
lean_dec(v_x_1646_);
v_x_35617__boxed_1651_ = lean_unbox_usize(v_x_1647_);
lean_dec(v_x_1647_);
v_res_1652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(v_00_u03b2_1644_, v_x_1645_, v_x_35616__boxed_1650_, v_x_35617__boxed_1651_, v_x_1648_, v_x_1649_);
return v_res_1652_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13(lean_object* v_00_u03b2_1653_, lean_object* v_n_1654_, lean_object* v_k_1655_, lean_object* v_v_1656_){
_start:
{
lean_object* v___x_1657_; 
v___x_1657_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v_n_1654_, v_k_1655_, v_v_1656_);
return v___x_1657_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1658_, size_t v_depth_1659_, lean_object* v_keys_1660_, lean_object* v_vals_1661_, lean_object* v_heq_1662_, lean_object* v_i_1663_, lean_object* v_entries_1664_){
_start:
{
lean_object* v___x_1665_; 
v___x_1665_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_1659_, v_keys_1660_, v_vals_1661_, v_i_1663_, v_entries_1664_);
return v___x_1665_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1666_, lean_object* v_depth_1667_, lean_object* v_keys_1668_, lean_object* v_vals_1669_, lean_object* v_heq_1670_, lean_object* v_i_1671_, lean_object* v_entries_1672_){
_start:
{
size_t v_depth_boxed_1673_; lean_object* v_res_1674_; 
v_depth_boxed_1673_ = lean_unbox_usize(v_depth_1667_);
lean_dec(v_depth_1667_);
v_res_1674_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(v_00_u03b2_1666_, v_depth_boxed_1673_, v_keys_1668_, v_vals_1669_, v_heq_1670_, v_i_1671_, v_entries_1672_);
lean_dec_ref(v_vals_1669_);
lean_dec_ref(v_keys_1668_);
return v_res_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_1675_, lean_object* v_x_1676_, lean_object* v_x_1677_, lean_object* v_x_1678_, lean_object* v_x_1679_){
_start:
{
lean_object* v___x_1680_; 
v___x_1680_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(v_x_1676_, v_x_1677_, v_x_1678_, v_x_1679_);
return v___x_1680_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* v_fvarId_1684_, lean_object* v_mvarId_1685_, uint8_t v_tryToClear_1686_, lean_object* v___y_1687_, lean_object* v___y_1688_, lean_object* v___y_1689_, lean_object* v___y_1690_){
_start:
{
lean_object* v___x_1692_; 
lean_inc(v_fvarId_1684_);
v___x_1692_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1684_, v___y_1687_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1692_) == 0)
{
lean_object* v_a_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v_a_1693_ = lean_ctor_get(v___x_1692_, 0);
lean_inc(v_a_1693_);
lean_dec_ref(v___x_1692_);
v___x_1694_ = l_Lean_LocalDecl_type(v_a_1693_);
lean_inc(v___y_1690_);
lean_inc_ref(v___y_1689_);
lean_inc(v___y_1688_);
lean_inc_ref(v___y_1687_);
v___x_1695_ = lean_whnf(v___x_1694_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1695_) == 0)
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1780_; 
v_a_1696_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1698_ = v___x_1695_;
v_isShared_1699_ = v_isSharedCheck_1780_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1695_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1780_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1700_; lean_object* v___x_1701_; uint8_t v___x_1702_; 
v___x_1700_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_1701_ = lean_unsigned_to_nat(4u);
v___x_1702_ = l_Lean_Expr_isAppOfArity(v_a_1696_, v___x_1700_, v___x_1701_);
if (v___x_1702_ == 0)
{
lean_object* v___x_1703_; lean_object* v___x_1705_; 
lean_dec(v_a_1696_);
lean_dec(v_a_1693_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
v___x_1703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1703_, 0, v_fvarId_1684_);
lean_ctor_set(v___x_1703_, 1, v_mvarId_1685_);
if (v_isShared_1699_ == 0)
{
lean_ctor_set(v___x_1698_, 0, v___x_1703_);
v___x_1705_ = v___x_1698_;
goto v_reusejp_1704_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1703_);
v___x_1705_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1704_;
}
v_reusejp_1704_:
{
return v___x_1705_;
}
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; lean_object* v___x_1712_; 
lean_del_object(v___x_1698_);
v___x_1707_ = l_Lean_Expr_appFn_x21(v_a_1696_);
v___x_1708_ = l_Lean_Expr_appFn_x21(v___x_1707_);
v___x_1709_ = l_Lean_Expr_appFn_x21(v___x_1708_);
v___x_1710_ = l_Lean_Expr_appArg_x21(v___x_1709_);
lean_dec_ref(v___x_1709_);
v___x_1711_ = l_Lean_Expr_appArg_x21(v___x_1707_);
lean_dec_ref(v___x_1707_);
v___x_1712_ = l_Lean_Meta_isExprDefEq(v___x_1710_, v___x_1711_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v___x_1715_; uint8_t v_isShared_1716_; uint8_t v_isSharedCheck_1771_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1715_ = v___x_1712_;
v_isShared_1716_ = v_isSharedCheck_1771_;
goto v_resetjp_1714_;
}
else
{
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1715_ = lean_box(0);
v_isShared_1716_ = v_isSharedCheck_1771_;
goto v_resetjp_1714_;
}
v_resetjp_1714_:
{
uint8_t v___x_1717_; 
v___x_1717_ = lean_unbox(v_a_1713_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; lean_object* v___x_1720_; 
lean_dec(v_a_1713_);
lean_dec_ref(v___x_1708_);
lean_dec(v_a_1696_);
lean_dec(v_a_1693_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_fvarId_1684_);
lean_ctor_set(v___x_1718_, 1, v_mvarId_1685_);
if (v_isShared_1716_ == 0)
{
lean_ctor_set(v___x_1715_, 0, v___x_1718_);
v___x_1720_ = v___x_1715_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v___x_1718_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
else
{
lean_object* v___x_1722_; lean_object* v___x_1723_; 
lean_del_object(v___x_1715_);
lean_inc(v_fvarId_1684_);
v___x_1722_ = l_Lean_mkFVar(v_fvarId_1684_);
v___x_1723_ = l_Lean_Meta_mkEqOfHEq(v___x_1722_, v___x_1702_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref(v___x_1723_);
v___x_1725_ = l_Lean_Expr_appArg_x21(v___x_1708_);
lean_dec_ref(v___x_1708_);
v___x_1726_ = l_Lean_Expr_appArg_x21(v_a_1696_);
lean_dec(v_a_1696_);
v___x_1727_ = l_Lean_Meta_mkEq(v___x_1725_, v___x_1726_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1727_) == 0)
{
lean_object* v_a_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; 
v_a_1728_ = lean_ctor_get(v___x_1727_, 0);
lean_inc(v_a_1728_);
lean_dec_ref(v___x_1727_);
v___x_1729_ = l_Lean_LocalDecl_userName(v_a_1693_);
lean_dec(v_a_1693_);
v___x_1730_ = l_Lean_MVarId_assert(v_mvarId_1685_, v___x_1729_, v_a_1728_, v_a_1724_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1730_) == 0)
{
if (v_tryToClear_1686_ == 0)
{
lean_object* v_a_1731_; uint8_t v___x_1732_; lean_object* v___x_1733_; 
lean_dec(v_fvarId_1684_);
v_a_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1731_);
lean_dec_ref(v___x_1730_);
v___x_1732_ = lean_unbox(v_a_1713_);
lean_dec(v_a_1713_);
v___x_1733_ = l_Lean_Meta_intro1Core(v_a_1731_, v___x_1732_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
return v___x_1733_;
}
else
{
lean_object* v_a_1734_; lean_object* v___x_1735_; 
v_a_1734_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_a_1734_);
lean_dec_ref(v___x_1730_);
v___x_1735_ = l_Lean_MVarId_tryClear(v_a_1734_, v_fvarId_1684_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref(v___x_1735_);
v___x_1737_ = lean_unbox(v_a_1713_);
lean_dec(v_a_1713_);
v___x_1738_ = l_Lean_Meta_intro1Core(v_a_1736_, v___x_1737_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
return v___x_1738_;
}
else
{
lean_object* v_a_1739_; lean_object* v___x_1741_; uint8_t v_isShared_1742_; uint8_t v_isSharedCheck_1746_; 
lean_dec(v_a_1713_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
v_a_1739_ = lean_ctor_get(v___x_1735_, 0);
v_isSharedCheck_1746_ = !lean_is_exclusive(v___x_1735_);
if (v_isSharedCheck_1746_ == 0)
{
v___x_1741_ = v___x_1735_;
v_isShared_1742_ = v_isSharedCheck_1746_;
goto v_resetjp_1740_;
}
else
{
lean_inc(v_a_1739_);
lean_dec(v___x_1735_);
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
}
else
{
lean_object* v_a_1747_; lean_object* v___x_1749_; uint8_t v_isShared_1750_; uint8_t v_isSharedCheck_1754_; 
lean_dec(v_a_1713_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v_fvarId_1684_);
v_a_1747_ = lean_ctor_get(v___x_1730_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v___x_1730_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1749_ = v___x_1730_;
v_isShared_1750_ = v_isSharedCheck_1754_;
goto v_resetjp_1748_;
}
else
{
lean_inc(v_a_1747_);
lean_dec(v___x_1730_);
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
lean_dec(v_a_1724_);
lean_dec(v_a_1713_);
lean_dec(v_a_1693_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v_mvarId_1685_);
lean_dec(v_fvarId_1684_);
v_a_1755_ = lean_ctor_get(v___x_1727_, 0);
v_isSharedCheck_1762_ = !lean_is_exclusive(v___x_1727_);
if (v_isSharedCheck_1762_ == 0)
{
v___x_1757_ = v___x_1727_;
v_isShared_1758_ = v_isSharedCheck_1762_;
goto v_resetjp_1756_;
}
else
{
lean_inc(v_a_1755_);
lean_dec(v___x_1727_);
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
else
{
lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1770_; 
lean_dec(v_a_1713_);
lean_dec_ref(v___x_1708_);
lean_dec(v_a_1696_);
lean_dec(v_a_1693_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v_mvarId_1685_);
lean_dec(v_fvarId_1684_);
v_a_1763_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1765_ = v___x_1723_;
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_dec(v___x_1723_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1770_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1768_; 
if (v_isShared_1766_ == 0)
{
v___x_1768_ = v___x_1765_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v_a_1763_);
v___x_1768_ = v_reuseFailAlloc_1769_;
goto v_reusejp_1767_;
}
v_reusejp_1767_:
{
return v___x_1768_;
}
}
}
}
}
}
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec_ref(v___x_1708_);
lean_dec(v_a_1696_);
lean_dec(v_a_1693_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v_mvarId_1685_);
lean_dec(v_fvarId_1684_);
v_a_1772_ = lean_ctor_get(v___x_1712_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1712_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1712_);
v___x_1774_ = lean_box(0);
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
v_resetjp_1773_:
{
lean_object* v___x_1777_; 
if (v_isShared_1775_ == 0)
{
v___x_1777_ = v___x_1774_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v_a_1772_);
v___x_1777_ = v_reuseFailAlloc_1778_;
goto v_reusejp_1776_;
}
v_reusejp_1776_:
{
return v___x_1777_;
}
}
}
}
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
lean_dec(v_a_1693_);
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v_mvarId_1685_);
lean_dec(v_fvarId_1684_);
v_a_1781_ = lean_ctor_get(v___x_1695_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1695_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1695_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1695_);
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
else
{
lean_object* v_a_1789_; lean_object* v___x_1791_; uint8_t v_isShared_1792_; uint8_t v_isSharedCheck_1796_; 
lean_dec(v___y_1690_);
lean_dec_ref(v___y_1689_);
lean_dec(v___y_1688_);
lean_dec_ref(v___y_1687_);
lean_dec(v_mvarId_1685_);
lean_dec(v_fvarId_1684_);
v_a_1789_ = lean_ctor_get(v___x_1692_, 0);
v_isSharedCheck_1796_ = !lean_is_exclusive(v___x_1692_);
if (v_isSharedCheck_1796_ == 0)
{
v___x_1791_ = v___x_1692_;
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
else
{
lean_inc(v_a_1789_);
lean_dec(v___x_1692_);
v___x_1791_ = lean_box(0);
v_isShared_1792_ = v_isSharedCheck_1796_;
goto v_resetjp_1790_;
}
v_resetjp_1790_:
{
lean_object* v___x_1794_; 
if (v_isShared_1792_ == 0)
{
v___x_1794_ = v___x_1791_;
goto v_reusejp_1793_;
}
else
{
lean_object* v_reuseFailAlloc_1795_; 
v_reuseFailAlloc_1795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1795_, 0, v_a_1789_);
v___x_1794_ = v_reuseFailAlloc_1795_;
goto v_reusejp_1793_;
}
v_reusejp_1793_:
{
return v___x_1794_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object* v_fvarId_1797_, lean_object* v_mvarId_1798_, lean_object* v_tryToClear_1799_, lean_object* v___y_1800_, lean_object* v___y_1801_, lean_object* v___y_1802_, lean_object* v___y_1803_, lean_object* v___y_1804_){
_start:
{
uint8_t v_tryToClear_boxed_1805_; lean_object* v_res_1806_; 
v_tryToClear_boxed_1805_ = lean_unbox(v_tryToClear_1799_);
v_res_1806_ = l_Lean_Meta_heqToEq___lam__0(v_fvarId_1797_, v_mvarId_1798_, v_tryToClear_boxed_1805_, v___y_1800_, v___y_1801_, v___y_1802_, v___y_1803_);
return v_res_1806_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object* v_mvarId_1807_, lean_object* v_fvarId_1808_, uint8_t v_tryToClear_1809_, lean_object* v_a_1810_, lean_object* v_a_1811_, lean_object* v_a_1812_, lean_object* v_a_1813_){
_start:
{
lean_object* v___x_1815_; lean_object* v___f_1816_; lean_object* v___x_1817_; 
v___x_1815_ = lean_box(v_tryToClear_1809_);
lean_inc(v_mvarId_1807_);
v___f_1816_ = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1816_, 0, v_fvarId_1808_);
lean_closure_set(v___f_1816_, 1, v_mvarId_1807_);
lean_closure_set(v___f_1816_, 2, v___x_1815_);
v___x_1817_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1807_, v___f_1816_, v_a_1810_, v_a_1811_, v_a_1812_, v_a_1813_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* v_mvarId_1818_, lean_object* v_fvarId_1819_, lean_object* v_tryToClear_1820_, lean_object* v_a_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_){
_start:
{
uint8_t v_tryToClear_boxed_1826_; lean_object* v_res_1827_; 
v_tryToClear_boxed_1826_ = lean_unbox(v_tryToClear_1820_);
v_res_1827_ = l_Lean_Meta_heqToEq(v_mvarId_1818_, v_fvarId_1819_, v_tryToClear_boxed_1826_, v_a_1821_, v_a_1822_, v_a_1823_, v_a_1824_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec(v_a_1822_);
lean_dec_ref(v_a_1821_);
return v_res_1827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1831_, lean_object* v_as_1832_, size_t v_sz_1833_, size_t v_i_1834_, lean_object* v_b_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
lean_object* v_a_1842_; uint8_t v___x_1846_; 
v___x_1846_ = lean_usize_dec_lt(v_i_1834_, v_sz_1833_);
if (v___x_1846_ == 0)
{
lean_object* v___x_1847_; 
lean_dec(v_x_1831_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_b_1835_);
return v___x_1847_;
}
else
{
lean_object* v___x_1848_; lean_object* v_a_1850_; lean_object* v___x_1854_; lean_object* v_a_1855_; 
lean_dec_ref(v_b_1835_);
v___x_1848_ = lean_box(0);
v___x_1854_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1855_ = lean_array_uget(v_as_1832_, v_i_1834_);
if (lean_obj_tag(v_a_1855_) == 0)
{
v_a_1842_ = v___x_1854_;
goto v___jp_1841_;
}
else
{
lean_object* v_val_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1943_; 
v_val_1856_ = lean_ctor_get(v_a_1855_, 0);
v_isSharedCheck_1943_ = !lean_is_exclusive(v_a_1855_);
if (v_isSharedCheck_1943_ == 0)
{
v___x_1858_ = v_a_1855_;
v_isShared_1859_ = v_isSharedCheck_1943_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_val_1856_);
lean_dec(v_a_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1943_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
uint8_t v___x_1867_; 
v___x_1867_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1856_);
if (v___x_1867_ == 0)
{
lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1873_ = l_Lean_LocalDecl_type(v_val_1856_);
v___x_1874_ = l_Lean_Meta_matchEq_x3f(v___x_1873_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref(v___x_1874_);
if (lean_obj_tag(v_a_1875_) == 1)
{
lean_object* v_val_1876_; lean_object* v_snd_1877_; lean_object* v_fst_1878_; lean_object* v_snd_1879_; lean_object* v___x_1880_; 
v_val_1876_ = lean_ctor_get(v_a_1875_, 0);
lean_inc(v_val_1876_);
lean_dec_ref(v_a_1875_);
v_snd_1877_ = lean_ctor_get(v_val_1876_, 1);
lean_inc(v_snd_1877_);
lean_dec(v_val_1876_);
v_fst_1878_ = lean_ctor_get(v_snd_1877_, 0);
lean_inc(v_fst_1878_);
v_snd_1879_ = lean_ctor_get(v_snd_1877_, 1);
lean_inc(v_snd_1879_);
lean_dec(v_snd_1877_);
v___x_1880_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1878_, v___y_1837_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; lean_object* v___x_1882_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref(v___x_1880_);
v___x_1882_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1879_, v___y_1837_);
if (lean_obj_tag(v___x_1882_) == 0)
{
lean_object* v_a_1883_; lean_object* v___y_1885_; uint8_t v___y_1886_; lean_object* v___y_1899_; uint8_t v___y_1904_; uint8_t v___x_1916_; 
v_a_1883_ = lean_ctor_get(v___x_1882_, 0);
lean_inc(v_a_1883_);
lean_dec_ref(v___x_1882_);
v___x_1916_ = l_Lean_Expr_isFVar(v_a_1883_);
if (v___x_1916_ == 0)
{
v___y_1904_ = v___x_1916_;
goto v___jp_1903_;
}
else
{
lean_object* v___x_1917_; uint8_t v___x_1918_; 
v___x_1917_ = l_Lean_Expr_fvarId_x21(v_a_1883_);
v___x_1918_ = l_Lean_instBEqFVarId_beq(v___x_1917_, v_x_1831_);
lean_dec(v___x_1917_);
v___y_1904_ = v___x_1918_;
goto v___jp_1903_;
}
v___jp_1884_:
{
if (v___y_1886_ == 0)
{
lean_dec(v_a_1883_);
lean_dec(v_val_1856_);
v_a_1842_ = v___x_1854_;
goto v___jp_1841_;
}
else
{
lean_object* v___x_1887_; 
lean_inc(v_x_1831_);
v___x_1887_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1883_, v_x_1831_, v___y_1885_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; uint8_t v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref(v___x_1887_);
v___x_1889_ = lean_unbox(v_a_1888_);
lean_dec(v_a_1888_);
if (v___x_1889_ == 0)
{
lean_dec(v_x_1831_);
goto v___jp_1868_;
}
else
{
if (v___x_1867_ == 0)
{
lean_dec(v_val_1856_);
v_a_1842_ = v___x_1854_;
goto v___jp_1841_;
}
else
{
lean_dec(v_x_1831_);
goto v___jp_1868_;
}
}
}
else
{
lean_object* v_a_1890_; lean_object* v___x_1892_; uint8_t v_isShared_1893_; uint8_t v_isSharedCheck_1897_; 
lean_dec(v_val_1856_);
lean_dec(v_x_1831_);
v_a_1890_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1897_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1897_ == 0)
{
v___x_1892_ = v___x_1887_;
v_isShared_1893_ = v_isSharedCheck_1897_;
goto v_resetjp_1891_;
}
else
{
lean_inc(v_a_1890_);
lean_dec(v___x_1887_);
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
v___jp_1898_:
{
uint8_t v___x_1900_; 
v___x_1900_ = l_Lean_Expr_isFVar(v_a_1881_);
if (v___x_1900_ == 0)
{
lean_dec(v_a_1881_);
v___y_1885_ = v___y_1899_;
v___y_1886_ = v___x_1900_;
goto v___jp_1884_;
}
else
{
lean_object* v___x_1901_; uint8_t v___x_1902_; 
v___x_1901_ = l_Lean_Expr_fvarId_x21(v_a_1881_);
lean_dec(v_a_1881_);
v___x_1902_ = l_Lean_instBEqFVarId_beq(v___x_1901_, v_x_1831_);
lean_dec(v___x_1901_);
v___y_1885_ = v___y_1899_;
v___y_1886_ = v___x_1902_;
goto v___jp_1884_;
}
}
v___jp_1903_:
{
if (v___y_1904_ == 0)
{
lean_del_object(v___x_1858_);
v___y_1899_ = v___y_1837_;
goto v___jp_1898_;
}
else
{
lean_object* v___x_1905_; 
lean_inc(v_x_1831_);
lean_inc(v_a_1881_);
v___x_1905_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1881_, v_x_1831_, v___y_1837_);
if (lean_obj_tag(v___x_1905_) == 0)
{
lean_object* v_a_1906_; uint8_t v___x_1907_; 
v_a_1906_ = lean_ctor_get(v___x_1905_, 0);
lean_inc(v_a_1906_);
lean_dec_ref(v___x_1905_);
v___x_1907_ = lean_unbox(v_a_1906_);
lean_dec(v_a_1906_);
if (v___x_1907_ == 0)
{
lean_dec(v_a_1883_);
lean_dec(v_a_1881_);
lean_dec(v_x_1831_);
goto v___jp_1860_;
}
else
{
if (v___x_1867_ == 0)
{
lean_del_object(v___x_1858_);
v___y_1899_ = v___y_1837_;
goto v___jp_1898_;
}
else
{
lean_dec(v_a_1883_);
lean_dec(v_a_1881_);
lean_dec(v_x_1831_);
goto v___jp_1860_;
}
}
}
else
{
lean_object* v_a_1908_; lean_object* v___x_1910_; uint8_t v_isShared_1911_; uint8_t v_isSharedCheck_1915_; 
lean_dec(v_a_1883_);
lean_dec(v_a_1881_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
lean_dec(v_x_1831_);
v_a_1908_ = lean_ctor_get(v___x_1905_, 0);
v_isSharedCheck_1915_ = !lean_is_exclusive(v___x_1905_);
if (v_isSharedCheck_1915_ == 0)
{
v___x_1910_ = v___x_1905_;
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
else
{
lean_inc(v_a_1908_);
lean_dec(v___x_1905_);
v___x_1910_ = lean_box(0);
v_isShared_1911_ = v_isSharedCheck_1915_;
goto v_resetjp_1909_;
}
v_resetjp_1909_:
{
lean_object* v___x_1913_; 
if (v_isShared_1911_ == 0)
{
v___x_1913_ = v___x_1910_;
goto v_reusejp_1912_;
}
else
{
lean_object* v_reuseFailAlloc_1914_; 
v_reuseFailAlloc_1914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1914_, 0, v_a_1908_);
v___x_1913_ = v_reuseFailAlloc_1914_;
goto v_reusejp_1912_;
}
v_reusejp_1912_:
{
return v___x_1913_;
}
}
}
}
}
}
else
{
lean_object* v_a_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1926_; 
lean_dec(v_a_1881_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
lean_dec(v_x_1831_);
v_a_1919_ = lean_ctor_get(v___x_1882_, 0);
v_isSharedCheck_1926_ = !lean_is_exclusive(v___x_1882_);
if (v_isSharedCheck_1926_ == 0)
{
v___x_1921_ = v___x_1882_;
v_isShared_1922_ = v_isSharedCheck_1926_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_a_1919_);
lean_dec(v___x_1882_);
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
lean_dec(v_snd_1879_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
lean_dec(v_x_1831_);
v_a_1927_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1880_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1880_);
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
else
{
lean_dec(v_a_1875_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
v_a_1842_ = v___x_1854_;
goto v___jp_1841_;
}
}
else
{
lean_object* v_a_1935_; lean_object* v___x_1937_; uint8_t v_isShared_1938_; uint8_t v_isSharedCheck_1942_; 
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
lean_dec(v_x_1831_);
v_a_1935_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1942_ == 0)
{
v___x_1937_ = v___x_1874_;
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
else
{
lean_inc(v_a_1935_);
lean_dec(v___x_1874_);
v___x_1937_ = lean_box(0);
v_isShared_1938_ = v_isSharedCheck_1942_;
goto v_resetjp_1936_;
}
v_resetjp_1936_:
{
lean_object* v___x_1940_; 
if (v_isShared_1938_ == 0)
{
v___x_1940_ = v___x_1937_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v_a_1935_);
v___x_1940_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
return v___x_1940_;
}
}
}
}
else
{
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
v_a_1842_ = v___x_1854_;
goto v___jp_1841_;
}
v___jp_1860_:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; lean_object* v___x_1863_; lean_object* v___x_1865_; 
v___x_1861_ = l_Lean_LocalDecl_fvarId(v_val_1856_);
lean_dec(v_val_1856_);
v___x_1862_ = lean_box(v___x_1846_);
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1861_);
lean_ctor_set(v___x_1863_, 1, v___x_1862_);
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1863_);
v___x_1865_ = v___x_1858_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v___x_1863_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
v_a_1850_ = v___x_1865_;
goto v___jp_1849_;
}
}
v___jp_1868_:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1869_ = l_Lean_LocalDecl_fvarId(v_val_1856_);
lean_dec(v_val_1856_);
v___x_1870_ = lean_box(v___x_1867_);
v___x_1871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1871_, 0, v___x_1869_);
lean_ctor_set(v___x_1871_, 1, v___x_1870_);
v___x_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1872_, 0, v___x_1871_);
v_a_1850_ = v___x_1872_;
goto v___jp_1849_;
}
}
}
v___jp_1849_:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1851_, 0, v_a_1850_);
v___x_1852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v___x_1848_);
v___x_1853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1853_, 0, v___x_1852_);
return v___x_1853_;
}
}
v___jp_1841_:
{
size_t v___x_1843_; size_t v___x_1844_; 
v___x_1843_ = ((size_t)1ULL);
v___x_1844_ = lean_usize_add(v_i_1834_, v___x_1843_);
lean_inc_ref(v_a_1842_);
v_i_1834_ = v___x_1844_;
v_b_1835_ = v_a_1842_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1944_, lean_object* v_as_1945_, lean_object* v_sz_1946_, lean_object* v_i_1947_, lean_object* v_b_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_){
_start:
{
size_t v_sz_boxed_1954_; size_t v_i_boxed_1955_; lean_object* v_res_1956_; 
v_sz_boxed_1954_ = lean_unbox_usize(v_sz_1946_);
lean_dec(v_sz_1946_);
v_i_boxed_1955_ = lean_unbox_usize(v_i_1947_);
lean_dec(v_i_1947_);
v_res_1956_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1944_, v_as_1945_, v_sz_boxed_1954_, v_i_boxed_1955_, v_b_1948_, v___y_1949_, v___y_1950_, v___y_1951_, v___y_1952_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
lean_dec(v___y_1950_);
lean_dec_ref(v___y_1949_);
lean_dec_ref(v_as_1945_);
return v_res_1956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object* v_x_1957_, lean_object* v_as_1958_, size_t v_sz_1959_, size_t v_i_1960_, lean_object* v_b_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v_a_1968_; uint8_t v___x_1972_; 
v___x_1972_ = lean_usize_dec_lt(v_i_1960_, v_sz_1959_);
if (v___x_1972_ == 0)
{
lean_object* v___x_1973_; 
lean_dec(v_x_1957_);
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v_b_1961_);
return v___x_1973_;
}
else
{
lean_object* v___x_1974_; lean_object* v_a_1976_; lean_object* v___x_1980_; lean_object* v_a_1981_; 
lean_dec_ref(v_b_1961_);
v___x_1974_ = lean_box(0);
v___x_1980_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1981_ = lean_array_uget(v_as_1958_, v_i_1960_);
if (lean_obj_tag(v_a_1981_) == 0)
{
v_a_1968_ = v___x_1980_;
goto v___jp_1967_;
}
else
{
lean_object* v_val_1982_; lean_object* v___x_1984_; uint8_t v_isShared_1985_; uint8_t v_isSharedCheck_2069_; 
v_val_1982_ = lean_ctor_get(v_a_1981_, 0);
v_isSharedCheck_2069_ = !lean_is_exclusive(v_a_1981_);
if (v_isSharedCheck_2069_ == 0)
{
v___x_1984_ = v_a_1981_;
v_isShared_1985_ = v_isSharedCheck_2069_;
goto v_resetjp_1983_;
}
else
{
lean_inc(v_val_1982_);
lean_dec(v_a_1981_);
v___x_1984_ = lean_box(0);
v_isShared_1985_ = v_isSharedCheck_2069_;
goto v_resetjp_1983_;
}
v_resetjp_1983_:
{
uint8_t v___x_1993_; 
v___x_1993_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1982_);
if (v___x_1993_ == 0)
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = l_Lean_LocalDecl_type(v_val_1982_);
v___x_2000_ = l_Lean_Meta_matchEq_x3f(v___x_1999_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref(v___x_2000_);
if (lean_obj_tag(v_a_2001_) == 1)
{
lean_object* v_val_2002_; lean_object* v_snd_2003_; lean_object* v_fst_2004_; lean_object* v_snd_2005_; lean_object* v___x_2006_; 
v_val_2002_ = lean_ctor_get(v_a_2001_, 0);
lean_inc(v_val_2002_);
lean_dec_ref(v_a_2001_);
v_snd_2003_ = lean_ctor_get(v_val_2002_, 1);
lean_inc(v_snd_2003_);
lean_dec(v_val_2002_);
v_fst_2004_ = lean_ctor_get(v_snd_2003_, 0);
lean_inc(v_fst_2004_);
v_snd_2005_ = lean_ctor_get(v_snd_2003_, 1);
lean_inc(v_snd_2005_);
lean_dec(v_snd_2003_);
v___x_2006_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_2004_, v___y_1963_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2008_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref(v___x_2006_);
v___x_2008_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_2005_, v___y_1963_);
if (lean_obj_tag(v___x_2008_) == 0)
{
lean_object* v_a_2009_; lean_object* v___y_2011_; uint8_t v___y_2012_; lean_object* v___y_2025_; uint8_t v___y_2030_; uint8_t v___x_2042_; 
v_a_2009_ = lean_ctor_get(v___x_2008_, 0);
lean_inc(v_a_2009_);
lean_dec_ref(v___x_2008_);
v___x_2042_ = l_Lean_Expr_isFVar(v_a_2009_);
if (v___x_2042_ == 0)
{
v___y_2030_ = v___x_2042_;
goto v___jp_2029_;
}
else
{
lean_object* v___x_2043_; uint8_t v___x_2044_; 
v___x_2043_ = l_Lean_Expr_fvarId_x21(v_a_2009_);
v___x_2044_ = l_Lean_instBEqFVarId_beq(v___x_2043_, v_x_1957_);
lean_dec(v___x_2043_);
v___y_2030_ = v___x_2044_;
goto v___jp_2029_;
}
v___jp_2010_:
{
if (v___y_2012_ == 0)
{
lean_dec(v_a_2009_);
lean_dec(v_val_1982_);
v_a_1968_ = v___x_1980_;
goto v___jp_1967_;
}
else
{
lean_object* v___x_2013_; 
lean_inc(v_x_1957_);
v___x_2013_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2009_, v_x_1957_, v___y_2011_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; uint8_t v___x_2015_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref(v___x_2013_);
v___x_2015_ = lean_unbox(v_a_2014_);
lean_dec(v_a_2014_);
if (v___x_2015_ == 0)
{
lean_dec(v_x_1957_);
goto v___jp_1994_;
}
else
{
if (v___x_1993_ == 0)
{
lean_dec(v_val_1982_);
v_a_1968_ = v___x_1980_;
goto v___jp_1967_;
}
else
{
lean_dec(v_x_1957_);
goto v___jp_1994_;
}
}
}
else
{
lean_object* v_a_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2023_; 
lean_dec(v_val_1982_);
lean_dec(v_x_1957_);
v_a_2016_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2023_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2023_ == 0)
{
v___x_2018_ = v___x_2013_;
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_a_2016_);
lean_dec(v___x_2013_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2023_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v___x_2021_; 
if (v_isShared_2019_ == 0)
{
v___x_2021_ = v___x_2018_;
goto v_reusejp_2020_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_a_2016_);
v___x_2021_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2020_;
}
v_reusejp_2020_:
{
return v___x_2021_;
}
}
}
}
}
v___jp_2024_:
{
uint8_t v___x_2026_; 
v___x_2026_ = l_Lean_Expr_isFVar(v_a_2007_);
if (v___x_2026_ == 0)
{
lean_dec(v_a_2007_);
v___y_2011_ = v___y_2025_;
v___y_2012_ = v___x_2026_;
goto v___jp_2010_;
}
else
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = l_Lean_Expr_fvarId_x21(v_a_2007_);
lean_dec(v_a_2007_);
v___x_2028_ = l_Lean_instBEqFVarId_beq(v___x_2027_, v_x_1957_);
lean_dec(v___x_2027_);
v___y_2011_ = v___y_2025_;
v___y_2012_ = v___x_2028_;
goto v___jp_2010_;
}
}
v___jp_2029_:
{
if (v___y_2030_ == 0)
{
lean_del_object(v___x_1984_);
v___y_2025_ = v___y_1963_;
goto v___jp_2024_;
}
else
{
lean_object* v___x_2031_; 
lean_inc(v_x_1957_);
lean_inc(v_a_2007_);
v___x_2031_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2007_, v_x_1957_, v___y_1963_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; uint8_t v___x_2033_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref(v___x_2031_);
v___x_2033_ = lean_unbox(v_a_2032_);
lean_dec(v_a_2032_);
if (v___x_2033_ == 0)
{
lean_dec(v_a_2009_);
lean_dec(v_a_2007_);
lean_dec(v_x_1957_);
goto v___jp_1986_;
}
else
{
if (v___x_1993_ == 0)
{
lean_del_object(v___x_1984_);
v___y_2025_ = v___y_1963_;
goto v___jp_2024_;
}
else
{
lean_dec(v_a_2009_);
lean_dec(v_a_2007_);
lean_dec(v_x_1957_);
goto v___jp_1986_;
}
}
}
else
{
lean_object* v_a_2034_; lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2041_; 
lean_dec(v_a_2009_);
lean_dec(v_a_2007_);
lean_del_object(v___x_1984_);
lean_dec(v_val_1982_);
lean_dec(v_x_1957_);
v_a_2034_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2041_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2041_ == 0)
{
v___x_2036_ = v___x_2031_;
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
else
{
lean_inc(v_a_2034_);
lean_dec(v___x_2031_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2041_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2039_; 
if (v_isShared_2037_ == 0)
{
v___x_2039_ = v___x_2036_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_a_2034_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
return v___x_2039_;
}
}
}
}
}
}
else
{
lean_object* v_a_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2052_; 
lean_dec(v_a_2007_);
lean_del_object(v___x_1984_);
lean_dec(v_val_1982_);
lean_dec(v_x_1957_);
v_a_2045_ = lean_ctor_get(v___x_2008_, 0);
v_isSharedCheck_2052_ = !lean_is_exclusive(v___x_2008_);
if (v_isSharedCheck_2052_ == 0)
{
v___x_2047_ = v___x_2008_;
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_a_2045_);
lean_dec(v___x_2008_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2052_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v___x_2050_; 
if (v_isShared_2048_ == 0)
{
v___x_2050_ = v___x_2047_;
goto v_reusejp_2049_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
v___x_2050_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2049_;
}
v_reusejp_2049_:
{
return v___x_2050_;
}
}
}
}
else
{
lean_object* v_a_2053_; lean_object* v___x_2055_; uint8_t v_isShared_2056_; uint8_t v_isSharedCheck_2060_; 
lean_dec(v_snd_2005_);
lean_del_object(v___x_1984_);
lean_dec(v_val_1982_);
lean_dec(v_x_1957_);
v_a_2053_ = lean_ctor_get(v___x_2006_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v___x_2006_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2055_ = v___x_2006_;
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
else
{
lean_inc(v_a_2053_);
lean_dec(v___x_2006_);
v___x_2055_ = lean_box(0);
v_isShared_2056_ = v_isSharedCheck_2060_;
goto v_resetjp_2054_;
}
v_resetjp_2054_:
{
lean_object* v___x_2058_; 
if (v_isShared_2056_ == 0)
{
v___x_2058_ = v___x_2055_;
goto v_reusejp_2057_;
}
else
{
lean_object* v_reuseFailAlloc_2059_; 
v_reuseFailAlloc_2059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2059_, 0, v_a_2053_);
v___x_2058_ = v_reuseFailAlloc_2059_;
goto v_reusejp_2057_;
}
v_reusejp_2057_:
{
return v___x_2058_;
}
}
}
}
else
{
lean_dec(v_a_2001_);
lean_del_object(v___x_1984_);
lean_dec(v_val_1982_);
v_a_1968_ = v___x_1980_;
goto v___jp_1967_;
}
}
else
{
lean_object* v_a_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2068_; 
lean_del_object(v___x_1984_);
lean_dec(v_val_1982_);
lean_dec(v_x_1957_);
v_a_2061_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2063_ = v___x_2000_;
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_a_2061_);
lean_dec(v___x_2000_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2068_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2064_ == 0)
{
v___x_2066_ = v___x_2063_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_a_2061_);
v___x_2066_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
return v___x_2066_;
}
}
}
}
else
{
lean_del_object(v___x_1984_);
lean_dec(v_val_1982_);
v_a_1968_ = v___x_1980_;
goto v___jp_1967_;
}
v___jp_1986_:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1991_; 
v___x_1987_ = l_Lean_LocalDecl_fvarId(v_val_1982_);
lean_dec(v_val_1982_);
v___x_1988_ = lean_box(v___x_1972_);
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1987_);
lean_ctor_set(v___x_1989_, 1, v___x_1988_);
if (v_isShared_1985_ == 0)
{
lean_ctor_set(v___x_1984_, 0, v___x_1989_);
v___x_1991_ = v___x_1984_;
goto v_reusejp_1990_;
}
else
{
lean_object* v_reuseFailAlloc_1992_; 
v_reuseFailAlloc_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1992_, 0, v___x_1989_);
v___x_1991_ = v_reuseFailAlloc_1992_;
goto v_reusejp_1990_;
}
v_reusejp_1990_:
{
v_a_1976_ = v___x_1991_;
goto v___jp_1975_;
}
}
v___jp_1994_:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1995_ = l_Lean_LocalDecl_fvarId(v_val_1982_);
lean_dec(v_val_1982_);
v___x_1996_ = lean_box(v___x_1993_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1995_);
lean_ctor_set(v___x_1997_, 1, v___x_1996_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
v_a_1976_ = v___x_1998_;
goto v___jp_1975_;
}
}
}
v___jp_1975_:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1977_, 0, v_a_1976_);
v___x_1978_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1977_);
lean_ctor_set(v___x_1978_, 1, v___x_1974_);
v___x_1979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___x_1978_);
return v___x_1979_;
}
}
v___jp_1967_:
{
size_t v___x_1969_; size_t v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = ((size_t)1ULL);
v___x_1970_ = lean_usize_add(v_i_1960_, v___x_1969_);
lean_inc_ref(v_a_1968_);
v___x_1971_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1957_, v_as_1958_, v_sz_1959_, v___x_1970_, v_a_1968_, v___y_1962_, v___y_1963_, v___y_1964_, v___y_1965_);
return v___x_1971_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2070_, lean_object* v_as_2071_, lean_object* v_sz_2072_, lean_object* v_i_2073_, lean_object* v_b_2074_, lean_object* v___y_2075_, lean_object* v___y_2076_, lean_object* v___y_2077_, lean_object* v___y_2078_, lean_object* v___y_2079_){
_start:
{
size_t v_sz_boxed_2080_; size_t v_i_boxed_2081_; lean_object* v_res_2082_; 
v_sz_boxed_2080_ = lean_unbox_usize(v_sz_2072_);
lean_dec(v_sz_2072_);
v_i_boxed_2081_ = lean_unbox_usize(v_i_2073_);
lean_dec(v_i_2073_);
v_res_2082_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2070_, v_as_2071_, v_sz_boxed_2080_, v_i_boxed_2081_, v_b_2074_, v___y_2075_, v___y_2076_, v___y_2077_, v___y_2078_);
lean_dec(v___y_2078_);
lean_dec_ref(v___y_2077_);
lean_dec(v___y_2076_);
lean_dec_ref(v___y_2075_);
lean_dec_ref(v_as_2071_);
return v_res_2082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object* v_x_2083_, lean_object* v_x_2084_, lean_object* v___y_2085_, lean_object* v___y_2086_, lean_object* v___y_2087_, lean_object* v___y_2088_){
_start:
{
if (lean_obj_tag(v_x_2084_) == 0)
{
lean_object* v_cs_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; size_t v_sz_2093_; size_t v___x_2094_; lean_object* v___x_2095_; 
v_cs_2090_ = lean_ctor_get(v_x_2084_, 0);
v___x_2091_ = lean_box(0);
v___x_2092_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2093_ = lean_array_size(v_cs_2090_);
v___x_2094_ = ((size_t)0ULL);
v___x_2095_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2083_, v_cs_2090_, v_sz_2093_, v___x_2094_, v___x_2092_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
if (lean_obj_tag(v___x_2095_) == 0)
{
lean_object* v_a_2096_; lean_object* v___x_2098_; uint8_t v_isShared_2099_; uint8_t v_isSharedCheck_2108_; 
v_a_2096_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2098_ = v___x_2095_;
v_isShared_2099_ = v_isSharedCheck_2108_;
goto v_resetjp_2097_;
}
else
{
lean_inc(v_a_2096_);
lean_dec(v___x_2095_);
v___x_2098_ = lean_box(0);
v_isShared_2099_ = v_isSharedCheck_2108_;
goto v_resetjp_2097_;
}
v_resetjp_2097_:
{
lean_object* v_fst_2100_; 
v_fst_2100_ = lean_ctor_get(v_a_2096_, 0);
lean_inc(v_fst_2100_);
lean_dec(v_a_2096_);
if (lean_obj_tag(v_fst_2100_) == 0)
{
lean_object* v___x_2102_; 
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v___x_2091_);
v___x_2102_ = v___x_2098_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v___x_2091_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
else
{
lean_object* v_val_2104_; lean_object* v___x_2106_; 
v_val_2104_ = lean_ctor_get(v_fst_2100_, 0);
lean_inc(v_val_2104_);
lean_dec_ref(v_fst_2100_);
if (v_isShared_2099_ == 0)
{
lean_ctor_set(v___x_2098_, 0, v_val_2104_);
v___x_2106_ = v___x_2098_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_val_2104_);
v___x_2106_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2105_;
}
v_reusejp_2105_:
{
return v___x_2106_;
}
}
}
}
else
{
lean_object* v_a_2109_; lean_object* v___x_2111_; uint8_t v_isShared_2112_; uint8_t v_isSharedCheck_2116_; 
v_a_2109_ = lean_ctor_get(v___x_2095_, 0);
v_isSharedCheck_2116_ = !lean_is_exclusive(v___x_2095_);
if (v_isSharedCheck_2116_ == 0)
{
v___x_2111_ = v___x_2095_;
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
else
{
lean_inc(v_a_2109_);
lean_dec(v___x_2095_);
v___x_2111_ = lean_box(0);
v_isShared_2112_ = v_isSharedCheck_2116_;
goto v_resetjp_2110_;
}
v_resetjp_2110_:
{
lean_object* v___x_2114_; 
if (v_isShared_2112_ == 0)
{
v___x_2114_ = v___x_2111_;
goto v_reusejp_2113_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_a_2109_);
v___x_2114_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2113_;
}
v_reusejp_2113_:
{
return v___x_2114_;
}
}
}
}
else
{
lean_object* v_vs_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; size_t v_sz_2120_; size_t v___x_2121_; lean_object* v___x_2122_; 
v_vs_2117_ = lean_ctor_get(v_x_2084_, 0);
v___x_2118_ = lean_box(0);
v___x_2119_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2120_ = lean_array_size(v_vs_2117_);
v___x_2121_ = ((size_t)0ULL);
v___x_2122_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2083_, v_vs_2117_, v_sz_2120_, v___x_2121_, v___x_2119_, v___y_2085_, v___y_2086_, v___y_2087_, v___y_2088_);
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
lean_dec_ref(v_fst_2127_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2144_, lean_object* v_as_2145_, size_t v_sz_2146_, size_t v_i_2147_, lean_object* v_b_2148_, lean_object* v___y_2149_, lean_object* v___y_2150_, lean_object* v___y_2151_, lean_object* v___y_2152_){
_start:
{
uint8_t v___x_2154_; 
v___x_2154_ = lean_usize_dec_lt(v_i_2147_, v_sz_2146_);
if (v___x_2154_ == 0)
{
lean_object* v___x_2155_; 
lean_dec(v_x_2144_);
v___x_2155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2155_, 0, v_b_2148_);
return v___x_2155_;
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2157_; 
lean_dec_ref(v_b_2148_);
v_a_2156_ = lean_array_uget_borrowed(v_as_2145_, v_i_2147_);
lean_inc(v_x_2144_);
v___x_2157_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2144_, v_a_2156_, v___y_2149_, v___y_2150_, v___y_2151_, v___y_2152_);
if (lean_obj_tag(v___x_2157_) == 0)
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2172_; 
v_a_2158_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2160_ = v___x_2157_;
v_isShared_2161_ = v_isSharedCheck_2172_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2157_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2172_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2162_; 
v___x_2162_ = lean_box(0);
if (lean_obj_tag(v_a_2158_) == 1)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2166_; 
lean_dec(v_x_2144_);
v___x_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2163_, 0, v_a_2158_);
v___x_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
lean_ctor_set(v___x_2164_, 1, v___x_2162_);
if (v_isShared_2161_ == 0)
{
lean_ctor_set(v___x_2160_, 0, v___x_2164_);
v___x_2166_ = v___x_2160_;
goto v_reusejp_2165_;
}
else
{
lean_object* v_reuseFailAlloc_2167_; 
v_reuseFailAlloc_2167_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2167_, 0, v___x_2164_);
v___x_2166_ = v_reuseFailAlloc_2167_;
goto v_reusejp_2165_;
}
v_reusejp_2165_:
{
return v___x_2166_;
}
}
else
{
lean_object* v___x_2168_; size_t v___x_2169_; size_t v___x_2170_; 
lean_del_object(v___x_2160_);
lean_dec(v_a_2158_);
v___x_2168_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2169_ = ((size_t)1ULL);
v___x_2170_ = lean_usize_add(v_i_2147_, v___x_2169_);
v_i_2147_ = v___x_2170_;
v_b_2148_ = v___x_2168_;
goto _start;
}
}
}
else
{
lean_object* v_a_2173_; lean_object* v___x_2175_; uint8_t v_isShared_2176_; uint8_t v_isSharedCheck_2180_; 
lean_dec(v_x_2144_);
v_a_2173_ = lean_ctor_get(v___x_2157_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2157_);
if (v_isSharedCheck_2180_ == 0)
{
v___x_2175_ = v___x_2157_;
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
else
{
lean_inc(v_a_2173_);
lean_dec(v___x_2157_);
v___x_2175_ = lean_box(0);
v_isShared_2176_ = v_isSharedCheck_2180_;
goto v_resetjp_2174_;
}
v_resetjp_2174_:
{
lean_object* v___x_2178_; 
if (v_isShared_2176_ == 0)
{
v___x_2178_ = v___x_2175_;
goto v_reusejp_2177_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_a_2173_);
v___x_2178_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2177_;
}
v_reusejp_2177_:
{
return v___x_2178_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2181_, lean_object* v_as_2182_, lean_object* v_sz_2183_, lean_object* v_i_2184_, lean_object* v_b_2185_, lean_object* v___y_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
size_t v_sz_boxed_2191_; size_t v_i_boxed_2192_; lean_object* v_res_2193_; 
v_sz_boxed_2191_ = lean_unbox_usize(v_sz_2183_);
lean_dec(v_sz_2183_);
v_i_boxed_2192_ = lean_unbox_usize(v_i_2184_);
lean_dec(v_i_2184_);
v_res_2193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2181_, v_as_2182_, v_sz_boxed_2191_, v_i_boxed_2192_, v_b_2185_, v___y_2186_, v___y_2187_, v___y_2188_, v___y_2189_);
lean_dec(v___y_2189_);
lean_dec_ref(v___y_2188_);
lean_dec(v___y_2187_);
lean_dec_ref(v___y_2186_);
lean_dec_ref(v_as_2182_);
return v_res_2193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2194_, lean_object* v_x_2195_, lean_object* v___y_2196_, lean_object* v___y_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_){
_start:
{
lean_object* v_res_2201_; 
v_res_2201_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2194_, v_x_2195_, v___y_2196_, v___y_2197_, v___y_2198_, v___y_2199_);
lean_dec(v___y_2199_);
lean_dec_ref(v___y_2198_);
lean_dec(v___y_2197_);
lean_dec_ref(v___y_2196_);
lean_dec_ref(v_x_2195_);
return v_res_2201_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object* v_x_2202_, lean_object* v_t_2203_, lean_object* v___y_2204_, lean_object* v___y_2205_, lean_object* v___y_2206_, lean_object* v___y_2207_){
_start:
{
lean_object* v_root_2209_; lean_object* v_tail_2210_; lean_object* v___x_2211_; 
v_root_2209_ = lean_ctor_get(v_t_2203_, 0);
v_tail_2210_ = lean_ctor_get(v_t_2203_, 1);
lean_inc(v_x_2202_);
v___x_2211_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2202_, v_root_2209_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
if (lean_obj_tag(v_a_2212_) == 0)
{
lean_object* v___x_2213_; size_t v_sz_2214_; size_t v___x_2215_; lean_object* v___x_2216_; 
lean_dec_ref(v___x_2211_);
v___x_2213_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2214_ = lean_array_size(v_tail_2210_);
v___x_2215_ = ((size_t)0ULL);
v___x_2216_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2202_, v_tail_2210_, v_sz_2214_, v___x_2215_, v___x_2213_, v___y_2204_, v___y_2205_, v___y_2206_, v___y_2207_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2219_; uint8_t v_isShared_2220_; uint8_t v_isSharedCheck_2229_; 
v_a_2217_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2219_ = v___x_2216_;
v_isShared_2220_ = v_isSharedCheck_2229_;
goto v_resetjp_2218_;
}
else
{
lean_inc(v_a_2217_);
lean_dec(v___x_2216_);
v___x_2219_ = lean_box(0);
v_isShared_2220_ = v_isSharedCheck_2229_;
goto v_resetjp_2218_;
}
v_resetjp_2218_:
{
lean_object* v_fst_2221_; 
v_fst_2221_ = lean_ctor_get(v_a_2217_, 0);
lean_inc(v_fst_2221_);
lean_dec(v_a_2217_);
if (lean_obj_tag(v_fst_2221_) == 0)
{
lean_object* v___x_2223_; 
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v_a_2212_);
v___x_2223_ = v___x_2219_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_a_2212_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
else
{
lean_object* v_val_2225_; lean_object* v___x_2227_; 
v_val_2225_ = lean_ctor_get(v_fst_2221_, 0);
lean_inc(v_val_2225_);
lean_dec_ref(v_fst_2221_);
if (v_isShared_2220_ == 0)
{
lean_ctor_set(v___x_2219_, 0, v_val_2225_);
v___x_2227_ = v___x_2219_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_val_2225_);
v___x_2227_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2226_;
}
v_reusejp_2226_:
{
return v___x_2227_;
}
}
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
v_a_2230_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2216_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2216_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2235_; 
if (v_isShared_2233_ == 0)
{
v___x_2235_ = v___x_2232_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v_a_2230_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
else
{
lean_dec_ref(v_a_2212_);
lean_dec(v_x_2202_);
return v___x_2211_;
}
}
else
{
lean_dec(v_x_2202_);
return v___x_2211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* v_x_2238_, lean_object* v_t_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_){
_start:
{
lean_object* v_res_2245_; 
v_res_2245_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2238_, v_t_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_);
lean_dec(v___y_2243_);
lean_dec_ref(v___y_2242_);
lean_dec(v___y_2241_);
lean_dec_ref(v___y_2240_);
lean_dec_ref(v_t_2239_);
return v_res_2245_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object* v_x_2246_, lean_object* v_lctx_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_, lean_object* v___y_2250_, lean_object* v___y_2251_){
_start:
{
lean_object* v_decls_2253_; lean_object* v___x_2254_; 
v_decls_2253_ = lean_ctor_get(v_lctx_2247_, 1);
v___x_2254_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2246_, v_decls_2253_, v___y_2248_, v___y_2249_, v___y_2250_, v___y_2251_);
return v___x_2254_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object* v_x_2255_, lean_object* v_lctx_2256_, lean_object* v___y_2257_, lean_object* v___y_2258_, lean_object* v___y_2259_, lean_object* v___y_2260_, lean_object* v___y_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2255_, v_lctx_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
lean_dec(v___y_2260_);
lean_dec_ref(v___y_2259_);
lean_dec(v___y_2258_);
lean_dec_ref(v___y_2257_);
lean_dec_ref(v_lctx_2256_);
return v_res_2262_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__0));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__2));
v___x_2268_ = l_Lean_stringToMessageData(v___x_2267_);
return v___x_2268_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; 
v___x_2270_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__4));
v___x_2271_ = l_Lean_stringToMessageData(v___x_2270_);
return v___x_2271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object* v_x_2272_, lean_object* v_mvarId_2273_, lean_object* v___y_2274_, lean_object* v___y_2275_, lean_object* v___y_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v___y_2280_; lean_object* v___y_2281_; lean_object* v___y_2282_; lean_object* v___y_2283_; lean_object* v___x_2328_; 
lean_inc(v_x_2272_);
v___x_2328_ = l_Lean_FVarId_getDecl___redArg(v_x_2272_, v___y_2274_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2328_) == 0)
{
lean_object* v_a_2329_; uint8_t v___x_2330_; uint8_t v___x_2331_; 
v_a_2329_ = lean_ctor_get(v___x_2328_, 0);
lean_inc(v_a_2329_);
lean_dec_ref(v___x_2328_);
v___x_2330_ = 0;
v___x_2331_ = l_Lean_LocalDecl_isLet(v_a_2329_, v___x_2330_);
lean_dec(v_a_2329_);
if (v___x_2331_ == 0)
{
v___y_2280_ = v___y_2274_;
v___y_2281_ = v___y_2275_;
v___y_2282_ = v___y_2276_;
v___y_2283_ = v___y_2277_;
goto v___jp_2279_;
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; 
v___x_2332_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2333_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2272_);
v___x_2334_ = l_Lean_mkFVar(v_x_2272_);
v___x_2335_ = l_Lean_MessageData_ofExpr(v___x_2334_);
v___x_2336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2333_);
lean_ctor_set(v___x_2336_, 1, v___x_2335_);
v___x_2337_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2338_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2338_, 0, v___x_2336_);
lean_ctor_set(v___x_2338_, 1, v___x_2337_);
v___x_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2339_, 0, v___x_2338_);
lean_inc(v_mvarId_2273_);
v___x_2340_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2332_, v_mvarId_2273_, v___x_2339_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_dec_ref(v___x_2340_);
v___y_2280_ = v___y_2274_;
v___y_2281_ = v___y_2275_;
v___y_2282_ = v___y_2276_;
v___y_2283_ = v___y_2277_;
goto v___jp_2279_;
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_dec(v_mvarId_2273_);
lean_dec(v_x_2272_);
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2340_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2340_);
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
else
{
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_mvarId_2273_);
lean_dec(v_x_2272_);
v_a_2349_ = lean_ctor_get(v___x_2328_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2328_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2328_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2328_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2354_; 
if (v_isShared_2352_ == 0)
{
v___x_2354_ = v___x_2351_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v_a_2349_);
v___x_2354_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
return v___x_2354_;
}
}
}
v___jp_2279_:
{
lean_object* v_lctx_2284_; lean_object* v___x_2285_; 
v_lctx_2284_ = lean_ctor_get(v___y_2280_, 2);
lean_inc(v_x_2272_);
v___x_2285_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2272_, v_lctx_2284_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
if (lean_obj_tag(v___x_2285_) == 0)
{
lean_object* v_a_2286_; 
v_a_2286_ = lean_ctor_get(v___x_2285_, 0);
lean_inc(v_a_2286_);
lean_dec_ref(v___x_2285_);
if (lean_obj_tag(v_a_2286_) == 1)
{
lean_object* v_val_2287_; lean_object* v_fst_2288_; lean_object* v_snd_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; uint8_t v___x_2292_; lean_object* v___x_2293_; 
lean_dec(v_x_2272_);
v_val_2287_ = lean_ctor_get(v_a_2286_, 0);
lean_inc(v_val_2287_);
lean_dec_ref(v_a_2286_);
v_fst_2288_ = lean_ctor_get(v_val_2287_, 0);
lean_inc(v_fst_2288_);
v_snd_2289_ = lean_ctor_get(v_val_2287_, 1);
lean_inc(v_snd_2289_);
lean_dec(v_val_2287_);
v___x_2290_ = lean_box(0);
v___x_2291_ = 1;
v___x_2292_ = lean_unbox(v_snd_2289_);
lean_dec(v_snd_2289_);
v___x_2293_ = l_Lean_Meta_substCore(v_mvarId_2273_, v_fst_2288_, v___x_2292_, v___x_2290_, v___x_2291_, v___x_2291_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
if (lean_obj_tag(v___x_2293_) == 0)
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2302_; 
v_a_2294_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2296_ = v___x_2293_;
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2293_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2302_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v_snd_2298_; lean_object* v___x_2300_; 
v_snd_2298_ = lean_ctor_get(v_a_2294_, 1);
lean_inc(v_snd_2298_);
lean_dec(v_a_2294_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 0, v_snd_2298_);
v___x_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_snd_2298_);
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
lean_object* v_a_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2310_; 
v_a_2303_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2310_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2310_ == 0)
{
v___x_2305_ = v___x_2293_;
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_a_2303_);
lean_dec(v___x_2293_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2310_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v___x_2308_; 
if (v_isShared_2306_ == 0)
{
v___x_2308_ = v___x_2305_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2309_; 
v_reuseFailAlloc_2309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2309_, 0, v_a_2303_);
v___x_2308_ = v_reuseFailAlloc_2309_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
return v___x_2308_;
}
}
}
}
else
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
lean_dec(v_a_2286_);
v___x_2311_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2312_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2313_ = l_Lean_mkFVar(v_x_2272_);
v___x_2314_ = l_Lean_MessageData_ofExpr(v___x_2313_);
v___x_2315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2315_, 0, v___x_2312_);
lean_ctor_set(v___x_2315_, 1, v___x_2314_);
v___x_2316_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_2317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2317_, 0, v___x_2315_);
lean_ctor_set(v___x_2317_, 1, v___x_2316_);
v___x_2318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2317_);
v___x_2319_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2311_, v_mvarId_2273_, v___x_2318_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_);
return v___x_2319_;
}
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2322_; uint8_t v_isShared_2323_; uint8_t v_isSharedCheck_2327_; 
lean_dec(v_mvarId_2273_);
lean_dec(v_x_2272_);
v_a_2320_ = lean_ctor_get(v___x_2285_, 0);
v_isSharedCheck_2327_ = !lean_is_exclusive(v___x_2285_);
if (v_isSharedCheck_2327_ == 0)
{
v___x_2322_ = v___x_2285_;
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
else
{
lean_inc(v_a_2320_);
lean_dec(v___x_2285_);
v___x_2322_ = lean_box(0);
v_isShared_2323_ = v_isSharedCheck_2327_;
goto v_resetjp_2321_;
}
v_resetjp_2321_:
{
lean_object* v___x_2325_; 
if (v_isShared_2323_ == 0)
{
v___x_2325_ = v___x_2322_;
goto v_reusejp_2324_;
}
else
{
lean_object* v_reuseFailAlloc_2326_; 
v_reuseFailAlloc_2326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2326_, 0, v_a_2320_);
v___x_2325_ = v_reuseFailAlloc_2326_;
goto v_reusejp_2324_;
}
v_reusejp_2324_:
{
return v___x_2325_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2357_, lean_object* v_mvarId_2358_, lean_object* v___y_2359_, lean_object* v___y_2360_, lean_object* v___y_2361_, lean_object* v___y_2362_, lean_object* v___y_2363_){
_start:
{
lean_object* v_res_2364_; 
v_res_2364_ = l_Lean_Meta_substVar___lam__0(v_x_2357_, v_mvarId_2358_, v___y_2359_, v___y_2360_, v___y_2361_, v___y_2362_);
lean_dec(v___y_2362_);
lean_dec_ref(v___y_2361_);
lean_dec(v___y_2360_);
lean_dec_ref(v___y_2359_);
return v_res_2364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2365_, lean_object* v_x_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_){
_start:
{
lean_object* v___f_2372_; lean_object* v___x_2373_; 
lean_inc(v_mvarId_2365_);
v___f_2372_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2372_, 0, v_x_2366_);
lean_closure_set(v___f_2372_, 1, v_mvarId_2365_);
v___x_2373_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2365_, v___f_2372_, v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2374_, lean_object* v_x_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v_res_2381_; 
v_res_2381_ = l_Lean_Meta_substVar(v_mvarId_2374_, v_x_2375_, v_a_2376_, v_a_2377_, v_a_2378_, v_a_2379_);
lean_dec(v_a_2379_);
lean_dec_ref(v_a_2378_);
lean_dec(v_a_2377_);
lean_dec_ref(v_a_2376_);
return v_res_2381_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2383_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2384_ = l_Lean_stringToMessageData(v___x_2383_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2385_, lean_object* v_snd_2386_, uint8_t v___x_2387_, lean_object* v_fvarSubst_2388_, lean_object* v___y_2389_, lean_object* v___y_2390_, lean_object* v___y_2391_, lean_object* v___y_2392_){
_start:
{
lean_object* v___x_2394_; 
lean_inc(v_fst_2385_);
v___x_2394_ = l_Lean_FVarId_getDecl___redArg(v_fst_2385_, v___y_2389_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; lean_object* v___y_2397_; lean_object* v___y_2398_; lean_object* v___y_2399_; lean_object* v___y_2400_; lean_object* v_newType_2409_; uint8_t v_symm_2410_; lean_object* v___y_2411_; lean_object* v___y_2412_; lean_object* v___y_2413_; lean_object* v___y_2414_; lean_object* v___x_2450_; lean_object* v___x_2451_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref(v___x_2394_);
v___x_2450_ = l_Lean_LocalDecl_type(v_a_2395_);
v___x_2451_ = l_Lean_Meta_matchEq_x3f(v___x_2450_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref(v___x_2451_);
if (lean_obj_tag(v_a_2452_) == 1)
{
lean_object* v_val_2453_; lean_object* v_snd_2454_; lean_object* v_fst_2455_; lean_object* v_snd_2456_; lean_object* v___x_2457_; 
v_val_2453_ = lean_ctor_get(v_a_2452_, 0);
lean_inc(v_val_2453_);
lean_dec_ref(v_a_2452_);
v_snd_2454_ = lean_ctor_get(v_val_2453_, 1);
lean_inc(v_snd_2454_);
lean_dec(v_val_2453_);
v_fst_2455_ = lean_ctor_get(v_snd_2454_, 0);
lean_inc(v_fst_2455_);
v_snd_2456_ = lean_ctor_get(v_snd_2454_, 1);
lean_inc_n(v_snd_2456_, 2);
lean_dec(v_snd_2454_);
lean_inc(v___y_2392_);
lean_inc_ref(v___y_2391_);
lean_inc(v___y_2390_);
lean_inc_ref(v___y_2389_);
v___x_2457_ = lean_whnf(v_snd_2456_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2457_) == 0)
{
lean_object* v_a_2458_; uint8_t v___x_2459_; 
v_a_2458_ = lean_ctor_get(v___x_2457_, 0);
lean_inc(v_a_2458_);
lean_dec_ref(v___x_2457_);
v___x_2459_ = l_Lean_Expr_isFVar(v_a_2458_);
if (v___x_2459_ == 0)
{
lean_object* v___x_2460_; 
lean_dec(v_a_2458_);
lean_inc(v___y_2392_);
lean_inc_ref(v___y_2391_);
lean_inc(v___y_2390_);
lean_inc_ref(v___y_2389_);
lean_inc(v_fst_2455_);
v___x_2460_ = lean_whnf(v_fst_2455_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; uint8_t v___y_2463_; uint8_t v___x_2475_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref(v___x_2460_);
v___x_2475_ = l_Lean_Expr_isFVar(v_a_2461_);
if (v___x_2475_ == 0)
{
lean_dec(v_a_2461_);
lean_dec(v_snd_2456_);
lean_dec(v_fst_2455_);
lean_dec(v_fvarSubst_2388_);
lean_dec(v_fst_2385_);
v___y_2397_ = v___y_2389_;
v___y_2398_ = v___y_2390_;
v___y_2399_ = v___y_2391_;
v___y_2400_ = v___y_2392_;
goto v___jp_2396_;
}
else
{
uint8_t v___x_2476_; 
v___x_2476_ = lean_expr_eqv(v_fst_2455_, v_a_2461_);
lean_dec(v_fst_2455_);
if (v___x_2476_ == 0)
{
v___y_2463_ = v___x_2475_;
goto v___jp_2462_;
}
else
{
v___y_2463_ = v___x_2459_;
goto v___jp_2462_;
}
}
v___jp_2462_:
{
if (v___y_2463_ == 0)
{
lean_object* v___x_2464_; 
lean_dec(v_a_2461_);
lean_dec(v_snd_2456_);
lean_dec(v_a_2395_);
v___x_2464_ = l_Lean_Meta_substCore(v_snd_2386_, v_fst_2385_, v___y_2463_, v_fvarSubst_2388_, v___x_2387_, v___x_2387_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
return v___x_2464_;
}
else
{
lean_object* v___x_2465_; 
v___x_2465_ = l_Lean_Meta_mkEq(v_a_2461_, v_snd_2456_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref(v___x_2465_);
v_newType_2409_ = v_a_2466_;
v_symm_2410_ = v___x_2459_;
v___y_2411_ = v___y_2389_;
v___y_2412_ = v___y_2390_;
v___y_2413_ = v___y_2391_;
v___y_2414_ = v___y_2392_;
goto v___jp_2408_;
}
else
{
lean_object* v_a_2467_; lean_object* v___x_2469_; uint8_t v_isShared_2470_; uint8_t v_isSharedCheck_2474_; 
lean_dec(v_a_2395_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_fvarSubst_2388_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
v_a_2467_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_2469_ = v___x_2465_;
v_isShared_2470_ = v_isSharedCheck_2474_;
goto v_resetjp_2468_;
}
else
{
lean_inc(v_a_2467_);
lean_dec(v___x_2465_);
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
}
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec(v_snd_2456_);
lean_dec(v_fst_2455_);
lean_dec(v_a_2395_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_fvarSubst_2388_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
v_a_2477_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2460_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2460_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
uint8_t v___x_2485_; 
v___x_2485_ = lean_expr_eqv(v_snd_2456_, v_a_2458_);
lean_dec(v_snd_2456_);
if (v___x_2485_ == 0)
{
if (v___x_2459_ == 0)
{
lean_object* v___x_2486_; 
lean_dec(v_a_2458_);
lean_dec(v_fst_2455_);
lean_dec(v_a_2395_);
v___x_2486_ = l_Lean_Meta_substCore(v_snd_2386_, v_fst_2385_, v___x_2387_, v_fvarSubst_2388_, v___x_2387_, v___x_2387_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
return v___x_2486_;
}
else
{
lean_object* v___x_2487_; 
v___x_2487_ = l_Lean_Meta_mkEq(v_fst_2455_, v_a_2458_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
if (lean_obj_tag(v___x_2487_) == 0)
{
lean_object* v_a_2488_; 
v_a_2488_ = lean_ctor_get(v___x_2487_, 0);
lean_inc(v_a_2488_);
lean_dec_ref(v___x_2487_);
v_newType_2409_ = v_a_2488_;
v_symm_2410_ = v___x_2387_;
v___y_2411_ = v___y_2389_;
v___y_2412_ = v___y_2390_;
v___y_2413_ = v___y_2391_;
v___y_2414_ = v___y_2392_;
goto v___jp_2408_;
}
else
{
lean_object* v_a_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2496_; 
lean_dec(v_a_2395_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_fvarSubst_2388_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
v_a_2489_ = lean_ctor_get(v___x_2487_, 0);
v_isSharedCheck_2496_ = !lean_is_exclusive(v___x_2487_);
if (v_isSharedCheck_2496_ == 0)
{
v___x_2491_ = v___x_2487_;
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_a_2489_);
lean_dec(v___x_2487_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2496_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2494_; 
if (v_isShared_2492_ == 0)
{
v___x_2494_ = v___x_2491_;
goto v_reusejp_2493_;
}
else
{
lean_object* v_reuseFailAlloc_2495_; 
v_reuseFailAlloc_2495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2495_, 0, v_a_2489_);
v___x_2494_ = v_reuseFailAlloc_2495_;
goto v_reusejp_2493_;
}
v_reusejp_2493_:
{
return v___x_2494_;
}
}
}
}
}
else
{
lean_object* v___x_2497_; 
lean_dec(v_a_2458_);
lean_dec(v_fst_2455_);
lean_dec(v_a_2395_);
v___x_2497_ = l_Lean_Meta_substCore(v_snd_2386_, v_fst_2385_, v___x_2387_, v_fvarSubst_2388_, v___x_2387_, v___x_2387_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
return v___x_2497_;
}
}
}
else
{
lean_object* v_a_2498_; lean_object* v___x_2500_; uint8_t v_isShared_2501_; uint8_t v_isSharedCheck_2505_; 
lean_dec(v_snd_2456_);
lean_dec(v_fst_2455_);
lean_dec(v_a_2395_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_fvarSubst_2388_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
v_a_2498_ = lean_ctor_get(v___x_2457_, 0);
v_isSharedCheck_2505_ = !lean_is_exclusive(v___x_2457_);
if (v_isSharedCheck_2505_ == 0)
{
v___x_2500_ = v___x_2457_;
v_isShared_2501_ = v_isSharedCheck_2505_;
goto v_resetjp_2499_;
}
else
{
lean_inc(v_a_2498_);
lean_dec(v___x_2457_);
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
lean_dec(v_a_2452_);
lean_dec(v_fvarSubst_2388_);
lean_dec(v_fst_2385_);
v___y_2397_ = v___y_2389_;
v___y_2398_ = v___y_2390_;
v___y_2399_ = v___y_2391_;
v___y_2400_ = v___y_2392_;
goto v___jp_2396_;
}
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_a_2395_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_fvarSubst_2388_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
v_a_2506_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2451_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2451_);
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
v___jp_2396_:
{
lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2401_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2402_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2403_ = l_Lean_LocalDecl_type(v_a_2395_);
lean_dec(v_a_2395_);
v___x_2404_ = l_Lean_indentExpr(v___x_2403_);
v___x_2405_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2405_, 0, v___x_2402_);
lean_ctor_set(v___x_2405_, 1, v___x_2404_);
v___x_2406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2405_);
v___x_2407_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2401_, v_snd_2386_, v___x_2406_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v___x_2407_;
}
v___jp_2408_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = l_Lean_LocalDecl_userName(v_a_2395_);
lean_dec(v_a_2395_);
lean_inc(v_fst_2385_);
v___x_2416_ = l_Lean_mkFVar(v_fst_2385_);
v___x_2417_ = l_Lean_MVarId_assert(v_snd_2386_, v___x_2415_, v_newType_2409_, v___x_2416_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2419_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref(v___x_2417_);
v___x_2419_ = l_Lean_Meta_intro1Core(v_a_2418_, v___x_2387_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v_fst_2421_; lean_object* v_snd_2422_; lean_object* v___x_2423_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref(v___x_2419_);
v_fst_2421_ = lean_ctor_get(v_a_2420_, 0);
lean_inc(v_fst_2421_);
v_snd_2422_ = lean_ctor_get(v_a_2420_, 1);
lean_inc(v_snd_2422_);
lean_dec(v_a_2420_);
v___x_2423_ = l_Lean_MVarId_clear(v_snd_2422_, v_fst_2385_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
if (lean_obj_tag(v___x_2423_) == 0)
{
lean_object* v_a_2424_; lean_object* v___x_2425_; 
v_a_2424_ = lean_ctor_get(v___x_2423_, 0);
lean_inc(v_a_2424_);
lean_dec_ref(v___x_2423_);
v___x_2425_ = l_Lean_Meta_substCore(v_a_2424_, v_fst_2421_, v_symm_2410_, v_fvarSubst_2388_, v___x_2387_, v___x_2387_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_);
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
lean_dec(v_fvarSubst_2388_);
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
lean_dec(v_fvarSubst_2388_);
lean_dec(v_fst_2385_);
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
lean_dec(v_fvarSubst_2388_);
lean_dec(v_fst_2385_);
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
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
lean_dec(v___y_2390_);
lean_dec_ref(v___y_2389_);
lean_dec(v_fvarSubst_2388_);
lean_dec(v_snd_2386_);
lean_dec(v_fst_2385_);
v_a_2514_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2394_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2394_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2522_, lean_object* v_snd_2523_, lean_object* v___x_2524_, lean_object* v_fvarSubst_2525_, lean_object* v___y_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_){
_start:
{
uint8_t v___x_1937__boxed_2531_; lean_object* v_res_2532_; 
v___x_1937__boxed_2531_ = lean_unbox(v___x_2524_);
v_res_2532_ = l_Lean_Meta_substEq___lam__0(v_fst_2522_, v_snd_2523_, v___x_1937__boxed_2531_, v_fvarSubst_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2533_, lean_object* v_hFVarId_2534_, lean_object* v_fvarSubst_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_){
_start:
{
uint8_t v___x_2541_; lean_object* v___x_2542_; 
v___x_2541_ = 1;
v___x_2542_ = l_Lean_Meta_heqToEq(v_mvarId_2533_, v_hFVarId_2534_, v___x_2541_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v_fst_2544_; lean_object* v_snd_2545_; lean_object* v___x_2546_; lean_object* v___f_2547_; lean_object* v___x_2548_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref(v___x_2542_);
v_fst_2544_ = lean_ctor_get(v_a_2543_, 0);
lean_inc(v_fst_2544_);
v_snd_2545_ = lean_ctor_get(v_a_2543_, 1);
lean_inc_n(v_snd_2545_, 2);
lean_dec(v_a_2543_);
v___x_2546_ = lean_box(v___x_2541_);
v___f_2547_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2547_, 0, v_fst_2544_);
lean_closure_set(v___f_2547_, 1, v_snd_2545_);
lean_closure_set(v___f_2547_, 2, v___x_2546_);
lean_closure_set(v___f_2547_, 3, v_fvarSubst_2535_);
v___x_2548_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_snd_2545_, v___f_2547_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_);
return v___x_2548_;
}
else
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2556_; 
lean_dec(v_fvarSubst_2535_);
v_a_2549_ = lean_ctor_get(v___x_2542_, 0);
v_isSharedCheck_2556_ = !lean_is_exclusive(v___x_2542_);
if (v_isSharedCheck_2556_ == 0)
{
v___x_2551_ = v___x_2542_;
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___x_2542_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2556_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
lean_object* v___x_2554_; 
if (v_isShared_2552_ == 0)
{
v___x_2554_ = v___x_2551_;
goto v_reusejp_2553_;
}
else
{
lean_object* v_reuseFailAlloc_2555_; 
v_reuseFailAlloc_2555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2555_, 0, v_a_2549_);
v___x_2554_ = v_reuseFailAlloc_2555_;
goto v_reusejp_2553_;
}
v_reusejp_2553_:
{
return v___x_2554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2557_, lean_object* v_hFVarId_2558_, lean_object* v_fvarSubst_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lean_Meta_substEq(v_mvarId_2557_, v_hFVarId_2558_, v_fvarSubst_2559_, v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2566_, lean_object* v_mvarId_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_, lean_object* v___y_2571_){
_start:
{
lean_object* v___x_2573_; 
lean_inc(v_h_2566_);
v___x_2573_ = l_Lean_FVarId_getType___redArg(v_h_2566_, v___y_2568_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2575_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc_n(v_a_2574_, 2);
lean_dec_ref(v___x_2573_);
v___x_2575_ = l_Lean_Meta_matchEq_x3f(v_a_2574_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref(v___x_2575_);
if (lean_obj_tag(v_a_2576_) == 0)
{
lean_object* v___x_2577_; 
v___x_2577_ = l_Lean_Meta_matchHEq_x3f(v_a_2574_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref(v___x_2577_);
if (lean_obj_tag(v_a_2578_) == 0)
{
lean_object* v___x_2579_; 
v___x_2579_ = l_Lean_Meta_substVar(v_mvarId_2567_, v_h_2566_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2579_;
}
else
{
uint8_t v___x_2580_; lean_object* v___x_2581_; 
lean_dec_ref(v_a_2578_);
v___x_2580_ = 1;
lean_inc(v_h_2566_);
lean_inc(v_mvarId_2567_);
v___x_2581_ = l_Lean_Meta_heqToEq(v_mvarId_2567_, v_h_2566_, v___x_2580_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v_fst_2583_; lean_object* v_snd_2584_; uint8_t v___x_2585_; 
v_a_2582_ = lean_ctor_get(v___x_2581_, 0);
lean_inc(v_a_2582_);
lean_dec_ref(v___x_2581_);
v_fst_2583_ = lean_ctor_get(v_a_2582_, 0);
lean_inc(v_fst_2583_);
v_snd_2584_ = lean_ctor_get(v_a_2582_, 1);
lean_inc(v_snd_2584_);
lean_dec(v_a_2582_);
v___x_2585_ = l_Lean_instBEqMVarId_beq(v_mvarId_2567_, v_snd_2584_);
if (v___x_2585_ == 0)
{
lean_object* v___x_2586_; 
lean_dec(v_mvarId_2567_);
lean_dec(v_h_2566_);
v___x_2586_ = l_Lean_Meta_subst(v_snd_2584_, v_fst_2583_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2586_;
}
else
{
lean_object* v___x_2587_; 
lean_dec(v_snd_2584_);
lean_dec(v_fst_2583_);
v___x_2587_ = l_Lean_Meta_substVar(v_mvarId_2567_, v_h_2566_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
return v___x_2587_;
}
}
else
{
lean_object* v_a_2588_; lean_object* v___x_2590_; uint8_t v_isShared_2591_; uint8_t v_isSharedCheck_2595_; 
lean_dec(v_mvarId_2567_);
lean_dec(v_h_2566_);
v_a_2588_ = lean_ctor_get(v___x_2581_, 0);
v_isSharedCheck_2595_ = !lean_is_exclusive(v___x_2581_);
if (v_isSharedCheck_2595_ == 0)
{
v___x_2590_ = v___x_2581_;
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
else
{
lean_inc(v_a_2588_);
lean_dec(v___x_2581_);
v___x_2590_ = lean_box(0);
v_isShared_2591_ = v_isSharedCheck_2595_;
goto v_resetjp_2589_;
}
v_resetjp_2589_:
{
lean_object* v___x_2593_; 
if (v_isShared_2591_ == 0)
{
v___x_2593_ = v___x_2590_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_a_2588_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
}
else
{
lean_object* v_a_2596_; lean_object* v___x_2598_; uint8_t v_isShared_2599_; uint8_t v_isSharedCheck_2603_; 
lean_dec(v_mvarId_2567_);
lean_dec(v_h_2566_);
v_a_2596_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2603_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2603_ == 0)
{
v___x_2598_ = v___x_2577_;
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
else
{
lean_inc(v_a_2596_);
lean_dec(v___x_2577_);
v___x_2598_ = lean_box(0);
v_isShared_2599_ = v_isSharedCheck_2603_;
goto v_resetjp_2597_;
}
v_resetjp_2597_:
{
lean_object* v___x_2601_; 
if (v_isShared_2599_ == 0)
{
v___x_2601_ = v___x_2598_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2602_; 
v_reuseFailAlloc_2602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2602_, 0, v_a_2596_);
v___x_2601_ = v_reuseFailAlloc_2602_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
return v___x_2601_;
}
}
}
}
else
{
lean_object* v___x_2604_; lean_object* v___x_2605_; 
lean_dec_ref(v_a_2576_);
lean_dec(v_a_2574_);
v___x_2604_ = lean_box(0);
v___x_2605_ = l_Lean_Meta_substEq(v_mvarId_2567_, v_h_2566_, v___x_2604_, v___y_2568_, v___y_2569_, v___y_2570_, v___y_2571_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2614_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2614_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2614_ == 0)
{
v___x_2608_ = v___x_2605_;
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_dec(v___x_2605_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2614_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v_snd_2610_; lean_object* v___x_2612_; 
v_snd_2610_ = lean_ctor_get(v_a_2606_, 1);
lean_inc(v_snd_2610_);
lean_dec(v_a_2606_);
if (v_isShared_2609_ == 0)
{
lean_ctor_set(v___x_2608_, 0, v_snd_2610_);
v___x_2612_ = v___x_2608_;
goto v_reusejp_2611_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_snd_2610_);
v___x_2612_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2611_;
}
v_reusejp_2611_:
{
return v___x_2612_;
}
}
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
v_a_2615_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2605_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2605_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec(v_a_2574_);
lean_dec(v_mvarId_2567_);
lean_dec(v_h_2566_);
v_a_2623_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2575_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2575_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec(v_mvarId_2567_);
lean_dec(v_h_2566_);
v_a_2631_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2573_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2573_);
v___x_2633_ = lean_box(0);
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
v_resetjp_2632_:
{
lean_object* v___x_2636_; 
if (v_isShared_2634_ == 0)
{
v___x_2636_ = v___x_2633_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_a_2631_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2639_, lean_object* v_mvarId_2640_, lean_object* v___y_2641_, lean_object* v___y_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_){
_start:
{
lean_object* v_res_2646_; 
v_res_2646_ = l_Lean_Meta_subst___lam__0(v_h_2639_, v_mvarId_2640_, v___y_2641_, v___y_2642_, v___y_2643_, v___y_2644_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
lean_dec(v___y_2642_);
lean_dec_ref(v___y_2641_);
return v_res_2646_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2647_, lean_object* v_h_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_, lean_object* v_a_2652_){
_start:
{
lean_object* v___f_2654_; lean_object* v___x_2655_; 
lean_inc(v_mvarId_2647_);
v___f_2654_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2654_, 0, v_h_2648_);
lean_closure_set(v___f_2654_, 1, v_mvarId_2647_);
v___x_2655_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2647_, v___f_2654_, v_a_2649_, v_a_2650_, v_a_2651_, v_a_2652_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2656_, lean_object* v_h_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_Lean_Meta_subst(v_mvarId_2656_, v_h_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2664_, lean_object* v___y_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_){
_start:
{
lean_object* v___x_2670_; 
v___x_2670_ = l_Lean_Meta_saveState___redArg(v___y_2666_, v___y_2668_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v_a_2671_; lean_object* v___x_2672_; 
v_a_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_a_2671_);
lean_dec_ref(v___x_2670_);
lean_inc(v___y_2668_);
lean_inc_ref(v___y_2667_);
lean_inc(v___y_2666_);
lean_inc_ref(v___y_2665_);
v___x_2672_ = lean_apply_5(v_x_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, lean_box(0));
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_dec(v_a_2671_);
return v___x_2672_;
}
else
{
lean_object* v_a_2673_; uint8_t v___y_2675_; uint8_t v___x_2693_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
v___x_2693_ = l_Lean_Exception_isInterrupt(v_a_2673_);
if (v___x_2693_ == 0)
{
uint8_t v___x_2694_; 
lean_inc(v_a_2673_);
v___x_2694_ = l_Lean_Exception_isRuntime(v_a_2673_);
v___y_2675_ = v___x_2694_;
goto v___jp_2674_;
}
else
{
v___y_2675_ = v___x_2693_;
goto v___jp_2674_;
}
v___jp_2674_:
{
if (v___y_2675_ == 0)
{
lean_object* v___x_2676_; 
lean_dec_ref(v___x_2672_);
v___x_2676_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2671_, v___y_2666_, v___y_2668_);
lean_dec(v_a_2671_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2683_ == 0)
{
lean_object* v_unused_2684_; 
v_unused_2684_ = lean_ctor_get(v___x_2676_, 0);
lean_dec(v_unused_2684_);
v___x_2678_ = v___x_2676_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_dec(v___x_2676_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
lean_ctor_set_tag(v___x_2678_, 1);
lean_ctor_set(v___x_2678_, 0, v_a_2673_);
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2673_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_dec(v_a_2673_);
v_a_2685_ = lean_ctor_get(v___x_2676_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2676_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2676_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2676_);
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
else
{
lean_dec(v_a_2673_);
lean_dec(v_a_2671_);
return v___x_2672_;
}
}
}
}
else
{
lean_object* v_a_2695_; lean_object* v___x_2697_; uint8_t v_isShared_2698_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref(v_x_2664_);
v_a_2695_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2702_ == 0)
{
v___x_2697_ = v___x_2670_;
v_isShared_2698_ = v_isSharedCheck_2702_;
goto v_resetjp_2696_;
}
else
{
lean_inc(v_a_2695_);
lean_dec(v___x_2670_);
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
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2703_, v___y_2704_, v___y_2705_, v___y_2706_, v___y_2707_);
lean_dec(v___y_2707_);
lean_dec_ref(v___y_2706_);
lean_dec(v___y_2705_);
lean_dec_ref(v___y_2704_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2710_, lean_object* v_x_2711_, lean_object* v___y_2712_, lean_object* v___y_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_){
_start:
{
lean_object* v___x_2717_; 
v___x_2717_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2711_, v___y_2712_, v___y_2713_, v___y_2714_, v___y_2715_);
return v___x_2717_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2718_, lean_object* v_x_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2718_, v_x_2719_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec(v___y_2721_);
lean_dec_ref(v___y_2720_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_, lean_object* v___y_2729_, lean_object* v___y_2730_){
_start:
{
lean_object* v_ref_2732_; lean_object* v___x_2733_; lean_object* v_a_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2742_; 
v_ref_2732_ = lean_ctor_get(v___y_2729_, 5);
v___x_2733_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msg_2726_, v___y_2727_, v___y_2728_, v___y_2729_, v___y_2730_);
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2742_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2736_ = v___x_2733_;
v_isShared_2737_ = v_isSharedCheck_2742_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_a_2734_);
lean_dec(v___x_2733_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2742_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2740_; 
lean_inc(v_ref_2732_);
v___x_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2738_, 0, v_ref_2732_);
lean_ctor_set(v___x_2738_, 1, v_a_2734_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set_tag(v___x_2736_, 1);
lean_ctor_set(v___x_2736_, 0, v___x_2738_);
v___x_2740_ = v___x_2736_;
goto v_reusejp_2739_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2738_);
v___x_2740_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2739_;
}
v_reusejp_2739_:
{
return v___x_2740_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_, lean_object* v___y_2746_, lean_object* v___y_2747_, lean_object* v___y_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
lean_dec(v___y_2747_);
lean_dec_ref(v___y_2746_);
lean_dec(v___y_2745_);
lean_dec_ref(v___y_2744_);
return v_res_2749_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
return v___x_2752_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2755_ = l_Lean_stringToMessageData(v___x_2754_);
return v___x_2755_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2758_ = l_Lean_stringToMessageData(v___x_2757_);
return v___x_2758_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2760_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2761_ = l_Lean_stringToMessageData(v___x_2760_);
return v___x_2761_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; 
v___x_2763_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2764_ = l_Lean_stringToMessageData(v___x_2763_);
return v___x_2764_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; 
v___x_2777_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2778_ = l_Lean_stringToMessageData(v___x_2777_);
return v___x_2778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2787_, uint8_t v_substLHS_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_, lean_object* v___y_2792_){
_start:
{
lean_object* v___x_2794_; 
lean_inc(v_mvarId_2787_);
v___x_2794_ = l_Lean_MVarId_getType_x27(v_mvarId_2787_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
lean_inc(v_a_2795_);
lean_dec_ref(v___x_2794_);
if (lean_obj_tag(v_a_2795_) == 7)
{
lean_object* v_binderType_2799_; lean_object* v_body_2800_; uint8_t v___x_2801_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v___y_2893_; lean_object* v___y_2894_; lean_object* v___y_2895_; lean_object* v___y_2896_; lean_object* v_fst_2936_; lean_object* v_fst_2937_; lean_object* v_fst_2938_; lean_object* v_snd_2939_; lean_object* v___y_2940_; lean_object* v___y_2941_; lean_object* v___y_2942_; lean_object* v___y_2943_; 
v_binderType_2799_ = lean_ctor_get(v_a_2795_, 1);
lean_inc_ref(v_binderType_2799_);
v_body_2800_ = lean_ctor_get(v_a_2795_, 2);
lean_inc_ref(v_body_2800_);
lean_dec_ref(v_a_2795_);
v___x_2801_ = l_Lean_Expr_hasLooseBVars(v_body_2800_);
if (v___x_2801_ == 0)
{
lean_object* v___x_2955_; 
v___x_2955_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2799_, v___y_2790_);
if (lean_obj_tag(v___x_2955_) == 0)
{
lean_object* v_a_2956_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___y_2960_; lean_object* v___y_2961_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v_a_2956_ = lean_ctor_get(v___x_2955_, 0);
lean_inc(v_a_2956_);
lean_dec_ref(v___x_2955_);
v___x_2972_ = l_Lean_Expr_cleanupAnnotations(v_a_2956_);
v___x_2973_ = l_Lean_Expr_isApp(v___x_2972_);
if (v___x_2973_ == 0)
{
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_body_2800_);
lean_dec(v_mvarId_2787_);
v___y_2958_ = v___y_2789_;
v___y_2959_ = v___y_2790_;
v___y_2960_ = v___y_2791_;
v___y_2961_ = v___y_2792_;
goto v___jp_2957_;
}
else
{
lean_object* v_arg_2974_; lean_object* v___x_2975_; uint8_t v___x_2976_; 
v_arg_2974_ = lean_ctor_get(v___x_2972_, 1);
lean_inc_ref(v_arg_2974_);
v___x_2975_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2972_);
v___x_2976_ = l_Lean_Expr_isApp(v___x_2975_);
if (v___x_2976_ == 0)
{
lean_dec_ref(v___x_2975_);
lean_dec_ref(v_arg_2974_);
lean_dec_ref(v_body_2800_);
lean_dec(v_mvarId_2787_);
v___y_2958_ = v___y_2789_;
v___y_2959_ = v___y_2790_;
v___y_2960_ = v___y_2791_;
v___y_2961_ = v___y_2792_;
goto v___jp_2957_;
}
else
{
lean_object* v_arg_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v_arg_2977_ = lean_ctor_get(v___x_2975_, 1);
lean_inc_ref(v_arg_2977_);
v___x_2978_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2975_);
v___x_2979_ = l_Lean_Expr_isApp(v___x_2978_);
if (v___x_2979_ == 0)
{
lean_dec_ref(v___x_2978_);
lean_dec_ref(v_arg_2977_);
lean_dec_ref(v_arg_2974_);
lean_dec_ref(v_body_2800_);
lean_dec(v_mvarId_2787_);
v___y_2958_ = v___y_2789_;
v___y_2959_ = v___y_2790_;
v___y_2960_ = v___y_2791_;
v___y_2961_ = v___y_2792_;
goto v___jp_2957_;
}
else
{
lean_object* v_arg_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; uint8_t v___x_2983_; 
v_arg_2980_ = lean_ctor_get(v___x_2978_, 1);
lean_inc_ref(v_arg_2980_);
v___x_2981_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2978_);
v___x_2982_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_2983_ = l_Lean_Expr_isConstOf(v___x_2981_, v___x_2982_);
if (v___x_2983_ == 0)
{
uint8_t v___x_2984_; 
v___x_2984_ = l_Lean_Expr_isApp(v___x_2981_);
if (v___x_2984_ == 0)
{
lean_dec_ref(v___x_2981_);
lean_dec_ref(v_arg_2980_);
lean_dec_ref(v_arg_2977_);
lean_dec_ref(v_arg_2974_);
lean_dec_ref(v_body_2800_);
lean_dec(v_mvarId_2787_);
v___y_2958_ = v___y_2789_;
v___y_2959_ = v___y_2790_;
v___y_2960_ = v___y_2791_;
v___y_2961_ = v___y_2792_;
goto v___jp_2957_;
}
else
{
lean_object* v_arg_2985_; lean_object* v___y_2987_; lean_object* v___y_2988_; lean_object* v___y_2989_; lean_object* v___y_2990_; lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v_arg_2985_ = lean_ctor_get(v___x_2981_, 1);
lean_inc_ref(v_arg_2985_);
v___x_2993_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2981_);
v___x_2994_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_2995_ = l_Lean_Expr_isConstOf(v___x_2993_, v___x_2994_);
lean_dec_ref(v___x_2993_);
if (v___x_2995_ == 0)
{
lean_dec_ref(v_arg_2985_);
lean_dec_ref(v_arg_2980_);
lean_dec_ref(v_arg_2977_);
lean_dec_ref(v_arg_2974_);
lean_dec_ref(v_body_2800_);
lean_dec(v_mvarId_2787_);
v___y_2958_ = v___y_2789_;
v___y_2959_ = v___y_2790_;
v___y_2960_ = v___y_2791_;
v___y_2961_ = v___y_2792_;
goto v___jp_2957_;
}
else
{
lean_object* v___x_2996_; 
lean_inc_ref(v_arg_2985_);
v___x_2996_ = l_Lean_Meta_isExprDefEq(v_arg_2985_, v_arg_2977_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
if (lean_obj_tag(v___x_2996_) == 0)
{
lean_object* v_a_2997_; uint8_t v___x_2998_; 
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
lean_inc(v_a_2997_);
lean_dec_ref(v___x_2996_);
v___x_2998_ = lean_unbox(v_a_2997_);
lean_dec(v_a_2997_);
if (v___x_2998_ == 0)
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
lean_dec_ref(v_arg_2985_);
lean_dec_ref(v_arg_2980_);
lean_dec_ref(v_arg_2974_);
lean_dec_ref(v_body_2800_);
lean_dec(v_mvarId_2787_);
v___x_2999_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_3000_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2999_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_3003_ = v___x_3000_;
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
else
{
lean_inc(v_a_3001_);
lean_dec(v___x_3000_);
v___x_3003_ = lean_box(0);
v_isShared_3004_ = v_isSharedCheck_3008_;
goto v_resetjp_3002_;
}
v_resetjp_3002_:
{
lean_object* v___x_3006_; 
if (v_isShared_3004_ == 0)
{
v___x_3006_ = v___x_3003_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3007_; 
v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_a_3001_);
v___x_3006_ = v_reuseFailAlloc_3007_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
return v___x_3006_;
}
}
}
else
{
v___y_2987_ = v___y_2789_;
v___y_2988_ = v___y_2790_;
v___y_2989_ = v___y_2791_;
v___y_2990_ = v___y_2792_;
goto v___jp_2986_;
}
}
else
{
lean_object* v_a_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3016_; 
lean_dec_ref(v_arg_2985_);
lean_dec_ref(v_arg_2980_);
lean_dec_ref(v_arg_2974_);
lean_dec_ref(v_body_2800_);
lean_dec(v_mvarId_2787_);
v_a_3009_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3016_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3016_ == 0)
{
v___x_3011_ = v___x_2996_;
v_isShared_3012_ = v_isSharedCheck_3016_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_a_3009_);
lean_dec(v___x_2996_);
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
v___jp_2986_:
{
if (v_substLHS_2788_ == 0)
{
lean_object* v___x_2991_; 
v___x_2991_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2936_ = v_arg_2985_;
v_fst_2937_ = v_arg_2980_;
v_fst_2938_ = v_arg_2974_;
v_snd_2939_ = v___x_2991_;
v___y_2940_ = v___y_2987_;
v___y_2941_ = v___y_2988_;
v___y_2942_ = v___y_2989_;
v___y_2943_ = v___y_2990_;
goto v___jp_2935_;
}
else
{
lean_object* v___x_2992_; 
v___x_2992_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2936_ = v_arg_2985_;
v_fst_2937_ = v_arg_2974_;
v_fst_2938_ = v_arg_2980_;
v_snd_2939_ = v___x_2992_;
v___y_2940_ = v___y_2987_;
v___y_2941_ = v___y_2988_;
v___y_2942_ = v___y_2989_;
v___y_2943_ = v___y_2990_;
goto v___jp_2935_;
}
}
}
}
else
{
lean_dec_ref(v___x_2981_);
if (v_substLHS_2788_ == 0)
{
lean_object* v___x_3017_; 
v___x_3017_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2936_ = v_arg_2980_;
v_fst_2937_ = v_arg_2977_;
v_fst_2938_ = v_arg_2974_;
v_snd_2939_ = v___x_3017_;
v___y_2940_ = v___y_2789_;
v___y_2941_ = v___y_2790_;
v___y_2942_ = v___y_2791_;
v___y_2943_ = v___y_2792_;
goto v___jp_2935_;
}
else
{
lean_object* v___x_3018_; 
v___x_3018_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2936_ = v_arg_2980_;
v_fst_2937_ = v_arg_2974_;
v_fst_2938_ = v_arg_2977_;
v_snd_2939_ = v___x_3018_;
v___y_2940_ = v___y_2789_;
v___y_2941_ = v___y_2790_;
v___y_2942_ = v___y_2791_;
v___y_2943_ = v___y_2792_;
goto v___jp_2935_;
}
}
}
}
}
v___jp_2957_:
{
lean_object* v___x_2962_; lean_object* v___x_2963_; lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
v___x_2962_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_2963_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2962_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
v_a_2964_ = lean_ctor_get(v___x_2963_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2963_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2963_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2963_);
v___x_2966_ = lean_box(0);
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
v_resetjp_2965_:
{
lean_object* v___x_2969_; 
if (v_isShared_2967_ == 0)
{
v___x_2969_ = v___x_2966_;
goto v_reusejp_2968_;
}
else
{
lean_object* v_reuseFailAlloc_2970_; 
v_reuseFailAlloc_2970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2970_, 0, v_a_2964_);
v___x_2969_ = v_reuseFailAlloc_2970_;
goto v_reusejp_2968_;
}
v_reusejp_2968_:
{
return v___x_2969_;
}
}
}
}
else
{
lean_object* v_a_3019_; lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
lean_dec_ref(v_body_2800_);
lean_dec(v_mvarId_2787_);
v_a_3019_ = lean_ctor_get(v___x_2955_, 0);
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_2955_);
if (v_isSharedCheck_3026_ == 0)
{
v___x_3021_ = v___x_2955_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_inc(v_a_3019_);
lean_dec(v___x_2955_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_a_3019_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
}
else
{
lean_dec_ref(v_body_2800_);
lean_dec_ref(v_binderType_2799_);
lean_dec(v_mvarId_2787_);
goto v___jp_2796_;
}
v___jp_2802_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; uint8_t v___x_2816_; uint8_t v___x_2817_; lean_object* v___x_2818_; 
v___x_2814_ = lean_mk_empty_array_with_capacity(v___y_2809_);
lean_inc_ref(v___x_2814_);
v___x_2815_ = lean_array_push(v___x_2814_, v___y_2803_);
v___x_2816_ = 1;
v___x_2817_ = 1;
v___x_2818_ = l_Lean_Meta_mkLambdaFVars(v___x_2815_, v_body_2800_, v___x_2801_, v___x_2816_, v___x_2801_, v___x_2816_, v___x_2817_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
lean_dec_ref(v___x_2815_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref(v___x_2818_);
lean_inc(v___y_2805_);
v___x_2820_ = l_Lean_MVarId_getTag(v___y_2805_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref(v___x_2820_);
lean_inc_ref(v___y_2804_);
v___x_2822_ = lean_array_push(v___x_2814_, v___y_2804_);
lean_inc(v_a_2819_);
v___x_2823_ = l_Lean_Expr_beta(v_a_2819_, v___x_2822_);
lean_inc_ref(v___x_2823_);
v___x_2824_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2823_, v_a_2821_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2826_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref(v___x_2824_);
v___x_2826_ = l_Lean_Meta_getLevel(v___x_2823_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v_a_2827_; lean_object* v___x_2828_; 
v_a_2827_ = lean_ctor_get(v___x_2826_, 0);
lean_inc(v_a_2827_);
lean_dec_ref(v___x_2826_);
lean_inc_ref(v___y_2808_);
v___x_2828_ = l_Lean_Meta_getLevel(v___y_2808_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2828_) == 0)
{
lean_object* v_a_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2846_; 
v_a_2829_ = lean_ctor_get(v___x_2828_, 0);
lean_inc(v_a_2829_);
lean_dec_ref(v___x_2828_);
v___x_2830_ = lean_box(0);
v___x_2831_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2831_, 0, v_a_2829_);
lean_ctor_set(v___x_2831_, 1, v___x_2830_);
v___x_2832_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2832_, 0, v_a_2827_);
lean_ctor_set(v___x_2832_, 1, v___x_2831_);
lean_inc(v___y_2807_);
v___x_2833_ = l_Lean_mkConst(v___y_2807_, v___x_2832_);
lean_inc(v_a_2825_);
lean_inc_ref(v___y_2804_);
v___x_2834_ = l_Lean_mkApp4(v___x_2833_, v___y_2808_, v___y_2804_, v_a_2819_, v_a_2825_);
v___x_2835_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v___y_2805_, v___x_2834_, v___y_2811_);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2835_);
if (v_isSharedCheck_2846_ == 0)
{
lean_object* v_unused_2847_; 
v_unused_2847_ = lean_ctor_get(v___x_2835_, 0);
lean_dec(v_unused_2847_);
v___x_2837_ = v___x_2835_;
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
else
{
lean_dec(v___x_2835_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2846_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2844_; 
v___x_2839_ = l_Lean_Meta_FVarSubst_empty;
v___x_2840_ = l_Lean_Meta_FVarSubst_insert(v___x_2839_, v___y_2806_, v___y_2804_);
v___x_2841_ = l_Lean_Expr_mvarId_x21(v_a_2825_);
lean_dec(v_a_2825_);
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2840_);
lean_ctor_set(v___x_2842_, 1, v___x_2841_);
if (v_isShared_2838_ == 0)
{
lean_ctor_set(v___x_2837_, 0, v___x_2842_);
v___x_2844_ = v___x_2837_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v___x_2842_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_dec(v_a_2827_);
lean_dec(v_a_2825_);
lean_dec(v_a_2819_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
v_a_2848_ = lean_ctor_get(v___x_2828_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2828_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2828_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2828_);
v___x_2850_ = lean_box(0);
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
v_resetjp_2849_:
{
lean_object* v___x_2853_; 
if (v_isShared_2851_ == 0)
{
v___x_2853_ = v___x_2850_;
goto v_reusejp_2852_;
}
else
{
lean_object* v_reuseFailAlloc_2854_; 
v_reuseFailAlloc_2854_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2854_, 0, v_a_2848_);
v___x_2853_ = v_reuseFailAlloc_2854_;
goto v_reusejp_2852_;
}
v_reusejp_2852_:
{
return v___x_2853_;
}
}
}
}
else
{
lean_object* v_a_2856_; lean_object* v___x_2858_; uint8_t v_isShared_2859_; uint8_t v_isSharedCheck_2863_; 
lean_dec(v_a_2825_);
lean_dec(v_a_2819_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
v_a_2856_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2863_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2863_ == 0)
{
v___x_2858_ = v___x_2826_;
v_isShared_2859_ = v_isSharedCheck_2863_;
goto v_resetjp_2857_;
}
else
{
lean_inc(v_a_2856_);
lean_dec(v___x_2826_);
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
lean_dec_ref(v___x_2823_);
lean_dec(v_a_2819_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
v_a_2864_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2871_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2871_ == 0)
{
v___x_2866_ = v___x_2824_;
v_isShared_2867_ = v_isSharedCheck_2871_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_a_2864_);
lean_dec(v___x_2824_);
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
lean_dec(v_a_2819_);
lean_dec_ref(v___x_2814_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
v_a_2872_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2874_ = v___x_2820_;
v_isShared_2875_ = v_isSharedCheck_2879_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_a_2872_);
lean_dec(v___x_2820_);
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
lean_dec_ref(v___x_2814_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2806_);
lean_dec(v___y_2805_);
lean_dec_ref(v___y_2804_);
v_a_2880_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2887_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2887_ == 0)
{
v___x_2882_ = v___x_2818_;
v_isShared_2883_ = v_isSharedCheck_2887_;
goto v_resetjp_2881_;
}
else
{
lean_inc(v_a_2880_);
lean_dec(v___x_2818_);
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
v___jp_2888_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2897_ = l_Lean_Expr_fvarId_x21(v___y_2889_);
v___x_2898_ = lean_unsigned_to_nat(1u);
v___x_2899_ = lean_mk_empty_array_with_capacity(v___x_2898_);
lean_inc(v___x_2897_);
v___x_2900_ = lean_array_push(v___x_2899_, v___x_2897_);
v___x_2901_ = l_Lean_MVarId_revert(v_mvarId_2787_, v___x_2900_, v___x_2801_, v___x_2801_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
if (lean_obj_tag(v___x_2901_) == 0)
{
lean_object* v_a_2902_; lean_object* v_fst_2903_; lean_object* v_snd_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2926_; 
v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
lean_inc(v_a_2902_);
lean_dec_ref(v___x_2901_);
v_fst_2903_ = lean_ctor_get(v_a_2902_, 0);
v_snd_2904_ = lean_ctor_get(v_a_2902_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_a_2902_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2906_ = v_a_2902_;
v_isShared_2907_ = v_isSharedCheck_2926_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_snd_2904_);
lean_inc(v_fst_2903_);
lean_dec(v_a_2902_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2926_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = lean_array_get_size(v_fst_2903_);
lean_dec(v_fst_2903_);
v___x_2909_ = lean_nat_dec_eq(v___x_2908_, v___x_2898_);
if (v___x_2909_ == 0)
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2913_; 
lean_dec(v_snd_2904_);
lean_dec(v___x_2897_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v_body_2800_);
v___x_2910_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2911_ = l_Lean_MessageData_ofExpr(v___y_2889_);
if (v_isShared_2907_ == 0)
{
lean_ctor_set_tag(v___x_2906_, 7);
lean_ctor_set(v___x_2906_, 1, v___x_2911_);
lean_ctor_set(v___x_2906_, 0, v___x_2910_);
v___x_2913_ = v___x_2906_;
goto v_reusejp_2912_;
}
else
{
lean_object* v_reuseFailAlloc_2925_; 
v_reuseFailAlloc_2925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2910_);
lean_ctor_set(v_reuseFailAlloc_2925_, 1, v___x_2911_);
v___x_2913_ = v_reuseFailAlloc_2925_;
goto v_reusejp_2912_;
}
v_reusejp_2912_:
{
lean_object* v___x_2914_; lean_object* v___x_2915_; lean_object* v___x_2916_; lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
v___x_2914_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2913_);
lean_ctor_set(v___x_2915_, 1, v___x_2914_);
v___x_2916_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2915_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_);
v_a_2917_ = lean_ctor_get(v___x_2916_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2916_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2916_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2916_);
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
else
{
lean_del_object(v___x_2906_);
v___y_2803_ = v___y_2889_;
v___y_2804_ = v___y_2890_;
v___y_2805_ = v_snd_2904_;
v___y_2806_ = v___x_2897_;
v___y_2807_ = v___y_2891_;
v___y_2808_ = v___y_2892_;
v___y_2809_ = v___x_2898_;
v___y_2810_ = v___y_2893_;
v___y_2811_ = v___y_2894_;
v___y_2812_ = v___y_2895_;
v___y_2813_ = v___y_2896_;
goto v___jp_2802_;
}
}
}
else
{
lean_object* v_a_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2934_; 
lean_dec(v___x_2897_);
lean_dec_ref(v___y_2892_);
lean_dec_ref(v___y_2890_);
lean_dec_ref(v___y_2889_);
lean_dec_ref(v_body_2800_);
v_a_2927_ = lean_ctor_get(v___x_2901_, 0);
v_isSharedCheck_2934_ = !lean_is_exclusive(v___x_2901_);
if (v_isSharedCheck_2934_ == 0)
{
v___x_2929_ = v___x_2901_;
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_a_2927_);
lean_dec(v___x_2901_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2934_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2932_; 
if (v_isShared_2930_ == 0)
{
v___x_2932_ = v___x_2929_;
goto v_reusejp_2931_;
}
else
{
lean_object* v_reuseFailAlloc_2933_; 
v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
v___x_2932_ = v_reuseFailAlloc_2933_;
goto v_reusejp_2931_;
}
v_reusejp_2931_:
{
return v___x_2932_;
}
}
}
}
v___jp_2935_:
{
uint8_t v___x_2944_; 
v___x_2944_ = l_Lean_Expr_isFVar(v_fst_2938_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec_ref(v_fst_2938_);
lean_dec_ref(v_fst_2937_);
lean_dec_ref(v_fst_2936_);
lean_dec_ref(v_body_2800_);
lean_dec(v_mvarId_2787_);
v___x_2945_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2946_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2945_, v___y_2940_, v___y_2941_, v___y_2942_, v___y_2943_);
v_a_2947_ = lean_ctor_get(v___x_2946_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2946_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2946_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2946_);
v___x_2949_ = lean_box(0);
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
v_resetjp_2948_:
{
lean_object* v___x_2952_; 
if (v_isShared_2950_ == 0)
{
v___x_2952_ = v___x_2949_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
}
else
{
v___y_2889_ = v_fst_2938_;
v___y_2890_ = v_fst_2937_;
v___y_2891_ = v_snd_2939_;
v___y_2892_ = v_fst_2936_;
v___y_2893_ = v___y_2940_;
v___y_2894_ = v___y_2941_;
v___y_2895_ = v___y_2942_;
v___y_2896_ = v___y_2943_;
goto v___jp_2888_;
}
}
}
else
{
lean_dec(v_a_2795_);
lean_dec(v_mvarId_2787_);
goto v___jp_2796_;
}
v___jp_2796_:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2798_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2797_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
return v___x_2798_;
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_mvarId_2787_);
v_a_3027_ = lean_ctor_get(v___x_2794_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_2794_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_2794_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object* v_mvarId_3035_, lean_object* v_substLHS_3036_, lean_object* v___y_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_){
_start:
{
uint8_t v_substLHS_boxed_3042_; lean_object* v_res_3043_; 
v_substLHS_boxed_3042_ = lean_unbox(v_substLHS_3036_);
v_res_3043_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_3035_, v_substLHS_boxed_3042_, v___y_3037_, v___y_3038_, v___y_3039_, v___y_3040_);
lean_dec(v___y_3040_);
lean_dec_ref(v___y_3039_);
lean_dec(v___y_3038_);
lean_dec_ref(v___y_3037_);
return v_res_3043_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3044_, lean_object* v_i_3045_, lean_object* v_k_3046_){
_start:
{
lean_object* v___x_3047_; uint8_t v___x_3048_; 
v___x_3047_ = lean_array_get_size(v_keys_3044_);
v___x_3048_ = lean_nat_dec_lt(v_i_3045_, v___x_3047_);
if (v___x_3048_ == 0)
{
lean_dec(v_i_3045_);
return v___x_3048_;
}
else
{
lean_object* v_k_x27_3049_; uint8_t v___x_3050_; 
v_k_x27_3049_ = lean_array_fget_borrowed(v_keys_3044_, v_i_3045_);
v___x_3050_ = l_Lean_instBEqMVarId_beq(v_k_3046_, v_k_x27_3049_);
if (v___x_3050_ == 0)
{
lean_object* v___x_3051_; lean_object* v___x_3052_; 
v___x_3051_ = lean_unsigned_to_nat(1u);
v___x_3052_ = lean_nat_add(v_i_3045_, v___x_3051_);
lean_dec(v_i_3045_);
v_i_3045_ = v___x_3052_;
goto _start;
}
else
{
lean_dec(v_i_3045_);
return v___x_3050_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3054_, lean_object* v_i_3055_, lean_object* v_k_3056_){
_start:
{
uint8_t v_res_3057_; lean_object* v_r_3058_; 
v_res_3057_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3054_, v_i_3055_, v_k_3056_);
lean_dec(v_k_3056_);
lean_dec_ref(v_keys_3054_);
v_r_3058_ = lean_box(v_res_3057_);
return v_r_3058_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3059_, size_t v_x_3060_, lean_object* v_x_3061_){
_start:
{
if (lean_obj_tag(v_x_3059_) == 0)
{
lean_object* v_es_3062_; lean_object* v___x_3063_; size_t v___x_3064_; size_t v___x_3065_; size_t v___x_3066_; lean_object* v_j_3067_; lean_object* v___x_3068_; 
v_es_3062_ = lean_ctor_get(v_x_3059_, 0);
v___x_3063_ = lean_box(2);
v___x_3064_ = ((size_t)5ULL);
v___x_3065_ = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__1);
v___x_3066_ = lean_usize_land(v_x_3060_, v___x_3065_);
v_j_3067_ = lean_usize_to_nat(v___x_3066_);
v___x_3068_ = lean_array_get_borrowed(v___x_3063_, v_es_3062_, v_j_3067_);
lean_dec(v_j_3067_);
switch(lean_obj_tag(v___x_3068_))
{
case 0:
{
lean_object* v_key_3069_; uint8_t v___x_3070_; 
v_key_3069_ = lean_ctor_get(v___x_3068_, 0);
v___x_3070_ = l_Lean_instBEqMVarId_beq(v_x_3061_, v_key_3069_);
return v___x_3070_;
}
case 1:
{
lean_object* v_node_3071_; size_t v___x_3072_; 
v_node_3071_ = lean_ctor_get(v___x_3068_, 0);
v___x_3072_ = lean_usize_shift_right(v_x_3060_, v___x_3064_);
v_x_3059_ = v_node_3071_;
v_x_3060_ = v___x_3072_;
goto _start;
}
default: 
{
uint8_t v___x_3074_; 
v___x_3074_ = 0;
return v___x_3074_;
}
}
}
else
{
lean_object* v_ks_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; 
v_ks_3075_ = lean_ctor_get(v_x_3059_, 0);
v___x_3076_ = lean_unsigned_to_nat(0u);
v___x_3077_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3075_, v___x_3076_, v_x_3061_);
return v___x_3077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3078_, lean_object* v_x_3079_, lean_object* v_x_3080_){
_start:
{
size_t v_x_12606__boxed_3081_; uint8_t v_res_3082_; lean_object* v_r_3083_; 
v_x_12606__boxed_3081_ = lean_unbox_usize(v_x_3079_);
lean_dec(v_x_3079_);
v_res_3082_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3078_, v_x_12606__boxed_3081_, v_x_3080_);
lean_dec(v_x_3080_);
lean_dec_ref(v_x_3078_);
v_r_3083_ = lean_box(v_res_3082_);
return v_r_3083_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3084_, lean_object* v_x_3085_){
_start:
{
uint64_t v___x_3086_; size_t v___x_3087_; uint8_t v___x_3088_; 
v___x_3086_ = l_Lean_instHashableMVarId_hash(v_x_3085_);
v___x_3087_ = lean_uint64_to_usize(v___x_3086_);
v___x_3088_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3084_, v___x_3087_, v_x_3085_);
return v___x_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3089_, lean_object* v_x_3090_){
_start:
{
uint8_t v_res_3091_; lean_object* v_r_3092_; 
v_res_3091_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3089_, v_x_3090_);
lean_dec(v_x_3090_);
lean_dec_ref(v_x_3089_);
v_r_3092_ = lean_box(v_res_3091_);
return v_r_3092_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; lean_object* v_mctx_3097_; lean_object* v_eAssignment_3098_; uint8_t v___x_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3096_ = lean_st_ref_get(v___y_3094_);
v_mctx_3097_ = lean_ctor_get(v___x_3096_, 0);
lean_inc_ref(v_mctx_3097_);
lean_dec(v___x_3096_);
v_eAssignment_3098_ = lean_ctor_get(v_mctx_3097_, 7);
lean_inc_ref(v_eAssignment_3098_);
lean_dec_ref(v_mctx_3097_);
v___x_3099_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3098_, v_mvarId_3093_);
lean_dec_ref(v_eAssignment_3098_);
v___x_3100_ = lean_box(v___x_3099_);
v___x_3101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3101_, 0, v___x_3100_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3102_, lean_object* v___y_3103_, lean_object* v___y_3104_){
_start:
{
lean_object* v_res_3105_; 
v_res_3105_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3102_, v___y_3103_);
lean_dec(v___y_3103_);
lean_dec(v_mvarId_3102_);
return v_res_3105_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; 
v___x_3107_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3108_ = l_Lean_stringToMessageData(v___x_3107_);
return v___x_3108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3109_, uint8_t v___y_3110_, lean_object* v_____r_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___y_3118_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___x_3153_; lean_object* v_a_3154_; uint8_t v___x_3155_; 
v___x_3153_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3109_, v___y_3113_);
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref(v___x_3153_);
v___x_3155_ = lean_unbox(v_a_3154_);
lean_dec(v_a_3154_);
if (v___x_3155_ == 0)
{
v___y_3118_ = v___y_3112_;
v___y_3119_ = v___y_3113_;
v___y_3120_ = v___y_3114_;
v___y_3121_ = v___y_3115_;
goto v___jp_3117_;
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3165_; 
lean_dec(v_mvarId_3109_);
v___x_3156_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3157_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3156_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3165_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3165_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3165_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3163_; 
if (v_isShared_3161_ == 0)
{
v___x_3163_ = v___x_3160_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_a_3158_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
}
v___jp_3117_:
{
lean_object* v___x_3122_; 
v___x_3122_ = l_Lean_Meta_intro1Core(v_mvarId_3109_, v___y_3110_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
if (lean_obj_tag(v___x_3122_) == 0)
{
lean_object* v_a_3123_; lean_object* v_fst_3124_; lean_object* v_snd_3125_; lean_object* v___x_3126_; lean_object* v___x_3127_; 
v_a_3123_ = lean_ctor_get(v___x_3122_, 0);
lean_inc(v_a_3123_);
lean_dec_ref(v___x_3122_);
v_fst_3124_ = lean_ctor_get(v_a_3123_, 0);
lean_inc(v_fst_3124_);
v_snd_3125_ = lean_ctor_get(v_a_3123_, 1);
lean_inc(v_snd_3125_);
lean_dec(v_a_3123_);
v___x_3126_ = lean_box(0);
v___x_3127_ = l_Lean_Meta_substEq(v_snd_3125_, v_fst_3124_, v___x_3126_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
if (lean_obj_tag(v___x_3127_) == 0)
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3136_; 
v_a_3128_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3130_ = v___x_3127_;
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3127_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3136_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3132_; lean_object* v___x_3134_; 
v___x_3132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3132_, 0, v_a_3128_);
if (v_isShared_3131_ == 0)
{
lean_ctor_set(v___x_3130_, 0, v___x_3132_);
v___x_3134_ = v___x_3130_;
goto v_reusejp_3133_;
}
else
{
lean_object* v_reuseFailAlloc_3135_; 
v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3135_, 0, v___x_3132_);
v___x_3134_ = v_reuseFailAlloc_3135_;
goto v_reusejp_3133_;
}
v_reusejp_3133_:
{
return v___x_3134_;
}
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
v_a_3137_ = lean_ctor_get(v___x_3127_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3127_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3127_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3127_);
v___x_3139_ = lean_box(0);
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
v_resetjp_3138_:
{
lean_object* v___x_3142_; 
if (v_isShared_3140_ == 0)
{
v___x_3142_ = v___x_3139_;
goto v_reusejp_3141_;
}
else
{
lean_object* v_reuseFailAlloc_3143_; 
v_reuseFailAlloc_3143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_a_3137_);
v___x_3142_ = v_reuseFailAlloc_3143_;
goto v_reusejp_3141_;
}
v_reusejp_3141_:
{
return v___x_3142_;
}
}
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
v_a_3145_ = lean_ctor_get(v___x_3122_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3122_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3122_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3122_);
v___x_3147_ = lean_box(0);
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
v_resetjp_3146_:
{
lean_object* v___x_3150_; 
if (v_isShared_3148_ == 0)
{
v___x_3150_ = v___x_3147_;
goto v_reusejp_3149_;
}
else
{
lean_object* v_reuseFailAlloc_3151_; 
v_reuseFailAlloc_3151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3151_, 0, v_a_3145_);
v___x_3150_ = v_reuseFailAlloc_3151_;
goto v_reusejp_3149_;
}
v_reusejp_3149_:
{
return v___x_3150_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3166_, lean_object* v___y_3167_, lean_object* v_____r_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_){
_start:
{
uint8_t v___y_12680__boxed_3174_; lean_object* v_res_3175_; 
v___y_12680__boxed_3174_ = lean_unbox(v___y_3167_);
v_res_3175_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3166_, v___y_12680__boxed_3174_, v_____r_3168_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
lean_dec(v___y_3172_);
lean_dec_ref(v___y_3171_);
lean_dec(v___y_3170_);
lean_dec_ref(v___y_3169_);
return v_res_3175_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__2(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3179_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3180_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
v___x_3181_ = l_Lean_Name_append(v___x_3180_, v___x_3179_);
return v___x_3181_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__4(void){
_start:
{
lean_object* v___x_3183_; lean_object* v___x_3184_; 
v___x_3183_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__3));
v___x_3184_ = l_Lean_stringToMessageData(v___x_3183_);
return v___x_3184_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__6(void){
_start:
{
lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3186_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__5));
v___x_3187_ = l_Lean_stringToMessageData(v___x_3186_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3188_, uint8_t v_substLHS_3189_, lean_object* v_a_3190_, lean_object* v_a_3191_, lean_object* v_a_3192_, lean_object* v_a_3193_){
_start:
{
lean_object* v___y_3196_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3214_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
lean_inc(v_mvarId_3188_);
v___x_3215_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3188_, v___x_3214_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v___x_3216_; lean_object* v___f_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
lean_dec_ref(v___x_3215_);
v___x_3216_ = lean_box(v_substLHS_3189_);
lean_inc_n(v_mvarId_3188_, 2);
v___f_3217_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3217_, 0, v_mvarId_3188_);
lean_closure_set(v___f_3217_, 1, v___x_3216_);
v___x_3218_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed), 8, 3);
lean_closure_set(v___x_3218_, 0, lean_box(0));
lean_closure_set(v___x_3218_, 1, v_mvarId_3188_);
lean_closure_set(v___x_3218_, 2, v___f_3217_);
v___x_3219_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3218_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_dec(v_mvarId_3188_);
return v___x_3219_;
}
else
{
lean_object* v_a_3220_; lean_object* v___y_3222_; uint8_t v___y_3226_; uint8_t v___x_3260_; 
v_a_3220_ = lean_ctor_get(v___x_3219_, 0);
lean_inc(v_a_3220_);
v___x_3260_ = l_Lean_Exception_isInterrupt(v_a_3220_);
if (v___x_3260_ == 0)
{
uint8_t v___x_3261_; 
lean_inc(v_a_3220_);
v___x_3261_ = l_Lean_Exception_isRuntime(v_a_3220_);
v___y_3226_ = v___x_3261_;
goto v___jp_3225_;
}
else
{
v___y_3226_ = v___x_3260_;
goto v___jp_3225_;
}
v___jp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_box(0);
lean_inc(v_a_3193_);
lean_inc_ref(v_a_3192_);
lean_inc(v_a_3191_);
lean_inc_ref(v_a_3190_);
v___x_3224_ = lean_apply_6(v___y_3222_, v___x_3223_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, lean_box(0));
v___y_3196_ = v___x_3224_;
goto v___jp_3195_;
}
v___jp_3225_:
{
if (v___y_3226_ == 0)
{
lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3258_; 
v_isSharedCheck_3258_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; 
v_unused_3259_ = lean_ctor_get(v___x_3219_, 0);
lean_dec(v_unused_3259_);
v___x_3228_ = v___x_3219_;
v_isShared_3229_ = v_isSharedCheck_3258_;
goto v_resetjp_3227_;
}
else
{
lean_dec(v___x_3219_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3258_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v_options_3230_; lean_object* v_inheritedTraceOptions_3231_; uint8_t v_hasTrace_3232_; lean_object* v___x_3233_; lean_object* v___f_3234_; 
v_options_3230_ = lean_ctor_get(v_a_3192_, 2);
v_inheritedTraceOptions_3231_ = lean_ctor_get(v_a_3192_, 13);
v_hasTrace_3232_ = lean_ctor_get_uint8(v_options_3230_, sizeof(void*)*1);
v___x_3233_ = lean_box(v___y_3226_);
lean_inc(v_mvarId_3188_);
v___f_3234_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3234_, 0, v_mvarId_3188_);
lean_closure_set(v___f_3234_, 1, v___x_3233_);
if (v_hasTrace_3232_ == 0)
{
lean_del_object(v___x_3228_);
lean_dec(v_a_3220_);
lean_dec(v_mvarId_3188_);
v___y_3222_ = v___f_3234_;
goto v___jp_3221_;
}
else
{
lean_object* v___x_3235_; lean_object* v___x_3236_; uint8_t v___x_3237_; 
v___x_3235_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3236_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__2, &l_Lean_Meta_introSubstEq___closed__2_once, _init_l_Lean_Meta_introSubstEq___closed__2);
v___x_3237_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3231_, v_options_3230_, v___x_3236_);
if (v___x_3237_ == 0)
{
lean_del_object(v___x_3228_);
lean_dec(v_a_3220_);
lean_dec(v_mvarId_3188_);
v___y_3222_ = v___f_3234_;
goto v___jp_3221_;
}
else
{
lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; lean_object* v___x_3242_; lean_object* v___x_3244_; 
lean_dec_ref(v___f_3234_);
v___x_3238_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__4, &l_Lean_Meta_introSubstEq___closed__4_once, _init_l_Lean_Meta_introSubstEq___closed__4);
v___x_3239_ = l_Lean_Exception_toMessageData(v_a_3220_);
v___x_3240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3240_, 0, v___x_3238_);
lean_ctor_set(v___x_3240_, 1, v___x_3239_);
v___x_3241_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__6, &l_Lean_Meta_introSubstEq___closed__6_once, _init_l_Lean_Meta_introSubstEq___closed__6);
v___x_3242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3242_, 0, v___x_3240_);
lean_ctor_set(v___x_3242_, 1, v___x_3241_);
lean_inc(v_mvarId_3188_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 0, v_mvarId_3188_);
v___x_3244_ = v___x_3228_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_mvarId_3188_);
v___x_3244_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
v___x_3245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3245_, 0, v___x_3242_);
lean_ctor_set(v___x_3245_, 1, v___x_3244_);
v___x_3246_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_3235_, v___x_3245_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v_a_3247_; lean_object* v___x_3248_; 
v_a_3247_ = lean_ctor_get(v___x_3246_, 0);
lean_inc(v_a_3247_);
lean_dec_ref(v___x_3246_);
v___x_3248_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3188_, v___y_3226_, v_a_3247_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_);
v___y_3196_ = v___x_3248_;
goto v___jp_3195_;
}
else
{
lean_object* v_a_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3256_; 
lean_dec(v_mvarId_3188_);
v_a_3249_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3251_ = v___x_3246_;
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_a_3249_);
lean_dec(v___x_3246_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3256_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3254_; 
if (v_isShared_3252_ == 0)
{
v___x_3254_ = v___x_3251_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_a_3249_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
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
lean_dec(v_a_3220_);
lean_dec(v_mvarId_3188_);
return v___x_3219_;
}
}
}
}
else
{
lean_object* v_a_3262_; lean_object* v___x_3264_; uint8_t v_isShared_3265_; uint8_t v_isSharedCheck_3269_; 
lean_dec(v_mvarId_3188_);
v_a_3262_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3269_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3269_ == 0)
{
v___x_3264_ = v___x_3215_;
v_isShared_3265_ = v_isSharedCheck_3269_;
goto v_resetjp_3263_;
}
else
{
lean_inc(v_a_3262_);
lean_dec(v___x_3215_);
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
v___jp_3195_:
{
if (lean_obj_tag(v___y_3196_) == 0)
{
lean_object* v_a_3197_; lean_object* v___x_3199_; uint8_t v_isShared_3200_; uint8_t v_isSharedCheck_3205_; 
v_a_3197_ = lean_ctor_get(v___y_3196_, 0);
v_isSharedCheck_3205_ = !lean_is_exclusive(v___y_3196_);
if (v_isSharedCheck_3205_ == 0)
{
v___x_3199_ = v___y_3196_;
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
else
{
lean_inc(v_a_3197_);
lean_dec(v___y_3196_);
v___x_3199_ = lean_box(0);
v_isShared_3200_ = v_isSharedCheck_3205_;
goto v_resetjp_3198_;
}
v_resetjp_3198_:
{
lean_object* v_a_3201_; lean_object* v___x_3203_; 
v_a_3201_ = lean_ctor_get(v_a_3197_, 0);
lean_inc(v_a_3201_);
lean_dec(v_a_3197_);
if (v_isShared_3200_ == 0)
{
lean_ctor_set(v___x_3199_, 0, v_a_3201_);
v___x_3203_ = v___x_3199_;
goto v_reusejp_3202_;
}
else
{
lean_object* v_reuseFailAlloc_3204_; 
v_reuseFailAlloc_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3201_);
v___x_3203_ = v_reuseFailAlloc_3204_;
goto v_reusejp_3202_;
}
v_reusejp_3202_:
{
return v___x_3203_;
}
}
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3208_; uint8_t v_isShared_3209_; uint8_t v_isSharedCheck_3213_; 
v_a_3206_ = lean_ctor_get(v___y_3196_, 0);
v_isSharedCheck_3213_ = !lean_is_exclusive(v___y_3196_);
if (v_isSharedCheck_3213_ == 0)
{
v___x_3208_ = v___y_3196_;
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
else
{
lean_inc(v_a_3206_);
lean_dec(v___y_3196_);
v___x_3208_ = lean_box(0);
v_isShared_3209_ = v_isSharedCheck_3213_;
goto v_resetjp_3207_;
}
v_resetjp_3207_:
{
lean_object* v___x_3211_; 
if (v_isShared_3209_ == 0)
{
v___x_3211_ = v___x_3208_;
goto v_reusejp_3210_;
}
else
{
lean_object* v_reuseFailAlloc_3212_; 
v_reuseFailAlloc_3212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3212_, 0, v_a_3206_);
v___x_3211_ = v_reuseFailAlloc_3212_;
goto v_reusejp_3210_;
}
v_reusejp_3210_:
{
return v___x_3211_;
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
size_t v_x_13044__boxed_3327_; uint8_t v_res_3328_; lean_object* v_r_3329_; 
v_x_13044__boxed_3327_ = lean_unbox_usize(v_x_3325_);
lean_dec(v_x_3325_);
v_res_3328_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3323_, v_x_3324_, v_x_13044__boxed_3327_, v_x_3326_);
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
lean_dec_ref(v___x_3351_);
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
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3392_; 
v_a_3363_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3392_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3392_ == 0)
{
v___x_3365_ = v___x_3353_;
v_isShared_3366_ = v_isSharedCheck_3392_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3353_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3392_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
uint8_t v___y_3368_; uint8_t v___x_3390_; 
v___x_3390_ = l_Lean_Exception_isInterrupt(v_a_3363_);
if (v___x_3390_ == 0)
{
uint8_t v___x_3391_; 
lean_inc(v_a_3363_);
v___x_3391_ = l_Lean_Exception_isRuntime(v_a_3363_);
v___y_3368_ = v___x_3391_;
goto v___jp_3367_;
}
else
{
v___y_3368_ = v___x_3390_;
goto v___jp_3367_;
}
v___jp_3367_:
{
if (v___y_3368_ == 0)
{
lean_object* v___x_3369_; 
lean_del_object(v___x_3365_);
lean_dec(v_a_3363_);
v___x_3369_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3352_, v___y_3347_, v___y_3349_);
lean_dec(v_a_3352_);
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
}
}
}
else
{
lean_object* v_a_3393_; lean_object* v___x_3395_; uint8_t v_isShared_3396_; uint8_t v_isSharedCheck_3400_; 
lean_dec_ref(v_x_3345_);
v_a_3393_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3395_ = v___x_3351_;
v_isShared_3396_ = v_isSharedCheck_3400_;
goto v_resetjp_3394_;
}
else
{
lean_inc(v_a_3393_);
lean_dec(v___x_3351_);
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
lean_dec_ref(v_a_3497_);
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
lean_dec_ref(v_a_3533_);
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
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = l_Lean_LocalDecl_fvarId(v_val_3590_);
lean_dec(v_val_3590_);
lean_inc(v_mvarId_3564_);
v___x_3595_ = l_Lean_Meta_subst_x3f(v_mvarId_3564_, v___x_3594_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3619_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3619_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3619_ == 0)
{
v___x_3598_ = v___x_3595_;
v_isShared_3599_ = v_isSharedCheck_3619_;
goto v_resetjp_3597_;
}
else
{
lean_inc(v_a_3596_);
lean_dec(v___x_3595_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3619_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; 
v___x_3600_ = lean_box(0);
if (lean_obj_tag(v_a_3596_) == 1)
{
lean_object* v___x_3602_; 
lean_del_object(v___x_3578_);
lean_dec(v_mvarId_3564_);
lean_inc_ref(v_a_3596_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v_a_3596_);
v___x_3602_ = v___x_3592_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3596_);
v___x_3602_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3604_; uint8_t v_isShared_3605_; uint8_t v_isSharedCheck_3615_; 
v_isSharedCheck_3615_ = !lean_is_exclusive(v_a_3596_);
if (v_isSharedCheck_3615_ == 0)
{
lean_object* v_unused_3616_; 
v_unused_3616_ = lean_ctor_get(v_a_3596_, 0);
lean_dec(v_unused_3616_);
v___x_3604_ = v_a_3596_;
v_isShared_3605_ = v_isSharedCheck_3615_;
goto v_resetjp_3603_;
}
else
{
lean_dec(v_a_3596_);
v___x_3604_ = lean_box(0);
v_isShared_3605_ = v_isSharedCheck_3615_;
goto v_resetjp_3603_;
}
v_resetjp_3603_:
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3602_);
lean_ctor_set(v___x_3606_, 1, v___x_3600_);
if (v_isShared_3605_ == 0)
{
lean_ctor_set_tag(v___x_3604_, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3606_);
v___x_3608_ = v___x_3604_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3614_; 
v_reuseFailAlloc_3614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3614_, 0, v___x_3606_);
v___x_3608_ = v_reuseFailAlloc_3614_;
goto v_reusejp_3607_;
}
v_reusejp_3607_:
{
lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3612_; 
v___x_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3608_);
v___x_3610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3609_);
lean_ctor_set(v___x_3610_, 1, v_snd_3576_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set(v___x_3598_, 0, v___x_3610_);
v___x_3612_ = v___x_3598_;
goto v_reusejp_3611_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v___x_3610_);
v___x_3612_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3611_;
}
v_reusejp_3611_:
{
return v___x_3612_;
}
}
}
}
}
else
{
lean_object* v___x_3618_; 
lean_del_object(v___x_3598_);
lean_dec(v_a_3596_);
lean_del_object(v___x_3592_);
lean_dec(v_snd_3576_);
v___x_3618_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3582_ = v___x_3618_;
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
v_a_3620_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3627_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3627_ == 0)
{
v___x_3622_ = v___x_3595_;
v_isShared_3623_ = v_isSharedCheck_3627_;
goto v_resetjp_3621_;
}
else
{
lean_inc(v_a_3620_);
lean_dec(v___x_3595_);
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
lean_object* v___x_3674_; lean_object* v___x_3675_; 
v___x_3674_ = l_Lean_LocalDecl_fvarId(v_val_3670_);
lean_dec(v_val_3670_);
lean_inc(v_mvarId_3644_);
v___x_3675_ = l_Lean_Meta_subst_x3f(v_mvarId_3644_, v___x_3674_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3675_) == 0)
{
lean_object* v_a_3676_; lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3699_; 
v_a_3676_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3678_ = v___x_3675_;
v_isShared_3679_ = v_isSharedCheck_3699_;
goto v_resetjp_3677_;
}
else
{
lean_inc(v_a_3676_);
lean_dec(v___x_3675_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3699_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; 
v___x_3680_ = lean_box(0);
if (lean_obj_tag(v_a_3676_) == 1)
{
lean_object* v___x_3682_; 
lean_del_object(v___x_3658_);
lean_dec(v_mvarId_3644_);
lean_inc_ref(v_a_3676_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v_a_3676_);
v___x_3682_ = v___x_3672_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3697_; 
v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3676_);
v___x_3682_ = v_reuseFailAlloc_3697_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_3695_; 
v_isSharedCheck_3695_ = !lean_is_exclusive(v_a_3676_);
if (v_isSharedCheck_3695_ == 0)
{
lean_object* v_unused_3696_; 
v_unused_3696_ = lean_ctor_get(v_a_3676_, 0);
lean_dec(v_unused_3696_);
v___x_3684_ = v_a_3676_;
v_isShared_3685_ = v_isSharedCheck_3695_;
goto v_resetjp_3683_;
}
else
{
lean_dec(v_a_3676_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_3695_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3682_);
lean_ctor_set(v___x_3686_, 1, v___x_3680_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set_tag(v___x_3684_, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3686_);
v___x_3688_ = v___x_3684_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v___x_3686_);
v___x_3688_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3687_;
}
v_reusejp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3690_; lean_object* v___x_3692_; 
v___x_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3689_, 0, v___x_3688_);
v___x_3690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3690_, 0, v___x_3689_);
lean_ctor_set(v___x_3690_, 1, v_snd_3656_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set(v___x_3678_, 0, v___x_3690_);
v___x_3692_ = v___x_3678_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3690_);
v___x_3692_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3691_;
}
v_reusejp_3691_:
{
return v___x_3692_;
}
}
}
}
}
else
{
lean_object* v___x_3698_; 
lean_del_object(v___x_3678_);
lean_dec(v_a_3676_);
lean_del_object(v___x_3672_);
lean_dec(v_snd_3656_);
v___x_3698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3662_ = v___x_3698_;
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
v_a_3700_ = lean_ctor_get(v___x_3675_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3675_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3675_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3675_);
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
lean_object* v_cs_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3767_; 
v_cs_3733_ = lean_ctor_get(v_n_3726_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_n_3726_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3735_ = v_n_3726_;
v_isShared_3736_ = v_isSharedCheck_3767_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_cs_3733_);
lean_dec(v_n_3726_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3767_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; size_t v_sz_3739_; size_t v___x_3740_; lean_object* v___x_3741_; 
v___x_3737_ = lean_box(0);
v___x_3738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3738_, 0, v___x_3737_);
lean_ctor_set(v___x_3738_, 1, v_b_3727_);
v_sz_3739_ = lean_array_size(v_cs_3733_);
v___x_3740_ = ((size_t)0ULL);
v___x_3741_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3724_, v_mvarId_3725_, v_cs_3733_, v_sz_3739_, v___x_3740_, v___x_3738_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
lean_dec_ref(v_cs_3733_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3758_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3744_ = v___x_3741_;
v_isShared_3745_ = v_isSharedCheck_3758_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3758_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v_fst_3746_; 
v_fst_3746_ = lean_ctor_get(v_a_3742_, 0);
if (lean_obj_tag(v_fst_3746_) == 0)
{
lean_object* v_snd_3747_; lean_object* v___x_3749_; 
v_snd_3747_ = lean_ctor_get(v_a_3742_, 1);
lean_inc(v_snd_3747_);
lean_dec(v_a_3742_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set_tag(v___x_3735_, 1);
lean_ctor_set(v___x_3735_, 0, v_snd_3747_);
v___x_3749_ = v___x_3735_;
goto v_reusejp_3748_;
}
else
{
lean_object* v_reuseFailAlloc_3753_; 
v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_snd_3747_);
v___x_3749_ = v_reuseFailAlloc_3753_;
goto v_reusejp_3748_;
}
v_reusejp_3748_:
{
lean_object* v___x_3751_; 
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v___x_3749_);
v___x_3751_ = v___x_3744_;
goto v_reusejp_3750_;
}
else
{
lean_object* v_reuseFailAlloc_3752_; 
v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
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
lean_object* v_val_3754_; lean_object* v___x_3756_; 
lean_inc_ref(v_fst_3746_);
lean_dec(v_a_3742_);
lean_del_object(v___x_3735_);
v_val_3754_ = lean_ctor_get(v_fst_3746_, 0);
lean_inc(v_val_3754_);
lean_dec_ref(v_fst_3746_);
if (v_isShared_3745_ == 0)
{
lean_ctor_set(v___x_3744_, 0, v_val_3754_);
v___x_3756_ = v___x_3744_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_val_3754_);
v___x_3756_ = v_reuseFailAlloc_3757_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
return v___x_3756_;
}
}
}
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_del_object(v___x_3735_);
v_a_3759_ = lean_ctor_get(v___x_3741_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3741_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3741_);
v___x_3761_ = lean_box(0);
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
v_resetjp_3760_:
{
lean_object* v___x_3764_; 
if (v_isShared_3762_ == 0)
{
v___x_3764_ = v___x_3761_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v_a_3759_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
return v___x_3764_;
}
}
}
}
}
else
{
lean_object* v_vs_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3802_; 
v_vs_3768_ = lean_ctor_get(v_n_3726_, 0);
v_isSharedCheck_3802_ = !lean_is_exclusive(v_n_3726_);
if (v_isSharedCheck_3802_ == 0)
{
v___x_3770_ = v_n_3726_;
v_isShared_3771_ = v_isSharedCheck_3802_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_vs_3768_);
lean_dec(v_n_3726_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3802_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3772_; lean_object* v___x_3773_; size_t v_sz_3774_; size_t v___x_3775_; lean_object* v___x_3776_; 
v___x_3772_ = lean_box(0);
v___x_3773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3772_);
lean_ctor_set(v___x_3773_, 1, v_b_3727_);
v_sz_3774_ = lean_array_size(v_vs_3768_);
v___x_3775_ = ((size_t)0ULL);
v___x_3776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3725_, v_vs_3768_, v_sz_3774_, v___x_3775_, v___x_3773_, v___y_3728_, v___y_3729_, v___y_3730_, v___y_3731_);
lean_dec_ref(v_vs_3768_);
if (lean_obj_tag(v___x_3776_) == 0)
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3793_; 
v_a_3777_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3779_ = v___x_3776_;
v_isShared_3780_ = v_isSharedCheck_3793_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3776_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3793_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v_fst_3781_; 
v_fst_3781_ = lean_ctor_get(v_a_3777_, 0);
if (lean_obj_tag(v_fst_3781_) == 0)
{
lean_object* v_snd_3782_; lean_object* v___x_3784_; 
v_snd_3782_ = lean_ctor_get(v_a_3777_, 1);
lean_inc(v_snd_3782_);
lean_dec(v_a_3777_);
if (v_isShared_3771_ == 0)
{
lean_ctor_set(v___x_3770_, 0, v_snd_3782_);
v___x_3784_ = v___x_3770_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_snd_3782_);
v___x_3784_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
lean_object* v___x_3786_; 
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v___x_3784_);
v___x_3786_ = v___x_3779_;
goto v_reusejp_3785_;
}
else
{
lean_object* v_reuseFailAlloc_3787_; 
v_reuseFailAlloc_3787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3787_, 0, v___x_3784_);
v___x_3786_ = v_reuseFailAlloc_3787_;
goto v_reusejp_3785_;
}
v_reusejp_3785_:
{
return v___x_3786_;
}
}
}
else
{
lean_object* v_val_3789_; lean_object* v___x_3791_; 
lean_inc_ref(v_fst_3781_);
lean_dec(v_a_3777_);
lean_del_object(v___x_3770_);
v_val_3789_ = lean_ctor_get(v_fst_3781_, 0);
lean_inc(v_val_3789_);
lean_dec_ref(v_fst_3781_);
if (v_isShared_3780_ == 0)
{
lean_ctor_set(v___x_3779_, 0, v_val_3789_);
v___x_3791_ = v___x_3779_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3792_; 
v_reuseFailAlloc_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3792_, 0, v_val_3789_);
v___x_3791_ = v_reuseFailAlloc_3792_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
return v___x_3791_;
}
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
lean_del_object(v___x_3770_);
v_a_3794_ = lean_ctor_get(v___x_3776_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3776_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3776_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3776_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_init_3803_, lean_object* v_mvarId_3804_, lean_object* v_as_3805_, size_t v_sz_3806_, size_t v_i_3807_, lean_object* v_b_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_){
_start:
{
uint8_t v___x_3814_; 
v___x_3814_ = lean_usize_dec_lt(v_i_3807_, v_sz_3806_);
if (v___x_3814_ == 0)
{
lean_object* v___x_3815_; 
lean_dec(v_mvarId_3804_);
v___x_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3815_, 0, v_b_3808_);
return v___x_3815_;
}
else
{
lean_object* v_snd_3816_; lean_object* v___x_3818_; uint8_t v_isShared_3819_; uint8_t v_isSharedCheck_3850_; 
v_snd_3816_ = lean_ctor_get(v_b_3808_, 1);
v_isSharedCheck_3850_ = !lean_is_exclusive(v_b_3808_);
if (v_isSharedCheck_3850_ == 0)
{
lean_object* v_unused_3851_; 
v_unused_3851_ = lean_ctor_get(v_b_3808_, 0);
lean_dec(v_unused_3851_);
v___x_3818_ = v_b_3808_;
v_isShared_3819_ = v_isSharedCheck_3850_;
goto v_resetjp_3817_;
}
else
{
lean_inc(v_snd_3816_);
lean_dec(v_b_3808_);
v___x_3818_ = lean_box(0);
v_isShared_3819_ = v_isSharedCheck_3850_;
goto v_resetjp_3817_;
}
v_resetjp_3817_:
{
lean_object* v_a_3820_; lean_object* v___x_3821_; 
v_a_3820_ = lean_array_uget_borrowed(v_as_3805_, v_i_3807_);
lean_inc(v_snd_3816_);
lean_inc(v_a_3820_);
lean_inc(v_mvarId_3804_);
v___x_3821_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3803_, v_mvarId_3804_, v_a_3820_, v_snd_3816_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
if (lean_obj_tag(v___x_3821_) == 0)
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3841_; 
v_a_3822_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3841_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3841_ == 0)
{
v___x_3824_ = v___x_3821_;
v_isShared_3825_ = v_isSharedCheck_3841_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3821_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3841_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
if (lean_obj_tag(v_a_3822_) == 0)
{
lean_object* v___x_3826_; lean_object* v___x_3828_; 
lean_dec(v_mvarId_3804_);
v___x_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3826_, 0, v_a_3822_);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 0, v___x_3826_);
v___x_3828_ = v___x_3818_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v___x_3826_);
lean_ctor_set(v_reuseFailAlloc_3832_, 1, v_snd_3816_);
v___x_3828_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
lean_object* v___x_3830_; 
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
}
else
{
lean_object* v_a_3833_; lean_object* v___x_3834_; lean_object* v___x_3836_; 
lean_del_object(v___x_3824_);
lean_dec(v_snd_3816_);
v_a_3833_ = lean_ctor_get(v_a_3822_, 0);
lean_inc(v_a_3833_);
lean_dec_ref(v_a_3822_);
v___x_3834_ = lean_box(0);
if (v_isShared_3819_ == 0)
{
lean_ctor_set(v___x_3818_, 1, v_a_3833_);
lean_ctor_set(v___x_3818_, 0, v___x_3834_);
v___x_3836_ = v___x_3818_;
goto v_reusejp_3835_;
}
else
{
lean_object* v_reuseFailAlloc_3840_; 
v_reuseFailAlloc_3840_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3840_, 0, v___x_3834_);
lean_ctor_set(v_reuseFailAlloc_3840_, 1, v_a_3833_);
v___x_3836_ = v_reuseFailAlloc_3840_;
goto v_reusejp_3835_;
}
v_reusejp_3835_:
{
size_t v___x_3837_; size_t v___x_3838_; 
v___x_3837_ = ((size_t)1ULL);
v___x_3838_ = lean_usize_add(v_i_3807_, v___x_3837_);
v_i_3807_ = v___x_3838_;
v_b_3808_ = v___x_3836_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3842_; lean_object* v___x_3844_; uint8_t v_isShared_3845_; uint8_t v_isSharedCheck_3849_; 
lean_del_object(v___x_3818_);
lean_dec(v_snd_3816_);
lean_dec(v_mvarId_3804_);
v_a_3842_ = lean_ctor_get(v___x_3821_, 0);
v_isSharedCheck_3849_ = !lean_is_exclusive(v___x_3821_);
if (v_isSharedCheck_3849_ == 0)
{
v___x_3844_ = v___x_3821_;
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
else
{
lean_inc(v_a_3842_);
lean_dec(v___x_3821_);
v___x_3844_ = lean_box(0);
v_isShared_3845_ = v_isSharedCheck_3849_;
goto v_resetjp_3843_;
}
v_resetjp_3843_:
{
lean_object* v___x_3847_; 
if (v_isShared_3845_ == 0)
{
v___x_3847_ = v___x_3844_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v_a_3842_);
v___x_3847_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
return v___x_3847_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3852_, lean_object* v_mvarId_3853_, lean_object* v_as_3854_, lean_object* v_sz_3855_, lean_object* v_i_3856_, lean_object* v_b_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
size_t v_sz_boxed_3863_; size_t v_i_boxed_3864_; lean_object* v_res_3865_; 
v_sz_boxed_3863_ = lean_unbox_usize(v_sz_3855_);
lean_dec(v_sz_3855_);
v_i_boxed_3864_ = lean_unbox_usize(v_i_3856_);
lean_dec(v_i_3856_);
v_res_3865_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3852_, v_mvarId_3853_, v_as_3854_, v_sz_boxed_3863_, v_i_boxed_3864_, v_b_3857_, v___y_3858_, v___y_3859_, v___y_3860_, v___y_3861_);
lean_dec(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec(v___y_3859_);
lean_dec_ref(v___y_3858_);
lean_dec_ref(v_as_3854_);
lean_dec_ref(v_init_3852_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_init_3866_, lean_object* v_mvarId_3867_, lean_object* v_n_3868_, lean_object* v_b_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_, lean_object* v___y_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_){
_start:
{
lean_object* v_res_3875_; 
v_res_3875_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3866_, v_mvarId_3867_, v_n_3868_, v_b_3869_, v___y_3870_, v___y_3871_, v___y_3872_, v___y_3873_);
lean_dec(v___y_3873_);
lean_dec_ref(v___y_3872_);
lean_dec(v___y_3871_);
lean_dec_ref(v___y_3870_);
lean_dec_ref(v_init_3866_);
return v_res_3875_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3879_, lean_object* v_as_3880_, size_t v_sz_3881_, size_t v_i_3882_, lean_object* v_b_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
uint8_t v___x_3889_; 
v___x_3889_ = lean_usize_dec_lt(v_i_3882_, v_sz_3881_);
if (v___x_3889_ == 0)
{
lean_object* v___x_3890_; 
lean_dec(v_mvarId_3879_);
v___x_3890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3890_, 0, v_b_3883_);
return v___x_3890_;
}
else
{
lean_object* v_snd_3891_; lean_object* v___x_3893_; uint8_t v_isShared_3894_; uint8_t v_isSharedCheck_3943_; 
v_snd_3891_ = lean_ctor_get(v_b_3883_, 1);
v_isSharedCheck_3943_ = !lean_is_exclusive(v_b_3883_);
if (v_isSharedCheck_3943_ == 0)
{
lean_object* v_unused_3944_; 
v_unused_3944_ = lean_ctor_get(v_b_3883_, 0);
lean_dec(v_unused_3944_);
v___x_3893_ = v_b_3883_;
v_isShared_3894_ = v_isSharedCheck_3943_;
goto v_resetjp_3892_;
}
else
{
lean_inc(v_snd_3891_);
lean_dec(v_b_3883_);
v___x_3893_ = lean_box(0);
v_isShared_3894_ = v_isSharedCheck_3943_;
goto v_resetjp_3892_;
}
v_resetjp_3892_:
{
lean_object* v___x_3895_; lean_object* v_a_3897_; lean_object* v_a_3904_; 
v___x_3895_ = lean_box(0);
v_a_3904_ = lean_array_uget(v_as_3880_, v_i_3882_);
if (lean_obj_tag(v_a_3904_) == 0)
{
v_a_3897_ = v_snd_3891_;
goto v___jp_3896_;
}
else
{
lean_object* v_val_3905_; lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3942_; 
v_val_3905_ = lean_ctor_get(v_a_3904_, 0);
v_isSharedCheck_3942_ = !lean_is_exclusive(v_a_3904_);
if (v_isSharedCheck_3942_ == 0)
{
v___x_3907_ = v_a_3904_;
v_isShared_3908_ = v_isSharedCheck_3942_;
goto v_resetjp_3906_;
}
else
{
lean_inc(v_val_3905_);
lean_dec(v_a_3904_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3942_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = l_Lean_LocalDecl_fvarId(v_val_3905_);
lean_dec(v_val_3905_);
lean_inc(v_mvarId_3879_);
v___x_3910_ = l_Lean_Meta_subst_x3f(v_mvarId_3879_, v___x_3909_, v___y_3884_, v___y_3885_, v___y_3886_, v___y_3887_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3913_; uint8_t v_isShared_3914_; uint8_t v_isSharedCheck_3933_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3913_ = v___x_3910_;
v_isShared_3914_ = v_isSharedCheck_3933_;
goto v_resetjp_3912_;
}
else
{
lean_inc(v_a_3911_);
lean_dec(v___x_3910_);
v___x_3913_ = lean_box(0);
v_isShared_3914_ = v_isSharedCheck_3933_;
goto v_resetjp_3912_;
}
v_resetjp_3912_:
{
lean_object* v___x_3915_; 
v___x_3915_ = lean_box(0);
if (lean_obj_tag(v_a_3911_) == 1)
{
lean_object* v___x_3917_; 
lean_del_object(v___x_3893_);
lean_dec(v_mvarId_3879_);
lean_inc_ref(v_a_3911_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set(v___x_3907_, 0, v_a_3911_);
v___x_3917_ = v___x_3907_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3911_);
v___x_3917_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3929_; 
v_isSharedCheck_3929_ = !lean_is_exclusive(v_a_3911_);
if (v_isSharedCheck_3929_ == 0)
{
lean_object* v_unused_3930_; 
v_unused_3930_ = lean_ctor_get(v_a_3911_, 0);
lean_dec(v_unused_3930_);
v___x_3919_ = v_a_3911_;
v_isShared_3920_ = v_isSharedCheck_3929_;
goto v_resetjp_3918_;
}
else
{
lean_dec(v_a_3911_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3929_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3921_; lean_object* v___x_3923_; 
v___x_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3921_, 0, v___x_3917_);
lean_ctor_set(v___x_3921_, 1, v___x_3915_);
if (v_isShared_3920_ == 0)
{
lean_ctor_set(v___x_3919_, 0, v___x_3921_);
v___x_3923_ = v___x_3919_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3921_);
v___x_3923_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
lean_object* v___x_3924_; lean_object* v___x_3926_; 
v___x_3924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
lean_ctor_set(v___x_3924_, 1, v_snd_3891_);
if (v_isShared_3914_ == 0)
{
lean_ctor_set(v___x_3913_, 0, v___x_3924_);
v___x_3926_ = v___x_3913_;
goto v_reusejp_3925_;
}
else
{
lean_object* v_reuseFailAlloc_3927_; 
v_reuseFailAlloc_3927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3927_, 0, v___x_3924_);
v___x_3926_ = v_reuseFailAlloc_3927_;
goto v_reusejp_3925_;
}
v_reusejp_3925_:
{
return v___x_3926_;
}
}
}
}
}
else
{
lean_object* v___x_3932_; 
lean_del_object(v___x_3913_);
lean_dec(v_a_3911_);
lean_del_object(v___x_3907_);
lean_dec(v_snd_3891_);
v___x_3932_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3897_ = v___x_3932_;
goto v___jp_3896_;
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_del_object(v___x_3907_);
lean_del_object(v___x_3893_);
lean_dec(v_snd_3891_);
lean_dec(v_mvarId_3879_);
v_a_3934_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3910_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3910_);
v___x_3936_ = lean_box(0);
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
v_resetjp_3935_:
{
lean_object* v___x_3939_; 
if (v_isShared_3937_ == 0)
{
v___x_3939_ = v___x_3936_;
goto v_reusejp_3938_;
}
else
{
lean_object* v_reuseFailAlloc_3940_; 
v_reuseFailAlloc_3940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3940_, 0, v_a_3934_);
v___x_3939_ = v_reuseFailAlloc_3940_;
goto v_reusejp_3938_;
}
v_reusejp_3938_:
{
return v___x_3939_;
}
}
}
}
}
v___jp_3896_:
{
lean_object* v___x_3899_; 
if (v_isShared_3894_ == 0)
{
lean_ctor_set(v___x_3893_, 1, v_a_3897_);
lean_ctor_set(v___x_3893_, 0, v___x_3895_);
v___x_3899_ = v___x_3893_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3903_; 
v_reuseFailAlloc_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3903_, 0, v___x_3895_);
lean_ctor_set(v_reuseFailAlloc_3903_, 1, v_a_3897_);
v___x_3899_ = v_reuseFailAlloc_3903_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
size_t v___x_3900_; size_t v___x_3901_; 
v___x_3900_ = ((size_t)1ULL);
v___x_3901_ = lean_usize_add(v_i_3882_, v___x_3900_);
v_i_3882_ = v___x_3901_;
v_b_3883_ = v___x_3899_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3945_, lean_object* v_as_3946_, lean_object* v_sz_3947_, lean_object* v_i_3948_, lean_object* v_b_3949_, lean_object* v___y_3950_, lean_object* v___y_3951_, lean_object* v___y_3952_, lean_object* v___y_3953_, lean_object* v___y_3954_){
_start:
{
size_t v_sz_boxed_3955_; size_t v_i_boxed_3956_; lean_object* v_res_3957_; 
v_sz_boxed_3955_ = lean_unbox_usize(v_sz_3947_);
lean_dec(v_sz_3947_);
v_i_boxed_3956_ = lean_unbox_usize(v_i_3948_);
lean_dec(v_i_3948_);
v_res_3957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3945_, v_as_3946_, v_sz_boxed_3955_, v_i_boxed_3956_, v_b_3949_, v___y_3950_, v___y_3951_, v___y_3952_, v___y_3953_);
lean_dec(v___y_3953_);
lean_dec_ref(v___y_3952_);
lean_dec(v___y_3951_);
lean_dec_ref(v___y_3950_);
lean_dec_ref(v_as_3946_);
return v_res_3957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_3958_, lean_object* v_as_3959_, size_t v_sz_3960_, size_t v_i_3961_, lean_object* v_b_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_){
_start:
{
uint8_t v___x_3968_; 
v___x_3968_ = lean_usize_dec_lt(v_i_3961_, v_sz_3960_);
if (v___x_3968_ == 0)
{
lean_object* v___x_3969_; 
lean_dec(v_mvarId_3958_);
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v_b_3962_);
return v___x_3969_;
}
else
{
lean_object* v_snd_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_4022_; 
v_snd_3970_ = lean_ctor_get(v_b_3962_, 1);
v_isSharedCheck_4022_ = !lean_is_exclusive(v_b_3962_);
if (v_isSharedCheck_4022_ == 0)
{
lean_object* v_unused_4023_; 
v_unused_4023_ = lean_ctor_get(v_b_3962_, 0);
lean_dec(v_unused_4023_);
v___x_3972_ = v_b_3962_;
v_isShared_3973_ = v_isSharedCheck_4022_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_snd_3970_);
lean_dec(v_b_3962_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_4022_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v_a_3976_; lean_object* v_a_3983_; 
v___x_3974_ = lean_box(0);
v_a_3983_ = lean_array_uget(v_as_3959_, v_i_3961_);
if (lean_obj_tag(v_a_3983_) == 0)
{
v_a_3976_ = v_snd_3970_;
goto v___jp_3975_;
}
else
{
lean_object* v_val_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_4021_; 
v_val_3984_ = lean_ctor_get(v_a_3983_, 0);
v_isSharedCheck_4021_ = !lean_is_exclusive(v_a_3983_);
if (v_isSharedCheck_4021_ == 0)
{
v___x_3986_ = v_a_3983_;
v_isShared_3987_ = v_isSharedCheck_4021_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_val_3984_);
lean_dec(v_a_3983_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_4021_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3988_; lean_object* v___x_3989_; 
v___x_3988_ = l_Lean_LocalDecl_fvarId(v_val_3984_);
lean_dec(v_val_3984_);
lean_inc(v_mvarId_3958_);
v___x_3989_ = l_Lean_Meta_subst_x3f(v_mvarId_3958_, v___x_3988_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
if (lean_obj_tag(v___x_3989_) == 0)
{
lean_object* v_a_3990_; lean_object* v___x_3992_; uint8_t v_isShared_3993_; uint8_t v_isSharedCheck_4012_; 
v_a_3990_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4012_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4012_ == 0)
{
v___x_3992_ = v___x_3989_;
v_isShared_3993_ = v_isSharedCheck_4012_;
goto v_resetjp_3991_;
}
else
{
lean_inc(v_a_3990_);
lean_dec(v___x_3989_);
v___x_3992_ = lean_box(0);
v_isShared_3993_ = v_isSharedCheck_4012_;
goto v_resetjp_3991_;
}
v_resetjp_3991_:
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_box(0);
if (lean_obj_tag(v_a_3990_) == 1)
{
lean_object* v___x_3996_; 
lean_del_object(v___x_3972_);
lean_dec(v_mvarId_3958_);
lean_inc_ref(v_a_3990_);
if (v_isShared_3987_ == 0)
{
lean_ctor_set(v___x_3986_, 0, v_a_3990_);
v___x_3996_ = v___x_3986_;
goto v_reusejp_3995_;
}
else
{
lean_object* v_reuseFailAlloc_4010_; 
v_reuseFailAlloc_4010_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4010_, 0, v_a_3990_);
v___x_3996_ = v_reuseFailAlloc_4010_;
goto v_reusejp_3995_;
}
v_reusejp_3995_:
{
lean_object* v___x_3998_; uint8_t v_isShared_3999_; uint8_t v_isSharedCheck_4008_; 
v_isSharedCheck_4008_ = !lean_is_exclusive(v_a_3990_);
if (v_isSharedCheck_4008_ == 0)
{
lean_object* v_unused_4009_; 
v_unused_4009_ = lean_ctor_get(v_a_3990_, 0);
lean_dec(v_unused_4009_);
v___x_3998_ = v_a_3990_;
v_isShared_3999_ = v_isSharedCheck_4008_;
goto v_resetjp_3997_;
}
else
{
lean_dec(v_a_3990_);
v___x_3998_ = lean_box(0);
v_isShared_3999_ = v_isSharedCheck_4008_;
goto v_resetjp_3997_;
}
v_resetjp_3997_:
{
lean_object* v___x_4000_; lean_object* v___x_4002_; 
v___x_4000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4000_, 0, v___x_3996_);
lean_ctor_set(v___x_4000_, 1, v___x_3994_);
if (v_isShared_3999_ == 0)
{
lean_ctor_set(v___x_3998_, 0, v___x_4000_);
v___x_4002_ = v___x_3998_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_4000_);
v___x_4002_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
lean_object* v___x_4003_; lean_object* v___x_4005_; 
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
lean_ctor_set(v___x_4003_, 1, v_snd_3970_);
if (v_isShared_3993_ == 0)
{
lean_ctor_set(v___x_3992_, 0, v___x_4003_);
v___x_4005_ = v___x_3992_;
goto v_reusejp_4004_;
}
else
{
lean_object* v_reuseFailAlloc_4006_; 
v_reuseFailAlloc_4006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4006_, 0, v___x_4003_);
v___x_4005_ = v_reuseFailAlloc_4006_;
goto v_reusejp_4004_;
}
v_reusejp_4004_:
{
return v___x_4005_;
}
}
}
}
}
else
{
lean_object* v___x_4011_; 
lean_del_object(v___x_3992_);
lean_dec(v_a_3990_);
lean_del_object(v___x_3986_);
lean_dec(v_snd_3970_);
v___x_4011_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3976_ = v___x_4011_;
goto v___jp_3975_;
}
}
}
else
{
lean_object* v_a_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4020_; 
lean_del_object(v___x_3986_);
lean_del_object(v___x_3972_);
lean_dec(v_snd_3970_);
lean_dec(v_mvarId_3958_);
v_a_4013_ = lean_ctor_get(v___x_3989_, 0);
v_isSharedCheck_4020_ = !lean_is_exclusive(v___x_3989_);
if (v_isSharedCheck_4020_ == 0)
{
v___x_4015_ = v___x_3989_;
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_a_4013_);
lean_dec(v___x_3989_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4020_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v___x_4018_; 
if (v_isShared_4016_ == 0)
{
v___x_4018_ = v___x_4015_;
goto v_reusejp_4017_;
}
else
{
lean_object* v_reuseFailAlloc_4019_; 
v_reuseFailAlloc_4019_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4019_, 0, v_a_4013_);
v___x_4018_ = v_reuseFailAlloc_4019_;
goto v_reusejp_4017_;
}
v_reusejp_4017_:
{
return v___x_4018_;
}
}
}
}
}
v___jp_3975_:
{
lean_object* v___x_3978_; 
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 1, v_a_3976_);
lean_ctor_set(v___x_3972_, 0, v___x_3974_);
v___x_3978_ = v___x_3972_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3982_; 
v_reuseFailAlloc_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3982_, 0, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_3982_, 1, v_a_3976_);
v___x_3978_ = v_reuseFailAlloc_3982_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
size_t v___x_3979_; size_t v___x_3980_; lean_object* v___x_3981_; 
v___x_3979_ = ((size_t)1ULL);
v___x_3980_ = lean_usize_add(v_i_3961_, v___x_3979_);
v___x_3981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3958_, v_as_3959_, v_sz_3960_, v___x_3980_, v___x_3978_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
return v___x_3981_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_4024_, lean_object* v_as_4025_, lean_object* v_sz_4026_, lean_object* v_i_4027_, lean_object* v_b_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
size_t v_sz_boxed_4034_; size_t v_i_boxed_4035_; lean_object* v_res_4036_; 
v_sz_boxed_4034_ = lean_unbox_usize(v_sz_4026_);
lean_dec(v_sz_4026_);
v_i_boxed_4035_ = lean_unbox_usize(v_i_4027_);
lean_dec(v_i_4027_);
v_res_4036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4024_, v_as_4025_, v_sz_boxed_4034_, v_i_boxed_4035_, v_b_4028_, v___y_4029_, v___y_4030_, v___y_4031_, v___y_4032_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
lean_dec(v___y_4030_);
lean_dec_ref(v___y_4029_);
lean_dec_ref(v_as_4025_);
return v_res_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4037_, lean_object* v_t_4038_, lean_object* v_init_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_root_4045_; lean_object* v_tail_4046_; lean_object* v___x_4047_; 
v_root_4045_ = lean_ctor_get(v_t_4038_, 0);
lean_inc_ref(v_root_4045_);
v_tail_4046_ = lean_ctor_get(v_t_4038_, 1);
lean_inc_ref(v_tail_4046_);
lean_dec_ref(v_t_4038_);
lean_inc(v_mvarId_4037_);
lean_inc_ref(v_init_4039_);
v___x_4047_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_4039_, v_mvarId_4037_, v_root_4045_, v_init_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec_ref(v_init_4039_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4084_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4084_ == 0)
{
v___x_4050_ = v___x_4047_;
v_isShared_4051_ = v_isSharedCheck_4084_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4047_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4084_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
if (lean_obj_tag(v_a_4048_) == 0)
{
lean_object* v_a_4052_; lean_object* v___x_4054_; 
lean_dec_ref(v_tail_4046_);
lean_dec(v_mvarId_4037_);
v_a_4052_ = lean_ctor_get(v_a_4048_, 0);
lean_inc(v_a_4052_);
lean_dec_ref(v_a_4048_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v_a_4052_);
v___x_4054_ = v___x_4050_;
goto v_reusejp_4053_;
}
else
{
lean_object* v_reuseFailAlloc_4055_; 
v_reuseFailAlloc_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4052_);
v___x_4054_ = v_reuseFailAlloc_4055_;
goto v_reusejp_4053_;
}
v_reusejp_4053_:
{
return v___x_4054_;
}
}
else
{
lean_object* v_a_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; size_t v_sz_4059_; size_t v___x_4060_; lean_object* v___x_4061_; 
lean_del_object(v___x_4050_);
v_a_4056_ = lean_ctor_get(v_a_4048_, 0);
lean_inc(v_a_4056_);
lean_dec_ref(v_a_4048_);
v___x_4057_ = lean_box(0);
v___x_4058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4058_, 0, v___x_4057_);
lean_ctor_set(v___x_4058_, 1, v_a_4056_);
v_sz_4059_ = lean_array_size(v_tail_4046_);
v___x_4060_ = ((size_t)0ULL);
v___x_4061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4037_, v_tail_4046_, v_sz_4059_, v___x_4060_, v___x_4058_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec_ref(v_tail_4046_);
if (lean_obj_tag(v___x_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4075_; 
v_a_4062_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4075_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4075_ == 0)
{
v___x_4064_ = v___x_4061_;
v_isShared_4065_ = v_isSharedCheck_4075_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4061_);
v___x_4064_ = lean_box(0);
v_isShared_4065_ = v_isSharedCheck_4075_;
goto v_resetjp_4063_;
}
v_resetjp_4063_:
{
lean_object* v_fst_4066_; 
v_fst_4066_ = lean_ctor_get(v_a_4062_, 0);
if (lean_obj_tag(v_fst_4066_) == 0)
{
lean_object* v_snd_4067_; lean_object* v___x_4069_; 
v_snd_4067_ = lean_ctor_get(v_a_4062_, 1);
lean_inc(v_snd_4067_);
lean_dec(v_a_4062_);
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 0, v_snd_4067_);
v___x_4069_ = v___x_4064_;
goto v_reusejp_4068_;
}
else
{
lean_object* v_reuseFailAlloc_4070_; 
v_reuseFailAlloc_4070_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4070_, 0, v_snd_4067_);
v___x_4069_ = v_reuseFailAlloc_4070_;
goto v_reusejp_4068_;
}
v_reusejp_4068_:
{
return v___x_4069_;
}
}
else
{
lean_object* v_val_4071_; lean_object* v___x_4073_; 
lean_inc_ref(v_fst_4066_);
lean_dec(v_a_4062_);
v_val_4071_ = lean_ctor_get(v_fst_4066_, 0);
lean_inc(v_val_4071_);
lean_dec_ref(v_fst_4066_);
if (v_isShared_4065_ == 0)
{
lean_ctor_set(v___x_4064_, 0, v_val_4071_);
v___x_4073_ = v___x_4064_;
goto v_reusejp_4072_;
}
else
{
lean_object* v_reuseFailAlloc_4074_; 
v_reuseFailAlloc_4074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4074_, 0, v_val_4071_);
v___x_4073_ = v_reuseFailAlloc_4074_;
goto v_reusejp_4072_;
}
v_reusejp_4072_:
{
return v___x_4073_;
}
}
}
}
else
{
lean_object* v_a_4076_; lean_object* v___x_4078_; uint8_t v_isShared_4079_; uint8_t v_isSharedCheck_4083_; 
v_a_4076_ = lean_ctor_get(v___x_4061_, 0);
v_isSharedCheck_4083_ = !lean_is_exclusive(v___x_4061_);
if (v_isSharedCheck_4083_ == 0)
{
v___x_4078_ = v___x_4061_;
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
else
{
lean_inc(v_a_4076_);
lean_dec(v___x_4061_);
v___x_4078_ = lean_box(0);
v_isShared_4079_ = v_isSharedCheck_4083_;
goto v_resetjp_4077_;
}
v_resetjp_4077_:
{
lean_object* v___x_4081_; 
if (v_isShared_4079_ == 0)
{
v___x_4081_ = v___x_4078_;
goto v_reusejp_4080_;
}
else
{
lean_object* v_reuseFailAlloc_4082_; 
v_reuseFailAlloc_4082_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4082_, 0, v_a_4076_);
v___x_4081_ = v_reuseFailAlloc_4082_;
goto v_reusejp_4080_;
}
v_reusejp_4080_:
{
return v___x_4081_;
}
}
}
}
}
}
else
{
lean_object* v_a_4085_; lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4092_; 
lean_dec_ref(v_tail_4046_);
lean_dec(v_mvarId_4037_);
v_a_4085_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4092_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4092_ == 0)
{
v___x_4087_ = v___x_4047_;
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
else
{
lean_inc(v_a_4085_);
lean_dec(v___x_4047_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4092_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4090_; 
if (v_isShared_4088_ == 0)
{
v___x_4090_ = v___x_4087_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4091_; 
v_reuseFailAlloc_4091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4091_, 0, v_a_4085_);
v___x_4090_ = v_reuseFailAlloc_4091_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
return v___x_4090_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4093_, lean_object* v_t_4094_, lean_object* v_init_4095_, lean_object* v___y_4096_, lean_object* v___y_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_){
_start:
{
lean_object* v_res_4101_; 
v_res_4101_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4093_, v_t_4094_, v_init_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_);
lean_dec(v___y_4099_);
lean_dec_ref(v___y_4098_);
lean_dec(v___y_4097_);
lean_dec_ref(v___y_4096_);
return v_res_4101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_, lean_object* v___y_4108_, lean_object* v___y_4109_){
_start:
{
lean_object* v_lctx_4111_; lean_object* v_decls_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
v_lctx_4111_ = lean_ctor_get(v___y_4106_, 2);
v_decls_4112_ = lean_ctor_get(v_lctx_4111_, 1);
lean_inc_ref(v_decls_4112_);
v___x_4113_ = lean_box(0);
v___x_4114_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4115_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4105_, v_decls_4112_, v___x_4114_, v___y_4106_, v___y_4107_, v___y_4108_, v___y_4109_);
lean_dec_ref(v___y_4106_);
if (lean_obj_tag(v___x_4115_) == 0)
{
lean_object* v_a_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4128_; 
v_a_4116_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4128_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4128_ == 0)
{
v___x_4118_ = v___x_4115_;
v_isShared_4119_ = v_isSharedCheck_4128_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_a_4116_);
lean_dec(v___x_4115_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4128_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v_fst_4120_; 
v_fst_4120_ = lean_ctor_get(v_a_4116_, 0);
lean_inc(v_fst_4120_);
lean_dec(v_a_4116_);
if (lean_obj_tag(v_fst_4120_) == 0)
{
lean_object* v___x_4122_; 
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v___x_4113_);
v___x_4122_ = v___x_4118_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v___x_4113_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
else
{
lean_object* v_val_4124_; lean_object* v___x_4126_; 
v_val_4124_ = lean_ctor_get(v_fst_4120_, 0);
lean_inc(v_val_4124_);
lean_dec_ref(v_fst_4120_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set(v___x_4118_, 0, v_val_4124_);
v___x_4126_ = v___x_4118_;
goto v_reusejp_4125_;
}
else
{
lean_object* v_reuseFailAlloc_4127_; 
v_reuseFailAlloc_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4127_, 0, v_val_4124_);
v___x_4126_ = v_reuseFailAlloc_4127_;
goto v_reusejp_4125_;
}
v_reusejp_4125_:
{
return v___x_4126_;
}
}
}
}
else
{
lean_object* v_a_4129_; lean_object* v___x_4131_; uint8_t v_isShared_4132_; uint8_t v_isSharedCheck_4136_; 
v_a_4129_ = lean_ctor_get(v___x_4115_, 0);
v_isSharedCheck_4136_ = !lean_is_exclusive(v___x_4115_);
if (v_isSharedCheck_4136_ == 0)
{
v___x_4131_ = v___x_4115_;
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
else
{
lean_inc(v_a_4129_);
lean_dec(v___x_4115_);
v___x_4131_ = lean_box(0);
v_isShared_4132_ = v_isSharedCheck_4136_;
goto v_resetjp_4130_;
}
v_resetjp_4130_:
{
lean_object* v___x_4134_; 
if (v_isShared_4132_ == 0)
{
v___x_4134_ = v___x_4131_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v_a_4129_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_, lean_object* v___y_4142_){
_start:
{
lean_object* v_res_4143_; 
v_res_4143_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4137_, v___y_4138_, v___y_4139_, v___y_4140_, v___y_4141_);
lean_dec(v___y_4141_);
lean_dec_ref(v___y_4140_);
lean_dec(v___y_4139_);
return v_res_4143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_, lean_object* v_a_4148_){
_start:
{
lean_object* v___f_4150_; lean_object* v___x_4151_; 
lean_inc(v_mvarId_4144_);
v___f_4150_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4150_, 0, v_mvarId_4144_);
v___x_4151_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_4144_, v___f_4150_, v_a_4145_, v_a_4146_, v_a_4147_, v_a_4148_);
return v___x_4151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4152_, lean_object* v_a_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_){
_start:
{
lean_object* v_res_4158_; 
v_res_4158_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4152_, v_a_4153_, v_a_4154_, v_a_4155_, v_a_4156_);
lean_dec(v_a_4156_);
lean_dec_ref(v_a_4155_);
lean_dec(v_a_4154_);
lean_dec_ref(v_a_4153_);
return v_res_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4159_, lean_object* v_a_4160_, lean_object* v_a_4161_, lean_object* v_a_4162_, lean_object* v_a_4163_){
_start:
{
lean_object* v___x_4165_; 
lean_inc(v_mvarId_4159_);
v___x_4165_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4159_, v_a_4160_, v_a_4161_, v_a_4162_, v_a_4163_);
if (lean_obj_tag(v___x_4165_) == 0)
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4175_; 
v_a_4166_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4168_ = v___x_4165_;
v_isShared_4169_ = v_isSharedCheck_4175_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4165_);
v___x_4168_ = lean_box(0);
v_isShared_4169_ = v_isSharedCheck_4175_;
goto v_resetjp_4167_;
}
v_resetjp_4167_:
{
if (lean_obj_tag(v_a_4166_) == 1)
{
lean_object* v_val_4170_; 
lean_del_object(v___x_4168_);
lean_dec(v_mvarId_4159_);
v_val_4170_ = lean_ctor_get(v_a_4166_, 0);
lean_inc(v_val_4170_);
lean_dec_ref(v_a_4166_);
v_mvarId_4159_ = v_val_4170_;
goto _start;
}
else
{
lean_object* v___x_4173_; 
lean_dec(v_a_4166_);
if (v_isShared_4169_ == 0)
{
lean_ctor_set(v___x_4168_, 0, v_mvarId_4159_);
v___x_4173_ = v___x_4168_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_mvarId_4159_);
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
lean_dec(v_mvarId_4159_);
v_a_4176_ = lean_ctor_get(v___x_4165_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4165_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4165_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4165_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_, lean_object* v_a_4189_){
_start:
{
lean_object* v_res_4190_; 
v_res_4190_ = l_Lean_Meta_substVars(v_mvarId_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_);
lean_dec(v_a_4188_);
lean_dec_ref(v_a_4187_);
lean_dec(v_a_4186_);
lean_dec_ref(v_a_4185_);
return v_res_4190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4253_; uint8_t v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4253_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_4254_ = 0;
v___x_4255_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4256_ = l_Lean_registerTraceClass(v___x_4253_, v___x_4254_, v___x_4255_);
return v___x_4256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4257_){
_start:
{
lean_object* v_res_4258_; 
v_res_4258_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4258_;
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
