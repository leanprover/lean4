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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
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
uint8_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = l_Lean_Expr_hasMVar(v_e_1_);
v___x_5_ = lean_bool_not(v___x_4_);
if (v___x_5_ == 0)
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
else
{
lean_object* v___x_26_; 
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v_e_1_);
return v___x_26_;
}
}
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
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0(lean_object* v_e_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_e_31_, v___y_33_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___boxed(lean_object* v_e_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_, lean_object* v___y_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0(v_e_38_, v___y_39_, v___y_40_, v___y_41_, v___y_42_);
lean_dec(v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v___y_40_);
lean_dec_ref(v___y_39_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__1(lean_object* v_msg_46_, lean_object* v___y_47_, lean_object* v___y_48_, lean_object* v___y_49_, lean_object* v___y_50_){
_start:
{
lean_object* v___f_52_; lean_object* v___x_28601__overap_53_; lean_object* v___x_54_; 
v___f_52_ = ((lean_object*)(l_panic___at___00Lean_Meta_substCore_spec__1___closed__0));
v___x_28601__overap_53_ = lean_panic_fn_borrowed(v___f_52_, v_msg_46_);
lean_inc(v___y_50_);
lean_inc_ref(v___y_49_);
lean_inc(v___y_48_);
lean_inc_ref(v___y_47_);
v___x_54_ = lean_apply_5(v___x_28601__overap_53_, v___y_47_, v___y_48_, v___y_49_, v___y_50_, lean_box(0));
return v___x_54_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_substCore_spec__1___boxed(lean_object* v_msg_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_, lean_object* v___y_59_, lean_object* v___y_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_panic___at___00Lean_Meta_substCore_spec__1(v_msg_55_, v___y_56_, v___y_57_, v___y_58_, v___y_59_);
lean_dec(v___y_59_);
lean_dec_ref(v___y_58_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
return v_res_61_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__0(lean_object* v_x_62_){
_start:
{
uint8_t v___x_63_; 
v___x_63_ = 0;
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__0___boxed(lean_object* v_x_64_){
_start:
{
uint8_t v_res_65_; lean_object* v_r_66_; 
v_res_65_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__0(v_x_64_);
lean_dec(v_x_64_);
v_r_66_ = lean_box(v_res_65_);
return v_r_66_;
}
}
LEAN_EXPORT uint8_t l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1(lean_object* v_fvarId_67_, lean_object* v_x_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = l_Lean_instBEqFVarId_beq(v_fvarId_67_, v_x_68_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1___boxed(lean_object* v_fvarId_70_, lean_object* v_x_71_){
_start:
{
uint8_t v_res_72_; lean_object* v_r_73_; 
v_res_72_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1(v_fvarId_70_, v_x_71_);
lean_dec(v_x_71_);
lean_dec(v_fvarId_70_);
v_r_73_ = lean_box(v_res_72_);
return v_r_73_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_75_ = lean_box(0);
v___x_76_ = lean_unsigned_to_nat(16u);
v___x_77_ = lean_mk_array(v___x_76_, v___x_75_);
return v___x_77_;
}
}
static lean_object* _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__1);
v___x_79_ = lean_unsigned_to_nat(0u);
v___x_80_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(lean_object* v_e_81_, lean_object* v_fvarId_82_, lean_object* v___y_83_){
_start:
{
lean_object* v___x_85_; uint8_t v_fst_87_; lean_object* v_mctx_88_; lean_object* v_mctx_105_; lean_object* v___f_106_; lean_object* v___f_107_; lean_object* v___x_108_; lean_object* v___x_109_; uint8_t v___y_111_; uint8_t v___x_118_; uint8_t v___x_119_; 
v___x_85_ = lean_st_ref_get(v___y_83_);
v_mctx_105_ = lean_ctor_get(v___x_85_, 0);
lean_inc_ref_n(v_mctx_105_, 2);
lean_dec(v___x_85_);
v___f_106_ = ((lean_object*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__0));
v___f_107_ = lean_alloc_closure((void*)(l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___lam__1___boxed), 2, 1);
lean_closure_set(v___f_107_, 0, v_fvarId_82_);
v___x_108_ = lean_obj_once(&l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2, &l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2_once, _init_l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___closed__2);
v___x_109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_109_, 0, v___x_108_);
lean_ctor_set(v___x_109_, 1, v_mctx_105_);
v___x_118_ = l_Lean_Expr_hasFVar(v_e_81_);
v___x_119_ = lean_bool_not(v___x_118_);
if (v___x_119_ == 0)
{
v___y_111_ = v___x_119_;
goto v___jp_110_;
}
else
{
uint8_t v___x_120_; uint8_t v___x_121_; 
v___x_120_ = l_Lean_Expr_hasMVar(v_e_81_);
v___x_121_ = lean_bool_not(v___x_120_);
v___y_111_ = v___x_121_;
goto v___jp_110_;
}
v___jp_86_:
{
lean_object* v___x_89_; lean_object* v_cache_90_; lean_object* v_zetaDeltaFVarIds_91_; lean_object* v_postponed_92_; lean_object* v_diag_93_; lean_object* v___x_95_; uint8_t v_isShared_96_; uint8_t v_isSharedCheck_103_; 
v___x_89_ = lean_st_ref_take(v___y_83_);
v_cache_90_ = lean_ctor_get(v___x_89_, 1);
v_zetaDeltaFVarIds_91_ = lean_ctor_get(v___x_89_, 2);
v_postponed_92_ = lean_ctor_get(v___x_89_, 3);
v_diag_93_ = lean_ctor_get(v___x_89_, 4);
v_isSharedCheck_103_ = !lean_is_exclusive(v___x_89_);
if (v_isSharedCheck_103_ == 0)
{
lean_object* v_unused_104_; 
v_unused_104_ = lean_ctor_get(v___x_89_, 0);
lean_dec(v_unused_104_);
v___x_95_ = v___x_89_;
v_isShared_96_ = v_isSharedCheck_103_;
goto v_resetjp_94_;
}
else
{
lean_inc(v_diag_93_);
lean_inc(v_postponed_92_);
lean_inc(v_zetaDeltaFVarIds_91_);
lean_inc(v_cache_90_);
lean_dec(v___x_89_);
v___x_95_ = lean_box(0);
v_isShared_96_ = v_isSharedCheck_103_;
goto v_resetjp_94_;
}
v_resetjp_94_:
{
lean_object* v___x_98_; 
if (v_isShared_96_ == 0)
{
lean_ctor_set(v___x_95_, 0, v_mctx_88_);
v___x_98_ = v___x_95_;
goto v_reusejp_97_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_mctx_88_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_cache_90_);
lean_ctor_set(v_reuseFailAlloc_102_, 2, v_zetaDeltaFVarIds_91_);
lean_ctor_set(v_reuseFailAlloc_102_, 3, v_postponed_92_);
lean_ctor_set(v_reuseFailAlloc_102_, 4, v_diag_93_);
v___x_98_ = v_reuseFailAlloc_102_;
goto v_reusejp_97_;
}
v_reusejp_97_:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_99_ = lean_st_ref_set(v___y_83_, v___x_98_);
v___x_100_ = lean_box(v_fst_87_);
v___x_101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_101_, 0, v___x_100_);
return v___x_101_;
}
}
}
v___jp_110_:
{
if (v___y_111_ == 0)
{
lean_object* v___x_112_; lean_object* v_snd_113_; lean_object* v_fst_114_; lean_object* v_mctx_115_; uint8_t v___x_116_; 
lean_dec_ref(v_mctx_105_);
v___x_112_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(v___f_107_, v___f_106_, v_e_81_, v___x_109_);
v_snd_113_ = lean_ctor_get(v___x_112_, 1);
lean_inc(v_snd_113_);
v_fst_114_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_fst_114_);
lean_dec_ref(v___x_112_);
v_mctx_115_ = lean_ctor_get(v_snd_113_, 1);
lean_inc_ref(v_mctx_115_);
lean_dec(v_snd_113_);
v___x_116_ = lean_unbox(v_fst_114_);
lean_dec(v_fst_114_);
v_fst_87_ = v___x_116_;
v_mctx_88_ = v_mctx_115_;
goto v___jp_86_;
}
else
{
uint8_t v___x_117_; 
lean_dec_ref_known(v___x_109_, 2);
lean_dec_ref(v___f_107_);
lean_dec_ref(v_e_81_);
v___x_117_ = 0;
v_fst_87_ = v___x_117_;
v_mctx_88_ = v_mctx_105_;
goto v___jp_86_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg___boxed(lean_object* v_e_122_, lean_object* v_fvarId_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_e_122_, v_fvarId_123_, v___y_124_);
lean_dec(v___y_124_);
return v_res_126_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4(lean_object* v_e_127_, lean_object* v_fvarId_128_, lean_object* v___y_129_, lean_object* v___y_130_, lean_object* v___y_131_, lean_object* v___y_132_){
_start:
{
lean_object* v___x_134_; 
v___x_134_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_e_127_, v_fvarId_128_, v___y_130_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___boxed(lean_object* v_e_135_, lean_object* v_fvarId_136_, lean_object* v___y_137_, lean_object* v___y_138_, lean_object* v___y_139_, lean_object* v___y_140_, lean_object* v___y_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4(v_e_135_, v_fvarId_136_, v___y_137_, v___y_138_, v___y_139_, v___y_140_);
lean_dec(v___y_140_);
lean_dec_ref(v___y_139_);
lean_dec(v___y_138_);
lean_dec_ref(v___y_137_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(lean_object* v_mvarId_143_, lean_object* v_x_144_, lean_object* v___y_145_, lean_object* v___y_146_, lean_object* v___y_147_, lean_object* v___y_148_){
_start:
{
lean_object* v___x_150_; 
v___x_150_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_143_, v_x_144_, v___y_145_, v___y_146_, v___y_147_, v___y_148_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_object* v_a_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_158_; 
v_a_151_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_158_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_158_ == 0)
{
v___x_153_ = v___x_150_;
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_a_151_);
lean_dec(v___x_150_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_158_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_156_; 
if (v_isShared_154_ == 0)
{
v___x_156_ = v___x_153_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v_a_151_);
v___x_156_ = v_reuseFailAlloc_157_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
return v___x_156_;
}
}
}
else
{
lean_object* v_a_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_166_; 
v_a_159_ = lean_ctor_get(v___x_150_, 0);
v_isSharedCheck_166_ = !lean_is_exclusive(v___x_150_);
if (v_isSharedCheck_166_ == 0)
{
v___x_161_ = v___x_150_;
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_a_159_);
lean_dec(v___x_150_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_166_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_164_; 
if (v_isShared_162_ == 0)
{
v___x_164_ = v___x_161_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_165_; 
v_reuseFailAlloc_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_165_, 0, v_a_159_);
v___x_164_ = v_reuseFailAlloc_165_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
return v___x_164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg___boxed(lean_object* v_mvarId_167_, lean_object* v_x_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_, lean_object* v___y_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_167_, v_x_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec(v___y_172_);
lean_dec_ref(v___y_171_);
lean_dec(v___y_170_);
lean_dec_ref(v___y_169_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(lean_object* v_00_u03b1_175_, lean_object* v_mvarId_176_, lean_object* v_x_177_, lean_object* v___y_178_, lean_object* v___y_179_, lean_object* v___y_180_, lean_object* v___y_181_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_176_, v_x_177_, v___y_178_, v___y_179_, v___y_180_, v___y_181_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed(lean_object* v_00_u03b1_184_, lean_object* v_mvarId_185_, lean_object* v_x_186_, lean_object* v___y_187_, lean_object* v___y_188_, lean_object* v___y_189_, lean_object* v___y_190_, lean_object* v___y_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7(v_00_u03b1_184_, v_mvarId_185_, v_x_186_, v___y_187_, v___y_188_, v___y_189_, v___y_190_);
lean_dec(v___y_190_);
lean_dec_ref(v___y_189_);
lean_dec(v___y_188_);
lean_dec_ref(v___y_187_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0(lean_object* v___x_196_, lean_object* v___y_197_, lean_object* v___y_198_, lean_object* v___y_199_, lean_object* v___y_200_){
_start:
{
lean_object* v_options_202_; uint8_t v_hasTrace_203_; 
v_options_202_ = lean_ctor_get(v___y_199_, 2);
v_hasTrace_203_ = lean_ctor_get_uint8(v_options_202_, sizeof(void*)*1);
if (v_hasTrace_203_ == 0)
{
lean_object* v___x_204_; lean_object* v___x_205_; 
lean_dec(v___x_196_);
v___x_204_ = lean_box(v_hasTrace_203_);
v___x_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_205_, 0, v___x_204_);
return v___x_205_;
}
else
{
lean_object* v_inheritedTraceOptions_206_; lean_object* v___x_207_; lean_object* v___x_208_; uint8_t v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v_inheritedTraceOptions_206_ = lean_ctor_get(v___y_199_, 13);
v___x_207_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
v___x_208_ = l_Lean_Name_append(v___x_207_, v___x_196_);
v___x_209_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_206_, v_options_202_, v___x_208_);
lean_dec(v___x_208_);
v___x_210_ = lean_box(v___x_209_);
v___x_211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__0___boxed(lean_object* v___x_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Meta_substCore___lam__0(v___x_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1(lean_object* v_type_219_, lean_object* v___x_220_, lean_object* v___x_221_, lean_object* v___x_222_, uint8_t v___x_223_, uint8_t v___x_224_, lean_object* v_hAux_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_, lean_object* v___y_229_){
_start:
{
lean_object* v___x_231_; 
lean_inc_ref(v_hAux_225_);
v___x_231_ = l_Lean_Meta_mkEqSymm(v_hAux_225_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
if (lean_obj_tag(v___x_231_) == 0)
{
lean_object* v_a_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; uint8_t v___x_237_; lean_object* v___x_238_; 
v_a_232_ = lean_ctor_get(v___x_231_, 0);
lean_inc(v_a_232_);
lean_dec_ref_known(v___x_231_, 1);
v___x_233_ = l_Lean_Expr_replaceFVar(v_type_219_, v___x_220_, v_a_232_);
lean_dec(v_a_232_);
v___x_234_ = lean_mk_empty_array_with_capacity(v___x_221_);
v___x_235_ = lean_array_push(v___x_234_, v___x_222_);
v___x_236_ = lean_array_push(v___x_235_, v_hAux_225_);
v___x_237_ = 1;
v___x_238_ = l_Lean_Meta_mkLambdaFVars(v___x_236_, v___x_233_, v___x_223_, v___x_224_, v___x_223_, v___x_224_, v___x_237_, v___y_226_, v___y_227_, v___y_228_, v___y_229_);
lean_dec_ref(v___x_236_);
return v___x_238_;
}
else
{
lean_dec_ref(v_hAux_225_);
lean_dec_ref(v___x_222_);
lean_dec_ref(v___x_220_);
return v___x_231_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__1___boxed(lean_object* v_type_239_, lean_object* v___x_240_, lean_object* v___x_241_, lean_object* v___x_242_, lean_object* v___x_243_, lean_object* v___x_244_, lean_object* v_hAux_245_, lean_object* v___y_246_, lean_object* v___y_247_, lean_object* v___y_248_, lean_object* v___y_249_, lean_object* v___y_250_){
_start:
{
uint8_t v___x_33016__boxed_251_; uint8_t v___x_33017__boxed_252_; lean_object* v_res_253_; 
v___x_33016__boxed_251_ = lean_unbox(v___x_243_);
v___x_33017__boxed_252_ = lean_unbox(v___x_244_);
v_res_253_ = l_Lean_Meta_substCore___lam__1(v_type_239_, v___x_240_, v___x_241_, v___x_242_, v___x_33016__boxed_251_, v___x_33017__boxed_252_, v_hAux_245_, v___y_246_, v___y_247_, v___y_248_, v___y_249_);
lean_dec(v___y_249_);
lean_dec_ref(v___y_248_);
lean_dec(v___y_247_);
lean_dec_ref(v___y_246_);
lean_dec(v___x_241_);
lean_dec_ref(v_type_239_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0(lean_object* v_k_254_, lean_object* v_b_255_, lean_object* v___y_256_, lean_object* v___y_257_, lean_object* v___y_258_, lean_object* v___y_259_){
_start:
{
lean_object* v___x_261_; 
lean_inc(v___y_259_);
lean_inc_ref(v___y_258_);
lean_inc(v___y_257_);
lean_inc_ref(v___y_256_);
v___x_261_ = lean_apply_6(v_k_254_, v_b_255_, v___y_256_, v___y_257_, v___y_258_, v___y_259_, lean_box(0));
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0___boxed(lean_object* v_k_262_, lean_object* v_b_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_, lean_object* v___y_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0(v_k_262_, v_b_263_, v___y_264_, v___y_265_, v___y_266_, v___y_267_);
lean_dec(v___y_267_);
lean_dec_ref(v___y_266_);
lean_dec(v___y_265_);
lean_dec_ref(v___y_264_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(lean_object* v_name_270_, uint8_t v_bi_271_, lean_object* v_type_272_, lean_object* v_k_273_, uint8_t v_kind_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_){
_start:
{
lean_object* v___f_280_; lean_object* v___x_281_; 
v___f_280_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_280_, 0, v_k_273_);
v___x_281_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_270_, v_bi_271_, v_type_272_, v___f_280_, v_kind_274_, v___y_275_, v___y_276_, v___y_277_, v___y_278_);
if (lean_obj_tag(v___x_281_) == 0)
{
lean_object* v_a_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_289_; 
v_a_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_289_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_289_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_a_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_289_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_287_; 
if (v_isShared_285_ == 0)
{
v___x_287_ = v___x_284_;
goto v_reusejp_286_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v_a_282_);
v___x_287_ = v_reuseFailAlloc_288_;
goto v_reusejp_286_;
}
v_reusejp_286_:
{
return v___x_287_;
}
}
}
else
{
lean_object* v_a_290_; lean_object* v___x_292_; uint8_t v_isShared_293_; uint8_t v_isSharedCheck_297_; 
v_a_290_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_297_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_297_ == 0)
{
v___x_292_ = v___x_281_;
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
else
{
lean_inc(v_a_290_);
lean_dec(v___x_281_);
v___x_292_ = lean_box(0);
v_isShared_293_ = v_isSharedCheck_297_;
goto v_resetjp_291_;
}
v_resetjp_291_:
{
lean_object* v___x_295_; 
if (v_isShared_293_ == 0)
{
v___x_295_ = v___x_292_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_296_; 
v_reuseFailAlloc_296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_296_, 0, v_a_290_);
v___x_295_ = v_reuseFailAlloc_296_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
return v___x_295_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg___boxed(lean_object* v_name_298_, lean_object* v_bi_299_, lean_object* v_type_300_, lean_object* v_k_301_, lean_object* v_kind_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
uint8_t v_bi_boxed_308_; uint8_t v_kind_boxed_309_; lean_object* v_res_310_; 
v_bi_boxed_308_ = lean_unbox(v_bi_299_);
v_kind_boxed_309_ = lean_unbox(v_kind_302_);
v_res_310_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_298_, v_bi_boxed_308_, v_type_300_, v_k_301_, v_kind_boxed_309_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_306_);
lean_dec_ref(v___y_305_);
lean_dec(v___y_304_);
lean_dec_ref(v___y_303_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(lean_object* v_name_311_, lean_object* v_type_312_, lean_object* v_k_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
uint8_t v___x_319_; uint8_t v___x_320_; lean_object* v___x_321_; 
v___x_319_ = 0;
v___x_320_ = 0;
v___x_321_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_311_, v___x_319_, v_type_312_, v_k_313_, v___x_320_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg___boxed(lean_object* v_name_322_, lean_object* v_type_323_, lean_object* v_k_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_){
_start:
{
lean_object* v_res_330_; 
v_res_330_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v_name_322_, v_type_323_, v_k_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
return v_res_330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(lean_object* v_fst_331_, lean_object* v_fst_332_, lean_object* v_n_333_, lean_object* v_i_334_, lean_object* v_a_335_){
_start:
{
lean_object* v_zero_337_; uint8_t v_isZero_338_; 
v_zero_337_ = lean_unsigned_to_nat(0u);
v_isZero_338_ = lean_nat_dec_eq(v_i_334_, v_zero_337_);
if (v_isZero_338_ == 1)
{
lean_object* v___x_339_; 
lean_dec(v_i_334_);
v___x_339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_339_, 0, v_a_335_);
return v___x_339_;
}
else
{
lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v_one_342_; lean_object* v_n_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v___x_340_ = lean_unsigned_to_nat(2u);
v___x_341_ = lean_box(0);
v_one_342_ = lean_unsigned_to_nat(1u);
v_n_343_ = lean_nat_sub(v_i_334_, v_one_342_);
lean_dec(v_i_334_);
v___x_344_ = lean_nat_sub(v_n_333_, v_n_343_);
v___x_345_ = lean_nat_sub(v___x_344_, v_one_342_);
lean_dec(v___x_344_);
v___x_346_ = lean_nat_add(v___x_345_, v___x_340_);
v___x_347_ = lean_array_get_borrowed(v___x_341_, v_fst_331_, v___x_346_);
lean_dec(v___x_346_);
v___x_348_ = lean_array_fget_borrowed(v_fst_332_, v___x_345_);
lean_dec(v___x_345_);
lean_inc(v___x_348_);
v___x_349_ = l_Lean_mkFVar(v___x_348_);
lean_inc(v___x_347_);
v___x_350_ = l_Lean_Meta_FVarSubst_insert(v_a_335_, v___x_347_, v___x_349_);
v_i_334_ = v_n_343_;
v_a_335_ = v___x_350_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg___boxed(lean_object* v_fst_352_, lean_object* v_fst_353_, lean_object* v_n_354_, lean_object* v_i_355_, lean_object* v_a_356_, lean_object* v___y_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_352_, v_fst_353_, v_n_354_, v_i_355_, v_a_356_);
lean_dec(v_n_354_);
lean_dec_ref(v_fst_353_);
lean_dec_ref(v_fst_352_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(lean_object* v_msgData_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_){
_start:
{
lean_object* v___x_365_; lean_object* v_env_366_; lean_object* v___x_367_; lean_object* v_mctx_368_; lean_object* v_lctx_369_; lean_object* v_options_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_365_ = lean_st_ref_get(v___y_363_);
v_env_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc_ref(v_env_366_);
lean_dec(v___x_365_);
v___x_367_ = lean_st_ref_get(v___y_361_);
v_mctx_368_ = lean_ctor_get(v___x_367_, 0);
lean_inc_ref(v_mctx_368_);
lean_dec(v___x_367_);
v_lctx_369_ = lean_ctor_get(v___y_360_, 2);
v_options_370_ = lean_ctor_get(v___y_362_, 2);
lean_inc_ref(v_options_370_);
lean_inc_ref(v_lctx_369_);
v___x_371_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_371_, 0, v_env_366_);
lean_ctor_set(v___x_371_, 1, v_mctx_368_);
lean_ctor_set(v___x_371_, 2, v_lctx_369_);
lean_ctor_set(v___x_371_, 3, v_options_370_);
v___x_372_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
lean_ctor_set(v___x_372_, 1, v_msgData_359_);
v___x_373_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3___boxed(lean_object* v_msgData_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_){
_start:
{
lean_object* v_res_380_; 
v_res_380_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msgData_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_);
lean_dec(v___y_378_);
lean_dec_ref(v___y_377_);
lean_dec(v___y_376_);
lean_dec_ref(v___y_375_);
return v_res_380_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0(void){
_start:
{
lean_object* v___x_381_; double v___x_382_; 
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = lean_float_of_nat(v___x_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(lean_object* v_cls_386_, lean_object* v_msg_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_ref_393_; lean_object* v___x_394_; lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_439_; 
v_ref_393_ = lean_ctor_get(v___y_390_, 5);
v___x_394_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msg_387_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
v_a_395_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_439_ == 0)
{
v___x_397_ = v___x_394_;
v_isShared_398_ = v_isSharedCheck_439_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_394_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_439_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_399_; lean_object* v_traceState_400_; lean_object* v_env_401_; lean_object* v_nextMacroScope_402_; lean_object* v_ngen_403_; lean_object* v_auxDeclNGen_404_; lean_object* v_cache_405_; lean_object* v_messages_406_; lean_object* v_infoState_407_; lean_object* v_snapshotTasks_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_438_; 
v___x_399_ = lean_st_ref_take(v___y_391_);
v_traceState_400_ = lean_ctor_get(v___x_399_, 4);
v_env_401_ = lean_ctor_get(v___x_399_, 0);
v_nextMacroScope_402_ = lean_ctor_get(v___x_399_, 1);
v_ngen_403_ = lean_ctor_get(v___x_399_, 2);
v_auxDeclNGen_404_ = lean_ctor_get(v___x_399_, 3);
v_cache_405_ = lean_ctor_get(v___x_399_, 5);
v_messages_406_ = lean_ctor_get(v___x_399_, 6);
v_infoState_407_ = lean_ctor_get(v___x_399_, 7);
v_snapshotTasks_408_ = lean_ctor_get(v___x_399_, 8);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_399_);
if (v_isSharedCheck_438_ == 0)
{
v___x_410_ = v___x_399_;
v_isShared_411_ = v_isSharedCheck_438_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_snapshotTasks_408_);
lean_inc(v_infoState_407_);
lean_inc(v_messages_406_);
lean_inc(v_cache_405_);
lean_inc(v_traceState_400_);
lean_inc(v_auxDeclNGen_404_);
lean_inc(v_ngen_403_);
lean_inc(v_nextMacroScope_402_);
lean_inc(v_env_401_);
lean_dec(v___x_399_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_438_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
uint64_t v_tid_412_; lean_object* v_traces_413_; lean_object* v___x_415_; uint8_t v_isShared_416_; uint8_t v_isSharedCheck_437_; 
v_tid_412_ = lean_ctor_get_uint64(v_traceState_400_, sizeof(void*)*1);
v_traces_413_ = lean_ctor_get(v_traceState_400_, 0);
v_isSharedCheck_437_ = !lean_is_exclusive(v_traceState_400_);
if (v_isSharedCheck_437_ == 0)
{
v___x_415_ = v_traceState_400_;
v_isShared_416_ = v_isSharedCheck_437_;
goto v_resetjp_414_;
}
else
{
lean_inc(v_traces_413_);
lean_dec(v_traceState_400_);
v___x_415_ = lean_box(0);
v_isShared_416_ = v_isSharedCheck_437_;
goto v_resetjp_414_;
}
v_resetjp_414_:
{
lean_object* v___x_417_; double v___x_418_; uint8_t v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_427_; 
v___x_417_ = lean_box(0);
v___x_418_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0, &l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__0);
v___x_419_ = 0;
v___x_420_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__1));
v___x_421_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_421_, 0, v_cls_386_);
lean_ctor_set(v___x_421_, 1, v___x_417_);
lean_ctor_set(v___x_421_, 2, v___x_420_);
lean_ctor_set_float(v___x_421_, sizeof(void*)*3, v___x_418_);
lean_ctor_set_float(v___x_421_, sizeof(void*)*3 + 8, v___x_418_);
lean_ctor_set_uint8(v___x_421_, sizeof(void*)*3 + 16, v___x_419_);
v___x_422_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___closed__2));
v___x_423_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_423_, 0, v___x_421_);
lean_ctor_set(v___x_423_, 1, v_a_395_);
lean_ctor_set(v___x_423_, 2, v___x_422_);
lean_inc(v_ref_393_);
v___x_424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_424_, 0, v_ref_393_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_Lean_PersistentArray_push___redArg(v_traces_413_, v___x_424_);
if (v_isShared_416_ == 0)
{
lean_ctor_set(v___x_415_, 0, v___x_425_);
v___x_427_ = v___x_415_;
goto v_reusejp_426_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v___x_425_);
lean_ctor_set_uint64(v_reuseFailAlloc_436_, sizeof(void*)*1, v_tid_412_);
v___x_427_ = v_reuseFailAlloc_436_;
goto v_reusejp_426_;
}
v_reusejp_426_:
{
lean_object* v___x_429_; 
if (v_isShared_411_ == 0)
{
lean_ctor_set(v___x_410_, 4, v___x_427_);
v___x_429_ = v___x_410_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_env_401_);
lean_ctor_set(v_reuseFailAlloc_435_, 1, v_nextMacroScope_402_);
lean_ctor_set(v_reuseFailAlloc_435_, 2, v_ngen_403_);
lean_ctor_set(v_reuseFailAlloc_435_, 3, v_auxDeclNGen_404_);
lean_ctor_set(v_reuseFailAlloc_435_, 4, v___x_427_);
lean_ctor_set(v_reuseFailAlloc_435_, 5, v_cache_405_);
lean_ctor_set(v_reuseFailAlloc_435_, 6, v_messages_406_);
lean_ctor_set(v_reuseFailAlloc_435_, 7, v_infoState_407_);
lean_ctor_set(v_reuseFailAlloc_435_, 8, v_snapshotTasks_408_);
v___x_429_ = v_reuseFailAlloc_435_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_433_; 
v___x_430_ = lean_st_ref_set(v___y_391_, v___x_429_);
v___x_431_ = lean_box(0);
if (v_isShared_398_ == 0)
{
lean_ctor_set(v___x_397_, 0, v___x_431_);
v___x_433_ = v___x_397_;
goto v_reusejp_432_;
}
else
{
lean_object* v_reuseFailAlloc_434_; 
v_reuseFailAlloc_434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_434_, 0, v___x_431_);
v___x_433_ = v_reuseFailAlloc_434_;
goto v_reusejp_432_;
}
v_reusejp_432_:
{
return v___x_433_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3___boxed(lean_object* v_cls_440_, lean_object* v_msg_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v_cls_440_, v_msg_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(lean_object* v_x_448_, lean_object* v_x_449_, lean_object* v_x_450_, lean_object* v_x_451_){
_start:
{
lean_object* v_ks_452_; lean_object* v_vs_453_; lean_object* v___x_455_; uint8_t v_isShared_456_; uint8_t v_isSharedCheck_477_; 
v_ks_452_ = lean_ctor_get(v_x_448_, 0);
v_vs_453_ = lean_ctor_get(v_x_448_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_448_);
if (v_isSharedCheck_477_ == 0)
{
v___x_455_ = v_x_448_;
v_isShared_456_ = v_isSharedCheck_477_;
goto v_resetjp_454_;
}
else
{
lean_inc(v_vs_453_);
lean_inc(v_ks_452_);
lean_dec(v_x_448_);
v___x_455_ = lean_box(0);
v_isShared_456_ = v_isSharedCheck_477_;
goto v_resetjp_454_;
}
v_resetjp_454_:
{
lean_object* v___x_457_; uint8_t v___x_458_; 
v___x_457_ = lean_array_get_size(v_ks_452_);
v___x_458_ = lean_nat_dec_lt(v_x_449_, v___x_457_);
if (v___x_458_ == 0)
{
lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_462_; 
lean_dec(v_x_449_);
v___x_459_ = lean_array_push(v_ks_452_, v_x_450_);
v___x_460_ = lean_array_push(v_vs_453_, v_x_451_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_460_);
lean_ctor_set(v___x_455_, 0, v___x_459_);
v___x_462_ = v___x_455_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v___x_459_);
lean_ctor_set(v_reuseFailAlloc_463_, 1, v___x_460_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
else
{
lean_object* v_k_x27_464_; uint8_t v___x_465_; 
v_k_x27_464_ = lean_array_fget_borrowed(v_ks_452_, v_x_449_);
v___x_465_ = l_Lean_instBEqMVarId_beq(v_x_450_, v_k_x27_464_);
if (v___x_465_ == 0)
{
lean_object* v___x_467_; 
if (v_isShared_456_ == 0)
{
v___x_467_ = v___x_455_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_ks_452_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v_vs_453_);
v___x_467_ = v_reuseFailAlloc_471_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(1u);
v___x_469_ = lean_nat_add(v_x_449_, v___x_468_);
lean_dec(v_x_449_);
v_x_448_ = v___x_467_;
v_x_449_ = v___x_469_;
goto _start;
}
}
else
{
lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_472_ = lean_array_fset(v_ks_452_, v_x_449_, v_x_450_);
v___x_473_ = lean_array_fset(v_vs_453_, v_x_449_, v_x_451_);
lean_dec(v_x_449_);
if (v_isShared_456_ == 0)
{
lean_ctor_set(v___x_455_, 1, v___x_473_);
lean_ctor_set(v___x_455_, 0, v___x_472_);
v___x_475_ = v___x_455_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(lean_object* v_n_478_, lean_object* v_k_479_, lean_object* v_v_480_){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_481_ = lean_unsigned_to_nat(0u);
v___x_482_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(v_n_478_, v___x_481_, v_k_479_, v_v_480_);
return v___x_482_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(lean_object* v_x_484_, size_t v_x_485_, size_t v_x_486_, lean_object* v_x_487_, lean_object* v_x_488_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v_es_489_; size_t v___x_490_; size_t v___x_491_; lean_object* v_j_492_; lean_object* v___x_493_; uint8_t v___x_494_; 
v_es_489_ = lean_ctor_get(v_x_484_, 0);
v___x_490_ = ((size_t)31ULL);
v___x_491_ = lean_usize_land(v_x_485_, v___x_490_);
v_j_492_ = lean_usize_to_nat(v___x_491_);
v___x_493_ = lean_array_get_size(v_es_489_);
v___x_494_ = lean_nat_dec_lt(v_j_492_, v___x_493_);
if (v___x_494_ == 0)
{
lean_dec(v_j_492_);
lean_dec(v_x_488_);
lean_dec(v_x_487_);
return v_x_484_;
}
else
{
lean_object* v___x_496_; uint8_t v_isShared_497_; uint8_t v_isSharedCheck_533_; 
lean_inc_ref(v_es_489_);
v_isSharedCheck_533_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v_x_484_, 0);
lean_dec(v_unused_534_);
v___x_496_ = v_x_484_;
v_isShared_497_ = v_isSharedCheck_533_;
goto v_resetjp_495_;
}
else
{
lean_dec(v_x_484_);
v___x_496_ = lean_box(0);
v_isShared_497_ = v_isSharedCheck_533_;
goto v_resetjp_495_;
}
v_resetjp_495_:
{
lean_object* v_v_498_; lean_object* v___x_499_; lean_object* v_xs_x27_500_; lean_object* v___y_502_; 
v_v_498_ = lean_array_fget(v_es_489_, v_j_492_);
v___x_499_ = lean_box(0);
v_xs_x27_500_ = lean_array_fset(v_es_489_, v_j_492_, v___x_499_);
switch(lean_obj_tag(v_v_498_))
{
case 0:
{
lean_object* v_key_507_; lean_object* v_val_508_; lean_object* v___x_510_; uint8_t v_isShared_511_; uint8_t v_isSharedCheck_518_; 
v_key_507_ = lean_ctor_get(v_v_498_, 0);
v_val_508_ = lean_ctor_get(v_v_498_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_v_498_);
if (v_isSharedCheck_518_ == 0)
{
v___x_510_ = v_v_498_;
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
else
{
lean_inc(v_val_508_);
lean_inc(v_key_507_);
lean_dec(v_v_498_);
v___x_510_ = lean_box(0);
v_isShared_511_ = v_isSharedCheck_518_;
goto v_resetjp_509_;
}
v_resetjp_509_:
{
uint8_t v___x_512_; 
v___x_512_ = l_Lean_instBEqMVarId_beq(v_x_487_, v_key_507_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_del_object(v___x_510_);
v___x_513_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_507_, v_val_508_, v_x_487_, v_x_488_);
v___x_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
v___y_502_ = v___x_514_;
goto v___jp_501_;
}
else
{
lean_object* v___x_516_; 
lean_dec(v_val_508_);
lean_dec(v_key_507_);
if (v_isShared_511_ == 0)
{
lean_ctor_set(v___x_510_, 1, v_x_488_);
lean_ctor_set(v___x_510_, 0, v_x_487_);
v___x_516_ = v___x_510_;
goto v_reusejp_515_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_x_487_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_x_488_);
v___x_516_ = v_reuseFailAlloc_517_;
goto v_reusejp_515_;
}
v_reusejp_515_:
{
v___y_502_ = v___x_516_;
goto v___jp_501_;
}
}
}
}
case 1:
{
lean_object* v_node_519_; lean_object* v___x_521_; uint8_t v_isShared_522_; uint8_t v_isSharedCheck_531_; 
v_node_519_ = lean_ctor_get(v_v_498_, 0);
v_isSharedCheck_531_ = !lean_is_exclusive(v_v_498_);
if (v_isSharedCheck_531_ == 0)
{
v___x_521_ = v_v_498_;
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
else
{
lean_inc(v_node_519_);
lean_dec(v_v_498_);
v___x_521_ = lean_box(0);
v_isShared_522_ = v_isSharedCheck_531_;
goto v_resetjp_520_;
}
v_resetjp_520_:
{
size_t v___x_523_; size_t v___x_524_; size_t v___x_525_; size_t v___x_526_; lean_object* v___x_527_; lean_object* v___x_529_; 
v___x_523_ = ((size_t)5ULL);
v___x_524_ = lean_usize_shift_right(v_x_485_, v___x_523_);
v___x_525_ = ((size_t)1ULL);
v___x_526_ = lean_usize_add(v_x_486_, v___x_525_);
v___x_527_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_node_519_, v___x_524_, v___x_526_, v_x_487_, v_x_488_);
if (v_isShared_522_ == 0)
{
lean_ctor_set(v___x_521_, 0, v___x_527_);
v___x_529_ = v___x_521_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_530_; 
v_reuseFailAlloc_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_530_, 0, v___x_527_);
v___x_529_ = v_reuseFailAlloc_530_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
v___y_502_ = v___x_529_;
goto v___jp_501_;
}
}
}
default: 
{
lean_object* v___x_532_; 
v___x_532_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_532_, 0, v_x_487_);
lean_ctor_set(v___x_532_, 1, v_x_488_);
v___y_502_ = v___x_532_;
goto v___jp_501_;
}
}
v___jp_501_:
{
lean_object* v___x_503_; lean_object* v___x_505_; 
v___x_503_ = lean_array_fset(v_xs_x27_500_, v_j_492_, v___y_502_);
lean_dec(v_j_492_);
if (v_isShared_497_ == 0)
{
lean_ctor_set(v___x_496_, 0, v___x_503_);
v___x_505_ = v___x_496_;
goto v_reusejp_504_;
}
else
{
lean_object* v_reuseFailAlloc_506_; 
v_reuseFailAlloc_506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_506_, 0, v___x_503_);
v___x_505_ = v_reuseFailAlloc_506_;
goto v_reusejp_504_;
}
v_reusejp_504_:
{
return v___x_505_;
}
}
}
}
}
else
{
lean_object* v_ks_535_; lean_object* v_vs_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_556_; 
v_ks_535_ = lean_ctor_get(v_x_484_, 0);
v_vs_536_ = lean_ctor_get(v_x_484_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_556_ == 0)
{
v___x_538_ = v_x_484_;
v_isShared_539_ = v_isSharedCheck_556_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_vs_536_);
lean_inc(v_ks_535_);
lean_dec(v_x_484_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_556_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_ks_535_);
lean_ctor_set(v_reuseFailAlloc_555_, 1, v_vs_536_);
v___x_541_ = v_reuseFailAlloc_555_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v_newNode_542_; uint8_t v___y_544_; size_t v___x_550_; uint8_t v___x_551_; 
v_newNode_542_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v___x_541_, v_x_487_, v_x_488_);
v___x_550_ = ((size_t)7ULL);
v___x_551_ = lean_usize_dec_le(v___x_550_, v_x_486_);
if (v___x_551_ == 0)
{
lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_552_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_542_);
v___x_553_ = lean_unsigned_to_nat(4u);
v___x_554_ = lean_nat_dec_lt(v___x_552_, v___x_553_);
lean_dec(v___x_552_);
v___y_544_ = v___x_554_;
goto v___jp_543_;
}
else
{
v___y_544_ = v___x_551_;
goto v___jp_543_;
}
v___jp_543_:
{
if (v___y_544_ == 0)
{
lean_object* v_ks_545_; lean_object* v_vs_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_ks_545_ = lean_ctor_get(v_newNode_542_, 0);
lean_inc_ref(v_ks_545_);
v_vs_546_ = lean_ctor_get(v_newNode_542_, 1);
lean_inc_ref(v_vs_546_);
lean_dec_ref(v_newNode_542_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0);
v___x_549_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_x_486_, v_ks_545_, v_vs_546_, v___x_547_, v___x_548_);
lean_dec_ref(v_vs_546_);
lean_dec_ref(v_ks_545_);
return v___x_549_;
}
else
{
return v_newNode_542_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(size_t v_depth_557_, lean_object* v_keys_558_, lean_object* v_vals_559_, lean_object* v_i_560_, lean_object* v_entries_561_){
_start:
{
lean_object* v___x_562_; uint8_t v___x_563_; 
v___x_562_ = lean_array_get_size(v_keys_558_);
v___x_563_ = lean_nat_dec_lt(v_i_560_, v___x_562_);
if (v___x_563_ == 0)
{
lean_dec(v_i_560_);
return v_entries_561_;
}
else
{
lean_object* v_k_564_; lean_object* v_v_565_; uint64_t v___x_566_; size_t v_h_567_; size_t v___x_568_; lean_object* v___x_569_; size_t v___x_570_; size_t v___x_571_; size_t v___x_572_; size_t v_h_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_k_564_ = lean_array_fget_borrowed(v_keys_558_, v_i_560_);
v_v_565_ = lean_array_fget_borrowed(v_vals_559_, v_i_560_);
v___x_566_ = l_Lean_instHashableMVarId_hash(v_k_564_);
v_h_567_ = lean_uint64_to_usize(v___x_566_);
v___x_568_ = ((size_t)5ULL);
v___x_569_ = lean_unsigned_to_nat(1u);
v___x_570_ = ((size_t)1ULL);
v___x_571_ = lean_usize_sub(v_depth_557_, v___x_570_);
v___x_572_ = lean_usize_mul(v___x_568_, v___x_571_);
v_h_573_ = lean_usize_shift_right(v_h_567_, v___x_572_);
v___x_574_ = lean_nat_add(v_i_560_, v___x_569_);
lean_dec(v_i_560_);
lean_inc(v_v_565_);
lean_inc(v_k_564_);
v___x_575_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_entries_561_, v_h_573_, v_depth_557_, v_k_564_, v_v_565_);
v_i_560_ = v___x_574_;
v_entries_561_ = v___x_575_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_depth_577_, lean_object* v_keys_578_, lean_object* v_vals_579_, lean_object* v_i_580_, lean_object* v_entries_581_){
_start:
{
size_t v_depth_boxed_582_; lean_object* v_res_583_; 
v_depth_boxed_582_ = lean_unbox_usize(v_depth_577_);
lean_dec(v_depth_577_);
v_res_583_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_boxed_582_, v_keys_578_, v_vals_579_, v_i_580_, v_entries_581_);
lean_dec_ref(v_vals_579_);
lean_dec_ref(v_keys_578_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_, lean_object* v_x_587_, lean_object* v_x_588_){
_start:
{
size_t v_x_33388__boxed_589_; size_t v_x_33389__boxed_590_; lean_object* v_res_591_; 
v_x_33388__boxed_589_ = lean_unbox_usize(v_x_585_);
lean_dec(v_x_585_);
v_x_33389__boxed_590_ = lean_unbox_usize(v_x_586_);
lean_dec(v_x_586_);
v_res_591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_584_, v_x_33388__boxed_589_, v_x_33389__boxed_590_, v_x_587_, v_x_588_);
return v_res_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(lean_object* v_x_592_, lean_object* v_x_593_, lean_object* v_x_594_){
_start:
{
uint64_t v___x_595_; size_t v___x_596_; size_t v___x_597_; lean_object* v___x_598_; 
v___x_595_ = l_Lean_instHashableMVarId_hash(v_x_593_);
v___x_596_ = lean_uint64_to_usize(v___x_595_);
v___x_597_ = ((size_t)1ULL);
v___x_598_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_592_, v___x_596_, v___x_597_, v_x_593_, v_x_594_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(lean_object* v_mvarId_599_, lean_object* v_val_600_, lean_object* v___y_601_){
_start:
{
lean_object* v___x_603_; lean_object* v_mctx_604_; lean_object* v_cache_605_; lean_object* v_zetaDeltaFVarIds_606_; lean_object* v_postponed_607_; lean_object* v_diag_608_; lean_object* v___x_610_; uint8_t v_isShared_611_; uint8_t v_isSharedCheck_636_; 
v___x_603_ = lean_st_ref_take(v___y_601_);
v_mctx_604_ = lean_ctor_get(v___x_603_, 0);
v_cache_605_ = lean_ctor_get(v___x_603_, 1);
v_zetaDeltaFVarIds_606_ = lean_ctor_get(v___x_603_, 2);
v_postponed_607_ = lean_ctor_get(v___x_603_, 3);
v_diag_608_ = lean_ctor_get(v___x_603_, 4);
v_isSharedCheck_636_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_636_ == 0)
{
v___x_610_ = v___x_603_;
v_isShared_611_ = v_isSharedCheck_636_;
goto v_resetjp_609_;
}
else
{
lean_inc(v_diag_608_);
lean_inc(v_postponed_607_);
lean_inc(v_zetaDeltaFVarIds_606_);
lean_inc(v_cache_605_);
lean_inc(v_mctx_604_);
lean_dec(v___x_603_);
v___x_610_ = lean_box(0);
v_isShared_611_ = v_isSharedCheck_636_;
goto v_resetjp_609_;
}
v_resetjp_609_:
{
lean_object* v_depth_612_; lean_object* v_levelAssignDepth_613_; lean_object* v_lmvarCounter_614_; lean_object* v_mvarCounter_615_; lean_object* v_lDecls_616_; lean_object* v_decls_617_; lean_object* v_userNames_618_; lean_object* v_lAssignment_619_; lean_object* v_eAssignment_620_; lean_object* v_dAssignment_621_; lean_object* v___x_623_; uint8_t v_isShared_624_; uint8_t v_isSharedCheck_635_; 
v_depth_612_ = lean_ctor_get(v_mctx_604_, 0);
v_levelAssignDepth_613_ = lean_ctor_get(v_mctx_604_, 1);
v_lmvarCounter_614_ = lean_ctor_get(v_mctx_604_, 2);
v_mvarCounter_615_ = lean_ctor_get(v_mctx_604_, 3);
v_lDecls_616_ = lean_ctor_get(v_mctx_604_, 4);
v_decls_617_ = lean_ctor_get(v_mctx_604_, 5);
v_userNames_618_ = lean_ctor_get(v_mctx_604_, 6);
v_lAssignment_619_ = lean_ctor_get(v_mctx_604_, 7);
v_eAssignment_620_ = lean_ctor_get(v_mctx_604_, 8);
v_dAssignment_621_ = lean_ctor_get(v_mctx_604_, 9);
v_isSharedCheck_635_ = !lean_is_exclusive(v_mctx_604_);
if (v_isSharedCheck_635_ == 0)
{
v___x_623_ = v_mctx_604_;
v_isShared_624_ = v_isSharedCheck_635_;
goto v_resetjp_622_;
}
else
{
lean_inc(v_dAssignment_621_);
lean_inc(v_eAssignment_620_);
lean_inc(v_lAssignment_619_);
lean_inc(v_userNames_618_);
lean_inc(v_decls_617_);
lean_inc(v_lDecls_616_);
lean_inc(v_mvarCounter_615_);
lean_inc(v_lmvarCounter_614_);
lean_inc(v_levelAssignDepth_613_);
lean_inc(v_depth_612_);
lean_dec(v_mctx_604_);
v___x_623_ = lean_box(0);
v_isShared_624_ = v_isSharedCheck_635_;
goto v_resetjp_622_;
}
v_resetjp_622_:
{
lean_object* v___x_625_; lean_object* v___x_627_; 
v___x_625_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_eAssignment_620_, v_mvarId_599_, v_val_600_);
if (v_isShared_624_ == 0)
{
lean_ctor_set(v___x_623_, 8, v___x_625_);
v___x_627_ = v___x_623_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_634_; 
v_reuseFailAlloc_634_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_634_, 0, v_depth_612_);
lean_ctor_set(v_reuseFailAlloc_634_, 1, v_levelAssignDepth_613_);
lean_ctor_set(v_reuseFailAlloc_634_, 2, v_lmvarCounter_614_);
lean_ctor_set(v_reuseFailAlloc_634_, 3, v_mvarCounter_615_);
lean_ctor_set(v_reuseFailAlloc_634_, 4, v_lDecls_616_);
lean_ctor_set(v_reuseFailAlloc_634_, 5, v_decls_617_);
lean_ctor_set(v_reuseFailAlloc_634_, 6, v_userNames_618_);
lean_ctor_set(v_reuseFailAlloc_634_, 7, v_lAssignment_619_);
lean_ctor_set(v_reuseFailAlloc_634_, 8, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_634_, 9, v_dAssignment_621_);
v___x_627_ = v_reuseFailAlloc_634_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_629_; 
if (v_isShared_611_ == 0)
{
lean_ctor_set(v___x_610_, 0, v___x_627_);
v___x_629_ = v___x_610_;
goto v_reusejp_628_;
}
else
{
lean_object* v_reuseFailAlloc_633_; 
v_reuseFailAlloc_633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_627_);
lean_ctor_set(v_reuseFailAlloc_633_, 1, v_cache_605_);
lean_ctor_set(v_reuseFailAlloc_633_, 2, v_zetaDeltaFVarIds_606_);
lean_ctor_set(v_reuseFailAlloc_633_, 3, v_postponed_607_);
lean_ctor_set(v_reuseFailAlloc_633_, 4, v_diag_608_);
v___x_629_ = v_reuseFailAlloc_633_;
goto v_reusejp_628_;
}
v_reusejp_628_:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_630_ = lean_st_ref_set(v___y_601_, v___x_629_);
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
lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_701_; lean_object* v_mvarId_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_705_; lean_object* v___y_706_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v_newVal_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_760_; lean_object* v___y_784_; lean_object* v___y_785_; uint8_t v___y_786_; lean_object* v___y_787_; lean_object* v_major_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; uint8_t v___y_825_; lean_object* v___y_826_; lean_object* v_motive_827_; lean_object* v_newType_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___y_831_; lean_object* v___y_832_; lean_object* v___x_843_; 
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
v___x_688_ = l_Lean_Meta_FVarSubst_insert(v___y_685_, v_fvarId_662_, v___y_687_);
v___x_689_ = l_Lean_Meta_FVarSubst_insert(v___x_688_, v_hFVarId_663_, v___x_664_);
v___x_690_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_690_, 0, v___x_689_);
lean_ctor_set(v___x_690_, 1, v___y_686_);
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
lean_dec_ref(v___y_693_);
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref(v___x_697_);
v___y_685_ = v_a_698_;
v___y_686_ = v___y_694_;
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
v___y_685_ = v_a_699_;
v___y_686_ = v___y_694_;
v___y_687_ = v___y_693_;
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
v___y_693_ = v___y_701_;
v___y_694_ = v_snd_714_;
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
v___y_693_ = v___y_701_;
v___y_694_ = v_snd_716_;
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
v___y_693_ = v___y_701_;
v___y_694_ = v_snd_716_;
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
v___x_793_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_785_, v_a_675_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_793_) == 0)
{
if (v___y_786_ == 0)
{
lean_object* v_a_794_; lean_object* v___x_795_; 
v_a_794_ = lean_ctor_get(v___x_793_, 0);
lean_inc_n(v_a_794_, 2);
lean_dec_ref_known(v___x_793_, 1);
v___x_795_ = l_Lean_Meta_mkEqNDRec(v___y_784_, v_a_794_, v_major_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_795_) == 0)
{
lean_object* v_a_796_; 
v_a_796_ = lean_ctor_get(v___x_795_, 0);
lean_inc(v_a_796_);
lean_dec_ref_known(v___x_795_, 1);
v___y_754_ = v___y_787_;
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
lean_dec_ref(v___y_787_);
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
v___x_806_ = l_Lean_Meta_mkEqRec(v___y_784_, v_a_805_, v_major_788_, v___y_789_, v___y_790_, v___y_791_, v___y_792_);
if (lean_obj_tag(v___x_806_) == 0)
{
lean_object* v_a_807_; 
v_a_807_ = lean_ctor_get(v___x_806_, 0);
lean_inc(v_a_807_);
lean_dec_ref_known(v___x_806_, 1);
v___y_754_ = v___y_787_;
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
lean_dec_ref(v___y_787_);
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
lean_dec_ref(v___y_784_);
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
v___y_784_ = v_motive_827_;
v___y_785_ = v_newType_828_;
v___y_786_ = v___y_825_;
v___y_787_ = v___y_826_;
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
v___y_784_ = v_motive_827_;
v___y_785_ = v_newType_828_;
v___y_786_ = v___y_825_;
v___y_787_ = v___y_826_;
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
uint8_t v_clearH_boxed_979_; uint8_t v_skip_boxed_980_; uint8_t v___x_33648__boxed_981_; uint8_t v_symm_boxed_982_; uint8_t v___x_33652__boxed_983_; lean_object* v_res_984_; 
v_clearH_boxed_979_ = lean_unbox(v_clearH_962_);
v_skip_boxed_980_ = lean_unbox(v_skip_966_);
v___x_33648__boxed_981_ = lean_unbox(v___x_967_);
v_symm_boxed_982_ = lean_unbox(v_symm_971_);
v___x_33652__boxed_983_ = lean_unbox(v___x_972_);
v_res_984_ = l_Lean_Meta_substCore___lam__2(v_snd_955_, v___x_956_, v_fvarId_957_, v_hFVarId_958_, v___x_959_, v_fst_960_, v_fvarSubst_961_, v_clearH_boxed_979_, v___x_963_, v___x_964_, v___x_965_, v_skip_boxed_980_, v___x_33648__boxed_981_, v___x_968_, v___x_969_, v_a_970_, v_symm_boxed_982_, v___x_33652__boxed_983_, v___x_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
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
lean_object* v_val_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1465_; 
v_val_1141_ = lean_ctor_get(v_a_1138_, 0);
v_isSharedCheck_1465_ = !lean_is_exclusive(v_a_1138_);
if (v_isSharedCheck_1465_ == 0)
{
v___x_1143_ = v_a_1138_;
v_isShared_1144_ = v_isSharedCheck_1465_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_val_1141_);
lean_dec(v_a_1138_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1465_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_snd_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1463_; 
v_snd_1145_ = lean_ctor_get(v_val_1141_, 1);
v_isSharedCheck_1463_ = !lean_is_exclusive(v_val_1141_);
if (v_isSharedCheck_1463_ == 0)
{
lean_object* v_unused_1464_; 
v_unused_1464_ = lean_ctor_get(v_val_1141_, 0);
lean_dec(v_unused_1464_);
v___x_1147_ = v_val_1141_;
v_isShared_1148_ = v_isSharedCheck_1463_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_snd_1145_);
lean_dec(v_val_1141_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1463_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v_fst_1149_; lean_object* v_snd_1150_; lean_object* v___x_1152_; uint8_t v_isShared_1153_; uint8_t v_isSharedCheck_1462_; 
v_fst_1149_ = lean_ctor_get(v_snd_1145_, 0);
v_snd_1150_ = lean_ctor_get(v_snd_1145_, 1);
v_isSharedCheck_1462_ = !lean_is_exclusive(v_snd_1145_);
if (v_isSharedCheck_1462_ == 0)
{
v___x_1152_ = v_snd_1145_;
v_isShared_1153_ = v_isSharedCheck_1462_;
goto v_resetjp_1151_;
}
else
{
lean_inc(v_snd_1150_);
lean_inc(v_fst_1149_);
lean_dec(v_snd_1145_);
v___x_1152_ = lean_box(0);
v_isShared_1153_ = v_isSharedCheck_1462_;
goto v_resetjp_1151_;
}
v_resetjp_1151_:
{
uint8_t v___x_1154_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; uint8_t v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; lean_object* v___y_1171_; lean_object* v___y_1172_; uint8_t v_skip_1173_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; uint8_t v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; uint8_t v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1196_; lean_object* v___y_1197_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; uint8_t v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; uint8_t v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1239_; lean_object* v___y_1240_; lean_object* v___y_1241_; lean_object* v___y_1242_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; uint8_t v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; uint8_t v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1286_; lean_object* v___y_1287_; lean_object* v___y_1288_; lean_object* v___y_1289_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1338_; lean_object* v___y_1339_; lean_object* v___y_1340_; lean_object* v___y_1341_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1396_; lean_object* v___y_1397_; lean_object* v___y_1398_; lean_object* v___y_1399_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1458_; 
v___x_1154_ = 1;
if (v_symm_1071_ == 0)
{
lean_inc(v_fst_1149_);
v___y_1458_ = v_fst_1149_;
goto v___jp_1457_;
}
else
{
lean_inc(v_snd_1150_);
v___y_1458_ = v_snd_1150_;
goto v___jp_1457_;
}
v___jp_1155_:
{
lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; 
v___x_1174_ = lean_box(v_clearH_1069_);
v___x_1175_ = lean_box(v_skip_1173_);
v___x_1176_ = lean_box(v___x_1154_);
v___x_1177_ = lean_box(v_symm_1071_);
v___x_1178_ = lean_box(v___y_1160_);
v___f_1179_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__2___boxed), 24, 19);
lean_closure_set(v___f_1179_, 0, v___y_1158_);
lean_closure_set(v___f_1179_, 1, v___y_1156_);
lean_closure_set(v___f_1179_, 2, v___y_1164_);
lean_closure_set(v___f_1179_, 3, v_hFVarId_1067_);
lean_closure_set(v___f_1179_, 4, v___y_1166_);
lean_closure_set(v___f_1179_, 5, v___y_1165_);
lean_closure_set(v___f_1179_, 6, v_fvarSubst_1070_);
lean_closure_set(v___f_1179_, 7, v___x_1174_);
lean_closure_set(v___f_1179_, 8, v___y_1172_);
lean_closure_set(v___f_1179_, 9, v___y_1168_);
lean_closure_set(v___f_1179_, 10, v___y_1162_);
lean_closure_set(v___f_1179_, 11, v___x_1175_);
lean_closure_set(v___f_1179_, 12, v___x_1176_);
lean_closure_set(v___f_1179_, 13, v___y_1171_);
lean_closure_set(v___f_1179_, 14, v___y_1159_);
lean_closure_set(v___f_1179_, 15, v_a_1117_);
lean_closure_set(v___f_1179_, 16, v___x_1177_);
lean_closure_set(v___f_1179_, 17, v___x_1178_);
lean_closure_set(v___f_1179_, 18, v___y_1157_);
v___x_1180_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v___y_1169_, v___f_1179_, v___y_1167_, v___y_1163_, v___y_1170_, v___y_1161_);
lean_dec(v___y_1161_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1163_);
lean_dec_ref(v___y_1167_);
return v___x_1180_;
}
v___jp_1181_:
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; uint8_t v___x_1204_; 
v___x_1198_ = lean_unsigned_to_nat(0u);
v___x_1199_ = lean_array_get(v___x_1068_, v___y_1190_, v___x_1198_);
lean_inc(v___x_1199_);
v___x_1200_ = l_Lean_mkFVar(v___x_1199_);
v___x_1201_ = lean_unsigned_to_nat(1u);
v___x_1202_ = lean_array_get(v___x_1068_, v___y_1190_, v___x_1201_);
lean_dec_ref(v___y_1190_);
lean_inc(v___x_1202_);
v___x_1203_ = l_Lean_mkFVar(v___x_1202_);
v___x_1204_ = lean_bool_not(v_tryToSkip_1072_);
if (v___x_1204_ == 0)
{
lean_object* v___x_1205_; uint8_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1205_ = lean_array_get_size(v___y_1193_);
lean_dec_ref(v___y_1193_);
v___x_1206_ = lean_nat_dec_eq(v___x_1205_, v___y_1189_);
lean_dec(v___y_1189_);
v___x_1207_ = lean_bool_not(v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; 
lean_inc(v___y_1191_);
v___x_1208_ = l_Lean_MVarId_getType(v___y_1191_, v___y_1194_, v___y_1195_, v___y_1196_, v___y_1197_);
if (lean_obj_tag(v___x_1208_) == 0)
{
lean_object* v_a_1209_; lean_object* v___x_1210_; lean_object* v_a_1211_; uint8_t v___x_1212_; 
v_a_1209_ = lean_ctor_get(v___x_1208_, 0);
lean_inc_n(v_a_1209_, 2);
lean_dec_ref_known(v___x_1208_, 1);
lean_inc(v___x_1199_);
v___x_1210_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1209_, v___x_1199_, v___y_1195_);
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref(v___x_1210_);
v___x_1212_ = lean_unbox(v_a_1211_);
lean_dec(v_a_1211_);
if (v___x_1212_ == 0)
{
lean_object* v___x_1213_; lean_object* v_a_1214_; uint8_t v___x_1215_; 
lean_inc(v___x_1202_);
v___x_1213_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1209_, v___x_1202_, v___y_1195_);
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
lean_inc(v_a_1214_);
lean_dec_ref(v___x_1213_);
v___x_1215_ = lean_unbox(v_a_1214_);
lean_dec(v_a_1214_);
if (v___x_1215_ == 0)
{
lean_dec_ref(v___x_1203_);
lean_dec_ref(v___x_1200_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec(v_a_1117_);
lean_dec(v_hFVarId_1067_);
v___y_1079_ = v___y_1195_;
v___y_1080_ = v___x_1202_;
v___y_1081_ = v___y_1194_;
v___y_1082_ = v___x_1199_;
v___y_1083_ = v___y_1191_;
v___y_1084_ = v___y_1196_;
v___y_1085_ = v___y_1197_;
goto v___jp_1078_;
}
else
{
v___y_1156_ = v___x_1202_;
v___y_1157_ = v___x_1201_;
v___y_1158_ = v___y_1187_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1186_;
v___y_1161_ = v___y_1197_;
v___y_1162_ = v___y_1182_;
v___y_1163_ = v___y_1195_;
v___y_1164_ = v___y_1184_;
v___y_1165_ = v___y_1183_;
v___y_1166_ = v___x_1203_;
v___y_1167_ = v___y_1194_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___y_1191_;
v___y_1170_ = v___y_1196_;
v___y_1171_ = v___y_1188_;
v___y_1172_ = v___x_1200_;
v_skip_1173_ = v___y_1192_;
goto v___jp_1155_;
}
}
else
{
lean_dec(v_a_1209_);
v___y_1156_ = v___x_1202_;
v___y_1157_ = v___x_1201_;
v___y_1158_ = v___y_1187_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1186_;
v___y_1161_ = v___y_1197_;
v___y_1162_ = v___y_1182_;
v___y_1163_ = v___y_1195_;
v___y_1164_ = v___y_1184_;
v___y_1165_ = v___y_1183_;
v___y_1166_ = v___x_1203_;
v___y_1167_ = v___y_1194_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___y_1191_;
v___y_1170_ = v___y_1196_;
v___y_1171_ = v___y_1188_;
v___y_1172_ = v___x_1200_;
v_skip_1173_ = v___y_1192_;
goto v___jp_1155_;
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec_ref(v___x_1203_);
lean_dec(v___x_1202_);
lean_dec_ref(v___x_1200_);
lean_dec(v___x_1199_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
lean_dec(v___y_1195_);
lean_dec_ref(v___y_1194_);
lean_dec(v___y_1191_);
lean_dec(v___y_1188_);
lean_dec(v___y_1187_);
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec_ref(v___y_1183_);
lean_dec(v___y_1182_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
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
else
{
v___y_1156_ = v___x_1202_;
v___y_1157_ = v___x_1201_;
v___y_1158_ = v___y_1187_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1186_;
v___y_1161_ = v___y_1197_;
v___y_1162_ = v___y_1182_;
v___y_1163_ = v___y_1195_;
v___y_1164_ = v___y_1184_;
v___y_1165_ = v___y_1183_;
v___y_1166_ = v___x_1203_;
v___y_1167_ = v___y_1194_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___y_1191_;
v___y_1170_ = v___y_1196_;
v___y_1171_ = v___y_1188_;
v___y_1172_ = v___x_1200_;
v_skip_1173_ = v___y_1192_;
goto v___jp_1155_;
}
}
else
{
lean_dec_ref(v___y_1193_);
lean_dec(v___y_1189_);
v___y_1156_ = v___x_1202_;
v___y_1157_ = v___x_1201_;
v___y_1158_ = v___y_1187_;
v___y_1159_ = v___x_1199_;
v___y_1160_ = v___y_1186_;
v___y_1161_ = v___y_1197_;
v___y_1162_ = v___y_1182_;
v___y_1163_ = v___y_1195_;
v___y_1164_ = v___y_1184_;
v___y_1165_ = v___y_1183_;
v___y_1166_ = v___x_1203_;
v___y_1167_ = v___y_1194_;
v___y_1168_ = v___y_1185_;
v___y_1169_ = v___y_1191_;
v___y_1170_ = v___y_1196_;
v___y_1171_ = v___y_1188_;
v___y_1172_ = v___x_1200_;
v_skip_1173_ = v___y_1192_;
goto v___jp_1155_;
}
}
v___jp_1224_:
{
lean_object* v___x_1243_; 
lean_inc_ref(v___y_1238_);
lean_inc(v___y_1242_);
lean_inc_ref(v___y_1241_);
lean_inc(v___y_1240_);
lean_inc_ref(v___y_1239_);
v___x_1243_ = lean_apply_5(v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_, lean_box(0));
if (lean_obj_tag(v___x_1243_) == 0)
{
lean_object* v_a_1244_; uint8_t v___x_1245_; 
v_a_1244_ = lean_ctor_get(v___x_1243_, 0);
lean_inc(v_a_1244_);
lean_dec_ref_known(v___x_1243_, 1);
v___x_1245_ = lean_unbox(v_a_1244_);
lean_dec(v_a_1244_);
if (v___x_1245_ == 0)
{
lean_dec(v___y_1234_);
lean_del_object(v___x_1152_);
v___y_1182_ = v___y_1225_;
v___y_1183_ = v___y_1227_;
v___y_1184_ = v___y_1226_;
v___y_1185_ = v___y_1228_;
v___y_1186_ = v___y_1230_;
v___y_1187_ = v___y_1229_;
v___y_1188_ = v___y_1231_;
v___y_1189_ = v___y_1233_;
v___y_1190_ = v___y_1232_;
v___y_1191_ = v___y_1235_;
v___y_1192_ = v___y_1236_;
v___y_1193_ = v___y_1237_;
v___y_1194_ = v___y_1239_;
v___y_1195_ = v___y_1240_;
v___y_1196_ = v___y_1241_;
v___y_1197_ = v___y_1242_;
goto v___jp_1181_;
}
else
{
lean_object* v___x_1246_; size_t v_sz_1247_; size_t v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1255_; 
v___x_1246_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__11, &l_Lean_Meta_substCore___lam__3___closed__11_once, _init_l_Lean_Meta_substCore___lam__3___closed__11);
v_sz_1247_ = lean_array_size(v___y_1237_);
v___x_1248_ = ((size_t)0ULL);
lean_inc_ref(v___y_1237_);
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1247_, v___x_1248_, v___y_1237_);
v___x_1250_ = lean_array_to_list(v___x_1249_);
v___x_1251_ = lean_box(0);
v___x_1252_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(v___x_1250_, v___x_1251_);
v___x_1253_ = l_Lean_MessageData_ofList(v___x_1252_);
if (v_isShared_1153_ == 0)
{
lean_ctor_set_tag(v___x_1152_, 7);
lean_ctor_set(v___x_1152_, 1, v___x_1253_);
lean_ctor_set(v___x_1152_, 0, v___x_1246_);
v___x_1255_ = v___x_1152_;
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
v___x_1256_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1234_, v___x_1255_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1256_) == 0)
{
lean_dec_ref_known(v___x_1256_, 1);
v___y_1182_ = v___y_1225_;
v___y_1183_ = v___y_1227_;
v___y_1184_ = v___y_1226_;
v___y_1185_ = v___y_1228_;
v___y_1186_ = v___y_1230_;
v___y_1187_ = v___y_1229_;
v___y_1188_ = v___y_1231_;
v___y_1189_ = v___y_1233_;
v___y_1190_ = v___y_1232_;
v___y_1191_ = v___y_1235_;
v___y_1192_ = v___y_1236_;
v___y_1193_ = v___y_1237_;
v___y_1194_ = v___y_1239_;
v___y_1195_ = v___y_1240_;
v___y_1196_ = v___y_1241_;
v___y_1197_ = v___y_1242_;
goto v___jp_1181_;
}
else
{
lean_object* v_a_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1264_; 
lean_dec(v___y_1242_);
lean_dec_ref(v___y_1241_);
lean_dec(v___y_1240_);
lean_dec_ref(v___y_1239_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1235_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
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
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
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
lean_inc(v___y_1280_);
v___x_1291_ = l_Lean_Meta_introNCore(v___y_1285_, v___y_1280_, v___x_1290_, v___y_1282_, v___x_1154_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1291_) == 0)
{
lean_object* v_a_1292_; lean_object* v_fst_1293_; lean_object* v_snd_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1323_; 
v_a_1292_ = lean_ctor_get(v___x_1291_, 0);
lean_inc(v_a_1292_);
lean_dec_ref_known(v___x_1291_, 1);
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
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1289_);
lean_inc_ref(v___y_1288_);
lean_inc(v___y_1287_);
lean_inc_ref(v___y_1286_);
v___x_1298_ = lean_apply_5(v___y_1284_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_, lean_box(0));
if (lean_obj_tag(v___x_1298_) == 0)
{
lean_object* v_a_1299_; uint8_t v___x_1300_; 
v_a_1299_ = lean_ctor_get(v___x_1298_, 0);
lean_inc(v_a_1299_);
lean_dec_ref_known(v___x_1298_, 1);
v___x_1300_ = lean_unbox(v_a_1299_);
lean_dec(v_a_1299_);
if (v___x_1300_ == 0)
{
lean_del_object(v___x_1296_);
lean_inc(v_snd_1294_);
v___y_1225_ = v___x_1290_;
v___y_1226_ = v___y_1275_;
v___y_1227_ = v___y_1276_;
v___y_1228_ = v___y_1277_;
v___y_1229_ = v_snd_1294_;
v___y_1230_ = v___y_1278_;
v___y_1231_ = v___y_1279_;
v___y_1232_ = v_fst_1293_;
v___y_1233_ = v___y_1280_;
v___y_1234_ = v___y_1281_;
v___y_1235_ = v_snd_1294_;
v___y_1236_ = v___y_1282_;
v___y_1237_ = v___y_1283_;
v___y_1238_ = v___y_1284_;
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
lean_inc(v___y_1281_);
v___x_1305_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1281_, v___x_1304_, v___y_1286_, v___y_1287_, v___y_1288_, v___y_1289_);
if (lean_obj_tag(v___x_1305_) == 0)
{
lean_dec_ref_known(v___x_1305_, 1);
lean_inc(v_snd_1294_);
v___y_1225_ = v___x_1290_;
v___y_1226_ = v___y_1275_;
v___y_1227_ = v___y_1276_;
v___y_1228_ = v___y_1277_;
v___y_1229_ = v_snd_1294_;
v___y_1230_ = v___y_1278_;
v___y_1231_ = v___y_1279_;
v___y_1232_ = v_fst_1293_;
v___y_1233_ = v___y_1280_;
v___y_1234_ = v___y_1281_;
v___y_1235_ = v_snd_1294_;
v___y_1236_ = v___y_1282_;
v___y_1237_ = v___y_1283_;
v___y_1238_ = v___y_1284_;
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
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
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
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
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
lean_dec_ref(v___y_1283_);
lean_dec(v___y_1281_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec(v___y_1277_);
lean_dec_ref(v___y_1276_);
lean_dec(v___y_1275_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
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
v___x_1344_ = lean_array_push(v___x_1343_, v___y_1337_);
lean_inc(v_hFVarId_1067_);
v___x_1345_ = lean_array_push(v___x_1344_, v_hFVarId_1067_);
v___x_1346_ = 0;
v___x_1347_ = l_Lean_MVarId_revert(v_mvarId_1066_, v___x_1345_, v___x_1154_, v___x_1346_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1347_) == 0)
{
lean_object* v_a_1348_; lean_object* v_fst_1349_; lean_object* v_snd_1350_; lean_object* v___x_1352_; uint8_t v_isShared_1353_; uint8_t v_isSharedCheck_1379_; 
v_a_1348_ = lean_ctor_get(v___x_1347_, 0);
lean_inc(v_a_1348_);
lean_dec_ref_known(v___x_1347_, 1);
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
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1341_);
lean_inc_ref(v___y_1340_);
lean_inc(v___y_1339_);
lean_inc_ref(v___y_1338_);
v___x_1354_ = lean_apply_5(v___y_1336_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_, lean_box(0));
if (lean_obj_tag(v___x_1354_) == 0)
{
lean_object* v_a_1355_; uint8_t v___x_1356_; 
v_a_1355_ = lean_ctor_get(v___x_1354_, 0);
lean_inc(v_a_1355_);
lean_dec_ref_known(v___x_1354_, 1);
v___x_1356_ = lean_unbox(v_a_1355_);
lean_dec(v_a_1355_);
if (v___x_1356_ == 0)
{
lean_del_object(v___x_1352_);
lean_inc(v_fst_1349_);
v___y_1275_ = v___y_1333_;
v___y_1276_ = v_fst_1349_;
v___y_1277_ = v___x_1342_;
v___y_1278_ = v___x_1346_;
v___y_1279_ = v___y_1334_;
v___y_1280_ = v___x_1342_;
v___y_1281_ = v___y_1335_;
v___y_1282_ = v___x_1346_;
v___y_1283_ = v_fst_1349_;
v___y_1284_ = v___y_1336_;
v___y_1285_ = v_snd_1350_;
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
lean_inc(v___y_1335_);
v___x_1361_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1335_, v___x_1360_, v___y_1338_, v___y_1339_, v___y_1340_, v___y_1341_);
if (lean_obj_tag(v___x_1361_) == 0)
{
lean_dec_ref_known(v___x_1361_, 1);
lean_inc(v_fst_1349_);
v___y_1275_ = v___y_1333_;
v___y_1276_ = v_fst_1349_;
v___y_1277_ = v___x_1342_;
v___y_1278_ = v___x_1346_;
v___y_1279_ = v___y_1334_;
v___y_1280_ = v___x_1342_;
v___y_1281_ = v___y_1335_;
v___y_1282_ = v___x_1346_;
v___y_1283_ = v_fst_1349_;
v___y_1284_ = v___y_1336_;
v___y_1285_ = v_snd_1350_;
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
lean_dec(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec(v___y_1333_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
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
lean_dec(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec(v___y_1333_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
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
lean_dec(v___y_1335_);
lean_dec(v___y_1334_);
lean_dec(v___y_1333_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
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
lean_inc(v___y_1393_);
lean_inc_ref(v___y_1394_);
v___x_1400_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v___y_1394_, v___y_1393_, v___y_1397_);
v_a_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_a_1401_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = lean_unbox(v_a_1401_);
lean_dec(v_a_1401_);
if (v___x_1402_ == 0)
{
lean_dec_ref(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_del_object(v___x_1147_);
lean_del_object(v___x_1143_);
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
if (v_isShared_1148_ == 0)
{
lean_ctor_set_tag(v___x_1147_, 7);
lean_ctor_set(v___x_1147_, 1, v___x_1404_);
lean_ctor_set(v___x_1147_, 0, v___x_1403_);
v___x_1406_ = v___x_1147_;
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
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 0, v___x_1410_);
v___x_1412_ = v___x_1143_;
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
lean_inc(v_mvarId_1066_);
v___x_1413_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1118_, v_mvarId_1066_, v___x_1412_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_dec_ref_known(v___x_1413_, 1);
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
lean_dec(v___y_1391_);
lean_dec(v___y_1390_);
lean_dec(v___y_1389_);
lean_del_object(v___x_1152_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
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
v___x_1427_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1426_, v___y_1074_);
if (lean_obj_tag(v___y_1425_) == 1)
{
lean_object* v_a_1428_; lean_object* v_fvarId_1429_; lean_object* v___x_1430_; lean_object* v___f_1431_; lean_object* v___x_1432_; lean_object* v_a_1433_; uint8_t v___x_1434_; 
lean_dec_ref(v___x_1122_);
v_a_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc(v_a_1428_);
lean_dec_ref(v___x_1427_);
v_fvarId_1429_ = lean_ctor_get(v___y_1425_, 0);
lean_inc(v_fvarId_1429_);
v___x_1430_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___f_1431_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__23));
v___x_1432_ = l_Lean_Meta_substCore___lam__0(v___x_1430_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
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
v___y_1391_ = v___x_1430_;
v___y_1392_ = v___f_1431_;
v___y_1393_ = v_fvarId_1429_;
v___y_1394_ = v_a_1428_;
v___y_1395_ = v___y_1425_;
v___y_1396_ = v___y_1073_;
v___y_1397_ = v___y_1074_;
v___y_1398_ = v___y_1075_;
v___y_1399_ = v___y_1076_;
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
v___x_1446_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_1430_, v___x_1445_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
if (lean_obj_tag(v___x_1446_) == 0)
{
lean_dec_ref_known(v___x_1446_, 1);
lean_inc(v_fvarId_1429_);
v___y_1389_ = v_fvarId_1429_;
v___y_1390_ = v___x_1430_;
v___y_1391_ = v___x_1430_;
v___y_1392_ = v___f_1431_;
v___y_1393_ = v_fvarId_1429_;
v___y_1394_ = v_a_1428_;
v___y_1395_ = v___y_1425_;
v___y_1396_ = v___y_1073_;
v___y_1397_ = v___y_1074_;
v___y_1398_ = v___y_1075_;
v___y_1399_ = v___y_1076_;
goto v___jp_1388_;
}
else
{
lean_object* v_a_1447_; lean_object* v___x_1449_; uint8_t v_isShared_1450_; uint8_t v_isSharedCheck_1454_; 
lean_dec(v_fvarId_1429_);
lean_dec(v_a_1428_);
lean_dec_ref_known(v___y_1425_, 1);
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
lean_del_object(v___x_1152_);
lean_del_object(v___x_1147_);
lean_del_object(v___x_1143_);
lean_dec(v_a_1117_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
if (v_symm_1071_ == 0)
{
lean_object* v___x_1455_; 
v___x_1455_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__30));
v___y_1124_ = v___y_1425_;
v___y_1125_ = v___x_1455_;
goto v___jp_1123_;
}
else
{
lean_object* v___x_1456_; 
v___x_1456_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__31));
v___y_1124_ = v___y_1425_;
v___y_1125_ = v___x_1456_;
goto v___jp_1123_;
}
}
}
v___jp_1457_:
{
lean_object* v___x_1459_; 
v___x_1459_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1458_, v___y_1074_);
if (v_symm_1071_ == 0)
{
lean_object* v_a_1460_; 
lean_dec(v_fst_1149_);
v_a_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1460_);
lean_dec_ref(v___x_1459_);
v___y_1425_ = v_a_1460_;
v___y_1426_ = v_snd_1150_;
goto v___jp_1424_;
}
else
{
lean_object* v_a_1461_; 
lean_dec(v_snd_1150_);
v_a_1461_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_a_1461_);
lean_dec_ref(v___x_1459_);
v___y_1425_ = v_a_1461_;
v___y_1426_ = v_fst_1149_;
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
lean_dec_ref(v___x_1122_);
lean_dec(v_a_1117_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
v_a_1466_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1473_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1473_ == 0)
{
v___x_1468_ = v___x_1137_;
v_isShared_1469_ = v_isSharedCheck_1473_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_a_1466_);
lean_dec(v___x_1137_);
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
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1481_; 
lean_dec(v_a_1117_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
v_a_1474_ = lean_ctor_get(v___x_1120_, 0);
v_isSharedCheck_1481_ = !lean_is_exclusive(v___x_1120_);
if (v_isSharedCheck_1481_ == 0)
{
v___x_1476_ = v___x_1120_;
v_isShared_1477_ = v_isSharedCheck_1481_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1120_);
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
lean_dec(v_a_1117_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
v_a_1482_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1119_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1119_);
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
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v_fvarSubst_1070_);
lean_dec(v_hFVarId_1067_);
lean_dec(v_mvarId_1066_);
v_a_1490_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1116_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1116_);
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
v___jp_1078_:
{
if (v_clearH_1069_ == 0)
{
lean_object* v___x_1086_; lean_object* v___x_1087_; 
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1080_);
lean_dec(v___y_1079_);
v___x_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1086_, 0, v_fvarSubst_1070_);
lean_ctor_set(v___x_1086_, 1, v___y_1083_);
v___x_1087_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
return v___x_1087_;
}
else
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_MVarId_clear(v___y_1083_, v___y_1080_, v___y_1081_, v___y_1079_, v___y_1084_, v___y_1085_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
v___x_1090_ = l_Lean_MVarId_clear(v_a_1089_, v___y_1082_, v___y_1081_, v___y_1079_, v___y_1084_, v___y_1085_);
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1081_);
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
lean_dec(v___y_1085_);
lean_dec_ref(v___y_1084_);
lean_dec(v___y_1082_);
lean_dec_ref(v___y_1081_);
lean_dec(v___y_1079_);
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
size_t v_x_35452__boxed_1650_; size_t v_x_35453__boxed_1651_; lean_object* v_res_1652_; 
v_x_35452__boxed_1650_ = lean_unbox_usize(v_x_1646_);
lean_dec(v_x_1646_);
v_x_35453__boxed_1651_ = lean_unbox_usize(v_x_1647_);
lean_dec(v_x_1647_);
v_res_1652_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(v_00_u03b2_1644_, v_x_1645_, v_x_35452__boxed_1650_, v_x_35453__boxed_1651_, v_x_1648_, v_x_1649_);
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
lean_dec_ref_known(v___x_1692_, 1);
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
lean_dec_ref_known(v___x_1723_, 1);
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
lean_dec_ref_known(v___x_1727_, 1);
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
lean_dec_ref_known(v___x_1730_, 1);
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
lean_dec_ref_known(v___x_1730_, 1);
v___x_1735_ = l_Lean_MVarId_tryClear(v_a_1734_, v_fvarId_1684_, v___y_1687_, v___y_1688_, v___y_1689_, v___y_1690_);
if (lean_obj_tag(v___x_1735_) == 0)
{
lean_object* v_a_1736_; uint8_t v___x_1737_; lean_object* v___x_1738_; 
v_a_1736_ = lean_ctor_get(v___x_1735_, 0);
lean_inc(v_a_1736_);
lean_dec_ref_known(v___x_1735_, 1);
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
lean_object* v_val_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1962_; 
v_val_1856_ = lean_ctor_get(v_a_1855_, 0);
v_isSharedCheck_1962_ = !lean_is_exclusive(v_a_1855_);
if (v_isSharedCheck_1962_ == 0)
{
v___x_1858_ = v_a_1855_;
v_isShared_1859_ = v_isSharedCheck_1962_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_val_1856_);
lean_dec(v_a_1855_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1962_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
uint8_t v___x_1860_; 
v___x_1860_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1856_);
if (v___x_1860_ == 0)
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = l_Lean_LocalDecl_type(v_val_1856_);
v___x_1862_ = l_Lean_Meta_matchEq_x3f(v___x_1861_, v___y_1836_, v___y_1837_, v___y_1838_, v___y_1839_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v_a_1863_; 
v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_a_1863_);
lean_dec_ref_known(v___x_1862_, 1);
if (lean_obj_tag(v_a_1863_) == 1)
{
lean_object* v_val_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1953_; 
v_val_1864_ = lean_ctor_get(v_a_1863_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v_a_1863_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1866_ = v_a_1863_;
v_isShared_1867_ = v_isSharedCheck_1953_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_val_1864_);
lean_dec(v_a_1863_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1953_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v_snd_1868_; lean_object* v___x_1870_; uint8_t v_isShared_1871_; uint8_t v_isSharedCheck_1951_; 
v_snd_1868_ = lean_ctor_get(v_val_1864_, 1);
v_isSharedCheck_1951_ = !lean_is_exclusive(v_val_1864_);
if (v_isSharedCheck_1951_ == 0)
{
lean_object* v_unused_1952_; 
v_unused_1952_ = lean_ctor_get(v_val_1864_, 0);
lean_dec(v_unused_1952_);
v___x_1870_ = v_val_1864_;
v_isShared_1871_ = v_isSharedCheck_1951_;
goto v_resetjp_1869_;
}
else
{
lean_inc(v_snd_1868_);
lean_dec(v_val_1864_);
v___x_1870_ = lean_box(0);
v_isShared_1871_ = v_isSharedCheck_1951_;
goto v_resetjp_1869_;
}
v_resetjp_1869_:
{
lean_object* v_fst_1872_; lean_object* v_snd_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1950_; 
v_fst_1872_ = lean_ctor_get(v_snd_1868_, 0);
v_snd_1873_ = lean_ctor_get(v_snd_1868_, 1);
v_isSharedCheck_1950_ = !lean_is_exclusive(v_snd_1868_);
if (v_isSharedCheck_1950_ == 0)
{
v___x_1875_ = v_snd_1868_;
v_isShared_1876_ = v_isSharedCheck_1950_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_snd_1873_);
lean_inc(v_fst_1872_);
lean_dec(v_snd_1868_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1950_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1872_, v___y_1837_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v_a_1878_; lean_object* v___x_1879_; 
v_a_1878_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_a_1878_);
lean_dec_ref_known(v___x_1877_, 1);
v___x_1879_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1873_, v___y_1837_);
if (lean_obj_tag(v___x_1879_) == 0)
{
lean_object* v_a_1880_; lean_object* v___y_1882_; uint8_t v___y_1883_; lean_object* v___y_1905_; uint8_t v___y_1910_; uint8_t v___x_1931_; 
v_a_1880_ = lean_ctor_get(v___x_1879_, 0);
lean_inc(v_a_1880_);
lean_dec_ref_known(v___x_1879_, 1);
v___x_1931_ = l_Lean_Expr_isFVar(v_a_1880_);
if (v___x_1931_ == 0)
{
v___y_1910_ = v___x_1931_;
goto v___jp_1909_;
}
else
{
lean_object* v___x_1932_; uint8_t v___x_1933_; 
v___x_1932_ = l_Lean_Expr_fvarId_x21(v_a_1880_);
v___x_1933_ = l_Lean_instBEqFVarId_beq(v___x_1932_, v_x_1831_);
lean_dec(v___x_1932_);
v___y_1910_ = v___x_1933_;
goto v___jp_1909_;
}
v___jp_1881_:
{
if (v___y_1883_ == 0)
{
lean_dec(v_a_1880_);
lean_del_object(v___x_1875_);
lean_del_object(v___x_1866_);
lean_dec(v_val_1856_);
v_a_1842_ = v___x_1854_;
goto v___jp_1841_;
}
else
{
lean_object* v___x_1884_; 
lean_inc(v_x_1831_);
v___x_1884_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1880_, v_x_1831_, v___y_1882_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v_a_1885_; uint8_t v___x_1886_; uint8_t v___x_1887_; 
v_a_1885_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_a_1885_);
lean_dec_ref_known(v___x_1884_, 1);
v___x_1886_ = lean_unbox(v_a_1885_);
lean_dec(v_a_1885_);
v___x_1887_ = lean_bool_not(v___x_1886_);
if (v___x_1887_ == 0)
{
lean_del_object(v___x_1875_);
lean_del_object(v___x_1866_);
lean_dec(v_val_1856_);
v_a_1842_ = v___x_1854_;
goto v___jp_1841_;
}
else
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1891_; 
lean_dec(v_x_1831_);
v___x_1888_ = l_Lean_LocalDecl_fvarId(v_val_1856_);
lean_dec(v_val_1856_);
v___x_1889_ = lean_box(v___x_1860_);
if (v_isShared_1876_ == 0)
{
lean_ctor_set(v___x_1875_, 1, v___x_1889_);
lean_ctor_set(v___x_1875_, 0, v___x_1888_);
v___x_1891_ = v___x_1875_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1895_; 
v_reuseFailAlloc_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1895_, 0, v___x_1888_);
lean_ctor_set(v_reuseFailAlloc_1895_, 1, v___x_1889_);
v___x_1891_ = v_reuseFailAlloc_1895_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
lean_object* v___x_1893_; 
if (v_isShared_1867_ == 0)
{
lean_ctor_set(v___x_1866_, 0, v___x_1891_);
v___x_1893_ = v___x_1866_;
goto v_reusejp_1892_;
}
else
{
lean_object* v_reuseFailAlloc_1894_; 
v_reuseFailAlloc_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1894_, 0, v___x_1891_);
v___x_1893_ = v_reuseFailAlloc_1894_;
goto v_reusejp_1892_;
}
v_reusejp_1892_:
{
v_a_1850_ = v___x_1893_;
goto v___jp_1849_;
}
}
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_del_object(v___x_1875_);
lean_del_object(v___x_1866_);
lean_dec(v_val_1856_);
lean_dec(v_x_1831_);
v_a_1896_ = lean_ctor_get(v___x_1884_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1884_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1884_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1884_);
v___x_1898_ = lean_box(0);
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
v_resetjp_1897_:
{
lean_object* v___x_1901_; 
if (v_isShared_1899_ == 0)
{
v___x_1901_ = v___x_1898_;
goto v_reusejp_1900_;
}
else
{
lean_object* v_reuseFailAlloc_1902_; 
v_reuseFailAlloc_1902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1902_, 0, v_a_1896_);
v___x_1901_ = v_reuseFailAlloc_1902_;
goto v_reusejp_1900_;
}
v_reusejp_1900_:
{
return v___x_1901_;
}
}
}
}
}
v___jp_1904_:
{
uint8_t v___x_1906_; 
v___x_1906_ = l_Lean_Expr_isFVar(v_a_1878_);
if (v___x_1906_ == 0)
{
lean_dec(v_a_1878_);
v___y_1882_ = v___y_1905_;
v___y_1883_ = v___x_1906_;
goto v___jp_1881_;
}
else
{
lean_object* v___x_1907_; uint8_t v___x_1908_; 
v___x_1907_ = l_Lean_Expr_fvarId_x21(v_a_1878_);
lean_dec(v_a_1878_);
v___x_1908_ = l_Lean_instBEqFVarId_beq(v___x_1907_, v_x_1831_);
lean_dec(v___x_1907_);
v___y_1882_ = v___y_1905_;
v___y_1883_ = v___x_1908_;
goto v___jp_1881_;
}
}
v___jp_1909_:
{
if (v___y_1910_ == 0)
{
lean_del_object(v___x_1870_);
lean_del_object(v___x_1858_);
v___y_1905_ = v___y_1837_;
goto v___jp_1904_;
}
else
{
lean_object* v___x_1911_; 
lean_inc(v_x_1831_);
lean_inc(v_a_1878_);
v___x_1911_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1878_, v_x_1831_, v___y_1837_);
if (lean_obj_tag(v___x_1911_) == 0)
{
lean_object* v_a_1912_; uint8_t v___x_1913_; uint8_t v___x_1914_; 
v_a_1912_ = lean_ctor_get(v___x_1911_, 0);
lean_inc(v_a_1912_);
lean_dec_ref_known(v___x_1911_, 1);
v___x_1913_ = lean_unbox(v_a_1912_);
lean_dec(v_a_1912_);
v___x_1914_ = lean_bool_not(v___x_1913_);
if (v___x_1914_ == 0)
{
lean_del_object(v___x_1870_);
lean_del_object(v___x_1858_);
v___y_1905_ = v___y_1837_;
goto v___jp_1904_;
}
else
{
lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1918_; 
lean_dec(v_a_1880_);
lean_dec(v_a_1878_);
lean_del_object(v___x_1875_);
lean_del_object(v___x_1866_);
lean_dec(v_x_1831_);
v___x_1915_ = l_Lean_LocalDecl_fvarId(v_val_1856_);
lean_dec(v_val_1856_);
v___x_1916_ = lean_box(v___x_1846_);
if (v_isShared_1871_ == 0)
{
lean_ctor_set(v___x_1870_, 1, v___x_1916_);
lean_ctor_set(v___x_1870_, 0, v___x_1915_);
v___x_1918_ = v___x_1870_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1922_; 
v_reuseFailAlloc_1922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1922_, 0, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1922_, 1, v___x_1916_);
v___x_1918_ = v_reuseFailAlloc_1922_;
goto v_reusejp_1917_;
}
v_reusejp_1917_:
{
lean_object* v___x_1920_; 
if (v_isShared_1859_ == 0)
{
lean_ctor_set(v___x_1858_, 0, v___x_1918_);
v___x_1920_ = v___x_1858_;
goto v_reusejp_1919_;
}
else
{
lean_object* v_reuseFailAlloc_1921_; 
v_reuseFailAlloc_1921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
v___x_1920_ = v_reuseFailAlloc_1921_;
goto v_reusejp_1919_;
}
v_reusejp_1919_:
{
v_a_1850_ = v___x_1920_;
goto v___jp_1849_;
}
}
}
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v_a_1880_);
lean_dec(v_a_1878_);
lean_del_object(v___x_1875_);
lean_del_object(v___x_1870_);
lean_del_object(v___x_1866_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
lean_dec(v_x_1831_);
v_a_1923_ = lean_ctor_get(v___x_1911_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1911_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1911_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1911_);
v___x_1925_ = lean_box(0);
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
v_resetjp_1924_:
{
lean_object* v___x_1928_; 
if (v_isShared_1926_ == 0)
{
v___x_1928_ = v___x_1925_;
goto v_reusejp_1927_;
}
else
{
lean_object* v_reuseFailAlloc_1929_; 
v_reuseFailAlloc_1929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1929_, 0, v_a_1923_);
v___x_1928_ = v_reuseFailAlloc_1929_;
goto v_reusejp_1927_;
}
v_reusejp_1927_:
{
return v___x_1928_;
}
}
}
}
}
}
else
{
lean_object* v_a_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1941_; 
lean_dec(v_a_1878_);
lean_del_object(v___x_1875_);
lean_del_object(v___x_1870_);
lean_del_object(v___x_1866_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
lean_dec(v_x_1831_);
v_a_1934_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1941_ == 0)
{
v___x_1936_ = v___x_1879_;
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_a_1934_);
lean_dec(v___x_1879_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1941_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_a_1934_);
v___x_1939_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
return v___x_1939_;
}
}
}
}
else
{
lean_object* v_a_1942_; lean_object* v___x_1944_; uint8_t v_isShared_1945_; uint8_t v_isSharedCheck_1949_; 
lean_del_object(v___x_1875_);
lean_dec(v_snd_1873_);
lean_del_object(v___x_1870_);
lean_del_object(v___x_1866_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
lean_dec(v_x_1831_);
v_a_1942_ = lean_ctor_get(v___x_1877_, 0);
v_isSharedCheck_1949_ = !lean_is_exclusive(v___x_1877_);
if (v_isSharedCheck_1949_ == 0)
{
v___x_1944_ = v___x_1877_;
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
else
{
lean_inc(v_a_1942_);
lean_dec(v___x_1877_);
v___x_1944_ = lean_box(0);
v_isShared_1945_ = v_isSharedCheck_1949_;
goto v_resetjp_1943_;
}
v_resetjp_1943_:
{
lean_object* v___x_1947_; 
if (v_isShared_1945_ == 0)
{
v___x_1947_ = v___x_1944_;
goto v_reusejp_1946_;
}
else
{
lean_object* v_reuseFailAlloc_1948_; 
v_reuseFailAlloc_1948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1948_, 0, v_a_1942_);
v___x_1947_ = v_reuseFailAlloc_1948_;
goto v_reusejp_1946_;
}
v_reusejp_1946_:
{
return v___x_1947_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_1863_);
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
v_a_1842_ = v___x_1854_;
goto v___jp_1841_;
}
}
else
{
lean_object* v_a_1954_; lean_object* v___x_1956_; uint8_t v_isShared_1957_; uint8_t v_isSharedCheck_1961_; 
lean_del_object(v___x_1858_);
lean_dec(v_val_1856_);
lean_dec(v_x_1831_);
v_a_1954_ = lean_ctor_get(v___x_1862_, 0);
v_isSharedCheck_1961_ = !lean_is_exclusive(v___x_1862_);
if (v_isSharedCheck_1961_ == 0)
{
v___x_1956_ = v___x_1862_;
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
else
{
lean_inc(v_a_1954_);
lean_dec(v___x_1862_);
v___x_1956_ = lean_box(0);
v_isShared_1957_ = v_isSharedCheck_1961_;
goto v_resetjp_1955_;
}
v_resetjp_1955_:
{
lean_object* v___x_1959_; 
if (v_isShared_1957_ == 0)
{
v___x_1959_ = v___x_1956_;
goto v_reusejp_1958_;
}
else
{
lean_object* v_reuseFailAlloc_1960_; 
v_reuseFailAlloc_1960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1960_, 0, v_a_1954_);
v___x_1959_ = v_reuseFailAlloc_1960_;
goto v_reusejp_1958_;
}
v_reusejp_1958_:
{
return v___x_1959_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1963_, lean_object* v_as_1964_, lean_object* v_sz_1965_, lean_object* v_i_1966_, lean_object* v_b_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
size_t v_sz_boxed_1973_; size_t v_i_boxed_1974_; lean_object* v_res_1975_; 
v_sz_boxed_1973_ = lean_unbox_usize(v_sz_1965_);
lean_dec(v_sz_1965_);
v_i_boxed_1974_ = lean_unbox_usize(v_i_1966_);
lean_dec(v_i_1966_);
v_res_1975_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1963_, v_as_1964_, v_sz_boxed_1973_, v_i_boxed_1974_, v_b_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
lean_dec_ref(v_as_1964_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object* v_x_1976_, lean_object* v_as_1977_, size_t v_sz_1978_, size_t v_i_1979_, lean_object* v_b_1980_, lean_object* v___y_1981_, lean_object* v___y_1982_, lean_object* v___y_1983_, lean_object* v___y_1984_){
_start:
{
lean_object* v_a_1987_; uint8_t v___x_1991_; 
v___x_1991_ = lean_usize_dec_lt(v_i_1979_, v_sz_1978_);
if (v___x_1991_ == 0)
{
lean_object* v___x_1992_; 
lean_dec(v_x_1976_);
v___x_1992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1992_, 0, v_b_1980_);
return v___x_1992_;
}
else
{
lean_object* v___x_1993_; lean_object* v_a_1995_; lean_object* v___x_1999_; lean_object* v_a_2000_; 
lean_dec_ref(v_b_1980_);
v___x_1993_ = lean_box(0);
v___x_1999_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_2000_ = lean_array_uget(v_as_1977_, v_i_1979_);
if (lean_obj_tag(v_a_2000_) == 0)
{
v_a_1987_ = v___x_1999_;
goto v___jp_1986_;
}
else
{
lean_object* v_val_2001_; lean_object* v___x_2003_; uint8_t v_isShared_2004_; uint8_t v_isSharedCheck_2107_; 
v_val_2001_ = lean_ctor_get(v_a_2000_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v_a_2000_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2003_ = v_a_2000_;
v_isShared_2004_ = v_isSharedCheck_2107_;
goto v_resetjp_2002_;
}
else
{
lean_inc(v_val_2001_);
lean_dec(v_a_2000_);
v___x_2003_ = lean_box(0);
v_isShared_2004_ = v_isSharedCheck_2107_;
goto v_resetjp_2002_;
}
v_resetjp_2002_:
{
uint8_t v___x_2005_; 
v___x_2005_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2001_);
if (v___x_2005_ == 0)
{
lean_object* v___x_2006_; lean_object* v___x_2007_; 
v___x_2006_ = l_Lean_LocalDecl_type(v_val_2001_);
v___x_2007_ = l_Lean_Meta_matchEq_x3f(v___x_2006_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
if (lean_obj_tag(v_a_2008_) == 1)
{
lean_object* v_val_2009_; lean_object* v___x_2011_; uint8_t v_isShared_2012_; uint8_t v_isSharedCheck_2098_; 
v_val_2009_ = lean_ctor_get(v_a_2008_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v_a_2008_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2011_ = v_a_2008_;
v_isShared_2012_ = v_isSharedCheck_2098_;
goto v_resetjp_2010_;
}
else
{
lean_inc(v_val_2009_);
lean_dec(v_a_2008_);
v___x_2011_ = lean_box(0);
v_isShared_2012_ = v_isSharedCheck_2098_;
goto v_resetjp_2010_;
}
v_resetjp_2010_:
{
lean_object* v_snd_2013_; lean_object* v___x_2015_; uint8_t v_isShared_2016_; uint8_t v_isSharedCheck_2096_; 
v_snd_2013_ = lean_ctor_get(v_val_2009_, 1);
v_isSharedCheck_2096_ = !lean_is_exclusive(v_val_2009_);
if (v_isSharedCheck_2096_ == 0)
{
lean_object* v_unused_2097_; 
v_unused_2097_ = lean_ctor_get(v_val_2009_, 0);
lean_dec(v_unused_2097_);
v___x_2015_ = v_val_2009_;
v_isShared_2016_ = v_isSharedCheck_2096_;
goto v_resetjp_2014_;
}
else
{
lean_inc(v_snd_2013_);
lean_dec(v_val_2009_);
v___x_2015_ = lean_box(0);
v_isShared_2016_ = v_isSharedCheck_2096_;
goto v_resetjp_2014_;
}
v_resetjp_2014_:
{
lean_object* v_fst_2017_; lean_object* v_snd_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2095_; 
v_fst_2017_ = lean_ctor_get(v_snd_2013_, 0);
v_snd_2018_ = lean_ctor_get(v_snd_2013_, 1);
v_isSharedCheck_2095_ = !lean_is_exclusive(v_snd_2013_);
if (v_isSharedCheck_2095_ == 0)
{
v___x_2020_ = v_snd_2013_;
v_isShared_2021_ = v_isSharedCheck_2095_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_snd_2018_);
lean_inc(v_fst_2017_);
lean_dec(v_snd_2013_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2095_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_2017_, v___y_1982_);
if (lean_obj_tag(v___x_2022_) == 0)
{
lean_object* v_a_2023_; lean_object* v___x_2024_; 
v_a_2023_ = lean_ctor_get(v___x_2022_, 0);
lean_inc(v_a_2023_);
lean_dec_ref_known(v___x_2022_, 1);
v___x_2024_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_2018_, v___y_1982_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___y_2027_; uint8_t v___y_2028_; lean_object* v___y_2050_; uint8_t v___y_2055_; uint8_t v___x_2076_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2076_ = l_Lean_Expr_isFVar(v_a_2025_);
if (v___x_2076_ == 0)
{
v___y_2055_ = v___x_2076_;
goto v___jp_2054_;
}
else
{
lean_object* v___x_2077_; uint8_t v___x_2078_; 
v___x_2077_ = l_Lean_Expr_fvarId_x21(v_a_2025_);
v___x_2078_ = l_Lean_instBEqFVarId_beq(v___x_2077_, v_x_1976_);
lean_dec(v___x_2077_);
v___y_2055_ = v___x_2078_;
goto v___jp_2054_;
}
v___jp_2026_:
{
if (v___y_2028_ == 0)
{
lean_dec(v_a_2025_);
lean_del_object(v___x_2020_);
lean_del_object(v___x_2011_);
lean_dec(v_val_2001_);
v_a_1987_ = v___x_1999_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2029_; 
lean_inc(v_x_1976_);
v___x_2029_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2025_, v_x_1976_, v___y_2027_);
if (lean_obj_tag(v___x_2029_) == 0)
{
lean_object* v_a_2030_; uint8_t v___x_2031_; uint8_t v___x_2032_; 
v_a_2030_ = lean_ctor_get(v___x_2029_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2029_, 1);
v___x_2031_ = lean_unbox(v_a_2030_);
lean_dec(v_a_2030_);
v___x_2032_ = lean_bool_not(v___x_2031_);
if (v___x_2032_ == 0)
{
lean_del_object(v___x_2020_);
lean_del_object(v___x_2011_);
lean_dec(v_val_2001_);
v_a_1987_ = v___x_1999_;
goto v___jp_1986_;
}
else
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
lean_dec(v_x_1976_);
v___x_2033_ = l_Lean_LocalDecl_fvarId(v_val_2001_);
lean_dec(v_val_2001_);
v___x_2034_ = lean_box(v___x_2005_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 1, v___x_2034_);
lean_ctor_set(v___x_2020_, 0, v___x_2033_);
v___x_2036_ = v___x_2020_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2033_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2038_; 
if (v_isShared_2012_ == 0)
{
lean_ctor_set(v___x_2011_, 0, v___x_2036_);
v___x_2038_ = v___x_2011_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2039_; 
v_reuseFailAlloc_2039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2039_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2039_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
v_a_1995_ = v___x_2038_;
goto v___jp_1994_;
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_del_object(v___x_2020_);
lean_del_object(v___x_2011_);
lean_dec(v_val_2001_);
lean_dec(v_x_1976_);
v_a_2041_ = lean_ctor_get(v___x_2029_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2029_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2029_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2029_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
}
v___jp_2049_:
{
uint8_t v___x_2051_; 
v___x_2051_ = l_Lean_Expr_isFVar(v_a_2023_);
if (v___x_2051_ == 0)
{
lean_dec(v_a_2023_);
v___y_2027_ = v___y_2050_;
v___y_2028_ = v___x_2051_;
goto v___jp_2026_;
}
else
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = l_Lean_Expr_fvarId_x21(v_a_2023_);
lean_dec(v_a_2023_);
v___x_2053_ = l_Lean_instBEqFVarId_beq(v___x_2052_, v_x_1976_);
lean_dec(v___x_2052_);
v___y_2027_ = v___y_2050_;
v___y_2028_ = v___x_2053_;
goto v___jp_2026_;
}
}
v___jp_2054_:
{
if (v___y_2055_ == 0)
{
lean_del_object(v___x_2015_);
lean_del_object(v___x_2003_);
v___y_2050_ = v___y_1982_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2056_; 
lean_inc(v_x_1976_);
lean_inc(v_a_2023_);
v___x_2056_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2023_, v_x_1976_, v___y_1982_);
if (lean_obj_tag(v___x_2056_) == 0)
{
lean_object* v_a_2057_; uint8_t v___x_2058_; uint8_t v___x_2059_; 
v_a_2057_ = lean_ctor_get(v___x_2056_, 0);
lean_inc(v_a_2057_);
lean_dec_ref_known(v___x_2056_, 1);
v___x_2058_ = lean_unbox(v_a_2057_);
lean_dec(v_a_2057_);
v___x_2059_ = lean_bool_not(v___x_2058_);
if (v___x_2059_ == 0)
{
lean_del_object(v___x_2015_);
lean_del_object(v___x_2003_);
v___y_2050_ = v___y_1982_;
goto v___jp_2049_;
}
else
{
lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2063_; 
lean_dec(v_a_2025_);
lean_dec(v_a_2023_);
lean_del_object(v___x_2020_);
lean_del_object(v___x_2011_);
lean_dec(v_x_1976_);
v___x_2060_ = l_Lean_LocalDecl_fvarId(v_val_2001_);
lean_dec(v_val_2001_);
v___x_2061_ = lean_box(v___x_1991_);
if (v_isShared_2016_ == 0)
{
lean_ctor_set(v___x_2015_, 1, v___x_2061_);
lean_ctor_set(v___x_2015_, 0, v___x_2060_);
v___x_2063_ = v___x_2015_;
goto v_reusejp_2062_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v___x_2060_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v___x_2061_);
v___x_2063_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2062_;
}
v_reusejp_2062_:
{
lean_object* v___x_2065_; 
if (v_isShared_2004_ == 0)
{
lean_ctor_set(v___x_2003_, 0, v___x_2063_);
v___x_2065_ = v___x_2003_;
goto v_reusejp_2064_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2063_);
v___x_2065_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2064_;
}
v_reusejp_2064_:
{
v_a_1995_ = v___x_2065_;
goto v___jp_1994_;
}
}
}
}
else
{
lean_object* v_a_2068_; lean_object* v___x_2070_; uint8_t v_isShared_2071_; uint8_t v_isSharedCheck_2075_; 
lean_dec(v_a_2025_);
lean_dec(v_a_2023_);
lean_del_object(v___x_2020_);
lean_del_object(v___x_2015_);
lean_del_object(v___x_2011_);
lean_del_object(v___x_2003_);
lean_dec(v_val_2001_);
lean_dec(v_x_1976_);
v_a_2068_ = lean_ctor_get(v___x_2056_, 0);
v_isSharedCheck_2075_ = !lean_is_exclusive(v___x_2056_);
if (v_isSharedCheck_2075_ == 0)
{
v___x_2070_ = v___x_2056_;
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
else
{
lean_inc(v_a_2068_);
lean_dec(v___x_2056_);
v___x_2070_ = lean_box(0);
v_isShared_2071_ = v_isSharedCheck_2075_;
goto v_resetjp_2069_;
}
v_resetjp_2069_:
{
lean_object* v___x_2073_; 
if (v_isShared_2071_ == 0)
{
v___x_2073_ = v___x_2070_;
goto v_reusejp_2072_;
}
else
{
lean_object* v_reuseFailAlloc_2074_; 
v_reuseFailAlloc_2074_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2074_, 0, v_a_2068_);
v___x_2073_ = v_reuseFailAlloc_2074_;
goto v_reusejp_2072_;
}
v_reusejp_2072_:
{
return v___x_2073_;
}
}
}
}
}
}
else
{
lean_object* v_a_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2086_; 
lean_dec(v_a_2023_);
lean_del_object(v___x_2020_);
lean_del_object(v___x_2015_);
lean_del_object(v___x_2011_);
lean_del_object(v___x_2003_);
lean_dec(v_val_2001_);
lean_dec(v_x_1976_);
v_a_2079_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2086_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2086_ == 0)
{
v___x_2081_ = v___x_2024_;
v_isShared_2082_ = v_isSharedCheck_2086_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_a_2079_);
lean_dec(v___x_2024_);
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
lean_object* v_a_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2094_; 
lean_del_object(v___x_2020_);
lean_dec(v_snd_2018_);
lean_del_object(v___x_2015_);
lean_del_object(v___x_2011_);
lean_del_object(v___x_2003_);
lean_dec(v_val_2001_);
lean_dec(v_x_1976_);
v_a_2087_ = lean_ctor_get(v___x_2022_, 0);
v_isSharedCheck_2094_ = !lean_is_exclusive(v___x_2022_);
if (v_isSharedCheck_2094_ == 0)
{
v___x_2089_ = v___x_2022_;
v_isShared_2090_ = v_isSharedCheck_2094_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_a_2087_);
lean_dec(v___x_2022_);
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
}
}
}
else
{
lean_dec(v_a_2008_);
lean_del_object(v___x_2003_);
lean_dec(v_val_2001_);
v_a_1987_ = v___x_1999_;
goto v___jp_1986_;
}
}
else
{
lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_del_object(v___x_2003_);
lean_dec(v_val_2001_);
lean_dec(v_x_1976_);
v_a_2099_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2007_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_dec(v___x_2007_);
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
lean_del_object(v___x_2003_);
lean_dec(v_val_2001_);
v_a_1987_ = v___x_1999_;
goto v___jp_1986_;
}
}
}
v___jp_1994_:
{
lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; 
v___x_1996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1996_, 0, v_a_1995_);
v___x_1997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1997_, 0, v___x_1996_);
lean_ctor_set(v___x_1997_, 1, v___x_1993_);
v___x_1998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1997_);
return v___x_1998_;
}
}
v___jp_1986_:
{
size_t v___x_1988_; size_t v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = ((size_t)1ULL);
v___x_1989_ = lean_usize_add(v_i_1979_, v___x_1988_);
lean_inc_ref(v_a_1987_);
v___x_1990_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1976_, v_as_1977_, v_sz_1978_, v___x_1989_, v_a_1987_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_);
return v___x_1990_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2108_, lean_object* v_as_2109_, lean_object* v_sz_2110_, lean_object* v_i_2111_, lean_object* v_b_2112_, lean_object* v___y_2113_, lean_object* v___y_2114_, lean_object* v___y_2115_, lean_object* v___y_2116_, lean_object* v___y_2117_){
_start:
{
size_t v_sz_boxed_2118_; size_t v_i_boxed_2119_; lean_object* v_res_2120_; 
v_sz_boxed_2118_ = lean_unbox_usize(v_sz_2110_);
lean_dec(v_sz_2110_);
v_i_boxed_2119_ = lean_unbox_usize(v_i_2111_);
lean_dec(v_i_2111_);
v_res_2120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2108_, v_as_2109_, v_sz_boxed_2118_, v_i_boxed_2119_, v_b_2112_, v___y_2113_, v___y_2114_, v___y_2115_, v___y_2116_);
lean_dec(v___y_2116_);
lean_dec_ref(v___y_2115_);
lean_dec(v___y_2114_);
lean_dec_ref(v___y_2113_);
lean_dec_ref(v_as_2109_);
return v_res_2120_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object* v_x_2121_, lean_object* v_x_2122_, lean_object* v___y_2123_, lean_object* v___y_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_){
_start:
{
if (lean_obj_tag(v_x_2122_) == 0)
{
lean_object* v_cs_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; size_t v_sz_2131_; size_t v___x_2132_; lean_object* v___x_2133_; 
v_cs_2128_ = lean_ctor_get(v_x_2122_, 0);
v___x_2129_ = lean_box(0);
v___x_2130_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2131_ = lean_array_size(v_cs_2128_);
v___x_2132_ = ((size_t)0ULL);
v___x_2133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2121_, v_cs_2128_, v_sz_2131_, v___x_2132_, v___x_2130_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2146_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2136_ = v___x_2133_;
v_isShared_2137_ = v_isSharedCheck_2146_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2133_);
v___x_2136_ = lean_box(0);
v_isShared_2137_ = v_isSharedCheck_2146_;
goto v_resetjp_2135_;
}
v_resetjp_2135_:
{
lean_object* v_fst_2138_; 
v_fst_2138_ = lean_ctor_get(v_a_2134_, 0);
lean_inc(v_fst_2138_);
lean_dec(v_a_2134_);
if (lean_obj_tag(v_fst_2138_) == 0)
{
lean_object* v___x_2140_; 
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v___x_2129_);
v___x_2140_ = v___x_2136_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v___x_2129_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
else
{
lean_object* v_val_2142_; lean_object* v___x_2144_; 
v_val_2142_ = lean_ctor_get(v_fst_2138_, 0);
lean_inc(v_val_2142_);
lean_dec_ref_known(v_fst_2138_, 1);
if (v_isShared_2137_ == 0)
{
lean_ctor_set(v___x_2136_, 0, v_val_2142_);
v___x_2144_ = v___x_2136_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_val_2142_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
else
{
lean_object* v_a_2147_; lean_object* v___x_2149_; uint8_t v_isShared_2150_; uint8_t v_isSharedCheck_2154_; 
v_a_2147_ = lean_ctor_get(v___x_2133_, 0);
v_isSharedCheck_2154_ = !lean_is_exclusive(v___x_2133_);
if (v_isSharedCheck_2154_ == 0)
{
v___x_2149_ = v___x_2133_;
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
else
{
lean_inc(v_a_2147_);
lean_dec(v___x_2133_);
v___x_2149_ = lean_box(0);
v_isShared_2150_ = v_isSharedCheck_2154_;
goto v_resetjp_2148_;
}
v_resetjp_2148_:
{
lean_object* v___x_2152_; 
if (v_isShared_2150_ == 0)
{
v___x_2152_ = v___x_2149_;
goto v_reusejp_2151_;
}
else
{
lean_object* v_reuseFailAlloc_2153_; 
v_reuseFailAlloc_2153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2153_, 0, v_a_2147_);
v___x_2152_ = v_reuseFailAlloc_2153_;
goto v_reusejp_2151_;
}
v_reusejp_2151_:
{
return v___x_2152_;
}
}
}
}
else
{
lean_object* v_vs_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; size_t v_sz_2158_; size_t v___x_2159_; lean_object* v___x_2160_; 
v_vs_2155_ = lean_ctor_get(v_x_2122_, 0);
v___x_2156_ = lean_box(0);
v___x_2157_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2158_ = lean_array_size(v_vs_2155_);
v___x_2159_ = ((size_t)0ULL);
v___x_2160_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2121_, v_vs_2155_, v_sz_2158_, v___x_2159_, v___x_2157_, v___y_2123_, v___y_2124_, v___y_2125_, v___y_2126_);
if (lean_obj_tag(v___x_2160_) == 0)
{
lean_object* v_a_2161_; lean_object* v___x_2163_; uint8_t v_isShared_2164_; uint8_t v_isSharedCheck_2173_; 
v_a_2161_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2163_ = v___x_2160_;
v_isShared_2164_ = v_isSharedCheck_2173_;
goto v_resetjp_2162_;
}
else
{
lean_inc(v_a_2161_);
lean_dec(v___x_2160_);
v___x_2163_ = lean_box(0);
v_isShared_2164_ = v_isSharedCheck_2173_;
goto v_resetjp_2162_;
}
v_resetjp_2162_:
{
lean_object* v_fst_2165_; 
v_fst_2165_ = lean_ctor_get(v_a_2161_, 0);
lean_inc(v_fst_2165_);
lean_dec(v_a_2161_);
if (lean_obj_tag(v_fst_2165_) == 0)
{
lean_object* v___x_2167_; 
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v___x_2156_);
v___x_2167_ = v___x_2163_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v___x_2156_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
else
{
lean_object* v_val_2169_; lean_object* v___x_2171_; 
v_val_2169_ = lean_ctor_get(v_fst_2165_, 0);
lean_inc(v_val_2169_);
lean_dec_ref_known(v_fst_2165_, 1);
if (v_isShared_2164_ == 0)
{
lean_ctor_set(v___x_2163_, 0, v_val_2169_);
v___x_2171_ = v___x_2163_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_val_2169_);
v___x_2171_ = v_reuseFailAlloc_2172_;
goto v_reusejp_2170_;
}
v_reusejp_2170_:
{
return v___x_2171_;
}
}
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
v_a_2174_ = lean_ctor_get(v___x_2160_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2160_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2160_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2160_);
v___x_2176_ = lean_box(0);
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
v_resetjp_2175_:
{
lean_object* v___x_2179_; 
if (v_isShared_2177_ == 0)
{
v___x_2179_ = v___x_2176_;
goto v_reusejp_2178_;
}
else
{
lean_object* v_reuseFailAlloc_2180_; 
v_reuseFailAlloc_2180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2180_, 0, v_a_2174_);
v___x_2179_ = v_reuseFailAlloc_2180_;
goto v_reusejp_2178_;
}
v_reusejp_2178_:
{
return v___x_2179_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2182_, lean_object* v_as_2183_, size_t v_sz_2184_, size_t v_i_2185_, lean_object* v_b_2186_, lean_object* v___y_2187_, lean_object* v___y_2188_, lean_object* v___y_2189_, lean_object* v___y_2190_){
_start:
{
uint8_t v___x_2192_; 
v___x_2192_ = lean_usize_dec_lt(v_i_2185_, v_sz_2184_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2193_; 
lean_dec(v_x_2182_);
v___x_2193_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2193_, 0, v_b_2186_);
return v___x_2193_;
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2195_; 
lean_dec_ref(v_b_2186_);
v_a_2194_ = lean_array_uget_borrowed(v_as_2183_, v_i_2185_);
lean_inc(v_x_2182_);
v___x_2195_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2182_, v_a_2194_, v___y_2187_, v___y_2188_, v___y_2189_, v___y_2190_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2210_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2210_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2210_ == 0)
{
v___x_2198_ = v___x_2195_;
v_isShared_2199_ = v_isSharedCheck_2210_;
goto v_resetjp_2197_;
}
else
{
lean_inc(v_a_2196_);
lean_dec(v___x_2195_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2210_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_box(0);
if (lean_obj_tag(v_a_2196_) == 1)
{
lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
lean_dec(v_x_2182_);
v___x_2201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2201_, 0, v_a_2196_);
v___x_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2202_, 0, v___x_2201_);
lean_ctor_set(v___x_2202_, 1, v___x_2200_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 0, v___x_2202_);
v___x_2204_ = v___x_2198_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2202_);
v___x_2204_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
return v___x_2204_;
}
}
else
{
lean_object* v___x_2206_; size_t v___x_2207_; size_t v___x_2208_; 
lean_del_object(v___x_2198_);
lean_dec(v_a_2196_);
v___x_2206_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2207_ = ((size_t)1ULL);
v___x_2208_ = lean_usize_add(v_i_2185_, v___x_2207_);
v_i_2185_ = v___x_2208_;
v_b_2186_ = v___x_2206_;
goto _start;
}
}
}
else
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2218_; 
lean_dec(v_x_2182_);
v_a_2211_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2218_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2218_ == 0)
{
v___x_2213_ = v___x_2195_;
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2195_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2218_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v___x_2216_; 
if (v_isShared_2214_ == 0)
{
v___x_2216_ = v___x_2213_;
goto v_reusejp_2215_;
}
else
{
lean_object* v_reuseFailAlloc_2217_; 
v_reuseFailAlloc_2217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2217_, 0, v_a_2211_);
v___x_2216_ = v_reuseFailAlloc_2217_;
goto v_reusejp_2215_;
}
v_reusejp_2215_:
{
return v___x_2216_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2219_, lean_object* v_as_2220_, lean_object* v_sz_2221_, lean_object* v_i_2222_, lean_object* v_b_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_, lean_object* v___y_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_){
_start:
{
size_t v_sz_boxed_2229_; size_t v_i_boxed_2230_; lean_object* v_res_2231_; 
v_sz_boxed_2229_ = lean_unbox_usize(v_sz_2221_);
lean_dec(v_sz_2221_);
v_i_boxed_2230_ = lean_unbox_usize(v_i_2222_);
lean_dec(v_i_2222_);
v_res_2231_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2219_, v_as_2220_, v_sz_boxed_2229_, v_i_boxed_2230_, v_b_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_);
lean_dec(v___y_2227_);
lean_dec_ref(v___y_2226_);
lean_dec(v___y_2225_);
lean_dec_ref(v___y_2224_);
lean_dec_ref(v_as_2220_);
return v_res_2231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2232_, lean_object* v_x_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2232_, v_x_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec_ref(v_x_2233_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object* v_x_2240_, lean_object* v_t_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_root_2247_; lean_object* v_tail_2248_; lean_object* v___x_2249_; 
v_root_2247_ = lean_ctor_get(v_t_2241_, 0);
v_tail_2248_ = lean_ctor_get(v_t_2241_, 1);
lean_inc(v_x_2240_);
v___x_2249_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2240_, v_root_2247_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
if (lean_obj_tag(v_a_2250_) == 0)
{
lean_object* v___x_2251_; size_t v_sz_2252_; size_t v___x_2253_; lean_object* v___x_2254_; 
lean_dec_ref_known(v___x_2249_, 1);
v___x_2251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2252_ = lean_array_size(v_tail_2248_);
v___x_2253_ = ((size_t)0ULL);
v___x_2254_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2240_, v_tail_2248_, v_sz_2252_, v___x_2253_, v___x_2251_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
if (lean_obj_tag(v___x_2254_) == 0)
{
lean_object* v_a_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2267_; 
v_a_2255_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2257_ = v___x_2254_;
v_isShared_2258_ = v_isSharedCheck_2267_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_a_2255_);
lean_dec(v___x_2254_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2267_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v_fst_2259_; 
v_fst_2259_ = lean_ctor_get(v_a_2255_, 0);
lean_inc(v_fst_2259_);
lean_dec(v_a_2255_);
if (lean_obj_tag(v_fst_2259_) == 0)
{
lean_object* v___x_2261_; 
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v_a_2250_);
v___x_2261_ = v___x_2257_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v_a_2250_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
else
{
lean_object* v_val_2263_; lean_object* v___x_2265_; 
v_val_2263_ = lean_ctor_get(v_fst_2259_, 0);
lean_inc(v_val_2263_);
lean_dec_ref_known(v_fst_2259_, 1);
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 0, v_val_2263_);
v___x_2265_ = v___x_2257_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_val_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v_a_2268_ = lean_ctor_get(v___x_2254_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2254_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2254_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2254_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2250_, 1);
lean_dec(v_x_2240_);
return v___x_2249_;
}
}
else
{
lean_dec(v_x_2240_);
return v___x_2249_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* v_x_2276_, lean_object* v_t_2277_, lean_object* v___y_2278_, lean_object* v___y_2279_, lean_object* v___y_2280_, lean_object* v___y_2281_, lean_object* v___y_2282_){
_start:
{
lean_object* v_res_2283_; 
v_res_2283_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2276_, v_t_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_);
lean_dec(v___y_2281_);
lean_dec_ref(v___y_2280_);
lean_dec(v___y_2279_);
lean_dec_ref(v___y_2278_);
lean_dec_ref(v_t_2277_);
return v_res_2283_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object* v_x_2284_, lean_object* v_lctx_2285_, lean_object* v___y_2286_, lean_object* v___y_2287_, lean_object* v___y_2288_, lean_object* v___y_2289_){
_start:
{
lean_object* v_decls_2291_; lean_object* v___x_2292_; 
v_decls_2291_ = lean_ctor_get(v_lctx_2285_, 1);
v___x_2292_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2284_, v_decls_2291_, v___y_2286_, v___y_2287_, v___y_2288_, v___y_2289_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object* v_x_2293_, lean_object* v_lctx_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
lean_object* v_res_2300_; 
v_res_2300_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2293_, v_lctx_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec_ref(v_lctx_2294_);
return v_res_2300_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__0));
v___x_2303_ = l_Lean_stringToMessageData(v___x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2305_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__2));
v___x_2306_ = l_Lean_stringToMessageData(v___x_2305_);
return v___x_2306_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2308_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__4));
v___x_2309_ = l_Lean_stringToMessageData(v___x_2308_);
return v___x_2309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object* v_x_2310_, lean_object* v_mvarId_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_){
_start:
{
lean_object* v___y_2318_; lean_object* v___y_2319_; lean_object* v___y_2320_; lean_object* v___y_2321_; lean_object* v___x_2366_; 
lean_inc(v_x_2310_);
v___x_2366_ = l_Lean_FVarId_getDecl___redArg(v_x_2310_, v___y_2312_, v___y_2314_, v___y_2315_);
if (lean_obj_tag(v___x_2366_) == 0)
{
lean_object* v_a_2367_; uint8_t v___x_2368_; uint8_t v___x_2369_; 
v_a_2367_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2366_, 1);
v___x_2368_ = 0;
v___x_2369_ = l_Lean_LocalDecl_isLet(v_a_2367_, v___x_2368_);
lean_dec(v_a_2367_);
if (v___x_2369_ == 0)
{
v___y_2318_ = v___y_2312_;
v___y_2319_ = v___y_2313_;
v___y_2320_ = v___y_2314_;
v___y_2321_ = v___y_2315_;
goto v___jp_2317_;
}
else
{
lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2370_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2371_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2310_);
v___x_2372_ = l_Lean_mkFVar(v_x_2310_);
v___x_2373_ = l_Lean_MessageData_ofExpr(v___x_2372_);
v___x_2374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2371_);
lean_ctor_set(v___x_2374_, 1, v___x_2373_);
v___x_2375_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2376_, 0, v___x_2374_);
lean_ctor_set(v___x_2376_, 1, v___x_2375_);
v___x_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_inc(v_mvarId_2311_);
v___x_2378_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2370_, v_mvarId_2311_, v___x_2377_, v___y_2312_, v___y_2313_, v___y_2314_, v___y_2315_);
if (lean_obj_tag(v___x_2378_) == 0)
{
lean_dec_ref_known(v___x_2378_, 1);
v___y_2318_ = v___y_2312_;
v___y_2319_ = v___y_2313_;
v___y_2320_ = v___y_2314_;
v___y_2321_ = v___y_2315_;
goto v___jp_2317_;
}
else
{
lean_object* v_a_2379_; lean_object* v___x_2381_; uint8_t v_isShared_2382_; uint8_t v_isSharedCheck_2386_; 
lean_dec(v_mvarId_2311_);
lean_dec(v_x_2310_);
v_a_2379_ = lean_ctor_get(v___x_2378_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2378_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2381_ = v___x_2378_;
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
else
{
lean_inc(v_a_2379_);
lean_dec(v___x_2378_);
v___x_2381_ = lean_box(0);
v_isShared_2382_ = v_isSharedCheck_2386_;
goto v_resetjp_2380_;
}
v_resetjp_2380_:
{
lean_object* v___x_2384_; 
if (v_isShared_2382_ == 0)
{
v___x_2384_ = v___x_2381_;
goto v_reusejp_2383_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_a_2379_);
v___x_2384_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2383_;
}
v_reusejp_2383_:
{
return v___x_2384_;
}
}
}
}
}
else
{
lean_object* v_a_2387_; lean_object* v___x_2389_; uint8_t v_isShared_2390_; uint8_t v_isSharedCheck_2394_; 
lean_dec(v_mvarId_2311_);
lean_dec(v_x_2310_);
v_a_2387_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2389_ = v___x_2366_;
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
else
{
lean_inc(v_a_2387_);
lean_dec(v___x_2366_);
v___x_2389_ = lean_box(0);
v_isShared_2390_ = v_isSharedCheck_2394_;
goto v_resetjp_2388_;
}
v_resetjp_2388_:
{
lean_object* v___x_2392_; 
if (v_isShared_2390_ == 0)
{
v___x_2392_ = v___x_2389_;
goto v_reusejp_2391_;
}
else
{
lean_object* v_reuseFailAlloc_2393_; 
v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
v___x_2392_ = v_reuseFailAlloc_2393_;
goto v_reusejp_2391_;
}
v_reusejp_2391_:
{
return v___x_2392_;
}
}
}
v___jp_2317_:
{
lean_object* v_lctx_2322_; lean_object* v___x_2323_; 
v_lctx_2322_ = lean_ctor_get(v___y_2318_, 2);
lean_inc(v_x_2310_);
v___x_2323_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2310_, v_lctx_2322_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
if (lean_obj_tag(v_a_2324_) == 1)
{
lean_object* v_val_2325_; lean_object* v_fst_2326_; lean_object* v_snd_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; uint8_t v___x_2330_; lean_object* v___x_2331_; 
lean_dec(v_x_2310_);
v_val_2325_ = lean_ctor_get(v_a_2324_, 0);
lean_inc(v_val_2325_);
lean_dec_ref_known(v_a_2324_, 1);
v_fst_2326_ = lean_ctor_get(v_val_2325_, 0);
lean_inc(v_fst_2326_);
v_snd_2327_ = lean_ctor_get(v_val_2325_, 1);
lean_inc(v_snd_2327_);
lean_dec(v_val_2325_);
v___x_2328_ = lean_box(0);
v___x_2329_ = 1;
v___x_2330_ = lean_unbox(v_snd_2327_);
lean_dec(v_snd_2327_);
v___x_2331_ = l_Lean_Meta_substCore(v_mvarId_2311_, v_fst_2326_, v___x_2330_, v___x_2328_, v___x_2329_, v___x_2329_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
if (lean_obj_tag(v___x_2331_) == 0)
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2340_; 
v_a_2332_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2334_ = v___x_2331_;
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2331_);
v___x_2334_ = lean_box(0);
v_isShared_2335_ = v_isSharedCheck_2340_;
goto v_resetjp_2333_;
}
v_resetjp_2333_:
{
lean_object* v_snd_2336_; lean_object* v___x_2338_; 
v_snd_2336_ = lean_ctor_get(v_a_2332_, 1);
lean_inc(v_snd_2336_);
lean_dec(v_a_2332_);
if (v_isShared_2335_ == 0)
{
lean_ctor_set(v___x_2334_, 0, v_snd_2336_);
v___x_2338_ = v___x_2334_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_snd_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
v_a_2341_ = lean_ctor_get(v___x_2331_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2331_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2331_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2331_);
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
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; 
lean_dec(v_a_2324_);
v___x_2349_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2350_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2351_ = l_Lean_mkFVar(v_x_2310_);
v___x_2352_ = l_Lean_MessageData_ofExpr(v___x_2351_);
v___x_2353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2350_);
lean_ctor_set(v___x_2353_, 1, v___x_2352_);
v___x_2354_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_2355_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2353_);
lean_ctor_set(v___x_2355_, 1, v___x_2354_);
v___x_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2356_, 0, v___x_2355_);
v___x_2357_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2349_, v_mvarId_2311_, v___x_2356_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_);
return v___x_2357_;
}
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_dec(v_mvarId_2311_);
lean_dec(v_x_2310_);
v_a_2358_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2323_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2323_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2395_, lean_object* v_mvarId_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
lean_object* v_res_2402_; 
v_res_2402_ = l_Lean_Meta_substVar___lam__0(v_x_2395_, v_mvarId_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
return v_res_2402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2403_, lean_object* v_x_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v___f_2410_; lean_object* v___x_2411_; 
lean_inc(v_mvarId_2403_);
v___f_2410_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2410_, 0, v_x_2404_);
lean_closure_set(v___f_2410_, 1, v_mvarId_2403_);
v___x_2411_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2403_, v___f_2410_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
return v___x_2411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2412_, lean_object* v_x_2413_, lean_object* v_a_2414_, lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_){
_start:
{
lean_object* v_res_2419_; 
v_res_2419_ = l_Lean_Meta_substVar(v_mvarId_2412_, v_x_2413_, v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_);
lean_dec(v_a_2417_);
lean_dec_ref(v_a_2416_);
lean_dec(v_a_2415_);
lean_dec_ref(v_a_2414_);
return v_res_2419_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2421_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2422_ = l_Lean_stringToMessageData(v___x_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2423_, lean_object* v_snd_2424_, uint8_t v___x_2425_, lean_object* v_fvarSubst_2426_, lean_object* v___y_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_){
_start:
{
lean_object* v___x_2432_; 
lean_inc(v_fst_2423_);
v___x_2432_ = l_Lean_FVarId_getDecl___redArg(v_fst_2423_, v___y_2427_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2432_) == 0)
{
lean_object* v_a_2433_; lean_object* v_newType_2435_; uint8_t v_symm_2436_; lean_object* v___y_2437_; lean_object* v___y_2438_; lean_object* v___y_2439_; lean_object* v___y_2440_; lean_object* v___y_2477_; lean_object* v___y_2478_; lean_object* v___y_2479_; lean_object* v___y_2480_; lean_object* v___x_2488_; lean_object* v___x_2489_; 
v_a_2433_ = lean_ctor_get(v___x_2432_, 0);
lean_inc(v_a_2433_);
lean_dec_ref_known(v___x_2432_, 1);
v___x_2488_ = l_Lean_LocalDecl_type(v_a_2433_);
v___x_2489_ = l_Lean_Meta_matchEq_x3f(v___x_2488_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
if (lean_obj_tag(v_a_2490_) == 1)
{
lean_object* v_val_2491_; lean_object* v_snd_2492_; lean_object* v_fst_2493_; lean_object* v_snd_2494_; lean_object* v___x_2495_; 
v_val_2491_ = lean_ctor_get(v_a_2490_, 0);
lean_inc(v_val_2491_);
lean_dec_ref_known(v_a_2490_, 1);
v_snd_2492_ = lean_ctor_get(v_val_2491_, 1);
lean_inc(v_snd_2492_);
lean_dec(v_val_2491_);
v_fst_2493_ = lean_ctor_get(v_snd_2492_, 0);
lean_inc(v_fst_2493_);
v_snd_2494_ = lean_ctor_get(v_snd_2492_, 1);
lean_inc_n(v_snd_2494_, 2);
lean_dec(v_snd_2492_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
lean_inc(v___y_2428_);
lean_inc_ref(v___y_2427_);
v___x_2495_ = lean_whnf(v_snd_2494_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2495_) == 0)
{
lean_object* v_a_2496_; uint8_t v___x_2497_; 
v_a_2496_ = lean_ctor_get(v___x_2495_, 0);
lean_inc(v_a_2496_);
lean_dec_ref_known(v___x_2495_, 1);
v___x_2497_ = l_Lean_Expr_isFVar(v_a_2496_);
if (v___x_2497_ == 0)
{
lean_object* v___x_2498_; 
lean_dec(v_a_2496_);
lean_inc(v___y_2430_);
lean_inc_ref(v___y_2429_);
lean_inc(v___y_2428_);
lean_inc_ref(v___y_2427_);
lean_inc(v_fst_2493_);
v___x_2498_ = lean_whnf(v_fst_2493_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2498_) == 0)
{
lean_object* v_a_2499_; uint8_t v___x_2500_; 
v_a_2499_ = lean_ctor_get(v___x_2498_, 0);
lean_inc(v_a_2499_);
lean_dec_ref_known(v___x_2498_, 1);
v___x_2500_ = l_Lean_Expr_isFVar(v_a_2499_);
if (v___x_2500_ == 0)
{
lean_dec(v_a_2499_);
lean_dec(v_snd_2494_);
lean_dec(v_fst_2493_);
lean_dec(v_fvarSubst_2426_);
lean_dec(v_fst_2423_);
v___y_2477_ = v___y_2427_;
v___y_2478_ = v___y_2428_;
v___y_2479_ = v___y_2429_;
v___y_2480_ = v___y_2430_;
goto v___jp_2476_;
}
else
{
uint8_t v___x_2501_; uint8_t v___x_2502_; 
v___x_2501_ = lean_expr_eqv(v_fst_2493_, v_a_2499_);
lean_dec(v_fst_2493_);
v___x_2502_ = lean_bool_not(v___x_2501_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; 
lean_dec(v_a_2499_);
lean_dec(v_snd_2494_);
lean_dec(v_a_2433_);
v___x_2503_ = l_Lean_Meta_substCore(v_snd_2424_, v_fst_2423_, v___x_2502_, v_fvarSubst_2426_, v___x_2425_, v___x_2425_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
return v___x_2503_;
}
else
{
lean_object* v___x_2504_; 
v___x_2504_ = l_Lean_Meta_mkEq(v_a_2499_, v_snd_2494_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2504_) == 0)
{
lean_object* v_a_2505_; 
v_a_2505_ = lean_ctor_get(v___x_2504_, 0);
lean_inc(v_a_2505_);
lean_dec_ref_known(v___x_2504_, 1);
v_newType_2435_ = v_a_2505_;
v_symm_2436_ = v___x_2497_;
v___y_2437_ = v___y_2427_;
v___y_2438_ = v___y_2428_;
v___y_2439_ = v___y_2429_;
v___y_2440_ = v___y_2430_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec(v_a_2433_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v_fvarSubst_2426_);
lean_dec(v_snd_2424_);
lean_dec(v_fst_2423_);
v_a_2506_ = lean_ctor_get(v___x_2504_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2504_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2504_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2504_);
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
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec(v_snd_2494_);
lean_dec(v_fst_2493_);
lean_dec(v_a_2433_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v_fvarSubst_2426_);
lean_dec(v_snd_2424_);
lean_dec(v_fst_2423_);
v_a_2514_ = lean_ctor_get(v___x_2498_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2498_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2498_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2498_);
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
else
{
uint8_t v___x_2522_; uint8_t v___x_2523_; 
v___x_2522_ = lean_expr_eqv(v_snd_2494_, v_a_2496_);
lean_dec(v_snd_2494_);
v___x_2523_ = lean_bool_not(v___x_2522_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; 
lean_dec(v_a_2496_);
lean_dec(v_fst_2493_);
lean_dec(v_a_2433_);
v___x_2524_ = l_Lean_Meta_substCore(v_snd_2424_, v_fst_2423_, v___x_2425_, v_fvarSubst_2426_, v___x_2425_, v___x_2425_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
return v___x_2524_;
}
else
{
lean_object* v___x_2525_; 
v___x_2525_ = l_Lean_Meta_mkEq(v_fst_2493_, v_a_2496_, v___y_2427_, v___y_2428_, v___y_2429_, v___y_2430_);
if (lean_obj_tag(v___x_2525_) == 0)
{
lean_object* v_a_2526_; 
v_a_2526_ = lean_ctor_get(v___x_2525_, 0);
lean_inc(v_a_2526_);
lean_dec_ref_known(v___x_2525_, 1);
v_newType_2435_ = v_a_2526_;
v_symm_2436_ = v___x_2425_;
v___y_2437_ = v___y_2427_;
v___y_2438_ = v___y_2428_;
v___y_2439_ = v___y_2429_;
v___y_2440_ = v___y_2430_;
goto v___jp_2434_;
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v_a_2433_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v_fvarSubst_2426_);
lean_dec(v_snd_2424_);
lean_dec(v_fst_2423_);
v_a_2527_ = lean_ctor_get(v___x_2525_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___x_2525_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___x_2525_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___x_2525_);
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
}
}
else
{
lean_object* v_a_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2542_; 
lean_dec(v_snd_2494_);
lean_dec(v_fst_2493_);
lean_dec(v_a_2433_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v_fvarSubst_2426_);
lean_dec(v_snd_2424_);
lean_dec(v_fst_2423_);
v_a_2535_ = lean_ctor_get(v___x_2495_, 0);
v_isSharedCheck_2542_ = !lean_is_exclusive(v___x_2495_);
if (v_isSharedCheck_2542_ == 0)
{
v___x_2537_ = v___x_2495_;
v_isShared_2538_ = v_isSharedCheck_2542_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_a_2535_);
lean_dec(v___x_2495_);
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
else
{
lean_dec(v_a_2490_);
lean_dec(v_fvarSubst_2426_);
lean_dec(v_fst_2423_);
v___y_2477_ = v___y_2427_;
v___y_2478_ = v___y_2428_;
v___y_2479_ = v___y_2429_;
v___y_2480_ = v___y_2430_;
goto v___jp_2476_;
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec(v_a_2433_);
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v_fvarSubst_2426_);
lean_dec(v_snd_2424_);
lean_dec(v_fst_2423_);
v_a_2543_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2489_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2489_);
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
v___jp_2434_:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; lean_object* v___x_2443_; 
v___x_2441_ = l_Lean_LocalDecl_userName(v_a_2433_);
lean_dec(v_a_2433_);
lean_inc(v_fst_2423_);
v___x_2442_ = l_Lean_mkFVar(v_fst_2423_);
v___x_2443_ = l_Lean_MVarId_assert(v_snd_2424_, v___x_2441_, v_newType_2435_, v___x_2442_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
if (lean_obj_tag(v___x_2443_) == 0)
{
lean_object* v_a_2444_; lean_object* v___x_2445_; 
v_a_2444_ = lean_ctor_get(v___x_2443_, 0);
lean_inc(v_a_2444_);
lean_dec_ref_known(v___x_2443_, 1);
v___x_2445_ = l_Lean_Meta_intro1Core(v_a_2444_, v___x_2425_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; lean_object* v_fst_2447_; lean_object* v_snd_2448_; lean_object* v___x_2449_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
v_fst_2447_ = lean_ctor_get(v_a_2446_, 0);
lean_inc(v_fst_2447_);
v_snd_2448_ = lean_ctor_get(v_a_2446_, 1);
lean_inc(v_snd_2448_);
lean_dec(v_a_2446_);
v___x_2449_ = l_Lean_MVarId_clear(v_snd_2448_, v_fst_2423_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2451_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v___x_2451_ = l_Lean_Meta_substCore(v_a_2450_, v_fst_2447_, v_symm_2436_, v_fvarSubst_2426_, v___x_2425_, v___x_2425_, v___y_2437_, v___y_2438_, v___y_2439_, v___y_2440_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
return v___x_2451_;
}
else
{
lean_object* v_a_2452_; lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2459_; 
lean_dec(v_fst_2447_);
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v_fvarSubst_2426_);
v_a_2452_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2459_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2459_ == 0)
{
v___x_2454_ = v___x_2449_;
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
else
{
lean_inc(v_a_2452_);
lean_dec(v___x_2449_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2459_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2457_; 
if (v_isShared_2455_ == 0)
{
v___x_2457_ = v___x_2454_;
goto v_reusejp_2456_;
}
else
{
lean_object* v_reuseFailAlloc_2458_; 
v_reuseFailAlloc_2458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2458_, 0, v_a_2452_);
v___x_2457_ = v_reuseFailAlloc_2458_;
goto v_reusejp_2456_;
}
v_reusejp_2456_:
{
return v___x_2457_;
}
}
}
}
else
{
lean_object* v_a_2460_; lean_object* v___x_2462_; uint8_t v_isShared_2463_; uint8_t v_isSharedCheck_2467_; 
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v_fvarSubst_2426_);
lean_dec(v_fst_2423_);
v_a_2460_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2467_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2467_ == 0)
{
v___x_2462_ = v___x_2445_;
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
else
{
lean_inc(v_a_2460_);
lean_dec(v___x_2445_);
v___x_2462_ = lean_box(0);
v_isShared_2463_ = v_isSharedCheck_2467_;
goto v_resetjp_2461_;
}
v_resetjp_2461_:
{
lean_object* v___x_2465_; 
if (v_isShared_2463_ == 0)
{
v___x_2465_ = v___x_2462_;
goto v_reusejp_2464_;
}
else
{
lean_object* v_reuseFailAlloc_2466_; 
v_reuseFailAlloc_2466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
v___x_2465_ = v_reuseFailAlloc_2466_;
goto v_reusejp_2464_;
}
v_reusejp_2464_:
{
return v___x_2465_;
}
}
}
}
else
{
lean_object* v_a_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2475_; 
lean_dec(v___y_2440_);
lean_dec_ref(v___y_2439_);
lean_dec(v___y_2438_);
lean_dec_ref(v___y_2437_);
lean_dec(v_fvarSubst_2426_);
lean_dec(v_fst_2423_);
v_a_2468_ = lean_ctor_get(v___x_2443_, 0);
v_isSharedCheck_2475_ = !lean_is_exclusive(v___x_2443_);
if (v_isSharedCheck_2475_ == 0)
{
v___x_2470_ = v___x_2443_;
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_a_2468_);
lean_dec(v___x_2443_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2475_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v___x_2473_; 
if (v_isShared_2471_ == 0)
{
v___x_2473_ = v___x_2470_;
goto v_reusejp_2472_;
}
else
{
lean_object* v_reuseFailAlloc_2474_; 
v_reuseFailAlloc_2474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2474_, 0, v_a_2468_);
v___x_2473_ = v_reuseFailAlloc_2474_;
goto v_reusejp_2472_;
}
v_reusejp_2472_:
{
return v___x_2473_;
}
}
}
}
v___jp_2476_:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2481_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2482_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2483_ = l_Lean_LocalDecl_type(v_a_2433_);
lean_dec(v_a_2433_);
v___x_2484_ = l_Lean_indentExpr(v___x_2483_);
v___x_2485_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2485_, 0, v___x_2482_);
lean_ctor_set(v___x_2485_, 1, v___x_2484_);
v___x_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2486_, 0, v___x_2485_);
v___x_2487_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2481_, v_snd_2424_, v___x_2486_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
lean_dec(v___y_2480_);
lean_dec_ref(v___y_2479_);
lean_dec(v___y_2478_);
lean_dec_ref(v___y_2477_);
return v___x_2487_;
}
}
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_dec(v___y_2430_);
lean_dec_ref(v___y_2429_);
lean_dec(v___y_2428_);
lean_dec_ref(v___y_2427_);
lean_dec(v_fvarSubst_2426_);
lean_dec(v_snd_2424_);
lean_dec(v_fst_2423_);
v_a_2551_ = lean_ctor_get(v___x_2432_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2432_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2432_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2432_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2559_, lean_object* v_snd_2560_, lean_object* v___x_2561_, lean_object* v_fvarSubst_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
uint8_t v___x_1847__boxed_2568_; lean_object* v_res_2569_; 
v___x_1847__boxed_2568_ = lean_unbox(v___x_2561_);
v_res_2569_ = l_Lean_Meta_substEq___lam__0(v_fst_2559_, v_snd_2560_, v___x_1847__boxed_2568_, v_fvarSubst_2562_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
return v_res_2569_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2570_, lean_object* v_hFVarId_2571_, lean_object* v_fvarSubst_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
uint8_t v___x_2578_; lean_object* v___x_2579_; 
v___x_2578_ = 1;
v___x_2579_ = l_Lean_Meta_heqToEq(v_mvarId_2570_, v_hFVarId_2571_, v___x_2578_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
if (lean_obj_tag(v___x_2579_) == 0)
{
lean_object* v_a_2580_; lean_object* v_fst_2581_; lean_object* v_snd_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; lean_object* v___x_2585_; 
v_a_2580_ = lean_ctor_get(v___x_2579_, 0);
lean_inc(v_a_2580_);
lean_dec_ref_known(v___x_2579_, 1);
v_fst_2581_ = lean_ctor_get(v_a_2580_, 0);
lean_inc(v_fst_2581_);
v_snd_2582_ = lean_ctor_get(v_a_2580_, 1);
lean_inc_n(v_snd_2582_, 2);
lean_dec(v_a_2580_);
v___x_2583_ = lean_box(v___x_2578_);
v___f_2584_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2584_, 0, v_fst_2581_);
lean_closure_set(v___f_2584_, 1, v_snd_2582_);
lean_closure_set(v___f_2584_, 2, v___x_2583_);
lean_closure_set(v___f_2584_, 3, v_fvarSubst_2572_);
v___x_2585_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_snd_2582_, v___f_2584_, v_a_2573_, v_a_2574_, v_a_2575_, v_a_2576_);
return v___x_2585_;
}
else
{
lean_object* v_a_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2593_; 
lean_dec(v_fvarSubst_2572_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2594_, lean_object* v_hFVarId_2595_, lean_object* v_fvarSubst_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_){
_start:
{
lean_object* v_res_2602_; 
v_res_2602_ = l_Lean_Meta_substEq(v_mvarId_2594_, v_hFVarId_2595_, v_fvarSubst_2596_, v_a_2597_, v_a_2598_, v_a_2599_, v_a_2600_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
return v_res_2602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2603_, lean_object* v_mvarId_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
lean_object* v___x_2610_; 
lean_inc(v_h_2603_);
v___x_2610_ = l_Lean_FVarId_getType___redArg(v_h_2603_, v___y_2605_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2610_) == 0)
{
lean_object* v_a_2611_; lean_object* v___x_2612_; 
v_a_2611_ = lean_ctor_get(v___x_2610_, 0);
lean_inc_n(v_a_2611_, 2);
lean_dec_ref_known(v___x_2610_, 1);
v___x_2612_ = l_Lean_Meta_matchEq_x3f(v_a_2611_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
if (lean_obj_tag(v_a_2613_) == 0)
{
lean_object* v___x_2614_; 
v___x_2614_ = l_Lean_Meta_matchHEq_x3f(v_a_2611_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2614_) == 0)
{
lean_object* v_a_2615_; 
v_a_2615_ = lean_ctor_get(v___x_2614_, 0);
lean_inc(v_a_2615_);
lean_dec_ref_known(v___x_2614_, 1);
if (lean_obj_tag(v_a_2615_) == 0)
{
lean_object* v___x_2616_; 
v___x_2616_ = l_Lean_Meta_substVar(v_mvarId_2604_, v_h_2603_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2616_;
}
else
{
uint8_t v___x_2617_; lean_object* v___x_2618_; 
lean_dec_ref_known(v_a_2615_, 1);
v___x_2617_ = 1;
lean_inc(v_h_2603_);
lean_inc(v_mvarId_2604_);
v___x_2618_ = l_Lean_Meta_heqToEq(v_mvarId_2604_, v_h_2603_, v___x_2617_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v_fst_2620_; lean_object* v_snd_2621_; uint8_t v___x_2622_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v_fst_2620_ = lean_ctor_get(v_a_2619_, 0);
lean_inc(v_fst_2620_);
v_snd_2621_ = lean_ctor_get(v_a_2619_, 1);
lean_inc(v_snd_2621_);
lean_dec(v_a_2619_);
v___x_2622_ = l_Lean_instBEqMVarId_beq(v_mvarId_2604_, v_snd_2621_);
if (v___x_2622_ == 0)
{
lean_object* v___x_2623_; 
lean_dec(v_mvarId_2604_);
lean_dec(v_h_2603_);
v___x_2623_ = l_Lean_Meta_subst(v_snd_2621_, v_fst_2620_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2623_;
}
else
{
lean_object* v___x_2624_; 
lean_dec(v_snd_2621_);
lean_dec(v_fst_2620_);
v___x_2624_ = l_Lean_Meta_substVar(v_mvarId_2604_, v_h_2603_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
return v___x_2624_;
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_mvarId_2604_);
lean_dec(v_h_2603_);
v_a_2625_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2618_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2618_);
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
lean_dec(v_mvarId_2604_);
lean_dec(v_h_2603_);
v_a_2633_ = lean_ctor_get(v___x_2614_, 0);
v_isSharedCheck_2640_ = !lean_is_exclusive(v___x_2614_);
if (v_isSharedCheck_2640_ == 0)
{
v___x_2635_ = v___x_2614_;
v_isShared_2636_ = v_isSharedCheck_2640_;
goto v_resetjp_2634_;
}
else
{
lean_inc(v_a_2633_);
lean_dec(v___x_2614_);
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
lean_object* v___x_2641_; lean_object* v___x_2642_; 
lean_dec_ref_known(v_a_2613_, 1);
lean_dec(v_a_2611_);
v___x_2641_ = lean_box(0);
v___x_2642_ = l_Lean_Meta_substEq(v_mvarId_2604_, v_h_2603_, v___x_2641_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2645_; uint8_t v_isShared_2646_; uint8_t v_isSharedCheck_2651_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2651_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2651_ == 0)
{
v___x_2645_ = v___x_2642_;
v_isShared_2646_ = v_isSharedCheck_2651_;
goto v_resetjp_2644_;
}
else
{
lean_inc(v_a_2643_);
lean_dec(v___x_2642_);
v___x_2645_ = lean_box(0);
v_isShared_2646_ = v_isSharedCheck_2651_;
goto v_resetjp_2644_;
}
v_resetjp_2644_:
{
lean_object* v_snd_2647_; lean_object* v___x_2649_; 
v_snd_2647_ = lean_ctor_get(v_a_2643_, 1);
lean_inc(v_snd_2647_);
lean_dec(v_a_2643_);
if (v_isShared_2646_ == 0)
{
lean_ctor_set(v___x_2645_, 0, v_snd_2647_);
v___x_2649_ = v___x_2645_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v_snd_2647_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
return v___x_2649_;
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
v_a_2652_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2642_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2642_);
v___x_2654_ = lean_box(0);
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
v_resetjp_2653_:
{
lean_object* v___x_2657_; 
if (v_isShared_2655_ == 0)
{
v___x_2657_ = v___x_2654_;
goto v_reusejp_2656_;
}
else
{
lean_object* v_reuseFailAlloc_2658_; 
v_reuseFailAlloc_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2652_);
v___x_2657_ = v_reuseFailAlloc_2658_;
goto v_reusejp_2656_;
}
v_reusejp_2656_:
{
return v___x_2657_;
}
}
}
}
}
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_dec(v_a_2611_);
lean_dec(v_mvarId_2604_);
lean_dec(v_h_2603_);
v_a_2660_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2612_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2612_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
lean_object* v___x_2665_; 
if (v_isShared_2663_ == 0)
{
v___x_2665_ = v___x_2662_;
goto v_reusejp_2664_;
}
else
{
lean_object* v_reuseFailAlloc_2666_; 
v_reuseFailAlloc_2666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2666_, 0, v_a_2660_);
v___x_2665_ = v_reuseFailAlloc_2666_;
goto v_reusejp_2664_;
}
v_reusejp_2664_:
{
return v___x_2665_;
}
}
}
}
else
{
lean_object* v_a_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2675_; 
lean_dec(v_mvarId_2604_);
lean_dec(v_h_2603_);
v_a_2668_ = lean_ctor_get(v___x_2610_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2610_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2610_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2610_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
lean_object* v___x_2673_; 
if (v_isShared_2671_ == 0)
{
v___x_2673_ = v___x_2670_;
goto v_reusejp_2672_;
}
else
{
lean_object* v_reuseFailAlloc_2674_; 
v_reuseFailAlloc_2674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2674_, 0, v_a_2668_);
v___x_2673_ = v_reuseFailAlloc_2674_;
goto v_reusejp_2672_;
}
v_reusejp_2672_:
{
return v___x_2673_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2676_, lean_object* v_mvarId_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_, lean_object* v___y_2680_, lean_object* v___y_2681_, lean_object* v___y_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_Lean_Meta_subst___lam__0(v_h_2676_, v_mvarId_2677_, v___y_2678_, v___y_2679_, v___y_2680_, v___y_2681_);
lean_dec(v___y_2681_);
lean_dec_ref(v___y_2680_);
lean_dec(v___y_2679_);
lean_dec_ref(v___y_2678_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2684_, lean_object* v_h_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_){
_start:
{
lean_object* v___f_2691_; lean_object* v___x_2692_; 
lean_inc(v_mvarId_2684_);
v___f_2691_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2691_, 0, v_h_2685_);
lean_closure_set(v___f_2691_, 1, v_mvarId_2684_);
v___x_2692_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2684_, v___f_2691_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2693_, lean_object* v_h_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_Lean_Meta_subst(v_mvarId_2693_, v_h_2694_, v_a_2695_, v_a_2696_, v_a_2697_, v_a_2698_);
lean_dec(v_a_2698_);
lean_dec_ref(v_a_2697_);
lean_dec(v_a_2696_);
lean_dec_ref(v_a_2695_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_, lean_object* v___y_2705_){
_start:
{
lean_object* v___x_2707_; 
v___x_2707_ = l_Lean_Meta_saveState___redArg(v___y_2703_, v___y_2705_);
if (lean_obj_tag(v___x_2707_) == 0)
{
lean_object* v_a_2708_; lean_object* v___x_2709_; 
v_a_2708_ = lean_ctor_get(v___x_2707_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2707_, 1);
lean_inc(v___y_2705_);
lean_inc_ref(v___y_2704_);
lean_inc(v___y_2703_);
lean_inc_ref(v___y_2702_);
v___x_2709_ = lean_apply_5(v_x_2701_, v___y_2702_, v___y_2703_, v___y_2704_, v___y_2705_, lean_box(0));
if (lean_obj_tag(v___x_2709_) == 0)
{
lean_dec(v_a_2708_);
return v___x_2709_;
}
else
{
lean_object* v_a_2710_; uint8_t v___y_2712_; uint8_t v___x_2730_; 
v_a_2710_ = lean_ctor_get(v___x_2709_, 0);
lean_inc(v_a_2710_);
v___x_2730_ = l_Lean_Exception_isInterrupt(v_a_2710_);
if (v___x_2730_ == 0)
{
uint8_t v___x_2731_; 
lean_inc(v_a_2710_);
v___x_2731_ = l_Lean_Exception_isRuntime(v_a_2710_);
v___y_2712_ = v___x_2731_;
goto v___jp_2711_;
}
else
{
v___y_2712_ = v___x_2730_;
goto v___jp_2711_;
}
v___jp_2711_:
{
if (v___y_2712_ == 0)
{
lean_object* v___x_2713_; 
lean_dec_ref_known(v___x_2709_, 1);
v___x_2713_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2708_, v___y_2703_, v___y_2705_);
lean_dec(v_a_2708_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v___x_2715_; uint8_t v_isShared_2716_; uint8_t v_isSharedCheck_2720_; 
v_isSharedCheck_2720_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2720_ == 0)
{
lean_object* v_unused_2721_; 
v_unused_2721_ = lean_ctor_get(v___x_2713_, 0);
lean_dec(v_unused_2721_);
v___x_2715_ = v___x_2713_;
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
else
{
lean_dec(v___x_2713_);
v___x_2715_ = lean_box(0);
v_isShared_2716_ = v_isSharedCheck_2720_;
goto v_resetjp_2714_;
}
v_resetjp_2714_:
{
lean_object* v___x_2718_; 
if (v_isShared_2716_ == 0)
{
lean_ctor_set_tag(v___x_2715_, 1);
lean_ctor_set(v___x_2715_, 0, v_a_2710_);
v___x_2718_ = v___x_2715_;
goto v_reusejp_2717_;
}
else
{
lean_object* v_reuseFailAlloc_2719_; 
v_reuseFailAlloc_2719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2719_, 0, v_a_2710_);
v___x_2718_ = v_reuseFailAlloc_2719_;
goto v_reusejp_2717_;
}
v_reusejp_2717_:
{
return v___x_2718_;
}
}
}
else
{
lean_object* v_a_2722_; lean_object* v___x_2724_; uint8_t v_isShared_2725_; uint8_t v_isSharedCheck_2729_; 
lean_dec(v_a_2710_);
v_a_2722_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2724_ = v___x_2713_;
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
else
{
lean_inc(v_a_2722_);
lean_dec(v___x_2713_);
v___x_2724_ = lean_box(0);
v_isShared_2725_ = v_isSharedCheck_2729_;
goto v_resetjp_2723_;
}
v_resetjp_2723_:
{
lean_object* v___x_2727_; 
if (v_isShared_2725_ == 0)
{
v___x_2727_ = v___x_2724_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2722_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
}
else
{
lean_dec(v_a_2710_);
lean_dec(v_a_2708_);
return v___x_2709_;
}
}
}
}
else
{
lean_object* v_a_2732_; lean_object* v___x_2734_; uint8_t v_isShared_2735_; uint8_t v_isSharedCheck_2739_; 
lean_dec_ref(v_x_2701_);
v_a_2732_ = lean_ctor_get(v___x_2707_, 0);
v_isSharedCheck_2739_ = !lean_is_exclusive(v___x_2707_);
if (v_isSharedCheck_2739_ == 0)
{
v___x_2734_ = v___x_2707_;
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
else
{
lean_inc(v_a_2732_);
lean_dec(v___x_2707_);
v___x_2734_ = lean_box(0);
v_isShared_2735_ = v_isSharedCheck_2739_;
goto v_resetjp_2733_;
}
v_resetjp_2733_:
{
lean_object* v___x_2737_; 
if (v_isShared_2735_ == 0)
{
v___x_2737_ = v___x_2734_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_a_2732_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_, lean_object* v___y_2745_){
_start:
{
lean_object* v_res_2746_; 
v_res_2746_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
lean_dec(v___y_2744_);
lean_dec_ref(v___y_2743_);
lean_dec(v___y_2742_);
lean_dec_ref(v___y_2741_);
return v_res_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2747_, lean_object* v_x_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v___x_2754_; 
v___x_2754_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
return v___x_2754_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2755_, lean_object* v_x_2756_, lean_object* v___y_2757_, lean_object* v___y_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_){
_start:
{
lean_object* v_res_2762_; 
v_res_2762_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2755_, v_x_2756_, v___y_2757_, v___y_2758_, v___y_2759_, v___y_2760_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v___y_2758_);
lean_dec_ref(v___y_2757_);
return v_res_2762_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2763_, lean_object* v___y_2764_, lean_object* v___y_2765_, lean_object* v___y_2766_, lean_object* v___y_2767_){
_start:
{
lean_object* v_ref_2769_; lean_object* v___x_2770_; lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2779_; 
v_ref_2769_ = lean_ctor_get(v___y_2766_, 5);
v___x_2770_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msg_2763_, v___y_2764_, v___y_2765_, v___y_2766_, v___y_2767_);
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2773_ = v___x_2770_;
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2770_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2779_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2775_; lean_object* v___x_2777_; 
lean_inc(v_ref_2769_);
v___x_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2775_, 0, v_ref_2769_);
lean_ctor_set(v___x_2775_, 1, v_a_2771_);
if (v_isShared_2774_ == 0)
{
lean_ctor_set_tag(v___x_2773_, 1);
lean_ctor_set(v___x_2773_, 0, v___x_2775_);
v___x_2777_ = v___x_2773_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v___x_2775_);
v___x_2777_ = v_reuseFailAlloc_2778_;
goto v_reusejp_2776_;
}
v_reusejp_2776_:
{
return v___x_2777_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2780_, lean_object* v___y_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_res_2786_; 
v_res_2786_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2780_, v___y_2781_, v___y_2782_, v___y_2783_, v___y_2784_);
lean_dec(v___y_2784_);
lean_dec_ref(v___y_2783_);
lean_dec(v___y_2782_);
lean_dec_ref(v___y_2781_);
return v_res_2786_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; 
v___x_2788_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2789_ = l_Lean_stringToMessageData(v___x_2788_);
return v___x_2789_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2792_ = l_Lean_stringToMessageData(v___x_2791_);
return v___x_2792_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2794_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2795_ = l_Lean_stringToMessageData(v___x_2794_);
return v___x_2795_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; 
v___x_2797_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2798_ = l_Lean_stringToMessageData(v___x_2797_);
return v___x_2798_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2800_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2801_ = l_Lean_stringToMessageData(v___x_2800_);
return v___x_2801_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; 
v___x_2814_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2815_ = l_Lean_stringToMessageData(v___x_2814_);
return v___x_2815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2824_, uint8_t v_substLHS_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___x_2831_; 
lean_inc(v_mvarId_2824_);
v___x_2831_ = l_Lean_MVarId_getType_x27(v_mvarId_2824_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
if (lean_obj_tag(v_a_2832_) == 7)
{
lean_object* v_binderType_2836_; lean_object* v_body_2837_; uint8_t v___x_2838_; lean_object* v___y_2840_; lean_object* v___y_2841_; lean_object* v___y_2842_; lean_object* v___y_2843_; lean_object* v___y_2844_; lean_object* v___y_2845_; lean_object* v___y_2846_; lean_object* v___y_2847_; lean_object* v___y_2848_; lean_object* v___y_2849_; lean_object* v___y_2850_; lean_object* v___y_2926_; lean_object* v___y_2927_; lean_object* v___y_2928_; lean_object* v___y_2929_; lean_object* v___y_2930_; lean_object* v___y_2931_; lean_object* v___y_2932_; lean_object* v___y_2933_; lean_object* v_fst_2973_; lean_object* v_fst_2974_; lean_object* v_fst_2975_; lean_object* v_snd_2976_; lean_object* v___y_2977_; lean_object* v___y_2978_; lean_object* v___y_2979_; lean_object* v___y_2980_; 
v_binderType_2836_ = lean_ctor_get(v_a_2832_, 1);
lean_inc_ref(v_binderType_2836_);
v_body_2837_ = lean_ctor_get(v_a_2832_, 2);
lean_inc_ref(v_body_2837_);
lean_dec_ref_known(v_a_2832_, 3);
v___x_2838_ = l_Lean_Expr_hasLooseBVars(v_body_2837_);
if (v___x_2838_ == 0)
{
lean_object* v___x_2992_; 
v___x_2992_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2836_, v___y_2827_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; lean_object* v___y_2995_; lean_object* v___y_2996_; lean_object* v___y_2997_; lean_object* v___y_2998_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v___x_3009_ = l_Lean_Expr_cleanupAnnotations(v_a_2993_);
v___x_3010_ = l_Lean_Expr_isApp(v___x_3009_);
if (v___x_3010_ == 0)
{
lean_dec_ref(v___x_3009_);
lean_dec_ref(v_body_2837_);
lean_dec(v_mvarId_2824_);
v___y_2995_ = v___y_2826_;
v___y_2996_ = v___y_2827_;
v___y_2997_ = v___y_2828_;
v___y_2998_ = v___y_2829_;
goto v___jp_2994_;
}
else
{
lean_object* v_arg_3011_; lean_object* v___x_3012_; uint8_t v___x_3013_; 
v_arg_3011_ = lean_ctor_get(v___x_3009_, 1);
lean_inc_ref(v_arg_3011_);
v___x_3012_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3009_);
v___x_3013_ = l_Lean_Expr_isApp(v___x_3012_);
if (v___x_3013_ == 0)
{
lean_dec_ref(v___x_3012_);
lean_dec_ref(v_arg_3011_);
lean_dec_ref(v_body_2837_);
lean_dec(v_mvarId_2824_);
v___y_2995_ = v___y_2826_;
v___y_2996_ = v___y_2827_;
v___y_2997_ = v___y_2828_;
v___y_2998_ = v___y_2829_;
goto v___jp_2994_;
}
else
{
lean_object* v_arg_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v_arg_3014_ = lean_ctor_get(v___x_3012_, 1);
lean_inc_ref(v_arg_3014_);
v___x_3015_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3012_);
v___x_3016_ = l_Lean_Expr_isApp(v___x_3015_);
if (v___x_3016_ == 0)
{
lean_dec_ref(v___x_3015_);
lean_dec_ref(v_arg_3014_);
lean_dec_ref(v_arg_3011_);
lean_dec_ref(v_body_2837_);
lean_dec(v_mvarId_2824_);
v___y_2995_ = v___y_2826_;
v___y_2996_ = v___y_2827_;
v___y_2997_ = v___y_2828_;
v___y_2998_ = v___y_2829_;
goto v___jp_2994_;
}
else
{
lean_object* v_arg_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; uint8_t v___x_3020_; 
v_arg_3017_ = lean_ctor_get(v___x_3015_, 1);
lean_inc_ref(v_arg_3017_);
v___x_3018_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3015_);
v___x_3019_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_3020_ = l_Lean_Expr_isConstOf(v___x_3018_, v___x_3019_);
if (v___x_3020_ == 0)
{
uint8_t v___x_3021_; 
v___x_3021_ = l_Lean_Expr_isApp(v___x_3018_);
if (v___x_3021_ == 0)
{
lean_dec_ref(v___x_3018_);
lean_dec_ref(v_arg_3017_);
lean_dec_ref(v_arg_3014_);
lean_dec_ref(v_arg_3011_);
lean_dec_ref(v_body_2837_);
lean_dec(v_mvarId_2824_);
v___y_2995_ = v___y_2826_;
v___y_2996_ = v___y_2827_;
v___y_2997_ = v___y_2828_;
v___y_2998_ = v___y_2829_;
goto v___jp_2994_;
}
else
{
lean_object* v_arg_3022_; lean_object* v___y_3024_; lean_object* v___y_3025_; lean_object* v___y_3026_; lean_object* v___y_3027_; lean_object* v___x_3030_; lean_object* v___x_3031_; uint8_t v___x_3032_; 
v_arg_3022_ = lean_ctor_get(v___x_3018_, 1);
lean_inc_ref(v_arg_3022_);
v___x_3030_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3018_);
v___x_3031_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_3032_ = l_Lean_Expr_isConstOf(v___x_3030_, v___x_3031_);
lean_dec_ref(v___x_3030_);
if (v___x_3032_ == 0)
{
lean_dec_ref(v_arg_3022_);
lean_dec_ref(v_arg_3017_);
lean_dec_ref(v_arg_3014_);
lean_dec_ref(v_arg_3011_);
lean_dec_ref(v_body_2837_);
lean_dec(v_mvarId_2824_);
v___y_2995_ = v___y_2826_;
v___y_2996_ = v___y_2827_;
v___y_2997_ = v___y_2828_;
v___y_2998_ = v___y_2829_;
goto v___jp_2994_;
}
else
{
lean_object* v___x_3033_; 
lean_inc_ref(v_arg_3022_);
v___x_3033_ = l_Lean_Meta_isExprDefEq(v_arg_3022_, v_arg_3014_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_3033_) == 0)
{
lean_object* v_a_3034_; uint8_t v___x_3035_; 
v_a_3034_ = lean_ctor_get(v___x_3033_, 0);
lean_inc(v_a_3034_);
lean_dec_ref_known(v___x_3033_, 1);
v___x_3035_ = lean_unbox(v_a_3034_);
lean_dec(v_a_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; lean_object* v_a_3038_; lean_object* v___x_3040_; uint8_t v_isShared_3041_; uint8_t v_isSharedCheck_3045_; 
lean_dec_ref(v_arg_3022_);
lean_dec_ref(v_arg_3017_);
lean_dec_ref(v_arg_3011_);
lean_dec_ref(v_body_2837_);
lean_dec(v_mvarId_2824_);
v___x_3036_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_3037_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3036_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
v_a_3038_ = lean_ctor_get(v___x_3037_, 0);
v_isSharedCheck_3045_ = !lean_is_exclusive(v___x_3037_);
if (v_isSharedCheck_3045_ == 0)
{
v___x_3040_ = v___x_3037_;
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
else
{
lean_inc(v_a_3038_);
lean_dec(v___x_3037_);
v___x_3040_ = lean_box(0);
v_isShared_3041_ = v_isSharedCheck_3045_;
goto v_resetjp_3039_;
}
v_resetjp_3039_:
{
lean_object* v___x_3043_; 
if (v_isShared_3041_ == 0)
{
v___x_3043_ = v___x_3040_;
goto v_reusejp_3042_;
}
else
{
lean_object* v_reuseFailAlloc_3044_; 
v_reuseFailAlloc_3044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3044_, 0, v_a_3038_);
v___x_3043_ = v_reuseFailAlloc_3044_;
goto v_reusejp_3042_;
}
v_reusejp_3042_:
{
return v___x_3043_;
}
}
}
else
{
v___y_3024_ = v___y_2826_;
v___y_3025_ = v___y_2827_;
v___y_3026_ = v___y_2828_;
v___y_3027_ = v___y_2829_;
goto v___jp_3023_;
}
}
else
{
lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3053_; 
lean_dec_ref(v_arg_3022_);
lean_dec_ref(v_arg_3017_);
lean_dec_ref(v_arg_3011_);
lean_dec_ref(v_body_2837_);
lean_dec(v_mvarId_2824_);
v_a_3046_ = lean_ctor_get(v___x_3033_, 0);
v_isSharedCheck_3053_ = !lean_is_exclusive(v___x_3033_);
if (v_isSharedCheck_3053_ == 0)
{
v___x_3048_ = v___x_3033_;
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_dec(v___x_3033_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3053_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
lean_object* v___x_3051_; 
if (v_isShared_3049_ == 0)
{
v___x_3051_ = v___x_3048_;
goto v_reusejp_3050_;
}
else
{
lean_object* v_reuseFailAlloc_3052_; 
v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
v___x_3051_ = v_reuseFailAlloc_3052_;
goto v_reusejp_3050_;
}
v_reusejp_3050_:
{
return v___x_3051_;
}
}
}
}
v___jp_3023_:
{
if (v_substLHS_2825_ == 0)
{
lean_object* v___x_3028_; 
v___x_3028_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2973_ = v_arg_3022_;
v_fst_2974_ = v_arg_3017_;
v_fst_2975_ = v_arg_3011_;
v_snd_2976_ = v___x_3028_;
v___y_2977_ = v___y_3024_;
v___y_2978_ = v___y_3025_;
v___y_2979_ = v___y_3026_;
v___y_2980_ = v___y_3027_;
goto v___jp_2972_;
}
else
{
lean_object* v___x_3029_; 
v___x_3029_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2973_ = v_arg_3022_;
v_fst_2974_ = v_arg_3011_;
v_fst_2975_ = v_arg_3017_;
v_snd_2976_ = v___x_3029_;
v___y_2977_ = v___y_3024_;
v___y_2978_ = v___y_3025_;
v___y_2979_ = v___y_3026_;
v___y_2980_ = v___y_3027_;
goto v___jp_2972_;
}
}
}
}
else
{
lean_dec_ref(v___x_3018_);
if (v_substLHS_2825_ == 0)
{
lean_object* v___x_3054_; 
v___x_3054_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2973_ = v_arg_3017_;
v_fst_2974_ = v_arg_3014_;
v_fst_2975_ = v_arg_3011_;
v_snd_2976_ = v___x_3054_;
v___y_2977_ = v___y_2826_;
v___y_2978_ = v___y_2827_;
v___y_2979_ = v___y_2828_;
v___y_2980_ = v___y_2829_;
goto v___jp_2972_;
}
else
{
lean_object* v___x_3055_; 
v___x_3055_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2973_ = v_arg_3017_;
v_fst_2974_ = v_arg_3011_;
v_fst_2975_ = v_arg_3014_;
v_snd_2976_ = v___x_3055_;
v___y_2977_ = v___y_2826_;
v___y_2978_ = v___y_2827_;
v___y_2979_ = v___y_2828_;
v___y_2980_ = v___y_2829_;
goto v___jp_2972_;
}
}
}
}
}
v___jp_2994_:
{
lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v_a_3001_; lean_object* v___x_3003_; uint8_t v_isShared_3004_; uint8_t v_isSharedCheck_3008_; 
v___x_2999_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_3000_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2999_, v___y_2995_, v___y_2996_, v___y_2997_, v___y_2998_);
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
}
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_dec_ref(v_body_2837_);
lean_dec(v_mvarId_2824_);
v_a_3056_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_2992_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_2992_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
else
{
lean_dec_ref(v_body_2837_);
lean_dec_ref(v_binderType_2836_);
lean_dec(v_mvarId_2824_);
goto v___jp_2833_;
}
v___jp_2839_:
{
lean_object* v___x_2851_; lean_object* v___x_2852_; uint8_t v___x_2853_; uint8_t v___x_2854_; lean_object* v___x_2855_; 
v___x_2851_ = lean_mk_empty_array_with_capacity(v___y_2842_);
lean_inc_ref(v___x_2851_);
v___x_2852_ = lean_array_push(v___x_2851_, v___y_2846_);
v___x_2853_ = 1;
v___x_2854_ = 1;
v___x_2855_ = l_Lean_Meta_mkLambdaFVars(v___x_2852_, v_body_2837_, v___x_2838_, v___x_2853_, v___x_2838_, v___x_2853_, v___x_2854_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
lean_dec_ref(v___x_2852_);
if (lean_obj_tag(v___x_2855_) == 0)
{
lean_object* v_a_2856_; lean_object* v___x_2857_; 
v_a_2856_ = lean_ctor_get(v___x_2855_, 0);
lean_inc(v_a_2856_);
lean_dec_ref_known(v___x_2855_, 1);
lean_inc(v___y_2845_);
v___x_2857_ = l_Lean_MVarId_getTag(v___y_2845_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
lean_inc_ref(v___y_2841_);
v___x_2859_ = lean_array_push(v___x_2851_, v___y_2841_);
lean_inc(v_a_2856_);
v___x_2860_ = l_Lean_Expr_beta(v_a_2856_, v___x_2859_);
lean_inc_ref(v___x_2860_);
v___x_2861_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2860_, v_a_2858_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v_a_2862_; lean_object* v___x_2863_; 
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
lean_inc(v_a_2862_);
lean_dec_ref_known(v___x_2861_, 1);
v___x_2863_ = l_Lean_Meta_getLevel(v___x_2860_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
if (lean_obj_tag(v___x_2863_) == 0)
{
lean_object* v_a_2864_; lean_object* v___x_2865_; 
v_a_2864_ = lean_ctor_get(v___x_2863_, 0);
lean_inc(v_a_2864_);
lean_dec_ref_known(v___x_2863_, 1);
lean_inc_ref(v___y_2843_);
v___x_2865_ = l_Lean_Meta_getLevel(v___y_2843_, v___y_2847_, v___y_2848_, v___y_2849_, v___y_2850_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2883_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
v___x_2867_ = lean_box(0);
v___x_2868_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2868_, 0, v_a_2866_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
v___x_2869_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2869_, 0, v_a_2864_);
lean_ctor_set(v___x_2869_, 1, v___x_2868_);
lean_inc(v___y_2840_);
v___x_2870_ = l_Lean_mkConst(v___y_2840_, v___x_2869_);
lean_inc(v_a_2862_);
lean_inc_ref(v___y_2841_);
v___x_2871_ = l_Lean_mkApp4(v___x_2870_, v___y_2843_, v___y_2841_, v_a_2856_, v_a_2862_);
v___x_2872_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v___y_2845_, v___x_2871_, v___y_2848_);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2883_ == 0)
{
lean_object* v_unused_2884_; 
v_unused_2884_ = lean_ctor_get(v___x_2872_, 0);
lean_dec(v_unused_2884_);
v___x_2874_ = v___x_2872_;
v_isShared_2875_ = v_isSharedCheck_2883_;
goto v_resetjp_2873_;
}
else
{
lean_dec(v___x_2872_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2883_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2881_; 
v___x_2876_ = l_Lean_Meta_FVarSubst_empty;
v___x_2877_ = l_Lean_Meta_FVarSubst_insert(v___x_2876_, v___y_2844_, v___y_2841_);
v___x_2878_ = l_Lean_Expr_mvarId_x21(v_a_2862_);
lean_dec(v_a_2862_);
v___x_2879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set(v___x_2874_, 0, v___x_2879_);
v___x_2881_ = v___x_2874_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v_a_2864_);
lean_dec(v_a_2862_);
lean_dec(v_a_2856_);
lean_dec(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v___y_2841_);
v_a_2885_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2865_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2865_);
v___x_2887_ = lean_box(0);
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
v_resetjp_2886_:
{
lean_object* v___x_2890_; 
if (v_isShared_2888_ == 0)
{
v___x_2890_ = v___x_2887_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_a_2885_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v_a_2862_);
lean_dec(v_a_2856_);
lean_dec(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v___y_2841_);
v_a_2893_ = lean_ctor_get(v___x_2863_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2863_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2863_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2863_);
v___x_2895_ = lean_box(0);
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
v_resetjp_2894_:
{
lean_object* v___x_2898_; 
if (v_isShared_2896_ == 0)
{
v___x_2898_ = v___x_2895_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2893_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref(v___x_2860_);
lean_dec(v_a_2856_);
lean_dec(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v___y_2841_);
v_a_2901_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2861_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2861_);
v___x_2903_ = lean_box(0);
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
v_resetjp_2902_:
{
lean_object* v___x_2906_; 
if (v_isShared_2904_ == 0)
{
v___x_2906_ = v___x_2903_;
goto v_reusejp_2905_;
}
else
{
lean_object* v_reuseFailAlloc_2907_; 
v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
v___x_2906_ = v_reuseFailAlloc_2907_;
goto v_reusejp_2905_;
}
v_reusejp_2905_:
{
return v___x_2906_;
}
}
}
}
else
{
lean_object* v_a_2909_; lean_object* v___x_2911_; uint8_t v_isShared_2912_; uint8_t v_isSharedCheck_2916_; 
lean_dec(v_a_2856_);
lean_dec_ref(v___x_2851_);
lean_dec(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v___y_2841_);
v_a_2909_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2916_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2916_ == 0)
{
v___x_2911_ = v___x_2857_;
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
else
{
lean_inc(v_a_2909_);
lean_dec(v___x_2857_);
v___x_2911_ = lean_box(0);
v_isShared_2912_ = v_isSharedCheck_2916_;
goto v_resetjp_2910_;
}
v_resetjp_2910_:
{
lean_object* v___x_2914_; 
if (v_isShared_2912_ == 0)
{
v___x_2914_ = v___x_2911_;
goto v_reusejp_2913_;
}
else
{
lean_object* v_reuseFailAlloc_2915_; 
v_reuseFailAlloc_2915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2915_, 0, v_a_2909_);
v___x_2914_ = v_reuseFailAlloc_2915_;
goto v_reusejp_2913_;
}
v_reusejp_2913_:
{
return v___x_2914_;
}
}
}
}
else
{
lean_object* v_a_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2924_; 
lean_dec_ref(v___x_2851_);
lean_dec(v___y_2845_);
lean_dec(v___y_2844_);
lean_dec_ref(v___y_2843_);
lean_dec_ref(v___y_2841_);
v_a_2917_ = lean_ctor_get(v___x_2855_, 0);
v_isSharedCheck_2924_ = !lean_is_exclusive(v___x_2855_);
if (v_isSharedCheck_2924_ == 0)
{
v___x_2919_ = v___x_2855_;
v_isShared_2920_ = v_isSharedCheck_2924_;
goto v_resetjp_2918_;
}
else
{
lean_inc(v_a_2917_);
lean_dec(v___x_2855_);
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
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2934_ = l_Lean_Expr_fvarId_x21(v___y_2929_);
v___x_2935_ = lean_unsigned_to_nat(1u);
v___x_2936_ = lean_mk_empty_array_with_capacity(v___x_2935_);
lean_inc(v___x_2934_);
v___x_2937_ = lean_array_push(v___x_2936_, v___x_2934_);
v___x_2938_ = l_Lean_MVarId_revert(v_mvarId_2824_, v___x_2937_, v___x_2838_, v___x_2838_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v_a_2939_; lean_object* v_fst_2940_; lean_object* v_snd_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2963_; 
v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
lean_inc(v_a_2939_);
lean_dec_ref_known(v___x_2938_, 1);
v_fst_2940_ = lean_ctor_get(v_a_2939_, 0);
v_snd_2941_ = lean_ctor_get(v_a_2939_, 1);
v_isSharedCheck_2963_ = !lean_is_exclusive(v_a_2939_);
if (v_isSharedCheck_2963_ == 0)
{
v___x_2943_ = v_a_2939_;
v_isShared_2944_ = v_isSharedCheck_2963_;
goto v_resetjp_2942_;
}
else
{
lean_inc(v_snd_2941_);
lean_inc(v_fst_2940_);
lean_dec(v_a_2939_);
v___x_2943_ = lean_box(0);
v_isShared_2944_ = v_isSharedCheck_2963_;
goto v_resetjp_2942_;
}
v_resetjp_2942_:
{
lean_object* v___x_2945_; uint8_t v___x_2946_; 
v___x_2945_ = lean_array_get_size(v_fst_2940_);
lean_dec(v_fst_2940_);
v___x_2946_ = lean_nat_dec_eq(v___x_2945_, v___x_2935_);
if (v___x_2946_ == 0)
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2950_; 
lean_dec(v_snd_2941_);
lean_dec(v___x_2934_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v_body_2837_);
v___x_2947_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2948_ = l_Lean_MessageData_ofExpr(v___y_2929_);
if (v_isShared_2944_ == 0)
{
lean_ctor_set_tag(v___x_2943_, 7);
lean_ctor_set(v___x_2943_, 1, v___x_2948_);
lean_ctor_set(v___x_2943_, 0, v___x_2947_);
v___x_2950_ = v___x_2943_;
goto v_reusejp_2949_;
}
else
{
lean_object* v_reuseFailAlloc_2962_; 
v_reuseFailAlloc_2962_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2962_, 0, v___x_2947_);
lean_ctor_set(v_reuseFailAlloc_2962_, 1, v___x_2948_);
v___x_2950_ = v_reuseFailAlloc_2962_;
goto v_reusejp_2949_;
}
v_reusejp_2949_:
{
lean_object* v___x_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v_a_2954_; lean_object* v___x_2956_; uint8_t v_isShared_2957_; uint8_t v_isSharedCheck_2961_; 
v___x_2951_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2952_, 0, v___x_2950_);
lean_ctor_set(v___x_2952_, 1, v___x_2951_);
v___x_2953_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2952_, v___y_2930_, v___y_2931_, v___y_2932_, v___y_2933_);
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
lean_del_object(v___x_2943_);
v___y_2840_ = v___y_2927_;
v___y_2841_ = v___y_2926_;
v___y_2842_ = v___x_2935_;
v___y_2843_ = v___y_2928_;
v___y_2844_ = v___x_2934_;
v___y_2845_ = v_snd_2941_;
v___y_2846_ = v___y_2929_;
v___y_2847_ = v___y_2930_;
v___y_2848_ = v___y_2931_;
v___y_2849_ = v___y_2932_;
v___y_2850_ = v___y_2933_;
goto v___jp_2839_;
}
}
}
else
{
lean_object* v_a_2964_; lean_object* v___x_2966_; uint8_t v_isShared_2967_; uint8_t v_isSharedCheck_2971_; 
lean_dec(v___x_2934_);
lean_dec_ref(v___y_2929_);
lean_dec_ref(v___y_2928_);
lean_dec_ref(v___y_2926_);
lean_dec_ref(v_body_2837_);
v_a_2964_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2971_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2971_ == 0)
{
v___x_2966_ = v___x_2938_;
v_isShared_2967_ = v_isSharedCheck_2971_;
goto v_resetjp_2965_;
}
else
{
lean_inc(v_a_2964_);
lean_dec(v___x_2938_);
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
v___jp_2972_:
{
uint8_t v___x_2981_; 
v___x_2981_ = l_Lean_Expr_isFVar(v_fst_2975_);
if (v___x_2981_ == 0)
{
lean_object* v___x_2982_; lean_object* v___x_2983_; lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v_fst_2975_);
lean_dec_ref(v_fst_2974_);
lean_dec_ref(v_fst_2973_);
lean_dec_ref(v_body_2837_);
lean_dec(v_mvarId_2824_);
v___x_2982_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2983_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2982_, v___y_2977_, v___y_2978_, v___y_2979_, v___y_2980_);
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2983_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2983_);
v___x_2986_ = lean_box(0);
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
v_resetjp_2985_:
{
lean_object* v___x_2989_; 
if (v_isShared_2987_ == 0)
{
v___x_2989_ = v___x_2986_;
goto v_reusejp_2988_;
}
else
{
lean_object* v_reuseFailAlloc_2990_; 
v_reuseFailAlloc_2990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2990_, 0, v_a_2984_);
v___x_2989_ = v_reuseFailAlloc_2990_;
goto v_reusejp_2988_;
}
v_reusejp_2988_:
{
return v___x_2989_;
}
}
}
else
{
v___y_2926_ = v_fst_2974_;
v___y_2927_ = v_snd_2976_;
v___y_2928_ = v_fst_2973_;
v___y_2929_ = v_fst_2975_;
v___y_2930_ = v___y_2977_;
v___y_2931_ = v___y_2978_;
v___y_2932_ = v___y_2979_;
v___y_2933_ = v___y_2980_;
goto v___jp_2925_;
}
}
}
else
{
lean_dec(v_a_2832_);
lean_dec(v_mvarId_2824_);
goto v___jp_2833_;
}
v___jp_2833_:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2835_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2834_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
return v___x_2835_;
}
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_dec(v_mvarId_2824_);
v_a_3064_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_2831_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_2831_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3069_; 
if (v_isShared_3067_ == 0)
{
v___x_3069_ = v___x_3066_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3070_; 
v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
v___x_3069_ = v_reuseFailAlloc_3070_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
return v___x_3069_;
}
}
}
}
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
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3081_, lean_object* v_i_3082_, lean_object* v_k_3083_){
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
return v___x_3087_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3091_, lean_object* v_i_3092_, lean_object* v_k_3093_){
_start:
{
uint8_t v_res_3094_; lean_object* v_r_3095_; 
v_res_3094_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3091_, v_i_3092_, v_k_3093_);
lean_dec(v_k_3093_);
lean_dec_ref(v_keys_3091_);
v_r_3095_ = lean_box(v_res_3094_);
return v_r_3095_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3096_, size_t v_x_3097_, lean_object* v_x_3098_){
_start:
{
if (lean_obj_tag(v_x_3096_) == 0)
{
lean_object* v_es_3099_; lean_object* v___x_3100_; size_t v___x_3101_; size_t v___x_3102_; lean_object* v_j_3103_; lean_object* v___x_3104_; 
v_es_3099_ = lean_ctor_get(v_x_3096_, 0);
v___x_3100_ = lean_box(2);
v___x_3101_ = ((size_t)31ULL);
v___x_3102_ = lean_usize_land(v_x_3097_, v___x_3101_);
v_j_3103_ = lean_usize_to_nat(v___x_3102_);
v___x_3104_ = lean_array_get_borrowed(v___x_3100_, v_es_3099_, v_j_3103_);
lean_dec(v_j_3103_);
switch(lean_obj_tag(v___x_3104_))
{
case 0:
{
lean_object* v_key_3105_; uint8_t v___x_3106_; 
v_key_3105_ = lean_ctor_get(v___x_3104_, 0);
v___x_3106_ = l_Lean_instBEqMVarId_beq(v_x_3098_, v_key_3105_);
return v___x_3106_;
}
case 1:
{
lean_object* v_node_3107_; size_t v___x_3108_; size_t v___x_3109_; 
v_node_3107_ = lean_ctor_get(v___x_3104_, 0);
v___x_3108_ = ((size_t)5ULL);
v___x_3109_ = lean_usize_shift_right(v_x_3097_, v___x_3108_);
v_x_3096_ = v_node_3107_;
v_x_3097_ = v___x_3109_;
goto _start;
}
default: 
{
uint8_t v___x_3111_; 
v___x_3111_ = 0;
return v___x_3111_;
}
}
}
else
{
lean_object* v_ks_3112_; lean_object* v___x_3113_; uint8_t v___x_3114_; 
v_ks_3112_ = lean_ctor_get(v_x_3096_, 0);
v___x_3113_ = lean_unsigned_to_nat(0u);
v___x_3114_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3112_, v___x_3113_, v_x_3098_);
return v___x_3114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3115_, lean_object* v_x_3116_, lean_object* v_x_3117_){
_start:
{
size_t v_x_12601__boxed_3118_; uint8_t v_res_3119_; lean_object* v_r_3120_; 
v_x_12601__boxed_3118_ = lean_unbox_usize(v_x_3116_);
lean_dec(v_x_3116_);
v_res_3119_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3115_, v_x_12601__boxed_3118_, v_x_3117_);
lean_dec(v_x_3117_);
lean_dec_ref(v_x_3115_);
v_r_3120_ = lean_box(v_res_3119_);
return v_r_3120_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3121_, lean_object* v_x_3122_){
_start:
{
uint64_t v___x_3123_; size_t v___x_3124_; uint8_t v___x_3125_; 
v___x_3123_ = l_Lean_instHashableMVarId_hash(v_x_3122_);
v___x_3124_ = lean_uint64_to_usize(v___x_3123_);
v___x_3125_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3121_, v___x_3124_, v_x_3122_);
return v___x_3125_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3126_, lean_object* v_x_3127_){
_start:
{
uint8_t v_res_3128_; lean_object* v_r_3129_; 
v_res_3128_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3126_, v_x_3127_);
lean_dec(v_x_3127_);
lean_dec_ref(v_x_3126_);
v_r_3129_ = lean_box(v_res_3128_);
return v_r_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3130_, lean_object* v___y_3131_){
_start:
{
lean_object* v___x_3133_; lean_object* v_mctx_3134_; lean_object* v_eAssignment_3135_; uint8_t v___x_3136_; lean_object* v___x_3137_; lean_object* v___x_3138_; 
v___x_3133_ = lean_st_ref_get(v___y_3131_);
v_mctx_3134_ = lean_ctor_get(v___x_3133_, 0);
lean_inc_ref(v_mctx_3134_);
lean_dec(v___x_3133_);
v_eAssignment_3135_ = lean_ctor_get(v_mctx_3134_, 8);
lean_inc_ref(v_eAssignment_3135_);
lean_dec_ref(v_mctx_3134_);
v___x_3136_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3135_, v_mvarId_3130_);
lean_dec_ref(v_eAssignment_3135_);
v___x_3137_ = lean_box(v___x_3136_);
v___x_3138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3138_, 0, v___x_3137_);
return v___x_3138_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3139_, lean_object* v___y_3140_, lean_object* v___y_3141_){
_start:
{
lean_object* v_res_3142_; 
v_res_3142_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3139_, v___y_3140_);
lean_dec(v___y_3140_);
lean_dec(v_mvarId_3139_);
return v_res_3142_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
v___x_3144_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3145_ = l_Lean_stringToMessageData(v___x_3144_);
return v___x_3145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3146_, uint8_t v___y_3147_, lean_object* v_____r_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_){
_start:
{
lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___x_3190_; lean_object* v_a_3191_; uint8_t v___x_3192_; 
v___x_3190_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3146_, v___y_3150_);
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref(v___x_3190_);
v___x_3192_ = lean_unbox(v_a_3191_);
lean_dec(v_a_3191_);
if (v___x_3192_ == 0)
{
v___y_3155_ = v___y_3149_;
v___y_3156_ = v___y_3150_;
v___y_3157_ = v___y_3151_;
v___y_3158_ = v___y_3152_;
goto v___jp_3154_;
}
else
{
lean_object* v___x_3193_; lean_object* v___x_3194_; lean_object* v_a_3195_; lean_object* v___x_3197_; uint8_t v_isShared_3198_; uint8_t v_isSharedCheck_3202_; 
lean_dec(v_mvarId_3146_);
v___x_3193_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3194_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3193_, v___y_3149_, v___y_3150_, v___y_3151_, v___y_3152_);
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
v___jp_3154_:
{
lean_object* v___x_3159_; 
v___x_3159_ = l_Lean_Meta_intro1Core(v_mvarId_3146_, v___y_3147_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
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
v___x_3164_ = l_Lean_Meta_substEq(v_snd_3162_, v_fst_3161_, v___x_3163_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3203_, lean_object* v___y_3204_, lean_object* v_____r_3205_, lean_object* v___y_3206_, lean_object* v___y_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_){
_start:
{
uint8_t v___y_12673__boxed_3211_; lean_object* v_res_3212_; 
v___y_12673__boxed_3211_ = lean_unbox(v___y_3204_);
v_res_3212_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3203_, v___y_12673__boxed_3211_, v_____r_3205_, v___y_3206_, v___y_3207_, v___y_3208_, v___y_3209_);
lean_dec(v___y_3209_);
lean_dec_ref(v___y_3208_);
lean_dec(v___y_3207_);
lean_dec_ref(v___y_3206_);
return v_res_3212_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__2(void){
_start:
{
lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3216_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3217_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
v___x_3218_ = l_Lean_Name_append(v___x_3217_, v___x_3216_);
return v___x_3218_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__4(void){
_start:
{
lean_object* v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__3));
v___x_3221_ = l_Lean_stringToMessageData(v___x_3220_);
return v___x_3221_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__6(void){
_start:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__5));
v___x_3224_ = l_Lean_stringToMessageData(v___x_3223_);
return v___x_3224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3225_, uint8_t v_substLHS_3226_, lean_object* v_a_3227_, lean_object* v_a_3228_, lean_object* v_a_3229_, lean_object* v_a_3230_){
_start:
{
lean_object* v___y_3233_; lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
lean_inc(v_mvarId_3225_);
v___x_3252_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3225_, v___x_3251_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3252_) == 0)
{
lean_object* v___x_3253_; lean_object* v___f_3254_; lean_object* v___x_3255_; lean_object* v___x_3256_; 
lean_dec_ref_known(v___x_3252_, 1);
v___x_3253_ = lean_box(v_substLHS_3226_);
lean_inc_n(v_mvarId_3225_, 2);
v___f_3254_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3254_, 0, v_mvarId_3225_);
lean_closure_set(v___f_3254_, 1, v___x_3253_);
v___x_3255_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed), 8, 3);
lean_closure_set(v___x_3255_, 0, lean_box(0));
lean_closure_set(v___x_3255_, 1, v_mvarId_3225_);
lean_closure_set(v___x_3255_, 2, v___f_3254_);
v___x_3256_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3255_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3256_) == 0)
{
lean_dec(v_mvarId_3225_);
return v___x_3256_;
}
else
{
lean_object* v_a_3257_; lean_object* v___y_3259_; uint8_t v___y_3263_; uint8_t v___x_3297_; 
v_a_3257_ = lean_ctor_get(v___x_3256_, 0);
lean_inc(v_a_3257_);
v___x_3297_ = l_Lean_Exception_isInterrupt(v_a_3257_);
if (v___x_3297_ == 0)
{
uint8_t v___x_3298_; 
lean_inc(v_a_3257_);
v___x_3298_ = l_Lean_Exception_isRuntime(v_a_3257_);
v___y_3263_ = v___x_3298_;
goto v___jp_3262_;
}
else
{
v___y_3263_ = v___x_3297_;
goto v___jp_3262_;
}
v___jp_3258_:
{
lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3260_ = lean_box(0);
lean_inc(v_a_3230_);
lean_inc_ref(v_a_3229_);
lean_inc(v_a_3228_);
lean_inc_ref(v_a_3227_);
v___x_3261_ = lean_apply_6(v___y_3259_, v___x_3260_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_, lean_box(0));
v___y_3233_ = v___x_3261_;
goto v___jp_3232_;
}
v___jp_3262_:
{
if (v___y_3263_ == 0)
{
lean_object* v___x_3265_; uint8_t v_isShared_3266_; uint8_t v_isSharedCheck_3295_; 
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3256_);
if (v_isSharedCheck_3295_ == 0)
{
lean_object* v_unused_3296_; 
v_unused_3296_ = lean_ctor_get(v___x_3256_, 0);
lean_dec(v_unused_3296_);
v___x_3265_ = v___x_3256_;
v_isShared_3266_ = v_isSharedCheck_3295_;
goto v_resetjp_3264_;
}
else
{
lean_dec(v___x_3256_);
v___x_3265_ = lean_box(0);
v_isShared_3266_ = v_isSharedCheck_3295_;
goto v_resetjp_3264_;
}
v_resetjp_3264_:
{
lean_object* v_options_3267_; lean_object* v_inheritedTraceOptions_3268_; uint8_t v_hasTrace_3269_; lean_object* v___x_3270_; lean_object* v___f_3271_; 
v_options_3267_ = lean_ctor_get(v_a_3229_, 2);
v_inheritedTraceOptions_3268_ = lean_ctor_get(v_a_3229_, 13);
v_hasTrace_3269_ = lean_ctor_get_uint8(v_options_3267_, sizeof(void*)*1);
v___x_3270_ = lean_box(v___y_3263_);
lean_inc(v_mvarId_3225_);
v___f_3271_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3271_, 0, v_mvarId_3225_);
lean_closure_set(v___f_3271_, 1, v___x_3270_);
if (v_hasTrace_3269_ == 0)
{
lean_del_object(v___x_3265_);
lean_dec(v_a_3257_);
lean_dec(v_mvarId_3225_);
v___y_3259_ = v___f_3271_;
goto v___jp_3258_;
}
else
{
lean_object* v___x_3272_; lean_object* v___x_3273_; uint8_t v___x_3274_; 
v___x_3272_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3273_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__2, &l_Lean_Meta_introSubstEq___closed__2_once, _init_l_Lean_Meta_introSubstEq___closed__2);
v___x_3274_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3268_, v_options_3267_, v___x_3273_);
if (v___x_3274_ == 0)
{
lean_del_object(v___x_3265_);
lean_dec(v_a_3257_);
lean_dec(v_mvarId_3225_);
v___y_3259_ = v___f_3271_;
goto v___jp_3258_;
}
else
{
lean_object* v___x_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3281_; 
lean_dec_ref(v___f_3271_);
v___x_3275_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__4, &l_Lean_Meta_introSubstEq___closed__4_once, _init_l_Lean_Meta_introSubstEq___closed__4);
v___x_3276_ = l_Lean_Exception_toMessageData(v_a_3257_);
v___x_3277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3275_);
lean_ctor_set(v___x_3277_, 1, v___x_3276_);
v___x_3278_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__6, &l_Lean_Meta_introSubstEq___closed__6_once, _init_l_Lean_Meta_introSubstEq___closed__6);
v___x_3279_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3277_);
lean_ctor_set(v___x_3279_, 1, v___x_3278_);
lean_inc(v_mvarId_3225_);
if (v_isShared_3266_ == 0)
{
lean_ctor_set(v___x_3265_, 0, v_mvarId_3225_);
v___x_3281_ = v___x_3265_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3294_; 
v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_mvarId_3225_);
v___x_3281_ = v_reuseFailAlloc_3294_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___x_3282_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3279_);
lean_ctor_set(v___x_3282_, 1, v___x_3281_);
v___x_3283_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_3272_, v___x_3282_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3285_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
lean_inc(v_a_3284_);
lean_dec_ref_known(v___x_3283_, 1);
v___x_3285_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3225_, v___y_3263_, v_a_3284_, v_a_3227_, v_a_3228_, v_a_3229_, v_a_3230_);
v___y_3233_ = v___x_3285_;
goto v___jp_3232_;
}
else
{
lean_object* v_a_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3293_; 
lean_dec(v_mvarId_3225_);
v_a_3286_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3293_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3293_ == 0)
{
v___x_3288_ = v___x_3283_;
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_a_3286_);
lean_dec(v___x_3283_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3293_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v___x_3291_; 
if (v_isShared_3289_ == 0)
{
v___x_3291_ = v___x_3288_;
goto v_reusejp_3290_;
}
else
{
lean_object* v_reuseFailAlloc_3292_; 
v_reuseFailAlloc_3292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3292_, 0, v_a_3286_);
v___x_3291_ = v_reuseFailAlloc_3292_;
goto v_reusejp_3290_;
}
v_reusejp_3290_:
{
return v___x_3291_;
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
lean_dec(v_a_3257_);
lean_dec(v_mvarId_3225_);
return v___x_3256_;
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v_mvarId_3225_);
v_a_3299_ = lean_ctor_get(v___x_3252_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3252_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3252_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3252_);
v___x_3301_ = lean_box(0);
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
v_resetjp_3300_:
{
lean_object* v___x_3304_; 
if (v_isShared_3302_ == 0)
{
v___x_3304_ = v___x_3301_;
goto v_reusejp_3303_;
}
else
{
lean_object* v_reuseFailAlloc_3305_; 
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3305_, 0, v_a_3299_);
v___x_3304_ = v_reuseFailAlloc_3305_;
goto v_reusejp_3303_;
}
v_reusejp_3303_:
{
return v___x_3304_;
}
}
}
v___jp_3232_:
{
if (lean_obj_tag(v___y_3233_) == 0)
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3242_; 
v_a_3234_ = lean_ctor_get(v___y_3233_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___y_3233_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3236_ = v___y_3233_;
v_isShared_3237_ = v_isSharedCheck_3242_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___y_3233_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3242_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v_a_3238_; lean_object* v___x_3240_; 
v_a_3238_ = lean_ctor_get(v_a_3234_, 0);
lean_inc(v_a_3238_);
lean_dec(v_a_3234_);
if (v_isShared_3237_ == 0)
{
lean_ctor_set(v___x_3236_, 0, v_a_3238_);
v___x_3240_ = v___x_3236_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3238_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
v_a_3243_ = lean_ctor_get(v___y_3233_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___y_3233_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___y_3233_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___y_3233_);
v___x_3245_ = lean_box(0);
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
v_resetjp_3244_:
{
lean_object* v___x_3248_; 
if (v_isShared_3246_ == 0)
{
v___x_3248_ = v___x_3245_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_a_3243_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object* v_mvarId_3307_, lean_object* v_substLHS_3308_, lean_object* v_a_3309_, lean_object* v_a_3310_, lean_object* v_a_3311_, lean_object* v_a_3312_, lean_object* v_a_3313_){
_start:
{
uint8_t v_substLHS_boxed_3314_; lean_object* v_res_3315_; 
v_substLHS_boxed_3314_ = lean_unbox(v_substLHS_3308_);
v_res_3315_ = l_Lean_Meta_introSubstEq(v_mvarId_3307_, v_substLHS_boxed_3314_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
lean_dec(v_a_3312_);
lean_dec_ref(v_a_3311_);
lean_dec(v_a_3310_);
lean_dec_ref(v_a_3309_);
return v_res_3315_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object* v_00_u03b1_3316_, lean_object* v_msg_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v___x_3323_; 
v___x_3323_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_3317_, v___y_3318_, v___y_3319_, v___y_3320_, v___y_3321_);
return v___x_3323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object* v_00_u03b1_3324_, lean_object* v_msg_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_, lean_object* v___y_3330_){
_start:
{
lean_object* v_res_3331_; 
v_res_3331_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(v_00_u03b1_3324_, v_msg_3325_, v___y_3326_, v___y_3327_, v___y_3328_, v___y_3329_);
lean_dec(v___y_3329_);
lean_dec_ref(v___y_3328_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object* v_mvarId_3332_, lean_object* v___y_3333_, lean_object* v___y_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_){
_start:
{
lean_object* v___x_3338_; 
v___x_3338_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3332_, v___y_3334_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object* v_mvarId_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_){
_start:
{
lean_object* v_res_3345_; 
v_res_3345_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_);
lean_dec(v___y_3343_);
lean_dec_ref(v___y_3342_);
lean_dec(v___y_3341_);
lean_dec_ref(v___y_3340_);
lean_dec(v_mvarId_3339_);
return v_res_3345_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object* v_00_u03b2_3346_, lean_object* v_x_3347_, lean_object* v_x_3348_){
_start:
{
uint8_t v___x_3349_; 
v___x_3349_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3347_, v_x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3350_, lean_object* v_x_3351_, lean_object* v_x_3352_){
_start:
{
uint8_t v_res_3353_; lean_object* v_r_3354_; 
v_res_3353_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(v_00_u03b2_3350_, v_x_3351_, v_x_3352_);
lean_dec(v_x_3352_);
lean_dec_ref(v_x_3351_);
v_r_3354_ = lean_box(v_res_3353_);
return v_r_3354_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_3355_, lean_object* v_x_3356_, size_t v_x_3357_, lean_object* v_x_3358_){
_start:
{
uint8_t v___x_3359_; 
v___x_3359_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3356_, v_x_3357_, v_x_3358_);
return v___x_3359_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3360_, lean_object* v_x_3361_, lean_object* v_x_3362_, lean_object* v_x_3363_){
_start:
{
size_t v_x_13037__boxed_3364_; uint8_t v_res_3365_; lean_object* v_r_3366_; 
v_x_13037__boxed_3364_ = lean_unbox_usize(v_x_3362_);
lean_dec(v_x_3362_);
v_res_3365_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3360_, v_x_3361_, v_x_13037__boxed_3364_, v_x_3363_);
lean_dec(v_x_3363_);
lean_dec_ref(v_x_3361_);
v_r_3366_ = lean_box(v_res_3365_);
return v_r_3366_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3367_, lean_object* v_keys_3368_, lean_object* v_vals_3369_, lean_object* v_heq_3370_, lean_object* v_i_3371_, lean_object* v_k_3372_){
_start:
{
uint8_t v___x_3373_; 
v___x_3373_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3368_, v_i_3371_, v_k_3372_);
return v___x_3373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3374_, lean_object* v_keys_3375_, lean_object* v_vals_3376_, lean_object* v_heq_3377_, lean_object* v_i_3378_, lean_object* v_k_3379_){
_start:
{
uint8_t v_res_3380_; lean_object* v_r_3381_; 
v_res_3380_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(v_00_u03b2_3374_, v_keys_3375_, v_vals_3376_, v_heq_3377_, v_i_3378_, v_k_3379_);
lean_dec(v_k_3379_);
lean_dec_ref(v_vals_3376_);
lean_dec_ref(v_keys_3375_);
v_r_3381_ = lean_box(v_res_3380_);
return v_r_3381_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* v_x_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_Lean_Meta_saveState___redArg(v___y_3384_, v___y_3386_);
if (lean_obj_tag(v___x_3388_) == 0)
{
lean_object* v_a_3389_; lean_object* v___x_3390_; 
v_a_3389_ = lean_ctor_get(v___x_3388_, 0);
lean_inc(v_a_3389_);
lean_dec_ref_known(v___x_3388_, 1);
lean_inc(v___y_3386_);
lean_inc_ref(v___y_3385_);
lean_inc(v___y_3384_);
lean_inc_ref(v___y_3383_);
v___x_3390_ = lean_apply_5(v_x_3382_, v___y_3383_, v___y_3384_, v___y_3385_, v___y_3386_, lean_box(0));
if (lean_obj_tag(v___x_3390_) == 0)
{
lean_object* v_a_3391_; lean_object* v___x_3393_; uint8_t v_isShared_3394_; uint8_t v_isSharedCheck_3399_; 
lean_dec(v_a_3389_);
v_a_3391_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3393_ = v___x_3390_;
v_isShared_3394_ = v_isSharedCheck_3399_;
goto v_resetjp_3392_;
}
else
{
lean_inc(v_a_3391_);
lean_dec(v___x_3390_);
v___x_3393_ = lean_box(0);
v_isShared_3394_ = v_isSharedCheck_3399_;
goto v_resetjp_3392_;
}
v_resetjp_3392_:
{
lean_object* v___x_3395_; lean_object* v___x_3397_; 
v___x_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3395_, 0, v_a_3391_);
if (v_isShared_3394_ == 0)
{
lean_ctor_set(v___x_3393_, 0, v___x_3395_);
v___x_3397_ = v___x_3393_;
goto v_reusejp_3396_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3395_);
v___x_3397_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3396_;
}
v_reusejp_3396_:
{
return v___x_3397_;
}
}
}
else
{
lean_object* v_a_3400_; lean_object* v___x_3402_; uint8_t v_isShared_3403_; uint8_t v_isSharedCheck_3429_; 
v_a_3400_ = lean_ctor_get(v___x_3390_, 0);
v_isSharedCheck_3429_ = !lean_is_exclusive(v___x_3390_);
if (v_isSharedCheck_3429_ == 0)
{
v___x_3402_ = v___x_3390_;
v_isShared_3403_ = v_isSharedCheck_3429_;
goto v_resetjp_3401_;
}
else
{
lean_inc(v_a_3400_);
lean_dec(v___x_3390_);
v___x_3402_ = lean_box(0);
v_isShared_3403_ = v_isSharedCheck_3429_;
goto v_resetjp_3401_;
}
v_resetjp_3401_:
{
uint8_t v___y_3405_; uint8_t v___x_3427_; 
v___x_3427_ = l_Lean_Exception_isInterrupt(v_a_3400_);
if (v___x_3427_ == 0)
{
uint8_t v___x_3428_; 
lean_inc(v_a_3400_);
v___x_3428_ = l_Lean_Exception_isRuntime(v_a_3400_);
v___y_3405_ = v___x_3428_;
goto v___jp_3404_;
}
else
{
v___y_3405_ = v___x_3427_;
goto v___jp_3404_;
}
v___jp_3404_:
{
if (v___y_3405_ == 0)
{
lean_object* v___x_3406_; 
lean_del_object(v___x_3402_);
lean_dec(v_a_3400_);
v___x_3406_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3389_, v___y_3384_, v___y_3386_);
lean_dec(v_a_3389_);
if (lean_obj_tag(v___x_3406_) == 0)
{
lean_object* v___x_3408_; uint8_t v_isShared_3409_; uint8_t v_isSharedCheck_3414_; 
v_isSharedCheck_3414_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3414_ == 0)
{
lean_object* v_unused_3415_; 
v_unused_3415_ = lean_ctor_get(v___x_3406_, 0);
lean_dec(v_unused_3415_);
v___x_3408_ = v___x_3406_;
v_isShared_3409_ = v_isSharedCheck_3414_;
goto v_resetjp_3407_;
}
else
{
lean_dec(v___x_3406_);
v___x_3408_ = lean_box(0);
v_isShared_3409_ = v_isSharedCheck_3414_;
goto v_resetjp_3407_;
}
v_resetjp_3407_:
{
lean_object* v___x_3410_; lean_object* v___x_3412_; 
v___x_3410_ = lean_box(0);
if (v_isShared_3409_ == 0)
{
lean_ctor_set(v___x_3408_, 0, v___x_3410_);
v___x_3412_ = v___x_3408_;
goto v_reusejp_3411_;
}
else
{
lean_object* v_reuseFailAlloc_3413_; 
v_reuseFailAlloc_3413_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3413_, 0, v___x_3410_);
v___x_3412_ = v_reuseFailAlloc_3413_;
goto v_reusejp_3411_;
}
v_reusejp_3411_:
{
return v___x_3412_;
}
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
v_a_3416_ = lean_ctor_get(v___x_3406_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3406_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3406_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3406_);
v___x_3418_ = lean_box(0);
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
v_resetjp_3417_:
{
lean_object* v___x_3421_; 
if (v_isShared_3419_ == 0)
{
v___x_3421_ = v___x_3418_;
goto v_reusejp_3420_;
}
else
{
lean_object* v_reuseFailAlloc_3422_; 
v_reuseFailAlloc_3422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3422_, 0, v_a_3416_);
v___x_3421_ = v_reuseFailAlloc_3422_;
goto v_reusejp_3420_;
}
v_reusejp_3420_:
{
return v___x_3421_;
}
}
}
}
else
{
lean_object* v___x_3425_; 
lean_dec(v_a_3389_);
if (v_isShared_3403_ == 0)
{
v___x_3425_ = v___x_3402_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3400_);
v___x_3425_ = v_reuseFailAlloc_3426_;
goto v_reusejp_3424_;
}
v_reusejp_3424_:
{
return v___x_3425_;
}
}
}
}
}
}
else
{
lean_object* v_a_3430_; lean_object* v___x_3432_; uint8_t v_isShared_3433_; uint8_t v_isSharedCheck_3437_; 
lean_dec_ref(v_x_3382_);
v_a_3430_ = lean_ctor_get(v___x_3388_, 0);
v_isSharedCheck_3437_ = !lean_is_exclusive(v___x_3388_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3432_ = v___x_3388_;
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
else
{
lean_inc(v_a_3430_);
lean_dec(v___x_3388_);
v___x_3432_ = lean_box(0);
v_isShared_3433_ = v_isSharedCheck_3437_;
goto v_resetjp_3431_;
}
v_resetjp_3431_:
{
lean_object* v___x_3435_; 
if (v_isShared_3433_ == 0)
{
v___x_3435_ = v___x_3432_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3436_; 
v_reuseFailAlloc_3436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3436_, 0, v_a_3430_);
v___x_3435_ = v_reuseFailAlloc_3436_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
return v___x_3435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object* v_x_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object* v_00_u03b1_3445_, lean_object* v_x_3446_, lean_object* v___y_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_){
_start:
{
lean_object* v___x_3452_; 
v___x_3452_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3446_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object* v_00_u03b1_3453_, lean_object* v_x_3454_, lean_object* v___y_3455_, lean_object* v___y_3456_, lean_object* v___y_3457_, lean_object* v___y_3458_, lean_object* v___y_3459_){
_start:
{
lean_object* v_res_3460_; 
v_res_3460_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(v_00_u03b1_3453_, v_x_3454_, v___y_3455_, v___y_3456_, v___y_3457_, v___y_3458_);
lean_dec(v___y_3458_);
lean_dec_ref(v___y_3457_);
lean_dec(v___y_3456_);
lean_dec_ref(v___y_3455_);
return v_res_3460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* v_mvarId_3461_, lean_object* v_hFVarId_3462_, lean_object* v_a_3463_, lean_object* v_a_3464_, lean_object* v_a_3465_, lean_object* v_a_3466_){
_start:
{
lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3468_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___boxed), 7, 2);
lean_closure_set(v___x_3468_, 0, v_mvarId_3461_);
lean_closure_set(v___x_3468_, 1, v_hFVarId_3462_);
v___x_3469_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3468_, v_a_3463_, v_a_3464_, v_a_3465_, v_a_3466_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object* v_mvarId_3470_, lean_object* v_hFVarId_3471_, lean_object* v_a_3472_, lean_object* v_a_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_){
_start:
{
lean_object* v_res_3477_; 
v_res_3477_ = l_Lean_Meta_substVar_x3f(v_mvarId_3470_, v_hFVarId_3471_, v_a_3472_, v_a_3473_, v_a_3474_, v_a_3475_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
lean_dec(v_a_3473_);
lean_dec_ref(v_a_3472_);
return v_res_3477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* v_mvarId_3478_, lean_object* v_hFVarId_3479_, lean_object* v_a_3480_, lean_object* v_a_3481_, lean_object* v_a_3482_, lean_object* v_a_3483_){
_start:
{
lean_object* v___x_3485_; lean_object* v___x_3486_; 
v___x_3485_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 7, 2);
lean_closure_set(v___x_3485_, 0, v_mvarId_3478_);
lean_closure_set(v___x_3485_, 1, v_hFVarId_3479_);
v___x_3486_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3485_, v_a_3480_, v_a_3481_, v_a_3482_, v_a_3483_);
return v___x_3486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object* v_mvarId_3487_, lean_object* v_hFVarId_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_, lean_object* v_a_3491_, lean_object* v_a_3492_, lean_object* v_a_3493_){
_start:
{
lean_object* v_res_3494_; 
v_res_3494_ = l_Lean_Meta_subst_x3f(v_mvarId_3487_, v_hFVarId_3488_, v_a_3489_, v_a_3490_, v_a_3491_, v_a_3492_);
lean_dec(v_a_3492_);
lean_dec_ref(v_a_3491_);
lean_dec(v_a_3490_);
lean_dec_ref(v_a_3489_);
return v_res_3494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* v_mvarId_3495_, lean_object* v_hFVarId_3496_, uint8_t v_symm_3497_, lean_object* v_fvarSubst_3498_, uint8_t v_clearH_3499_, uint8_t v_tryToSkip_3500_, lean_object* v_a_3501_, lean_object* v_a_3502_, lean_object* v_a_3503_, lean_object* v_a_3504_){
_start:
{
lean_object* v___x_3506_; lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
v___x_3506_ = lean_box(v_symm_3497_);
v___x_3507_ = lean_box(v_clearH_3499_);
v___x_3508_ = lean_box(v_tryToSkip_3500_);
v___x_3509_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_3509_, 0, v_mvarId_3495_);
lean_closure_set(v___x_3509_, 1, v_hFVarId_3496_);
lean_closure_set(v___x_3509_, 2, v___x_3506_);
lean_closure_set(v___x_3509_, 3, v_fvarSubst_3498_);
lean_closure_set(v___x_3509_, 4, v___x_3507_);
lean_closure_set(v___x_3509_, 5, v___x_3508_);
v___x_3510_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3509_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_);
return v___x_3510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* v_mvarId_3511_, lean_object* v_hFVarId_3512_, lean_object* v_symm_3513_, lean_object* v_fvarSubst_3514_, lean_object* v_clearH_3515_, lean_object* v_tryToSkip_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_, lean_object* v_a_3520_, lean_object* v_a_3521_){
_start:
{
uint8_t v_symm_boxed_3522_; uint8_t v_clearH_boxed_3523_; uint8_t v_tryToSkip_boxed_3524_; lean_object* v_res_3525_; 
v_symm_boxed_3522_ = lean_unbox(v_symm_3513_);
v_clearH_boxed_3523_ = lean_unbox(v_clearH_3515_);
v_tryToSkip_boxed_3524_ = lean_unbox(v_tryToSkip_3516_);
v_res_3525_ = l_Lean_Meta_substCore_x3f(v_mvarId_3511_, v_hFVarId_3512_, v_symm_boxed_3522_, v_fvarSubst_3514_, v_clearH_boxed_3523_, v_tryToSkip_boxed_3524_, v_a_3517_, v_a_3518_, v_a_3519_, v_a_3520_);
lean_dec(v_a_3520_);
lean_dec_ref(v_a_3519_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* v_mvarId_3526_, lean_object* v_hFVarId_3527_, lean_object* v_a_3528_, lean_object* v_a_3529_, lean_object* v_a_3530_, lean_object* v_a_3531_){
_start:
{
lean_object* v___x_3533_; 
lean_inc(v_mvarId_3526_);
v___x_3533_ = l_Lean_Meta_substVar_x3f(v_mvarId_3526_, v_hFVarId_3527_, v_a_3528_, v_a_3529_, v_a_3530_, v_a_3531_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object* v_mvarId_3554_, lean_object* v_hFVarId_3555_, lean_object* v_a_3556_, lean_object* v_a_3557_, lean_object* v_a_3558_, lean_object* v_a_3559_, lean_object* v_a_3560_){
_start:
{
lean_object* v_res_3561_; 
v_res_3561_ = l_Lean_Meta_trySubstVar(v_mvarId_3554_, v_hFVarId_3555_, v_a_3556_, v_a_3557_, v_a_3558_, v_a_3559_);
lean_dec(v_a_3559_);
lean_dec_ref(v_a_3558_);
lean_dec(v_a_3557_);
lean_dec_ref(v_a_3556_);
return v_res_3561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* v_mvarId_3562_, lean_object* v_hFVarId_3563_, lean_object* v_a_3564_, lean_object* v_a_3565_, lean_object* v_a_3566_, lean_object* v_a_3567_){
_start:
{
lean_object* v___x_3569_; 
lean_inc(v_mvarId_3562_);
v___x_3569_ = l_Lean_Meta_subst_x3f(v_mvarId_3562_, v_hFVarId_3563_, v_a_3564_, v_a_3565_, v_a_3566_, v_a_3567_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3581_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3572_ = v___x_3569_;
v_isShared_3573_ = v_isSharedCheck_3581_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3569_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3581_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
if (lean_obj_tag(v_a_3570_) == 0)
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v_mvarId_3562_);
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_mvarId_3562_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
else
{
lean_object* v_val_3577_; lean_object* v___x_3579_; 
lean_dec(v_mvarId_3562_);
v_val_3577_ = lean_ctor_get(v_a_3570_, 0);
lean_inc(v_val_3577_);
lean_dec_ref_known(v_a_3570_, 1);
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 0, v_val_3577_);
v___x_3579_ = v___x_3572_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_val_3577_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
return v___x_3579_;
}
}
}
}
else
{
lean_object* v_a_3582_; lean_object* v___x_3584_; uint8_t v_isShared_3585_; uint8_t v_isSharedCheck_3589_; 
lean_dec(v_mvarId_3562_);
v_a_3582_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3589_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3589_ == 0)
{
v___x_3584_ = v___x_3569_;
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
else
{
lean_inc(v_a_3582_);
lean_dec(v___x_3569_);
v___x_3584_ = lean_box(0);
v_isShared_3585_ = v_isSharedCheck_3589_;
goto v_resetjp_3583_;
}
v_resetjp_3583_:
{
lean_object* v___x_3587_; 
if (v_isShared_3585_ == 0)
{
v___x_3587_ = v___x_3584_;
goto v_reusejp_3586_;
}
else
{
lean_object* v_reuseFailAlloc_3588_; 
v_reuseFailAlloc_3588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3588_, 0, v_a_3582_);
v___x_3587_ = v_reuseFailAlloc_3588_;
goto v_reusejp_3586_;
}
v_reusejp_3586_:
{
return v___x_3587_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object* v_mvarId_3590_, lean_object* v_hFVarId_3591_, lean_object* v_a_3592_, lean_object* v_a_3593_, lean_object* v_a_3594_, lean_object* v_a_3595_, lean_object* v_a_3596_){
_start:
{
lean_object* v_res_3597_; 
v_res_3597_ = l_Lean_Meta_trySubst(v_mvarId_3590_, v_hFVarId_3591_, v_a_3592_, v_a_3593_, v_a_3594_, v_a_3595_);
lean_dec(v_a_3595_);
lean_dec_ref(v_a_3594_);
lean_dec(v_a_3593_);
lean_dec_ref(v_a_3592_);
return v_res_3597_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_mvarId_3601_, lean_object* v_as_3602_, size_t v_sz_3603_, size_t v_i_3604_, lean_object* v_b_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_, lean_object* v___y_3609_){
_start:
{
uint8_t v___x_3611_; 
v___x_3611_ = lean_usize_dec_lt(v_i_3604_, v_sz_3603_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; 
lean_dec(v_mvarId_3601_);
v___x_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3612_, 0, v_b_3605_);
return v___x_3612_;
}
else
{
lean_object* v_snd_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3666_; 
v_snd_3613_ = lean_ctor_get(v_b_3605_, 1);
v_isSharedCheck_3666_ = !lean_is_exclusive(v_b_3605_);
if (v_isSharedCheck_3666_ == 0)
{
lean_object* v_unused_3667_; 
v_unused_3667_ = lean_ctor_get(v_b_3605_, 0);
lean_dec(v_unused_3667_);
v___x_3615_ = v_b_3605_;
v_isShared_3616_ = v_isSharedCheck_3666_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_snd_3613_);
lean_dec(v_b_3605_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3666_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3617_; lean_object* v_a_3619_; lean_object* v_a_3626_; 
v___x_3617_ = lean_box(0);
v_a_3626_ = lean_array_uget(v_as_3602_, v_i_3604_);
if (lean_obj_tag(v_a_3626_) == 0)
{
v_a_3619_ = v_snd_3613_;
goto v___jp_3618_;
}
else
{
lean_object* v_val_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3665_; 
v_val_3627_ = lean_ctor_get(v_a_3626_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v_a_3626_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3629_ = v_a_3626_;
v_isShared_3630_ = v_isSharedCheck_3665_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_val_3627_);
lean_dec(v_a_3626_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3665_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; 
v___x_3631_ = l_Lean_LocalDecl_fvarId(v_val_3627_);
lean_dec(v_val_3627_);
lean_inc(v_mvarId_3601_);
v___x_3632_ = l_Lean_Meta_subst_x3f(v_mvarId_3601_, v___x_3631_, v___y_3606_, v___y_3607_, v___y_3608_, v___y_3609_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3656_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3656_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3656_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3656_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3637_; 
v___x_3637_ = lean_box(0);
if (lean_obj_tag(v_a_3633_) == 1)
{
lean_object* v___x_3639_; 
lean_del_object(v___x_3615_);
lean_dec(v_mvarId_3601_);
lean_inc_ref(v_a_3633_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v_a_3633_);
v___x_3639_ = v___x_3629_;
goto v_reusejp_3638_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v_a_3633_);
v___x_3639_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3638_;
}
v_reusejp_3638_:
{
lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3652_; 
v_isSharedCheck_3652_ = !lean_is_exclusive(v_a_3633_);
if (v_isSharedCheck_3652_ == 0)
{
lean_object* v_unused_3653_; 
v_unused_3653_ = lean_ctor_get(v_a_3633_, 0);
lean_dec(v_unused_3653_);
v___x_3641_ = v_a_3633_;
v_isShared_3642_ = v_isSharedCheck_3652_;
goto v_resetjp_3640_;
}
else
{
lean_dec(v_a_3633_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3652_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3643_; lean_object* v___x_3645_; 
v___x_3643_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3639_);
lean_ctor_set(v___x_3643_, 1, v___x_3637_);
if (v_isShared_3642_ == 0)
{
lean_ctor_set_tag(v___x_3641_, 0);
lean_ctor_set(v___x_3641_, 0, v___x_3643_);
v___x_3645_ = v___x_3641_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3646_, 0, v___x_3645_);
v___x_3647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3646_);
lean_ctor_set(v___x_3647_, 1, v_snd_3613_);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3647_);
v___x_3649_ = v___x_3635_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
}
}
else
{
lean_object* v___x_3655_; 
lean_del_object(v___x_3635_);
lean_dec(v_a_3633_);
lean_del_object(v___x_3629_);
lean_dec(v_snd_3613_);
v___x_3655_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3619_ = v___x_3655_;
goto v___jp_3618_;
}
}
}
else
{
lean_object* v_a_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3664_; 
lean_del_object(v___x_3629_);
lean_del_object(v___x_3615_);
lean_dec(v_snd_3613_);
lean_dec(v_mvarId_3601_);
v_a_3657_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3659_ = v___x_3632_;
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_a_3657_);
lean_dec(v___x_3632_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3664_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3662_; 
if (v_isShared_3660_ == 0)
{
v___x_3662_ = v___x_3659_;
goto v_reusejp_3661_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v_a_3657_);
v___x_3662_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3661_;
}
v_reusejp_3661_:
{
return v___x_3662_;
}
}
}
}
}
v___jp_3618_:
{
lean_object* v___x_3621_; 
if (v_isShared_3616_ == 0)
{
lean_ctor_set(v___x_3615_, 1, v_a_3619_);
lean_ctor_set(v___x_3615_, 0, v___x_3617_);
v___x_3621_ = v___x_3615_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v___x_3617_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_a_3619_);
v___x_3621_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
size_t v___x_3622_; size_t v___x_3623_; 
v___x_3622_ = ((size_t)1ULL);
v___x_3623_ = lean_usize_add(v_i_3604_, v___x_3622_);
v_i_3604_ = v___x_3623_;
v_b_3605_ = v___x_3621_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_mvarId_3668_, lean_object* v_as_3669_, lean_object* v_sz_3670_, lean_object* v_i_3671_, lean_object* v_b_3672_, lean_object* v___y_3673_, lean_object* v___y_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_){
_start:
{
size_t v_sz_boxed_3678_; size_t v_i_boxed_3679_; lean_object* v_res_3680_; 
v_sz_boxed_3678_ = lean_unbox_usize(v_sz_3670_);
lean_dec(v_sz_3670_);
v_i_boxed_3679_ = lean_unbox_usize(v_i_3671_);
lean_dec(v_i_3671_);
v_res_3680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3668_, v_as_3669_, v_sz_boxed_3678_, v_i_boxed_3679_, v_b_3672_, v___y_3673_, v___y_3674_, v___y_3675_, v___y_3676_);
lean_dec(v___y_3676_);
lean_dec_ref(v___y_3675_);
lean_dec(v___y_3674_);
lean_dec_ref(v___y_3673_);
lean_dec_ref(v_as_3669_);
return v_res_3680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object* v_mvarId_3681_, lean_object* v_as_3682_, size_t v_sz_3683_, size_t v_i_3684_, lean_object* v_b_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
uint8_t v___x_3691_; 
v___x_3691_ = lean_usize_dec_lt(v_i_3684_, v_sz_3683_);
if (v___x_3691_ == 0)
{
lean_object* v___x_3692_; 
lean_dec(v_mvarId_3681_);
v___x_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3692_, 0, v_b_3685_);
return v___x_3692_;
}
else
{
lean_object* v_snd_3693_; lean_object* v___x_3695_; uint8_t v_isShared_3696_; uint8_t v_isSharedCheck_3746_; 
v_snd_3693_ = lean_ctor_get(v_b_3685_, 1);
v_isSharedCheck_3746_ = !lean_is_exclusive(v_b_3685_);
if (v_isSharedCheck_3746_ == 0)
{
lean_object* v_unused_3747_; 
v_unused_3747_ = lean_ctor_get(v_b_3685_, 0);
lean_dec(v_unused_3747_);
v___x_3695_ = v_b_3685_;
v_isShared_3696_ = v_isSharedCheck_3746_;
goto v_resetjp_3694_;
}
else
{
lean_inc(v_snd_3693_);
lean_dec(v_b_3685_);
v___x_3695_ = lean_box(0);
v_isShared_3696_ = v_isSharedCheck_3746_;
goto v_resetjp_3694_;
}
v_resetjp_3694_:
{
lean_object* v___x_3697_; lean_object* v_a_3699_; lean_object* v_a_3706_; 
v___x_3697_ = lean_box(0);
v_a_3706_ = lean_array_uget(v_as_3682_, v_i_3684_);
if (lean_obj_tag(v_a_3706_) == 0)
{
v_a_3699_ = v_snd_3693_;
goto v___jp_3698_;
}
else
{
lean_object* v_val_3707_; lean_object* v___x_3709_; uint8_t v_isShared_3710_; uint8_t v_isSharedCheck_3745_; 
v_val_3707_ = lean_ctor_get(v_a_3706_, 0);
v_isSharedCheck_3745_ = !lean_is_exclusive(v_a_3706_);
if (v_isSharedCheck_3745_ == 0)
{
v___x_3709_ = v_a_3706_;
v_isShared_3710_ = v_isSharedCheck_3745_;
goto v_resetjp_3708_;
}
else
{
lean_inc(v_val_3707_);
lean_dec(v_a_3706_);
v___x_3709_ = lean_box(0);
v_isShared_3710_ = v_isSharedCheck_3745_;
goto v_resetjp_3708_;
}
v_resetjp_3708_:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = l_Lean_LocalDecl_fvarId(v_val_3707_);
lean_dec(v_val_3707_);
lean_inc(v_mvarId_3681_);
v___x_3712_ = l_Lean_Meta_subst_x3f(v_mvarId_3681_, v___x_3711_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3736_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3715_ = v___x_3712_;
v_isShared_3716_ = v_isSharedCheck_3736_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3712_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3736_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3717_; 
v___x_3717_ = lean_box(0);
if (lean_obj_tag(v_a_3713_) == 1)
{
lean_object* v___x_3719_; 
lean_del_object(v___x_3695_);
lean_dec(v_mvarId_3681_);
lean_inc_ref(v_a_3713_);
if (v_isShared_3710_ == 0)
{
lean_ctor_set(v___x_3709_, 0, v_a_3713_);
v___x_3719_ = v___x_3709_;
goto v_reusejp_3718_;
}
else
{
lean_object* v_reuseFailAlloc_3734_; 
v_reuseFailAlloc_3734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3734_, 0, v_a_3713_);
v___x_3719_ = v_reuseFailAlloc_3734_;
goto v_reusejp_3718_;
}
v_reusejp_3718_:
{
lean_object* v___x_3721_; uint8_t v_isShared_3722_; uint8_t v_isSharedCheck_3732_; 
v_isSharedCheck_3732_ = !lean_is_exclusive(v_a_3713_);
if (v_isSharedCheck_3732_ == 0)
{
lean_object* v_unused_3733_; 
v_unused_3733_ = lean_ctor_get(v_a_3713_, 0);
lean_dec(v_unused_3733_);
v___x_3721_ = v_a_3713_;
v_isShared_3722_ = v_isSharedCheck_3732_;
goto v_resetjp_3720_;
}
else
{
lean_dec(v_a_3713_);
v___x_3721_ = lean_box(0);
v_isShared_3722_ = v_isSharedCheck_3732_;
goto v_resetjp_3720_;
}
v_resetjp_3720_:
{
lean_object* v___x_3723_; lean_object* v___x_3725_; 
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3719_);
lean_ctor_set(v___x_3723_, 1, v___x_3717_);
if (v_isShared_3722_ == 0)
{
lean_ctor_set_tag(v___x_3721_, 0);
lean_ctor_set(v___x_3721_, 0, v___x_3723_);
v___x_3725_ = v___x_3721_;
goto v_reusejp_3724_;
}
else
{
lean_object* v_reuseFailAlloc_3731_; 
v_reuseFailAlloc_3731_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3731_, 0, v___x_3723_);
v___x_3725_ = v_reuseFailAlloc_3731_;
goto v_reusejp_3724_;
}
v_reusejp_3724_:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3729_; 
v___x_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3726_, 0, v___x_3725_);
v___x_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3727_, 0, v___x_3726_);
lean_ctor_set(v___x_3727_, 1, v_snd_3693_);
if (v_isShared_3716_ == 0)
{
lean_ctor_set(v___x_3715_, 0, v___x_3727_);
v___x_3729_ = v___x_3715_;
goto v_reusejp_3728_;
}
else
{
lean_object* v_reuseFailAlloc_3730_; 
v_reuseFailAlloc_3730_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3730_, 0, v___x_3727_);
v___x_3729_ = v_reuseFailAlloc_3730_;
goto v_reusejp_3728_;
}
v_reusejp_3728_:
{
return v___x_3729_;
}
}
}
}
}
else
{
lean_object* v___x_3735_; 
lean_del_object(v___x_3715_);
lean_dec(v_a_3713_);
lean_del_object(v___x_3709_);
lean_dec(v_snd_3693_);
v___x_3735_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3699_ = v___x_3735_;
goto v___jp_3698_;
}
}
}
else
{
lean_object* v_a_3737_; lean_object* v___x_3739_; uint8_t v_isShared_3740_; uint8_t v_isSharedCheck_3744_; 
lean_del_object(v___x_3709_);
lean_del_object(v___x_3695_);
lean_dec(v_snd_3693_);
lean_dec(v_mvarId_3681_);
v_a_3737_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3744_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3744_ == 0)
{
v___x_3739_ = v___x_3712_;
v_isShared_3740_ = v_isSharedCheck_3744_;
goto v_resetjp_3738_;
}
else
{
lean_inc(v_a_3737_);
lean_dec(v___x_3712_);
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
}
v___jp_3698_:
{
lean_object* v___x_3701_; 
if (v_isShared_3696_ == 0)
{
lean_ctor_set(v___x_3695_, 1, v_a_3699_);
lean_ctor_set(v___x_3695_, 0, v___x_3697_);
v___x_3701_ = v___x_3695_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3705_; 
v_reuseFailAlloc_3705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3705_, 0, v___x_3697_);
lean_ctor_set(v_reuseFailAlloc_3705_, 1, v_a_3699_);
v___x_3701_ = v_reuseFailAlloc_3705_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
size_t v___x_3702_; size_t v___x_3703_; lean_object* v___x_3704_; 
v___x_3702_ = ((size_t)1ULL);
v___x_3703_ = lean_usize_add(v_i_3684_, v___x_3702_);
v___x_3704_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3681_, v_as_3682_, v_sz_3683_, v___x_3703_, v___x_3701_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
return v___x_3704_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_3748_, lean_object* v_as_3749_, lean_object* v_sz_3750_, lean_object* v_i_3751_, lean_object* v_b_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
size_t v_sz_boxed_3758_; size_t v_i_boxed_3759_; lean_object* v_res_3760_; 
v_sz_boxed_3758_ = lean_unbox_usize(v_sz_3750_);
lean_dec(v_sz_3750_);
v_i_boxed_3759_ = lean_unbox_usize(v_i_3751_);
lean_dec(v_i_3751_);
v_res_3760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3748_, v_as_3749_, v_sz_boxed_3758_, v_i_boxed_3759_, v_b_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec_ref(v_as_3749_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* v_init_3761_, lean_object* v_mvarId_3762_, lean_object* v_n_3763_, lean_object* v_b_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
if (lean_obj_tag(v_n_3763_) == 0)
{
lean_object* v_cs_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; size_t v_sz_3773_; size_t v___x_3774_; lean_object* v___x_3775_; 
v_cs_3770_ = lean_ctor_get(v_n_3763_, 0);
v___x_3771_ = lean_box(0);
v___x_3772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3771_);
lean_ctor_set(v___x_3772_, 1, v_b_3764_);
v_sz_3773_ = lean_array_size(v_cs_3770_);
v___x_3774_ = ((size_t)0ULL);
v___x_3775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3761_, v_mvarId_3762_, v_cs_3770_, v_sz_3773_, v___x_3774_, v___x_3772_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3775_) == 0)
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3790_; 
v_a_3776_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3778_ = v___x_3775_;
v_isShared_3779_ = v_isSharedCheck_3790_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3775_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3790_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v_fst_3780_; 
v_fst_3780_ = lean_ctor_get(v_a_3776_, 0);
if (lean_obj_tag(v_fst_3780_) == 0)
{
lean_object* v_snd_3781_; lean_object* v___x_3782_; lean_object* v___x_3784_; 
v_snd_3781_ = lean_ctor_get(v_a_3776_, 1);
lean_inc(v_snd_3781_);
lean_dec(v_a_3776_);
v___x_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3782_, 0, v_snd_3781_);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v___x_3782_);
v___x_3784_ = v___x_3778_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3782_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
else
{
lean_object* v_val_3786_; lean_object* v___x_3788_; 
lean_inc_ref(v_fst_3780_);
lean_dec(v_a_3776_);
v_val_3786_ = lean_ctor_get(v_fst_3780_, 0);
lean_inc(v_val_3786_);
lean_dec_ref_known(v_fst_3780_, 1);
if (v_isShared_3779_ == 0)
{
lean_ctor_set(v___x_3778_, 0, v_val_3786_);
v___x_3788_ = v___x_3778_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_val_3786_);
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
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
v_a_3791_ = lean_ctor_get(v___x_3775_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3775_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3775_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3775_);
v___x_3793_ = lean_box(0);
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
v_resetjp_3792_:
{
lean_object* v___x_3796_; 
if (v_isShared_3794_ == 0)
{
v___x_3796_ = v___x_3793_;
goto v_reusejp_3795_;
}
else
{
lean_object* v_reuseFailAlloc_3797_; 
v_reuseFailAlloc_3797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3797_, 0, v_a_3791_);
v___x_3796_ = v_reuseFailAlloc_3797_;
goto v_reusejp_3795_;
}
v_reusejp_3795_:
{
return v___x_3796_;
}
}
}
}
else
{
lean_object* v_vs_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; size_t v_sz_3802_; size_t v___x_3803_; lean_object* v___x_3804_; 
v_vs_3799_ = lean_ctor_get(v_n_3763_, 0);
v___x_3800_ = lean_box(0);
v___x_3801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3801_, 0, v___x_3800_);
lean_ctor_set(v___x_3801_, 1, v_b_3764_);
v_sz_3802_ = lean_array_size(v_vs_3799_);
v___x_3803_ = ((size_t)0ULL);
v___x_3804_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3762_, v_vs_3799_, v_sz_3802_, v___x_3803_, v___x_3801_, v___y_3765_, v___y_3766_, v___y_3767_, v___y_3768_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3819_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3819_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3819_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
lean_object* v_fst_3809_; 
v_fst_3809_ = lean_ctor_get(v_a_3805_, 0);
if (lean_obj_tag(v_fst_3809_) == 0)
{
lean_object* v_snd_3810_; lean_object* v___x_3811_; lean_object* v___x_3813_; 
v_snd_3810_ = lean_ctor_get(v_a_3805_, 1);
lean_inc(v_snd_3810_);
lean_dec(v_a_3805_);
v___x_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3811_, 0, v_snd_3810_);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3811_);
v___x_3813_ = v___x_3807_;
goto v_reusejp_3812_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
v___x_3813_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3812_;
}
v_reusejp_3812_:
{
return v___x_3813_;
}
}
else
{
lean_object* v_val_3815_; lean_object* v___x_3817_; 
lean_inc_ref(v_fst_3809_);
lean_dec(v_a_3805_);
v_val_3815_ = lean_ctor_get(v_fst_3809_, 0);
lean_inc(v_val_3815_);
lean_dec_ref_known(v_fst_3809_, 1);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v_val_3815_);
v___x_3817_ = v___x_3807_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_val_3815_);
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
else
{
lean_object* v_a_3820_; lean_object* v___x_3822_; uint8_t v_isShared_3823_; uint8_t v_isSharedCheck_3827_; 
v_a_3820_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3804_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3804_);
v___x_3822_ = lean_box(0);
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
v_resetjp_3821_:
{
lean_object* v___x_3825_; 
if (v_isShared_3823_ == 0)
{
v___x_3825_ = v___x_3822_;
goto v_reusejp_3824_;
}
else
{
lean_object* v_reuseFailAlloc_3826_; 
v_reuseFailAlloc_3826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3826_, 0, v_a_3820_);
v___x_3825_ = v_reuseFailAlloc_3826_;
goto v_reusejp_3824_;
}
v_reusejp_3824_:
{
return v___x_3825_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_init_3828_, lean_object* v_mvarId_3829_, lean_object* v_as_3830_, size_t v_sz_3831_, size_t v_i_3832_, lean_object* v_b_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
uint8_t v___x_3839_; 
v___x_3839_ = lean_usize_dec_lt(v_i_3832_, v_sz_3831_);
if (v___x_3839_ == 0)
{
lean_object* v___x_3840_; 
lean_dec(v_mvarId_3829_);
v___x_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3840_, 0, v_b_3833_);
return v___x_3840_;
}
else
{
lean_object* v_snd_3841_; lean_object* v___x_3843_; uint8_t v_isShared_3844_; uint8_t v_isSharedCheck_3875_; 
v_snd_3841_ = lean_ctor_get(v_b_3833_, 1);
v_isSharedCheck_3875_ = !lean_is_exclusive(v_b_3833_);
if (v_isSharedCheck_3875_ == 0)
{
lean_object* v_unused_3876_; 
v_unused_3876_ = lean_ctor_get(v_b_3833_, 0);
lean_dec(v_unused_3876_);
v___x_3843_ = v_b_3833_;
v_isShared_3844_ = v_isSharedCheck_3875_;
goto v_resetjp_3842_;
}
else
{
lean_inc(v_snd_3841_);
lean_dec(v_b_3833_);
v___x_3843_ = lean_box(0);
v_isShared_3844_ = v_isSharedCheck_3875_;
goto v_resetjp_3842_;
}
v_resetjp_3842_:
{
lean_object* v_a_3845_; lean_object* v___x_3846_; 
v_a_3845_ = lean_array_uget_borrowed(v_as_3830_, v_i_3832_);
lean_inc(v_snd_3841_);
lean_inc(v_mvarId_3829_);
v___x_3846_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3828_, v_mvarId_3829_, v_a_3845_, v_snd_3841_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3866_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3849_ = v___x_3846_;
v_isShared_3850_ = v_isSharedCheck_3866_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3846_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3866_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
if (lean_obj_tag(v_a_3847_) == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3853_; 
lean_dec(v_mvarId_3829_);
v___x_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3851_, 0, v_a_3847_);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 0, v___x_3851_);
v___x_3853_ = v___x_3843_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v___x_3851_);
lean_ctor_set(v_reuseFailAlloc_3857_, 1, v_snd_3841_);
v___x_3853_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
lean_object* v___x_3855_; 
if (v_isShared_3850_ == 0)
{
lean_ctor_set(v___x_3849_, 0, v___x_3853_);
v___x_3855_ = v___x_3849_;
goto v_reusejp_3854_;
}
else
{
lean_object* v_reuseFailAlloc_3856_; 
v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3856_, 0, v___x_3853_);
v___x_3855_ = v_reuseFailAlloc_3856_;
goto v_reusejp_3854_;
}
v_reusejp_3854_:
{
return v___x_3855_;
}
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3859_; lean_object* v___x_3861_; 
lean_del_object(v___x_3849_);
lean_dec(v_snd_3841_);
v_a_3858_ = lean_ctor_get(v_a_3847_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v_a_3847_, 1);
v___x_3859_ = lean_box(0);
if (v_isShared_3844_ == 0)
{
lean_ctor_set(v___x_3843_, 1, v_a_3858_);
lean_ctor_set(v___x_3843_, 0, v___x_3859_);
v___x_3861_ = v___x_3843_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v___x_3859_);
lean_ctor_set(v_reuseFailAlloc_3865_, 1, v_a_3858_);
v___x_3861_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
size_t v___x_3862_; size_t v___x_3863_; 
v___x_3862_ = ((size_t)1ULL);
v___x_3863_ = lean_usize_add(v_i_3832_, v___x_3862_);
v_i_3832_ = v___x_3863_;
v_b_3833_ = v___x_3861_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3867_; lean_object* v___x_3869_; uint8_t v_isShared_3870_; uint8_t v_isSharedCheck_3874_; 
lean_del_object(v___x_3843_);
lean_dec(v_snd_3841_);
lean_dec(v_mvarId_3829_);
v_a_3867_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3874_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3874_ == 0)
{
v___x_3869_ = v___x_3846_;
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
else
{
lean_inc(v_a_3867_);
lean_dec(v___x_3846_);
v___x_3869_ = lean_box(0);
v_isShared_3870_ = v_isSharedCheck_3874_;
goto v_resetjp_3868_;
}
v_resetjp_3868_:
{
lean_object* v___x_3872_; 
if (v_isShared_3870_ == 0)
{
v___x_3872_ = v___x_3869_;
goto v_reusejp_3871_;
}
else
{
lean_object* v_reuseFailAlloc_3873_; 
v_reuseFailAlloc_3873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3873_, 0, v_a_3867_);
v___x_3872_ = v_reuseFailAlloc_3873_;
goto v_reusejp_3871_;
}
v_reusejp_3871_:
{
return v___x_3872_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3877_, lean_object* v_mvarId_3878_, lean_object* v_as_3879_, lean_object* v_sz_3880_, lean_object* v_i_3881_, lean_object* v_b_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_){
_start:
{
size_t v_sz_boxed_3888_; size_t v_i_boxed_3889_; lean_object* v_res_3890_; 
v_sz_boxed_3888_ = lean_unbox_usize(v_sz_3880_);
lean_dec(v_sz_3880_);
v_i_boxed_3889_ = lean_unbox_usize(v_i_3881_);
lean_dec(v_i_3881_);
v_res_3890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3877_, v_mvarId_3878_, v_as_3879_, v_sz_boxed_3888_, v_i_boxed_3889_, v_b_3882_, v___y_3883_, v___y_3884_, v___y_3885_, v___y_3886_);
lean_dec(v___y_3886_);
lean_dec_ref(v___y_3885_);
lean_dec(v___y_3884_);
lean_dec_ref(v___y_3883_);
lean_dec_ref(v_as_3879_);
lean_dec_ref(v_init_3877_);
return v_res_3890_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_init_3891_, lean_object* v_mvarId_3892_, lean_object* v_n_3893_, lean_object* v_b_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3891_, v_mvarId_3892_, v_n_3893_, v_b_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec_ref(v_n_3893_);
lean_dec_ref(v_init_3891_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3904_, lean_object* v_as_3905_, size_t v_sz_3906_, size_t v_i_3907_, lean_object* v_b_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
uint8_t v___x_3914_; 
v___x_3914_ = lean_usize_dec_lt(v_i_3907_, v_sz_3906_);
if (v___x_3914_ == 0)
{
lean_object* v___x_3915_; 
lean_dec(v_mvarId_3904_);
v___x_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3915_, 0, v_b_3908_);
return v___x_3915_;
}
else
{
lean_object* v_snd_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3968_; 
v_snd_3916_ = lean_ctor_get(v_b_3908_, 1);
v_isSharedCheck_3968_ = !lean_is_exclusive(v_b_3908_);
if (v_isSharedCheck_3968_ == 0)
{
lean_object* v_unused_3969_; 
v_unused_3969_ = lean_ctor_get(v_b_3908_, 0);
lean_dec(v_unused_3969_);
v___x_3918_ = v_b_3908_;
v_isShared_3919_ = v_isSharedCheck_3968_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_snd_3916_);
lean_dec(v_b_3908_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3968_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3920_; lean_object* v_a_3922_; lean_object* v_a_3929_; 
v___x_3920_ = lean_box(0);
v_a_3929_ = lean_array_uget(v_as_3905_, v_i_3907_);
if (lean_obj_tag(v_a_3929_) == 0)
{
v_a_3922_ = v_snd_3916_;
goto v___jp_3921_;
}
else
{
lean_object* v_val_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3967_; 
v_val_3930_ = lean_ctor_get(v_a_3929_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v_a_3929_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3932_ = v_a_3929_;
v_isShared_3933_ = v_isSharedCheck_3967_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_val_3930_);
lean_dec(v_a_3929_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3967_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3934_; lean_object* v___x_3935_; 
v___x_3934_ = l_Lean_LocalDecl_fvarId(v_val_3930_);
lean_dec(v_val_3930_);
lean_inc(v_mvarId_3904_);
v___x_3935_ = l_Lean_Meta_subst_x3f(v_mvarId_3904_, v___x_3934_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_);
if (lean_obj_tag(v___x_3935_) == 0)
{
lean_object* v_a_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3958_; 
v_a_3936_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3958_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3958_ == 0)
{
v___x_3938_ = v___x_3935_;
v_isShared_3939_ = v_isSharedCheck_3958_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_a_3936_);
lean_dec(v___x_3935_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3958_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; 
v___x_3940_ = lean_box(0);
if (lean_obj_tag(v_a_3936_) == 1)
{
lean_object* v___x_3942_; 
lean_del_object(v___x_3918_);
lean_dec(v_mvarId_3904_);
lean_inc_ref(v_a_3936_);
if (v_isShared_3933_ == 0)
{
lean_ctor_set(v___x_3932_, 0, v_a_3936_);
v___x_3942_ = v___x_3932_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v_a_3936_);
v___x_3942_ = v_reuseFailAlloc_3956_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3954_; 
v_isSharedCheck_3954_ = !lean_is_exclusive(v_a_3936_);
if (v_isSharedCheck_3954_ == 0)
{
lean_object* v_unused_3955_; 
v_unused_3955_ = lean_ctor_get(v_a_3936_, 0);
lean_dec(v_unused_3955_);
v___x_3944_ = v_a_3936_;
v_isShared_3945_ = v_isSharedCheck_3954_;
goto v_resetjp_3943_;
}
else
{
lean_dec(v_a_3936_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3954_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3946_; lean_object* v___x_3948_; 
v___x_3946_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3942_);
lean_ctor_set(v___x_3946_, 1, v___x_3940_);
if (v_isShared_3945_ == 0)
{
lean_ctor_set(v___x_3944_, 0, v___x_3946_);
v___x_3948_ = v___x_3944_;
goto v_reusejp_3947_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3946_);
v___x_3948_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3947_;
}
v_reusejp_3947_:
{
lean_object* v___x_3949_; lean_object* v___x_3951_; 
v___x_3949_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3948_);
lean_ctor_set(v___x_3949_, 1, v_snd_3916_);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 0, v___x_3949_);
v___x_3951_ = v___x_3938_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3949_);
v___x_3951_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3950_;
}
v_reusejp_3950_:
{
return v___x_3951_;
}
}
}
}
}
else
{
lean_object* v___x_3957_; 
lean_del_object(v___x_3938_);
lean_dec(v_a_3936_);
lean_del_object(v___x_3932_);
lean_dec(v_snd_3916_);
v___x_3957_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3922_ = v___x_3957_;
goto v___jp_3921_;
}
}
}
else
{
lean_object* v_a_3959_; lean_object* v___x_3961_; uint8_t v_isShared_3962_; uint8_t v_isSharedCheck_3966_; 
lean_del_object(v___x_3932_);
lean_del_object(v___x_3918_);
lean_dec(v_snd_3916_);
lean_dec(v_mvarId_3904_);
v_a_3959_ = lean_ctor_get(v___x_3935_, 0);
v_isSharedCheck_3966_ = !lean_is_exclusive(v___x_3935_);
if (v_isSharedCheck_3966_ == 0)
{
v___x_3961_ = v___x_3935_;
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
else
{
lean_inc(v_a_3959_);
lean_dec(v___x_3935_);
v___x_3961_ = lean_box(0);
v_isShared_3962_ = v_isSharedCheck_3966_;
goto v_resetjp_3960_;
}
v_resetjp_3960_:
{
lean_object* v___x_3964_; 
if (v_isShared_3962_ == 0)
{
v___x_3964_ = v___x_3961_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3965_; 
v_reuseFailAlloc_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3965_, 0, v_a_3959_);
v___x_3964_ = v_reuseFailAlloc_3965_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
return v___x_3964_;
}
}
}
}
}
v___jp_3921_:
{
lean_object* v___x_3924_; 
if (v_isShared_3919_ == 0)
{
lean_ctor_set(v___x_3918_, 1, v_a_3922_);
lean_ctor_set(v___x_3918_, 0, v___x_3920_);
v___x_3924_ = v___x_3918_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3928_; 
v_reuseFailAlloc_3928_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3928_, 0, v___x_3920_);
lean_ctor_set(v_reuseFailAlloc_3928_, 1, v_a_3922_);
v___x_3924_ = v_reuseFailAlloc_3928_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
size_t v___x_3925_; size_t v___x_3926_; 
v___x_3925_ = ((size_t)1ULL);
v___x_3926_ = lean_usize_add(v_i_3907_, v___x_3925_);
v_i_3907_ = v___x_3926_;
v_b_3908_ = v___x_3924_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3970_, lean_object* v_as_3971_, lean_object* v_sz_3972_, lean_object* v_i_3973_, lean_object* v_b_3974_, lean_object* v___y_3975_, lean_object* v___y_3976_, lean_object* v___y_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_){
_start:
{
size_t v_sz_boxed_3980_; size_t v_i_boxed_3981_; lean_object* v_res_3982_; 
v_sz_boxed_3980_ = lean_unbox_usize(v_sz_3972_);
lean_dec(v_sz_3972_);
v_i_boxed_3981_ = lean_unbox_usize(v_i_3973_);
lean_dec(v_i_3973_);
v_res_3982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3970_, v_as_3971_, v_sz_boxed_3980_, v_i_boxed_3981_, v_b_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_);
lean_dec(v___y_3978_);
lean_dec_ref(v___y_3977_);
lean_dec(v___y_3976_);
lean_dec_ref(v___y_3975_);
lean_dec_ref(v_as_3971_);
return v_res_3982_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_3983_, lean_object* v_as_3984_, size_t v_sz_3985_, size_t v_i_3986_, lean_object* v_b_3987_, lean_object* v___y_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_){
_start:
{
uint8_t v___x_3993_; 
v___x_3993_ = lean_usize_dec_lt(v_i_3986_, v_sz_3985_);
if (v___x_3993_ == 0)
{
lean_object* v___x_3994_; 
lean_dec(v_mvarId_3983_);
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v_b_3987_);
return v___x_3994_;
}
else
{
lean_object* v_snd_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4047_; 
v_snd_3995_ = lean_ctor_get(v_b_3987_, 1);
v_isSharedCheck_4047_ = !lean_is_exclusive(v_b_3987_);
if (v_isSharedCheck_4047_ == 0)
{
lean_object* v_unused_4048_; 
v_unused_4048_ = lean_ctor_get(v_b_3987_, 0);
lean_dec(v_unused_4048_);
v___x_3997_ = v_b_3987_;
v_isShared_3998_ = v_isSharedCheck_4047_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_snd_3995_);
lean_dec(v_b_3987_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4047_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_3999_; lean_object* v_a_4001_; lean_object* v_a_4008_; 
v___x_3999_ = lean_box(0);
v_a_4008_ = lean_array_uget(v_as_3984_, v_i_3986_);
if (lean_obj_tag(v_a_4008_) == 0)
{
v_a_4001_ = v_snd_3995_;
goto v___jp_4000_;
}
else
{
lean_object* v_val_4009_; lean_object* v___x_4011_; uint8_t v_isShared_4012_; uint8_t v_isSharedCheck_4046_; 
v_val_4009_ = lean_ctor_get(v_a_4008_, 0);
v_isSharedCheck_4046_ = !lean_is_exclusive(v_a_4008_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4011_ = v_a_4008_;
v_isShared_4012_ = v_isSharedCheck_4046_;
goto v_resetjp_4010_;
}
else
{
lean_inc(v_val_4009_);
lean_dec(v_a_4008_);
v___x_4011_ = lean_box(0);
v_isShared_4012_ = v_isSharedCheck_4046_;
goto v_resetjp_4010_;
}
v_resetjp_4010_:
{
lean_object* v___x_4013_; lean_object* v___x_4014_; 
v___x_4013_ = l_Lean_LocalDecl_fvarId(v_val_4009_);
lean_dec(v_val_4009_);
lean_inc(v_mvarId_3983_);
v___x_4014_ = l_Lean_Meta_subst_x3f(v_mvarId_3983_, v___x_4013_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4037_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4017_ = v___x_4014_;
v_isShared_4018_ = v_isSharedCheck_4037_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4014_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4037_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4019_; 
v___x_4019_ = lean_box(0);
if (lean_obj_tag(v_a_4015_) == 1)
{
lean_object* v___x_4021_; 
lean_del_object(v___x_3997_);
lean_dec(v_mvarId_3983_);
lean_inc_ref(v_a_4015_);
if (v_isShared_4012_ == 0)
{
lean_ctor_set(v___x_4011_, 0, v_a_4015_);
v___x_4021_ = v___x_4011_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v_a_4015_);
v___x_4021_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
lean_object* v___x_4023_; uint8_t v_isShared_4024_; uint8_t v_isSharedCheck_4033_; 
v_isSharedCheck_4033_ = !lean_is_exclusive(v_a_4015_);
if (v_isSharedCheck_4033_ == 0)
{
lean_object* v_unused_4034_; 
v_unused_4034_ = lean_ctor_get(v_a_4015_, 0);
lean_dec(v_unused_4034_);
v___x_4023_ = v_a_4015_;
v_isShared_4024_ = v_isSharedCheck_4033_;
goto v_resetjp_4022_;
}
else
{
lean_dec(v_a_4015_);
v___x_4023_ = lean_box(0);
v_isShared_4024_ = v_isSharedCheck_4033_;
goto v_resetjp_4022_;
}
v_resetjp_4022_:
{
lean_object* v___x_4025_; lean_object* v___x_4027_; 
v___x_4025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4025_, 0, v___x_4021_);
lean_ctor_set(v___x_4025_, 1, v___x_4019_);
if (v_isShared_4024_ == 0)
{
lean_ctor_set(v___x_4023_, 0, v___x_4025_);
v___x_4027_ = v___x_4023_;
goto v_reusejp_4026_;
}
else
{
lean_object* v_reuseFailAlloc_4032_; 
v_reuseFailAlloc_4032_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4032_, 0, v___x_4025_);
v___x_4027_ = v_reuseFailAlloc_4032_;
goto v_reusejp_4026_;
}
v_reusejp_4026_:
{
lean_object* v___x_4028_; lean_object* v___x_4030_; 
v___x_4028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
lean_ctor_set(v___x_4028_, 1, v_snd_3995_);
if (v_isShared_4018_ == 0)
{
lean_ctor_set(v___x_4017_, 0, v___x_4028_);
v___x_4030_ = v___x_4017_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4031_; 
v_reuseFailAlloc_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4031_, 0, v___x_4028_);
v___x_4030_ = v_reuseFailAlloc_4031_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
return v___x_4030_;
}
}
}
}
}
else
{
lean_object* v___x_4036_; 
lean_del_object(v___x_4017_);
lean_dec(v_a_4015_);
lean_del_object(v___x_4011_);
lean_dec(v_snd_3995_);
v___x_4036_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_4001_ = v___x_4036_;
goto v___jp_4000_;
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4040_; uint8_t v_isShared_4041_; uint8_t v_isSharedCheck_4045_; 
lean_del_object(v___x_4011_);
lean_del_object(v___x_3997_);
lean_dec(v_snd_3995_);
lean_dec(v_mvarId_3983_);
v_a_4038_ = lean_ctor_get(v___x_4014_, 0);
v_isSharedCheck_4045_ = !lean_is_exclusive(v___x_4014_);
if (v_isSharedCheck_4045_ == 0)
{
v___x_4040_ = v___x_4014_;
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
else
{
lean_inc(v_a_4038_);
lean_dec(v___x_4014_);
v___x_4040_ = lean_box(0);
v_isShared_4041_ = v_isSharedCheck_4045_;
goto v_resetjp_4039_;
}
v_resetjp_4039_:
{
lean_object* v___x_4043_; 
if (v_isShared_4041_ == 0)
{
v___x_4043_ = v___x_4040_;
goto v_reusejp_4042_;
}
else
{
lean_object* v_reuseFailAlloc_4044_; 
v_reuseFailAlloc_4044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4044_, 0, v_a_4038_);
v___x_4043_ = v_reuseFailAlloc_4044_;
goto v_reusejp_4042_;
}
v_reusejp_4042_:
{
return v___x_4043_;
}
}
}
}
}
v___jp_4000_:
{
lean_object* v___x_4003_; 
if (v_isShared_3998_ == 0)
{
lean_ctor_set(v___x_3997_, 1, v_a_4001_);
lean_ctor_set(v___x_3997_, 0, v___x_3999_);
v___x_4003_ = v___x_3997_;
goto v_reusejp_4002_;
}
else
{
lean_object* v_reuseFailAlloc_4007_; 
v_reuseFailAlloc_4007_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4007_, 0, v___x_3999_);
lean_ctor_set(v_reuseFailAlloc_4007_, 1, v_a_4001_);
v___x_4003_ = v_reuseFailAlloc_4007_;
goto v_reusejp_4002_;
}
v_reusejp_4002_:
{
size_t v___x_4004_; size_t v___x_4005_; lean_object* v___x_4006_; 
v___x_4004_ = ((size_t)1ULL);
v___x_4005_ = lean_usize_add(v_i_3986_, v___x_4004_);
v___x_4006_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3983_, v_as_3984_, v_sz_3985_, v___x_4005_, v___x_4003_, v___y_3988_, v___y_3989_, v___y_3990_, v___y_3991_);
return v___x_4006_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_4049_, lean_object* v_as_4050_, lean_object* v_sz_4051_, lean_object* v_i_4052_, lean_object* v_b_4053_, lean_object* v___y_4054_, lean_object* v___y_4055_, lean_object* v___y_4056_, lean_object* v___y_4057_, lean_object* v___y_4058_){
_start:
{
size_t v_sz_boxed_4059_; size_t v_i_boxed_4060_; lean_object* v_res_4061_; 
v_sz_boxed_4059_ = lean_unbox_usize(v_sz_4051_);
lean_dec(v_sz_4051_);
v_i_boxed_4060_ = lean_unbox_usize(v_i_4052_);
lean_dec(v_i_4052_);
v_res_4061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4049_, v_as_4050_, v_sz_boxed_4059_, v_i_boxed_4060_, v_b_4053_, v___y_4054_, v___y_4055_, v___y_4056_, v___y_4057_);
lean_dec(v___y_4057_);
lean_dec_ref(v___y_4056_);
lean_dec(v___y_4055_);
lean_dec_ref(v___y_4054_);
lean_dec_ref(v_as_4050_);
return v_res_4061_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4062_, lean_object* v_t_4063_, lean_object* v_init_4064_, lean_object* v___y_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_){
_start:
{
lean_object* v_root_4070_; lean_object* v_tail_4071_; lean_object* v___x_4072_; 
v_root_4070_ = lean_ctor_get(v_t_4063_, 0);
v_tail_4071_ = lean_ctor_get(v_t_4063_, 1);
lean_inc(v_mvarId_4062_);
lean_inc_ref(v_init_4064_);
v___x_4072_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_4064_, v_mvarId_4062_, v_root_4070_, v_init_4064_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
lean_dec_ref(v_init_4064_);
if (lean_obj_tag(v___x_4072_) == 0)
{
lean_object* v_a_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4109_; 
v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4075_ = v___x_4072_;
v_isShared_4076_ = v_isSharedCheck_4109_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_a_4073_);
lean_dec(v___x_4072_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4109_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
if (lean_obj_tag(v_a_4073_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4079_; 
lean_dec(v_mvarId_4062_);
v_a_4077_ = lean_ctor_get(v_a_4073_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v_a_4073_, 1);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 0, v_a_4077_);
v___x_4079_ = v___x_4075_;
goto v_reusejp_4078_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v_a_4077_);
v___x_4079_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4078_;
}
v_reusejp_4078_:
{
return v___x_4079_;
}
}
else
{
lean_object* v_a_4081_; lean_object* v___x_4082_; lean_object* v___x_4083_; size_t v_sz_4084_; size_t v___x_4085_; lean_object* v___x_4086_; 
lean_del_object(v___x_4075_);
v_a_4081_ = lean_ctor_get(v_a_4073_, 0);
lean_inc(v_a_4081_);
lean_dec_ref_known(v_a_4073_, 1);
v___x_4082_ = lean_box(0);
v___x_4083_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4083_, 0, v___x_4082_);
lean_ctor_set(v___x_4083_, 1, v_a_4081_);
v_sz_4084_ = lean_array_size(v_tail_4071_);
v___x_4085_ = ((size_t)0ULL);
v___x_4086_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4062_, v_tail_4071_, v_sz_4084_, v___x_4085_, v___x_4083_, v___y_4065_, v___y_4066_, v___y_4067_, v___y_4068_);
if (lean_obj_tag(v___x_4086_) == 0)
{
lean_object* v_a_4087_; lean_object* v___x_4089_; uint8_t v_isShared_4090_; uint8_t v_isSharedCheck_4100_; 
v_a_4087_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4089_ = v___x_4086_;
v_isShared_4090_ = v_isSharedCheck_4100_;
goto v_resetjp_4088_;
}
else
{
lean_inc(v_a_4087_);
lean_dec(v___x_4086_);
v___x_4089_ = lean_box(0);
v_isShared_4090_ = v_isSharedCheck_4100_;
goto v_resetjp_4088_;
}
v_resetjp_4088_:
{
lean_object* v_fst_4091_; 
v_fst_4091_ = lean_ctor_get(v_a_4087_, 0);
if (lean_obj_tag(v_fst_4091_) == 0)
{
lean_object* v_snd_4092_; lean_object* v___x_4094_; 
v_snd_4092_ = lean_ctor_get(v_a_4087_, 1);
lean_inc(v_snd_4092_);
lean_dec(v_a_4087_);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v_snd_4092_);
v___x_4094_ = v___x_4089_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v_snd_4092_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
return v___x_4094_;
}
}
else
{
lean_object* v_val_4096_; lean_object* v___x_4098_; 
lean_inc_ref(v_fst_4091_);
lean_dec(v_a_4087_);
v_val_4096_ = lean_ctor_get(v_fst_4091_, 0);
lean_inc(v_val_4096_);
lean_dec_ref_known(v_fst_4091_, 1);
if (v_isShared_4090_ == 0)
{
lean_ctor_set(v___x_4089_, 0, v_val_4096_);
v___x_4098_ = v___x_4089_;
goto v_reusejp_4097_;
}
else
{
lean_object* v_reuseFailAlloc_4099_; 
v_reuseFailAlloc_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4099_, 0, v_val_4096_);
v___x_4098_ = v_reuseFailAlloc_4099_;
goto v_reusejp_4097_;
}
v_reusejp_4097_:
{
return v___x_4098_;
}
}
}
}
else
{
lean_object* v_a_4101_; lean_object* v___x_4103_; uint8_t v_isShared_4104_; uint8_t v_isSharedCheck_4108_; 
v_a_4101_ = lean_ctor_get(v___x_4086_, 0);
v_isSharedCheck_4108_ = !lean_is_exclusive(v___x_4086_);
if (v_isSharedCheck_4108_ == 0)
{
v___x_4103_ = v___x_4086_;
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
else
{
lean_inc(v_a_4101_);
lean_dec(v___x_4086_);
v___x_4103_ = lean_box(0);
v_isShared_4104_ = v_isSharedCheck_4108_;
goto v_resetjp_4102_;
}
v_resetjp_4102_:
{
lean_object* v___x_4106_; 
if (v_isShared_4104_ == 0)
{
v___x_4106_ = v___x_4103_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v_a_4101_);
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
}
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
lean_dec(v_mvarId_4062_);
v_a_4110_ = lean_ctor_get(v___x_4072_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4072_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4072_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4072_);
v___x_4112_ = lean_box(0);
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
v_resetjp_4111_:
{
lean_object* v___x_4115_; 
if (v_isShared_4113_ == 0)
{
v___x_4115_ = v___x_4112_;
goto v_reusejp_4114_;
}
else
{
lean_object* v_reuseFailAlloc_4116_; 
v_reuseFailAlloc_4116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4116_, 0, v_a_4110_);
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4118_, lean_object* v_t_4119_, lean_object* v_init_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_){
_start:
{
lean_object* v_res_4126_; 
v_res_4126_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4118_, v_t_4119_, v_init_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_);
lean_dec(v___y_4124_);
lean_dec_ref(v___y_4123_);
lean_dec(v___y_4122_);
lean_dec_ref(v___y_4121_);
lean_dec_ref(v_t_4119_);
return v_res_4126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_, lean_object* v___y_4134_){
_start:
{
lean_object* v_lctx_4136_; lean_object* v_decls_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; 
v_lctx_4136_ = lean_ctor_get(v___y_4131_, 2);
v_decls_4137_ = lean_ctor_get(v_lctx_4136_, 1);
v___x_4138_ = lean_box(0);
v___x_4139_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4140_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4130_, v_decls_4137_, v___x_4139_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4143_; uint8_t v_isShared_4144_; uint8_t v_isSharedCheck_4153_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4153_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4153_ == 0)
{
v___x_4143_ = v___x_4140_;
v_isShared_4144_ = v_isSharedCheck_4153_;
goto v_resetjp_4142_;
}
else
{
lean_inc(v_a_4141_);
lean_dec(v___x_4140_);
v___x_4143_ = lean_box(0);
v_isShared_4144_ = v_isSharedCheck_4153_;
goto v_resetjp_4142_;
}
v_resetjp_4142_:
{
lean_object* v_fst_4145_; 
v_fst_4145_ = lean_ctor_get(v_a_4141_, 0);
lean_inc(v_fst_4145_);
lean_dec(v_a_4141_);
if (lean_obj_tag(v_fst_4145_) == 0)
{
lean_object* v___x_4147_; 
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v___x_4138_);
v___x_4147_ = v___x_4143_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4138_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
else
{
lean_object* v_val_4149_; lean_object* v___x_4151_; 
v_val_4149_ = lean_ctor_get(v_fst_4145_, 0);
lean_inc(v_val_4149_);
lean_dec_ref_known(v_fst_4145_, 1);
if (v_isShared_4144_ == 0)
{
lean_ctor_set(v___x_4143_, 0, v_val_4149_);
v___x_4151_ = v___x_4143_;
goto v_reusejp_4150_;
}
else
{
lean_object* v_reuseFailAlloc_4152_; 
v_reuseFailAlloc_4152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4152_, 0, v_val_4149_);
v___x_4151_ = v_reuseFailAlloc_4152_;
goto v_reusejp_4150_;
}
v_reusejp_4150_:
{
return v___x_4151_;
}
}
}
}
else
{
lean_object* v_a_4154_; lean_object* v___x_4156_; uint8_t v_isShared_4157_; uint8_t v_isSharedCheck_4161_; 
v_a_4154_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4161_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4161_ == 0)
{
v___x_4156_ = v___x_4140_;
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
else
{
lean_inc(v_a_4154_);
lean_dec(v___x_4140_);
v___x_4156_ = lean_box(0);
v_isShared_4157_ = v_isSharedCheck_4161_;
goto v_resetjp_4155_;
}
v_resetjp_4155_:
{
lean_object* v___x_4159_; 
if (v_isShared_4157_ == 0)
{
v___x_4159_ = v___x_4156_;
goto v_reusejp_4158_;
}
else
{
lean_object* v_reuseFailAlloc_4160_; 
v_reuseFailAlloc_4160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4160_, 0, v_a_4154_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_, lean_object* v___y_4166_, lean_object* v___y_4167_){
_start:
{
lean_object* v_res_4168_; 
v_res_4168_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4162_, v___y_4163_, v___y_4164_, v___y_4165_, v___y_4166_);
lean_dec(v___y_4166_);
lean_dec_ref(v___y_4165_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
return v_res_4168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v___f_4175_; lean_object* v___x_4176_; 
lean_inc(v_mvarId_4169_);
v___f_4175_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4175_, 0, v_mvarId_4169_);
v___x_4176_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_4169_, v___f_4175_, v_a_4170_, v_a_4171_, v_a_4172_, v_a_4173_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4177_, lean_object* v_a_4178_, lean_object* v_a_4179_, lean_object* v_a_4180_, lean_object* v_a_4181_, lean_object* v_a_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4177_, v_a_4178_, v_a_4179_, v_a_4180_, v_a_4181_);
lean_dec(v_a_4181_);
lean_dec_ref(v_a_4180_);
lean_dec(v_a_4179_);
lean_dec_ref(v_a_4178_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4184_, lean_object* v_a_4185_, lean_object* v_a_4186_, lean_object* v_a_4187_, lean_object* v_a_4188_){
_start:
{
lean_object* v___x_4190_; 
lean_inc(v_mvarId_4184_);
v___x_4190_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4184_, v_a_4185_, v_a_4186_, v_a_4187_, v_a_4188_);
if (lean_obj_tag(v___x_4190_) == 0)
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4200_; 
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4193_ = v___x_4190_;
v_isShared_4194_ = v_isSharedCheck_4200_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4190_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4200_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
if (lean_obj_tag(v_a_4191_) == 1)
{
lean_object* v_val_4195_; 
lean_del_object(v___x_4193_);
lean_dec(v_mvarId_4184_);
v_val_4195_ = lean_ctor_get(v_a_4191_, 0);
lean_inc(v_val_4195_);
lean_dec_ref_known(v_a_4191_, 1);
v_mvarId_4184_ = v_val_4195_;
goto _start;
}
else
{
lean_object* v___x_4198_; 
lean_dec(v_a_4191_);
if (v_isShared_4194_ == 0)
{
lean_ctor_set(v___x_4193_, 0, v_mvarId_4184_);
v___x_4198_ = v___x_4193_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v_mvarId_4184_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
else
{
lean_object* v_a_4201_; lean_object* v___x_4203_; uint8_t v_isShared_4204_; uint8_t v_isSharedCheck_4208_; 
lean_dec(v_mvarId_4184_);
v_a_4201_ = lean_ctor_get(v___x_4190_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v___x_4190_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4203_ = v___x_4190_;
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
else
{
lean_inc(v_a_4201_);
lean_dec(v___x_4190_);
v___x_4203_ = lean_box(0);
v_isShared_4204_ = v_isSharedCheck_4208_;
goto v_resetjp_4202_;
}
v_resetjp_4202_:
{
lean_object* v___x_4206_; 
if (v_isShared_4204_ == 0)
{
v___x_4206_ = v___x_4203_;
goto v_reusejp_4205_;
}
else
{
lean_object* v_reuseFailAlloc_4207_; 
v_reuseFailAlloc_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4207_, 0, v_a_4201_);
v___x_4206_ = v_reuseFailAlloc_4207_;
goto v_reusejp_4205_;
}
v_reusejp_4205_:
{
return v___x_4206_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4209_, lean_object* v_a_4210_, lean_object* v_a_4211_, lean_object* v_a_4212_, lean_object* v_a_4213_, lean_object* v_a_4214_){
_start:
{
lean_object* v_res_4215_; 
v_res_4215_ = l_Lean_Meta_substVars(v_mvarId_4209_, v_a_4210_, v_a_4211_, v_a_4212_, v_a_4213_);
lean_dec(v_a_4213_);
lean_dec_ref(v_a_4212_);
lean_dec(v_a_4211_);
lean_dec_ref(v_a_4210_);
return v_res_4215_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4278_; uint8_t v___x_4279_; lean_object* v___x_4280_; lean_object* v___x_4281_; 
v___x_4278_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_4279_ = 0;
v___x_4280_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4281_ = l_Lean_registerTraceClass(v___x_4278_, v___x_4279_, v___x_4280_);
return v___x_4281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4282_){
_start:
{
lean_object* v_res_4283_; 
v_res_4283_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4283_;
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
