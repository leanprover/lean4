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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
lean_object* v___f_51_; lean_object* v___x_23122__overap_52_; lean_object* v___x_53_; 
v___f_51_ = ((lean_object*)(l_panic___at___00Lean_Meta_substCore_spec__1___closed__0));
v___x_23122__overap_52_ = lean_panic_fn_borrowed(v___f_51_, v_msg_45_);
lean_inc(v___y_49_);
lean_inc_ref(v___y_48_);
lean_inc(v___y_47_);
lean_inc_ref(v___y_46_);
v___x_53_ = lean_apply_5(v___x_23122__overap_52_, v___y_46_, v___y_47_, v___y_48_, v___y_49_, lean_box(0));
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
lean_dec_ref_known(v___x_114_, 2);
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
v___x_98_ = lean_st_ref_put(v___y_82_, v___x_97_);
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
lean_dec_ref_known(v___x_228_, 1);
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
uint8_t v___x_27043__boxed_248_; uint8_t v___x_27044__boxed_249_; lean_object* v_res_250_; 
v___x_27043__boxed_248_ = lean_unbox(v___x_240_);
v___x_27044__boxed_249_ = lean_unbox(v___x_241_);
v_res_250_ = l_Lean_Meta_substCore___lam__1(v_type_236_, v___x_237_, v___x_238_, v___x_239_, v___x_27043__boxed_248_, v___x_27044__boxed_249_, v_hAux_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
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
v___x_427_ = lean_st_ref_put(v___y_388_, v___x_426_);
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
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0(void){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(lean_object* v_x_481_, size_t v_x_482_, size_t v_x_483_, lean_object* v_x_484_, lean_object* v_x_485_){
_start:
{
if (lean_obj_tag(v_x_481_) == 0)
{
lean_object* v_es_486_; size_t v___x_487_; size_t v___x_488_; lean_object* v_j_489_; lean_object* v___x_490_; uint8_t v___x_491_; 
v_es_486_ = lean_ctor_get(v_x_481_, 0);
v___x_487_ = ((size_t)31ULL);
v___x_488_ = lean_usize_land(v_x_482_, v___x_487_);
v_j_489_ = lean_usize_to_nat(v___x_488_);
v___x_490_ = lean_array_get_size(v_es_486_);
v___x_491_ = lean_nat_dec_lt(v_j_489_, v___x_490_);
if (v___x_491_ == 0)
{
lean_dec(v_j_489_);
lean_dec(v_x_485_);
lean_dec(v_x_484_);
return v_x_481_;
}
else
{
lean_object* v___x_493_; uint8_t v_isShared_494_; uint8_t v_isSharedCheck_530_; 
lean_inc_ref(v_es_486_);
v_isSharedCheck_530_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_530_ == 0)
{
lean_object* v_unused_531_; 
v_unused_531_ = lean_ctor_get(v_x_481_, 0);
lean_dec(v_unused_531_);
v___x_493_ = v_x_481_;
v_isShared_494_ = v_isSharedCheck_530_;
goto v_resetjp_492_;
}
else
{
lean_dec(v_x_481_);
v___x_493_ = lean_box(0);
v_isShared_494_ = v_isSharedCheck_530_;
goto v_resetjp_492_;
}
v_resetjp_492_:
{
lean_object* v_v_495_; lean_object* v___x_496_; lean_object* v_xs_x27_497_; lean_object* v___y_499_; 
v_v_495_ = lean_array_fget(v_es_486_, v_j_489_);
v___x_496_ = lean_box(0);
v_xs_x27_497_ = lean_array_fset(v_es_486_, v_j_489_, v___x_496_);
switch(lean_obj_tag(v_v_495_))
{
case 0:
{
lean_object* v_key_504_; lean_object* v_val_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_515_; 
v_key_504_ = lean_ctor_get(v_v_495_, 0);
v_val_505_ = lean_ctor_get(v_v_495_, 1);
v_isSharedCheck_515_ = !lean_is_exclusive(v_v_495_);
if (v_isSharedCheck_515_ == 0)
{
v___x_507_ = v_v_495_;
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_val_505_);
lean_inc(v_key_504_);
lean_dec(v_v_495_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_515_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
uint8_t v___x_509_; 
v___x_509_ = l_Lean_instBEqMVarId_beq(v_x_484_, v_key_504_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; lean_object* v___x_511_; 
lean_del_object(v___x_507_);
v___x_510_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_504_, v_val_505_, v_x_484_, v_x_485_);
v___x_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_511_, 0, v___x_510_);
v___y_499_ = v___x_511_;
goto v___jp_498_;
}
else
{
lean_object* v___x_513_; 
lean_dec(v_val_505_);
lean_dec(v_key_504_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 1, v_x_485_);
lean_ctor_set(v___x_507_, 0, v_x_484_);
v___x_513_ = v___x_507_;
goto v_reusejp_512_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v_x_484_);
lean_ctor_set(v_reuseFailAlloc_514_, 1, v_x_485_);
v___x_513_ = v_reuseFailAlloc_514_;
goto v_reusejp_512_;
}
v_reusejp_512_:
{
v___y_499_ = v___x_513_;
goto v___jp_498_;
}
}
}
}
case 1:
{
lean_object* v_node_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_528_; 
v_node_516_ = lean_ctor_get(v_v_495_, 0);
v_isSharedCheck_528_ = !lean_is_exclusive(v_v_495_);
if (v_isSharedCheck_528_ == 0)
{
v___x_518_ = v_v_495_;
v_isShared_519_ = v_isSharedCheck_528_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_node_516_);
lean_dec(v_v_495_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_528_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
size_t v___x_520_; size_t v___x_521_; size_t v___x_522_; size_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_526_; 
v___x_520_ = ((size_t)5ULL);
v___x_521_ = lean_usize_shift_right(v_x_482_, v___x_520_);
v___x_522_ = ((size_t)1ULL);
v___x_523_ = lean_usize_add(v_x_483_, v___x_522_);
v___x_524_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_node_516_, v___x_521_, v___x_523_, v_x_484_, v_x_485_);
if (v_isShared_519_ == 0)
{
lean_ctor_set(v___x_518_, 0, v___x_524_);
v___x_526_ = v___x_518_;
goto v_reusejp_525_;
}
else
{
lean_object* v_reuseFailAlloc_527_; 
v_reuseFailAlloc_527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_527_, 0, v___x_524_);
v___x_526_ = v_reuseFailAlloc_527_;
goto v_reusejp_525_;
}
v_reusejp_525_:
{
v___y_499_ = v___x_526_;
goto v___jp_498_;
}
}
}
default: 
{
lean_object* v___x_529_; 
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_x_484_);
lean_ctor_set(v___x_529_, 1, v_x_485_);
v___y_499_ = v___x_529_;
goto v___jp_498_;
}
}
v___jp_498_:
{
lean_object* v___x_500_; lean_object* v___x_502_; 
v___x_500_ = lean_array_fset(v_xs_x27_497_, v_j_489_, v___y_499_);
lean_dec(v_j_489_);
if (v_isShared_494_ == 0)
{
lean_ctor_set(v___x_493_, 0, v___x_500_);
v___x_502_ = v___x_493_;
goto v_reusejp_501_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v___x_500_);
v___x_502_ = v_reuseFailAlloc_503_;
goto v_reusejp_501_;
}
v_reusejp_501_:
{
return v___x_502_;
}
}
}
}
}
else
{
lean_object* v_ks_532_; lean_object* v_vs_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_551_; 
v_ks_532_ = lean_ctor_get(v_x_481_, 0);
v_vs_533_ = lean_ctor_get(v_x_481_, 1);
v_isSharedCheck_551_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_551_ == 0)
{
v___x_535_ = v_x_481_;
v_isShared_536_ = v_isSharedCheck_551_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_vs_533_);
lean_inc(v_ks_532_);
lean_dec(v_x_481_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_551_;
goto v_resetjp_534_;
}
v_resetjp_534_:
{
lean_object* v___x_538_; 
if (v_isShared_536_ == 0)
{
v___x_538_ = v___x_535_;
goto v_reusejp_537_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_ks_532_);
lean_ctor_set(v_reuseFailAlloc_550_, 1, v_vs_533_);
v___x_538_ = v_reuseFailAlloc_550_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v_newNode_539_; size_t v___x_540_; uint8_t v___x_541_; 
v_newNode_539_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v___x_538_, v_x_484_, v_x_485_);
v___x_540_ = ((size_t)7ULL);
v___x_541_ = lean_usize_dec_le(v___x_540_, v_x_483_);
if (v___x_541_ == 0)
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_539_);
v___x_543_ = lean_unsigned_to_nat(4u);
v___x_544_ = lean_nat_dec_lt(v___x_542_, v___x_543_);
lean_dec(v___x_542_);
if (v___x_544_ == 0)
{
lean_object* v_ks_545_; lean_object* v_vs_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; 
v_ks_545_ = lean_ctor_get(v_newNode_539_, 0);
lean_inc_ref(v_ks_545_);
v_vs_546_ = lean_ctor_get(v_newNode_539_, 1);
lean_inc_ref(v_vs_546_);
lean_dec_ref(v_newNode_539_);
v___x_547_ = lean_unsigned_to_nat(0u);
v___x_548_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0);
v___x_549_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_x_483_, v_ks_545_, v_vs_546_, v___x_547_, v___x_548_);
lean_dec_ref(v_vs_546_);
lean_dec_ref(v_ks_545_);
return v___x_549_;
}
else
{
return v_newNode_539_;
}
}
else
{
return v_newNode_539_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(size_t v_depth_552_, lean_object* v_keys_553_, lean_object* v_vals_554_, lean_object* v_i_555_, lean_object* v_entries_556_){
_start:
{
lean_object* v___x_557_; uint8_t v___x_558_; 
v___x_557_ = lean_array_get_size(v_keys_553_);
v___x_558_ = lean_nat_dec_lt(v_i_555_, v___x_557_);
if (v___x_558_ == 0)
{
lean_dec(v_i_555_);
return v_entries_556_;
}
else
{
lean_object* v_k_559_; lean_object* v_v_560_; uint64_t v___x_561_; size_t v_h_562_; size_t v___x_563_; lean_object* v___x_564_; size_t v___x_565_; size_t v___x_566_; size_t v___x_567_; size_t v_h_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_k_559_ = lean_array_fget_borrowed(v_keys_553_, v_i_555_);
v_v_560_ = lean_array_fget_borrowed(v_vals_554_, v_i_555_);
v___x_561_ = l_Lean_instHashableMVarId_hash(v_k_559_);
v_h_562_ = lean_uint64_to_usize(v___x_561_);
v___x_563_ = ((size_t)5ULL);
v___x_564_ = lean_unsigned_to_nat(1u);
v___x_565_ = ((size_t)1ULL);
v___x_566_ = lean_usize_sub(v_depth_552_, v___x_565_);
v___x_567_ = lean_usize_mul(v___x_563_, v___x_566_);
v_h_568_ = lean_usize_shift_right(v_h_562_, v___x_567_);
v___x_569_ = lean_nat_add(v_i_555_, v___x_564_);
lean_dec(v_i_555_);
lean_inc(v_v_560_);
lean_inc(v_k_559_);
v___x_570_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_entries_556_, v_h_568_, v_depth_552_, v_k_559_, v_v_560_);
v_i_555_ = v___x_569_;
v_entries_556_ = v___x_570_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_depth_572_, lean_object* v_keys_573_, lean_object* v_vals_574_, lean_object* v_i_575_, lean_object* v_entries_576_){
_start:
{
size_t v_depth_boxed_577_; lean_object* v_res_578_; 
v_depth_boxed_577_ = lean_unbox_usize(v_depth_572_);
lean_dec(v_depth_572_);
v_res_578_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_boxed_577_, v_keys_573_, v_vals_574_, v_i_575_, v_entries_576_);
lean_dec_ref(v_vals_574_);
lean_dec_ref(v_keys_573_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_579_, lean_object* v_x_580_, lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_){
_start:
{
size_t v_x_27415__boxed_584_; size_t v_x_27416__boxed_585_; lean_object* v_res_586_; 
v_x_27415__boxed_584_ = lean_unbox_usize(v_x_580_);
lean_dec(v_x_580_);
v_x_27416__boxed_585_ = lean_unbox_usize(v_x_581_);
lean_dec(v_x_581_);
v_res_586_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_579_, v_x_27415__boxed_584_, v_x_27416__boxed_585_, v_x_582_, v_x_583_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(lean_object* v_x_587_, lean_object* v_x_588_, lean_object* v_x_589_){
_start:
{
uint64_t v___x_590_; size_t v___x_591_; size_t v___x_592_; lean_object* v___x_593_; 
v___x_590_ = l_Lean_instHashableMVarId_hash(v_x_588_);
v___x_591_ = lean_uint64_to_usize(v___x_590_);
v___x_592_ = ((size_t)1ULL);
v___x_593_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_587_, v___x_591_, v___x_592_, v_x_588_, v_x_589_);
return v___x_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(lean_object* v_mvarId_594_, lean_object* v_val_595_, lean_object* v___y_596_){
_start:
{
lean_object* v___x_598_; lean_object* v_mctx_599_; lean_object* v_cache_600_; lean_object* v_zetaDeltaFVarIds_601_; lean_object* v_postponed_602_; lean_object* v_diag_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_632_; 
v___x_598_ = lean_st_ref_take(v___y_596_);
v_mctx_599_ = lean_ctor_get(v___x_598_, 0);
v_cache_600_ = lean_ctor_get(v___x_598_, 1);
v_zetaDeltaFVarIds_601_ = lean_ctor_get(v___x_598_, 2);
v_postponed_602_ = lean_ctor_get(v___x_598_, 3);
v_diag_603_ = lean_ctor_get(v___x_598_, 4);
v_isSharedCheck_632_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_632_ == 0)
{
v___x_605_ = v___x_598_;
v_isShared_606_ = v_isSharedCheck_632_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_diag_603_);
lean_inc(v_postponed_602_);
lean_inc(v_zetaDeltaFVarIds_601_);
lean_inc(v_cache_600_);
lean_inc(v_mctx_599_);
lean_dec(v___x_598_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_632_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v_depth_607_; lean_object* v_levelAssignDepth_608_; lean_object* v_lmvarCounter_609_; lean_object* v_mvarCounter_610_; lean_object* v_lDecls_611_; lean_object* v_decls_612_; lean_object* v_userNames_613_; lean_object* v_lAssignment_614_; lean_object* v_eAssignment_615_; lean_object* v_dAssignment_616_; lean_object* v_instanceTypedMVars_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_631_; 
v_depth_607_ = lean_ctor_get(v_mctx_599_, 0);
v_levelAssignDepth_608_ = lean_ctor_get(v_mctx_599_, 1);
v_lmvarCounter_609_ = lean_ctor_get(v_mctx_599_, 2);
v_mvarCounter_610_ = lean_ctor_get(v_mctx_599_, 3);
v_lDecls_611_ = lean_ctor_get(v_mctx_599_, 4);
v_decls_612_ = lean_ctor_get(v_mctx_599_, 5);
v_userNames_613_ = lean_ctor_get(v_mctx_599_, 6);
v_lAssignment_614_ = lean_ctor_get(v_mctx_599_, 7);
v_eAssignment_615_ = lean_ctor_get(v_mctx_599_, 8);
v_dAssignment_616_ = lean_ctor_get(v_mctx_599_, 9);
v_instanceTypedMVars_617_ = lean_ctor_get(v_mctx_599_, 10);
v_isSharedCheck_631_ = !lean_is_exclusive(v_mctx_599_);
if (v_isSharedCheck_631_ == 0)
{
v___x_619_ = v_mctx_599_;
v_isShared_620_ = v_isSharedCheck_631_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_instanceTypedMVars_617_);
lean_inc(v_dAssignment_616_);
lean_inc(v_eAssignment_615_);
lean_inc(v_lAssignment_614_);
lean_inc(v_userNames_613_);
lean_inc(v_decls_612_);
lean_inc(v_lDecls_611_);
lean_inc(v_mvarCounter_610_);
lean_inc(v_lmvarCounter_609_);
lean_inc(v_levelAssignDepth_608_);
lean_inc(v_depth_607_);
lean_dec(v_mctx_599_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_631_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
lean_object* v___x_621_; lean_object* v___x_623_; 
v___x_621_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_eAssignment_615_, v_mvarId_594_, v_val_595_);
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 8, v___x_621_);
v___x_623_ = v___x_619_;
goto v_reusejp_622_;
}
else
{
lean_object* v_reuseFailAlloc_630_; 
v_reuseFailAlloc_630_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_630_, 0, v_depth_607_);
lean_ctor_set(v_reuseFailAlloc_630_, 1, v_levelAssignDepth_608_);
lean_ctor_set(v_reuseFailAlloc_630_, 2, v_lmvarCounter_609_);
lean_ctor_set(v_reuseFailAlloc_630_, 3, v_mvarCounter_610_);
lean_ctor_set(v_reuseFailAlloc_630_, 4, v_lDecls_611_);
lean_ctor_set(v_reuseFailAlloc_630_, 5, v_decls_612_);
lean_ctor_set(v_reuseFailAlloc_630_, 6, v_userNames_613_);
lean_ctor_set(v_reuseFailAlloc_630_, 7, v_lAssignment_614_);
lean_ctor_set(v_reuseFailAlloc_630_, 8, v___x_621_);
lean_ctor_set(v_reuseFailAlloc_630_, 9, v_dAssignment_616_);
lean_ctor_set(v_reuseFailAlloc_630_, 10, v_instanceTypedMVars_617_);
v___x_623_ = v_reuseFailAlloc_630_;
goto v_reusejp_622_;
}
v_reusejp_622_:
{
lean_object* v___x_625_; 
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_623_);
v___x_625_ = v___x_605_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_629_; 
v_reuseFailAlloc_629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_629_, 0, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_629_, 1, v_cache_600_);
lean_ctor_set(v_reuseFailAlloc_629_, 2, v_zetaDeltaFVarIds_601_);
lean_ctor_set(v_reuseFailAlloc_629_, 3, v_postponed_602_);
lean_ctor_set(v_reuseFailAlloc_629_, 4, v_diag_603_);
v___x_625_ = v_reuseFailAlloc_629_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; 
v___x_626_ = lean_st_ref_put(v___y_596_, v___x_625_);
v___x_627_ = lean_box(0);
v___x_628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_628_, 0, v___x_627_);
return v___x_628_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object* v_mvarId_633_, lean_object* v_val_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v_res_637_; 
v_res_637_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_mvarId_633_, v_val_634_, v___y_635_);
lean_dec(v___y_635_);
return v_res_637_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__1(void){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_639_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__0));
v___x_640_ = l_Lean_stringToMessageData(v___x_639_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__3(void){
_start:
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__2));
v___x_643_ = l_Lean_stringToMessageData(v___x_642_);
return v___x_643_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__7(void){
_start:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; 
v___x_647_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__6));
v___x_648_ = lean_unsigned_to_nat(22u);
v___x_649_ = lean_unsigned_to_nat(64u);
v___x_650_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__5));
v___x_651_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__4));
v___x_652_ = l_mkPanicMessageWithDecl(v___x_651_, v___x_650_, v___x_649_, v___x_648_, v___x_647_);
return v___x_652_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object* v_snd_656_, lean_object* v___x_657_, lean_object* v_fvarId_658_, lean_object* v_hFVarId_659_, lean_object* v___x_660_, lean_object* v_fst_661_, lean_object* v_fvarSubst_662_, uint8_t v_clearH_663_, lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v___x_666_, uint8_t v_skip_667_, uint8_t v___x_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v_a_671_, uint8_t v_symm_672_, uint8_t v___x_673_, lean_object* v___x_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_){
_start:
{
lean_object* v___y_681_; lean_object* v___y_682_; lean_object* v___y_683_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; lean_object* v___y_697_; lean_object* v_mvarId_698_; lean_object* v___y_699_; lean_object* v___y_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v_newVal_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; uint8_t v___y_780_; lean_object* v___y_781_; lean_object* v___y_782_; lean_object* v___y_783_; lean_object* v_major_784_; lean_object* v___y_785_; lean_object* v___y_786_; lean_object* v___y_787_; lean_object* v___y_788_; uint8_t v___y_821_; lean_object* v___y_822_; lean_object* v_motive_823_; lean_object* v_newType_824_; lean_object* v___y_825_; lean_object* v___y_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___x_839_; 
lean_inc(v_snd_656_);
v___x_839_ = l_Lean_MVarId_getDecl(v_snd_656_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v_a_840_; lean_object* v___x_841_; 
v_a_840_ = lean_ctor_get(v___x_839_, 0);
lean_inc(v_a_840_);
lean_dec_ref_known(v___x_839_, 1);
lean_inc(v___x_657_);
v___x_841_ = l_Lean_FVarId_getDecl___redArg(v___x_657_, v___y_675_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
v___x_843_ = l_Lean_LocalDecl_type(v_a_842_);
lean_dec(v_a_842_);
v___x_844_ = l_Lean_Meta_matchEq_x3f(v___x_843_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_844_) == 0)
{
lean_object* v_a_845_; 
v_a_845_ = lean_ctor_get(v___x_844_, 0);
lean_inc(v_a_845_);
lean_dec_ref_known(v___x_844_, 1);
if (lean_obj_tag(v_a_845_) == 0)
{
lean_object* v___x_846_; lean_object* v___x_847_; 
lean_dec(v_a_840_);
lean_dec(v_a_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v___x_846_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__7, &l_Lean_Meta_substCore___lam__2___closed__7_once, _init_l_Lean_Meta_substCore___lam__2___closed__7);
v___x_847_ = l_panic___at___00Lean_Meta_substCore_spec__1(v___x_846_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
return v___x_847_;
}
else
{
lean_object* v_val_848_; lean_object* v_snd_849_; lean_object* v_fst_850_; lean_object* v_snd_851_; lean_object* v_type_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___f_855_; lean_object* v___y_857_; 
v_val_848_ = lean_ctor_get(v_a_845_, 0);
lean_inc(v_val_848_);
lean_dec_ref_known(v_a_845_, 1);
v_snd_849_ = lean_ctor_get(v_val_848_, 1);
lean_inc(v_snd_849_);
lean_dec(v_val_848_);
v_fst_850_ = lean_ctor_get(v_snd_849_, 0);
lean_inc(v_fst_850_);
v_snd_851_ = lean_ctor_get(v_snd_849_, 1);
lean_inc(v_snd_851_);
lean_dec(v_snd_849_);
v_type_852_ = lean_ctor_get(v_a_840_, 2);
lean_inc_ref_n(v_type_852_, 2);
lean_dec(v_a_840_);
v___x_853_ = lean_box(v___x_673_);
v___x_854_ = lean_box(v___x_668_);
lean_inc_ref(v___x_664_);
lean_inc(v___x_665_);
lean_inc_ref(v___x_660_);
v___f_855_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 12, 6);
lean_closure_set(v___f_855_, 0, v_type_852_);
lean_closure_set(v___f_855_, 1, v___x_660_);
lean_closure_set(v___f_855_, 2, v___x_665_);
lean_closure_set(v___f_855_, 3, v___x_664_);
lean_closure_set(v___f_855_, 4, v___x_853_);
lean_closure_set(v___f_855_, 5, v___x_854_);
if (v_symm_672_ == 0)
{
lean_dec(v_fst_850_);
v___y_857_ = v_snd_851_;
goto v___jp_856_;
}
else
{
lean_dec(v_snd_851_);
v___y_857_ = v_fst_850_;
goto v___jp_856_;
}
v___jp_856_:
{
lean_object* v___x_858_; lean_object* v_a_859_; lean_object* v___x_860_; lean_object* v_a_861_; uint8_t v___x_862_; 
v___x_858_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_857_, v___y_676_);
v_a_859_ = lean_ctor_get(v___x_858_, 0);
lean_inc(v_a_859_);
lean_dec_ref(v___x_858_);
lean_inc(v___x_657_);
lean_inc_ref(v_type_852_);
v___x_860_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_type_852_, v___x_657_, v___y_676_);
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref(v___x_860_);
v___x_862_ = lean_unbox(v_a_861_);
if (v___x_862_ == 0)
{
lean_object* v___x_863_; lean_object* v___x_864_; uint8_t v___x_865_; lean_object* v___x_866_; 
lean_dec_ref(v___f_855_);
v___x_863_ = lean_mk_empty_array_with_capacity(v___x_674_);
lean_inc_ref(v___x_664_);
v___x_864_ = lean_array_push(v___x_863_, v___x_664_);
v___x_865_ = 1;
lean_inc_ref(v_type_852_);
v___x_866_ = l_Lean_Meta_mkLambdaFVars(v___x_864_, v_type_852_, v___x_673_, v___x_668_, v___x_673_, v___x_668_, v___x_865_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec_ref(v___x_864_);
if (lean_obj_tag(v___x_866_) == 0)
{
lean_object* v_a_867_; lean_object* v___x_868_; uint8_t v___x_869_; 
v_a_867_ = lean_ctor_get(v___x_866_, 0);
lean_inc(v_a_867_);
lean_dec_ref_known(v___x_866_, 1);
lean_inc_ref(v___x_664_);
v___x_868_ = l_Lean_Expr_replaceFVar(v_type_852_, v___x_664_, v_a_859_);
lean_dec_ref(v_type_852_);
v___x_869_ = lean_unbox(v_a_861_);
lean_dec(v_a_861_);
v___y_821_ = v___x_869_;
v___y_822_ = v_a_859_;
v_motive_823_ = v_a_867_;
v_newType_824_ = v___x_868_;
v___y_825_ = v___y_675_;
v___y_826_ = v___y_676_;
v___y_827_ = v___y_677_;
v___y_828_ = v___y_678_;
goto v___jp_820_;
}
else
{
lean_object* v_a_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_877_; 
lean_dec(v_a_861_);
lean_dec(v_a_859_);
lean_dec_ref(v_type_852_);
lean_dec(v_a_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_870_ = lean_ctor_get(v___x_866_, 0);
v_isSharedCheck_877_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_877_ == 0)
{
v___x_872_ = v___x_866_;
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_a_870_);
lean_dec(v___x_866_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_877_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v___x_875_; 
if (v_isShared_873_ == 0)
{
v___x_875_ = v___x_872_;
goto v_reusejp_874_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_a_870_);
v___x_875_ = v_reuseFailAlloc_876_;
goto v_reusejp_874_;
}
v_reusejp_874_:
{
return v___x_875_;
}
}
}
}
else
{
lean_object* v___x_878_; lean_object* v___x_879_; 
lean_inc_ref(v___x_664_);
v___x_878_ = l_Lean_Expr_replaceFVar(v_type_852_, v___x_664_, v_a_859_);
lean_inc(v_a_859_);
v___x_879_ = l_Lean_Meta_mkEqRefl(v_a_859_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_879_) == 0)
{
lean_object* v_a_880_; lean_object* v___x_881_; 
v_a_880_ = lean_ctor_get(v___x_879_, 0);
lean_inc(v_a_880_);
lean_dec_ref_known(v___x_879_, 1);
lean_inc_ref(v___x_660_);
v___x_881_ = l_Lean_Expr_replaceFVar(v___x_878_, v___x_660_, v_a_880_);
lean_dec(v_a_880_);
lean_dec_ref(v___x_878_);
if (v_symm_672_ == 0)
{
lean_object* v___x_882_; 
lean_dec_ref(v_type_852_);
lean_inc_ref(v___x_664_);
lean_inc(v_a_859_);
v___x_882_ = l_Lean_Meta_mkEq(v_a_859_, v___x_664_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_882_) == 0)
{
lean_object* v_a_883_; lean_object* v___x_884_; lean_object* v___x_885_; 
v_a_883_ = lean_ctor_get(v___x_882_, 0);
lean_inc(v_a_883_);
lean_dec_ref_known(v___x_882_, 1);
v___x_884_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__9));
v___x_885_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v___x_884_, v_a_883_, v___f_855_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; uint8_t v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = lean_unbox(v_a_861_);
lean_dec(v_a_861_);
v___y_821_ = v___x_887_;
v___y_822_ = v_a_859_;
v_motive_823_ = v_a_886_;
v_newType_824_ = v___x_881_;
v___y_825_ = v___y_675_;
v___y_826_ = v___y_676_;
v___y_827_ = v___y_677_;
v___y_828_ = v___y_678_;
goto v___jp_820_;
}
else
{
lean_object* v_a_888_; lean_object* v___x_890_; uint8_t v_isShared_891_; uint8_t v_isSharedCheck_895_; 
lean_dec_ref(v___x_881_);
lean_dec(v_a_861_);
lean_dec(v_a_859_);
lean_dec(v_a_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_888_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_895_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_895_ == 0)
{
v___x_890_ = v___x_885_;
v_isShared_891_ = v_isSharedCheck_895_;
goto v_resetjp_889_;
}
else
{
lean_inc(v_a_888_);
lean_dec(v___x_885_);
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
lean_object* v_a_896_; lean_object* v___x_898_; uint8_t v_isShared_899_; uint8_t v_isSharedCheck_903_; 
lean_dec_ref(v___x_881_);
lean_dec(v_a_861_);
lean_dec(v_a_859_);
lean_dec_ref(v___f_855_);
lean_dec(v_a_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_896_ = lean_ctor_get(v___x_882_, 0);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_882_);
if (v_isSharedCheck_903_ == 0)
{
v___x_898_ = v___x_882_;
v_isShared_899_ = v_isSharedCheck_903_;
goto v_resetjp_897_;
}
else
{
lean_inc(v_a_896_);
lean_dec(v___x_882_);
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
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; uint8_t v___x_907_; lean_object* v___x_908_; 
lean_dec_ref(v___f_855_);
v___x_904_ = lean_mk_empty_array_with_capacity(v___x_665_);
lean_inc_ref(v___x_664_);
v___x_905_ = lean_array_push(v___x_904_, v___x_664_);
lean_inc_ref(v___x_660_);
v___x_906_ = lean_array_push(v___x_905_, v___x_660_);
v___x_907_ = 1;
v___x_908_ = l_Lean_Meta_mkLambdaFVars(v___x_906_, v_type_852_, v___x_673_, v___x_668_, v___x_673_, v___x_668_, v___x_907_, v___y_675_, v___y_676_, v___y_677_, v___y_678_);
lean_dec_ref(v___x_906_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; uint8_t v___x_910_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
v___x_910_ = lean_unbox(v_a_861_);
lean_dec(v_a_861_);
v___y_821_ = v___x_910_;
v___y_822_ = v_a_859_;
v_motive_823_ = v_a_909_;
v_newType_824_ = v___x_881_;
v___y_825_ = v___y_675_;
v___y_826_ = v___y_676_;
v___y_827_ = v___y_677_;
v___y_828_ = v___y_678_;
goto v___jp_820_;
}
else
{
lean_object* v_a_911_; lean_object* v___x_913_; uint8_t v_isShared_914_; uint8_t v_isSharedCheck_918_; 
lean_dec_ref(v___x_881_);
lean_dec(v_a_861_);
lean_dec(v_a_859_);
lean_dec(v_a_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_911_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_918_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_918_ == 0)
{
v___x_913_ = v___x_908_;
v_isShared_914_ = v_isSharedCheck_918_;
goto v_resetjp_912_;
}
else
{
lean_inc(v_a_911_);
lean_dec(v___x_908_);
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
else
{
lean_object* v_a_919_; lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_926_; 
lean_dec_ref(v___x_878_);
lean_dec(v_a_861_);
lean_dec(v_a_859_);
lean_dec_ref(v___f_855_);
lean_dec_ref(v_type_852_);
lean_dec(v_a_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_919_ = lean_ctor_get(v___x_879_, 0);
v_isSharedCheck_926_ = !lean_is_exclusive(v___x_879_);
if (v_isSharedCheck_926_ == 0)
{
v___x_921_ = v___x_879_;
v_isShared_922_ = v_isSharedCheck_926_;
goto v_resetjp_920_;
}
else
{
lean_inc(v_a_919_);
lean_dec(v___x_879_);
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
}
}
else
{
lean_object* v_a_927_; lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_934_; 
lean_dec(v_a_840_);
lean_dec(v_a_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_927_ = lean_ctor_get(v___x_844_, 0);
v_isSharedCheck_934_ = !lean_is_exclusive(v___x_844_);
if (v_isSharedCheck_934_ == 0)
{
v___x_929_ = v___x_844_;
v_isShared_930_ = v_isSharedCheck_934_;
goto v_resetjp_928_;
}
else
{
lean_inc(v_a_927_);
lean_dec(v___x_844_);
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
else
{
lean_object* v_a_935_; lean_object* v___x_937_; uint8_t v_isShared_938_; uint8_t v_isSharedCheck_942_; 
lean_dec(v_a_840_);
lean_dec(v_a_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_935_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_942_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_942_ == 0)
{
v___x_937_ = v___x_841_;
v_isShared_938_ = v_isSharedCheck_942_;
goto v_resetjp_936_;
}
else
{
lean_inc(v_a_935_);
lean_dec(v___x_841_);
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
lean_dec(v_a_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_943_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_950_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_950_ == 0)
{
v___x_945_ = v___x_839_;
v_isShared_946_ = v_isSharedCheck_950_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_a_943_);
lean_dec(v___x_839_);
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
v___jp_680_:
{
lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_684_ = l_Lean_Meta_FVarSubst_insert(v___y_682_, v_fvarId_658_, v___y_683_);
v___x_685_ = l_Lean_Meta_FVarSubst_insert(v___x_684_, v_hFVarId_659_, v___x_660_);
v___x_686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_686_, 0, v___x_685_);
lean_ctor_set(v___x_686_, 1, v___y_681_);
v___x_687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_687_, 0, v___x_686_);
return v___x_687_;
}
v___jp_688_:
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = lean_array_get_size(v___y_689_);
v___x_693_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_661_, v___y_689_, v___x_692_, v___x_692_, v_fvarSubst_662_);
lean_dec_ref(v___y_689_);
if (v_clearH_663_ == 0)
{
lean_object* v_a_694_; 
lean_dec_ref(v___y_691_);
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref(v___x_693_);
v___y_681_ = v___y_690_;
v___y_682_ = v_a_694_;
v___y_683_ = v___x_664_;
goto v___jp_680_;
}
else
{
lean_object* v_a_695_; 
lean_dec_ref(v___x_664_);
v_a_695_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_695_);
lean_dec_ref(v___x_693_);
v___y_681_ = v___y_690_;
v___y_682_ = v_a_695_;
v___y_683_ = v___y_691_;
goto v___jp_680_;
}
}
v___jp_696_:
{
lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_703_ = lean_array_get_size(v_fst_661_);
v___x_704_ = lean_nat_sub(v___x_703_, v___x_665_);
lean_dec(v___x_665_);
lean_inc(v___x_704_);
v___x_705_ = l_Lean_Meta_introNCore(v_mvarId_698_, v___x_704_, v___x_666_, v_skip_667_, v___x_668_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v_a_706_; lean_object* v_options_707_; uint8_t v_hasTrace_708_; 
v_a_706_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_a_706_);
lean_dec_ref_known(v___x_705_, 1);
v_options_707_ = lean_ctor_get(v___y_701_, 2);
v_hasTrace_708_ = lean_ctor_get_uint8(v_options_707_, sizeof(void*)*1);
if (v_hasTrace_708_ == 0)
{
lean_object* v_fst_709_; lean_object* v_snd_710_; 
lean_dec(v___x_704_);
lean_dec(v___x_669_);
v_fst_709_ = lean_ctor_get(v_a_706_, 0);
lean_inc(v_fst_709_);
v_snd_710_ = lean_ctor_get(v_a_706_, 1);
lean_inc(v_snd_710_);
lean_dec(v_a_706_);
v___y_689_ = v_fst_709_;
v___y_690_ = v_snd_710_;
v___y_691_ = v___y_697_;
goto v___jp_688_;
}
else
{
lean_object* v_fst_711_; lean_object* v_snd_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_740_; 
v_fst_711_ = lean_ctor_get(v_a_706_, 0);
v_snd_712_ = lean_ctor_get(v_a_706_, 1);
v_isSharedCheck_740_ = !lean_is_exclusive(v_a_706_);
if (v_isSharedCheck_740_ == 0)
{
v___x_714_ = v_a_706_;
v_isShared_715_ = v_isSharedCheck_740_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_snd_712_);
lean_inc(v_fst_711_);
lean_dec(v_a_706_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_740_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v_inheritedTraceOptions_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_inheritedTraceOptions_716_ = lean_ctor_get(v___y_701_, 13);
v___x_717_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
lean_inc(v___x_669_);
v___x_718_ = l_Lean_Name_append(v___x_717_, v___x_669_);
v___x_719_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_716_, v_options_707_, v___x_718_);
lean_dec(v___x_718_);
if (v___x_719_ == 0)
{
lean_del_object(v___x_714_);
lean_dec(v___x_704_);
lean_dec(v___x_669_);
v___y_689_ = v_fst_711_;
v___y_690_ = v_snd_712_;
v___y_691_ = v___y_697_;
goto v___jp_688_;
}
else
{
lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_725_; 
v___x_720_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__1, &l_Lean_Meta_substCore___lam__2___closed__1_once, _init_l_Lean_Meta_substCore___lam__2___closed__1);
v___x_721_ = l_Nat_reprFast(v___x_704_);
v___x_722_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_722_, 0, v___x_721_);
v___x_723_ = l_Lean_MessageData_ofFormat(v___x_722_);
if (v_isShared_715_ == 0)
{
lean_ctor_set_tag(v___x_714_, 7);
lean_ctor_set(v___x_714_, 1, v___x_723_);
lean_ctor_set(v___x_714_, 0, v___x_720_);
v___x_725_ = v___x_714_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_739_; 
v_reuseFailAlloc_739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_720_);
lean_ctor_set(v_reuseFailAlloc_739_, 1, v___x_723_);
v___x_725_ = v_reuseFailAlloc_739_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_726_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__3, &l_Lean_Meta_substCore___lam__2___closed__3_once, _init_l_Lean_Meta_substCore___lam__2___closed__3);
v___x_727_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_725_);
lean_ctor_set(v___x_727_, 1, v___x_726_);
lean_inc(v_snd_712_);
v___x_728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_728_, 0, v_snd_712_);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
v___x_730_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_669_, v___x_729_, v___y_699_, v___y_700_, v___y_701_, v___y_702_);
if (lean_obj_tag(v___x_730_) == 0)
{
lean_dec_ref_known(v___x_730_, 1);
v___y_689_ = v_fst_711_;
v___y_690_ = v_snd_712_;
v___y_691_ = v___y_697_;
goto v___jp_688_;
}
else
{
lean_object* v_a_731_; lean_object* v___x_733_; uint8_t v_isShared_734_; uint8_t v_isSharedCheck_738_; 
lean_dec(v_snd_712_);
lean_dec(v_fst_711_);
lean_dec_ref(v___y_697_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
v_a_731_ = lean_ctor_get(v___x_730_, 0);
v_isSharedCheck_738_ = !lean_is_exclusive(v___x_730_);
if (v_isSharedCheck_738_ == 0)
{
v___x_733_ = v___x_730_;
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
else
{
lean_inc(v_a_731_);
lean_dec(v___x_730_);
v___x_733_ = lean_box(0);
v_isShared_734_ = v_isSharedCheck_738_;
goto v_resetjp_732_;
}
v_resetjp_732_:
{
lean_object* v___x_736_; 
if (v_isShared_734_ == 0)
{
v___x_736_ = v___x_733_;
goto v_reusejp_735_;
}
else
{
lean_object* v_reuseFailAlloc_737_; 
v_reuseFailAlloc_737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_737_, 0, v_a_731_);
v___x_736_ = v_reuseFailAlloc_737_;
goto v_reusejp_735_;
}
v_reusejp_735_:
{
return v___x_736_;
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
lean_object* v_a_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_748_; 
lean_dec(v___x_704_);
lean_dec_ref(v___y_697_);
lean_dec(v___x_669_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
v_a_741_ = lean_ctor_get(v___x_705_, 0);
v_isSharedCheck_748_ = !lean_is_exclusive(v___x_705_);
if (v_isSharedCheck_748_ == 0)
{
v___x_743_ = v___x_705_;
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_a_741_);
lean_dec(v___x_705_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_748_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_746_; 
if (v_isShared_744_ == 0)
{
v___x_746_ = v___x_743_;
goto v_reusejp_745_;
}
else
{
lean_object* v_reuseFailAlloc_747_; 
v_reuseFailAlloc_747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_747_, 0, v_a_741_);
v___x_746_ = v_reuseFailAlloc_747_;
goto v_reusejp_745_;
}
v_reusejp_745_:
{
return v___x_746_;
}
}
}
}
v___jp_749_:
{
lean_object* v___x_757_; lean_object* v___x_758_; 
v___x_757_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_snd_656_, v_newVal_752_, v___y_754_);
lean_dec_ref(v___x_757_);
v___x_758_ = l_Lean_Expr_mvarId_x21(v___y_750_);
lean_dec_ref(v___y_750_);
if (v_clearH_663_ == 0)
{
lean_dec(v___x_670_);
lean_dec(v___x_657_);
v___y_697_ = v___y_751_;
v_mvarId_698_ = v___x_758_;
v___y_699_ = v___y_753_;
v___y_700_ = v___y_754_;
v___y_701_ = v___y_755_;
v___y_702_ = v___y_756_;
goto v___jp_696_;
}
else
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_MVarId_clear(v___x_758_, v___x_657_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_759_) == 0)
{
lean_object* v_a_760_; lean_object* v___x_761_; 
v_a_760_ = lean_ctor_get(v___x_759_, 0);
lean_inc(v_a_760_);
lean_dec_ref_known(v___x_759_, 1);
v___x_761_ = l_Lean_MVarId_clear(v_a_760_, v___x_670_, v___y_753_, v___y_754_, v___y_755_, v___y_756_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___y_697_ = v___y_751_;
v_mvarId_698_ = v_a_762_;
v___y_699_ = v___y_753_;
v___y_700_ = v___y_754_;
v___y_701_ = v___y_755_;
v___y_702_ = v___y_756_;
goto v___jp_696_;
}
else
{
lean_object* v_a_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_770_; 
lean_dec_ref(v___y_751_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
v_a_763_ = lean_ctor_get(v___x_761_, 0);
v_isSharedCheck_770_ = !lean_is_exclusive(v___x_761_);
if (v_isSharedCheck_770_ == 0)
{
v___x_765_ = v___x_761_;
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_a_763_);
lean_dec(v___x_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_770_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_768_; 
if (v_isShared_766_ == 0)
{
v___x_768_ = v___x_765_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_a_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
}
}
else
{
lean_object* v_a_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_778_; 
lean_dec_ref(v___y_751_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
v_a_771_ = lean_ctor_get(v___x_759_, 0);
v_isSharedCheck_778_ = !lean_is_exclusive(v___x_759_);
if (v_isSharedCheck_778_ == 0)
{
v___x_773_ = v___x_759_;
v_isShared_774_ = v_isSharedCheck_778_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_a_771_);
lean_dec(v___x_759_);
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
}
v___jp_779_:
{
lean_object* v___x_789_; 
v___x_789_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_781_, v_a_671_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_789_) == 0)
{
if (v___y_780_ == 0)
{
lean_object* v_a_790_; lean_object* v___x_791_; 
v_a_790_ = lean_ctor_get(v___x_789_, 0);
lean_inc_n(v_a_790_, 2);
lean_dec_ref_known(v___x_789_, 1);
v___x_791_ = l_Lean_Meta_mkEqNDRec(v___y_782_, v_a_790_, v_major_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_791_) == 0)
{
lean_object* v_a_792_; 
v_a_792_ = lean_ctor_get(v___x_791_, 0);
lean_inc(v_a_792_);
lean_dec_ref_known(v___x_791_, 1);
v___y_750_ = v_a_790_;
v___y_751_ = v___y_783_;
v_newVal_752_ = v_a_792_;
v___y_753_ = v___y_785_;
v___y_754_ = v___y_786_;
v___y_755_ = v___y_787_;
v___y_756_ = v___y_788_;
goto v___jp_749_;
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
lean_dec(v_a_790_);
lean_dec_ref(v___y_783_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_793_ = lean_ctor_get(v___x_791_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_791_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_791_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_791_);
v___x_795_ = lean_box(0);
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
v_resetjp_794_:
{
lean_object* v___x_798_; 
if (v_isShared_796_ == 0)
{
v___x_798_ = v___x_795_;
goto v_reusejp_797_;
}
else
{
lean_object* v_reuseFailAlloc_799_; 
v_reuseFailAlloc_799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_799_, 0, v_a_793_);
v___x_798_ = v_reuseFailAlloc_799_;
goto v_reusejp_797_;
}
v_reusejp_797_:
{
return v___x_798_;
}
}
}
}
else
{
lean_object* v_a_801_; lean_object* v___x_802_; 
v_a_801_ = lean_ctor_get(v___x_789_, 0);
lean_inc_n(v_a_801_, 2);
lean_dec_ref_known(v___x_789_, 1);
v___x_802_ = l_Lean_Meta_mkEqRec(v___y_782_, v_a_801_, v_major_784_, v___y_785_, v___y_786_, v___y_787_, v___y_788_);
if (lean_obj_tag(v___x_802_) == 0)
{
lean_object* v_a_803_; 
v_a_803_ = lean_ctor_get(v___x_802_, 0);
lean_inc(v_a_803_);
lean_dec_ref_known(v___x_802_, 1);
v___y_750_ = v_a_801_;
v___y_751_ = v___y_783_;
v_newVal_752_ = v_a_803_;
v___y_753_ = v___y_785_;
v___y_754_ = v___y_786_;
v___y_755_ = v___y_787_;
v___y_756_ = v___y_788_;
goto v___jp_749_;
}
else
{
lean_object* v_a_804_; lean_object* v___x_806_; uint8_t v_isShared_807_; uint8_t v_isSharedCheck_811_; 
lean_dec(v_a_801_);
lean_dec_ref(v___y_783_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_804_ = lean_ctor_get(v___x_802_, 0);
v_isSharedCheck_811_ = !lean_is_exclusive(v___x_802_);
if (v_isSharedCheck_811_ == 0)
{
v___x_806_ = v___x_802_;
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
else
{
lean_inc(v_a_804_);
lean_dec(v___x_802_);
v___x_806_ = lean_box(0);
v_isShared_807_ = v_isSharedCheck_811_;
goto v_resetjp_805_;
}
v_resetjp_805_:
{
lean_object* v___x_809_; 
if (v_isShared_807_ == 0)
{
v___x_809_ = v___x_806_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_810_; 
v_reuseFailAlloc_810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_810_, 0, v_a_804_);
v___x_809_ = v_reuseFailAlloc_810_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
return v___x_809_;
}
}
}
}
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec_ref(v_major_784_);
lean_dec_ref(v___y_783_);
lean_dec_ref(v___y_782_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_812_ = lean_ctor_get(v___x_789_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_789_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_789_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_789_);
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
v___jp_820_:
{
if (v_symm_672_ == 0)
{
lean_object* v___x_829_; 
lean_inc_ref(v___x_660_);
v___x_829_ = l_Lean_Meta_mkEqSymm(v___x_660_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
if (lean_obj_tag(v___x_829_) == 0)
{
lean_object* v_a_830_; 
v_a_830_ = lean_ctor_get(v___x_829_, 0);
lean_inc(v_a_830_);
lean_dec_ref_known(v___x_829_, 1);
v___y_780_ = v___y_821_;
v___y_781_ = v_newType_824_;
v___y_782_ = v_motive_823_;
v___y_783_ = v___y_822_;
v_major_784_ = v_a_830_;
v___y_785_ = v___y_825_;
v___y_786_ = v___y_826_;
v___y_787_ = v___y_827_;
v___y_788_ = v___y_828_;
goto v___jp_779_;
}
else
{
lean_object* v_a_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_838_; 
lean_dec_ref(v_newType_824_);
lean_dec_ref(v_motive_823_);
lean_dec_ref(v___y_822_);
lean_dec(v_a_671_);
lean_dec(v___x_670_);
lean_dec(v___x_669_);
lean_dec(v___x_666_);
lean_dec(v___x_665_);
lean_dec_ref(v___x_664_);
lean_dec(v_fvarSubst_662_);
lean_dec_ref(v___x_660_);
lean_dec(v_hFVarId_659_);
lean_dec(v_fvarId_658_);
lean_dec(v___x_657_);
lean_dec(v_snd_656_);
v_a_831_ = lean_ctor_get(v___x_829_, 0);
v_isSharedCheck_838_ = !lean_is_exclusive(v___x_829_);
if (v_isSharedCheck_838_ == 0)
{
v___x_833_ = v___x_829_;
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_a_831_);
lean_dec(v___x_829_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_838_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_836_; 
if (v_isShared_834_ == 0)
{
v___x_836_ = v___x_833_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v_a_831_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
}
}
else
{
lean_inc_ref(v___x_660_);
v___y_780_ = v___y_821_;
v___y_781_ = v_newType_824_;
v___y_782_ = v_motive_823_;
v___y_783_ = v___y_822_;
v_major_784_ = v___x_660_;
v___y_785_ = v___y_825_;
v___y_786_ = v___y_826_;
v___y_787_ = v___y_827_;
v___y_788_ = v___y_828_;
goto v___jp_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object** _args){
lean_object* v_snd_951_ = _args[0];
lean_object* v___x_952_ = _args[1];
lean_object* v_fvarId_953_ = _args[2];
lean_object* v_hFVarId_954_ = _args[3];
lean_object* v___x_955_ = _args[4];
lean_object* v_fst_956_ = _args[5];
lean_object* v_fvarSubst_957_ = _args[6];
lean_object* v_clearH_958_ = _args[7];
lean_object* v___x_959_ = _args[8];
lean_object* v___x_960_ = _args[9];
lean_object* v___x_961_ = _args[10];
lean_object* v_skip_962_ = _args[11];
lean_object* v___x_963_ = _args[12];
lean_object* v___x_964_ = _args[13];
lean_object* v___x_965_ = _args[14];
lean_object* v_a_966_ = _args[15];
lean_object* v_symm_967_ = _args[16];
lean_object* v___x_968_ = _args[17];
lean_object* v___x_969_ = _args[18];
lean_object* v___y_970_ = _args[19];
lean_object* v___y_971_ = _args[20];
lean_object* v___y_972_ = _args[21];
lean_object* v___y_973_ = _args[22];
lean_object* v___y_974_ = _args[23];
_start:
{
uint8_t v_clearH_boxed_975_; uint8_t v_skip_boxed_976_; uint8_t v___x_27671__boxed_977_; uint8_t v_symm_boxed_978_; uint8_t v___x_27675__boxed_979_; lean_object* v_res_980_; 
v_clearH_boxed_975_ = lean_unbox(v_clearH_958_);
v_skip_boxed_976_ = lean_unbox(v_skip_962_);
v___x_27671__boxed_977_ = lean_unbox(v___x_963_);
v_symm_boxed_978_ = lean_unbox(v_symm_967_);
v___x_27675__boxed_979_ = lean_unbox(v___x_968_);
v_res_980_ = l_Lean_Meta_substCore___lam__2(v_snd_951_, v___x_952_, v_fvarId_953_, v_hFVarId_954_, v___x_955_, v_fst_956_, v_fvarSubst_957_, v_clearH_boxed_975_, v___x_959_, v___x_960_, v___x_961_, v_skip_boxed_976_, v___x_27671__boxed_977_, v___x_964_, v___x_965_, v_a_966_, v_symm_boxed_978_, v___x_27675__boxed_979_, v___x_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___x_969_);
lean_dec_ref(v_fst_956_);
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
lean_object* v_val_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1459_; 
v_val_1137_ = lean_ctor_get(v_a_1134_, 0);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_a_1134_);
if (v_isSharedCheck_1459_ == 0)
{
v___x_1139_ = v_a_1134_;
v_isShared_1140_ = v_isSharedCheck_1459_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_val_1137_);
lean_dec(v_a_1134_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1459_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_snd_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1457_; 
v_snd_1141_ = lean_ctor_get(v_val_1137_, 1);
v_isSharedCheck_1457_ = !lean_is_exclusive(v_val_1137_);
if (v_isSharedCheck_1457_ == 0)
{
lean_object* v_unused_1458_; 
v_unused_1458_ = lean_ctor_get(v_val_1137_, 0);
lean_dec(v_unused_1458_);
v___x_1143_ = v_val_1137_;
v_isShared_1144_ = v_isSharedCheck_1457_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_snd_1141_);
lean_dec(v_val_1137_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1457_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_fst_1145_; lean_object* v_snd_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1456_; 
v_fst_1145_ = lean_ctor_get(v_snd_1141_, 0);
v_snd_1146_ = lean_ctor_get(v_snd_1141_, 1);
v_isSharedCheck_1456_ = !lean_is_exclusive(v_snd_1141_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1148_ = v_snd_1141_;
v_isShared_1149_ = v_isSharedCheck_1456_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_snd_1146_);
lean_inc(v_fst_1145_);
lean_dec(v_snd_1141_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1456_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
uint8_t v___x_1150_; lean_object* v___y_1152_; lean_object* v___y_1153_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; uint8_t v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; lean_object* v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; uint8_t v_skip_1169_; lean_object* v___y_1178_; lean_object* v___y_1179_; lean_object* v___y_1180_; uint8_t v___y_1181_; lean_object* v___y_1182_; lean_object* v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; uint8_t v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; lean_object* v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1219_; lean_object* v___y_1220_; lean_object* v___y_1221_; uint8_t v___y_1222_; lean_object* v___y_1223_; lean_object* v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; uint8_t v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; lean_object* v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1269_; uint8_t v___y_1270_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; lean_object* v___y_1274_; lean_object* v___y_1275_; uint8_t v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; lean_object* v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1327_; lean_object* v___y_1328_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1383_; lean_object* v___y_1384_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1419_; lean_object* v___y_1420_; lean_object* v___y_1452_; 
v___x_1150_ = 1;
if (v_symm_1067_ == 0)
{
lean_inc(v_fst_1145_);
v___y_1452_ = v_fst_1145_;
goto v___jp_1451_;
}
else
{
lean_inc(v_snd_1146_);
v___y_1452_ = v_snd_1146_;
goto v___jp_1451_;
}
v___jp_1151_:
{
lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___f_1175_; lean_object* v___x_1176_; 
v___x_1170_ = lean_box(v_clearH_1065_);
v___x_1171_ = lean_box(v_skip_1169_);
v___x_1172_ = lean_box(v___x_1150_);
v___x_1173_ = lean_box(v_symm_1067_);
v___x_1174_ = lean_box(v___y_1157_);
v___f_1175_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__2___boxed), 24, 19);
lean_closure_set(v___f_1175_, 0, v___y_1153_);
lean_closure_set(v___f_1175_, 1, v___y_1161_);
lean_closure_set(v___f_1175_, 2, v___y_1167_);
lean_closure_set(v___f_1175_, 3, v_hFVarId_1063_);
lean_closure_set(v___f_1175_, 4, v___y_1152_);
lean_closure_set(v___f_1175_, 5, v___y_1162_);
lean_closure_set(v___f_1175_, 6, v_fvarSubst_1066_);
lean_closure_set(v___f_1175_, 7, v___x_1170_);
lean_closure_set(v___f_1175_, 8, v___y_1168_);
lean_closure_set(v___f_1175_, 9, v___y_1165_);
lean_closure_set(v___f_1175_, 10, v___y_1163_);
lean_closure_set(v___f_1175_, 11, v___x_1171_);
lean_closure_set(v___f_1175_, 12, v___x_1172_);
lean_closure_set(v___f_1175_, 13, v___y_1159_);
lean_closure_set(v___f_1175_, 14, v___y_1154_);
lean_closure_set(v___f_1175_, 15, v_a_1113_);
lean_closure_set(v___f_1175_, 16, v___x_1173_);
lean_closure_set(v___f_1175_, 17, v___x_1174_);
lean_closure_set(v___f_1175_, 18, v___y_1164_);
v___x_1176_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v___y_1166_, v___f_1175_, v___y_1156_, v___y_1160_, v___y_1158_, v___y_1155_);
lean_dec(v___y_1155_);
lean_dec_ref(v___y_1158_);
lean_dec(v___y_1160_);
lean_dec_ref(v___y_1156_);
return v___x_1176_;
}
v___jp_1177_:
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1194_ = lean_unsigned_to_nat(0u);
v___x_1195_ = lean_array_get(v___x_1064_, v___y_1185_, v___x_1194_);
lean_inc(v___x_1195_);
v___x_1196_ = l_Lean_mkFVar(v___x_1195_);
v___x_1197_ = lean_unsigned_to_nat(1u);
v___x_1198_ = lean_array_get(v___x_1064_, v___y_1185_, v___x_1197_);
lean_dec_ref(v___y_1185_);
lean_inc(v___x_1198_);
v___x_1199_ = l_Lean_mkFVar(v___x_1198_);
if (v_tryToSkip_1068_ == 0)
{
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1186_);
v___y_1152_ = v___x_1199_;
v___y_1153_ = v___y_1178_;
v___y_1154_ = v___x_1195_;
v___y_1155_ = v___y_1193_;
v___y_1156_ = v___y_1190_;
v___y_1157_ = v___y_1181_;
v___y_1158_ = v___y_1192_;
v___y_1159_ = v___y_1183_;
v___y_1160_ = v___y_1191_;
v___y_1161_ = v___x_1198_;
v___y_1162_ = v___y_1179_;
v___y_1163_ = v___y_1180_;
v___y_1164_ = v___x_1197_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1187_;
v___y_1167_ = v___y_1184_;
v___y_1168_ = v___x_1196_;
v_skip_1169_ = v___y_1188_;
goto v___jp_1151_;
}
else
{
lean_object* v___x_1200_; uint8_t v___x_1201_; 
v___x_1200_ = lean_array_get_size(v___y_1186_);
lean_dec_ref(v___y_1186_);
v___x_1201_ = lean_nat_dec_eq(v___x_1200_, v___y_1189_);
lean_dec(v___y_1189_);
if (v___x_1201_ == 0)
{
v___y_1152_ = v___x_1199_;
v___y_1153_ = v___y_1178_;
v___y_1154_ = v___x_1195_;
v___y_1155_ = v___y_1193_;
v___y_1156_ = v___y_1190_;
v___y_1157_ = v___y_1181_;
v___y_1158_ = v___y_1192_;
v___y_1159_ = v___y_1183_;
v___y_1160_ = v___y_1191_;
v___y_1161_ = v___x_1198_;
v___y_1162_ = v___y_1179_;
v___y_1163_ = v___y_1180_;
v___y_1164_ = v___x_1197_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1187_;
v___y_1167_ = v___y_1184_;
v___y_1168_ = v___x_1196_;
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
v___x_1204_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1203_, v___x_1195_, v___y_1191_);
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc(v_a_1205_);
lean_dec_ref(v___x_1204_);
v___x_1206_ = lean_unbox(v_a_1205_);
lean_dec(v_a_1205_);
if (v___x_1206_ == 0)
{
lean_object* v___x_1207_; lean_object* v_a_1208_; uint8_t v___x_1209_; 
lean_inc(v___x_1198_);
v___x_1207_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1203_, v___x_1198_, v___y_1191_);
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
lean_dec(v___y_1182_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec(v_a_1113_);
lean_dec(v_hFVarId_1063_);
v___y_1075_ = v___x_1198_;
v___y_1076_ = v___x_1195_;
v___y_1077_ = v___y_1193_;
v___y_1078_ = v___y_1190_;
v___y_1079_ = v___y_1192_;
v___y_1080_ = v___y_1187_;
v___y_1081_ = v___y_1191_;
goto v___jp_1074_;
}
else
{
v___y_1152_ = v___x_1199_;
v___y_1153_ = v___y_1178_;
v___y_1154_ = v___x_1195_;
v___y_1155_ = v___y_1193_;
v___y_1156_ = v___y_1190_;
v___y_1157_ = v___y_1181_;
v___y_1158_ = v___y_1192_;
v___y_1159_ = v___y_1183_;
v___y_1160_ = v___y_1191_;
v___y_1161_ = v___x_1198_;
v___y_1162_ = v___y_1179_;
v___y_1163_ = v___y_1180_;
v___y_1164_ = v___x_1197_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1187_;
v___y_1167_ = v___y_1184_;
v___y_1168_ = v___x_1196_;
v_skip_1169_ = v___y_1188_;
goto v___jp_1151_;
}
}
else
{
lean_dec(v_a_1203_);
v___y_1152_ = v___x_1199_;
v___y_1153_ = v___y_1178_;
v___y_1154_ = v___x_1195_;
v___y_1155_ = v___y_1193_;
v___y_1156_ = v___y_1190_;
v___y_1157_ = v___y_1181_;
v___y_1158_ = v___y_1192_;
v___y_1159_ = v___y_1183_;
v___y_1160_ = v___y_1191_;
v___y_1161_ = v___x_1198_;
v___y_1162_ = v___y_1179_;
v___y_1163_ = v___y_1180_;
v___y_1164_ = v___x_1197_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1187_;
v___y_1167_ = v___y_1184_;
v___y_1168_ = v___x_1196_;
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
lean_dec(v___y_1182_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
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
lean_object* v___x_1237_; 
lean_inc_ref(v___y_1230_);
lean_inc(v___y_1236_);
lean_inc_ref(v___y_1235_);
lean_inc(v___y_1234_);
lean_inc_ref(v___y_1233_);
v___x_1237_ = lean_apply_5(v___y_1230_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_, lean_box(0));
if (lean_obj_tag(v___x_1237_) == 0)
{
lean_object* v_a_1238_; uint8_t v___x_1239_; 
v_a_1238_ = lean_ctor_get(v___x_1237_, 0);
lean_inc(v_a_1238_);
lean_dec_ref_known(v___x_1237_, 1);
v___x_1239_ = lean_unbox(v_a_1238_);
lean_dec(v_a_1238_);
if (v___x_1239_ == 0)
{
lean_dec(v___y_1231_);
lean_del_object(v___x_1148_);
v___y_1178_ = v___y_1219_;
v___y_1179_ = v___y_1220_;
v___y_1180_ = v___y_1221_;
v___y_1181_ = v___y_1222_;
v___y_1182_ = v___y_1223_;
v___y_1183_ = v___y_1224_;
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1226_;
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1229_;
v___y_1189_ = v___y_1232_;
v___y_1190_ = v___y_1233_;
v___y_1191_ = v___y_1234_;
v___y_1192_ = v___y_1235_;
v___y_1193_ = v___y_1236_;
goto v___jp_1177_;
}
else
{
lean_object* v___x_1240_; size_t v_sz_1241_; size_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1249_; 
v___x_1240_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__11, &l_Lean_Meta_substCore___lam__3___closed__11_once, _init_l_Lean_Meta_substCore___lam__3___closed__11);
v_sz_1241_ = lean_array_size(v___y_1227_);
v___x_1242_ = ((size_t)0ULL);
lean_inc_ref(v___y_1227_);
v___x_1243_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1241_, v___x_1242_, v___y_1227_);
v___x_1244_ = lean_array_to_list(v___x_1243_);
v___x_1245_ = lean_box(0);
v___x_1246_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(v___x_1244_, v___x_1245_);
v___x_1247_ = l_Lean_MessageData_ofList(v___x_1246_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set_tag(v___x_1148_, 7);
lean_ctor_set(v___x_1148_, 1, v___x_1247_);
lean_ctor_set(v___x_1148_, 0, v___x_1240_);
v___x_1249_ = v___x_1148_;
goto v_reusejp_1248_;
}
else
{
lean_object* v_reuseFailAlloc_1259_; 
v_reuseFailAlloc_1259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1259_, 0, v___x_1240_);
lean_ctor_set(v_reuseFailAlloc_1259_, 1, v___x_1247_);
v___x_1249_ = v_reuseFailAlloc_1259_;
goto v_reusejp_1248_;
}
v_reusejp_1248_:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1231_, v___x_1249_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_dec_ref_known(v___x_1250_, 1);
v___y_1178_ = v___y_1219_;
v___y_1179_ = v___y_1220_;
v___y_1180_ = v___y_1221_;
v___y_1181_ = v___y_1222_;
v___y_1182_ = v___y_1223_;
v___y_1183_ = v___y_1224_;
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1226_;
v___y_1186_ = v___y_1227_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1229_;
v___y_1189_ = v___y_1232_;
v___y_1190_ = v___y_1233_;
v___y_1191_ = v___y_1234_;
v___y_1192_ = v___y_1235_;
v___y_1193_ = v___y_1236_;
goto v___jp_1177_;
}
else
{
lean_object* v_a_1251_; lean_object* v___x_1253_; uint8_t v_isShared_1254_; uint8_t v_isSharedCheck_1258_; 
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1258_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1258_ == 0)
{
v___x_1253_ = v___x_1250_;
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
else
{
lean_inc(v_a_1251_);
lean_dec(v___x_1250_);
v___x_1253_ = lean_box(0);
v_isShared_1254_ = v_isSharedCheck_1258_;
goto v_resetjp_1252_;
}
v_resetjp_1252_:
{
lean_object* v___x_1256_; 
if (v_isShared_1254_ == 0)
{
v___x_1256_ = v___x_1253_;
goto v_reusejp_1255_;
}
else
{
lean_object* v_reuseFailAlloc_1257_; 
v_reuseFailAlloc_1257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1257_, 0, v_a_1251_);
v___x_1256_ = v_reuseFailAlloc_1257_;
goto v_reusejp_1255_;
}
v_reusejp_1255_:
{
return v___x_1256_;
}
}
}
}
}
}
else
{
lean_object* v_a_1260_; lean_object* v___x_1262_; uint8_t v_isShared_1263_; uint8_t v_isSharedCheck_1267_; 
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec_ref(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1224_);
lean_dec(v___y_1223_);
lean_dec(v___y_1221_);
lean_dec_ref(v___y_1220_);
lean_dec(v___y_1219_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
v_a_1260_ = lean_ctor_get(v___x_1237_, 0);
v_isSharedCheck_1267_ = !lean_is_exclusive(v___x_1237_);
if (v_isSharedCheck_1267_ == 0)
{
v___x_1262_ = v___x_1237_;
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
else
{
lean_inc(v_a_1260_);
lean_dec(v___x_1237_);
v___x_1262_ = lean_box(0);
v_isShared_1263_ = v_isSharedCheck_1267_;
goto v_resetjp_1261_;
}
v_resetjp_1261_:
{
lean_object* v___x_1265_; 
if (v_isShared_1263_ == 0)
{
v___x_1265_ = v___x_1262_;
goto v_reusejp_1264_;
}
else
{
lean_object* v_reuseFailAlloc_1266_; 
v_reuseFailAlloc_1266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1266_, 0, v_a_1260_);
v___x_1265_ = v_reuseFailAlloc_1266_;
goto v_reusejp_1264_;
}
v_reusejp_1264_:
{
return v___x_1265_;
}
}
}
}
v___jp_1268_:
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
v___x_1284_ = lean_box(0);
lean_inc(v___y_1279_);
v___x_1285_ = l_Lean_Meta_introNCore(v___y_1277_, v___y_1279_, v___x_1284_, v___y_1276_, v___x_1150_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
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
lean_inc_ref(v___y_1275_);
lean_inc(v___y_1283_);
lean_inc_ref(v___y_1282_);
lean_inc(v___y_1281_);
lean_inc_ref(v___y_1280_);
v___x_1292_ = lean_apply_5(v___y_1275_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_, lean_box(0));
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
lean_inc(v_snd_1288_);
v___y_1219_ = v_snd_1288_;
v___y_1220_ = v___y_1269_;
v___y_1221_ = v___x_1284_;
v___y_1222_ = v___y_1270_;
v___y_1223_ = v___y_1271_;
v___y_1224_ = v___y_1272_;
v___y_1225_ = v___y_1273_;
v___y_1226_ = v_fst_1287_;
v___y_1227_ = v___y_1274_;
v___y_1228_ = v_snd_1288_;
v___y_1229_ = v___y_1276_;
v___y_1230_ = v___y_1275_;
v___y_1231_ = v___y_1278_;
v___y_1232_ = v___y_1279_;
v___y_1233_ = v___y_1280_;
v___y_1234_ = v___y_1281_;
v___y_1235_ = v___y_1282_;
v___y_1236_ = v___y_1283_;
goto v___jp_1218_;
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
lean_inc(v___y_1278_);
v___x_1299_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1278_, v___x_1298_, v___y_1280_, v___y_1281_, v___y_1282_, v___y_1283_);
if (lean_obj_tag(v___x_1299_) == 0)
{
lean_dec_ref_known(v___x_1299_, 1);
lean_inc(v_snd_1288_);
v___y_1219_ = v_snd_1288_;
v___y_1220_ = v___y_1269_;
v___y_1221_ = v___x_1284_;
v___y_1222_ = v___y_1270_;
v___y_1223_ = v___y_1271_;
v___y_1224_ = v___y_1272_;
v___y_1225_ = v___y_1273_;
v___y_1226_ = v_fst_1287_;
v___y_1227_ = v___y_1274_;
v___y_1228_ = v_snd_1288_;
v___y_1229_ = v___y_1276_;
v___y_1230_ = v___y_1275_;
v___y_1231_ = v___y_1278_;
v___y_1232_ = v___y_1279_;
v___y_1233_ = v___y_1280_;
v___y_1234_ = v___y_1281_;
v___y_1235_ = v___y_1282_;
v___y_1236_ = v___y_1283_;
goto v___jp_1218_;
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
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1269_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
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
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1269_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
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
lean_dec(v___y_1278_);
lean_dec_ref(v___y_1274_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1269_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
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
lean_inc(v_hFVarId_1063_);
v___x_1339_ = lean_array_push(v___x_1338_, v_hFVarId_1063_);
v___x_1340_ = 0;
v___x_1341_ = l_Lean_MVarId_revert(v_mvarId_1062_, v___x_1339_, v___x_1150_, v___x_1340_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
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
lean_inc(v_fst_1343_);
v___y_1269_ = v_fst_1343_;
v___y_1270_ = v___x_1340_;
v___y_1271_ = v___x_1336_;
v___y_1272_ = v___y_1327_;
v___y_1273_ = v___y_1328_;
v___y_1274_ = v_fst_1343_;
v___y_1275_ = v___y_1330_;
v___y_1276_ = v___x_1340_;
v___y_1277_ = v_snd_1344_;
v___y_1278_ = v___y_1331_;
v___y_1279_ = v___x_1336_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___y_1333_;
v___y_1282_ = v___y_1334_;
v___y_1283_ = v___y_1335_;
goto v___jp_1268_;
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
v___x_1355_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1331_, v___x_1354_, v___y_1332_, v___y_1333_, v___y_1334_, v___y_1335_);
if (lean_obj_tag(v___x_1355_) == 0)
{
lean_dec_ref_known(v___x_1355_, 1);
lean_inc(v_fst_1343_);
v___y_1269_ = v_fst_1343_;
v___y_1270_ = v___x_1340_;
v___y_1271_ = v___x_1336_;
v___y_1272_ = v___y_1327_;
v___y_1273_ = v___y_1328_;
v___y_1274_ = v_fst_1343_;
v___y_1275_ = v___y_1330_;
v___y_1276_ = v___x_1340_;
v___y_1277_ = v_snd_1344_;
v___y_1278_ = v___y_1331_;
v___y_1279_ = v___x_1336_;
v___y_1280_ = v___y_1332_;
v___y_1281_ = v___y_1333_;
v___y_1282_ = v___y_1334_;
v___y_1283_ = v___y_1335_;
goto v___jp_1268_;
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
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
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
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
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
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
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
lean_object* v___x_1394_; lean_object* v_a_1395_; uint8_t v___x_1396_; 
lean_inc(v___y_1385_);
lean_inc_ref(v___y_1389_);
v___x_1394_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v___y_1389_, v___y_1385_, v___y_1391_);
v_a_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_a_1395_);
lean_dec_ref(v___x_1394_);
v___x_1396_ = lean_unbox(v_a_1395_);
lean_dec(v_a_1395_);
if (v___x_1396_ == 0)
{
lean_dec_ref(v___y_1389_);
lean_dec_ref(v___y_1386_);
lean_del_object(v___x_1143_);
lean_del_object(v___x_1139_);
v___y_1327_ = v___y_1383_;
v___y_1328_ = v___y_1384_;
v___y_1329_ = v___y_1385_;
v___y_1330_ = v___y_1387_;
v___y_1331_ = v___y_1388_;
v___y_1332_ = v___y_1390_;
v___y_1333_ = v___y_1391_;
v___y_1334_ = v___y_1392_;
v___y_1335_ = v___y_1393_;
goto v___jp_1326_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; 
v___x_1397_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_1398_ = l_Lean_MessageData_ofExpr(v___y_1386_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set_tag(v___x_1143_, 7);
lean_ctor_set(v___x_1143_, 1, v___x_1398_);
lean_ctor_set(v___x_1143_, 0, v___x_1397_);
v___x_1400_ = v___x_1143_;
goto v_reusejp_1399_;
}
else
{
lean_object* v_reuseFailAlloc_1417_; 
v_reuseFailAlloc_1417_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1417_, 0, v___x_1397_);
lean_ctor_set(v_reuseFailAlloc_1417_, 1, v___x_1398_);
v___x_1400_ = v_reuseFailAlloc_1417_;
goto v_reusejp_1399_;
}
v_reusejp_1399_:
{
lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1406_; 
v___x_1401_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__19, &l_Lean_Meta_substCore___lam__3___closed__19_once, _init_l_Lean_Meta_substCore___lam__3___closed__19);
v___x_1402_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1400_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = l_Lean_indentExpr(v___y_1389_);
v___x_1404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1402_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 0, v___x_1404_);
v___x_1406_ = v___x_1139_;
goto v_reusejp_1405_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v___x_1404_);
v___x_1406_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1405_;
}
v_reusejp_1405_:
{
lean_object* v___x_1407_; 
lean_inc(v_mvarId_1062_);
v___x_1407_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1114_, v_mvarId_1062_, v___x_1406_, v___y_1390_, v___y_1391_, v___y_1392_, v___y_1393_);
if (lean_obj_tag(v___x_1407_) == 0)
{
lean_dec_ref_known(v___x_1407_, 1);
v___y_1327_ = v___y_1383_;
v___y_1328_ = v___y_1384_;
v___y_1329_ = v___y_1385_;
v___y_1330_ = v___y_1387_;
v___y_1331_ = v___y_1388_;
v___y_1332_ = v___y_1390_;
v___y_1333_ = v___y_1391_;
v___y_1334_ = v___y_1392_;
v___y_1335_ = v___y_1393_;
goto v___jp_1326_;
}
else
{
lean_object* v_a_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1415_; 
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec_ref(v___y_1390_);
lean_dec(v___y_1388_);
lean_dec(v___y_1385_);
lean_dec(v___y_1384_);
lean_dec(v___y_1383_);
lean_del_object(v___x_1148_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
v_a_1408_ = lean_ctor_get(v___x_1407_, 0);
v_isSharedCheck_1415_ = !lean_is_exclusive(v___x_1407_);
if (v_isSharedCheck_1415_ == 0)
{
v___x_1410_ = v___x_1407_;
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_a_1408_);
lean_dec(v___x_1407_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1415_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v___x_1413_; 
if (v_isShared_1411_ == 0)
{
v___x_1413_ = v___x_1410_;
goto v_reusejp_1412_;
}
else
{
lean_object* v_reuseFailAlloc_1414_; 
v_reuseFailAlloc_1414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1414_, 0, v_a_1408_);
v___x_1413_ = v_reuseFailAlloc_1414_;
goto v_reusejp_1412_;
}
v_reusejp_1412_:
{
return v___x_1413_;
}
}
}
}
}
}
}
v___jp_1418_:
{
lean_object* v___x_1421_; 
v___x_1421_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1420_, v___y_1070_);
if (lean_obj_tag(v___y_1419_) == 1)
{
lean_object* v_a_1422_; lean_object* v_fvarId_1423_; lean_object* v___x_1424_; lean_object* v___f_1425_; lean_object* v___x_1426_; lean_object* v_a_1427_; uint8_t v___x_1428_; 
lean_dec_ref(v___x_1118_);
v_a_1422_ = lean_ctor_get(v___x_1421_, 0);
lean_inc(v_a_1422_);
lean_dec_ref(v___x_1421_);
v_fvarId_1423_ = lean_ctor_get(v___y_1419_, 0);
lean_inc(v_fvarId_1423_);
v___x_1424_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___f_1425_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__23));
v___x_1426_ = l_Lean_Meta_substCore___lam__0(v___x_1424_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
v_a_1427_ = lean_ctor_get(v___x_1426_, 0);
lean_inc(v_a_1427_);
lean_dec_ref(v___x_1426_);
v___x_1428_ = lean_unbox(v_a_1427_);
lean_dec(v_a_1427_);
if (v___x_1428_ == 0)
{
lean_inc(v_fvarId_1423_);
v___y_1383_ = v___x_1424_;
v___y_1384_ = v_fvarId_1423_;
v___y_1385_ = v_fvarId_1423_;
v___y_1386_ = v___y_1419_;
v___y_1387_ = v___f_1425_;
v___y_1388_ = v___x_1424_;
v___y_1389_ = v_a_1422_;
v___y_1390_ = v___y_1069_;
v___y_1391_ = v___y_1070_;
v___y_1392_ = v___y_1071_;
v___y_1393_ = v___y_1072_;
goto v___jp_1382_;
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1429_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__25, &l_Lean_Meta_substCore___lam__3___closed__25_once, _init_l_Lean_Meta_substCore___lam__3___closed__25);
lean_inc_ref(v___y_1419_);
v___x_1430_ = l_Lean_MessageData_ofExpr(v___y_1419_);
v___x_1431_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1431_, 0, v___x_1429_);
lean_ctor_set(v___x_1431_, 1, v___x_1430_);
v___x_1432_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__27, &l_Lean_Meta_substCore___lam__3___closed__27_once, _init_l_Lean_Meta_substCore___lam__3___closed__27);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
lean_inc(v_fvarId_1423_);
v___x_1434_ = l_Lean_MessageData_ofName(v_fvarId_1423_);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
v___x_1436_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__29, &l_Lean_Meta_substCore___lam__3___closed__29_once, _init_l_Lean_Meta_substCore___lam__3___closed__29);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
lean_inc(v_a_1422_);
v___x_1438_ = l_Lean_MessageData_ofExpr(v_a_1422_);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
v___x_1440_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_1424_, v___x_1439_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_dec_ref_known(v___x_1440_, 1);
lean_inc(v_fvarId_1423_);
v___y_1383_ = v___x_1424_;
v___y_1384_ = v_fvarId_1423_;
v___y_1385_ = v_fvarId_1423_;
v___y_1386_ = v___y_1419_;
v___y_1387_ = v___f_1425_;
v___y_1388_ = v___x_1424_;
v___y_1389_ = v_a_1422_;
v___y_1390_ = v___y_1069_;
v___y_1391_ = v___y_1070_;
v___y_1392_ = v___y_1071_;
v___y_1393_ = v___y_1072_;
goto v___jp_1382_;
}
else
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
lean_dec(v_fvarId_1423_);
lean_dec_ref_known(v___y_1419_, 1);
lean_dec(v_a_1422_);
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
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1421_);
lean_del_object(v___x_1148_);
lean_del_object(v___x_1143_);
lean_del_object(v___x_1139_);
lean_dec(v_a_1113_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
if (v_symm_1067_ == 0)
{
lean_object* v___x_1449_; 
v___x_1449_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__30));
v___y_1120_ = v___y_1419_;
v___y_1121_ = v___x_1449_;
goto v___jp_1119_;
}
else
{
lean_object* v___x_1450_; 
v___x_1450_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__31));
v___y_1120_ = v___y_1419_;
v___y_1121_ = v___x_1450_;
goto v___jp_1119_;
}
}
}
v___jp_1451_:
{
lean_object* v___x_1453_; 
v___x_1453_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1452_, v___y_1070_);
if (v_symm_1067_ == 0)
{
lean_object* v_a_1454_; 
lean_dec(v_fst_1145_);
v_a_1454_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1454_);
lean_dec_ref(v___x_1453_);
v___y_1419_ = v_a_1454_;
v___y_1420_ = v_snd_1146_;
goto v___jp_1418_;
}
else
{
lean_object* v_a_1455_; 
lean_dec(v_snd_1146_);
v_a_1455_ = lean_ctor_get(v___x_1453_, 0);
lean_inc(v_a_1455_);
lean_dec_ref(v___x_1453_);
v___y_1419_ = v_a_1455_;
v___y_1420_ = v_fst_1145_;
goto v___jp_1418_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1460_; lean_object* v___x_1462_; uint8_t v_isShared_1463_; uint8_t v_isSharedCheck_1467_; 
lean_dec_ref(v___x_1118_);
lean_dec(v_a_1113_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
v_a_1460_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1467_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1467_ == 0)
{
v___x_1462_ = v___x_1133_;
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
else
{
lean_inc(v_a_1460_);
lean_dec(v___x_1133_);
v___x_1462_ = lean_box(0);
v_isShared_1463_ = v_isSharedCheck_1467_;
goto v_resetjp_1461_;
}
v_resetjp_1461_:
{
lean_object* v___x_1465_; 
if (v_isShared_1463_ == 0)
{
v___x_1465_ = v___x_1462_;
goto v_reusejp_1464_;
}
else
{
lean_object* v_reuseFailAlloc_1466_; 
v_reuseFailAlloc_1466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1466_, 0, v_a_1460_);
v___x_1465_ = v_reuseFailAlloc_1466_;
goto v_reusejp_1464_;
}
v_reusejp_1464_:
{
return v___x_1465_;
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
lean_object* v_a_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1475_; 
lean_dec(v_a_1113_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
v_a_1468_ = lean_ctor_get(v___x_1116_, 0);
v_isSharedCheck_1475_ = !lean_is_exclusive(v___x_1116_);
if (v_isSharedCheck_1475_ == 0)
{
v___x_1470_ = v___x_1116_;
v_isShared_1471_ = v_isSharedCheck_1475_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_a_1468_);
lean_dec(v___x_1116_);
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
}
else
{
lean_object* v_a_1476_; lean_object* v___x_1478_; uint8_t v_isShared_1479_; uint8_t v_isSharedCheck_1483_; 
lean_dec(v_a_1113_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
v_a_1476_ = lean_ctor_get(v___x_1115_, 0);
v_isSharedCheck_1483_ = !lean_is_exclusive(v___x_1115_);
if (v_isSharedCheck_1483_ == 0)
{
v___x_1478_ = v___x_1115_;
v_isShared_1479_ = v_isSharedCheck_1483_;
goto v_resetjp_1477_;
}
else
{
lean_inc(v_a_1476_);
lean_dec(v___x_1115_);
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
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v_fvarSubst_1066_);
lean_dec(v_hFVarId_1063_);
lean_dec(v_mvarId_1062_);
v_a_1484_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1491_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1491_ == 0)
{
v___x_1486_ = v___x_1112_;
v_isShared_1487_ = v_isSharedCheck_1491_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1112_);
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
v___jp_1074_:
{
if (v_clearH_1065_ == 0)
{
lean_object* v___x_1082_; lean_object* v___x_1083_; 
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec(v___y_1075_);
v___x_1082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1082_, 0, v_fvarSubst_1066_);
lean_ctor_set(v___x_1082_, 1, v___y_1080_);
v___x_1083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1083_, 0, v___x_1082_);
return v___x_1083_;
}
else
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_MVarId_clear(v___y_1080_, v___y_1075_, v___y_1078_, v___y_1081_, v___y_1079_, v___y_1077_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___x_1086_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
v___x_1086_ = l_Lean_MVarId_clear(v_a_1085_, v___y_1076_, v___y_1078_, v___y_1081_, v___y_1079_, v___y_1077_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1081_);
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
lean_dec(v___y_1081_);
lean_dec_ref(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec(v___y_1076_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3___boxed(lean_object* v_mvarId_1492_, lean_object* v_hFVarId_1493_, lean_object* v___x_1494_, lean_object* v_clearH_1495_, lean_object* v_fvarSubst_1496_, lean_object* v_symm_1497_, lean_object* v_tryToSkip_1498_, lean_object* v___y_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
uint8_t v_clearH_boxed_1504_; uint8_t v_symm_boxed_1505_; uint8_t v_tryToSkip_boxed_1506_; lean_object* v_res_1507_; 
v_clearH_boxed_1504_ = lean_unbox(v_clearH_1495_);
v_symm_boxed_1505_ = lean_unbox(v_symm_1497_);
v_tryToSkip_boxed_1506_ = lean_unbox(v_tryToSkip_1498_);
v_res_1507_ = l_Lean_Meta_substCore___lam__3(v_mvarId_1492_, v_hFVarId_1493_, v___x_1494_, v_clearH_boxed_1504_, v_fvarSubst_1496_, v_symm_boxed_1505_, v_tryToSkip_boxed_1506_, v___y_1499_, v___y_1500_, v___y_1501_, v___y_1502_);
lean_dec(v___x_1494_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object* v_mvarId_1508_, lean_object* v_hFVarId_1509_, uint8_t v_symm_1510_, lean_object* v_fvarSubst_1511_, uint8_t v_clearH_1512_, uint8_t v_tryToSkip_1513_, lean_object* v_a_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___f_1523_; lean_object* v___x_1524_; 
v___x_1519_ = lean_box(0);
v___x_1520_ = lean_box(v_clearH_1512_);
v___x_1521_ = lean_box(v_symm_1510_);
v___x_1522_ = lean_box(v_tryToSkip_1513_);
lean_inc(v_mvarId_1508_);
v___f_1523_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__3___boxed), 12, 7);
lean_closure_set(v___f_1523_, 0, v_mvarId_1508_);
lean_closure_set(v___f_1523_, 1, v_hFVarId_1509_);
lean_closure_set(v___f_1523_, 2, v___x_1519_);
lean_closure_set(v___f_1523_, 3, v___x_1520_);
lean_closure_set(v___f_1523_, 4, v_fvarSubst_1511_);
lean_closure_set(v___f_1523_, 5, v___x_1521_);
lean_closure_set(v___f_1523_, 6, v___x_1522_);
v___x_1524_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1508_, v___f_1523_, v_a_1514_, v_a_1515_, v_a_1516_, v_a_1517_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* v_mvarId_1525_, lean_object* v_hFVarId_1526_, lean_object* v_symm_1527_, lean_object* v_fvarSubst_1528_, lean_object* v_clearH_1529_, lean_object* v_tryToSkip_1530_, lean_object* v_a_1531_, lean_object* v_a_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_){
_start:
{
uint8_t v_symm_boxed_1536_; uint8_t v_clearH_boxed_1537_; uint8_t v_tryToSkip_boxed_1538_; lean_object* v_res_1539_; 
v_symm_boxed_1536_ = lean_unbox(v_symm_1527_);
v_clearH_boxed_1537_ = lean_unbox(v_clearH_1529_);
v_tryToSkip_boxed_1538_ = lean_unbox(v_tryToSkip_1530_);
v_res_1539_ = l_Lean_Meta_substCore(v_mvarId_1525_, v_hFVarId_1526_, v_symm_boxed_1536_, v_fvarSubst_1528_, v_clearH_boxed_1537_, v_tryToSkip_boxed_1538_, v_a_1531_, v_a_1532_, v_a_1533_, v_a_1534_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
lean_dec(v_a_1532_);
lean_dec_ref(v_a_1531_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(lean_object* v_fst_1540_, lean_object* v_fst_1541_, lean_object* v_n_1542_, lean_object* v_i_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v___y_1546_, lean_object* v___y_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_){
_start:
{
lean_object* v___x_1551_; 
v___x_1551_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_1540_, v_fst_1541_, v_n_1542_, v_i_1543_, v_a_1545_);
return v___x_1551_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___boxed(lean_object* v_fst_1552_, lean_object* v_fst_1553_, lean_object* v_n_1554_, lean_object* v_i_1555_, lean_object* v_a_1556_, lean_object* v_a_1557_, lean_object* v___y_1558_, lean_object* v___y_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(v_fst_1552_, v_fst_1553_, v_n_1554_, v_i_1555_, v_a_1556_, v_a_1557_, v___y_1558_, v___y_1559_, v___y_1560_, v___y_1561_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v___y_1559_);
lean_dec_ref(v___y_1558_);
lean_dec(v_n_1554_);
lean_dec_ref(v_fst_1553_);
lean_dec_ref(v_fst_1552_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(lean_object* v_mvarId_1564_, lean_object* v_val_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
lean_object* v___x_1571_; 
v___x_1571_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_mvarId_1564_, v_val_1565_, v___y_1567_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___boxed(lean_object* v_mvarId_1572_, lean_object* v_val_1573_, lean_object* v___y_1574_, lean_object* v___y_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_){
_start:
{
lean_object* v_res_1579_; 
v_res_1579_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(v_mvarId_1572_, v_val_1573_, v___y_1574_, v___y_1575_, v___y_1576_, v___y_1577_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
lean_dec(v___y_1575_);
lean_dec_ref(v___y_1574_);
return v_res_1579_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(lean_object* v_00_u03b1_1580_, lean_object* v_name_1581_, uint8_t v_bi_1582_, lean_object* v_type_1583_, lean_object* v_k_1584_, uint8_t v_kind_1585_, lean_object* v___y_1586_, lean_object* v___y_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_){
_start:
{
lean_object* v___x_1591_; 
v___x_1591_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_1581_, v_bi_1582_, v_type_1583_, v_k_1584_, v_kind_1585_, v___y_1586_, v___y_1587_, v___y_1588_, v___y_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1592_, lean_object* v_name_1593_, lean_object* v_bi_1594_, lean_object* v_type_1595_, lean_object* v_k_1596_, lean_object* v_kind_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
uint8_t v_bi_boxed_1603_; uint8_t v_kind_boxed_1604_; lean_object* v_res_1605_; 
v_bi_boxed_1603_ = lean_unbox(v_bi_1594_);
v_kind_boxed_1604_ = lean_unbox(v_kind_1597_);
v_res_1605_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(v_00_u03b1_1592_, v_name_1593_, v_bi_boxed_1603_, v_type_1595_, v_k_1596_, v_kind_boxed_1604_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(lean_object* v_00_u03b1_1606_, lean_object* v_name_1607_, lean_object* v_type_1608_, lean_object* v_k_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; 
v___x_1615_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v_name_1607_, v_type_1608_, v_k_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___boxed(lean_object* v_00_u03b1_1616_, lean_object* v_name_1617_, lean_object* v_type_1618_, lean_object* v_k_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(v_00_u03b1_1616_, v_name_1617_, v_type_1618_, v_k_1619_, v___y_1620_, v___y_1621_, v___y_1622_, v___y_1623_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
lean_dec(v___y_1621_);
lean_dec_ref(v___y_1620_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6(lean_object* v_00_u03b2_1626_, lean_object* v_x_1627_, lean_object* v_x_1628_, lean_object* v_x_1629_){
_start:
{
lean_object* v___x_1630_; 
v___x_1630_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_x_1627_, v_x_1628_, v_x_1629_);
return v___x_1630_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1631_, lean_object* v_x_1632_, size_t v_x_1633_, size_t v_x_1634_, lean_object* v_x_1635_, lean_object* v_x_1636_){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_1632_, v_x_1633_, v_x_1634_, v_x_1635_, v_x_1636_);
return v___x_1637_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1638_, lean_object* v_x_1639_, lean_object* v_x_1640_, lean_object* v_x_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_){
_start:
{
size_t v_x_29471__boxed_1644_; size_t v_x_29472__boxed_1645_; lean_object* v_res_1646_; 
v_x_29471__boxed_1644_ = lean_unbox_usize(v_x_1640_);
lean_dec(v_x_1640_);
v_x_29472__boxed_1645_ = lean_unbox_usize(v_x_1641_);
lean_dec(v_x_1641_);
v_res_1646_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(v_00_u03b2_1638_, v_x_1639_, v_x_29471__boxed_1644_, v_x_29472__boxed_1645_, v_x_1642_, v_x_1643_);
return v_res_1646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13(lean_object* v_00_u03b2_1647_, lean_object* v_n_1648_, lean_object* v_k_1649_, lean_object* v_v_1650_){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v_n_1648_, v_k_1649_, v_v_1650_);
return v___x_1651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1652_, size_t v_depth_1653_, lean_object* v_keys_1654_, lean_object* v_vals_1655_, lean_object* v_heq_1656_, lean_object* v_i_1657_, lean_object* v_entries_1658_){
_start:
{
lean_object* v___x_1659_; 
v___x_1659_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_1653_, v_keys_1654_, v_vals_1655_, v_i_1657_, v_entries_1658_);
return v___x_1659_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1660_, lean_object* v_depth_1661_, lean_object* v_keys_1662_, lean_object* v_vals_1663_, lean_object* v_heq_1664_, lean_object* v_i_1665_, lean_object* v_entries_1666_){
_start:
{
size_t v_depth_boxed_1667_; lean_object* v_res_1668_; 
v_depth_boxed_1667_ = lean_unbox_usize(v_depth_1661_);
lean_dec(v_depth_1661_);
v_res_1668_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(v_00_u03b2_1660_, v_depth_boxed_1667_, v_keys_1662_, v_vals_1663_, v_heq_1664_, v_i_1665_, v_entries_1666_);
lean_dec_ref(v_vals_1663_);
lean_dec_ref(v_keys_1662_);
return v_res_1668_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_1669_, lean_object* v_x_1670_, lean_object* v_x_1671_, lean_object* v_x_1672_, lean_object* v_x_1673_){
_start:
{
lean_object* v___x_1674_; 
v___x_1674_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(v_x_1670_, v_x_1671_, v_x_1672_, v_x_1673_);
return v___x_1674_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* v_fvarId_1678_, lean_object* v_mvarId_1679_, uint8_t v_tryToClear_1680_, lean_object* v___y_1681_, lean_object* v___y_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_){
_start:
{
lean_object* v___x_1686_; 
lean_inc(v_fvarId_1678_);
v___x_1686_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1678_, v___y_1681_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1686_) == 0)
{
lean_object* v_a_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_a_1687_ = lean_ctor_get(v___x_1686_, 0);
lean_inc(v_a_1687_);
lean_dec_ref_known(v___x_1686_, 1);
v___x_1688_ = l_Lean_LocalDecl_type(v_a_1687_);
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
lean_inc(v___y_1682_);
lean_inc_ref(v___y_1681_);
v___x_1689_ = lean_whnf(v___x_1688_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1689_) == 0)
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1774_; 
v_a_1690_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1774_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1774_ == 0)
{
v___x_1692_ = v___x_1689_;
v_isShared_1693_ = v_isSharedCheck_1774_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1689_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1774_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1694_; lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1694_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_1695_ = lean_unsigned_to_nat(4u);
v___x_1696_ = l_Lean_Expr_isAppOfArity(v_a_1690_, v___x_1694_, v___x_1695_);
if (v___x_1696_ == 0)
{
lean_object* v___x_1697_; lean_object* v___x_1699_; 
lean_dec(v_a_1690_);
lean_dec(v_a_1687_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
v___x_1697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1697_, 0, v_fvarId_1678_);
lean_ctor_set(v___x_1697_, 1, v_mvarId_1679_);
if (v_isShared_1693_ == 0)
{
lean_ctor_set(v___x_1692_, 0, v___x_1697_);
v___x_1699_ = v___x_1692_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
else
{
lean_object* v___x_1701_; lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; 
lean_del_object(v___x_1692_);
v___x_1701_ = l_Lean_Expr_appFn_x21(v_a_1690_);
v___x_1702_ = l_Lean_Expr_appFn_x21(v___x_1701_);
v___x_1703_ = l_Lean_Expr_appFn_x21(v___x_1702_);
v___x_1704_ = l_Lean_Expr_appArg_x21(v___x_1703_);
lean_dec_ref(v___x_1703_);
v___x_1705_ = l_Lean_Expr_appArg_x21(v___x_1701_);
lean_dec_ref(v___x_1701_);
v___x_1706_ = l_Lean_Meta_isExprDefEq(v___x_1704_, v___x_1705_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1706_) == 0)
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1765_; 
v_a_1707_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1765_ == 0)
{
v___x_1709_ = v___x_1706_;
v_isShared_1710_ = v_isSharedCheck_1765_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1706_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1765_;
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
lean_dec_ref(v___x_1702_);
lean_dec(v_a_1690_);
lean_dec(v_a_1687_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
v___x_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1712_, 0, v_fvarId_1678_);
lean_ctor_set(v___x_1712_, 1, v_mvarId_1679_);
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
lean_inc(v_fvarId_1678_);
v___x_1716_ = l_Lean_mkFVar(v_fvarId_1678_);
v___x_1717_ = l_Lean_Meta_mkEqOfHEq(v___x_1716_, v___x_1696_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1717_) == 0)
{
lean_object* v_a_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; 
v_a_1718_ = lean_ctor_get(v___x_1717_, 0);
lean_inc(v_a_1718_);
lean_dec_ref_known(v___x_1717_, 1);
v___x_1719_ = l_Lean_Expr_appArg_x21(v___x_1702_);
lean_dec_ref(v___x_1702_);
v___x_1720_ = l_Lean_Expr_appArg_x21(v_a_1690_);
lean_dec(v_a_1690_);
v___x_1721_ = l_Lean_Meta_mkEq(v___x_1719_, v___x_1720_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1721_) == 0)
{
lean_object* v_a_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; 
v_a_1722_ = lean_ctor_get(v___x_1721_, 0);
lean_inc(v_a_1722_);
lean_dec_ref_known(v___x_1721_, 1);
v___x_1723_ = l_Lean_LocalDecl_userName(v_a_1687_);
lean_dec(v_a_1687_);
v___x_1724_ = l_Lean_MVarId_assert(v_mvarId_1679_, v___x_1723_, v_a_1722_, v_a_1718_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1724_) == 0)
{
if (v_tryToClear_1680_ == 0)
{
lean_object* v_a_1725_; uint8_t v___x_1726_; lean_object* v___x_1727_; 
lean_dec(v_fvarId_1678_);
v_a_1725_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1725_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1726_ = lean_unbox(v_a_1707_);
lean_dec(v_a_1707_);
v___x_1727_ = l_Lean_Meta_intro1Core(v_a_1725_, v___x_1726_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v___x_1727_;
}
else
{
lean_object* v_a_1728_; lean_object* v___x_1729_; 
v_a_1728_ = lean_ctor_get(v___x_1724_, 0);
lean_inc(v_a_1728_);
lean_dec_ref_known(v___x_1724_, 1);
v___x_1729_ = l_Lean_MVarId_tryClear(v_a_1728_, v_fvarId_1678_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
if (lean_obj_tag(v___x_1729_) == 0)
{
lean_object* v_a_1730_; uint8_t v___x_1731_; lean_object* v___x_1732_; 
v_a_1730_ = lean_ctor_get(v___x_1729_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1729_, 1);
v___x_1731_ = lean_unbox(v_a_1707_);
lean_dec(v_a_1707_);
v___x_1732_ = l_Lean_Meta_intro1Core(v_a_1730_, v___x_1731_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
return v___x_1732_;
}
else
{
lean_object* v_a_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1740_; 
lean_dec(v_a_1707_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
v_a_1733_ = lean_ctor_get(v___x_1729_, 0);
v_isSharedCheck_1740_ = !lean_is_exclusive(v___x_1729_);
if (v_isSharedCheck_1740_ == 0)
{
v___x_1735_ = v___x_1729_;
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
else
{
lean_inc(v_a_1733_);
lean_dec(v___x_1729_);
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1740_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1738_; 
if (v_isShared_1736_ == 0)
{
v___x_1738_ = v___x_1735_;
goto v_reusejp_1737_;
}
else
{
lean_object* v_reuseFailAlloc_1739_; 
v_reuseFailAlloc_1739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1739_, 0, v_a_1733_);
v___x_1738_ = v_reuseFailAlloc_1739_;
goto v_reusejp_1737_;
}
v_reusejp_1737_:
{
return v___x_1738_;
}
}
}
}
}
else
{
lean_object* v_a_1741_; lean_object* v___x_1743_; uint8_t v_isShared_1744_; uint8_t v_isSharedCheck_1748_; 
lean_dec(v_a_1707_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_fvarId_1678_);
v_a_1741_ = lean_ctor_get(v___x_1724_, 0);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1724_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1743_ = v___x_1724_;
v_isShared_1744_ = v_isSharedCheck_1748_;
goto v_resetjp_1742_;
}
else
{
lean_inc(v_a_1741_);
lean_dec(v___x_1724_);
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
else
{
lean_object* v_a_1749_; lean_object* v___x_1751_; uint8_t v_isShared_1752_; uint8_t v_isSharedCheck_1756_; 
lean_dec(v_a_1718_);
lean_dec(v_a_1707_);
lean_dec(v_a_1687_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_mvarId_1679_);
lean_dec(v_fvarId_1678_);
v_a_1749_ = lean_ctor_get(v___x_1721_, 0);
v_isSharedCheck_1756_ = !lean_is_exclusive(v___x_1721_);
if (v_isSharedCheck_1756_ == 0)
{
v___x_1751_ = v___x_1721_;
v_isShared_1752_ = v_isSharedCheck_1756_;
goto v_resetjp_1750_;
}
else
{
lean_inc(v_a_1749_);
lean_dec(v___x_1721_);
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
lean_dec(v_a_1707_);
lean_dec_ref(v___x_1702_);
lean_dec(v_a_1690_);
lean_dec(v_a_1687_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_mvarId_1679_);
lean_dec(v_fvarId_1678_);
v_a_1757_ = lean_ctor_get(v___x_1717_, 0);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1764_ == 0)
{
v___x_1759_ = v___x_1717_;
v_isShared_1760_ = v_isSharedCheck_1764_;
goto v_resetjp_1758_;
}
else
{
lean_inc(v_a_1757_);
lean_dec(v___x_1717_);
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
}
}
else
{
lean_object* v_a_1766_; lean_object* v___x_1768_; uint8_t v_isShared_1769_; uint8_t v_isSharedCheck_1773_; 
lean_dec_ref(v___x_1702_);
lean_dec(v_a_1690_);
lean_dec(v_a_1687_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_mvarId_1679_);
lean_dec(v_fvarId_1678_);
v_a_1766_ = lean_ctor_get(v___x_1706_, 0);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1706_);
if (v_isSharedCheck_1773_ == 0)
{
v___x_1768_ = v___x_1706_;
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
else
{
lean_inc(v_a_1766_);
lean_dec(v___x_1706_);
v___x_1768_ = lean_box(0);
v_isShared_1769_ = v_isSharedCheck_1773_;
goto v_resetjp_1767_;
}
v_resetjp_1767_:
{
lean_object* v___x_1771_; 
if (v_isShared_1769_ == 0)
{
v___x_1771_ = v___x_1768_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v_a_1766_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
}
}
}
else
{
lean_object* v_a_1775_; lean_object* v___x_1777_; uint8_t v_isShared_1778_; uint8_t v_isSharedCheck_1782_; 
lean_dec(v_a_1687_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_mvarId_1679_);
lean_dec(v_fvarId_1678_);
v_a_1775_ = lean_ctor_get(v___x_1689_, 0);
v_isSharedCheck_1782_ = !lean_is_exclusive(v___x_1689_);
if (v_isSharedCheck_1782_ == 0)
{
v___x_1777_ = v___x_1689_;
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
else
{
lean_inc(v_a_1775_);
lean_dec(v___x_1689_);
v___x_1777_ = lean_box(0);
v_isShared_1778_ = v_isSharedCheck_1782_;
goto v_resetjp_1776_;
}
v_resetjp_1776_:
{
lean_object* v___x_1780_; 
if (v_isShared_1778_ == 0)
{
v___x_1780_ = v___x_1777_;
goto v_reusejp_1779_;
}
else
{
lean_object* v_reuseFailAlloc_1781_; 
v_reuseFailAlloc_1781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1781_, 0, v_a_1775_);
v___x_1780_ = v_reuseFailAlloc_1781_;
goto v_reusejp_1779_;
}
v_reusejp_1779_:
{
return v___x_1780_;
}
}
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v___y_1682_);
lean_dec_ref(v___y_1681_);
lean_dec(v_mvarId_1679_);
lean_dec(v_fvarId_1678_);
v_a_1783_ = lean_ctor_get(v___x_1686_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1686_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1686_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1686_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object* v_fvarId_1791_, lean_object* v_mvarId_1792_, lean_object* v_tryToClear_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
uint8_t v_tryToClear_boxed_1799_; lean_object* v_res_1800_; 
v_tryToClear_boxed_1799_ = lean_unbox(v_tryToClear_1793_);
v_res_1800_ = l_Lean_Meta_heqToEq___lam__0(v_fvarId_1791_, v_mvarId_1792_, v_tryToClear_boxed_1799_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
return v_res_1800_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object* v_mvarId_1801_, lean_object* v_fvarId_1802_, uint8_t v_tryToClear_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_){
_start:
{
lean_object* v___x_1809_; lean_object* v___f_1810_; lean_object* v___x_1811_; 
v___x_1809_ = lean_box(v_tryToClear_1803_);
lean_inc(v_mvarId_1801_);
v___f_1810_ = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1810_, 0, v_fvarId_1802_);
lean_closure_set(v___f_1810_, 1, v_mvarId_1801_);
lean_closure_set(v___f_1810_, 2, v___x_1809_);
v___x_1811_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1801_, v___f_1810_, v_a_1804_, v_a_1805_, v_a_1806_, v_a_1807_);
return v___x_1811_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* v_mvarId_1812_, lean_object* v_fvarId_1813_, lean_object* v_tryToClear_1814_, lean_object* v_a_1815_, lean_object* v_a_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_){
_start:
{
uint8_t v_tryToClear_boxed_1820_; lean_object* v_res_1821_; 
v_tryToClear_boxed_1820_ = lean_unbox(v_tryToClear_1814_);
v_res_1821_ = l_Lean_Meta_heqToEq(v_mvarId_1812_, v_fvarId_1813_, v_tryToClear_boxed_1820_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
lean_dec(v_a_1816_);
lean_dec_ref(v_a_1815_);
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1825_, lean_object* v_as_1826_, size_t v_sz_1827_, size_t v_i_1828_, lean_object* v_b_1829_, lean_object* v___y_1830_, lean_object* v___y_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_){
_start:
{
lean_object* v_a_1836_; uint8_t v___x_1840_; 
v___x_1840_ = lean_usize_dec_lt(v_i_1828_, v_sz_1827_);
if (v___x_1840_ == 0)
{
lean_object* v___x_1841_; 
lean_dec(v_x_1825_);
v___x_1841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1841_, 0, v_b_1829_);
return v___x_1841_;
}
else
{
lean_object* v___x_1842_; lean_object* v_a_1844_; lean_object* v___x_1848_; lean_object* v_a_1849_; 
lean_dec_ref(v_b_1829_);
v___x_1842_ = lean_box(0);
v___x_1848_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1849_ = lean_array_uget(v_as_1826_, v_i_1828_);
if (lean_obj_tag(v_a_1849_) == 0)
{
v_a_1836_ = v___x_1848_;
goto v___jp_1835_;
}
else
{
lean_object* v_val_1850_; lean_object* v___x_1852_; uint8_t v_isShared_1853_; uint8_t v_isSharedCheck_1937_; 
v_val_1850_ = lean_ctor_get(v_a_1849_, 0);
v_isSharedCheck_1937_ = !lean_is_exclusive(v_a_1849_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1852_ = v_a_1849_;
v_isShared_1853_ = v_isSharedCheck_1937_;
goto v_resetjp_1851_;
}
else
{
lean_inc(v_val_1850_);
lean_dec(v_a_1849_);
v___x_1852_ = lean_box(0);
v_isShared_1853_ = v_isSharedCheck_1937_;
goto v_resetjp_1851_;
}
v_resetjp_1851_:
{
uint8_t v___x_1861_; 
v___x_1861_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1850_);
if (v___x_1861_ == 0)
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = l_Lean_LocalDecl_type(v_val_1850_);
v___x_1868_ = l_Lean_Meta_matchEq_x3f(v___x_1867_, v___y_1830_, v___y_1831_, v___y_1832_, v___y_1833_);
if (lean_obj_tag(v___x_1868_) == 0)
{
lean_object* v_a_1869_; 
v_a_1869_ = lean_ctor_get(v___x_1868_, 0);
lean_inc(v_a_1869_);
lean_dec_ref_known(v___x_1868_, 1);
if (lean_obj_tag(v_a_1869_) == 1)
{
lean_object* v_val_1870_; lean_object* v_snd_1871_; lean_object* v_fst_1872_; lean_object* v_snd_1873_; lean_object* v___x_1874_; 
v_val_1870_ = lean_ctor_get(v_a_1869_, 0);
lean_inc(v_val_1870_);
lean_dec_ref_known(v_a_1869_, 1);
v_snd_1871_ = lean_ctor_get(v_val_1870_, 1);
lean_inc(v_snd_1871_);
lean_dec(v_val_1870_);
v_fst_1872_ = lean_ctor_get(v_snd_1871_, 0);
lean_inc(v_fst_1872_);
v_snd_1873_ = lean_ctor_get(v_snd_1871_, 1);
lean_inc(v_snd_1873_);
lean_dec(v_snd_1871_);
v___x_1874_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1872_, v___y_1831_);
if (lean_obj_tag(v___x_1874_) == 0)
{
lean_object* v_a_1875_; lean_object* v___x_1876_; 
v_a_1875_ = lean_ctor_get(v___x_1874_, 0);
lean_inc(v_a_1875_);
lean_dec_ref_known(v___x_1874_, 1);
v___x_1876_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1873_, v___y_1831_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___y_1879_; uint8_t v___y_1880_; lean_object* v___y_1893_; uint8_t v___y_1898_; uint8_t v___x_1910_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v___x_1910_ = l_Lean_Expr_isFVar(v_a_1877_);
if (v___x_1910_ == 0)
{
v___y_1898_ = v___x_1861_;
goto v___jp_1897_;
}
else
{
lean_object* v___x_1911_; uint8_t v___x_1912_; 
v___x_1911_ = l_Lean_Expr_fvarId_x21(v_a_1877_);
v___x_1912_ = l_Lean_instBEqFVarId_beq(v___x_1911_, v_x_1825_);
lean_dec(v___x_1911_);
v___y_1898_ = v___x_1912_;
goto v___jp_1897_;
}
v___jp_1878_:
{
if (v___y_1880_ == 0)
{
lean_dec(v_a_1877_);
lean_dec(v_val_1850_);
v_a_1836_ = v___x_1848_;
goto v___jp_1835_;
}
else
{
lean_object* v___x_1881_; 
lean_inc(v_x_1825_);
v___x_1881_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1877_, v_x_1825_, v___y_1879_);
if (lean_obj_tag(v___x_1881_) == 0)
{
lean_object* v_a_1882_; uint8_t v___x_1883_; 
v_a_1882_ = lean_ctor_get(v___x_1881_, 0);
lean_inc(v_a_1882_);
lean_dec_ref_known(v___x_1881_, 1);
v___x_1883_ = lean_unbox(v_a_1882_);
lean_dec(v_a_1882_);
if (v___x_1883_ == 0)
{
lean_dec(v_x_1825_);
goto v___jp_1862_;
}
else
{
if (v___x_1861_ == 0)
{
lean_dec(v_val_1850_);
v_a_1836_ = v___x_1848_;
goto v___jp_1835_;
}
else
{
lean_dec(v_x_1825_);
goto v___jp_1862_;
}
}
}
else
{
lean_object* v_a_1884_; lean_object* v___x_1886_; uint8_t v_isShared_1887_; uint8_t v_isSharedCheck_1891_; 
lean_dec(v_val_1850_);
lean_dec(v_x_1825_);
v_a_1884_ = lean_ctor_get(v___x_1881_, 0);
v_isSharedCheck_1891_ = !lean_is_exclusive(v___x_1881_);
if (v_isSharedCheck_1891_ == 0)
{
v___x_1886_ = v___x_1881_;
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
else
{
lean_inc(v_a_1884_);
lean_dec(v___x_1881_);
v___x_1886_ = lean_box(0);
v_isShared_1887_ = v_isSharedCheck_1891_;
goto v_resetjp_1885_;
}
v_resetjp_1885_:
{
lean_object* v___x_1889_; 
if (v_isShared_1887_ == 0)
{
v___x_1889_ = v___x_1886_;
goto v_reusejp_1888_;
}
else
{
lean_object* v_reuseFailAlloc_1890_; 
v_reuseFailAlloc_1890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1890_, 0, v_a_1884_);
v___x_1889_ = v_reuseFailAlloc_1890_;
goto v_reusejp_1888_;
}
v_reusejp_1888_:
{
return v___x_1889_;
}
}
}
}
}
v___jp_1892_:
{
uint8_t v___x_1894_; 
v___x_1894_ = l_Lean_Expr_isFVar(v_a_1875_);
if (v___x_1894_ == 0)
{
lean_dec(v_a_1875_);
v___y_1879_ = v___y_1893_;
v___y_1880_ = v___x_1861_;
goto v___jp_1878_;
}
else
{
lean_object* v___x_1895_; uint8_t v___x_1896_; 
v___x_1895_ = l_Lean_Expr_fvarId_x21(v_a_1875_);
lean_dec(v_a_1875_);
v___x_1896_ = l_Lean_instBEqFVarId_beq(v___x_1895_, v_x_1825_);
lean_dec(v___x_1895_);
v___y_1879_ = v___y_1893_;
v___y_1880_ = v___x_1896_;
goto v___jp_1878_;
}
}
v___jp_1897_:
{
if (v___y_1898_ == 0)
{
lean_del_object(v___x_1852_);
v___y_1893_ = v___y_1831_;
goto v___jp_1892_;
}
else
{
lean_object* v___x_1899_; 
lean_inc(v_x_1825_);
lean_inc(v_a_1875_);
v___x_1899_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1875_, v_x_1825_, v___y_1831_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v_a_1900_; uint8_t v___x_1901_; 
v_a_1900_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_a_1900_);
lean_dec_ref_known(v___x_1899_, 1);
v___x_1901_ = lean_unbox(v_a_1900_);
lean_dec(v_a_1900_);
if (v___x_1901_ == 0)
{
lean_dec(v_a_1877_);
lean_dec(v_a_1875_);
lean_dec(v_x_1825_);
goto v___jp_1854_;
}
else
{
if (v___x_1861_ == 0)
{
lean_del_object(v___x_1852_);
v___y_1893_ = v___y_1831_;
goto v___jp_1892_;
}
else
{
lean_dec(v_a_1877_);
lean_dec(v_a_1875_);
lean_dec(v_x_1825_);
goto v___jp_1854_;
}
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_dec(v_a_1877_);
lean_dec(v_a_1875_);
lean_del_object(v___x_1852_);
lean_dec(v_val_1850_);
lean_dec(v_x_1825_);
v_a_1902_ = lean_ctor_get(v___x_1899_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1899_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1899_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1899_);
v___x_1904_ = lean_box(0);
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
v_resetjp_1903_:
{
lean_object* v___x_1907_; 
if (v_isShared_1905_ == 0)
{
v___x_1907_ = v___x_1904_;
goto v_reusejp_1906_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_a_1902_);
v___x_1907_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1906_;
}
v_reusejp_1906_:
{
return v___x_1907_;
}
}
}
}
}
}
else
{
lean_object* v_a_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1920_; 
lean_dec(v_a_1875_);
lean_del_object(v___x_1852_);
lean_dec(v_val_1850_);
lean_dec(v_x_1825_);
v_a_1913_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1920_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1920_ == 0)
{
v___x_1915_ = v___x_1876_;
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_a_1913_);
lean_dec(v___x_1876_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1920_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1918_; 
if (v_isShared_1916_ == 0)
{
v___x_1918_ = v___x_1915_;
goto v_reusejp_1917_;
}
else
{
lean_object* v_reuseFailAlloc_1919_; 
v_reuseFailAlloc_1919_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_a_1913_);
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
lean_dec(v_snd_1873_);
lean_del_object(v___x_1852_);
lean_dec(v_val_1850_);
lean_dec(v_x_1825_);
v_a_1921_ = lean_ctor_get(v___x_1874_, 0);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1874_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1874_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_dec(v___x_1874_);
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
lean_dec(v_a_1869_);
lean_del_object(v___x_1852_);
lean_dec(v_val_1850_);
v_a_1836_ = v___x_1848_;
goto v___jp_1835_;
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
lean_del_object(v___x_1852_);
lean_dec(v_val_1850_);
lean_dec(v_x_1825_);
v_a_1929_ = lean_ctor_get(v___x_1868_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1868_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1868_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1868_);
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
lean_del_object(v___x_1852_);
lean_dec(v_val_1850_);
v_a_1836_ = v___x_1848_;
goto v___jp_1835_;
}
v___jp_1854_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1859_; 
v___x_1855_ = l_Lean_LocalDecl_fvarId(v_val_1850_);
lean_dec(v_val_1850_);
v___x_1856_ = lean_box(v___x_1840_);
v___x_1857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1857_, 0, v___x_1855_);
lean_ctor_set(v___x_1857_, 1, v___x_1856_);
if (v_isShared_1853_ == 0)
{
lean_ctor_set(v___x_1852_, 0, v___x_1857_);
v___x_1859_ = v___x_1852_;
goto v_reusejp_1858_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1857_);
v___x_1859_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1858_;
}
v_reusejp_1858_:
{
v_a_1844_ = v___x_1859_;
goto v___jp_1843_;
}
}
v___jp_1862_:
{
lean_object* v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = l_Lean_LocalDecl_fvarId(v_val_1850_);
lean_dec(v_val_1850_);
v___x_1864_ = lean_box(v___x_1861_);
v___x_1865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1865_, 0, v___x_1863_);
lean_ctor_set(v___x_1865_, 1, v___x_1864_);
v___x_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1866_, 0, v___x_1865_);
v_a_1844_ = v___x_1866_;
goto v___jp_1843_;
}
}
}
v___jp_1843_:
{
lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1845_, 0, v_a_1844_);
v___x_1846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1846_, 0, v___x_1845_);
lean_ctor_set(v___x_1846_, 1, v___x_1842_);
v___x_1847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1847_, 0, v___x_1846_);
return v___x_1847_;
}
}
v___jp_1835_:
{
size_t v___x_1837_; size_t v___x_1838_; 
v___x_1837_ = ((size_t)1ULL);
v___x_1838_ = lean_usize_add(v_i_1828_, v___x_1837_);
lean_inc_ref(v_a_1836_);
v_i_1828_ = v___x_1838_;
v_b_1829_ = v_a_1836_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1938_, lean_object* v_as_1939_, lean_object* v_sz_1940_, lean_object* v_i_1941_, lean_object* v_b_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
size_t v_sz_boxed_1948_; size_t v_i_boxed_1949_; lean_object* v_res_1950_; 
v_sz_boxed_1948_ = lean_unbox_usize(v_sz_1940_);
lean_dec(v_sz_1940_);
v_i_boxed_1949_ = lean_unbox_usize(v_i_1941_);
lean_dec(v_i_1941_);
v_res_1950_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1938_, v_as_1939_, v_sz_boxed_1948_, v_i_boxed_1949_, v_b_1942_, v___y_1943_, v___y_1944_, v___y_1945_, v___y_1946_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec(v___y_1944_);
lean_dec_ref(v___y_1943_);
lean_dec_ref(v_as_1939_);
return v_res_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object* v_x_1951_, lean_object* v_as_1952_, size_t v_sz_1953_, size_t v_i_1954_, lean_object* v_b_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_){
_start:
{
lean_object* v_a_1962_; uint8_t v___x_1966_; 
v___x_1966_ = lean_usize_dec_lt(v_i_1954_, v_sz_1953_);
if (v___x_1966_ == 0)
{
lean_object* v___x_1967_; 
lean_dec(v_x_1951_);
v___x_1967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1967_, 0, v_b_1955_);
return v___x_1967_;
}
else
{
lean_object* v___x_1968_; lean_object* v_a_1970_; lean_object* v___x_1974_; lean_object* v_a_1975_; 
lean_dec_ref(v_b_1955_);
v___x_1968_ = lean_box(0);
v___x_1974_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1975_ = lean_array_uget(v_as_1952_, v_i_1954_);
if (lean_obj_tag(v_a_1975_) == 0)
{
v_a_1962_ = v___x_1974_;
goto v___jp_1961_;
}
else
{
lean_object* v_val_1976_; lean_object* v___x_1978_; uint8_t v_isShared_1979_; uint8_t v_isSharedCheck_2063_; 
v_val_1976_ = lean_ctor_get(v_a_1975_, 0);
v_isSharedCheck_2063_ = !lean_is_exclusive(v_a_1975_);
if (v_isSharedCheck_2063_ == 0)
{
v___x_1978_ = v_a_1975_;
v_isShared_1979_ = v_isSharedCheck_2063_;
goto v_resetjp_1977_;
}
else
{
lean_inc(v_val_1976_);
lean_dec(v_a_1975_);
v___x_1978_ = lean_box(0);
v_isShared_1979_ = v_isSharedCheck_2063_;
goto v_resetjp_1977_;
}
v_resetjp_1977_:
{
uint8_t v___x_1987_; 
v___x_1987_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1976_);
if (v___x_1987_ == 0)
{
lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1993_ = l_Lean_LocalDecl_type(v_val_1976_);
v___x_1994_ = l_Lean_Meta_matchEq_x3f(v___x_1993_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
if (lean_obj_tag(v___x_1994_) == 0)
{
lean_object* v_a_1995_; 
v_a_1995_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_a_1995_);
lean_dec_ref_known(v___x_1994_, 1);
if (lean_obj_tag(v_a_1995_) == 1)
{
lean_object* v_val_1996_; lean_object* v_snd_1997_; lean_object* v_fst_1998_; lean_object* v_snd_1999_; lean_object* v___x_2000_; 
v_val_1996_ = lean_ctor_get(v_a_1995_, 0);
lean_inc(v_val_1996_);
lean_dec_ref_known(v_a_1995_, 1);
v_snd_1997_ = lean_ctor_get(v_val_1996_, 1);
lean_inc(v_snd_1997_);
lean_dec(v_val_1996_);
v_fst_1998_ = lean_ctor_get(v_snd_1997_, 0);
lean_inc(v_fst_1998_);
v_snd_1999_ = lean_ctor_get(v_snd_1997_, 1);
lean_inc(v_snd_1999_);
lean_dec(v_snd_1997_);
v___x_2000_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1998_, v___y_1957_);
if (lean_obj_tag(v___x_2000_) == 0)
{
lean_object* v_a_2001_; lean_object* v___x_2002_; 
v_a_2001_ = lean_ctor_get(v___x_2000_, 0);
lean_inc(v_a_2001_);
lean_dec_ref_known(v___x_2000_, 1);
v___x_2002_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1999_, v___y_1957_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___y_2005_; uint8_t v___y_2006_; lean_object* v___y_2019_; uint8_t v___y_2024_; uint8_t v___x_2036_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2036_ = l_Lean_Expr_isFVar(v_a_2003_);
if (v___x_2036_ == 0)
{
v___y_2024_ = v___x_1987_;
goto v___jp_2023_;
}
else
{
lean_object* v___x_2037_; uint8_t v___x_2038_; 
v___x_2037_ = l_Lean_Expr_fvarId_x21(v_a_2003_);
v___x_2038_ = l_Lean_instBEqFVarId_beq(v___x_2037_, v_x_1951_);
lean_dec(v___x_2037_);
v___y_2024_ = v___x_2038_;
goto v___jp_2023_;
}
v___jp_2004_:
{
if (v___y_2006_ == 0)
{
lean_dec(v_a_2003_);
lean_dec(v_val_1976_);
v_a_1962_ = v___x_1974_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_2007_; 
lean_inc(v_x_1951_);
v___x_2007_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2003_, v_x_1951_, v___y_2005_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; uint8_t v___x_2009_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = lean_unbox(v_a_2008_);
lean_dec(v_a_2008_);
if (v___x_2009_ == 0)
{
lean_dec(v_x_1951_);
goto v___jp_1988_;
}
else
{
if (v___x_1987_ == 0)
{
lean_dec(v_val_1976_);
v_a_1962_ = v___x_1974_;
goto v___jp_1961_;
}
else
{
lean_dec(v_x_1951_);
goto v___jp_1988_;
}
}
}
else
{
lean_object* v_a_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2017_; 
lean_dec(v_val_1976_);
lean_dec(v_x_1951_);
v_a_2010_ = lean_ctor_get(v___x_2007_, 0);
v_isSharedCheck_2017_ = !lean_is_exclusive(v___x_2007_);
if (v_isSharedCheck_2017_ == 0)
{
v___x_2012_ = v___x_2007_;
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_a_2010_);
lean_dec(v___x_2007_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2017_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v___x_2015_; 
if (v_isShared_2013_ == 0)
{
v___x_2015_ = v___x_2012_;
goto v_reusejp_2014_;
}
else
{
lean_object* v_reuseFailAlloc_2016_; 
v_reuseFailAlloc_2016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2016_, 0, v_a_2010_);
v___x_2015_ = v_reuseFailAlloc_2016_;
goto v_reusejp_2014_;
}
v_reusejp_2014_:
{
return v___x_2015_;
}
}
}
}
}
v___jp_2018_:
{
uint8_t v___x_2020_; 
v___x_2020_ = l_Lean_Expr_isFVar(v_a_2001_);
if (v___x_2020_ == 0)
{
lean_dec(v_a_2001_);
v___y_2005_ = v___y_2019_;
v___y_2006_ = v___x_1987_;
goto v___jp_2004_;
}
else
{
lean_object* v___x_2021_; uint8_t v___x_2022_; 
v___x_2021_ = l_Lean_Expr_fvarId_x21(v_a_2001_);
lean_dec(v_a_2001_);
v___x_2022_ = l_Lean_instBEqFVarId_beq(v___x_2021_, v_x_1951_);
lean_dec(v___x_2021_);
v___y_2005_ = v___y_2019_;
v___y_2006_ = v___x_2022_;
goto v___jp_2004_;
}
}
v___jp_2023_:
{
if (v___y_2024_ == 0)
{
lean_del_object(v___x_1978_);
v___y_2019_ = v___y_1957_;
goto v___jp_2018_;
}
else
{
lean_object* v___x_2025_; 
lean_inc(v_x_1951_);
lean_inc(v_a_2001_);
v___x_2025_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2001_, v_x_1951_, v___y_1957_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; uint8_t v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
v___x_2027_ = lean_unbox(v_a_2026_);
lean_dec(v_a_2026_);
if (v___x_2027_ == 0)
{
lean_dec(v_a_2003_);
lean_dec(v_a_2001_);
lean_dec(v_x_1951_);
goto v___jp_1980_;
}
else
{
if (v___x_1987_ == 0)
{
lean_del_object(v___x_1978_);
v___y_2019_ = v___y_1957_;
goto v___jp_2018_;
}
else
{
lean_dec(v_a_2003_);
lean_dec(v_a_2001_);
lean_dec(v_x_1951_);
goto v___jp_1980_;
}
}
}
else
{
lean_object* v_a_2028_; lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2035_; 
lean_dec(v_a_2003_);
lean_dec(v_a_2001_);
lean_del_object(v___x_1978_);
lean_dec(v_val_1976_);
lean_dec(v_x_1951_);
v_a_2028_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2035_ == 0)
{
v___x_2030_ = v___x_2025_;
v_isShared_2031_ = v_isSharedCheck_2035_;
goto v_resetjp_2029_;
}
else
{
lean_inc(v_a_2028_);
lean_dec(v___x_2025_);
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
else
{
lean_object* v_a_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2046_; 
lean_dec(v_a_2001_);
lean_del_object(v___x_1978_);
lean_dec(v_val_1976_);
lean_dec(v_x_1951_);
v_a_2039_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2046_ == 0)
{
v___x_2041_ = v___x_2002_;
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_a_2039_);
lean_dec(v___x_2002_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2046_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
v___x_2044_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
return v___x_2044_;
}
}
}
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec(v_snd_1999_);
lean_del_object(v___x_1978_);
lean_dec(v_val_1976_);
lean_dec(v_x_1951_);
v_a_2047_ = lean_ctor_get(v___x_2000_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2000_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2000_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2000_);
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
lean_dec(v_a_1995_);
lean_del_object(v___x_1978_);
lean_dec(v_val_1976_);
v_a_1962_ = v___x_1974_;
goto v___jp_1961_;
}
}
else
{
lean_object* v_a_2055_; lean_object* v___x_2057_; uint8_t v_isShared_2058_; uint8_t v_isSharedCheck_2062_; 
lean_del_object(v___x_1978_);
lean_dec(v_val_1976_);
lean_dec(v_x_1951_);
v_a_2055_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2062_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2062_ == 0)
{
v___x_2057_ = v___x_1994_;
v_isShared_2058_ = v_isSharedCheck_2062_;
goto v_resetjp_2056_;
}
else
{
lean_inc(v_a_2055_);
lean_dec(v___x_1994_);
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
lean_del_object(v___x_1978_);
lean_dec(v_val_1976_);
v_a_1962_ = v___x_1974_;
goto v___jp_1961_;
}
v___jp_1980_:
{
lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1985_; 
v___x_1981_ = l_Lean_LocalDecl_fvarId(v_val_1976_);
lean_dec(v_val_1976_);
v___x_1982_ = lean_box(v___x_1966_);
v___x_1983_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1983_, 0, v___x_1981_);
lean_ctor_set(v___x_1983_, 1, v___x_1982_);
if (v_isShared_1979_ == 0)
{
lean_ctor_set(v___x_1978_, 0, v___x_1983_);
v___x_1985_ = v___x_1978_;
goto v_reusejp_1984_;
}
else
{
lean_object* v_reuseFailAlloc_1986_; 
v_reuseFailAlloc_1986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1983_);
v___x_1985_ = v_reuseFailAlloc_1986_;
goto v_reusejp_1984_;
}
v_reusejp_1984_:
{
v_a_1970_ = v___x_1985_;
goto v___jp_1969_;
}
}
v___jp_1988_:
{
lean_object* v___x_1989_; lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1989_ = l_Lean_LocalDecl_fvarId(v_val_1976_);
lean_dec(v_val_1976_);
v___x_1990_ = lean_box(v___x_1987_);
v___x_1991_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1991_, 0, v___x_1989_);
lean_ctor_set(v___x_1991_, 1, v___x_1990_);
v___x_1992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
v_a_1970_ = v___x_1992_;
goto v___jp_1969_;
}
}
}
v___jp_1969_:
{
lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; 
v___x_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1971_, 0, v_a_1970_);
v___x_1972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1971_);
lean_ctor_set(v___x_1972_, 1, v___x_1968_);
v___x_1973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___x_1972_);
return v___x_1973_;
}
}
v___jp_1961_:
{
size_t v___x_1963_; size_t v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = ((size_t)1ULL);
v___x_1964_ = lean_usize_add(v_i_1954_, v___x_1963_);
lean_inc_ref(v_a_1962_);
v___x_1965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1951_, v_as_1952_, v_sz_1953_, v___x_1964_, v_a_1962_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
return v___x_1965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2064_, lean_object* v_as_2065_, lean_object* v_sz_2066_, lean_object* v_i_2067_, lean_object* v_b_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_){
_start:
{
size_t v_sz_boxed_2074_; size_t v_i_boxed_2075_; lean_object* v_res_2076_; 
v_sz_boxed_2074_ = lean_unbox_usize(v_sz_2066_);
lean_dec(v_sz_2066_);
v_i_boxed_2075_ = lean_unbox_usize(v_i_2067_);
lean_dec(v_i_2067_);
v_res_2076_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2064_, v_as_2065_, v_sz_boxed_2074_, v_i_boxed_2075_, v_b_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec(v___y_2070_);
lean_dec_ref(v___y_2069_);
lean_dec_ref(v_as_2065_);
return v_res_2076_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object* v_x_2077_, lean_object* v_x_2078_, lean_object* v___y_2079_, lean_object* v___y_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_){
_start:
{
if (lean_obj_tag(v_x_2078_) == 0)
{
lean_object* v_cs_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; size_t v_sz_2087_; size_t v___x_2088_; lean_object* v___x_2089_; 
v_cs_2084_ = lean_ctor_get(v_x_2078_, 0);
v___x_2085_ = lean_box(0);
v___x_2086_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2087_ = lean_array_size(v_cs_2084_);
v___x_2088_ = ((size_t)0ULL);
v___x_2089_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2077_, v_cs_2084_, v_sz_2087_, v___x_2088_, v___x_2086_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; lean_object* v___x_2092_; uint8_t v_isShared_2093_; uint8_t v_isSharedCheck_2102_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2102_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2102_ == 0)
{
v___x_2092_ = v___x_2089_;
v_isShared_2093_ = v_isSharedCheck_2102_;
goto v_resetjp_2091_;
}
else
{
lean_inc(v_a_2090_);
lean_dec(v___x_2089_);
v___x_2092_ = lean_box(0);
v_isShared_2093_ = v_isSharedCheck_2102_;
goto v_resetjp_2091_;
}
v_resetjp_2091_:
{
lean_object* v_fst_2094_; 
v_fst_2094_ = lean_ctor_get(v_a_2090_, 0);
lean_inc(v_fst_2094_);
lean_dec(v_a_2090_);
if (lean_obj_tag(v_fst_2094_) == 0)
{
lean_object* v___x_2096_; 
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v___x_2085_);
v___x_2096_ = v___x_2092_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v___x_2085_);
v___x_2096_ = v_reuseFailAlloc_2097_;
goto v_reusejp_2095_;
}
v_reusejp_2095_:
{
return v___x_2096_;
}
}
else
{
lean_object* v_val_2098_; lean_object* v___x_2100_; 
v_val_2098_ = lean_ctor_get(v_fst_2094_, 0);
lean_inc(v_val_2098_);
lean_dec_ref_known(v_fst_2094_, 1);
if (v_isShared_2093_ == 0)
{
lean_ctor_set(v___x_2092_, 0, v_val_2098_);
v___x_2100_ = v___x_2092_;
goto v_reusejp_2099_;
}
else
{
lean_object* v_reuseFailAlloc_2101_; 
v_reuseFailAlloc_2101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_val_2098_);
v___x_2100_ = v_reuseFailAlloc_2101_;
goto v_reusejp_2099_;
}
v_reusejp_2099_:
{
return v___x_2100_;
}
}
}
}
else
{
lean_object* v_a_2103_; lean_object* v___x_2105_; uint8_t v_isShared_2106_; uint8_t v_isSharedCheck_2110_; 
v_a_2103_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2110_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2110_ == 0)
{
v___x_2105_ = v___x_2089_;
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
else
{
lean_inc(v_a_2103_);
lean_dec(v___x_2089_);
v___x_2105_ = lean_box(0);
v_isShared_2106_ = v_isSharedCheck_2110_;
goto v_resetjp_2104_;
}
v_resetjp_2104_:
{
lean_object* v___x_2108_; 
if (v_isShared_2106_ == 0)
{
v___x_2108_ = v___x_2105_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2109_; 
v_reuseFailAlloc_2109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2109_, 0, v_a_2103_);
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
lean_object* v_vs_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; size_t v_sz_2114_; size_t v___x_2115_; lean_object* v___x_2116_; 
v_vs_2111_ = lean_ctor_get(v_x_2078_, 0);
v___x_2112_ = lean_box(0);
v___x_2113_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2114_ = lean_array_size(v_vs_2111_);
v___x_2115_ = ((size_t)0ULL);
v___x_2116_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2077_, v_vs_2111_, v_sz_2114_, v___x_2115_, v___x_2113_, v___y_2079_, v___y_2080_, v___y_2081_, v___y_2082_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v_a_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2129_; 
v_a_2117_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2119_ = v___x_2116_;
v_isShared_2120_ = v_isSharedCheck_2129_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_a_2117_);
lean_dec(v___x_2116_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2129_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v_fst_2121_; 
v_fst_2121_ = lean_ctor_get(v_a_2117_, 0);
lean_inc(v_fst_2121_);
lean_dec(v_a_2117_);
if (lean_obj_tag(v_fst_2121_) == 0)
{
lean_object* v___x_2123_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2112_);
v___x_2123_ = v___x_2119_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v___x_2112_);
v___x_2123_ = v_reuseFailAlloc_2124_;
goto v_reusejp_2122_;
}
v_reusejp_2122_:
{
return v___x_2123_;
}
}
else
{
lean_object* v_val_2125_; lean_object* v___x_2127_; 
v_val_2125_ = lean_ctor_get(v_fst_2121_, 0);
lean_inc(v_val_2125_);
lean_dec_ref_known(v_fst_2121_, 1);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v_val_2125_);
v___x_2127_ = v___x_2119_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_val_2125_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
v_a_2130_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2116_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2116_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2138_, lean_object* v_as_2139_, size_t v_sz_2140_, size_t v_i_2141_, lean_object* v_b_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_){
_start:
{
uint8_t v___x_2148_; 
v___x_2148_ = lean_usize_dec_lt(v_i_2141_, v_sz_2140_);
if (v___x_2148_ == 0)
{
lean_object* v___x_2149_; 
lean_dec(v_x_2138_);
v___x_2149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2149_, 0, v_b_2142_);
return v___x_2149_;
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2151_; 
lean_dec_ref(v_b_2142_);
v_a_2150_ = lean_array_uget_borrowed(v_as_2139_, v_i_2141_);
lean_inc(v_x_2138_);
v___x_2151_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2138_, v_a_2150_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
if (lean_obj_tag(v___x_2151_) == 0)
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2166_; 
v_a_2152_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2154_ = v___x_2151_;
v_isShared_2155_ = v_isSharedCheck_2166_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2151_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2166_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; 
v___x_2156_ = lean_box(0);
if (lean_obj_tag(v_a_2152_) == 1)
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2160_; 
lean_dec(v_x_2138_);
v___x_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2157_, 0, v_a_2152_);
v___x_2158_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2158_, 0, v___x_2157_);
lean_ctor_set(v___x_2158_, 1, v___x_2156_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 0, v___x_2158_);
v___x_2160_ = v___x_2154_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2158_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
else
{
lean_object* v___x_2162_; size_t v___x_2163_; size_t v___x_2164_; 
lean_del_object(v___x_2154_);
lean_dec(v_a_2152_);
v___x_2162_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2163_ = ((size_t)1ULL);
v___x_2164_ = lean_usize_add(v_i_2141_, v___x_2163_);
v_i_2141_ = v___x_2164_;
v_b_2142_ = v___x_2162_;
goto _start;
}
}
}
else
{
lean_object* v_a_2167_; lean_object* v___x_2169_; uint8_t v_isShared_2170_; uint8_t v_isSharedCheck_2174_; 
lean_dec(v_x_2138_);
v_a_2167_ = lean_ctor_get(v___x_2151_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v___x_2151_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2169_ = v___x_2151_;
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
else
{
lean_inc(v_a_2167_);
lean_dec(v___x_2151_);
v___x_2169_ = lean_box(0);
v_isShared_2170_ = v_isSharedCheck_2174_;
goto v_resetjp_2168_;
}
v_resetjp_2168_:
{
lean_object* v___x_2172_; 
if (v_isShared_2170_ == 0)
{
v___x_2172_ = v___x_2169_;
goto v_reusejp_2171_;
}
else
{
lean_object* v_reuseFailAlloc_2173_; 
v_reuseFailAlloc_2173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2173_, 0, v_a_2167_);
v___x_2172_ = v_reuseFailAlloc_2173_;
goto v_reusejp_2171_;
}
v_reusejp_2171_:
{
return v___x_2172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2175_, lean_object* v_as_2176_, lean_object* v_sz_2177_, lean_object* v_i_2178_, lean_object* v_b_2179_, lean_object* v___y_2180_, lean_object* v___y_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_){
_start:
{
size_t v_sz_boxed_2185_; size_t v_i_boxed_2186_; lean_object* v_res_2187_; 
v_sz_boxed_2185_ = lean_unbox_usize(v_sz_2177_);
lean_dec(v_sz_2177_);
v_i_boxed_2186_ = lean_unbox_usize(v_i_2178_);
lean_dec(v_i_2178_);
v_res_2187_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2175_, v_as_2176_, v_sz_boxed_2185_, v_i_boxed_2186_, v_b_2179_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec(v___y_2181_);
lean_dec_ref(v___y_2180_);
lean_dec_ref(v_as_2176_);
return v_res_2187_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2188_, lean_object* v_x_2189_, lean_object* v___y_2190_, lean_object* v___y_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_){
_start:
{
lean_object* v_res_2195_; 
v_res_2195_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2188_, v_x_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec(v___y_2191_);
lean_dec_ref(v___y_2190_);
lean_dec_ref(v_x_2189_);
return v_res_2195_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object* v_x_2196_, lean_object* v_t_2197_, lean_object* v___y_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_){
_start:
{
lean_object* v_root_2203_; lean_object* v_tail_2204_; lean_object* v___x_2205_; 
v_root_2203_ = lean_ctor_get(v_t_2197_, 0);
v_tail_2204_ = lean_ctor_get(v_t_2197_, 1);
lean_inc(v_x_2196_);
v___x_2205_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2196_, v_root_2203_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
if (lean_obj_tag(v_a_2206_) == 0)
{
lean_object* v___x_2207_; size_t v_sz_2208_; size_t v___x_2209_; lean_object* v___x_2210_; 
lean_dec_ref_known(v___x_2205_, 1);
v___x_2207_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2208_ = lean_array_size(v_tail_2204_);
v___x_2209_ = ((size_t)0ULL);
v___x_2210_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2196_, v_tail_2204_, v_sz_2208_, v___x_2209_, v___x_2207_, v___y_2198_, v___y_2199_, v___y_2200_, v___y_2201_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2213_; uint8_t v_isShared_2214_; uint8_t v_isSharedCheck_2223_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2213_ = v___x_2210_;
v_isShared_2214_ = v_isSharedCheck_2223_;
goto v_resetjp_2212_;
}
else
{
lean_inc(v_a_2211_);
lean_dec(v___x_2210_);
v___x_2213_ = lean_box(0);
v_isShared_2214_ = v_isSharedCheck_2223_;
goto v_resetjp_2212_;
}
v_resetjp_2212_:
{
lean_object* v_fst_2215_; 
v_fst_2215_ = lean_ctor_get(v_a_2211_, 0);
lean_inc(v_fst_2215_);
lean_dec(v_a_2211_);
if (lean_obj_tag(v_fst_2215_) == 0)
{
lean_object* v___x_2217_; 
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v_a_2206_);
v___x_2217_ = v___x_2213_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2218_; 
v_reuseFailAlloc_2218_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2206_);
v___x_2217_ = v_reuseFailAlloc_2218_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
return v___x_2217_;
}
}
else
{
lean_object* v_val_2219_; lean_object* v___x_2221_; 
v_val_2219_ = lean_ctor_get(v_fst_2215_, 0);
lean_inc(v_val_2219_);
lean_dec_ref_known(v_fst_2215_, 1);
if (v_isShared_2214_ == 0)
{
lean_ctor_set(v___x_2213_, 0, v_val_2219_);
v___x_2221_ = v___x_2213_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v_val_2219_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2226_; uint8_t v_isShared_2227_; uint8_t v_isSharedCheck_2231_; 
v_a_2224_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2231_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2231_ == 0)
{
v___x_2226_ = v___x_2210_;
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
else
{
lean_inc(v_a_2224_);
lean_dec(v___x_2210_);
v___x_2226_ = lean_box(0);
v_isShared_2227_ = v_isSharedCheck_2231_;
goto v_resetjp_2225_;
}
v_resetjp_2225_:
{
lean_object* v___x_2229_; 
if (v_isShared_2227_ == 0)
{
v___x_2229_ = v___x_2226_;
goto v_reusejp_2228_;
}
else
{
lean_object* v_reuseFailAlloc_2230_; 
v_reuseFailAlloc_2230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2230_, 0, v_a_2224_);
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
lean_dec_ref_known(v_a_2206_, 1);
lean_dec(v_x_2196_);
return v___x_2205_;
}
}
else
{
lean_dec(v_x_2196_);
return v___x_2205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* v_x_2232_, lean_object* v_t_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_){
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2232_, v_t_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec(v___y_2235_);
lean_dec_ref(v___y_2234_);
lean_dec_ref(v_t_2233_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object* v_x_2240_, lean_object* v_lctx_2241_, lean_object* v___y_2242_, lean_object* v___y_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_){
_start:
{
lean_object* v_decls_2247_; lean_object* v___x_2248_; 
v_decls_2247_ = lean_ctor_get(v_lctx_2241_, 1);
v___x_2248_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2240_, v_decls_2247_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_);
return v___x_2248_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object* v_x_2249_, lean_object* v_lctx_2250_, lean_object* v___y_2251_, lean_object* v___y_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_){
_start:
{
lean_object* v_res_2256_; 
v_res_2256_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2249_, v_lctx_2250_, v___y_2251_, v___y_2252_, v___y_2253_, v___y_2254_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec(v___y_2252_);
lean_dec_ref(v___y_2251_);
lean_dec_ref(v_lctx_2250_);
return v_res_2256_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2258_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__0));
v___x_2259_ = l_Lean_stringToMessageData(v___x_2258_);
return v___x_2259_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2261_; lean_object* v___x_2262_; 
v___x_2261_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__2));
v___x_2262_ = l_Lean_stringToMessageData(v___x_2261_);
return v___x_2262_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2264_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__4));
v___x_2265_ = l_Lean_stringToMessageData(v___x_2264_);
return v___x_2265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object* v_x_2266_, lean_object* v_mvarId_2267_, lean_object* v___y_2268_, lean_object* v___y_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_){
_start:
{
lean_object* v___y_2274_; lean_object* v___y_2275_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___x_2322_; 
lean_inc(v_x_2266_);
v___x_2322_ = l_Lean_FVarId_getDecl___redArg(v_x_2266_, v___y_2268_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; uint8_t v___x_2324_; uint8_t v___x_2325_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2324_ = 0;
v___x_2325_ = l_Lean_LocalDecl_isLet(v_a_2323_, v___x_2324_);
lean_dec(v_a_2323_);
if (v___x_2325_ == 0)
{
v___y_2274_ = v___y_2268_;
v___y_2275_ = v___y_2269_;
v___y_2276_ = v___y_2270_;
v___y_2277_ = v___y_2271_;
goto v___jp_2273_;
}
else
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2326_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2327_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2266_);
v___x_2328_ = l_Lean_mkFVar(v_x_2266_);
v___x_2329_ = l_Lean_MessageData_ofExpr(v___x_2328_);
v___x_2330_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2330_, 0, v___x_2327_);
lean_ctor_set(v___x_2330_, 1, v___x_2329_);
v___x_2331_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2330_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
lean_inc(v_mvarId_2267_);
v___x_2334_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2326_, v_mvarId_2267_, v___x_2333_, v___y_2268_, v___y_2269_, v___y_2270_, v___y_2271_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_dec_ref_known(v___x_2334_, 1);
v___y_2274_ = v___y_2268_;
v___y_2275_ = v___y_2269_;
v___y_2276_ = v___y_2270_;
v___y_2277_ = v___y_2271_;
goto v___jp_2273_;
}
else
{
lean_object* v_a_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2342_; 
lean_dec(v_mvarId_2267_);
lean_dec(v_x_2266_);
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2337_ = v___x_2334_;
v_isShared_2338_ = v_isSharedCheck_2342_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_a_2335_);
lean_dec(v___x_2334_);
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
}
}
else
{
lean_object* v_a_2343_; lean_object* v___x_2345_; uint8_t v_isShared_2346_; uint8_t v_isSharedCheck_2350_; 
lean_dec(v_mvarId_2267_);
lean_dec(v_x_2266_);
v_a_2343_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2350_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2350_ == 0)
{
v___x_2345_ = v___x_2322_;
v_isShared_2346_ = v_isSharedCheck_2350_;
goto v_resetjp_2344_;
}
else
{
lean_inc(v_a_2343_);
lean_dec(v___x_2322_);
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
v___jp_2273_:
{
lean_object* v_lctx_2278_; lean_object* v___x_2279_; 
v_lctx_2278_ = lean_ctor_get(v___y_2274_, 2);
lean_inc(v_x_2266_);
v___x_2279_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2266_, v_lctx_2278_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2279_) == 0)
{
lean_object* v_a_2280_; 
v_a_2280_ = lean_ctor_get(v___x_2279_, 0);
lean_inc(v_a_2280_);
lean_dec_ref_known(v___x_2279_, 1);
if (lean_obj_tag(v_a_2280_) == 1)
{
lean_object* v_val_2281_; lean_object* v_fst_2282_; lean_object* v_snd_2283_; lean_object* v___x_2284_; uint8_t v___x_2285_; uint8_t v___x_2286_; lean_object* v___x_2287_; 
lean_dec(v_x_2266_);
v_val_2281_ = lean_ctor_get(v_a_2280_, 0);
lean_inc(v_val_2281_);
lean_dec_ref_known(v_a_2280_, 1);
v_fst_2282_ = lean_ctor_get(v_val_2281_, 0);
lean_inc(v_fst_2282_);
v_snd_2283_ = lean_ctor_get(v_val_2281_, 1);
lean_inc(v_snd_2283_);
lean_dec(v_val_2281_);
v___x_2284_ = lean_box(0);
v___x_2285_ = 1;
v___x_2286_ = lean_unbox(v_snd_2283_);
lean_dec(v_snd_2283_);
v___x_2287_ = l_Lean_Meta_substCore(v_mvarId_2267_, v_fst_2282_, v___x_2286_, v___x_2284_, v___x_2285_, v___x_2285_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2296_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2290_ = v___x_2287_;
v_isShared_2291_ = v_isSharedCheck_2296_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2287_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2296_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v_snd_2292_; lean_object* v___x_2294_; 
v_snd_2292_ = lean_ctor_get(v_a_2288_, 1);
lean_inc(v_snd_2292_);
lean_dec(v_a_2288_);
if (v_isShared_2291_ == 0)
{
lean_ctor_set(v___x_2290_, 0, v_snd_2292_);
v___x_2294_ = v___x_2290_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2295_; 
v_reuseFailAlloc_2295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2295_, 0, v_snd_2292_);
v___x_2294_ = v_reuseFailAlloc_2295_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
return v___x_2294_;
}
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
v_a_2297_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2287_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2287_);
v___x_2299_ = lean_box(0);
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
v_resetjp_2298_:
{
lean_object* v___x_2302_; 
if (v_isShared_2300_ == 0)
{
v___x_2302_ = v___x_2299_;
goto v_reusejp_2301_;
}
else
{
lean_object* v_reuseFailAlloc_2303_; 
v_reuseFailAlloc_2303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2303_, 0, v_a_2297_);
v___x_2302_ = v_reuseFailAlloc_2303_;
goto v_reusejp_2301_;
}
v_reusejp_2301_:
{
return v___x_2302_;
}
}
}
}
else
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
lean_dec(v_a_2280_);
v___x_2305_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2306_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2307_ = l_Lean_mkFVar(v_x_2266_);
v___x_2308_ = l_Lean_MessageData_ofExpr(v___x_2307_);
v___x_2309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2309_, 0, v___x_2306_);
lean_ctor_set(v___x_2309_, 1, v___x_2308_);
v___x_2310_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2309_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
v___x_2313_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2305_, v_mvarId_2267_, v___x_2312_, v___y_2274_, v___y_2275_, v___y_2276_, v___y_2277_);
return v___x_2313_;
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_dec(v_mvarId_2267_);
lean_dec(v_x_2266_);
v_a_2314_ = lean_ctor_get(v___x_2279_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2279_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2279_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2279_);
v___x_2316_ = lean_box(0);
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
v_resetjp_2315_:
{
lean_object* v___x_2319_; 
if (v_isShared_2317_ == 0)
{
v___x_2319_ = v___x_2316_;
goto v_reusejp_2318_;
}
else
{
lean_object* v_reuseFailAlloc_2320_; 
v_reuseFailAlloc_2320_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_a_2314_);
v___x_2319_ = v_reuseFailAlloc_2320_;
goto v_reusejp_2318_;
}
v_reusejp_2318_:
{
return v___x_2319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2351_, lean_object* v_mvarId_2352_, lean_object* v___y_2353_, lean_object* v___y_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lean_Meta_substVar___lam__0(v_x_2351_, v_mvarId_2352_, v___y_2353_, v___y_2354_, v___y_2355_, v___y_2356_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
lean_dec(v___y_2354_);
lean_dec_ref(v___y_2353_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2359_, lean_object* v_x_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_){
_start:
{
lean_object* v___f_2366_; lean_object* v___x_2367_; 
lean_inc(v_mvarId_2359_);
v___f_2366_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2366_, 0, v_x_2360_);
lean_closure_set(v___f_2366_, 1, v_mvarId_2359_);
v___x_2367_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2359_, v___f_2366_, v_a_2361_, v_a_2362_, v_a_2363_, v_a_2364_);
return v___x_2367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2368_, lean_object* v_x_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_){
_start:
{
lean_object* v_res_2375_; 
v_res_2375_ = l_Lean_Meta_substVar(v_mvarId_2368_, v_x_2369_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
lean_dec(v_a_2371_);
lean_dec_ref(v_a_2370_);
return v_res_2375_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; 
v___x_2377_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2378_ = l_Lean_stringToMessageData(v___x_2377_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2379_, lean_object* v_snd_2380_, uint8_t v___x_2381_, lean_object* v_fvarSubst_2382_, lean_object* v___y_2383_, lean_object* v___y_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_){
_start:
{
lean_object* v___x_2388_; 
lean_inc(v_fst_2379_);
v___x_2388_ = l_Lean_FVarId_getDecl___redArg(v_fst_2379_, v___y_2383_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_object* v_a_2389_; lean_object* v___y_2391_; lean_object* v___y_2392_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v_newType_2403_; uint8_t v_symm_2404_; lean_object* v___y_2405_; lean_object* v___y_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
lean_inc(v_a_2389_);
lean_dec_ref_known(v___x_2388_, 1);
v___x_2444_ = l_Lean_LocalDecl_type(v_a_2389_);
v___x_2445_ = l_Lean_Meta_matchEq_x3f(v___x_2444_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2445_) == 0)
{
lean_object* v_a_2446_; 
v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
lean_inc(v_a_2446_);
lean_dec_ref_known(v___x_2445_, 1);
if (lean_obj_tag(v_a_2446_) == 1)
{
lean_object* v_val_2447_; lean_object* v_snd_2448_; lean_object* v_fst_2449_; lean_object* v_snd_2450_; lean_object* v___x_2451_; 
v_val_2447_ = lean_ctor_get(v_a_2446_, 0);
lean_inc(v_val_2447_);
lean_dec_ref_known(v_a_2446_, 1);
v_snd_2448_ = lean_ctor_get(v_val_2447_, 1);
lean_inc(v_snd_2448_);
lean_dec(v_val_2447_);
v_fst_2449_ = lean_ctor_get(v_snd_2448_, 0);
lean_inc(v_fst_2449_);
v_snd_2450_ = lean_ctor_get(v_snd_2448_, 1);
lean_inc_n(v_snd_2450_, 2);
lean_dec(v_snd_2448_);
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
v___x_2451_ = lean_whnf(v_snd_2450_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; uint8_t v___x_2453_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v___x_2453_ = l_Lean_Expr_isFVar(v_a_2452_);
if (v___x_2453_ == 0)
{
lean_object* v___x_2454_; 
lean_dec(v_a_2452_);
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
lean_inc(v___y_2384_);
lean_inc_ref(v___y_2383_);
lean_inc(v_fst_2449_);
v___x_2454_ = lean_whnf(v_fst_2449_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v_a_2455_; uint8_t v___y_2457_; uint8_t v___x_2469_; 
v_a_2455_ = lean_ctor_get(v___x_2454_, 0);
lean_inc(v_a_2455_);
lean_dec_ref_known(v___x_2454_, 1);
v___x_2469_ = l_Lean_Expr_isFVar(v_a_2455_);
if (v___x_2469_ == 0)
{
lean_dec(v_a_2455_);
lean_dec(v_snd_2450_);
lean_dec(v_fst_2449_);
lean_dec(v_fvarSubst_2382_);
lean_dec(v_fst_2379_);
v___y_2391_ = v___y_2383_;
v___y_2392_ = v___y_2384_;
v___y_2393_ = v___y_2385_;
v___y_2394_ = v___y_2386_;
goto v___jp_2390_;
}
else
{
uint8_t v___x_2470_; 
v___x_2470_ = lean_expr_eqv(v_fst_2449_, v_a_2455_);
lean_dec(v_fst_2449_);
if (v___x_2470_ == 0)
{
v___y_2457_ = v___x_2469_;
goto v___jp_2456_;
}
else
{
v___y_2457_ = v___x_2453_;
goto v___jp_2456_;
}
}
v___jp_2456_:
{
if (v___y_2457_ == 0)
{
lean_object* v___x_2458_; 
lean_dec(v_a_2455_);
lean_dec(v_snd_2450_);
lean_dec(v_a_2389_);
v___x_2458_ = l_Lean_Meta_substCore(v_snd_2380_, v_fst_2379_, v___y_2457_, v_fvarSubst_2382_, v___x_2381_, v___x_2381_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v___x_2458_;
}
else
{
lean_object* v___x_2459_; 
v___x_2459_ = l_Lean_Meta_mkEq(v_a_2455_, v_snd_2450_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2459_) == 0)
{
lean_object* v_a_2460_; 
v_a_2460_ = lean_ctor_get(v___x_2459_, 0);
lean_inc(v_a_2460_);
lean_dec_ref_known(v___x_2459_, 1);
v_newType_2403_ = v_a_2460_;
v_symm_2404_ = v___x_2453_;
v___y_2405_ = v___y_2383_;
v___y_2406_ = v___y_2384_;
v___y_2407_ = v___y_2385_;
v___y_2408_ = v___y_2386_;
goto v___jp_2402_;
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_a_2389_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v_fvarSubst_2382_);
lean_dec(v_snd_2380_);
lean_dec(v_fst_2379_);
v_a_2461_ = lean_ctor_get(v___x_2459_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2459_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2459_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2459_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec(v_snd_2450_);
lean_dec(v_fst_2449_);
lean_dec(v_a_2389_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v_fvarSubst_2382_);
lean_dec(v_snd_2380_);
lean_dec(v_fst_2379_);
v_a_2471_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2454_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2454_);
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
else
{
uint8_t v___x_2479_; 
v___x_2479_ = lean_expr_eqv(v_snd_2450_, v_a_2452_);
lean_dec(v_snd_2450_);
if (v___x_2479_ == 0)
{
if (v___x_2453_ == 0)
{
lean_object* v___x_2480_; 
lean_dec(v_a_2452_);
lean_dec(v_fst_2449_);
lean_dec(v_a_2389_);
v___x_2480_ = l_Lean_Meta_substCore(v_snd_2380_, v_fst_2379_, v___x_2381_, v_fvarSubst_2382_, v___x_2381_, v___x_2381_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v___x_2480_;
}
else
{
lean_object* v___x_2481_; 
v___x_2481_ = l_Lean_Meta_mkEq(v_fst_2449_, v_a_2452_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
if (lean_obj_tag(v___x_2481_) == 0)
{
lean_object* v_a_2482_; 
v_a_2482_ = lean_ctor_get(v___x_2481_, 0);
lean_inc(v_a_2482_);
lean_dec_ref_known(v___x_2481_, 1);
v_newType_2403_ = v_a_2482_;
v_symm_2404_ = v___x_2381_;
v___y_2405_ = v___y_2383_;
v___y_2406_ = v___y_2384_;
v___y_2407_ = v___y_2385_;
v___y_2408_ = v___y_2386_;
goto v___jp_2402_;
}
else
{
lean_object* v_a_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_2490_; 
lean_dec(v_a_2389_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v_fvarSubst_2382_);
lean_dec(v_snd_2380_);
lean_dec(v_fst_2379_);
v_a_2483_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2485_ = v___x_2481_;
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_a_2483_);
lean_dec(v___x_2481_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_2490_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v___x_2488_; 
if (v_isShared_2486_ == 0)
{
v___x_2488_ = v___x_2485_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_a_2483_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
else
{
lean_object* v___x_2491_; 
lean_dec(v_a_2452_);
lean_dec(v_fst_2449_);
lean_dec(v_a_2389_);
v___x_2491_ = l_Lean_Meta_substCore(v_snd_2380_, v_fst_2379_, v___x_2381_, v_fvarSubst_2382_, v___x_2381_, v___x_2381_, v___y_2383_, v___y_2384_, v___y_2385_, v___y_2386_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
return v___x_2491_;
}
}
}
else
{
lean_object* v_a_2492_; lean_object* v___x_2494_; uint8_t v_isShared_2495_; uint8_t v_isSharedCheck_2499_; 
lean_dec(v_snd_2450_);
lean_dec(v_fst_2449_);
lean_dec(v_a_2389_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v_fvarSubst_2382_);
lean_dec(v_snd_2380_);
lean_dec(v_fst_2379_);
v_a_2492_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2499_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2499_ == 0)
{
v___x_2494_ = v___x_2451_;
v_isShared_2495_ = v_isSharedCheck_2499_;
goto v_resetjp_2493_;
}
else
{
lean_inc(v_a_2492_);
lean_dec(v___x_2451_);
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
}
else
{
lean_dec(v_a_2446_);
lean_dec(v_fvarSubst_2382_);
lean_dec(v_fst_2379_);
v___y_2391_ = v___y_2383_;
v___y_2392_ = v___y_2384_;
v___y_2393_ = v___y_2385_;
v___y_2394_ = v___y_2386_;
goto v___jp_2390_;
}
}
else
{
lean_object* v_a_2500_; lean_object* v___x_2502_; uint8_t v_isShared_2503_; uint8_t v_isSharedCheck_2507_; 
lean_dec(v_a_2389_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v_fvarSubst_2382_);
lean_dec(v_snd_2380_);
lean_dec(v_fst_2379_);
v_a_2500_ = lean_ctor_get(v___x_2445_, 0);
v_isSharedCheck_2507_ = !lean_is_exclusive(v___x_2445_);
if (v_isSharedCheck_2507_ == 0)
{
v___x_2502_ = v___x_2445_;
v_isShared_2503_ = v_isSharedCheck_2507_;
goto v_resetjp_2501_;
}
else
{
lean_inc(v_a_2500_);
lean_dec(v___x_2445_);
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
v___jp_2390_:
{
lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2395_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2396_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2397_ = l_Lean_LocalDecl_type(v_a_2389_);
lean_dec(v_a_2389_);
v___x_2398_ = l_Lean_indentExpr(v___x_2397_);
v___x_2399_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2399_, 0, v___x_2396_);
lean_ctor_set(v___x_2399_, 1, v___x_2398_);
v___x_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2400_, 0, v___x_2399_);
v___x_2401_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2395_, v_snd_2380_, v___x_2400_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
lean_dec(v___y_2392_);
lean_dec_ref(v___y_2391_);
return v___x_2401_;
}
v___jp_2402_:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = l_Lean_LocalDecl_userName(v_a_2389_);
lean_dec(v_a_2389_);
lean_inc(v_fst_2379_);
v___x_2410_ = l_Lean_mkFVar(v_fst_2379_);
v___x_2411_ = l_Lean_MVarId_assert(v_snd_2380_, v___x_2409_, v_newType_2403_, v___x_2410_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; lean_object* v___x_2413_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
v___x_2413_ = l_Lean_Meta_intro1Core(v_a_2412_, v___x_2381_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v_fst_2415_; lean_object* v_snd_2416_; lean_object* v___x_2417_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 1);
v_fst_2415_ = lean_ctor_get(v_a_2414_, 0);
lean_inc(v_fst_2415_);
v_snd_2416_ = lean_ctor_get(v_a_2414_, 1);
lean_inc(v_snd_2416_);
lean_dec(v_a_2414_);
v___x_2417_ = l_Lean_MVarId_clear(v_snd_2416_, v_fst_2379_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
if (lean_obj_tag(v___x_2417_) == 0)
{
lean_object* v_a_2418_; lean_object* v___x_2419_; 
v_a_2418_ = lean_ctor_get(v___x_2417_, 0);
lean_inc(v_a_2418_);
lean_dec_ref_known(v___x_2417_, 1);
v___x_2419_ = l_Lean_Meta_substCore(v_a_2418_, v_fst_2415_, v_symm_2404_, v_fvarSubst_2382_, v___x_2381_, v___x_2381_, v___y_2405_, v___y_2406_, v___y_2407_, v___y_2408_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
return v___x_2419_;
}
else
{
lean_object* v_a_2420_; lean_object* v___x_2422_; uint8_t v_isShared_2423_; uint8_t v_isSharedCheck_2427_; 
lean_dec(v_fst_2415_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v_fvarSubst_2382_);
v_a_2420_ = lean_ctor_get(v___x_2417_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2417_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2417_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2417_);
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
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v_fvarSubst_2382_);
lean_dec(v_fst_2379_);
v_a_2428_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2413_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2413_);
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
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v___y_2406_);
lean_dec_ref(v___y_2405_);
lean_dec(v_fvarSubst_2382_);
lean_dec(v_fst_2379_);
v_a_2436_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2411_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2411_);
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
}
else
{
lean_object* v_a_2508_; lean_object* v___x_2510_; uint8_t v_isShared_2511_; uint8_t v_isSharedCheck_2515_; 
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v___y_2384_);
lean_dec_ref(v___y_2383_);
lean_dec(v_fvarSubst_2382_);
lean_dec(v_snd_2380_);
lean_dec(v_fst_2379_);
v_a_2508_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2515_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2515_ == 0)
{
v___x_2510_ = v___x_2388_;
v_isShared_2511_ = v_isSharedCheck_2515_;
goto v_resetjp_2509_;
}
else
{
lean_inc(v_a_2508_);
lean_dec(v___x_2388_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2516_, lean_object* v_snd_2517_, lean_object* v___x_2518_, lean_object* v_fvarSubst_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
uint8_t v___x_1434__boxed_2525_; lean_object* v_res_2526_; 
v___x_1434__boxed_2525_ = lean_unbox(v___x_2518_);
v_res_2526_ = l_Lean_Meta_substEq___lam__0(v_fst_2516_, v_snd_2517_, v___x_1434__boxed_2525_, v_fvarSubst_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
return v_res_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2527_, lean_object* v_hFVarId_2528_, lean_object* v_fvarSubst_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
uint8_t v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = 1;
v___x_2536_ = l_Lean_Meta_heqToEq(v_mvarId_2527_, v_hFVarId_2528_, v___x_2535_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v_fst_2538_; lean_object* v_snd_2539_; lean_object* v___x_2540_; lean_object* v___f_2541_; lean_object* v___x_2542_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v_fst_2538_ = lean_ctor_get(v_a_2537_, 0);
lean_inc(v_fst_2538_);
v_snd_2539_ = lean_ctor_get(v_a_2537_, 1);
lean_inc_n(v_snd_2539_, 2);
lean_dec(v_a_2537_);
v___x_2540_ = lean_box(v___x_2535_);
v___f_2541_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2541_, 0, v_fst_2538_);
lean_closure_set(v___f_2541_, 1, v_snd_2539_);
lean_closure_set(v___f_2541_, 2, v___x_2540_);
lean_closure_set(v___f_2541_, 3, v_fvarSubst_2529_);
v___x_2542_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_snd_2539_, v___f_2541_, v_a_2530_, v_a_2531_, v_a_2532_, v_a_2533_);
return v___x_2542_;
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_dec(v_fvarSubst_2529_);
v_a_2543_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2536_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2536_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2551_, lean_object* v_hFVarId_2552_, lean_object* v_fvarSubst_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v_res_2559_; 
v_res_2559_ = l_Lean_Meta_substEq(v_mvarId_2551_, v_hFVarId_2552_, v_fvarSubst_2553_, v_a_2554_, v_a_2555_, v_a_2556_, v_a_2557_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
lean_dec(v_a_2555_);
lean_dec_ref(v_a_2554_);
return v_res_2559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2560_, lean_object* v_mvarId_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
lean_object* v___x_2567_; 
lean_inc(v_h_2560_);
v___x_2567_ = l_Lean_FVarId_getType___redArg(v_h_2560_, v___y_2562_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2567_) == 0)
{
lean_object* v_a_2568_; lean_object* v___x_2569_; 
v_a_2568_ = lean_ctor_get(v___x_2567_, 0);
lean_inc_n(v_a_2568_, 2);
lean_dec_ref_known(v___x_2567_, 1);
v___x_2569_ = l_Lean_Meta_matchEq_x3f(v_a_2568_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
if (lean_obj_tag(v_a_2570_) == 0)
{
lean_object* v___x_2571_; 
v___x_2571_ = l_Lean_Meta_matchHEq_x3f(v_a_2568_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
if (lean_obj_tag(v_a_2572_) == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Meta_substVar(v_mvarId_2561_, v_h_2560_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
return v___x_2573_;
}
else
{
uint8_t v___x_2574_; lean_object* v___x_2575_; 
lean_dec_ref_known(v_a_2572_, 1);
v___x_2574_ = 1;
lean_inc(v_h_2560_);
lean_inc(v_mvarId_2561_);
v___x_2575_ = l_Lean_Meta_heqToEq(v_mvarId_2561_, v_h_2560_, v___x_2574_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v_fst_2577_; lean_object* v_snd_2578_; uint8_t v___x_2579_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v_fst_2577_ = lean_ctor_get(v_a_2576_, 0);
lean_inc(v_fst_2577_);
v_snd_2578_ = lean_ctor_get(v_a_2576_, 1);
lean_inc(v_snd_2578_);
lean_dec(v_a_2576_);
v___x_2579_ = l_Lean_instBEqMVarId_beq(v_mvarId_2561_, v_snd_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; 
lean_dec(v_mvarId_2561_);
lean_dec(v_h_2560_);
v___x_2580_ = l_Lean_Meta_subst(v_snd_2578_, v_fst_2577_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
return v___x_2580_;
}
else
{
lean_object* v___x_2581_; 
lean_dec(v_snd_2578_);
lean_dec(v_fst_2577_);
v___x_2581_ = l_Lean_Meta_substVar(v_mvarId_2561_, v_h_2560_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
return v___x_2581_;
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_dec(v_mvarId_2561_);
lean_dec(v_h_2560_);
v_a_2582_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2575_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2575_);
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
}
else
{
lean_object* v_a_2590_; lean_object* v___x_2592_; uint8_t v_isShared_2593_; uint8_t v_isSharedCheck_2597_; 
lean_dec(v_mvarId_2561_);
lean_dec(v_h_2560_);
v_a_2590_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2597_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2597_ == 0)
{
v___x_2592_ = v___x_2571_;
v_isShared_2593_ = v_isSharedCheck_2597_;
goto v_resetjp_2591_;
}
else
{
lean_inc(v_a_2590_);
lean_dec(v___x_2571_);
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
else
{
lean_object* v___x_2598_; lean_object* v___x_2599_; 
lean_dec_ref_known(v_a_2570_, 1);
lean_dec(v_a_2568_);
v___x_2598_ = lean_box(0);
v___x_2599_ = l_Lean_Meta_substEq(v_mvarId_2561_, v_h_2560_, v___x_2598_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2599_) == 0)
{
lean_object* v_a_2600_; lean_object* v___x_2602_; uint8_t v_isShared_2603_; uint8_t v_isSharedCheck_2608_; 
v_a_2600_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2608_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2608_ == 0)
{
v___x_2602_ = v___x_2599_;
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
else
{
lean_inc(v_a_2600_);
lean_dec(v___x_2599_);
v___x_2602_ = lean_box(0);
v_isShared_2603_ = v_isSharedCheck_2608_;
goto v_resetjp_2601_;
}
v_resetjp_2601_:
{
lean_object* v_snd_2604_; lean_object* v___x_2606_; 
v_snd_2604_ = lean_ctor_get(v_a_2600_, 1);
lean_inc(v_snd_2604_);
lean_dec(v_a_2600_);
if (v_isShared_2603_ == 0)
{
lean_ctor_set(v___x_2602_, 0, v_snd_2604_);
v___x_2606_ = v___x_2602_;
goto v_reusejp_2605_;
}
else
{
lean_object* v_reuseFailAlloc_2607_; 
v_reuseFailAlloc_2607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2607_, 0, v_snd_2604_);
v___x_2606_ = v_reuseFailAlloc_2607_;
goto v_reusejp_2605_;
}
v_reusejp_2605_:
{
return v___x_2606_;
}
}
}
else
{
lean_object* v_a_2609_; lean_object* v___x_2611_; uint8_t v_isShared_2612_; uint8_t v_isSharedCheck_2616_; 
v_a_2609_ = lean_ctor_get(v___x_2599_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2599_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2611_ = v___x_2599_;
v_isShared_2612_ = v_isSharedCheck_2616_;
goto v_resetjp_2610_;
}
else
{
lean_inc(v_a_2609_);
lean_dec(v___x_2599_);
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
}
else
{
lean_object* v_a_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2624_; 
lean_dec(v_a_2568_);
lean_dec(v_mvarId_2561_);
lean_dec(v_h_2560_);
v_a_2617_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2624_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2624_ == 0)
{
v___x_2619_ = v___x_2569_;
v_isShared_2620_ = v_isSharedCheck_2624_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_a_2617_);
lean_dec(v___x_2569_);
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
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec(v_mvarId_2561_);
lean_dec(v_h_2560_);
v_a_2625_ = lean_ctor_get(v___x_2567_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2567_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2567_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2567_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2633_, lean_object* v_mvarId_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_){
_start:
{
lean_object* v_res_2640_; 
v_res_2640_ = l_Lean_Meta_subst___lam__0(v_h_2633_, v_mvarId_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
lean_dec(v___y_2636_);
lean_dec_ref(v___y_2635_);
return v_res_2640_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2641_, lean_object* v_h_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_){
_start:
{
lean_object* v___f_2648_; lean_object* v___x_2649_; 
lean_inc(v_mvarId_2641_);
v___f_2648_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2648_, 0, v_h_2642_);
lean_closure_set(v___f_2648_, 1, v_mvarId_2641_);
v___x_2649_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2641_, v___f_2648_, v_a_2643_, v_a_2644_, v_a_2645_, v_a_2646_);
return v___x_2649_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2650_, lean_object* v_h_2651_, lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_){
_start:
{
lean_object* v_res_2657_; 
v_res_2657_ = l_Lean_Meta_subst(v_mvarId_2650_, v_h_2651_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
lean_dec(v_a_2653_);
lean_dec_ref(v_a_2652_);
return v_res_2657_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_){
_start:
{
lean_object* v___x_2664_; 
v___x_2664_ = l_Lean_Meta_saveState___redArg(v___y_2660_, v___y_2662_);
if (lean_obj_tag(v___x_2664_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2666_; 
v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v___x_2664_, 1);
lean_inc(v___y_2662_);
lean_inc_ref(v___y_2661_);
lean_inc(v___y_2660_);
lean_inc_ref(v___y_2659_);
v___x_2666_ = lean_apply_5(v_x_2658_, v___y_2659_, v___y_2660_, v___y_2661_, v___y_2662_, lean_box(0));
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_dec(v_a_2665_);
return v___x_2666_;
}
else
{
lean_object* v_a_2667_; uint8_t v___y_2669_; uint8_t v___x_2687_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
v___x_2687_ = l_Lean_Exception_isInterrupt(v_a_2667_);
if (v___x_2687_ == 0)
{
uint8_t v___x_2688_; 
lean_inc(v_a_2667_);
v___x_2688_ = l_Lean_Exception_isRuntime(v_a_2667_);
v___y_2669_ = v___x_2688_;
goto v___jp_2668_;
}
else
{
v___y_2669_ = v___x_2687_;
goto v___jp_2668_;
}
v___jp_2668_:
{
if (v___y_2669_ == 0)
{
lean_object* v___x_2670_; 
lean_dec_ref_known(v___x_2666_, 1);
v___x_2670_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2665_, v___y_2660_, v___y_2662_);
lean_dec(v_a_2665_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_object* v___x_2672_; uint8_t v_isShared_2673_; uint8_t v_isSharedCheck_2677_; 
v_isSharedCheck_2677_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2677_ == 0)
{
lean_object* v_unused_2678_; 
v_unused_2678_ = lean_ctor_get(v___x_2670_, 0);
lean_dec(v_unused_2678_);
v___x_2672_ = v___x_2670_;
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
else
{
lean_dec(v___x_2670_);
v___x_2672_ = lean_box(0);
v_isShared_2673_ = v_isSharedCheck_2677_;
goto v_resetjp_2671_;
}
v_resetjp_2671_:
{
lean_object* v___x_2675_; 
if (v_isShared_2673_ == 0)
{
lean_ctor_set_tag(v___x_2672_, 1);
lean_ctor_set(v___x_2672_, 0, v_a_2667_);
v___x_2675_ = v___x_2672_;
goto v_reusejp_2674_;
}
else
{
lean_object* v_reuseFailAlloc_2676_; 
v_reuseFailAlloc_2676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2676_, 0, v_a_2667_);
v___x_2675_ = v_reuseFailAlloc_2676_;
goto v_reusejp_2674_;
}
v_reusejp_2674_:
{
return v___x_2675_;
}
}
}
else
{
lean_object* v_a_2679_; lean_object* v___x_2681_; uint8_t v_isShared_2682_; uint8_t v_isSharedCheck_2686_; 
lean_dec(v_a_2667_);
v_a_2679_ = lean_ctor_get(v___x_2670_, 0);
v_isSharedCheck_2686_ = !lean_is_exclusive(v___x_2670_);
if (v_isSharedCheck_2686_ == 0)
{
v___x_2681_ = v___x_2670_;
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
else
{
lean_inc(v_a_2679_);
lean_dec(v___x_2670_);
v___x_2681_ = lean_box(0);
v_isShared_2682_ = v_isSharedCheck_2686_;
goto v_resetjp_2680_;
}
v_resetjp_2680_:
{
lean_object* v___x_2684_; 
if (v_isShared_2682_ == 0)
{
v___x_2684_ = v___x_2681_;
goto v_reusejp_2683_;
}
else
{
lean_object* v_reuseFailAlloc_2685_; 
v_reuseFailAlloc_2685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_a_2679_);
v___x_2684_ = v_reuseFailAlloc_2685_;
goto v_reusejp_2683_;
}
v_reusejp_2683_:
{
return v___x_2684_;
}
}
}
}
else
{
lean_dec(v_a_2667_);
lean_dec(v_a_2665_);
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v___x_2691_; uint8_t v_isShared_2692_; uint8_t v_isSharedCheck_2696_; 
lean_dec_ref(v_x_2658_);
v_a_2689_ = lean_ctor_get(v___x_2664_, 0);
v_isSharedCheck_2696_ = !lean_is_exclusive(v___x_2664_);
if (v_isSharedCheck_2696_ == 0)
{
v___x_2691_ = v___x_2664_;
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
else
{
lean_inc(v_a_2689_);
lean_dec(v___x_2664_);
v___x_2691_ = lean_box(0);
v_isShared_2692_ = v_isSharedCheck_2696_;
goto v_resetjp_2690_;
}
v_resetjp_2690_:
{
lean_object* v___x_2694_; 
if (v_isShared_2692_ == 0)
{
v___x_2694_ = v___x_2691_;
goto v_reusejp_2693_;
}
else
{
lean_object* v_reuseFailAlloc_2695_; 
v_reuseFailAlloc_2695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2695_, 0, v_a_2689_);
v___x_2694_ = v_reuseFailAlloc_2695_;
goto v_reusejp_2693_;
}
v_reusejp_2693_:
{
return v___x_2694_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2697_, lean_object* v___y_2698_, lean_object* v___y_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_){
_start:
{
lean_object* v_res_2703_; 
v_res_2703_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
lean_dec(v___y_2699_);
lean_dec_ref(v___y_2698_);
return v_res_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2704_, lean_object* v_x_2705_, lean_object* v___y_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2705_, v___y_2706_, v___y_2707_, v___y_2708_, v___y_2709_);
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2712_, lean_object* v_x_2713_, lean_object* v___y_2714_, lean_object* v___y_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2712_, v_x_2713_, v___y_2714_, v___y_2715_, v___y_2716_, v___y_2717_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
lean_dec(v___y_2715_);
lean_dec_ref(v___y_2714_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
lean_object* v_ref_2726_; lean_object* v___x_2727_; lean_object* v_a_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2736_; 
v_ref_2726_ = lean_ctor_get(v___y_2723_, 5);
v___x_2727_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msg_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
v_a_2728_ = lean_ctor_get(v___x_2727_, 0);
v_isSharedCheck_2736_ = !lean_is_exclusive(v___x_2727_);
if (v_isSharedCheck_2736_ == 0)
{
v___x_2730_ = v___x_2727_;
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_a_2728_);
lean_dec(v___x_2727_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2736_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; lean_object* v___x_2734_; 
lean_inc(v_ref_2726_);
v___x_2732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2732_, 0, v_ref_2726_);
lean_ctor_set(v___x_2732_, 1, v_a_2728_);
if (v_isShared_2731_ == 0)
{
lean_ctor_set_tag(v___x_2730_, 1);
lean_ctor_set(v___x_2730_, 0, v___x_2732_);
v___x_2734_ = v___x_2730_;
goto v_reusejp_2733_;
}
else
{
lean_object* v_reuseFailAlloc_2735_; 
v_reuseFailAlloc_2735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___x_2732_);
v___x_2734_ = v_reuseFailAlloc_2735_;
goto v_reusejp_2733_;
}
v_reusejp_2733_:
{
return v___x_2734_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2737_, lean_object* v___y_2738_, lean_object* v___y_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
lean_dec(v___y_2739_);
lean_dec_ref(v___y_2738_);
return v_res_2743_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2745_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2746_ = l_Lean_stringToMessageData(v___x_2745_);
return v___x_2746_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2749_ = l_Lean_stringToMessageData(v___x_2748_);
return v___x_2749_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2752_ = l_Lean_stringToMessageData(v___x_2751_);
return v___x_2752_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; 
v___x_2754_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2755_ = l_Lean_stringToMessageData(v___x_2754_);
return v___x_2755_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2758_ = l_Lean_stringToMessageData(v___x_2757_);
return v___x_2758_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2772_ = l_Lean_stringToMessageData(v___x_2771_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2781_, uint8_t v_substLHS_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_){
_start:
{
lean_object* v___x_2788_; 
lean_inc(v_mvarId_2781_);
v___x_2788_ = l_Lean_MVarId_getType_x27(v_mvarId_2781_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
lean_inc(v_a_2789_);
lean_dec_ref_known(v___x_2788_, 1);
if (lean_obj_tag(v_a_2789_) == 7)
{
lean_object* v_binderType_2793_; lean_object* v_body_2794_; uint8_t v___x_2795_; lean_object* v___y_2797_; lean_object* v___y_2798_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2883_; lean_object* v___y_2884_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v_fst_2930_; lean_object* v_fst_2931_; lean_object* v_fst_2932_; lean_object* v_snd_2933_; lean_object* v___y_2934_; lean_object* v___y_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; 
v_binderType_2793_ = lean_ctor_get(v_a_2789_, 1);
lean_inc_ref(v_binderType_2793_);
v_body_2794_ = lean_ctor_get(v_a_2789_, 2);
lean_inc_ref(v_body_2794_);
lean_dec_ref_known(v_a_2789_, 3);
v___x_2795_ = l_Lean_Expr_hasLooseBVars(v_body_2794_);
if (v___x_2795_ == 0)
{
lean_object* v___x_2949_; 
v___x_2949_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2793_, v___y_2784_);
if (lean_obj_tag(v___x_2949_) == 0)
{
lean_object* v_a_2950_; lean_object* v___y_2952_; lean_object* v___y_2953_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___x_2966_; uint8_t v___x_2967_; 
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
lean_inc(v_a_2950_);
lean_dec_ref_known(v___x_2949_, 1);
v___x_2966_ = l_Lean_Expr_cleanupAnnotations(v_a_2950_);
v___x_2967_ = l_Lean_Expr_isApp(v___x_2966_);
if (v___x_2967_ == 0)
{
lean_dec_ref(v___x_2966_);
lean_dec_ref(v_body_2794_);
lean_dec(v_mvarId_2781_);
v___y_2952_ = v___y_2783_;
v___y_2953_ = v___y_2784_;
v___y_2954_ = v___y_2785_;
v___y_2955_ = v___y_2786_;
goto v___jp_2951_;
}
else
{
lean_object* v_arg_2968_; lean_object* v___x_2969_; uint8_t v___x_2970_; 
v_arg_2968_ = lean_ctor_get(v___x_2966_, 1);
lean_inc_ref(v_arg_2968_);
v___x_2969_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2966_);
v___x_2970_ = l_Lean_Expr_isApp(v___x_2969_);
if (v___x_2970_ == 0)
{
lean_dec_ref(v___x_2969_);
lean_dec_ref(v_arg_2968_);
lean_dec_ref(v_body_2794_);
lean_dec(v_mvarId_2781_);
v___y_2952_ = v___y_2783_;
v___y_2953_ = v___y_2784_;
v___y_2954_ = v___y_2785_;
v___y_2955_ = v___y_2786_;
goto v___jp_2951_;
}
else
{
lean_object* v_arg_2971_; lean_object* v___x_2972_; uint8_t v___x_2973_; 
v_arg_2971_ = lean_ctor_get(v___x_2969_, 1);
lean_inc_ref(v_arg_2971_);
v___x_2972_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2969_);
v___x_2973_ = l_Lean_Expr_isApp(v___x_2972_);
if (v___x_2973_ == 0)
{
lean_dec_ref(v___x_2972_);
lean_dec_ref(v_arg_2971_);
lean_dec_ref(v_arg_2968_);
lean_dec_ref(v_body_2794_);
lean_dec(v_mvarId_2781_);
v___y_2952_ = v___y_2783_;
v___y_2953_ = v___y_2784_;
v___y_2954_ = v___y_2785_;
v___y_2955_ = v___y_2786_;
goto v___jp_2951_;
}
else
{
lean_object* v_arg_2974_; lean_object* v___x_2975_; lean_object* v___x_2976_; uint8_t v___x_2977_; 
v_arg_2974_ = lean_ctor_get(v___x_2972_, 1);
lean_inc_ref(v_arg_2974_);
v___x_2975_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2972_);
v___x_2976_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_2977_ = l_Lean_Expr_isConstOf(v___x_2975_, v___x_2976_);
if (v___x_2977_ == 0)
{
uint8_t v___x_2978_; 
v___x_2978_ = l_Lean_Expr_isApp(v___x_2975_);
if (v___x_2978_ == 0)
{
lean_dec_ref(v___x_2975_);
lean_dec_ref(v_arg_2974_);
lean_dec_ref(v_arg_2971_);
lean_dec_ref(v_arg_2968_);
lean_dec_ref(v_body_2794_);
lean_dec(v_mvarId_2781_);
v___y_2952_ = v___y_2783_;
v___y_2953_ = v___y_2784_;
v___y_2954_ = v___y_2785_;
v___y_2955_ = v___y_2786_;
goto v___jp_2951_;
}
else
{
lean_object* v_arg_2979_; lean_object* v___y_2981_; lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___x_2987_; lean_object* v___x_2988_; uint8_t v___x_2989_; 
v_arg_2979_ = lean_ctor_get(v___x_2975_, 1);
lean_inc_ref(v_arg_2979_);
v___x_2987_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2975_);
v___x_2988_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_2989_ = l_Lean_Expr_isConstOf(v___x_2987_, v___x_2988_);
lean_dec_ref(v___x_2987_);
if (v___x_2989_ == 0)
{
lean_dec_ref(v_arg_2979_);
lean_dec_ref(v_arg_2974_);
lean_dec_ref(v_arg_2971_);
lean_dec_ref(v_arg_2968_);
lean_dec_ref(v_body_2794_);
lean_dec(v_mvarId_2781_);
v___y_2952_ = v___y_2783_;
v___y_2953_ = v___y_2784_;
v___y_2954_ = v___y_2785_;
v___y_2955_ = v___y_2786_;
goto v___jp_2951_;
}
else
{
lean_object* v___x_2990_; 
lean_inc_ref(v_arg_2979_);
v___x_2990_ = l_Lean_Meta_isExprDefEq(v_arg_2979_, v_arg_2971_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v_a_2991_; uint8_t v___x_2992_; 
v_a_2991_ = lean_ctor_get(v___x_2990_, 0);
lean_inc(v_a_2991_);
lean_dec_ref_known(v___x_2990_, 1);
v___x_2992_ = lean_unbox(v_a_2991_);
lean_dec(v_a_2991_);
if (v___x_2992_ == 0)
{
lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v_a_2995_; lean_object* v___x_2997_; uint8_t v_isShared_2998_; uint8_t v_isSharedCheck_3002_; 
lean_dec_ref(v_arg_2979_);
lean_dec_ref(v_arg_2974_);
lean_dec_ref(v_arg_2968_);
lean_dec_ref(v_body_2794_);
lean_dec(v_mvarId_2781_);
v___x_2993_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_2994_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2993_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
v_a_2995_ = lean_ctor_get(v___x_2994_, 0);
v_isSharedCheck_3002_ = !lean_is_exclusive(v___x_2994_);
if (v_isSharedCheck_3002_ == 0)
{
v___x_2997_ = v___x_2994_;
v_isShared_2998_ = v_isSharedCheck_3002_;
goto v_resetjp_2996_;
}
else
{
lean_inc(v_a_2995_);
lean_dec(v___x_2994_);
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
else
{
v___y_2981_ = v___y_2783_;
v___y_2982_ = v___y_2784_;
v___y_2983_ = v___y_2785_;
v___y_2984_ = v___y_2786_;
goto v___jp_2980_;
}
}
else
{
lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec_ref(v_arg_2979_);
lean_dec_ref(v_arg_2974_);
lean_dec_ref(v_arg_2968_);
lean_dec_ref(v_body_2794_);
lean_dec(v_mvarId_2781_);
v_a_3003_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2990_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_dec(v___x_2990_);
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
}
v___jp_2980_:
{
if (v_substLHS_2782_ == 0)
{
lean_object* v___x_2985_; 
v___x_2985_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2930_ = v_arg_2979_;
v_fst_2931_ = v_arg_2974_;
v_fst_2932_ = v_arg_2968_;
v_snd_2933_ = v___x_2985_;
v___y_2934_ = v___y_2981_;
v___y_2935_ = v___y_2982_;
v___y_2936_ = v___y_2983_;
v___y_2937_ = v___y_2984_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_2986_; 
v___x_2986_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2930_ = v_arg_2979_;
v_fst_2931_ = v_arg_2968_;
v_fst_2932_ = v_arg_2974_;
v_snd_2933_ = v___x_2986_;
v___y_2934_ = v___y_2981_;
v___y_2935_ = v___y_2982_;
v___y_2936_ = v___y_2983_;
v___y_2937_ = v___y_2984_;
goto v___jp_2929_;
}
}
}
}
else
{
lean_dec_ref(v___x_2975_);
if (v_substLHS_2782_ == 0)
{
lean_object* v___x_3011_; 
v___x_3011_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2930_ = v_arg_2974_;
v_fst_2931_ = v_arg_2971_;
v_fst_2932_ = v_arg_2968_;
v_snd_2933_ = v___x_3011_;
v___y_2934_ = v___y_2783_;
v___y_2935_ = v___y_2784_;
v___y_2936_ = v___y_2785_;
v___y_2937_ = v___y_2786_;
goto v___jp_2929_;
}
else
{
lean_object* v___x_3012_; 
v___x_3012_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2930_ = v_arg_2974_;
v_fst_2931_ = v_arg_2968_;
v_fst_2932_ = v_arg_2971_;
v_snd_2933_ = v___x_3012_;
v___y_2934_ = v___y_2783_;
v___y_2935_ = v___y_2784_;
v___y_2936_ = v___y_2785_;
v___y_2937_ = v___y_2786_;
goto v___jp_2929_;
}
}
}
}
}
v___jp_2951_:
{
lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
v___x_2956_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_2957_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2956_, v___y_2952_, v___y_2953_, v___y_2954_, v___y_2955_);
v_a_2958_ = lean_ctor_get(v___x_2957_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2957_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2957_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2957_);
v___x_2960_ = lean_box(0);
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
v_resetjp_2959_:
{
lean_object* v___x_2963_; 
if (v_isShared_2961_ == 0)
{
v___x_2963_ = v___x_2960_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_a_2958_);
v___x_2963_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
return v___x_2963_;
}
}
}
}
else
{
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec_ref(v_body_2794_);
lean_dec(v_mvarId_2781_);
v_a_3013_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2949_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2949_);
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
else
{
lean_dec_ref(v_body_2794_);
lean_dec_ref(v_binderType_2793_);
lean_dec(v_mvarId_2781_);
goto v___jp_2790_;
}
v___jp_2796_:
{
lean_object* v___x_2808_; lean_object* v___x_2809_; uint8_t v___x_2810_; uint8_t v___x_2811_; lean_object* v___x_2812_; 
v___x_2808_ = lean_mk_empty_array_with_capacity(v___y_2800_);
lean_inc_ref(v___x_2808_);
v___x_2809_ = lean_array_push(v___x_2808_, v___y_2799_);
v___x_2810_ = 1;
v___x_2811_ = 1;
v___x_2812_ = l_Lean_Meta_mkLambdaFVars(v___x_2809_, v_body_2794_, v___x_2795_, v___x_2810_, v___x_2795_, v___x_2810_, v___x_2811_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
lean_dec_ref(v___x_2809_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
lean_inc(v___y_2797_);
v___x_2814_ = l_Lean_MVarId_getTag(v___y_2797_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
lean_inc_ref(v___y_2801_);
v___x_2816_ = lean_array_push(v___x_2808_, v___y_2801_);
lean_inc(v_a_2813_);
v___x_2817_ = l_Lean_Expr_beta(v_a_2813_, v___x_2816_);
lean_inc_ref(v___x_2817_);
v___x_2818_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2817_, v_a_2815_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2818_) == 0)
{
lean_object* v_a_2819_; lean_object* v___x_2820_; 
v_a_2819_ = lean_ctor_get(v___x_2818_, 0);
lean_inc(v_a_2819_);
lean_dec_ref_known(v___x_2818_, 1);
v___x_2820_ = l_Lean_Meta_getLevel(v___x_2817_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
lean_inc_ref(v___y_2798_);
v___x_2822_ = l_Lean_Meta_getLevel(v___y_2798_, v___y_2804_, v___y_2805_, v___y_2806_, v___y_2807_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2840_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
v___x_2824_ = lean_box(0);
v___x_2825_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2825_, 0, v_a_2823_);
lean_ctor_set(v___x_2825_, 1, v___x_2824_);
v___x_2826_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2826_, 0, v_a_2821_);
lean_ctor_set(v___x_2826_, 1, v___x_2825_);
lean_inc(v___y_2803_);
v___x_2827_ = l_Lean_mkConst(v___y_2803_, v___x_2826_);
lean_inc(v_a_2819_);
lean_inc_ref(v___y_2801_);
v___x_2828_ = l_Lean_mkApp4(v___x_2827_, v___y_2798_, v___y_2801_, v_a_2813_, v_a_2819_);
v___x_2829_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v___y_2797_, v___x_2828_, v___y_2805_);
v_isSharedCheck_2840_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2840_ == 0)
{
lean_object* v_unused_2841_; 
v_unused_2841_ = lean_ctor_get(v___x_2829_, 0);
lean_dec(v_unused_2841_);
v___x_2831_ = v___x_2829_;
v_isShared_2832_ = v_isSharedCheck_2840_;
goto v_resetjp_2830_;
}
else
{
lean_dec(v___x_2829_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2840_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2838_; 
v___x_2833_ = l_Lean_Meta_FVarSubst_empty;
v___x_2834_ = l_Lean_Meta_FVarSubst_insert(v___x_2833_, v___y_2802_, v___y_2801_);
v___x_2835_ = l_Lean_Expr_mvarId_x21(v_a_2819_);
lean_dec(v_a_2819_);
v___x_2836_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2834_);
lean_ctor_set(v___x_2836_, 1, v___x_2835_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 0, v___x_2836_);
v___x_2838_ = v___x_2831_;
goto v_reusejp_2837_;
}
else
{
lean_object* v_reuseFailAlloc_2839_; 
v_reuseFailAlloc_2839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2839_, 0, v___x_2836_);
v___x_2838_ = v_reuseFailAlloc_2839_;
goto v_reusejp_2837_;
}
v_reusejp_2837_:
{
return v___x_2838_;
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v_a_2821_);
lean_dec(v_a_2819_);
lean_dec(v_a_2813_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
v_a_2842_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2822_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2822_);
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
lean_dec(v_a_2819_);
lean_dec(v_a_2813_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
v_a_2850_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2820_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2820_);
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
lean_dec_ref(v___x_2817_);
lean_dec(v_a_2813_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
v_a_2858_ = lean_ctor_get(v___x_2818_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2818_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2818_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2818_);
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
lean_dec(v_a_2813_);
lean_dec_ref(v___x_2808_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
v_a_2866_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2814_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2814_);
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
lean_dec_ref(v___x_2808_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec_ref(v___y_2798_);
lean_dec(v___y_2797_);
v_a_2874_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2881_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2881_ == 0)
{
v___x_2876_ = v___x_2812_;
v_isShared_2877_ = v_isSharedCheck_2881_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_a_2874_);
lean_dec(v___x_2812_);
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
v___jp_2882_:
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2891_ = l_Lean_Expr_fvarId_x21(v___y_2884_);
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_mk_empty_array_with_capacity(v___x_2892_);
lean_inc(v___x_2891_);
v___x_2894_ = lean_array_push(v___x_2893_, v___x_2891_);
v___x_2895_ = l_Lean_MVarId_revert(v_mvarId_2781_, v___x_2894_, v___x_2795_, v___x_2795_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v_fst_2897_; lean_object* v_snd_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2920_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v_fst_2897_ = lean_ctor_get(v_a_2896_, 0);
v_snd_2898_ = lean_ctor_get(v_a_2896_, 1);
v_isSharedCheck_2920_ = !lean_is_exclusive(v_a_2896_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2900_ = v_a_2896_;
v_isShared_2901_ = v_isSharedCheck_2920_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_snd_2898_);
lean_inc(v_fst_2897_);
lean_dec(v_a_2896_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2920_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2902_; uint8_t v___x_2903_; 
v___x_2902_ = lean_array_get_size(v_fst_2897_);
lean_dec(v_fst_2897_);
v___x_2903_ = lean_nat_dec_eq(v___x_2902_, v___x_2892_);
if (v___x_2903_ == 0)
{
lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2907_; 
lean_dec(v_snd_2898_);
lean_dec(v___x_2891_);
lean_dec_ref(v___y_2885_);
lean_dec_ref(v___y_2883_);
lean_dec_ref(v_body_2794_);
v___x_2904_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2905_ = l_Lean_MessageData_ofExpr(v___y_2884_);
if (v_isShared_2901_ == 0)
{
lean_ctor_set_tag(v___x_2900_, 7);
lean_ctor_set(v___x_2900_, 1, v___x_2905_);
lean_ctor_set(v___x_2900_, 0, v___x_2904_);
v___x_2907_ = v___x_2900_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v___x_2904_);
lean_ctor_set(v_reuseFailAlloc_2919_, 1, v___x_2905_);
v___x_2907_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
v___x_2908_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2907_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2909_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
v_a_2911_ = lean_ctor_get(v___x_2910_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2910_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2910_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2910_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_a_2911_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
}
else
{
lean_del_object(v___x_2900_);
v___y_2797_ = v_snd_2898_;
v___y_2798_ = v___y_2883_;
v___y_2799_ = v___y_2884_;
v___y_2800_ = v___x_2892_;
v___y_2801_ = v___y_2885_;
v___y_2802_ = v___x_2891_;
v___y_2803_ = v___y_2886_;
v___y_2804_ = v___y_2887_;
v___y_2805_ = v___y_2888_;
v___y_2806_ = v___y_2889_;
v___y_2807_ = v___y_2890_;
goto v___jp_2796_;
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v___x_2891_);
lean_dec_ref(v___y_2885_);
lean_dec_ref(v___y_2884_);
lean_dec_ref(v___y_2883_);
lean_dec_ref(v_body_2794_);
v_a_2921_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2895_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2895_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
v___jp_2929_:
{
uint8_t v___x_2938_; 
v___x_2938_ = l_Lean_Expr_isFVar(v_fst_2932_);
if (v___x_2938_ == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v_a_2941_; lean_object* v___x_2943_; uint8_t v_isShared_2944_; uint8_t v_isSharedCheck_2948_; 
lean_dec_ref(v_fst_2932_);
lean_dec_ref(v_fst_2931_);
lean_dec_ref(v_fst_2930_);
lean_dec_ref(v_body_2794_);
lean_dec(v_mvarId_2781_);
v___x_2939_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2940_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2939_, v___y_2934_, v___y_2935_, v___y_2936_, v___y_2937_);
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
else
{
v___y_2883_ = v_fst_2930_;
v___y_2884_ = v_fst_2932_;
v___y_2885_ = v_fst_2931_;
v___y_2886_ = v_snd_2933_;
v___y_2887_ = v___y_2934_;
v___y_2888_ = v___y_2935_;
v___y_2889_ = v___y_2936_;
v___y_2890_ = v___y_2937_;
goto v___jp_2882_;
}
}
}
else
{
lean_dec(v_a_2789_);
lean_dec(v_mvarId_2781_);
goto v___jp_2790_;
}
v___jp_2790_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; 
v___x_2791_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2792_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2791_, v___y_2783_, v___y_2784_, v___y_2785_, v___y_2786_);
return v___x_2792_;
}
}
else
{
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_dec(v_mvarId_2781_);
v_a_3021_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2788_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2788_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object* v_mvarId_3029_, lean_object* v_substLHS_3030_, lean_object* v___y_3031_, lean_object* v___y_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_){
_start:
{
uint8_t v_substLHS_boxed_3036_; lean_object* v_res_3037_; 
v_substLHS_boxed_3036_ = lean_unbox(v_substLHS_3030_);
v_res_3037_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_3029_, v_substLHS_boxed_3036_, v___y_3031_, v___y_3032_, v___y_3033_, v___y_3034_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
lean_dec(v___y_3032_);
lean_dec_ref(v___y_3031_);
return v_res_3037_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3038_, lean_object* v_i_3039_, lean_object* v_k_3040_){
_start:
{
lean_object* v___x_3041_; uint8_t v___x_3042_; 
v___x_3041_ = lean_array_get_size(v_keys_3038_);
v___x_3042_ = lean_nat_dec_lt(v_i_3039_, v___x_3041_);
if (v___x_3042_ == 0)
{
lean_dec(v_i_3039_);
return v___x_3042_;
}
else
{
lean_object* v_k_x27_3043_; uint8_t v___x_3044_; 
v_k_x27_3043_ = lean_array_fget_borrowed(v_keys_3038_, v_i_3039_);
v___x_3044_ = l_Lean_instBEqMVarId_beq(v_k_3040_, v_k_x27_3043_);
if (v___x_3044_ == 0)
{
lean_object* v___x_3045_; lean_object* v___x_3046_; 
v___x_3045_ = lean_unsigned_to_nat(1u);
v___x_3046_ = lean_nat_add(v_i_3039_, v___x_3045_);
lean_dec(v_i_3039_);
v_i_3039_ = v___x_3046_;
goto _start;
}
else
{
lean_dec(v_i_3039_);
return v___x_3042_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3048_, lean_object* v_i_3049_, lean_object* v_k_3050_){
_start:
{
uint8_t v_res_3051_; lean_object* v_r_3052_; 
v_res_3051_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3048_, v_i_3049_, v_k_3050_);
lean_dec(v_k_3050_);
lean_dec_ref(v_keys_3048_);
v_r_3052_ = lean_box(v_res_3051_);
return v_r_3052_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3053_, size_t v_x_3054_, lean_object* v_x_3055_){
_start:
{
if (lean_obj_tag(v_x_3053_) == 0)
{
lean_object* v_es_3056_; lean_object* v___x_3057_; size_t v___x_3058_; size_t v___x_3059_; lean_object* v_j_3060_; lean_object* v___x_3061_; 
v_es_3056_ = lean_ctor_get(v_x_3053_, 0);
v___x_3057_ = lean_box(2);
v___x_3058_ = ((size_t)31ULL);
v___x_3059_ = lean_usize_land(v_x_3054_, v___x_3058_);
v_j_3060_ = lean_usize_to_nat(v___x_3059_);
v___x_3061_ = lean_array_get_borrowed(v___x_3057_, v_es_3056_, v_j_3060_);
lean_dec(v_j_3060_);
switch(lean_obj_tag(v___x_3061_))
{
case 0:
{
lean_object* v_key_3062_; uint8_t v___x_3063_; 
v_key_3062_ = lean_ctor_get(v___x_3061_, 0);
v___x_3063_ = l_Lean_instBEqMVarId_beq(v_x_3055_, v_key_3062_);
return v___x_3063_;
}
case 1:
{
lean_object* v_node_3064_; size_t v___x_3065_; size_t v___x_3066_; 
v_node_3064_ = lean_ctor_get(v___x_3061_, 0);
v___x_3065_ = ((size_t)5ULL);
v___x_3066_ = lean_usize_shift_right(v_x_3054_, v___x_3065_);
v_x_3053_ = v_node_3064_;
v_x_3054_ = v___x_3066_;
goto _start;
}
default: 
{
uint8_t v___x_3068_; 
v___x_3068_ = 0;
return v___x_3068_;
}
}
}
else
{
lean_object* v_ks_3069_; lean_object* v___x_3070_; uint8_t v___x_3071_; 
v_ks_3069_ = lean_ctor_get(v_x_3053_, 0);
v___x_3070_ = lean_unsigned_to_nat(0u);
v___x_3071_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3069_, v___x_3070_, v_x_3055_);
return v___x_3071_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3072_, lean_object* v_x_3073_, lean_object* v_x_3074_){
_start:
{
size_t v_x_10567__boxed_3075_; uint8_t v_res_3076_; lean_object* v_r_3077_; 
v_x_10567__boxed_3075_ = lean_unbox_usize(v_x_3073_);
lean_dec(v_x_3073_);
v_res_3076_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3072_, v_x_10567__boxed_3075_, v_x_3074_);
lean_dec(v_x_3074_);
lean_dec_ref(v_x_3072_);
v_r_3077_ = lean_box(v_res_3076_);
return v_r_3077_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3078_, lean_object* v_x_3079_){
_start:
{
uint64_t v___x_3080_; size_t v___x_3081_; uint8_t v___x_3082_; 
v___x_3080_ = l_Lean_instHashableMVarId_hash(v_x_3079_);
v___x_3081_ = lean_uint64_to_usize(v___x_3080_);
v___x_3082_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3078_, v___x_3081_, v_x_3079_);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3083_, lean_object* v_x_3084_){
_start:
{
uint8_t v_res_3085_; lean_object* v_r_3086_; 
v_res_3085_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3083_, v_x_3084_);
lean_dec(v_x_3084_);
lean_dec_ref(v_x_3083_);
v_r_3086_ = lean_box(v_res_3085_);
return v_r_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3087_, lean_object* v___y_3088_){
_start:
{
lean_object* v___x_3090_; lean_object* v_mctx_3091_; lean_object* v_eAssignment_3092_; uint8_t v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
v___x_3090_ = lean_st_ref_get(v___y_3088_);
v_mctx_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc_ref(v_mctx_3091_);
lean_dec(v___x_3090_);
v_eAssignment_3092_ = lean_ctor_get(v_mctx_3091_, 8);
lean_inc_ref(v_eAssignment_3092_);
lean_dec_ref(v_mctx_3091_);
v___x_3093_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3092_, v_mvarId_3087_);
lean_dec_ref(v_eAssignment_3092_);
v___x_3094_ = lean_box(v___x_3093_);
v___x_3095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_){
_start:
{
lean_object* v_res_3099_; 
v_res_3099_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3096_, v___y_3097_);
lean_dec(v___y_3097_);
lean_dec(v_mvarId_3096_);
return v_res_3099_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3101_; lean_object* v___x_3102_; 
v___x_3101_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3102_ = l_Lean_stringToMessageData(v___x_3101_);
return v___x_3102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3103_, uint8_t v___y_3104_, lean_object* v_____r_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_){
_start:
{
lean_object* v___y_3112_; lean_object* v___y_3113_; lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___x_3147_; lean_object* v_a_3148_; uint8_t v___x_3149_; 
v___x_3147_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3103_, v___y_3107_);
v_a_3148_ = lean_ctor_get(v___x_3147_, 0);
lean_inc(v_a_3148_);
lean_dec_ref(v___x_3147_);
v___x_3149_ = lean_unbox(v_a_3148_);
lean_dec(v_a_3148_);
if (v___x_3149_ == 0)
{
v___y_3112_ = v___y_3106_;
v___y_3113_ = v___y_3107_;
v___y_3114_ = v___y_3108_;
v___y_3115_ = v___y_3109_;
goto v___jp_3111_;
}
else
{
lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v_a_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3159_; 
lean_dec(v_mvarId_3103_);
v___x_3150_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3151_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3150_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_);
v_a_3152_ = lean_ctor_get(v___x_3151_, 0);
v_isSharedCheck_3159_ = !lean_is_exclusive(v___x_3151_);
if (v_isSharedCheck_3159_ == 0)
{
v___x_3154_ = v___x_3151_;
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_a_3152_);
lean_dec(v___x_3151_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3159_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v___x_3157_; 
if (v_isShared_3155_ == 0)
{
v___x_3157_ = v___x_3154_;
goto v_reusejp_3156_;
}
else
{
lean_object* v_reuseFailAlloc_3158_; 
v_reuseFailAlloc_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3158_, 0, v_a_3152_);
v___x_3157_ = v_reuseFailAlloc_3158_;
goto v_reusejp_3156_;
}
v_reusejp_3156_:
{
return v___x_3157_;
}
}
}
v___jp_3111_:
{
lean_object* v___x_3116_; 
v___x_3116_ = l_Lean_Meta_intro1Core(v_mvarId_3103_, v___y_3104_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
if (lean_obj_tag(v___x_3116_) == 0)
{
lean_object* v_a_3117_; lean_object* v_fst_3118_; lean_object* v_snd_3119_; lean_object* v___x_3120_; lean_object* v___x_3121_; 
v_a_3117_ = lean_ctor_get(v___x_3116_, 0);
lean_inc(v_a_3117_);
lean_dec_ref_known(v___x_3116_, 1);
v_fst_3118_ = lean_ctor_get(v_a_3117_, 0);
lean_inc(v_fst_3118_);
v_snd_3119_ = lean_ctor_get(v_a_3117_, 1);
lean_inc(v_snd_3119_);
lean_dec(v_a_3117_);
v___x_3120_ = lean_box(0);
v___x_3121_ = l_Lean_Meta_substEq(v_snd_3119_, v_fst_3118_, v___x_3120_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
if (lean_obj_tag(v___x_3121_) == 0)
{
lean_object* v_a_3122_; lean_object* v___x_3124_; uint8_t v_isShared_3125_; uint8_t v_isSharedCheck_3130_; 
v_a_3122_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3130_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3130_ == 0)
{
v___x_3124_ = v___x_3121_;
v_isShared_3125_ = v_isSharedCheck_3130_;
goto v_resetjp_3123_;
}
else
{
lean_inc(v_a_3122_);
lean_dec(v___x_3121_);
v___x_3124_ = lean_box(0);
v_isShared_3125_ = v_isSharedCheck_3130_;
goto v_resetjp_3123_;
}
v_resetjp_3123_:
{
lean_object* v___x_3126_; lean_object* v___x_3128_; 
v___x_3126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3126_, 0, v_a_3122_);
if (v_isShared_3125_ == 0)
{
lean_ctor_set(v___x_3124_, 0, v___x_3126_);
v___x_3128_ = v___x_3124_;
goto v_reusejp_3127_;
}
else
{
lean_object* v_reuseFailAlloc_3129_; 
v_reuseFailAlloc_3129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3129_, 0, v___x_3126_);
v___x_3128_ = v_reuseFailAlloc_3129_;
goto v_reusejp_3127_;
}
v_reusejp_3127_:
{
return v___x_3128_;
}
}
}
else
{
lean_object* v_a_3131_; lean_object* v___x_3133_; uint8_t v_isShared_3134_; uint8_t v_isSharedCheck_3138_; 
v_a_3131_ = lean_ctor_get(v___x_3121_, 0);
v_isSharedCheck_3138_ = !lean_is_exclusive(v___x_3121_);
if (v_isSharedCheck_3138_ == 0)
{
v___x_3133_ = v___x_3121_;
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
else
{
lean_inc(v_a_3131_);
lean_dec(v___x_3121_);
v___x_3133_ = lean_box(0);
v_isShared_3134_ = v_isSharedCheck_3138_;
goto v_resetjp_3132_;
}
v_resetjp_3132_:
{
lean_object* v___x_3136_; 
if (v_isShared_3134_ == 0)
{
v___x_3136_ = v___x_3133_;
goto v_reusejp_3135_;
}
else
{
lean_object* v_reuseFailAlloc_3137_; 
v_reuseFailAlloc_3137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3137_, 0, v_a_3131_);
v___x_3136_ = v_reuseFailAlloc_3137_;
goto v_reusejp_3135_;
}
v_reusejp_3135_:
{
return v___x_3136_;
}
}
}
}
else
{
lean_object* v_a_3139_; lean_object* v___x_3141_; uint8_t v_isShared_3142_; uint8_t v_isSharedCheck_3146_; 
v_a_3139_ = lean_ctor_get(v___x_3116_, 0);
v_isSharedCheck_3146_ = !lean_is_exclusive(v___x_3116_);
if (v_isSharedCheck_3146_ == 0)
{
v___x_3141_ = v___x_3116_;
v_isShared_3142_ = v_isSharedCheck_3146_;
goto v_resetjp_3140_;
}
else
{
lean_inc(v_a_3139_);
lean_dec(v___x_3116_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3160_, lean_object* v___y_3161_, lean_object* v_____r_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_){
_start:
{
uint8_t v___y_10639__boxed_3168_; lean_object* v_res_3169_; 
v___y_10639__boxed_3168_ = lean_unbox(v___y_3161_);
v_res_3169_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3160_, v___y_10639__boxed_3168_, v_____r_3162_, v___y_3163_, v___y_3164_, v___y_3165_, v___y_3166_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
return v_res_3169_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__2(void){
_start:
{
lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; 
v___x_3173_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3174_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
v___x_3175_ = l_Lean_Name_append(v___x_3174_, v___x_3173_);
return v___x_3175_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__4(void){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__3));
v___x_3178_ = l_Lean_stringToMessageData(v___x_3177_);
return v___x_3178_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__6(void){
_start:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; 
v___x_3180_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__5));
v___x_3181_ = l_Lean_stringToMessageData(v___x_3180_);
return v___x_3181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3182_, uint8_t v_substLHS_3183_, lean_object* v_a_3184_, lean_object* v_a_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v___y_3190_; lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
lean_inc(v_mvarId_3182_);
v___x_3209_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3182_, v___x_3208_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_);
if (lean_obj_tag(v___x_3209_) == 0)
{
lean_object* v___x_3210_; lean_object* v___f_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
lean_dec_ref_known(v___x_3209_, 1);
v___x_3210_ = lean_box(v_substLHS_3183_);
lean_inc_n(v_mvarId_3182_, 2);
v___f_3211_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3211_, 0, v_mvarId_3182_);
lean_closure_set(v___f_3211_, 1, v___x_3210_);
v___x_3212_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed), 8, 3);
lean_closure_set(v___x_3212_, 0, lean_box(0));
lean_closure_set(v___x_3212_, 1, v_mvarId_3182_);
lean_closure_set(v___x_3212_, 2, v___f_3211_);
v___x_3213_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3212_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_);
if (lean_obj_tag(v___x_3213_) == 0)
{
lean_dec(v_mvarId_3182_);
return v___x_3213_;
}
else
{
lean_object* v_a_3214_; lean_object* v___y_3216_; uint8_t v___y_3220_; uint8_t v___x_3254_; 
v_a_3214_ = lean_ctor_get(v___x_3213_, 0);
lean_inc(v_a_3214_);
v___x_3254_ = l_Lean_Exception_isInterrupt(v_a_3214_);
if (v___x_3254_ == 0)
{
uint8_t v___x_3255_; 
lean_inc(v_a_3214_);
v___x_3255_ = l_Lean_Exception_isRuntime(v_a_3214_);
v___y_3220_ = v___x_3255_;
goto v___jp_3219_;
}
else
{
v___y_3220_ = v___x_3254_;
goto v___jp_3219_;
}
v___jp_3215_:
{
lean_object* v___x_3217_; lean_object* v___x_3218_; 
v___x_3217_ = lean_box(0);
lean_inc(v_a_3187_);
lean_inc_ref(v_a_3186_);
lean_inc(v_a_3185_);
lean_inc_ref(v_a_3184_);
v___x_3218_ = lean_apply_6(v___y_3216_, v___x_3217_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_, lean_box(0));
v___y_3190_ = v___x_3218_;
goto v___jp_3189_;
}
v___jp_3219_:
{
if (v___y_3220_ == 0)
{
lean_object* v___x_3222_; uint8_t v_isShared_3223_; uint8_t v_isSharedCheck_3252_; 
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3213_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; 
v_unused_3253_ = lean_ctor_get(v___x_3213_, 0);
lean_dec(v_unused_3253_);
v___x_3222_ = v___x_3213_;
v_isShared_3223_ = v_isSharedCheck_3252_;
goto v_resetjp_3221_;
}
else
{
lean_dec(v___x_3213_);
v___x_3222_ = lean_box(0);
v_isShared_3223_ = v_isSharedCheck_3252_;
goto v_resetjp_3221_;
}
v_resetjp_3221_:
{
lean_object* v_options_3224_; lean_object* v_inheritedTraceOptions_3225_; uint8_t v_hasTrace_3226_; lean_object* v___x_3227_; lean_object* v___f_3228_; 
v_options_3224_ = lean_ctor_get(v_a_3186_, 2);
v_inheritedTraceOptions_3225_ = lean_ctor_get(v_a_3186_, 13);
v_hasTrace_3226_ = lean_ctor_get_uint8(v_options_3224_, sizeof(void*)*1);
v___x_3227_ = lean_box(v___y_3220_);
lean_inc(v_mvarId_3182_);
v___f_3228_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3228_, 0, v_mvarId_3182_);
lean_closure_set(v___f_3228_, 1, v___x_3227_);
if (v_hasTrace_3226_ == 0)
{
lean_del_object(v___x_3222_);
lean_dec(v_a_3214_);
lean_dec(v_mvarId_3182_);
v___y_3216_ = v___f_3228_;
goto v___jp_3215_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; uint8_t v___x_3231_; 
v___x_3229_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3230_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__2, &l_Lean_Meta_introSubstEq___closed__2_once, _init_l_Lean_Meta_introSubstEq___closed__2);
v___x_3231_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3225_, v_options_3224_, v___x_3230_);
if (v___x_3231_ == 0)
{
lean_del_object(v___x_3222_);
lean_dec(v_a_3214_);
lean_dec(v_mvarId_3182_);
v___y_3216_ = v___f_3228_;
goto v___jp_3215_;
}
else
{
lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3238_; 
lean_dec_ref(v___f_3228_);
v___x_3232_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__4, &l_Lean_Meta_introSubstEq___closed__4_once, _init_l_Lean_Meta_introSubstEq___closed__4);
v___x_3233_ = l_Lean_Exception_toMessageData(v_a_3214_);
v___x_3234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3232_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__6, &l_Lean_Meta_introSubstEq___closed__6_once, _init_l_Lean_Meta_introSubstEq___closed__6);
v___x_3236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3234_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
lean_inc(v_mvarId_3182_);
if (v_isShared_3223_ == 0)
{
lean_ctor_set(v___x_3222_, 0, v_mvarId_3182_);
v___x_3238_ = v___x_3222_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_mvarId_3182_);
v___x_3238_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; 
v___x_3239_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3239_, 0, v___x_3236_);
lean_ctor_set(v___x_3239_, 1, v___x_3238_);
v___x_3240_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_3229_, v___x_3239_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v_a_3241_; lean_object* v___x_3242_; 
v_a_3241_ = lean_ctor_get(v___x_3240_, 0);
lean_inc(v_a_3241_);
lean_dec_ref_known(v___x_3240_, 1);
v___x_3242_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3182_, v___y_3220_, v_a_3241_, v_a_3184_, v_a_3185_, v_a_3186_, v_a_3187_);
v___y_3190_ = v___x_3242_;
goto v___jp_3189_;
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_dec(v_mvarId_3182_);
v_a_3243_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3240_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3240_);
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
}
}
else
{
lean_dec(v_a_3214_);
lean_dec(v_mvarId_3182_);
return v___x_3213_;
}
}
}
}
else
{
lean_object* v_a_3256_; lean_object* v___x_3258_; uint8_t v_isShared_3259_; uint8_t v_isSharedCheck_3263_; 
lean_dec(v_mvarId_3182_);
v_a_3256_ = lean_ctor_get(v___x_3209_, 0);
v_isSharedCheck_3263_ = !lean_is_exclusive(v___x_3209_);
if (v_isSharedCheck_3263_ == 0)
{
v___x_3258_ = v___x_3209_;
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
else
{
lean_inc(v_a_3256_);
lean_dec(v___x_3209_);
v___x_3258_ = lean_box(0);
v_isShared_3259_ = v_isSharedCheck_3263_;
goto v_resetjp_3257_;
}
v_resetjp_3257_:
{
lean_object* v___x_3261_; 
if (v_isShared_3259_ == 0)
{
v___x_3261_ = v___x_3258_;
goto v_reusejp_3260_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
v___x_3261_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3260_;
}
v_reusejp_3260_:
{
return v___x_3261_;
}
}
}
v___jp_3189_:
{
if (lean_obj_tag(v___y_3190_) == 0)
{
lean_object* v_a_3191_; lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3199_; 
v_a_3191_ = lean_ctor_get(v___y_3190_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___y_3190_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3193_ = v___y_3190_;
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
else
{
lean_inc(v_a_3191_);
lean_dec(v___y_3190_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3199_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v_a_3195_; lean_object* v___x_3197_; 
v_a_3195_ = lean_ctor_get(v_a_3191_, 0);
lean_inc(v_a_3195_);
lean_dec(v_a_3191_);
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v_a_3195_);
v___x_3197_ = v___x_3193_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3195_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
v_a_3200_ = lean_ctor_get(v___y_3190_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___y_3190_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___y_3190_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___y_3190_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object* v_mvarId_3264_, lean_object* v_substLHS_3265_, lean_object* v_a_3266_, lean_object* v_a_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_){
_start:
{
uint8_t v_substLHS_boxed_3271_; lean_object* v_res_3272_; 
v_substLHS_boxed_3271_ = lean_unbox(v_substLHS_3265_);
v_res_3272_ = l_Lean_Meta_introSubstEq(v_mvarId_3264_, v_substLHS_boxed_3271_, v_a_3266_, v_a_3267_, v_a_3268_, v_a_3269_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
lean_dec(v_a_3267_);
lean_dec_ref(v_a_3266_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object* v_00_u03b1_3273_, lean_object* v_msg_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
return v___x_3280_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object* v_00_u03b1_3281_, lean_object* v_msg_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_){
_start:
{
lean_object* v_res_3288_; 
v_res_3288_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(v_00_u03b1_3281_, v_msg_3282_, v___y_3283_, v___y_3284_, v___y_3285_, v___y_3286_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
lean_dec(v___y_3284_);
lean_dec_ref(v___y_3283_);
return v_res_3288_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object* v_mvarId_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_){
_start:
{
lean_object* v___x_3295_; 
v___x_3295_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3289_, v___y_3291_);
return v___x_3295_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object* v_mvarId_3296_, lean_object* v___y_3297_, lean_object* v___y_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3296_, v___y_3297_, v___y_3298_, v___y_3299_, v___y_3300_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v___y_3298_);
lean_dec_ref(v___y_3297_);
lean_dec(v_mvarId_3296_);
return v_res_3302_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object* v_00_u03b2_3303_, lean_object* v_x_3304_, lean_object* v_x_3305_){
_start:
{
uint8_t v___x_3306_; 
v___x_3306_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3304_, v_x_3305_);
return v___x_3306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3307_, lean_object* v_x_3308_, lean_object* v_x_3309_){
_start:
{
uint8_t v_res_3310_; lean_object* v_r_3311_; 
v_res_3310_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(v_00_u03b2_3307_, v_x_3308_, v_x_3309_);
lean_dec(v_x_3309_);
lean_dec_ref(v_x_3308_);
v_r_3311_ = lean_box(v_res_3310_);
return v_r_3311_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_3312_, lean_object* v_x_3313_, size_t v_x_3314_, lean_object* v_x_3315_){
_start:
{
uint8_t v___x_3316_; 
v___x_3316_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3313_, v_x_3314_, v_x_3315_);
return v___x_3316_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3317_, lean_object* v_x_3318_, lean_object* v_x_3319_, lean_object* v_x_3320_){
_start:
{
size_t v_x_11003__boxed_3321_; uint8_t v_res_3322_; lean_object* v_r_3323_; 
v_x_11003__boxed_3321_ = lean_unbox_usize(v_x_3319_);
lean_dec(v_x_3319_);
v_res_3322_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3317_, v_x_3318_, v_x_11003__boxed_3321_, v_x_3320_);
lean_dec(v_x_3320_);
lean_dec_ref(v_x_3318_);
v_r_3323_ = lean_box(v_res_3322_);
return v_r_3323_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3324_, lean_object* v_keys_3325_, lean_object* v_vals_3326_, lean_object* v_heq_3327_, lean_object* v_i_3328_, lean_object* v_k_3329_){
_start:
{
uint8_t v___x_3330_; 
v___x_3330_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3325_, v_i_3328_, v_k_3329_);
return v___x_3330_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3331_, lean_object* v_keys_3332_, lean_object* v_vals_3333_, lean_object* v_heq_3334_, lean_object* v_i_3335_, lean_object* v_k_3336_){
_start:
{
uint8_t v_res_3337_; lean_object* v_r_3338_; 
v_res_3337_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(v_00_u03b2_3331_, v_keys_3332_, v_vals_3333_, v_heq_3334_, v_i_3335_, v_k_3336_);
lean_dec(v_k_3336_);
lean_dec_ref(v_vals_3333_);
lean_dec_ref(v_keys_3332_);
v_r_3338_ = lean_box(v_res_3337_);
return v_r_3338_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* v_x_3339_, lean_object* v___y_3340_, lean_object* v___y_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_){
_start:
{
lean_object* v___x_3345_; 
v___x_3345_ = l_Lean_Meta_saveState___redArg(v___y_3341_, v___y_3343_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
lean_inc(v___y_3343_);
lean_inc_ref(v___y_3342_);
lean_inc(v___y_3341_);
lean_inc_ref(v___y_3340_);
v___x_3347_ = lean_apply_5(v_x_3339_, v___y_3340_, v___y_3341_, v___y_3342_, v___y_3343_, lean_box(0));
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3350_; uint8_t v_isShared_3351_; uint8_t v_isSharedCheck_3356_; 
lean_dec(v_a_3346_);
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3356_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3356_ == 0)
{
v___x_3350_ = v___x_3347_;
v_isShared_3351_ = v_isSharedCheck_3356_;
goto v_resetjp_3349_;
}
else
{
lean_inc(v_a_3348_);
lean_dec(v___x_3347_);
v___x_3350_ = lean_box(0);
v_isShared_3351_ = v_isSharedCheck_3356_;
goto v_resetjp_3349_;
}
v_resetjp_3349_:
{
lean_object* v___x_3352_; lean_object* v___x_3354_; 
v___x_3352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3352_, 0, v_a_3348_);
if (v_isShared_3351_ == 0)
{
lean_ctor_set(v___x_3350_, 0, v___x_3352_);
v___x_3354_ = v___x_3350_;
goto v_reusejp_3353_;
}
else
{
lean_object* v_reuseFailAlloc_3355_; 
v_reuseFailAlloc_3355_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3355_, 0, v___x_3352_);
v___x_3354_ = v_reuseFailAlloc_3355_;
goto v_reusejp_3353_;
}
v_reusejp_3353_:
{
return v___x_3354_;
}
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3386_; 
v_a_3357_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3386_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3386_ == 0)
{
v___x_3359_ = v___x_3347_;
v_isShared_3360_ = v_isSharedCheck_3386_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3347_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3386_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
uint8_t v___y_3362_; uint8_t v___x_3384_; 
v___x_3384_ = l_Lean_Exception_isInterrupt(v_a_3357_);
if (v___x_3384_ == 0)
{
uint8_t v___x_3385_; 
lean_inc(v_a_3357_);
v___x_3385_ = l_Lean_Exception_isRuntime(v_a_3357_);
v___y_3362_ = v___x_3385_;
goto v___jp_3361_;
}
else
{
v___y_3362_ = v___x_3384_;
goto v___jp_3361_;
}
v___jp_3361_:
{
if (v___y_3362_ == 0)
{
lean_object* v___x_3363_; 
lean_del_object(v___x_3359_);
lean_dec(v_a_3357_);
v___x_3363_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3346_, v___y_3341_, v___y_3343_);
lean_dec(v_a_3346_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3371_; 
v_isSharedCheck_3371_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3371_ == 0)
{
lean_object* v_unused_3372_; 
v_unused_3372_ = lean_ctor_get(v___x_3363_, 0);
lean_dec(v_unused_3372_);
v___x_3365_ = v___x_3363_;
v_isShared_3366_ = v_isSharedCheck_3371_;
goto v_resetjp_3364_;
}
else
{
lean_dec(v___x_3363_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3371_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3367_ = lean_box(0);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3367_);
v___x_3369_ = v___x_3365_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3370_; 
v_reuseFailAlloc_3370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3370_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3370_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
return v___x_3369_;
}
}
}
else
{
lean_object* v_a_3373_; lean_object* v___x_3375_; uint8_t v_isShared_3376_; uint8_t v_isSharedCheck_3380_; 
v_a_3373_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3375_ = v___x_3363_;
v_isShared_3376_ = v_isSharedCheck_3380_;
goto v_resetjp_3374_;
}
else
{
lean_inc(v_a_3373_);
lean_dec(v___x_3363_);
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
else
{
lean_object* v___x_3382_; 
lean_dec(v_a_3346_);
if (v_isShared_3360_ == 0)
{
v___x_3382_ = v___x_3359_;
goto v_reusejp_3381_;
}
else
{
lean_object* v_reuseFailAlloc_3383_; 
v_reuseFailAlloc_3383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3383_, 0, v_a_3357_);
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
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v_x_3339_);
v_a_3387_ = lean_ctor_get(v___x_3345_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3345_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3345_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3345_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object* v_x_3395_, lean_object* v___y_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3395_, v___y_3396_, v___y_3397_, v___y_3398_, v___y_3399_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
lean_dec(v___y_3397_);
lean_dec_ref(v___y_3396_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object* v_00_u03b1_3402_, lean_object* v_x_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_){
_start:
{
lean_object* v___x_3409_; 
v___x_3409_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3403_, v___y_3404_, v___y_3405_, v___y_3406_, v___y_3407_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object* v_00_u03b1_3410_, lean_object* v_x_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_){
_start:
{
lean_object* v_res_3417_; 
v_res_3417_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(v_00_u03b1_3410_, v_x_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
lean_dec(v___y_3413_);
lean_dec_ref(v___y_3412_);
return v_res_3417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* v_mvarId_3418_, lean_object* v_hFVarId_3419_, lean_object* v_a_3420_, lean_object* v_a_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_){
_start:
{
lean_object* v___x_3425_; lean_object* v___x_3426_; 
v___x_3425_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___boxed), 7, 2);
lean_closure_set(v___x_3425_, 0, v_mvarId_3418_);
lean_closure_set(v___x_3425_, 1, v_hFVarId_3419_);
v___x_3426_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3425_, v_a_3420_, v_a_3421_, v_a_3422_, v_a_3423_);
return v___x_3426_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object* v_mvarId_3427_, lean_object* v_hFVarId_3428_, lean_object* v_a_3429_, lean_object* v_a_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_){
_start:
{
lean_object* v_res_3434_; 
v_res_3434_ = l_Lean_Meta_substVar_x3f(v_mvarId_3427_, v_hFVarId_3428_, v_a_3429_, v_a_3430_, v_a_3431_, v_a_3432_);
lean_dec(v_a_3432_);
lean_dec_ref(v_a_3431_);
lean_dec(v_a_3430_);
lean_dec_ref(v_a_3429_);
return v_res_3434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* v_mvarId_3435_, lean_object* v_hFVarId_3436_, lean_object* v_a_3437_, lean_object* v_a_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_){
_start:
{
lean_object* v___x_3442_; lean_object* v___x_3443_; 
v___x_3442_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 7, 2);
lean_closure_set(v___x_3442_, 0, v_mvarId_3435_);
lean_closure_set(v___x_3442_, 1, v_hFVarId_3436_);
v___x_3443_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3442_, v_a_3437_, v_a_3438_, v_a_3439_, v_a_3440_);
return v___x_3443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object* v_mvarId_3444_, lean_object* v_hFVarId_3445_, lean_object* v_a_3446_, lean_object* v_a_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_){
_start:
{
lean_object* v_res_3451_; 
v_res_3451_ = l_Lean_Meta_subst_x3f(v_mvarId_3444_, v_hFVarId_3445_, v_a_3446_, v_a_3447_, v_a_3448_, v_a_3449_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
lean_dec(v_a_3447_);
lean_dec_ref(v_a_3446_);
return v_res_3451_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* v_mvarId_3452_, lean_object* v_hFVarId_3453_, uint8_t v_symm_3454_, lean_object* v_fvarSubst_3455_, uint8_t v_clearH_3456_, uint8_t v_tryToSkip_3457_, lean_object* v_a_3458_, lean_object* v_a_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_){
_start:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3463_ = lean_box(v_symm_3454_);
v___x_3464_ = lean_box(v_clearH_3456_);
v___x_3465_ = lean_box(v_tryToSkip_3457_);
v___x_3466_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_3466_, 0, v_mvarId_3452_);
lean_closure_set(v___x_3466_, 1, v_hFVarId_3453_);
lean_closure_set(v___x_3466_, 2, v___x_3463_);
lean_closure_set(v___x_3466_, 3, v_fvarSubst_3455_);
lean_closure_set(v___x_3466_, 4, v___x_3464_);
lean_closure_set(v___x_3466_, 5, v___x_3465_);
v___x_3467_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3466_, v_a_3458_, v_a_3459_, v_a_3460_, v_a_3461_);
return v___x_3467_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* v_mvarId_3468_, lean_object* v_hFVarId_3469_, lean_object* v_symm_3470_, lean_object* v_fvarSubst_3471_, lean_object* v_clearH_3472_, lean_object* v_tryToSkip_3473_, lean_object* v_a_3474_, lean_object* v_a_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_){
_start:
{
uint8_t v_symm_boxed_3479_; uint8_t v_clearH_boxed_3480_; uint8_t v_tryToSkip_boxed_3481_; lean_object* v_res_3482_; 
v_symm_boxed_3479_ = lean_unbox(v_symm_3470_);
v_clearH_boxed_3480_ = lean_unbox(v_clearH_3472_);
v_tryToSkip_boxed_3481_ = lean_unbox(v_tryToSkip_3473_);
v_res_3482_ = l_Lean_Meta_substCore_x3f(v_mvarId_3468_, v_hFVarId_3469_, v_symm_boxed_3479_, v_fvarSubst_3471_, v_clearH_boxed_3480_, v_tryToSkip_boxed_3481_, v_a_3474_, v_a_3475_, v_a_3476_, v_a_3477_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
lean_dec(v_a_3475_);
lean_dec_ref(v_a_3474_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* v_mvarId_3483_, lean_object* v_hFVarId_3484_, lean_object* v_a_3485_, lean_object* v_a_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_){
_start:
{
lean_object* v___x_3490_; 
lean_inc(v_mvarId_3483_);
v___x_3490_ = l_Lean_Meta_substVar_x3f(v_mvarId_3483_, v_hFVarId_3484_, v_a_3485_, v_a_3486_, v_a_3487_, v_a_3488_);
if (lean_obj_tag(v___x_3490_) == 0)
{
lean_object* v_a_3491_; lean_object* v___x_3493_; uint8_t v_isShared_3494_; uint8_t v_isSharedCheck_3502_; 
v_a_3491_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3502_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3502_ == 0)
{
v___x_3493_ = v___x_3490_;
v_isShared_3494_ = v_isSharedCheck_3502_;
goto v_resetjp_3492_;
}
else
{
lean_inc(v_a_3491_);
lean_dec(v___x_3490_);
v___x_3493_ = lean_box(0);
v_isShared_3494_ = v_isSharedCheck_3502_;
goto v_resetjp_3492_;
}
v_resetjp_3492_:
{
if (lean_obj_tag(v_a_3491_) == 0)
{
lean_object* v___x_3496_; 
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v_mvarId_3483_);
v___x_3496_ = v___x_3493_;
goto v_reusejp_3495_;
}
else
{
lean_object* v_reuseFailAlloc_3497_; 
v_reuseFailAlloc_3497_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3497_, 0, v_mvarId_3483_);
v___x_3496_ = v_reuseFailAlloc_3497_;
goto v_reusejp_3495_;
}
v_reusejp_3495_:
{
return v___x_3496_;
}
}
else
{
lean_object* v_val_3498_; lean_object* v___x_3500_; 
lean_dec(v_mvarId_3483_);
v_val_3498_ = lean_ctor_get(v_a_3491_, 0);
lean_inc(v_val_3498_);
lean_dec_ref_known(v_a_3491_, 1);
if (v_isShared_3494_ == 0)
{
lean_ctor_set(v___x_3493_, 0, v_val_3498_);
v___x_3500_ = v___x_3493_;
goto v_reusejp_3499_;
}
else
{
lean_object* v_reuseFailAlloc_3501_; 
v_reuseFailAlloc_3501_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3501_, 0, v_val_3498_);
v___x_3500_ = v_reuseFailAlloc_3501_;
goto v_reusejp_3499_;
}
v_reusejp_3499_:
{
return v___x_3500_;
}
}
}
}
else
{
lean_object* v_a_3503_; lean_object* v___x_3505_; uint8_t v_isShared_3506_; uint8_t v_isSharedCheck_3510_; 
lean_dec(v_mvarId_3483_);
v_a_3503_ = lean_ctor_get(v___x_3490_, 0);
v_isSharedCheck_3510_ = !lean_is_exclusive(v___x_3490_);
if (v_isSharedCheck_3510_ == 0)
{
v___x_3505_ = v___x_3490_;
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
else
{
lean_inc(v_a_3503_);
lean_dec(v___x_3490_);
v___x_3505_ = lean_box(0);
v_isShared_3506_ = v_isSharedCheck_3510_;
goto v_resetjp_3504_;
}
v_resetjp_3504_:
{
lean_object* v___x_3508_; 
if (v_isShared_3506_ == 0)
{
v___x_3508_ = v___x_3505_;
goto v_reusejp_3507_;
}
else
{
lean_object* v_reuseFailAlloc_3509_; 
v_reuseFailAlloc_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_a_3503_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object* v_mvarId_3511_, lean_object* v_hFVarId_3512_, lean_object* v_a_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_){
_start:
{
lean_object* v_res_3518_; 
v_res_3518_ = l_Lean_Meta_trySubstVar(v_mvarId_3511_, v_hFVarId_3512_, v_a_3513_, v_a_3514_, v_a_3515_, v_a_3516_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
lean_dec(v_a_3514_);
lean_dec_ref(v_a_3513_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* v_mvarId_3519_, lean_object* v_hFVarId_3520_, lean_object* v_a_3521_, lean_object* v_a_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_){
_start:
{
lean_object* v___x_3526_; 
lean_inc(v_mvarId_3519_);
v___x_3526_ = l_Lean_Meta_subst_x3f(v_mvarId_3519_, v_hFVarId_3520_, v_a_3521_, v_a_3522_, v_a_3523_, v_a_3524_);
if (lean_obj_tag(v___x_3526_) == 0)
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3538_; 
v_a_3527_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3529_ = v___x_3526_;
v_isShared_3530_ = v_isSharedCheck_3538_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3526_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3538_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
if (lean_obj_tag(v_a_3527_) == 0)
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v_mvarId_3519_);
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_mvarId_3519_);
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
lean_object* v_val_3534_; lean_object* v___x_3536_; 
lean_dec(v_mvarId_3519_);
v_val_3534_ = lean_ctor_get(v_a_3527_, 0);
lean_inc(v_val_3534_);
lean_dec_ref_known(v_a_3527_, 1);
if (v_isShared_3530_ == 0)
{
lean_ctor_set(v___x_3529_, 0, v_val_3534_);
v___x_3536_ = v___x_3529_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_val_3534_);
v___x_3536_ = v_reuseFailAlloc_3537_;
goto v_reusejp_3535_;
}
v_reusejp_3535_:
{
return v___x_3536_;
}
}
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_mvarId_3519_);
v_a_3539_ = lean_ctor_get(v___x_3526_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3526_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3526_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3526_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object* v_mvarId_3547_, lean_object* v_hFVarId_3548_, lean_object* v_a_3549_, lean_object* v_a_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_){
_start:
{
lean_object* v_res_3554_; 
v_res_3554_ = l_Lean_Meta_trySubst(v_mvarId_3547_, v_hFVarId_3548_, v_a_3549_, v_a_3550_, v_a_3551_, v_a_3552_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
lean_dec(v_a_3550_);
lean_dec_ref(v_a_3549_);
return v_res_3554_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_mvarId_3558_, lean_object* v_as_3559_, size_t v_sz_3560_, size_t v_i_3561_, lean_object* v_b_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_){
_start:
{
uint8_t v___x_3568_; 
v___x_3568_ = lean_usize_dec_lt(v_i_3561_, v_sz_3560_);
if (v___x_3568_ == 0)
{
lean_object* v___x_3569_; 
lean_dec(v_mvarId_3558_);
v___x_3569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3569_, 0, v_b_3562_);
return v___x_3569_;
}
else
{
lean_object* v_snd_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3623_; 
v_snd_3570_ = lean_ctor_get(v_b_3562_, 1);
v_isSharedCheck_3623_ = !lean_is_exclusive(v_b_3562_);
if (v_isSharedCheck_3623_ == 0)
{
lean_object* v_unused_3624_; 
v_unused_3624_ = lean_ctor_get(v_b_3562_, 0);
lean_dec(v_unused_3624_);
v___x_3572_ = v_b_3562_;
v_isShared_3573_ = v_isSharedCheck_3623_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_snd_3570_);
lean_dec(v_b_3562_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3623_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3574_; lean_object* v_a_3576_; lean_object* v_a_3583_; 
v___x_3574_ = lean_box(0);
v_a_3583_ = lean_array_uget(v_as_3559_, v_i_3561_);
if (lean_obj_tag(v_a_3583_) == 0)
{
v_a_3576_ = v_snd_3570_;
goto v___jp_3575_;
}
else
{
lean_object* v_val_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3622_; 
v_val_3584_ = lean_ctor_get(v_a_3583_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_a_3583_);
if (v_isSharedCheck_3622_ == 0)
{
v___x_3586_ = v_a_3583_;
v_isShared_3587_ = v_isSharedCheck_3622_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_val_3584_);
lean_dec(v_a_3583_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3622_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = l_Lean_LocalDecl_fvarId(v_val_3584_);
lean_dec(v_val_3584_);
lean_inc(v_mvarId_3558_);
v___x_3589_ = l_Lean_Meta_subst_x3f(v_mvarId_3558_, v___x_3588_, v___y_3563_, v___y_3564_, v___y_3565_, v___y_3566_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3613_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3613_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3613_ == 0)
{
v___x_3592_ = v___x_3589_;
v_isShared_3593_ = v_isSharedCheck_3613_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_a_3590_);
lean_dec(v___x_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3613_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; 
v___x_3594_ = lean_box(0);
if (lean_obj_tag(v_a_3590_) == 1)
{
lean_object* v___x_3596_; 
lean_del_object(v___x_3572_);
lean_dec(v_mvarId_3558_);
lean_inc_ref(v_a_3590_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set(v___x_3586_, 0, v_a_3590_);
v___x_3596_ = v___x_3586_;
goto v_reusejp_3595_;
}
else
{
lean_object* v_reuseFailAlloc_3611_; 
v_reuseFailAlloc_3611_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3611_, 0, v_a_3590_);
v___x_3596_ = v_reuseFailAlloc_3611_;
goto v_reusejp_3595_;
}
v_reusejp_3595_:
{
lean_object* v___x_3598_; uint8_t v_isShared_3599_; uint8_t v_isSharedCheck_3609_; 
v_isSharedCheck_3609_ = !lean_is_exclusive(v_a_3590_);
if (v_isSharedCheck_3609_ == 0)
{
lean_object* v_unused_3610_; 
v_unused_3610_ = lean_ctor_get(v_a_3590_, 0);
lean_dec(v_unused_3610_);
v___x_3598_ = v_a_3590_;
v_isShared_3599_ = v_isSharedCheck_3609_;
goto v_resetjp_3597_;
}
else
{
lean_dec(v_a_3590_);
v___x_3598_ = lean_box(0);
v_isShared_3599_ = v_isSharedCheck_3609_;
goto v_resetjp_3597_;
}
v_resetjp_3597_:
{
lean_object* v___x_3600_; lean_object* v___x_3602_; 
v___x_3600_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3596_);
lean_ctor_set(v___x_3600_, 1, v___x_3594_);
if (v_isShared_3599_ == 0)
{
lean_ctor_set_tag(v___x_3598_, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3600_);
v___x_3602_ = v___x_3598_;
goto v_reusejp_3601_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3600_);
v___x_3602_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3601_;
}
v_reusejp_3601_:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3606_; 
v___x_3603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
v___x_3604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3604_, 0, v___x_3603_);
lean_ctor_set(v___x_3604_, 1, v_snd_3570_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3604_);
v___x_3606_ = v___x_3592_;
goto v_reusejp_3605_;
}
else
{
lean_object* v_reuseFailAlloc_3607_; 
v_reuseFailAlloc_3607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3607_, 0, v___x_3604_);
v___x_3606_ = v_reuseFailAlloc_3607_;
goto v_reusejp_3605_;
}
v_reusejp_3605_:
{
return v___x_3606_;
}
}
}
}
}
else
{
lean_object* v___x_3612_; 
lean_del_object(v___x_3592_);
lean_dec(v_a_3590_);
lean_del_object(v___x_3586_);
lean_dec(v_snd_3570_);
v___x_3612_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3576_ = v___x_3612_;
goto v___jp_3575_;
}
}
}
else
{
lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3621_; 
lean_del_object(v___x_3586_);
lean_del_object(v___x_3572_);
lean_dec(v_snd_3570_);
lean_dec(v_mvarId_3558_);
v_a_3614_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3621_ == 0)
{
v___x_3616_ = v___x_3589_;
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_dec(v___x_3589_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3621_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_a_3614_);
v___x_3619_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
return v___x_3619_;
}
}
}
}
}
v___jp_3575_:
{
lean_object* v___x_3578_; 
if (v_isShared_3573_ == 0)
{
lean_ctor_set(v___x_3572_, 1, v_a_3576_);
lean_ctor_set(v___x_3572_, 0, v___x_3574_);
v___x_3578_ = v___x_3572_;
goto v_reusejp_3577_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v___x_3574_);
lean_ctor_set(v_reuseFailAlloc_3582_, 1, v_a_3576_);
v___x_3578_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3577_;
}
v_reusejp_3577_:
{
size_t v___x_3579_; size_t v___x_3580_; 
v___x_3579_ = ((size_t)1ULL);
v___x_3580_ = lean_usize_add(v_i_3561_, v___x_3579_);
v_i_3561_ = v___x_3580_;
v_b_3562_ = v___x_3578_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_mvarId_3625_, lean_object* v_as_3626_, lean_object* v_sz_3627_, lean_object* v_i_3628_, lean_object* v_b_3629_, lean_object* v___y_3630_, lean_object* v___y_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_){
_start:
{
size_t v_sz_boxed_3635_; size_t v_i_boxed_3636_; lean_object* v_res_3637_; 
v_sz_boxed_3635_ = lean_unbox_usize(v_sz_3627_);
lean_dec(v_sz_3627_);
v_i_boxed_3636_ = lean_unbox_usize(v_i_3628_);
lean_dec(v_i_3628_);
v_res_3637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3625_, v_as_3626_, v_sz_boxed_3635_, v_i_boxed_3636_, v_b_3629_, v___y_3630_, v___y_3631_, v___y_3632_, v___y_3633_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec(v___y_3631_);
lean_dec_ref(v___y_3630_);
lean_dec_ref(v_as_3626_);
return v_res_3637_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object* v_mvarId_3638_, lean_object* v_as_3639_, size_t v_sz_3640_, size_t v_i_3641_, lean_object* v_b_3642_, lean_object* v___y_3643_, lean_object* v___y_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_){
_start:
{
uint8_t v___x_3648_; 
v___x_3648_ = lean_usize_dec_lt(v_i_3641_, v_sz_3640_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; 
lean_dec(v_mvarId_3638_);
v___x_3649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3649_, 0, v_b_3642_);
return v___x_3649_;
}
else
{
lean_object* v_snd_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3703_; 
v_snd_3650_ = lean_ctor_get(v_b_3642_, 1);
v_isSharedCheck_3703_ = !lean_is_exclusive(v_b_3642_);
if (v_isSharedCheck_3703_ == 0)
{
lean_object* v_unused_3704_; 
v_unused_3704_ = lean_ctor_get(v_b_3642_, 0);
lean_dec(v_unused_3704_);
v___x_3652_ = v_b_3642_;
v_isShared_3653_ = v_isSharedCheck_3703_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_snd_3650_);
lean_dec(v_b_3642_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3703_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v___x_3654_; lean_object* v_a_3656_; lean_object* v_a_3663_; 
v___x_3654_ = lean_box(0);
v_a_3663_ = lean_array_uget(v_as_3639_, v_i_3641_);
if (lean_obj_tag(v_a_3663_) == 0)
{
v_a_3656_ = v_snd_3650_;
goto v___jp_3655_;
}
else
{
lean_object* v_val_3664_; lean_object* v___x_3666_; uint8_t v_isShared_3667_; uint8_t v_isSharedCheck_3702_; 
v_val_3664_ = lean_ctor_get(v_a_3663_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v_a_3663_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3666_ = v_a_3663_;
v_isShared_3667_ = v_isSharedCheck_3702_;
goto v_resetjp_3665_;
}
else
{
lean_inc(v_val_3664_);
lean_dec(v_a_3663_);
v___x_3666_ = lean_box(0);
v_isShared_3667_ = v_isSharedCheck_3702_;
goto v_resetjp_3665_;
}
v_resetjp_3665_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = l_Lean_LocalDecl_fvarId(v_val_3664_);
lean_dec(v_val_3664_);
lean_inc(v_mvarId_3638_);
v___x_3669_ = l_Lean_Meta_subst_x3f(v_mvarId_3638_, v___x_3668_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3693_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3672_ = v___x_3669_;
v_isShared_3673_ = v_isSharedCheck_3693_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3669_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3693_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3674_; 
v___x_3674_ = lean_box(0);
if (lean_obj_tag(v_a_3670_) == 1)
{
lean_object* v___x_3676_; 
lean_del_object(v___x_3652_);
lean_dec(v_mvarId_3638_);
lean_inc_ref(v_a_3670_);
if (v_isShared_3667_ == 0)
{
lean_ctor_set(v___x_3666_, 0, v_a_3670_);
v___x_3676_ = v___x_3666_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3691_; 
v_reuseFailAlloc_3691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3670_);
v___x_3676_ = v_reuseFailAlloc_3691_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3678_; uint8_t v_isShared_3679_; uint8_t v_isSharedCheck_3689_; 
v_isSharedCheck_3689_ = !lean_is_exclusive(v_a_3670_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v_a_3670_, 0);
lean_dec(v_unused_3690_);
v___x_3678_ = v_a_3670_;
v_isShared_3679_ = v_isSharedCheck_3689_;
goto v_resetjp_3677_;
}
else
{
lean_dec(v_a_3670_);
v___x_3678_ = lean_box(0);
v_isShared_3679_ = v_isSharedCheck_3689_;
goto v_resetjp_3677_;
}
v_resetjp_3677_:
{
lean_object* v___x_3680_; lean_object* v___x_3682_; 
v___x_3680_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3676_);
lean_ctor_set(v___x_3680_, 1, v___x_3674_);
if (v_isShared_3679_ == 0)
{
lean_ctor_set_tag(v___x_3678_, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3680_);
v___x_3682_ = v___x_3678_;
goto v_reusejp_3681_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3680_);
v___x_3682_ = v_reuseFailAlloc_3688_;
goto v_reusejp_3681_;
}
v_reusejp_3681_:
{
lean_object* v___x_3683_; lean_object* v___x_3684_; lean_object* v___x_3686_; 
v___x_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3683_, 0, v___x_3682_);
v___x_3684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3684_, 0, v___x_3683_);
lean_ctor_set(v___x_3684_, 1, v_snd_3650_);
if (v_isShared_3673_ == 0)
{
lean_ctor_set(v___x_3672_, 0, v___x_3684_);
v___x_3686_ = v___x_3672_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3684_);
v___x_3686_ = v_reuseFailAlloc_3687_;
goto v_reusejp_3685_;
}
v_reusejp_3685_:
{
return v___x_3686_;
}
}
}
}
}
else
{
lean_object* v___x_3692_; 
lean_del_object(v___x_3672_);
lean_dec(v_a_3670_);
lean_del_object(v___x_3666_);
lean_dec(v_snd_3650_);
v___x_3692_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3656_ = v___x_3692_;
goto v___jp_3655_;
}
}
}
else
{
lean_object* v_a_3694_; lean_object* v___x_3696_; uint8_t v_isShared_3697_; uint8_t v_isSharedCheck_3701_; 
lean_del_object(v___x_3666_);
lean_del_object(v___x_3652_);
lean_dec(v_snd_3650_);
lean_dec(v_mvarId_3638_);
v_a_3694_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3701_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3701_ == 0)
{
v___x_3696_ = v___x_3669_;
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
else
{
lean_inc(v_a_3694_);
lean_dec(v___x_3669_);
v___x_3696_ = lean_box(0);
v_isShared_3697_ = v_isSharedCheck_3701_;
goto v_resetjp_3695_;
}
v_resetjp_3695_:
{
lean_object* v___x_3699_; 
if (v_isShared_3697_ == 0)
{
v___x_3699_ = v___x_3696_;
goto v_reusejp_3698_;
}
else
{
lean_object* v_reuseFailAlloc_3700_; 
v_reuseFailAlloc_3700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3700_, 0, v_a_3694_);
v___x_3699_ = v_reuseFailAlloc_3700_;
goto v_reusejp_3698_;
}
v_reusejp_3698_:
{
return v___x_3699_;
}
}
}
}
}
v___jp_3655_:
{
lean_object* v___x_3658_; 
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 1, v_a_3656_);
lean_ctor_set(v___x_3652_, 0, v___x_3654_);
v___x_3658_ = v___x_3652_;
goto v_reusejp_3657_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3654_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_a_3656_);
v___x_3658_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3657_;
}
v_reusejp_3657_:
{
size_t v___x_3659_; size_t v___x_3660_; lean_object* v___x_3661_; 
v___x_3659_ = ((size_t)1ULL);
v___x_3660_ = lean_usize_add(v_i_3641_, v___x_3659_);
v___x_3661_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3638_, v_as_3639_, v_sz_3640_, v___x_3660_, v___x_3658_, v___y_3643_, v___y_3644_, v___y_3645_, v___y_3646_);
return v___x_3661_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_3705_, lean_object* v_as_3706_, lean_object* v_sz_3707_, lean_object* v_i_3708_, lean_object* v_b_3709_, lean_object* v___y_3710_, lean_object* v___y_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_){
_start:
{
size_t v_sz_boxed_3715_; size_t v_i_boxed_3716_; lean_object* v_res_3717_; 
v_sz_boxed_3715_ = lean_unbox_usize(v_sz_3707_);
lean_dec(v_sz_3707_);
v_i_boxed_3716_ = lean_unbox_usize(v_i_3708_);
lean_dec(v_i_3708_);
v_res_3717_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3705_, v_as_3706_, v_sz_boxed_3715_, v_i_boxed_3716_, v_b_3709_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec(v___y_3711_);
lean_dec_ref(v___y_3710_);
lean_dec_ref(v_as_3706_);
return v_res_3717_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* v_init_3718_, lean_object* v_mvarId_3719_, lean_object* v_n_3720_, lean_object* v_b_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_){
_start:
{
if (lean_obj_tag(v_n_3720_) == 0)
{
lean_object* v_cs_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; size_t v_sz_3730_; size_t v___x_3731_; lean_object* v___x_3732_; 
v_cs_3727_ = lean_ctor_get(v_n_3720_, 0);
v___x_3728_ = lean_box(0);
v___x_3729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3729_, 0, v___x_3728_);
lean_ctor_set(v___x_3729_, 1, v_b_3721_);
v_sz_3730_ = lean_array_size(v_cs_3727_);
v___x_3731_ = ((size_t)0ULL);
v___x_3732_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3718_, v_mvarId_3719_, v_cs_3727_, v_sz_3730_, v___x_3731_, v___x_3729_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
if (lean_obj_tag(v___x_3732_) == 0)
{
lean_object* v_a_3733_; lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3747_; 
v_a_3733_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3747_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3747_ == 0)
{
v___x_3735_ = v___x_3732_;
v_isShared_3736_ = v_isSharedCheck_3747_;
goto v_resetjp_3734_;
}
else
{
lean_inc(v_a_3733_);
lean_dec(v___x_3732_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3747_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v_fst_3737_; 
v_fst_3737_ = lean_ctor_get(v_a_3733_, 0);
if (lean_obj_tag(v_fst_3737_) == 0)
{
lean_object* v_snd_3738_; lean_object* v___x_3739_; lean_object* v___x_3741_; 
v_snd_3738_ = lean_ctor_get(v_a_3733_, 1);
lean_inc(v_snd_3738_);
lean_dec(v_a_3733_);
v___x_3739_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3739_, 0, v_snd_3738_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v___x_3739_);
v___x_3741_ = v___x_3735_;
goto v_reusejp_3740_;
}
else
{
lean_object* v_reuseFailAlloc_3742_; 
v_reuseFailAlloc_3742_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3742_, 0, v___x_3739_);
v___x_3741_ = v_reuseFailAlloc_3742_;
goto v_reusejp_3740_;
}
v_reusejp_3740_:
{
return v___x_3741_;
}
}
else
{
lean_object* v_val_3743_; lean_object* v___x_3745_; 
lean_inc_ref(v_fst_3737_);
lean_dec(v_a_3733_);
v_val_3743_ = lean_ctor_get(v_fst_3737_, 0);
lean_inc(v_val_3743_);
lean_dec_ref_known(v_fst_3737_, 1);
if (v_isShared_3736_ == 0)
{
lean_ctor_set(v___x_3735_, 0, v_val_3743_);
v___x_3745_ = v___x_3735_;
goto v_reusejp_3744_;
}
else
{
lean_object* v_reuseFailAlloc_3746_; 
v_reuseFailAlloc_3746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3746_, 0, v_val_3743_);
v___x_3745_ = v_reuseFailAlloc_3746_;
goto v_reusejp_3744_;
}
v_reusejp_3744_:
{
return v___x_3745_;
}
}
}
}
else
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3755_; 
v_a_3748_ = lean_ctor_get(v___x_3732_, 0);
v_isSharedCheck_3755_ = !lean_is_exclusive(v___x_3732_);
if (v_isSharedCheck_3755_ == 0)
{
v___x_3750_ = v___x_3732_;
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3732_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3755_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v___x_3753_; 
if (v_isShared_3751_ == 0)
{
v___x_3753_ = v___x_3750_;
goto v_reusejp_3752_;
}
else
{
lean_object* v_reuseFailAlloc_3754_; 
v_reuseFailAlloc_3754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3754_, 0, v_a_3748_);
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
lean_object* v_vs_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; size_t v_sz_3759_; size_t v___x_3760_; lean_object* v___x_3761_; 
v_vs_3756_ = lean_ctor_get(v_n_3720_, 0);
v___x_3757_ = lean_box(0);
v___x_3758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3757_);
lean_ctor_set(v___x_3758_, 1, v_b_3721_);
v_sz_3759_ = lean_array_size(v_vs_3756_);
v___x_3760_ = ((size_t)0ULL);
v___x_3761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3719_, v_vs_3756_, v_sz_3759_, v___x_3760_, v___x_3758_, v___y_3722_, v___y_3723_, v___y_3724_, v___y_3725_);
if (lean_obj_tag(v___x_3761_) == 0)
{
lean_object* v_a_3762_; lean_object* v___x_3764_; uint8_t v_isShared_3765_; uint8_t v_isSharedCheck_3776_; 
v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3764_ = v___x_3761_;
v_isShared_3765_ = v_isSharedCheck_3776_;
goto v_resetjp_3763_;
}
else
{
lean_inc(v_a_3762_);
lean_dec(v___x_3761_);
v___x_3764_ = lean_box(0);
v_isShared_3765_ = v_isSharedCheck_3776_;
goto v_resetjp_3763_;
}
v_resetjp_3763_:
{
lean_object* v_fst_3766_; 
v_fst_3766_ = lean_ctor_get(v_a_3762_, 0);
if (lean_obj_tag(v_fst_3766_) == 0)
{
lean_object* v_snd_3767_; lean_object* v___x_3768_; lean_object* v___x_3770_; 
v_snd_3767_ = lean_ctor_get(v_a_3762_, 1);
lean_inc(v_snd_3767_);
lean_dec(v_a_3762_);
v___x_3768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3768_, 0, v_snd_3767_);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v___x_3768_);
v___x_3770_ = v___x_3764_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v___x_3768_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
else
{
lean_object* v_val_3772_; lean_object* v___x_3774_; 
lean_inc_ref(v_fst_3766_);
lean_dec(v_a_3762_);
v_val_3772_ = lean_ctor_get(v_fst_3766_, 0);
lean_inc(v_val_3772_);
lean_dec_ref_known(v_fst_3766_, 1);
if (v_isShared_3765_ == 0)
{
lean_ctor_set(v___x_3764_, 0, v_val_3772_);
v___x_3774_ = v___x_3764_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_val_3772_);
v___x_3774_ = v_reuseFailAlloc_3775_;
goto v_reusejp_3773_;
}
v_reusejp_3773_:
{
return v___x_3774_;
}
}
}
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
v_a_3777_ = lean_ctor_get(v___x_3761_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3761_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3761_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3761_);
v___x_3779_ = lean_box(0);
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
v_resetjp_3778_:
{
lean_object* v___x_3782_; 
if (v_isShared_3780_ == 0)
{
v___x_3782_ = v___x_3779_;
goto v_reusejp_3781_;
}
else
{
lean_object* v_reuseFailAlloc_3783_; 
v_reuseFailAlloc_3783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3783_, 0, v_a_3777_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_init_3785_, lean_object* v_mvarId_3786_, lean_object* v_as_3787_, size_t v_sz_3788_, size_t v_i_3789_, lean_object* v_b_3790_, lean_object* v___y_3791_, lean_object* v___y_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_){
_start:
{
uint8_t v___x_3796_; 
v___x_3796_ = lean_usize_dec_lt(v_i_3789_, v_sz_3788_);
if (v___x_3796_ == 0)
{
lean_object* v___x_3797_; 
lean_dec(v_mvarId_3786_);
v___x_3797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3797_, 0, v_b_3790_);
return v___x_3797_;
}
else
{
lean_object* v_snd_3798_; lean_object* v___x_3800_; uint8_t v_isShared_3801_; uint8_t v_isSharedCheck_3832_; 
v_snd_3798_ = lean_ctor_get(v_b_3790_, 1);
v_isSharedCheck_3832_ = !lean_is_exclusive(v_b_3790_);
if (v_isSharedCheck_3832_ == 0)
{
lean_object* v_unused_3833_; 
v_unused_3833_ = lean_ctor_get(v_b_3790_, 0);
lean_dec(v_unused_3833_);
v___x_3800_ = v_b_3790_;
v_isShared_3801_ = v_isSharedCheck_3832_;
goto v_resetjp_3799_;
}
else
{
lean_inc(v_snd_3798_);
lean_dec(v_b_3790_);
v___x_3800_ = lean_box(0);
v_isShared_3801_ = v_isSharedCheck_3832_;
goto v_resetjp_3799_;
}
v_resetjp_3799_:
{
lean_object* v_a_3802_; lean_object* v___x_3803_; 
v_a_3802_ = lean_array_uget_borrowed(v_as_3787_, v_i_3789_);
lean_inc(v_snd_3798_);
lean_inc(v_mvarId_3786_);
v___x_3803_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3785_, v_mvarId_3786_, v_a_3802_, v_snd_3798_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3823_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3823_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3823_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
if (lean_obj_tag(v_a_3804_) == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
lean_dec(v_mvarId_3786_);
v___x_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3808_, 0, v_a_3804_);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 0, v___x_3808_);
v___x_3810_ = v___x_3800_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3808_);
lean_ctor_set(v_reuseFailAlloc_3814_, 1, v_snd_3798_);
v___x_3810_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___x_3812_; 
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v___x_3810_);
v___x_3812_ = v___x_3806_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3813_; 
v_reuseFailAlloc_3813_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3813_, 0, v___x_3810_);
v___x_3812_ = v_reuseFailAlloc_3813_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
return v___x_3812_;
}
}
}
else
{
lean_object* v_a_3815_; lean_object* v___x_3816_; lean_object* v___x_3818_; 
lean_del_object(v___x_3806_);
lean_dec(v_snd_3798_);
v_a_3815_ = lean_ctor_get(v_a_3804_, 0);
lean_inc(v_a_3815_);
lean_dec_ref_known(v_a_3804_, 1);
v___x_3816_ = lean_box(0);
if (v_isShared_3801_ == 0)
{
lean_ctor_set(v___x_3800_, 1, v_a_3815_);
lean_ctor_set(v___x_3800_, 0, v___x_3816_);
v___x_3818_ = v___x_3800_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3816_);
lean_ctor_set(v_reuseFailAlloc_3822_, 1, v_a_3815_);
v___x_3818_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
size_t v___x_3819_; size_t v___x_3820_; 
v___x_3819_ = ((size_t)1ULL);
v___x_3820_ = lean_usize_add(v_i_3789_, v___x_3819_);
v_i_3789_ = v___x_3820_;
v_b_3790_ = v___x_3818_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_del_object(v___x_3800_);
lean_dec(v_snd_3798_);
lean_dec(v_mvarId_3786_);
v_a_3824_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3803_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3803_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
v___x_3829_ = v_reuseFailAlloc_3830_;
goto v_reusejp_3828_;
}
v_reusejp_3828_:
{
return v___x_3829_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3834_, lean_object* v_mvarId_3835_, lean_object* v_as_3836_, lean_object* v_sz_3837_, lean_object* v_i_3838_, lean_object* v_b_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_){
_start:
{
size_t v_sz_boxed_3845_; size_t v_i_boxed_3846_; lean_object* v_res_3847_; 
v_sz_boxed_3845_ = lean_unbox_usize(v_sz_3837_);
lean_dec(v_sz_3837_);
v_i_boxed_3846_ = lean_unbox_usize(v_i_3838_);
lean_dec(v_i_3838_);
v_res_3847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3834_, v_mvarId_3835_, v_as_3836_, v_sz_boxed_3845_, v_i_boxed_3846_, v_b_3839_, v___y_3840_, v___y_3841_, v___y_3842_, v___y_3843_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec(v___y_3841_);
lean_dec_ref(v___y_3840_);
lean_dec_ref(v_as_3836_);
lean_dec_ref(v_init_3834_);
return v_res_3847_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_init_3848_, lean_object* v_mvarId_3849_, lean_object* v_n_3850_, lean_object* v_b_3851_, lean_object* v___y_3852_, lean_object* v___y_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3848_, v_mvarId_3849_, v_n_3850_, v_b_3851_, v___y_3852_, v___y_3853_, v___y_3854_, v___y_3855_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec(v___y_3853_);
lean_dec_ref(v___y_3852_);
lean_dec_ref(v_n_3850_);
lean_dec_ref(v_init_3848_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3861_, lean_object* v_as_3862_, size_t v_sz_3863_, size_t v_i_3864_, lean_object* v_b_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_){
_start:
{
uint8_t v___x_3871_; 
v___x_3871_ = lean_usize_dec_lt(v_i_3864_, v_sz_3863_);
if (v___x_3871_ == 0)
{
lean_object* v___x_3872_; 
lean_dec(v_mvarId_3861_);
v___x_3872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3872_, 0, v_b_3865_);
return v___x_3872_;
}
else
{
lean_object* v_snd_3873_; lean_object* v___x_3875_; uint8_t v_isShared_3876_; uint8_t v_isSharedCheck_3925_; 
v_snd_3873_ = lean_ctor_get(v_b_3865_, 1);
v_isSharedCheck_3925_ = !lean_is_exclusive(v_b_3865_);
if (v_isSharedCheck_3925_ == 0)
{
lean_object* v_unused_3926_; 
v_unused_3926_ = lean_ctor_get(v_b_3865_, 0);
lean_dec(v_unused_3926_);
v___x_3875_ = v_b_3865_;
v_isShared_3876_ = v_isSharedCheck_3925_;
goto v_resetjp_3874_;
}
else
{
lean_inc(v_snd_3873_);
lean_dec(v_b_3865_);
v___x_3875_ = lean_box(0);
v_isShared_3876_ = v_isSharedCheck_3925_;
goto v_resetjp_3874_;
}
v_resetjp_3874_:
{
lean_object* v___x_3877_; lean_object* v_a_3879_; lean_object* v_a_3886_; 
v___x_3877_ = lean_box(0);
v_a_3886_ = lean_array_uget(v_as_3862_, v_i_3864_);
if (lean_obj_tag(v_a_3886_) == 0)
{
v_a_3879_ = v_snd_3873_;
goto v___jp_3878_;
}
else
{
lean_object* v_val_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3924_; 
v_val_3887_ = lean_ctor_get(v_a_3886_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v_a_3886_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3889_ = v_a_3886_;
v_isShared_3890_ = v_isSharedCheck_3924_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_val_3887_);
lean_dec(v_a_3886_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3924_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3891_; lean_object* v___x_3892_; 
v___x_3891_ = l_Lean_LocalDecl_fvarId(v_val_3887_);
lean_dec(v_val_3887_);
lean_inc(v_mvarId_3861_);
v___x_3892_ = l_Lean_Meta_subst_x3f(v_mvarId_3861_, v___x_3891_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_);
if (lean_obj_tag(v___x_3892_) == 0)
{
lean_object* v_a_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3915_; 
v_a_3893_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3915_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3915_ == 0)
{
v___x_3895_ = v___x_3892_;
v_isShared_3896_ = v_isSharedCheck_3915_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_a_3893_);
lean_dec(v___x_3892_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3915_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v___x_3897_; 
v___x_3897_ = lean_box(0);
if (lean_obj_tag(v_a_3893_) == 1)
{
lean_object* v___x_3899_; 
lean_del_object(v___x_3875_);
lean_dec(v_mvarId_3861_);
lean_inc_ref(v_a_3893_);
if (v_isShared_3890_ == 0)
{
lean_ctor_set(v___x_3889_, 0, v_a_3893_);
v___x_3899_ = v___x_3889_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3913_; 
v_reuseFailAlloc_3913_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3913_, 0, v_a_3893_);
v___x_3899_ = v_reuseFailAlloc_3913_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
lean_object* v___x_3901_; uint8_t v_isShared_3902_; uint8_t v_isSharedCheck_3911_; 
v_isSharedCheck_3911_ = !lean_is_exclusive(v_a_3893_);
if (v_isSharedCheck_3911_ == 0)
{
lean_object* v_unused_3912_; 
v_unused_3912_ = lean_ctor_get(v_a_3893_, 0);
lean_dec(v_unused_3912_);
v___x_3901_ = v_a_3893_;
v_isShared_3902_ = v_isSharedCheck_3911_;
goto v_resetjp_3900_;
}
else
{
lean_dec(v_a_3893_);
v___x_3901_ = lean_box(0);
v_isShared_3902_ = v_isSharedCheck_3911_;
goto v_resetjp_3900_;
}
v_resetjp_3900_:
{
lean_object* v___x_3903_; lean_object* v___x_3905_; 
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3899_);
lean_ctor_set(v___x_3903_, 1, v___x_3897_);
if (v_isShared_3902_ == 0)
{
lean_ctor_set(v___x_3901_, 0, v___x_3903_);
v___x_3905_ = v___x_3901_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3910_; 
v_reuseFailAlloc_3910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3910_, 0, v___x_3903_);
v___x_3905_ = v_reuseFailAlloc_3910_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
lean_object* v___x_3906_; lean_object* v___x_3908_; 
v___x_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
lean_ctor_set(v___x_3906_, 1, v_snd_3873_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3906_);
v___x_3908_ = v___x_3895_;
goto v_reusejp_3907_;
}
else
{
lean_object* v_reuseFailAlloc_3909_; 
v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3909_, 0, v___x_3906_);
v___x_3908_ = v_reuseFailAlloc_3909_;
goto v_reusejp_3907_;
}
v_reusejp_3907_:
{
return v___x_3908_;
}
}
}
}
}
else
{
lean_object* v___x_3914_; 
lean_del_object(v___x_3895_);
lean_dec(v_a_3893_);
lean_del_object(v___x_3889_);
lean_dec(v_snd_3873_);
v___x_3914_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3879_ = v___x_3914_;
goto v___jp_3878_;
}
}
}
else
{
lean_object* v_a_3916_; lean_object* v___x_3918_; uint8_t v_isShared_3919_; uint8_t v_isSharedCheck_3923_; 
lean_del_object(v___x_3889_);
lean_del_object(v___x_3875_);
lean_dec(v_snd_3873_);
lean_dec(v_mvarId_3861_);
v_a_3916_ = lean_ctor_get(v___x_3892_, 0);
v_isSharedCheck_3923_ = !lean_is_exclusive(v___x_3892_);
if (v_isSharedCheck_3923_ == 0)
{
v___x_3918_ = v___x_3892_;
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
else
{
lean_inc(v_a_3916_);
lean_dec(v___x_3892_);
v___x_3918_ = lean_box(0);
v_isShared_3919_ = v_isSharedCheck_3923_;
goto v_resetjp_3917_;
}
v_resetjp_3917_:
{
lean_object* v___x_3921_; 
if (v_isShared_3919_ == 0)
{
v___x_3921_ = v___x_3918_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v_a_3916_);
v___x_3921_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
return v___x_3921_;
}
}
}
}
}
v___jp_3878_:
{
lean_object* v___x_3881_; 
if (v_isShared_3876_ == 0)
{
lean_ctor_set(v___x_3875_, 1, v_a_3879_);
lean_ctor_set(v___x_3875_, 0, v___x_3877_);
v___x_3881_ = v___x_3875_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v___x_3877_);
lean_ctor_set(v_reuseFailAlloc_3885_, 1, v_a_3879_);
v___x_3881_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
size_t v___x_3882_; size_t v___x_3883_; 
v___x_3882_ = ((size_t)1ULL);
v___x_3883_ = lean_usize_add(v_i_3864_, v___x_3882_);
v_i_3864_ = v___x_3883_;
v_b_3865_ = v___x_3881_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3927_, lean_object* v_as_3928_, lean_object* v_sz_3929_, lean_object* v_i_3930_, lean_object* v_b_3931_, lean_object* v___y_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
size_t v_sz_boxed_3937_; size_t v_i_boxed_3938_; lean_object* v_res_3939_; 
v_sz_boxed_3937_ = lean_unbox_usize(v_sz_3929_);
lean_dec(v_sz_3929_);
v_i_boxed_3938_ = lean_unbox_usize(v_i_3930_);
lean_dec(v_i_3930_);
v_res_3939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3927_, v_as_3928_, v_sz_boxed_3937_, v_i_boxed_3938_, v_b_3931_, v___y_3932_, v___y_3933_, v___y_3934_, v___y_3935_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec(v___y_3933_);
lean_dec_ref(v___y_3932_);
lean_dec_ref(v_as_3928_);
return v_res_3939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_3940_, lean_object* v_as_3941_, size_t v_sz_3942_, size_t v_i_3943_, lean_object* v_b_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_){
_start:
{
uint8_t v___x_3950_; 
v___x_3950_ = lean_usize_dec_lt(v_i_3943_, v_sz_3942_);
if (v___x_3950_ == 0)
{
lean_object* v___x_3951_; 
lean_dec(v_mvarId_3940_);
v___x_3951_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3951_, 0, v_b_3944_);
return v___x_3951_;
}
else
{
lean_object* v_snd_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_4004_; 
v_snd_3952_ = lean_ctor_get(v_b_3944_, 1);
v_isSharedCheck_4004_ = !lean_is_exclusive(v_b_3944_);
if (v_isSharedCheck_4004_ == 0)
{
lean_object* v_unused_4005_; 
v_unused_4005_ = lean_ctor_get(v_b_3944_, 0);
lean_dec(v_unused_4005_);
v___x_3954_ = v_b_3944_;
v_isShared_3955_ = v_isSharedCheck_4004_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_snd_3952_);
lean_dec(v_b_3944_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_4004_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3956_; lean_object* v_a_3958_; lean_object* v_a_3965_; 
v___x_3956_ = lean_box(0);
v_a_3965_ = lean_array_uget(v_as_3941_, v_i_3943_);
if (lean_obj_tag(v_a_3965_) == 0)
{
v_a_3958_ = v_snd_3952_;
goto v___jp_3957_;
}
else
{
lean_object* v_val_3966_; lean_object* v___x_3968_; uint8_t v_isShared_3969_; uint8_t v_isSharedCheck_4003_; 
v_val_3966_ = lean_ctor_get(v_a_3965_, 0);
v_isSharedCheck_4003_ = !lean_is_exclusive(v_a_3965_);
if (v_isSharedCheck_4003_ == 0)
{
v___x_3968_ = v_a_3965_;
v_isShared_3969_ = v_isSharedCheck_4003_;
goto v_resetjp_3967_;
}
else
{
lean_inc(v_val_3966_);
lean_dec(v_a_3965_);
v___x_3968_ = lean_box(0);
v_isShared_3969_ = v_isSharedCheck_4003_;
goto v_resetjp_3967_;
}
v_resetjp_3967_:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; 
v___x_3970_ = l_Lean_LocalDecl_fvarId(v_val_3966_);
lean_dec(v_val_3966_);
lean_inc(v_mvarId_3940_);
v___x_3971_ = l_Lean_Meta_subst_x3f(v_mvarId_3940_, v___x_3970_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
if (lean_obj_tag(v___x_3971_) == 0)
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3994_; 
v_a_3972_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_3994_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_3994_ == 0)
{
v___x_3974_ = v___x_3971_;
v_isShared_3975_ = v_isSharedCheck_3994_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3971_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3994_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3976_; 
v___x_3976_ = lean_box(0);
if (lean_obj_tag(v_a_3972_) == 1)
{
lean_object* v___x_3978_; 
lean_del_object(v___x_3954_);
lean_dec(v_mvarId_3940_);
lean_inc_ref(v_a_3972_);
if (v_isShared_3969_ == 0)
{
lean_ctor_set(v___x_3968_, 0, v_a_3972_);
v___x_3978_ = v___x_3968_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3972_);
v___x_3978_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
lean_object* v___x_3980_; uint8_t v_isShared_3981_; uint8_t v_isSharedCheck_3990_; 
v_isSharedCheck_3990_ = !lean_is_exclusive(v_a_3972_);
if (v_isSharedCheck_3990_ == 0)
{
lean_object* v_unused_3991_; 
v_unused_3991_ = lean_ctor_get(v_a_3972_, 0);
lean_dec(v_unused_3991_);
v___x_3980_ = v_a_3972_;
v_isShared_3981_ = v_isSharedCheck_3990_;
goto v_resetjp_3979_;
}
else
{
lean_dec(v_a_3972_);
v___x_3980_ = lean_box(0);
v_isShared_3981_ = v_isSharedCheck_3990_;
goto v_resetjp_3979_;
}
v_resetjp_3979_:
{
lean_object* v___x_3982_; lean_object* v___x_3984_; 
v___x_3982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3982_, 0, v___x_3978_);
lean_ctor_set(v___x_3982_, 1, v___x_3976_);
if (v_isShared_3981_ == 0)
{
lean_ctor_set(v___x_3980_, 0, v___x_3982_);
v___x_3984_ = v___x_3980_;
goto v_reusejp_3983_;
}
else
{
lean_object* v_reuseFailAlloc_3989_; 
v_reuseFailAlloc_3989_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3989_, 0, v___x_3982_);
v___x_3984_ = v_reuseFailAlloc_3989_;
goto v_reusejp_3983_;
}
v_reusejp_3983_:
{
lean_object* v___x_3985_; lean_object* v___x_3987_; 
v___x_3985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3985_, 0, v___x_3984_);
lean_ctor_set(v___x_3985_, 1, v_snd_3952_);
if (v_isShared_3975_ == 0)
{
lean_ctor_set(v___x_3974_, 0, v___x_3985_);
v___x_3987_ = v___x_3974_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v___x_3985_);
v___x_3987_ = v_reuseFailAlloc_3988_;
goto v_reusejp_3986_;
}
v_reusejp_3986_:
{
return v___x_3987_;
}
}
}
}
}
else
{
lean_object* v___x_3993_; 
lean_del_object(v___x_3974_);
lean_dec(v_a_3972_);
lean_del_object(v___x_3968_);
lean_dec(v_snd_3952_);
v___x_3993_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3958_ = v___x_3993_;
goto v___jp_3957_;
}
}
}
else
{
lean_object* v_a_3995_; lean_object* v___x_3997_; uint8_t v_isShared_3998_; uint8_t v_isSharedCheck_4002_; 
lean_del_object(v___x_3968_);
lean_del_object(v___x_3954_);
lean_dec(v_snd_3952_);
lean_dec(v_mvarId_3940_);
v_a_3995_ = lean_ctor_get(v___x_3971_, 0);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3971_);
if (v_isSharedCheck_4002_ == 0)
{
v___x_3997_ = v___x_3971_;
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
else
{
lean_inc(v_a_3995_);
lean_dec(v___x_3971_);
v___x_3997_ = lean_box(0);
v_isShared_3998_ = v_isSharedCheck_4002_;
goto v_resetjp_3996_;
}
v_resetjp_3996_:
{
lean_object* v___x_4000_; 
if (v_isShared_3998_ == 0)
{
v___x_4000_ = v___x_3997_;
goto v_reusejp_3999_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v_a_3995_);
v___x_4000_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3999_;
}
v_reusejp_3999_:
{
return v___x_4000_;
}
}
}
}
}
v___jp_3957_:
{
lean_object* v___x_3960_; 
if (v_isShared_3955_ == 0)
{
lean_ctor_set(v___x_3954_, 1, v_a_3958_);
lean_ctor_set(v___x_3954_, 0, v___x_3956_);
v___x_3960_ = v___x_3954_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v___x_3956_);
lean_ctor_set(v_reuseFailAlloc_3964_, 1, v_a_3958_);
v___x_3960_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
size_t v___x_3961_; size_t v___x_3962_; lean_object* v___x_3963_; 
v___x_3961_ = ((size_t)1ULL);
v___x_3962_ = lean_usize_add(v_i_3943_, v___x_3961_);
v___x_3963_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3940_, v_as_3941_, v_sz_3942_, v___x_3962_, v___x_3960_, v___y_3945_, v___y_3946_, v___y_3947_, v___y_3948_);
return v___x_3963_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_4006_, lean_object* v_as_4007_, lean_object* v_sz_4008_, lean_object* v_i_4009_, lean_object* v_b_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_){
_start:
{
size_t v_sz_boxed_4016_; size_t v_i_boxed_4017_; lean_object* v_res_4018_; 
v_sz_boxed_4016_ = lean_unbox_usize(v_sz_4008_);
lean_dec(v_sz_4008_);
v_i_boxed_4017_ = lean_unbox_usize(v_i_4009_);
lean_dec(v_i_4009_);
v_res_4018_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4006_, v_as_4007_, v_sz_boxed_4016_, v_i_boxed_4017_, v_b_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec(v___y_4012_);
lean_dec_ref(v___y_4011_);
lean_dec_ref(v_as_4007_);
return v_res_4018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4019_, lean_object* v_t_4020_, lean_object* v_init_4021_, lean_object* v___y_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_){
_start:
{
lean_object* v_root_4027_; lean_object* v_tail_4028_; lean_object* v___x_4029_; 
v_root_4027_ = lean_ctor_get(v_t_4020_, 0);
v_tail_4028_ = lean_ctor_get(v_t_4020_, 1);
lean_inc(v_mvarId_4019_);
lean_inc_ref(v_init_4021_);
v___x_4029_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_4021_, v_mvarId_4019_, v_root_4027_, v_init_4021_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
lean_dec_ref(v_init_4021_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4032_; uint8_t v_isShared_4033_; uint8_t v_isSharedCheck_4066_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4066_ == 0)
{
v___x_4032_ = v___x_4029_;
v_isShared_4033_ = v_isSharedCheck_4066_;
goto v_resetjp_4031_;
}
else
{
lean_inc(v_a_4030_);
lean_dec(v___x_4029_);
v___x_4032_ = lean_box(0);
v_isShared_4033_ = v_isSharedCheck_4066_;
goto v_resetjp_4031_;
}
v_resetjp_4031_:
{
if (lean_obj_tag(v_a_4030_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4036_; 
lean_dec(v_mvarId_4019_);
v_a_4034_ = lean_ctor_get(v_a_4030_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v_a_4030_, 1);
if (v_isShared_4033_ == 0)
{
lean_ctor_set(v___x_4032_, 0, v_a_4034_);
v___x_4036_ = v___x_4032_;
goto v_reusejp_4035_;
}
else
{
lean_object* v_reuseFailAlloc_4037_; 
v_reuseFailAlloc_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4037_, 0, v_a_4034_);
v___x_4036_ = v_reuseFailAlloc_4037_;
goto v_reusejp_4035_;
}
v_reusejp_4035_:
{
return v___x_4036_;
}
}
else
{
lean_object* v_a_4038_; lean_object* v___x_4039_; lean_object* v___x_4040_; size_t v_sz_4041_; size_t v___x_4042_; lean_object* v___x_4043_; 
lean_del_object(v___x_4032_);
v_a_4038_ = lean_ctor_get(v_a_4030_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v_a_4030_, 1);
v___x_4039_ = lean_box(0);
v___x_4040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4040_, 0, v___x_4039_);
lean_ctor_set(v___x_4040_, 1, v_a_4038_);
v_sz_4041_ = lean_array_size(v_tail_4028_);
v___x_4042_ = ((size_t)0ULL);
v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4019_, v_tail_4028_, v_sz_4041_, v___x_4042_, v___x_4040_, v___y_4022_, v___y_4023_, v___y_4024_, v___y_4025_);
if (lean_obj_tag(v___x_4043_) == 0)
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4057_; 
v_a_4044_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4057_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4057_ == 0)
{
v___x_4046_ = v___x_4043_;
v_isShared_4047_ = v_isSharedCheck_4057_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4043_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4057_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v_fst_4048_; 
v_fst_4048_ = lean_ctor_get(v_a_4044_, 0);
if (lean_obj_tag(v_fst_4048_) == 0)
{
lean_object* v_snd_4049_; lean_object* v___x_4051_; 
v_snd_4049_ = lean_ctor_get(v_a_4044_, 1);
lean_inc(v_snd_4049_);
lean_dec(v_a_4044_);
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 0, v_snd_4049_);
v___x_4051_ = v___x_4046_;
goto v_reusejp_4050_;
}
else
{
lean_object* v_reuseFailAlloc_4052_; 
v_reuseFailAlloc_4052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4052_, 0, v_snd_4049_);
v___x_4051_ = v_reuseFailAlloc_4052_;
goto v_reusejp_4050_;
}
v_reusejp_4050_:
{
return v___x_4051_;
}
}
else
{
lean_object* v_val_4053_; lean_object* v___x_4055_; 
lean_inc_ref(v_fst_4048_);
lean_dec(v_a_4044_);
v_val_4053_ = lean_ctor_get(v_fst_4048_, 0);
lean_inc(v_val_4053_);
lean_dec_ref_known(v_fst_4048_, 1);
if (v_isShared_4047_ == 0)
{
lean_ctor_set(v___x_4046_, 0, v_val_4053_);
v___x_4055_ = v___x_4046_;
goto v_reusejp_4054_;
}
else
{
lean_object* v_reuseFailAlloc_4056_; 
v_reuseFailAlloc_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_val_4053_);
v___x_4055_ = v_reuseFailAlloc_4056_;
goto v_reusejp_4054_;
}
v_reusejp_4054_:
{
return v___x_4055_;
}
}
}
}
else
{
lean_object* v_a_4058_; lean_object* v___x_4060_; uint8_t v_isShared_4061_; uint8_t v_isSharedCheck_4065_; 
v_a_4058_ = lean_ctor_get(v___x_4043_, 0);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4043_);
if (v_isSharedCheck_4065_ == 0)
{
v___x_4060_ = v___x_4043_;
v_isShared_4061_ = v_isSharedCheck_4065_;
goto v_resetjp_4059_;
}
else
{
lean_inc(v_a_4058_);
lean_dec(v___x_4043_);
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
}
else
{
lean_object* v_a_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4074_; 
lean_dec(v_mvarId_4019_);
v_a_4067_ = lean_ctor_get(v___x_4029_, 0);
v_isSharedCheck_4074_ = !lean_is_exclusive(v___x_4029_);
if (v_isSharedCheck_4074_ == 0)
{
v___x_4069_ = v___x_4029_;
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_a_4067_);
lean_dec(v___x_4029_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4074_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4072_; 
if (v_isShared_4070_ == 0)
{
v___x_4072_ = v___x_4069_;
goto v_reusejp_4071_;
}
else
{
lean_object* v_reuseFailAlloc_4073_; 
v_reuseFailAlloc_4073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4073_, 0, v_a_4067_);
v___x_4072_ = v_reuseFailAlloc_4073_;
goto v_reusejp_4071_;
}
v_reusejp_4071_:
{
return v___x_4072_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4075_, lean_object* v_t_4076_, lean_object* v_init_4077_, lean_object* v___y_4078_, lean_object* v___y_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_){
_start:
{
lean_object* v_res_4083_; 
v_res_4083_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4075_, v_t_4076_, v_init_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec(v___y_4079_);
lean_dec_ref(v___y_4078_);
lean_dec_ref(v_t_4076_);
return v_res_4083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v_lctx_4093_; lean_object* v_decls_4094_; lean_object* v___x_4095_; lean_object* v___x_4096_; lean_object* v___x_4097_; 
v_lctx_4093_ = lean_ctor_get(v___y_4088_, 2);
v_decls_4094_ = lean_ctor_get(v_lctx_4093_, 1);
v___x_4095_ = lean_box(0);
v___x_4096_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4097_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4087_, v_decls_4094_, v___x_4096_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4110_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4100_ = v___x_4097_;
v_isShared_4101_ = v_isSharedCheck_4110_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4097_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4110_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
lean_object* v_fst_4102_; 
v_fst_4102_ = lean_ctor_get(v_a_4098_, 0);
lean_inc(v_fst_4102_);
lean_dec(v_a_4098_);
if (lean_obj_tag(v_fst_4102_) == 0)
{
lean_object* v___x_4104_; 
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4095_);
v___x_4104_ = v___x_4100_;
goto v_reusejp_4103_;
}
else
{
lean_object* v_reuseFailAlloc_4105_; 
v_reuseFailAlloc_4105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4105_, 0, v___x_4095_);
v___x_4104_ = v_reuseFailAlloc_4105_;
goto v_reusejp_4103_;
}
v_reusejp_4103_:
{
return v___x_4104_;
}
}
else
{
lean_object* v_val_4106_; lean_object* v___x_4108_; 
v_val_4106_ = lean_ctor_get(v_fst_4102_, 0);
lean_inc(v_val_4106_);
lean_dec_ref_known(v_fst_4102_, 1);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v_val_4106_);
v___x_4108_ = v___x_4100_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_val_4106_);
v___x_4108_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4107_;
}
v_reusejp_4107_:
{
return v___x_4108_;
}
}
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
v_a_4111_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4097_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4097_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4116_; 
if (v_isShared_4114_ == 0)
{
v___x_4116_ = v___x_4113_;
goto v_reusejp_4115_;
}
else
{
lean_object* v_reuseFailAlloc_4117_; 
v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4119_, lean_object* v___y_4120_, lean_object* v___y_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v_res_4125_; 
v_res_4125_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
lean_dec(v___y_4121_);
lean_dec_ref(v___y_4120_);
return v_res_4125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4126_, lean_object* v_a_4127_, lean_object* v_a_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_){
_start:
{
lean_object* v___f_4132_; lean_object* v___x_4133_; 
lean_inc(v_mvarId_4126_);
v___f_4132_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4132_, 0, v_mvarId_4126_);
v___x_4133_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_4126_, v___f_4132_, v_a_4127_, v_a_4128_, v_a_4129_, v_a_4130_);
return v___x_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_){
_start:
{
lean_object* v_res_4140_; 
v_res_4140_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
lean_dec(v_a_4136_);
lean_dec_ref(v_a_4135_);
return v_res_4140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4141_, lean_object* v_a_4142_, lean_object* v_a_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_){
_start:
{
lean_object* v___x_4147_; 
lean_inc(v_mvarId_4141_);
v___x_4147_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4141_, v_a_4142_, v_a_4143_, v_a_4144_, v_a_4145_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; lean_object* v___x_4150_; uint8_t v_isShared_4151_; uint8_t v_isSharedCheck_4157_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4150_ = v___x_4147_;
v_isShared_4151_ = v_isSharedCheck_4157_;
goto v_resetjp_4149_;
}
else
{
lean_inc(v_a_4148_);
lean_dec(v___x_4147_);
v___x_4150_ = lean_box(0);
v_isShared_4151_ = v_isSharedCheck_4157_;
goto v_resetjp_4149_;
}
v_resetjp_4149_:
{
if (lean_obj_tag(v_a_4148_) == 1)
{
lean_object* v_val_4152_; 
lean_del_object(v___x_4150_);
lean_dec(v_mvarId_4141_);
v_val_4152_ = lean_ctor_get(v_a_4148_, 0);
lean_inc(v_val_4152_);
lean_dec_ref_known(v_a_4148_, 1);
v_mvarId_4141_ = v_val_4152_;
goto _start;
}
else
{
lean_object* v___x_4155_; 
lean_dec(v_a_4148_);
if (v_isShared_4151_ == 0)
{
lean_ctor_set(v___x_4150_, 0, v_mvarId_4141_);
v___x_4155_ = v___x_4150_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_mvarId_4141_);
v___x_4155_ = v_reuseFailAlloc_4156_;
goto v_reusejp_4154_;
}
v_reusejp_4154_:
{
return v___x_4155_;
}
}
}
}
else
{
lean_object* v_a_4158_; lean_object* v___x_4160_; uint8_t v_isShared_4161_; uint8_t v_isSharedCheck_4165_; 
lean_dec(v_mvarId_4141_);
v_a_4158_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4147_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4147_);
v___x_4160_ = lean_box(0);
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
v_resetjp_4159_:
{
lean_object* v___x_4163_; 
if (v_isShared_4161_ == 0)
{
v___x_4163_ = v___x_4160_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v_a_4158_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4166_, lean_object* v_a_4167_, lean_object* v_a_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_Meta_substVars(v_mvarId_4166_, v_a_4167_, v_a_4168_, v_a_4169_, v_a_4170_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
lean_dec(v_a_4168_);
lean_dec_ref(v_a_4167_);
return v_res_4172_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4235_; uint8_t v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4235_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_4236_ = 0;
v___x_4237_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4238_ = l_Lean_registerTraceClass(v___x_4235_, v___x_4236_, v___x_4237_);
return v___x_4238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4240_;
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
