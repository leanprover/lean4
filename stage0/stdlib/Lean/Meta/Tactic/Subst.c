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
uint8_t v___x_33178__boxed_248_; uint8_t v___x_33179__boxed_249_; lean_object* v_res_250_; 
v___x_33178__boxed_248_ = lean_unbox(v___x_240_);
v___x_33179__boxed_249_ = lean_unbox(v___x_241_);
v_res_250_ = l_Lean_Meta_substCore___lam__1(v_type_236_, v___x_237_, v___x_238_, v___x_239_, v___x_33178__boxed_248_, v___x_33179__boxed_249_, v_hAux_242_, v___y_243_, v___y_244_, v___y_245_, v___y_246_);
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
lean_object* v_ks_532_; lean_object* v_vs_533_; lean_object* v___x_535_; uint8_t v_isShared_536_; uint8_t v_isSharedCheck_553_; 
v_ks_532_ = lean_ctor_get(v_x_481_, 0);
v_vs_533_ = lean_ctor_get(v_x_481_, 1);
v_isSharedCheck_553_ = !lean_is_exclusive(v_x_481_);
if (v_isSharedCheck_553_ == 0)
{
v___x_535_ = v_x_481_;
v_isShared_536_ = v_isSharedCheck_553_;
goto v_resetjp_534_;
}
else
{
lean_inc(v_vs_533_);
lean_inc(v_ks_532_);
lean_dec(v_x_481_);
v___x_535_ = lean_box(0);
v_isShared_536_ = v_isSharedCheck_553_;
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
lean_object* v_reuseFailAlloc_552_; 
v_reuseFailAlloc_552_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_552_, 0, v_ks_532_);
lean_ctor_set(v_reuseFailAlloc_552_, 1, v_vs_533_);
v___x_538_ = v_reuseFailAlloc_552_;
goto v_reusejp_537_;
}
v_reusejp_537_:
{
lean_object* v_newNode_539_; uint8_t v___y_541_; size_t v___x_547_; uint8_t v___x_548_; 
v_newNode_539_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v___x_538_, v_x_484_, v_x_485_);
v___x_547_ = ((size_t)7ULL);
v___x_548_ = lean_usize_dec_le(v___x_547_, v_x_483_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; uint8_t v___x_551_; 
v___x_549_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_539_);
v___x_550_ = lean_unsigned_to_nat(4u);
v___x_551_ = lean_nat_dec_lt(v___x_549_, v___x_550_);
lean_dec(v___x_549_);
v___y_541_ = v___x_551_;
goto v___jp_540_;
}
else
{
v___y_541_ = v___x_548_;
goto v___jp_540_;
}
v___jp_540_:
{
if (v___y_541_ == 0)
{
lean_object* v_ks_542_; lean_object* v_vs_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v_ks_542_ = lean_ctor_get(v_newNode_539_, 0);
lean_inc_ref(v_ks_542_);
v_vs_543_ = lean_ctor_get(v_newNode_539_, 1);
lean_inc_ref(v_vs_543_);
lean_dec_ref(v_newNode_539_);
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___closed__0);
v___x_546_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_x_483_, v_ks_542_, v_vs_543_, v___x_544_, v___x_545_);
lean_dec_ref(v_vs_543_);
lean_dec_ref(v_ks_542_);
return v___x_546_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(size_t v_depth_554_, lean_object* v_keys_555_, lean_object* v_vals_556_, lean_object* v_i_557_, lean_object* v_entries_558_){
_start:
{
lean_object* v___x_559_; uint8_t v___x_560_; 
v___x_559_ = lean_array_get_size(v_keys_555_);
v___x_560_ = lean_nat_dec_lt(v_i_557_, v___x_559_);
if (v___x_560_ == 0)
{
lean_dec(v_i_557_);
return v_entries_558_;
}
else
{
lean_object* v_k_561_; lean_object* v_v_562_; uint64_t v___x_563_; size_t v_h_564_; size_t v___x_565_; lean_object* v___x_566_; size_t v___x_567_; size_t v___x_568_; size_t v___x_569_; size_t v_h_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v_k_561_ = lean_array_fget_borrowed(v_keys_555_, v_i_557_);
v_v_562_ = lean_array_fget_borrowed(v_vals_556_, v_i_557_);
v___x_563_ = l_Lean_instHashableMVarId_hash(v_k_561_);
v_h_564_ = lean_uint64_to_usize(v___x_563_);
v___x_565_ = ((size_t)5ULL);
v___x_566_ = lean_unsigned_to_nat(1u);
v___x_567_ = ((size_t)1ULL);
v___x_568_ = lean_usize_sub(v_depth_554_, v___x_567_);
v___x_569_ = lean_usize_mul(v___x_565_, v___x_568_);
v_h_570_ = lean_usize_shift_right(v_h_564_, v___x_569_);
v___x_571_ = lean_nat_add(v_i_557_, v___x_566_);
lean_dec(v_i_557_);
lean_inc(v_v_562_);
lean_inc(v_k_561_);
v___x_572_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_entries_558_, v_h_570_, v_depth_554_, v_k_561_, v_v_562_);
v_i_557_ = v___x_571_;
v_entries_558_ = v___x_572_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg___boxed(lean_object* v_depth_574_, lean_object* v_keys_575_, lean_object* v_vals_576_, lean_object* v_i_577_, lean_object* v_entries_578_){
_start:
{
size_t v_depth_boxed_579_; lean_object* v_res_580_; 
v_depth_boxed_579_ = lean_unbox_usize(v_depth_574_);
lean_dec(v_depth_574_);
v_res_580_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_boxed_579_, v_keys_575_, v_vals_576_, v_i_577_, v_entries_578_);
lean_dec_ref(v_vals_576_);
lean_dec_ref(v_keys_575_);
return v_res_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg___boxed(lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_){
_start:
{
size_t v_x_33550__boxed_586_; size_t v_x_33551__boxed_587_; lean_object* v_res_588_; 
v_x_33550__boxed_586_ = lean_unbox_usize(v_x_582_);
lean_dec(v_x_582_);
v_x_33551__boxed_587_ = lean_unbox_usize(v_x_583_);
lean_dec(v_x_583_);
v_res_588_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_581_, v_x_33550__boxed_586_, v_x_33551__boxed_587_, v_x_584_, v_x_585_);
return v_res_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(lean_object* v_x_589_, lean_object* v_x_590_, lean_object* v_x_591_){
_start:
{
uint64_t v___x_592_; size_t v___x_593_; size_t v___x_594_; lean_object* v___x_595_; 
v___x_592_ = l_Lean_instHashableMVarId_hash(v_x_590_);
v___x_593_ = lean_uint64_to_usize(v___x_592_);
v___x_594_ = ((size_t)1ULL);
v___x_595_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_589_, v___x_593_, v___x_594_, v_x_590_, v_x_591_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(lean_object* v_mvarId_596_, lean_object* v_val_597_, lean_object* v___y_598_){
_start:
{
lean_object* v___x_600_; lean_object* v_mctx_601_; lean_object* v_cache_602_; lean_object* v_zetaDeltaFVarIds_603_; lean_object* v_postponed_604_; lean_object* v_diag_605_; lean_object* v___x_607_; uint8_t v_isShared_608_; uint8_t v_isSharedCheck_634_; 
v___x_600_ = lean_st_ref_take(v___y_598_);
v_mctx_601_ = lean_ctor_get(v___x_600_, 0);
v_cache_602_ = lean_ctor_get(v___x_600_, 1);
v_zetaDeltaFVarIds_603_ = lean_ctor_get(v___x_600_, 2);
v_postponed_604_ = lean_ctor_get(v___x_600_, 3);
v_diag_605_ = lean_ctor_get(v___x_600_, 4);
v_isSharedCheck_634_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_634_ == 0)
{
v___x_607_ = v___x_600_;
v_isShared_608_ = v_isSharedCheck_634_;
goto v_resetjp_606_;
}
else
{
lean_inc(v_diag_605_);
lean_inc(v_postponed_604_);
lean_inc(v_zetaDeltaFVarIds_603_);
lean_inc(v_cache_602_);
lean_inc(v_mctx_601_);
lean_dec(v___x_600_);
v___x_607_ = lean_box(0);
v_isShared_608_ = v_isSharedCheck_634_;
goto v_resetjp_606_;
}
v_resetjp_606_:
{
lean_object* v_depth_609_; lean_object* v_levelAssignDepth_610_; lean_object* v_lmvarCounter_611_; lean_object* v_mvarCounter_612_; lean_object* v_lDecls_613_; lean_object* v_decls_614_; lean_object* v_userNames_615_; lean_object* v_lAssignment_616_; lean_object* v_eAssignment_617_; lean_object* v_dAssignment_618_; lean_object* v_instanceTypedMVars_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_633_; 
v_depth_609_ = lean_ctor_get(v_mctx_601_, 0);
v_levelAssignDepth_610_ = lean_ctor_get(v_mctx_601_, 1);
v_lmvarCounter_611_ = lean_ctor_get(v_mctx_601_, 2);
v_mvarCounter_612_ = lean_ctor_get(v_mctx_601_, 3);
v_lDecls_613_ = lean_ctor_get(v_mctx_601_, 4);
v_decls_614_ = lean_ctor_get(v_mctx_601_, 5);
v_userNames_615_ = lean_ctor_get(v_mctx_601_, 6);
v_lAssignment_616_ = lean_ctor_get(v_mctx_601_, 7);
v_eAssignment_617_ = lean_ctor_get(v_mctx_601_, 8);
v_dAssignment_618_ = lean_ctor_get(v_mctx_601_, 9);
v_instanceTypedMVars_619_ = lean_ctor_get(v_mctx_601_, 10);
v_isSharedCheck_633_ = !lean_is_exclusive(v_mctx_601_);
if (v_isSharedCheck_633_ == 0)
{
v___x_621_ = v_mctx_601_;
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_instanceTypedMVars_619_);
lean_inc(v_dAssignment_618_);
lean_inc(v_eAssignment_617_);
lean_inc(v_lAssignment_616_);
lean_inc(v_userNames_615_);
lean_inc(v_decls_614_);
lean_inc(v_lDecls_613_);
lean_inc(v_mvarCounter_612_);
lean_inc(v_lmvarCounter_611_);
lean_inc(v_levelAssignDepth_610_);
lean_inc(v_depth_609_);
lean_dec(v_mctx_601_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_633_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_625_; 
v___x_623_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_eAssignment_617_, v_mvarId_596_, v_val_597_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 8, v___x_623_);
v___x_625_ = v___x_621_;
goto v_reusejp_624_;
}
else
{
lean_object* v_reuseFailAlloc_632_; 
v_reuseFailAlloc_632_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_632_, 0, v_depth_609_);
lean_ctor_set(v_reuseFailAlloc_632_, 1, v_levelAssignDepth_610_);
lean_ctor_set(v_reuseFailAlloc_632_, 2, v_lmvarCounter_611_);
lean_ctor_set(v_reuseFailAlloc_632_, 3, v_mvarCounter_612_);
lean_ctor_set(v_reuseFailAlloc_632_, 4, v_lDecls_613_);
lean_ctor_set(v_reuseFailAlloc_632_, 5, v_decls_614_);
lean_ctor_set(v_reuseFailAlloc_632_, 6, v_userNames_615_);
lean_ctor_set(v_reuseFailAlloc_632_, 7, v_lAssignment_616_);
lean_ctor_set(v_reuseFailAlloc_632_, 8, v___x_623_);
lean_ctor_set(v_reuseFailAlloc_632_, 9, v_dAssignment_618_);
lean_ctor_set(v_reuseFailAlloc_632_, 10, v_instanceTypedMVars_619_);
v___x_625_ = v_reuseFailAlloc_632_;
goto v_reusejp_624_;
}
v_reusejp_624_:
{
lean_object* v___x_627_; 
if (v_isShared_608_ == 0)
{
lean_ctor_set(v___x_607_, 0, v___x_625_);
v___x_627_ = v___x_607_;
goto v_reusejp_626_;
}
else
{
lean_object* v_reuseFailAlloc_631_; 
v_reuseFailAlloc_631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_625_);
lean_ctor_set(v_reuseFailAlloc_631_, 1, v_cache_602_);
lean_ctor_set(v_reuseFailAlloc_631_, 2, v_zetaDeltaFVarIds_603_);
lean_ctor_set(v_reuseFailAlloc_631_, 3, v_postponed_604_);
lean_ctor_set(v_reuseFailAlloc_631_, 4, v_diag_605_);
v___x_627_ = v_reuseFailAlloc_631_;
goto v_reusejp_626_;
}
v_reusejp_626_:
{
lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
v___x_628_ = lean_st_ref_put(v___y_598_, v___x_627_);
v___x_629_ = lean_box(0);
v___x_630_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_630_, 0, v___x_629_);
return v___x_630_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg___boxed(lean_object* v_mvarId_635_, lean_object* v_val_636_, lean_object* v___y_637_, lean_object* v___y_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_mvarId_635_, v_val_636_, v___y_637_);
lean_dec(v___y_637_);
return v_res_639_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__1(void){
_start:
{
lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_641_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__0));
v___x_642_ = l_Lean_stringToMessageData(v___x_641_);
return v___x_642_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__3(void){
_start:
{
lean_object* v___x_644_; lean_object* v___x_645_; 
v___x_644_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__2));
v___x_645_ = l_Lean_stringToMessageData(v___x_644_);
return v___x_645_;
}
}
static lean_object* _init_l_Lean_Meta_substCore___lam__2___closed__7(void){
_start:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; 
v___x_649_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__6));
v___x_650_ = lean_unsigned_to_nat(22u);
v___x_651_ = lean_unsigned_to_nat(64u);
v___x_652_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__5));
v___x_653_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__4));
v___x_654_ = l_mkPanicMessageWithDecl(v___x_653_, v___x_652_, v___x_651_, v___x_650_, v___x_649_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2(lean_object* v_snd_658_, lean_object* v___x_659_, lean_object* v_fvarId_660_, lean_object* v_hFVarId_661_, lean_object* v___x_662_, lean_object* v_fst_663_, lean_object* v_fvarSubst_664_, uint8_t v_clearH_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v___x_668_, uint8_t v_skip_669_, uint8_t v___x_670_, lean_object* v___x_671_, lean_object* v___x_672_, lean_object* v_a_673_, uint8_t v_symm_674_, uint8_t v___x_675_, lean_object* v___x_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_){
_start:
{
lean_object* v___y_683_; lean_object* v___y_684_; lean_object* v___y_685_; lean_object* v___y_691_; lean_object* v___y_692_; lean_object* v___y_693_; lean_object* v___y_699_; lean_object* v_mvarId_700_; lean_object* v___y_701_; lean_object* v___y_702_; lean_object* v___y_703_; lean_object* v___y_704_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v_newVal_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_782_; uint8_t v___y_783_; lean_object* v___y_784_; lean_object* v___y_785_; lean_object* v_major_786_; lean_object* v___y_787_; lean_object* v___y_788_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_823_; uint8_t v___y_824_; lean_object* v_motive_825_; lean_object* v_newType_826_; lean_object* v___y_827_; lean_object* v___y_828_; lean_object* v___y_829_; lean_object* v___y_830_; lean_object* v___x_841_; 
lean_inc(v_snd_658_);
v___x_841_ = l_Lean_MVarId_getDecl(v_snd_658_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v_a_842_; lean_object* v___x_843_; 
v_a_842_ = lean_ctor_get(v___x_841_, 0);
lean_inc(v_a_842_);
lean_dec_ref_known(v___x_841_, 1);
lean_inc(v___x_659_);
v___x_843_ = l_Lean_FVarId_getDecl___redArg(v___x_659_, v___y_677_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_843_) == 0)
{
lean_object* v_a_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v_a_844_ = lean_ctor_get(v___x_843_, 0);
lean_inc(v_a_844_);
lean_dec_ref_known(v___x_843_, 1);
v___x_845_ = l_Lean_LocalDecl_type(v_a_844_);
lean_dec(v_a_844_);
v___x_846_ = l_Lean_Meta_matchEq_x3f(v___x_845_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v_a_847_; 
v_a_847_ = lean_ctor_get(v___x_846_, 0);
lean_inc(v_a_847_);
lean_dec_ref_known(v___x_846_, 1);
if (lean_obj_tag(v_a_847_) == 0)
{
lean_object* v___x_848_; lean_object* v___x_849_; 
lean_dec(v_a_842_);
lean_dec(v_a_673_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
v___x_848_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__7, &l_Lean_Meta_substCore___lam__2___closed__7_once, _init_l_Lean_Meta_substCore___lam__2___closed__7);
v___x_849_ = l_panic___at___00Lean_Meta_substCore_spec__1(v___x_848_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
return v___x_849_;
}
else
{
lean_object* v_val_850_; lean_object* v_snd_851_; lean_object* v_fst_852_; lean_object* v_snd_853_; lean_object* v_type_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___f_857_; lean_object* v___y_859_; 
v_val_850_ = lean_ctor_get(v_a_847_, 0);
lean_inc(v_val_850_);
lean_dec_ref_known(v_a_847_, 1);
v_snd_851_ = lean_ctor_get(v_val_850_, 1);
lean_inc(v_snd_851_);
lean_dec(v_val_850_);
v_fst_852_ = lean_ctor_get(v_snd_851_, 0);
lean_inc(v_fst_852_);
v_snd_853_ = lean_ctor_get(v_snd_851_, 1);
lean_inc(v_snd_853_);
lean_dec(v_snd_851_);
v_type_854_ = lean_ctor_get(v_a_842_, 2);
lean_inc_ref_n(v_type_854_, 2);
lean_dec(v_a_842_);
v___x_855_ = lean_box(v___x_675_);
v___x_856_ = lean_box(v___x_670_);
lean_inc_ref(v___x_666_);
lean_inc(v___x_667_);
lean_inc_ref(v___x_662_);
v___f_857_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__1___boxed), 12, 6);
lean_closure_set(v___f_857_, 0, v_type_854_);
lean_closure_set(v___f_857_, 1, v___x_662_);
lean_closure_set(v___f_857_, 2, v___x_667_);
lean_closure_set(v___f_857_, 3, v___x_666_);
lean_closure_set(v___f_857_, 4, v___x_855_);
lean_closure_set(v___f_857_, 5, v___x_856_);
if (v_symm_674_ == 0)
{
lean_dec(v_fst_852_);
v___y_859_ = v_snd_853_;
goto v___jp_858_;
}
else
{
lean_dec(v_snd_853_);
v___y_859_ = v_fst_852_;
goto v___jp_858_;
}
v___jp_858_:
{
lean_object* v___x_860_; lean_object* v_a_861_; lean_object* v___x_862_; lean_object* v_a_863_; uint8_t v___x_864_; 
v___x_860_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_859_, v___y_678_);
v_a_861_ = lean_ctor_get(v___x_860_, 0);
lean_inc(v_a_861_);
lean_dec_ref(v___x_860_);
lean_inc(v___x_659_);
lean_inc_ref(v_type_854_);
v___x_862_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_type_854_, v___x_659_, v___y_678_);
v_a_863_ = lean_ctor_get(v___x_862_, 0);
lean_inc(v_a_863_);
lean_dec_ref(v___x_862_);
v___x_864_ = lean_unbox(v_a_863_);
if (v___x_864_ == 0)
{
lean_object* v___x_865_; lean_object* v___x_866_; uint8_t v___x_867_; lean_object* v___x_868_; 
lean_dec_ref(v___f_857_);
v___x_865_ = lean_mk_empty_array_with_capacity(v___x_676_);
lean_inc_ref(v___x_666_);
v___x_866_ = lean_array_push(v___x_865_, v___x_666_);
v___x_867_ = 1;
lean_inc_ref(v_type_854_);
v___x_868_ = l_Lean_Meta_mkLambdaFVars(v___x_866_, v_type_854_, v___x_675_, v___x_670_, v___x_675_, v___x_670_, v___x_867_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref(v___x_866_);
if (lean_obj_tag(v___x_868_) == 0)
{
lean_object* v_a_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v_a_869_ = lean_ctor_get(v___x_868_, 0);
lean_inc(v_a_869_);
lean_dec_ref_known(v___x_868_, 1);
lean_inc_ref(v___x_666_);
v___x_870_ = l_Lean_Expr_replaceFVar(v_type_854_, v___x_666_, v_a_861_);
lean_dec_ref(v_type_854_);
v___x_871_ = lean_unbox(v_a_863_);
lean_dec(v_a_863_);
v___y_823_ = v_a_861_;
v___y_824_ = v___x_871_;
v_motive_825_ = v_a_869_;
v_newType_826_ = v___x_870_;
v___y_827_ = v___y_677_;
v___y_828_ = v___y_678_;
v___y_829_ = v___y_679_;
v___y_830_ = v___y_680_;
goto v___jp_822_;
}
else
{
lean_object* v_a_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_879_; 
lean_dec(v_a_863_);
lean_dec(v_a_861_);
lean_dec_ref(v_type_854_);
lean_dec(v_a_673_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
v_a_872_ = lean_ctor_get(v___x_868_, 0);
v_isSharedCheck_879_ = !lean_is_exclusive(v___x_868_);
if (v_isSharedCheck_879_ == 0)
{
v___x_874_ = v___x_868_;
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_a_872_);
lean_dec(v___x_868_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_879_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_877_; 
if (v_isShared_875_ == 0)
{
v___x_877_ = v___x_874_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_878_; 
v_reuseFailAlloc_878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_878_, 0, v_a_872_);
v___x_877_ = v_reuseFailAlloc_878_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
return v___x_877_;
}
}
}
}
else
{
lean_object* v___x_880_; lean_object* v___x_881_; 
lean_inc_ref(v___x_666_);
v___x_880_ = l_Lean_Expr_replaceFVar(v_type_854_, v___x_666_, v_a_861_);
lean_inc(v_a_861_);
v___x_881_ = l_Lean_Meta_mkEqRefl(v_a_861_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_881_) == 0)
{
lean_object* v_a_882_; lean_object* v___x_883_; 
v_a_882_ = lean_ctor_get(v___x_881_, 0);
lean_inc(v_a_882_);
lean_dec_ref_known(v___x_881_, 1);
lean_inc_ref(v___x_662_);
v___x_883_ = l_Lean_Expr_replaceFVar(v___x_880_, v___x_662_, v_a_882_);
lean_dec(v_a_882_);
lean_dec_ref(v___x_880_);
if (v_symm_674_ == 0)
{
lean_object* v___x_884_; 
lean_dec_ref(v_type_854_);
lean_inc_ref(v___x_666_);
lean_inc(v_a_861_);
v___x_884_ = l_Lean_Meta_mkEq(v_a_861_, v___x_666_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_884_) == 0)
{
lean_object* v_a_885_; lean_object* v___x_886_; lean_object* v___x_887_; 
v_a_885_ = lean_ctor_get(v___x_884_, 0);
lean_inc(v_a_885_);
lean_dec_ref_known(v___x_884_, 1);
v___x_886_ = ((lean_object*)(l_Lean_Meta_substCore___lam__2___closed__9));
v___x_887_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v___x_886_, v_a_885_, v___f_857_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; uint8_t v___x_889_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_889_ = lean_unbox(v_a_863_);
lean_dec(v_a_863_);
v___y_823_ = v_a_861_;
v___y_824_ = v___x_889_;
v_motive_825_ = v_a_888_;
v_newType_826_ = v___x_883_;
v___y_827_ = v___y_677_;
v___y_828_ = v___y_678_;
v___y_829_ = v___y_679_;
v___y_830_ = v___y_680_;
goto v___jp_822_;
}
else
{
lean_object* v_a_890_; lean_object* v___x_892_; uint8_t v_isShared_893_; uint8_t v_isSharedCheck_897_; 
lean_dec_ref(v___x_883_);
lean_dec(v_a_863_);
lean_dec(v_a_861_);
lean_dec(v_a_673_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
v_a_890_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_897_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_897_ == 0)
{
v___x_892_ = v___x_887_;
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
else
{
lean_inc(v_a_890_);
lean_dec(v___x_887_);
v___x_892_ = lean_box(0);
v_isShared_893_ = v_isSharedCheck_897_;
goto v_resetjp_891_;
}
v_resetjp_891_:
{
lean_object* v___x_895_; 
if (v_isShared_893_ == 0)
{
v___x_895_ = v___x_892_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v_a_890_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
else
{
lean_object* v_a_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_905_; 
lean_dec_ref(v___x_883_);
lean_dec(v_a_863_);
lean_dec(v_a_861_);
lean_dec_ref(v___f_857_);
lean_dec(v_a_673_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
v_a_898_ = lean_ctor_get(v___x_884_, 0);
v_isSharedCheck_905_ = !lean_is_exclusive(v___x_884_);
if (v_isSharedCheck_905_ == 0)
{
v___x_900_ = v___x_884_;
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_a_898_);
lean_dec(v___x_884_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_905_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_903_; 
if (v_isShared_901_ == 0)
{
v___x_903_ = v___x_900_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_a_898_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
else
{
lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; uint8_t v___x_909_; lean_object* v___x_910_; 
lean_dec_ref(v___f_857_);
v___x_906_ = lean_mk_empty_array_with_capacity(v___x_667_);
lean_inc_ref(v___x_666_);
v___x_907_ = lean_array_push(v___x_906_, v___x_666_);
lean_inc_ref(v___x_662_);
v___x_908_ = lean_array_push(v___x_907_, v___x_662_);
v___x_909_ = 1;
v___x_910_ = l_Lean_Meta_mkLambdaFVars(v___x_908_, v_type_854_, v___x_675_, v___x_670_, v___x_675_, v___x_670_, v___x_909_, v___y_677_, v___y_678_, v___y_679_, v___y_680_);
lean_dec_ref(v___x_908_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; uint8_t v___x_912_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v___x_912_ = lean_unbox(v_a_863_);
lean_dec(v_a_863_);
v___y_823_ = v_a_861_;
v___y_824_ = v___x_912_;
v_motive_825_ = v_a_911_;
v_newType_826_ = v___x_883_;
v___y_827_ = v___y_677_;
v___y_828_ = v___y_678_;
v___y_829_ = v___y_679_;
v___y_830_ = v___y_680_;
goto v___jp_822_;
}
else
{
lean_object* v_a_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_920_; 
lean_dec_ref(v___x_883_);
lean_dec(v_a_863_);
lean_dec(v_a_861_);
lean_dec(v_a_673_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
v_a_913_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_920_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_920_ == 0)
{
v___x_915_ = v___x_910_;
v_isShared_916_ = v_isSharedCheck_920_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_a_913_);
lean_dec(v___x_910_);
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
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
lean_dec_ref(v___x_880_);
lean_dec(v_a_863_);
lean_dec(v_a_861_);
lean_dec_ref(v___f_857_);
lean_dec_ref(v_type_854_);
lean_dec(v_a_673_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
v_a_921_ = lean_ctor_get(v___x_881_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_881_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_881_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_881_);
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
}
}
}
}
else
{
lean_object* v_a_929_; lean_object* v___x_931_; uint8_t v_isShared_932_; uint8_t v_isSharedCheck_936_; 
lean_dec(v_a_842_);
lean_dec(v_a_673_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
v_a_929_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_936_ == 0)
{
v___x_931_ = v___x_846_;
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
else
{
lean_inc(v_a_929_);
lean_dec(v___x_846_);
v___x_931_ = lean_box(0);
v_isShared_932_ = v_isSharedCheck_936_;
goto v_resetjp_930_;
}
v_resetjp_930_:
{
lean_object* v___x_934_; 
if (v_isShared_932_ == 0)
{
v___x_934_ = v___x_931_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_a_929_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_a_842_);
lean_dec(v_a_673_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
v_a_937_ = lean_ctor_get(v___x_843_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_843_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_843_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_843_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_a_673_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
v_a_945_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_841_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_841_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
v___jp_682_:
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_686_ = l_Lean_Meta_FVarSubst_insert(v___y_683_, v_fvarId_660_, v___y_685_);
v___x_687_ = l_Lean_Meta_FVarSubst_insert(v___x_686_, v_hFVarId_661_, v___x_662_);
v___x_688_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_688_, 0, v___x_687_);
lean_ctor_set(v___x_688_, 1, v___y_684_);
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v___x_688_);
return v___x_689_;
}
v___jp_690_:
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = lean_array_get_size(v___y_692_);
v___x_695_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_663_, v___y_692_, v___x_694_, v___x_694_, v_fvarSubst_664_);
lean_dec_ref(v___y_692_);
if (v_clearH_665_ == 0)
{
lean_object* v_a_696_; 
lean_dec_ref(v___y_691_);
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
lean_dec_ref(v___x_695_);
v___y_683_ = v_a_696_;
v___y_684_ = v___y_693_;
v___y_685_ = v___x_666_;
goto v___jp_682_;
}
else
{
lean_object* v_a_697_; 
lean_dec_ref(v___x_666_);
v_a_697_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_697_);
lean_dec_ref(v___x_695_);
v___y_683_ = v_a_697_;
v___y_684_ = v___y_693_;
v___y_685_ = v___y_691_;
goto v___jp_682_;
}
}
v___jp_698_:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_array_get_size(v_fst_663_);
v___x_706_ = lean_nat_sub(v___x_705_, v___x_667_);
lean_dec(v___x_667_);
lean_inc(v___x_706_);
v___x_707_ = l_Lean_Meta_introNCore(v_mvarId_700_, v___x_706_, v___x_668_, v_skip_669_, v___x_670_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v_options_709_; uint8_t v_hasTrace_710_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
lean_inc(v_a_708_);
lean_dec_ref_known(v___x_707_, 1);
v_options_709_ = lean_ctor_get(v___y_703_, 2);
v_hasTrace_710_ = lean_ctor_get_uint8(v_options_709_, sizeof(void*)*1);
if (v_hasTrace_710_ == 0)
{
lean_object* v_fst_711_; lean_object* v_snd_712_; 
lean_dec(v___x_706_);
lean_dec(v___x_671_);
v_fst_711_ = lean_ctor_get(v_a_708_, 0);
lean_inc(v_fst_711_);
v_snd_712_ = lean_ctor_get(v_a_708_, 1);
lean_inc(v_snd_712_);
lean_dec(v_a_708_);
v___y_691_ = v___y_699_;
v___y_692_ = v_fst_711_;
v___y_693_ = v_snd_712_;
goto v___jp_690_;
}
else
{
lean_object* v_fst_713_; lean_object* v_snd_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_742_; 
v_fst_713_ = lean_ctor_get(v_a_708_, 0);
v_snd_714_ = lean_ctor_get(v_a_708_, 1);
v_isSharedCheck_742_ = !lean_is_exclusive(v_a_708_);
if (v_isSharedCheck_742_ == 0)
{
v___x_716_ = v_a_708_;
v_isShared_717_ = v_isSharedCheck_742_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_snd_714_);
lean_inc(v_fst_713_);
lean_dec(v_a_708_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_742_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_inheritedTraceOptions_718_; lean_object* v___x_719_; lean_object* v___x_720_; uint8_t v___x_721_; 
v_inheritedTraceOptions_718_ = lean_ctor_get(v___y_703_, 13);
v___x_719_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
lean_inc(v___x_671_);
v___x_720_ = l_Lean_Name_append(v___x_719_, v___x_671_);
v___x_721_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_718_, v_options_709_, v___x_720_);
lean_dec(v___x_720_);
if (v___x_721_ == 0)
{
lean_del_object(v___x_716_);
lean_dec(v___x_706_);
lean_dec(v___x_671_);
v___y_691_ = v___y_699_;
v___y_692_ = v_fst_713_;
v___y_693_ = v_snd_714_;
goto v___jp_690_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_727_; 
v___x_722_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__1, &l_Lean_Meta_substCore___lam__2___closed__1_once, _init_l_Lean_Meta_substCore___lam__2___closed__1);
v___x_723_ = l_Nat_reprFast(v___x_706_);
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
v___x_728_ = lean_obj_once(&l_Lean_Meta_substCore___lam__2___closed__3, &l_Lean_Meta_substCore___lam__2___closed__3_once, _init_l_Lean_Meta_substCore___lam__2___closed__3);
v___x_729_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_729_, 0, v___x_727_);
lean_ctor_set(v___x_729_, 1, v___x_728_);
lean_inc(v_snd_714_);
v___x_730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_730_, 0, v_snd_714_);
v___x_731_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_731_, 0, v___x_729_);
lean_ctor_set(v___x_731_, 1, v___x_730_);
v___x_732_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_671_, v___x_731_, v___y_701_, v___y_702_, v___y_703_, v___y_704_);
if (lean_obj_tag(v___x_732_) == 0)
{
lean_dec_ref_known(v___x_732_, 1);
v___y_691_ = v___y_699_;
v___y_692_ = v_fst_713_;
v___y_693_ = v_snd_714_;
goto v___jp_690_;
}
else
{
lean_object* v_a_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_740_; 
lean_dec(v_snd_714_);
lean_dec(v_fst_713_);
lean_dec_ref(v___y_699_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
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
lean_dec(v___x_706_);
lean_dec_ref(v___y_699_);
lean_dec(v___x_671_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
v_a_743_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_750_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_750_ == 0)
{
v___x_745_ = v___x_707_;
v_isShared_746_ = v_isSharedCheck_750_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_a_743_);
lean_dec(v___x_707_);
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
v___x_759_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_snd_658_, v_newVal_754_, v___y_756_);
lean_dec_ref(v___x_759_);
v___x_760_ = l_Lean_Expr_mvarId_x21(v___y_753_);
lean_dec_ref(v___y_753_);
if (v_clearH_665_ == 0)
{
lean_dec(v___x_672_);
lean_dec(v___x_659_);
v___y_699_ = v___y_752_;
v_mvarId_700_ = v___x_760_;
v___y_701_ = v___y_755_;
v___y_702_ = v___y_756_;
v___y_703_ = v___y_757_;
v___y_704_ = v___y_758_;
goto v___jp_698_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = l_Lean_MVarId_clear(v___x_760_, v___x_659_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_761_) == 0)
{
lean_object* v_a_762_; lean_object* v___x_763_; 
v_a_762_ = lean_ctor_get(v___x_761_, 0);
lean_inc(v_a_762_);
lean_dec_ref_known(v___x_761_, 1);
v___x_763_ = l_Lean_MVarId_clear(v_a_762_, v___x_672_, v___y_755_, v___y_756_, v___y_757_, v___y_758_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v___y_699_ = v___y_752_;
v_mvarId_700_ = v_a_764_;
v___y_701_ = v___y_755_;
v___y_702_ = v___y_756_;
v___y_703_ = v___y_757_;
v___y_704_ = v___y_758_;
goto v___jp_698_;
}
else
{
lean_object* v_a_765_; lean_object* v___x_767_; uint8_t v_isShared_768_; uint8_t v_isSharedCheck_772_; 
lean_dec_ref(v___y_752_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
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
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
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
v___x_791_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___y_785_, v_a_673_, v___y_787_, v___y_788_, v___y_789_, v___y_790_);
if (lean_obj_tag(v___x_791_) == 0)
{
if (v___y_783_ == 0)
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
v___y_752_ = v___y_782_;
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
lean_dec_ref(v___y_782_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
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
v___y_752_ = v___y_782_;
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
lean_dec_ref(v___y_782_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
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
lean_dec_ref(v___y_784_);
lean_dec_ref(v___y_782_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
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
if (v_symm_674_ == 0)
{
lean_object* v___x_831_; 
lean_inc_ref(v___x_662_);
v___x_831_ = l_Lean_Meta_mkEqSymm(v___x_662_, v___y_827_, v___y_828_, v___y_829_, v___y_830_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
lean_inc(v_a_832_);
lean_dec_ref_known(v___x_831_, 1);
v___y_782_ = v___y_823_;
v___y_783_ = v___y_824_;
v___y_784_ = v_motive_825_;
v___y_785_ = v_newType_826_;
v_major_786_ = v_a_832_;
v___y_787_ = v___y_827_;
v___y_788_ = v___y_828_;
v___y_789_ = v___y_829_;
v___y_790_ = v___y_830_;
goto v___jp_781_;
}
else
{
lean_object* v_a_833_; lean_object* v___x_835_; uint8_t v_isShared_836_; uint8_t v_isSharedCheck_840_; 
lean_dec_ref(v_newType_826_);
lean_dec_ref(v_motive_825_);
lean_dec_ref(v___y_823_);
lean_dec(v_a_673_);
lean_dec(v___x_672_);
lean_dec(v___x_671_);
lean_dec(v___x_668_);
lean_dec(v___x_667_);
lean_dec_ref(v___x_666_);
lean_dec(v_fvarSubst_664_);
lean_dec_ref(v___x_662_);
lean_dec(v_hFVarId_661_);
lean_dec(v_fvarId_660_);
lean_dec(v___x_659_);
lean_dec(v_snd_658_);
v_a_833_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_840_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_840_ == 0)
{
v___x_835_ = v___x_831_;
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
else
{
lean_inc(v_a_833_);
lean_dec(v___x_831_);
v___x_835_ = lean_box(0);
v_isShared_836_ = v_isSharedCheck_840_;
goto v_resetjp_834_;
}
v_resetjp_834_:
{
lean_object* v___x_838_; 
if (v_isShared_836_ == 0)
{
v___x_838_ = v___x_835_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v_a_833_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
}
}
else
{
lean_inc_ref(v___x_662_);
v___y_782_ = v___y_823_;
v___y_783_ = v___y_824_;
v___y_784_ = v_motive_825_;
v___y_785_ = v_newType_826_;
v_major_786_ = v___x_662_;
v___y_787_ = v___y_827_;
v___y_788_ = v___y_828_;
v___y_789_ = v___y_829_;
v___y_790_ = v___y_830_;
goto v___jp_781_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__2___boxed(lean_object** _args){
lean_object* v_snd_953_ = _args[0];
lean_object* v___x_954_ = _args[1];
lean_object* v_fvarId_955_ = _args[2];
lean_object* v_hFVarId_956_ = _args[3];
lean_object* v___x_957_ = _args[4];
lean_object* v_fst_958_ = _args[5];
lean_object* v_fvarSubst_959_ = _args[6];
lean_object* v_clearH_960_ = _args[7];
lean_object* v___x_961_ = _args[8];
lean_object* v___x_962_ = _args[9];
lean_object* v___x_963_ = _args[10];
lean_object* v_skip_964_ = _args[11];
lean_object* v___x_965_ = _args[12];
lean_object* v___x_966_ = _args[13];
lean_object* v___x_967_ = _args[14];
lean_object* v_a_968_ = _args[15];
lean_object* v_symm_969_ = _args[16];
lean_object* v___x_970_ = _args[17];
lean_object* v___x_971_ = _args[18];
lean_object* v___y_972_ = _args[19];
lean_object* v___y_973_ = _args[20];
lean_object* v___y_974_ = _args[21];
lean_object* v___y_975_ = _args[22];
lean_object* v___y_976_ = _args[23];
_start:
{
uint8_t v_clearH_boxed_977_; uint8_t v_skip_boxed_978_; uint8_t v___x_33810__boxed_979_; uint8_t v_symm_boxed_980_; uint8_t v___x_33814__boxed_981_; lean_object* v_res_982_; 
v_clearH_boxed_977_ = lean_unbox(v_clearH_960_);
v_skip_boxed_978_ = lean_unbox(v_skip_964_);
v___x_33810__boxed_979_ = lean_unbox(v___x_965_);
v_symm_boxed_980_ = lean_unbox(v_symm_969_);
v___x_33814__boxed_981_ = lean_unbox(v___x_970_);
v_res_982_ = l_Lean_Meta_substCore___lam__2(v_snd_953_, v___x_954_, v_fvarId_955_, v_hFVarId_956_, v___x_957_, v_fst_958_, v_fvarSubst_959_, v_clearH_boxed_977_, v___x_961_, v___x_962_, v___x_963_, v_skip_boxed_978_, v___x_33810__boxed_979_, v___x_966_, v___x_967_, v_a_968_, v_symm_boxed_980_, v___x_33814__boxed_981_, v___x_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___x_971_);
lean_dec_ref(v_fst_958_);
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
lean_object* v_val_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1461_; 
v_val_1139_ = lean_ctor_get(v_a_1136_, 0);
v_isSharedCheck_1461_ = !lean_is_exclusive(v_a_1136_);
if (v_isSharedCheck_1461_ == 0)
{
v___x_1141_ = v_a_1136_;
v_isShared_1142_ = v_isSharedCheck_1461_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_val_1139_);
lean_dec(v_a_1136_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1461_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v_snd_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1459_; 
v_snd_1143_ = lean_ctor_get(v_val_1139_, 1);
v_isSharedCheck_1459_ = !lean_is_exclusive(v_val_1139_);
if (v_isSharedCheck_1459_ == 0)
{
lean_object* v_unused_1460_; 
v_unused_1460_ = lean_ctor_get(v_val_1139_, 0);
lean_dec(v_unused_1460_);
v___x_1145_ = v_val_1139_;
v_isShared_1146_ = v_isSharedCheck_1459_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_snd_1143_);
lean_dec(v_val_1139_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1459_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v_fst_1147_; lean_object* v_snd_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1458_; 
v_fst_1147_ = lean_ctor_get(v_snd_1143_, 0);
v_snd_1148_ = lean_ctor_get(v_snd_1143_, 1);
v_isSharedCheck_1458_ = !lean_is_exclusive(v_snd_1143_);
if (v_isSharedCheck_1458_ == 0)
{
v___x_1150_ = v_snd_1143_;
v_isShared_1151_ = v_isSharedCheck_1458_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_snd_1148_);
lean_inc(v_fst_1147_);
lean_dec(v_snd_1143_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1458_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
uint8_t v___x_1152_; lean_object* v___y_1154_; lean_object* v___y_1155_; lean_object* v___y_1156_; lean_object* v___y_1157_; lean_object* v___y_1158_; lean_object* v___y_1159_; lean_object* v___y_1160_; lean_object* v___y_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; lean_object* v___y_1164_; lean_object* v___y_1165_; uint8_t v___y_1166_; lean_object* v___y_1167_; lean_object* v___y_1168_; lean_object* v___y_1169_; lean_object* v___y_1170_; uint8_t v_skip_1171_; lean_object* v___y_1180_; lean_object* v___y_1181_; lean_object* v___y_1182_; uint8_t v___y_1183_; lean_object* v___y_1184_; lean_object* v___y_1185_; lean_object* v___y_1186_; lean_object* v___y_1187_; lean_object* v___y_1188_; lean_object* v___y_1189_; lean_object* v___y_1190_; uint8_t v___y_1191_; lean_object* v___y_1192_; lean_object* v___y_1193_; lean_object* v___y_1194_; lean_object* v___y_1195_; lean_object* v___y_1221_; lean_object* v___y_1222_; lean_object* v___y_1223_; uint8_t v___y_1224_; lean_object* v___y_1225_; lean_object* v___y_1226_; lean_object* v___y_1227_; lean_object* v___y_1228_; lean_object* v___y_1229_; lean_object* v___y_1230_; lean_object* v___y_1231_; lean_object* v___y_1232_; lean_object* v___y_1233_; uint8_t v___y_1234_; lean_object* v___y_1235_; lean_object* v___y_1236_; lean_object* v___y_1237_; lean_object* v___y_1238_; lean_object* v___y_1271_; lean_object* v___y_1272_; lean_object* v___y_1273_; uint8_t v___y_1274_; lean_object* v___y_1275_; lean_object* v___y_1276_; lean_object* v___y_1277_; lean_object* v___y_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; uint8_t v___y_1281_; lean_object* v___y_1282_; lean_object* v___y_1283_; lean_object* v___y_1284_; lean_object* v___y_1285_; lean_object* v___y_1329_; lean_object* v___y_1330_; lean_object* v___y_1331_; lean_object* v___y_1332_; lean_object* v___y_1333_; lean_object* v___y_1334_; lean_object* v___y_1335_; lean_object* v___y_1336_; lean_object* v___y_1337_; lean_object* v___y_1385_; lean_object* v___y_1386_; lean_object* v___y_1387_; lean_object* v___y_1388_; lean_object* v___y_1389_; lean_object* v___y_1390_; lean_object* v___y_1391_; lean_object* v___y_1392_; lean_object* v___y_1393_; lean_object* v___y_1394_; lean_object* v___y_1395_; lean_object* v___y_1421_; lean_object* v___y_1422_; lean_object* v___y_1454_; 
v___x_1152_ = 1;
if (v_symm_1069_ == 0)
{
lean_inc(v_fst_1147_);
v___y_1454_ = v_fst_1147_;
goto v___jp_1453_;
}
else
{
lean_inc(v_snd_1148_);
v___y_1454_ = v_snd_1148_;
goto v___jp_1453_;
}
v___jp_1153_:
{
lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___f_1177_; lean_object* v___x_1178_; 
v___x_1172_ = lean_box(v_clearH_1067_);
v___x_1173_ = lean_box(v_skip_1171_);
v___x_1174_ = lean_box(v___x_1152_);
v___x_1175_ = lean_box(v_symm_1069_);
v___x_1176_ = lean_box(v___y_1166_);
v___f_1177_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__2___boxed), 24, 19);
lean_closure_set(v___f_1177_, 0, v___y_1160_);
lean_closure_set(v___f_1177_, 1, v___y_1157_);
lean_closure_set(v___f_1177_, 2, v___y_1162_);
lean_closure_set(v___f_1177_, 3, v_hFVarId_1065_);
lean_closure_set(v___f_1177_, 4, v___y_1159_);
lean_closure_set(v___f_1177_, 5, v___y_1161_);
lean_closure_set(v___f_1177_, 6, v_fvarSubst_1068_);
lean_closure_set(v___f_1177_, 7, v___x_1172_);
lean_closure_set(v___f_1177_, 8, v___y_1158_);
lean_closure_set(v___f_1177_, 9, v___y_1165_);
lean_closure_set(v___f_1177_, 10, v___y_1169_);
lean_closure_set(v___f_1177_, 11, v___x_1173_);
lean_closure_set(v___f_1177_, 12, v___x_1174_);
lean_closure_set(v___f_1177_, 13, v___y_1170_);
lean_closure_set(v___f_1177_, 14, v___y_1156_);
lean_closure_set(v___f_1177_, 15, v_a_1115_);
lean_closure_set(v___f_1177_, 16, v___x_1175_);
lean_closure_set(v___f_1177_, 17, v___x_1176_);
lean_closure_set(v___f_1177_, 18, v___y_1163_);
v___x_1178_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v___y_1154_, v___f_1177_, v___y_1167_, v___y_1164_, v___y_1155_, v___y_1168_);
lean_dec(v___y_1168_);
lean_dec_ref(v___y_1155_);
lean_dec(v___y_1164_);
lean_dec_ref(v___y_1167_);
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
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
v___y_1154_ = v___y_1187_;
v___y_1155_ = v___y_1194_;
v___y_1156_ = v___x_1197_;
v___y_1157_ = v___x_1200_;
v___y_1158_ = v___x_1198_;
v___y_1159_ = v___x_1201_;
v___y_1160_ = v___y_1186_;
v___y_1161_ = v___y_1180_;
v___y_1162_ = v___y_1181_;
v___y_1163_ = v___x_1199_;
v___y_1164_ = v___y_1193_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1183_;
v___y_1167_ = v___y_1192_;
v___y_1168_ = v___y_1195_;
v___y_1169_ = v___y_1184_;
v___y_1170_ = v___y_1185_;
v_skip_1171_ = v___y_1191_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1202_; uint8_t v___x_1203_; 
v___x_1202_ = lean_array_get_size(v___y_1188_);
lean_dec_ref(v___y_1188_);
v___x_1203_ = lean_nat_dec_eq(v___x_1202_, v___y_1189_);
lean_dec(v___y_1189_);
if (v___x_1203_ == 0)
{
v___y_1154_ = v___y_1187_;
v___y_1155_ = v___y_1194_;
v___y_1156_ = v___x_1197_;
v___y_1157_ = v___x_1200_;
v___y_1158_ = v___x_1198_;
v___y_1159_ = v___x_1201_;
v___y_1160_ = v___y_1186_;
v___y_1161_ = v___y_1180_;
v___y_1162_ = v___y_1181_;
v___y_1163_ = v___x_1199_;
v___y_1164_ = v___y_1193_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1183_;
v___y_1167_ = v___y_1192_;
v___y_1168_ = v___y_1195_;
v___y_1169_ = v___y_1184_;
v___y_1170_ = v___y_1185_;
v_skip_1171_ = v___y_1191_;
goto v___jp_1153_;
}
else
{
lean_object* v___x_1204_; 
lean_inc(v___y_1187_);
v___x_1204_ = l_Lean_MVarId_getType(v___y_1187_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1206_; lean_object* v_a_1207_; uint8_t v___x_1208_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
lean_inc_n(v_a_1205_, 2);
lean_dec_ref_known(v___x_1204_, 1);
lean_inc(v___x_1197_);
v___x_1206_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1205_, v___x_1197_, v___y_1193_);
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
lean_inc(v_a_1207_);
lean_dec_ref(v___x_1206_);
v___x_1208_ = lean_unbox(v_a_1207_);
lean_dec(v_a_1207_);
if (v___x_1208_ == 0)
{
lean_object* v___x_1209_; lean_object* v_a_1210_; uint8_t v___x_1211_; 
lean_inc(v___x_1200_);
v___x_1209_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1205_, v___x_1200_, v___y_1193_);
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
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v_a_1115_);
lean_dec(v_hFVarId_1065_);
v___y_1077_ = v___y_1187_;
v___y_1078_ = v___x_1197_;
v___y_1079_ = v___y_1194_;
v___y_1080_ = v___y_1193_;
v___y_1081_ = v___x_1200_;
v___y_1082_ = v___y_1192_;
v___y_1083_ = v___y_1195_;
goto v___jp_1076_;
}
else
{
v___y_1154_ = v___y_1187_;
v___y_1155_ = v___y_1194_;
v___y_1156_ = v___x_1197_;
v___y_1157_ = v___x_1200_;
v___y_1158_ = v___x_1198_;
v___y_1159_ = v___x_1201_;
v___y_1160_ = v___y_1186_;
v___y_1161_ = v___y_1180_;
v___y_1162_ = v___y_1181_;
v___y_1163_ = v___x_1199_;
v___y_1164_ = v___y_1193_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1183_;
v___y_1167_ = v___y_1192_;
v___y_1168_ = v___y_1195_;
v___y_1169_ = v___y_1184_;
v___y_1170_ = v___y_1185_;
v_skip_1171_ = v___y_1191_;
goto v___jp_1153_;
}
}
else
{
lean_dec(v_a_1205_);
v___y_1154_ = v___y_1187_;
v___y_1155_ = v___y_1194_;
v___y_1156_ = v___x_1197_;
v___y_1157_ = v___x_1200_;
v___y_1158_ = v___x_1198_;
v___y_1159_ = v___x_1201_;
v___y_1160_ = v___y_1186_;
v___y_1161_ = v___y_1180_;
v___y_1162_ = v___y_1181_;
v___y_1163_ = v___x_1199_;
v___y_1164_ = v___y_1193_;
v___y_1165_ = v___y_1182_;
v___y_1166_ = v___y_1183_;
v___y_1167_ = v___y_1192_;
v___y_1168_ = v___y_1195_;
v___y_1169_ = v___y_1184_;
v___y_1170_ = v___y_1185_;
v_skip_1171_ = v___y_1191_;
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
lean_dec(v___y_1187_);
lean_dec(v___y_1186_);
lean_dec(v___y_1185_);
lean_dec(v___y_1184_);
lean_dec(v___y_1182_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
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
lean_dec(v___y_1232_);
lean_del_object(v___x_1150_);
v___y_1180_ = v___y_1221_;
v___y_1181_ = v___y_1222_;
v___y_1182_ = v___y_1223_;
v___y_1183_ = v___y_1224_;
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1227_;
v___y_1186_ = v___y_1226_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1229_;
v___y_1189_ = v___y_1230_;
v___y_1190_ = v___y_1233_;
v___y_1191_ = v___y_1234_;
v___y_1192_ = v___y_1235_;
v___y_1193_ = v___y_1236_;
v___y_1194_ = v___y_1237_;
v___y_1195_ = v___y_1238_;
goto v___jp_1179_;
}
else
{
lean_object* v___x_1242_; size_t v_sz_1243_; size_t v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1251_; 
v___x_1242_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__11, &l_Lean_Meta_substCore___lam__3___closed__11_once, _init_l_Lean_Meta_substCore___lam__3___closed__11);
v_sz_1243_ = lean_array_size(v___y_1229_);
v___x_1244_ = ((size_t)0ULL);
lean_inc_ref(v___y_1229_);
v___x_1245_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_substCore_spec__8(v_sz_1243_, v___x_1244_, v___y_1229_);
v___x_1246_ = lean_array_to_list(v___x_1245_);
v___x_1247_ = lean_box(0);
v___x_1248_ = l_List_mapTR_loop___at___00Lean_Meta_substCore_spec__9(v___x_1246_, v___x_1247_);
v___x_1249_ = l_Lean_MessageData_ofList(v___x_1248_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set_tag(v___x_1150_, 7);
lean_ctor_set(v___x_1150_, 1, v___x_1249_);
lean_ctor_set(v___x_1150_, 0, v___x_1242_);
v___x_1251_ = v___x_1150_;
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
v___x_1252_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1232_, v___x_1251_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1252_) == 0)
{
lean_dec_ref_known(v___x_1252_, 1);
v___y_1180_ = v___y_1221_;
v___y_1181_ = v___y_1222_;
v___y_1182_ = v___y_1223_;
v___y_1183_ = v___y_1224_;
v___y_1184_ = v___y_1225_;
v___y_1185_ = v___y_1227_;
v___y_1186_ = v___y_1226_;
v___y_1187_ = v___y_1228_;
v___y_1188_ = v___y_1229_;
v___y_1189_ = v___y_1230_;
v___y_1190_ = v___y_1233_;
v___y_1191_ = v___y_1234_;
v___y_1192_ = v___y_1235_;
v___y_1193_ = v___y_1236_;
v___y_1194_ = v___y_1237_;
v___y_1195_ = v___y_1238_;
goto v___jp_1179_;
}
else
{
lean_object* v_a_1253_; lean_object* v___x_1255_; uint8_t v_isShared_1256_; uint8_t v_isSharedCheck_1260_; 
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
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
lean_dec_ref(v___y_1233_);
lean_dec(v___y_1232_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec(v___y_1225_);
lean_dec(v___y_1223_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
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
lean_object* v___x_1286_; lean_object* v___x_1287_; 
v___x_1286_ = lean_box(0);
lean_inc(v___y_1279_);
v___x_1287_ = l_Lean_Meta_introNCore(v___y_1276_, v___y_1279_, v___x_1286_, v___y_1281_, v___x_1152_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v_a_1288_; lean_object* v_fst_1289_; lean_object* v_snd_1290_; lean_object* v___x_1292_; uint8_t v_isShared_1293_; uint8_t v_isSharedCheck_1319_; 
v_a_1288_ = lean_ctor_get(v___x_1287_, 0);
lean_inc(v_a_1288_);
lean_dec_ref_known(v___x_1287_, 1);
v_fst_1289_ = lean_ctor_get(v_a_1288_, 0);
v_snd_1290_ = lean_ctor_get(v_a_1288_, 1);
v_isSharedCheck_1319_ = !lean_is_exclusive(v_a_1288_);
if (v_isSharedCheck_1319_ == 0)
{
v___x_1292_ = v_a_1288_;
v_isShared_1293_ = v_isSharedCheck_1319_;
goto v_resetjp_1291_;
}
else
{
lean_inc(v_snd_1290_);
lean_inc(v_fst_1289_);
lean_dec(v_a_1288_);
v___x_1292_ = lean_box(0);
v_isShared_1293_ = v_isSharedCheck_1319_;
goto v_resetjp_1291_;
}
v_resetjp_1291_:
{
lean_object* v___x_1294_; 
lean_inc_ref(v___y_1278_);
lean_inc(v___y_1285_);
lean_inc_ref(v___y_1284_);
lean_inc(v___y_1283_);
lean_inc_ref(v___y_1282_);
v___x_1294_ = lean_apply_5(v___y_1278_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_, lean_box(0));
if (lean_obj_tag(v___x_1294_) == 0)
{
lean_object* v_a_1295_; uint8_t v___x_1296_; 
v_a_1295_ = lean_ctor_get(v___x_1294_, 0);
lean_inc(v_a_1295_);
lean_dec_ref_known(v___x_1294_, 1);
v___x_1296_ = lean_unbox(v_a_1295_);
lean_dec(v_a_1295_);
if (v___x_1296_ == 0)
{
lean_del_object(v___x_1292_);
lean_inc(v_snd_1290_);
v___y_1221_ = v___y_1271_;
v___y_1222_ = v___y_1272_;
v___y_1223_ = v___y_1273_;
v___y_1224_ = v___y_1274_;
v___y_1225_ = v___x_1286_;
v___y_1226_ = v_snd_1290_;
v___y_1227_ = v___y_1275_;
v___y_1228_ = v_snd_1290_;
v___y_1229_ = v___y_1277_;
v___y_1230_ = v___y_1279_;
v___y_1231_ = v___y_1278_;
v___y_1232_ = v___y_1280_;
v___y_1233_ = v_fst_1289_;
v___y_1234_ = v___y_1281_;
v___y_1235_ = v___y_1282_;
v___y_1236_ = v___y_1283_;
v___y_1237_ = v___y_1284_;
v___y_1238_ = v___y_1285_;
goto v___jp_1220_;
}
else
{
lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1297_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__13, &l_Lean_Meta_substCore___lam__3___closed__13_once, _init_l_Lean_Meta_substCore___lam__3___closed__13);
lean_inc(v_snd_1290_);
v___x_1298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1298_, 0, v_snd_1290_);
if (v_isShared_1293_ == 0)
{
lean_ctor_set_tag(v___x_1292_, 7);
lean_ctor_set(v___x_1292_, 1, v___x_1298_);
lean_ctor_set(v___x_1292_, 0, v___x_1297_);
v___x_1300_ = v___x_1292_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1310_; 
v_reuseFailAlloc_1310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1297_);
lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1310_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1301_; 
lean_inc(v___y_1280_);
v___x_1301_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1280_, v___x_1300_, v___y_1282_, v___y_1283_, v___y_1284_, v___y_1285_);
if (lean_obj_tag(v___x_1301_) == 0)
{
lean_dec_ref_known(v___x_1301_, 1);
lean_inc(v_snd_1290_);
v___y_1221_ = v___y_1271_;
v___y_1222_ = v___y_1272_;
v___y_1223_ = v___y_1273_;
v___y_1224_ = v___y_1274_;
v___y_1225_ = v___x_1286_;
v___y_1226_ = v_snd_1290_;
v___y_1227_ = v___y_1275_;
v___y_1228_ = v_snd_1290_;
v___y_1229_ = v___y_1277_;
v___y_1230_ = v___y_1279_;
v___y_1231_ = v___y_1278_;
v___y_1232_ = v___y_1280_;
v___y_1233_ = v_fst_1289_;
v___y_1234_ = v___y_1281_;
v___y_1235_ = v___y_1282_;
v___y_1236_ = v___y_1283_;
v___y_1237_ = v___y_1284_;
v___y_1238_ = v___y_1285_;
goto v___jp_1220_;
}
else
{
lean_object* v_a_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1309_; 
lean_dec(v_snd_1290_);
lean_dec(v_fst_1289_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1275_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1302_ = lean_ctor_get(v___x_1301_, 0);
v_isSharedCheck_1309_ = !lean_is_exclusive(v___x_1301_);
if (v_isSharedCheck_1309_ == 0)
{
v___x_1304_ = v___x_1301_;
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
else
{
lean_inc(v_a_1302_);
lean_dec(v___x_1301_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1309_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1307_; 
if (v_isShared_1305_ == 0)
{
v___x_1307_ = v___x_1304_;
goto v_reusejp_1306_;
}
else
{
lean_object* v_reuseFailAlloc_1308_; 
v_reuseFailAlloc_1308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1308_, 0, v_a_1302_);
v___x_1307_ = v_reuseFailAlloc_1308_;
goto v_reusejp_1306_;
}
v_reusejp_1306_:
{
return v___x_1307_;
}
}
}
}
}
}
else
{
lean_object* v_a_1311_; lean_object* v___x_1313_; uint8_t v_isShared_1314_; uint8_t v_isSharedCheck_1318_; 
lean_del_object(v___x_1292_);
lean_dec(v_snd_1290_);
lean_dec(v_fst_1289_);
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1275_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1311_ = lean_ctor_get(v___x_1294_, 0);
v_isSharedCheck_1318_ = !lean_is_exclusive(v___x_1294_);
if (v_isSharedCheck_1318_ == 0)
{
v___x_1313_ = v___x_1294_;
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
else
{
lean_inc(v_a_1311_);
lean_dec(v___x_1294_);
v___x_1313_ = lean_box(0);
v_isShared_1314_ = v_isSharedCheck_1318_;
goto v_resetjp_1312_;
}
v_resetjp_1312_:
{
lean_object* v___x_1316_; 
if (v_isShared_1314_ == 0)
{
v___x_1316_ = v___x_1313_;
goto v_reusejp_1315_;
}
else
{
lean_object* v_reuseFailAlloc_1317_; 
v_reuseFailAlloc_1317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1317_, 0, v_a_1311_);
v___x_1316_ = v_reuseFailAlloc_1317_;
goto v_reusejp_1315_;
}
v_reusejp_1315_:
{
return v___x_1316_;
}
}
}
}
}
else
{
lean_object* v_a_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1327_; 
lean_dec(v___y_1285_);
lean_dec_ref(v___y_1284_);
lean_dec(v___y_1283_);
lean_dec_ref(v___y_1282_);
lean_dec(v___y_1280_);
lean_dec(v___y_1279_);
lean_dec_ref(v___y_1277_);
lean_dec(v___y_1275_);
lean_dec(v___y_1273_);
lean_dec(v___y_1272_);
lean_dec_ref(v___y_1271_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1320_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1322_ = v___x_1287_;
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_a_1320_);
lean_dec(v___x_1287_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1327_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1325_; 
if (v_isShared_1323_ == 0)
{
v___x_1325_ = v___x_1322_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v_a_1320_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
v___jp_1328_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; uint8_t v___x_1342_; lean_object* v___x_1343_; 
v___x_1338_ = lean_unsigned_to_nat(2u);
v___x_1339_ = lean_mk_empty_array_with_capacity(v___x_1338_);
v___x_1340_ = lean_array_push(v___x_1339_, v___y_1331_);
lean_inc(v_hFVarId_1065_);
v___x_1341_ = lean_array_push(v___x_1340_, v_hFVarId_1065_);
v___x_1342_ = 0;
v___x_1343_ = l_Lean_MVarId_revert(v_mvarId_1064_, v___x_1341_, v___x_1152_, v___x_1342_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1343_) == 0)
{
lean_object* v_a_1344_; lean_object* v_fst_1345_; lean_object* v_snd_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1375_; 
v_a_1344_ = lean_ctor_get(v___x_1343_, 0);
lean_inc(v_a_1344_);
lean_dec_ref_known(v___x_1343_, 1);
v_fst_1345_ = lean_ctor_get(v_a_1344_, 0);
v_snd_1346_ = lean_ctor_get(v_a_1344_, 1);
v_isSharedCheck_1375_ = !lean_is_exclusive(v_a_1344_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1348_ = v_a_1344_;
v_isShared_1349_ = v_isSharedCheck_1375_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_snd_1346_);
lean_inc(v_fst_1345_);
lean_dec(v_a_1344_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1375_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; 
lean_inc_ref(v___y_1332_);
lean_inc(v___y_1337_);
lean_inc_ref(v___y_1336_);
lean_inc(v___y_1335_);
lean_inc_ref(v___y_1334_);
v___x_1350_ = lean_apply_5(v___y_1332_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_, lean_box(0));
if (lean_obj_tag(v___x_1350_) == 0)
{
lean_object* v_a_1351_; uint8_t v___x_1352_; 
v_a_1351_ = lean_ctor_get(v___x_1350_, 0);
lean_inc(v_a_1351_);
lean_dec_ref_known(v___x_1350_, 1);
v___x_1352_ = lean_unbox(v_a_1351_);
lean_dec(v_a_1351_);
if (v___x_1352_ == 0)
{
lean_del_object(v___x_1348_);
lean_inc(v_fst_1345_);
v___y_1271_ = v_fst_1345_;
v___y_1272_ = v___y_1329_;
v___y_1273_ = v___x_1338_;
v___y_1274_ = v___x_1342_;
v___y_1275_ = v___y_1330_;
v___y_1276_ = v_snd_1346_;
v___y_1277_ = v_fst_1345_;
v___y_1278_ = v___y_1332_;
v___y_1279_ = v___x_1338_;
v___y_1280_ = v___y_1333_;
v___y_1281_ = v___x_1342_;
v___y_1282_ = v___y_1334_;
v___y_1283_ = v___y_1335_;
v___y_1284_ = v___y_1336_;
v___y_1285_ = v___y_1337_;
goto v___jp_1270_;
}
else
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1356_; 
v___x_1353_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__15, &l_Lean_Meta_substCore___lam__3___closed__15_once, _init_l_Lean_Meta_substCore___lam__3___closed__15);
lean_inc(v_snd_1346_);
v___x_1354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1354_, 0, v_snd_1346_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set_tag(v___x_1348_, 7);
lean_ctor_set(v___x_1348_, 1, v___x_1354_);
lean_ctor_set(v___x_1348_, 0, v___x_1353_);
v___x_1356_ = v___x_1348_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1366_; 
v_reuseFailAlloc_1366_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1366_, 0, v___x_1353_);
lean_ctor_set(v_reuseFailAlloc_1366_, 1, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1366_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
lean_object* v___x_1357_; 
lean_inc(v___y_1333_);
v___x_1357_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___y_1333_, v___x_1356_, v___y_1334_, v___y_1335_, v___y_1336_, v___y_1337_);
if (lean_obj_tag(v___x_1357_) == 0)
{
lean_dec_ref_known(v___x_1357_, 1);
lean_inc(v_fst_1345_);
v___y_1271_ = v_fst_1345_;
v___y_1272_ = v___y_1329_;
v___y_1273_ = v___x_1338_;
v___y_1274_ = v___x_1342_;
v___y_1275_ = v___y_1330_;
v___y_1276_ = v_snd_1346_;
v___y_1277_ = v_fst_1345_;
v___y_1278_ = v___y_1332_;
v___y_1279_ = v___x_1338_;
v___y_1280_ = v___y_1333_;
v___y_1281_ = v___x_1342_;
v___y_1282_ = v___y_1334_;
v___y_1283_ = v___y_1335_;
v___y_1284_ = v___y_1336_;
v___y_1285_ = v___y_1337_;
goto v___jp_1270_;
}
else
{
lean_object* v_a_1358_; lean_object* v___x_1360_; uint8_t v_isShared_1361_; uint8_t v_isSharedCheck_1365_; 
lean_dec(v_snd_1346_);
lean_dec(v_fst_1345_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec(v___y_1330_);
lean_dec(v___y_1329_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1358_ = lean_ctor_get(v___x_1357_, 0);
v_isSharedCheck_1365_ = !lean_is_exclusive(v___x_1357_);
if (v_isSharedCheck_1365_ == 0)
{
v___x_1360_ = v___x_1357_;
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
else
{
lean_inc(v_a_1358_);
lean_dec(v___x_1357_);
v___x_1360_ = lean_box(0);
v_isShared_1361_ = v_isSharedCheck_1365_;
goto v_resetjp_1359_;
}
v_resetjp_1359_:
{
lean_object* v___x_1363_; 
if (v_isShared_1361_ == 0)
{
v___x_1363_ = v___x_1360_;
goto v_reusejp_1362_;
}
else
{
lean_object* v_reuseFailAlloc_1364_; 
v_reuseFailAlloc_1364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1364_, 0, v_a_1358_);
v___x_1363_ = v_reuseFailAlloc_1364_;
goto v_reusejp_1362_;
}
v_reusejp_1362_:
{
return v___x_1363_;
}
}
}
}
}
}
else
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
lean_del_object(v___x_1348_);
lean_dec(v_snd_1346_);
lean_dec(v_fst_1345_);
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec(v___y_1330_);
lean_dec(v___y_1329_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1367_ = lean_ctor_get(v___x_1350_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1350_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1350_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1350_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v___x_1372_; 
if (v_isShared_1370_ == 0)
{
v___x_1372_ = v___x_1369_;
goto v_reusejp_1371_;
}
else
{
lean_object* v_reuseFailAlloc_1373_; 
v_reuseFailAlloc_1373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1373_, 0, v_a_1367_);
v___x_1372_ = v_reuseFailAlloc_1373_;
goto v_reusejp_1371_;
}
v_reusejp_1371_:
{
return v___x_1372_;
}
}
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
lean_dec(v___y_1337_);
lean_dec_ref(v___y_1336_);
lean_dec(v___y_1335_);
lean_dec_ref(v___y_1334_);
lean_dec(v___y_1333_);
lean_dec(v___y_1330_);
lean_dec(v___y_1329_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
v_a_1376_ = lean_ctor_get(v___x_1343_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1343_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1343_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1343_);
v___x_1378_ = lean_box(0);
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
v_resetjp_1377_:
{
lean_object* v___x_1381_; 
if (v_isShared_1379_ == 0)
{
v___x_1381_ = v___x_1378_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v_a_1376_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
v___jp_1384_:
{
lean_object* v___x_1396_; lean_object* v_a_1397_; uint8_t v___x_1398_; 
lean_inc(v___y_1388_);
lean_inc_ref(v___y_1390_);
v___x_1396_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v___y_1390_, v___y_1388_, v___y_1393_);
v_a_1397_ = lean_ctor_get(v___x_1396_, 0);
lean_inc(v_a_1397_);
lean_dec_ref(v___x_1396_);
v___x_1398_ = lean_unbox(v_a_1397_);
lean_dec(v_a_1397_);
if (v___x_1398_ == 0)
{
lean_dec_ref(v___y_1390_);
lean_dec_ref(v___y_1387_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1141_);
v___y_1329_ = v___y_1385_;
v___y_1330_ = v___y_1386_;
v___y_1331_ = v___y_1388_;
v___y_1332_ = v___y_1389_;
v___y_1333_ = v___y_1391_;
v___y_1334_ = v___y_1392_;
v___y_1335_ = v___y_1393_;
v___y_1336_ = v___y_1394_;
v___y_1337_ = v___y_1395_;
goto v___jp_1328_;
}
else
{
lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1402_; 
v___x_1399_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_1400_ = l_Lean_MessageData_ofExpr(v___y_1387_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set_tag(v___x_1145_, 7);
lean_ctor_set(v___x_1145_, 1, v___x_1400_);
lean_ctor_set(v___x_1145_, 0, v___x_1399_);
v___x_1402_ = v___x_1145_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1419_; 
v_reuseFailAlloc_1419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1419_, 0, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1419_, 1, v___x_1400_);
v___x_1402_ = v_reuseFailAlloc_1419_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1408_; 
v___x_1403_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__19, &l_Lean_Meta_substCore___lam__3___closed__19_once, _init_l_Lean_Meta_substCore___lam__3___closed__19);
v___x_1404_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1402_);
lean_ctor_set(v___x_1404_, 1, v___x_1403_);
v___x_1405_ = l_Lean_indentExpr(v___y_1390_);
v___x_1406_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1404_);
lean_ctor_set(v___x_1406_, 1, v___x_1405_);
if (v_isShared_1142_ == 0)
{
lean_ctor_set(v___x_1141_, 0, v___x_1406_);
v___x_1408_ = v___x_1141_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1418_; 
v_reuseFailAlloc_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1418_, 0, v___x_1406_);
v___x_1408_ = v_reuseFailAlloc_1418_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; 
lean_inc(v_mvarId_1064_);
v___x_1409_ = l_Lean_Meta_throwTacticEx___redArg(v___x_1116_, v_mvarId_1064_, v___x_1408_, v___y_1392_, v___y_1393_, v___y_1394_, v___y_1395_);
if (lean_obj_tag(v___x_1409_) == 0)
{
lean_dec_ref_known(v___x_1409_, 1);
v___y_1329_ = v___y_1385_;
v___y_1330_ = v___y_1386_;
v___y_1331_ = v___y_1388_;
v___y_1332_ = v___y_1389_;
v___y_1333_ = v___y_1391_;
v___y_1334_ = v___y_1392_;
v___y_1335_ = v___y_1393_;
v___y_1336_ = v___y_1394_;
v___y_1337_ = v___y_1395_;
goto v___jp_1328_;
}
else
{
lean_object* v_a_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1417_; 
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
lean_dec(v___y_1393_);
lean_dec_ref(v___y_1392_);
lean_dec(v___y_1391_);
lean_dec(v___y_1388_);
lean_dec(v___y_1386_);
lean_dec(v___y_1385_);
lean_del_object(v___x_1150_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1410_ = lean_ctor_get(v___x_1409_, 0);
v_isSharedCheck_1417_ = !lean_is_exclusive(v___x_1409_);
if (v_isSharedCheck_1417_ == 0)
{
v___x_1412_ = v___x_1409_;
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_a_1410_);
lean_dec(v___x_1409_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1417_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
lean_object* v___x_1415_; 
if (v_isShared_1413_ == 0)
{
v___x_1415_ = v___x_1412_;
goto v_reusejp_1414_;
}
else
{
lean_object* v_reuseFailAlloc_1416_; 
v_reuseFailAlloc_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1416_, 0, v_a_1410_);
v___x_1415_ = v_reuseFailAlloc_1416_;
goto v_reusejp_1414_;
}
v_reusejp_1414_:
{
return v___x_1415_;
}
}
}
}
}
}
}
v___jp_1420_:
{
lean_object* v___x_1423_; 
v___x_1423_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1422_, v___y_1072_);
if (lean_obj_tag(v___y_1421_) == 1)
{
lean_object* v_a_1424_; lean_object* v_fvarId_1425_; lean_object* v___x_1426_; lean_object* v___f_1427_; lean_object* v___x_1428_; lean_object* v_a_1429_; uint8_t v___x_1430_; 
lean_dec_ref(v___x_1120_);
v_a_1424_ = lean_ctor_get(v___x_1423_, 0);
lean_inc(v_a_1424_);
lean_dec_ref(v___x_1423_);
v_fvarId_1425_ = lean_ctor_get(v___y_1421_, 0);
lean_inc(v_fvarId_1425_);
v___x_1426_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___f_1427_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__23));
v___x_1428_ = l_Lean_Meta_substCore___lam__0(v___x_1426_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
v_a_1429_ = lean_ctor_get(v___x_1428_, 0);
lean_inc(v_a_1429_);
lean_dec_ref(v___x_1428_);
v___x_1430_ = lean_unbox(v_a_1429_);
lean_dec(v_a_1429_);
if (v___x_1430_ == 0)
{
lean_inc(v_fvarId_1425_);
v___y_1385_ = v_fvarId_1425_;
v___y_1386_ = v___x_1426_;
v___y_1387_ = v___y_1421_;
v___y_1388_ = v_fvarId_1425_;
v___y_1389_ = v___f_1427_;
v___y_1390_ = v_a_1424_;
v___y_1391_ = v___x_1426_;
v___y_1392_ = v___y_1071_;
v___y_1393_ = v___y_1072_;
v___y_1394_ = v___y_1073_;
v___y_1395_ = v___y_1074_;
goto v___jp_1384_;
}
else
{
lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1431_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__25, &l_Lean_Meta_substCore___lam__3___closed__25_once, _init_l_Lean_Meta_substCore___lam__3___closed__25);
lean_inc_ref(v___y_1421_);
v___x_1432_ = l_Lean_MessageData_ofExpr(v___y_1421_);
v___x_1433_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1431_);
lean_ctor_set(v___x_1433_, 1, v___x_1432_);
v___x_1434_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__27, &l_Lean_Meta_substCore___lam__3___closed__27_once, _init_l_Lean_Meta_substCore___lam__3___closed__27);
v___x_1435_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1435_, 0, v___x_1433_);
lean_ctor_set(v___x_1435_, 1, v___x_1434_);
lean_inc(v_fvarId_1425_);
v___x_1436_ = l_Lean_MessageData_ofName(v_fvarId_1425_);
v___x_1437_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1437_, 0, v___x_1435_);
lean_ctor_set(v___x_1437_, 1, v___x_1436_);
v___x_1438_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__29, &l_Lean_Meta_substCore___lam__3___closed__29_once, _init_l_Lean_Meta_substCore___lam__3___closed__29);
v___x_1439_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1437_);
lean_ctor_set(v___x_1439_, 1, v___x_1438_);
lean_inc(v_a_1424_);
v___x_1440_ = l_Lean_MessageData_ofExpr(v_a_1424_);
v___x_1441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1439_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
v___x_1442_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_1426_, v___x_1441_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_);
if (lean_obj_tag(v___x_1442_) == 0)
{
lean_dec_ref_known(v___x_1442_, 1);
lean_inc(v_fvarId_1425_);
v___y_1385_ = v_fvarId_1425_;
v___y_1386_ = v___x_1426_;
v___y_1387_ = v___y_1421_;
v___y_1388_ = v_fvarId_1425_;
v___y_1389_ = v___f_1427_;
v___y_1390_ = v_a_1424_;
v___y_1391_ = v___x_1426_;
v___y_1392_ = v___y_1071_;
v___y_1393_ = v___y_1072_;
v___y_1394_ = v___y_1073_;
v___y_1395_ = v___y_1074_;
goto v___jp_1384_;
}
else
{
lean_object* v_a_1443_; lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1450_; 
lean_dec(v_fvarId_1425_);
lean_dec_ref_known(v___y_1421_, 1);
lean_dec(v_a_1424_);
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
v_a_1443_ = lean_ctor_get(v___x_1442_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v___x_1442_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1445_ = v___x_1442_;
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
else
{
lean_inc(v_a_1443_);
lean_dec(v___x_1442_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1450_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1448_; 
if (v_isShared_1446_ == 0)
{
v___x_1448_ = v___x_1445_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v_a_1443_);
v___x_1448_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
return v___x_1448_;
}
}
}
}
}
else
{
lean_dec_ref(v___x_1423_);
lean_del_object(v___x_1150_);
lean_del_object(v___x_1145_);
lean_del_object(v___x_1141_);
lean_dec(v_a_1115_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
if (v_symm_1069_ == 0)
{
lean_object* v___x_1451_; 
v___x_1451_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__30));
v___y_1122_ = v___y_1421_;
v___y_1123_ = v___x_1451_;
goto v___jp_1121_;
}
else
{
lean_object* v___x_1452_; 
v___x_1452_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__31));
v___y_1122_ = v___y_1421_;
v___y_1123_ = v___x_1452_;
goto v___jp_1121_;
}
}
}
v___jp_1453_:
{
lean_object* v___x_1455_; 
v___x_1455_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v___y_1454_, v___y_1072_);
if (v_symm_1069_ == 0)
{
lean_object* v_a_1456_; 
lean_dec(v_fst_1147_);
v_a_1456_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1456_);
lean_dec_ref(v___x_1455_);
v___y_1421_ = v_a_1456_;
v___y_1422_ = v_snd_1148_;
goto v___jp_1420_;
}
else
{
lean_object* v_a_1457_; 
lean_dec(v_snd_1148_);
v_a_1457_ = lean_ctor_get(v___x_1455_, 0);
lean_inc(v_a_1457_);
lean_dec_ref(v___x_1455_);
v___y_1421_ = v_a_1457_;
v___y_1422_ = v_fst_1147_;
goto v___jp_1420_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_1462_; lean_object* v___x_1464_; uint8_t v_isShared_1465_; uint8_t v_isSharedCheck_1469_; 
lean_dec_ref(v___x_1120_);
lean_dec(v_a_1115_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1462_ = lean_ctor_get(v___x_1135_, 0);
v_isSharedCheck_1469_ = !lean_is_exclusive(v___x_1135_);
if (v_isSharedCheck_1469_ == 0)
{
v___x_1464_ = v___x_1135_;
v_isShared_1465_ = v_isSharedCheck_1469_;
goto v_resetjp_1463_;
}
else
{
lean_inc(v_a_1462_);
lean_dec(v___x_1135_);
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
lean_object* v_a_1470_; lean_object* v___x_1472_; uint8_t v_isShared_1473_; uint8_t v_isSharedCheck_1477_; 
lean_dec(v_a_1115_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1470_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1477_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1477_ == 0)
{
v___x_1472_ = v___x_1118_;
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
else
{
lean_inc(v_a_1470_);
lean_dec(v___x_1118_);
v___x_1472_ = lean_box(0);
v_isShared_1473_ = v_isSharedCheck_1477_;
goto v_resetjp_1471_;
}
v_resetjp_1471_:
{
lean_object* v___x_1475_; 
if (v_isShared_1473_ == 0)
{
v___x_1475_ = v___x_1472_;
goto v_reusejp_1474_;
}
else
{
lean_object* v_reuseFailAlloc_1476_; 
v_reuseFailAlloc_1476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1476_, 0, v_a_1470_);
v___x_1475_ = v_reuseFailAlloc_1476_;
goto v_reusejp_1474_;
}
v_reusejp_1474_:
{
return v___x_1475_;
}
}
}
}
else
{
lean_object* v_a_1478_; lean_object* v___x_1480_; uint8_t v_isShared_1481_; uint8_t v_isSharedCheck_1485_; 
lean_dec(v_a_1115_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1478_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1485_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1485_ == 0)
{
v___x_1480_ = v___x_1117_;
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
else
{
lean_inc(v_a_1478_);
lean_dec(v___x_1117_);
v___x_1480_ = lean_box(0);
v_isShared_1481_ = v_isSharedCheck_1485_;
goto v_resetjp_1479_;
}
v_resetjp_1479_:
{
lean_object* v___x_1483_; 
if (v_isShared_1481_ == 0)
{
v___x_1483_ = v___x_1480_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v_a_1478_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
}
else
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1493_; 
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v_fvarSubst_1068_);
lean_dec(v_hFVarId_1065_);
lean_dec(v_mvarId_1064_);
v_a_1486_ = lean_ctor_get(v___x_1114_, 0);
v_isSharedCheck_1493_ = !lean_is_exclusive(v___x_1114_);
if (v_isSharedCheck_1493_ == 0)
{
v___x_1488_ = v___x_1114_;
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1114_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1493_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v___x_1491_; 
if (v_isShared_1489_ == 0)
{
v___x_1491_ = v___x_1488_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_a_1486_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
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
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
v___x_1084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1084_, 0, v_fvarSubst_1068_);
lean_ctor_set(v___x_1084_, 1, v___y_1077_);
v___x_1085_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; 
v___x_1086_ = l_Lean_MVarId_clear(v___y_1077_, v___y_1081_, v___y_1082_, v___y_1080_, v___y_1079_, v___y_1083_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v_a_1087_; lean_object* v___x_1088_; 
v_a_1087_ = lean_ctor_get(v___x_1086_, 0);
lean_inc(v_a_1087_);
lean_dec_ref_known(v___x_1086_, 1);
v___x_1088_ = l_Lean_MVarId_clear(v_a_1087_, v___y_1078_, v___y_1082_, v___y_1080_, v___y_1079_, v___y_1083_);
lean_dec(v___y_1083_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1082_);
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
lean_dec(v___y_1080_);
lean_dec_ref(v___y_1079_);
lean_dec(v___y_1078_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___lam__3___boxed(lean_object* v_mvarId_1494_, lean_object* v_hFVarId_1495_, lean_object* v___x_1496_, lean_object* v_clearH_1497_, lean_object* v_fvarSubst_1498_, lean_object* v_symm_1499_, lean_object* v_tryToSkip_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_){
_start:
{
uint8_t v_clearH_boxed_1506_; uint8_t v_symm_boxed_1507_; uint8_t v_tryToSkip_boxed_1508_; lean_object* v_res_1509_; 
v_clearH_boxed_1506_ = lean_unbox(v_clearH_1497_);
v_symm_boxed_1507_ = lean_unbox(v_symm_1499_);
v_tryToSkip_boxed_1508_ = lean_unbox(v_tryToSkip_1500_);
v_res_1509_ = l_Lean_Meta_substCore___lam__3(v_mvarId_1494_, v_hFVarId_1495_, v___x_1496_, v_clearH_boxed_1506_, v_fvarSubst_1498_, v_symm_boxed_1507_, v_tryToSkip_boxed_1508_, v___y_1501_, v___y_1502_, v___y_1503_, v___y_1504_);
lean_dec(v___x_1496_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore(lean_object* v_mvarId_1510_, lean_object* v_hFVarId_1511_, uint8_t v_symm_1512_, lean_object* v_fvarSubst_1513_, uint8_t v_clearH_1514_, uint8_t v_tryToSkip_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_){
_start:
{
lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___f_1525_; lean_object* v___x_1526_; 
v___x_1521_ = lean_box(0);
v___x_1522_ = lean_box(v_clearH_1514_);
v___x_1523_ = lean_box(v_symm_1512_);
v___x_1524_ = lean_box(v_tryToSkip_1515_);
lean_inc(v_mvarId_1510_);
v___f_1525_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___lam__3___boxed), 12, 7);
lean_closure_set(v___f_1525_, 0, v_mvarId_1510_);
lean_closure_set(v___f_1525_, 1, v_hFVarId_1511_);
lean_closure_set(v___f_1525_, 2, v___x_1521_);
lean_closure_set(v___f_1525_, 3, v___x_1522_);
lean_closure_set(v___f_1525_, 4, v_fvarSubst_1513_);
lean_closure_set(v___f_1525_, 5, v___x_1523_);
lean_closure_set(v___f_1525_, 6, v___x_1524_);
v___x_1526_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1510_, v___f_1525_, v_a_1516_, v_a_1517_, v_a_1518_, v_a_1519_);
return v___x_1526_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore___boxed(lean_object* v_mvarId_1527_, lean_object* v_hFVarId_1528_, lean_object* v_symm_1529_, lean_object* v_fvarSubst_1530_, lean_object* v_clearH_1531_, lean_object* v_tryToSkip_1532_, lean_object* v_a_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_){
_start:
{
uint8_t v_symm_boxed_1538_; uint8_t v_clearH_boxed_1539_; uint8_t v_tryToSkip_boxed_1540_; lean_object* v_res_1541_; 
v_symm_boxed_1538_ = lean_unbox(v_symm_1529_);
v_clearH_boxed_1539_ = lean_unbox(v_clearH_1531_);
v_tryToSkip_boxed_1540_ = lean_unbox(v_tryToSkip_1532_);
v_res_1541_ = l_Lean_Meta_substCore(v_mvarId_1527_, v_hFVarId_1528_, v_symm_boxed_1538_, v_fvarSubst_1530_, v_clearH_boxed_1539_, v_tryToSkip_boxed_1540_, v_a_1533_, v_a_1534_, v_a_1535_, v_a_1536_);
lean_dec(v_a_1536_);
lean_dec_ref(v_a_1535_);
lean_dec(v_a_1534_);
lean_dec_ref(v_a_1533_);
return v_res_1541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(lean_object* v_fst_1542_, lean_object* v_fst_1543_, lean_object* v_n_1544_, lean_object* v_i_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_, lean_object* v___y_1548_, lean_object* v___y_1549_, lean_object* v___y_1550_, lean_object* v___y_1551_){
_start:
{
lean_object* v___x_1553_; 
v___x_1553_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___redArg(v_fst_1542_, v_fst_1543_, v_n_1544_, v_i_1545_, v_a_1547_);
return v___x_1553_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2___boxed(lean_object* v_fst_1554_, lean_object* v_fst_1555_, lean_object* v_n_1556_, lean_object* v_i_1557_, lean_object* v_a_1558_, lean_object* v_a_1559_, lean_object* v___y_1560_, lean_object* v___y_1561_, lean_object* v___y_1562_, lean_object* v___y_1563_, lean_object* v___y_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l___private_Init_Data_Nat_Control_0__Nat_foldM_loop___at___00Lean_Meta_substCore_spec__2(v_fst_1554_, v_fst_1555_, v_n_1556_, v_i_1557_, v_a_1558_, v_a_1559_, v___y_1560_, v___y_1561_, v___y_1562_, v___y_1563_);
lean_dec(v___y_1563_);
lean_dec_ref(v___y_1562_);
lean_dec(v___y_1561_);
lean_dec_ref(v___y_1560_);
lean_dec(v_n_1556_);
lean_dec_ref(v_fst_1555_);
lean_dec_ref(v_fst_1554_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(lean_object* v_mvarId_1566_, lean_object* v_val_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1573_; 
v___x_1573_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v_mvarId_1566_, v_val_1567_, v___y_1569_);
return v___x_1573_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___boxed(lean_object* v_mvarId_1574_, lean_object* v_val_1575_, lean_object* v___y_1576_, lean_object* v___y_1577_, lean_object* v___y_1578_, lean_object* v___y_1579_, lean_object* v___y_1580_){
_start:
{
lean_object* v_res_1581_; 
v_res_1581_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5(v_mvarId_1574_, v_val_1575_, v___y_1576_, v___y_1577_, v___y_1578_, v___y_1579_);
lean_dec(v___y_1579_);
lean_dec_ref(v___y_1578_);
lean_dec(v___y_1577_);
lean_dec_ref(v___y_1576_);
return v_res_1581_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(lean_object* v_00_u03b1_1582_, lean_object* v_name_1583_, uint8_t v_bi_1584_, lean_object* v_type_1585_, lean_object* v_k_1586_, uint8_t v_kind_1587_, lean_object* v___y_1588_, lean_object* v___y_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_){
_start:
{
lean_object* v___x_1593_; 
v___x_1593_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___redArg(v_name_1583_, v_bi_1584_, v_type_1585_, v_k_1586_, v_kind_1587_, v___y_1588_, v___y_1589_, v___y_1590_, v___y_1591_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8___boxed(lean_object* v_00_u03b1_1594_, lean_object* v_name_1595_, lean_object* v_bi_1596_, lean_object* v_type_1597_, lean_object* v_k_1598_, lean_object* v_kind_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_, lean_object* v___y_1604_){
_start:
{
uint8_t v_bi_boxed_1605_; uint8_t v_kind_boxed_1606_; lean_object* v_res_1607_; 
v_bi_boxed_1605_ = lean_unbox(v_bi_1596_);
v_kind_boxed_1606_ = lean_unbox(v_kind_1599_);
v_res_1607_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6_spec__8(v_00_u03b1_1594_, v_name_1595_, v_bi_boxed_1605_, v_type_1597_, v_k_1598_, v_kind_boxed_1606_, v___y_1600_, v___y_1601_, v___y_1602_, v___y_1603_);
lean_dec(v___y_1603_);
lean_dec_ref(v___y_1602_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
return v_res_1607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(lean_object* v_00_u03b1_1608_, lean_object* v_name_1609_, lean_object* v_type_1610_, lean_object* v_k_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_, lean_object* v___y_1615_){
_start:
{
lean_object* v___x_1617_; 
v___x_1617_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___redArg(v_name_1609_, v_type_1610_, v_k_1611_, v___y_1612_, v___y_1613_, v___y_1614_, v___y_1615_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6___boxed(lean_object* v_00_u03b1_1618_, lean_object* v_name_1619_, lean_object* v_type_1620_, lean_object* v_k_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_, lean_object* v___y_1624_, lean_object* v___y_1625_, lean_object* v___y_1626_){
_start:
{
lean_object* v_res_1627_; 
v_res_1627_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_substCore_spec__6(v_00_u03b1_1618_, v_name_1619_, v_type_1620_, v_k_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_);
lean_dec(v___y_1625_);
lean_dec_ref(v___y_1624_);
lean_dec(v___y_1623_);
lean_dec_ref(v___y_1622_);
return v_res_1627_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6(lean_object* v_00_u03b2_1628_, lean_object* v_x_1629_, lean_object* v_x_1630_, lean_object* v_x_1631_){
_start:
{
lean_object* v___x_1632_; 
v___x_1632_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6___redArg(v_x_1629_, v_x_1630_, v_x_1631_);
return v___x_1632_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(lean_object* v_00_u03b2_1633_, lean_object* v_x_1634_, size_t v_x_1635_, size_t v_x_1636_, lean_object* v_x_1637_, lean_object* v_x_1638_){
_start:
{
lean_object* v___x_1639_; 
v___x_1639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___redArg(v_x_1634_, v_x_1635_, v_x_1636_, v_x_1637_, v_x_1638_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8___boxed(lean_object* v_00_u03b2_1640_, lean_object* v_x_1641_, lean_object* v_x_1642_, lean_object* v_x_1643_, lean_object* v_x_1644_, lean_object* v_x_1645_){
_start:
{
size_t v_x_35610__boxed_1646_; size_t v_x_35611__boxed_1647_; lean_object* v_res_1648_; 
v_x_35610__boxed_1646_ = lean_unbox_usize(v_x_1642_);
lean_dec(v_x_1642_);
v_x_35611__boxed_1647_ = lean_unbox_usize(v_x_1643_);
lean_dec(v_x_1643_);
v_res_1648_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8(v_00_u03b2_1640_, v_x_1641_, v_x_35610__boxed_1646_, v_x_35611__boxed_1647_, v_x_1644_, v_x_1645_);
return v_res_1648_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13(lean_object* v_00_u03b2_1649_, lean_object* v_n_1650_, lean_object* v_k_1651_, lean_object* v_v_1652_){
_start:
{
lean_object* v___x_1653_; 
v___x_1653_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13___redArg(v_n_1650_, v_k_1651_, v_v_1652_);
return v___x_1653_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(lean_object* v_00_u03b2_1654_, size_t v_depth_1655_, lean_object* v_keys_1656_, lean_object* v_vals_1657_, lean_object* v_heq_1658_, lean_object* v_i_1659_, lean_object* v_entries_1660_){
_start:
{
lean_object* v___x_1661_; 
v___x_1661_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___redArg(v_depth_1655_, v_keys_1656_, v_vals_1657_, v_i_1659_, v_entries_1660_);
return v___x_1661_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14___boxed(lean_object* v_00_u03b2_1662_, lean_object* v_depth_1663_, lean_object* v_keys_1664_, lean_object* v_vals_1665_, lean_object* v_heq_1666_, lean_object* v_i_1667_, lean_object* v_entries_1668_){
_start:
{
size_t v_depth_boxed_1669_; lean_object* v_res_1670_; 
v_depth_boxed_1669_ = lean_unbox_usize(v_depth_1663_);
lean_dec(v_depth_1663_);
v_res_1670_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__14(v_00_u03b2_1662_, v_depth_boxed_1669_, v_keys_1664_, v_vals_1665_, v_heq_1666_, v_i_1667_, v_entries_1668_);
lean_dec_ref(v_vals_1665_);
lean_dec_ref(v_keys_1664_);
return v_res_1670_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14(lean_object* v_00_u03b2_1671_, lean_object* v_x_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v___x_1676_; 
v___x_1676_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5_spec__6_spec__8_spec__13_spec__14___redArg(v_x_1672_, v_x_1673_, v_x_1674_, v_x_1675_);
return v___x_1676_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0(lean_object* v_fvarId_1680_, lean_object* v_mvarId_1681_, uint8_t v_tryToClear_1682_, lean_object* v___y_1683_, lean_object* v___y_1684_, lean_object* v___y_1685_, lean_object* v___y_1686_){
_start:
{
lean_object* v___x_1688_; 
lean_inc(v_fvarId_1680_);
v___x_1688_ = l_Lean_FVarId_getDecl___redArg(v_fvarId_1680_, v___y_1683_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1688_) == 0)
{
lean_object* v_a_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v_a_1689_ = lean_ctor_get(v___x_1688_, 0);
lean_inc(v_a_1689_);
lean_dec_ref_known(v___x_1688_, 1);
v___x_1690_ = l_Lean_LocalDecl_type(v_a_1689_);
lean_inc(v___y_1686_);
lean_inc_ref(v___y_1685_);
lean_inc(v___y_1684_);
lean_inc_ref(v___y_1683_);
v___x_1691_ = lean_whnf(v___x_1690_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1691_) == 0)
{
lean_object* v_a_1692_; lean_object* v___x_1694_; uint8_t v_isShared_1695_; uint8_t v_isSharedCheck_1776_; 
v_a_1692_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1776_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1776_ == 0)
{
v___x_1694_ = v___x_1691_;
v_isShared_1695_ = v_isSharedCheck_1776_;
goto v_resetjp_1693_;
}
else
{
lean_inc(v_a_1692_);
lean_dec(v___x_1691_);
v___x_1694_ = lean_box(0);
v_isShared_1695_ = v_isSharedCheck_1776_;
goto v_resetjp_1693_;
}
v_resetjp_1693_:
{
lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1696_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_1697_ = lean_unsigned_to_nat(4u);
v___x_1698_ = l_Lean_Expr_isAppOfArity(v_a_1692_, v___x_1696_, v___x_1697_);
if (v___x_1698_ == 0)
{
lean_object* v___x_1699_; lean_object* v___x_1701_; 
lean_dec(v_a_1692_);
lean_dec(v_a_1689_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
v___x_1699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1699_, 0, v_fvarId_1680_);
lean_ctor_set(v___x_1699_, 1, v_mvarId_1681_);
if (v_isShared_1695_ == 0)
{
lean_ctor_set(v___x_1694_, 0, v___x_1699_);
v___x_1701_ = v___x_1694_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v___x_1699_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
lean_del_object(v___x_1694_);
v___x_1703_ = l_Lean_Expr_appFn_x21(v_a_1692_);
v___x_1704_ = l_Lean_Expr_appFn_x21(v___x_1703_);
v___x_1705_ = l_Lean_Expr_appFn_x21(v___x_1704_);
v___x_1706_ = l_Lean_Expr_appArg_x21(v___x_1705_);
lean_dec_ref(v___x_1705_);
v___x_1707_ = l_Lean_Expr_appArg_x21(v___x_1703_);
lean_dec_ref(v___x_1703_);
v___x_1708_ = l_Lean_Meta_isExprDefEq(v___x_1706_, v___x_1707_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1708_) == 0)
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1767_; 
v_a_1709_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1767_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1767_ == 0)
{
v___x_1711_ = v___x_1708_;
v_isShared_1712_ = v_isSharedCheck_1767_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1708_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1767_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
uint8_t v___x_1713_; 
v___x_1713_ = lean_unbox(v_a_1709_);
if (v___x_1713_ == 0)
{
lean_object* v___x_1714_; lean_object* v___x_1716_; 
lean_dec(v_a_1709_);
lean_dec_ref(v___x_1704_);
lean_dec(v_a_1692_);
lean_dec(v_a_1689_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
v___x_1714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1714_, 0, v_fvarId_1680_);
lean_ctor_set(v___x_1714_, 1, v_mvarId_1681_);
if (v_isShared_1712_ == 0)
{
lean_ctor_set(v___x_1711_, 0, v___x_1714_);
v___x_1716_ = v___x_1711_;
goto v_reusejp_1715_;
}
else
{
lean_object* v_reuseFailAlloc_1717_; 
v_reuseFailAlloc_1717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1717_, 0, v___x_1714_);
v___x_1716_ = v_reuseFailAlloc_1717_;
goto v_reusejp_1715_;
}
v_reusejp_1715_:
{
return v___x_1716_;
}
}
else
{
lean_object* v___x_1718_; lean_object* v___x_1719_; 
lean_del_object(v___x_1711_);
lean_inc(v_fvarId_1680_);
v___x_1718_ = l_Lean_mkFVar(v_fvarId_1680_);
v___x_1719_ = l_Lean_Meta_mkEqOfHEq(v___x_1718_, v___x_1698_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1719_) == 0)
{
lean_object* v_a_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; 
v_a_1720_ = lean_ctor_get(v___x_1719_, 0);
lean_inc(v_a_1720_);
lean_dec_ref_known(v___x_1719_, 1);
v___x_1721_ = l_Lean_Expr_appArg_x21(v___x_1704_);
lean_dec_ref(v___x_1704_);
v___x_1722_ = l_Lean_Expr_appArg_x21(v_a_1692_);
lean_dec(v_a_1692_);
v___x_1723_ = l_Lean_Meta_mkEq(v___x_1721_, v___x_1722_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1723_) == 0)
{
lean_object* v_a_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v_a_1724_ = lean_ctor_get(v___x_1723_, 0);
lean_inc(v_a_1724_);
lean_dec_ref_known(v___x_1723_, 1);
v___x_1725_ = l_Lean_LocalDecl_userName(v_a_1689_);
lean_dec(v_a_1689_);
v___x_1726_ = l_Lean_MVarId_assert(v_mvarId_1681_, v___x_1725_, v_a_1724_, v_a_1720_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1726_) == 0)
{
if (v_tryToClear_1682_ == 0)
{
lean_object* v_a_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; 
lean_dec(v_fvarId_1680_);
v_a_1727_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1727_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1728_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
v___x_1729_ = l_Lean_Meta_intro1Core(v_a_1727_, v___x_1728_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v___x_1729_;
}
else
{
lean_object* v_a_1730_; lean_object* v___x_1731_; 
v_a_1730_ = lean_ctor_get(v___x_1726_, 0);
lean_inc(v_a_1730_);
lean_dec_ref_known(v___x_1726_, 1);
v___x_1731_ = l_Lean_MVarId_tryClear(v_a_1730_, v_fvarId_1680_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
if (lean_obj_tag(v___x_1731_) == 0)
{
lean_object* v_a_1732_; uint8_t v___x_1733_; lean_object* v___x_1734_; 
v_a_1732_ = lean_ctor_get(v___x_1731_, 0);
lean_inc(v_a_1732_);
lean_dec_ref_known(v___x_1731_, 1);
v___x_1733_ = lean_unbox(v_a_1709_);
lean_dec(v_a_1709_);
v___x_1734_ = l_Lean_Meta_intro1Core(v_a_1732_, v___x_1733_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
return v___x_1734_;
}
else
{
lean_object* v_a_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1742_; 
lean_dec(v_a_1709_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
v_a_1735_ = lean_ctor_get(v___x_1731_, 0);
v_isSharedCheck_1742_ = !lean_is_exclusive(v___x_1731_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1737_ = v___x_1731_;
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_a_1735_);
lean_dec(v___x_1731_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1742_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1740_; 
if (v_isShared_1738_ == 0)
{
v___x_1740_ = v___x_1737_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
v___x_1740_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
return v___x_1740_;
}
}
}
}
}
else
{
lean_object* v_a_1743_; lean_object* v___x_1745_; uint8_t v_isShared_1746_; uint8_t v_isSharedCheck_1750_; 
lean_dec(v_a_1709_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_fvarId_1680_);
v_a_1743_ = lean_ctor_get(v___x_1726_, 0);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1726_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1745_ = v___x_1726_;
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
else
{
lean_inc(v_a_1743_);
lean_dec(v___x_1726_);
v___x_1745_ = lean_box(0);
v_isShared_1746_ = v_isSharedCheck_1750_;
goto v_resetjp_1744_;
}
v_resetjp_1744_:
{
lean_object* v___x_1748_; 
if (v_isShared_1746_ == 0)
{
v___x_1748_ = v___x_1745_;
goto v_reusejp_1747_;
}
else
{
lean_object* v_reuseFailAlloc_1749_; 
v_reuseFailAlloc_1749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
v___x_1748_ = v_reuseFailAlloc_1749_;
goto v_reusejp_1747_;
}
v_reusejp_1747_:
{
return v___x_1748_;
}
}
}
}
else
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1758_; 
lean_dec(v_a_1720_);
lean_dec(v_a_1709_);
lean_dec(v_a_1689_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_mvarId_1681_);
lean_dec(v_fvarId_1680_);
v_a_1751_ = lean_ctor_get(v___x_1723_, 0);
v_isSharedCheck_1758_ = !lean_is_exclusive(v___x_1723_);
if (v_isSharedCheck_1758_ == 0)
{
v___x_1753_ = v___x_1723_;
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1723_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1758_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
lean_object* v___x_1756_; 
if (v_isShared_1754_ == 0)
{
v___x_1756_ = v___x_1753_;
goto v_reusejp_1755_;
}
else
{
lean_object* v_reuseFailAlloc_1757_; 
v_reuseFailAlloc_1757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1757_, 0, v_a_1751_);
v___x_1756_ = v_reuseFailAlloc_1757_;
goto v_reusejp_1755_;
}
v_reusejp_1755_:
{
return v___x_1756_;
}
}
}
}
else
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1766_; 
lean_dec(v_a_1709_);
lean_dec_ref(v___x_1704_);
lean_dec(v_a_1692_);
lean_dec(v_a_1689_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_mvarId_1681_);
lean_dec(v_fvarId_1680_);
v_a_1759_ = lean_ctor_get(v___x_1719_, 0);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1719_);
if (v_isSharedCheck_1766_ == 0)
{
v___x_1761_ = v___x_1719_;
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1719_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1766_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v_a_1759_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
}
}
}
else
{
lean_object* v_a_1768_; lean_object* v___x_1770_; uint8_t v_isShared_1771_; uint8_t v_isSharedCheck_1775_; 
lean_dec_ref(v___x_1704_);
lean_dec(v_a_1692_);
lean_dec(v_a_1689_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_mvarId_1681_);
lean_dec(v_fvarId_1680_);
v_a_1768_ = lean_ctor_get(v___x_1708_, 0);
v_isSharedCheck_1775_ = !lean_is_exclusive(v___x_1708_);
if (v_isSharedCheck_1775_ == 0)
{
v___x_1770_ = v___x_1708_;
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
else
{
lean_inc(v_a_1768_);
lean_dec(v___x_1708_);
v___x_1770_ = lean_box(0);
v_isShared_1771_ = v_isSharedCheck_1775_;
goto v_resetjp_1769_;
}
v_resetjp_1769_:
{
lean_object* v___x_1773_; 
if (v_isShared_1771_ == 0)
{
v___x_1773_ = v___x_1770_;
goto v_reusejp_1772_;
}
else
{
lean_object* v_reuseFailAlloc_1774_; 
v_reuseFailAlloc_1774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1774_, 0, v_a_1768_);
v___x_1773_ = v_reuseFailAlloc_1774_;
goto v_reusejp_1772_;
}
v_reusejp_1772_:
{
return v___x_1773_;
}
}
}
}
}
}
else
{
lean_object* v_a_1777_; lean_object* v___x_1779_; uint8_t v_isShared_1780_; uint8_t v_isSharedCheck_1784_; 
lean_dec(v_a_1689_);
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_mvarId_1681_);
lean_dec(v_fvarId_1680_);
v_a_1777_ = lean_ctor_get(v___x_1691_, 0);
v_isSharedCheck_1784_ = !lean_is_exclusive(v___x_1691_);
if (v_isSharedCheck_1784_ == 0)
{
v___x_1779_ = v___x_1691_;
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
else
{
lean_inc(v_a_1777_);
lean_dec(v___x_1691_);
v___x_1779_ = lean_box(0);
v_isShared_1780_ = v_isSharedCheck_1784_;
goto v_resetjp_1778_;
}
v_resetjp_1778_:
{
lean_object* v___x_1782_; 
if (v_isShared_1780_ == 0)
{
v___x_1782_ = v___x_1779_;
goto v_reusejp_1781_;
}
else
{
lean_object* v_reuseFailAlloc_1783_; 
v_reuseFailAlloc_1783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1783_, 0, v_a_1777_);
v___x_1782_ = v_reuseFailAlloc_1783_;
goto v_reusejp_1781_;
}
v_reusejp_1781_:
{
return v___x_1782_;
}
}
}
}
else
{
lean_object* v_a_1785_; lean_object* v___x_1787_; uint8_t v_isShared_1788_; uint8_t v_isSharedCheck_1792_; 
lean_dec(v___y_1686_);
lean_dec_ref(v___y_1685_);
lean_dec(v___y_1684_);
lean_dec_ref(v___y_1683_);
lean_dec(v_mvarId_1681_);
lean_dec(v_fvarId_1680_);
v_a_1785_ = lean_ctor_get(v___x_1688_, 0);
v_isSharedCheck_1792_ = !lean_is_exclusive(v___x_1688_);
if (v_isSharedCheck_1792_ == 0)
{
v___x_1787_ = v___x_1688_;
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
else
{
lean_inc(v_a_1785_);
lean_dec(v___x_1688_);
v___x_1787_ = lean_box(0);
v_isShared_1788_ = v_isSharedCheck_1792_;
goto v_resetjp_1786_;
}
v_resetjp_1786_:
{
lean_object* v___x_1790_; 
if (v_isShared_1788_ == 0)
{
v___x_1790_ = v___x_1787_;
goto v_reusejp_1789_;
}
else
{
lean_object* v_reuseFailAlloc_1791_; 
v_reuseFailAlloc_1791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1791_, 0, v_a_1785_);
v___x_1790_ = v_reuseFailAlloc_1791_;
goto v_reusejp_1789_;
}
v_reusejp_1789_:
{
return v___x_1790_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___lam__0___boxed(lean_object* v_fvarId_1793_, lean_object* v_mvarId_1794_, lean_object* v_tryToClear_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_, lean_object* v___y_1799_, lean_object* v___y_1800_){
_start:
{
uint8_t v_tryToClear_boxed_1801_; lean_object* v_res_1802_; 
v_tryToClear_boxed_1801_ = lean_unbox(v_tryToClear_1795_);
v_res_1802_ = l_Lean_Meta_heqToEq___lam__0(v_fvarId_1793_, v_mvarId_1794_, v_tryToClear_boxed_1801_, v___y_1796_, v___y_1797_, v___y_1798_, v___y_1799_);
return v_res_1802_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq(lean_object* v_mvarId_1803_, lean_object* v_fvarId_1804_, uint8_t v_tryToClear_1805_, lean_object* v_a_1806_, lean_object* v_a_1807_, lean_object* v_a_1808_, lean_object* v_a_1809_){
_start:
{
lean_object* v___x_1811_; lean_object* v___f_1812_; lean_object* v___x_1813_; 
v___x_1811_ = lean_box(v_tryToClear_1805_);
lean_inc(v_mvarId_1803_);
v___f_1812_ = lean_alloc_closure((void*)(l_Lean_Meta_heqToEq___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1812_, 0, v_fvarId_1804_);
lean_closure_set(v___f_1812_, 1, v_mvarId_1803_);
lean_closure_set(v___f_1812_, 2, v___x_1811_);
v___x_1813_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_1803_, v___f_1812_, v_a_1806_, v_a_1807_, v_a_1808_, v_a_1809_);
return v___x_1813_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_heqToEq___boxed(lean_object* v_mvarId_1814_, lean_object* v_fvarId_1815_, lean_object* v_tryToClear_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_, lean_object* v_a_1819_, lean_object* v_a_1820_, lean_object* v_a_1821_){
_start:
{
uint8_t v_tryToClear_boxed_1822_; lean_object* v_res_1823_; 
v_tryToClear_boxed_1822_ = lean_unbox(v_tryToClear_1816_);
v_res_1823_ = l_Lean_Meta_heqToEq(v_mvarId_1814_, v_fvarId_1815_, v_tryToClear_boxed_1822_, v_a_1817_, v_a_1818_, v_a_1819_, v_a_1820_);
lean_dec(v_a_1820_);
lean_dec_ref(v_a_1819_);
lean_dec(v_a_1818_);
lean_dec_ref(v_a_1817_);
return v_res_1823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(lean_object* v_x_1827_, lean_object* v_as_1828_, size_t v_sz_1829_, size_t v_i_1830_, lean_object* v_b_1831_, lean_object* v___y_1832_, lean_object* v___y_1833_, lean_object* v___y_1834_, lean_object* v___y_1835_){
_start:
{
lean_object* v_a_1838_; uint8_t v___x_1842_; 
v___x_1842_ = lean_usize_dec_lt(v_i_1830_, v_sz_1829_);
if (v___x_1842_ == 0)
{
lean_object* v___x_1843_; 
lean_dec(v_x_1827_);
v___x_1843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1843_, 0, v_b_1831_);
return v___x_1843_;
}
else
{
lean_object* v___x_1844_; lean_object* v_a_1846_; lean_object* v___x_1850_; lean_object* v_a_1851_; 
lean_dec_ref(v_b_1831_);
v___x_1844_ = lean_box(0);
v___x_1850_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1851_ = lean_array_uget(v_as_1828_, v_i_1830_);
if (lean_obj_tag(v_a_1851_) == 0)
{
v_a_1838_ = v___x_1850_;
goto v___jp_1837_;
}
else
{
lean_object* v_val_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1939_; 
v_val_1852_ = lean_ctor_get(v_a_1851_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v_a_1851_);
if (v_isSharedCheck_1939_ == 0)
{
v___x_1854_ = v_a_1851_;
v_isShared_1855_ = v_isSharedCheck_1939_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_val_1852_);
lean_dec(v_a_1851_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1939_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
uint8_t v___x_1863_; 
v___x_1863_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1852_);
if (v___x_1863_ == 0)
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = l_Lean_LocalDecl_type(v_val_1852_);
v___x_1870_ = l_Lean_Meta_matchEq_x3f(v___x_1869_, v___y_1832_, v___y_1833_, v___y_1834_, v___y_1835_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v_a_1871_; 
v_a_1871_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_a_1871_);
lean_dec_ref_known(v___x_1870_, 1);
if (lean_obj_tag(v_a_1871_) == 1)
{
lean_object* v_val_1872_; lean_object* v_snd_1873_; lean_object* v_fst_1874_; lean_object* v_snd_1875_; lean_object* v___x_1876_; 
v_val_1872_ = lean_ctor_get(v_a_1871_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v_a_1871_, 1);
v_snd_1873_ = lean_ctor_get(v_val_1872_, 1);
lean_inc(v_snd_1873_);
lean_dec(v_val_1872_);
v_fst_1874_ = lean_ctor_get(v_snd_1873_, 0);
lean_inc(v_fst_1874_);
v_snd_1875_ = lean_ctor_get(v_snd_1873_, 1);
lean_inc(v_snd_1875_);
lean_dec(v_snd_1873_);
v___x_1876_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_1874_, v___y_1833_);
if (lean_obj_tag(v___x_1876_) == 0)
{
lean_object* v_a_1877_; lean_object* v___x_1878_; 
v_a_1877_ = lean_ctor_get(v___x_1876_, 0);
lean_inc(v_a_1877_);
lean_dec_ref_known(v___x_1876_, 1);
v___x_1878_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_1875_, v___y_1833_);
if (lean_obj_tag(v___x_1878_) == 0)
{
lean_object* v_a_1879_; lean_object* v___y_1881_; uint8_t v___y_1882_; lean_object* v___y_1895_; uint8_t v___y_1900_; uint8_t v___x_1912_; 
v_a_1879_ = lean_ctor_get(v___x_1878_, 0);
lean_inc(v_a_1879_);
lean_dec_ref_known(v___x_1878_, 1);
v___x_1912_ = l_Lean_Expr_isFVar(v_a_1879_);
if (v___x_1912_ == 0)
{
v___y_1900_ = v___x_1912_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1913_; uint8_t v___x_1914_; 
v___x_1913_ = l_Lean_Expr_fvarId_x21(v_a_1879_);
v___x_1914_ = l_Lean_instBEqFVarId_beq(v___x_1913_, v_x_1827_);
lean_dec(v___x_1913_);
v___y_1900_ = v___x_1914_;
goto v___jp_1899_;
}
v___jp_1880_:
{
if (v___y_1882_ == 0)
{
lean_dec(v_a_1879_);
lean_dec(v_val_1852_);
v_a_1838_ = v___x_1850_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1883_; 
lean_inc(v_x_1827_);
v___x_1883_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1879_, v_x_1827_, v___y_1881_);
if (lean_obj_tag(v___x_1883_) == 0)
{
lean_object* v_a_1884_; uint8_t v___x_1885_; 
v_a_1884_ = lean_ctor_get(v___x_1883_, 0);
lean_inc(v_a_1884_);
lean_dec_ref_known(v___x_1883_, 1);
v___x_1885_ = lean_unbox(v_a_1884_);
lean_dec(v_a_1884_);
if (v___x_1885_ == 0)
{
lean_dec(v_x_1827_);
goto v___jp_1864_;
}
else
{
if (v___x_1863_ == 0)
{
lean_dec(v_val_1852_);
v_a_1838_ = v___x_1850_;
goto v___jp_1837_;
}
else
{
lean_dec(v_x_1827_);
goto v___jp_1864_;
}
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_dec(v_val_1852_);
lean_dec(v_x_1827_);
v_a_1886_ = lean_ctor_get(v___x_1883_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1883_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1883_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1883_);
v___x_1888_ = lean_box(0);
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
v_resetjp_1887_:
{
lean_object* v___x_1891_; 
if (v_isShared_1889_ == 0)
{
v___x_1891_ = v___x_1888_;
goto v_reusejp_1890_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1886_);
v___x_1891_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1890_;
}
v_reusejp_1890_:
{
return v___x_1891_;
}
}
}
}
}
v___jp_1894_:
{
uint8_t v___x_1896_; 
v___x_1896_ = l_Lean_Expr_isFVar(v_a_1877_);
if (v___x_1896_ == 0)
{
lean_dec(v_a_1877_);
v___y_1881_ = v___y_1895_;
v___y_1882_ = v___x_1896_;
goto v___jp_1880_;
}
else
{
lean_object* v___x_1897_; uint8_t v___x_1898_; 
v___x_1897_ = l_Lean_Expr_fvarId_x21(v_a_1877_);
lean_dec(v_a_1877_);
v___x_1898_ = l_Lean_instBEqFVarId_beq(v___x_1897_, v_x_1827_);
lean_dec(v___x_1897_);
v___y_1881_ = v___y_1895_;
v___y_1882_ = v___x_1898_;
goto v___jp_1880_;
}
}
v___jp_1899_:
{
if (v___y_1900_ == 0)
{
lean_del_object(v___x_1854_);
v___y_1895_ = v___y_1833_;
goto v___jp_1894_;
}
else
{
lean_object* v___x_1901_; 
lean_inc(v_x_1827_);
lean_inc(v_a_1877_);
v___x_1901_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_1877_, v_x_1827_, v___y_1833_);
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
lean_dec(v_a_1879_);
lean_dec(v_a_1877_);
lean_dec(v_x_1827_);
goto v___jp_1856_;
}
else
{
if (v___x_1863_ == 0)
{
lean_del_object(v___x_1854_);
v___y_1895_ = v___y_1833_;
goto v___jp_1894_;
}
else
{
lean_dec(v_a_1879_);
lean_dec(v_a_1877_);
lean_dec(v_x_1827_);
goto v___jp_1856_;
}
}
}
else
{
lean_object* v_a_1904_; lean_object* v___x_1906_; uint8_t v_isShared_1907_; uint8_t v_isSharedCheck_1911_; 
lean_dec(v_a_1879_);
lean_dec(v_a_1877_);
lean_del_object(v___x_1854_);
lean_dec(v_val_1852_);
lean_dec(v_x_1827_);
v_a_1904_ = lean_ctor_get(v___x_1901_, 0);
v_isSharedCheck_1911_ = !lean_is_exclusive(v___x_1901_);
if (v_isSharedCheck_1911_ == 0)
{
v___x_1906_ = v___x_1901_;
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
else
{
lean_inc(v_a_1904_);
lean_dec(v___x_1901_);
v___x_1906_ = lean_box(0);
v_isShared_1907_ = v_isSharedCheck_1911_;
goto v_resetjp_1905_;
}
v_resetjp_1905_:
{
lean_object* v___x_1909_; 
if (v_isShared_1907_ == 0)
{
v___x_1909_ = v___x_1906_;
goto v_reusejp_1908_;
}
else
{
lean_object* v_reuseFailAlloc_1910_; 
v_reuseFailAlloc_1910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1910_, 0, v_a_1904_);
v___x_1909_ = v_reuseFailAlloc_1910_;
goto v_reusejp_1908_;
}
v_reusejp_1908_:
{
return v___x_1909_;
}
}
}
}
}
}
else
{
lean_object* v_a_1915_; lean_object* v___x_1917_; uint8_t v_isShared_1918_; uint8_t v_isSharedCheck_1922_; 
lean_dec(v_a_1877_);
lean_del_object(v___x_1854_);
lean_dec(v_val_1852_);
lean_dec(v_x_1827_);
v_a_1915_ = lean_ctor_get(v___x_1878_, 0);
v_isSharedCheck_1922_ = !lean_is_exclusive(v___x_1878_);
if (v_isSharedCheck_1922_ == 0)
{
v___x_1917_ = v___x_1878_;
v_isShared_1918_ = v_isSharedCheck_1922_;
goto v_resetjp_1916_;
}
else
{
lean_inc(v_a_1915_);
lean_dec(v___x_1878_);
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
else
{
lean_object* v_a_1923_; lean_object* v___x_1925_; uint8_t v_isShared_1926_; uint8_t v_isSharedCheck_1930_; 
lean_dec(v_snd_1875_);
lean_del_object(v___x_1854_);
lean_dec(v_val_1852_);
lean_dec(v_x_1827_);
v_a_1923_ = lean_ctor_get(v___x_1876_, 0);
v_isSharedCheck_1930_ = !lean_is_exclusive(v___x_1876_);
if (v_isSharedCheck_1930_ == 0)
{
v___x_1925_ = v___x_1876_;
v_isShared_1926_ = v_isSharedCheck_1930_;
goto v_resetjp_1924_;
}
else
{
lean_inc(v_a_1923_);
lean_dec(v___x_1876_);
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
else
{
lean_dec(v_a_1871_);
lean_del_object(v___x_1854_);
lean_dec(v_val_1852_);
v_a_1838_ = v___x_1850_;
goto v___jp_1837_;
}
}
else
{
lean_object* v_a_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1938_; 
lean_del_object(v___x_1854_);
lean_dec(v_val_1852_);
lean_dec(v_x_1827_);
v_a_1931_ = lean_ctor_get(v___x_1870_, 0);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1870_);
if (v_isSharedCheck_1938_ == 0)
{
v___x_1933_ = v___x_1870_;
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_a_1931_);
lean_dec(v___x_1870_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1938_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v___x_1936_; 
if (v_isShared_1934_ == 0)
{
v___x_1936_ = v___x_1933_;
goto v_reusejp_1935_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
v___x_1936_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1935_;
}
v_reusejp_1935_:
{
return v___x_1936_;
}
}
}
}
else
{
lean_del_object(v___x_1854_);
lean_dec(v_val_1852_);
v_a_1838_ = v___x_1850_;
goto v___jp_1837_;
}
v___jp_1856_:
{
lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
v___x_1857_ = l_Lean_LocalDecl_fvarId(v_val_1852_);
lean_dec(v_val_1852_);
v___x_1858_ = lean_box(v___x_1842_);
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1857_);
lean_ctor_set(v___x_1859_, 1, v___x_1858_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 0, v___x_1859_);
v___x_1861_ = v___x_1854_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
v_a_1846_ = v___x_1861_;
goto v___jp_1845_;
}
}
v___jp_1864_:
{
lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1865_ = l_Lean_LocalDecl_fvarId(v_val_1852_);
lean_dec(v_val_1852_);
v___x_1866_ = lean_box(v___x_1863_);
v___x_1867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1867_, 0, v___x_1865_);
lean_ctor_set(v___x_1867_, 1, v___x_1866_);
v___x_1868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1868_, 0, v___x_1867_);
v_a_1846_ = v___x_1868_;
goto v___jp_1845_;
}
}
}
v___jp_1845_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1847_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1847_, 0, v_a_1846_);
v___x_1848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1848_, 0, v___x_1847_);
lean_ctor_set(v___x_1848_, 1, v___x_1844_);
v___x_1849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1849_, 0, v___x_1848_);
return v___x_1849_;
}
}
v___jp_1837_:
{
size_t v___x_1839_; size_t v___x_1840_; 
v___x_1839_ = ((size_t)1ULL);
v___x_1840_ = lean_usize_add(v_i_1830_, v___x_1839_);
lean_inc_ref(v_a_1838_);
v_i_1830_ = v___x_1840_;
v_b_1831_ = v_a_1838_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___boxed(lean_object* v_x_1940_, lean_object* v_as_1941_, lean_object* v_sz_1942_, lean_object* v_i_1943_, lean_object* v_b_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
size_t v_sz_boxed_1950_; size_t v_i_boxed_1951_; lean_object* v_res_1952_; 
v_sz_boxed_1950_ = lean_unbox_usize(v_sz_1942_);
lean_dec(v_sz_1942_);
v_i_boxed_1951_ = lean_unbox_usize(v_i_1943_);
lean_dec(v_i_1943_);
v_res_1952_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1940_, v_as_1941_, v_sz_boxed_1950_, v_i_boxed_1951_, v_b_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
lean_dec_ref(v_as_1941_);
return v_res_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(lean_object* v_x_1953_, lean_object* v_as_1954_, size_t v_sz_1955_, size_t v_i_1956_, lean_object* v_b_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_){
_start:
{
lean_object* v_a_1964_; uint8_t v___x_1968_; 
v___x_1968_ = lean_usize_dec_lt(v_i_1956_, v_sz_1955_);
if (v___x_1968_ == 0)
{
lean_object* v___x_1969_; 
lean_dec(v_x_1953_);
v___x_1969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1969_, 0, v_b_1957_);
return v___x_1969_;
}
else
{
lean_object* v___x_1970_; lean_object* v_a_1972_; lean_object* v___x_1976_; lean_object* v_a_1977_; 
lean_dec_ref(v_b_1957_);
v___x_1970_ = lean_box(0);
v___x_1976_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_a_1977_ = lean_array_uget(v_as_1954_, v_i_1956_);
if (lean_obj_tag(v_a_1977_) == 0)
{
v_a_1964_ = v___x_1976_;
goto v___jp_1963_;
}
else
{
lean_object* v_val_1978_; lean_object* v___x_1980_; uint8_t v_isShared_1981_; uint8_t v_isSharedCheck_2065_; 
v_val_1978_ = lean_ctor_get(v_a_1977_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v_a_1977_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_1980_ = v_a_1977_;
v_isShared_1981_ = v_isSharedCheck_2065_;
goto v_resetjp_1979_;
}
else
{
lean_inc(v_val_1978_);
lean_dec(v_a_1977_);
v___x_1980_ = lean_box(0);
v_isShared_1981_ = v_isSharedCheck_2065_;
goto v_resetjp_1979_;
}
v_resetjp_1979_:
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1978_);
if (v___x_1989_ == 0)
{
lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1995_ = l_Lean_LocalDecl_type(v_val_1978_);
v___x_1996_ = l_Lean_Meta_matchEq_x3f(v___x_1995_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
if (lean_obj_tag(v___x_1996_) == 0)
{
lean_object* v_a_1997_; 
v_a_1997_ = lean_ctor_get(v___x_1996_, 0);
lean_inc(v_a_1997_);
lean_dec_ref_known(v___x_1996_, 1);
if (lean_obj_tag(v_a_1997_) == 1)
{
lean_object* v_val_1998_; lean_object* v_snd_1999_; lean_object* v_fst_2000_; lean_object* v_snd_2001_; lean_object* v___x_2002_; 
v_val_1998_ = lean_ctor_get(v_a_1997_, 0);
lean_inc(v_val_1998_);
lean_dec_ref_known(v_a_1997_, 1);
v_snd_1999_ = lean_ctor_get(v_val_1998_, 1);
lean_inc(v_snd_1999_);
lean_dec(v_val_1998_);
v_fst_2000_ = lean_ctor_get(v_snd_1999_, 0);
lean_inc(v_fst_2000_);
v_snd_2001_ = lean_ctor_get(v_snd_1999_, 1);
lean_inc(v_snd_2001_);
lean_dec(v_snd_1999_);
v___x_2002_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_fst_2000_, v___y_1959_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = l_Lean_instantiateMVars___at___00Lean_Meta_substCore_spec__0___redArg(v_snd_2001_, v___y_1959_);
if (lean_obj_tag(v___x_2004_) == 0)
{
lean_object* v_a_2005_; lean_object* v___y_2007_; uint8_t v___y_2008_; lean_object* v___y_2021_; uint8_t v___y_2026_; uint8_t v___x_2038_; 
v_a_2005_ = lean_ctor_get(v___x_2004_, 0);
lean_inc(v_a_2005_);
lean_dec_ref_known(v___x_2004_, 1);
v___x_2038_ = l_Lean_Expr_isFVar(v_a_2005_);
if (v___x_2038_ == 0)
{
v___y_2026_ = v___x_2038_;
goto v___jp_2025_;
}
else
{
lean_object* v___x_2039_; uint8_t v___x_2040_; 
v___x_2039_ = l_Lean_Expr_fvarId_x21(v_a_2005_);
v___x_2040_ = l_Lean_instBEqFVarId_beq(v___x_2039_, v_x_1953_);
lean_dec(v___x_2039_);
v___y_2026_ = v___x_2040_;
goto v___jp_2025_;
}
v___jp_2006_:
{
if (v___y_2008_ == 0)
{
lean_dec(v_a_2005_);
lean_dec(v_val_1978_);
v_a_1964_ = v___x_1976_;
goto v___jp_1963_;
}
else
{
lean_object* v___x_2009_; 
lean_inc(v_x_1953_);
v___x_2009_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2005_, v_x_1953_, v___y_2007_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; uint8_t v___x_2011_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
v___x_2011_ = lean_unbox(v_a_2010_);
lean_dec(v_a_2010_);
if (v___x_2011_ == 0)
{
lean_dec(v_x_1953_);
goto v___jp_1990_;
}
else
{
if (v___x_1989_ == 0)
{
lean_dec(v_val_1978_);
v_a_1964_ = v___x_1976_;
goto v___jp_1963_;
}
else
{
lean_dec(v_x_1953_);
goto v___jp_1990_;
}
}
}
else
{
lean_object* v_a_2012_; lean_object* v___x_2014_; uint8_t v_isShared_2015_; uint8_t v_isSharedCheck_2019_; 
lean_dec(v_val_1978_);
lean_dec(v_x_1953_);
v_a_2012_ = lean_ctor_get(v___x_2009_, 0);
v_isSharedCheck_2019_ = !lean_is_exclusive(v___x_2009_);
if (v_isSharedCheck_2019_ == 0)
{
v___x_2014_ = v___x_2009_;
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
else
{
lean_inc(v_a_2012_);
lean_dec(v___x_2009_);
v___x_2014_ = lean_box(0);
v_isShared_2015_ = v_isSharedCheck_2019_;
goto v_resetjp_2013_;
}
v_resetjp_2013_:
{
lean_object* v___x_2017_; 
if (v_isShared_2015_ == 0)
{
v___x_2017_ = v___x_2014_;
goto v_reusejp_2016_;
}
else
{
lean_object* v_reuseFailAlloc_2018_; 
v_reuseFailAlloc_2018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
v___x_2017_ = v_reuseFailAlloc_2018_;
goto v_reusejp_2016_;
}
v_reusejp_2016_:
{
return v___x_2017_;
}
}
}
}
}
v___jp_2020_:
{
uint8_t v___x_2022_; 
v___x_2022_ = l_Lean_Expr_isFVar(v_a_2003_);
if (v___x_2022_ == 0)
{
lean_dec(v_a_2003_);
v___y_2007_ = v___y_2021_;
v___y_2008_ = v___x_2022_;
goto v___jp_2006_;
}
else
{
lean_object* v___x_2023_; uint8_t v___x_2024_; 
v___x_2023_ = l_Lean_Expr_fvarId_x21(v_a_2003_);
lean_dec(v_a_2003_);
v___x_2024_ = l_Lean_instBEqFVarId_beq(v___x_2023_, v_x_1953_);
lean_dec(v___x_2023_);
v___y_2007_ = v___y_2021_;
v___y_2008_ = v___x_2024_;
goto v___jp_2006_;
}
}
v___jp_2025_:
{
if (v___y_2026_ == 0)
{
lean_del_object(v___x_1980_);
v___y_2021_ = v___y_1959_;
goto v___jp_2020_;
}
else
{
lean_object* v___x_2027_; 
lean_inc(v_x_1953_);
lean_inc(v_a_2003_);
v___x_2027_ = l_Lean_exprDependsOn___at___00Lean_Meta_substCore_spec__4___redArg(v_a_2003_, v_x_1953_, v___y_1959_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; uint8_t v___x_2029_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2029_ = lean_unbox(v_a_2028_);
lean_dec(v_a_2028_);
if (v___x_2029_ == 0)
{
lean_dec(v_a_2005_);
lean_dec(v_a_2003_);
lean_dec(v_x_1953_);
goto v___jp_1982_;
}
else
{
if (v___x_1989_ == 0)
{
lean_del_object(v___x_1980_);
v___y_2021_ = v___y_1959_;
goto v___jp_2020_;
}
else
{
lean_dec(v_a_2005_);
lean_dec(v_a_2003_);
lean_dec(v_x_1953_);
goto v___jp_1982_;
}
}
}
else
{
lean_object* v_a_2030_; lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2037_; 
lean_dec(v_a_2005_);
lean_dec(v_a_2003_);
lean_del_object(v___x_1980_);
lean_dec(v_val_1978_);
lean_dec(v_x_1953_);
v_a_2030_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2032_ = v___x_2027_;
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
else
{
lean_inc(v_a_2030_);
lean_dec(v___x_2027_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2037_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2035_; 
if (v_isShared_2033_ == 0)
{
v___x_2035_ = v___x_2032_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2030_);
v___x_2035_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
return v___x_2035_;
}
}
}
}
}
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec(v_a_2003_);
lean_del_object(v___x_1980_);
lean_dec(v_val_1978_);
lean_dec(v_x_1953_);
v_a_2041_ = lean_ctor_get(v___x_2004_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2004_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2004_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2004_);
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
else
{
lean_object* v_a_2049_; lean_object* v___x_2051_; uint8_t v_isShared_2052_; uint8_t v_isSharedCheck_2056_; 
lean_dec(v_snd_2001_);
lean_del_object(v___x_1980_);
lean_dec(v_val_1978_);
lean_dec(v_x_1953_);
v_a_2049_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2051_ = v___x_2002_;
v_isShared_2052_ = v_isSharedCheck_2056_;
goto v_resetjp_2050_;
}
else
{
lean_inc(v_a_2049_);
lean_dec(v___x_2002_);
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
else
{
lean_dec(v_a_1997_);
lean_del_object(v___x_1980_);
lean_dec(v_val_1978_);
v_a_1964_ = v___x_1976_;
goto v___jp_1963_;
}
}
else
{
lean_object* v_a_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2064_; 
lean_del_object(v___x_1980_);
lean_dec(v_val_1978_);
lean_dec(v_x_1953_);
v_a_2057_ = lean_ctor_get(v___x_1996_, 0);
v_isSharedCheck_2064_ = !lean_is_exclusive(v___x_1996_);
if (v_isSharedCheck_2064_ == 0)
{
v___x_2059_ = v___x_1996_;
v_isShared_2060_ = v_isSharedCheck_2064_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_a_2057_);
lean_dec(v___x_1996_);
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
lean_del_object(v___x_1980_);
lean_dec(v_val_1978_);
v_a_1964_ = v___x_1976_;
goto v___jp_1963_;
}
v___jp_1982_:
{
lean_object* v___x_1983_; lean_object* v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1987_; 
v___x_1983_ = l_Lean_LocalDecl_fvarId(v_val_1978_);
lean_dec(v_val_1978_);
v___x_1984_ = lean_box(v___x_1968_);
v___x_1985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1985_, 0, v___x_1983_);
lean_ctor_set(v___x_1985_, 1, v___x_1984_);
if (v_isShared_1981_ == 0)
{
lean_ctor_set(v___x_1980_, 0, v___x_1985_);
v___x_1987_ = v___x_1980_;
goto v_reusejp_1986_;
}
else
{
lean_object* v_reuseFailAlloc_1988_; 
v_reuseFailAlloc_1988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1988_, 0, v___x_1985_);
v___x_1987_ = v_reuseFailAlloc_1988_;
goto v_reusejp_1986_;
}
v_reusejp_1986_:
{
v_a_1972_ = v___x_1987_;
goto v___jp_1971_;
}
}
v___jp_1990_:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v___x_1994_; 
v___x_1991_ = l_Lean_LocalDecl_fvarId(v_val_1978_);
lean_dec(v_val_1978_);
v___x_1992_ = lean_box(v___x_1989_);
v___x_1993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1993_, 0, v___x_1991_);
lean_ctor_set(v___x_1993_, 1, v___x_1992_);
v___x_1994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1994_, 0, v___x_1993_);
v_a_1972_ = v___x_1994_;
goto v___jp_1971_;
}
}
}
v___jp_1971_:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___x_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1973_, 0, v_a_1972_);
v___x_1974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v___x_1970_);
v___x_1975_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1974_);
return v___x_1975_;
}
}
v___jp_1963_:
{
size_t v___x_1965_; size_t v___x_1966_; lean_object* v___x_1967_; 
v___x_1965_ = ((size_t)1ULL);
v___x_1966_ = lean_usize_add(v_i_1956_, v___x_1965_);
lean_inc_ref(v_a_1964_);
v___x_1967_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4(v_x_1953_, v_as_1954_, v_sz_1955_, v___x_1966_, v_a_1964_, v___y_1958_, v___y_1959_, v___y_1960_, v___y_1961_);
return v___x_1967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2___boxed(lean_object* v_x_2066_, lean_object* v_as_2067_, lean_object* v_sz_2068_, lean_object* v_i_2069_, lean_object* v_b_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_, lean_object* v___y_2073_, lean_object* v___y_2074_, lean_object* v___y_2075_){
_start:
{
size_t v_sz_boxed_2076_; size_t v_i_boxed_2077_; lean_object* v_res_2078_; 
v_sz_boxed_2076_ = lean_unbox_usize(v_sz_2068_);
lean_dec(v_sz_2068_);
v_i_boxed_2077_ = lean_unbox_usize(v_i_2069_);
lean_dec(v_i_2069_);
v_res_2078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2066_, v_as_2067_, v_sz_boxed_2076_, v_i_boxed_2077_, v_b_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_);
lean_dec(v___y_2074_);
lean_dec_ref(v___y_2073_);
lean_dec(v___y_2072_);
lean_dec_ref(v___y_2071_);
lean_dec_ref(v_as_2067_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(lean_object* v_x_2079_, lean_object* v_x_2080_, lean_object* v___y_2081_, lean_object* v___y_2082_, lean_object* v___y_2083_, lean_object* v___y_2084_){
_start:
{
if (lean_obj_tag(v_x_2080_) == 0)
{
lean_object* v_cs_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; size_t v_sz_2089_; size_t v___x_2090_; lean_object* v___x_2091_; 
v_cs_2086_ = lean_ctor_get(v_x_2080_, 0);
v___x_2087_ = lean_box(0);
v___x_2088_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2089_ = lean_array_size(v_cs_2086_);
v___x_2090_ = ((size_t)0ULL);
v___x_2091_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2079_, v_cs_2086_, v_sz_2089_, v___x_2090_, v___x_2088_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2091_) == 0)
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2104_; 
v_a_2092_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2104_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2104_ == 0)
{
v___x_2094_ = v___x_2091_;
v_isShared_2095_ = v_isSharedCheck_2104_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2091_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2104_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v_fst_2096_; 
v_fst_2096_ = lean_ctor_get(v_a_2092_, 0);
lean_inc(v_fst_2096_);
lean_dec(v_a_2092_);
if (lean_obj_tag(v_fst_2096_) == 0)
{
lean_object* v___x_2098_; 
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v___x_2087_);
v___x_2098_ = v___x_2094_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2087_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
else
{
lean_object* v_val_2100_; lean_object* v___x_2102_; 
v_val_2100_ = lean_ctor_get(v_fst_2096_, 0);
lean_inc(v_val_2100_);
lean_dec_ref_known(v_fst_2096_, 1);
if (v_isShared_2095_ == 0)
{
lean_ctor_set(v___x_2094_, 0, v_val_2100_);
v___x_2102_ = v___x_2094_;
goto v_reusejp_2101_;
}
else
{
lean_object* v_reuseFailAlloc_2103_; 
v_reuseFailAlloc_2103_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2103_, 0, v_val_2100_);
v___x_2102_ = v_reuseFailAlloc_2103_;
goto v_reusejp_2101_;
}
v_reusejp_2101_:
{
return v___x_2102_;
}
}
}
}
else
{
lean_object* v_a_2105_; lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2112_; 
v_a_2105_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2112_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2112_ == 0)
{
v___x_2107_ = v___x_2091_;
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
else
{
lean_inc(v_a_2105_);
lean_dec(v___x_2091_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2112_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2110_; 
if (v_isShared_2108_ == 0)
{
v___x_2110_ = v___x_2107_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2111_; 
v_reuseFailAlloc_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2111_, 0, v_a_2105_);
v___x_2110_ = v_reuseFailAlloc_2111_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
return v___x_2110_;
}
}
}
}
else
{
lean_object* v_vs_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; size_t v_sz_2116_; size_t v___x_2117_; lean_object* v___x_2118_; 
v_vs_2113_ = lean_ctor_get(v_x_2080_, 0);
v___x_2114_ = lean_box(0);
v___x_2115_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2116_ = lean_array_size(v_vs_2113_);
v___x_2117_ = ((size_t)0ULL);
v___x_2118_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2079_, v_vs_2113_, v_sz_2116_, v___x_2117_, v___x_2115_, v___y_2081_, v___y_2082_, v___y_2083_, v___y_2084_);
if (lean_obj_tag(v___x_2118_) == 0)
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2131_; 
v_a_2119_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2121_ = v___x_2118_;
v_isShared_2122_ = v_isSharedCheck_2131_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2118_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2131_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v_fst_2123_; 
v_fst_2123_ = lean_ctor_get(v_a_2119_, 0);
lean_inc(v_fst_2123_);
lean_dec(v_a_2119_);
if (lean_obj_tag(v_fst_2123_) == 0)
{
lean_object* v___x_2125_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v___x_2114_);
v___x_2125_ = v___x_2121_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v___x_2114_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
else
{
lean_object* v_val_2127_; lean_object* v___x_2129_; 
v_val_2127_ = lean_ctor_get(v_fst_2123_, 0);
lean_inc(v_val_2127_);
lean_dec_ref_known(v_fst_2123_, 1);
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 0, v_val_2127_);
v___x_2129_ = v___x_2121_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_val_2127_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
v_a_2132_ = lean_ctor_get(v___x_2118_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2118_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2118_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2118_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(lean_object* v_x_2140_, lean_object* v_as_2141_, size_t v_sz_2142_, size_t v_i_2143_, lean_object* v_b_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_, lean_object* v___y_2148_){
_start:
{
uint8_t v___x_2150_; 
v___x_2150_ = lean_usize_dec_lt(v_i_2143_, v_sz_2142_);
if (v___x_2150_ == 0)
{
lean_object* v___x_2151_; 
lean_dec(v_x_2140_);
v___x_2151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2151_, 0, v_b_2144_);
return v___x_2151_;
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2153_; 
lean_dec_ref(v_b_2144_);
v_a_2152_ = lean_array_uget_borrowed(v_as_2141_, v_i_2143_);
lean_inc(v_x_2140_);
v___x_2153_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2140_, v_a_2152_, v___y_2145_, v___y_2146_, v___y_2147_, v___y_2148_);
if (lean_obj_tag(v___x_2153_) == 0)
{
lean_object* v_a_2154_; lean_object* v___x_2156_; uint8_t v_isShared_2157_; uint8_t v_isSharedCheck_2168_; 
v_a_2154_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2168_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2168_ == 0)
{
v___x_2156_ = v___x_2153_;
v_isShared_2157_ = v_isSharedCheck_2168_;
goto v_resetjp_2155_;
}
else
{
lean_inc(v_a_2154_);
lean_dec(v___x_2153_);
v___x_2156_ = lean_box(0);
v_isShared_2157_ = v_isSharedCheck_2168_;
goto v_resetjp_2155_;
}
v_resetjp_2155_:
{
lean_object* v___x_2158_; 
v___x_2158_ = lean_box(0);
if (lean_obj_tag(v_a_2154_) == 1)
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2162_; 
lean_dec(v_x_2140_);
v___x_2159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2159_, 0, v_a_2154_);
v___x_2160_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2160_, 0, v___x_2159_);
lean_ctor_set(v___x_2160_, 1, v___x_2158_);
if (v_isShared_2157_ == 0)
{
lean_ctor_set(v___x_2156_, 0, v___x_2160_);
v___x_2162_ = v___x_2156_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v___x_2160_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
else
{
lean_object* v___x_2164_; size_t v___x_2165_; size_t v___x_2166_; 
lean_del_object(v___x_2156_);
lean_dec(v_a_2154_);
v___x_2164_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v___x_2165_ = ((size_t)1ULL);
v___x_2166_ = lean_usize_add(v_i_2143_, v___x_2165_);
v_i_2143_ = v___x_2166_;
v_b_2144_ = v___x_2164_;
goto _start;
}
}
}
else
{
lean_object* v_a_2169_; lean_object* v___x_2171_; uint8_t v_isShared_2172_; uint8_t v_isSharedCheck_2176_; 
lean_dec(v_x_2140_);
v_a_2169_ = lean_ctor_get(v___x_2153_, 0);
v_isSharedCheck_2176_ = !lean_is_exclusive(v___x_2153_);
if (v_isSharedCheck_2176_ == 0)
{
v___x_2171_ = v___x_2153_;
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
else
{
lean_inc(v_a_2169_);
lean_dec(v___x_2153_);
v___x_2171_ = lean_box(0);
v_isShared_2172_ = v_isSharedCheck_2176_;
goto v_resetjp_2170_;
}
v_resetjp_2170_:
{
lean_object* v___x_2174_; 
if (v_isShared_2172_ == 0)
{
v___x_2174_ = v___x_2171_;
goto v_reusejp_2173_;
}
else
{
lean_object* v_reuseFailAlloc_2175_; 
v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
v___x_2174_ = v_reuseFailAlloc_2175_;
goto v_reusejp_2173_;
}
v_reusejp_2173_:
{
return v___x_2174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_x_2177_, lean_object* v_as_2178_, lean_object* v_sz_2179_, lean_object* v_i_2180_, lean_object* v_b_2181_, lean_object* v___y_2182_, lean_object* v___y_2183_, lean_object* v___y_2184_, lean_object* v___y_2185_, lean_object* v___y_2186_){
_start:
{
size_t v_sz_boxed_2187_; size_t v_i_boxed_2188_; lean_object* v_res_2189_; 
v_sz_boxed_2187_ = lean_unbox_usize(v_sz_2179_);
lean_dec(v_sz_2179_);
v_i_boxed_2188_ = lean_unbox_usize(v_i_2180_);
lean_dec(v_i_2180_);
v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1_spec__2(v_x_2177_, v_as_2178_, v_sz_boxed_2187_, v_i_boxed_2188_, v_b_2181_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
lean_dec(v___y_2185_);
lean_dec_ref(v___y_2184_);
lean_dec(v___y_2183_);
lean_dec_ref(v___y_2182_);
lean_dec_ref(v_as_2178_);
return v_res_2189_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1___boxed(lean_object* v_x_2190_, lean_object* v_x_2191_, lean_object* v___y_2192_, lean_object* v___y_2193_, lean_object* v___y_2194_, lean_object* v___y_2195_, lean_object* v___y_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2190_, v_x_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_);
lean_dec(v___y_2195_);
lean_dec_ref(v___y_2194_);
lean_dec(v___y_2193_);
lean_dec_ref(v___y_2192_);
lean_dec_ref(v_x_2191_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(lean_object* v_x_2198_, lean_object* v_t_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
lean_object* v_root_2205_; lean_object* v_tail_2206_; lean_object* v___x_2207_; 
v_root_2205_ = lean_ctor_get(v_t_2199_, 0);
v_tail_2206_ = lean_ctor_get(v_t_2199_, 1);
lean_inc(v_x_2198_);
v___x_2207_ = l_Lean_PersistentArray_findSomeMAux___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__1(v_x_2198_, v_root_2205_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2207_) == 0)
{
lean_object* v_a_2208_; 
v_a_2208_ = lean_ctor_get(v___x_2207_, 0);
lean_inc(v_a_2208_);
if (lean_obj_tag(v_a_2208_) == 0)
{
lean_object* v___x_2209_; size_t v_sz_2210_; size_t v___x_2211_; lean_object* v___x_2212_; 
lean_dec_ref_known(v___x_2207_, 1);
v___x_2209_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2_spec__4___closed__0));
v_sz_2210_ = lean_array_size(v_tail_2206_);
v___x_2211_ = ((size_t)0ULL);
v___x_2212_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0_spec__2(v_x_2198_, v_tail_2206_, v_sz_2210_, v___x_2211_, v___x_2209_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2212_) == 0)
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2225_; 
v_a_2213_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2225_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2225_ == 0)
{
v___x_2215_ = v___x_2212_;
v_isShared_2216_ = v_isSharedCheck_2225_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2212_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2225_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v_fst_2217_; 
v_fst_2217_ = lean_ctor_get(v_a_2213_, 0);
lean_inc(v_fst_2217_);
lean_dec(v_a_2213_);
if (lean_obj_tag(v_fst_2217_) == 0)
{
lean_object* v___x_2219_; 
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v_a_2208_);
v___x_2219_ = v___x_2215_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2208_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
else
{
lean_object* v_val_2221_; lean_object* v___x_2223_; 
v_val_2221_ = lean_ctor_get(v_fst_2217_, 0);
lean_inc(v_val_2221_);
lean_dec_ref_known(v_fst_2217_, 1);
if (v_isShared_2216_ == 0)
{
lean_ctor_set(v___x_2215_, 0, v_val_2221_);
v___x_2223_ = v___x_2215_;
goto v_reusejp_2222_;
}
else
{
lean_object* v_reuseFailAlloc_2224_; 
v_reuseFailAlloc_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2224_, 0, v_val_2221_);
v___x_2223_ = v_reuseFailAlloc_2224_;
goto v_reusejp_2222_;
}
v_reusejp_2222_:
{
return v___x_2223_;
}
}
}
}
else
{
lean_object* v_a_2226_; lean_object* v___x_2228_; uint8_t v_isShared_2229_; uint8_t v_isSharedCheck_2233_; 
v_a_2226_ = lean_ctor_get(v___x_2212_, 0);
v_isSharedCheck_2233_ = !lean_is_exclusive(v___x_2212_);
if (v_isSharedCheck_2233_ == 0)
{
v___x_2228_ = v___x_2212_;
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
else
{
lean_inc(v_a_2226_);
lean_dec(v___x_2212_);
v___x_2228_ = lean_box(0);
v_isShared_2229_ = v_isSharedCheck_2233_;
goto v_resetjp_2227_;
}
v_resetjp_2227_:
{
lean_object* v___x_2231_; 
if (v_isShared_2229_ == 0)
{
v___x_2231_ = v___x_2228_;
goto v_reusejp_2230_;
}
else
{
lean_object* v_reuseFailAlloc_2232_; 
v_reuseFailAlloc_2232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2232_, 0, v_a_2226_);
v___x_2231_ = v_reuseFailAlloc_2232_;
goto v_reusejp_2230_;
}
v_reusejp_2230_:
{
return v___x_2231_;
}
}
}
}
else
{
lean_dec_ref_known(v_a_2208_, 1);
lean_dec(v_x_2198_);
return v___x_2207_;
}
}
else
{
lean_dec(v_x_2198_);
return v___x_2207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0___boxed(lean_object* v_x_2234_, lean_object* v_t_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2234_, v_t_2235_, v___y_2236_, v___y_2237_, v___y_2238_, v___y_2239_);
lean_dec(v___y_2239_);
lean_dec_ref(v___y_2238_);
lean_dec(v___y_2237_);
lean_dec_ref(v___y_2236_);
lean_dec_ref(v_t_2235_);
return v_res_2241_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(lean_object* v_x_2242_, lean_object* v_lctx_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v_decls_2249_; lean_object* v___x_2250_; 
v_decls_2249_ = lean_ctor_get(v_lctx_2243_, 1);
v___x_2250_ = l_Lean_PersistentArray_findSomeM_x3f___at___00Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0_spec__0(v_x_2242_, v_decls_2249_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
return v___x_2250_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0___boxed(lean_object* v_x_2251_, lean_object* v_lctx_2252_, lean_object* v___y_2253_, lean_object* v___y_2254_, lean_object* v___y_2255_, lean_object* v___y_2256_, lean_object* v___y_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2251_, v_lctx_2252_, v___y_2253_, v___y_2254_, v___y_2255_, v___y_2256_);
lean_dec(v___y_2256_);
lean_dec_ref(v___y_2255_);
lean_dec(v___y_2254_);
lean_dec_ref(v___y_2253_);
lean_dec_ref(v_lctx_2252_);
return v_res_2258_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
v___x_2260_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__0));
v___x_2261_ = l_Lean_stringToMessageData(v___x_2260_);
return v___x_2261_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2263_; lean_object* v___x_2264_; 
v___x_2263_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__2));
v___x_2264_ = l_Lean_stringToMessageData(v___x_2263_);
return v___x_2264_;
}
}
static lean_object* _init_l_Lean_Meta_substVar___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_Meta_substVar___lam__0___closed__4));
v___x_2267_ = l_Lean_stringToMessageData(v___x_2266_);
return v___x_2267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0(lean_object* v_x_2268_, lean_object* v_mvarId_2269_, lean_object* v___y_2270_, lean_object* v___y_2271_, lean_object* v___y_2272_, lean_object* v___y_2273_){
_start:
{
lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___x_2324_; 
lean_inc(v_x_2268_);
v___x_2324_ = l_Lean_FVarId_getDecl___redArg(v_x_2268_, v___y_2270_, v___y_2272_, v___y_2273_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; uint8_t v___x_2326_; uint8_t v___x_2327_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = 0;
v___x_2327_ = l_Lean_LocalDecl_isLet(v_a_2325_, v___x_2326_);
lean_dec(v_a_2325_);
if (v___x_2327_ == 0)
{
v___y_2276_ = v___y_2270_;
v___y_2277_ = v___y_2271_;
v___y_2278_ = v___y_2272_;
v___y_2279_ = v___y_2273_;
goto v___jp_2275_;
}
else
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2328_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2329_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__3, &l_Lean_Meta_substVar___lam__0___closed__3_once, _init_l_Lean_Meta_substVar___lam__0___closed__3);
lean_inc(v_x_2268_);
v___x_2330_ = l_Lean_mkFVar(v_x_2268_);
v___x_2331_ = l_Lean_MessageData_ofExpr(v___x_2330_);
v___x_2332_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2329_);
lean_ctor_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__5, &l_Lean_Meta_substVar___lam__0___closed__5_once, _init_l_Lean_Meta_substVar___lam__0___closed__5);
v___x_2334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2332_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_inc(v_mvarId_2269_);
v___x_2336_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2328_, v_mvarId_2269_, v___x_2335_, v___y_2270_, v___y_2271_, v___y_2272_, v___y_2273_);
if (lean_obj_tag(v___x_2336_) == 0)
{
lean_dec_ref_known(v___x_2336_, 1);
v___y_2276_ = v___y_2270_;
v___y_2277_ = v___y_2271_;
v___y_2278_ = v___y_2272_;
v___y_2279_ = v___y_2273_;
goto v___jp_2275_;
}
else
{
lean_object* v_a_2337_; lean_object* v___x_2339_; uint8_t v_isShared_2340_; uint8_t v_isSharedCheck_2344_; 
lean_dec(v_mvarId_2269_);
lean_dec(v_x_2268_);
v_a_2337_ = lean_ctor_get(v___x_2336_, 0);
v_isSharedCheck_2344_ = !lean_is_exclusive(v___x_2336_);
if (v_isSharedCheck_2344_ == 0)
{
v___x_2339_ = v___x_2336_;
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
else
{
lean_inc(v_a_2337_);
lean_dec(v___x_2336_);
v___x_2339_ = lean_box(0);
v_isShared_2340_ = v_isSharedCheck_2344_;
goto v_resetjp_2338_;
}
v_resetjp_2338_:
{
lean_object* v___x_2342_; 
if (v_isShared_2340_ == 0)
{
v___x_2342_ = v___x_2339_;
goto v_reusejp_2341_;
}
else
{
lean_object* v_reuseFailAlloc_2343_; 
v_reuseFailAlloc_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2343_, 0, v_a_2337_);
v___x_2342_ = v_reuseFailAlloc_2343_;
goto v_reusejp_2341_;
}
v_reusejp_2341_:
{
return v___x_2342_;
}
}
}
}
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2347_; uint8_t v_isShared_2348_; uint8_t v_isSharedCheck_2352_; 
lean_dec(v_mvarId_2269_);
lean_dec(v_x_2268_);
v_a_2345_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2352_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2347_ = v___x_2324_;
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
else
{
lean_inc(v_a_2345_);
lean_dec(v___x_2324_);
v___x_2347_ = lean_box(0);
v_isShared_2348_ = v_isSharedCheck_2352_;
goto v_resetjp_2346_;
}
v_resetjp_2346_:
{
lean_object* v___x_2350_; 
if (v_isShared_2348_ == 0)
{
v___x_2350_ = v___x_2347_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v_a_2345_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
return v___x_2350_;
}
}
}
v___jp_2275_:
{
lean_object* v_lctx_2280_; lean_object* v___x_2281_; 
v_lctx_2280_ = lean_ctor_get(v___y_2276_, 2);
lean_inc(v_x_2268_);
v___x_2281_ = l_Lean_LocalContext_findDeclM_x3f___at___00Lean_Meta_substVar_spec__0(v_x_2268_, v_lctx_2280_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
if (lean_obj_tag(v_a_2282_) == 1)
{
lean_object* v_val_2283_; lean_object* v_fst_2284_; lean_object* v_snd_2285_; lean_object* v___x_2286_; uint8_t v___x_2287_; uint8_t v___x_2288_; lean_object* v___x_2289_; 
lean_dec(v_x_2268_);
v_val_2283_ = lean_ctor_get(v_a_2282_, 0);
lean_inc(v_val_2283_);
lean_dec_ref_known(v_a_2282_, 1);
v_fst_2284_ = lean_ctor_get(v_val_2283_, 0);
lean_inc(v_fst_2284_);
v_snd_2285_ = lean_ctor_get(v_val_2283_, 1);
lean_inc(v_snd_2285_);
lean_dec(v_val_2283_);
v___x_2286_ = lean_box(0);
v___x_2287_ = 1;
v___x_2288_ = lean_unbox(v_snd_2285_);
lean_dec(v_snd_2285_);
v___x_2289_ = l_Lean_Meta_substCore(v_mvarId_2269_, v_fst_2284_, v___x_2288_, v___x_2286_, v___x_2287_, v___x_2287_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2292_; uint8_t v_isShared_2293_; uint8_t v_isSharedCheck_2298_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2292_ = v___x_2289_;
v_isShared_2293_ = v_isSharedCheck_2298_;
goto v_resetjp_2291_;
}
else
{
lean_inc(v_a_2290_);
lean_dec(v___x_2289_);
v___x_2292_ = lean_box(0);
v_isShared_2293_ = v_isSharedCheck_2298_;
goto v_resetjp_2291_;
}
v_resetjp_2291_:
{
lean_object* v_snd_2294_; lean_object* v___x_2296_; 
v_snd_2294_ = lean_ctor_get(v_a_2290_, 1);
lean_inc(v_snd_2294_);
lean_dec(v_a_2290_);
if (v_isShared_2293_ == 0)
{
lean_ctor_set(v___x_2292_, 0, v_snd_2294_);
v___x_2296_ = v___x_2292_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v_snd_2294_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v___x_2301_; uint8_t v_isShared_2302_; uint8_t v_isSharedCheck_2306_; 
v_a_2299_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2306_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2306_ == 0)
{
v___x_2301_ = v___x_2289_;
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
else
{
lean_inc(v_a_2299_);
lean_dec(v___x_2289_);
v___x_2301_ = lean_box(0);
v_isShared_2302_ = v_isSharedCheck_2306_;
goto v_resetjp_2300_;
}
v_resetjp_2300_:
{
lean_object* v___x_2304_; 
if (v_isShared_2302_ == 0)
{
v___x_2304_ = v___x_2301_;
goto v_reusejp_2303_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_a_2299_);
v___x_2304_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2303_;
}
v_reusejp_2303_:
{
return v___x_2304_;
}
}
}
}
else
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; 
lean_dec(v_a_2282_);
v___x_2307_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2308_ = lean_obj_once(&l_Lean_Meta_substVar___lam__0___closed__1, &l_Lean_Meta_substVar___lam__0___closed__1_once, _init_l_Lean_Meta_substVar___lam__0___closed__1);
v___x_2309_ = l_Lean_mkFVar(v_x_2268_);
v___x_2310_ = l_Lean_MessageData_ofExpr(v___x_2309_);
v___x_2311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2311_, 0, v___x_2308_);
lean_ctor_set(v___x_2311_, 1, v___x_2310_);
v___x_2312_ = lean_obj_once(&l_Lean_Meta_substCore___lam__3___closed__17, &l_Lean_Meta_substCore___lam__3___closed__17_once, _init_l_Lean_Meta_substCore___lam__3___closed__17);
v___x_2313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2313_, 0, v___x_2311_);
lean_ctor_set(v___x_2313_, 1, v___x_2312_);
v___x_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2314_, 0, v___x_2313_);
v___x_2315_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2307_, v_mvarId_2269_, v___x_2314_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
return v___x_2315_;
}
}
else
{
lean_object* v_a_2316_; lean_object* v___x_2318_; uint8_t v_isShared_2319_; uint8_t v_isSharedCheck_2323_; 
lean_dec(v_mvarId_2269_);
lean_dec(v_x_2268_);
v_a_2316_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2323_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2323_ == 0)
{
v___x_2318_ = v___x_2281_;
v_isShared_2319_ = v_isSharedCheck_2323_;
goto v_resetjp_2317_;
}
else
{
lean_inc(v_a_2316_);
lean_dec(v___x_2281_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___lam__0___boxed(lean_object* v_x_2353_, lean_object* v_mvarId_2354_, lean_object* v___y_2355_, lean_object* v___y_2356_, lean_object* v___y_2357_, lean_object* v___y_2358_, lean_object* v___y_2359_){
_start:
{
lean_object* v_res_2360_; 
v_res_2360_ = l_Lean_Meta_substVar___lam__0(v_x_2353_, v_mvarId_2354_, v___y_2355_, v___y_2356_, v___y_2357_, v___y_2358_);
lean_dec(v___y_2358_);
lean_dec_ref(v___y_2357_);
lean_dec(v___y_2356_);
lean_dec_ref(v___y_2355_);
return v_res_2360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar(lean_object* v_mvarId_2361_, lean_object* v_x_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v___f_2368_; lean_object* v___x_2369_; 
lean_inc(v_mvarId_2361_);
v___f_2368_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2368_, 0, v_x_2362_);
lean_closure_set(v___f_2368_, 1, v_mvarId_2361_);
v___x_2369_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2361_, v___f_2368_, v_a_2363_, v_a_2364_, v_a_2365_, v_a_2366_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar___boxed(lean_object* v_mvarId_2370_, lean_object* v_x_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_Lean_Meta_substVar(v_mvarId_2370_, v_x_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_);
lean_dec(v_a_2375_);
lean_dec_ref(v_a_2374_);
lean_dec(v_a_2373_);
lean_dec_ref(v_a_2372_);
return v_res_2377_;
}
}
static lean_object* _init_l_Lean_Meta_substEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; 
v___x_2379_ = ((lean_object*)(l_Lean_Meta_substEq___lam__0___closed__0));
v___x_2380_ = l_Lean_stringToMessageData(v___x_2379_);
return v___x_2380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0(lean_object* v_fst_2381_, lean_object* v_snd_2382_, uint8_t v___x_2383_, lean_object* v_fvarSubst_2384_, lean_object* v___y_2385_, lean_object* v___y_2386_, lean_object* v___y_2387_, lean_object* v___y_2388_){
_start:
{
lean_object* v___x_2390_; 
lean_inc(v_fst_2381_);
v___x_2390_ = l_Lean_FVarId_getDecl___redArg(v_fst_2381_, v___y_2385_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; lean_object* v___y_2393_; lean_object* v___y_2394_; lean_object* v___y_2395_; lean_object* v___y_2396_; lean_object* v_newType_2405_; uint8_t v_symm_2406_; lean_object* v___y_2407_; lean_object* v___y_2408_; lean_object* v___y_2409_; lean_object* v___y_2410_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
v___x_2446_ = l_Lean_LocalDecl_type(v_a_2391_);
v___x_2447_ = l_Lean_Meta_matchEq_x3f(v___x_2446_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2447_) == 0)
{
lean_object* v_a_2448_; 
v_a_2448_ = lean_ctor_get(v___x_2447_, 0);
lean_inc(v_a_2448_);
lean_dec_ref_known(v___x_2447_, 1);
if (lean_obj_tag(v_a_2448_) == 1)
{
lean_object* v_val_2449_; lean_object* v_snd_2450_; lean_object* v_fst_2451_; lean_object* v_snd_2452_; lean_object* v___x_2453_; 
v_val_2449_ = lean_ctor_get(v_a_2448_, 0);
lean_inc(v_val_2449_);
lean_dec_ref_known(v_a_2448_, 1);
v_snd_2450_ = lean_ctor_get(v_val_2449_, 1);
lean_inc(v_snd_2450_);
lean_dec(v_val_2449_);
v_fst_2451_ = lean_ctor_get(v_snd_2450_, 0);
lean_inc(v_fst_2451_);
v_snd_2452_ = lean_ctor_get(v_snd_2450_, 1);
lean_inc_n(v_snd_2452_, 2);
lean_dec(v_snd_2450_);
lean_inc(v___y_2388_);
lean_inc_ref(v___y_2387_);
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
v___x_2453_ = lean_whnf(v_snd_2452_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v_a_2454_; uint8_t v___x_2455_; 
v_a_2454_ = lean_ctor_get(v___x_2453_, 0);
lean_inc(v_a_2454_);
lean_dec_ref_known(v___x_2453_, 1);
v___x_2455_ = l_Lean_Expr_isFVar(v_a_2454_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
lean_dec(v_a_2454_);
lean_inc(v___y_2388_);
lean_inc_ref(v___y_2387_);
lean_inc(v___y_2386_);
lean_inc_ref(v___y_2385_);
lean_inc(v_fst_2451_);
v___x_2456_ = lean_whnf(v_fst_2451_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v_a_2457_; uint8_t v___y_2459_; uint8_t v___x_2471_; 
v_a_2457_ = lean_ctor_get(v___x_2456_, 0);
lean_inc(v_a_2457_);
lean_dec_ref_known(v___x_2456_, 1);
v___x_2471_ = l_Lean_Expr_isFVar(v_a_2457_);
if (v___x_2471_ == 0)
{
lean_dec(v_a_2457_);
lean_dec(v_snd_2452_);
lean_dec(v_fst_2451_);
lean_dec(v_fvarSubst_2384_);
lean_dec(v_fst_2381_);
v___y_2393_ = v___y_2385_;
v___y_2394_ = v___y_2386_;
v___y_2395_ = v___y_2387_;
v___y_2396_ = v___y_2388_;
goto v___jp_2392_;
}
else
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_expr_eqv(v_fst_2451_, v_a_2457_);
lean_dec(v_fst_2451_);
if (v___x_2472_ == 0)
{
v___y_2459_ = v___x_2471_;
goto v___jp_2458_;
}
else
{
v___y_2459_ = v___x_2455_;
goto v___jp_2458_;
}
}
v___jp_2458_:
{
if (v___y_2459_ == 0)
{
lean_object* v___x_2460_; 
lean_dec(v_a_2457_);
lean_dec(v_snd_2452_);
lean_dec(v_a_2391_);
v___x_2460_ = l_Lean_Meta_substCore(v_snd_2382_, v_fst_2381_, v___y_2459_, v_fvarSubst_2384_, v___x_2383_, v___x_2383_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v___x_2460_;
}
else
{
lean_object* v___x_2461_; 
v___x_2461_ = l_Lean_Meta_mkEq(v_a_2457_, v_snd_2452_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2461_) == 0)
{
lean_object* v_a_2462_; 
v_a_2462_ = lean_ctor_get(v___x_2461_, 0);
lean_inc(v_a_2462_);
lean_dec_ref_known(v___x_2461_, 1);
v_newType_2405_ = v_a_2462_;
v_symm_2406_ = v___x_2455_;
v___y_2407_ = v___y_2385_;
v___y_2408_ = v___y_2386_;
v___y_2409_ = v___y_2387_;
v___y_2410_ = v___y_2388_;
goto v___jp_2404_;
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec(v_a_2391_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v_fvarSubst_2384_);
lean_dec(v_snd_2382_);
lean_dec(v_fst_2381_);
v_a_2463_ = lean_ctor_get(v___x_2461_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2461_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2461_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2461_);
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
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec(v_snd_2452_);
lean_dec(v_fst_2451_);
lean_dec(v_a_2391_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v_fvarSubst_2384_);
lean_dec(v_snd_2382_);
lean_dec(v_fst_2381_);
v_a_2473_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2456_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2456_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
uint8_t v___x_2481_; 
v___x_2481_ = lean_expr_eqv(v_snd_2452_, v_a_2454_);
lean_dec(v_snd_2452_);
if (v___x_2481_ == 0)
{
if (v___x_2455_ == 0)
{
lean_object* v___x_2482_; 
lean_dec(v_a_2454_);
lean_dec(v_fst_2451_);
lean_dec(v_a_2391_);
v___x_2482_ = l_Lean_Meta_substCore(v_snd_2382_, v_fst_2381_, v___x_2383_, v_fvarSubst_2384_, v___x_2383_, v___x_2383_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v___x_2482_;
}
else
{
lean_object* v___x_2483_; 
v___x_2483_ = l_Lean_Meta_mkEq(v_fst_2451_, v_a_2454_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
if (lean_obj_tag(v___x_2483_) == 0)
{
lean_object* v_a_2484_; 
v_a_2484_ = lean_ctor_get(v___x_2483_, 0);
lean_inc(v_a_2484_);
lean_dec_ref_known(v___x_2483_, 1);
v_newType_2405_ = v_a_2484_;
v_symm_2406_ = v___x_2383_;
v___y_2407_ = v___y_2385_;
v___y_2408_ = v___y_2386_;
v___y_2409_ = v___y_2387_;
v___y_2410_ = v___y_2388_;
goto v___jp_2404_;
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec(v_a_2391_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v_fvarSubst_2384_);
lean_dec(v_snd_2382_);
lean_dec(v_fst_2381_);
v_a_2485_ = lean_ctor_get(v___x_2483_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2483_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2483_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2483_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
else
{
lean_object* v___x_2493_; 
lean_dec(v_a_2454_);
lean_dec(v_fst_2451_);
lean_dec(v_a_2391_);
v___x_2493_ = l_Lean_Meta_substCore(v_snd_2382_, v_fst_2381_, v___x_2383_, v_fvarSubst_2384_, v___x_2383_, v___x_2383_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
return v___x_2493_;
}
}
}
else
{
lean_object* v_a_2494_; lean_object* v___x_2496_; uint8_t v_isShared_2497_; uint8_t v_isSharedCheck_2501_; 
lean_dec(v_snd_2452_);
lean_dec(v_fst_2451_);
lean_dec(v_a_2391_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v_fvarSubst_2384_);
lean_dec(v_snd_2382_);
lean_dec(v_fst_2381_);
v_a_2494_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2501_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2501_ == 0)
{
v___x_2496_ = v___x_2453_;
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
else
{
lean_inc(v_a_2494_);
lean_dec(v___x_2453_);
v___x_2496_ = lean_box(0);
v_isShared_2497_ = v_isSharedCheck_2501_;
goto v_resetjp_2495_;
}
v_resetjp_2495_:
{
lean_object* v___x_2499_; 
if (v_isShared_2497_ == 0)
{
v___x_2499_ = v___x_2496_;
goto v_reusejp_2498_;
}
else
{
lean_object* v_reuseFailAlloc_2500_; 
v_reuseFailAlloc_2500_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2500_, 0, v_a_2494_);
v___x_2499_ = v_reuseFailAlloc_2500_;
goto v_reusejp_2498_;
}
v_reusejp_2498_:
{
return v___x_2499_;
}
}
}
}
else
{
lean_dec(v_a_2448_);
lean_dec(v_fvarSubst_2384_);
lean_dec(v_fst_2381_);
v___y_2393_ = v___y_2385_;
v___y_2394_ = v___y_2386_;
v___y_2395_ = v___y_2387_;
v___y_2396_ = v___y_2388_;
goto v___jp_2392_;
}
}
else
{
lean_object* v_a_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2509_; 
lean_dec(v_a_2391_);
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v_fvarSubst_2384_);
lean_dec(v_snd_2382_);
lean_dec(v_fst_2381_);
v_a_2502_ = lean_ctor_get(v___x_2447_, 0);
v_isSharedCheck_2509_ = !lean_is_exclusive(v___x_2447_);
if (v_isSharedCheck_2509_ == 0)
{
v___x_2504_ = v___x_2447_;
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_a_2502_);
lean_dec(v___x_2447_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2509_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2507_; 
if (v_isShared_2505_ == 0)
{
v___x_2507_ = v___x_2504_;
goto v_reusejp_2506_;
}
else
{
lean_object* v_reuseFailAlloc_2508_; 
v_reuseFailAlloc_2508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2508_, 0, v_a_2502_);
v___x_2507_ = v_reuseFailAlloc_2508_;
goto v_reusejp_2506_;
}
v_reusejp_2506_:
{
return v___x_2507_;
}
}
}
v___jp_2392_:
{
lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v___x_2397_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__1));
v___x_2398_ = lean_obj_once(&l_Lean_Meta_substEq___lam__0___closed__1, &l_Lean_Meta_substEq___lam__0___closed__1_once, _init_l_Lean_Meta_substEq___lam__0___closed__1);
v___x_2399_ = l_Lean_LocalDecl_type(v_a_2391_);
lean_dec(v_a_2391_);
v___x_2400_ = l_Lean_indentExpr(v___x_2399_);
v___x_2401_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2401_, 0, v___x_2398_);
lean_ctor_set(v___x_2401_, 1, v___x_2400_);
v___x_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2401_);
v___x_2403_ = l_Lean_Meta_throwTacticEx___redArg(v___x_2397_, v_snd_2382_, v___x_2402_, v___y_2393_, v___y_2394_, v___y_2395_, v___y_2396_);
lean_dec(v___y_2396_);
lean_dec_ref(v___y_2395_);
lean_dec(v___y_2394_);
lean_dec_ref(v___y_2393_);
return v___x_2403_;
}
v___jp_2404_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; 
v___x_2411_ = l_Lean_LocalDecl_userName(v_a_2391_);
lean_dec(v_a_2391_);
lean_inc(v_fst_2381_);
v___x_2412_ = l_Lean_mkFVar(v_fst_2381_);
v___x_2413_ = l_Lean_MVarId_assert(v_snd_2382_, v___x_2411_, v_newType_2405_, v___x_2412_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; lean_object* v___x_2415_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 1);
v___x_2415_ = l_Lean_Meta_intro1Core(v_a_2414_, v___x_2383_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2415_) == 0)
{
lean_object* v_a_2416_; lean_object* v_fst_2417_; lean_object* v_snd_2418_; lean_object* v___x_2419_; 
v_a_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_a_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v_fst_2417_ = lean_ctor_get(v_a_2416_, 0);
lean_inc(v_fst_2417_);
v_snd_2418_ = lean_ctor_get(v_a_2416_, 1);
lean_inc(v_snd_2418_);
lean_dec(v_a_2416_);
v___x_2419_ = l_Lean_MVarId_clear(v_snd_2418_, v_fst_2381_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v___x_2421_ = l_Lean_Meta_substCore(v_a_2420_, v_fst_2417_, v_symm_2406_, v_fvarSubst_2384_, v___x_2383_, v___x_2383_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
return v___x_2421_;
}
else
{
lean_object* v_a_2422_; lean_object* v___x_2424_; uint8_t v_isShared_2425_; uint8_t v_isSharedCheck_2429_; 
lean_dec(v_fst_2417_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v_fvarSubst_2384_);
v_a_2422_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2429_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2429_ == 0)
{
v___x_2424_ = v___x_2419_;
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
else
{
lean_inc(v_a_2422_);
lean_dec(v___x_2419_);
v___x_2424_ = lean_box(0);
v_isShared_2425_ = v_isSharedCheck_2429_;
goto v_resetjp_2423_;
}
v_resetjp_2423_:
{
lean_object* v___x_2427_; 
if (v_isShared_2425_ == 0)
{
v___x_2427_ = v___x_2424_;
goto v_reusejp_2426_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_a_2422_);
v___x_2427_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2426_;
}
v_reusejp_2426_:
{
return v___x_2427_;
}
}
}
}
else
{
lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2437_; 
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v_fvarSubst_2384_);
lean_dec(v_fst_2381_);
v_a_2430_ = lean_ctor_get(v___x_2415_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v___x_2415_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2432_ = v___x_2415_;
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2415_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2437_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2435_; 
if (v_isShared_2433_ == 0)
{
v___x_2435_ = v___x_2432_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2436_; 
v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
v___x_2435_ = v_reuseFailAlloc_2436_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
return v___x_2435_;
}
}
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec(v_fvarSubst_2384_);
lean_dec(v_fst_2381_);
v_a_2438_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2413_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2413_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_a_2438_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
else
{
lean_object* v_a_2510_; lean_object* v___x_2512_; uint8_t v_isShared_2513_; uint8_t v_isSharedCheck_2517_; 
lean_dec(v___y_2388_);
lean_dec_ref(v___y_2387_);
lean_dec(v___y_2386_);
lean_dec_ref(v___y_2385_);
lean_dec(v_fvarSubst_2384_);
lean_dec(v_snd_2382_);
lean_dec(v_fst_2381_);
v_a_2510_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2512_ = v___x_2390_;
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
else
{
lean_inc(v_a_2510_);
lean_dec(v___x_2390_);
v___x_2512_ = lean_box(0);
v_isShared_2513_ = v_isSharedCheck_2517_;
goto v_resetjp_2511_;
}
v_resetjp_2511_:
{
lean_object* v___x_2515_; 
if (v_isShared_2513_ == 0)
{
v___x_2515_ = v___x_2512_;
goto v_reusejp_2514_;
}
else
{
lean_object* v_reuseFailAlloc_2516_; 
v_reuseFailAlloc_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2516_, 0, v_a_2510_);
v___x_2515_ = v_reuseFailAlloc_2516_;
goto v_reusejp_2514_;
}
v_reusejp_2514_:
{
return v___x_2515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___lam__0___boxed(lean_object* v_fst_2518_, lean_object* v_snd_2519_, lean_object* v___x_2520_, lean_object* v_fvarSubst_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
uint8_t v___x_1937__boxed_2527_; lean_object* v_res_2528_; 
v___x_1937__boxed_2527_ = lean_unbox(v___x_2520_);
v_res_2528_ = l_Lean_Meta_substEq___lam__0(v_fst_2518_, v_snd_2519_, v___x_1937__boxed_2527_, v_fvarSubst_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
return v_res_2528_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq(lean_object* v_mvarId_2529_, lean_object* v_hFVarId_2530_, lean_object* v_fvarSubst_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
uint8_t v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = 1;
v___x_2538_ = l_Lean_Meta_heqToEq(v_mvarId_2529_, v_hFVarId_2530_, v___x_2537_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v_fst_2540_; lean_object* v_snd_2541_; lean_object* v___x_2542_; lean_object* v___f_2543_; lean_object* v___x_2544_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
v_fst_2540_ = lean_ctor_get(v_a_2539_, 0);
lean_inc(v_fst_2540_);
v_snd_2541_ = lean_ctor_get(v_a_2539_, 1);
lean_inc_n(v_snd_2541_, 2);
lean_dec(v_a_2539_);
v___x_2542_ = lean_box(v___x_2537_);
v___f_2543_ = lean_alloc_closure((void*)(l_Lean_Meta_substEq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_2543_, 0, v_fst_2540_);
lean_closure_set(v___f_2543_, 1, v_snd_2541_);
lean_closure_set(v___f_2543_, 2, v___x_2542_);
lean_closure_set(v___f_2543_, 3, v_fvarSubst_2531_);
v___x_2544_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_snd_2541_, v___f_2543_, v_a_2532_, v_a_2533_, v_a_2534_, v_a_2535_);
return v___x_2544_;
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
lean_dec(v_fvarSubst_2531_);
v_a_2545_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2538_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2538_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substEq___boxed(lean_object* v_mvarId_2553_, lean_object* v_hFVarId_2554_, lean_object* v_fvarSubst_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v_res_2561_; 
v_res_2561_ = l_Lean_Meta_substEq(v_mvarId_2553_, v_hFVarId_2554_, v_fvarSubst_2555_, v_a_2556_, v_a_2557_, v_a_2558_, v_a_2559_);
lean_dec(v_a_2559_);
lean_dec_ref(v_a_2558_);
lean_dec(v_a_2557_);
lean_dec_ref(v_a_2556_);
return v_res_2561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0(lean_object* v_h_2562_, lean_object* v_mvarId_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_){
_start:
{
lean_object* v___x_2569_; 
lean_inc(v_h_2562_);
v___x_2569_ = l_Lean_FVarId_getType___redArg(v_h_2562_, v___y_2564_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; lean_object* v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc_n(v_a_2570_, 2);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = l_Lean_Meta_matchEq_x3f(v_a_2570_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2571_) == 0)
{
lean_object* v_a_2572_; 
v_a_2572_ = lean_ctor_get(v___x_2571_, 0);
lean_inc(v_a_2572_);
lean_dec_ref_known(v___x_2571_, 1);
if (lean_obj_tag(v_a_2572_) == 0)
{
lean_object* v___x_2573_; 
v___x_2573_ = l_Lean_Meta_matchHEq_x3f(v_a_2570_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
if (lean_obj_tag(v_a_2574_) == 0)
{
lean_object* v___x_2575_; 
v___x_2575_ = l_Lean_Meta_substVar(v_mvarId_2563_, v_h_2562_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
return v___x_2575_;
}
else
{
uint8_t v___x_2576_; lean_object* v___x_2577_; 
lean_dec_ref_known(v_a_2574_, 1);
v___x_2576_ = 1;
lean_inc(v_h_2562_);
lean_inc(v_mvarId_2563_);
v___x_2577_ = l_Lean_Meta_heqToEq(v_mvarId_2563_, v_h_2562_, v___x_2576_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2577_) == 0)
{
lean_object* v_a_2578_; lean_object* v_fst_2579_; lean_object* v_snd_2580_; uint8_t v___x_2581_; 
v_a_2578_ = lean_ctor_get(v___x_2577_, 0);
lean_inc(v_a_2578_);
lean_dec_ref_known(v___x_2577_, 1);
v_fst_2579_ = lean_ctor_get(v_a_2578_, 0);
lean_inc(v_fst_2579_);
v_snd_2580_ = lean_ctor_get(v_a_2578_, 1);
lean_inc(v_snd_2580_);
lean_dec(v_a_2578_);
v___x_2581_ = l_Lean_instBEqMVarId_beq(v_mvarId_2563_, v_snd_2580_);
if (v___x_2581_ == 0)
{
lean_object* v___x_2582_; 
lean_dec(v_mvarId_2563_);
lean_dec(v_h_2562_);
v___x_2582_ = l_Lean_Meta_subst(v_snd_2580_, v_fst_2579_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
return v___x_2582_;
}
else
{
lean_object* v___x_2583_; 
lean_dec(v_snd_2580_);
lean_dec(v_fst_2579_);
v___x_2583_ = l_Lean_Meta_substVar(v_mvarId_2563_, v_h_2562_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
return v___x_2583_;
}
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec(v_mvarId_2563_);
lean_dec(v_h_2562_);
v_a_2584_ = lean_ctor_get(v___x_2577_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2577_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2577_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2577_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec(v_mvarId_2563_);
lean_dec(v_h_2562_);
v_a_2592_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2573_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2573_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
else
{
lean_object* v___x_2600_; lean_object* v___x_2601_; 
lean_dec_ref_known(v_a_2572_, 1);
lean_dec(v_a_2570_);
v___x_2600_ = lean_box(0);
v___x_2601_ = l_Lean_Meta_substEq(v_mvarId_2563_, v_h_2562_, v___x_2600_, v___y_2564_, v___y_2565_, v___y_2566_, v___y_2567_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_object* v_a_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2610_; 
v_a_2602_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2610_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2610_ == 0)
{
v___x_2604_ = v___x_2601_;
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_a_2602_);
lean_dec(v___x_2601_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2610_;
goto v_resetjp_2603_;
}
v_resetjp_2603_:
{
lean_object* v_snd_2606_; lean_object* v___x_2608_; 
v_snd_2606_ = lean_ctor_get(v_a_2602_, 1);
lean_inc(v_snd_2606_);
lean_dec(v_a_2602_);
if (v_isShared_2605_ == 0)
{
lean_ctor_set(v___x_2604_, 0, v_snd_2606_);
v___x_2608_ = v___x_2604_;
goto v_reusejp_2607_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_snd_2606_);
v___x_2608_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2607_;
}
v_reusejp_2607_:
{
return v___x_2608_;
}
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
v_a_2611_ = lean_ctor_get(v___x_2601_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2601_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2601_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2601_);
v___x_2613_ = lean_box(0);
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
v_resetjp_2612_:
{
lean_object* v___x_2616_; 
if (v_isShared_2614_ == 0)
{
v___x_2616_ = v___x_2613_;
goto v_reusejp_2615_;
}
else
{
lean_object* v_reuseFailAlloc_2617_; 
v_reuseFailAlloc_2617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2617_, 0, v_a_2611_);
v___x_2616_ = v_reuseFailAlloc_2617_;
goto v_reusejp_2615_;
}
v_reusejp_2615_:
{
return v___x_2616_;
}
}
}
}
}
else
{
lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2626_; 
lean_dec(v_a_2570_);
lean_dec(v_mvarId_2563_);
lean_dec(v_h_2562_);
v_a_2619_ = lean_ctor_get(v___x_2571_, 0);
v_isSharedCheck_2626_ = !lean_is_exclusive(v___x_2571_);
if (v_isSharedCheck_2626_ == 0)
{
v___x_2621_ = v___x_2571_;
v_isShared_2622_ = v_isSharedCheck_2626_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_dec(v___x_2571_);
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
else
{
lean_object* v_a_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2634_; 
lean_dec(v_mvarId_2563_);
lean_dec(v_h_2562_);
v_a_2627_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2634_ == 0)
{
v___x_2629_ = v___x_2569_;
v_isShared_2630_ = v_isSharedCheck_2634_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_a_2627_);
lean_dec(v___x_2569_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___lam__0___boxed(lean_object* v_h_2635_, lean_object* v_mvarId_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_, lean_object* v___y_2639_, lean_object* v___y_2640_, lean_object* v___y_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_Lean_Meta_subst___lam__0(v_h_2635_, v_mvarId_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_);
lean_dec(v___y_2640_);
lean_dec_ref(v___y_2639_);
lean_dec(v___y_2638_);
lean_dec_ref(v___y_2637_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst(lean_object* v_mvarId_2643_, lean_object* v_h_2644_, lean_object* v_a_2645_, lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_){
_start:
{
lean_object* v___f_2650_; lean_object* v___x_2651_; 
lean_inc(v_mvarId_2643_);
v___f_2650_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2650_, 0, v_h_2644_);
lean_closure_set(v___f_2650_, 1, v_mvarId_2643_);
v___x_2651_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_2643_, v___f_2650_, v_a_2645_, v_a_2646_, v_a_2647_, v_a_2648_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst___boxed(lean_object* v_mvarId_2652_, lean_object* v_h_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lean_Meta_subst(v_mvarId_2652_, v_h_2653_, v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(lean_object* v_x_2660_, lean_object* v___y_2661_, lean_object* v___y_2662_, lean_object* v___y_2663_, lean_object* v___y_2664_){
_start:
{
lean_object* v___x_2666_; 
v___x_2666_ = l_Lean_Meta_saveState___redArg(v___y_2662_, v___y_2664_);
if (lean_obj_tag(v___x_2666_) == 0)
{
lean_object* v_a_2667_; lean_object* v___x_2668_; 
v_a_2667_ = lean_ctor_get(v___x_2666_, 0);
lean_inc(v_a_2667_);
lean_dec_ref_known(v___x_2666_, 1);
lean_inc(v___y_2664_);
lean_inc_ref(v___y_2663_);
lean_inc(v___y_2662_);
lean_inc_ref(v___y_2661_);
v___x_2668_ = lean_apply_5(v_x_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, lean_box(0));
if (lean_obj_tag(v___x_2668_) == 0)
{
lean_dec(v_a_2667_);
return v___x_2668_;
}
else
{
lean_object* v_a_2669_; uint8_t v___y_2671_; uint8_t v___x_2689_; 
v_a_2669_ = lean_ctor_get(v___x_2668_, 0);
lean_inc(v_a_2669_);
v___x_2689_ = l_Lean_Exception_isInterrupt(v_a_2669_);
if (v___x_2689_ == 0)
{
uint8_t v___x_2690_; 
lean_inc(v_a_2669_);
v___x_2690_ = l_Lean_Exception_isRuntime(v_a_2669_);
v___y_2671_ = v___x_2690_;
goto v___jp_2670_;
}
else
{
v___y_2671_ = v___x_2689_;
goto v___jp_2670_;
}
v___jp_2670_:
{
if (v___y_2671_ == 0)
{
lean_object* v___x_2672_; 
lean_dec_ref_known(v___x_2668_, 1);
v___x_2672_ = l_Lean_Meta_SavedState_restore___redArg(v_a_2667_, v___y_2662_, v___y_2664_);
lean_dec(v_a_2667_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
v_isSharedCheck_2679_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; 
v_unused_2680_ = lean_ctor_get(v___x_2672_, 0);
lean_dec(v_unused_2680_);
v___x_2674_ = v___x_2672_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_dec(v___x_2672_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
lean_ctor_set_tag(v___x_2674_, 1);
lean_ctor_set(v___x_2674_, 0, v_a_2669_);
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2669_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
else
{
lean_object* v_a_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2688_; 
lean_dec(v_a_2669_);
v_a_2681_ = lean_ctor_get(v___x_2672_, 0);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2672_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2683_ = v___x_2672_;
v_isShared_2684_ = v_isSharedCheck_2688_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_a_2681_);
lean_dec(v___x_2672_);
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
else
{
lean_dec(v_a_2669_);
lean_dec(v_a_2667_);
return v___x_2668_;
}
}
}
}
else
{
lean_object* v_a_2691_; lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2698_; 
lean_dec_ref(v_x_2660_);
v_a_2691_ = lean_ctor_get(v___x_2666_, 0);
v_isSharedCheck_2698_ = !lean_is_exclusive(v___x_2666_);
if (v_isSharedCheck_2698_ == 0)
{
v___x_2693_ = v___x_2666_;
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
else
{
lean_inc(v_a_2691_);
lean_dec(v___x_2666_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2698_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2696_; 
if (v_isShared_2694_ == 0)
{
v___x_2696_ = v___x_2693_;
goto v_reusejp_2695_;
}
else
{
lean_object* v_reuseFailAlloc_2697_; 
v_reuseFailAlloc_2697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2697_, 0, v_a_2691_);
v___x_2696_ = v_reuseFailAlloc_2697_;
goto v_reusejp_2695_;
}
v_reusejp_2695_:
{
return v___x_2696_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg___boxed(lean_object* v_x_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(lean_object* v_00_u03b1_2706_, lean_object* v_x_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_, lean_object* v___y_2711_){
_start:
{
lean_object* v___x_2713_; 
v___x_2713_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v_x_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
return v___x_2713_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___boxed(lean_object* v_00_u03b1_2714_, lean_object* v_x_2715_, lean_object* v___y_2716_, lean_object* v___y_2717_, lean_object* v___y_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_){
_start:
{
lean_object* v_res_2721_; 
v_res_2721_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1(v_00_u03b1_2714_, v_x_2715_, v___y_2716_, v___y_2717_, v___y_2718_, v___y_2719_);
lean_dec(v___y_2719_);
lean_dec_ref(v___y_2718_);
lean_dec(v___y_2717_);
lean_dec_ref(v___y_2716_);
return v_res_2721_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(lean_object* v_msg_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
lean_object* v_ref_2728_; lean_object* v___x_2729_; lean_object* v_a_2730_; lean_object* v___x_2732_; uint8_t v_isShared_2733_; uint8_t v_isSharedCheck_2738_; 
v_ref_2728_ = lean_ctor_get(v___y_2725_, 5);
v___x_2729_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_substCore_spec__3_spec__3(v_msg_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
v_a_2730_ = lean_ctor_get(v___x_2729_, 0);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2729_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2732_ = v___x_2729_;
v_isShared_2733_ = v_isSharedCheck_2738_;
goto v_resetjp_2731_;
}
else
{
lean_inc(v_a_2730_);
lean_dec(v___x_2729_);
v___x_2732_ = lean_box(0);
v_isShared_2733_ = v_isSharedCheck_2738_;
goto v_resetjp_2731_;
}
v_resetjp_2731_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
lean_inc(v_ref_2728_);
v___x_2734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2734_, 0, v_ref_2728_);
lean_ctor_set(v___x_2734_, 1, v_a_2730_);
if (v_isShared_2733_ == 0)
{
lean_ctor_set_tag(v___x_2732_, 1);
lean_ctor_set(v___x_2732_, 0, v___x_2734_);
v___x_2736_ = v___x_2732_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v___x_2734_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg___boxed(lean_object* v_msg_2739_, lean_object* v___y_2740_, lean_object* v___y_2741_, lean_object* v___y_2742_, lean_object* v___y_2743_, lean_object* v___y_2744_){
_start:
{
lean_object* v_res_2745_; 
v_res_2745_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_);
lean_dec(v___y_2743_);
lean_dec_ref(v___y_2742_);
lean_dec(v___y_2741_);
lean_dec_ref(v___y_2740_);
return v_res_2745_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2747_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__0));
v___x_2748_ = l_Lean_stringToMessageData(v___x_2747_);
return v___x_2748_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2750_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__2));
v___x_2751_ = l_Lean_stringToMessageData(v___x_2750_);
return v___x_2751_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; 
v___x_2753_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__4));
v___x_2754_ = l_Lean_stringToMessageData(v___x_2753_);
return v___x_2754_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2756_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__6));
v___x_2757_ = l_Lean_stringToMessageData(v___x_2756_);
return v___x_2757_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__9(void){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; 
v___x_2759_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__8));
v___x_2760_ = l_Lean_stringToMessageData(v___x_2759_);
return v___x_2760_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__0___closed__17(void){
_start:
{
lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2773_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__16));
v___x_2774_ = l_Lean_stringToMessageData(v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0(lean_object* v_mvarId_2783_, uint8_t v_substLHS_2784_, lean_object* v___y_2785_, lean_object* v___y_2786_, lean_object* v___y_2787_, lean_object* v___y_2788_){
_start:
{
lean_object* v___x_2790_; 
lean_inc(v_mvarId_2783_);
v___x_2790_ = l_Lean_MVarId_getType_x27(v_mvarId_2783_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2790_) == 0)
{
lean_object* v_a_2791_; 
v_a_2791_ = lean_ctor_get(v___x_2790_, 0);
lean_inc(v_a_2791_);
lean_dec_ref_known(v___x_2790_, 1);
if (lean_obj_tag(v_a_2791_) == 7)
{
lean_object* v_binderType_2795_; lean_object* v_body_2796_; uint8_t v___x_2797_; lean_object* v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; lean_object* v___y_2805_; lean_object* v___y_2806_; lean_object* v___y_2807_; lean_object* v___y_2808_; lean_object* v___y_2809_; lean_object* v___y_2885_; lean_object* v___y_2886_; lean_object* v___y_2887_; lean_object* v___y_2888_; lean_object* v___y_2889_; lean_object* v___y_2890_; lean_object* v___y_2891_; lean_object* v___y_2892_; lean_object* v_fst_2932_; lean_object* v_fst_2933_; lean_object* v_fst_2934_; lean_object* v_snd_2935_; lean_object* v___y_2936_; lean_object* v___y_2937_; lean_object* v___y_2938_; lean_object* v___y_2939_; 
v_binderType_2795_ = lean_ctor_get(v_a_2791_, 1);
lean_inc_ref(v_binderType_2795_);
v_body_2796_ = lean_ctor_get(v_a_2791_, 2);
lean_inc_ref(v_body_2796_);
lean_dec_ref_known(v_a_2791_, 3);
v___x_2797_ = l_Lean_Expr_hasLooseBVars(v_body_2796_);
if (v___x_2797_ == 0)
{
lean_object* v___x_2951_; 
v___x_2951_ = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_binderType_2795_, v___y_2786_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v___y_2954_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___x_2968_; uint8_t v___x_2969_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v___x_2968_ = l_Lean_Expr_cleanupAnnotations(v_a_2952_);
v___x_2969_ = l_Lean_Expr_isApp(v___x_2968_);
if (v___x_2969_ == 0)
{
lean_dec_ref(v___x_2968_);
lean_dec_ref(v_body_2796_);
lean_dec(v_mvarId_2783_);
v___y_2954_ = v___y_2785_;
v___y_2955_ = v___y_2786_;
v___y_2956_ = v___y_2787_;
v___y_2957_ = v___y_2788_;
goto v___jp_2953_;
}
else
{
lean_object* v_arg_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_arg_2970_ = lean_ctor_get(v___x_2968_, 1);
lean_inc_ref(v_arg_2970_);
v___x_2971_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2968_);
v___x_2972_ = l_Lean_Expr_isApp(v___x_2971_);
if (v___x_2972_ == 0)
{
lean_dec_ref(v___x_2971_);
lean_dec_ref(v_arg_2970_);
lean_dec_ref(v_body_2796_);
lean_dec(v_mvarId_2783_);
v___y_2954_ = v___y_2785_;
v___y_2955_ = v___y_2786_;
v___y_2956_ = v___y_2787_;
v___y_2957_ = v___y_2788_;
goto v___jp_2953_;
}
else
{
lean_object* v_arg_2973_; lean_object* v___x_2974_; uint8_t v___x_2975_; 
v_arg_2973_ = lean_ctor_get(v___x_2971_, 1);
lean_inc_ref(v_arg_2973_);
v___x_2974_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2971_);
v___x_2975_ = l_Lean_Expr_isApp(v___x_2974_);
if (v___x_2975_ == 0)
{
lean_dec_ref(v___x_2974_);
lean_dec_ref(v_arg_2973_);
lean_dec_ref(v_arg_2970_);
lean_dec_ref(v_body_2796_);
lean_dec(v_mvarId_2783_);
v___y_2954_ = v___y_2785_;
v___y_2955_ = v___y_2786_;
v___y_2956_ = v___y_2787_;
v___y_2957_ = v___y_2788_;
goto v___jp_2953_;
}
else
{
lean_object* v_arg_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; uint8_t v___x_2979_; 
v_arg_2976_ = lean_ctor_get(v___x_2974_, 1);
lean_inc_ref(v_arg_2976_);
v___x_2977_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2974_);
v___x_2978_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__11));
v___x_2979_ = l_Lean_Expr_isConstOf(v___x_2977_, v___x_2978_);
if (v___x_2979_ == 0)
{
uint8_t v___x_2980_; 
v___x_2980_ = l_Lean_Expr_isApp(v___x_2977_);
if (v___x_2980_ == 0)
{
lean_dec_ref(v___x_2977_);
lean_dec_ref(v_arg_2976_);
lean_dec_ref(v_arg_2973_);
lean_dec_ref(v_arg_2970_);
lean_dec_ref(v_body_2796_);
lean_dec(v_mvarId_2783_);
v___y_2954_ = v___y_2785_;
v___y_2955_ = v___y_2786_;
v___y_2956_ = v___y_2787_;
v___y_2957_ = v___y_2788_;
goto v___jp_2953_;
}
else
{
lean_object* v_arg_2981_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___x_2989_; lean_object* v___x_2990_; uint8_t v___x_2991_; 
v_arg_2981_ = lean_ctor_get(v___x_2977_, 1);
lean_inc_ref(v_arg_2981_);
v___x_2989_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2977_);
v___x_2990_ = ((lean_object*)(l_Lean_Meta_heqToEq___lam__0___closed__1));
v___x_2991_ = l_Lean_Expr_isConstOf(v___x_2989_, v___x_2990_);
lean_dec_ref(v___x_2989_);
if (v___x_2991_ == 0)
{
lean_dec_ref(v_arg_2981_);
lean_dec_ref(v_arg_2976_);
lean_dec_ref(v_arg_2973_);
lean_dec_ref(v_arg_2970_);
lean_dec_ref(v_body_2796_);
lean_dec(v_mvarId_2783_);
v___y_2954_ = v___y_2785_;
v___y_2955_ = v___y_2786_;
v___y_2956_ = v___y_2787_;
v___y_2957_ = v___y_2788_;
goto v___jp_2953_;
}
else
{
lean_object* v___x_2992_; 
lean_inc_ref(v_arg_2981_);
v___x_2992_ = l_Lean_Meta_isExprDefEq(v_arg_2981_, v_arg_2973_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
if (lean_obj_tag(v___x_2992_) == 0)
{
lean_object* v_a_2993_; uint8_t v___x_2994_; 
v_a_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_a_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v___x_2994_ = lean_unbox(v_a_2993_);
lean_dec(v_a_2993_);
if (v___x_2994_ == 0)
{
lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_dec_ref(v_arg_2981_);
lean_dec_ref(v_arg_2976_);
lean_dec_ref(v_arg_2970_);
lean_dec_ref(v_body_2796_);
lean_dec(v_mvarId_2783_);
v___x_2995_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__17, &l_Lean_Meta_introSubstEq___lam__0___closed__17_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__17);
v___x_2996_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2995_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
v_a_2997_ = lean_ctor_get(v___x_2996_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2996_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2996_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2996_);
v___x_2999_ = lean_box(0);
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
v_resetjp_2998_:
{
lean_object* v___x_3002_; 
if (v_isShared_3000_ == 0)
{
v___x_3002_ = v___x_2999_;
goto v_reusejp_3001_;
}
else
{
lean_object* v_reuseFailAlloc_3003_; 
v_reuseFailAlloc_3003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3003_, 0, v_a_2997_);
v___x_3002_ = v_reuseFailAlloc_3003_;
goto v_reusejp_3001_;
}
v_reusejp_3001_:
{
return v___x_3002_;
}
}
}
else
{
v___y_2983_ = v___y_2785_;
v___y_2984_ = v___y_2786_;
v___y_2985_ = v___y_2787_;
v___y_2986_ = v___y_2788_;
goto v___jp_2982_;
}
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_dec_ref(v_arg_2981_);
lean_dec_ref(v_arg_2976_);
lean_dec_ref(v_arg_2970_);
lean_dec_ref(v_body_2796_);
lean_dec(v_mvarId_2783_);
v_a_3005_ = lean_ctor_get(v___x_2992_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2992_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2992_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2992_);
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
v___jp_2982_:
{
if (v_substLHS_2784_ == 0)
{
lean_object* v___x_2987_; 
v___x_2987_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__13));
v_fst_2932_ = v_arg_2981_;
v_fst_2933_ = v_arg_2976_;
v_fst_2934_ = v_arg_2970_;
v_snd_2935_ = v___x_2987_;
v___y_2936_ = v___y_2983_;
v___y_2937_ = v___y_2984_;
v___y_2938_ = v___y_2985_;
v___y_2939_ = v___y_2986_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_2988_; 
v___x_2988_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__15));
v_fst_2932_ = v_arg_2981_;
v_fst_2933_ = v_arg_2970_;
v_fst_2934_ = v_arg_2976_;
v_snd_2935_ = v___x_2988_;
v___y_2936_ = v___y_2983_;
v___y_2937_ = v___y_2984_;
v___y_2938_ = v___y_2985_;
v___y_2939_ = v___y_2986_;
goto v___jp_2931_;
}
}
}
}
else
{
lean_dec_ref(v___x_2977_);
if (v_substLHS_2784_ == 0)
{
lean_object* v___x_3013_; 
v___x_3013_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__19));
v_fst_2932_ = v_arg_2976_;
v_fst_2933_ = v_arg_2973_;
v_fst_2934_ = v_arg_2970_;
v_snd_2935_ = v___x_3013_;
v___y_2936_ = v___y_2785_;
v___y_2937_ = v___y_2786_;
v___y_2938_ = v___y_2787_;
v___y_2939_ = v___y_2788_;
goto v___jp_2931_;
}
else
{
lean_object* v___x_3014_; 
v___x_3014_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__0___closed__21));
v_fst_2932_ = v_arg_2976_;
v_fst_2933_ = v_arg_2970_;
v_fst_2934_ = v_arg_2973_;
v_snd_2935_ = v___x_3014_;
v___y_2936_ = v___y_2785_;
v___y_2937_ = v___y_2786_;
v___y_2938_ = v___y_2787_;
v___y_2939_ = v___y_2788_;
goto v___jp_2931_;
}
}
}
}
}
v___jp_2953_:
{
lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
v___x_2958_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__9, &l_Lean_Meta_introSubstEq___lam__0___closed__9_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__9);
v___x_2959_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2958_, v___y_2954_, v___y_2955_, v___y_2956_, v___y_2957_);
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2959_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2959_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec_ref(v_body_2796_);
lean_dec(v_mvarId_2783_);
v_a_3015_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2951_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2951_);
v___x_3017_ = lean_box(0);
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
v_resetjp_3016_:
{
lean_object* v___x_3020_; 
if (v_isShared_3018_ == 0)
{
v___x_3020_ = v___x_3017_;
goto v_reusejp_3019_;
}
else
{
lean_object* v_reuseFailAlloc_3021_; 
v_reuseFailAlloc_3021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3021_, 0, v_a_3015_);
v___x_3020_ = v_reuseFailAlloc_3021_;
goto v_reusejp_3019_;
}
v_reusejp_3019_:
{
return v___x_3020_;
}
}
}
}
else
{
lean_dec_ref(v_body_2796_);
lean_dec_ref(v_binderType_2795_);
lean_dec(v_mvarId_2783_);
goto v___jp_2792_;
}
v___jp_2798_:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; uint8_t v___x_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; 
v___x_2810_ = lean_mk_empty_array_with_capacity(v___y_2799_);
lean_inc_ref(v___x_2810_);
v___x_2811_ = lean_array_push(v___x_2810_, v___y_2805_);
v___x_2812_ = 1;
v___x_2813_ = 1;
v___x_2814_ = l_Lean_Meta_mkLambdaFVars(v___x_2811_, v_body_2796_, v___x_2797_, v___x_2812_, v___x_2797_, v___x_2812_, v___x_2813_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec_ref(v___x_2811_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; lean_object* v___x_2816_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
lean_inc(v___y_2802_);
v___x_2816_ = l_Lean_MVarId_getTag(v___y_2802_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2816_) == 0)
{
lean_object* v_a_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v_a_2817_ = lean_ctor_get(v___x_2816_, 0);
lean_inc(v_a_2817_);
lean_dec_ref_known(v___x_2816_, 1);
lean_inc_ref(v___y_2801_);
v___x_2818_ = lean_array_push(v___x_2810_, v___y_2801_);
lean_inc(v_a_2815_);
v___x_2819_ = l_Lean_Expr_beta(v_a_2815_, v___x_2818_);
lean_inc_ref(v___x_2819_);
v___x_2820_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v___x_2819_, v_a_2817_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = l_Lean_Meta_getLevel(v___x_2819_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2822_) == 0)
{
lean_object* v_a_2823_; lean_object* v___x_2824_; 
v_a_2823_ = lean_ctor_get(v___x_2822_, 0);
lean_inc(v_a_2823_);
lean_dec_ref_known(v___x_2822_, 1);
lean_inc_ref(v___y_2804_);
v___x_2824_ = l_Lean_Meta_getLevel(v___y_2804_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2842_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
v___x_2826_ = lean_box(0);
v___x_2827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2827_, 0, v_a_2825_);
lean_ctor_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2828_, 0, v_a_2823_);
lean_ctor_set(v___x_2828_, 1, v___x_2827_);
lean_inc(v___y_2803_);
v___x_2829_ = l_Lean_mkConst(v___y_2803_, v___x_2828_);
lean_inc(v_a_2821_);
lean_inc_ref(v___y_2801_);
v___x_2830_ = l_Lean_mkApp4(v___x_2829_, v___y_2804_, v___y_2801_, v_a_2815_, v_a_2821_);
v___x_2831_ = l_Lean_MVarId_assign___at___00Lean_Meta_substCore_spec__5___redArg(v___y_2802_, v___x_2830_, v___y_2807_);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2842_ == 0)
{
lean_object* v_unused_2843_; 
v_unused_2843_ = lean_ctor_get(v___x_2831_, 0);
lean_dec(v_unused_2843_);
v___x_2833_ = v___x_2831_;
v_isShared_2834_ = v_isSharedCheck_2842_;
goto v_resetjp_2832_;
}
else
{
lean_dec(v___x_2831_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2842_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2840_; 
v___x_2835_ = l_Lean_Meta_FVarSubst_empty;
v___x_2836_ = l_Lean_Meta_FVarSubst_insert(v___x_2835_, v___y_2800_, v___y_2801_);
v___x_2837_ = l_Lean_Expr_mvarId_x21(v_a_2821_);
lean_dec(v_a_2821_);
v___x_2838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2836_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2838_);
v___x_2840_ = v___x_2833_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v___x_2838_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec(v_a_2823_);
lean_dec(v_a_2821_);
lean_dec(v_a_2815_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
v_a_2844_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___x_2824_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___x_2824_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_a_2821_);
lean_dec(v_a_2815_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
v_a_2852_ = lean_ctor_get(v___x_2822_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2822_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2822_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2822_);
v___x_2854_ = lean_box(0);
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
v_resetjp_2853_:
{
lean_object* v___x_2857_; 
if (v_isShared_2855_ == 0)
{
v___x_2857_ = v___x_2854_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v_a_2852_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec_ref(v___x_2819_);
lean_dec(v_a_2815_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
v_a_2860_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2820_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2820_);
v___x_2862_ = lean_box(0);
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
v_resetjp_2861_:
{
lean_object* v___x_2865_; 
if (v_isShared_2863_ == 0)
{
v___x_2865_ = v___x_2862_;
goto v_reusejp_2864_;
}
else
{
lean_object* v_reuseFailAlloc_2866_; 
v_reuseFailAlloc_2866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2866_, 0, v_a_2860_);
v___x_2865_ = v_reuseFailAlloc_2866_;
goto v_reusejp_2864_;
}
v_reusejp_2864_:
{
return v___x_2865_;
}
}
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec(v_a_2815_);
lean_dec_ref(v___x_2810_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
v_a_2868_ = lean_ctor_get(v___x_2816_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2816_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2816_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2816_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v___x_2873_; 
if (v_isShared_2871_ == 0)
{
v___x_2873_ = v___x_2870_;
goto v_reusejp_2872_;
}
else
{
lean_object* v_reuseFailAlloc_2874_; 
v_reuseFailAlloc_2874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2868_);
v___x_2873_ = v_reuseFailAlloc_2874_;
goto v_reusejp_2872_;
}
v_reusejp_2872_:
{
return v___x_2873_;
}
}
}
}
else
{
lean_object* v_a_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2883_; 
lean_dec_ref(v___x_2810_);
lean_dec_ref(v___y_2804_);
lean_dec(v___y_2802_);
lean_dec_ref(v___y_2801_);
lean_dec(v___y_2800_);
v_a_2876_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2883_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2883_ == 0)
{
v___x_2878_ = v___x_2814_;
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_a_2876_);
lean_dec(v___x_2814_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2883_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
lean_object* v___x_2881_; 
if (v_isShared_2879_ == 0)
{
v___x_2881_ = v___x_2878_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2882_; 
v_reuseFailAlloc_2882_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2882_, 0, v_a_2876_);
v___x_2881_ = v_reuseFailAlloc_2882_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
return v___x_2881_;
}
}
}
}
v___jp_2884_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; 
v___x_2893_ = l_Lean_Expr_fvarId_x21(v___y_2888_);
v___x_2894_ = lean_unsigned_to_nat(1u);
v___x_2895_ = lean_mk_empty_array_with_capacity(v___x_2894_);
lean_inc(v___x_2893_);
v___x_2896_ = lean_array_push(v___x_2895_, v___x_2893_);
v___x_2897_ = l_Lean_MVarId_revert(v_mvarId_2783_, v___x_2896_, v___x_2797_, v___x_2797_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
if (lean_obj_tag(v___x_2897_) == 0)
{
lean_object* v_a_2898_; lean_object* v_fst_2899_; lean_object* v_snd_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2922_; 
v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
lean_inc(v_a_2898_);
lean_dec_ref_known(v___x_2897_, 1);
v_fst_2899_ = lean_ctor_get(v_a_2898_, 0);
v_snd_2900_ = lean_ctor_get(v_a_2898_, 1);
v_isSharedCheck_2922_ = !lean_is_exclusive(v_a_2898_);
if (v_isSharedCheck_2922_ == 0)
{
v___x_2902_ = v_a_2898_;
v_isShared_2903_ = v_isSharedCheck_2922_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_snd_2900_);
lean_inc(v_fst_2899_);
lean_dec(v_a_2898_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2922_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = lean_array_get_size(v_fst_2899_);
lean_dec(v_fst_2899_);
v___x_2905_ = lean_nat_dec_eq(v___x_2904_, v___x_2894_);
if (v___x_2905_ == 0)
{
lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2909_; 
lean_dec(v_snd_2900_);
lean_dec(v___x_2893_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec_ref(v_body_2796_);
v___x_2906_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__3, &l_Lean_Meta_introSubstEq___lam__0___closed__3_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__3);
v___x_2907_ = l_Lean_MessageData_ofExpr(v___y_2888_);
if (v_isShared_2903_ == 0)
{
lean_ctor_set_tag(v___x_2902_, 7);
lean_ctor_set(v___x_2902_, 1, v___x_2907_);
lean_ctor_set(v___x_2902_, 0, v___x_2906_);
v___x_2909_ = v___x_2902_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2921_; 
v_reuseFailAlloc_2921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2921_, 0, v___x_2906_);
lean_ctor_set(v_reuseFailAlloc_2921_, 1, v___x_2907_);
v___x_2909_ = v_reuseFailAlloc_2921_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
v___x_2910_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__5, &l_Lean_Meta_introSubstEq___lam__0___closed__5_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__5);
v___x_2911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2909_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2911_, v___y_2889_, v___y_2890_, v___y_2891_, v___y_2892_);
v_a_2913_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2912_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2912_);
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
else
{
lean_del_object(v___x_2902_);
v___y_2799_ = v___x_2894_;
v___y_2800_ = v___x_2893_;
v___y_2801_ = v___y_2885_;
v___y_2802_ = v_snd_2900_;
v___y_2803_ = v___y_2887_;
v___y_2804_ = v___y_2886_;
v___y_2805_ = v___y_2888_;
v___y_2806_ = v___y_2889_;
v___y_2807_ = v___y_2890_;
v___y_2808_ = v___y_2891_;
v___y_2809_ = v___y_2892_;
goto v___jp_2798_;
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v___x_2893_);
lean_dec_ref(v___y_2888_);
lean_dec_ref(v___y_2886_);
lean_dec_ref(v___y_2885_);
lean_dec_ref(v_body_2796_);
v_a_2923_ = lean_ctor_get(v___x_2897_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2897_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2897_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2897_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
v___jp_2931_:
{
uint8_t v___x_2940_; 
v___x_2940_ = l_Lean_Expr_isFVar(v_fst_2934_);
if (v___x_2940_ == 0)
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_dec_ref(v_fst_2934_);
lean_dec_ref(v_fst_2933_);
lean_dec_ref(v_fst_2932_);
lean_dec_ref(v_body_2796_);
lean_dec(v_mvarId_2783_);
v___x_2941_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__7, &l_Lean_Meta_introSubstEq___lam__0___closed__7_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__7);
v___x_2942_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2941_, v___y_2936_, v___y_2937_, v___y_2938_, v___y_2939_);
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2942_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2942_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2942_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_a_2943_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
else
{
v___y_2885_ = v_fst_2933_;
v___y_2886_ = v_fst_2932_;
v___y_2887_ = v_snd_2935_;
v___y_2888_ = v_fst_2934_;
v___y_2889_ = v___y_2936_;
v___y_2890_ = v___y_2937_;
v___y_2891_ = v___y_2938_;
v___y_2892_ = v___y_2939_;
goto v___jp_2884_;
}
}
}
else
{
lean_dec(v_a_2791_);
lean_dec(v_mvarId_2783_);
goto v___jp_2792_;
}
v___jp_2792_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; 
v___x_2793_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__0___closed__1, &l_Lean_Meta_introSubstEq___lam__0___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__0___closed__1);
v___x_2794_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_2793_, v___y_2785_, v___y_2786_, v___y_2787_, v___y_2788_);
return v___x_2794_;
}
}
else
{
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_dec(v_mvarId_2783_);
v_a_3023_ = lean_ctor_get(v___x_2790_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2790_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2790_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2790_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
if (v_isShared_3026_ == 0)
{
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v_a_3023_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
return v___x_3028_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__0___boxed(lean_object* v_mvarId_3031_, lean_object* v_substLHS_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
uint8_t v_substLHS_boxed_3038_; lean_object* v_res_3039_; 
v_substLHS_boxed_3038_ = lean_unbox(v_substLHS_3032_);
v_res_3039_ = l_Lean_Meta_introSubstEq___lam__0(v_mvarId_3031_, v_substLHS_boxed_3038_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
lean_dec(v___y_3036_);
lean_dec_ref(v___y_3035_);
lean_dec(v___y_3034_);
lean_dec_ref(v___y_3033_);
return v_res_3039_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(lean_object* v_keys_3040_, lean_object* v_i_3041_, lean_object* v_k_3042_){
_start:
{
lean_object* v___x_3043_; uint8_t v___x_3044_; 
v___x_3043_ = lean_array_get_size(v_keys_3040_);
v___x_3044_ = lean_nat_dec_lt(v_i_3041_, v___x_3043_);
if (v___x_3044_ == 0)
{
lean_dec(v_i_3041_);
return v___x_3044_;
}
else
{
lean_object* v_k_x27_3045_; uint8_t v___x_3046_; 
v_k_x27_3045_ = lean_array_fget_borrowed(v_keys_3040_, v_i_3041_);
v___x_3046_ = l_Lean_instBEqMVarId_beq(v_k_3042_, v_k_x27_3045_);
if (v___x_3046_ == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; 
v___x_3047_ = lean_unsigned_to_nat(1u);
v___x_3048_ = lean_nat_add(v_i_3041_, v___x_3047_);
lean_dec(v_i_3041_);
v_i_3041_ = v___x_3048_;
goto _start;
}
else
{
lean_dec(v_i_3041_);
return v___x_3046_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg___boxed(lean_object* v_keys_3050_, lean_object* v_i_3051_, lean_object* v_k_3052_){
_start:
{
uint8_t v_res_3053_; lean_object* v_r_3054_; 
v_res_3053_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3050_, v_i_3051_, v_k_3052_);
lean_dec(v_k_3052_);
lean_dec_ref(v_keys_3050_);
v_r_3054_ = lean_box(v_res_3053_);
return v_r_3054_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(lean_object* v_x_3055_, size_t v_x_3056_, lean_object* v_x_3057_){
_start:
{
if (lean_obj_tag(v_x_3055_) == 0)
{
lean_object* v_es_3058_; lean_object* v___x_3059_; size_t v___x_3060_; size_t v___x_3061_; lean_object* v_j_3062_; lean_object* v___x_3063_; 
v_es_3058_ = lean_ctor_get(v_x_3055_, 0);
v___x_3059_ = lean_box(2);
v___x_3060_ = ((size_t)31ULL);
v___x_3061_ = lean_usize_land(v_x_3056_, v___x_3060_);
v_j_3062_ = lean_usize_to_nat(v___x_3061_);
v___x_3063_ = lean_array_get_borrowed(v___x_3059_, v_es_3058_, v_j_3062_);
lean_dec(v_j_3062_);
switch(lean_obj_tag(v___x_3063_))
{
case 0:
{
lean_object* v_key_3064_; uint8_t v___x_3065_; 
v_key_3064_ = lean_ctor_get(v___x_3063_, 0);
v___x_3065_ = l_Lean_instBEqMVarId_beq(v_x_3057_, v_key_3064_);
return v___x_3065_;
}
case 1:
{
lean_object* v_node_3066_; size_t v___x_3067_; size_t v___x_3068_; 
v_node_3066_ = lean_ctor_get(v___x_3063_, 0);
v___x_3067_ = ((size_t)5ULL);
v___x_3068_ = lean_usize_shift_right(v_x_3056_, v___x_3067_);
v_x_3055_ = v_node_3066_;
v_x_3056_ = v___x_3068_;
goto _start;
}
default: 
{
uint8_t v___x_3070_; 
v___x_3070_ = 0;
return v___x_3070_;
}
}
}
else
{
lean_object* v_ks_3071_; lean_object* v___x_3072_; uint8_t v___x_3073_; 
v_ks_3071_ = lean_ctor_get(v_x_3055_, 0);
v___x_3072_ = lean_unsigned_to_nat(0u);
v___x_3073_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_ks_3071_, v___x_3072_, v_x_3057_);
return v___x_3073_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg___boxed(lean_object* v_x_3074_, lean_object* v_x_3075_, lean_object* v_x_3076_){
_start:
{
size_t v_x_12601__boxed_3077_; uint8_t v_res_3078_; lean_object* v_r_3079_; 
v_x_12601__boxed_3077_ = lean_unbox_usize(v_x_3075_);
lean_dec(v_x_3075_);
v_res_3078_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3074_, v_x_12601__boxed_3077_, v_x_3076_);
lean_dec(v_x_3076_);
lean_dec_ref(v_x_3074_);
v_r_3079_ = lean_box(v_res_3078_);
return v_r_3079_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(lean_object* v_x_3080_, lean_object* v_x_3081_){
_start:
{
uint64_t v___x_3082_; size_t v___x_3083_; uint8_t v___x_3084_; 
v___x_3082_ = l_Lean_instHashableMVarId_hash(v_x_3081_);
v___x_3083_ = lean_uint64_to_usize(v___x_3082_);
v___x_3084_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3080_, v___x_3083_, v_x_3081_);
return v___x_3084_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg___boxed(lean_object* v_x_3085_, lean_object* v_x_3086_){
_start:
{
uint8_t v_res_3087_; lean_object* v_r_3088_; 
v_res_3087_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3085_, v_x_3086_);
lean_dec(v_x_3086_);
lean_dec_ref(v_x_3085_);
v_r_3088_ = lean_box(v_res_3087_);
return v_r_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(lean_object* v_mvarId_3089_, lean_object* v___y_3090_){
_start:
{
lean_object* v___x_3092_; lean_object* v_mctx_3093_; lean_object* v_eAssignment_3094_; uint8_t v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3097_; 
v___x_3092_ = lean_st_ref_get(v___y_3090_);
v_mctx_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc_ref(v_mctx_3093_);
lean_dec(v___x_3092_);
v_eAssignment_3094_ = lean_ctor_get(v_mctx_3093_, 8);
lean_inc_ref(v_eAssignment_3094_);
lean_dec_ref(v_mctx_3093_);
v___x_3095_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_eAssignment_3094_, v_mvarId_3089_);
lean_dec_ref(v_eAssignment_3094_);
v___x_3096_ = lean_box(v___x_3095_);
v___x_3097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3097_, 0, v___x_3096_);
return v___x_3097_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg___boxed(lean_object* v_mvarId_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3098_, v___y_3099_);
lean_dec(v___y_3099_);
lean_dec(v_mvarId_3098_);
return v_res_3101_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___lam__1___closed__1(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = ((lean_object*)(l_Lean_Meta_introSubstEq___lam__1___closed__0));
v___x_3104_ = l_Lean_stringToMessageData(v___x_3103_);
return v___x_3104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1(lean_object* v_mvarId_3105_, uint8_t v___y_3106_, lean_object* v_____r_3107_, lean_object* v___y_3108_, lean_object* v___y_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_){
_start:
{
lean_object* v___y_3114_; lean_object* v___y_3115_; lean_object* v___y_3116_; lean_object* v___y_3117_; lean_object* v___x_3149_; lean_object* v_a_3150_; uint8_t v___x_3151_; 
v___x_3149_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3105_, v___y_3109_);
v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
lean_inc(v_a_3150_);
lean_dec_ref(v___x_3149_);
v___x_3151_ = lean_unbox(v_a_3150_);
lean_dec(v_a_3150_);
if (v___x_3151_ == 0)
{
v___y_3114_ = v___y_3108_;
v___y_3115_ = v___y_3109_;
v___y_3116_ = v___y_3110_;
v___y_3117_ = v___y_3111_;
goto v___jp_3113_;
}
else
{
lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v_a_3154_; lean_object* v___x_3156_; uint8_t v_isShared_3157_; uint8_t v_isSharedCheck_3161_; 
lean_dec(v_mvarId_3105_);
v___x_3152_ = lean_obj_once(&l_Lean_Meta_introSubstEq___lam__1___closed__1, &l_Lean_Meta_introSubstEq___lam__1___closed__1_once, _init_l_Lean_Meta_introSubstEq___lam__1___closed__1);
v___x_3153_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v___x_3152_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
v_isSharedCheck_3161_ = !lean_is_exclusive(v___x_3153_);
if (v_isSharedCheck_3161_ == 0)
{
v___x_3156_ = v___x_3153_;
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
else
{
lean_inc(v_a_3154_);
lean_dec(v___x_3153_);
v___x_3156_ = lean_box(0);
v_isShared_3157_ = v_isSharedCheck_3161_;
goto v_resetjp_3155_;
}
v_resetjp_3155_:
{
lean_object* v___x_3159_; 
if (v_isShared_3157_ == 0)
{
v___x_3159_ = v___x_3156_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3160_; 
v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
v___x_3159_ = v_reuseFailAlloc_3160_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
return v___x_3159_;
}
}
}
v___jp_3113_:
{
lean_object* v___x_3118_; 
v___x_3118_ = l_Lean_Meta_intro1Core(v_mvarId_3105_, v___y_3106_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3118_) == 0)
{
lean_object* v_a_3119_; lean_object* v_fst_3120_; lean_object* v_snd_3121_; lean_object* v___x_3122_; lean_object* v___x_3123_; 
v_a_3119_ = lean_ctor_get(v___x_3118_, 0);
lean_inc(v_a_3119_);
lean_dec_ref_known(v___x_3118_, 1);
v_fst_3120_ = lean_ctor_get(v_a_3119_, 0);
lean_inc(v_fst_3120_);
v_snd_3121_ = lean_ctor_get(v_a_3119_, 1);
lean_inc(v_snd_3121_);
lean_dec(v_a_3119_);
v___x_3122_ = lean_box(0);
v___x_3123_ = l_Lean_Meta_substEq(v_snd_3121_, v_fst_3120_, v___x_3122_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_);
if (lean_obj_tag(v___x_3123_) == 0)
{
lean_object* v_a_3124_; lean_object* v___x_3126_; uint8_t v_isShared_3127_; uint8_t v_isSharedCheck_3132_; 
v_a_3124_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3132_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3132_ == 0)
{
v___x_3126_ = v___x_3123_;
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
else
{
lean_inc(v_a_3124_);
lean_dec(v___x_3123_);
v___x_3126_ = lean_box(0);
v_isShared_3127_ = v_isSharedCheck_3132_;
goto v_resetjp_3125_;
}
v_resetjp_3125_:
{
lean_object* v___x_3128_; lean_object* v___x_3130_; 
v___x_3128_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3128_, 0, v_a_3124_);
if (v_isShared_3127_ == 0)
{
lean_ctor_set(v___x_3126_, 0, v___x_3128_);
v___x_3130_ = v___x_3126_;
goto v_reusejp_3129_;
}
else
{
lean_object* v_reuseFailAlloc_3131_; 
v_reuseFailAlloc_3131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3131_, 0, v___x_3128_);
v___x_3130_ = v_reuseFailAlloc_3131_;
goto v_reusejp_3129_;
}
v_reusejp_3129_:
{
return v___x_3130_;
}
}
}
else
{
lean_object* v_a_3133_; lean_object* v___x_3135_; uint8_t v_isShared_3136_; uint8_t v_isSharedCheck_3140_; 
v_a_3133_ = lean_ctor_get(v___x_3123_, 0);
v_isSharedCheck_3140_ = !lean_is_exclusive(v___x_3123_);
if (v_isSharedCheck_3140_ == 0)
{
v___x_3135_ = v___x_3123_;
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
else
{
lean_inc(v_a_3133_);
lean_dec(v___x_3123_);
v___x_3135_ = lean_box(0);
v_isShared_3136_ = v_isSharedCheck_3140_;
goto v_resetjp_3134_;
}
v_resetjp_3134_:
{
lean_object* v___x_3138_; 
if (v_isShared_3136_ == 0)
{
v___x_3138_ = v___x_3135_;
goto v_reusejp_3137_;
}
else
{
lean_object* v_reuseFailAlloc_3139_; 
v_reuseFailAlloc_3139_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3139_, 0, v_a_3133_);
v___x_3138_ = v_reuseFailAlloc_3139_;
goto v_reusejp_3137_;
}
v_reusejp_3137_:
{
return v___x_3138_;
}
}
}
}
else
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_a_3141_ = lean_ctor_get(v___x_3118_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3118_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3118_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3118_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___lam__1___boxed(lean_object* v_mvarId_3162_, lean_object* v___y_3163_, lean_object* v_____r_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_, lean_object* v___y_3167_, lean_object* v___y_3168_, lean_object* v___y_3169_){
_start:
{
uint8_t v___y_12673__boxed_3170_; lean_object* v_res_3171_; 
v___y_12673__boxed_3170_ = lean_unbox(v___y_3163_);
v_res_3171_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3162_, v___y_12673__boxed_3170_, v_____r_3164_, v___y_3165_, v___y_3166_, v___y_3167_, v___y_3168_);
lean_dec(v___y_3168_);
lean_dec_ref(v___y_3167_);
lean_dec(v___y_3166_);
lean_dec_ref(v___y_3165_);
return v_res_3171_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__2(void){
_start:
{
lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___x_3175_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3176_ = ((lean_object*)(l_Lean_Meta_substCore___lam__0___closed__1));
v___x_3177_ = l_Lean_Name_append(v___x_3176_, v___x_3175_);
return v___x_3177_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__4(void){
_start:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; 
v___x_3179_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__3));
v___x_3180_ = l_Lean_stringToMessageData(v___x_3179_);
return v___x_3180_;
}
}
static lean_object* _init_l_Lean_Meta_introSubstEq___closed__6(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__5));
v___x_3183_ = l_Lean_stringToMessageData(v___x_3182_);
return v___x_3183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq(lean_object* v_mvarId_3184_, uint8_t v_substLHS_3185_, lean_object* v_a_3186_, lean_object* v_a_3187_, lean_object* v_a_3188_, lean_object* v_a_3189_){
_start:
{
lean_object* v___y_3192_; lean_object* v___x_3210_; lean_object* v___x_3211_; 
v___x_3210_ = ((lean_object*)(l_Lean_Meta_introSubstEq___closed__1));
lean_inc(v_mvarId_3184_);
v___x_3211_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_3184_, v___x_3210_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3211_) == 0)
{
lean_object* v___x_3212_; lean_object* v___f_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
lean_dec_ref_known(v___x_3211_, 1);
v___x_3212_ = lean_box(v_substLHS_3185_);
lean_inc_n(v_mvarId_3184_, 2);
v___f_3213_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__0___boxed), 7, 2);
lean_closure_set(v___f_3213_, 0, v_mvarId_3184_);
lean_closure_set(v___f_3213_, 1, v___x_3212_);
v___x_3214_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___boxed), 8, 3);
lean_closure_set(v___x_3214_, 0, lean_box(0));
lean_closure_set(v___x_3214_, 1, v_mvarId_3184_);
lean_closure_set(v___x_3214_, 2, v___f_3213_);
v___x_3215_ = l_Lean_commitIfNoEx___at___00Lean_Meta_introSubstEq_spec__1___redArg(v___x_3214_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_dec(v_mvarId_3184_);
return v___x_3215_;
}
else
{
lean_object* v_a_3216_; lean_object* v___y_3218_; uint8_t v___y_3222_; uint8_t v___x_3256_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
v___x_3256_ = l_Lean_Exception_isInterrupt(v_a_3216_);
if (v___x_3256_ == 0)
{
uint8_t v___x_3257_; 
lean_inc(v_a_3216_);
v___x_3257_ = l_Lean_Exception_isRuntime(v_a_3216_);
v___y_3222_ = v___x_3257_;
goto v___jp_3221_;
}
else
{
v___y_3222_ = v___x_3256_;
goto v___jp_3221_;
}
v___jp_3217_:
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_box(0);
lean_inc(v_a_3189_);
lean_inc_ref(v_a_3188_);
lean_inc(v_a_3187_);
lean_inc_ref(v_a_3186_);
v___x_3220_ = lean_apply_6(v___y_3218_, v___x_3219_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, lean_box(0));
v___y_3192_ = v___x_3220_;
goto v___jp_3191_;
}
v___jp_3221_:
{
if (v___y_3222_ == 0)
{
lean_object* v___x_3224_; uint8_t v_isShared_3225_; uint8_t v_isSharedCheck_3254_; 
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3254_ == 0)
{
lean_object* v_unused_3255_; 
v_unused_3255_ = lean_ctor_get(v___x_3215_, 0);
lean_dec(v_unused_3255_);
v___x_3224_ = v___x_3215_;
v_isShared_3225_ = v_isSharedCheck_3254_;
goto v_resetjp_3223_;
}
else
{
lean_dec(v___x_3215_);
v___x_3224_ = lean_box(0);
v_isShared_3225_ = v_isSharedCheck_3254_;
goto v_resetjp_3223_;
}
v_resetjp_3223_:
{
lean_object* v_options_3226_; lean_object* v_inheritedTraceOptions_3227_; uint8_t v_hasTrace_3228_; lean_object* v___x_3229_; lean_object* v___f_3230_; 
v_options_3226_ = lean_ctor_get(v_a_3188_, 2);
v_inheritedTraceOptions_3227_ = lean_ctor_get(v_a_3188_, 13);
v_hasTrace_3228_ = lean_ctor_get_uint8(v_options_3226_, sizeof(void*)*1);
v___x_3229_ = lean_box(v___y_3222_);
lean_inc(v_mvarId_3184_);
v___f_3230_ = lean_alloc_closure((void*)(l_Lean_Meta_introSubstEq___lam__1___boxed), 8, 2);
lean_closure_set(v___f_3230_, 0, v_mvarId_3184_);
lean_closure_set(v___f_3230_, 1, v___x_3229_);
if (v_hasTrace_3228_ == 0)
{
lean_del_object(v___x_3224_);
lean_dec(v_a_3216_);
lean_dec(v_mvarId_3184_);
v___y_3218_ = v___f_3230_;
goto v___jp_3217_;
}
else
{
lean_object* v___x_3231_; lean_object* v___x_3232_; uint8_t v___x_3233_; 
v___x_3231_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_3232_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__2, &l_Lean_Meta_introSubstEq___closed__2_once, _init_l_Lean_Meta_introSubstEq___closed__2);
v___x_3233_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3227_, v_options_3226_, v___x_3232_);
if (v___x_3233_ == 0)
{
lean_del_object(v___x_3224_);
lean_dec(v_a_3216_);
lean_dec(v_mvarId_3184_);
v___y_3218_ = v___f_3230_;
goto v___jp_3217_;
}
else
{
lean_object* v___x_3234_; lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; 
lean_dec_ref(v___f_3230_);
v___x_3234_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__4, &l_Lean_Meta_introSubstEq___closed__4_once, _init_l_Lean_Meta_introSubstEq___closed__4);
v___x_3235_ = l_Lean_Exception_toMessageData(v_a_3216_);
v___x_3236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3236_, 0, v___x_3234_);
lean_ctor_set(v___x_3236_, 1, v___x_3235_);
v___x_3237_ = lean_obj_once(&l_Lean_Meta_introSubstEq___closed__6, &l_Lean_Meta_introSubstEq___closed__6_once, _init_l_Lean_Meta_introSubstEq___closed__6);
v___x_3238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3238_, 0, v___x_3236_);
lean_ctor_set(v___x_3238_, 1, v___x_3237_);
lean_inc(v_mvarId_3184_);
if (v_isShared_3225_ == 0)
{
lean_ctor_set(v___x_3224_, 0, v_mvarId_3184_);
v___x_3240_ = v___x_3224_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_mvarId_3184_);
v___x_3240_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
lean_object* v___x_3241_; lean_object* v___x_3242_; 
v___x_3241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3238_);
lean_ctor_set(v___x_3241_, 1, v___x_3240_);
v___x_3242_ = l_Lean_addTrace___at___00Lean_Meta_substCore_spec__3(v___x_3231_, v___x_3241_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; lean_object* v___x_3244_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3242_, 1);
v___x_3244_ = l_Lean_Meta_introSubstEq___lam__1(v_mvarId_3184_, v___y_3222_, v_a_3243_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_);
v___y_3192_ = v___x_3244_;
goto v___jp_3191_;
}
else
{
lean_object* v_a_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3252_; 
lean_dec(v_mvarId_3184_);
v_a_3245_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3247_ = v___x_3242_;
v_isShared_3248_ = v_isSharedCheck_3252_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_a_3245_);
lean_dec(v___x_3242_);
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
}
}
}
}
}
else
{
lean_dec(v_a_3216_);
lean_dec(v_mvarId_3184_);
return v___x_3215_;
}
}
}
}
else
{
lean_object* v_a_3258_; lean_object* v___x_3260_; uint8_t v_isShared_3261_; uint8_t v_isSharedCheck_3265_; 
lean_dec(v_mvarId_3184_);
v_a_3258_ = lean_ctor_get(v___x_3211_, 0);
v_isSharedCheck_3265_ = !lean_is_exclusive(v___x_3211_);
if (v_isSharedCheck_3265_ == 0)
{
v___x_3260_ = v___x_3211_;
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
else
{
lean_inc(v_a_3258_);
lean_dec(v___x_3211_);
v___x_3260_ = lean_box(0);
v_isShared_3261_ = v_isSharedCheck_3265_;
goto v_resetjp_3259_;
}
v_resetjp_3259_:
{
lean_object* v___x_3263_; 
if (v_isShared_3261_ == 0)
{
v___x_3263_ = v___x_3260_;
goto v_reusejp_3262_;
}
else
{
lean_object* v_reuseFailAlloc_3264_; 
v_reuseFailAlloc_3264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3264_, 0, v_a_3258_);
v___x_3263_ = v_reuseFailAlloc_3264_;
goto v_reusejp_3262_;
}
v_reusejp_3262_:
{
return v___x_3263_;
}
}
}
v___jp_3191_:
{
if (lean_obj_tag(v___y_3192_) == 0)
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3201_; 
v_a_3193_ = lean_ctor_get(v___y_3192_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___y_3192_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3195_ = v___y_3192_;
v_isShared_3196_ = v_isSharedCheck_3201_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___y_3192_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3201_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v_a_3197_; lean_object* v___x_3199_; 
v_a_3197_ = lean_ctor_get(v_a_3193_, 0);
lean_inc(v_a_3197_);
lean_dec(v_a_3193_);
if (v_isShared_3196_ == 0)
{
lean_ctor_set(v___x_3195_, 0, v_a_3197_);
v___x_3199_ = v___x_3195_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3197_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
v_a_3202_ = lean_ctor_get(v___y_3192_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___y_3192_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___y_3192_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___y_3192_);
v___x_3204_ = lean_box(0);
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
v_resetjp_3203_:
{
lean_object* v___x_3207_; 
if (v_isShared_3205_ == 0)
{
v___x_3207_ = v___x_3204_;
goto v_reusejp_3206_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v_a_3202_);
v___x_3207_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3206_;
}
v_reusejp_3206_:
{
return v___x_3207_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_introSubstEq___boxed(lean_object* v_mvarId_3266_, lean_object* v_substLHS_3267_, lean_object* v_a_3268_, lean_object* v_a_3269_, lean_object* v_a_3270_, lean_object* v_a_3271_, lean_object* v_a_3272_){
_start:
{
uint8_t v_substLHS_boxed_3273_; lean_object* v_res_3274_; 
v_substLHS_boxed_3273_ = lean_unbox(v_substLHS_3267_);
v_res_3274_ = l_Lean_Meta_introSubstEq(v_mvarId_3266_, v_substLHS_boxed_3273_, v_a_3268_, v_a_3269_, v_a_3270_, v_a_3271_);
lean_dec(v_a_3271_);
lean_dec_ref(v_a_3270_);
lean_dec(v_a_3269_);
lean_dec_ref(v_a_3268_);
return v_res_3274_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(lean_object* v_00_u03b1_3275_, lean_object* v_msg_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_, lean_object* v___y_3280_){
_start:
{
lean_object* v___x_3282_; 
v___x_3282_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___redArg(v_msg_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_);
return v___x_3282_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0___boxed(lean_object* v_00_u03b1_3283_, lean_object* v_msg_3284_, lean_object* v___y_3285_, lean_object* v___y_3286_, lean_object* v___y_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_){
_start:
{
lean_object* v_res_3290_; 
v_res_3290_ = l_Lean_throwError___at___00Lean_Meta_introSubstEq_spec__0(v_00_u03b1_3283_, v_msg_3284_, v___y_3285_, v___y_3286_, v___y_3287_, v___y_3288_);
lean_dec(v___y_3288_);
lean_dec_ref(v___y_3287_);
lean_dec(v___y_3286_);
lean_dec_ref(v___y_3285_);
return v_res_3290_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(lean_object* v_mvarId_3291_, lean_object* v___y_3292_, lean_object* v___y_3293_, lean_object* v___y_3294_, lean_object* v___y_3295_){
_start:
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___redArg(v_mvarId_3291_, v___y_3293_);
return v___x_3297_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2___boxed(lean_object* v_mvarId_3298_, lean_object* v___y_3299_, lean_object* v___y_3300_, lean_object* v___y_3301_, lean_object* v___y_3302_, lean_object* v___y_3303_){
_start:
{
lean_object* v_res_3304_; 
v_res_3304_ = l_Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2(v_mvarId_3298_, v___y_3299_, v___y_3300_, v___y_3301_, v___y_3302_);
lean_dec(v___y_3302_);
lean_dec_ref(v___y_3301_);
lean_dec(v___y_3300_);
lean_dec_ref(v___y_3299_);
lean_dec(v_mvarId_3298_);
return v_res_3304_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(lean_object* v_00_u03b2_3305_, lean_object* v_x_3306_, lean_object* v_x_3307_){
_start:
{
uint8_t v___x_3308_; 
v___x_3308_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___redArg(v_x_3306_, v_x_3307_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2___boxed(lean_object* v_00_u03b2_3309_, lean_object* v_x_3310_, lean_object* v_x_3311_){
_start:
{
uint8_t v_res_3312_; lean_object* v_r_3313_; 
v_res_3312_ = l_Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2(v_00_u03b2_3309_, v_x_3310_, v_x_3311_);
lean_dec(v_x_3311_);
lean_dec_ref(v_x_3310_);
v_r_3313_ = lean_box(v_res_3312_);
return v_r_3313_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(lean_object* v_00_u03b2_3314_, lean_object* v_x_3315_, size_t v_x_3316_, lean_object* v_x_3317_){
_start:
{
uint8_t v___x_3318_; 
v___x_3318_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___redArg(v_x_3315_, v_x_3316_, v_x_3317_);
return v___x_3318_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3___boxed(lean_object* v_00_u03b2_3319_, lean_object* v_x_3320_, lean_object* v_x_3321_, lean_object* v_x_3322_){
_start:
{
size_t v_x_13037__boxed_3323_; uint8_t v_res_3324_; lean_object* v_r_3325_; 
v_x_13037__boxed_3323_ = lean_unbox_usize(v_x_3321_);
lean_dec(v_x_3321_);
v_res_3324_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3(v_00_u03b2_3319_, v_x_3320_, v_x_13037__boxed_3323_, v_x_3322_);
lean_dec(v_x_3322_);
lean_dec_ref(v_x_3320_);
v_r_3325_ = lean_box(v_res_3324_);
return v_r_3325_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(lean_object* v_00_u03b2_3326_, lean_object* v_keys_3327_, lean_object* v_vals_3328_, lean_object* v_heq_3329_, lean_object* v_i_3330_, lean_object* v_k_3331_){
_start:
{
uint8_t v___x_3332_; 
v___x_3332_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___redArg(v_keys_3327_, v_i_3330_, v_k_3331_);
return v___x_3332_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4___boxed(lean_object* v_00_u03b2_3333_, lean_object* v_keys_3334_, lean_object* v_vals_3335_, lean_object* v_heq_3336_, lean_object* v_i_3337_, lean_object* v_k_3338_){
_start:
{
uint8_t v_res_3339_; lean_object* v_r_3340_; 
v_res_3339_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_MVarId_isAssigned___at___00Lean_Meta_introSubstEq_spec__2_spec__2_spec__3_spec__4(v_00_u03b2_3333_, v_keys_3334_, v_vals_3335_, v_heq_3336_, v_i_3337_, v_k_3338_);
lean_dec(v_k_3338_);
lean_dec_ref(v_vals_3335_);
lean_dec_ref(v_keys_3334_);
v_r_3340_ = lean_box(v_res_3339_);
return v_r_3340_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(lean_object* v_x_3341_, lean_object* v___y_3342_, lean_object* v___y_3343_, lean_object* v___y_3344_, lean_object* v___y_3345_){
_start:
{
lean_object* v___x_3347_; 
v___x_3347_ = l_Lean_Meta_saveState___redArg(v___y_3343_, v___y_3345_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3349_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
lean_inc(v___y_3345_);
lean_inc_ref(v___y_3344_);
lean_inc(v___y_3343_);
lean_inc_ref(v___y_3342_);
v___x_3349_ = lean_apply_5(v_x_3341_, v___y_3342_, v___y_3343_, v___y_3344_, v___y_3345_, lean_box(0));
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3352_; uint8_t v_isShared_3353_; uint8_t v_isSharedCheck_3358_; 
lean_dec(v_a_3348_);
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3358_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3358_ == 0)
{
v___x_3352_ = v___x_3349_;
v_isShared_3353_ = v_isSharedCheck_3358_;
goto v_resetjp_3351_;
}
else
{
lean_inc(v_a_3350_);
lean_dec(v___x_3349_);
v___x_3352_ = lean_box(0);
v_isShared_3353_ = v_isSharedCheck_3358_;
goto v_resetjp_3351_;
}
v_resetjp_3351_:
{
lean_object* v___x_3354_; lean_object* v___x_3356_; 
v___x_3354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3354_, 0, v_a_3350_);
if (v_isShared_3353_ == 0)
{
lean_ctor_set(v___x_3352_, 0, v___x_3354_);
v___x_3356_ = v___x_3352_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3357_; 
v_reuseFailAlloc_3357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3357_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3357_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
return v___x_3356_;
}
}
}
else
{
lean_object* v_a_3359_; lean_object* v___x_3361_; uint8_t v_isShared_3362_; uint8_t v_isSharedCheck_3388_; 
v_a_3359_ = lean_ctor_get(v___x_3349_, 0);
v_isSharedCheck_3388_ = !lean_is_exclusive(v___x_3349_);
if (v_isSharedCheck_3388_ == 0)
{
v___x_3361_ = v___x_3349_;
v_isShared_3362_ = v_isSharedCheck_3388_;
goto v_resetjp_3360_;
}
else
{
lean_inc(v_a_3359_);
lean_dec(v___x_3349_);
v___x_3361_ = lean_box(0);
v_isShared_3362_ = v_isSharedCheck_3388_;
goto v_resetjp_3360_;
}
v_resetjp_3360_:
{
uint8_t v___y_3364_; uint8_t v___x_3386_; 
v___x_3386_ = l_Lean_Exception_isInterrupt(v_a_3359_);
if (v___x_3386_ == 0)
{
uint8_t v___x_3387_; 
lean_inc(v_a_3359_);
v___x_3387_ = l_Lean_Exception_isRuntime(v_a_3359_);
v___y_3364_ = v___x_3387_;
goto v___jp_3363_;
}
else
{
v___y_3364_ = v___x_3386_;
goto v___jp_3363_;
}
v___jp_3363_:
{
if (v___y_3364_ == 0)
{
lean_object* v___x_3365_; 
lean_del_object(v___x_3361_);
lean_dec(v_a_3359_);
v___x_3365_ = l_Lean_Meta_SavedState_restore___redArg(v_a_3348_, v___y_3343_, v___y_3345_);
lean_dec(v_a_3348_);
if (lean_obj_tag(v___x_3365_) == 0)
{
lean_object* v___x_3367_; uint8_t v_isShared_3368_; uint8_t v_isSharedCheck_3373_; 
v_isSharedCheck_3373_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3373_ == 0)
{
lean_object* v_unused_3374_; 
v_unused_3374_ = lean_ctor_get(v___x_3365_, 0);
lean_dec(v_unused_3374_);
v___x_3367_ = v___x_3365_;
v_isShared_3368_ = v_isSharedCheck_3373_;
goto v_resetjp_3366_;
}
else
{
lean_dec(v___x_3365_);
v___x_3367_ = lean_box(0);
v_isShared_3368_ = v_isSharedCheck_3373_;
goto v_resetjp_3366_;
}
v_resetjp_3366_:
{
lean_object* v___x_3369_; lean_object* v___x_3371_; 
v___x_3369_ = lean_box(0);
if (v_isShared_3368_ == 0)
{
lean_ctor_set(v___x_3367_, 0, v___x_3369_);
v___x_3371_ = v___x_3367_;
goto v_reusejp_3370_;
}
else
{
lean_object* v_reuseFailAlloc_3372_; 
v_reuseFailAlloc_3372_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
v___x_3371_ = v_reuseFailAlloc_3372_;
goto v_reusejp_3370_;
}
v_reusejp_3370_:
{
return v___x_3371_;
}
}
}
else
{
lean_object* v_a_3375_; lean_object* v___x_3377_; uint8_t v_isShared_3378_; uint8_t v_isSharedCheck_3382_; 
v_a_3375_ = lean_ctor_get(v___x_3365_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3365_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3377_ = v___x_3365_;
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
else
{
lean_inc(v_a_3375_);
lean_dec(v___x_3365_);
v___x_3377_ = lean_box(0);
v_isShared_3378_ = v_isSharedCheck_3382_;
goto v_resetjp_3376_;
}
v_resetjp_3376_:
{
lean_object* v___x_3380_; 
if (v_isShared_3378_ == 0)
{
v___x_3380_ = v___x_3377_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
return v___x_3380_;
}
}
}
}
else
{
lean_object* v___x_3384_; 
lean_dec(v_a_3348_);
if (v_isShared_3362_ == 0)
{
v___x_3384_ = v___x_3361_;
goto v_reusejp_3383_;
}
else
{
lean_object* v_reuseFailAlloc_3385_; 
v_reuseFailAlloc_3385_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3385_, 0, v_a_3359_);
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
}
}
else
{
lean_object* v_a_3389_; lean_object* v___x_3391_; uint8_t v_isShared_3392_; uint8_t v_isSharedCheck_3396_; 
lean_dec_ref(v_x_3341_);
v_a_3389_ = lean_ctor_get(v___x_3347_, 0);
v_isSharedCheck_3396_ = !lean_is_exclusive(v___x_3347_);
if (v_isSharedCheck_3396_ == 0)
{
v___x_3391_ = v___x_3347_;
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
else
{
lean_inc(v_a_3389_);
lean_dec(v___x_3347_);
v___x_3391_ = lean_box(0);
v_isShared_3392_ = v_isSharedCheck_3396_;
goto v_resetjp_3390_;
}
v_resetjp_3390_:
{
lean_object* v___x_3394_; 
if (v_isShared_3392_ == 0)
{
v___x_3394_ = v___x_3391_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v_a_3389_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
return v___x_3394_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg___boxed(lean_object* v_x_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
lean_dec(v___y_3401_);
lean_dec_ref(v___y_3400_);
lean_dec(v___y_3399_);
lean_dec_ref(v___y_3398_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(lean_object* v_00_u03b1_3404_, lean_object* v_x_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_){
_start:
{
lean_object* v___x_3411_; 
v___x_3411_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v_x_3405_, v___y_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
return v___x_3411_;
}
}
LEAN_EXPORT lean_object* l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___boxed(lean_object* v_00_u03b1_3412_, lean_object* v_x_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_, lean_object* v___y_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0(v_00_u03b1_3412_, v_x_3413_, v___y_3414_, v___y_3415_, v___y_3416_, v___y_3417_);
lean_dec(v___y_3417_);
lean_dec_ref(v___y_3416_);
lean_dec(v___y_3415_);
lean_dec_ref(v___y_3414_);
return v_res_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f(lean_object* v_mvarId_3420_, lean_object* v_hFVarId_3421_, lean_object* v_a_3422_, lean_object* v_a_3423_, lean_object* v_a_3424_, lean_object* v_a_3425_){
_start:
{
lean_object* v___x_3427_; lean_object* v___x_3428_; 
v___x_3427_ = lean_alloc_closure((void*)(l_Lean_Meta_substVar___boxed), 7, 2);
lean_closure_set(v___x_3427_, 0, v_mvarId_3420_);
lean_closure_set(v___x_3427_, 1, v_hFVarId_3421_);
v___x_3428_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3427_, v_a_3422_, v_a_3423_, v_a_3424_, v_a_3425_);
return v___x_3428_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVar_x3f___boxed(lean_object* v_mvarId_3429_, lean_object* v_hFVarId_3430_, lean_object* v_a_3431_, lean_object* v_a_3432_, lean_object* v_a_3433_, lean_object* v_a_3434_, lean_object* v_a_3435_){
_start:
{
lean_object* v_res_3436_; 
v_res_3436_ = l_Lean_Meta_substVar_x3f(v_mvarId_3429_, v_hFVarId_3430_, v_a_3431_, v_a_3432_, v_a_3433_, v_a_3434_);
lean_dec(v_a_3434_);
lean_dec_ref(v_a_3433_);
lean_dec(v_a_3432_);
lean_dec_ref(v_a_3431_);
return v_res_3436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f(lean_object* v_mvarId_3437_, lean_object* v_hFVarId_3438_, lean_object* v_a_3439_, lean_object* v_a_3440_, lean_object* v_a_3441_, lean_object* v_a_3442_){
_start:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; 
v___x_3444_ = lean_alloc_closure((void*)(l_Lean_Meta_subst___boxed), 7, 2);
lean_closure_set(v___x_3444_, 0, v_mvarId_3437_);
lean_closure_set(v___x_3444_, 1, v_hFVarId_3438_);
v___x_3445_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3444_, v_a_3439_, v_a_3440_, v_a_3441_, v_a_3442_);
return v___x_3445_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_subst_x3f___boxed(lean_object* v_mvarId_3446_, lean_object* v_hFVarId_3447_, lean_object* v_a_3448_, lean_object* v_a_3449_, lean_object* v_a_3450_, lean_object* v_a_3451_, lean_object* v_a_3452_){
_start:
{
lean_object* v_res_3453_; 
v_res_3453_ = l_Lean_Meta_subst_x3f(v_mvarId_3446_, v_hFVarId_3447_, v_a_3448_, v_a_3449_, v_a_3450_, v_a_3451_);
lean_dec(v_a_3451_);
lean_dec_ref(v_a_3450_);
lean_dec(v_a_3449_);
lean_dec_ref(v_a_3448_);
return v_res_3453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f(lean_object* v_mvarId_3454_, lean_object* v_hFVarId_3455_, uint8_t v_symm_3456_, lean_object* v_fvarSubst_3457_, uint8_t v_clearH_3458_, uint8_t v_tryToSkip_3459_, lean_object* v_a_3460_, lean_object* v_a_3461_, lean_object* v_a_3462_, lean_object* v_a_3463_){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; lean_object* v___x_3468_; lean_object* v___x_3469_; 
v___x_3465_ = lean_box(v_symm_3456_);
v___x_3466_ = lean_box(v_clearH_3458_);
v___x_3467_ = lean_box(v_tryToSkip_3459_);
v___x_3468_ = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(v___x_3468_, 0, v_mvarId_3454_);
lean_closure_set(v___x_3468_, 1, v_hFVarId_3455_);
lean_closure_set(v___x_3468_, 2, v___x_3465_);
lean_closure_set(v___x_3468_, 3, v_fvarSubst_3457_);
lean_closure_set(v___x_3468_, 4, v___x_3466_);
lean_closure_set(v___x_3468_, 5, v___x_3467_);
v___x_3469_ = l_Lean_observing_x3f___at___00Lean_Meta_substVar_x3f_spec__0___redArg(v___x_3468_, v_a_3460_, v_a_3461_, v_a_3462_, v_a_3463_);
return v___x_3469_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substCore_x3f___boxed(lean_object* v_mvarId_3470_, lean_object* v_hFVarId_3471_, lean_object* v_symm_3472_, lean_object* v_fvarSubst_3473_, lean_object* v_clearH_3474_, lean_object* v_tryToSkip_3475_, lean_object* v_a_3476_, lean_object* v_a_3477_, lean_object* v_a_3478_, lean_object* v_a_3479_, lean_object* v_a_3480_){
_start:
{
uint8_t v_symm_boxed_3481_; uint8_t v_clearH_boxed_3482_; uint8_t v_tryToSkip_boxed_3483_; lean_object* v_res_3484_; 
v_symm_boxed_3481_ = lean_unbox(v_symm_3472_);
v_clearH_boxed_3482_ = lean_unbox(v_clearH_3474_);
v_tryToSkip_boxed_3483_ = lean_unbox(v_tryToSkip_3475_);
v_res_3484_ = l_Lean_Meta_substCore_x3f(v_mvarId_3470_, v_hFVarId_3471_, v_symm_boxed_3481_, v_fvarSubst_3473_, v_clearH_boxed_3482_, v_tryToSkip_boxed_3483_, v_a_3476_, v_a_3477_, v_a_3478_, v_a_3479_);
lean_dec(v_a_3479_);
lean_dec_ref(v_a_3478_);
lean_dec(v_a_3477_);
lean_dec_ref(v_a_3476_);
return v_res_3484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar(lean_object* v_mvarId_3485_, lean_object* v_hFVarId_3486_, lean_object* v_a_3487_, lean_object* v_a_3488_, lean_object* v_a_3489_, lean_object* v_a_3490_){
_start:
{
lean_object* v___x_3492_; 
lean_inc(v_mvarId_3485_);
v___x_3492_ = l_Lean_Meta_substVar_x3f(v_mvarId_3485_, v_hFVarId_3486_, v_a_3487_, v_a_3488_, v_a_3489_, v_a_3490_);
if (lean_obj_tag(v___x_3492_) == 0)
{
lean_object* v_a_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3504_; 
v_a_3493_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3495_ = v___x_3492_;
v_isShared_3496_ = v_isSharedCheck_3504_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_a_3493_);
lean_dec(v___x_3492_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3504_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
if (lean_obj_tag(v_a_3493_) == 0)
{
lean_object* v___x_3498_; 
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v_mvarId_3485_);
v___x_3498_ = v___x_3495_;
goto v_reusejp_3497_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_mvarId_3485_);
v___x_3498_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3497_;
}
v_reusejp_3497_:
{
return v___x_3498_;
}
}
else
{
lean_object* v_val_3500_; lean_object* v___x_3502_; 
lean_dec(v_mvarId_3485_);
v_val_3500_ = lean_ctor_get(v_a_3493_, 0);
lean_inc(v_val_3500_);
lean_dec_ref_known(v_a_3493_, 1);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 0, v_val_3500_);
v___x_3502_ = v___x_3495_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_val_3500_);
v___x_3502_ = v_reuseFailAlloc_3503_;
goto v_reusejp_3501_;
}
v_reusejp_3501_:
{
return v___x_3502_;
}
}
}
}
else
{
lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_mvarId_3485_);
v_a_3505_ = lean_ctor_get(v___x_3492_, 0);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3492_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3492_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_dec(v___x_3492_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubstVar___boxed(lean_object* v_mvarId_3513_, lean_object* v_hFVarId_3514_, lean_object* v_a_3515_, lean_object* v_a_3516_, lean_object* v_a_3517_, lean_object* v_a_3518_, lean_object* v_a_3519_){
_start:
{
lean_object* v_res_3520_; 
v_res_3520_ = l_Lean_Meta_trySubstVar(v_mvarId_3513_, v_hFVarId_3514_, v_a_3515_, v_a_3516_, v_a_3517_, v_a_3518_);
lean_dec(v_a_3518_);
lean_dec_ref(v_a_3517_);
lean_dec(v_a_3516_);
lean_dec_ref(v_a_3515_);
return v_res_3520_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst(lean_object* v_mvarId_3521_, lean_object* v_hFVarId_3522_, lean_object* v_a_3523_, lean_object* v_a_3524_, lean_object* v_a_3525_, lean_object* v_a_3526_){
_start:
{
lean_object* v___x_3528_; 
lean_inc(v_mvarId_3521_);
v___x_3528_ = l_Lean_Meta_subst_x3f(v_mvarId_3521_, v_hFVarId_3522_, v_a_3523_, v_a_3524_, v_a_3525_, v_a_3526_);
if (lean_obj_tag(v___x_3528_) == 0)
{
lean_object* v_a_3529_; lean_object* v___x_3531_; uint8_t v_isShared_3532_; uint8_t v_isSharedCheck_3540_; 
v_a_3529_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3531_ = v___x_3528_;
v_isShared_3532_ = v_isSharedCheck_3540_;
goto v_resetjp_3530_;
}
else
{
lean_inc(v_a_3529_);
lean_dec(v___x_3528_);
v___x_3531_ = lean_box(0);
v_isShared_3532_ = v_isSharedCheck_3540_;
goto v_resetjp_3530_;
}
v_resetjp_3530_:
{
if (lean_obj_tag(v_a_3529_) == 0)
{
lean_object* v___x_3534_; 
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v_mvarId_3521_);
v___x_3534_ = v___x_3531_;
goto v_reusejp_3533_;
}
else
{
lean_object* v_reuseFailAlloc_3535_; 
v_reuseFailAlloc_3535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3535_, 0, v_mvarId_3521_);
v___x_3534_ = v_reuseFailAlloc_3535_;
goto v_reusejp_3533_;
}
v_reusejp_3533_:
{
return v___x_3534_;
}
}
else
{
lean_object* v_val_3536_; lean_object* v___x_3538_; 
lean_dec(v_mvarId_3521_);
v_val_3536_ = lean_ctor_get(v_a_3529_, 0);
lean_inc(v_val_3536_);
lean_dec_ref_known(v_a_3529_, 1);
if (v_isShared_3532_ == 0)
{
lean_ctor_set(v___x_3531_, 0, v_val_3536_);
v___x_3538_ = v___x_3531_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_val_3536_);
v___x_3538_ = v_reuseFailAlloc_3539_;
goto v_reusejp_3537_;
}
v_reusejp_3537_:
{
return v___x_3538_;
}
}
}
}
else
{
lean_object* v_a_3541_; lean_object* v___x_3543_; uint8_t v_isShared_3544_; uint8_t v_isSharedCheck_3548_; 
lean_dec(v_mvarId_3521_);
v_a_3541_ = lean_ctor_get(v___x_3528_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3528_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3528_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3528_);
v___x_3543_ = lean_box(0);
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
v_resetjp_3542_:
{
lean_object* v___x_3546_; 
if (v_isShared_3544_ == 0)
{
v___x_3546_ = v___x_3543_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_a_3541_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
return v___x_3546_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_trySubst___boxed(lean_object* v_mvarId_3549_, lean_object* v_hFVarId_3550_, lean_object* v_a_3551_, lean_object* v_a_3552_, lean_object* v_a_3553_, lean_object* v_a_3554_, lean_object* v_a_3555_){
_start:
{
lean_object* v_res_3556_; 
v_res_3556_ = l_Lean_Meta_trySubst(v_mvarId_3549_, v_hFVarId_3550_, v_a_3551_, v_a_3552_, v_a_3553_, v_a_3554_);
lean_dec(v_a_3554_);
lean_dec_ref(v_a_3553_);
lean_dec(v_a_3552_);
lean_dec_ref(v_a_3551_);
return v_res_3556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(lean_object* v_mvarId_3560_, lean_object* v_as_3561_, size_t v_sz_3562_, size_t v_i_3563_, lean_object* v_b_3564_, lean_object* v___y_3565_, lean_object* v___y_3566_, lean_object* v___y_3567_, lean_object* v___y_3568_){
_start:
{
uint8_t v___x_3570_; 
v___x_3570_ = lean_usize_dec_lt(v_i_3563_, v_sz_3562_);
if (v___x_3570_ == 0)
{
lean_object* v___x_3571_; 
lean_dec(v_mvarId_3560_);
v___x_3571_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3571_, 0, v_b_3564_);
return v___x_3571_;
}
else
{
lean_object* v_snd_3572_; lean_object* v___x_3574_; uint8_t v_isShared_3575_; uint8_t v_isSharedCheck_3625_; 
v_snd_3572_ = lean_ctor_get(v_b_3564_, 1);
v_isSharedCheck_3625_ = !lean_is_exclusive(v_b_3564_);
if (v_isSharedCheck_3625_ == 0)
{
lean_object* v_unused_3626_; 
v_unused_3626_ = lean_ctor_get(v_b_3564_, 0);
lean_dec(v_unused_3626_);
v___x_3574_ = v_b_3564_;
v_isShared_3575_ = v_isSharedCheck_3625_;
goto v_resetjp_3573_;
}
else
{
lean_inc(v_snd_3572_);
lean_dec(v_b_3564_);
v___x_3574_ = lean_box(0);
v_isShared_3575_ = v_isSharedCheck_3625_;
goto v_resetjp_3573_;
}
v_resetjp_3573_:
{
lean_object* v___x_3576_; lean_object* v_a_3578_; lean_object* v_a_3585_; 
v___x_3576_ = lean_box(0);
v_a_3585_ = lean_array_uget(v_as_3561_, v_i_3563_);
if (lean_obj_tag(v_a_3585_) == 0)
{
v_a_3578_ = v_snd_3572_;
goto v___jp_3577_;
}
else
{
lean_object* v_val_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3624_; 
v_val_3586_ = lean_ctor_get(v_a_3585_, 0);
v_isSharedCheck_3624_ = !lean_is_exclusive(v_a_3585_);
if (v_isSharedCheck_3624_ == 0)
{
v___x_3588_ = v_a_3585_;
v_isShared_3589_ = v_isSharedCheck_3624_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_val_3586_);
lean_dec(v_a_3585_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3624_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = l_Lean_LocalDecl_fvarId(v_val_3586_);
lean_dec(v_val_3586_);
lean_inc(v_mvarId_3560_);
v___x_3591_ = l_Lean_Meta_subst_x3f(v_mvarId_3560_, v___x_3590_, v___y_3565_, v___y_3566_, v___y_3567_, v___y_3568_);
if (lean_obj_tag(v___x_3591_) == 0)
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3615_; 
v_a_3592_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3615_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3615_ == 0)
{
v___x_3594_ = v___x_3591_;
v_isShared_3595_ = v_isSharedCheck_3615_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3591_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3615_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3596_; 
v___x_3596_ = lean_box(0);
if (lean_obj_tag(v_a_3592_) == 1)
{
lean_object* v___x_3598_; 
lean_del_object(v___x_3574_);
lean_dec(v_mvarId_3560_);
lean_inc_ref(v_a_3592_);
if (v_isShared_3589_ == 0)
{
lean_ctor_set(v___x_3588_, 0, v_a_3592_);
v___x_3598_ = v___x_3588_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3613_; 
v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3592_);
v___x_3598_ = v_reuseFailAlloc_3613_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
lean_object* v___x_3600_; uint8_t v_isShared_3601_; uint8_t v_isSharedCheck_3611_; 
v_isSharedCheck_3611_ = !lean_is_exclusive(v_a_3592_);
if (v_isSharedCheck_3611_ == 0)
{
lean_object* v_unused_3612_; 
v_unused_3612_ = lean_ctor_get(v_a_3592_, 0);
lean_dec(v_unused_3612_);
v___x_3600_ = v_a_3592_;
v_isShared_3601_ = v_isSharedCheck_3611_;
goto v_resetjp_3599_;
}
else
{
lean_dec(v_a_3592_);
v___x_3600_ = lean_box(0);
v_isShared_3601_ = v_isSharedCheck_3611_;
goto v_resetjp_3599_;
}
v_resetjp_3599_:
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
v___x_3602_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3602_, 0, v___x_3598_);
lean_ctor_set(v___x_3602_, 1, v___x_3596_);
if (v_isShared_3601_ == 0)
{
lean_ctor_set_tag(v___x_3600_, 0);
lean_ctor_set(v___x_3600_, 0, v___x_3602_);
v___x_3604_ = v___x_3600_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3605_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v_snd_3572_);
if (v_isShared_3595_ == 0)
{
lean_ctor_set(v___x_3594_, 0, v___x_3606_);
v___x_3608_ = v___x_3594_;
goto v_reusejp_3607_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3606_);
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
else
{
lean_object* v___x_3614_; 
lean_del_object(v___x_3594_);
lean_dec(v_a_3592_);
lean_del_object(v___x_3588_);
lean_dec(v_snd_3572_);
v___x_3614_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3578_ = v___x_3614_;
goto v___jp_3577_;
}
}
}
else
{
lean_object* v_a_3616_; lean_object* v___x_3618_; uint8_t v_isShared_3619_; uint8_t v_isSharedCheck_3623_; 
lean_del_object(v___x_3588_);
lean_del_object(v___x_3574_);
lean_dec(v_snd_3572_);
lean_dec(v_mvarId_3560_);
v_a_3616_ = lean_ctor_get(v___x_3591_, 0);
v_isSharedCheck_3623_ = !lean_is_exclusive(v___x_3591_);
if (v_isSharedCheck_3623_ == 0)
{
v___x_3618_ = v___x_3591_;
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
else
{
lean_inc(v_a_3616_);
lean_dec(v___x_3591_);
v___x_3618_ = lean_box(0);
v_isShared_3619_ = v_isSharedCheck_3623_;
goto v_resetjp_3617_;
}
v_resetjp_3617_:
{
lean_object* v___x_3621_; 
if (v_isShared_3619_ == 0)
{
v___x_3621_ = v___x_3618_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v_a_3616_);
v___x_3621_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
return v___x_3621_;
}
}
}
}
}
v___jp_3577_:
{
lean_object* v___x_3580_; 
if (v_isShared_3575_ == 0)
{
lean_ctor_set(v___x_3574_, 1, v_a_3578_);
lean_ctor_set(v___x_3574_, 0, v___x_3576_);
v___x_3580_ = v___x_3574_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v___x_3576_);
lean_ctor_set(v_reuseFailAlloc_3584_, 1, v_a_3578_);
v___x_3580_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
size_t v___x_3581_; size_t v___x_3582_; 
v___x_3581_ = ((size_t)1ULL);
v___x_3582_ = lean_usize_add(v_i_3563_, v___x_3581_);
v_i_3563_ = v___x_3582_;
v_b_3564_ = v___x_3580_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_mvarId_3627_, lean_object* v_as_3628_, lean_object* v_sz_3629_, lean_object* v_i_3630_, lean_object* v_b_3631_, lean_object* v___y_3632_, lean_object* v___y_3633_, lean_object* v___y_3634_, lean_object* v___y_3635_, lean_object* v___y_3636_){
_start:
{
size_t v_sz_boxed_3637_; size_t v_i_boxed_3638_; lean_object* v_res_3639_; 
v_sz_boxed_3637_ = lean_unbox_usize(v_sz_3629_);
lean_dec(v_sz_3629_);
v_i_boxed_3638_ = lean_unbox_usize(v_i_3630_);
lean_dec(v_i_3630_);
v_res_3639_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3627_, v_as_3628_, v_sz_boxed_3637_, v_i_boxed_3638_, v_b_3631_, v___y_3632_, v___y_3633_, v___y_3634_, v___y_3635_);
lean_dec(v___y_3635_);
lean_dec_ref(v___y_3634_);
lean_dec(v___y_3633_);
lean_dec_ref(v___y_3632_);
lean_dec_ref(v_as_3628_);
return v_res_3639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(lean_object* v_mvarId_3640_, lean_object* v_as_3641_, size_t v_sz_3642_, size_t v_i_3643_, lean_object* v_b_3644_, lean_object* v___y_3645_, lean_object* v___y_3646_, lean_object* v___y_3647_, lean_object* v___y_3648_){
_start:
{
uint8_t v___x_3650_; 
v___x_3650_ = lean_usize_dec_lt(v_i_3643_, v_sz_3642_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; 
lean_dec(v_mvarId_3640_);
v___x_3651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3651_, 0, v_b_3644_);
return v___x_3651_;
}
else
{
lean_object* v_snd_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3705_; 
v_snd_3652_ = lean_ctor_get(v_b_3644_, 1);
v_isSharedCheck_3705_ = !lean_is_exclusive(v_b_3644_);
if (v_isSharedCheck_3705_ == 0)
{
lean_object* v_unused_3706_; 
v_unused_3706_ = lean_ctor_get(v_b_3644_, 0);
lean_dec(v_unused_3706_);
v___x_3654_ = v_b_3644_;
v_isShared_3655_ = v_isSharedCheck_3705_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_snd_3652_);
lean_dec(v_b_3644_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3705_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3656_; lean_object* v_a_3658_; lean_object* v_a_3665_; 
v___x_3656_ = lean_box(0);
v_a_3665_ = lean_array_uget(v_as_3641_, v_i_3643_);
if (lean_obj_tag(v_a_3665_) == 0)
{
v_a_3658_ = v_snd_3652_;
goto v___jp_3657_;
}
else
{
lean_object* v_val_3666_; lean_object* v___x_3668_; uint8_t v_isShared_3669_; uint8_t v_isSharedCheck_3704_; 
v_val_3666_ = lean_ctor_get(v_a_3665_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v_a_3665_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3668_ = v_a_3665_;
v_isShared_3669_ = v_isSharedCheck_3704_;
goto v_resetjp_3667_;
}
else
{
lean_inc(v_val_3666_);
lean_dec(v_a_3665_);
v___x_3668_ = lean_box(0);
v_isShared_3669_ = v_isSharedCheck_3704_;
goto v_resetjp_3667_;
}
v_resetjp_3667_:
{
lean_object* v___x_3670_; lean_object* v___x_3671_; 
v___x_3670_ = l_Lean_LocalDecl_fvarId(v_val_3666_);
lean_dec(v_val_3666_);
lean_inc(v_mvarId_3640_);
v___x_3671_ = l_Lean_Meta_subst_x3f(v_mvarId_3640_, v___x_3670_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3695_; 
v_a_3672_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3674_ = v___x_3671_;
v_isShared_3675_ = v_isSharedCheck_3695_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3671_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3695_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_box(0);
if (lean_obj_tag(v_a_3672_) == 1)
{
lean_object* v___x_3678_; 
lean_del_object(v___x_3654_);
lean_dec(v_mvarId_3640_);
lean_inc_ref(v_a_3672_);
if (v_isShared_3669_ == 0)
{
lean_ctor_set(v___x_3668_, 0, v_a_3672_);
v___x_3678_ = v___x_3668_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3672_);
v___x_3678_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3691_; 
v_isSharedCheck_3691_ = !lean_is_exclusive(v_a_3672_);
if (v_isSharedCheck_3691_ == 0)
{
lean_object* v_unused_3692_; 
v_unused_3692_ = lean_ctor_get(v_a_3672_, 0);
lean_dec(v_unused_3692_);
v___x_3680_ = v_a_3672_;
v_isShared_3681_ = v_isSharedCheck_3691_;
goto v_resetjp_3679_;
}
else
{
lean_dec(v_a_3672_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3691_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3682_, 0, v___x_3678_);
lean_ctor_set(v___x_3682_, 1, v___x_3676_);
if (v_isShared_3681_ == 0)
{
lean_ctor_set_tag(v___x_3680_, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3682_);
v___x_3684_ = v___x_3680_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3690_; 
v_reuseFailAlloc_3690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3690_, 0, v___x_3682_);
v___x_3684_ = v_reuseFailAlloc_3690_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
lean_object* v___x_3685_; lean_object* v___x_3686_; lean_object* v___x_3688_; 
v___x_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3685_, 0, v___x_3684_);
v___x_3686_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3686_, 0, v___x_3685_);
lean_ctor_set(v___x_3686_, 1, v_snd_3652_);
if (v_isShared_3675_ == 0)
{
lean_ctor_set(v___x_3674_, 0, v___x_3686_);
v___x_3688_ = v___x_3674_;
goto v_reusejp_3687_;
}
else
{
lean_object* v_reuseFailAlloc_3689_; 
v_reuseFailAlloc_3689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3689_, 0, v___x_3686_);
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
else
{
lean_object* v___x_3694_; 
lean_del_object(v___x_3674_);
lean_dec(v_a_3672_);
lean_del_object(v___x_3668_);
lean_dec(v_snd_3652_);
v___x_3694_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3___closed__0));
v_a_3658_ = v___x_3694_;
goto v___jp_3657_;
}
}
}
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_del_object(v___x_3668_);
lean_del_object(v___x_3654_);
lean_dec(v_snd_3652_);
lean_dec(v_mvarId_3640_);
v_a_3696_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3671_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3671_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3701_; 
if (v_isShared_3699_ == 0)
{
v___x_3701_ = v___x_3698_;
goto v_reusejp_3700_;
}
else
{
lean_object* v_reuseFailAlloc_3702_; 
v_reuseFailAlloc_3702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3702_, 0, v_a_3696_);
v___x_3701_ = v_reuseFailAlloc_3702_;
goto v_reusejp_3700_;
}
v_reusejp_3700_:
{
return v___x_3701_;
}
}
}
}
}
v___jp_3657_:
{
lean_object* v___x_3660_; 
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 1, v_a_3658_);
lean_ctor_set(v___x_3654_, 0, v___x_3656_);
v___x_3660_ = v___x_3654_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3656_);
lean_ctor_set(v_reuseFailAlloc_3664_, 1, v_a_3658_);
v___x_3660_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
size_t v___x_3661_; size_t v___x_3662_; lean_object* v___x_3663_; 
v___x_3661_ = ((size_t)1ULL);
v___x_3662_ = lean_usize_add(v_i_3643_, v___x_3661_);
v___x_3663_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2_spec__3(v_mvarId_3640_, v_as_3641_, v_sz_3642_, v___x_3662_, v___x_3660_, v___y_3645_, v___y_3646_, v___y_3647_, v___y_3648_);
return v___x_3663_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2___boxed(lean_object* v_mvarId_3707_, lean_object* v_as_3708_, lean_object* v_sz_3709_, lean_object* v_i_3710_, lean_object* v_b_3711_, lean_object* v___y_3712_, lean_object* v___y_3713_, lean_object* v___y_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_){
_start:
{
size_t v_sz_boxed_3717_; size_t v_i_boxed_3718_; lean_object* v_res_3719_; 
v_sz_boxed_3717_ = lean_unbox_usize(v_sz_3709_);
lean_dec(v_sz_3709_);
v_i_boxed_3718_ = lean_unbox_usize(v_i_3710_);
lean_dec(v_i_3710_);
v_res_3719_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3707_, v_as_3708_, v_sz_boxed_3717_, v_i_boxed_3718_, v_b_3711_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_);
lean_dec(v___y_3715_);
lean_dec_ref(v___y_3714_);
lean_dec(v___y_3713_);
lean_dec_ref(v___y_3712_);
lean_dec_ref(v_as_3708_);
return v_res_3719_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(lean_object* v_init_3720_, lean_object* v_mvarId_3721_, lean_object* v_n_3722_, lean_object* v_b_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
if (lean_obj_tag(v_n_3722_) == 0)
{
lean_object* v_cs_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; size_t v_sz_3732_; size_t v___x_3733_; lean_object* v___x_3734_; 
v_cs_3729_ = lean_ctor_get(v_n_3722_, 0);
v___x_3730_ = lean_box(0);
v___x_3731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3731_, 0, v___x_3730_);
lean_ctor_set(v___x_3731_, 1, v_b_3723_);
v_sz_3732_ = lean_array_size(v_cs_3729_);
v___x_3733_ = ((size_t)0ULL);
v___x_3734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3720_, v_mvarId_3721_, v_cs_3729_, v_sz_3732_, v___x_3733_, v___x_3731_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3749_; 
v_a_3735_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3737_ = v___x_3734_;
v_isShared_3738_ = v_isSharedCheck_3749_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3734_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3749_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v_fst_3739_; 
v_fst_3739_ = lean_ctor_get(v_a_3735_, 0);
if (lean_obj_tag(v_fst_3739_) == 0)
{
lean_object* v_snd_3740_; lean_object* v___x_3741_; lean_object* v___x_3743_; 
v_snd_3740_ = lean_ctor_get(v_a_3735_, 1);
lean_inc(v_snd_3740_);
lean_dec(v_a_3735_);
v___x_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3741_, 0, v_snd_3740_);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v___x_3741_);
v___x_3743_ = v___x_3737_;
goto v_reusejp_3742_;
}
else
{
lean_object* v_reuseFailAlloc_3744_; 
v_reuseFailAlloc_3744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3744_, 0, v___x_3741_);
v___x_3743_ = v_reuseFailAlloc_3744_;
goto v_reusejp_3742_;
}
v_reusejp_3742_:
{
return v___x_3743_;
}
}
else
{
lean_object* v_val_3745_; lean_object* v___x_3747_; 
lean_inc_ref(v_fst_3739_);
lean_dec(v_a_3735_);
v_val_3745_ = lean_ctor_get(v_fst_3739_, 0);
lean_inc(v_val_3745_);
lean_dec_ref_known(v_fst_3739_, 1);
if (v_isShared_3738_ == 0)
{
lean_ctor_set(v___x_3737_, 0, v_val_3745_);
v___x_3747_ = v___x_3737_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_val_3745_);
v___x_3747_ = v_reuseFailAlloc_3748_;
goto v_reusejp_3746_;
}
v_reusejp_3746_:
{
return v___x_3747_;
}
}
}
}
else
{
lean_object* v_a_3750_; lean_object* v___x_3752_; uint8_t v_isShared_3753_; uint8_t v_isSharedCheck_3757_; 
v_a_3750_ = lean_ctor_get(v___x_3734_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3734_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3734_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3734_);
v___x_3752_ = lean_box(0);
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
v_resetjp_3751_:
{
lean_object* v___x_3755_; 
if (v_isShared_3753_ == 0)
{
v___x_3755_ = v___x_3752_;
goto v_reusejp_3754_;
}
else
{
lean_object* v_reuseFailAlloc_3756_; 
v_reuseFailAlloc_3756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3756_, 0, v_a_3750_);
v___x_3755_ = v_reuseFailAlloc_3756_;
goto v_reusejp_3754_;
}
v_reusejp_3754_:
{
return v___x_3755_;
}
}
}
}
else
{
lean_object* v_vs_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; size_t v_sz_3761_; size_t v___x_3762_; lean_object* v___x_3763_; 
v_vs_3758_ = lean_ctor_get(v_n_3722_, 0);
v___x_3759_ = lean_box(0);
v___x_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set(v___x_3760_, 1, v_b_3723_);
v_sz_3761_ = lean_array_size(v_vs_3758_);
v___x_3762_ = ((size_t)0ULL);
v___x_3763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__2(v_mvarId_3721_, v_vs_3758_, v_sz_3761_, v___x_3762_, v___x_3760_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
if (lean_obj_tag(v___x_3763_) == 0)
{
lean_object* v_a_3764_; lean_object* v___x_3766_; uint8_t v_isShared_3767_; uint8_t v_isSharedCheck_3778_; 
v_a_3764_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3778_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3778_ == 0)
{
v___x_3766_ = v___x_3763_;
v_isShared_3767_ = v_isSharedCheck_3778_;
goto v_resetjp_3765_;
}
else
{
lean_inc(v_a_3764_);
lean_dec(v___x_3763_);
v___x_3766_ = lean_box(0);
v_isShared_3767_ = v_isSharedCheck_3778_;
goto v_resetjp_3765_;
}
v_resetjp_3765_:
{
lean_object* v_fst_3768_; 
v_fst_3768_ = lean_ctor_get(v_a_3764_, 0);
if (lean_obj_tag(v_fst_3768_) == 0)
{
lean_object* v_snd_3769_; lean_object* v___x_3770_; lean_object* v___x_3772_; 
v_snd_3769_ = lean_ctor_get(v_a_3764_, 1);
lean_inc(v_snd_3769_);
lean_dec(v_a_3764_);
v___x_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3770_, 0, v_snd_3769_);
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 0, v___x_3770_);
v___x_3772_ = v___x_3766_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v___x_3770_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
else
{
lean_object* v_val_3774_; lean_object* v___x_3776_; 
lean_inc_ref(v_fst_3768_);
lean_dec(v_a_3764_);
v_val_3774_ = lean_ctor_get(v_fst_3768_, 0);
lean_inc(v_val_3774_);
lean_dec_ref_known(v_fst_3768_, 1);
if (v_isShared_3767_ == 0)
{
lean_ctor_set(v___x_3766_, 0, v_val_3774_);
v___x_3776_ = v___x_3766_;
goto v_reusejp_3775_;
}
else
{
lean_object* v_reuseFailAlloc_3777_; 
v_reuseFailAlloc_3777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3777_, 0, v_val_3774_);
v___x_3776_ = v_reuseFailAlloc_3777_;
goto v_reusejp_3775_;
}
v_reusejp_3775_:
{
return v___x_3776_;
}
}
}
}
else
{
lean_object* v_a_3779_; lean_object* v___x_3781_; uint8_t v_isShared_3782_; uint8_t v_isSharedCheck_3786_; 
v_a_3779_ = lean_ctor_get(v___x_3763_, 0);
v_isSharedCheck_3786_ = !lean_is_exclusive(v___x_3763_);
if (v_isSharedCheck_3786_ == 0)
{
v___x_3781_ = v___x_3763_;
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
else
{
lean_inc(v_a_3779_);
lean_dec(v___x_3763_);
v___x_3781_ = lean_box(0);
v_isShared_3782_ = v_isSharedCheck_3786_;
goto v_resetjp_3780_;
}
v_resetjp_3780_:
{
lean_object* v___x_3784_; 
if (v_isShared_3782_ == 0)
{
v___x_3784_ = v___x_3781_;
goto v_reusejp_3783_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_a_3779_);
v___x_3784_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3783_;
}
v_reusejp_3783_:
{
return v___x_3784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(lean_object* v_init_3787_, lean_object* v_mvarId_3788_, lean_object* v_as_3789_, size_t v_sz_3790_, size_t v_i_3791_, lean_object* v_b_3792_, lean_object* v___y_3793_, lean_object* v___y_3794_, lean_object* v___y_3795_, lean_object* v___y_3796_){
_start:
{
uint8_t v___x_3798_; 
v___x_3798_ = lean_usize_dec_lt(v_i_3791_, v_sz_3790_);
if (v___x_3798_ == 0)
{
lean_object* v___x_3799_; 
lean_dec(v_mvarId_3788_);
v___x_3799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3799_, 0, v_b_3792_);
return v___x_3799_;
}
else
{
lean_object* v_snd_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3834_; 
v_snd_3800_ = lean_ctor_get(v_b_3792_, 1);
v_isSharedCheck_3834_ = !lean_is_exclusive(v_b_3792_);
if (v_isSharedCheck_3834_ == 0)
{
lean_object* v_unused_3835_; 
v_unused_3835_ = lean_ctor_get(v_b_3792_, 0);
lean_dec(v_unused_3835_);
v___x_3802_ = v_b_3792_;
v_isShared_3803_ = v_isSharedCheck_3834_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_snd_3800_);
lean_dec(v_b_3792_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3834_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v_a_3804_; lean_object* v___x_3805_; 
v_a_3804_ = lean_array_uget_borrowed(v_as_3789_, v_i_3791_);
lean_inc(v_snd_3800_);
lean_inc(v_mvarId_3788_);
v___x_3805_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3787_, v_mvarId_3788_, v_a_3804_, v_snd_3800_, v___y_3793_, v___y_3794_, v___y_3795_, v___y_3796_);
if (lean_obj_tag(v___x_3805_) == 0)
{
lean_object* v_a_3806_; lean_object* v___x_3808_; uint8_t v_isShared_3809_; uint8_t v_isSharedCheck_3825_; 
v_a_3806_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3825_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3825_ == 0)
{
v___x_3808_ = v___x_3805_;
v_isShared_3809_ = v_isSharedCheck_3825_;
goto v_resetjp_3807_;
}
else
{
lean_inc(v_a_3806_);
lean_dec(v___x_3805_);
v___x_3808_ = lean_box(0);
v_isShared_3809_ = v_isSharedCheck_3825_;
goto v_resetjp_3807_;
}
v_resetjp_3807_:
{
if (lean_obj_tag(v_a_3806_) == 0)
{
lean_object* v___x_3810_; lean_object* v___x_3812_; 
lean_dec(v_mvarId_3788_);
v___x_3810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3810_, 0, v_a_3806_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3810_);
v___x_3812_ = v___x_3802_;
goto v_reusejp_3811_;
}
else
{
lean_object* v_reuseFailAlloc_3816_; 
v_reuseFailAlloc_3816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3816_, 0, v___x_3810_);
lean_ctor_set(v_reuseFailAlloc_3816_, 1, v_snd_3800_);
v___x_3812_ = v_reuseFailAlloc_3816_;
goto v_reusejp_3811_;
}
v_reusejp_3811_:
{
lean_object* v___x_3814_; 
if (v_isShared_3809_ == 0)
{
lean_ctor_set(v___x_3808_, 0, v___x_3812_);
v___x_3814_ = v___x_3808_;
goto v_reusejp_3813_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3812_);
v___x_3814_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3813_;
}
v_reusejp_3813_:
{
return v___x_3814_;
}
}
}
else
{
lean_object* v_a_3817_; lean_object* v___x_3818_; lean_object* v___x_3820_; 
lean_del_object(v___x_3808_);
lean_dec(v_snd_3800_);
v_a_3817_ = lean_ctor_get(v_a_3806_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v_a_3806_, 1);
v___x_3818_ = lean_box(0);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 1, v_a_3817_);
lean_ctor_set(v___x_3802_, 0, v___x_3818_);
v___x_3820_ = v___x_3802_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3824_; 
v_reuseFailAlloc_3824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3824_, 0, v___x_3818_);
lean_ctor_set(v_reuseFailAlloc_3824_, 1, v_a_3817_);
v___x_3820_ = v_reuseFailAlloc_3824_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
size_t v___x_3821_; size_t v___x_3822_; 
v___x_3821_ = ((size_t)1ULL);
v___x_3822_ = lean_usize_add(v_i_3791_, v___x_3821_);
v_i_3791_ = v___x_3822_;
v_b_3792_ = v___x_3820_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_3826_; lean_object* v___x_3828_; uint8_t v_isShared_3829_; uint8_t v_isSharedCheck_3833_; 
lean_del_object(v___x_3802_);
lean_dec(v_snd_3800_);
lean_dec(v_mvarId_3788_);
v_a_3826_ = lean_ctor_get(v___x_3805_, 0);
v_isSharedCheck_3833_ = !lean_is_exclusive(v___x_3805_);
if (v_isSharedCheck_3833_ == 0)
{
v___x_3828_ = v___x_3805_;
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
else
{
lean_inc(v_a_3826_);
lean_dec(v___x_3805_);
v___x_3828_ = lean_box(0);
v_isShared_3829_ = v_isSharedCheck_3833_;
goto v_resetjp_3827_;
}
v_resetjp_3827_:
{
lean_object* v___x_3831_; 
if (v_isShared_3829_ == 0)
{
v___x_3831_ = v___x_3828_;
goto v_reusejp_3830_;
}
else
{
lean_object* v_reuseFailAlloc_3832_; 
v_reuseFailAlloc_3832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3832_, 0, v_a_3826_);
v___x_3831_ = v_reuseFailAlloc_3832_;
goto v_reusejp_3830_;
}
v_reusejp_3830_:
{
return v___x_3831_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_init_3836_, lean_object* v_mvarId_3837_, lean_object* v_as_3838_, lean_object* v_sz_3839_, lean_object* v_i_3840_, lean_object* v_b_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_, lean_object* v___y_3844_, lean_object* v___y_3845_, lean_object* v___y_3846_){
_start:
{
size_t v_sz_boxed_3847_; size_t v_i_boxed_3848_; lean_object* v_res_3849_; 
v_sz_boxed_3847_ = lean_unbox_usize(v_sz_3839_);
lean_dec(v_sz_3839_);
v_i_boxed_3848_ = lean_unbox_usize(v_i_3840_);
lean_dec(v_i_3840_);
v_res_3849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0_spec__1(v_init_3836_, v_mvarId_3837_, v_as_3838_, v_sz_boxed_3847_, v_i_boxed_3848_, v_b_3841_, v___y_3842_, v___y_3843_, v___y_3844_, v___y_3845_);
lean_dec(v___y_3845_);
lean_dec_ref(v___y_3844_);
lean_dec(v___y_3843_);
lean_dec_ref(v___y_3842_);
lean_dec_ref(v_as_3838_);
lean_dec_ref(v_init_3836_);
return v_res_3849_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0___boxed(lean_object* v_init_3850_, lean_object* v_mvarId_3851_, lean_object* v_n_3852_, lean_object* v_b_3853_, lean_object* v___y_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_){
_start:
{
lean_object* v_res_3859_; 
v_res_3859_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_3850_, v_mvarId_3851_, v_n_3852_, v_b_3853_, v___y_3854_, v___y_3855_, v___y_3856_, v___y_3857_);
lean_dec(v___y_3857_);
lean_dec_ref(v___y_3856_);
lean_dec(v___y_3855_);
lean_dec_ref(v___y_3854_);
lean_dec_ref(v_n_3852_);
lean_dec_ref(v_init_3850_);
return v_res_3859_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(lean_object* v_mvarId_3863_, lean_object* v_as_3864_, size_t v_sz_3865_, size_t v_i_3866_, lean_object* v_b_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
uint8_t v___x_3873_; 
v___x_3873_ = lean_usize_dec_lt(v_i_3866_, v_sz_3865_);
if (v___x_3873_ == 0)
{
lean_object* v___x_3874_; 
lean_dec(v_mvarId_3863_);
v___x_3874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3874_, 0, v_b_3867_);
return v___x_3874_;
}
else
{
lean_object* v_snd_3875_; lean_object* v___x_3877_; uint8_t v_isShared_3878_; uint8_t v_isSharedCheck_3927_; 
v_snd_3875_ = lean_ctor_get(v_b_3867_, 1);
v_isSharedCheck_3927_ = !lean_is_exclusive(v_b_3867_);
if (v_isSharedCheck_3927_ == 0)
{
lean_object* v_unused_3928_; 
v_unused_3928_ = lean_ctor_get(v_b_3867_, 0);
lean_dec(v_unused_3928_);
v___x_3877_ = v_b_3867_;
v_isShared_3878_ = v_isSharedCheck_3927_;
goto v_resetjp_3876_;
}
else
{
lean_inc(v_snd_3875_);
lean_dec(v_b_3867_);
v___x_3877_ = lean_box(0);
v_isShared_3878_ = v_isSharedCheck_3927_;
goto v_resetjp_3876_;
}
v_resetjp_3876_:
{
lean_object* v___x_3879_; lean_object* v_a_3881_; lean_object* v_a_3888_; 
v___x_3879_ = lean_box(0);
v_a_3888_ = lean_array_uget(v_as_3864_, v_i_3866_);
if (lean_obj_tag(v_a_3888_) == 0)
{
v_a_3881_ = v_snd_3875_;
goto v___jp_3880_;
}
else
{
lean_object* v_val_3889_; lean_object* v___x_3891_; uint8_t v_isShared_3892_; uint8_t v_isSharedCheck_3926_; 
v_val_3889_ = lean_ctor_get(v_a_3888_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v_a_3888_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3891_ = v_a_3888_;
v_isShared_3892_ = v_isSharedCheck_3926_;
goto v_resetjp_3890_;
}
else
{
lean_inc(v_val_3889_);
lean_dec(v_a_3888_);
v___x_3891_ = lean_box(0);
v_isShared_3892_ = v_isSharedCheck_3926_;
goto v_resetjp_3890_;
}
v_resetjp_3890_:
{
lean_object* v___x_3893_; lean_object* v___x_3894_; 
v___x_3893_ = l_Lean_LocalDecl_fvarId(v_val_3889_);
lean_dec(v_val_3889_);
lean_inc(v_mvarId_3863_);
v___x_3894_ = l_Lean_Meta_subst_x3f(v_mvarId_3863_, v___x_3893_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3894_) == 0)
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3917_; 
v_a_3895_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3917_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3917_ == 0)
{
v___x_3897_ = v___x_3894_;
v_isShared_3898_ = v_isSharedCheck_3917_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3894_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3917_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3899_; 
v___x_3899_ = lean_box(0);
if (lean_obj_tag(v_a_3895_) == 1)
{
lean_object* v___x_3901_; 
lean_del_object(v___x_3877_);
lean_dec(v_mvarId_3863_);
lean_inc_ref(v_a_3895_);
if (v_isShared_3892_ == 0)
{
lean_ctor_set(v___x_3891_, 0, v_a_3895_);
v___x_3901_ = v___x_3891_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3915_; 
v_reuseFailAlloc_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3915_, 0, v_a_3895_);
v___x_3901_ = v_reuseFailAlloc_3915_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
lean_object* v___x_3903_; uint8_t v_isShared_3904_; uint8_t v_isSharedCheck_3913_; 
v_isSharedCheck_3913_ = !lean_is_exclusive(v_a_3895_);
if (v_isSharedCheck_3913_ == 0)
{
lean_object* v_unused_3914_; 
v_unused_3914_ = lean_ctor_get(v_a_3895_, 0);
lean_dec(v_unused_3914_);
v___x_3903_ = v_a_3895_;
v_isShared_3904_ = v_isSharedCheck_3913_;
goto v_resetjp_3902_;
}
else
{
lean_dec(v_a_3895_);
v___x_3903_ = lean_box(0);
v_isShared_3904_ = v_isSharedCheck_3913_;
goto v_resetjp_3902_;
}
v_resetjp_3902_:
{
lean_object* v___x_3905_; lean_object* v___x_3907_; 
v___x_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3901_);
lean_ctor_set(v___x_3905_, 1, v___x_3899_);
if (v_isShared_3904_ == 0)
{
lean_ctor_set(v___x_3903_, 0, v___x_3905_);
v___x_3907_ = v___x_3903_;
goto v_reusejp_3906_;
}
else
{
lean_object* v_reuseFailAlloc_3912_; 
v_reuseFailAlloc_3912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3912_, 0, v___x_3905_);
v___x_3907_ = v_reuseFailAlloc_3912_;
goto v_reusejp_3906_;
}
v_reusejp_3906_:
{
lean_object* v___x_3908_; lean_object* v___x_3910_; 
v___x_3908_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v_snd_3875_);
if (v_isShared_3898_ == 0)
{
lean_ctor_set(v___x_3897_, 0, v___x_3908_);
v___x_3910_ = v___x_3897_;
goto v_reusejp_3909_;
}
else
{
lean_object* v_reuseFailAlloc_3911_; 
v_reuseFailAlloc_3911_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3911_, 0, v___x_3908_);
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
else
{
lean_object* v___x_3916_; 
lean_del_object(v___x_3897_);
lean_dec(v_a_3895_);
lean_del_object(v___x_3891_);
lean_dec(v_snd_3875_);
v___x_3916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3881_ = v___x_3916_;
goto v___jp_3880_;
}
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_del_object(v___x_3891_);
lean_del_object(v___x_3877_);
lean_dec(v_snd_3875_);
lean_dec(v_mvarId_3863_);
v_a_3918_ = lean_ctor_get(v___x_3894_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3894_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3894_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3894_);
v___x_3920_ = lean_box(0);
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
v_resetjp_3919_:
{
lean_object* v___x_3923_; 
if (v_isShared_3921_ == 0)
{
v___x_3923_ = v___x_3920_;
goto v_reusejp_3922_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v_a_3918_);
v___x_3923_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3922_;
}
v_reusejp_3922_:
{
return v___x_3923_;
}
}
}
}
}
v___jp_3880_:
{
lean_object* v___x_3883_; 
if (v_isShared_3878_ == 0)
{
lean_ctor_set(v___x_3877_, 1, v_a_3881_);
lean_ctor_set(v___x_3877_, 0, v___x_3879_);
v___x_3883_ = v___x_3877_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3887_; 
v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3887_, 0, v___x_3879_);
lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_a_3881_);
v___x_3883_ = v_reuseFailAlloc_3887_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
size_t v___x_3884_; size_t v___x_3885_; 
v___x_3884_ = ((size_t)1ULL);
v___x_3885_ = lean_usize_add(v_i_3866_, v___x_3884_);
v_i_3866_ = v___x_3885_;
v_b_3867_ = v___x_3883_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___boxed(lean_object* v_mvarId_3929_, lean_object* v_as_3930_, lean_object* v_sz_3931_, lean_object* v_i_3932_, lean_object* v_b_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_, lean_object* v___y_3937_, lean_object* v___y_3938_){
_start:
{
size_t v_sz_boxed_3939_; size_t v_i_boxed_3940_; lean_object* v_res_3941_; 
v_sz_boxed_3939_ = lean_unbox_usize(v_sz_3931_);
lean_dec(v_sz_3931_);
v_i_boxed_3940_ = lean_unbox_usize(v_i_3932_);
lean_dec(v_i_3932_);
v_res_3941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3929_, v_as_3930_, v_sz_boxed_3939_, v_i_boxed_3940_, v_b_3933_, v___y_3934_, v___y_3935_, v___y_3936_, v___y_3937_);
lean_dec(v___y_3937_);
lean_dec_ref(v___y_3936_);
lean_dec(v___y_3935_);
lean_dec_ref(v___y_3934_);
lean_dec_ref(v_as_3930_);
return v_res_3941_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(lean_object* v_mvarId_3942_, lean_object* v_as_3943_, size_t v_sz_3944_, size_t v_i_3945_, lean_object* v_b_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
uint8_t v___x_3952_; 
v___x_3952_ = lean_usize_dec_lt(v_i_3945_, v_sz_3944_);
if (v___x_3952_ == 0)
{
lean_object* v___x_3953_; 
lean_dec(v_mvarId_3942_);
v___x_3953_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3953_, 0, v_b_3946_);
return v___x_3953_;
}
else
{
lean_object* v_snd_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_4006_; 
v_snd_3954_ = lean_ctor_get(v_b_3946_, 1);
v_isSharedCheck_4006_ = !lean_is_exclusive(v_b_3946_);
if (v_isSharedCheck_4006_ == 0)
{
lean_object* v_unused_4007_; 
v_unused_4007_ = lean_ctor_get(v_b_3946_, 0);
lean_dec(v_unused_4007_);
v___x_3956_ = v_b_3946_;
v_isShared_3957_ = v_isSharedCheck_4006_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_snd_3954_);
lean_dec(v_b_3946_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_4006_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3958_; lean_object* v_a_3960_; lean_object* v_a_3967_; 
v___x_3958_ = lean_box(0);
v_a_3967_ = lean_array_uget(v_as_3943_, v_i_3945_);
if (lean_obj_tag(v_a_3967_) == 0)
{
v_a_3960_ = v_snd_3954_;
goto v___jp_3959_;
}
else
{
lean_object* v_val_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_4005_; 
v_val_3968_ = lean_ctor_get(v_a_3967_, 0);
v_isSharedCheck_4005_ = !lean_is_exclusive(v_a_3967_);
if (v_isSharedCheck_4005_ == 0)
{
v___x_3970_ = v_a_3967_;
v_isShared_3971_ = v_isSharedCheck_4005_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_val_3968_);
lean_dec(v_a_3967_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_4005_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3972_; lean_object* v___x_3973_; 
v___x_3972_ = l_Lean_LocalDecl_fvarId(v_val_3968_);
lean_dec(v_val_3968_);
lean_inc(v_mvarId_3942_);
v___x_3973_ = l_Lean_Meta_subst_x3f(v_mvarId_3942_, v___x_3972_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
if (lean_obj_tag(v___x_3973_) == 0)
{
lean_object* v_a_3974_; lean_object* v___x_3976_; uint8_t v_isShared_3977_; uint8_t v_isSharedCheck_3996_; 
v_a_3974_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_3996_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_3996_ == 0)
{
v___x_3976_ = v___x_3973_;
v_isShared_3977_ = v_isSharedCheck_3996_;
goto v_resetjp_3975_;
}
else
{
lean_inc(v_a_3974_);
lean_dec(v___x_3973_);
v___x_3976_ = lean_box(0);
v_isShared_3977_ = v_isSharedCheck_3996_;
goto v_resetjp_3975_;
}
v_resetjp_3975_:
{
lean_object* v___x_3978_; 
v___x_3978_ = lean_box(0);
if (lean_obj_tag(v_a_3974_) == 1)
{
lean_object* v___x_3980_; 
lean_del_object(v___x_3956_);
lean_dec(v_mvarId_3942_);
lean_inc_ref(v_a_3974_);
if (v_isShared_3971_ == 0)
{
lean_ctor_set(v___x_3970_, 0, v_a_3974_);
v___x_3980_ = v___x_3970_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3994_; 
v_reuseFailAlloc_3994_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3974_);
v___x_3980_ = v_reuseFailAlloc_3994_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3992_; 
v_isSharedCheck_3992_ = !lean_is_exclusive(v_a_3974_);
if (v_isSharedCheck_3992_ == 0)
{
lean_object* v_unused_3993_; 
v_unused_3993_ = lean_ctor_get(v_a_3974_, 0);
lean_dec(v_unused_3993_);
v___x_3982_ = v_a_3974_;
v_isShared_3983_ = v_isSharedCheck_3992_;
goto v_resetjp_3981_;
}
else
{
lean_dec(v_a_3974_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3992_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3984_; lean_object* v___x_3986_; 
v___x_3984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3984_, 0, v___x_3980_);
lean_ctor_set(v___x_3984_, 1, v___x_3978_);
if (v_isShared_3983_ == 0)
{
lean_ctor_set(v___x_3982_, 0, v___x_3984_);
v___x_3986_ = v___x_3982_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3991_; 
v_reuseFailAlloc_3991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3991_, 0, v___x_3984_);
v___x_3986_ = v_reuseFailAlloc_3991_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
lean_object* v___x_3987_; lean_object* v___x_3989_; 
v___x_3987_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3987_, 0, v___x_3986_);
lean_ctor_set(v___x_3987_, 1, v_snd_3954_);
if (v_isShared_3977_ == 0)
{
lean_ctor_set(v___x_3976_, 0, v___x_3987_);
v___x_3989_ = v___x_3976_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v___x_3987_);
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
else
{
lean_object* v___x_3995_; 
lean_del_object(v___x_3976_);
lean_dec(v_a_3974_);
lean_del_object(v___x_3970_);
lean_dec(v_snd_3954_);
v___x_3995_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4___closed__0));
v_a_3960_ = v___x_3995_;
goto v___jp_3959_;
}
}
}
else
{
lean_object* v_a_3997_; lean_object* v___x_3999_; uint8_t v_isShared_4000_; uint8_t v_isSharedCheck_4004_; 
lean_del_object(v___x_3970_);
lean_del_object(v___x_3956_);
lean_dec(v_snd_3954_);
lean_dec(v_mvarId_3942_);
v_a_3997_ = lean_ctor_get(v___x_3973_, 0);
v_isSharedCheck_4004_ = !lean_is_exclusive(v___x_3973_);
if (v_isSharedCheck_4004_ == 0)
{
v___x_3999_ = v___x_3973_;
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
else
{
lean_inc(v_a_3997_);
lean_dec(v___x_3973_);
v___x_3999_ = lean_box(0);
v_isShared_4000_ = v_isSharedCheck_4004_;
goto v_resetjp_3998_;
}
v_resetjp_3998_:
{
lean_object* v___x_4002_; 
if (v_isShared_4000_ == 0)
{
v___x_4002_ = v___x_3999_;
goto v_reusejp_4001_;
}
else
{
lean_object* v_reuseFailAlloc_4003_; 
v_reuseFailAlloc_4003_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4003_, 0, v_a_3997_);
v___x_4002_ = v_reuseFailAlloc_4003_;
goto v_reusejp_4001_;
}
v_reusejp_4001_:
{
return v___x_4002_;
}
}
}
}
}
v___jp_3959_:
{
lean_object* v___x_3962_; 
if (v_isShared_3957_ == 0)
{
lean_ctor_set(v___x_3956_, 1, v_a_3960_);
lean_ctor_set(v___x_3956_, 0, v___x_3958_);
v___x_3962_ = v___x_3956_;
goto v_reusejp_3961_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v___x_3958_);
lean_ctor_set(v_reuseFailAlloc_3966_, 1, v_a_3960_);
v___x_3962_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3961_;
}
v_reusejp_3961_:
{
size_t v___x_3963_; size_t v___x_3964_; lean_object* v___x_3965_; 
v___x_3963_ = ((size_t)1ULL);
v___x_3964_ = lean_usize_add(v_i_3945_, v___x_3963_);
v___x_3965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1_spec__4(v_mvarId_3942_, v_as_3943_, v_sz_3944_, v___x_3964_, v___x_3962_, v___y_3947_, v___y_3948_, v___y_3949_, v___y_3950_);
return v___x_3965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1___boxed(lean_object* v_mvarId_4008_, lean_object* v_as_4009_, lean_object* v_sz_4010_, lean_object* v_i_4011_, lean_object* v_b_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
size_t v_sz_boxed_4018_; size_t v_i_boxed_4019_; lean_object* v_res_4020_; 
v_sz_boxed_4018_ = lean_unbox_usize(v_sz_4010_);
lean_dec(v_sz_4010_);
v_i_boxed_4019_ = lean_unbox_usize(v_i_4011_);
lean_dec(v_i_4011_);
v_res_4020_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4008_, v_as_4009_, v_sz_boxed_4018_, v_i_boxed_4019_, v_b_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
lean_dec_ref(v_as_4009_);
return v_res_4020_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(lean_object* v_mvarId_4021_, lean_object* v_t_4022_, lean_object* v_init_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_){
_start:
{
lean_object* v_root_4029_; lean_object* v_tail_4030_; lean_object* v___x_4031_; 
v_root_4029_ = lean_ctor_get(v_t_4022_, 0);
v_tail_4030_ = lean_ctor_get(v_t_4022_, 1);
lean_inc(v_mvarId_4021_);
lean_inc_ref(v_init_4023_);
v___x_4031_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__0(v_init_4023_, v_mvarId_4021_, v_root_4029_, v_init_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
lean_dec_ref(v_init_4023_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4034_; uint8_t v_isShared_4035_; uint8_t v_isSharedCheck_4068_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4034_ = v___x_4031_;
v_isShared_4035_ = v_isSharedCheck_4068_;
goto v_resetjp_4033_;
}
else
{
lean_inc(v_a_4032_);
lean_dec(v___x_4031_);
v___x_4034_ = lean_box(0);
v_isShared_4035_ = v_isSharedCheck_4068_;
goto v_resetjp_4033_;
}
v_resetjp_4033_:
{
if (lean_obj_tag(v_a_4032_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4038_; 
lean_dec(v_mvarId_4021_);
v_a_4036_ = lean_ctor_get(v_a_4032_, 0);
lean_inc(v_a_4036_);
lean_dec_ref_known(v_a_4032_, 1);
if (v_isShared_4035_ == 0)
{
lean_ctor_set(v___x_4034_, 0, v_a_4036_);
v___x_4038_ = v___x_4034_;
goto v_reusejp_4037_;
}
else
{
lean_object* v_reuseFailAlloc_4039_; 
v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4039_, 0, v_a_4036_);
v___x_4038_ = v_reuseFailAlloc_4039_;
goto v_reusejp_4037_;
}
v_reusejp_4037_:
{
return v___x_4038_;
}
}
else
{
lean_object* v_a_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; size_t v_sz_4043_; size_t v___x_4044_; lean_object* v___x_4045_; 
lean_del_object(v___x_4034_);
v_a_4040_ = lean_ctor_get(v_a_4032_, 0);
lean_inc(v_a_4040_);
lean_dec_ref_known(v_a_4032_, 1);
v___x_4041_ = lean_box(0);
v___x_4042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4042_, 0, v___x_4041_);
lean_ctor_set(v___x_4042_, 1, v_a_4040_);
v_sz_4043_ = lean_array_size(v_tail_4030_);
v___x_4044_ = ((size_t)0ULL);
v___x_4045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0_spec__1(v_mvarId_4021_, v_tail_4030_, v_sz_4043_, v___x_4044_, v___x_4042_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
if (lean_obj_tag(v___x_4045_) == 0)
{
lean_object* v_a_4046_; lean_object* v___x_4048_; uint8_t v_isShared_4049_; uint8_t v_isSharedCheck_4059_; 
v_a_4046_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4048_ = v___x_4045_;
v_isShared_4049_ = v_isSharedCheck_4059_;
goto v_resetjp_4047_;
}
else
{
lean_inc(v_a_4046_);
lean_dec(v___x_4045_);
v___x_4048_ = lean_box(0);
v_isShared_4049_ = v_isSharedCheck_4059_;
goto v_resetjp_4047_;
}
v_resetjp_4047_:
{
lean_object* v_fst_4050_; 
v_fst_4050_ = lean_ctor_get(v_a_4046_, 0);
if (lean_obj_tag(v_fst_4050_) == 0)
{
lean_object* v_snd_4051_; lean_object* v___x_4053_; 
v_snd_4051_ = lean_ctor_get(v_a_4046_, 1);
lean_inc(v_snd_4051_);
lean_dec(v_a_4046_);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v_snd_4051_);
v___x_4053_ = v___x_4048_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_snd_4051_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
else
{
lean_object* v_val_4055_; lean_object* v___x_4057_; 
lean_inc_ref(v_fst_4050_);
lean_dec(v_a_4046_);
v_val_4055_ = lean_ctor_get(v_fst_4050_, 0);
lean_inc(v_val_4055_);
lean_dec_ref_known(v_fst_4050_, 1);
if (v_isShared_4049_ == 0)
{
lean_ctor_set(v___x_4048_, 0, v_val_4055_);
v___x_4057_ = v___x_4048_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_val_4055_);
v___x_4057_ = v_reuseFailAlloc_4058_;
goto v_reusejp_4056_;
}
v_reusejp_4056_:
{
return v___x_4057_;
}
}
}
}
else
{
lean_object* v_a_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4067_; 
v_a_4060_ = lean_ctor_get(v___x_4045_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4062_ = v___x_4045_;
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_a_4060_);
lean_dec(v___x_4045_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4067_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4065_; 
if (v_isShared_4063_ == 0)
{
v___x_4065_ = v___x_4062_;
goto v_reusejp_4064_;
}
else
{
lean_object* v_reuseFailAlloc_4066_; 
v_reuseFailAlloc_4066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4066_, 0, v_a_4060_);
v___x_4065_ = v_reuseFailAlloc_4066_;
goto v_reusejp_4064_;
}
v_reusejp_4064_:
{
return v___x_4065_;
}
}
}
}
}
}
else
{
lean_object* v_a_4069_; lean_object* v___x_4071_; uint8_t v_isShared_4072_; uint8_t v_isSharedCheck_4076_; 
lean_dec(v_mvarId_4021_);
v_a_4069_ = lean_ctor_get(v___x_4031_, 0);
v_isSharedCheck_4076_ = !lean_is_exclusive(v___x_4031_);
if (v_isSharedCheck_4076_ == 0)
{
v___x_4071_ = v___x_4031_;
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
else
{
lean_inc(v_a_4069_);
lean_dec(v___x_4031_);
v___x_4071_ = lean_box(0);
v_isShared_4072_ = v_isSharedCheck_4076_;
goto v_resetjp_4070_;
}
v_resetjp_4070_:
{
lean_object* v___x_4074_; 
if (v_isShared_4072_ == 0)
{
v___x_4074_ = v___x_4071_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4075_; 
v_reuseFailAlloc_4075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4075_, 0, v_a_4069_);
v___x_4074_ = v_reuseFailAlloc_4075_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
return v___x_4074_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0___boxed(lean_object* v_mvarId_4077_, lean_object* v_t_4078_, lean_object* v_init_4079_, lean_object* v___y_4080_, lean_object* v___y_4081_, lean_object* v___y_4082_, lean_object* v___y_4083_, lean_object* v___y_4084_){
_start:
{
lean_object* v_res_4085_; 
v_res_4085_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4077_, v_t_4078_, v_init_4079_, v___y_4080_, v___y_4081_, v___y_4082_, v___y_4083_);
lean_dec(v___y_4083_);
lean_dec_ref(v___y_4082_);
lean_dec(v___y_4081_);
lean_dec_ref(v___y_4080_);
lean_dec_ref(v_t_4078_);
return v_res_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0(lean_object* v_mvarId_4089_, lean_object* v___y_4090_, lean_object* v___y_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_){
_start:
{
lean_object* v_lctx_4095_; lean_object* v_decls_4096_; lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; 
v_lctx_4095_ = lean_ctor_get(v___y_4090_, 2);
v_decls_4096_ = lean_ctor_get(v_lctx_4095_, 1);
v___x_4097_ = lean_box(0);
v___x_4098_ = ((lean_object*)(l_Lean_Meta_substSomeVar_x3f___lam__0___closed__0));
v___x_4099_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_substSomeVar_x3f_spec__0(v_mvarId_4089_, v_decls_4096_, v___x_4098_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4102_; uint8_t v_isShared_4103_; uint8_t v_isSharedCheck_4112_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4112_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4112_ == 0)
{
v___x_4102_ = v___x_4099_;
v_isShared_4103_ = v_isSharedCheck_4112_;
goto v_resetjp_4101_;
}
else
{
lean_inc(v_a_4100_);
lean_dec(v___x_4099_);
v___x_4102_ = lean_box(0);
v_isShared_4103_ = v_isSharedCheck_4112_;
goto v_resetjp_4101_;
}
v_resetjp_4101_:
{
lean_object* v_fst_4104_; 
v_fst_4104_ = lean_ctor_get(v_a_4100_, 0);
lean_inc(v_fst_4104_);
lean_dec(v_a_4100_);
if (lean_obj_tag(v_fst_4104_) == 0)
{
lean_object* v___x_4106_; 
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v___x_4097_);
v___x_4106_ = v___x_4102_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4107_; 
v_reuseFailAlloc_4107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4107_, 0, v___x_4097_);
v___x_4106_ = v_reuseFailAlloc_4107_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
return v___x_4106_;
}
}
else
{
lean_object* v_val_4108_; lean_object* v___x_4110_; 
v_val_4108_ = lean_ctor_get(v_fst_4104_, 0);
lean_inc(v_val_4108_);
lean_dec_ref_known(v_fst_4104_, 1);
if (v_isShared_4103_ == 0)
{
lean_ctor_set(v___x_4102_, 0, v_val_4108_);
v___x_4110_ = v___x_4102_;
goto v_reusejp_4109_;
}
else
{
lean_object* v_reuseFailAlloc_4111_; 
v_reuseFailAlloc_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4111_, 0, v_val_4108_);
v___x_4110_ = v_reuseFailAlloc_4111_;
goto v_reusejp_4109_;
}
v_reusejp_4109_:
{
return v___x_4110_;
}
}
}
}
else
{
lean_object* v_a_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4120_; 
v_a_4113_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4120_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4120_ == 0)
{
v___x_4115_ = v___x_4099_;
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_a_4113_);
lean_dec(v___x_4099_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4120_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4118_; 
if (v_isShared_4116_ == 0)
{
v___x_4118_ = v___x_4115_;
goto v_reusejp_4117_;
}
else
{
lean_object* v_reuseFailAlloc_4119_; 
v_reuseFailAlloc_4119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4119_, 0, v_a_4113_);
v___x_4118_ = v_reuseFailAlloc_4119_;
goto v_reusejp_4117_;
}
v_reusejp_4117_:
{
return v___x_4118_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___lam__0___boxed(lean_object* v_mvarId_4121_, lean_object* v___y_4122_, lean_object* v___y_4123_, lean_object* v___y_4124_, lean_object* v___y_4125_, lean_object* v___y_4126_){
_start:
{
lean_object* v_res_4127_; 
v_res_4127_ = l_Lean_Meta_substSomeVar_x3f___lam__0(v_mvarId_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_);
lean_dec(v___y_4125_);
lean_dec_ref(v___y_4124_);
lean_dec(v___y_4123_);
lean_dec_ref(v___y_4122_);
return v_res_4127_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f(lean_object* v_mvarId_4128_, lean_object* v_a_4129_, lean_object* v_a_4130_, lean_object* v_a_4131_, lean_object* v_a_4132_){
_start:
{
lean_object* v___f_4134_; lean_object* v___x_4135_; 
lean_inc(v_mvarId_4128_);
v___f_4134_ = lean_alloc_closure((void*)(l_Lean_Meta_substSomeVar_x3f___lam__0___boxed), 6, 1);
lean_closure_set(v___f_4134_, 0, v_mvarId_4128_);
v___x_4135_ = l_Lean_MVarId_withContext___at___00Lean_Meta_substCore_spec__7___redArg(v_mvarId_4128_, v___f_4134_, v_a_4129_, v_a_4130_, v_a_4131_, v_a_4132_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substSomeVar_x3f___boxed(lean_object* v_mvarId_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_, lean_object* v_a_4139_, lean_object* v_a_4140_, lean_object* v_a_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4136_, v_a_4137_, v_a_4138_, v_a_4139_, v_a_4140_);
lean_dec(v_a_4140_);
lean_dec_ref(v_a_4139_);
lean_dec(v_a_4138_);
lean_dec_ref(v_a_4137_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars(lean_object* v_mvarId_4143_, lean_object* v_a_4144_, lean_object* v_a_4145_, lean_object* v_a_4146_, lean_object* v_a_4147_){
_start:
{
lean_object* v___x_4149_; 
lean_inc(v_mvarId_4143_);
v___x_4149_ = l_Lean_Meta_substSomeVar_x3f(v_mvarId_4143_, v_a_4144_, v_a_4145_, v_a_4146_, v_a_4147_);
if (lean_obj_tag(v___x_4149_) == 0)
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4159_; 
v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4152_ = v___x_4149_;
v_isShared_4153_ = v_isSharedCheck_4159_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4149_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4159_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
if (lean_obj_tag(v_a_4150_) == 1)
{
lean_object* v_val_4154_; 
lean_del_object(v___x_4152_);
lean_dec(v_mvarId_4143_);
v_val_4154_ = lean_ctor_get(v_a_4150_, 0);
lean_inc(v_val_4154_);
lean_dec_ref_known(v_a_4150_, 1);
v_mvarId_4143_ = v_val_4154_;
goto _start;
}
else
{
lean_object* v___x_4157_; 
lean_dec(v_a_4150_);
if (v_isShared_4153_ == 0)
{
lean_ctor_set(v___x_4152_, 0, v_mvarId_4143_);
v___x_4157_ = v___x_4152_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_mvarId_4143_);
v___x_4157_ = v_reuseFailAlloc_4158_;
goto v_reusejp_4156_;
}
v_reusejp_4156_:
{
return v___x_4157_;
}
}
}
}
else
{
lean_object* v_a_4160_; lean_object* v___x_4162_; uint8_t v_isShared_4163_; uint8_t v_isSharedCheck_4167_; 
lean_dec(v_mvarId_4143_);
v_a_4160_ = lean_ctor_get(v___x_4149_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4149_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4149_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4149_);
v___x_4162_ = lean_box(0);
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
v_resetjp_4161_:
{
lean_object* v___x_4165_; 
if (v_isShared_4163_ == 0)
{
v___x_4165_ = v___x_4162_;
goto v_reusejp_4164_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v_a_4160_);
v___x_4165_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4164_;
}
v_reusejp_4164_:
{
return v___x_4165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_substVars___boxed(lean_object* v_mvarId_4168_, lean_object* v_a_4169_, lean_object* v_a_4170_, lean_object* v_a_4171_, lean_object* v_a_4172_, lean_object* v_a_4173_){
_start:
{
lean_object* v_res_4174_; 
v_res_4174_ = l_Lean_Meta_substVars(v_mvarId_4168_, v_a_4169_, v_a_4170_, v_a_4171_, v_a_4172_);
lean_dec(v_a_4172_);
lean_dec_ref(v_a_4171_);
lean_dec(v_a_4170_);
lean_dec_ref(v_a_4169_);
return v_res_4174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4237_; uint8_t v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; 
v___x_4237_ = ((lean_object*)(l_Lean_Meta_substCore___lam__3___closed__22));
v___x_4238_ = 0;
v___x_4239_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_));
v___x_4240_ = l_Lean_registerTraceClass(v___x_4237_, v___x_4238_, v___x_4239_);
return v___x_4240_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2____boxed(lean_object* v_a_4241_){
_start:
{
lean_object* v_res_4242_; 
v_res_4242_ = l___private_Lean_Meta_Tactic_Subst_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Subst_1630641459____hygCtx___hyg_2_();
return v_res_4242_;
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
