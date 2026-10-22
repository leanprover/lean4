// Lean compiler output
// Module: Lean.Meta.Tactic.Contradiction
// Imports: public import Lean.Meta.Tactic.Assumption public import Lean.Meta.Tactic.Cases public import Lean.Meta.Tactic.Apply import Lean.Meta.HasNotBit import Lean.Meta.Tactic.Simp.Rewrite
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescope(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isEq(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkHEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqRefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* l_Lean_Meta_hasAssignableMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_cases(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_FVarSubst_apply(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_List_lengthTR___redArg(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_refutableHasNotBit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNe_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchNot_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_findLocalDeclWithType_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_find_expr(lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Meta_saveState___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateRefT_x27_lift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "elim"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1_value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(51, 114, 54, 50, 40, 156, 62, 47)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0_value;
static const lean_closure_object l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_saveState___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1_value;
static const lean_closure_object l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*5, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_StateRefT_x27_lift___boxed, .m_arity = 6, .m_num_fixed = 5, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__1_value)} };
static const lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2_value;
static const lean_ctor_object l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__2_value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__0_value)}};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0_value;
static const lean_array_object l_Lean_Meta_ElimEmptyInductive_elim___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__0 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + sizeof(size_t)*1, .m_other = 0, .m_tag = 0}, .m_objs = {(lean_object*)(size_t)(0ULL)}};
LEAN_EXPORT const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "contradiction"};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__3 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__3_value;
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__2 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__2_value;
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Meta"};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__1 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value;
static const lean_ctor_object l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value),LEAN_SCALAR_PTR_LITERAL(211, 174, 49, 251, 64, 24, 251, 1)}};
static const lean_ctor_object l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value_aux_0),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__2_value),LEAN_SCALAR_PTR_LITERAL(194, 95, 140, 15, 16, 100, 236, 219)}};
static const lean_ctor_object l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value_aux_1),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__3_value),LEAN_SCALAR_PTR_LITERAL(100, 147, 90, 76, 177, 67, 155, 92)}};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__4 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__4_value;
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__5 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__5_value;
static const lean_ctor_object l_Lean_Meta_ElimEmptyInductive_elim___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__6 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__6_value;
static lean_once_cell_t l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__7;
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 38, .m_capacity = 38, .m_length = 37, .m_data = "elimEmptyInductive, number subgoals: "};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_ElimEmptyInductive_elim___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "elimEmptyInductive out-of-fuel"};
static const lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__8 = (const lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__8_value;
static lean_once_cell_t l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_ElimEmptyInductive_elim___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_mkGenDiseqMask___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_mkGenDiseqMask___closed__0 = (const lean_object*)&l_Lean_Meta_mkGenDiseqMask___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___redArg___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Lean.Meta.Tactic.Contradiction"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "_private.Lean.Meta.Tactic.Contradiction.0.Lean.Meta.processGenDiseq"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "assertion violation: isGenDiseq localDecl.type\n  "};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2 = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2_value;
static lean_once_cell_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bool"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__1_value),LEAN_SCALAR_PTR_LITERAL(250, 44, 198, 216, 184, 195, 199, 178)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3_value_aux_0),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(117, 151, 161, 190, 111, 237, 188, 218)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "of_decide_eq_false"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__4_value),LEAN_SCALAR_PTR_LITERAL(101, 242, 48, 138, 187, 4, 117, 248)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_MVarId_contradictionCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__3_value),LEAN_SCALAR_PTR_LITERAL(177, 42, 230, 185, 74, 16, 247, 90)}};
static const lean_object* l_Lean_MVarId_contradictionCore___closed__0 = (const lean_object*)&l_Lean_MVarId_contradictionCore___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "_private"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(103, 214, 75, 80, 34, 198, 193, 153)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(90, 18, 126, 130, 18, 214, 172, 143)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value),LEAN_SCALAR_PTR_LITERAL(30, 196, 118, 96, 111, 225, 34, 188)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__2_value),LEAN_SCALAR_PTR_LITERAL(195, 68, 87, 56, 63, 220, 109, 253)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Contradiction"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(46, 99, 155, 115, 190, 254, 84, 130)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(215, 241, 81, 7, 129, 11, 88, 1)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__8_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(234, 199, 235, 149, 198, 6, 20, 106)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__9_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value),LEAN_SCALAR_PTR_LITERAL(78, 78, 37, 212, 63, 127, 41, 250)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "initFn"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__11_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(99, 88, 171, 83, 172, 77, 248, 159)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_@"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__12_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__13_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(86, 220, 174, 134, 139, 23, 35, 78)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__14_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(255, 173, 142, 211, 165, 86, 65, 180)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__15_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__1_value),LEAN_SCALAR_PTR_LITERAL(63, 154, 136, 66, 43, 95, 3, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__16_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Meta_ElimEmptyInductive_elim___closed__2_value),LEAN_SCALAR_PTR_LITERAL(142, 18, 4, 159, 144, 239, 124, 55)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__17_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(215, 255, 49, 161, 212, 67, 91, 246)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__18_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)(((size_t)(911661800) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(54, 37, 52, 164, 114, 188, 198, 209)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "_hygCtx"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__19_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__20_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(17, 78, 196, 57, 182, 60, 174, 81)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_hyg"};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__21_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__22_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(41, 112, 60, 29, 144, 20, 193, 203)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 2}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(84, 54, 65, 98, 52, 12, 188, 139)}};
static const lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(lean_object* v_e_6_){
_start:
{
lean_object* v___x_7_; lean_object* v___x_8_; uint8_t v___x_9_; 
v___x_7_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___closed__2));
v___x_8_ = lean_unsigned_to_nat(2u);
v___x_9_ = l_Lean_Expr_isAppOfArity(v_e_6_, v___x_7_, v___x_8_);
if (v___x_9_ == 0)
{
return v___x_9_;
}
else
{
lean_object* v___x_10_; uint8_t v___x_11_; 
v___x_10_ = l_Lean_Expr_appArg_x21(v_e_6_);
v___x_11_ = l_Lean_Expr_hasLooseBVars(v___x_10_);
lean_dec_ref(v___x_10_);
if (v___x_11_ == 0)
{
return v___x_9_;
}
else
{
uint8_t v___x_12_; 
v___x_12_ = 0;
return v___x_12_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0___boxed(lean_object* v_e_13_){
_start:
{
uint8_t v_res_14_; lean_object* v_r_15_; 
v_res_14_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___lam__0(v_e_13_);
lean_dec_ref(v_e_13_);
v_r_15_ = lean_box(v_res_14_);
return v_r_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_16_, lean_object* v_x_17_, lean_object* v_x_18_, lean_object* v_x_19_){
_start:
{
lean_object* v_ks_20_; lean_object* v_vs_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_45_; 
v_ks_20_ = lean_ctor_get(v_x_16_, 0);
v_vs_21_ = lean_ctor_get(v_x_16_, 1);
v_isSharedCheck_45_ = !lean_is_exclusive(v_x_16_);
if (v_isSharedCheck_45_ == 0)
{
v___x_23_ = v_x_16_;
v_isShared_24_ = v_isSharedCheck_45_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_vs_21_);
lean_inc(v_ks_20_);
lean_dec(v_x_16_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_45_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_25_; uint8_t v___x_26_; 
v___x_25_ = lean_array_get_size(v_ks_20_);
v___x_26_ = lean_nat_dec_lt(v_x_17_, v___x_25_);
if (v___x_26_ == 0)
{
lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_30_; 
lean_dec(v_x_17_);
v___x_27_ = lean_array_push(v_ks_20_, v_x_18_);
v___x_28_ = lean_array_push(v_vs_21_, v_x_19_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v___x_28_);
lean_ctor_set(v___x_23_, 0, v___x_27_);
v___x_30_ = v___x_23_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v___x_27_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
else
{
lean_object* v_k_x27_32_; uint8_t v___x_33_; 
v_k_x27_32_ = lean_array_fget_borrowed(v_ks_20_, v_x_17_);
v___x_33_ = l_Lean_instBEqMVarId_beq(v_x_18_, v_k_x27_32_);
if (v___x_33_ == 0)
{
lean_object* v___x_35_; 
if (v_isShared_24_ == 0)
{
v___x_35_ = v___x_23_;
goto v_reusejp_34_;
}
else
{
lean_object* v_reuseFailAlloc_39_; 
v_reuseFailAlloc_39_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_39_, 0, v_ks_20_);
lean_ctor_set(v_reuseFailAlloc_39_, 1, v_vs_21_);
v___x_35_ = v_reuseFailAlloc_39_;
goto v_reusejp_34_;
}
v_reusejp_34_:
{
lean_object* v___x_36_; lean_object* v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(1u);
v___x_37_ = lean_nat_add(v_x_17_, v___x_36_);
lean_dec(v_x_17_);
v_x_16_ = v___x_35_;
v_x_17_ = v___x_37_;
goto _start;
}
}
else
{
lean_object* v___x_40_; lean_object* v___x_41_; lean_object* v___x_43_; 
v___x_40_ = lean_array_fset(v_ks_20_, v_x_17_, v_x_18_);
v___x_41_ = lean_array_fset(v_vs_21_, v_x_17_, v_x_19_);
lean_dec(v_x_17_);
if (v_isShared_24_ == 0)
{
lean_ctor_set(v___x_23_, 1, v___x_41_);
lean_ctor_set(v___x_23_, 0, v___x_40_);
v___x_43_ = v___x_23_;
goto v_reusejp_42_;
}
else
{
lean_object* v_reuseFailAlloc_44_; 
v_reuseFailAlloc_44_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_44_, 0, v___x_40_);
lean_ctor_set(v_reuseFailAlloc_44_, 1, v___x_41_);
v___x_43_ = v_reuseFailAlloc_44_;
goto v_reusejp_42_;
}
v_reusejp_42_:
{
return v___x_43_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_46_, lean_object* v_k_47_, lean_object* v_v_48_){
_start:
{
lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___x_50_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_46_, v___x_49_, v_k_47_, v_v_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_51_; 
v___x_51_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(lean_object* v_x_52_, size_t v_x_53_, size_t v_x_54_, lean_object* v_x_55_, lean_object* v_x_56_){
_start:
{
if (lean_obj_tag(v_x_52_) == 0)
{
lean_object* v_es_57_; size_t v___x_58_; size_t v___x_59_; lean_object* v_j_60_; lean_object* v___x_61_; uint8_t v___x_62_; 
v_es_57_ = lean_ctor_get(v_x_52_, 0);
v___x_58_ = ((size_t)31ULL);
v___x_59_ = lean_usize_land(v_x_53_, v___x_58_);
v_j_60_ = lean_usize_to_nat(v___x_59_);
v___x_61_ = lean_array_get_size(v_es_57_);
v___x_62_ = lean_nat_dec_lt(v_j_60_, v___x_61_);
if (v___x_62_ == 0)
{
lean_dec(v_j_60_);
lean_dec(v_x_56_);
lean_dec(v_x_55_);
return v_x_52_;
}
else
{
lean_object* v___x_64_; uint8_t v_isShared_65_; uint8_t v_isSharedCheck_101_; 
lean_inc_ref(v_es_57_);
v_isSharedCheck_101_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_101_ == 0)
{
lean_object* v_unused_102_; 
v_unused_102_ = lean_ctor_get(v_x_52_, 0);
lean_dec(v_unused_102_);
v___x_64_ = v_x_52_;
v_isShared_65_ = v_isSharedCheck_101_;
goto v_resetjp_63_;
}
else
{
lean_dec(v_x_52_);
v___x_64_ = lean_box(0);
v_isShared_65_ = v_isSharedCheck_101_;
goto v_resetjp_63_;
}
v_resetjp_63_:
{
lean_object* v_v_66_; lean_object* v___x_67_; lean_object* v_xs_x27_68_; lean_object* v___y_70_; 
v_v_66_ = lean_array_fget(v_es_57_, v_j_60_);
v___x_67_ = lean_box(0);
v_xs_x27_68_ = lean_array_fset(v_es_57_, v_j_60_, v___x_67_);
switch(lean_obj_tag(v_v_66_))
{
case 0:
{
lean_object* v_key_75_; lean_object* v_val_76_; lean_object* v___x_78_; uint8_t v_isShared_79_; uint8_t v_isSharedCheck_86_; 
v_key_75_ = lean_ctor_get(v_v_66_, 0);
v_val_76_ = lean_ctor_get(v_v_66_, 1);
v_isSharedCheck_86_ = !lean_is_exclusive(v_v_66_);
if (v_isSharedCheck_86_ == 0)
{
v___x_78_ = v_v_66_;
v_isShared_79_ = v_isSharedCheck_86_;
goto v_resetjp_77_;
}
else
{
lean_inc(v_val_76_);
lean_inc(v_key_75_);
lean_dec(v_v_66_);
v___x_78_ = lean_box(0);
v_isShared_79_ = v_isSharedCheck_86_;
goto v_resetjp_77_;
}
v_resetjp_77_:
{
uint8_t v___x_80_; 
v___x_80_ = l_Lean_instBEqMVarId_beq(v_x_55_, v_key_75_);
if (v___x_80_ == 0)
{
lean_object* v___x_81_; lean_object* v___x_82_; 
lean_del_object(v___x_78_);
v___x_81_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_75_, v_val_76_, v_x_55_, v_x_56_);
v___x_82_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_82_, 0, v___x_81_);
v___y_70_ = v___x_82_;
goto v___jp_69_;
}
else
{
lean_object* v___x_84_; 
lean_dec(v_val_76_);
lean_dec(v_key_75_);
if (v_isShared_79_ == 0)
{
lean_ctor_set(v___x_78_, 1, v_x_56_);
lean_ctor_set(v___x_78_, 0, v_x_55_);
v___x_84_ = v___x_78_;
goto v_reusejp_83_;
}
else
{
lean_object* v_reuseFailAlloc_85_; 
v_reuseFailAlloc_85_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_85_, 0, v_x_55_);
lean_ctor_set(v_reuseFailAlloc_85_, 1, v_x_56_);
v___x_84_ = v_reuseFailAlloc_85_;
goto v_reusejp_83_;
}
v_reusejp_83_:
{
v___y_70_ = v___x_84_;
goto v___jp_69_;
}
}
}
}
case 1:
{
lean_object* v_node_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_99_; 
v_node_87_ = lean_ctor_get(v_v_66_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v_v_66_);
if (v_isSharedCheck_99_ == 0)
{
v___x_89_ = v_v_66_;
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_node_87_);
lean_dec(v_v_66_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_91_ = ((size_t)5ULL);
v___x_92_ = lean_usize_shift_right(v_x_53_, v___x_91_);
v___x_93_ = ((size_t)1ULL);
v___x_94_ = lean_usize_add(v_x_54_, v___x_93_);
v___x_95_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_node_87_, v___x_92_, v___x_94_, v_x_55_, v_x_56_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v___x_95_);
v___x_97_ = v___x_89_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
v___y_70_ = v___x_97_;
goto v___jp_69_;
}
}
}
default: 
{
lean_object* v___x_100_; 
v___x_100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_100_, 0, v_x_55_);
lean_ctor_set(v___x_100_, 1, v_x_56_);
v___y_70_ = v___x_100_;
goto v___jp_69_;
}
}
v___jp_69_:
{
lean_object* v___x_71_; lean_object* v___x_73_; 
v___x_71_ = lean_array_fset(v_xs_x27_68_, v_j_60_, v___y_70_);
lean_dec(v_j_60_);
if (v_isShared_65_ == 0)
{
lean_ctor_set(v___x_64_, 0, v___x_71_);
v___x_73_ = v___x_64_;
goto v_reusejp_72_;
}
else
{
lean_object* v_reuseFailAlloc_74_; 
v_reuseFailAlloc_74_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_74_, 0, v___x_71_);
v___x_73_ = v_reuseFailAlloc_74_;
goto v_reusejp_72_;
}
v_reusejp_72_:
{
return v___x_73_;
}
}
}
}
}
else
{
lean_object* v_ks_103_; lean_object* v_vs_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_122_; 
v_ks_103_ = lean_ctor_get(v_x_52_, 0);
v_vs_104_ = lean_ctor_get(v_x_52_, 1);
v_isSharedCheck_122_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_122_ == 0)
{
v___x_106_ = v_x_52_;
v_isShared_107_ = v_isSharedCheck_122_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_vs_104_);
lean_inc(v_ks_103_);
lean_dec(v_x_52_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_122_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_109_; 
if (v_isShared_107_ == 0)
{
v___x_109_ = v___x_106_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_121_; 
v_reuseFailAlloc_121_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_121_, 0, v_ks_103_);
lean_ctor_set(v_reuseFailAlloc_121_, 1, v_vs_104_);
v___x_109_ = v_reuseFailAlloc_121_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v_newNode_110_; size_t v___x_111_; uint8_t v___x_112_; 
v_newNode_110_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v___x_109_, v_x_55_, v_x_56_);
v___x_111_ = ((size_t)7ULL);
v___x_112_ = lean_usize_dec_le(v___x_111_, v_x_54_);
if (v___x_112_ == 0)
{
lean_object* v___x_113_; lean_object* v___x_114_; uint8_t v___x_115_; 
v___x_113_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_110_);
v___x_114_ = lean_unsigned_to_nat(4u);
v___x_115_ = lean_nat_dec_lt(v___x_113_, v___x_114_);
lean_dec(v___x_113_);
if (v___x_115_ == 0)
{
lean_object* v_ks_116_; lean_object* v_vs_117_; lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; 
v_ks_116_ = lean_ctor_get(v_newNode_110_, 0);
lean_inc_ref(v_ks_116_);
v_vs_117_ = lean_ctor_get(v_newNode_110_, 1);
lean_inc_ref(v_vs_117_);
lean_dec_ref(v_newNode_110_);
v___x_118_ = lean_unsigned_to_nat(0u);
v___x_119_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_120_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_x_54_, v_ks_116_, v_vs_117_, v___x_118_, v___x_119_);
lean_dec_ref(v_vs_117_);
lean_dec_ref(v_ks_116_);
return v___x_120_;
}
else
{
return v_newNode_110_;
}
}
else
{
return v_newNode_110_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_123_, lean_object* v_keys_124_, lean_object* v_vals_125_, lean_object* v_i_126_, lean_object* v_entries_127_){
_start:
{
lean_object* v___x_128_; uint8_t v___x_129_; 
v___x_128_ = lean_array_get_size(v_keys_124_);
v___x_129_ = lean_nat_dec_lt(v_i_126_, v___x_128_);
if (v___x_129_ == 0)
{
lean_dec(v_i_126_);
return v_entries_127_;
}
else
{
lean_object* v_k_130_; lean_object* v_v_131_; uint64_t v___x_132_; size_t v_h_133_; size_t v___x_134_; lean_object* v___x_135_; size_t v___x_136_; size_t v___x_137_; size_t v___x_138_; size_t v_h_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v_k_130_ = lean_array_fget_borrowed(v_keys_124_, v_i_126_);
v_v_131_ = lean_array_fget_borrowed(v_vals_125_, v_i_126_);
v___x_132_ = l_Lean_instHashableMVarId_hash(v_k_130_);
v_h_133_ = lean_uint64_to_usize(v___x_132_);
v___x_134_ = ((size_t)5ULL);
v___x_135_ = lean_unsigned_to_nat(1u);
v___x_136_ = ((size_t)1ULL);
v___x_137_ = lean_usize_sub(v_depth_123_, v___x_136_);
v___x_138_ = lean_usize_mul(v___x_134_, v___x_137_);
v_h_139_ = lean_usize_shift_right(v_h_133_, v___x_138_);
v___x_140_ = lean_nat_add(v_i_126_, v___x_135_);
lean_dec(v_i_126_);
lean_inc(v_v_131_);
lean_inc(v_k_130_);
v___x_141_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_entries_127_, v_h_139_, v_depth_123_, v_k_130_, v_v_131_);
v_i_126_ = v___x_140_;
v_entries_127_ = v___x_141_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_143_, lean_object* v_keys_144_, lean_object* v_vals_145_, lean_object* v_i_146_, lean_object* v_entries_147_){
_start:
{
size_t v_depth_boxed_148_; lean_object* v_res_149_; 
v_depth_boxed_148_ = lean_unbox_usize(v_depth_143_);
lean_dec(v_depth_143_);
v_res_149_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_148_, v_keys_144_, v_vals_145_, v_i_146_, v_entries_147_);
lean_dec_ref(v_vals_145_);
lean_dec_ref(v_keys_144_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_150_, lean_object* v_x_151_, lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_){
_start:
{
size_t v_x_1120__boxed_155_; size_t v_x_1121__boxed_156_; lean_object* v_res_157_; 
v_x_1120__boxed_155_ = lean_unbox_usize(v_x_151_);
lean_dec(v_x_151_);
v_x_1121__boxed_156_ = lean_unbox_usize(v_x_152_);
lean_dec(v_x_152_);
v_res_157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_150_, v_x_1120__boxed_155_, v_x_1121__boxed_156_, v_x_153_, v_x_154_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(lean_object* v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
uint64_t v___x_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v___x_164_; 
v___x_161_ = l_Lean_instHashableMVarId_hash(v_x_159_);
v___x_162_ = lean_uint64_to_usize(v___x_161_);
v___x_163_ = ((size_t)1ULL);
v___x_164_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_158_, v___x_162_, v___x_163_, v_x_159_, v_x_160_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(lean_object* v_mvarId_165_, lean_object* v_val_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; lean_object* v_mctx_170_; lean_object* v_cache_171_; lean_object* v_zetaDeltaFVarIds_172_; lean_object* v_postponed_173_; lean_object* v_diag_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_203_; 
v___x_169_ = lean_st_ref_take(v___y_167_);
v_mctx_170_ = lean_ctor_get(v___x_169_, 0);
v_cache_171_ = lean_ctor_get(v___x_169_, 1);
v_zetaDeltaFVarIds_172_ = lean_ctor_get(v___x_169_, 2);
v_postponed_173_ = lean_ctor_get(v___x_169_, 3);
v_diag_174_ = lean_ctor_get(v___x_169_, 4);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_203_ == 0)
{
v___x_176_ = v___x_169_;
v_isShared_177_ = v_isSharedCheck_203_;
goto v_resetjp_175_;
}
else
{
lean_inc(v_diag_174_);
lean_inc(v_postponed_173_);
lean_inc(v_zetaDeltaFVarIds_172_);
lean_inc(v_cache_171_);
lean_inc(v_mctx_170_);
lean_dec(v___x_169_);
v___x_176_ = lean_box(0);
v_isShared_177_ = v_isSharedCheck_203_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_depth_178_; lean_object* v_levelAssignDepth_179_; lean_object* v_lmvarCounter_180_; lean_object* v_mvarCounter_181_; lean_object* v_lDecls_182_; lean_object* v_decls_183_; lean_object* v_userNames_184_; lean_object* v_lAssignment_185_; lean_object* v_eAssignment_186_; lean_object* v_dAssignment_187_; lean_object* v_synthNormMemo_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_202_; 
v_depth_178_ = lean_ctor_get(v_mctx_170_, 0);
v_levelAssignDepth_179_ = lean_ctor_get(v_mctx_170_, 1);
v_lmvarCounter_180_ = lean_ctor_get(v_mctx_170_, 2);
v_mvarCounter_181_ = lean_ctor_get(v_mctx_170_, 3);
v_lDecls_182_ = lean_ctor_get(v_mctx_170_, 4);
v_decls_183_ = lean_ctor_get(v_mctx_170_, 5);
v_userNames_184_ = lean_ctor_get(v_mctx_170_, 6);
v_lAssignment_185_ = lean_ctor_get(v_mctx_170_, 7);
v_eAssignment_186_ = lean_ctor_get(v_mctx_170_, 8);
v_dAssignment_187_ = lean_ctor_get(v_mctx_170_, 9);
v_synthNormMemo_188_ = lean_ctor_get(v_mctx_170_, 10);
v_isSharedCheck_202_ = !lean_is_exclusive(v_mctx_170_);
if (v_isSharedCheck_202_ == 0)
{
v___x_190_ = v_mctx_170_;
v_isShared_191_ = v_isSharedCheck_202_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_synthNormMemo_188_);
lean_inc(v_dAssignment_187_);
lean_inc(v_eAssignment_186_);
lean_inc(v_lAssignment_185_);
lean_inc(v_userNames_184_);
lean_inc(v_decls_183_);
lean_inc(v_lDecls_182_);
lean_inc(v_mvarCounter_181_);
lean_inc(v_lmvarCounter_180_);
lean_inc(v_levelAssignDepth_179_);
lean_inc(v_depth_178_);
lean_dec(v_mctx_170_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_202_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_192_ = lean_box(0);
v___x_193_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_186_, v_mvarId_165_, v_val_166_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 8, v___x_193_);
v___x_195_ = v___x_190_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v_depth_178_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_levelAssignDepth_179_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_lmvarCounter_180_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_mvarCounter_181_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_lDecls_182_);
lean_ctor_set(v_reuseFailAlloc_201_, 5, v_decls_183_);
lean_ctor_set(v_reuseFailAlloc_201_, 6, v_userNames_184_);
lean_ctor_set(v_reuseFailAlloc_201_, 7, v_lAssignment_185_);
lean_ctor_set(v_reuseFailAlloc_201_, 8, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_201_, 9, v_dAssignment_187_);
lean_ctor_set(v_reuseFailAlloc_201_, 10, v_synthNormMemo_188_);
v___x_195_ = v_reuseFailAlloc_201_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_195_);
v___x_197_ = v___x_176_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_cache_171_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_zetaDeltaFVarIds_172_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_postponed_173_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_diag_174_);
v___x_197_ = v_reuseFailAlloc_200_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_st_ref_put(v___y_167_, v___x_197_);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_192_);
return v___x_199_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object* v_mvarId_204_, lean_object* v_val_205_, lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_204_, v_val_205_, v___y_206_);
lean_dec(v___y_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object* v_mvarId_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___f_216_; lean_object* v___x_217_; 
v___f_216_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
lean_inc(v_mvarId_210_);
v___x_217_ = l_Lean_MVarId_getType(v_mvarId_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_261_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_261_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_261_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_261_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_222_; 
v___x_222_ = lean_find_expr(v___f_216_, v_a_218_);
lean_dec(v_a_218_);
if (lean_obj_tag(v___x_222_) == 1)
{
lean_object* v_val_223_; lean_object* v___x_224_; lean_object* v___x_225_; 
lean_del_object(v___x_220_);
v_val_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_222_, 1);
v___x_224_ = l_Lean_Expr_appArg_x21(v_val_223_);
lean_dec(v_val_223_);
lean_inc(v_mvarId_210_);
v___x_225_ = l_Lean_MVarId_getType(v_mvarId_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_227_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = l_Lean_Meta_mkFalseElim(v_a_226_, v___x_224_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_227_) == 0)
{
lean_object* v_a_228_; lean_object* v___x_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_238_; 
v_a_228_ = lean_ctor_get(v___x_227_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v___x_227_, 1);
v___x_229_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_210_, v_a_228_, v_a_212_);
v_isSharedCheck_238_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_238_ == 0)
{
lean_object* v_unused_239_; 
v_unused_239_ = lean_ctor_get(v___x_229_, 0);
lean_dec(v_unused_239_);
v___x_231_ = v___x_229_;
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
else
{
lean_dec(v___x_229_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_238_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
uint8_t v___x_233_; lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_233_ = 1;
v___x_234_ = lean_box(v___x_233_);
if (v_isShared_232_ == 0)
{
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_236_ = v___x_231_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_237_; 
v_reuseFailAlloc_237_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_237_, 0, v___x_234_);
v___x_236_ = v_reuseFailAlloc_237_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
return v___x_236_;
}
}
}
else
{
lean_object* v_a_240_; lean_object* v___x_242_; uint8_t v_isShared_243_; uint8_t v_isSharedCheck_247_; 
lean_dec(v_mvarId_210_);
v_a_240_ = lean_ctor_get(v___x_227_, 0);
v_isSharedCheck_247_ = !lean_is_exclusive(v___x_227_);
if (v_isSharedCheck_247_ == 0)
{
v___x_242_ = v___x_227_;
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
else
{
lean_inc(v_a_240_);
lean_dec(v___x_227_);
v___x_242_ = lean_box(0);
v_isShared_243_ = v_isSharedCheck_247_;
goto v_resetjp_241_;
}
v_resetjp_241_:
{
lean_object* v___x_245_; 
if (v_isShared_243_ == 0)
{
v___x_245_ = v___x_242_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_a_240_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
}
}
else
{
lean_object* v_a_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_255_; 
lean_dec_ref(v___x_224_);
lean_dec(v_mvarId_210_);
v_a_248_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_225_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_225_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_251_ == 0)
{
v___x_253_ = v___x_250_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_a_248_);
v___x_253_ = v_reuseFailAlloc_254_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
return v___x_253_;
}
}
}
}
else
{
uint8_t v___x_256_; lean_object* v___x_257_; lean_object* v___x_259_; 
lean_dec(v___x_222_);
lean_dec(v_mvarId_210_);
v___x_256_ = 0;
v___x_257_ = lean_box(v___x_256_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_257_);
v___x_259_ = v___x_220_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_257_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
else
{
lean_object* v_a_262_; lean_object* v___x_264_; uint8_t v_isShared_265_; uint8_t v_isSharedCheck_269_; 
lean_dec(v_mvarId_210_);
v_a_262_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_217_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_217_);
v___x_264_ = lean_box(0);
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
v_resetjp_263_:
{
lean_object* v___x_267_; 
if (v_isShared_265_ == 0)
{
v___x_267_ = v___x_264_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_a_262_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___boxed(lean_object* v_mvarId_270_, lean_object* v_a_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_270_, v_a_271_, v_a_272_, v_a_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
lean_dec(v_a_272_);
lean_dec_ref(v_a_271_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object* v_mvarId_277_, lean_object* v_val_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_){
_start:
{
lean_object* v___x_284_; 
v___x_284_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_277_, v_val_278_, v___y_280_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object* v_mvarId_285_, lean_object* v_val_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(v_mvarId_285_, v_val_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0(lean_object* v_00_u03b2_293_, lean_object* v_x_294_, lean_object* v_x_295_, lean_object* v_x_296_){
_start:
{
lean_object* v___x_297_; 
v___x_297_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_x_294_, v_x_295_, v_x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_298_, lean_object* v_x_299_, size_t v_x_300_, size_t v_x_301_, lean_object* v_x_302_, lean_object* v_x_303_){
_start:
{
lean_object* v___x_304_; 
v___x_304_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_299_, v_x_300_, v_x_301_, v_x_302_, v_x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_305_, lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_){
_start:
{
size_t v_x_1471__boxed_311_; size_t v_x_1472__boxed_312_; lean_object* v_res_313_; 
v_x_1471__boxed_311_ = lean_unbox_usize(v_x_307_);
lean_dec(v_x_307_);
v_x_1472__boxed_312_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_res_313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_305_, v_x_306_, v_x_1471__boxed_311_, v_x_1472__boxed_312_, v_x_309_, v_x_310_);
return v_res_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_314_, lean_object* v_n_315_, lean_object* v_k_316_, lean_object* v_v_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v_n_315_, v_k_316_, v_v_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_319_, size_t v_depth_320_, lean_object* v_keys_321_, lean_object* v_vals_322_, lean_object* v_heq_323_, lean_object* v_i_324_, lean_object* v_entries_325_){
_start:
{
lean_object* v___x_326_; 
v___x_326_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_320_, v_keys_321_, v_vals_322_, v_i_324_, v_entries_325_);
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_327_, lean_object* v_depth_328_, lean_object* v_keys_329_, lean_object* v_vals_330_, lean_object* v_heq_331_, lean_object* v_i_332_, lean_object* v_entries_333_){
_start:
{
size_t v_depth_boxed_334_; lean_object* v_res_335_; 
v_depth_boxed_334_ = lean_unbox_usize(v_depth_328_);
lean_dec(v_depth_328_);
v_res_335_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_327_, v_depth_boxed_334_, v_keys_329_, v_vals_330_, v_heq_331_, v_i_332_, v_entries_333_);
lean_dec_ref(v_vals_330_);
lean_dec_ref(v_keys_329_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_336_, lean_object* v_x_337_, lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_337_, v_x_338_, v_x_339_, v_x_340_);
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object* v_fvarId_342_, lean_object* v_a_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Lean_FVarId_getType___redArg(v_fvarId_342_, v_a_343_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_352_) == 0)
{
lean_object* v_a_353_; lean_object* v___x_354_; 
v_a_353_ = lean_ctor_get(v___x_352_, 0);
lean_inc(v_a_353_);
lean_dec_ref_known(v___x_352_, 1);
v___x_354_ = l_Lean_Meta_whnfD(v_a_353_, v_a_343_, v_a_344_, v_a_345_, v_a_346_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_357_; uint8_t v_isShared_358_; uint8_t v_isSharedCheck_381_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_381_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_381_ == 0)
{
v___x_357_ = v___x_354_;
v_isShared_358_ = v_isSharedCheck_381_;
goto v_resetjp_356_;
}
else
{
lean_inc(v_a_355_);
lean_dec(v___x_354_);
v___x_357_ = lean_box(0);
v_isShared_358_ = v_isSharedCheck_381_;
goto v_resetjp_356_;
}
v_resetjp_356_:
{
lean_object* v___x_359_; 
v___x_359_ = l_Lean_Expr_getAppFn(v_a_355_);
lean_dec(v_a_355_);
if (lean_obj_tag(v___x_359_) == 4)
{
lean_object* v_declName_360_; lean_object* v___x_361_; lean_object* v_env_362_; uint8_t v___x_363_; lean_object* v___x_364_; 
v_declName_360_ = lean_ctor_get(v___x_359_, 0);
lean_inc(v_declName_360_);
lean_dec_ref_known(v___x_359_, 2);
v___x_361_ = lean_st_ref_get(v_a_346_);
v_env_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc_ref(v_env_362_);
lean_dec(v___x_361_);
v___x_363_ = 0;
v___x_364_ = l_Lean_Environment_find_x3f(v_env_362_, v_declName_360_, v___x_363_);
if (lean_obj_tag(v___x_364_) == 0)
{
lean_del_object(v___x_357_);
goto v___jp_348_;
}
else
{
lean_object* v_val_365_; 
v_val_365_ = lean_ctor_get(v___x_364_, 0);
lean_inc(v_val_365_);
lean_dec_ref_known(v___x_364_, 1);
if (lean_obj_tag(v_val_365_) == 5)
{
lean_object* v_val_366_; lean_object* v_numIndices_367_; lean_object* v_ctors_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v_val_366_ = lean_ctor_get(v_val_365_, 0);
lean_inc_ref(v_val_366_);
lean_dec_ref_known(v_val_365_, 1);
v_numIndices_367_ = lean_ctor_get(v_val_366_, 2);
lean_inc(v_numIndices_367_);
v_ctors_368_ = lean_ctor_get(v_val_366_, 4);
lean_inc(v_ctors_368_);
lean_dec_ref(v_val_366_);
v___x_369_ = l_List_lengthTR___redArg(v_ctors_368_);
lean_dec(v_ctors_368_);
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = lean_nat_dec_eq(v___x_369_, v___x_370_);
lean_dec(v___x_369_);
if (v___x_371_ == 0)
{
uint8_t v___x_372_; lean_object* v___x_373_; lean_object* v___x_375_; 
v___x_372_ = lean_nat_dec_lt(v___x_370_, v_numIndices_367_);
lean_dec(v_numIndices_367_);
v___x_373_ = lean_box(v___x_372_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_373_);
v___x_375_ = v___x_357_;
goto v_reusejp_374_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v___x_373_);
v___x_375_ = v_reuseFailAlloc_376_;
goto v_reusejp_374_;
}
v_reusejp_374_:
{
return v___x_375_;
}
}
else
{
lean_object* v___x_377_; lean_object* v___x_379_; 
lean_dec(v_numIndices_367_);
v___x_377_ = lean_box(v___x_371_);
if (v_isShared_358_ == 0)
{
lean_ctor_set(v___x_357_, 0, v___x_377_);
v___x_379_ = v___x_357_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v___x_377_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
else
{
lean_dec(v_val_365_);
lean_del_object(v___x_357_);
goto v___jp_348_;
}
}
}
else
{
lean_dec_ref(v___x_359_);
lean_del_object(v___x_357_);
goto v___jp_348_;
}
}
}
else
{
lean_object* v_a_382_; lean_object* v___x_384_; uint8_t v_isShared_385_; uint8_t v_isSharedCheck_389_; 
v_a_382_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_389_ == 0)
{
v___x_384_ = v___x_354_;
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
else
{
lean_inc(v_a_382_);
lean_dec(v___x_354_);
v___x_384_ = lean_box(0);
v_isShared_385_ = v_isSharedCheck_389_;
goto v_resetjp_383_;
}
v_resetjp_383_:
{
lean_object* v___x_387_; 
if (v_isShared_385_ == 0)
{
v___x_387_ = v___x_384_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v_a_382_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
return v___x_387_;
}
}
}
}
else
{
lean_object* v_a_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_397_; 
v_a_390_ = lean_ctor_get(v___x_352_, 0);
v_isSharedCheck_397_ = !lean_is_exclusive(v___x_352_);
if (v_isSharedCheck_397_ == 0)
{
v___x_392_ = v___x_352_;
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_a_390_);
lean_dec(v___x_352_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_397_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v_a_390_);
v___x_395_ = v_reuseFailAlloc_396_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
return v___x_395_;
}
}
}
v___jp_348_:
{
uint8_t v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_349_ = 0;
v___x_350_ = lean_box(v___x_349_);
v___x_351_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
return v___x_351_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate___boxed(lean_object* v_fvarId_398_, lean_object* v_a_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_398_, v_a_399_, v_a_400_, v_a_401_, v_a_402_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
lean_dec(v_a_400_);
lean_dec_ref(v_a_399_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object* v_s_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v___x_412_; 
v___x_412_ = l_Lean_Meta_SavedState_restore___redArg(v_s_405_, v___y_408_, v___y_410_);
return v___x_412_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object* v_s_413_, lean_object* v___y_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(v_s_413_, v___y_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec(v___y_414_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object* v_x_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_436_; 
lean_inc(v___y_430_);
v___x_436_ = lean_apply_6(v_x_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, lean_box(0));
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object* v_x_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(v_x_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_438_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object* v_mvarId_445_, lean_object* v_x_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___f_453_; lean_object* v___x_454_; 
lean_inc(v___y_447_);
v___f_453_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_453_, 0, v_x_446_);
lean_closure_set(v___f_453_, 1, v___y_447_);
v___x_454_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_445_, v___f_453_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
if (lean_obj_tag(v___x_454_) == 0)
{
return v___x_454_;
}
else
{
lean_object* v_a_455_; lean_object* v___x_457_; uint8_t v_isShared_458_; uint8_t v_isSharedCheck_462_; 
v_a_455_ = lean_ctor_get(v___x_454_, 0);
v_isSharedCheck_462_ = !lean_is_exclusive(v___x_454_);
if (v_isSharedCheck_462_ == 0)
{
v___x_457_ = v___x_454_;
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
else
{
lean_inc(v_a_455_);
lean_dec(v___x_454_);
v___x_457_ = lean_box(0);
v_isShared_458_ = v_isSharedCheck_462_;
goto v_resetjp_456_;
}
v_resetjp_456_:
{
lean_object* v___x_460_; 
if (v_isShared_458_ == 0)
{
v___x_460_ = v___x_457_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_a_455_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
return v___x_460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___boxed(lean_object* v_mvarId_463_, lean_object* v_x_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
lean_object* v_res_471_; 
v_res_471_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_463_, v_x_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
lean_dec_ref(v___y_466_);
lean_dec(v___y_465_);
return v_res_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object* v_00_u03b1_472_, lean_object* v_mvarId_473_, lean_object* v_x_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_){
_start:
{
lean_object* v___x_481_; 
v___x_481_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_473_, v_x_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___boxed(lean_object* v_00_u03b1_482_, lean_object* v_mvarId_483_, lean_object* v_x_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(v_00_u03b1_482_, v_mvarId_483_, v_x_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
lean_dec_ref(v___y_486_);
lean_dec(v___y_485_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object* v_x_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_Meta_saveState___redArg(v___y_495_, v___y_497_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v_a_500_; lean_object* v___y_502_; lean_object* v_a_503_; lean_object* v___x_523_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
lean_inc(v___y_497_);
lean_inc_ref(v___y_496_);
lean_inc(v___y_495_);
lean_inc_ref(v___y_494_);
lean_inc(v___y_493_);
v___x_523_ = lean_apply_6(v_x_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, lean_box(0));
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v_a_524_; uint8_t v___x_525_; 
v_a_524_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_524_);
v___x_525_ = lean_unbox(v_a_524_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; 
lean_dec_ref_known(v___x_523_, 1);
lean_inc(v_a_500_);
v___x_526_ = l_Lean_Meta_SavedState_restore___redArg(v_a_500_, v___y_495_, v___y_497_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_533_; 
lean_dec(v_a_500_);
v_isSharedCheck_533_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_533_ == 0)
{
lean_object* v_unused_534_; 
v_unused_534_ = lean_ctor_get(v___x_526_, 0);
lean_dec(v_unused_534_);
v___x_528_ = v___x_526_;
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
else
{
lean_dec(v___x_526_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_533_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v___x_531_; 
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v_a_524_);
v___x_531_ = v___x_528_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v_a_524_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
lean_object* v_a_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_542_; 
lean_dec(v_a_524_);
v_a_535_ = lean_ctor_get(v___x_526_, 0);
v_isSharedCheck_542_ = !lean_is_exclusive(v___x_526_);
if (v_isSharedCheck_542_ == 0)
{
v___x_537_ = v___x_526_;
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_a_535_);
lean_dec(v___x_526_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_542_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v___x_540_; 
lean_inc(v_a_535_);
if (v_isShared_538_ == 0)
{
v___x_540_ = v___x_537_;
goto v_reusejp_539_;
}
else
{
lean_object* v_reuseFailAlloc_541_; 
v_reuseFailAlloc_541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_541_, 0, v_a_535_);
v___x_540_ = v_reuseFailAlloc_541_;
goto v_reusejp_539_;
}
v_reusejp_539_:
{
v___y_502_ = v___x_540_;
v_a_503_ = v_a_535_;
goto v___jp_501_;
}
}
}
}
else
{
lean_dec(v_a_524_);
lean_dec(v_a_500_);
return v___x_523_;
}
}
else
{
lean_object* v_a_543_; 
v_a_543_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_a_543_);
v___y_502_ = v___x_523_;
v_a_503_ = v_a_543_;
goto v___jp_501_;
}
v___jp_501_:
{
uint8_t v___x_504_; 
v___x_504_ = l_Lean_Exception_isInterrupt(v_a_503_);
if (v___x_504_ == 0)
{
uint8_t v___x_505_; 
lean_inc_ref(v_a_503_);
v___x_505_ = l_Lean_Exception_isRuntime(v_a_503_);
if (v___x_505_ == 0)
{
lean_object* v___x_506_; 
lean_dec_ref(v___y_502_);
v___x_506_ = l_Lean_Meta_SavedState_restore___redArg(v_a_500_, v___y_495_, v___y_497_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_513_; 
v_isSharedCheck_513_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v___x_506_, 0);
lean_dec(v_unused_514_);
v___x_508_ = v___x_506_;
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
else
{
lean_dec(v___x_506_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_513_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_511_; 
if (v_isShared_509_ == 0)
{
lean_ctor_set_tag(v___x_508_, 1);
lean_ctor_set(v___x_508_, 0, v_a_503_);
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v_a_503_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
else
{
lean_object* v_a_515_; lean_object* v___x_517_; uint8_t v_isShared_518_; uint8_t v_isSharedCheck_522_; 
lean_dec_ref(v_a_503_);
v_a_515_ = lean_ctor_get(v___x_506_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_506_);
if (v_isSharedCheck_522_ == 0)
{
v___x_517_ = v___x_506_;
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
else
{
lean_inc(v_a_515_);
lean_dec(v___x_506_);
v___x_517_ = lean_box(0);
v_isShared_518_ = v_isSharedCheck_522_;
goto v_resetjp_516_;
}
v_resetjp_516_:
{
lean_object* v___x_520_; 
if (v_isShared_518_ == 0)
{
v___x_520_ = v___x_517_;
goto v_reusejp_519_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_a_515_);
v___x_520_ = v_reuseFailAlloc_521_;
goto v_reusejp_519_;
}
v_reusejp_519_:
{
return v___x_520_;
}
}
}
}
else
{
lean_dec_ref(v_a_503_);
lean_dec(v_a_500_);
return v___y_502_;
}
}
else
{
lean_dec_ref(v_a_503_);
lean_dec(v_a_500_);
return v___y_502_;
}
}
}
else
{
lean_object* v_a_544_; lean_object* v___x_546_; uint8_t v_isShared_547_; uint8_t v_isSharedCheck_551_; 
lean_dec_ref(v_x_492_);
v_a_544_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_551_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_551_ == 0)
{
v___x_546_ = v___x_499_;
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
else
{
lean_inc(v_a_544_);
lean_dec(v___x_499_);
v___x_546_ = lean_box(0);
v_isShared_547_ = v_isSharedCheck_551_;
goto v_resetjp_545_;
}
v_resetjp_545_:
{
lean_object* v___x_549_; 
if (v_isShared_547_ == 0)
{
v___x_549_ = v___x_546_;
goto v_reusejp_548_;
}
else
{
lean_object* v_reuseFailAlloc_550_; 
v_reuseFailAlloc_550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_550_, 0, v_a_544_);
v___x_549_ = v_reuseFailAlloc_550_;
goto v_reusejp_548_;
}
v_reusejp_548_:
{
return v___x_549_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(lean_object* v_msgData_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v___x_566_; lean_object* v_env_567_; uint8_t v___x_568_; lean_object* v_env_569_; lean_object* v___x_570_; lean_object* v_toCold_571_; lean_object* v_mctx_572_; lean_object* v_lctx_573_; lean_object* v_options_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; 
v___x_566_ = lean_st_ref_get(v___y_564_);
v_env_567_ = lean_ctor_get(v___x_566_, 0);
lean_inc_ref(v_env_567_);
lean_dec(v___x_566_);
v___x_568_ = 0;
v_env_569_ = l_Lean_Environment_setRecordingDeps(v_env_567_, v___x_568_);
v___x_570_ = lean_st_ref_get(v___y_562_);
v_toCold_571_ = lean_ctor_get(v___y_563_, 0);
v_mctx_572_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_mctx_572_);
lean_dec(v___x_570_);
v_lctx_573_ = lean_ctor_get(v___y_561_, 2);
v_options_574_ = lean_ctor_get(v_toCold_571_, 2);
lean_inc_ref(v_options_574_);
lean_inc_ref(v_lctx_573_);
v___x_575_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_575_, 0, v_env_569_);
lean_ctor_set(v___x_575_, 1, v_mctx_572_);
lean_ctor_set(v___x_575_, 2, v_lctx_573_);
lean_ctor_set(v___x_575_, 3, v_options_574_);
v___x_576_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_576_, 0, v___x_575_);
lean_ctor_set(v___x_576_, 1, v_msgData_560_);
v___x_577_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
return v___x_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object* v_msgData_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_){
_start:
{
lean_object* v_res_584_; 
v_res_584_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_578_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
lean_dec(v___y_580_);
lean_dec_ref(v___y_579_);
return v_res_584_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_585_; double v___x_586_; 
v___x_585_ = lean_unsigned_to_nat(0u);
v___x_586_ = lean_float_of_nat(v___x_585_);
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_590_, lean_object* v_msg_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_){
_start:
{
lean_object* v_ref_597_; lean_object* v___x_598_; lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_644_; 
v_ref_597_ = lean_ctor_get(v___y_594_, 2);
v___x_598_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
v_a_599_ = lean_ctor_get(v___x_598_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_598_);
if (v_isSharedCheck_644_ == 0)
{
v___x_601_ = v___x_598_;
v_isShared_602_ = v_isSharedCheck_644_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_598_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_644_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_603_; lean_object* v_traceState_604_; lean_object* v_env_605_; lean_object* v_nextMacroScope_606_; lean_object* v_ngen_607_; lean_object* v_auxDeclNGen_608_; lean_object* v_cache_609_; lean_object* v_recordedDeps_610_; lean_object* v_messages_611_; lean_object* v_infoState_612_; lean_object* v_snapshotTasks_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_643_; 
v___x_603_ = lean_st_ref_take(v___y_595_);
v_traceState_604_ = lean_ctor_get(v___x_603_, 4);
v_env_605_ = lean_ctor_get(v___x_603_, 0);
v_nextMacroScope_606_ = lean_ctor_get(v___x_603_, 1);
v_ngen_607_ = lean_ctor_get(v___x_603_, 2);
v_auxDeclNGen_608_ = lean_ctor_get(v___x_603_, 3);
v_cache_609_ = lean_ctor_get(v___x_603_, 5);
v_recordedDeps_610_ = lean_ctor_get(v___x_603_, 6);
v_messages_611_ = lean_ctor_get(v___x_603_, 7);
v_infoState_612_ = lean_ctor_get(v___x_603_, 8);
v_snapshotTasks_613_ = lean_ctor_get(v___x_603_, 9);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_643_ == 0)
{
v___x_615_ = v___x_603_;
v_isShared_616_ = v_isSharedCheck_643_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_snapshotTasks_613_);
lean_inc(v_infoState_612_);
lean_inc(v_messages_611_);
lean_inc(v_recordedDeps_610_);
lean_inc(v_cache_609_);
lean_inc(v_traceState_604_);
lean_inc(v_auxDeclNGen_608_);
lean_inc(v_ngen_607_);
lean_inc(v_nextMacroScope_606_);
lean_inc(v_env_605_);
lean_dec(v___x_603_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_643_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint64_t v_tid_617_; lean_object* v_traces_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_642_; 
v_tid_617_ = lean_ctor_get_uint64(v_traceState_604_, sizeof(void*)*1);
v_traces_618_ = lean_ctor_get(v_traceState_604_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_traceState_604_);
if (v_isSharedCheck_642_ == 0)
{
v___x_620_ = v_traceState_604_;
v_isShared_621_ = v_isSharedCheck_642_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_traces_618_);
lean_dec(v_traceState_604_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_642_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; lean_object* v___x_623_; double v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_622_ = lean_box(0);
v___x_623_ = lean_box(0);
v___x_624_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_625_ = 0;
v___x_626_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_627_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_627_, 0, v_cls_590_);
lean_ctor_set(v___x_627_, 1, v___x_623_);
lean_ctor_set(v___x_627_, 2, v___x_626_);
lean_ctor_set_float(v___x_627_, sizeof(void*)*3, v___x_624_);
lean_ctor_set_float(v___x_627_, sizeof(void*)*3 + 8, v___x_624_);
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*3 + 16, v___x_625_);
v___x_628_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_629_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v_a_599_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
lean_inc(v_ref_597_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v_ref_597_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_PersistentArray_push___redArg(v_traces_618_, v___x_630_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_631_);
v___x_633_ = v___x_620_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_631_);
lean_ctor_set_uint64(v_reuseFailAlloc_641_, sizeof(void*)*1, v_tid_617_);
v___x_633_ = v_reuseFailAlloc_641_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 4, v___x_633_);
v___x_635_ = v___x_615_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_env_605_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_nextMacroScope_606_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_ngen_607_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v_auxDeclNGen_608_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_640_, 5, v_cache_609_);
lean_ctor_set(v_reuseFailAlloc_640_, 6, v_recordedDeps_610_);
lean_ctor_set(v_reuseFailAlloc_640_, 7, v_messages_611_);
lean_ctor_set(v_reuseFailAlloc_640_, 8, v_infoState_612_);
lean_ctor_set(v_reuseFailAlloc_640_, 9, v_snapshotTasks_613_);
v___x_635_ = v_reuseFailAlloc_640_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_636_ = lean_st_ref_put(v___y_595_, v___x_635_);
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_622_);
v___x_638_ = v___x_601_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_622_);
v___x_638_ = v_reuseFailAlloc_639_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
return v___x_638_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_645_, lean_object* v_msg_646_, lean_object* v___y_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_){
_start:
{
lean_object* v_res_652_; 
v_res_652_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_645_, v_msg_646_, v___y_647_, v___y_648_, v___y_649_, v___y_650_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v___y_648_);
lean_dec_ref(v___y_647_);
return v_res_652_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_660_, lean_object* v_mvarId_661_, lean_object* v_fields_662_, lean_object* v_sz_663_, lean_object* v___x_664_, lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_){
_start:
{
size_t v_sz_boxed_673_; size_t v___x_15984__boxed_674_; uint8_t v___x_15986__boxed_675_; lean_object* v_res_676_; 
v_sz_boxed_673_ = lean_unbox_usize(v_sz_663_);
lean_dec(v_sz_663_);
v___x_15984__boxed_674_ = lean_unbox_usize(v___x_664_);
lean_dec(v___x_664_);
v___x_15986__boxed_675_ = lean_unbox(v___x_666_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_660_, v_mvarId_661_, v_fields_662_, v_sz_boxed_673_, v___x_15984__boxed_674_, v___x_665_, v___x_15986__boxed_675_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v___y_668_);
lean_dec(v___y_667_);
lean_dec_ref(v_fields_662_);
return v_res_676_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_677_, lean_object* v_as_678_, size_t v_sz_679_, size_t v_i_680_, lean_object* v_b_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_){
_start:
{
uint8_t v___x_688_; 
v___x_688_ = lean_usize_dec_lt(v_i_680_, v_sz_679_);
if (v___x_688_ == 0)
{
lean_object* v___x_689_; 
v___x_689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_689_, 0, v_b_681_);
return v___x_689_;
}
else
{
lean_object* v_a_690_; lean_object* v_toInductionSubgoal_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_b_681_);
v_a_690_ = lean_array_uget(v_as_678_, v_i_680_);
v_toInductionSubgoal_691_ = lean_ctor_get(v_a_690_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_a_690_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_a_690_, 1);
lean_dec(v_unused_733_);
v___x_693_ = v_a_690_;
v_isShared_694_ = v_isSharedCheck_732_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_toInductionSubgoal_691_);
lean_dec(v_a_690_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_732_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v_mvarId_695_; lean_object* v_fields_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; uint8_t v___x_700_; size_t v_sz_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___f_705_; lean_object* v___x_706_; 
v_mvarId_695_ = lean_ctor_get(v_toInductionSubgoal_691_, 0);
lean_inc_n(v_mvarId_695_, 2);
v_fields_696_ = lean_ctor_get(v_toInductionSubgoal_691_, 1);
lean_inc_ref(v_fields_696_);
v___x_697_ = lean_box(0);
v___x_698_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = lean_nat_dec_eq(v_val_677_, v___x_699_);
v_sz_701_ = lean_array_size(v_fields_696_);
v___x_702_ = lean_box_usize(v_sz_701_);
v___x_703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_704_ = lean_box(v___x_700_);
v___f_705_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_705_, 0, v_toInductionSubgoal_691_);
lean_closure_set(v___f_705_, 1, v_mvarId_695_);
lean_closure_set(v___f_705_, 2, v_fields_696_);
lean_closure_set(v___f_705_, 3, v___x_702_);
lean_closure_set(v___f_705_, 4, v___x_703_);
lean_closure_set(v___f_705_, 5, v___x_698_);
lean_closure_set(v___f_705_, 6, v___x_704_);
v___x_706_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_695_, v___f_705_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
if (lean_obj_tag(v___x_706_) == 0)
{
lean_object* v_a_707_; lean_object* v___x_709_; uint8_t v_isShared_710_; uint8_t v_isSharedCheck_723_; 
v_a_707_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_723_ == 0)
{
v___x_709_ = v___x_706_;
v_isShared_710_ = v_isSharedCheck_723_;
goto v_resetjp_708_;
}
else
{
lean_inc(v_a_707_);
lean_dec(v___x_706_);
v___x_709_ = lean_box(0);
v_isShared_710_ = v_isSharedCheck_723_;
goto v_resetjp_708_;
}
v_resetjp_708_:
{
uint8_t v___x_711_; 
v___x_711_ = lean_unbox(v_a_707_);
lean_dec(v_a_707_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_715_; 
v___x_712_ = lean_box(v___x_700_);
v___x_713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_713_, 0, v___x_712_);
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v___x_697_);
lean_ctor_set(v___x_693_, 0, v___x_713_);
v___x_715_ = v___x_693_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_713_);
lean_ctor_set(v_reuseFailAlloc_719_, 1, v___x_697_);
v___x_715_ = v_reuseFailAlloc_719_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
lean_object* v___x_717_; 
if (v_isShared_710_ == 0)
{
lean_ctor_set(v___x_709_, 0, v___x_715_);
v___x_717_ = v___x_709_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v___x_715_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
else
{
size_t v___x_720_; size_t v___x_721_; 
lean_del_object(v___x_709_);
lean_del_object(v___x_693_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_add(v_i_680_, v___x_720_);
v_i_680_ = v___x_721_;
v_b_681_ = v___x_698_;
goto _start;
}
}
}
else
{
lean_object* v_a_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_731_; 
lean_del_object(v___x_693_);
v_a_724_ = lean_ctor_get(v___x_706_, 0);
v_isSharedCheck_731_ = !lean_is_exclusive(v___x_706_);
if (v_isSharedCheck_731_ == 0)
{
v___x_726_ = v___x_706_;
v_isShared_727_ = v_isSharedCheck_731_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_a_724_);
lean_dec(v___x_706_);
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
}
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7(void){
_start:
{
lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; 
v___x_744_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_745_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__6));
v___x_746_ = l_Lean_Name_append(v___x_745_, v___x_744_);
return v___x_746_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_749_ = l_Lean_stringToMessageData(v___x_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_750_, lean_object* v_fvarId_751_, lean_object* v___x_752_, uint8_t v___x_753_, lean_object* v___x_754_, lean_object* v_val_755_, uint8_t v___x_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_MVarId_cases(v_mvarId_750_, v_fvarId_751_, v___x_752_, v___x_753_, v___x_754_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_763_) == 0)
{
lean_object* v_a_764_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v_toCold_797_; lean_object* v_options_798_; uint8_t v_hasTrace_799_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v_toCold_797_ = lean_ctor_get(v___y_760_, 0);
v_options_798_ = lean_ctor_get(v_toCold_797_, 2);
v_hasTrace_799_ = lean_ctor_get_uint8(v_options_798_, sizeof(void*)*1);
if (v_hasTrace_799_ == 0)
{
v___y_766_ = v___y_757_;
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
goto v___jp_765_;
}
else
{
lean_object* v_inheritedTraceOptions_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_inheritedTraceOptions_800_ = lean_ctor_get(v_toCold_797_, 11);
v___x_801_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_802_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_803_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_800_, v_options_798_, v___x_802_);
if (v___x_803_ == 0)
{
v___y_766_ = v___y_757_;
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
goto v___jp_765_;
}
else
{
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_804_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_805_ = lean_array_get_size(v_a_764_);
v___x_806_ = l_Nat_reprFast(v___x_805_);
v___x_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = l_Lean_MessageData_ofFormat(v___x_807_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_804_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_801_, v___x_809_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_dec_ref_known(v___x_810_, 1);
v___y_766_ = v___y_757_;
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
goto v___jp_765_;
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_a_764_);
v_a_811_ = lean_ctor_get(v___x_810_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v___x_810_);
if (v_isSharedCheck_818_ == 0)
{
v___x_813_ = v___x_810_;
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_a_811_);
lean_dec(v___x_810_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_818_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_816_; 
if (v_isShared_814_ == 0)
{
v___x_816_ = v___x_813_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v_a_811_);
v___x_816_ = v_reuseFailAlloc_817_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
return v___x_816_;
}
}
}
}
}
v___jp_765_:
{
lean_object* v___x_771_; size_t v_sz_772_; size_t v___x_773_; lean_object* v___x_774_; 
v___x_771_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_772_ = lean_array_size(v_a_764_);
v___x_773_ = ((size_t)0ULL);
v___x_774_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_755_, v_a_764_, v_sz_772_, v___x_773_, v___x_771_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v_a_764_);
if (lean_obj_tag(v___x_774_) == 0)
{
lean_object* v_a_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_788_; 
v_a_775_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_788_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_788_ == 0)
{
v___x_777_ = v___x_774_;
v_isShared_778_ = v_isSharedCheck_788_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_a_775_);
lean_dec(v___x_774_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_788_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_fst_779_; 
v_fst_779_ = lean_ctor_get(v_a_775_, 0);
lean_inc(v_fst_779_);
lean_dec(v_a_775_);
if (lean_obj_tag(v_fst_779_) == 0)
{
lean_object* v___x_780_; lean_object* v___x_782_; 
v___x_780_ = lean_box(v___x_756_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_780_);
v___x_782_ = v___x_777_;
goto v_reusejp_781_;
}
else
{
lean_object* v_reuseFailAlloc_783_; 
v_reuseFailAlloc_783_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_780_);
v___x_782_ = v_reuseFailAlloc_783_;
goto v_reusejp_781_;
}
v_reusejp_781_:
{
return v___x_782_;
}
}
else
{
lean_object* v_val_784_; lean_object* v___x_786_; 
v_val_784_ = lean_ctor_get(v_fst_779_, 0);
lean_inc(v_val_784_);
lean_dec_ref_known(v_fst_779_, 1);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v_val_784_);
v___x_786_ = v___x_777_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v_val_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
}
}
else
{
lean_object* v_a_789_; lean_object* v___x_791_; uint8_t v_isShared_792_; uint8_t v_isSharedCheck_796_; 
v_a_789_ = lean_ctor_get(v___x_774_, 0);
v_isSharedCheck_796_ = !lean_is_exclusive(v___x_774_);
if (v_isSharedCheck_796_ == 0)
{
v___x_791_ = v___x_774_;
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
else
{
lean_inc(v_a_789_);
lean_dec(v___x_774_);
v___x_791_ = lean_box(0);
v_isShared_792_ = v_isSharedCheck_796_;
goto v_resetjp_790_;
}
v_resetjp_790_:
{
lean_object* v___x_794_; 
if (v_isShared_792_ == 0)
{
v___x_794_ = v___x_791_;
goto v_reusejp_793_;
}
else
{
lean_object* v_reuseFailAlloc_795_; 
v_reuseFailAlloc_795_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_795_, 0, v_a_789_);
v___x_794_ = v_reuseFailAlloc_795_;
goto v_reusejp_793_;
}
v_reusejp_793_:
{
return v___x_794_;
}
}
}
}
}
else
{
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_865_; 
v_a_819_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_865_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_865_ == 0)
{
v___x_821_ = v___x_763_;
v_isShared_822_ = v_isSharedCheck_865_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_763_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_865_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___x_823_; 
v___x_823_ = l_Lean_Exception_isInterrupt(v_a_819_);
if (v___x_823_ == 0)
{
uint8_t v___x_824_; 
lean_inc(v_a_819_);
v___x_824_ = l_Lean_Exception_isRuntime(v_a_819_);
if (v___x_824_ == 0)
{
lean_object* v_toCold_825_; lean_object* v_options_826_; uint8_t v_hasTrace_827_; 
v_toCold_825_ = lean_ctor_get(v___y_760_, 0);
v_options_826_ = lean_ctor_get(v_toCold_825_, 2);
v_hasTrace_827_ = lean_ctor_get_uint8(v_options_826_, sizeof(void*)*1);
if (v_hasTrace_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
lean_dec(v_a_819_);
v___x_828_ = lean_box(v___x_753_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
lean_ctor_set(v___x_821_, 0, v___x_828_);
v___x_830_ = v___x_821_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_831_; 
v_reuseFailAlloc_831_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_831_, 0, v___x_828_);
v___x_830_ = v_reuseFailAlloc_831_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
return v___x_830_;
}
}
else
{
lean_object* v_inheritedTraceOptions_832_; lean_object* v___x_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v_inheritedTraceOptions_832_ = lean_ctor_get(v_toCold_825_, 11);
v___x_833_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_834_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_835_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_832_, v_options_826_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_838_; 
lean_dec(v_a_819_);
v___x_836_ = lean_box(v___x_753_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
lean_ctor_set(v___x_821_, 0, v___x_836_);
v___x_838_ = v___x_821_;
goto v_reusejp_837_;
}
else
{
lean_object* v_reuseFailAlloc_839_; 
v_reuseFailAlloc_839_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_839_, 0, v___x_836_);
v___x_838_ = v_reuseFailAlloc_839_;
goto v_reusejp_837_;
}
v_reusejp_837_:
{
return v___x_838_;
}
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; 
lean_del_object(v___x_821_);
v___x_840_ = l_Lean_Exception_toMessageData(v_a_819_);
v___x_841_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_833_, v___x_840_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_841_) == 0)
{
lean_object* v___x_843_; uint8_t v_isShared_844_; uint8_t v_isSharedCheck_849_; 
v_isSharedCheck_849_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v___x_841_, 0);
lean_dec(v_unused_850_);
v___x_843_ = v___x_841_;
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
else
{
lean_dec(v___x_841_);
v___x_843_ = lean_box(0);
v_isShared_844_ = v_isSharedCheck_849_;
goto v_resetjp_842_;
}
v_resetjp_842_:
{
lean_object* v___x_845_; lean_object* v___x_847_; 
v___x_845_ = lean_box(v___x_753_);
if (v_isShared_844_ == 0)
{
lean_ctor_set(v___x_843_, 0, v___x_845_);
v___x_847_ = v___x_843_;
goto v_reusejp_846_;
}
else
{
lean_object* v_reuseFailAlloc_848_; 
v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_848_, 0, v___x_845_);
v___x_847_ = v_reuseFailAlloc_848_;
goto v_reusejp_846_;
}
v_reusejp_846_:
{
return v___x_847_;
}
}
}
else
{
lean_object* v_a_851_; lean_object* v___x_853_; uint8_t v_isShared_854_; uint8_t v_isSharedCheck_858_; 
v_a_851_ = lean_ctor_get(v___x_841_, 0);
v_isSharedCheck_858_ = !lean_is_exclusive(v___x_841_);
if (v_isSharedCheck_858_ == 0)
{
v___x_853_ = v___x_841_;
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
else
{
lean_inc(v_a_851_);
lean_dec(v___x_841_);
v___x_853_ = lean_box(0);
v_isShared_854_ = v_isSharedCheck_858_;
goto v_resetjp_852_;
}
v_resetjp_852_:
{
lean_object* v___x_856_; 
if (v_isShared_854_ == 0)
{
v___x_856_ = v___x_853_;
goto v_reusejp_855_;
}
else
{
lean_object* v_reuseFailAlloc_857_; 
v_reuseFailAlloc_857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_857_, 0, v_a_851_);
v___x_856_ = v_reuseFailAlloc_857_;
goto v_reusejp_855_;
}
v_reusejp_855_:
{
return v___x_856_;
}
}
}
}
}
}
else
{
lean_object* v___x_860_; 
if (v_isShared_822_ == 0)
{
v___x_860_ = v___x_821_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_819_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
else
{
lean_object* v___x_863_; 
if (v_isShared_822_ == 0)
{
v___x_863_ = v___x_821_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v_a_819_);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_866_, lean_object* v_fvarId_867_, lean_object* v___x_868_, lean_object* v___x_869_, lean_object* v___x_870_, lean_object* v_val_871_, lean_object* v___x_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_){
_start:
{
uint8_t v___x_16106__boxed_879_; uint8_t v___x_16109__boxed_880_; lean_object* v_res_881_; 
v___x_16106__boxed_879_ = lean_unbox(v___x_869_);
v___x_16109__boxed_880_ = lean_unbox(v___x_872_);
v_res_881_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_866_, v_fvarId_867_, v___x_868_, v___x_16106__boxed_879_, v___x_870_, v_val_871_, v___x_16109__boxed_880_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_);
lean_dec(v___y_877_);
lean_dec_ref(v___y_876_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec(v_val_871_);
return v_res_881_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_883_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_884_ = l_Lean_stringToMessageData(v___x_883_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_885_, lean_object* v_fvarId_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; uint8_t v___x_899_; 
v___x_897_ = lean_st_ref_get(v_a_887_);
v___x_898_ = lean_unsigned_to_nat(0u);
v___x_899_ = lean_nat_dec_eq(v___x_897_, v___x_898_);
if (v___x_899_ == 0)
{
uint8_t v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___f_909_; lean_object* v___x_910_; 
v___x_900_ = 1;
v___x_901_ = lean_st_ref_take(v_a_887_);
v___x_902_ = lean_unsigned_to_nat(1u);
v___x_903_ = lean_nat_sub(v___x_901_, v___x_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_st_ref_put(v_a_887_, v___x_903_);
v___x_905_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_906_ = lean_box(0);
v___x_907_ = lean_box(v___x_899_);
v___x_908_ = lean_box(v___x_900_);
v___f_909_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_909_, 0, v_mvarId_885_);
lean_closure_set(v___f_909_, 1, v_fvarId_886_);
lean_closure_set(v___f_909_, 2, v___x_905_);
lean_closure_set(v___f_909_, 3, v___x_907_);
lean_closure_set(v___f_909_, 4, v___x_906_);
lean_closure_set(v___f_909_, 5, v___x_897_);
lean_closure_set(v___f_909_, 6, v___x_908_);
v___x_910_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_909_, v_a_887_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
return v___x_910_;
}
else
{
lean_object* v_toCold_911_; lean_object* v_options_912_; uint8_t v_hasTrace_913_; 
lean_dec(v___x_897_);
lean_dec(v_fvarId_886_);
lean_dec(v_mvarId_885_);
v_toCold_911_ = lean_ctor_get(v_a_890_, 0);
v_options_912_ = lean_ctor_get(v_toCold_911_, 2);
v_hasTrace_913_ = lean_ctor_get_uint8(v_options_912_, sizeof(void*)*1);
if (v_hasTrace_913_ == 0)
{
goto v___jp_893_;
}
else
{
lean_object* v_inheritedTraceOptions_914_; lean_object* v___x_915_; lean_object* v___x_916_; uint8_t v___x_917_; 
v_inheritedTraceOptions_914_ = lean_ctor_get(v_toCold_911_, 11);
v___x_915_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_916_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_917_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_914_, v_options_912_, v___x_916_);
if (v___x_917_ == 0)
{
goto v___jp_893_;
}
else
{
lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_918_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_919_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_915_, v___x_918_, v_a_888_, v_a_889_, v_a_890_, v_a_891_);
if (lean_obj_tag(v___x_919_) == 0)
{
lean_dec_ref_known(v___x_919_, 1);
goto v___jp_893_;
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
v_a_920_ = lean_ctor_get(v___x_919_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_919_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_919_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_919_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
}
}
v___jp_893_:
{
uint8_t v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_894_ = 0;
v___x_895_ = lean_box(v___x_894_);
v___x_896_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_896_, 0, v___x_895_);
return v___x_896_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_928_, lean_object* v___x_929_, lean_object* v_as_930_, size_t v_sz_931_, size_t v_i_932_, lean_object* v_b_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_a_941_; uint8_t v___x_945_; 
v___x_945_ = lean_usize_dec_lt(v_i_932_, v_sz_931_);
if (v___x_945_ == 0)
{
lean_object* v___x_946_; 
lean_dec(v___x_929_);
lean_dec_ref(v___x_928_);
v___x_946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_946_, 0, v_b_933_);
return v___x_946_;
}
else
{
lean_object* v_subst_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v_a_950_; lean_object* v___x_951_; uint8_t v___x_952_; 
lean_dec_ref(v_b_933_);
v_subst_947_ = lean_ctor_get(v___x_928_, 2);
v___x_948_ = lean_box(0);
v___x_949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_950_ = lean_array_uget_borrowed(v_as_930_, v_i_932_);
lean_inc(v_subst_947_);
v___x_951_ = l_Lean_Meta_FVarSubst_apply(v_subst_947_, v_a_950_);
v___x_952_ = l_Lean_Expr_isFVar(v___x_951_);
if (v___x_952_ == 0)
{
lean_dec_ref(v___x_951_);
v_a_941_ = v___x_949_;
goto v___jp_940_;
}
else
{
lean_object* v___x_953_; lean_object* v___x_954_; 
v___x_953_ = l_Lean_Expr_fvarId_x21(v___x_951_);
lean_dec_ref(v___x_951_);
lean_inc(v___x_953_);
v___x_954_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_953_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; uint8_t v___x_956_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
lean_inc(v_a_955_);
lean_dec_ref_known(v___x_954_, 1);
v___x_956_ = lean_unbox(v_a_955_);
lean_dec(v_a_955_);
if (v___x_956_ == 0)
{
lean_dec(v___x_953_);
v_a_941_ = v___x_949_;
goto v___jp_940_;
}
else
{
lean_object* v___x_957_; 
lean_inc(v___x_929_);
v___x_957_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_929_, v___x_953_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; lean_object* v___x_960_; uint8_t v_isShared_961_; uint8_t v_isSharedCheck_969_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_969_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_969_ == 0)
{
v___x_960_ = v___x_957_;
v_isShared_961_ = v_isSharedCheck_969_;
goto v_resetjp_959_;
}
else
{
lean_inc(v_a_958_);
lean_dec(v___x_957_);
v___x_960_ = lean_box(0);
v_isShared_961_ = v_isSharedCheck_969_;
goto v_resetjp_959_;
}
v_resetjp_959_:
{
uint8_t v___x_962_; 
v___x_962_ = lean_unbox(v_a_958_);
lean_dec(v_a_958_);
if (v___x_962_ == 0)
{
lean_del_object(v___x_960_);
v_a_941_ = v___x_949_;
goto v___jp_940_;
}
else
{
lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_967_; 
lean_dec(v___x_929_);
lean_dec_ref(v___x_928_);
v___x_963_ = lean_box(v___x_952_);
v___x_964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_964_, 0, v___x_963_);
v___x_965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
lean_ctor_set(v___x_965_, 1, v___x_948_);
if (v_isShared_961_ == 0)
{
lean_ctor_set(v___x_960_, 0, v___x_965_);
v___x_967_ = v___x_960_;
goto v_reusejp_966_;
}
else
{
lean_object* v_reuseFailAlloc_968_; 
v_reuseFailAlloc_968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
v___x_967_ = v_reuseFailAlloc_968_;
goto v_reusejp_966_;
}
v_reusejp_966_:
{
return v___x_967_;
}
}
}
}
else
{
lean_object* v_a_970_; lean_object* v___x_972_; uint8_t v_isShared_973_; uint8_t v_isSharedCheck_977_; 
lean_dec(v___x_929_);
lean_dec_ref(v___x_928_);
v_a_970_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_977_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_977_ == 0)
{
v___x_972_ = v___x_957_;
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
else
{
lean_inc(v_a_970_);
lean_dec(v___x_957_);
v___x_972_ = lean_box(0);
v_isShared_973_ = v_isSharedCheck_977_;
goto v_resetjp_971_;
}
v_resetjp_971_:
{
lean_object* v___x_975_; 
if (v_isShared_973_ == 0)
{
v___x_975_ = v___x_972_;
goto v_reusejp_974_;
}
else
{
lean_object* v_reuseFailAlloc_976_; 
v_reuseFailAlloc_976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_976_, 0, v_a_970_);
v___x_975_ = v_reuseFailAlloc_976_;
goto v_reusejp_974_;
}
v_reusejp_974_:
{
return v___x_975_;
}
}
}
}
}
else
{
lean_object* v_a_978_; lean_object* v___x_980_; uint8_t v_isShared_981_; uint8_t v_isSharedCheck_985_; 
lean_dec(v___x_953_);
lean_dec(v___x_929_);
lean_dec_ref(v___x_928_);
v_a_978_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_985_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_985_ == 0)
{
v___x_980_ = v___x_954_;
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
else
{
lean_inc(v_a_978_);
lean_dec(v___x_954_);
v___x_980_ = lean_box(0);
v_isShared_981_ = v_isSharedCheck_985_;
goto v_resetjp_979_;
}
v_resetjp_979_:
{
lean_object* v___x_983_; 
if (v_isShared_981_ == 0)
{
v___x_983_ = v___x_980_;
goto v_reusejp_982_;
}
else
{
lean_object* v_reuseFailAlloc_984_; 
v_reuseFailAlloc_984_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_984_, 0, v_a_978_);
v___x_983_ = v_reuseFailAlloc_984_;
goto v_reusejp_982_;
}
v_reusejp_982_:
{
return v___x_983_;
}
}
}
}
}
v___jp_940_:
{
size_t v___x_942_; size_t v___x_943_; 
v___x_942_ = ((size_t)1ULL);
v___x_943_ = lean_usize_add(v_i_932_, v___x_942_);
lean_inc_ref(v_a_941_);
v_i_932_ = v___x_943_;
v_b_933_ = v_a_941_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_986_, lean_object* v_mvarId_987_, lean_object* v_fields_988_, size_t v_sz_989_, size_t v___x_990_, lean_object* v___x_991_, uint8_t v___x_992_, lean_object* v___y_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_){
_start:
{
lean_object* v___x_999_; 
v___x_999_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_986_, v_mvarId_987_, v_fields_988_, v_sz_989_, v___x_990_, v___x_991_, v___y_993_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
if (lean_obj_tag(v___x_999_) == 0)
{
lean_object* v_a_1000_; lean_object* v___x_1002_; uint8_t v_isShared_1003_; uint8_t v_isSharedCheck_1013_; 
v_a_1000_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1013_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1013_ == 0)
{
v___x_1002_ = v___x_999_;
v_isShared_1003_ = v_isSharedCheck_1013_;
goto v_resetjp_1001_;
}
else
{
lean_inc(v_a_1000_);
lean_dec(v___x_999_);
v___x_1002_ = lean_box(0);
v_isShared_1003_ = v_isSharedCheck_1013_;
goto v_resetjp_1001_;
}
v_resetjp_1001_:
{
lean_object* v_fst_1004_; 
v_fst_1004_ = lean_ctor_get(v_a_1000_, 0);
lean_inc(v_fst_1004_);
lean_dec(v_a_1000_);
if (lean_obj_tag(v_fst_1004_) == 0)
{
lean_object* v___x_1005_; lean_object* v___x_1007_; 
v___x_1005_ = lean_box(v___x_992_);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v___x_1005_);
v___x_1007_ = v___x_1002_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
else
{
lean_object* v_val_1009_; lean_object* v___x_1011_; 
v_val_1009_ = lean_ctor_get(v_fst_1004_, 0);
lean_inc(v_val_1009_);
lean_dec_ref_known(v_fst_1004_, 1);
if (v_isShared_1003_ == 0)
{
lean_ctor_set(v___x_1002_, 0, v_val_1009_);
v___x_1011_ = v___x_1002_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v_val_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
}
}
else
{
lean_object* v_a_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1021_; 
v_a_1014_ = lean_ctor_get(v___x_999_, 0);
v_isSharedCheck_1021_ = !lean_is_exclusive(v___x_999_);
if (v_isSharedCheck_1021_ == 0)
{
v___x_1016_ = v___x_999_;
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_a_1014_);
lean_dec(v___x_999_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1021_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1019_; 
if (v_isShared_1017_ == 0)
{
v___x_1019_ = v___x_1016_;
goto v_reusejp_1018_;
}
else
{
lean_object* v_reuseFailAlloc_1020_; 
v_reuseFailAlloc_1020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1020_, 0, v_a_1014_);
v___x_1019_ = v_reuseFailAlloc_1020_;
goto v_reusejp_1018_;
}
v_reusejp_1018_:
{
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1022_, lean_object* v_as_1023_, lean_object* v_sz_1024_, lean_object* v_i_1025_, lean_object* v_b_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_){
_start:
{
size_t v_sz_boxed_1033_; size_t v_i_boxed_1034_; lean_object* v_res_1035_; 
v_sz_boxed_1033_ = lean_unbox_usize(v_sz_1024_);
lean_dec(v_sz_1024_);
v_i_boxed_1034_ = lean_unbox_usize(v_i_1025_);
lean_dec(v_i_1025_);
v_res_1035_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1022_, v_as_1023_, v_sz_boxed_1033_, v_i_boxed_1034_, v_b_1026_, v___y_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_);
lean_dec(v___y_1031_);
lean_dec_ref(v___y_1030_);
lean_dec(v___y_1029_);
lean_dec_ref(v___y_1028_);
lean_dec(v___y_1027_);
lean_dec_ref(v_as_1023_);
lean_dec(v_val_1022_);
return v_res_1035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1036_, lean_object* v___x_1037_, lean_object* v_as_1038_, lean_object* v_sz_1039_, lean_object* v_i_1040_, lean_object* v_b_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_){
_start:
{
size_t v_sz_boxed_1048_; size_t v_i_boxed_1049_; lean_object* v_res_1050_; 
v_sz_boxed_1048_ = lean_unbox_usize(v_sz_1039_);
lean_dec(v_sz_1039_);
v_i_boxed_1049_ = lean_unbox_usize(v_i_1040_);
lean_dec(v_i_1040_);
v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1036_, v___x_1037_, v_as_1038_, v_sz_boxed_1048_, v_i_boxed_1049_, v_b_1041_, v___y_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_);
lean_dec(v___y_1046_);
lean_dec_ref(v___y_1045_);
lean_dec(v___y_1044_);
lean_dec_ref(v___y_1043_);
lean_dec(v___y_1042_);
lean_dec_ref(v_as_1038_);
return v_res_1050_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1051_, lean_object* v_fvarId_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1051_, v_fvarId_1052_, v_a_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_);
lean_dec(v_a_1057_);
lean_dec_ref(v_a_1056_);
lean_dec(v_a_1055_);
lean_dec_ref(v_a_1054_);
lean_dec(v_a_1053_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1060_, lean_object* v_msg_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1060_, v_msg_1061_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1069_, lean_object* v_msg_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v_res_1077_; 
v_res_1077_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1069_, v_msg_1070_, v___y_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_);
lean_dec(v___y_1075_);
lean_dec_ref(v___y_1074_);
lean_dec(v___y_1073_);
lean_dec_ref(v___y_1072_);
lean_dec(v___y_1071_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Meta_saveState___redArg(v___y_1080_, v___y_1082_);
if (lean_obj_tag(v___x_1084_) == 0)
{
lean_object* v_a_1085_; lean_object* v___y_1087_; lean_object* v_a_1088_; lean_object* v___x_1108_; 
v_a_1085_ = lean_ctor_get(v___x_1084_, 0);
lean_inc(v_a_1085_);
lean_dec_ref_known(v___x_1084_, 1);
lean_inc(v___y_1082_);
lean_inc_ref(v___y_1081_);
lean_inc(v___y_1080_);
lean_inc_ref(v___y_1079_);
v___x_1108_ = lean_apply_5(v_x_1078_, v___y_1079_, v___y_1080_, v___y_1081_, v___y_1082_, lean_box(0));
if (lean_obj_tag(v___x_1108_) == 0)
{
lean_object* v_a_1109_; uint8_t v___x_1110_; 
v_a_1109_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1109_);
v___x_1110_ = lean_unbox(v_a_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec_ref_known(v___x_1108_, 1);
lean_inc(v_a_1085_);
v___x_1111_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1085_, v___y_1080_, v___y_1082_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_a_1085_);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; 
v_unused_1119_ = lean_ctor_get(v___x_1111_, 0);
lean_dec(v_unused_1119_);
v___x_1113_ = v___x_1111_;
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
else
{
lean_dec(v___x_1111_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1118_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___x_1116_; 
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 0, v_a_1109_);
v___x_1116_ = v___x_1113_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_a_1109_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
return v___x_1116_;
}
}
}
else
{
lean_object* v_a_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec(v_a_1109_);
v_a_1120_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1127_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v___x_1111_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_a_1120_);
lean_dec(v___x_1111_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
lean_inc(v_a_1120_);
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_a_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
v___y_1087_ = v___x_1125_;
v_a_1088_ = v_a_1120_;
goto v___jp_1086_;
}
}
}
}
else
{
lean_dec(v_a_1109_);
lean_dec(v_a_1085_);
return v___x_1108_;
}
}
else
{
lean_object* v_a_1128_; 
v_a_1128_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1128_);
v___y_1087_ = v___x_1108_;
v_a_1088_ = v_a_1128_;
goto v___jp_1086_;
}
v___jp_1086_:
{
uint8_t v___x_1089_; 
v___x_1089_ = l_Lean_Exception_isInterrupt(v_a_1088_);
if (v___x_1089_ == 0)
{
uint8_t v___x_1090_; 
lean_inc_ref(v_a_1088_);
v___x_1090_ = l_Lean_Exception_isRuntime(v_a_1088_);
if (v___x_1090_ == 0)
{
lean_object* v___x_1091_; 
lean_dec_ref(v___y_1087_);
v___x_1091_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1085_, v___y_1080_, v___y_1082_);
if (lean_obj_tag(v___x_1091_) == 0)
{
lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1098_; 
v_isSharedCheck_1098_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1098_ == 0)
{
lean_object* v_unused_1099_; 
v_unused_1099_ = lean_ctor_get(v___x_1091_, 0);
lean_dec(v_unused_1099_);
v___x_1093_ = v___x_1091_;
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
else
{
lean_dec(v___x_1091_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1098_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1096_; 
if (v_isShared_1094_ == 0)
{
lean_ctor_set_tag(v___x_1093_, 1);
lean_ctor_set(v___x_1093_, 0, v_a_1088_);
v___x_1096_ = v___x_1093_;
goto v_reusejp_1095_;
}
else
{
lean_object* v_reuseFailAlloc_1097_; 
v_reuseFailAlloc_1097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1088_);
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
lean_object* v_a_1100_; lean_object* v___x_1102_; uint8_t v_isShared_1103_; uint8_t v_isSharedCheck_1107_; 
lean_dec_ref(v_a_1088_);
v_a_1100_ = lean_ctor_get(v___x_1091_, 0);
v_isSharedCheck_1107_ = !lean_is_exclusive(v___x_1091_);
if (v_isSharedCheck_1107_ == 0)
{
v___x_1102_ = v___x_1091_;
v_isShared_1103_ = v_isSharedCheck_1107_;
goto v_resetjp_1101_;
}
else
{
lean_inc(v_a_1100_);
lean_dec(v___x_1091_);
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
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1085_);
return v___y_1087_;
}
}
else
{
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1085_);
return v___y_1087_;
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v_x_1078_);
v_a_1129_ = lean_ctor_get(v___x_1084_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1084_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1084_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1084_);
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
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_){
_start:
{
lean_object* v_res_1143_; 
v_res_1143_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1137_, v___y_1138_, v___y_1139_, v___y_1140_, v___y_1141_);
lean_dec(v___y_1141_);
lean_dec_ref(v___y_1140_);
lean_dec(v___y_1139_);
lean_dec_ref(v___y_1138_);
return v_res_1143_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1144_, lean_object* v_x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1151_; 
v___x_1151_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1144_, v_x_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
if (lean_obj_tag(v___x_1151_) == 0)
{
lean_object* v_a_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1159_; 
v_a_1152_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1159_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1159_ == 0)
{
v___x_1154_ = v___x_1151_;
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_a_1152_);
lean_dec(v___x_1151_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1159_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v___x_1157_; 
if (v_isShared_1155_ == 0)
{
v___x_1157_ = v___x_1154_;
goto v_reusejp_1156_;
}
else
{
lean_object* v_reuseFailAlloc_1158_; 
v_reuseFailAlloc_1158_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1158_, 0, v_a_1152_);
v___x_1157_ = v_reuseFailAlloc_1158_;
goto v_reusejp_1156_;
}
v_reusejp_1156_:
{
return v___x_1157_;
}
}
}
else
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_a_1160_ = lean_ctor_get(v___x_1151_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1151_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1151_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1151_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1165_; 
if (v_isShared_1163_ == 0)
{
v___x_1165_ = v___x_1162_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_a_1160_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1168_, lean_object* v_x_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1168_, v_x_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1176_, lean_object* v_mvarId_1177_, lean_object* v_x_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v___x_1184_; 
v___x_1184_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1177_, v_x_1178_, v___y_1179_, v___y_1180_, v___y_1181_, v___y_1182_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1185_, lean_object* v_mvarId_1186_, lean_object* v_x_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1185_, v_mvarId_1186_, v_x_1187_, v___y_1188_, v___y_1189_, v___y_1190_, v___y_1191_);
lean_dec(v___y_1191_);
lean_dec_ref(v___y_1190_);
lean_dec(v___y_1189_);
lean_dec_ref(v___y_1188_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1194_, lean_object* v_fuel_1195_, lean_object* v_fvarId_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v___x_1202_; 
v___x_1202_ = l_Lean_MVarId_exfalso(v_mvarId_1194_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
if (lean_obj_tag(v___x_1202_) == 0)
{
lean_object* v_a_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; 
v_a_1203_ = lean_ctor_get(v___x_1202_, 0);
lean_inc(v_a_1203_);
lean_dec_ref_known(v___x_1202_, 1);
v___x_1204_ = lean_st_mk_ref(v_fuel_1195_);
v___x_1205_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1203_, v_fvarId_1196_, v___x_1204_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
if (lean_obj_tag(v___x_1205_) == 0)
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1214_; 
v_a_1206_ = lean_ctor_get(v___x_1205_, 0);
v_isSharedCheck_1214_ = !lean_is_exclusive(v___x_1205_);
if (v_isSharedCheck_1214_ == 0)
{
v___x_1208_ = v___x_1205_;
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1205_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1214_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1210_; lean_object* v___x_1212_; 
v___x_1210_ = lean_st_ref_get(v___x_1204_);
lean_dec(v___x_1204_);
lean_dec(v___x_1210_);
if (v_isShared_1209_ == 0)
{
v___x_1212_ = v___x_1208_;
goto v_reusejp_1211_;
}
else
{
lean_object* v_reuseFailAlloc_1213_; 
v_reuseFailAlloc_1213_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1213_, 0, v_a_1206_);
v___x_1212_ = v_reuseFailAlloc_1213_;
goto v_reusejp_1211_;
}
v_reusejp_1211_:
{
return v___x_1212_;
}
}
}
else
{
lean_dec(v___x_1204_);
return v___x_1205_;
}
}
else
{
lean_object* v_a_1215_; lean_object* v___x_1217_; uint8_t v_isShared_1218_; uint8_t v_isSharedCheck_1222_; 
lean_dec(v_fvarId_1196_);
lean_dec(v_fuel_1195_);
v_a_1215_ = lean_ctor_get(v___x_1202_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1202_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1217_ = v___x_1202_;
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
else
{
lean_inc(v_a_1215_);
lean_dec(v___x_1202_);
v___x_1217_ = lean_box(0);
v_isShared_1218_ = v_isSharedCheck_1222_;
goto v_resetjp_1216_;
}
v_resetjp_1216_:
{
lean_object* v___x_1220_; 
if (v_isShared_1218_ == 0)
{
v___x_1220_ = v___x_1217_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1215_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1223_, lean_object* v_fuel_1224_, lean_object* v_fvarId_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1223_, v_fuel_1224_, v_fvarId_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec(v___y_1227_);
lean_dec_ref(v___y_1226_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1232_, lean_object* v___f_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v___x_1239_; 
v___x_1239_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1232_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
if (lean_obj_tag(v___x_1239_) == 0)
{
lean_object* v_a_1240_; uint8_t v___x_1241_; 
v_a_1240_ = lean_ctor_get(v___x_1239_, 0);
v___x_1241_ = lean_unbox(v_a_1240_);
if (v___x_1241_ == 0)
{
lean_dec_ref(v___f_1233_);
return v___x_1239_;
}
else
{
lean_object* v___x_1242_; 
lean_dec_ref_known(v___x_1239_, 1);
v___x_1242_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
return v___x_1242_;
}
}
else
{
lean_dec_ref(v___f_1233_);
return v___x_1239_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1243_, lean_object* v___f_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1243_, v___f_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
lean_dec(v___y_1248_);
lean_dec_ref(v___y_1247_);
lean_dec(v___y_1246_);
lean_dec_ref(v___y_1245_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1251_, lean_object* v_fvarId_1252_, lean_object* v_fuel_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_){
_start:
{
lean_object* v___f_1259_; lean_object* v___f_1260_; lean_object* v___x_1261_; 
lean_inc(v_fvarId_1252_);
lean_inc(v_mvarId_1251_);
v___f_1259_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1259_, 0, v_mvarId_1251_);
lean_closure_set(v___f_1259_, 1, v_fuel_1253_);
lean_closure_set(v___f_1259_, 2, v_fvarId_1252_);
v___f_1260_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1260_, 0, v_fvarId_1252_);
lean_closure_set(v___f_1260_, 1, v___f_1259_);
v___x_1261_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1251_, v___f_1260_, v_a_1254_, v_a_1255_, v_a_1256_, v_a_1257_);
return v___x_1261_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1262_, lean_object* v_fvarId_1263_, lean_object* v_fuel_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1262_, v_fvarId_1263_, v_fuel_1264_, v_a_1265_, v_a_1266_, v_a_1267_, v_a_1268_);
lean_dec(v_a_1268_);
lean_dec_ref(v_a_1267_);
lean_dec(v_a_1266_);
lean_dec_ref(v_a_1265_);
return v_res_1270_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1271_){
_start:
{
uint8_t v___x_1272_; 
v___x_1272_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1271_);
return v___x_1272_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1273_){
_start:
{
uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_res_1274_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1273_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1276_, lean_object* v_acc_1277_){
_start:
{
if (lean_obj_tag(v_e_1276_) == 7)
{
lean_object* v_binderType_1278_; lean_object* v_body_1279_; uint8_t v___y_1281_; lean_object* v___x_1285_; uint8_t v___x_1286_; 
v_binderType_1278_ = lean_ctor_get(v_e_1276_, 1);
v_body_1279_ = lean_ctor_get(v_e_1276_, 2);
v___x_1285_ = lean_unsigned_to_nat(0u);
v___x_1286_ = lean_expr_has_loose_bvar(v_body_1279_, v___x_1285_);
if (v___x_1286_ == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Lean_Expr_isEq(v_binderType_1278_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Lean_Expr_isHEq(v_binderType_1278_);
v___y_1281_ = v___x_1288_;
goto v___jp_1280_;
}
else
{
v___y_1281_ = v___x_1287_;
goto v___jp_1280_;
}
}
else
{
uint8_t v___x_1289_; 
v___x_1289_ = 0;
v___y_1281_ = v___x_1289_;
goto v___jp_1280_;
}
v___jp_1280_:
{
lean_object* v___x_1282_; lean_object* v___x_1283_; 
v___x_1282_ = lean_box(v___y_1281_);
v___x_1283_ = lean_array_push(v_acc_1277_, v___x_1282_);
v_e_1276_ = v_body_1279_;
v_acc_1277_ = v___x_1283_;
goto _start;
}
}
else
{
return v_acc_1277_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1290_, lean_object* v_acc_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1290_, v_acc_1291_);
lean_dec_ref(v_e_1290_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1295_){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
v___x_1296_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1297_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1295_, v___x_1296_);
return v___x_1297_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_Lean_Meta_mkGenDiseqMask(v_e_1298_);
lean_dec_ref(v_e_1298_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_){
_start:
{
lean_object* v___f_1307_; lean_object* v___x_4344__overap_1308_; lean_object* v___x_1309_; 
v___f_1307_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_4344__overap_1308_ = lean_panic_fn_borrowed(v___f_1307_, v_msg_1301_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
v___x_1309_ = lean_apply_5(v___x_4344__overap_1308_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, lean_box(0));
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_){
_start:
{
lean_object* v_res_1316_; 
v_res_1316_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1310_, v___y_1311_, v___y_1312_, v___y_1313_, v___y_1314_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
return v_res_1316_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1317_, lean_object* v___y_1318_){
_start:
{
uint8_t v___x_1320_; 
v___x_1320_ = l_Lean_Expr_hasMVar(v_e_1317_);
if (v___x_1320_ == 0)
{
lean_object* v___x_1321_; 
v___x_1321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1321_, 0, v_e_1317_);
return v___x_1321_;
}
else
{
lean_object* v___x_1322_; lean_object* v_mctx_1323_; lean_object* v___x_1324_; lean_object* v_fst_1325_; lean_object* v_snd_1326_; lean_object* v___x_1327_; lean_object* v_cache_1328_; lean_object* v_zetaDeltaFVarIds_1329_; lean_object* v_postponed_1330_; lean_object* v_diag_1331_; lean_object* v___x_1333_; uint8_t v_isShared_1334_; uint8_t v_isSharedCheck_1340_; 
v___x_1322_ = lean_st_ref_get(v___y_1318_);
v_mctx_1323_ = lean_ctor_get(v___x_1322_, 0);
lean_inc_ref(v_mctx_1323_);
lean_dec(v___x_1322_);
v___x_1324_ = l_Lean_instantiateMVarsCore(v_mctx_1323_, v_e_1317_);
v_fst_1325_ = lean_ctor_get(v___x_1324_, 0);
lean_inc(v_fst_1325_);
v_snd_1326_ = lean_ctor_get(v___x_1324_, 1);
lean_inc(v_snd_1326_);
lean_dec_ref(v___x_1324_);
v___x_1327_ = lean_st_ref_take(v___y_1318_);
v_cache_1328_ = lean_ctor_get(v___x_1327_, 1);
v_zetaDeltaFVarIds_1329_ = lean_ctor_get(v___x_1327_, 2);
v_postponed_1330_ = lean_ctor_get(v___x_1327_, 3);
v_diag_1331_ = lean_ctor_get(v___x_1327_, 4);
v_isSharedCheck_1340_ = !lean_is_exclusive(v___x_1327_);
if (v_isSharedCheck_1340_ == 0)
{
lean_object* v_unused_1341_; 
v_unused_1341_ = lean_ctor_get(v___x_1327_, 0);
lean_dec(v_unused_1341_);
v___x_1333_ = v___x_1327_;
v_isShared_1334_ = v_isSharedCheck_1340_;
goto v_resetjp_1332_;
}
else
{
lean_inc(v_diag_1331_);
lean_inc(v_postponed_1330_);
lean_inc(v_zetaDeltaFVarIds_1329_);
lean_inc(v_cache_1328_);
lean_dec(v___x_1327_);
v___x_1333_ = lean_box(0);
v_isShared_1334_ = v_isSharedCheck_1340_;
goto v_resetjp_1332_;
}
v_resetjp_1332_:
{
lean_object* v___x_1336_; 
if (v_isShared_1334_ == 0)
{
lean_ctor_set(v___x_1333_, 0, v_snd_1326_);
v___x_1336_ = v___x_1333_;
goto v_reusejp_1335_;
}
else
{
lean_object* v_reuseFailAlloc_1339_; 
v_reuseFailAlloc_1339_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1339_, 0, v_snd_1326_);
lean_ctor_set(v_reuseFailAlloc_1339_, 1, v_cache_1328_);
lean_ctor_set(v_reuseFailAlloc_1339_, 2, v_zetaDeltaFVarIds_1329_);
lean_ctor_set(v_reuseFailAlloc_1339_, 3, v_postponed_1330_);
lean_ctor_set(v_reuseFailAlloc_1339_, 4, v_diag_1331_);
v___x_1336_ = v_reuseFailAlloc_1339_;
goto v_reusejp_1335_;
}
v_reusejp_1335_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = lean_st_ref_put(v___y_1318_, v___x_1336_);
v___x_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1338_, 0, v_fst_1325_);
return v___x_1338_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1342_, lean_object* v___y_1343_, lean_object* v___y_1344_){
_start:
{
lean_object* v_res_1345_; 
v_res_1345_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1342_, v___y_1343_);
lean_dec(v___y_1343_);
return v_res_1345_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
lean_object* v___x_1352_; 
v___x_1352_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1346_, v___y_1348_);
return v___x_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v_res_1359_; 
v_res_1359_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
lean_dec(v___y_1357_);
lean_dec_ref(v___y_1356_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1360_, uint8_t v_allowLevelAssignments_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v___x_1367_; 
v___x_1367_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1361_, v_k_1360_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_object* v_a_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1375_; 
v_a_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1375_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1375_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_a_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1375_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1373_; 
if (v_isShared_1371_ == 0)
{
v___x_1373_ = v___x_1370_;
goto v_reusejp_1372_;
}
else
{
lean_object* v_reuseFailAlloc_1374_; 
v_reuseFailAlloc_1374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1374_, 0, v_a_1368_);
v___x_1373_ = v_reuseFailAlloc_1374_;
goto v_reusejp_1372_;
}
v_reusejp_1372_:
{
return v___x_1373_;
}
}
}
else
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
v_a_1376_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1367_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1367_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1384_, lean_object* v_allowLevelAssignments_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1391_; lean_object* v_res_1392_; 
v_allowLevelAssignments_boxed_1391_ = lean_unbox(v_allowLevelAssignments_1385_);
v_res_1392_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1384_, v_allowLevelAssignments_boxed_1391_, v___y_1386_, v___y_1387_, v___y_1388_, v___y_1389_);
lean_dec(v___y_1389_);
lean_dec_ref(v___y_1388_);
lean_dec(v___y_1387_);
lean_dec_ref(v___y_1386_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1393_, lean_object* v_k_1394_, uint8_t v_allowLevelAssignments_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_){
_start:
{
lean_object* v___x_1401_; 
v___x_1401_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1394_, v_allowLevelAssignments_1395_, v___y_1396_, v___y_1397_, v___y_1398_, v___y_1399_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1402_, lean_object* v_k_1403_, lean_object* v_allowLevelAssignments_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1410_; lean_object* v_res_1411_; 
v_allowLevelAssignments_boxed_1410_ = lean_unbox(v_allowLevelAssignments_1404_);
v_res_1411_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1402_, v_k_1403_, v_allowLevelAssignments_boxed_1410_, v___y_1405_, v___y_1406_, v___y_1407_, v___y_1408_);
lean_dec(v___y_1408_);
lean_dec_ref(v___y_1407_);
lean_dec(v___y_1406_);
lean_dec_ref(v___y_1405_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1414_, size_t v_sz_1415_, size_t v_i_1416_, lean_object* v_b_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_){
_start:
{
lean_object* v_a_1424_; uint8_t v___x_1428_; 
v___x_1428_ = lean_usize_dec_lt(v_i_1416_, v_sz_1415_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; 
v___x_1429_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1429_, 0, v_b_1417_);
return v___x_1429_;
}
else
{
lean_object* v_snd_1430_; lean_object* v___x_1432_; uint8_t v_isShared_1433_; uint8_t v_isSharedCheck_1592_; 
v_snd_1430_ = lean_ctor_get(v_b_1417_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_b_1417_);
if (v_isSharedCheck_1592_ == 0)
{
lean_object* v_unused_1593_; 
v_unused_1593_ = lean_ctor_get(v_b_1417_, 0);
lean_dec(v_unused_1593_);
v___x_1432_ = v_b_1417_;
v_isShared_1433_ = v_isSharedCheck_1592_;
goto v_resetjp_1431_;
}
else
{
lean_inc(v_snd_1430_);
lean_dec(v_b_1417_);
v___x_1432_ = lean_box(0);
v_isShared_1433_ = v_isSharedCheck_1592_;
goto v_resetjp_1431_;
}
v_resetjp_1431_:
{
lean_object* v_array_1434_; lean_object* v_start_1435_; lean_object* v_stop_1436_; lean_object* v___x_1437_; uint8_t v___x_1438_; 
v_array_1434_ = lean_ctor_get(v_snd_1430_, 0);
v_start_1435_ = lean_ctor_get(v_snd_1430_, 1);
v_stop_1436_ = lean_ctor_get(v_snd_1430_, 2);
v___x_1437_ = lean_box(0);
v___x_1438_ = lean_nat_dec_lt(v_start_1435_, v_stop_1436_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1440_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 0, v___x_1437_);
v___x_1440_ = v___x_1432_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1442_, 1, v_snd_1430_);
v___x_1440_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; 
v___x_1441_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
return v___x_1441_;
}
}
else
{
lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1588_; 
lean_inc(v_stop_1436_);
lean_inc(v_start_1435_);
lean_inc_ref(v_array_1434_);
v_isSharedCheck_1588_ = !lean_is_exclusive(v_snd_1430_);
if (v_isSharedCheck_1588_ == 0)
{
lean_object* v_unused_1589_; lean_object* v_unused_1590_; lean_object* v_unused_1591_; 
v_unused_1589_ = lean_ctor_get(v_snd_1430_, 2);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_snd_1430_, 1);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_snd_1430_, 0);
lean_dec(v_unused_1591_);
v___x_1444_ = v_snd_1430_;
v_isShared_1445_ = v_isSharedCheck_1588_;
goto v_resetjp_1443_;
}
else
{
lean_dec(v_snd_1430_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1588_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1450_; 
v___x_1446_ = lean_array_fget(v_array_1434_, v_start_1435_);
v___x_1447_ = lean_unsigned_to_nat(1u);
v___x_1448_ = lean_nat_add(v_start_1435_, v___x_1447_);
lean_dec(v_start_1435_);
if (v_isShared_1445_ == 0)
{
lean_ctor_set(v___x_1444_, 1, v___x_1448_);
v___x_1450_ = v___x_1444_;
goto v_reusejp_1449_;
}
else
{
lean_object* v_reuseFailAlloc_1587_; 
v_reuseFailAlloc_1587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1587_, 0, v_array_1434_);
lean_ctor_set(v_reuseFailAlloc_1587_, 1, v___x_1448_);
lean_ctor_set(v_reuseFailAlloc_1587_, 2, v_stop_1436_);
v___x_1450_ = v_reuseFailAlloc_1587_;
goto v_reusejp_1449_;
}
v_reusejp_1449_:
{
uint8_t v___x_1451_; 
v___x_1451_ = lean_unbox(v___x_1446_);
lean_dec(v___x_1446_);
if (v___x_1451_ == 0)
{
lean_object* v___x_1453_; 
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v___x_1450_);
lean_ctor_set(v___x_1432_, 0, v___x_1437_);
v___x_1453_ = v___x_1432_;
goto v_reusejp_1452_;
}
else
{
lean_object* v_reuseFailAlloc_1454_; 
v_reuseFailAlloc_1454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1454_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1454_, 1, v___x_1450_);
v___x_1453_ = v_reuseFailAlloc_1454_;
goto v_reusejp_1452_;
}
v_reusejp_1452_:
{
v_a_1424_ = v___x_1453_;
goto v___jp_1423_;
}
}
else
{
lean_object* v_a_1455_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___x_1527_; 
v_a_1455_ = lean_array_uget_borrowed(v_as_1414_, v_i_1416_);
lean_inc(v___y_1421_);
lean_inc_ref(v___y_1420_);
lean_inc(v___y_1419_);
lean_inc_ref(v___y_1418_);
lean_inc(v_a_1455_);
v___x_1527_ = lean_infer_type(v_a_1455_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___x_1529_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v___x_1529_ = l_Lean_Meta_matchEq_x3f(v_a_1528_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1529_) == 0)
{
lean_object* v_a_1530_; 
v_a_1530_ = lean_ctor_get(v___x_1529_, 0);
lean_inc(v_a_1530_);
lean_dec_ref_known(v___x_1529_, 1);
if (lean_obj_tag(v_a_1530_) == 1)
{
lean_object* v_val_1531_; lean_object* v_snd_1532_; lean_object* v_fst_1533_; lean_object* v___x_1535_; uint8_t v_isShared_1536_; uint8_t v_isSharedCheck_1569_; 
v_val_1531_ = lean_ctor_get(v_a_1530_, 0);
lean_inc(v_val_1531_);
lean_dec_ref_known(v_a_1530_, 1);
v_snd_1532_ = lean_ctor_get(v_val_1531_, 1);
lean_inc(v_snd_1532_);
lean_dec(v_val_1531_);
v_fst_1533_ = lean_ctor_get(v_snd_1532_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v_snd_1532_);
if (v_isSharedCheck_1569_ == 0)
{
lean_object* v_unused_1570_; 
v_unused_1570_ = lean_ctor_get(v_snd_1532_, 1);
lean_dec(v_unused_1570_);
v___x_1535_ = v_snd_1532_;
v_isShared_1536_ = v_isSharedCheck_1569_;
goto v_resetjp_1534_;
}
else
{
lean_inc(v_fst_1533_);
lean_dec(v_snd_1532_);
v___x_1535_ = lean_box(0);
v_isShared_1536_ = v_isSharedCheck_1569_;
goto v_resetjp_1534_;
}
v_resetjp_1534_:
{
lean_object* v___x_1537_; 
v___x_1537_ = l_Lean_Meta_mkEqRefl(v_fst_1533_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; lean_object* v___x_1539_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
lean_inc(v_a_1455_);
v___x_1539_ = l_Lean_Meta_isExprDefEq(v_a_1455_, v_a_1538_, v___y_1418_, v___y_1419_, v___y_1420_, v___y_1421_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1552_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1552_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1552_ == 0)
{
v___x_1542_ = v___x_1539_;
v_isShared_1543_ = v_isSharedCheck_1552_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1552_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
uint8_t v___x_1544_; 
v___x_1544_ = lean_unbox(v_a_1540_);
lean_dec(v_a_1540_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; lean_object* v___x_1547_; 
lean_del_object(v___x_1432_);
v___x_1545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1536_ == 0)
{
lean_ctor_set(v___x_1535_, 1, v___x_1450_);
lean_ctor_set(v___x_1535_, 0, v___x_1545_);
v___x_1547_ = v___x_1535_;
goto v_reusejp_1546_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1545_);
lean_ctor_set(v_reuseFailAlloc_1551_, 1, v___x_1450_);
v___x_1547_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1546_;
}
v_reusejp_1546_:
{
lean_object* v___x_1549_; 
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 0, v___x_1547_);
v___x_1549_ = v___x_1542_;
goto v_reusejp_1548_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1547_);
v___x_1549_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1548_;
}
v_reusejp_1548_:
{
return v___x_1549_;
}
}
}
else
{
lean_del_object(v___x_1542_);
lean_del_object(v___x_1535_);
v___y_1457_ = v___y_1418_;
v___y_1458_ = v___y_1419_;
v___y_1459_ = v___y_1420_;
v___y_1460_ = v___y_1421_;
goto v___jp_1456_;
}
}
}
else
{
lean_object* v_a_1553_; lean_object* v___x_1555_; uint8_t v_isShared_1556_; uint8_t v_isSharedCheck_1560_; 
lean_del_object(v___x_1535_);
lean_dec_ref(v___x_1450_);
lean_del_object(v___x_1432_);
v_a_1553_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1555_ = v___x_1539_;
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
else
{
lean_inc(v_a_1553_);
lean_dec(v___x_1539_);
v___x_1555_ = lean_box(0);
v_isShared_1556_ = v_isSharedCheck_1560_;
goto v_resetjp_1554_;
}
v_resetjp_1554_:
{
lean_object* v___x_1558_; 
if (v_isShared_1556_ == 0)
{
v___x_1558_ = v___x_1555_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_a_1553_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_del_object(v___x_1535_);
lean_dec_ref(v___x_1450_);
lean_del_object(v___x_1432_);
v_a_1561_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1537_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1537_);
v___x_1563_ = lean_box(0);
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
v_resetjp_1562_:
{
lean_object* v___x_1566_; 
if (v_isShared_1564_ == 0)
{
v___x_1566_ = v___x_1563_;
goto v_reusejp_1565_;
}
else
{
lean_object* v_reuseFailAlloc_1567_; 
v_reuseFailAlloc_1567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1567_, 0, v_a_1561_);
v___x_1566_ = v_reuseFailAlloc_1567_;
goto v_reusejp_1565_;
}
v_reusejp_1565_:
{
return v___x_1566_;
}
}
}
}
}
else
{
lean_dec(v_a_1530_);
v___y_1457_ = v___y_1418_;
v___y_1458_ = v___y_1419_;
v___y_1459_ = v___y_1420_;
v___y_1460_ = v___y_1421_;
goto v___jp_1456_;
}
}
else
{
lean_object* v_a_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1578_; 
lean_dec_ref(v___x_1450_);
lean_del_object(v___x_1432_);
v_a_1571_ = lean_ctor_get(v___x_1529_, 0);
v_isSharedCheck_1578_ = !lean_is_exclusive(v___x_1529_);
if (v_isSharedCheck_1578_ == 0)
{
v___x_1573_ = v___x_1529_;
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_a_1571_);
lean_dec(v___x_1529_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1578_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1576_; 
if (v_isShared_1574_ == 0)
{
v___x_1576_ = v___x_1573_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1577_; 
v_reuseFailAlloc_1577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1577_, 0, v_a_1571_);
v___x_1576_ = v_reuseFailAlloc_1577_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
return v___x_1576_;
}
}
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v___x_1450_);
lean_del_object(v___x_1432_);
v_a_1579_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1527_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1527_);
v___x_1581_ = lean_box(0);
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
v_resetjp_1580_:
{
lean_object* v___x_1584_; 
if (v_isShared_1582_ == 0)
{
v___x_1584_ = v___x_1581_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_a_1579_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
v___jp_1456_:
{
lean_object* v___x_1461_; 
lean_inc(v___y_1460_);
lean_inc_ref(v___y_1459_);
lean_inc(v___y_1458_);
lean_inc_ref(v___y_1457_);
lean_inc(v_a_1455_);
v___x_1461_ = lean_infer_type(v_a_1455_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1461_) == 0)
{
lean_object* v_a_1462_; lean_object* v___x_1463_; 
v_a_1462_ = lean_ctor_get(v___x_1461_, 0);
lean_inc(v_a_1462_);
lean_dec_ref_known(v___x_1461_, 1);
v___x_1463_ = l_Lean_Meta_matchHEq_x3f(v_a_1462_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1463_) == 0)
{
lean_object* v_a_1464_; 
v_a_1464_ = lean_ctor_get(v___x_1463_, 0);
lean_inc(v_a_1464_);
lean_dec_ref_known(v___x_1463_, 1);
if (lean_obj_tag(v_a_1464_) == 1)
{
lean_object* v_val_1465_; lean_object* v_snd_1466_; lean_object* v_fst_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1506_; 
lean_del_object(v___x_1432_);
v_val_1465_ = lean_ctor_get(v_a_1464_, 0);
lean_inc(v_val_1465_);
lean_dec_ref_known(v_a_1464_, 1);
v_snd_1466_ = lean_ctor_get(v_val_1465_, 1);
lean_inc(v_snd_1466_);
lean_dec(v_val_1465_);
v_fst_1467_ = lean_ctor_get(v_snd_1466_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v_snd_1466_);
if (v_isSharedCheck_1506_ == 0)
{
lean_object* v_unused_1507_; 
v_unused_1507_ = lean_ctor_get(v_snd_1466_, 1);
lean_dec(v_unused_1507_);
v___x_1469_ = v_snd_1466_;
v_isShared_1470_ = v_isSharedCheck_1506_;
goto v_resetjp_1468_;
}
else
{
lean_inc(v_fst_1467_);
lean_dec(v_snd_1466_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1506_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; 
v___x_1471_ = l_Lean_Meta_mkHEqRefl(v_fst_1467_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; lean_object* v___x_1473_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
lean_inc(v_a_1455_);
v___x_1473_ = l_Lean_Meta_isExprDefEq(v_a_1455_, v_a_1472_, v___y_1457_, v___y_1458_, v___y_1459_, v___y_1460_);
if (lean_obj_tag(v___x_1473_) == 0)
{
lean_object* v_a_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1489_; 
v_a_1474_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1476_ = v___x_1473_;
v_isShared_1477_ = v_isSharedCheck_1489_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_a_1474_);
lean_dec(v___x_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1489_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
uint8_t v___x_1478_; 
v___x_1478_ = lean_unbox(v_a_1474_);
lean_dec(v_a_1474_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; lean_object* v___x_1481_; 
v___x_1479_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1450_);
lean_ctor_set(v___x_1469_, 0, v___x_1479_);
v___x_1481_ = v___x_1469_;
goto v_reusejp_1480_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1479_);
lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1450_);
v___x_1481_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1480_;
}
v_reusejp_1480_:
{
lean_object* v___x_1483_; 
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 0, v___x_1481_);
v___x_1483_ = v___x_1476_;
goto v_reusejp_1482_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1481_);
v___x_1483_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1482_;
}
v_reusejp_1482_:
{
return v___x_1483_;
}
}
}
else
{
lean_object* v___x_1487_; 
lean_del_object(v___x_1476_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1450_);
lean_ctor_set(v___x_1469_, 0, v___x_1437_);
v___x_1487_ = v___x_1469_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1488_, 1, v___x_1450_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
v_a_1424_ = v___x_1487_;
goto v___jp_1423_;
}
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
lean_del_object(v___x_1469_);
lean_dec_ref(v___x_1450_);
v_a_1490_ = lean_ctor_get(v___x_1473_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1473_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1473_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1473_);
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
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_del_object(v___x_1469_);
lean_dec_ref(v___x_1450_);
v_a_1498_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1471_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1471_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
else
{
lean_object* v___x_1509_; 
lean_dec(v_a_1464_);
if (v_isShared_1433_ == 0)
{
lean_ctor_set(v___x_1432_, 1, v___x_1450_);
lean_ctor_set(v___x_1432_, 0, v___x_1437_);
v___x_1509_ = v___x_1432_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v___x_1437_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v___x_1450_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
v_a_1424_ = v___x_1509_;
goto v___jp_1423_;
}
}
}
else
{
lean_object* v_a_1511_; lean_object* v___x_1513_; uint8_t v_isShared_1514_; uint8_t v_isSharedCheck_1518_; 
lean_dec_ref(v___x_1450_);
lean_del_object(v___x_1432_);
v_a_1511_ = lean_ctor_get(v___x_1463_, 0);
v_isSharedCheck_1518_ = !lean_is_exclusive(v___x_1463_);
if (v_isSharedCheck_1518_ == 0)
{
v___x_1513_ = v___x_1463_;
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
else
{
lean_inc(v_a_1511_);
lean_dec(v___x_1463_);
v___x_1513_ = lean_box(0);
v_isShared_1514_ = v_isSharedCheck_1518_;
goto v_resetjp_1512_;
}
v_resetjp_1512_:
{
lean_object* v___x_1516_; 
if (v_isShared_1514_ == 0)
{
v___x_1516_ = v___x_1513_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v_a_1511_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
return v___x_1516_;
}
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v___x_1450_);
lean_del_object(v___x_1432_);
v_a_1519_ = lean_ctor_get(v___x_1461_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1461_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1461_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1461_);
v___x_1521_ = lean_box(0);
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
v_resetjp_1520_:
{
lean_object* v___x_1524_; 
if (v_isShared_1522_ == 0)
{
v___x_1524_ = v___x_1521_;
goto v_reusejp_1523_;
}
else
{
lean_object* v_reuseFailAlloc_1525_; 
v_reuseFailAlloc_1525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1525_, 0, v_a_1519_);
v___x_1524_ = v_reuseFailAlloc_1525_;
goto v_reusejp_1523_;
}
v_reusejp_1523_:
{
return v___x_1524_;
}
}
}
}
}
}
}
}
}
}
v___jp_1423_:
{
size_t v___x_1425_; size_t v___x_1426_; 
v___x_1425_ = ((size_t)1ULL);
v___x_1426_ = lean_usize_add(v_i_1416_, v___x_1425_);
v_i_1416_ = v___x_1426_;
v_b_1417_ = v_a_1424_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1594_, lean_object* v_sz_1595_, lean_object* v_i_1596_, lean_object* v_b_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_){
_start:
{
size_t v_sz_boxed_1603_; size_t v_i_boxed_1604_; lean_object* v_res_1605_; 
v_sz_boxed_1603_ = lean_unbox_usize(v_sz_1595_);
lean_dec(v_sz_1595_);
v_i_boxed_1604_ = lean_unbox_usize(v_i_1596_);
lean_dec(v_i_1596_);
v_res_1605_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1594_, v_sz_boxed_1603_, v_i_boxed_1604_, v_b_1597_, v___y_1598_, v___y_1599_, v___y_1600_, v___y_1601_);
lean_dec(v___y_1601_);
lean_dec_ref(v___y_1600_);
lean_dec(v___y_1599_);
lean_dec_ref(v___y_1598_);
lean_dec_ref(v_as_1594_);
return v_res_1605_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1606_, uint8_t v___x_1607_, lean_object* v_localDecl_1608_, lean_object* v_mvarId_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_){
_start:
{
lean_object* v___x_1615_; 
lean_inc_ref(v___x_1606_);
v___x_1615_ = l_Lean_Meta_forallMetaTelescope(v___x_1606_, v___x_1607_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v_fst_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1706_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
lean_inc(v_a_1616_);
lean_dec_ref_known(v___x_1615_, 1);
v_fst_1617_ = lean_ctor_get(v_a_1616_, 0);
v_isSharedCheck_1706_ = !lean_is_exclusive(v_a_1616_);
if (v_isSharedCheck_1706_ == 0)
{
lean_object* v_unused_1707_; 
v_unused_1707_ = lean_ctor_get(v_a_1616_, 1);
lean_dec(v_unused_1707_);
v___x_1619_ = v_a_1616_;
v_isShared_1620_ = v_isSharedCheck_1706_;
goto v_resetjp_1618_;
}
else
{
lean_inc(v_fst_1617_);
lean_dec(v_a_1616_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1706_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1621_ = l_Lean_Meta_mkGenDiseqMask(v___x_1606_);
lean_dec_ref(v___x_1606_);
v___x_1622_ = lean_unsigned_to_nat(0u);
v___x_1623_ = lean_array_get_size(v___x_1621_);
v___x_1624_ = l_Array_toSubarray___redArg(v___x_1621_, v___x_1622_, v___x_1623_);
v___x_1625_ = lean_box(0);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 1, v___x_1624_);
lean_ctor_set(v___x_1619_, 0, v___x_1625_);
v___x_1627_ = v___x_1619_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1705_; 
v_reuseFailAlloc_1705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1705_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1705_, 1, v___x_1624_);
v___x_1627_ = v_reuseFailAlloc_1705_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
size_t v_sz_1628_; size_t v___x_1629_; lean_object* v___x_1630_; 
v_sz_1628_ = lean_array_size(v_fst_1617_);
v___x_1629_ = ((size_t)0ULL);
v___x_1630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1617_, v_sz_1628_, v___x_1629_, v___x_1627_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1630_) == 0)
{
lean_object* v_a_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1696_; 
v_a_1631_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1633_ = v___x_1630_;
v_isShared_1634_ = v_isSharedCheck_1696_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_a_1631_);
lean_dec(v___x_1630_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1696_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
lean_object* v_fst_1635_; 
v_fst_1635_ = lean_ctor_get(v_a_1631_, 0);
lean_inc(v_fst_1635_);
lean_dec(v_a_1631_);
if (lean_obj_tag(v_fst_1635_) == 0)
{
lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1691_; 
lean_del_object(v___x_1633_);
v___x_1636_ = l_Lean_LocalDecl_toExpr(v_localDecl_1608_);
v___x_1637_ = l_Lean_mkAppN(v___x_1636_, v_fst_1617_);
lean_dec(v_fst_1617_);
v___x_1638_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1637_, v___y_1611_);
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1691_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1691_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v___x_1643_; 
lean_inc(v_a_1639_);
v___x_1643_ = l_Lean_Meta_hasAssignableMVar(v_a_1639_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1643_) == 0)
{
lean_object* v_a_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1682_; 
v_a_1644_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1682_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1682_ == 0)
{
v___x_1646_ = v___x_1643_;
v_isShared_1647_ = v_isSharedCheck_1682_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_a_1644_);
lean_dec(v___x_1643_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1682_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
uint8_t v___x_1648_; 
v___x_1648_ = lean_unbox(v_a_1644_);
lean_dec(v_a_1644_);
if (v___x_1648_ == 0)
{
lean_object* v___x_1649_; 
lean_del_object(v___x_1646_);
v___x_1649_ = l_Lean_MVarId_getType(v_mvarId_1609_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_a_1650_; lean_object* v___x_1651_; 
v_a_1650_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_a_1650_);
lean_dec_ref_known(v___x_1649_, 1);
v___x_1651_ = l_Lean_Meta_mkFalseElim(v_a_1650_, v_a_1639_, v___y_1610_, v___y_1611_, v___y_1612_, v___y_1613_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1662_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1662_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1662_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1662_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
lean_object* v___x_1657_; 
if (v_isShared_1642_ == 0)
{
lean_ctor_set_tag(v___x_1641_, 1);
lean_ctor_set(v___x_1641_, 0, v_a_1652_);
v___x_1657_ = v___x_1641_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_a_1652_);
v___x_1657_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
lean_object* v___x_1659_; 
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1657_);
v___x_1659_ = v___x_1654_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
else
{
lean_object* v_a_1663_; lean_object* v___x_1665_; uint8_t v_isShared_1666_; uint8_t v_isSharedCheck_1670_; 
lean_del_object(v___x_1641_);
v_a_1663_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1665_ = v___x_1651_;
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
else
{
lean_inc(v_a_1663_);
lean_dec(v___x_1651_);
v___x_1665_ = lean_box(0);
v_isShared_1666_ = v_isSharedCheck_1670_;
goto v_resetjp_1664_;
}
v_resetjp_1664_:
{
lean_object* v___x_1668_; 
if (v_isShared_1666_ == 0)
{
v___x_1668_ = v___x_1665_;
goto v_reusejp_1667_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1663_);
v___x_1668_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1667_;
}
v_reusejp_1667_:
{
return v___x_1668_;
}
}
}
}
else
{
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_del_object(v___x_1641_);
lean_dec(v_a_1639_);
v_a_1671_ = lean_ctor_get(v___x_1649_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1649_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1649_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1649_);
v___x_1673_ = lean_box(0);
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
v_resetjp_1672_:
{
lean_object* v___x_1676_; 
if (v_isShared_1674_ == 0)
{
v___x_1676_ = v___x_1673_;
goto v_reusejp_1675_;
}
else
{
lean_object* v_reuseFailAlloc_1677_; 
v_reuseFailAlloc_1677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1677_, 0, v_a_1671_);
v___x_1676_ = v_reuseFailAlloc_1677_;
goto v_reusejp_1675_;
}
v_reusejp_1675_:
{
return v___x_1676_;
}
}
}
}
else
{
lean_object* v___x_1680_; 
lean_del_object(v___x_1641_);
lean_dec(v_a_1639_);
lean_dec(v_mvarId_1609_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 0, v___x_1625_);
v___x_1680_ = v___x_1646_;
goto v_reusejp_1679_;
}
else
{
lean_object* v_reuseFailAlloc_1681_; 
v_reuseFailAlloc_1681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1681_, 0, v___x_1625_);
v___x_1680_ = v_reuseFailAlloc_1681_;
goto v_reusejp_1679_;
}
v_reusejp_1679_:
{
return v___x_1680_;
}
}
}
}
else
{
lean_object* v_a_1683_; lean_object* v___x_1685_; uint8_t v_isShared_1686_; uint8_t v_isSharedCheck_1690_; 
lean_del_object(v___x_1641_);
lean_dec(v_a_1639_);
lean_dec(v_mvarId_1609_);
v_a_1683_ = lean_ctor_get(v___x_1643_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1643_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1685_ = v___x_1643_;
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
else
{
lean_inc(v_a_1683_);
lean_dec(v___x_1643_);
v___x_1685_ = lean_box(0);
v_isShared_1686_ = v_isSharedCheck_1690_;
goto v_resetjp_1684_;
}
v_resetjp_1684_:
{
lean_object* v___x_1688_; 
if (v_isShared_1686_ == 0)
{
v___x_1688_ = v___x_1685_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v_a_1683_);
v___x_1688_ = v_reuseFailAlloc_1689_;
goto v_reusejp_1687_;
}
v_reusejp_1687_:
{
return v___x_1688_;
}
}
}
}
}
else
{
lean_object* v_val_1692_; lean_object* v___x_1694_; 
lean_dec(v_fst_1617_);
lean_dec(v_mvarId_1609_);
lean_dec_ref(v_localDecl_1608_);
v_val_1692_ = lean_ctor_get(v_fst_1635_, 0);
lean_inc(v_val_1692_);
lean_dec_ref_known(v_fst_1635_, 1);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v_val_1692_);
v___x_1694_ = v___x_1633_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_val_1692_);
v___x_1694_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
return v___x_1694_;
}
}
}
}
else
{
lean_object* v_a_1697_; lean_object* v___x_1699_; uint8_t v_isShared_1700_; uint8_t v_isSharedCheck_1704_; 
lean_dec(v_fst_1617_);
lean_dec(v_mvarId_1609_);
lean_dec_ref(v_localDecl_1608_);
v_a_1697_ = lean_ctor_get(v___x_1630_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1630_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1699_ = v___x_1630_;
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
else
{
lean_inc(v_a_1697_);
lean_dec(v___x_1630_);
v___x_1699_ = lean_box(0);
v_isShared_1700_ = v_isSharedCheck_1704_;
goto v_resetjp_1698_;
}
v_resetjp_1698_:
{
lean_object* v___x_1702_; 
if (v_isShared_1700_ == 0)
{
v___x_1702_ = v___x_1699_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_a_1697_);
v___x_1702_ = v_reuseFailAlloc_1703_;
goto v_reusejp_1701_;
}
v_reusejp_1701_:
{
return v___x_1702_;
}
}
}
}
}
}
else
{
lean_object* v_a_1708_; lean_object* v___x_1710_; uint8_t v_isShared_1711_; uint8_t v_isSharedCheck_1715_; 
lean_dec(v_mvarId_1609_);
lean_dec_ref(v_localDecl_1608_);
lean_dec_ref(v___x_1606_);
v_a_1708_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1715_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1715_ == 0)
{
v___x_1710_ = v___x_1615_;
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
else
{
lean_inc(v_a_1708_);
lean_dec(v___x_1615_);
v___x_1710_ = lean_box(0);
v_isShared_1711_ = v_isSharedCheck_1715_;
goto v_resetjp_1709_;
}
v_resetjp_1709_:
{
lean_object* v___x_1713_; 
if (v_isShared_1711_ == 0)
{
v___x_1713_ = v___x_1710_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1714_; 
v_reuseFailAlloc_1714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1714_, 0, v_a_1708_);
v___x_1713_ = v_reuseFailAlloc_1714_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
return v___x_1713_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1716_, lean_object* v___x_1717_, lean_object* v_localDecl_1718_, lean_object* v_mvarId_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_){
_start:
{
uint8_t v___x_6078__boxed_1725_; lean_object* v_res_1726_; 
v___x_6078__boxed_1725_ = lean_unbox(v___x_1717_);
v_res_1726_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1716_, v___x_6078__boxed_1725_, v_localDecl_1718_, v_mvarId_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
lean_dec(v___y_1723_);
lean_dec_ref(v___y_1722_);
lean_dec(v___y_1721_);
lean_dec_ref(v___y_1720_);
return v_res_1726_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1730_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1731_ = lean_unsigned_to_nat(2u);
v___x_1732_ = lean_unsigned_to_nat(120u);
v___x_1733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1735_ = l_mkPanicMessageWithDecl(v___x_1734_, v___x_1733_, v___x_1732_, v___x_1731_, v___x_1730_);
return v___x_1735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1736_, lean_object* v_localDecl_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_){
_start:
{
lean_object* v___x_1743_; uint8_t v___x_1744_; 
v___x_1743_ = l_Lean_LocalDecl_type(v_localDecl_1737_);
lean_inc_ref(v___x_1743_);
v___x_1744_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1743_);
if (v___x_1744_ == 0)
{
lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_dec_ref(v___x_1743_);
lean_dec_ref(v_localDecl_1737_);
lean_dec(v_mvarId_1736_);
v___x_1745_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1746_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1745_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
return v___x_1746_;
}
else
{
uint8_t v___x_1747_; lean_object* v___x_1748_; lean_object* v___f_1749_; uint8_t v___x_1750_; lean_object* v___x_1751_; 
v___x_1747_ = 0;
v___x_1748_ = lean_box(v___x_1747_);
lean_inc(v_mvarId_1736_);
v___f_1749_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1749_, 0, v___x_1743_);
lean_closure_set(v___f_1749_, 1, v___x_1748_);
lean_closure_set(v___f_1749_, 2, v_localDecl_1737_);
lean_closure_set(v___f_1749_, 3, v_mvarId_1736_);
v___x_1750_ = 0;
v___x_1751_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1749_, v___x_1750_, v_a_1738_, v_a_1739_, v_a_1740_, v_a_1741_);
if (lean_obj_tag(v___x_1751_) == 0)
{
lean_object* v_a_1752_; lean_object* v___x_1754_; uint8_t v_isShared_1755_; uint8_t v_isSharedCheck_1771_; 
v_a_1752_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1771_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1771_ == 0)
{
v___x_1754_ = v___x_1751_;
v_isShared_1755_ = v_isSharedCheck_1771_;
goto v_resetjp_1753_;
}
else
{
lean_inc(v_a_1752_);
lean_dec(v___x_1751_);
v___x_1754_ = lean_box(0);
v_isShared_1755_ = v_isSharedCheck_1771_;
goto v_resetjp_1753_;
}
v_resetjp_1753_:
{
if (lean_obj_tag(v_a_1752_) == 1)
{
lean_object* v_val_1756_; lean_object* v___x_1757_; lean_object* v___x_1759_; uint8_t v_isShared_1760_; uint8_t v_isSharedCheck_1765_; 
lean_del_object(v___x_1754_);
v_val_1756_ = lean_ctor_get(v_a_1752_, 0);
lean_inc(v_val_1756_);
lean_dec_ref_known(v_a_1752_, 1);
v___x_1757_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1736_, v_val_1756_, v_a_1739_);
v_isSharedCheck_1765_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1765_ == 0)
{
lean_object* v_unused_1766_; 
v_unused_1766_ = lean_ctor_get(v___x_1757_, 0);
lean_dec(v_unused_1766_);
v___x_1759_ = v___x_1757_;
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
else
{
lean_dec(v___x_1757_);
v___x_1759_ = lean_box(0);
v_isShared_1760_ = v_isSharedCheck_1765_;
goto v_resetjp_1758_;
}
v_resetjp_1758_:
{
lean_object* v___x_1761_; lean_object* v___x_1763_; 
v___x_1761_ = lean_box(v___x_1744_);
if (v_isShared_1760_ == 0)
{
lean_ctor_set(v___x_1759_, 0, v___x_1761_);
v___x_1763_ = v___x_1759_;
goto v_reusejp_1762_;
}
else
{
lean_object* v_reuseFailAlloc_1764_; 
v_reuseFailAlloc_1764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1764_, 0, v___x_1761_);
v___x_1763_ = v_reuseFailAlloc_1764_;
goto v_reusejp_1762_;
}
v_reusejp_1762_:
{
return v___x_1763_;
}
}
}
else
{
lean_object* v___x_1767_; lean_object* v___x_1769_; 
lean_dec(v_a_1752_);
lean_dec(v_mvarId_1736_);
v___x_1767_ = lean_box(v___x_1750_);
if (v_isShared_1755_ == 0)
{
lean_ctor_set(v___x_1754_, 0, v___x_1767_);
v___x_1769_ = v___x_1754_;
goto v_reusejp_1768_;
}
else
{
lean_object* v_reuseFailAlloc_1770_; 
v_reuseFailAlloc_1770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1770_, 0, v___x_1767_);
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
else
{
lean_object* v_a_1772_; lean_object* v___x_1774_; uint8_t v_isShared_1775_; uint8_t v_isSharedCheck_1779_; 
lean_dec(v_mvarId_1736_);
v_a_1772_ = lean_ctor_get(v___x_1751_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1751_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1774_ = v___x_1751_;
v_isShared_1775_ = v_isSharedCheck_1779_;
goto v_resetjp_1773_;
}
else
{
lean_inc(v_a_1772_);
lean_dec(v___x_1751_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1780_, lean_object* v_localDecl_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v_res_1787_; 
v_res_1787_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1780_, v_localDecl_1781_, v_a_1782_, v_a_1783_, v_a_1784_, v_a_1785_);
lean_dec(v_a_1785_);
lean_dec_ref(v_a_1784_);
lean_dec(v_a_1783_);
lean_dec_ref(v_a_1782_);
return v_res_1787_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1799_ = lean_box(0);
v___x_1800_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1801_ = l_Lean_mkConst(v___x_1800_, v___x_1799_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1802_; lean_object* v_dummy_1803_; 
v___x_1802_ = lean_box(0);
v_dummy_1803_ = l_Lean_Expr_sort___override(v___x_1802_);
return v_dummy_1803_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1804_, lean_object* v_mvarId_1805_, lean_object* v_as_1806_, size_t v_sz_1807_, size_t v_i_1808_, lean_object* v_b_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_){
_start:
{
uint8_t v___x_1815_; 
v___x_1815_ = lean_usize_dec_lt(v_i_1808_, v_sz_1807_);
if (v___x_1815_ == 0)
{
lean_object* v___x_1816_; 
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v___x_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1816_, 0, v_b_1809_);
return v___x_1816_;
}
else
{
lean_object* v_snd_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_2398_; 
v_snd_1817_ = lean_ctor_get(v_b_1809_, 1);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_b_1809_);
if (v_isSharedCheck_2398_ == 0)
{
lean_object* v_unused_2399_; 
v_unused_2399_ = lean_ctor_get(v_b_1809_, 0);
lean_dec(v_unused_2399_);
v___x_1819_ = v_b_1809_;
v_isShared_1820_ = v_isSharedCheck_2398_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_snd_1817_);
lean_dec(v_b_1809_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_2398_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v_a_1822_; lean_object* v___x_1828_; lean_object* v_a_1830_; lean_object* v_a_1835_; 
v___x_1828_ = lean_box(0);
v_a_1835_ = lean_array_uget(v_as_1806_, v_i_1808_);
if (lean_obj_tag(v_a_1835_) == 0)
{
lean_del_object(v___x_1819_);
v_a_1830_ = v_snd_1817_;
goto v___jp_1829_;
}
else
{
lean_object* v_val_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_2397_; 
v_val_1836_ = lean_ctor_get(v_a_1835_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v_a_1835_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_1838_ = v_a_1835_;
v_isShared_1839_ = v_isSharedCheck_2397_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_val_1836_);
lean_dec(v_a_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_2397_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; uint8_t v___y_1843_; uint8_t v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; uint8_t v___x_1868_; 
v___x_1840_ = lean_box(0);
v___x_1841_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1868_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1836_);
if (v___x_1868_ == 0)
{
lean_object* v___x_1869_; uint8_t v___y_1871_; uint8_t v___y_1872_; lean_object* v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; uint8_t v___y_1894_; lean_object* v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; uint8_t v___y_1898_; lean_object* v___y_1899_; lean_object* v_a_1900_; uint8_t v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; uint8_t v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; uint8_t v___y_1950_; uint8_t v_isHEq_1951_; lean_object* v___y_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; uint8_t v_isEq_1993_; lean_object* v___y_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_2109_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2200_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___x_2334_; 
v___x_1869_ = l_Lean_LocalDecl_type(v_val_1836_);
lean_inc_ref(v___x_1869_);
v___x_2334_ = l_Lean_Meta_matchNot_x3f(v___x_1869_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
if (lean_obj_tag(v_a_2335_) == 1)
{
lean_object* v_val_2336_; lean_object* v___x_2337_; 
v_val_2336_ = lean_ctor_get(v_a_2335_, 0);
lean_inc(v_val_2336_);
lean_dec_ref_known(v_a_2335_, 1);
v___x_2337_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2336_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
if (lean_obj_tag(v_a_2338_) == 1)
{
lean_object* v_val_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec_ref(v_config_1804_);
v_val_2339_ = lean_ctor_get(v_a_2338_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v_a_2338_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2341_ = v_a_2338_;
v_isShared_2342_ = v_isSharedCheck_2380_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_val_2339_);
lean_dec(v_a_2338_);
v___x_2341_ = lean_box(0);
v_isShared_2342_ = v_isSharedCheck_2380_;
goto v_resetjp_2340_;
}
v_resetjp_2340_:
{
lean_object* v___x_2343_; 
lean_inc(v_mvarId_1805_);
v___x_2343_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v___x_2345_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_2346_ = l_Lean_mkFVar(v_val_2339_);
v___x_2347_ = l_Lean_Expr_app___override(v___x_2345_, v___x_2346_);
v___x_2348_ = l_Lean_Meta_mkFalseElim(v_a_2344_, v___x_2347_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_2349_, v___y_1811_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v___x_2351_; lean_object* v___x_2353_; 
lean_dec_ref_known(v___x_2350_, 1);
v___x_2351_ = lean_box(v___x_1815_);
if (v_isShared_2342_ == 0)
{
lean_ctor_set(v___x_2341_, 0, v___x_2351_);
v___x_2353_ = v___x_2341_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2355_; 
v_reuseFailAlloc_2355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2355_, 0, v___x_2351_);
v___x_2353_ = v_reuseFailAlloc_2355_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
lean_object* v___x_2354_; 
v___x_2354_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
lean_ctor_set(v___x_2354_, 1, v___x_1840_);
v_a_1822_ = v___x_2354_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_del_object(v___x_2341_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_2356_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2350_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2350_);
v___x_2358_ = lean_box(0);
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
v_resetjp_2357_:
{
lean_object* v___x_2361_; 
if (v_isShared_2359_ == 0)
{
v___x_2361_ = v___x_2358_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v_a_2356_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
}
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_del_object(v___x_2341_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2364_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2348_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2348_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
lean_del_object(v___x_2341_);
lean_dec(v_val_2339_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2372_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2343_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2343_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
else
{
lean_dec(v_a_2338_);
v___y_2200_ = v___y_1810_;
v___y_2201_ = v___y_1811_;
v___y_2202_ = v___y_1812_;
v___y_2203_ = v___y_1813_;
goto v___jp_2199_;
}
}
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2381_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2337_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2337_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
else
{
lean_dec(v_a_2335_);
v___y_2200_ = v___y_1810_;
v___y_2201_ = v___y_1811_;
v___y_2202_ = v___y_1812_;
v___y_2203_ = v___y_1813_;
goto v___jp_2199_;
}
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2389_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2334_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2334_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
v___jp_1870_:
{
uint8_t v_genDiseq_1877_; 
v_genDiseq_1877_ = lean_ctor_get_uint8(v_config_1804_, sizeof(void*)*1 + 2);
if (v_genDiseq_1877_ == 0)
{
lean_dec_ref(v___x_1869_);
v___y_1843_ = v___y_1871_;
v___y_1844_ = v___y_1872_;
v___y_1845_ = v___y_1873_;
v___y_1846_ = v___y_1874_;
v___y_1847_ = v___y_1875_;
v___y_1848_ = v___y_1876_;
goto v___jp_1842_;
}
else
{
uint8_t v___x_1878_; 
v___x_1878_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1869_);
if (v___x_1878_ == 0)
{
v___y_1843_ = v___y_1871_;
v___y_1844_ = v___y_1872_;
v___y_1845_ = v___y_1873_;
v___y_1846_ = v___y_1874_;
v___y_1847_ = v___y_1875_;
v___y_1848_ = v___y_1876_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1879_; 
lean_inc(v_val_1836_);
lean_inc(v_mvarId_1805_);
v___x_1879_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1805_, v_val_1836_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_);
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
v___y_1843_ = v___y_1871_;
v___y_1844_ = v___y_1872_;
v___y_1845_ = v___y_1873_;
v___y_1846_ = v___y_1874_;
v___y_1847_ = v___y_1875_;
v___y_1848_ = v___y_1876_;
goto v___jp_1842_;
}
else
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v___x_1882_ = lean_box(v___x_1815_);
v___x_1883_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1883_, 0, v___x_1882_);
v___x_1884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
lean_ctor_set(v___x_1884_, 1, v___x_1840_);
v_a_1822_ = v___x_1884_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_1885_; lean_object* v___x_1887_; uint8_t v_isShared_1888_; uint8_t v_isSharedCheck_1892_; 
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_1885_ = lean_ctor_get(v___x_1879_, 0);
v_isSharedCheck_1892_ = !lean_is_exclusive(v___x_1879_);
if (v_isSharedCheck_1892_ == 0)
{
v___x_1887_ = v___x_1879_;
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
else
{
lean_inc(v_a_1885_);
lean_dec(v___x_1879_);
v___x_1887_ = lean_box(0);
v_isShared_1888_ = v_isSharedCheck_1892_;
goto v_resetjp_1886_;
}
v_resetjp_1886_:
{
lean_object* v___x_1890_; 
if (v_isShared_1888_ == 0)
{
v___x_1890_ = v___x_1887_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1891_; 
v_reuseFailAlloc_1891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1891_, 0, v_a_1885_);
v___x_1890_ = v_reuseFailAlloc_1891_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
return v___x_1890_;
}
}
}
}
}
}
v___jp_1893_:
{
uint8_t v___x_1901_; 
v___x_1901_ = l_Lean_Exception_isInterrupt(v_a_1900_);
if (v___x_1901_ == 0)
{
uint8_t v___x_1902_; 
lean_inc_ref(v_a_1900_);
v___x_1902_ = l_Lean_Exception_isRuntime(v_a_1900_);
if (v___x_1902_ == 0)
{
lean_dec_ref(v_a_1900_);
v___y_1871_ = v___y_1894_;
v___y_1872_ = v___y_1898_;
v___y_1873_ = v___y_1899_;
v___y_1874_ = v___y_1897_;
v___y_1875_ = v___y_1896_;
v___y_1876_ = v___y_1895_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1903_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v___x_1903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1903_, 0, v_a_1900_);
return v___x_1903_;
}
}
else
{
lean_object* v___x_1904_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v___x_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_a_1900_);
return v___x_1904_;
}
}
v___jp_1905_:
{
if (lean_obj_tag(v___y_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; uint8_t v___x_1916_; 
v_a_1914_ = lean_ctor_get(v___y_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___y_1913_, 1);
v___x_1915_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_1916_ = l_Lean_Expr_isConstOf(v_a_1914_, v___x_1915_);
lean_dec(v_a_1914_);
if (v___x_1916_ == 0)
{
lean_dec_ref(v___y_1908_);
v___y_1871_ = v___y_1906_;
v___y_1872_ = v___y_1911_;
v___y_1873_ = v___y_1912_;
v___y_1874_ = v___y_1910_;
v___y_1875_ = v___y_1909_;
v___y_1876_ = v___y_1907_;
goto v___jp_1870_;
}
else
{
lean_object* v___x_1917_; 
lean_inc_ref(v___y_1908_);
v___x_1917_ = l_Lean_Meta_mkEqRefl(v___y_1908_, v___y_1912_, v___y_1910_, v___y_1909_, v___y_1907_);
if (lean_obj_tag(v___x_1917_) == 0)
{
lean_object* v_a_1918_; lean_object* v___x_1919_; lean_object* v_dummy_1920_; lean_object* v_nargs_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v_a_1918_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1918_);
lean_dec_ref_known(v___x_1917_, 1);
v___x_1919_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_1920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_1921_ = l_Lean_Expr_getAppNumArgs(v___y_1908_);
lean_inc(v_nargs_1921_);
v___x_1922_ = lean_mk_array(v_nargs_1921_, v_dummy_1920_);
v___x_1923_ = lean_unsigned_to_nat(1u);
v___x_1924_ = lean_nat_sub(v_nargs_1921_, v___x_1923_);
lean_dec(v_nargs_1921_);
v___x_1925_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_1908_, v___x_1922_, v___x_1924_);
v___x_1926_ = lean_array_push(v___x_1925_, v_a_1918_);
v___x_1927_ = l_Lean_mkAppN(v___x_1919_, v___x_1926_);
lean_dec_ref(v___x_1926_);
lean_inc(v_mvarId_1805_);
v___x_1928_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_1912_, v___y_1910_, v___y_1909_, v___y_1907_);
if (lean_obj_tag(v___x_1928_) == 0)
{
lean_object* v_a_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v_a_1929_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1929_);
lean_dec_ref_known(v___x_1928_, 1);
lean_inc(v_val_1836_);
v___x_1930_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_1931_ = l_Lean_Meta_mkAbsurd(v_a_1929_, v___x_1930_, v___x_1927_, v___y_1912_, v___y_1910_, v___y_1909_, v___y_1907_);
if (lean_obj_tag(v___x_1931_) == 0)
{
lean_object* v_a_1932_; lean_object* v___x_1933_; 
v_a_1932_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1932_);
lean_dec_ref_known(v___x_1931_, 1);
lean_inc(v_mvarId_1805_);
v___x_1933_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_1932_, v___y_1910_);
if (lean_obj_tag(v___x_1933_) == 0)
{
lean_object* v___x_1935_; uint8_t v_isShared_1936_; uint8_t v_isSharedCheck_1942_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_isSharedCheck_1942_ = !lean_is_exclusive(v___x_1933_);
if (v_isSharedCheck_1942_ == 0)
{
lean_object* v_unused_1943_; 
v_unused_1943_ = lean_ctor_get(v___x_1933_, 0);
lean_dec(v_unused_1943_);
v___x_1935_ = v___x_1933_;
v_isShared_1936_ = v_isSharedCheck_1942_;
goto v_resetjp_1934_;
}
else
{
lean_dec(v___x_1933_);
v___x_1935_ = lean_box(0);
v_isShared_1936_ = v_isSharedCheck_1942_;
goto v_resetjp_1934_;
}
v_resetjp_1934_:
{
lean_object* v___x_1937_; lean_object* v___x_1939_; 
v___x_1937_ = lean_box(v___x_1815_);
if (v_isShared_1936_ == 0)
{
lean_ctor_set_tag(v___x_1935_, 1);
lean_ctor_set(v___x_1935_, 0, v___x_1937_);
v___x_1939_ = v___x_1935_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1941_; 
v_reuseFailAlloc_1941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1941_, 0, v___x_1937_);
v___x_1939_ = v_reuseFailAlloc_1941_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1940_, 0, v___x_1939_);
lean_ctor_set(v___x_1940_, 1, v___x_1840_);
v_a_1822_ = v___x_1940_;
goto v___jp_1821_;
}
}
}
else
{
lean_object* v_a_1944_; 
v_a_1944_ = lean_ctor_get(v___x_1933_, 0);
lean_inc(v_a_1944_);
lean_dec_ref_known(v___x_1933_, 1);
v___y_1894_ = v___y_1906_;
v___y_1895_ = v___y_1907_;
v___y_1896_ = v___y_1909_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v_a_1900_ = v_a_1944_;
goto v___jp_1893_;
}
}
else
{
lean_object* v_a_1945_; 
v_a_1945_ = lean_ctor_get(v___x_1931_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1931_, 1);
v___y_1894_ = v___y_1906_;
v___y_1895_ = v___y_1907_;
v___y_1896_ = v___y_1909_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v_a_1900_ = v_a_1945_;
goto v___jp_1893_;
}
}
else
{
lean_object* v_a_1946_; 
lean_dec_ref(v___x_1927_);
v_a_1946_ = lean_ctor_get(v___x_1928_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1928_, 1);
v___y_1894_ = v___y_1906_;
v___y_1895_ = v___y_1907_;
v___y_1896_ = v___y_1909_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v_a_1900_ = v_a_1946_;
goto v___jp_1893_;
}
}
else
{
lean_object* v_a_1947_; 
lean_dec_ref(v___y_1908_);
v_a_1947_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1917_, 1);
v___y_1894_ = v___y_1906_;
v___y_1895_ = v___y_1907_;
v___y_1896_ = v___y_1909_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v_a_1900_ = v_a_1947_;
goto v___jp_1893_;
}
}
}
else
{
lean_object* v_a_1948_; 
lean_dec_ref(v___y_1908_);
v_a_1948_ = lean_ctor_get(v___y_1913_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___y_1913_, 1);
v___y_1894_ = v___y_1906_;
v___y_1895_ = v___y_1907_;
v___y_1896_ = v___y_1909_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v_a_1900_ = v_a_1948_;
goto v___jp_1893_;
}
}
v___jp_1949_:
{
uint8_t v_useDecide_1956_; 
v_useDecide_1956_ = lean_ctor_get_uint8(v_config_1804_, sizeof(void*)*1);
if (v_useDecide_1956_ == 0)
{
v___y_1871_ = v_isHEq_1951_;
v___y_1872_ = v___y_1950_;
v___y_1873_ = v___y_1952_;
v___y_1874_ = v___y_1953_;
v___y_1875_ = v___y_1954_;
v___y_1876_ = v___y_1955_;
goto v___jp_1870_;
}
else
{
uint8_t v___x_1957_; 
v___x_1957_ = l_Lean_Expr_hasFVar(v___x_1869_);
if (v___x_1957_ == 0)
{
lean_object* v___x_1958_; 
lean_inc_ref(v___x_1869_);
v___x_1958_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1869_, v___y_1953_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; uint8_t v___x_1960_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
lean_dec_ref_known(v___x_1958_, 1);
v___x_1960_ = l_Lean_Expr_hasMVar(v_a_1959_);
if (v___x_1960_ == 0)
{
uint8_t v___x_1961_; 
v___x_1961_ = l_Lean_Expr_hasFVar(v_a_1959_);
lean_dec(v_a_1959_);
if (v___x_1961_ == 0)
{
lean_object* v___x_1962_; 
lean_inc_ref(v___x_1869_);
v___x_1962_ = l_Lean_Meta_mkDecide(v___x_1869_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v___x_1964_; uint8_t v_transparency_1965_; uint8_t v___x_1966_; uint8_t v___x_1967_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1963_);
lean_dec_ref_known(v___x_1962_, 1);
v___x_1964_ = l_Lean_Meta_Context_config(v___y_1952_);
v_transparency_1965_ = lean_ctor_get_uint8(v___x_1964_, 9);
lean_dec_ref(v___x_1964_);
v___x_1966_ = 1;
v___x_1967_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1965_, v___x_1966_);
if (v___x_1967_ == 0)
{
lean_object* v_keyedConfig_1968_; uint8_t v_trackZetaDelta_1969_; lean_object* v_zetaDeltaSet_1970_; lean_object* v_lctx_1971_; lean_object* v_localInstances_1972_; lean_object* v_defEqCtx_x3f_1973_; lean_object* v_synthPendingDepth_1974_; lean_object* v_customCanUnfoldPredicate_x3f_1975_; uint8_t v_univApprox_1976_; uint8_t v_inTypeClassResolution_1977_; uint8_t v_cacheInferType_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v_keyedConfig_1968_ = lean_ctor_get(v___y_1952_, 0);
v_trackZetaDelta_1969_ = lean_ctor_get_uint8(v___y_1952_, sizeof(void*)*7);
v_zetaDeltaSet_1970_ = lean_ctor_get(v___y_1952_, 1);
v_lctx_1971_ = lean_ctor_get(v___y_1952_, 2);
v_localInstances_1972_ = lean_ctor_get(v___y_1952_, 3);
v_defEqCtx_x3f_1973_ = lean_ctor_get(v___y_1952_, 4);
v_synthPendingDepth_1974_ = lean_ctor_get(v___y_1952_, 5);
v_customCanUnfoldPredicate_x3f_1975_ = lean_ctor_get(v___y_1952_, 6);
v_univApprox_1976_ = lean_ctor_get_uint8(v___y_1952_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1977_ = lean_ctor_get_uint8(v___y_1952_, sizeof(void*)*7 + 2);
v_cacheInferType_1978_ = lean_ctor_get_uint8(v___y_1952_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1968_);
v___x_1979_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1966_, v_keyedConfig_1968_);
lean_inc(v_customCanUnfoldPredicate_x3f_1975_);
lean_inc(v_synthPendingDepth_1974_);
lean_inc(v_defEqCtx_x3f_1973_);
lean_inc_ref(v_localInstances_1972_);
lean_inc_ref(v_lctx_1971_);
lean_inc(v_zetaDeltaSet_1970_);
v___x_1980_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1980_, 0, v___x_1979_);
lean_ctor_set(v___x_1980_, 1, v_zetaDeltaSet_1970_);
lean_ctor_set(v___x_1980_, 2, v_lctx_1971_);
lean_ctor_set(v___x_1980_, 3, v_localInstances_1972_);
lean_ctor_set(v___x_1980_, 4, v_defEqCtx_x3f_1973_);
lean_ctor_set(v___x_1980_, 5, v_synthPendingDepth_1974_);
lean_ctor_set(v___x_1980_, 6, v_customCanUnfoldPredicate_x3f_1975_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*7, v_trackZetaDelta_1969_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*7 + 1, v_univApprox_1976_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1977_);
lean_ctor_set_uint8(v___x_1980_, sizeof(void*)*7 + 3, v_cacheInferType_1978_);
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1953_);
lean_inc(v_a_1963_);
v___x_1981_ = lean_whnf(v_a_1963_, v___x_1980_, v___y_1953_, v___y_1954_, v___y_1955_);
v___y_1906_ = v_isHEq_1951_;
v___y_1907_ = v___y_1955_;
v___y_1908_ = v_a_1963_;
v___y_1909_ = v___y_1954_;
v___y_1910_ = v___y_1953_;
v___y_1911_ = v___y_1950_;
v___y_1912_ = v___y_1952_;
v___y_1913_ = v___x_1981_;
goto v___jp_1905_;
}
else
{
lean_object* v___x_1982_; 
lean_inc(v___y_1955_);
lean_inc_ref(v___y_1954_);
lean_inc(v___y_1953_);
lean_inc_ref(v___y_1952_);
lean_inc(v_a_1963_);
v___x_1982_ = lean_whnf(v_a_1963_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
v___y_1906_ = v_isHEq_1951_;
v___y_1907_ = v___y_1955_;
v___y_1908_ = v_a_1963_;
v___y_1909_ = v___y_1954_;
v___y_1910_ = v___y_1953_;
v___y_1911_ = v___y_1950_;
v___y_1912_ = v___y_1952_;
v___y_1913_ = v___x_1982_;
goto v___jp_1905_;
}
}
else
{
lean_object* v_a_1983_; 
v_a_1983_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_a_1983_);
lean_dec_ref_known(v___x_1962_, 1);
v___y_1894_ = v_isHEq_1951_;
v___y_1895_ = v___y_1955_;
v___y_1896_ = v___y_1954_;
v___y_1897_ = v___y_1953_;
v___y_1898_ = v___y_1950_;
v___y_1899_ = v___y_1952_;
v_a_1900_ = v_a_1983_;
goto v___jp_1893_;
}
}
else
{
v___y_1871_ = v_isHEq_1951_;
v___y_1872_ = v___y_1950_;
v___y_1873_ = v___y_1952_;
v___y_1874_ = v___y_1953_;
v___y_1875_ = v___y_1954_;
v___y_1876_ = v___y_1955_;
goto v___jp_1870_;
}
}
else
{
lean_dec(v_a_1959_);
v___y_1871_ = v_isHEq_1951_;
v___y_1872_ = v___y_1950_;
v___y_1873_ = v___y_1952_;
v___y_1874_ = v___y_1953_;
v___y_1875_ = v___y_1954_;
v___y_1876_ = v___y_1955_;
goto v___jp_1870_;
}
}
else
{
lean_object* v_a_1984_; lean_object* v___x_1986_; uint8_t v_isShared_1987_; uint8_t v_isSharedCheck_1991_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_1984_ = lean_ctor_get(v___x_1958_, 0);
v_isSharedCheck_1991_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_1991_ == 0)
{
v___x_1986_ = v___x_1958_;
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
else
{
lean_inc(v_a_1984_);
lean_dec(v___x_1958_);
v___x_1986_ = lean_box(0);
v_isShared_1987_ = v_isSharedCheck_1991_;
goto v_resetjp_1985_;
}
v_resetjp_1985_:
{
lean_object* v___x_1989_; 
if (v_isShared_1987_ == 0)
{
v___x_1989_ = v___x_1986_;
goto v_reusejp_1988_;
}
else
{
lean_object* v_reuseFailAlloc_1990_; 
v_reuseFailAlloc_1990_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1990_, 0, v_a_1984_);
v___x_1989_ = v_reuseFailAlloc_1990_;
goto v_reusejp_1988_;
}
v_reusejp_1988_:
{
return v___x_1989_;
}
}
}
}
else
{
v___y_1871_ = v_isHEq_1951_;
v___y_1872_ = v___y_1950_;
v___y_1873_ = v___y_1952_;
v___y_1874_ = v___y_1953_;
v___y_1875_ = v___y_1954_;
v___y_1876_ = v___y_1955_;
goto v___jp_1870_;
}
}
}
v___jp_1992_:
{
lean_object* v___x_1998_; 
lean_inc_ref(v___x_1869_);
v___x_1998_ = l_Lean_Meta_matchHEq_x3f(v___x_1869_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_1998_) == 0)
{
lean_object* v_a_1999_; 
v_a_1999_ = lean_ctor_get(v___x_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___x_1998_, 1);
if (lean_obj_tag(v_a_1999_) == 1)
{
lean_object* v_val_2000_; lean_object* v_snd_2001_; lean_object* v_snd_2002_; lean_object* v_fst_2003_; lean_object* v_fst_2004_; lean_object* v_fst_2005_; lean_object* v_snd_2006_; lean_object* v___x_2008_; uint8_t v_isShared_2009_; uint8_t v_isSharedCheck_2099_; 
v_val_2000_ = lean_ctor_get(v_a_1999_, 0);
lean_inc(v_val_2000_);
lean_dec_ref_known(v_a_1999_, 1);
v_snd_2001_ = lean_ctor_get(v_val_2000_, 1);
lean_inc(v_snd_2001_);
v_snd_2002_ = lean_ctor_get(v_snd_2001_, 1);
lean_inc(v_snd_2002_);
v_fst_2003_ = lean_ctor_get(v_val_2000_, 0);
lean_inc(v_fst_2003_);
lean_dec(v_val_2000_);
v_fst_2004_ = lean_ctor_get(v_snd_2001_, 0);
lean_inc(v_fst_2004_);
lean_dec(v_snd_2001_);
v_fst_2005_ = lean_ctor_get(v_snd_2002_, 0);
v_snd_2006_ = lean_ctor_get(v_snd_2002_, 1);
v_isSharedCheck_2099_ = !lean_is_exclusive(v_snd_2002_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2008_ = v_snd_2002_;
v_isShared_2009_ = v_isSharedCheck_2099_;
goto v_resetjp_2007_;
}
else
{
lean_inc(v_snd_2006_);
lean_inc(v_fst_2005_);
lean_dec(v_snd_2002_);
v___x_2008_ = lean_box(0);
v_isShared_2009_ = v_isSharedCheck_2099_;
goto v_resetjp_2007_;
}
v_resetjp_2007_:
{
lean_object* v___x_2010_; 
v___x_2010_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2004_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
if (lean_obj_tag(v_a_2011_) == 1)
{
lean_object* v_val_2012_; lean_object* v___x_2013_; 
v_val_2012_ = lean_ctor_get(v_a_2011_, 0);
lean_inc(v_val_2012_);
lean_dec_ref_known(v_a_2011_, 1);
v___x_2013_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2006_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
if (lean_obj_tag(v_a_2014_) == 1)
{
lean_object* v_toConstantVal_2015_; lean_object* v_val_2016_; lean_object* v___x_2018_; uint8_t v_isShared_2019_; uint8_t v_isSharedCheck_2082_; 
v_toConstantVal_2015_ = lean_ctor_get(v_val_2012_, 0);
lean_inc_ref(v_toConstantVal_2015_);
lean_dec(v_val_2012_);
v_val_2016_ = lean_ctor_get(v_a_2014_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v_a_2014_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2018_ = v_a_2014_;
v_isShared_2019_ = v_isSharedCheck_2082_;
goto v_resetjp_2017_;
}
else
{
lean_inc(v_val_2016_);
lean_dec(v_a_2014_);
v___x_2018_ = lean_box(0);
v_isShared_2019_ = v_isSharedCheck_2082_;
goto v_resetjp_2017_;
}
v_resetjp_2017_:
{
lean_object* v_toConstantVal_2020_; lean_object* v_name_2021_; lean_object* v_name_2022_; uint8_t v___x_2023_; 
v_toConstantVal_2020_ = lean_ctor_get(v_val_2016_, 0);
lean_inc_ref(v_toConstantVal_2020_);
lean_dec(v_val_2016_);
v_name_2021_ = lean_ctor_get(v_toConstantVal_2015_, 0);
lean_inc(v_name_2021_);
lean_dec_ref(v_toConstantVal_2015_);
v_name_2022_ = lean_ctor_get(v_toConstantVal_2020_, 0);
lean_inc(v_name_2022_);
lean_dec_ref(v_toConstantVal_2020_);
v___x_2023_ = lean_name_eq(v_name_2021_, v_name_2022_);
lean_dec(v_name_2022_);
lean_dec(v_name_2021_);
if (v___x_2023_ == 0)
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_Meta_isExprDefEq(v_fst_2003_, v_fst_2005_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; uint8_t v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
v___x_2026_ = lean_unbox(v_a_2025_);
lean_dec(v_a_2025_);
if (v___x_2026_ == 0)
{
lean_del_object(v___x_2018_);
lean_del_object(v___x_2008_);
v___y_1950_ = v_isEq_1993_;
v_isHEq_1951_ = v___x_1815_;
v___y_1952_ = v___y_1994_;
v___y_1953_ = v___y_1995_;
v___y_1954_ = v___y_1996_;
v___y_1955_ = v___y_1997_;
goto v___jp_1949_;
}
else
{
lean_object* v___x_2027_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec_ref(v_config_1804_);
lean_inc(v_mvarId_1805_);
v___x_2027_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v_a_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v_a_2028_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2028_);
lean_dec_ref_known(v___x_2027_, 1);
v___x_2029_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_2030_ = l_Lean_Meta_mkEqOfHEq(v___x_2029_, v___x_1815_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2030_) == 0)
{
lean_object* v_a_2031_; lean_object* v___x_2032_; 
v_a_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2030_, 1);
v___x_2032_ = l_Lean_Meta_mkNoConfusion(v_a_2028_, v_a_2031_, v___y_1994_, v___y_1995_, v___y_1996_, v___y_1997_);
if (lean_obj_tag(v___x_2032_) == 0)
{
lean_object* v_a_2033_; lean_object* v___x_2034_; 
v_a_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2032_, 1);
v___x_2034_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_2033_, v___y_1995_);
if (lean_obj_tag(v___x_2034_) == 0)
{
lean_object* v___x_2035_; lean_object* v___x_2037_; 
lean_dec_ref_known(v___x_2034_, 1);
v___x_2035_ = lean_box(v___x_1815_);
if (v_isShared_2019_ == 0)
{
lean_ctor_set(v___x_2018_, 0, v___x_2035_);
v___x_2037_ = v___x_2018_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2039_; 
if (v_isShared_2009_ == 0)
{
lean_ctor_set(v___x_2008_, 1, v___x_1840_);
lean_ctor_set(v___x_2008_, 0, v___x_2037_);
v___x_2039_ = v___x_2008_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v___x_1840_);
v___x_2039_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
v_a_1822_ = v___x_2039_;
goto v___jp_1821_;
}
}
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_del_object(v___x_2018_);
lean_del_object(v___x_2008_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_2042_ = lean_ctor_get(v___x_2034_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2034_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2034_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2034_);
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
else
{
lean_object* v_a_2050_; lean_object* v___x_2052_; uint8_t v_isShared_2053_; uint8_t v_isSharedCheck_2057_; 
lean_del_object(v___x_2018_);
lean_del_object(v___x_2008_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2050_ = lean_ctor_get(v___x_2032_, 0);
v_isSharedCheck_2057_ = !lean_is_exclusive(v___x_2032_);
if (v_isSharedCheck_2057_ == 0)
{
v___x_2052_ = v___x_2032_;
v_isShared_2053_ = v_isSharedCheck_2057_;
goto v_resetjp_2051_;
}
else
{
lean_inc(v_a_2050_);
lean_dec(v___x_2032_);
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
else
{
lean_object* v_a_2058_; lean_object* v___x_2060_; uint8_t v_isShared_2061_; uint8_t v_isSharedCheck_2065_; 
lean_dec(v_a_2028_);
lean_del_object(v___x_2018_);
lean_del_object(v___x_2008_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2058_ = lean_ctor_get(v___x_2030_, 0);
v_isSharedCheck_2065_ = !lean_is_exclusive(v___x_2030_);
if (v_isSharedCheck_2065_ == 0)
{
v___x_2060_ = v___x_2030_;
v_isShared_2061_ = v_isSharedCheck_2065_;
goto v_resetjp_2059_;
}
else
{
lean_inc(v_a_2058_);
lean_dec(v___x_2030_);
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
lean_del_object(v___x_2018_);
lean_del_object(v___x_2008_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2066_ = lean_ctor_get(v___x_2027_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2027_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2027_);
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
else
{
lean_object* v_a_2074_; lean_object* v___x_2076_; uint8_t v_isShared_2077_; uint8_t v_isSharedCheck_2081_; 
lean_del_object(v___x_2018_);
lean_del_object(v___x_2008_);
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2074_ = lean_ctor_get(v___x_2024_, 0);
v_isSharedCheck_2081_ = !lean_is_exclusive(v___x_2024_);
if (v_isSharedCheck_2081_ == 0)
{
v___x_2076_ = v___x_2024_;
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
else
{
lean_inc(v_a_2074_);
lean_dec(v___x_2024_);
v___x_2076_ = lean_box(0);
v_isShared_2077_ = v_isSharedCheck_2081_;
goto v_resetjp_2075_;
}
v_resetjp_2075_:
{
lean_object* v___x_2079_; 
if (v_isShared_2077_ == 0)
{
v___x_2079_ = v___x_2076_;
goto v_reusejp_2078_;
}
else
{
lean_object* v_reuseFailAlloc_2080_; 
v_reuseFailAlloc_2080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2080_, 0, v_a_2074_);
v___x_2079_ = v_reuseFailAlloc_2080_;
goto v_reusejp_2078_;
}
v_reusejp_2078_:
{
return v___x_2079_;
}
}
}
}
else
{
lean_del_object(v___x_2018_);
lean_del_object(v___x_2008_);
lean_dec(v_fst_2005_);
lean_dec(v_fst_2003_);
v___y_1950_ = v_isEq_1993_;
v_isHEq_1951_ = v___x_1815_;
v___y_1952_ = v___y_1994_;
v___y_1953_ = v___y_1995_;
v___y_1954_ = v___y_1996_;
v___y_1955_ = v___y_1997_;
goto v___jp_1949_;
}
}
}
else
{
lean_dec(v_a_2014_);
lean_dec(v_val_2012_);
lean_del_object(v___x_2008_);
lean_dec(v_fst_2005_);
lean_dec(v_fst_2003_);
v___y_1950_ = v_isEq_1993_;
v_isHEq_1951_ = v___x_1815_;
v___y_1952_ = v___y_1994_;
v___y_1953_ = v___y_1995_;
v___y_1954_ = v___y_1996_;
v___y_1955_ = v___y_1997_;
goto v___jp_1949_;
}
}
else
{
lean_object* v_a_2083_; lean_object* v___x_2085_; uint8_t v_isShared_2086_; uint8_t v_isSharedCheck_2090_; 
lean_dec(v_val_2012_);
lean_del_object(v___x_2008_);
lean_dec(v_fst_2005_);
lean_dec(v_fst_2003_);
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2083_ = lean_ctor_get(v___x_2013_, 0);
v_isSharedCheck_2090_ = !lean_is_exclusive(v___x_2013_);
if (v_isSharedCheck_2090_ == 0)
{
v___x_2085_ = v___x_2013_;
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
else
{
lean_inc(v_a_2083_);
lean_dec(v___x_2013_);
v___x_2085_ = lean_box(0);
v_isShared_2086_ = v_isSharedCheck_2090_;
goto v_resetjp_2084_;
}
v_resetjp_2084_:
{
lean_object* v___x_2088_; 
if (v_isShared_2086_ == 0)
{
v___x_2088_ = v___x_2085_;
goto v_reusejp_2087_;
}
else
{
lean_object* v_reuseFailAlloc_2089_; 
v_reuseFailAlloc_2089_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2089_, 0, v_a_2083_);
v___x_2088_ = v_reuseFailAlloc_2089_;
goto v_reusejp_2087_;
}
v_reusejp_2087_:
{
return v___x_2088_;
}
}
}
}
else
{
lean_dec(v_a_2011_);
lean_del_object(v___x_2008_);
lean_dec(v_snd_2006_);
lean_dec(v_fst_2005_);
lean_dec(v_fst_2003_);
v___y_1950_ = v_isEq_1993_;
v_isHEq_1951_ = v___x_1815_;
v___y_1952_ = v___y_1994_;
v___y_1953_ = v___y_1995_;
v___y_1954_ = v___y_1996_;
v___y_1955_ = v___y_1997_;
goto v___jp_1949_;
}
}
else
{
lean_object* v_a_2091_; lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2098_; 
lean_del_object(v___x_2008_);
lean_dec(v_snd_2006_);
lean_dec(v_fst_2005_);
lean_dec(v_fst_2003_);
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2091_ = lean_ctor_get(v___x_2010_, 0);
v_isSharedCheck_2098_ = !lean_is_exclusive(v___x_2010_);
if (v_isSharedCheck_2098_ == 0)
{
v___x_2093_ = v___x_2010_;
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
else
{
lean_inc(v_a_2091_);
lean_dec(v___x_2010_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2098_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2096_; 
if (v_isShared_2094_ == 0)
{
v___x_2096_ = v___x_2093_;
goto v_reusejp_2095_;
}
else
{
lean_object* v_reuseFailAlloc_2097_; 
v_reuseFailAlloc_2097_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2097_, 0, v_a_2091_);
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
}
else
{
lean_dec(v_a_1999_);
v___y_1950_ = v_isEq_1993_;
v_isHEq_1951_ = v___x_1868_;
v___y_1952_ = v___y_1994_;
v___y_1953_ = v___y_1995_;
v___y_1954_ = v___y_1996_;
v___y_1955_ = v___y_1997_;
goto v___jp_1949_;
}
}
else
{
lean_object* v_a_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2107_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2100_ = lean_ctor_get(v___x_1998_, 0);
v_isSharedCheck_2107_ = !lean_is_exclusive(v___x_1998_);
if (v_isSharedCheck_2107_ == 0)
{
v___x_2102_ = v___x_1998_;
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_a_2100_);
lean_dec(v___x_1998_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2107_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v___x_2105_; 
if (v_isShared_2103_ == 0)
{
v___x_2105_ = v___x_2102_;
goto v_reusejp_2104_;
}
else
{
lean_object* v_reuseFailAlloc_2106_; 
v_reuseFailAlloc_2106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_a_2100_);
v___x_2105_ = v_reuseFailAlloc_2106_;
goto v_reusejp_2104_;
}
v_reusejp_2104_:
{
return v___x_2105_;
}
}
}
}
v___jp_2108_:
{
lean_object* v___x_2113_; 
lean_inc_ref(v___x_1869_);
v___x_2113_ = l_Lean_Meta_matchEq_x3f(v___x_1869_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
if (lean_obj_tag(v_a_2114_) == 1)
{
lean_object* v_val_2115_; lean_object* v_snd_2116_; lean_object* v_fst_2117_; lean_object* v_snd_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2190_; 
v_val_2115_ = lean_ctor_get(v_a_2114_, 0);
lean_inc(v_val_2115_);
lean_dec_ref_known(v_a_2114_, 1);
v_snd_2116_ = lean_ctor_get(v_val_2115_, 1);
lean_inc(v_snd_2116_);
lean_dec(v_val_2115_);
v_fst_2117_ = lean_ctor_get(v_snd_2116_, 0);
v_snd_2118_ = lean_ctor_get(v_snd_2116_, 1);
v_isSharedCheck_2190_ = !lean_is_exclusive(v_snd_2116_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2120_ = v_snd_2116_;
v_isShared_2121_ = v_isSharedCheck_2190_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_snd_2118_);
lean_inc(v_fst_2117_);
lean_dec(v_snd_2116_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2190_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2122_; 
v___x_2122_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2117_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2122_) == 0)
{
lean_object* v_a_2123_; 
v_a_2123_ = lean_ctor_get(v___x_2122_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v___x_2122_, 1);
if (lean_obj_tag(v_a_2123_) == 1)
{
lean_object* v_val_2124_; lean_object* v___x_2125_; 
v_val_2124_ = lean_ctor_get(v_a_2123_, 0);
lean_inc(v_val_2124_);
lean_dec_ref_known(v_a_2123_, 1);
v___x_2125_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2118_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
if (lean_obj_tag(v_a_2126_) == 1)
{
lean_object* v_toConstantVal_2127_; lean_object* v_val_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2173_; 
v_toConstantVal_2127_ = lean_ctor_get(v_val_2124_, 0);
lean_inc_ref(v_toConstantVal_2127_);
lean_dec(v_val_2124_);
v_val_2128_ = lean_ctor_get(v_a_2126_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v_a_2126_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2130_ = v_a_2126_;
v_isShared_2131_ = v_isSharedCheck_2173_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_val_2128_);
lean_dec(v_a_2126_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2173_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v_toConstantVal_2132_; lean_object* v_name_2133_; lean_object* v_name_2134_; uint8_t v___x_2135_; 
v_toConstantVal_2132_ = lean_ctor_get(v_val_2128_, 0);
lean_inc_ref(v_toConstantVal_2132_);
lean_dec(v_val_2128_);
v_name_2133_ = lean_ctor_get(v_toConstantVal_2127_, 0);
lean_inc(v_name_2133_);
lean_dec_ref(v_toConstantVal_2127_);
v_name_2134_ = lean_ctor_get(v_toConstantVal_2132_, 0);
lean_inc(v_name_2134_);
lean_dec_ref(v_toConstantVal_2132_);
v___x_2135_ = lean_name_eq(v_name_2133_, v_name_2134_);
lean_dec(v_name_2134_);
lean_dec(v_name_2133_);
if (v___x_2135_ == 0)
{
lean_object* v___x_2136_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec_ref(v_config_1804_);
lean_inc(v_mvarId_1805_);
v___x_2136_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v_a_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
v_a_2137_ = lean_ctor_get(v___x_2136_, 0);
lean_inc(v_a_2137_);
lean_dec_ref_known(v___x_2136_, 1);
v___x_2138_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_2139_ = l_Lean_Meta_mkNoConfusion(v_a_2137_, v___x_2138_, v___y_2109_, v___y_2110_, v___y_2111_, v___y_2112_);
if (lean_obj_tag(v___x_2139_) == 0)
{
lean_object* v_a_2140_; lean_object* v___x_2141_; 
v_a_2140_ = lean_ctor_get(v___x_2139_, 0);
lean_inc(v_a_2140_);
lean_dec_ref_known(v___x_2139_, 1);
v___x_2141_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_2140_, v___y_2110_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v___x_2142_; lean_object* v___x_2144_; 
lean_dec_ref_known(v___x_2141_, 1);
v___x_2142_ = lean_box(v___x_1815_);
if (v_isShared_2131_ == 0)
{
lean_ctor_set(v___x_2130_, 0, v___x_2142_);
v___x_2144_ = v___x_2130_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2142_);
v___x_2144_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
lean_object* v___x_2146_; 
if (v_isShared_2121_ == 0)
{
lean_ctor_set(v___x_2120_, 1, v___x_1840_);
lean_ctor_set(v___x_2120_, 0, v___x_2144_);
v___x_2146_ = v___x_2120_;
goto v_reusejp_2145_;
}
else
{
lean_object* v_reuseFailAlloc_2147_; 
v_reuseFailAlloc_2147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2147_, 0, v___x_2144_);
lean_ctor_set(v_reuseFailAlloc_2147_, 1, v___x_1840_);
v___x_2146_ = v_reuseFailAlloc_2147_;
goto v_reusejp_2145_;
}
v_reusejp_2145_:
{
v_a_1822_ = v___x_2146_;
goto v___jp_1821_;
}
}
}
else
{
lean_object* v_a_2149_; lean_object* v___x_2151_; uint8_t v_isShared_2152_; uint8_t v_isSharedCheck_2156_; 
lean_del_object(v___x_2130_);
lean_del_object(v___x_2120_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_2149_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2156_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2156_ == 0)
{
v___x_2151_ = v___x_2141_;
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
else
{
lean_inc(v_a_2149_);
lean_dec(v___x_2141_);
v___x_2151_ = lean_box(0);
v_isShared_2152_ = v_isSharedCheck_2156_;
goto v_resetjp_2150_;
}
v_resetjp_2150_:
{
lean_object* v___x_2154_; 
if (v_isShared_2152_ == 0)
{
v___x_2154_ = v___x_2151_;
goto v_reusejp_2153_;
}
else
{
lean_object* v_reuseFailAlloc_2155_; 
v_reuseFailAlloc_2155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2155_, 0, v_a_2149_);
v___x_2154_ = v_reuseFailAlloc_2155_;
goto v_reusejp_2153_;
}
v_reusejp_2153_:
{
return v___x_2154_;
}
}
}
}
else
{
lean_object* v_a_2157_; lean_object* v___x_2159_; uint8_t v_isShared_2160_; uint8_t v_isSharedCheck_2164_; 
lean_del_object(v___x_2130_);
lean_del_object(v___x_2120_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2157_ = lean_ctor_get(v___x_2139_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v___x_2139_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2159_ = v___x_2139_;
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
else
{
lean_inc(v_a_2157_);
lean_dec(v___x_2139_);
v___x_2159_ = lean_box(0);
v_isShared_2160_ = v_isSharedCheck_2164_;
goto v_resetjp_2158_;
}
v_resetjp_2158_:
{
lean_object* v___x_2162_; 
if (v_isShared_2160_ == 0)
{
v___x_2162_ = v___x_2159_;
goto v_reusejp_2161_;
}
else
{
lean_object* v_reuseFailAlloc_2163_; 
v_reuseFailAlloc_2163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2163_, 0, v_a_2157_);
v___x_2162_ = v_reuseFailAlloc_2163_;
goto v_reusejp_2161_;
}
v_reusejp_2161_:
{
return v___x_2162_;
}
}
}
}
else
{
lean_object* v_a_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2172_; 
lean_del_object(v___x_2130_);
lean_del_object(v___x_2120_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2165_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2172_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2172_ == 0)
{
v___x_2167_ = v___x_2136_;
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_a_2165_);
lean_dec(v___x_2136_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2172_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v___x_2170_; 
if (v_isShared_2168_ == 0)
{
v___x_2170_ = v___x_2167_;
goto v_reusejp_2169_;
}
else
{
lean_object* v_reuseFailAlloc_2171_; 
v_reuseFailAlloc_2171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2171_, 0, v_a_2165_);
v___x_2170_ = v_reuseFailAlloc_2171_;
goto v_reusejp_2169_;
}
v_reusejp_2169_:
{
return v___x_2170_;
}
}
}
}
else
{
lean_del_object(v___x_2130_);
lean_del_object(v___x_2120_);
v_isEq_1993_ = v___x_1815_;
v___y_1994_ = v___y_2109_;
v___y_1995_ = v___y_2110_;
v___y_1996_ = v___y_2111_;
v___y_1997_ = v___y_2112_;
goto v___jp_1992_;
}
}
}
else
{
lean_dec(v_a_2126_);
lean_dec(v_val_2124_);
lean_del_object(v___x_2120_);
v_isEq_1993_ = v___x_1815_;
v___y_1994_ = v___y_2109_;
v___y_1995_ = v___y_2110_;
v___y_1996_ = v___y_2111_;
v___y_1997_ = v___y_2112_;
goto v___jp_1992_;
}
}
else
{
lean_object* v_a_2174_; lean_object* v___x_2176_; uint8_t v_isShared_2177_; uint8_t v_isSharedCheck_2181_; 
lean_dec(v_val_2124_);
lean_del_object(v___x_2120_);
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2174_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2181_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2181_ == 0)
{
v___x_2176_ = v___x_2125_;
v_isShared_2177_ = v_isSharedCheck_2181_;
goto v_resetjp_2175_;
}
else
{
lean_inc(v_a_2174_);
lean_dec(v___x_2125_);
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
else
{
lean_dec(v_a_2123_);
lean_del_object(v___x_2120_);
lean_dec(v_snd_2118_);
v_isEq_1993_ = v___x_1815_;
v___y_1994_ = v___y_2109_;
v___y_1995_ = v___y_2110_;
v___y_1996_ = v___y_2111_;
v___y_1997_ = v___y_2112_;
goto v___jp_1992_;
}
}
else
{
lean_object* v_a_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2189_; 
lean_del_object(v___x_2120_);
lean_dec(v_snd_2118_);
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2182_ = lean_ctor_get(v___x_2122_, 0);
v_isSharedCheck_2189_ = !lean_is_exclusive(v___x_2122_);
if (v_isSharedCheck_2189_ == 0)
{
v___x_2184_ = v___x_2122_;
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_a_2182_);
lean_dec(v___x_2122_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2189_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2185_ == 0)
{
v___x_2187_ = v___x_2184_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v_a_2182_);
v___x_2187_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
return v___x_2187_;
}
}
}
}
}
else
{
lean_dec(v_a_2114_);
v_isEq_1993_ = v___x_1868_;
v___y_1994_ = v___y_2109_;
v___y_1995_ = v___y_2110_;
v___y_1996_ = v___y_2111_;
v___y_1997_ = v___y_2112_;
goto v___jp_1992_;
}
}
else
{
lean_object* v_a_2191_; lean_object* v___x_2193_; uint8_t v_isShared_2194_; uint8_t v_isSharedCheck_2198_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2191_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2198_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2198_ == 0)
{
v___x_2193_ = v___x_2113_;
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
else
{
lean_inc(v_a_2191_);
lean_dec(v___x_2113_);
v___x_2193_ = lean_box(0);
v_isShared_2194_ = v_isSharedCheck_2198_;
goto v_resetjp_2192_;
}
v_resetjp_2192_:
{
lean_object* v___x_2196_; 
if (v_isShared_2194_ == 0)
{
v___x_2196_ = v___x_2193_;
goto v_reusejp_2195_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
v___x_2196_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2195_;
}
v_reusejp_2195_:
{
return v___x_2196_;
}
}
}
}
v___jp_2199_:
{
lean_object* v___x_2204_; 
lean_inc_ref(v___x_1869_);
v___x_2204_ = l_Lean_refutableHasNotBit_x3f(v___x_1869_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2204_) == 0)
{
lean_object* v_a_2205_; 
v_a_2205_ = lean_ctor_get(v___x_2204_, 0);
lean_inc(v_a_2205_);
lean_dec_ref_known(v___x_2204_, 1);
if (lean_obj_tag(v_a_2205_) == 1)
{
lean_object* v_val_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2245_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec_ref(v_config_1804_);
v_val_2206_ = lean_ctor_get(v_a_2205_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v_a_2205_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2208_ = v_a_2205_;
v_isShared_2209_ = v_isSharedCheck_2245_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_val_2206_);
lean_dec(v_a_2205_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2245_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2210_; 
lean_inc(v_mvarId_1805_);
v___x_2210_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2210_) == 0)
{
lean_object* v_a_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v_a_2211_ = lean_ctor_get(v___x_2210_, 0);
lean_inc(v_a_2211_);
lean_dec_ref_known(v___x_2210_, 1);
v___x_2212_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_2213_ = l_Lean_Meta_mkAbsurd(v_a_2211_, v_val_2206_, v___x_2212_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; lean_object* v___x_2215_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
v___x_2215_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_2214_, v___y_2201_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v___x_2216_; lean_object* v___x_2218_; 
lean_dec_ref_known(v___x_2215_, 1);
v___x_2216_ = lean_box(v___x_1815_);
if (v_isShared_2209_ == 0)
{
lean_ctor_set(v___x_2208_, 0, v___x_2216_);
v___x_2218_ = v___x_2208_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v___x_2216_);
v___x_2218_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
lean_object* v___x_2219_; 
v___x_2219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2219_, 0, v___x_2218_);
lean_ctor_set(v___x_2219_, 1, v___x_1840_);
v_a_1822_ = v___x_2219_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_del_object(v___x_2208_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_2221_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2215_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2215_);
v___x_2223_ = lean_box(0);
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
v_resetjp_2222_:
{
lean_object* v___x_2226_; 
if (v_isShared_2224_ == 0)
{
v___x_2226_ = v___x_2223_;
goto v_reusejp_2225_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_a_2221_);
v___x_2226_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2225_;
}
v_reusejp_2225_:
{
return v___x_2226_;
}
}
}
}
else
{
lean_object* v_a_2229_; lean_object* v___x_2231_; uint8_t v_isShared_2232_; uint8_t v_isSharedCheck_2236_; 
lean_del_object(v___x_2208_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2229_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2236_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2236_ == 0)
{
v___x_2231_ = v___x_2213_;
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
else
{
lean_inc(v_a_2229_);
lean_dec(v___x_2213_);
v___x_2231_ = lean_box(0);
v_isShared_2232_ = v_isSharedCheck_2236_;
goto v_resetjp_2230_;
}
v_resetjp_2230_:
{
lean_object* v___x_2234_; 
if (v_isShared_2232_ == 0)
{
v___x_2234_ = v___x_2231_;
goto v_reusejp_2233_;
}
else
{
lean_object* v_reuseFailAlloc_2235_; 
v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2229_);
v___x_2234_ = v_reuseFailAlloc_2235_;
goto v_reusejp_2233_;
}
v_reusejp_2233_:
{
return v___x_2234_;
}
}
}
}
else
{
lean_object* v_a_2237_; lean_object* v___x_2239_; uint8_t v_isShared_2240_; uint8_t v_isSharedCheck_2244_; 
lean_del_object(v___x_2208_);
lean_dec(v_val_2206_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2237_ = lean_ctor_get(v___x_2210_, 0);
v_isSharedCheck_2244_ = !lean_is_exclusive(v___x_2210_);
if (v_isSharedCheck_2244_ == 0)
{
v___x_2239_ = v___x_2210_;
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
else
{
lean_inc(v_a_2237_);
lean_dec(v___x_2210_);
v___x_2239_ = lean_box(0);
v_isShared_2240_ = v_isSharedCheck_2244_;
goto v_resetjp_2238_;
}
v_resetjp_2238_:
{
lean_object* v___x_2242_; 
if (v_isShared_2240_ == 0)
{
v___x_2242_ = v___x_2239_;
goto v_reusejp_2241_;
}
else
{
lean_object* v_reuseFailAlloc_2243_; 
v_reuseFailAlloc_2243_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2243_, 0, v_a_2237_);
v___x_2242_ = v_reuseFailAlloc_2243_;
goto v_reusejp_2241_;
}
v_reusejp_2241_:
{
return v___x_2242_;
}
}
}
}
}
else
{
lean_object* v___x_2246_; 
lean_dec(v_a_2205_);
lean_inc_ref(v___x_1869_);
v___x_2246_ = l_Lean_Meta_matchNe_x3f(v___x_1869_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
if (lean_obj_tag(v_a_2247_) == 1)
{
lean_object* v_val_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2317_; 
v_val_2248_ = lean_ctor_get(v_a_2247_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_a_2247_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2250_ = v_a_2247_;
v_isShared_2251_ = v_isSharedCheck_2317_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_val_2248_);
lean_dec(v_a_2247_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2317_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_snd_2252_; lean_object* v_fst_2253_; lean_object* v_snd_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2316_; 
v_snd_2252_ = lean_ctor_get(v_val_2248_, 1);
lean_inc(v_snd_2252_);
lean_dec(v_val_2248_);
v_fst_2253_ = lean_ctor_get(v_snd_2252_, 0);
v_snd_2254_ = lean_ctor_get(v_snd_2252_, 1);
v_isSharedCheck_2316_ = !lean_is_exclusive(v_snd_2252_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2256_ = v_snd_2252_;
v_isShared_2257_ = v_isSharedCheck_2316_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_snd_2254_);
lean_inc(v_fst_2253_);
lean_dec(v_snd_2252_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2316_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v___x_2258_; 
lean_inc(v_fst_2253_);
v___x_2258_ = l_Lean_Meta_isExprDefEq(v_fst_2253_, v_snd_2254_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; uint8_t v___x_2260_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
lean_inc(v_a_2259_);
lean_dec_ref_known(v___x_2258_, 1);
v___x_2260_ = lean_unbox(v_a_2259_);
lean_dec(v_a_2259_);
if (v___x_2260_ == 0)
{
lean_del_object(v___x_2256_);
lean_dec(v_fst_2253_);
lean_del_object(v___x_2250_);
v___y_2109_ = v___y_2200_;
v___y_2110_ = v___y_2201_;
v___y_2111_ = v___y_2202_;
v___y_2112_ = v___y_2203_;
goto v___jp_2108_;
}
else
{
lean_object* v___x_2261_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec_ref(v_config_1804_);
lean_inc(v_mvarId_1805_);
v___x_2261_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; lean_object* v___x_2263_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
v___x_2263_ = l_Lean_Meta_mkEqRefl(v_fst_2253_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
lean_inc(v_a_2264_);
lean_dec_ref_known(v___x_2263_, 1);
v___x_2265_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_2266_ = l_Lean_Meta_mkAbsurd(v_a_2262_, v_a_2264_, v___x_2265_, v___y_2200_, v___y_2201_, v___y_2202_, v___y_2203_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2268_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_2267_, v___y_2201_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
lean_dec_ref_known(v___x_2268_, 1);
v___x_2269_ = lean_box(v___x_1815_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2269_);
v___x_2271_ = v___x_2250_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2269_);
v___x_2271_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2273_; 
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 1, v___x_1840_);
lean_ctor_set(v___x_2256_, 0, v___x_2271_);
v___x_2273_ = v___x_2256_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v___x_1840_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
v_a_1822_ = v___x_2273_;
goto v___jp_1821_;
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_del_object(v___x_2256_);
lean_del_object(v___x_2250_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_2276_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2268_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2268_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_del_object(v___x_2256_);
lean_del_object(v___x_2250_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2284_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2266_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2266_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
else
{
lean_object* v_a_2292_; lean_object* v___x_2294_; uint8_t v_isShared_2295_; uint8_t v_isSharedCheck_2299_; 
lean_dec(v_a_2262_);
lean_del_object(v___x_2256_);
lean_del_object(v___x_2250_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2292_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2263_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2263_);
v___x_2294_ = lean_box(0);
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
v_resetjp_2293_:
{
lean_object* v___x_2297_; 
if (v_isShared_2295_ == 0)
{
v___x_2297_ = v___x_2294_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2298_; 
v_reuseFailAlloc_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2298_, 0, v_a_2292_);
v___x_2297_ = v_reuseFailAlloc_2298_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
return v___x_2297_;
}
}
}
}
else
{
lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_del_object(v___x_2256_);
lean_dec(v_fst_2253_);
lean_del_object(v___x_2250_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2300_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2261_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_dec(v___x_2261_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
}
else
{
lean_object* v_a_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2315_; 
lean_del_object(v___x_2256_);
lean_dec(v_fst_2253_);
lean_del_object(v___x_2250_);
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2308_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2315_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2315_ == 0)
{
v___x_2310_ = v___x_2258_;
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_a_2308_);
lean_dec(v___x_2258_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2315_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
lean_object* v___x_2313_; 
if (v_isShared_2311_ == 0)
{
v___x_2313_ = v___x_2310_;
goto v_reusejp_2312_;
}
else
{
lean_object* v_reuseFailAlloc_2314_; 
v_reuseFailAlloc_2314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2314_, 0, v_a_2308_);
v___x_2313_ = v_reuseFailAlloc_2314_;
goto v_reusejp_2312_;
}
v_reusejp_2312_:
{
return v___x_2313_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2247_);
v___y_2109_ = v___y_2200_;
v___y_2110_ = v___y_2201_;
v___y_2111_ = v___y_2202_;
v___y_2112_ = v___y_2203_;
goto v___jp_2108_;
}
}
else
{
lean_object* v_a_2318_; lean_object* v___x_2320_; uint8_t v_isShared_2321_; uint8_t v_isSharedCheck_2325_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2318_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2325_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2325_ == 0)
{
v___x_2320_ = v___x_2246_;
v_isShared_2321_ = v_isSharedCheck_2325_;
goto v_resetjp_2319_;
}
else
{
lean_inc(v_a_2318_);
lean_dec(v___x_2246_);
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
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v___x_1869_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2326_ = lean_ctor_get(v___x_2204_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2204_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2204_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2204_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
}
else
{
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_1830_ = v___x_1841_;
goto v___jp_1829_;
}
v___jp_1842_:
{
uint8_t v_emptyType_1849_; 
v_emptyType_1849_ = lean_ctor_get_uint8(v_config_1804_, sizeof(void*)*1 + 1);
if (v_emptyType_1849_ == 0)
{
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_1830_ = v___x_1841_;
goto v___jp_1829_;
}
else
{
if (v___y_1844_ == 0)
{
if (v___y_1843_ == 0)
{
lean_object* v_searchFuel_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v_searchFuel_1850_ = lean_ctor_get(v_config_1804_, 0);
v___x_1851_ = l_Lean_LocalDecl_fvarId(v_val_1836_);
lean_dec(v_val_1836_);
lean_inc(v_searchFuel_1850_);
lean_inc(v_mvarId_1805_);
v___x_1852_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1805_, v___x_1851_, v_searchFuel_1850_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v_a_1853_; uint8_t v___x_1854_; 
v_a_1853_ = lean_ctor_get(v___x_1852_, 0);
lean_inc(v_a_1853_);
lean_dec_ref_known(v___x_1852_, 1);
v___x_1854_ = lean_unbox(v_a_1853_);
lean_dec(v_a_1853_);
if (v___x_1854_ == 0)
{
lean_del_object(v___x_1838_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_1830_ = v___x_1841_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1857_; 
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v___x_1855_ = lean_box(v___x_1815_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1855_);
v___x_1857_ = v___x_1838_;
goto v_reusejp_1856_;
}
else
{
lean_object* v_reuseFailAlloc_1859_; 
v_reuseFailAlloc_1859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1859_, 0, v___x_1855_);
v___x_1857_ = v_reuseFailAlloc_1859_;
goto v_reusejp_1856_;
}
v_reusejp_1856_:
{
lean_object* v___x_1858_; 
v___x_1858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1858_, 0, v___x_1857_);
lean_ctor_set(v___x_1858_, 1, v___x_1840_);
v_a_1822_ = v___x_1858_;
goto v___jp_1821_;
}
}
}
else
{
lean_object* v_a_1860_; lean_object* v___x_1862_; uint8_t v_isShared_1863_; uint8_t v_isSharedCheck_1867_; 
lean_del_object(v___x_1838_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_1860_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1867_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1867_ == 0)
{
v___x_1862_ = v___x_1852_;
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
else
{
lean_inc(v_a_1860_);
lean_dec(v___x_1852_);
v___x_1862_ = lean_box(0);
v_isShared_1863_ = v_isSharedCheck_1867_;
goto v_resetjp_1861_;
}
v_resetjp_1861_:
{
lean_object* v___x_1865_; 
if (v_isShared_1863_ == 0)
{
v___x_1865_ = v___x_1862_;
goto v_reusejp_1864_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1860_);
v___x_1865_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1864_;
}
v_reusejp_1864_:
{
return v___x_1865_;
}
}
}
}
else
{
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_1830_ = v___x_1841_;
goto v___jp_1829_;
}
}
else
{
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_1830_ = v___x_1841_;
goto v___jp_1829_;
}
}
}
}
}
v___jp_1821_:
{
lean_object* v___x_1823_; lean_object* v___x_1825_; 
v___x_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_a_1822_);
if (v_isShared_1820_ == 0)
{
lean_ctor_set(v___x_1819_, 0, v___x_1823_);
v___x_1825_ = v___x_1819_;
goto v_reusejp_1824_;
}
else
{
lean_object* v_reuseFailAlloc_1827_; 
v_reuseFailAlloc_1827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1827_, 0, v___x_1823_);
lean_ctor_set(v_reuseFailAlloc_1827_, 1, v_snd_1817_);
v___x_1825_ = v_reuseFailAlloc_1827_;
goto v_reusejp_1824_;
}
v_reusejp_1824_:
{
lean_object* v___x_1826_; 
v___x_1826_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1826_, 0, v___x_1825_);
return v___x_1826_;
}
}
v___jp_1829_:
{
lean_object* v___x_1831_; size_t v___x_1832_; size_t v___x_1833_; 
v___x_1831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1831_, 0, v___x_1828_);
lean_ctor_set(v___x_1831_, 1, v_a_1830_);
v___x_1832_ = ((size_t)1ULL);
v___x_1833_ = lean_usize_add(v_i_1808_, v___x_1832_);
v_i_1808_ = v___x_1833_;
v_b_1809_ = v___x_1831_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2400_, lean_object* v_mvarId_2401_, lean_object* v_as_2402_, lean_object* v_sz_2403_, lean_object* v_i_2404_, lean_object* v_b_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
size_t v_sz_boxed_2411_; size_t v_i_boxed_2412_; lean_object* v_res_2413_; 
v_sz_boxed_2411_ = lean_unbox_usize(v_sz_2403_);
lean_dec(v_sz_2403_);
v_i_boxed_2412_ = lean_unbox_usize(v_i_2404_);
lean_dec(v_i_2404_);
v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2400_, v_mvarId_2401_, v_as_2402_, v_sz_boxed_2411_, v_i_boxed_2412_, v_b_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec_ref(v_as_2402_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2414_, lean_object* v_mvarId_2415_, lean_object* v_as_2416_, size_t v_sz_2417_, size_t v_i_2418_, lean_object* v_b_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_){
_start:
{
uint8_t v___x_2425_; 
v___x_2425_ = lean_usize_dec_lt(v_i_2418_, v_sz_2417_);
if (v___x_2425_ == 0)
{
lean_object* v___x_2426_; 
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v___x_2426_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2426_, 0, v_b_2419_);
return v___x_2426_;
}
else
{
lean_object* v_snd_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_3008_; 
v_snd_2427_ = lean_ctor_get(v_b_2419_, 1);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_b_2419_);
if (v_isSharedCheck_3008_ == 0)
{
lean_object* v_unused_3009_; 
v_unused_3009_ = lean_ctor_get(v_b_2419_, 0);
lean_dec(v_unused_3009_);
v___x_2429_ = v_b_2419_;
v_isShared_2430_ = v_isSharedCheck_3008_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_snd_2427_);
lean_dec(v_b_2419_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_3008_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v_a_2432_; lean_object* v___x_2438_; lean_object* v_a_2440_; lean_object* v_a_2445_; 
v___x_2438_ = lean_box(0);
v_a_2445_ = lean_array_uget(v_as_2416_, v_i_2418_);
if (lean_obj_tag(v_a_2445_) == 0)
{
lean_del_object(v___x_2429_);
v_a_2440_ = v_snd_2427_;
goto v___jp_2439_;
}
else
{
lean_object* v_val_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_3007_; 
v_val_2446_ = lean_ctor_get(v_a_2445_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v_a_2445_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_2448_ = v_a_2445_;
v_isShared_2449_ = v_isSharedCheck_3007_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_val_2446_);
lean_dec(v_a_2445_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_3007_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; uint8_t v___y_2453_; uint8_t v___y_2454_; lean_object* v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; uint8_t v___x_2478_; 
v___x_2450_ = lean_box(0);
v___x_2451_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2478_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2446_);
if (v___x_2478_ == 0)
{
lean_object* v___x_2479_; uint8_t v___y_2481_; uint8_t v___y_2482_; lean_object* v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2504_; uint8_t v___y_2505_; lean_object* v___y_2506_; lean_object* v___y_2507_; uint8_t v___y_2508_; lean_object* v___y_2509_; lean_object* v_a_2510_; lean_object* v___y_2516_; uint8_t v___y_2517_; lean_object* v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; uint8_t v___y_2521_; lean_object* v___y_2522_; lean_object* v___y_2523_; uint8_t v___y_2560_; uint8_t v_isHEq_2561_; lean_object* v___y_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; uint8_t v_isEq_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2810_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___x_2944_; 
v___x_2479_ = l_Lean_LocalDecl_type(v_val_2446_);
lean_inc_ref(v___x_2479_);
v___x_2944_ = l_Lean_Meta_matchNot_x3f(v___x_2479_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2944_) == 0)
{
lean_object* v_a_2945_; 
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref_known(v___x_2944_, 1);
if (lean_obj_tag(v_a_2945_) == 1)
{
lean_object* v_val_2946_; lean_object* v___x_2947_; 
v_val_2946_ = lean_ctor_get(v_a_2945_, 0);
lean_inc(v_val_2946_);
lean_dec_ref_known(v_a_2945_, 1);
v___x_2947_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2946_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2947_) == 0)
{
lean_object* v_a_2948_; 
v_a_2948_ = lean_ctor_get(v___x_2947_, 0);
lean_inc(v_a_2948_);
lean_dec_ref_known(v___x_2947_, 1);
if (lean_obj_tag(v_a_2948_) == 1)
{
lean_object* v_val_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2990_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec_ref(v_config_2414_);
v_val_2949_ = lean_ctor_get(v_a_2948_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v_a_2948_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2951_ = v_a_2948_;
v_isShared_2952_ = v_isSharedCheck_2990_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_val_2949_);
lean_dec(v_a_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2990_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2953_; 
lean_inc(v_mvarId_2415_);
v___x_2953_ = l_Lean_MVarId_getType(v_mvarId_2415_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2953_) == 0)
{
lean_object* v_a_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; 
v_a_2954_ = lean_ctor_get(v___x_2953_, 0);
lean_inc(v_a_2954_);
lean_dec_ref_known(v___x_2953_, 1);
v___x_2955_ = l_Lean_LocalDecl_toExpr(v_val_2446_);
v___x_2956_ = l_Lean_mkFVar(v_val_2949_);
v___x_2957_ = l_Lean_Expr_app___override(v___x_2955_, v___x_2956_);
v___x_2958_ = l_Lean_Meta_mkFalseElim(v_a_2954_, v___x_2957_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
if (lean_obj_tag(v___x_2958_) == 0)
{
lean_object* v_a_2959_; lean_object* v___x_2960_; 
v_a_2959_ = lean_ctor_get(v___x_2958_, 0);
lean_inc(v_a_2959_);
lean_dec_ref_known(v___x_2958_, 1);
v___x_2960_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2415_, v_a_2959_, v___y_2421_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v___x_2961_; lean_object* v___x_2963_; 
lean_dec_ref_known(v___x_2960_, 1);
v___x_2961_ = lean_box(v___x_2425_);
if (v_isShared_2952_ == 0)
{
lean_ctor_set(v___x_2951_, 0, v___x_2961_);
v___x_2963_ = v___x_2951_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2961_);
v___x_2963_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; 
v___x_2964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2964_, 0, v___x_2963_);
lean_ctor_set(v___x_2964_, 1, v___x_2450_);
v_a_2432_ = v___x_2964_;
goto v___jp_2431_;
}
}
else
{
lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_del_object(v___x_2951_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
v_a_2966_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2960_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_dec(v___x_2960_);
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
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_2981_; 
lean_del_object(v___x_2951_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2974_ = lean_ctor_get(v___x_2958_, 0);
v_isSharedCheck_2981_ = !lean_is_exclusive(v___x_2958_);
if (v_isSharedCheck_2981_ == 0)
{
v___x_2976_ = v___x_2958_;
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2958_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_2981_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v___x_2979_; 
if (v_isShared_2977_ == 0)
{
v___x_2979_ = v___x_2976_;
goto v_reusejp_2978_;
}
else
{
lean_object* v_reuseFailAlloc_2980_; 
v_reuseFailAlloc_2980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2980_, 0, v_a_2974_);
v___x_2979_ = v_reuseFailAlloc_2980_;
goto v_reusejp_2978_;
}
v_reusejp_2978_:
{
return v___x_2979_;
}
}
}
}
else
{
lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_2989_; 
lean_del_object(v___x_2951_);
lean_dec(v_val_2949_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2982_ = lean_ctor_get(v___x_2953_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v___x_2953_);
if (v_isSharedCheck_2989_ == 0)
{
v___x_2984_ = v___x_2953_;
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_dec(v___x_2953_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_2989_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
lean_object* v___x_2987_; 
if (v_isShared_2985_ == 0)
{
v___x_2987_ = v___x_2984_;
goto v_reusejp_2986_;
}
else
{
lean_object* v_reuseFailAlloc_2988_; 
v_reuseFailAlloc_2988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2988_, 0, v_a_2982_);
v___x_2987_ = v_reuseFailAlloc_2988_;
goto v_reusejp_2986_;
}
v_reusejp_2986_:
{
return v___x_2987_;
}
}
}
}
}
else
{
lean_dec(v_a_2948_);
v___y_2810_ = v___y_2420_;
v___y_2811_ = v___y_2421_;
v___y_2812_ = v___y_2422_;
v___y_2813_ = v___y_2423_;
goto v___jp_2809_;
}
}
else
{
lean_object* v_a_2991_; lean_object* v___x_2993_; uint8_t v_isShared_2994_; uint8_t v_isSharedCheck_2998_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2991_ = lean_ctor_get(v___x_2947_, 0);
v_isSharedCheck_2998_ = !lean_is_exclusive(v___x_2947_);
if (v_isSharedCheck_2998_ == 0)
{
v___x_2993_ = v___x_2947_;
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
else
{
lean_inc(v_a_2991_);
lean_dec(v___x_2947_);
v___x_2993_ = lean_box(0);
v_isShared_2994_ = v_isSharedCheck_2998_;
goto v_resetjp_2992_;
}
v_resetjp_2992_:
{
lean_object* v___x_2996_; 
if (v_isShared_2994_ == 0)
{
v___x_2996_ = v___x_2993_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v_a_2991_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
return v___x_2996_;
}
}
}
}
else
{
lean_dec(v_a_2945_);
v___y_2810_ = v___y_2420_;
v___y_2811_ = v___y_2421_;
v___y_2812_ = v___y_2422_;
v___y_2813_ = v___y_2423_;
goto v___jp_2809_;
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2999_ = lean_ctor_get(v___x_2944_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2944_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2944_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2944_);
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
v___jp_2480_:
{
uint8_t v_genDiseq_2487_; 
v_genDiseq_2487_ = lean_ctor_get_uint8(v_config_2414_, sizeof(void*)*1 + 2);
if (v_genDiseq_2487_ == 0)
{
lean_dec_ref(v___x_2479_);
v___y_2453_ = v___y_2481_;
v___y_2454_ = v___y_2482_;
v___y_2455_ = v___y_2483_;
v___y_2456_ = v___y_2484_;
v___y_2457_ = v___y_2485_;
v___y_2458_ = v___y_2486_;
goto v___jp_2452_;
}
else
{
uint8_t v___x_2488_; 
v___x_2488_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2479_);
if (v___x_2488_ == 0)
{
v___y_2453_ = v___y_2481_;
v___y_2454_ = v___y_2482_;
v___y_2455_ = v___y_2483_;
v___y_2456_ = v___y_2484_;
v___y_2457_ = v___y_2485_;
v___y_2458_ = v___y_2486_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2489_; 
lean_inc(v_val_2446_);
lean_inc(v_mvarId_2415_);
v___x_2489_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2415_, v_val_2446_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
if (lean_obj_tag(v___x_2489_) == 0)
{
lean_object* v_a_2490_; uint8_t v___x_2491_; 
v_a_2490_ = lean_ctor_get(v___x_2489_, 0);
lean_inc(v_a_2490_);
lean_dec_ref_known(v___x_2489_, 1);
v___x_2491_ = lean_unbox(v_a_2490_);
lean_dec(v_a_2490_);
if (v___x_2491_ == 0)
{
v___y_2453_ = v___y_2481_;
v___y_2454_ = v___y_2482_;
v___y_2455_ = v___y_2483_;
v___y_2456_ = v___y_2484_;
v___y_2457_ = v___y_2485_;
v___y_2458_ = v___y_2486_;
goto v___jp_2452_;
}
else
{
lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; 
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v___x_2492_ = lean_box(v___x_2425_);
v___x_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
v___x_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
lean_ctor_set(v___x_2494_, 1, v___x_2450_);
v_a_2432_ = v___x_2494_;
goto v___jp_2431_;
}
}
else
{
lean_object* v_a_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2502_; 
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2495_ = lean_ctor_get(v___x_2489_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2489_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2497_ = v___x_2489_;
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
else
{
lean_inc(v_a_2495_);
lean_dec(v___x_2489_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2502_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2500_; 
if (v_isShared_2498_ == 0)
{
v___x_2500_ = v___x_2497_;
goto v_reusejp_2499_;
}
else
{
lean_object* v_reuseFailAlloc_2501_; 
v_reuseFailAlloc_2501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2501_, 0, v_a_2495_);
v___x_2500_ = v_reuseFailAlloc_2501_;
goto v_reusejp_2499_;
}
v_reusejp_2499_:
{
return v___x_2500_;
}
}
}
}
}
}
v___jp_2503_:
{
uint8_t v___x_2511_; 
v___x_2511_ = l_Lean_Exception_isInterrupt(v_a_2510_);
if (v___x_2511_ == 0)
{
uint8_t v___x_2512_; 
lean_inc_ref(v_a_2510_);
v___x_2512_ = l_Lean_Exception_isRuntime(v_a_2510_);
if (v___x_2512_ == 0)
{
lean_dec_ref(v_a_2510_);
v___y_2481_ = v___y_2505_;
v___y_2482_ = v___y_2508_;
v___y_2483_ = v___y_2507_;
v___y_2484_ = v___y_2506_;
v___y_2485_ = v___y_2504_;
v___y_2486_ = v___y_2509_;
goto v___jp_2480_;
}
else
{
lean_object* v___x_2513_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v___x_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2513_, 0, v_a_2510_);
return v___x_2513_;
}
}
else
{
lean_object* v___x_2514_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v___x_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_a_2510_);
return v___x_2514_;
}
}
v___jp_2515_:
{
if (lean_obj_tag(v___y_2523_) == 0)
{
lean_object* v_a_2524_; lean_object* v___x_2525_; uint8_t v___x_2526_; 
v_a_2524_ = lean_ctor_get(v___y_2523_, 0);
lean_inc(v_a_2524_);
lean_dec_ref_known(v___y_2523_, 1);
v___x_2525_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2526_ = l_Lean_Expr_isConstOf(v_a_2524_, v___x_2525_);
lean_dec(v_a_2524_);
if (v___x_2526_ == 0)
{
lean_dec_ref(v___y_2519_);
v___y_2481_ = v___y_2517_;
v___y_2482_ = v___y_2521_;
v___y_2483_ = v___y_2520_;
v___y_2484_ = v___y_2518_;
v___y_2485_ = v___y_2516_;
v___y_2486_ = v___y_2522_;
goto v___jp_2480_;
}
else
{
lean_object* v___x_2527_; 
lean_inc_ref(v___y_2519_);
v___x_2527_ = l_Lean_Meta_mkEqRefl(v___y_2519_, v___y_2520_, v___y_2518_, v___y_2516_, v___y_2522_);
if (lean_obj_tag(v___x_2527_) == 0)
{
lean_object* v_a_2528_; lean_object* v___x_2529_; lean_object* v_dummy_2530_; lean_object* v_nargs_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; 
v_a_2528_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2528_);
lean_dec_ref_known(v___x_2527_, 1);
v___x_2529_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2530_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2531_ = l_Lean_Expr_getAppNumArgs(v___y_2519_);
lean_inc(v_nargs_2531_);
v___x_2532_ = lean_mk_array(v_nargs_2531_, v_dummy_2530_);
v___x_2533_ = lean_unsigned_to_nat(1u);
v___x_2534_ = lean_nat_sub(v_nargs_2531_, v___x_2533_);
lean_dec(v_nargs_2531_);
v___x_2535_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2519_, v___x_2532_, v___x_2534_);
v___x_2536_ = lean_array_push(v___x_2535_, v_a_2528_);
v___x_2537_ = l_Lean_mkAppN(v___x_2529_, v___x_2536_);
lean_dec_ref(v___x_2536_);
lean_inc(v_mvarId_2415_);
v___x_2538_ = l_Lean_MVarId_getType(v_mvarId_2415_, v___y_2520_, v___y_2518_, v___y_2516_, v___y_2522_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v_a_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; 
v_a_2539_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2539_);
lean_dec_ref_known(v___x_2538_, 1);
lean_inc(v_val_2446_);
v___x_2540_ = l_Lean_LocalDecl_toExpr(v_val_2446_);
v___x_2541_ = l_Lean_Meta_mkAbsurd(v_a_2539_, v___x_2540_, v___x_2537_, v___y_2520_, v___y_2518_, v___y_2516_, v___y_2522_);
if (lean_obj_tag(v___x_2541_) == 0)
{
lean_object* v_a_2542_; lean_object* v___x_2543_; 
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2542_);
lean_dec_ref_known(v___x_2541_, 1);
lean_inc(v_mvarId_2415_);
v___x_2543_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2415_, v_a_2542_, v___y_2518_);
if (lean_obj_tag(v___x_2543_) == 0)
{
lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2552_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2543_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; 
v_unused_2553_ = lean_ctor_get(v___x_2543_, 0);
lean_dec(v_unused_2553_);
v___x_2545_ = v___x_2543_;
v_isShared_2546_ = v_isSharedCheck_2552_;
goto v_resetjp_2544_;
}
else
{
lean_dec(v___x_2543_);
v___x_2545_ = lean_box(0);
v_isShared_2546_ = v_isSharedCheck_2552_;
goto v_resetjp_2544_;
}
v_resetjp_2544_:
{
lean_object* v___x_2547_; lean_object* v___x_2549_; 
v___x_2547_ = lean_box(v___x_2425_);
if (v_isShared_2546_ == 0)
{
lean_ctor_set_tag(v___x_2545_, 1);
lean_ctor_set(v___x_2545_, 0, v___x_2547_);
v___x_2549_ = v___x_2545_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v___x_2547_);
v___x_2549_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
lean_object* v___x_2550_; 
v___x_2550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2550_, 0, v___x_2549_);
lean_ctor_set(v___x_2550_, 1, v___x_2450_);
v_a_2432_ = v___x_2550_;
goto v___jp_2431_;
}
}
}
else
{
lean_object* v_a_2554_; 
v_a_2554_ = lean_ctor_get(v___x_2543_, 0);
lean_inc(v_a_2554_);
lean_dec_ref_known(v___x_2543_, 1);
v___y_2504_ = v___y_2516_;
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2518_;
v___y_2507_ = v___y_2520_;
v___y_2508_ = v___y_2521_;
v___y_2509_ = v___y_2522_;
v_a_2510_ = v_a_2554_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_2555_; 
v_a_2555_ = lean_ctor_get(v___x_2541_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2541_, 1);
v___y_2504_ = v___y_2516_;
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2518_;
v___y_2507_ = v___y_2520_;
v___y_2508_ = v___y_2521_;
v___y_2509_ = v___y_2522_;
v_a_2510_ = v_a_2555_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_2556_; 
lean_dec_ref(v___x_2537_);
v_a_2556_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2538_, 1);
v___y_2504_ = v___y_2516_;
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2518_;
v___y_2507_ = v___y_2520_;
v___y_2508_ = v___y_2521_;
v___y_2509_ = v___y_2522_;
v_a_2510_ = v_a_2556_;
goto v___jp_2503_;
}
}
else
{
lean_object* v_a_2557_; 
lean_dec_ref(v___y_2519_);
v_a_2557_ = lean_ctor_get(v___x_2527_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2527_, 1);
v___y_2504_ = v___y_2516_;
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2518_;
v___y_2507_ = v___y_2520_;
v___y_2508_ = v___y_2521_;
v___y_2509_ = v___y_2522_;
v_a_2510_ = v_a_2557_;
goto v___jp_2503_;
}
}
}
else
{
lean_object* v_a_2558_; 
lean_dec_ref(v___y_2519_);
v_a_2558_ = lean_ctor_get(v___y_2523_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___y_2523_, 1);
v___y_2504_ = v___y_2516_;
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2518_;
v___y_2507_ = v___y_2520_;
v___y_2508_ = v___y_2521_;
v___y_2509_ = v___y_2522_;
v_a_2510_ = v_a_2558_;
goto v___jp_2503_;
}
}
v___jp_2559_:
{
uint8_t v_useDecide_2566_; 
v_useDecide_2566_ = lean_ctor_get_uint8(v_config_2414_, sizeof(void*)*1);
if (v_useDecide_2566_ == 0)
{
v___y_2481_ = v___y_2560_;
v___y_2482_ = v_isHEq_2561_;
v___y_2483_ = v___y_2562_;
v___y_2484_ = v___y_2563_;
v___y_2485_ = v___y_2564_;
v___y_2486_ = v___y_2565_;
goto v___jp_2480_;
}
else
{
uint8_t v___x_2567_; 
v___x_2567_ = l_Lean_Expr_hasFVar(v___x_2479_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; 
lean_inc_ref(v___x_2479_);
v___x_2568_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2479_, v___y_2563_);
if (lean_obj_tag(v___x_2568_) == 0)
{
lean_object* v_a_2569_; uint8_t v___x_2570_; 
v_a_2569_ = lean_ctor_get(v___x_2568_, 0);
lean_inc(v_a_2569_);
lean_dec_ref_known(v___x_2568_, 1);
v___x_2570_ = l_Lean_Expr_hasMVar(v_a_2569_);
if (v___x_2570_ == 0)
{
uint8_t v___x_2571_; 
v___x_2571_ = l_Lean_Expr_hasFVar(v_a_2569_);
lean_dec(v_a_2569_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; 
lean_inc_ref(v___x_2479_);
v___x_2572_ = l_Lean_Meta_mkDecide(v___x_2479_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2572_) == 0)
{
lean_object* v_a_2573_; lean_object* v___x_2574_; uint8_t v_transparency_2575_; uint8_t v___x_2576_; uint8_t v___x_2577_; 
v_a_2573_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2573_);
lean_dec_ref_known(v___x_2572_, 1);
v___x_2574_ = l_Lean_Meta_Context_config(v___y_2562_);
v_transparency_2575_ = lean_ctor_get_uint8(v___x_2574_, 9);
lean_dec_ref(v___x_2574_);
v___x_2576_ = 1;
v___x_2577_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2575_, v___x_2576_);
if (v___x_2577_ == 0)
{
lean_object* v_keyedConfig_2578_; uint8_t v_trackZetaDelta_2579_; lean_object* v_zetaDeltaSet_2580_; lean_object* v_lctx_2581_; lean_object* v_localInstances_2582_; lean_object* v_defEqCtx_x3f_2583_; lean_object* v_synthPendingDepth_2584_; lean_object* v_customCanUnfoldPredicate_x3f_2585_; uint8_t v_univApprox_2586_; uint8_t v_inTypeClassResolution_2587_; uint8_t v_cacheInferType_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v_keyedConfig_2578_ = lean_ctor_get(v___y_2562_, 0);
v_trackZetaDelta_2579_ = lean_ctor_get_uint8(v___y_2562_, sizeof(void*)*7);
v_zetaDeltaSet_2580_ = lean_ctor_get(v___y_2562_, 1);
v_lctx_2581_ = lean_ctor_get(v___y_2562_, 2);
v_localInstances_2582_ = lean_ctor_get(v___y_2562_, 3);
v_defEqCtx_x3f_2583_ = lean_ctor_get(v___y_2562_, 4);
v_synthPendingDepth_2584_ = lean_ctor_get(v___y_2562_, 5);
v_customCanUnfoldPredicate_x3f_2585_ = lean_ctor_get(v___y_2562_, 6);
v_univApprox_2586_ = lean_ctor_get_uint8(v___y_2562_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2587_ = lean_ctor_get_uint8(v___y_2562_, sizeof(void*)*7 + 2);
v_cacheInferType_2588_ = lean_ctor_get_uint8(v___y_2562_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2578_);
v___x_2589_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2576_, v_keyedConfig_2578_);
lean_inc(v_customCanUnfoldPredicate_x3f_2585_);
lean_inc(v_synthPendingDepth_2584_);
lean_inc(v_defEqCtx_x3f_2583_);
lean_inc_ref(v_localInstances_2582_);
lean_inc_ref(v_lctx_2581_);
lean_inc(v_zetaDeltaSet_2580_);
v___x_2590_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2590_, 0, v___x_2589_);
lean_ctor_set(v___x_2590_, 1, v_zetaDeltaSet_2580_);
lean_ctor_set(v___x_2590_, 2, v_lctx_2581_);
lean_ctor_set(v___x_2590_, 3, v_localInstances_2582_);
lean_ctor_set(v___x_2590_, 4, v_defEqCtx_x3f_2583_);
lean_ctor_set(v___x_2590_, 5, v_synthPendingDepth_2584_);
lean_ctor_set(v___x_2590_, 6, v_customCanUnfoldPredicate_x3f_2585_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*7, v_trackZetaDelta_2579_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*7 + 1, v_univApprox_2586_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2587_);
lean_ctor_set_uint8(v___x_2590_, sizeof(void*)*7 + 3, v_cacheInferType_2588_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc(v_a_2573_);
v___x_2591_ = lean_whnf(v_a_2573_, v___x_2590_, v___y_2563_, v___y_2564_, v___y_2565_);
v___y_2516_ = v___y_2564_;
v___y_2517_ = v___y_2560_;
v___y_2518_ = v___y_2563_;
v___y_2519_ = v_a_2573_;
v___y_2520_ = v___y_2562_;
v___y_2521_ = v_isHEq_2561_;
v___y_2522_ = v___y_2565_;
v___y_2523_ = v___x_2591_;
goto v___jp_2515_;
}
else
{
lean_object* v___x_2592_; 
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc_ref(v___y_2562_);
lean_inc(v_a_2573_);
v___x_2592_ = lean_whnf(v_a_2573_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
v___y_2516_ = v___y_2564_;
v___y_2517_ = v___y_2560_;
v___y_2518_ = v___y_2563_;
v___y_2519_ = v_a_2573_;
v___y_2520_ = v___y_2562_;
v___y_2521_ = v_isHEq_2561_;
v___y_2522_ = v___y_2565_;
v___y_2523_ = v___x_2592_;
goto v___jp_2515_;
}
}
else
{
lean_object* v_a_2593_; 
v_a_2593_ = lean_ctor_get(v___x_2572_, 0);
lean_inc(v_a_2593_);
lean_dec_ref_known(v___x_2572_, 1);
v___y_2504_ = v___y_2564_;
v___y_2505_ = v___y_2560_;
v___y_2506_ = v___y_2563_;
v___y_2507_ = v___y_2562_;
v___y_2508_ = v_isHEq_2561_;
v___y_2509_ = v___y_2565_;
v_a_2510_ = v_a_2593_;
goto v___jp_2503_;
}
}
else
{
v___y_2481_ = v___y_2560_;
v___y_2482_ = v_isHEq_2561_;
v___y_2483_ = v___y_2562_;
v___y_2484_ = v___y_2563_;
v___y_2485_ = v___y_2564_;
v___y_2486_ = v___y_2565_;
goto v___jp_2480_;
}
}
else
{
lean_dec(v_a_2569_);
v___y_2481_ = v___y_2560_;
v___y_2482_ = v_isHEq_2561_;
v___y_2483_ = v___y_2562_;
v___y_2484_ = v___y_2563_;
v___y_2485_ = v___y_2564_;
v___y_2486_ = v___y_2565_;
goto v___jp_2480_;
}
}
else
{
lean_object* v_a_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2601_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2594_ = lean_ctor_get(v___x_2568_, 0);
v_isSharedCheck_2601_ = !lean_is_exclusive(v___x_2568_);
if (v_isSharedCheck_2601_ == 0)
{
v___x_2596_ = v___x_2568_;
v_isShared_2597_ = v_isSharedCheck_2601_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_a_2594_);
lean_dec(v___x_2568_);
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
v___y_2481_ = v___y_2560_;
v___y_2482_ = v_isHEq_2561_;
v___y_2483_ = v___y_2562_;
v___y_2484_ = v___y_2563_;
v___y_2485_ = v___y_2564_;
v___y_2486_ = v___y_2565_;
goto v___jp_2480_;
}
}
}
v___jp_2602_:
{
lean_object* v___x_2608_; 
lean_inc_ref(v___x_2479_);
v___x_2608_ = l_Lean_Meta_matchHEq_x3f(v___x_2479_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2608_) == 0)
{
lean_object* v_a_2609_; 
v_a_2609_ = lean_ctor_get(v___x_2608_, 0);
lean_inc(v_a_2609_);
lean_dec_ref_known(v___x_2608_, 1);
if (lean_obj_tag(v_a_2609_) == 1)
{
lean_object* v_val_2610_; lean_object* v_snd_2611_; lean_object* v_snd_2612_; lean_object* v_fst_2613_; lean_object* v_fst_2614_; lean_object* v_fst_2615_; lean_object* v_snd_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2709_; 
v_val_2610_ = lean_ctor_get(v_a_2609_, 0);
lean_inc(v_val_2610_);
lean_dec_ref_known(v_a_2609_, 1);
v_snd_2611_ = lean_ctor_get(v_val_2610_, 1);
lean_inc(v_snd_2611_);
v_snd_2612_ = lean_ctor_get(v_snd_2611_, 1);
lean_inc(v_snd_2612_);
v_fst_2613_ = lean_ctor_get(v_val_2610_, 0);
lean_inc(v_fst_2613_);
lean_dec(v_val_2610_);
v_fst_2614_ = lean_ctor_get(v_snd_2611_, 0);
lean_inc(v_fst_2614_);
lean_dec(v_snd_2611_);
v_fst_2615_ = lean_ctor_get(v_snd_2612_, 0);
v_snd_2616_ = lean_ctor_get(v_snd_2612_, 1);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_snd_2612_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2618_ = v_snd_2612_;
v_isShared_2619_ = v_isSharedCheck_2709_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_snd_2616_);
lean_inc(v_fst_2615_);
lean_dec(v_snd_2612_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2709_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2620_; 
v___x_2620_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2614_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2620_) == 0)
{
lean_object* v_a_2621_; 
v_a_2621_ = lean_ctor_get(v___x_2620_, 0);
lean_inc(v_a_2621_);
lean_dec_ref_known(v___x_2620_, 1);
if (lean_obj_tag(v_a_2621_) == 1)
{
lean_object* v_val_2622_; lean_object* v___x_2623_; 
v_val_2622_ = lean_ctor_get(v_a_2621_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v_a_2621_, 1);
v___x_2623_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2616_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2623_) == 0)
{
lean_object* v_a_2624_; 
v_a_2624_ = lean_ctor_get(v___x_2623_, 0);
lean_inc(v_a_2624_);
lean_dec_ref_known(v___x_2623_, 1);
if (lean_obj_tag(v_a_2624_) == 1)
{
lean_object* v_toConstantVal_2625_; lean_object* v_val_2626_; lean_object* v___x_2628_; uint8_t v_isShared_2629_; uint8_t v_isSharedCheck_2692_; 
v_toConstantVal_2625_ = lean_ctor_get(v_val_2622_, 0);
lean_inc_ref(v_toConstantVal_2625_);
lean_dec(v_val_2622_);
v_val_2626_ = lean_ctor_get(v_a_2624_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v_a_2624_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2628_ = v_a_2624_;
v_isShared_2629_ = v_isSharedCheck_2692_;
goto v_resetjp_2627_;
}
else
{
lean_inc(v_val_2626_);
lean_dec(v_a_2624_);
v___x_2628_ = lean_box(0);
v_isShared_2629_ = v_isSharedCheck_2692_;
goto v_resetjp_2627_;
}
v_resetjp_2627_:
{
lean_object* v_toConstantVal_2630_; lean_object* v_name_2631_; lean_object* v_name_2632_; uint8_t v___x_2633_; 
v_toConstantVal_2630_ = lean_ctor_get(v_val_2626_, 0);
lean_inc_ref(v_toConstantVal_2630_);
lean_dec(v_val_2626_);
v_name_2631_ = lean_ctor_get(v_toConstantVal_2625_, 0);
lean_inc(v_name_2631_);
lean_dec_ref(v_toConstantVal_2625_);
v_name_2632_ = lean_ctor_get(v_toConstantVal_2630_, 0);
lean_inc(v_name_2632_);
lean_dec_ref(v_toConstantVal_2630_);
v___x_2633_ = lean_name_eq(v_name_2631_, v_name_2632_);
lean_dec(v_name_2632_);
lean_dec(v_name_2631_);
if (v___x_2633_ == 0)
{
lean_object* v___x_2634_; 
v___x_2634_ = l_Lean_Meta_isExprDefEq(v_fst_2613_, v_fst_2615_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2634_) == 0)
{
lean_object* v_a_2635_; uint8_t v___x_2636_; 
v_a_2635_ = lean_ctor_get(v___x_2634_, 0);
lean_inc(v_a_2635_);
lean_dec_ref_known(v___x_2634_, 1);
v___x_2636_ = lean_unbox(v_a_2635_);
lean_dec(v_a_2635_);
if (v___x_2636_ == 0)
{
lean_del_object(v___x_2628_);
lean_del_object(v___x_2618_);
v___y_2560_ = v_isEq_2603_;
v_isHEq_2561_ = v___x_2425_;
v___y_2562_ = v___y_2604_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___y_2606_;
v___y_2565_ = v___y_2607_;
goto v___jp_2559_;
}
else
{
lean_object* v___x_2637_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec_ref(v_config_2414_);
lean_inc(v_mvarId_2415_);
v___x_2637_ = l_Lean_MVarId_getType(v_mvarId_2415_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2637_) == 0)
{
lean_object* v_a_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v_a_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_a_2638_);
lean_dec_ref_known(v___x_2637_, 1);
v___x_2639_ = l_Lean_LocalDecl_toExpr(v_val_2446_);
v___x_2640_ = l_Lean_Meta_mkEqOfHEq(v___x_2639_, v___x_2425_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2640_) == 0)
{
lean_object* v_a_2641_; lean_object* v___x_2642_; 
v_a_2641_ = lean_ctor_get(v___x_2640_, 0);
lean_inc(v_a_2641_);
lean_dec_ref_known(v___x_2640_, 1);
v___x_2642_ = l_Lean_Meta_mkNoConfusion(v_a_2638_, v_a_2641_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
if (lean_obj_tag(v___x_2642_) == 0)
{
lean_object* v_a_2643_; lean_object* v___x_2644_; 
v_a_2643_ = lean_ctor_get(v___x_2642_, 0);
lean_inc(v_a_2643_);
lean_dec_ref_known(v___x_2642_, 1);
v___x_2644_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2415_, v_a_2643_, v___y_2605_);
if (lean_obj_tag(v___x_2644_) == 0)
{
lean_object* v___x_2645_; lean_object* v___x_2647_; 
lean_dec_ref_known(v___x_2644_, 1);
v___x_2645_ = lean_box(v___x_2425_);
if (v_isShared_2629_ == 0)
{
lean_ctor_set(v___x_2628_, 0, v___x_2645_);
v___x_2647_ = v___x_2628_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2645_);
v___x_2647_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2649_; 
if (v_isShared_2619_ == 0)
{
lean_ctor_set(v___x_2618_, 1, v___x_2450_);
lean_ctor_set(v___x_2618_, 0, v___x_2647_);
v___x_2649_ = v___x_2618_;
goto v_reusejp_2648_;
}
else
{
lean_object* v_reuseFailAlloc_2650_; 
v_reuseFailAlloc_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2650_, 0, v___x_2647_);
lean_ctor_set(v_reuseFailAlloc_2650_, 1, v___x_2450_);
v___x_2649_ = v_reuseFailAlloc_2650_;
goto v_reusejp_2648_;
}
v_reusejp_2648_:
{
v_a_2432_ = v___x_2649_;
goto v___jp_2431_;
}
}
}
else
{
lean_object* v_a_2652_; lean_object* v___x_2654_; uint8_t v_isShared_2655_; uint8_t v_isSharedCheck_2659_; 
lean_del_object(v___x_2628_);
lean_del_object(v___x_2618_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
v_a_2652_ = lean_ctor_get(v___x_2644_, 0);
v_isSharedCheck_2659_ = !lean_is_exclusive(v___x_2644_);
if (v_isSharedCheck_2659_ == 0)
{
v___x_2654_ = v___x_2644_;
v_isShared_2655_ = v_isSharedCheck_2659_;
goto v_resetjp_2653_;
}
else
{
lean_inc(v_a_2652_);
lean_dec(v___x_2644_);
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
else
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2667_; 
lean_del_object(v___x_2628_);
lean_del_object(v___x_2618_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2660_ = lean_ctor_get(v___x_2642_, 0);
v_isSharedCheck_2667_ = !lean_is_exclusive(v___x_2642_);
if (v_isSharedCheck_2667_ == 0)
{
v___x_2662_ = v___x_2642_;
v_isShared_2663_ = v_isSharedCheck_2667_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___x_2642_);
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
lean_dec(v_a_2638_);
lean_del_object(v___x_2628_);
lean_del_object(v___x_2618_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2668_ = lean_ctor_get(v___x_2640_, 0);
v_isSharedCheck_2675_ = !lean_is_exclusive(v___x_2640_);
if (v_isSharedCheck_2675_ == 0)
{
v___x_2670_ = v___x_2640_;
v_isShared_2671_ = v_isSharedCheck_2675_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_a_2668_);
lean_dec(v___x_2640_);
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
else
{
lean_object* v_a_2676_; lean_object* v___x_2678_; uint8_t v_isShared_2679_; uint8_t v_isSharedCheck_2683_; 
lean_del_object(v___x_2628_);
lean_del_object(v___x_2618_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2676_ = lean_ctor_get(v___x_2637_, 0);
v_isSharedCheck_2683_ = !lean_is_exclusive(v___x_2637_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2678_ = v___x_2637_;
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
else
{
lean_inc(v_a_2676_);
lean_dec(v___x_2637_);
v___x_2678_ = lean_box(0);
v_isShared_2679_ = v_isSharedCheck_2683_;
goto v_resetjp_2677_;
}
v_resetjp_2677_:
{
lean_object* v___x_2681_; 
if (v_isShared_2679_ == 0)
{
v___x_2681_ = v___x_2678_;
goto v_reusejp_2680_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_a_2676_);
v___x_2681_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2680_;
}
v_reusejp_2680_:
{
return v___x_2681_;
}
}
}
}
}
else
{
lean_object* v_a_2684_; lean_object* v___x_2686_; uint8_t v_isShared_2687_; uint8_t v_isSharedCheck_2691_; 
lean_del_object(v___x_2628_);
lean_del_object(v___x_2618_);
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2684_ = lean_ctor_get(v___x_2634_, 0);
v_isSharedCheck_2691_ = !lean_is_exclusive(v___x_2634_);
if (v_isSharedCheck_2691_ == 0)
{
v___x_2686_ = v___x_2634_;
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
else
{
lean_inc(v_a_2684_);
lean_dec(v___x_2634_);
v___x_2686_ = lean_box(0);
v_isShared_2687_ = v_isSharedCheck_2691_;
goto v_resetjp_2685_;
}
v_resetjp_2685_:
{
lean_object* v___x_2689_; 
if (v_isShared_2687_ == 0)
{
v___x_2689_ = v___x_2686_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_a_2684_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
else
{
lean_del_object(v___x_2628_);
lean_del_object(v___x_2618_);
lean_dec(v_fst_2615_);
lean_dec(v_fst_2613_);
v___y_2560_ = v_isEq_2603_;
v_isHEq_2561_ = v___x_2425_;
v___y_2562_ = v___y_2604_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___y_2606_;
v___y_2565_ = v___y_2607_;
goto v___jp_2559_;
}
}
}
else
{
lean_dec(v_a_2624_);
lean_dec(v_val_2622_);
lean_del_object(v___x_2618_);
lean_dec(v_fst_2615_);
lean_dec(v_fst_2613_);
v___y_2560_ = v_isEq_2603_;
v_isHEq_2561_ = v___x_2425_;
v___y_2562_ = v___y_2604_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___y_2606_;
v___y_2565_ = v___y_2607_;
goto v___jp_2559_;
}
}
else
{
lean_object* v_a_2693_; lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2700_; 
lean_dec(v_val_2622_);
lean_del_object(v___x_2618_);
lean_dec(v_fst_2615_);
lean_dec(v_fst_2613_);
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2693_ = lean_ctor_get(v___x_2623_, 0);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2623_);
if (v_isSharedCheck_2700_ == 0)
{
v___x_2695_ = v___x_2623_;
v_isShared_2696_ = v_isSharedCheck_2700_;
goto v_resetjp_2694_;
}
else
{
lean_inc(v_a_2693_);
lean_dec(v___x_2623_);
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
else
{
lean_dec(v_a_2621_);
lean_del_object(v___x_2618_);
lean_dec(v_snd_2616_);
lean_dec(v_fst_2615_);
lean_dec(v_fst_2613_);
v___y_2560_ = v_isEq_2603_;
v_isHEq_2561_ = v___x_2425_;
v___y_2562_ = v___y_2604_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___y_2606_;
v___y_2565_ = v___y_2607_;
goto v___jp_2559_;
}
}
else
{
lean_object* v_a_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2708_; 
lean_del_object(v___x_2618_);
lean_dec(v_snd_2616_);
lean_dec(v_fst_2615_);
lean_dec(v_fst_2613_);
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2701_ = lean_ctor_get(v___x_2620_, 0);
v_isSharedCheck_2708_ = !lean_is_exclusive(v___x_2620_);
if (v_isSharedCheck_2708_ == 0)
{
v___x_2703_ = v___x_2620_;
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
else
{
lean_inc(v_a_2701_);
lean_dec(v___x_2620_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2708_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2706_; 
if (v_isShared_2704_ == 0)
{
v___x_2706_ = v___x_2703_;
goto v_reusejp_2705_;
}
else
{
lean_object* v_reuseFailAlloc_2707_; 
v_reuseFailAlloc_2707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_a_2701_);
v___x_2706_ = v_reuseFailAlloc_2707_;
goto v_reusejp_2705_;
}
v_reusejp_2705_:
{
return v___x_2706_;
}
}
}
}
}
else
{
lean_dec(v_a_2609_);
v___y_2560_ = v_isEq_2603_;
v_isHEq_2561_ = v___x_2478_;
v___y_2562_ = v___y_2604_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___y_2606_;
v___y_2565_ = v___y_2607_;
goto v___jp_2559_;
}
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2710_ = lean_ctor_get(v___x_2608_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2608_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2608_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2608_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
v___jp_2718_:
{
lean_object* v___x_2723_; 
lean_inc_ref(v___x_2479_);
v___x_2723_ = l_Lean_Meta_matchEq_x3f(v___x_2479_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
lean_inc(v_a_2724_);
lean_dec_ref_known(v___x_2723_, 1);
if (lean_obj_tag(v_a_2724_) == 1)
{
lean_object* v_val_2725_; lean_object* v_snd_2726_; lean_object* v_fst_2727_; lean_object* v_snd_2728_; lean_object* v___x_2730_; uint8_t v_isShared_2731_; uint8_t v_isSharedCheck_2800_; 
v_val_2725_ = lean_ctor_get(v_a_2724_, 0);
lean_inc(v_val_2725_);
lean_dec_ref_known(v_a_2724_, 1);
v_snd_2726_ = lean_ctor_get(v_val_2725_, 1);
lean_inc(v_snd_2726_);
lean_dec(v_val_2725_);
v_fst_2727_ = lean_ctor_get(v_snd_2726_, 0);
v_snd_2728_ = lean_ctor_get(v_snd_2726_, 1);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_snd_2726_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2730_ = v_snd_2726_;
v_isShared_2731_ = v_isSharedCheck_2800_;
goto v_resetjp_2729_;
}
else
{
lean_inc(v_snd_2728_);
lean_inc(v_fst_2727_);
lean_dec(v_snd_2726_);
v___x_2730_ = lean_box(0);
v_isShared_2731_ = v_isSharedCheck_2800_;
goto v_resetjp_2729_;
}
v_resetjp_2729_:
{
lean_object* v___x_2732_; 
v___x_2732_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2727_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2732_) == 0)
{
lean_object* v_a_2733_; 
v_a_2733_ = lean_ctor_get(v___x_2732_, 0);
lean_inc(v_a_2733_);
lean_dec_ref_known(v___x_2732_, 1);
if (lean_obj_tag(v_a_2733_) == 1)
{
lean_object* v_val_2734_; lean_object* v___x_2735_; 
v_val_2734_ = lean_ctor_get(v_a_2733_, 0);
lean_inc(v_val_2734_);
lean_dec_ref_known(v_a_2733_, 1);
v___x_2735_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2728_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
if (lean_obj_tag(v_a_2736_) == 1)
{
lean_object* v_toConstantVal_2737_; lean_object* v_val_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2783_; 
v_toConstantVal_2737_ = lean_ctor_get(v_val_2734_, 0);
lean_inc_ref(v_toConstantVal_2737_);
lean_dec(v_val_2734_);
v_val_2738_ = lean_ctor_get(v_a_2736_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v_a_2736_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2740_ = v_a_2736_;
v_isShared_2741_ = v_isSharedCheck_2783_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_val_2738_);
lean_dec(v_a_2736_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2783_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v_toConstantVal_2742_; lean_object* v_name_2743_; lean_object* v_name_2744_; uint8_t v___x_2745_; 
v_toConstantVal_2742_ = lean_ctor_get(v_val_2738_, 0);
lean_inc_ref(v_toConstantVal_2742_);
lean_dec(v_val_2738_);
v_name_2743_ = lean_ctor_get(v_toConstantVal_2737_, 0);
lean_inc(v_name_2743_);
lean_dec_ref(v_toConstantVal_2737_);
v_name_2744_ = lean_ctor_get(v_toConstantVal_2742_, 0);
lean_inc(v_name_2744_);
lean_dec_ref(v_toConstantVal_2742_);
v___x_2745_ = lean_name_eq(v_name_2743_, v_name_2744_);
lean_dec(v_name_2744_);
lean_dec(v_name_2743_);
if (v___x_2745_ == 0)
{
lean_object* v___x_2746_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec_ref(v_config_2414_);
lean_inc(v_mvarId_2415_);
v___x_2746_ = l_Lean_MVarId_getType(v_mvarId_2415_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2748_ = l_Lean_LocalDecl_toExpr(v_val_2446_);
v___x_2749_ = l_Lean_Meta_mkNoConfusion(v_a_2747_, v___x_2748_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
if (lean_obj_tag(v___x_2749_) == 0)
{
lean_object* v_a_2750_; lean_object* v___x_2751_; 
v_a_2750_ = lean_ctor_get(v___x_2749_, 0);
lean_inc(v_a_2750_);
lean_dec_ref_known(v___x_2749_, 1);
v___x_2751_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2415_, v_a_2750_, v___y_2720_);
if (lean_obj_tag(v___x_2751_) == 0)
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
lean_dec_ref_known(v___x_2751_, 1);
v___x_2752_ = lean_box(v___x_2425_);
if (v_isShared_2741_ == 0)
{
lean_ctor_set(v___x_2740_, 0, v___x_2752_);
v___x_2754_ = v___x_2740_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
lean_object* v___x_2756_; 
if (v_isShared_2731_ == 0)
{
lean_ctor_set(v___x_2730_, 1, v___x_2450_);
lean_ctor_set(v___x_2730_, 0, v___x_2754_);
v___x_2756_ = v___x_2730_;
goto v_reusejp_2755_;
}
else
{
lean_object* v_reuseFailAlloc_2757_; 
v_reuseFailAlloc_2757_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2757_, 0, v___x_2754_);
lean_ctor_set(v_reuseFailAlloc_2757_, 1, v___x_2450_);
v___x_2756_ = v_reuseFailAlloc_2757_;
goto v_reusejp_2755_;
}
v_reusejp_2755_:
{
v_a_2432_ = v___x_2756_;
goto v___jp_2431_;
}
}
}
else
{
lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2766_; 
lean_del_object(v___x_2740_);
lean_del_object(v___x_2730_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
v_a_2759_ = lean_ctor_get(v___x_2751_, 0);
v_isSharedCheck_2766_ = !lean_is_exclusive(v___x_2751_);
if (v_isSharedCheck_2766_ == 0)
{
v___x_2761_ = v___x_2751_;
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2751_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2766_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2764_; 
if (v_isShared_2762_ == 0)
{
v___x_2764_ = v___x_2761_;
goto v_reusejp_2763_;
}
else
{
lean_object* v_reuseFailAlloc_2765_; 
v_reuseFailAlloc_2765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2759_);
v___x_2764_ = v_reuseFailAlloc_2765_;
goto v_reusejp_2763_;
}
v_reusejp_2763_:
{
return v___x_2764_;
}
}
}
}
else
{
lean_object* v_a_2767_; lean_object* v___x_2769_; uint8_t v_isShared_2770_; uint8_t v_isSharedCheck_2774_; 
lean_del_object(v___x_2740_);
lean_del_object(v___x_2730_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2767_ = lean_ctor_get(v___x_2749_, 0);
v_isSharedCheck_2774_ = !lean_is_exclusive(v___x_2749_);
if (v_isSharedCheck_2774_ == 0)
{
v___x_2769_ = v___x_2749_;
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
else
{
lean_inc(v_a_2767_);
lean_dec(v___x_2749_);
v___x_2769_ = lean_box(0);
v_isShared_2770_ = v_isSharedCheck_2774_;
goto v_resetjp_2768_;
}
v_resetjp_2768_:
{
lean_object* v___x_2772_; 
if (v_isShared_2770_ == 0)
{
v___x_2772_ = v___x_2769_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2773_; 
v_reuseFailAlloc_2773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2773_, 0, v_a_2767_);
v___x_2772_ = v_reuseFailAlloc_2773_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
return v___x_2772_;
}
}
}
}
else
{
lean_object* v_a_2775_; lean_object* v___x_2777_; uint8_t v_isShared_2778_; uint8_t v_isSharedCheck_2782_; 
lean_del_object(v___x_2740_);
lean_del_object(v___x_2730_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2775_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2782_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2782_ == 0)
{
v___x_2777_ = v___x_2746_;
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
else
{
lean_inc(v_a_2775_);
lean_dec(v___x_2746_);
v___x_2777_ = lean_box(0);
v_isShared_2778_ = v_isSharedCheck_2782_;
goto v_resetjp_2776_;
}
v_resetjp_2776_:
{
lean_object* v___x_2780_; 
if (v_isShared_2778_ == 0)
{
v___x_2780_ = v___x_2777_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_a_2775_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
else
{
lean_del_object(v___x_2740_);
lean_del_object(v___x_2730_);
v_isEq_2603_ = v___x_2425_;
v___y_2604_ = v___y_2719_;
v___y_2605_ = v___y_2720_;
v___y_2606_ = v___y_2721_;
v___y_2607_ = v___y_2722_;
goto v___jp_2602_;
}
}
}
else
{
lean_dec(v_a_2736_);
lean_dec(v_val_2734_);
lean_del_object(v___x_2730_);
v_isEq_2603_ = v___x_2425_;
v___y_2604_ = v___y_2719_;
v___y_2605_ = v___y_2720_;
v___y_2606_ = v___y_2721_;
v___y_2607_ = v___y_2722_;
goto v___jp_2602_;
}
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_dec(v_val_2734_);
lean_del_object(v___x_2730_);
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2784_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2735_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2735_);
v___x_2786_ = lean_box(0);
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
v_resetjp_2785_:
{
lean_object* v___x_2789_; 
if (v_isShared_2787_ == 0)
{
v___x_2789_ = v___x_2786_;
goto v_reusejp_2788_;
}
else
{
lean_object* v_reuseFailAlloc_2790_; 
v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
v___x_2789_ = v_reuseFailAlloc_2790_;
goto v_reusejp_2788_;
}
v_reusejp_2788_:
{
return v___x_2789_;
}
}
}
}
else
{
lean_dec(v_a_2733_);
lean_del_object(v___x_2730_);
lean_dec(v_snd_2728_);
v_isEq_2603_ = v___x_2425_;
v___y_2604_ = v___y_2719_;
v___y_2605_ = v___y_2720_;
v___y_2606_ = v___y_2721_;
v___y_2607_ = v___y_2722_;
goto v___jp_2602_;
}
}
else
{
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_del_object(v___x_2730_);
lean_dec(v_snd_2728_);
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2792_ = lean_ctor_get(v___x_2732_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2732_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2732_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2732_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2797_; 
if (v_isShared_2795_ == 0)
{
v___x_2797_ = v___x_2794_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_a_2792_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
else
{
lean_dec(v_a_2724_);
v_isEq_2603_ = v___x_2478_;
v___y_2604_ = v___y_2719_;
v___y_2605_ = v___y_2720_;
v___y_2606_ = v___y_2721_;
v___y_2607_ = v___y_2722_;
goto v___jp_2602_;
}
}
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2801_ = lean_ctor_get(v___x_2723_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2723_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2723_);
v___x_2803_ = lean_box(0);
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
v_resetjp_2802_:
{
lean_object* v___x_2806_; 
if (v_isShared_2804_ == 0)
{
v___x_2806_ = v___x_2803_;
goto v_reusejp_2805_;
}
else
{
lean_object* v_reuseFailAlloc_2807_; 
v_reuseFailAlloc_2807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2807_, 0, v_a_2801_);
v___x_2806_ = v_reuseFailAlloc_2807_;
goto v_reusejp_2805_;
}
v_reusejp_2805_:
{
return v___x_2806_;
}
}
}
}
v___jp_2809_:
{
lean_object* v___x_2814_; 
lean_inc_ref(v___x_2479_);
v___x_2814_ = l_Lean_refutableHasNotBit_x3f(v___x_2479_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v_a_2815_; 
v_a_2815_ = lean_ctor_get(v___x_2814_, 0);
lean_inc(v_a_2815_);
lean_dec_ref_known(v___x_2814_, 1);
if (lean_obj_tag(v_a_2815_) == 1)
{
lean_object* v_val_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2855_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec_ref(v_config_2414_);
v_val_2816_ = lean_ctor_get(v_a_2815_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v_a_2815_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2818_ = v_a_2815_;
v_isShared_2819_ = v_isSharedCheck_2855_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_val_2816_);
lean_dec(v_a_2815_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2855_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2820_; 
lean_inc(v_mvarId_2415_);
v___x_2820_ = l_Lean_MVarId_getType(v_mvarId_2415_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2820_) == 0)
{
lean_object* v_a_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v_a_2821_ = lean_ctor_get(v___x_2820_, 0);
lean_inc(v_a_2821_);
lean_dec_ref_known(v___x_2820_, 1);
v___x_2822_ = l_Lean_LocalDecl_toExpr(v_val_2446_);
v___x_2823_ = l_Lean_Meta_mkAbsurd(v_a_2821_, v_val_2816_, v___x_2822_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2823_) == 0)
{
lean_object* v_a_2824_; lean_object* v___x_2825_; 
v_a_2824_ = lean_ctor_get(v___x_2823_, 0);
lean_inc(v_a_2824_);
lean_dec_ref_known(v___x_2823_, 1);
v___x_2825_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2415_, v_a_2824_, v___y_2811_);
if (lean_obj_tag(v___x_2825_) == 0)
{
lean_object* v___x_2826_; lean_object* v___x_2828_; 
lean_dec_ref_known(v___x_2825_, 1);
v___x_2826_ = lean_box(v___x_2425_);
if (v_isShared_2819_ == 0)
{
lean_ctor_set(v___x_2818_, 0, v___x_2826_);
v___x_2828_ = v___x_2818_;
goto v_reusejp_2827_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2826_);
v___x_2828_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2827_;
}
v_reusejp_2827_:
{
lean_object* v___x_2829_; 
v___x_2829_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2829_, 0, v___x_2828_);
lean_ctor_set(v___x_2829_, 1, v___x_2450_);
v_a_2432_ = v___x_2829_;
goto v___jp_2431_;
}
}
else
{
lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2838_; 
lean_del_object(v___x_2818_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
v_a_2831_ = lean_ctor_get(v___x_2825_, 0);
v_isSharedCheck_2838_ = !lean_is_exclusive(v___x_2825_);
if (v_isSharedCheck_2838_ == 0)
{
v___x_2833_ = v___x_2825_;
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_dec(v___x_2825_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2838_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2836_; 
if (v_isShared_2834_ == 0)
{
v___x_2836_ = v___x_2833_;
goto v_reusejp_2835_;
}
else
{
lean_object* v_reuseFailAlloc_2837_; 
v_reuseFailAlloc_2837_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2837_, 0, v_a_2831_);
v___x_2836_ = v_reuseFailAlloc_2837_;
goto v_reusejp_2835_;
}
v_reusejp_2835_:
{
return v___x_2836_;
}
}
}
}
else
{
lean_object* v_a_2839_; lean_object* v___x_2841_; uint8_t v_isShared_2842_; uint8_t v_isSharedCheck_2846_; 
lean_del_object(v___x_2818_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2839_ = lean_ctor_get(v___x_2823_, 0);
v_isSharedCheck_2846_ = !lean_is_exclusive(v___x_2823_);
if (v_isSharedCheck_2846_ == 0)
{
v___x_2841_ = v___x_2823_;
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
else
{
lean_inc(v_a_2839_);
lean_dec(v___x_2823_);
v___x_2841_ = lean_box(0);
v_isShared_2842_ = v_isSharedCheck_2846_;
goto v_resetjp_2840_;
}
v_resetjp_2840_:
{
lean_object* v___x_2844_; 
if (v_isShared_2842_ == 0)
{
v___x_2844_ = v___x_2841_;
goto v_reusejp_2843_;
}
else
{
lean_object* v_reuseFailAlloc_2845_; 
v_reuseFailAlloc_2845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2845_, 0, v_a_2839_);
v___x_2844_ = v_reuseFailAlloc_2845_;
goto v_reusejp_2843_;
}
v_reusejp_2843_:
{
return v___x_2844_;
}
}
}
}
else
{
lean_object* v_a_2847_; lean_object* v___x_2849_; uint8_t v_isShared_2850_; uint8_t v_isSharedCheck_2854_; 
lean_del_object(v___x_2818_);
lean_dec(v_val_2816_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2847_ = lean_ctor_get(v___x_2820_, 0);
v_isSharedCheck_2854_ = !lean_is_exclusive(v___x_2820_);
if (v_isSharedCheck_2854_ == 0)
{
v___x_2849_ = v___x_2820_;
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
else
{
lean_inc(v_a_2847_);
lean_dec(v___x_2820_);
v___x_2849_ = lean_box(0);
v_isShared_2850_ = v_isSharedCheck_2854_;
goto v_resetjp_2848_;
}
v_resetjp_2848_:
{
lean_object* v___x_2852_; 
if (v_isShared_2850_ == 0)
{
v___x_2852_ = v___x_2849_;
goto v_reusejp_2851_;
}
else
{
lean_object* v_reuseFailAlloc_2853_; 
v_reuseFailAlloc_2853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2853_, 0, v_a_2847_);
v___x_2852_ = v_reuseFailAlloc_2853_;
goto v_reusejp_2851_;
}
v_reusejp_2851_:
{
return v___x_2852_;
}
}
}
}
}
else
{
lean_object* v___x_2856_; 
lean_dec(v_a_2815_);
lean_inc_ref(v___x_2479_);
v___x_2856_ = l_Lean_Meta_matchNe_x3f(v___x_2479_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2856_) == 0)
{
lean_object* v_a_2857_; 
v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
lean_inc(v_a_2857_);
lean_dec_ref_known(v___x_2856_, 1);
if (lean_obj_tag(v_a_2857_) == 1)
{
lean_object* v_val_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2927_; 
v_val_2858_ = lean_ctor_get(v_a_2857_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_a_2857_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2860_ = v_a_2857_;
v_isShared_2861_ = v_isSharedCheck_2927_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_val_2858_);
lean_dec(v_a_2857_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2927_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v_snd_2862_; lean_object* v_fst_2863_; lean_object* v_snd_2864_; lean_object* v___x_2866_; uint8_t v_isShared_2867_; uint8_t v_isSharedCheck_2926_; 
v_snd_2862_ = lean_ctor_get(v_val_2858_, 1);
lean_inc(v_snd_2862_);
lean_dec(v_val_2858_);
v_fst_2863_ = lean_ctor_get(v_snd_2862_, 0);
v_snd_2864_ = lean_ctor_get(v_snd_2862_, 1);
v_isSharedCheck_2926_ = !lean_is_exclusive(v_snd_2862_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2866_ = v_snd_2862_;
v_isShared_2867_ = v_isSharedCheck_2926_;
goto v_resetjp_2865_;
}
else
{
lean_inc(v_snd_2864_);
lean_inc(v_fst_2863_);
lean_dec(v_snd_2862_);
v___x_2866_ = lean_box(0);
v_isShared_2867_ = v_isSharedCheck_2926_;
goto v_resetjp_2865_;
}
v_resetjp_2865_:
{
lean_object* v___x_2868_; 
lean_inc(v_fst_2863_);
v___x_2868_ = l_Lean_Meta_isExprDefEq(v_fst_2863_, v_snd_2864_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; uint8_t v___x_2870_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
lean_inc(v_a_2869_);
lean_dec_ref_known(v___x_2868_, 1);
v___x_2870_ = lean_unbox(v_a_2869_);
lean_dec(v_a_2869_);
if (v___x_2870_ == 0)
{
lean_del_object(v___x_2866_);
lean_dec(v_fst_2863_);
lean_del_object(v___x_2860_);
v___y_2719_ = v___y_2810_;
v___y_2720_ = v___y_2811_;
v___y_2721_ = v___y_2812_;
v___y_2722_ = v___y_2813_;
goto v___jp_2718_;
}
else
{
lean_object* v___x_2871_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec_ref(v_config_2414_);
lean_inc(v_mvarId_2415_);
v___x_2871_ = l_Lean_MVarId_getType(v_mvarId_2415_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2871_) == 0)
{
lean_object* v_a_2872_; lean_object* v___x_2873_; 
v_a_2872_ = lean_ctor_get(v___x_2871_, 0);
lean_inc(v_a_2872_);
lean_dec_ref_known(v___x_2871_, 1);
v___x_2873_ = l_Lean_Meta_mkEqRefl(v_fst_2863_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
v___x_2875_ = l_Lean_LocalDecl_toExpr(v_val_2446_);
v___x_2876_ = l_Lean_Meta_mkAbsurd(v_a_2872_, v_a_2874_, v___x_2875_, v___y_2810_, v___y_2811_, v___y_2812_, v___y_2813_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; lean_object* v___x_2878_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
v___x_2878_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2415_, v_a_2877_, v___y_2811_);
if (lean_obj_tag(v___x_2878_) == 0)
{
lean_object* v___x_2879_; lean_object* v___x_2881_; 
lean_dec_ref_known(v___x_2878_, 1);
v___x_2879_ = lean_box(v___x_2425_);
if (v_isShared_2861_ == 0)
{
lean_ctor_set(v___x_2860_, 0, v___x_2879_);
v___x_2881_ = v___x_2860_;
goto v_reusejp_2880_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2879_);
v___x_2881_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2880_;
}
v_reusejp_2880_:
{
lean_object* v___x_2883_; 
if (v_isShared_2867_ == 0)
{
lean_ctor_set(v___x_2866_, 1, v___x_2450_);
lean_ctor_set(v___x_2866_, 0, v___x_2881_);
v___x_2883_ = v___x_2866_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2884_, 1, v___x_2450_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
v_a_2432_ = v___x_2883_;
goto v___jp_2431_;
}
}
}
else
{
lean_object* v_a_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2893_; 
lean_del_object(v___x_2866_);
lean_del_object(v___x_2860_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
v_a_2886_ = lean_ctor_get(v___x_2878_, 0);
v_isSharedCheck_2893_ = !lean_is_exclusive(v___x_2878_);
if (v_isSharedCheck_2893_ == 0)
{
v___x_2888_ = v___x_2878_;
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
else
{
lean_inc(v_a_2886_);
lean_dec(v___x_2878_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2893_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2891_; 
if (v_isShared_2889_ == 0)
{
v___x_2891_ = v___x_2888_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_a_2886_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
}
}
else
{
lean_object* v_a_2894_; lean_object* v___x_2896_; uint8_t v_isShared_2897_; uint8_t v_isSharedCheck_2901_; 
lean_del_object(v___x_2866_);
lean_del_object(v___x_2860_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2894_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2901_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2901_ == 0)
{
v___x_2896_ = v___x_2876_;
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
else
{
lean_inc(v_a_2894_);
lean_dec(v___x_2876_);
v___x_2896_ = lean_box(0);
v_isShared_2897_ = v_isSharedCheck_2901_;
goto v_resetjp_2895_;
}
v_resetjp_2895_:
{
lean_object* v___x_2899_; 
if (v_isShared_2897_ == 0)
{
v___x_2899_ = v___x_2896_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2900_; 
v_reuseFailAlloc_2900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2900_, 0, v_a_2894_);
v___x_2899_ = v_reuseFailAlloc_2900_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
return v___x_2899_;
}
}
}
}
else
{
lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_a_2872_);
lean_del_object(v___x_2866_);
lean_del_object(v___x_2860_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2902_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2873_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_dec(v___x_2873_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
}
}
}
}
else
{
lean_object* v_a_2910_; lean_object* v___x_2912_; uint8_t v_isShared_2913_; uint8_t v_isSharedCheck_2917_; 
lean_del_object(v___x_2866_);
lean_dec(v_fst_2863_);
lean_del_object(v___x_2860_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
v_a_2910_ = lean_ctor_get(v___x_2871_, 0);
v_isSharedCheck_2917_ = !lean_is_exclusive(v___x_2871_);
if (v_isSharedCheck_2917_ == 0)
{
v___x_2912_ = v___x_2871_;
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
else
{
lean_inc(v_a_2910_);
lean_dec(v___x_2871_);
v___x_2912_ = lean_box(0);
v_isShared_2913_ = v_isSharedCheck_2917_;
goto v_resetjp_2911_;
}
v_resetjp_2911_:
{
lean_object* v___x_2915_; 
if (v_isShared_2913_ == 0)
{
v___x_2915_ = v___x_2912_;
goto v_reusejp_2914_;
}
else
{
lean_object* v_reuseFailAlloc_2916_; 
v_reuseFailAlloc_2916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
v___x_2915_ = v_reuseFailAlloc_2916_;
goto v_reusejp_2914_;
}
v_reusejp_2914_:
{
return v___x_2915_;
}
}
}
}
}
else
{
lean_object* v_a_2918_; lean_object* v___x_2920_; uint8_t v_isShared_2921_; uint8_t v_isSharedCheck_2925_; 
lean_del_object(v___x_2866_);
lean_dec(v_fst_2863_);
lean_del_object(v___x_2860_);
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2918_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2925_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2920_ = v___x_2868_;
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
else
{
lean_inc(v_a_2918_);
lean_dec(v___x_2868_);
v___x_2920_ = lean_box(0);
v_isShared_2921_ = v_isSharedCheck_2925_;
goto v_resetjp_2919_;
}
v_resetjp_2919_:
{
lean_object* v___x_2923_; 
if (v_isShared_2921_ == 0)
{
v___x_2923_ = v___x_2920_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
v___x_2923_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
return v___x_2923_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2857_);
v___y_2719_ = v___y_2810_;
v___y_2720_ = v___y_2811_;
v___y_2721_ = v___y_2812_;
v___y_2722_ = v___y_2813_;
goto v___jp_2718_;
}
}
else
{
lean_object* v_a_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2935_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2928_ = lean_ctor_get(v___x_2856_, 0);
v_isSharedCheck_2935_ = !lean_is_exclusive(v___x_2856_);
if (v_isSharedCheck_2935_ == 0)
{
v___x_2930_ = v___x_2856_;
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_a_2928_);
lean_dec(v___x_2856_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2935_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2933_; 
if (v_isShared_2931_ == 0)
{
v___x_2933_ = v___x_2930_;
goto v_reusejp_2932_;
}
else
{
lean_object* v_reuseFailAlloc_2934_; 
v_reuseFailAlloc_2934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2934_, 0, v_a_2928_);
v___x_2933_ = v_reuseFailAlloc_2934_;
goto v_reusejp_2932_;
}
v_reusejp_2932_:
{
return v___x_2933_;
}
}
}
}
}
else
{
lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2943_; 
lean_dec_ref(v___x_2479_);
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2936_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2943_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2943_ == 0)
{
v___x_2938_ = v___x_2814_;
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_dec(v___x_2814_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2943_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
lean_object* v___x_2941_; 
if (v_isShared_2939_ == 0)
{
v___x_2941_ = v___x_2938_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v_a_2936_);
v___x_2941_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
return v___x_2941_;
}
}
}
}
}
else
{
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
v_a_2440_ = v___x_2451_;
goto v___jp_2439_;
}
v___jp_2452_:
{
uint8_t v_emptyType_2459_; 
v_emptyType_2459_ = lean_ctor_get_uint8(v_config_2414_, sizeof(void*)*1 + 1);
if (v_emptyType_2459_ == 0)
{
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
v_a_2440_ = v___x_2451_;
goto v___jp_2439_;
}
else
{
if (v___y_2453_ == 0)
{
if (v___y_2454_ == 0)
{
lean_object* v_searchFuel_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; 
v_searchFuel_2460_ = lean_ctor_get(v_config_2414_, 0);
v___x_2461_ = l_Lean_LocalDecl_fvarId(v_val_2446_);
lean_dec(v_val_2446_);
lean_inc(v_searchFuel_2460_);
lean_inc(v_mvarId_2415_);
v___x_2462_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2415_, v___x_2461_, v_searchFuel_2460_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; uint8_t v___x_2464_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2464_ = lean_unbox(v_a_2463_);
lean_dec(v_a_2463_);
if (v___x_2464_ == 0)
{
lean_del_object(v___x_2448_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
v_a_2440_ = v___x_2451_;
goto v___jp_2439_;
}
else
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v___x_2465_ = lean_box(v___x_2425_);
if (v_isShared_2449_ == 0)
{
lean_ctor_set(v___x_2448_, 0, v___x_2465_);
v___x_2467_ = v___x_2448_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
lean_object* v___x_2468_; 
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2467_);
lean_ctor_set(v___x_2468_, 1, v___x_2450_);
v_a_2432_ = v___x_2468_;
goto v___jp_2431_;
}
}
}
else
{
lean_object* v_a_2470_; lean_object* v___x_2472_; uint8_t v_isShared_2473_; uint8_t v_isSharedCheck_2477_; 
lean_del_object(v___x_2448_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
lean_dec(v_mvarId_2415_);
lean_dec_ref(v_config_2414_);
v_a_2470_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2477_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2477_ == 0)
{
v___x_2472_ = v___x_2462_;
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
else
{
lean_inc(v_a_2470_);
lean_dec(v___x_2462_);
v___x_2472_ = lean_box(0);
v_isShared_2473_ = v_isSharedCheck_2477_;
goto v_resetjp_2471_;
}
v_resetjp_2471_:
{
lean_object* v___x_2475_; 
if (v_isShared_2473_ == 0)
{
v___x_2475_ = v___x_2472_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_a_2470_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
else
{
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
v_a_2440_ = v___x_2451_;
goto v___jp_2439_;
}
}
else
{
lean_del_object(v___x_2448_);
lean_dec(v_val_2446_);
lean_del_object(v___x_2429_);
lean_dec(v_snd_2427_);
v_a_2440_ = v___x_2451_;
goto v___jp_2439_;
}
}
}
}
}
v___jp_2431_:
{
lean_object* v___x_2433_; lean_object* v___x_2435_; 
v___x_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2433_, 0, v_a_2432_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 0, v___x_2433_);
v___x_2435_ = v___x_2429_;
goto v_reusejp_2434_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2433_);
lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_snd_2427_);
v___x_2435_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2434_;
}
v_reusejp_2434_:
{
lean_object* v___x_2436_; 
v___x_2436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2436_, 0, v___x_2435_);
return v___x_2436_;
}
}
v___jp_2439_:
{
lean_object* v___x_2441_; size_t v___x_2442_; size_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v___x_2438_);
lean_ctor_set(v___x_2441_, 1, v_a_2440_);
v___x_2442_ = ((size_t)1ULL);
v___x_2443_ = lean_usize_add(v_i_2418_, v___x_2442_);
v___x_2444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2414_, v_mvarId_2415_, v_as_2416_, v_sz_2417_, v___x_2443_, v___x_2441_, v___y_2420_, v___y_2421_, v___y_2422_, v___y_2423_);
return v___x_2444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3010_, lean_object* v_mvarId_3011_, lean_object* v_as_3012_, lean_object* v_sz_3013_, lean_object* v_i_3014_, lean_object* v_b_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
size_t v_sz_boxed_3021_; size_t v_i_boxed_3022_; lean_object* v_res_3023_; 
v_sz_boxed_3021_ = lean_unbox_usize(v_sz_3013_);
lean_dec(v_sz_3013_);
v_i_boxed_3022_ = lean_unbox_usize(v_i_3014_);
lean_dec(v_i_3014_);
v_res_3023_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3010_, v_mvarId_3011_, v_as_3012_, v_sz_boxed_3021_, v_i_boxed_3022_, v_b_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec_ref(v_as_3012_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3027_, lean_object* v_mvarId_3028_, lean_object* v_as_3029_, size_t v_sz_3030_, size_t v_i_3031_, lean_object* v_b_3032_, lean_object* v___y_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_){
_start:
{
uint8_t v___x_3038_; 
v___x_3038_ = lean_usize_dec_lt(v_i_3031_, v_sz_3030_);
if (v___x_3038_ == 0)
{
lean_object* v___x_3039_; 
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v___x_3039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3039_, 0, v_b_3032_);
return v___x_3039_;
}
else
{
lean_object* v_snd_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3653_; 
v_snd_3040_ = lean_ctor_get(v_b_3032_, 1);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_b_3032_);
if (v_isSharedCheck_3653_ == 0)
{
lean_object* v_unused_3654_; 
v_unused_3654_ = lean_ctor_get(v_b_3032_, 0);
lean_dec(v_unused_3654_);
v___x_3042_ = v_b_3032_;
v_isShared_3043_ = v_isSharedCheck_3653_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_snd_3040_);
lean_dec(v_b_3032_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3653_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v_a_3045_; lean_object* v___x_3051_; lean_object* v_a_3053_; lean_object* v_a_3058_; 
v___x_3051_ = lean_box(0);
v_a_3058_ = lean_array_uget(v_as_3029_, v_i_3031_);
if (lean_obj_tag(v_a_3058_) == 0)
{
lean_del_object(v___x_3042_);
v_a_3053_ = v_snd_3040_;
goto v___jp_3052_;
}
else
{
lean_object* v_val_3059_; lean_object* v___x_3061_; uint8_t v_isShared_3062_; uint8_t v_isSharedCheck_3652_; 
v_val_3059_ = lean_ctor_get(v_a_3058_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v_a_3058_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3061_ = v_a_3058_;
v_isShared_3062_ = v_isSharedCheck_3652_;
goto v_resetjp_3060_;
}
else
{
lean_inc(v_val_3059_);
lean_dec(v_a_3058_);
v___x_3061_ = lean_box(0);
v_isShared_3062_ = v_isSharedCheck_3652_;
goto v_resetjp_3060_;
}
v_resetjp_3060_:
{
lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___y_3066_; uint8_t v___y_3067_; lean_object* v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; uint8_t v___x_3092_; 
v___x_3063_ = lean_box(0);
v___x_3064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3092_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3059_);
if (v___x_3092_ == 0)
{
lean_object* v___x_3093_; uint8_t v___y_3095_; uint8_t v___y_3096_; lean_object* v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3119_; lean_object* v___y_3120_; lean_object* v___y_3121_; uint8_t v___y_3122_; uint8_t v___y_3123_; lean_object* v___y_3124_; lean_object* v_a_3125_; lean_object* v___y_3131_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; uint8_t v___y_3135_; uint8_t v___y_3136_; lean_object* v___y_3137_; lean_object* v___y_3138_; uint8_t v___y_3182_; uint8_t v_isHEq_3183_; lean_object* v___y_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; uint8_t v_isEq_3225_; lean_object* v___y_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___x_3582_; 
v___x_3093_ = l_Lean_LocalDecl_type(v_val_3059_);
lean_inc_ref(v___x_3093_);
v___x_3582_ = l_Lean_Meta_matchNot_x3f(v___x_3093_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
if (lean_obj_tag(v___x_3582_) == 0)
{
lean_object* v_a_3583_; 
v_a_3583_ = lean_ctor_get(v___x_3582_, 0);
lean_inc(v_a_3583_);
lean_dec_ref_known(v___x_3582_, 1);
if (lean_obj_tag(v_a_3583_) == 1)
{
lean_object* v_val_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3643_; 
v_val_3584_ = lean_ctor_get(v_a_3583_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v_a_3583_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3586_ = v_a_3583_;
v_isShared_3587_ = v_isSharedCheck_3643_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_val_3584_);
lean_dec(v_a_3583_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3643_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3588_; 
v___x_3588_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3584_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
if (lean_obj_tag(v___x_3588_) == 0)
{
lean_object* v_a_3589_; 
v_a_3589_ = lean_ctor_get(v___x_3588_, 0);
lean_inc(v_a_3589_);
lean_dec_ref_known(v___x_3588_, 1);
if (lean_obj_tag(v_a_3589_) == 1)
{
lean_object* v_val_3590_; lean_object* v___x_3592_; uint8_t v_isShared_3593_; uint8_t v_isSharedCheck_3634_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_config_3027_);
v_val_3590_ = lean_ctor_get(v_a_3589_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v_a_3589_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3592_ = v_a_3589_;
v_isShared_3593_ = v_isSharedCheck_3634_;
goto v_resetjp_3591_;
}
else
{
lean_inc(v_val_3590_);
lean_dec(v_a_3589_);
v___x_3592_ = lean_box(0);
v_isShared_3593_ = v_isSharedCheck_3634_;
goto v_resetjp_3591_;
}
v_resetjp_3591_:
{
lean_object* v___x_3594_; 
lean_inc(v_mvarId_3028_);
v___x_3594_ = l_Lean_MVarId_getType(v_mvarId_3028_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
if (lean_obj_tag(v___x_3594_) == 0)
{
lean_object* v_a_3595_; lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; 
v_a_3595_ = lean_ctor_get(v___x_3594_, 0);
lean_inc(v_a_3595_);
lean_dec_ref_known(v___x_3594_, 1);
v___x_3596_ = l_Lean_LocalDecl_toExpr(v_val_3059_);
v___x_3597_ = l_Lean_mkFVar(v_val_3590_);
v___x_3598_ = l_Lean_Expr_app___override(v___x_3596_, v___x_3597_);
v___x_3599_ = l_Lean_Meta_mkFalseElim(v_a_3595_, v___x_3598_, v___y_3033_, v___y_3034_, v___y_3035_, v___y_3036_);
if (lean_obj_tag(v___x_3599_) == 0)
{
lean_object* v_a_3600_; lean_object* v___x_3601_; 
v_a_3600_ = lean_ctor_get(v___x_3599_, 0);
lean_inc(v_a_3600_);
lean_dec_ref_known(v___x_3599_, 1);
v___x_3601_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3028_, v_a_3600_, v___y_3034_);
if (lean_obj_tag(v___x_3601_) == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3604_; 
lean_dec_ref_known(v___x_3601_, 1);
v___x_3602_ = lean_box(v___x_3038_);
if (v_isShared_3593_ == 0)
{
lean_ctor_set(v___x_3592_, 0, v___x_3602_);
v___x_3604_ = v___x_3592_;
goto v_reusejp_3603_;
}
else
{
lean_object* v_reuseFailAlloc_3609_; 
v_reuseFailAlloc_3609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3602_);
v___x_3604_ = v_reuseFailAlloc_3609_;
goto v_reusejp_3603_;
}
v_reusejp_3603_:
{
lean_object* v___x_3605_; lean_object* v___x_3607_; 
v___x_3605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3605_, 0, v___x_3604_);
lean_ctor_set(v___x_3605_, 1, v___x_3063_);
if (v_isShared_3587_ == 0)
{
lean_ctor_set_tag(v___x_3586_, 0);
lean_ctor_set(v___x_3586_, 0, v___x_3605_);
v___x_3607_ = v___x_3586_;
goto v_reusejp_3606_;
}
else
{
lean_object* v_reuseFailAlloc_3608_; 
v_reuseFailAlloc_3608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3608_, 0, v___x_3605_);
v___x_3607_ = v_reuseFailAlloc_3608_;
goto v_reusejp_3606_;
}
v_reusejp_3606_:
{
v_a_3045_ = v___x_3607_;
goto v___jp_3044_;
}
}
}
else
{
lean_object* v_a_3610_; lean_object* v___x_3612_; uint8_t v_isShared_3613_; uint8_t v_isSharedCheck_3617_; 
lean_del_object(v___x_3592_);
lean_del_object(v___x_3586_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
v_a_3610_ = lean_ctor_get(v___x_3601_, 0);
v_isSharedCheck_3617_ = !lean_is_exclusive(v___x_3601_);
if (v_isSharedCheck_3617_ == 0)
{
v___x_3612_ = v___x_3601_;
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
else
{
lean_inc(v_a_3610_);
lean_dec(v___x_3601_);
v___x_3612_ = lean_box(0);
v_isShared_3613_ = v_isSharedCheck_3617_;
goto v_resetjp_3611_;
}
v_resetjp_3611_:
{
lean_object* v___x_3615_; 
if (v_isShared_3613_ == 0)
{
v___x_3615_ = v___x_3612_;
goto v_reusejp_3614_;
}
else
{
lean_object* v_reuseFailAlloc_3616_; 
v_reuseFailAlloc_3616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3616_, 0, v_a_3610_);
v___x_3615_ = v_reuseFailAlloc_3616_;
goto v_reusejp_3614_;
}
v_reusejp_3614_:
{
return v___x_3615_;
}
}
}
}
else
{
lean_object* v_a_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3625_; 
lean_del_object(v___x_3592_);
lean_del_object(v___x_3586_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3618_ = lean_ctor_get(v___x_3599_, 0);
v_isSharedCheck_3625_ = !lean_is_exclusive(v___x_3599_);
if (v_isSharedCheck_3625_ == 0)
{
v___x_3620_ = v___x_3599_;
v_isShared_3621_ = v_isSharedCheck_3625_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_a_3618_);
lean_dec(v___x_3599_);
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
else
{
lean_object* v_a_3626_; lean_object* v___x_3628_; uint8_t v_isShared_3629_; uint8_t v_isSharedCheck_3633_; 
lean_del_object(v___x_3592_);
lean_dec(v_val_3590_);
lean_del_object(v___x_3586_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3626_ = lean_ctor_get(v___x_3594_, 0);
v_isSharedCheck_3633_ = !lean_is_exclusive(v___x_3594_);
if (v_isSharedCheck_3633_ == 0)
{
v___x_3628_ = v___x_3594_;
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
else
{
lean_inc(v_a_3626_);
lean_dec(v___x_3594_);
v___x_3628_ = lean_box(0);
v_isShared_3629_ = v_isSharedCheck_3633_;
goto v_resetjp_3627_;
}
v_resetjp_3627_:
{
lean_object* v___x_3631_; 
if (v_isShared_3629_ == 0)
{
v___x_3631_ = v___x_3628_;
goto v_reusejp_3630_;
}
else
{
lean_object* v_reuseFailAlloc_3632_; 
v_reuseFailAlloc_3632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3632_, 0, v_a_3626_);
v___x_3631_ = v_reuseFailAlloc_3632_;
goto v_reusejp_3630_;
}
v_reusejp_3630_:
{
return v___x_3631_;
}
}
}
}
}
else
{
lean_dec(v_a_3589_);
lean_del_object(v___x_3586_);
v___y_3446_ = v___y_3033_;
v___y_3447_ = v___y_3034_;
v___y_3448_ = v___y_3035_;
v___y_3449_ = v___y_3036_;
goto v___jp_3445_;
}
}
else
{
lean_object* v_a_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3642_; 
lean_del_object(v___x_3586_);
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3635_ = lean_ctor_get(v___x_3588_, 0);
v_isSharedCheck_3642_ = !lean_is_exclusive(v___x_3588_);
if (v_isSharedCheck_3642_ == 0)
{
v___x_3637_ = v___x_3588_;
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_a_3635_);
lean_dec(v___x_3588_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3642_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3640_; 
if (v_isShared_3638_ == 0)
{
v___x_3640_ = v___x_3637_;
goto v_reusejp_3639_;
}
else
{
lean_object* v_reuseFailAlloc_3641_; 
v_reuseFailAlloc_3641_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3641_, 0, v_a_3635_);
v___x_3640_ = v_reuseFailAlloc_3641_;
goto v_reusejp_3639_;
}
v_reusejp_3639_:
{
return v___x_3640_;
}
}
}
}
}
else
{
lean_dec(v_a_3583_);
v___y_3446_ = v___y_3033_;
v___y_3447_ = v___y_3034_;
v___y_3448_ = v___y_3035_;
v___y_3449_ = v___y_3036_;
goto v___jp_3445_;
}
}
else
{
lean_object* v_a_3644_; lean_object* v___x_3646_; uint8_t v_isShared_3647_; uint8_t v_isSharedCheck_3651_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3644_ = lean_ctor_get(v___x_3582_, 0);
v_isSharedCheck_3651_ = !lean_is_exclusive(v___x_3582_);
if (v_isSharedCheck_3651_ == 0)
{
v___x_3646_ = v___x_3582_;
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
else
{
lean_inc(v_a_3644_);
lean_dec(v___x_3582_);
v___x_3646_ = lean_box(0);
v_isShared_3647_ = v_isSharedCheck_3651_;
goto v_resetjp_3645_;
}
v_resetjp_3645_:
{
lean_object* v___x_3649_; 
if (v_isShared_3647_ == 0)
{
v___x_3649_ = v___x_3646_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3650_; 
v_reuseFailAlloc_3650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_a_3644_);
v___x_3649_ = v_reuseFailAlloc_3650_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
return v___x_3649_;
}
}
}
v___jp_3094_:
{
uint8_t v_genDiseq_3101_; 
v_genDiseq_3101_ = lean_ctor_get_uint8(v_config_3027_, sizeof(void*)*1 + 2);
if (v_genDiseq_3101_ == 0)
{
lean_dec_ref(v___x_3093_);
v___y_3066_ = v___y_3095_;
v___y_3067_ = v___y_3096_;
v___y_3068_ = v___y_3097_;
v___y_3069_ = v___y_3098_;
v___y_3070_ = v___y_3099_;
v___y_3071_ = v___y_3100_;
goto v___jp_3065_;
}
else
{
uint8_t v___x_3102_; 
v___x_3102_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3093_);
if (v___x_3102_ == 0)
{
v___y_3066_ = v___y_3095_;
v___y_3067_ = v___y_3096_;
v___y_3068_ = v___y_3097_;
v___y_3069_ = v___y_3098_;
v___y_3070_ = v___y_3099_;
v___y_3071_ = v___y_3100_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3103_; 
lean_inc(v_val_3059_);
lean_inc(v_mvarId_3028_);
v___x_3103_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3028_, v_val_3059_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; uint8_t v___x_3105_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3105_ = lean_unbox(v_a_3104_);
lean_dec(v_a_3104_);
if (v___x_3105_ == 0)
{
v___y_3066_ = v___y_3095_;
v___y_3067_ = v___y_3096_;
v___y_3068_ = v___y_3097_;
v___y_3069_ = v___y_3098_;
v___y_3070_ = v___y_3099_;
v___y_3071_ = v___y_3100_;
goto v___jp_3065_;
}
else
{
lean_object* v___x_3106_; lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; 
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v___x_3106_ = lean_box(v___x_3038_);
v___x_3107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3107_, 0, v___x_3106_);
v___x_3108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
lean_ctor_set(v___x_3108_, 1, v___x_3063_);
v___x_3109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
v_a_3045_ = v___x_3109_;
goto v___jp_3044_;
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3110_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3103_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3103_);
v___x_3112_ = lean_box(0);
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
v_resetjp_3111_:
{
lean_object* v___x_3115_; 
if (v_isShared_3113_ == 0)
{
v___x_3115_ = v___x_3112_;
goto v_reusejp_3114_;
}
else
{
lean_object* v_reuseFailAlloc_3116_; 
v_reuseFailAlloc_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_a_3110_);
v___x_3115_ = v_reuseFailAlloc_3116_;
goto v_reusejp_3114_;
}
v_reusejp_3114_:
{
return v___x_3115_;
}
}
}
}
}
}
v___jp_3118_:
{
uint8_t v___x_3126_; 
v___x_3126_ = l_Lean_Exception_isInterrupt(v_a_3125_);
if (v___x_3126_ == 0)
{
uint8_t v___x_3127_; 
lean_inc_ref(v_a_3125_);
v___x_3127_ = l_Lean_Exception_isRuntime(v_a_3125_);
if (v___x_3127_ == 0)
{
lean_dec_ref(v_a_3125_);
v___y_3095_ = v___y_3122_;
v___y_3096_ = v___y_3123_;
v___y_3097_ = v___y_3121_;
v___y_3098_ = v___y_3124_;
v___y_3099_ = v___y_3120_;
v___y_3100_ = v___y_3119_;
goto v___jp_3094_;
}
else
{
lean_object* v___x_3128_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v___x_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3128_, 0, v_a_3125_);
return v___x_3128_;
}
}
else
{
lean_object* v___x_3129_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v_a_3125_);
return v___x_3129_;
}
}
v___jp_3130_:
{
if (lean_obj_tag(v___y_3138_) == 0)
{
lean_object* v_a_3139_; lean_object* v___x_3140_; uint8_t v___x_3141_; 
v_a_3139_ = lean_ctor_get(v___y_3138_, 0);
lean_inc(v_a_3139_);
lean_dec_ref_known(v___y_3138_, 1);
v___x_3140_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3141_ = l_Lean_Expr_isConstOf(v_a_3139_, v___x_3140_);
lean_dec(v_a_3139_);
if (v___x_3141_ == 0)
{
lean_dec_ref(v___y_3131_);
v___y_3095_ = v___y_3135_;
v___y_3096_ = v___y_3136_;
v___y_3097_ = v___y_3134_;
v___y_3098_ = v___y_3137_;
v___y_3099_ = v___y_3133_;
v___y_3100_ = v___y_3132_;
goto v___jp_3094_;
}
else
{
lean_object* v___x_3142_; 
lean_inc_ref(v___y_3131_);
v___x_3142_ = l_Lean_Meta_mkEqRefl(v___y_3131_, v___y_3134_, v___y_3137_, v___y_3133_, v___y_3132_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3144_; lean_object* v_dummy_3145_; lean_object* v_nargs_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3143_);
lean_dec_ref_known(v___x_3142_, 1);
v___x_3144_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3146_ = l_Lean_Expr_getAppNumArgs(v___y_3131_);
lean_inc(v_nargs_3146_);
v___x_3147_ = lean_mk_array(v_nargs_3146_, v_dummy_3145_);
v___x_3148_ = lean_unsigned_to_nat(1u);
v___x_3149_ = lean_nat_sub(v_nargs_3146_, v___x_3148_);
lean_dec(v_nargs_3146_);
v___x_3150_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3131_, v___x_3147_, v___x_3149_);
v___x_3151_ = lean_array_push(v___x_3150_, v_a_3143_);
v___x_3152_ = l_Lean_mkAppN(v___x_3144_, v___x_3151_);
lean_dec_ref(v___x_3151_);
lean_inc(v_mvarId_3028_);
v___x_3153_ = l_Lean_MVarId_getType(v_mvarId_3028_, v___y_3134_, v___y_3137_, v___y_3133_, v___y_3132_);
if (lean_obj_tag(v___x_3153_) == 0)
{
lean_object* v_a_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v_a_3154_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3154_);
lean_dec_ref_known(v___x_3153_, 1);
lean_inc(v_val_3059_);
v___x_3155_ = l_Lean_LocalDecl_toExpr(v_val_3059_);
v___x_3156_ = l_Lean_Meta_mkAbsurd(v_a_3154_, v___x_3155_, v___x_3152_, v___y_3134_, v___y_3137_, v___y_3133_, v___y_3132_);
if (lean_obj_tag(v___x_3156_) == 0)
{
lean_object* v_a_3157_; lean_object* v___x_3159_; uint8_t v_isShared_3160_; uint8_t v_isSharedCheck_3176_; 
v_a_3157_ = lean_ctor_get(v___x_3156_, 0);
v_isSharedCheck_3176_ = !lean_is_exclusive(v___x_3156_);
if (v_isSharedCheck_3176_ == 0)
{
v___x_3159_ = v___x_3156_;
v_isShared_3160_ = v_isSharedCheck_3176_;
goto v_resetjp_3158_;
}
else
{
lean_inc(v_a_3157_);
lean_dec(v___x_3156_);
v___x_3159_ = lean_box(0);
v_isShared_3160_ = v_isSharedCheck_3176_;
goto v_resetjp_3158_;
}
v_resetjp_3158_:
{
lean_object* v___x_3161_; 
lean_inc(v_mvarId_3028_);
v___x_3161_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3028_, v_a_3157_, v___y_3137_);
if (lean_obj_tag(v___x_3161_) == 0)
{
lean_object* v___x_3163_; uint8_t v_isShared_3164_; uint8_t v_isSharedCheck_3173_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_isSharedCheck_3173_ = !lean_is_exclusive(v___x_3161_);
if (v_isSharedCheck_3173_ == 0)
{
lean_object* v_unused_3174_; 
v_unused_3174_ = lean_ctor_get(v___x_3161_, 0);
lean_dec(v_unused_3174_);
v___x_3163_ = v___x_3161_;
v_isShared_3164_ = v_isSharedCheck_3173_;
goto v_resetjp_3162_;
}
else
{
lean_dec(v___x_3161_);
v___x_3163_ = lean_box(0);
v_isShared_3164_ = v_isSharedCheck_3173_;
goto v_resetjp_3162_;
}
v_resetjp_3162_:
{
lean_object* v___x_3165_; lean_object* v___x_3167_; 
v___x_3165_ = lean_box(v___x_3038_);
if (v_isShared_3164_ == 0)
{
lean_ctor_set_tag(v___x_3163_, 1);
lean_ctor_set(v___x_3163_, 0, v___x_3165_);
v___x_3167_ = v___x_3163_;
goto v_reusejp_3166_;
}
else
{
lean_object* v_reuseFailAlloc_3172_; 
v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3172_, 0, v___x_3165_);
v___x_3167_ = v_reuseFailAlloc_3172_;
goto v_reusejp_3166_;
}
v_reusejp_3166_:
{
lean_object* v___x_3168_; lean_object* v___x_3170_; 
v___x_3168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3167_);
lean_ctor_set(v___x_3168_, 1, v___x_3063_);
if (v_isShared_3160_ == 0)
{
lean_ctor_set(v___x_3159_, 0, v___x_3168_);
v___x_3170_ = v___x_3159_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v___x_3168_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
v_a_3045_ = v___x_3170_;
goto v___jp_3044_;
}
}
}
}
else
{
lean_object* v_a_3175_; 
lean_del_object(v___x_3159_);
v_a_3175_ = lean_ctor_get(v___x_3161_, 0);
lean_inc(v_a_3175_);
lean_dec_ref_known(v___x_3161_, 1);
v___y_3119_ = v___y_3132_;
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3134_;
v___y_3122_ = v___y_3135_;
v___y_3123_ = v___y_3136_;
v___y_3124_ = v___y_3137_;
v_a_3125_ = v_a_3175_;
goto v___jp_3118_;
}
}
}
else
{
lean_object* v_a_3177_; 
v_a_3177_ = lean_ctor_get(v___x_3156_, 0);
lean_inc(v_a_3177_);
lean_dec_ref_known(v___x_3156_, 1);
v___y_3119_ = v___y_3132_;
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3134_;
v___y_3122_ = v___y_3135_;
v___y_3123_ = v___y_3136_;
v___y_3124_ = v___y_3137_;
v_a_3125_ = v_a_3177_;
goto v___jp_3118_;
}
}
else
{
lean_object* v_a_3178_; 
lean_dec_ref(v___x_3152_);
v_a_3178_ = lean_ctor_get(v___x_3153_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3153_, 1);
v___y_3119_ = v___y_3132_;
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3134_;
v___y_3122_ = v___y_3135_;
v___y_3123_ = v___y_3136_;
v___y_3124_ = v___y_3137_;
v_a_3125_ = v_a_3178_;
goto v___jp_3118_;
}
}
else
{
lean_object* v_a_3179_; 
lean_dec_ref(v___y_3131_);
v_a_3179_ = lean_ctor_get(v___x_3142_, 0);
lean_inc(v_a_3179_);
lean_dec_ref_known(v___x_3142_, 1);
v___y_3119_ = v___y_3132_;
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3134_;
v___y_3122_ = v___y_3135_;
v___y_3123_ = v___y_3136_;
v___y_3124_ = v___y_3137_;
v_a_3125_ = v_a_3179_;
goto v___jp_3118_;
}
}
}
else
{
lean_object* v_a_3180_; 
lean_dec_ref(v___y_3131_);
v_a_3180_ = lean_ctor_get(v___y_3138_, 0);
lean_inc(v_a_3180_);
lean_dec_ref_known(v___y_3138_, 1);
v___y_3119_ = v___y_3132_;
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3134_;
v___y_3122_ = v___y_3135_;
v___y_3123_ = v___y_3136_;
v___y_3124_ = v___y_3137_;
v_a_3125_ = v_a_3180_;
goto v___jp_3118_;
}
}
v___jp_3181_:
{
uint8_t v_useDecide_3188_; 
v_useDecide_3188_ = lean_ctor_get_uint8(v_config_3027_, sizeof(void*)*1);
if (v_useDecide_3188_ == 0)
{
v___y_3095_ = v___y_3182_;
v___y_3096_ = v_isHEq_3183_;
v___y_3097_ = v___y_3184_;
v___y_3098_ = v___y_3185_;
v___y_3099_ = v___y_3186_;
v___y_3100_ = v___y_3187_;
goto v___jp_3094_;
}
else
{
uint8_t v___x_3189_; 
v___x_3189_ = l_Lean_Expr_hasFVar(v___x_3093_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; 
lean_inc_ref(v___x_3093_);
v___x_3190_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3093_, v___y_3185_);
if (lean_obj_tag(v___x_3190_) == 0)
{
lean_object* v_a_3191_; uint8_t v___x_3192_; 
v_a_3191_ = lean_ctor_get(v___x_3190_, 0);
lean_inc(v_a_3191_);
lean_dec_ref_known(v___x_3190_, 1);
v___x_3192_ = l_Lean_Expr_hasMVar(v_a_3191_);
if (v___x_3192_ == 0)
{
uint8_t v___x_3193_; 
v___x_3193_ = l_Lean_Expr_hasFVar(v_a_3191_);
lean_dec(v_a_3191_);
if (v___x_3193_ == 0)
{
lean_object* v___x_3194_; 
lean_inc_ref(v___x_3093_);
v___x_3194_ = l_Lean_Meta_mkDecide(v___x_3093_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
if (lean_obj_tag(v___x_3194_) == 0)
{
lean_object* v_a_3195_; lean_object* v___x_3196_; uint8_t v_transparency_3197_; uint8_t v___x_3198_; uint8_t v___x_3199_; 
v_a_3195_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3195_);
lean_dec_ref_known(v___x_3194_, 1);
v___x_3196_ = l_Lean_Meta_Context_config(v___y_3184_);
v_transparency_3197_ = lean_ctor_get_uint8(v___x_3196_, 9);
lean_dec_ref(v___x_3196_);
v___x_3198_ = 1;
v___x_3199_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3197_, v___x_3198_);
if (v___x_3199_ == 0)
{
lean_object* v_keyedConfig_3200_; uint8_t v_trackZetaDelta_3201_; lean_object* v_zetaDeltaSet_3202_; lean_object* v_lctx_3203_; lean_object* v_localInstances_3204_; lean_object* v_defEqCtx_x3f_3205_; lean_object* v_synthPendingDepth_3206_; lean_object* v_customCanUnfoldPredicate_x3f_3207_; uint8_t v_univApprox_3208_; uint8_t v_inTypeClassResolution_3209_; uint8_t v_cacheInferType_3210_; lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v_keyedConfig_3200_ = lean_ctor_get(v___y_3184_, 0);
v_trackZetaDelta_3201_ = lean_ctor_get_uint8(v___y_3184_, sizeof(void*)*7);
v_zetaDeltaSet_3202_ = lean_ctor_get(v___y_3184_, 1);
v_lctx_3203_ = lean_ctor_get(v___y_3184_, 2);
v_localInstances_3204_ = lean_ctor_get(v___y_3184_, 3);
v_defEqCtx_x3f_3205_ = lean_ctor_get(v___y_3184_, 4);
v_synthPendingDepth_3206_ = lean_ctor_get(v___y_3184_, 5);
v_customCanUnfoldPredicate_x3f_3207_ = lean_ctor_get(v___y_3184_, 6);
v_univApprox_3208_ = lean_ctor_get_uint8(v___y_3184_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3209_ = lean_ctor_get_uint8(v___y_3184_, sizeof(void*)*7 + 2);
v_cacheInferType_3210_ = lean_ctor_get_uint8(v___y_3184_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3200_);
v___x_3211_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3198_, v_keyedConfig_3200_);
lean_inc(v_customCanUnfoldPredicate_x3f_3207_);
lean_inc(v_synthPendingDepth_3206_);
lean_inc(v_defEqCtx_x3f_3205_);
lean_inc_ref(v_localInstances_3204_);
lean_inc_ref(v_lctx_3203_);
lean_inc(v_zetaDeltaSet_3202_);
v___x_3212_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3212_, 0, v___x_3211_);
lean_ctor_set(v___x_3212_, 1, v_zetaDeltaSet_3202_);
lean_ctor_set(v___x_3212_, 2, v_lctx_3203_);
lean_ctor_set(v___x_3212_, 3, v_localInstances_3204_);
lean_ctor_set(v___x_3212_, 4, v_defEqCtx_x3f_3205_);
lean_ctor_set(v___x_3212_, 5, v_synthPendingDepth_3206_);
lean_ctor_set(v___x_3212_, 6, v_customCanUnfoldPredicate_x3f_3207_);
lean_ctor_set_uint8(v___x_3212_, sizeof(void*)*7, v_trackZetaDelta_3201_);
lean_ctor_set_uint8(v___x_3212_, sizeof(void*)*7 + 1, v_univApprox_3208_);
lean_ctor_set_uint8(v___x_3212_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3209_);
lean_ctor_set_uint8(v___x_3212_, sizeof(void*)*7 + 3, v_cacheInferType_3210_);
lean_inc(v___y_3187_);
lean_inc_ref(v___y_3186_);
lean_inc(v___y_3185_);
lean_inc(v_a_3195_);
v___x_3213_ = lean_whnf(v_a_3195_, v___x_3212_, v___y_3185_, v___y_3186_, v___y_3187_);
v___y_3131_ = v_a_3195_;
v___y_3132_ = v___y_3187_;
v___y_3133_ = v___y_3186_;
v___y_3134_ = v___y_3184_;
v___y_3135_ = v___y_3182_;
v___y_3136_ = v_isHEq_3183_;
v___y_3137_ = v___y_3185_;
v___y_3138_ = v___x_3213_;
goto v___jp_3130_;
}
else
{
lean_object* v___x_3214_; 
lean_inc(v___y_3187_);
lean_inc_ref(v___y_3186_);
lean_inc(v___y_3185_);
lean_inc_ref(v___y_3184_);
lean_inc(v_a_3195_);
v___x_3214_ = lean_whnf(v_a_3195_, v___y_3184_, v___y_3185_, v___y_3186_, v___y_3187_);
v___y_3131_ = v_a_3195_;
v___y_3132_ = v___y_3187_;
v___y_3133_ = v___y_3186_;
v___y_3134_ = v___y_3184_;
v___y_3135_ = v___y_3182_;
v___y_3136_ = v_isHEq_3183_;
v___y_3137_ = v___y_3185_;
v___y_3138_ = v___x_3214_;
goto v___jp_3130_;
}
}
else
{
lean_object* v_a_3215_; 
v_a_3215_ = lean_ctor_get(v___x_3194_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___x_3194_, 1);
v___y_3119_ = v___y_3187_;
v___y_3120_ = v___y_3186_;
v___y_3121_ = v___y_3184_;
v___y_3122_ = v___y_3182_;
v___y_3123_ = v_isHEq_3183_;
v___y_3124_ = v___y_3185_;
v_a_3125_ = v_a_3215_;
goto v___jp_3118_;
}
}
else
{
v___y_3095_ = v___y_3182_;
v___y_3096_ = v_isHEq_3183_;
v___y_3097_ = v___y_3184_;
v___y_3098_ = v___y_3185_;
v___y_3099_ = v___y_3186_;
v___y_3100_ = v___y_3187_;
goto v___jp_3094_;
}
}
else
{
lean_dec(v_a_3191_);
v___y_3095_ = v___y_3182_;
v___y_3096_ = v_isHEq_3183_;
v___y_3097_ = v___y_3184_;
v___y_3098_ = v___y_3185_;
v___y_3099_ = v___y_3186_;
v___y_3100_ = v___y_3187_;
goto v___jp_3094_;
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3216_ = lean_ctor_get(v___x_3190_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3190_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3190_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3190_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
else
{
v___y_3095_ = v___y_3182_;
v___y_3096_ = v_isHEq_3183_;
v___y_3097_ = v___y_3184_;
v___y_3098_ = v___y_3185_;
v___y_3099_ = v___y_3186_;
v___y_3100_ = v___y_3187_;
goto v___jp_3094_;
}
}
}
v___jp_3224_:
{
lean_object* v___x_3230_; 
lean_inc_ref(v___x_3093_);
v___x_3230_ = l_Lean_Meta_matchHEq_x3f(v___x_3093_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3230_) == 0)
{
lean_object* v_a_3231_; 
v_a_3231_ = lean_ctor_get(v___x_3230_, 0);
lean_inc(v_a_3231_);
lean_dec_ref_known(v___x_3230_, 1);
if (lean_obj_tag(v_a_3231_) == 1)
{
lean_object* v_val_3232_; lean_object* v_snd_3233_; lean_object* v_snd_3234_; lean_object* v_fst_3235_; lean_object* v_fst_3236_; lean_object* v_fst_3237_; lean_object* v_snd_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3338_; 
v_val_3232_ = lean_ctor_get(v_a_3231_, 0);
lean_inc(v_val_3232_);
lean_dec_ref_known(v_a_3231_, 1);
v_snd_3233_ = lean_ctor_get(v_val_3232_, 1);
lean_inc(v_snd_3233_);
v_snd_3234_ = lean_ctor_get(v_snd_3233_, 1);
lean_inc(v_snd_3234_);
v_fst_3235_ = lean_ctor_get(v_val_3232_, 0);
lean_inc(v_fst_3235_);
lean_dec(v_val_3232_);
v_fst_3236_ = lean_ctor_get(v_snd_3233_, 0);
lean_inc(v_fst_3236_);
lean_dec(v_snd_3233_);
v_fst_3237_ = lean_ctor_get(v_snd_3234_, 0);
v_snd_3238_ = lean_ctor_get(v_snd_3234_, 1);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_snd_3234_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3240_ = v_snd_3234_;
v_isShared_3241_ = v_isSharedCheck_3338_;
goto v_resetjp_3239_;
}
else
{
lean_inc(v_snd_3238_);
lean_inc(v_fst_3237_);
lean_dec(v_snd_3234_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3338_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3236_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v_a_3243_; 
v_a_3243_ = lean_ctor_get(v___x_3242_, 0);
lean_inc(v_a_3243_);
lean_dec_ref_known(v___x_3242_, 1);
if (lean_obj_tag(v_a_3243_) == 1)
{
lean_object* v_val_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3329_; 
v_val_3244_ = lean_ctor_get(v_a_3243_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v_a_3243_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3246_ = v_a_3243_;
v_isShared_3247_ = v_isSharedCheck_3329_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_val_3244_);
lean_dec(v_a_3243_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3329_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3248_; 
v___x_3248_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3238_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3248_) == 0)
{
lean_object* v_a_3249_; 
v_a_3249_ = lean_ctor_get(v___x_3248_, 0);
lean_inc(v_a_3249_);
lean_dec_ref_known(v___x_3248_, 1);
if (lean_obj_tag(v_a_3249_) == 1)
{
lean_object* v_toConstantVal_3250_; lean_object* v_val_3251_; lean_object* v___x_3253_; uint8_t v_isShared_3254_; uint8_t v_isSharedCheck_3320_; 
v_toConstantVal_3250_ = lean_ctor_get(v_val_3244_, 0);
lean_inc_ref(v_toConstantVal_3250_);
lean_dec(v_val_3244_);
v_val_3251_ = lean_ctor_get(v_a_3249_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v_a_3249_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3253_ = v_a_3249_;
v_isShared_3254_ = v_isSharedCheck_3320_;
goto v_resetjp_3252_;
}
else
{
lean_inc(v_val_3251_);
lean_dec(v_a_3249_);
v___x_3253_ = lean_box(0);
v_isShared_3254_ = v_isSharedCheck_3320_;
goto v_resetjp_3252_;
}
v_resetjp_3252_:
{
lean_object* v_toConstantVal_3255_; lean_object* v_name_3256_; lean_object* v_name_3257_; uint8_t v___x_3258_; 
v_toConstantVal_3255_ = lean_ctor_get(v_val_3251_, 0);
lean_inc_ref(v_toConstantVal_3255_);
lean_dec(v_val_3251_);
v_name_3256_ = lean_ctor_get(v_toConstantVal_3250_, 0);
lean_inc(v_name_3256_);
lean_dec_ref(v_toConstantVal_3250_);
v_name_3257_ = lean_ctor_get(v_toConstantVal_3255_, 0);
lean_inc(v_name_3257_);
lean_dec_ref(v_toConstantVal_3255_);
v___x_3258_ = lean_name_eq(v_name_3256_, v_name_3257_);
lean_dec(v_name_3257_);
lean_dec(v_name_3256_);
if (v___x_3258_ == 0)
{
lean_object* v___x_3259_; 
v___x_3259_ = l_Lean_Meta_isExprDefEq(v_fst_3235_, v_fst_3237_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3259_) == 0)
{
lean_object* v_a_3260_; uint8_t v___x_3261_; 
v_a_3260_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_a_3260_);
lean_dec_ref_known(v___x_3259_, 1);
v___x_3261_ = lean_unbox(v_a_3260_);
lean_dec(v_a_3260_);
if (v___x_3261_ == 0)
{
lean_del_object(v___x_3253_);
lean_del_object(v___x_3246_);
lean_del_object(v___x_3240_);
v___y_3182_ = v_isEq_3225_;
v_isHEq_3183_ = v___x_3038_;
v___y_3184_ = v___y_3226_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v___y_3228_;
v___y_3187_ = v___y_3229_;
goto v___jp_3181_;
}
else
{
lean_object* v___x_3262_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_config_3027_);
lean_inc(v_mvarId_3028_);
v___x_3262_ = l_Lean_MVarId_getType(v_mvarId_3028_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3262_) == 0)
{
lean_object* v_a_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
v_a_3263_ = lean_ctor_get(v___x_3262_, 0);
lean_inc(v_a_3263_);
lean_dec_ref_known(v___x_3262_, 1);
v___x_3264_ = l_Lean_LocalDecl_toExpr(v_val_3059_);
v___x_3265_ = l_Lean_Meta_mkEqOfHEq(v___x_3264_, v___x_3038_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3265_) == 0)
{
lean_object* v_a_3266_; lean_object* v___x_3267_; 
v_a_3266_ = lean_ctor_get(v___x_3265_, 0);
lean_inc(v_a_3266_);
lean_dec_ref_known(v___x_3265_, 1);
v___x_3267_ = l_Lean_Meta_mkNoConfusion(v_a_3263_, v_a_3266_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v_a_3268_; lean_object* v___x_3269_; 
v_a_3268_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_a_3268_);
lean_dec_ref_known(v___x_3267_, 1);
v___x_3269_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3028_, v_a_3268_, v___y_3227_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3272_; 
lean_dec_ref_known(v___x_3269_, 1);
v___x_3270_ = lean_box(v___x_3038_);
if (v_isShared_3254_ == 0)
{
lean_ctor_set(v___x_3253_, 0, v___x_3270_);
v___x_3272_ = v___x_3253_;
goto v_reusejp_3271_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3270_);
v___x_3272_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3271_;
}
v_reusejp_3271_:
{
lean_object* v___x_3274_; 
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 1, v___x_3063_);
lean_ctor_set(v___x_3240_, 0, v___x_3272_);
v___x_3274_ = v___x_3240_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v___x_3063_);
v___x_3274_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3276_; 
if (v_isShared_3247_ == 0)
{
lean_ctor_set_tag(v___x_3246_, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3274_);
v___x_3276_ = v___x_3246_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3277_; 
v_reuseFailAlloc_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3277_, 0, v___x_3274_);
v___x_3276_ = v_reuseFailAlloc_3277_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
v_a_3045_ = v___x_3276_;
goto v___jp_3044_;
}
}
}
}
else
{
lean_object* v_a_3280_; lean_object* v___x_3282_; uint8_t v_isShared_3283_; uint8_t v_isSharedCheck_3287_; 
lean_del_object(v___x_3253_);
lean_del_object(v___x_3246_);
lean_del_object(v___x_3240_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
v_a_3280_ = lean_ctor_get(v___x_3269_, 0);
v_isSharedCheck_3287_ = !lean_is_exclusive(v___x_3269_);
if (v_isSharedCheck_3287_ == 0)
{
v___x_3282_ = v___x_3269_;
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
else
{
lean_inc(v_a_3280_);
lean_dec(v___x_3269_);
v___x_3282_ = lean_box(0);
v_isShared_3283_ = v_isSharedCheck_3287_;
goto v_resetjp_3281_;
}
v_resetjp_3281_:
{
lean_object* v___x_3285_; 
if (v_isShared_3283_ == 0)
{
v___x_3285_ = v___x_3282_;
goto v_reusejp_3284_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_a_3280_);
v___x_3285_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3284_;
}
v_reusejp_3284_:
{
return v___x_3285_;
}
}
}
}
else
{
lean_object* v_a_3288_; lean_object* v___x_3290_; uint8_t v_isShared_3291_; uint8_t v_isSharedCheck_3295_; 
lean_del_object(v___x_3253_);
lean_del_object(v___x_3246_);
lean_del_object(v___x_3240_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3288_ = lean_ctor_get(v___x_3267_, 0);
v_isSharedCheck_3295_ = !lean_is_exclusive(v___x_3267_);
if (v_isSharedCheck_3295_ == 0)
{
v___x_3290_ = v___x_3267_;
v_isShared_3291_ = v_isSharedCheck_3295_;
goto v_resetjp_3289_;
}
else
{
lean_inc(v_a_3288_);
lean_dec(v___x_3267_);
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
else
{
lean_object* v_a_3296_; lean_object* v___x_3298_; uint8_t v_isShared_3299_; uint8_t v_isSharedCheck_3303_; 
lean_dec(v_a_3263_);
lean_del_object(v___x_3253_);
lean_del_object(v___x_3246_);
lean_del_object(v___x_3240_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3296_ = lean_ctor_get(v___x_3265_, 0);
v_isSharedCheck_3303_ = !lean_is_exclusive(v___x_3265_);
if (v_isSharedCheck_3303_ == 0)
{
v___x_3298_ = v___x_3265_;
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
else
{
lean_inc(v_a_3296_);
lean_dec(v___x_3265_);
v___x_3298_ = lean_box(0);
v_isShared_3299_ = v_isSharedCheck_3303_;
goto v_resetjp_3297_;
}
v_resetjp_3297_:
{
lean_object* v___x_3301_; 
if (v_isShared_3299_ == 0)
{
v___x_3301_ = v___x_3298_;
goto v_reusejp_3300_;
}
else
{
lean_object* v_reuseFailAlloc_3302_; 
v_reuseFailAlloc_3302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3302_, 0, v_a_3296_);
v___x_3301_ = v_reuseFailAlloc_3302_;
goto v_reusejp_3300_;
}
v_reusejp_3300_:
{
return v___x_3301_;
}
}
}
}
else
{
lean_object* v_a_3304_; lean_object* v___x_3306_; uint8_t v_isShared_3307_; uint8_t v_isSharedCheck_3311_; 
lean_del_object(v___x_3253_);
lean_del_object(v___x_3246_);
lean_del_object(v___x_3240_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3304_ = lean_ctor_get(v___x_3262_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3262_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3306_ = v___x_3262_;
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
else
{
lean_inc(v_a_3304_);
lean_dec(v___x_3262_);
v___x_3306_ = lean_box(0);
v_isShared_3307_ = v_isSharedCheck_3311_;
goto v_resetjp_3305_;
}
v_resetjp_3305_:
{
lean_object* v___x_3309_; 
if (v_isShared_3307_ == 0)
{
v___x_3309_ = v___x_3306_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_a_3304_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
}
else
{
lean_object* v_a_3312_; lean_object* v___x_3314_; uint8_t v_isShared_3315_; uint8_t v_isSharedCheck_3319_; 
lean_del_object(v___x_3253_);
lean_del_object(v___x_3246_);
lean_del_object(v___x_3240_);
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3312_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3319_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3319_ == 0)
{
v___x_3314_ = v___x_3259_;
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
else
{
lean_inc(v_a_3312_);
lean_dec(v___x_3259_);
v___x_3314_ = lean_box(0);
v_isShared_3315_ = v_isSharedCheck_3319_;
goto v_resetjp_3313_;
}
v_resetjp_3313_:
{
lean_object* v___x_3317_; 
if (v_isShared_3315_ == 0)
{
v___x_3317_ = v___x_3314_;
goto v_reusejp_3316_;
}
else
{
lean_object* v_reuseFailAlloc_3318_; 
v_reuseFailAlloc_3318_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3318_, 0, v_a_3312_);
v___x_3317_ = v_reuseFailAlloc_3318_;
goto v_reusejp_3316_;
}
v_reusejp_3316_:
{
return v___x_3317_;
}
}
}
}
else
{
lean_del_object(v___x_3253_);
lean_del_object(v___x_3246_);
lean_del_object(v___x_3240_);
lean_dec(v_fst_3237_);
lean_dec(v_fst_3235_);
v___y_3182_ = v_isEq_3225_;
v_isHEq_3183_ = v___x_3038_;
v___y_3184_ = v___y_3226_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v___y_3228_;
v___y_3187_ = v___y_3229_;
goto v___jp_3181_;
}
}
}
else
{
lean_dec(v_a_3249_);
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3240_);
lean_dec(v_fst_3237_);
lean_dec(v_fst_3235_);
v___y_3182_ = v_isEq_3225_;
v_isHEq_3183_ = v___x_3038_;
v___y_3184_ = v___y_3226_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v___y_3228_;
v___y_3187_ = v___y_3229_;
goto v___jp_3181_;
}
}
else
{
lean_object* v_a_3321_; lean_object* v___x_3323_; uint8_t v_isShared_3324_; uint8_t v_isSharedCheck_3328_; 
lean_del_object(v___x_3246_);
lean_dec(v_val_3244_);
lean_del_object(v___x_3240_);
lean_dec(v_fst_3237_);
lean_dec(v_fst_3235_);
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3321_ = lean_ctor_get(v___x_3248_, 0);
v_isSharedCheck_3328_ = !lean_is_exclusive(v___x_3248_);
if (v_isSharedCheck_3328_ == 0)
{
v___x_3323_ = v___x_3248_;
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
else
{
lean_inc(v_a_3321_);
lean_dec(v___x_3248_);
v___x_3323_ = lean_box(0);
v_isShared_3324_ = v_isSharedCheck_3328_;
goto v_resetjp_3322_;
}
v_resetjp_3322_:
{
lean_object* v___x_3326_; 
if (v_isShared_3324_ == 0)
{
v___x_3326_ = v___x_3323_;
goto v_reusejp_3325_;
}
else
{
lean_object* v_reuseFailAlloc_3327_; 
v_reuseFailAlloc_3327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3327_, 0, v_a_3321_);
v___x_3326_ = v_reuseFailAlloc_3327_;
goto v_reusejp_3325_;
}
v_reusejp_3325_:
{
return v___x_3326_;
}
}
}
}
}
else
{
lean_dec(v_a_3243_);
lean_del_object(v___x_3240_);
lean_dec(v_snd_3238_);
lean_dec(v_fst_3237_);
lean_dec(v_fst_3235_);
v___y_3182_ = v_isEq_3225_;
v_isHEq_3183_ = v___x_3038_;
v___y_3184_ = v___y_3226_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v___y_3228_;
v___y_3187_ = v___y_3229_;
goto v___jp_3181_;
}
}
else
{
lean_object* v_a_3330_; lean_object* v___x_3332_; uint8_t v_isShared_3333_; uint8_t v_isSharedCheck_3337_; 
lean_del_object(v___x_3240_);
lean_dec(v_snd_3238_);
lean_dec(v_fst_3237_);
lean_dec(v_fst_3235_);
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3330_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3332_ = v___x_3242_;
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
else
{
lean_inc(v_a_3330_);
lean_dec(v___x_3242_);
v___x_3332_ = lean_box(0);
v_isShared_3333_ = v_isSharedCheck_3337_;
goto v_resetjp_3331_;
}
v_resetjp_3331_:
{
lean_object* v___x_3335_; 
if (v_isShared_3333_ == 0)
{
v___x_3335_ = v___x_3332_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_a_3330_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
}
}
}
else
{
lean_dec(v_a_3231_);
v___y_3182_ = v_isEq_3225_;
v_isHEq_3183_ = v___x_3092_;
v___y_3184_ = v___y_3226_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v___y_3228_;
v___y_3187_ = v___y_3229_;
goto v___jp_3181_;
}
}
else
{
lean_object* v_a_3339_; lean_object* v___x_3341_; uint8_t v_isShared_3342_; uint8_t v_isSharedCheck_3346_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3339_ = lean_ctor_get(v___x_3230_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3230_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3341_ = v___x_3230_;
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
else
{
lean_inc(v_a_3339_);
lean_dec(v___x_3230_);
v___x_3341_ = lean_box(0);
v_isShared_3342_ = v_isSharedCheck_3346_;
goto v_resetjp_3340_;
}
v_resetjp_3340_:
{
lean_object* v___x_3344_; 
if (v_isShared_3342_ == 0)
{
v___x_3344_ = v___x_3341_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v_a_3339_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
}
}
v___jp_3347_:
{
lean_object* v___x_3352_; 
lean_inc_ref(v___x_3093_);
v___x_3352_ = l_Lean_Meta_matchEq_x3f(v___x_3093_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3352_) == 0)
{
lean_object* v_a_3353_; 
v_a_3353_ = lean_ctor_get(v___x_3352_, 0);
lean_inc(v_a_3353_);
lean_dec_ref_known(v___x_3352_, 1);
if (lean_obj_tag(v_a_3353_) == 1)
{
lean_object* v_val_3354_; lean_object* v_snd_3355_; lean_object* v_fst_3356_; lean_object* v_snd_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3436_; 
v_val_3354_ = lean_ctor_get(v_a_3353_, 0);
lean_inc(v_val_3354_);
lean_dec_ref_known(v_a_3353_, 1);
v_snd_3355_ = lean_ctor_get(v_val_3354_, 1);
lean_inc(v_snd_3355_);
lean_dec(v_val_3354_);
v_fst_3356_ = lean_ctor_get(v_snd_3355_, 0);
v_snd_3357_ = lean_ctor_get(v_snd_3355_, 1);
v_isSharedCheck_3436_ = !lean_is_exclusive(v_snd_3355_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3359_ = v_snd_3355_;
v_isShared_3360_ = v_isSharedCheck_3436_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_snd_3357_);
lean_inc(v_fst_3356_);
lean_dec(v_snd_3355_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3436_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; 
v___x_3361_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3356_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3362_);
lean_dec_ref_known(v___x_3361_, 1);
if (lean_obj_tag(v_a_3362_) == 1)
{
lean_object* v_val_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3427_; 
v_val_3363_ = lean_ctor_get(v_a_3362_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v_a_3362_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3365_ = v_a_3362_;
v_isShared_3366_ = v_isSharedCheck_3427_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_val_3363_);
lean_dec(v_a_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3427_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; 
v___x_3367_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3357_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3367_, 1);
if (lean_obj_tag(v_a_3368_) == 1)
{
lean_object* v_toConstantVal_3369_; lean_object* v_val_3370_; lean_object* v___x_3372_; uint8_t v_isShared_3373_; uint8_t v_isSharedCheck_3418_; 
v_toConstantVal_3369_ = lean_ctor_get(v_val_3363_, 0);
lean_inc_ref(v_toConstantVal_3369_);
lean_dec(v_val_3363_);
v_val_3370_ = lean_ctor_get(v_a_3368_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v_a_3368_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3372_ = v_a_3368_;
v_isShared_3373_ = v_isSharedCheck_3418_;
goto v_resetjp_3371_;
}
else
{
lean_inc(v_val_3370_);
lean_dec(v_a_3368_);
v___x_3372_ = lean_box(0);
v_isShared_3373_ = v_isSharedCheck_3418_;
goto v_resetjp_3371_;
}
v_resetjp_3371_:
{
lean_object* v_toConstantVal_3374_; lean_object* v_name_3375_; lean_object* v_name_3376_; uint8_t v___x_3377_; 
v_toConstantVal_3374_ = lean_ctor_get(v_val_3370_, 0);
lean_inc_ref(v_toConstantVal_3374_);
lean_dec(v_val_3370_);
v_name_3375_ = lean_ctor_get(v_toConstantVal_3369_, 0);
lean_inc(v_name_3375_);
lean_dec_ref(v_toConstantVal_3369_);
v_name_3376_ = lean_ctor_get(v_toConstantVal_3374_, 0);
lean_inc(v_name_3376_);
lean_dec_ref(v_toConstantVal_3374_);
v___x_3377_ = lean_name_eq(v_name_3375_, v_name_3376_);
lean_dec(v_name_3376_);
lean_dec(v_name_3375_);
if (v___x_3377_ == 0)
{
lean_object* v___x_3378_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_config_3027_);
lean_inc(v_mvarId_3028_);
v___x_3378_ = l_Lean_MVarId_getType(v_mvarId_3028_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
v___x_3380_ = l_Lean_LocalDecl_toExpr(v_val_3059_);
v___x_3381_ = l_Lean_Meta_mkNoConfusion(v_a_3379_, v___x_3380_, v___y_3348_, v___y_3349_, v___y_3350_, v___y_3351_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3383_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3381_, 1);
v___x_3383_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3028_, v_a_3382_, v___y_3349_);
if (lean_obj_tag(v___x_3383_) == 0)
{
lean_object* v___x_3384_; lean_object* v___x_3386_; 
lean_dec_ref_known(v___x_3383_, 1);
v___x_3384_ = lean_box(v___x_3038_);
if (v_isShared_3373_ == 0)
{
lean_ctor_set(v___x_3372_, 0, v___x_3384_);
v___x_3386_ = v___x_3372_;
goto v_reusejp_3385_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3384_);
v___x_3386_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3385_;
}
v_reusejp_3385_:
{
lean_object* v___x_3388_; 
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 1, v___x_3063_);
lean_ctor_set(v___x_3359_, 0, v___x_3386_);
v___x_3388_ = v___x_3359_;
goto v_reusejp_3387_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3386_);
lean_ctor_set(v_reuseFailAlloc_3392_, 1, v___x_3063_);
v___x_3388_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3387_;
}
v_reusejp_3387_:
{
lean_object* v___x_3390_; 
if (v_isShared_3366_ == 0)
{
lean_ctor_set_tag(v___x_3365_, 0);
lean_ctor_set(v___x_3365_, 0, v___x_3388_);
v___x_3390_ = v___x_3365_;
goto v_reusejp_3389_;
}
else
{
lean_object* v_reuseFailAlloc_3391_; 
v_reuseFailAlloc_3391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3388_);
v___x_3390_ = v_reuseFailAlloc_3391_;
goto v_reusejp_3389_;
}
v_reusejp_3389_:
{
v_a_3045_ = v___x_3390_;
goto v___jp_3044_;
}
}
}
}
else
{
lean_object* v_a_3394_; lean_object* v___x_3396_; uint8_t v_isShared_3397_; uint8_t v_isSharedCheck_3401_; 
lean_del_object(v___x_3372_);
lean_del_object(v___x_3365_);
lean_del_object(v___x_3359_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
v_a_3394_ = lean_ctor_get(v___x_3383_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3383_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3396_ = v___x_3383_;
v_isShared_3397_ = v_isSharedCheck_3401_;
goto v_resetjp_3395_;
}
else
{
lean_inc(v_a_3394_);
lean_dec(v___x_3383_);
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
else
{
lean_object* v_a_3402_; lean_object* v___x_3404_; uint8_t v_isShared_3405_; uint8_t v_isSharedCheck_3409_; 
lean_del_object(v___x_3372_);
lean_del_object(v___x_3365_);
lean_del_object(v___x_3359_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3402_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3409_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3409_ == 0)
{
v___x_3404_ = v___x_3381_;
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
else
{
lean_inc(v_a_3402_);
lean_dec(v___x_3381_);
v___x_3404_ = lean_box(0);
v_isShared_3405_ = v_isSharedCheck_3409_;
goto v_resetjp_3403_;
}
v_resetjp_3403_:
{
lean_object* v___x_3407_; 
if (v_isShared_3405_ == 0)
{
v___x_3407_ = v___x_3404_;
goto v_reusejp_3406_;
}
else
{
lean_object* v_reuseFailAlloc_3408_; 
v_reuseFailAlloc_3408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3408_, 0, v_a_3402_);
v___x_3407_ = v_reuseFailAlloc_3408_;
goto v_reusejp_3406_;
}
v_reusejp_3406_:
{
return v___x_3407_;
}
}
}
}
else
{
lean_object* v_a_3410_; lean_object* v___x_3412_; uint8_t v_isShared_3413_; uint8_t v_isSharedCheck_3417_; 
lean_del_object(v___x_3372_);
lean_del_object(v___x_3365_);
lean_del_object(v___x_3359_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3410_ = lean_ctor_get(v___x_3378_, 0);
v_isSharedCheck_3417_ = !lean_is_exclusive(v___x_3378_);
if (v_isSharedCheck_3417_ == 0)
{
v___x_3412_ = v___x_3378_;
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
else
{
lean_inc(v_a_3410_);
lean_dec(v___x_3378_);
v___x_3412_ = lean_box(0);
v_isShared_3413_ = v_isSharedCheck_3417_;
goto v_resetjp_3411_;
}
v_resetjp_3411_:
{
lean_object* v___x_3415_; 
if (v_isShared_3413_ == 0)
{
v___x_3415_ = v___x_3412_;
goto v_reusejp_3414_;
}
else
{
lean_object* v_reuseFailAlloc_3416_; 
v_reuseFailAlloc_3416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3416_, 0, v_a_3410_);
v___x_3415_ = v_reuseFailAlloc_3416_;
goto v_reusejp_3414_;
}
v_reusejp_3414_:
{
return v___x_3415_;
}
}
}
}
else
{
lean_del_object(v___x_3372_);
lean_del_object(v___x_3365_);
lean_del_object(v___x_3359_);
v_isEq_3225_ = v___x_3038_;
v___y_3226_ = v___y_3348_;
v___y_3227_ = v___y_3349_;
v___y_3228_ = v___y_3350_;
v___y_3229_ = v___y_3351_;
goto v___jp_3224_;
}
}
}
else
{
lean_dec(v_a_3368_);
lean_del_object(v___x_3365_);
lean_dec(v_val_3363_);
lean_del_object(v___x_3359_);
v_isEq_3225_ = v___x_3038_;
v___y_3226_ = v___y_3348_;
v___y_3227_ = v___y_3349_;
v___y_3228_ = v___y_3350_;
v___y_3229_ = v___y_3351_;
goto v___jp_3224_;
}
}
else
{
lean_object* v_a_3419_; lean_object* v___x_3421_; uint8_t v_isShared_3422_; uint8_t v_isSharedCheck_3426_; 
lean_del_object(v___x_3365_);
lean_dec(v_val_3363_);
lean_del_object(v___x_3359_);
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3419_ = lean_ctor_get(v___x_3367_, 0);
v_isSharedCheck_3426_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3426_ == 0)
{
v___x_3421_ = v___x_3367_;
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
else
{
lean_inc(v_a_3419_);
lean_dec(v___x_3367_);
v___x_3421_ = lean_box(0);
v_isShared_3422_ = v_isSharedCheck_3426_;
goto v_resetjp_3420_;
}
v_resetjp_3420_:
{
lean_object* v___x_3424_; 
if (v_isShared_3422_ == 0)
{
v___x_3424_ = v___x_3421_;
goto v_reusejp_3423_;
}
else
{
lean_object* v_reuseFailAlloc_3425_; 
v_reuseFailAlloc_3425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3425_, 0, v_a_3419_);
v___x_3424_ = v_reuseFailAlloc_3425_;
goto v_reusejp_3423_;
}
v_reusejp_3423_:
{
return v___x_3424_;
}
}
}
}
}
else
{
lean_dec(v_a_3362_);
lean_del_object(v___x_3359_);
lean_dec(v_snd_3357_);
v_isEq_3225_ = v___x_3038_;
v___y_3226_ = v___y_3348_;
v___y_3227_ = v___y_3349_;
v___y_3228_ = v___y_3350_;
v___y_3229_ = v___y_3351_;
goto v___jp_3224_;
}
}
else
{
lean_object* v_a_3428_; lean_object* v___x_3430_; uint8_t v_isShared_3431_; uint8_t v_isSharedCheck_3435_; 
lean_del_object(v___x_3359_);
lean_dec(v_snd_3357_);
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3428_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3435_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3435_ == 0)
{
v___x_3430_ = v___x_3361_;
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
else
{
lean_inc(v_a_3428_);
lean_dec(v___x_3361_);
v___x_3430_ = lean_box(0);
v_isShared_3431_ = v_isSharedCheck_3435_;
goto v_resetjp_3429_;
}
v_resetjp_3429_:
{
lean_object* v___x_3433_; 
if (v_isShared_3431_ == 0)
{
v___x_3433_ = v___x_3430_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3434_; 
v_reuseFailAlloc_3434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3434_, 0, v_a_3428_);
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
else
{
lean_dec(v_a_3353_);
v_isEq_3225_ = v___x_3092_;
v___y_3226_ = v___y_3348_;
v___y_3227_ = v___y_3349_;
v___y_3228_ = v___y_3350_;
v___y_3229_ = v___y_3351_;
goto v___jp_3224_;
}
}
else
{
lean_object* v_a_3437_; lean_object* v___x_3439_; uint8_t v_isShared_3440_; uint8_t v_isSharedCheck_3444_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3437_ = lean_ctor_get(v___x_3352_, 0);
v_isSharedCheck_3444_ = !lean_is_exclusive(v___x_3352_);
if (v_isSharedCheck_3444_ == 0)
{
v___x_3439_ = v___x_3352_;
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
else
{
lean_inc(v_a_3437_);
lean_dec(v___x_3352_);
v___x_3439_ = lean_box(0);
v_isShared_3440_ = v_isSharedCheck_3444_;
goto v_resetjp_3438_;
}
v_resetjp_3438_:
{
lean_object* v___x_3442_; 
if (v_isShared_3440_ == 0)
{
v___x_3442_ = v___x_3439_;
goto v_reusejp_3441_;
}
else
{
lean_object* v_reuseFailAlloc_3443_; 
v_reuseFailAlloc_3443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3443_, 0, v_a_3437_);
v___x_3442_ = v_reuseFailAlloc_3443_;
goto v_reusejp_3441_;
}
v_reusejp_3441_:
{
return v___x_3442_;
}
}
}
}
v___jp_3445_:
{
lean_object* v___x_3450_; 
lean_inc_ref(v___x_3093_);
v___x_3450_ = l_Lean_refutableHasNotBit_x3f(v___x_3093_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
if (lean_obj_tag(v_a_3451_) == 1)
{
lean_object* v_val_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3492_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_config_3027_);
v_val_3452_ = lean_ctor_get(v_a_3451_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v_a_3451_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3454_ = v_a_3451_;
v_isShared_3455_ = v_isSharedCheck_3492_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_val_3452_);
lean_dec(v_a_3451_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3492_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; 
lean_inc(v_mvarId_3028_);
v___x_3456_ = l_Lean_MVarId_getType(v_mvarId_3028_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = l_Lean_LocalDecl_toExpr(v_val_3059_);
v___x_3459_ = l_Lean_Meta_mkAbsurd(v_a_3457_, v_val_3452_, v___x_3458_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v___x_3461_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3028_, v_a_3460_, v___y_3447_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v___x_3462_; lean_object* v___x_3464_; 
lean_dec_ref_known(v___x_3461_, 1);
v___x_3462_ = lean_box(v___x_3038_);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v___x_3462_);
v___x_3464_ = v___x_3454_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3467_; 
v_reuseFailAlloc_3467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3467_, 0, v___x_3462_);
v___x_3464_ = v_reuseFailAlloc_3467_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; 
v___x_3465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
lean_ctor_set(v___x_3465_, 1, v___x_3063_);
v___x_3466_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
v_a_3045_ = v___x_3466_;
goto v___jp_3044_;
}
}
else
{
lean_object* v_a_3468_; lean_object* v___x_3470_; uint8_t v_isShared_3471_; uint8_t v_isSharedCheck_3475_; 
lean_del_object(v___x_3454_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
v_a_3468_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3475_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3475_ == 0)
{
v___x_3470_ = v___x_3461_;
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
else
{
lean_inc(v_a_3468_);
lean_dec(v___x_3461_);
v___x_3470_ = lean_box(0);
v_isShared_3471_ = v_isSharedCheck_3475_;
goto v_resetjp_3469_;
}
v_resetjp_3469_:
{
lean_object* v___x_3473_; 
if (v_isShared_3471_ == 0)
{
v___x_3473_ = v___x_3470_;
goto v_reusejp_3472_;
}
else
{
lean_object* v_reuseFailAlloc_3474_; 
v_reuseFailAlloc_3474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3474_, 0, v_a_3468_);
v___x_3473_ = v_reuseFailAlloc_3474_;
goto v_reusejp_3472_;
}
v_reusejp_3472_:
{
return v___x_3473_;
}
}
}
}
else
{
lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3483_; 
lean_del_object(v___x_3454_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3476_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3483_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3483_ == 0)
{
v___x_3478_ = v___x_3459_;
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_dec(v___x_3459_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3483_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
lean_object* v___x_3481_; 
if (v_isShared_3479_ == 0)
{
v___x_3481_ = v___x_3478_;
goto v_reusejp_3480_;
}
else
{
lean_object* v_reuseFailAlloc_3482_; 
v_reuseFailAlloc_3482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3482_, 0, v_a_3476_);
v___x_3481_ = v_reuseFailAlloc_3482_;
goto v_reusejp_3480_;
}
v_reusejp_3480_:
{
return v___x_3481_;
}
}
}
}
else
{
lean_object* v_a_3484_; lean_object* v___x_3486_; uint8_t v_isShared_3487_; uint8_t v_isSharedCheck_3491_; 
lean_del_object(v___x_3454_);
lean_dec(v_val_3452_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3484_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3491_ == 0)
{
v___x_3486_ = v___x_3456_;
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
else
{
lean_inc(v_a_3484_);
lean_dec(v___x_3456_);
v___x_3486_ = lean_box(0);
v_isShared_3487_ = v_isSharedCheck_3491_;
goto v_resetjp_3485_;
}
v_resetjp_3485_:
{
lean_object* v___x_3489_; 
if (v_isShared_3487_ == 0)
{
v___x_3489_ = v___x_3486_;
goto v_reusejp_3488_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_a_3484_);
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
}
else
{
lean_object* v___x_3493_; 
lean_dec(v_a_3451_);
lean_inc_ref(v___x_3093_);
v___x_3493_ = l_Lean_Meta_matchNe_x3f(v___x_3093_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3493_) == 0)
{
lean_object* v_a_3494_; 
v_a_3494_ = lean_ctor_get(v___x_3493_, 0);
lean_inc(v_a_3494_);
lean_dec_ref_known(v___x_3493_, 1);
if (lean_obj_tag(v_a_3494_) == 1)
{
lean_object* v_val_3495_; lean_object* v___x_3497_; uint8_t v_isShared_3498_; uint8_t v_isSharedCheck_3565_; 
v_val_3495_ = lean_ctor_get(v_a_3494_, 0);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_a_3494_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3497_ = v_a_3494_;
v_isShared_3498_ = v_isSharedCheck_3565_;
goto v_resetjp_3496_;
}
else
{
lean_inc(v_val_3495_);
lean_dec(v_a_3494_);
v___x_3497_ = lean_box(0);
v_isShared_3498_ = v_isSharedCheck_3565_;
goto v_resetjp_3496_;
}
v_resetjp_3496_:
{
lean_object* v_snd_3499_; lean_object* v_fst_3500_; lean_object* v_snd_3501_; lean_object* v___x_3503_; uint8_t v_isShared_3504_; uint8_t v_isSharedCheck_3564_; 
v_snd_3499_ = lean_ctor_get(v_val_3495_, 1);
lean_inc(v_snd_3499_);
lean_dec(v_val_3495_);
v_fst_3500_ = lean_ctor_get(v_snd_3499_, 0);
v_snd_3501_ = lean_ctor_get(v_snd_3499_, 1);
v_isSharedCheck_3564_ = !lean_is_exclusive(v_snd_3499_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3503_ = v_snd_3499_;
v_isShared_3504_ = v_isSharedCheck_3564_;
goto v_resetjp_3502_;
}
else
{
lean_inc(v_snd_3501_);
lean_inc(v_fst_3500_);
lean_dec(v_snd_3499_);
v___x_3503_ = lean_box(0);
v_isShared_3504_ = v_isSharedCheck_3564_;
goto v_resetjp_3502_;
}
v_resetjp_3502_:
{
lean_object* v___x_3505_; 
lean_inc(v_fst_3500_);
v___x_3505_ = l_Lean_Meta_isExprDefEq(v_fst_3500_, v_snd_3501_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; uint8_t v___x_3507_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
v___x_3507_ = lean_unbox(v_a_3506_);
lean_dec(v_a_3506_);
if (v___x_3507_ == 0)
{
lean_del_object(v___x_3503_);
lean_dec(v_fst_3500_);
lean_del_object(v___x_3497_);
v___y_3348_ = v___y_3446_;
v___y_3349_ = v___y_3447_;
v___y_3350_ = v___y_3448_;
v___y_3351_ = v___y_3449_;
goto v___jp_3347_;
}
else
{
lean_object* v___x_3508_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec_ref(v_config_3027_);
lean_inc(v_mvarId_3028_);
v___x_3508_ = l_Lean_MVarId_getType(v_mvarId_3028_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3508_) == 0)
{
lean_object* v_a_3509_; lean_object* v___x_3510_; 
v_a_3509_ = lean_ctor_get(v___x_3508_, 0);
lean_inc(v_a_3509_);
lean_dec_ref_known(v___x_3508_, 1);
v___x_3510_ = l_Lean_Meta_mkEqRefl(v_fst_3500_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; lean_object* v___x_3512_; lean_object* v___x_3513_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
v___x_3512_ = l_Lean_LocalDecl_toExpr(v_val_3059_);
v___x_3513_ = l_Lean_Meta_mkAbsurd(v_a_3509_, v_a_3511_, v___x_3512_, v___y_3446_, v___y_3447_, v___y_3448_, v___y_3449_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v_a_3514_; lean_object* v___x_3515_; 
v_a_3514_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_a_3514_);
lean_dec_ref_known(v___x_3513_, 1);
v___x_3515_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3028_, v_a_3514_, v___y_3447_);
if (lean_obj_tag(v___x_3515_) == 0)
{
lean_object* v___x_3516_; lean_object* v___x_3518_; 
lean_dec_ref_known(v___x_3515_, 1);
v___x_3516_ = lean_box(v___x_3038_);
if (v_isShared_3498_ == 0)
{
lean_ctor_set(v___x_3497_, 0, v___x_3516_);
v___x_3518_ = v___x_3497_;
goto v_reusejp_3517_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3516_);
v___x_3518_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3517_;
}
v_reusejp_3517_:
{
lean_object* v___x_3520_; 
if (v_isShared_3504_ == 0)
{
lean_ctor_set(v___x_3503_, 1, v___x_3063_);
lean_ctor_set(v___x_3503_, 0, v___x_3518_);
v___x_3520_ = v___x_3503_;
goto v_reusejp_3519_;
}
else
{
lean_object* v_reuseFailAlloc_3522_; 
v_reuseFailAlloc_3522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3522_, 0, v___x_3518_);
lean_ctor_set(v_reuseFailAlloc_3522_, 1, v___x_3063_);
v___x_3520_ = v_reuseFailAlloc_3522_;
goto v_reusejp_3519_;
}
v_reusejp_3519_:
{
lean_object* v___x_3521_; 
v___x_3521_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3520_);
v_a_3045_ = v___x_3521_;
goto v___jp_3044_;
}
}
}
else
{
lean_object* v_a_3524_; lean_object* v___x_3526_; uint8_t v_isShared_3527_; uint8_t v_isSharedCheck_3531_; 
lean_del_object(v___x_3503_);
lean_del_object(v___x_3497_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
v_a_3524_ = lean_ctor_get(v___x_3515_, 0);
v_isSharedCheck_3531_ = !lean_is_exclusive(v___x_3515_);
if (v_isSharedCheck_3531_ == 0)
{
v___x_3526_ = v___x_3515_;
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
else
{
lean_inc(v_a_3524_);
lean_dec(v___x_3515_);
v___x_3526_ = lean_box(0);
v_isShared_3527_ = v_isSharedCheck_3531_;
goto v_resetjp_3525_;
}
v_resetjp_3525_:
{
lean_object* v___x_3529_; 
if (v_isShared_3527_ == 0)
{
v___x_3529_ = v___x_3526_;
goto v_reusejp_3528_;
}
else
{
lean_object* v_reuseFailAlloc_3530_; 
v_reuseFailAlloc_3530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3530_, 0, v_a_3524_);
v___x_3529_ = v_reuseFailAlloc_3530_;
goto v_reusejp_3528_;
}
v_reusejp_3528_:
{
return v___x_3529_;
}
}
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_del_object(v___x_3503_);
lean_del_object(v___x_3497_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3532_ = lean_ctor_get(v___x_3513_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3513_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3513_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3513_);
v___x_3534_ = lean_box(0);
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
v_resetjp_3533_:
{
lean_object* v___x_3537_; 
if (v_isShared_3535_ == 0)
{
v___x_3537_ = v___x_3534_;
goto v_reusejp_3536_;
}
else
{
lean_object* v_reuseFailAlloc_3538_; 
v_reuseFailAlloc_3538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3538_, 0, v_a_3532_);
v___x_3537_ = v_reuseFailAlloc_3538_;
goto v_reusejp_3536_;
}
v_reusejp_3536_:
{
return v___x_3537_;
}
}
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec(v_a_3509_);
lean_del_object(v___x_3503_);
lean_del_object(v___x_3497_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3540_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3510_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3510_);
v___x_3542_ = lean_box(0);
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
v_resetjp_3541_:
{
lean_object* v___x_3545_; 
if (v_isShared_3543_ == 0)
{
v___x_3545_ = v___x_3542_;
goto v_reusejp_3544_;
}
else
{
lean_object* v_reuseFailAlloc_3546_; 
v_reuseFailAlloc_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3546_, 0, v_a_3540_);
v___x_3545_ = v_reuseFailAlloc_3546_;
goto v_reusejp_3544_;
}
v_reusejp_3544_:
{
return v___x_3545_;
}
}
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_del_object(v___x_3503_);
lean_dec(v_fst_3500_);
lean_del_object(v___x_3497_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
v_a_3548_ = lean_ctor_get(v___x_3508_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3508_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3508_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3508_);
v___x_3550_ = lean_box(0);
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
v_resetjp_3549_:
{
lean_object* v___x_3553_; 
if (v_isShared_3551_ == 0)
{
v___x_3553_ = v___x_3550_;
goto v_reusejp_3552_;
}
else
{
lean_object* v_reuseFailAlloc_3554_; 
v_reuseFailAlloc_3554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3554_, 0, v_a_3548_);
v___x_3553_ = v_reuseFailAlloc_3554_;
goto v_reusejp_3552_;
}
v_reusejp_3552_:
{
return v___x_3553_;
}
}
}
}
}
else
{
lean_object* v_a_3556_; lean_object* v___x_3558_; uint8_t v_isShared_3559_; uint8_t v_isSharedCheck_3563_; 
lean_del_object(v___x_3503_);
lean_dec(v_fst_3500_);
lean_del_object(v___x_3497_);
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3556_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3563_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3563_ == 0)
{
v___x_3558_ = v___x_3505_;
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
else
{
lean_inc(v_a_3556_);
lean_dec(v___x_3505_);
v___x_3558_ = lean_box(0);
v_isShared_3559_ = v_isSharedCheck_3563_;
goto v_resetjp_3557_;
}
v_resetjp_3557_:
{
lean_object* v___x_3561_; 
if (v_isShared_3559_ == 0)
{
v___x_3561_ = v___x_3558_;
goto v_reusejp_3560_;
}
else
{
lean_object* v_reuseFailAlloc_3562_; 
v_reuseFailAlloc_3562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3562_, 0, v_a_3556_);
v___x_3561_ = v_reuseFailAlloc_3562_;
goto v_reusejp_3560_;
}
v_reusejp_3560_:
{
return v___x_3561_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3494_);
v___y_3348_ = v___y_3446_;
v___y_3349_ = v___y_3447_;
v___y_3350_ = v___y_3448_;
v___y_3351_ = v___y_3449_;
goto v___jp_3347_;
}
}
else
{
lean_object* v_a_3566_; lean_object* v___x_3568_; uint8_t v_isShared_3569_; uint8_t v_isSharedCheck_3573_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3566_ = lean_ctor_get(v___x_3493_, 0);
v_isSharedCheck_3573_ = !lean_is_exclusive(v___x_3493_);
if (v_isSharedCheck_3573_ == 0)
{
v___x_3568_ = v___x_3493_;
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
else
{
lean_inc(v_a_3566_);
lean_dec(v___x_3493_);
v___x_3568_ = lean_box(0);
v_isShared_3569_ = v_isSharedCheck_3573_;
goto v_resetjp_3567_;
}
v_resetjp_3567_:
{
lean_object* v___x_3571_; 
if (v_isShared_3569_ == 0)
{
v___x_3571_ = v___x_3568_;
goto v_reusejp_3570_;
}
else
{
lean_object* v_reuseFailAlloc_3572_; 
v_reuseFailAlloc_3572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3572_, 0, v_a_3566_);
v___x_3571_ = v_reuseFailAlloc_3572_;
goto v_reusejp_3570_;
}
v_reusejp_3570_:
{
return v___x_3571_;
}
}
}
}
}
else
{
lean_object* v_a_3574_; lean_object* v___x_3576_; uint8_t v_isShared_3577_; uint8_t v_isSharedCheck_3581_; 
lean_dec_ref(v___x_3093_);
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3574_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3581_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3581_ == 0)
{
v___x_3576_ = v___x_3450_;
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
else
{
lean_inc(v_a_3574_);
lean_dec(v___x_3450_);
v___x_3576_ = lean_box(0);
v_isShared_3577_ = v_isSharedCheck_3581_;
goto v_resetjp_3575_;
}
v_resetjp_3575_:
{
lean_object* v___x_3579_; 
if (v_isShared_3577_ == 0)
{
v___x_3579_ = v___x_3576_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_a_3574_);
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
}
else
{
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
v_a_3053_ = v___x_3064_;
goto v___jp_3052_;
}
v___jp_3065_:
{
uint8_t v_emptyType_3072_; 
v_emptyType_3072_ = lean_ctor_get_uint8(v_config_3027_, sizeof(void*)*1 + 1);
if (v_emptyType_3072_ == 0)
{
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
v_a_3053_ = v___x_3064_;
goto v___jp_3052_;
}
else
{
if (v___y_3066_ == 0)
{
if (v___y_3067_ == 0)
{
lean_object* v_searchFuel_3073_; lean_object* v___x_3074_; lean_object* v___x_3075_; 
v_searchFuel_3073_ = lean_ctor_get(v_config_3027_, 0);
v___x_3074_ = l_Lean_LocalDecl_fvarId(v_val_3059_);
lean_dec(v_val_3059_);
lean_inc(v_searchFuel_3073_);
lean_inc(v_mvarId_3028_);
v___x_3075_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3028_, v___x_3074_, v_searchFuel_3073_, v___y_3068_, v___y_3069_, v___y_3070_, v___y_3071_);
if (lean_obj_tag(v___x_3075_) == 0)
{
lean_object* v_a_3076_; uint8_t v___x_3077_; 
v_a_3076_ = lean_ctor_get(v___x_3075_, 0);
lean_inc(v_a_3076_);
lean_dec_ref_known(v___x_3075_, 1);
v___x_3077_ = lean_unbox(v_a_3076_);
lean_dec(v_a_3076_);
if (v___x_3077_ == 0)
{
lean_del_object(v___x_3061_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
v_a_3053_ = v___x_3064_;
goto v___jp_3052_;
}
else
{
lean_object* v___x_3078_; lean_object* v___x_3080_; 
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v___x_3078_ = lean_box(v___x_3038_);
if (v_isShared_3062_ == 0)
{
lean_ctor_set(v___x_3061_, 0, v___x_3078_);
v___x_3080_ = v___x_3061_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v___x_3078_);
v___x_3080_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; 
v___x_3081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3081_, 0, v___x_3080_);
lean_ctor_set(v___x_3081_, 1, v___x_3063_);
v___x_3082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
v_a_3045_ = v___x_3082_;
goto v___jp_3044_;
}
}
}
else
{
lean_object* v_a_3084_; lean_object* v___x_3086_; uint8_t v_isShared_3087_; uint8_t v_isSharedCheck_3091_; 
lean_del_object(v___x_3061_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
lean_dec(v_mvarId_3028_);
lean_dec_ref(v_config_3027_);
v_a_3084_ = lean_ctor_get(v___x_3075_, 0);
v_isSharedCheck_3091_ = !lean_is_exclusive(v___x_3075_);
if (v_isSharedCheck_3091_ == 0)
{
v___x_3086_ = v___x_3075_;
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
else
{
lean_inc(v_a_3084_);
lean_dec(v___x_3075_);
v___x_3086_ = lean_box(0);
v_isShared_3087_ = v_isSharedCheck_3091_;
goto v_resetjp_3085_;
}
v_resetjp_3085_:
{
lean_object* v___x_3089_; 
if (v_isShared_3087_ == 0)
{
v___x_3089_ = v___x_3086_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3090_; 
v_reuseFailAlloc_3090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3090_, 0, v_a_3084_);
v___x_3089_ = v_reuseFailAlloc_3090_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
return v___x_3089_;
}
}
}
}
else
{
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
v_a_3053_ = v___x_3064_;
goto v___jp_3052_;
}
}
else
{
lean_del_object(v___x_3061_);
lean_dec(v_val_3059_);
lean_del_object(v___x_3042_);
lean_dec(v_snd_3040_);
v_a_3053_ = v___x_3064_;
goto v___jp_3052_;
}
}
}
}
}
v___jp_3044_:
{
lean_object* v___x_3046_; lean_object* v___x_3048_; 
v___x_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3046_, 0, v_a_3045_);
if (v_isShared_3043_ == 0)
{
lean_ctor_set(v___x_3042_, 0, v___x_3046_);
v___x_3048_ = v___x_3042_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v___x_3046_);
lean_ctor_set(v_reuseFailAlloc_3050_, 1, v_snd_3040_);
v___x_3048_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
lean_object* v___x_3049_; 
v___x_3049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3049_, 0, v___x_3048_);
return v___x_3049_;
}
}
v___jp_3052_:
{
lean_object* v___x_3054_; size_t v___x_3055_; size_t v___x_3056_; 
v___x_3054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3051_);
lean_ctor_set(v___x_3054_, 1, v_a_3053_);
v___x_3055_ = ((size_t)1ULL);
v___x_3056_ = lean_usize_add(v_i_3031_, v___x_3055_);
v_i_3031_ = v___x_3056_;
v_b_3032_ = v___x_3054_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3655_, lean_object* v_mvarId_3656_, lean_object* v_as_3657_, lean_object* v_sz_3658_, lean_object* v_i_3659_, lean_object* v_b_3660_, lean_object* v___y_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_){
_start:
{
size_t v_sz_boxed_3666_; size_t v_i_boxed_3667_; lean_object* v_res_3668_; 
v_sz_boxed_3666_ = lean_unbox_usize(v_sz_3658_);
lean_dec(v_sz_3658_);
v_i_boxed_3667_ = lean_unbox_usize(v_i_3659_);
lean_dec(v_i_3659_);
v_res_3668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3655_, v_mvarId_3656_, v_as_3657_, v_sz_boxed_3666_, v_i_boxed_3667_, v_b_3660_, v___y_3661_, v___y_3662_, v___y_3663_, v___y_3664_);
lean_dec(v___y_3664_);
lean_dec_ref(v___y_3663_);
lean_dec(v___y_3662_);
lean_dec_ref(v___y_3661_);
lean_dec_ref(v_as_3657_);
return v_res_3668_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3669_, lean_object* v_mvarId_3670_, lean_object* v_as_3671_, size_t v_sz_3672_, size_t v_i_3673_, lean_object* v_b_3674_, lean_object* v___y_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_){
_start:
{
uint8_t v___x_3680_; 
v___x_3680_ = lean_usize_dec_lt(v_i_3673_, v_sz_3672_);
if (v___x_3680_ == 0)
{
lean_object* v___x_3681_; 
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v___x_3681_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3681_, 0, v_b_3674_);
return v___x_3681_;
}
else
{
lean_object* v_snd_3682_; lean_object* v___x_3684_; uint8_t v_isShared_3685_; uint8_t v_isSharedCheck_4295_; 
v_snd_3682_ = lean_ctor_get(v_b_3674_, 1);
v_isSharedCheck_4295_ = !lean_is_exclusive(v_b_3674_);
if (v_isSharedCheck_4295_ == 0)
{
lean_object* v_unused_4296_; 
v_unused_4296_ = lean_ctor_get(v_b_3674_, 0);
lean_dec(v_unused_4296_);
v___x_3684_ = v_b_3674_;
v_isShared_3685_ = v_isSharedCheck_4295_;
goto v_resetjp_3683_;
}
else
{
lean_inc(v_snd_3682_);
lean_dec(v_b_3674_);
v___x_3684_ = lean_box(0);
v_isShared_3685_ = v_isSharedCheck_4295_;
goto v_resetjp_3683_;
}
v_resetjp_3683_:
{
lean_object* v_a_3687_; lean_object* v___x_3693_; lean_object* v_a_3695_; lean_object* v_a_3700_; 
v___x_3693_ = lean_box(0);
v_a_3700_ = lean_array_uget(v_as_3671_, v_i_3673_);
if (lean_obj_tag(v_a_3700_) == 0)
{
lean_del_object(v___x_3684_);
v_a_3695_ = v_snd_3682_;
goto v___jp_3694_;
}
else
{
lean_object* v_val_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_4294_; 
v_val_3701_ = lean_ctor_get(v_a_3700_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v_a_3700_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_3703_ = v_a_3700_;
v_isShared_3704_ = v_isSharedCheck_4294_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_val_3701_);
lean_dec(v_a_3700_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_4294_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; uint8_t v___y_3708_; uint8_t v___y_3709_; lean_object* v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; uint8_t v___x_3734_; 
v___x_3705_ = lean_box(0);
v___x_3706_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3734_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3701_);
if (v___x_3734_ == 0)
{
lean_object* v___x_3735_; uint8_t v___y_3737_; uint8_t v___y_3738_; lean_object* v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3761_; lean_object* v___y_3762_; lean_object* v___y_3763_; uint8_t v___y_3764_; uint8_t v___y_3765_; lean_object* v___y_3766_; lean_object* v_a_3767_; lean_object* v___y_3773_; lean_object* v___y_3774_; lean_object* v___y_3775_; uint8_t v___y_3776_; uint8_t v___y_3777_; lean_object* v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; uint8_t v___y_3824_; uint8_t v_isHEq_3825_; lean_object* v___y_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; uint8_t v_isEq_3867_; lean_object* v___y_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_4088_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___x_4224_; 
v___x_3735_ = l_Lean_LocalDecl_type(v_val_3701_);
lean_inc_ref(v___x_3735_);
v___x_4224_ = l_Lean_Meta_matchNot_x3f(v___x_3735_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
if (lean_obj_tag(v___x_4224_) == 0)
{
lean_object* v_a_4225_; 
v_a_4225_ = lean_ctor_get(v___x_4224_, 0);
lean_inc(v_a_4225_);
lean_dec_ref_known(v___x_4224_, 1);
if (lean_obj_tag(v_a_4225_) == 1)
{
lean_object* v_val_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4285_; 
v_val_4226_ = lean_ctor_get(v_a_4225_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v_a_4225_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4228_ = v_a_4225_;
v_isShared_4229_ = v_isSharedCheck_4285_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_val_4226_);
lean_dec(v_a_4225_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4285_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4230_; 
v___x_4230_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4226_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
if (lean_obj_tag(v___x_4230_) == 0)
{
lean_object* v_a_4231_; 
v_a_4231_ = lean_ctor_get(v___x_4230_, 0);
lean_inc(v_a_4231_);
lean_dec_ref_known(v___x_4230_, 1);
if (lean_obj_tag(v_a_4231_) == 1)
{
lean_object* v_val_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4276_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec_ref(v_config_3669_);
v_val_4232_ = lean_ctor_get(v_a_4231_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v_a_4231_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4234_ = v_a_4231_;
v_isShared_4235_ = v_isSharedCheck_4276_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_val_4232_);
lean_dec(v_a_4231_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4276_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4236_; 
lean_inc(v_mvarId_3670_);
v___x_4236_ = l_Lean_MVarId_getType(v_mvarId_3670_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
if (lean_obj_tag(v___x_4236_) == 0)
{
lean_object* v_a_4237_; lean_object* v___x_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; 
v_a_4237_ = lean_ctor_get(v___x_4236_, 0);
lean_inc(v_a_4237_);
lean_dec_ref_known(v___x_4236_, 1);
v___x_4238_ = l_Lean_LocalDecl_toExpr(v_val_3701_);
v___x_4239_ = l_Lean_mkFVar(v_val_4232_);
v___x_4240_ = l_Lean_Expr_app___override(v___x_4238_, v___x_4239_);
v___x_4241_ = l_Lean_Meta_mkFalseElim(v_a_4237_, v___x_4240_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
if (lean_obj_tag(v___x_4241_) == 0)
{
lean_object* v_a_4242_; lean_object* v___x_4243_; 
v_a_4242_ = lean_ctor_get(v___x_4241_, 0);
lean_inc(v_a_4242_);
lean_dec_ref_known(v___x_4241_, 1);
v___x_4243_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3670_, v_a_4242_, v___y_3676_);
if (lean_obj_tag(v___x_4243_) == 0)
{
lean_object* v___x_4244_; lean_object* v___x_4246_; 
lean_dec_ref_known(v___x_4243_, 1);
v___x_4244_ = lean_box(v___x_3680_);
if (v_isShared_4235_ == 0)
{
lean_ctor_set(v___x_4234_, 0, v___x_4244_);
v___x_4246_ = v___x_4234_;
goto v_reusejp_4245_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4244_);
v___x_4246_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4245_;
}
v_reusejp_4245_:
{
lean_object* v___x_4247_; lean_object* v___x_4249_; 
v___x_4247_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4246_);
lean_ctor_set(v___x_4247_, 1, v___x_3705_);
if (v_isShared_4229_ == 0)
{
lean_ctor_set_tag(v___x_4228_, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4247_);
v___x_4249_ = v___x_4228_;
goto v_reusejp_4248_;
}
else
{
lean_object* v_reuseFailAlloc_4250_; 
v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4247_);
v___x_4249_ = v_reuseFailAlloc_4250_;
goto v_reusejp_4248_;
}
v_reusejp_4248_:
{
v_a_3687_ = v___x_4249_;
goto v___jp_3686_;
}
}
}
else
{
lean_object* v_a_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_del_object(v___x_4234_);
lean_del_object(v___x_4228_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
v_a_4252_ = lean_ctor_get(v___x_4243_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4243_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4243_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_a_4252_);
lean_dec(v___x_4243_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
else
{
lean_object* v_a_4260_; lean_object* v___x_4262_; uint8_t v_isShared_4263_; uint8_t v_isSharedCheck_4267_; 
lean_del_object(v___x_4234_);
lean_del_object(v___x_4228_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_4260_ = lean_ctor_get(v___x_4241_, 0);
v_isSharedCheck_4267_ = !lean_is_exclusive(v___x_4241_);
if (v_isSharedCheck_4267_ == 0)
{
v___x_4262_ = v___x_4241_;
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
else
{
lean_inc(v_a_4260_);
lean_dec(v___x_4241_);
v___x_4262_ = lean_box(0);
v_isShared_4263_ = v_isSharedCheck_4267_;
goto v_resetjp_4261_;
}
v_resetjp_4261_:
{
lean_object* v___x_4265_; 
if (v_isShared_4263_ == 0)
{
v___x_4265_ = v___x_4262_;
goto v_reusejp_4264_;
}
else
{
lean_object* v_reuseFailAlloc_4266_; 
v_reuseFailAlloc_4266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4266_, 0, v_a_4260_);
v___x_4265_ = v_reuseFailAlloc_4266_;
goto v_reusejp_4264_;
}
v_reusejp_4264_:
{
return v___x_4265_;
}
}
}
}
else
{
lean_object* v_a_4268_; lean_object* v___x_4270_; uint8_t v_isShared_4271_; uint8_t v_isSharedCheck_4275_; 
lean_del_object(v___x_4234_);
lean_dec(v_val_4232_);
lean_del_object(v___x_4228_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_4268_ = lean_ctor_get(v___x_4236_, 0);
v_isSharedCheck_4275_ = !lean_is_exclusive(v___x_4236_);
if (v_isSharedCheck_4275_ == 0)
{
v___x_4270_ = v___x_4236_;
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
else
{
lean_inc(v_a_4268_);
lean_dec(v___x_4236_);
v___x_4270_ = lean_box(0);
v_isShared_4271_ = v_isSharedCheck_4275_;
goto v_resetjp_4269_;
}
v_resetjp_4269_:
{
lean_object* v___x_4273_; 
if (v_isShared_4271_ == 0)
{
v___x_4273_ = v___x_4270_;
goto v_reusejp_4272_;
}
else
{
lean_object* v_reuseFailAlloc_4274_; 
v_reuseFailAlloc_4274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4274_, 0, v_a_4268_);
v___x_4273_ = v_reuseFailAlloc_4274_;
goto v_reusejp_4272_;
}
v_reusejp_4272_:
{
return v___x_4273_;
}
}
}
}
}
else
{
lean_dec(v_a_4231_);
lean_del_object(v___x_4228_);
v___y_4088_ = v___y_3675_;
v___y_4089_ = v___y_3676_;
v___y_4090_ = v___y_3677_;
v___y_4091_ = v___y_3678_;
goto v___jp_4087_;
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_del_object(v___x_4228_);
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_4277_ = lean_ctor_get(v___x_4230_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4230_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4230_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4230_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_a_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
else
{
lean_dec(v_a_4225_);
v___y_4088_ = v___y_3675_;
v___y_4089_ = v___y_3676_;
v___y_4090_ = v___y_3677_;
v___y_4091_ = v___y_3678_;
goto v___jp_4087_;
}
}
else
{
lean_object* v_a_4286_; lean_object* v___x_4288_; uint8_t v_isShared_4289_; uint8_t v_isSharedCheck_4293_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_4286_ = lean_ctor_get(v___x_4224_, 0);
v_isSharedCheck_4293_ = !lean_is_exclusive(v___x_4224_);
if (v_isSharedCheck_4293_ == 0)
{
v___x_4288_ = v___x_4224_;
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
else
{
lean_inc(v_a_4286_);
lean_dec(v___x_4224_);
v___x_4288_ = lean_box(0);
v_isShared_4289_ = v_isSharedCheck_4293_;
goto v_resetjp_4287_;
}
v_resetjp_4287_:
{
lean_object* v___x_4291_; 
if (v_isShared_4289_ == 0)
{
v___x_4291_ = v___x_4288_;
goto v_reusejp_4290_;
}
else
{
lean_object* v_reuseFailAlloc_4292_; 
v_reuseFailAlloc_4292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4292_, 0, v_a_4286_);
v___x_4291_ = v_reuseFailAlloc_4292_;
goto v_reusejp_4290_;
}
v_reusejp_4290_:
{
return v___x_4291_;
}
}
}
v___jp_3736_:
{
uint8_t v_genDiseq_3743_; 
v_genDiseq_3743_ = lean_ctor_get_uint8(v_config_3669_, sizeof(void*)*1 + 2);
if (v_genDiseq_3743_ == 0)
{
lean_dec_ref(v___x_3735_);
v___y_3708_ = v___y_3737_;
v___y_3709_ = v___y_3738_;
v___y_3710_ = v___y_3739_;
v___y_3711_ = v___y_3740_;
v___y_3712_ = v___y_3741_;
v___y_3713_ = v___y_3742_;
goto v___jp_3707_;
}
else
{
uint8_t v___x_3744_; 
v___x_3744_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3735_);
if (v___x_3744_ == 0)
{
v___y_3708_ = v___y_3737_;
v___y_3709_ = v___y_3738_;
v___y_3710_ = v___y_3739_;
v___y_3711_ = v___y_3740_;
v___y_3712_ = v___y_3741_;
v___y_3713_ = v___y_3742_;
goto v___jp_3707_;
}
else
{
lean_object* v___x_3745_; 
lean_inc(v_val_3701_);
lean_inc(v_mvarId_3670_);
v___x_3745_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3670_, v_val_3701_, v___y_3739_, v___y_3740_, v___y_3741_, v___y_3742_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; uint8_t v___x_3747_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
v___x_3747_ = lean_unbox(v_a_3746_);
lean_dec(v_a_3746_);
if (v___x_3747_ == 0)
{
v___y_3708_ = v___y_3737_;
v___y_3709_ = v___y_3738_;
v___y_3710_ = v___y_3739_;
v___y_3711_ = v___y_3740_;
v___y_3712_ = v___y_3741_;
v___y_3713_ = v___y_3742_;
goto v___jp_3707_;
}
else
{
lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; 
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v___x_3748_ = lean_box(v___x_3680_);
v___x_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3749_, 0, v___x_3748_);
v___x_3750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
lean_ctor_set(v___x_3750_, 1, v___x_3705_);
v___x_3751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
v_a_3687_ = v___x_3751_;
goto v___jp_3686_;
}
}
else
{
lean_object* v_a_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3759_; 
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_3752_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3759_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3759_ == 0)
{
v___x_3754_ = v___x_3745_;
v_isShared_3755_ = v_isSharedCheck_3759_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_a_3752_);
lean_dec(v___x_3745_);
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
}
}
v___jp_3760_:
{
uint8_t v___x_3768_; 
v___x_3768_ = l_Lean_Exception_isInterrupt(v_a_3767_);
if (v___x_3768_ == 0)
{
uint8_t v___x_3769_; 
lean_inc_ref(v_a_3767_);
v___x_3769_ = l_Lean_Exception_isRuntime(v_a_3767_);
if (v___x_3769_ == 0)
{
lean_dec_ref(v_a_3767_);
v___y_3737_ = v___y_3764_;
v___y_3738_ = v___y_3765_;
v___y_3739_ = v___y_3762_;
v___y_3740_ = v___y_3763_;
v___y_3741_ = v___y_3766_;
v___y_3742_ = v___y_3761_;
goto v___jp_3736_;
}
else
{
lean_object* v___x_3770_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v___x_3770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3770_, 0, v_a_3767_);
return v___x_3770_;
}
}
else
{
lean_object* v___x_3771_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v___x_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3771_, 0, v_a_3767_);
return v___x_3771_;
}
}
v___jp_3772_:
{
if (lean_obj_tag(v___y_3780_) == 0)
{
lean_object* v_a_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v_a_3781_ = lean_ctor_get(v___y_3780_, 0);
lean_inc(v_a_3781_);
lean_dec_ref_known(v___y_3780_, 1);
v___x_3782_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3783_ = l_Lean_Expr_isConstOf(v_a_3781_, v___x_3782_);
lean_dec(v_a_3781_);
if (v___x_3783_ == 0)
{
lean_dec_ref(v___y_3778_);
v___y_3737_ = v___y_3776_;
v___y_3738_ = v___y_3777_;
v___y_3739_ = v___y_3774_;
v___y_3740_ = v___y_3775_;
v___y_3741_ = v___y_3779_;
v___y_3742_ = v___y_3773_;
goto v___jp_3736_;
}
else
{
lean_object* v___x_3784_; 
lean_inc_ref(v___y_3778_);
v___x_3784_ = l_Lean_Meta_mkEqRefl(v___y_3778_, v___y_3774_, v___y_3775_, v___y_3779_, v___y_3773_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; lean_object* v___x_3786_; lean_object* v_dummy_3787_; lean_object* v_nargs_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
v___x_3786_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3787_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3788_ = l_Lean_Expr_getAppNumArgs(v___y_3778_);
lean_inc(v_nargs_3788_);
v___x_3789_ = lean_mk_array(v_nargs_3788_, v_dummy_3787_);
v___x_3790_ = lean_unsigned_to_nat(1u);
v___x_3791_ = lean_nat_sub(v_nargs_3788_, v___x_3790_);
lean_dec(v_nargs_3788_);
v___x_3792_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3778_, v___x_3789_, v___x_3791_);
v___x_3793_ = lean_array_push(v___x_3792_, v_a_3785_);
v___x_3794_ = l_Lean_mkAppN(v___x_3786_, v___x_3793_);
lean_dec_ref(v___x_3793_);
lean_inc(v_mvarId_3670_);
v___x_3795_ = l_Lean_MVarId_getType(v_mvarId_3670_, v___y_3774_, v___y_3775_, v___y_3779_, v___y_3773_);
if (lean_obj_tag(v___x_3795_) == 0)
{
lean_object* v_a_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; 
v_a_3796_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3796_);
lean_dec_ref_known(v___x_3795_, 1);
lean_inc(v_val_3701_);
v___x_3797_ = l_Lean_LocalDecl_toExpr(v_val_3701_);
v___x_3798_ = l_Lean_Meta_mkAbsurd(v_a_3796_, v___x_3797_, v___x_3794_, v___y_3774_, v___y_3775_, v___y_3779_, v___y_3773_);
if (lean_obj_tag(v___x_3798_) == 0)
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3818_; 
v_a_3799_ = lean_ctor_get(v___x_3798_, 0);
v_isSharedCheck_3818_ = !lean_is_exclusive(v___x_3798_);
if (v_isSharedCheck_3818_ == 0)
{
v___x_3801_ = v___x_3798_;
v_isShared_3802_ = v_isSharedCheck_3818_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3798_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3818_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3803_; 
lean_inc(v_mvarId_3670_);
v___x_3803_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3670_, v_a_3799_, v___y_3775_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3815_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_isSharedCheck_3815_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3815_ == 0)
{
lean_object* v_unused_3816_; 
v_unused_3816_ = lean_ctor_get(v___x_3803_, 0);
lean_dec(v_unused_3816_);
v___x_3805_ = v___x_3803_;
v_isShared_3806_ = v_isSharedCheck_3815_;
goto v_resetjp_3804_;
}
else
{
lean_dec(v___x_3803_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3815_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3807_ = lean_box(v___x_3680_);
if (v_isShared_3806_ == 0)
{
lean_ctor_set_tag(v___x_3805_, 1);
lean_ctor_set(v___x_3805_, 0, v___x_3807_);
v___x_3809_ = v___x_3805_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3814_; 
v_reuseFailAlloc_3814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3814_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3810_; lean_object* v___x_3812_; 
v___x_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3809_);
lean_ctor_set(v___x_3810_, 1, v___x_3705_);
if (v_isShared_3802_ == 0)
{
lean_ctor_set(v___x_3801_, 0, v___x_3810_);
v___x_3812_ = v___x_3801_;
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
v_a_3687_ = v___x_3812_;
goto v___jp_3686_;
}
}
}
}
else
{
lean_object* v_a_3817_; 
lean_del_object(v___x_3801_);
v_a_3817_ = lean_ctor_get(v___x_3803_, 0);
lean_inc(v_a_3817_);
lean_dec_ref_known(v___x_3803_, 1);
v___y_3761_ = v___y_3773_;
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3779_;
v_a_3767_ = v_a_3817_;
goto v___jp_3760_;
}
}
}
else
{
lean_object* v_a_3819_; 
v_a_3819_ = lean_ctor_get(v___x_3798_, 0);
lean_inc(v_a_3819_);
lean_dec_ref_known(v___x_3798_, 1);
v___y_3761_ = v___y_3773_;
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3779_;
v_a_3767_ = v_a_3819_;
goto v___jp_3760_;
}
}
else
{
lean_object* v_a_3820_; 
lean_dec_ref(v___x_3794_);
v_a_3820_ = lean_ctor_get(v___x_3795_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3795_, 1);
v___y_3761_ = v___y_3773_;
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3779_;
v_a_3767_ = v_a_3820_;
goto v___jp_3760_;
}
}
else
{
lean_object* v_a_3821_; 
lean_dec_ref(v___y_3778_);
v_a_3821_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3784_, 1);
v___y_3761_ = v___y_3773_;
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3779_;
v_a_3767_ = v_a_3821_;
goto v___jp_3760_;
}
}
}
else
{
lean_object* v_a_3822_; 
lean_dec_ref(v___y_3778_);
v_a_3822_ = lean_ctor_get(v___y_3780_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___y_3780_, 1);
v___y_3761_ = v___y_3773_;
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3779_;
v_a_3767_ = v_a_3822_;
goto v___jp_3760_;
}
}
v___jp_3823_:
{
uint8_t v_useDecide_3830_; 
v_useDecide_3830_ = lean_ctor_get_uint8(v_config_3669_, sizeof(void*)*1);
if (v_useDecide_3830_ == 0)
{
v___y_3737_ = v_isHEq_3825_;
v___y_3738_ = v___y_3824_;
v___y_3739_ = v___y_3826_;
v___y_3740_ = v___y_3827_;
v___y_3741_ = v___y_3828_;
v___y_3742_ = v___y_3829_;
goto v___jp_3736_;
}
else
{
uint8_t v___x_3831_; 
v___x_3831_ = l_Lean_Expr_hasFVar(v___x_3735_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; 
lean_inc_ref(v___x_3735_);
v___x_3832_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3735_, v___y_3827_);
if (lean_obj_tag(v___x_3832_) == 0)
{
lean_object* v_a_3833_; uint8_t v___x_3834_; 
v_a_3833_ = lean_ctor_get(v___x_3832_, 0);
lean_inc(v_a_3833_);
lean_dec_ref_known(v___x_3832_, 1);
v___x_3834_ = l_Lean_Expr_hasMVar(v_a_3833_);
if (v___x_3834_ == 0)
{
uint8_t v___x_3835_; 
v___x_3835_ = l_Lean_Expr_hasFVar(v_a_3833_);
lean_dec(v_a_3833_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; 
lean_inc_ref(v___x_3735_);
v___x_3836_ = l_Lean_Meta_mkDecide(v___x_3735_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3838_; uint8_t v_transparency_3839_; uint8_t v___x_3840_; uint8_t v___x_3841_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3837_);
lean_dec_ref_known(v___x_3836_, 1);
v___x_3838_ = l_Lean_Meta_Context_config(v___y_3826_);
v_transparency_3839_ = lean_ctor_get_uint8(v___x_3838_, 9);
lean_dec_ref(v___x_3838_);
v___x_3840_ = 1;
v___x_3841_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3839_, v___x_3840_);
if (v___x_3841_ == 0)
{
lean_object* v_keyedConfig_3842_; uint8_t v_trackZetaDelta_3843_; lean_object* v_zetaDeltaSet_3844_; lean_object* v_lctx_3845_; lean_object* v_localInstances_3846_; lean_object* v_defEqCtx_x3f_3847_; lean_object* v_synthPendingDepth_3848_; lean_object* v_customCanUnfoldPredicate_x3f_3849_; uint8_t v_univApprox_3850_; uint8_t v_inTypeClassResolution_3851_; uint8_t v_cacheInferType_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; 
v_keyedConfig_3842_ = lean_ctor_get(v___y_3826_, 0);
v_trackZetaDelta_3843_ = lean_ctor_get_uint8(v___y_3826_, sizeof(void*)*7);
v_zetaDeltaSet_3844_ = lean_ctor_get(v___y_3826_, 1);
v_lctx_3845_ = lean_ctor_get(v___y_3826_, 2);
v_localInstances_3846_ = lean_ctor_get(v___y_3826_, 3);
v_defEqCtx_x3f_3847_ = lean_ctor_get(v___y_3826_, 4);
v_synthPendingDepth_3848_ = lean_ctor_get(v___y_3826_, 5);
v_customCanUnfoldPredicate_x3f_3849_ = lean_ctor_get(v___y_3826_, 6);
v_univApprox_3850_ = lean_ctor_get_uint8(v___y_3826_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3851_ = lean_ctor_get_uint8(v___y_3826_, sizeof(void*)*7 + 2);
v_cacheInferType_3852_ = lean_ctor_get_uint8(v___y_3826_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3842_);
v___x_3853_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3840_, v_keyedConfig_3842_);
lean_inc(v_customCanUnfoldPredicate_x3f_3849_);
lean_inc(v_synthPendingDepth_3848_);
lean_inc(v_defEqCtx_x3f_3847_);
lean_inc_ref(v_localInstances_3846_);
lean_inc_ref(v_lctx_3845_);
lean_inc(v_zetaDeltaSet_3844_);
v___x_3854_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3854_, 0, v___x_3853_);
lean_ctor_set(v___x_3854_, 1, v_zetaDeltaSet_3844_);
lean_ctor_set(v___x_3854_, 2, v_lctx_3845_);
lean_ctor_set(v___x_3854_, 3, v_localInstances_3846_);
lean_ctor_set(v___x_3854_, 4, v_defEqCtx_x3f_3847_);
lean_ctor_set(v___x_3854_, 5, v_synthPendingDepth_3848_);
lean_ctor_set(v___x_3854_, 6, v_customCanUnfoldPredicate_x3f_3849_);
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*7, v_trackZetaDelta_3843_);
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*7 + 1, v_univApprox_3850_);
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3851_);
lean_ctor_set_uint8(v___x_3854_, sizeof(void*)*7 + 3, v_cacheInferType_3852_);
lean_inc(v___y_3829_);
lean_inc_ref(v___y_3828_);
lean_inc(v___y_3827_);
lean_inc(v_a_3837_);
v___x_3855_ = lean_whnf(v_a_3837_, v___x_3854_, v___y_3827_, v___y_3828_, v___y_3829_);
v___y_3773_ = v___y_3829_;
v___y_3774_ = v___y_3826_;
v___y_3775_ = v___y_3827_;
v___y_3776_ = v_isHEq_3825_;
v___y_3777_ = v___y_3824_;
v___y_3778_ = v_a_3837_;
v___y_3779_ = v___y_3828_;
v___y_3780_ = v___x_3855_;
goto v___jp_3772_;
}
else
{
lean_object* v___x_3856_; 
lean_inc(v___y_3829_);
lean_inc_ref(v___y_3828_);
lean_inc(v___y_3827_);
lean_inc_ref(v___y_3826_);
lean_inc(v_a_3837_);
v___x_3856_ = lean_whnf(v_a_3837_, v___y_3826_, v___y_3827_, v___y_3828_, v___y_3829_);
v___y_3773_ = v___y_3829_;
v___y_3774_ = v___y_3826_;
v___y_3775_ = v___y_3827_;
v___y_3776_ = v_isHEq_3825_;
v___y_3777_ = v___y_3824_;
v___y_3778_ = v_a_3837_;
v___y_3779_ = v___y_3828_;
v___y_3780_ = v___x_3856_;
goto v___jp_3772_;
}
}
else
{
lean_object* v_a_3857_; 
v_a_3857_ = lean_ctor_get(v___x_3836_, 0);
lean_inc(v_a_3857_);
lean_dec_ref_known(v___x_3836_, 1);
v___y_3761_ = v___y_3829_;
v___y_3762_ = v___y_3826_;
v___y_3763_ = v___y_3827_;
v___y_3764_ = v_isHEq_3825_;
v___y_3765_ = v___y_3824_;
v___y_3766_ = v___y_3828_;
v_a_3767_ = v_a_3857_;
goto v___jp_3760_;
}
}
else
{
v___y_3737_ = v_isHEq_3825_;
v___y_3738_ = v___y_3824_;
v___y_3739_ = v___y_3826_;
v___y_3740_ = v___y_3827_;
v___y_3741_ = v___y_3828_;
v___y_3742_ = v___y_3829_;
goto v___jp_3736_;
}
}
else
{
lean_dec(v_a_3833_);
v___y_3737_ = v_isHEq_3825_;
v___y_3738_ = v___y_3824_;
v___y_3739_ = v___y_3826_;
v___y_3740_ = v___y_3827_;
v___y_3741_ = v___y_3828_;
v___y_3742_ = v___y_3829_;
goto v___jp_3736_;
}
}
else
{
lean_object* v_a_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_3865_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_3858_ = lean_ctor_get(v___x_3832_, 0);
v_isSharedCheck_3865_ = !lean_is_exclusive(v___x_3832_);
if (v_isSharedCheck_3865_ == 0)
{
v___x_3860_ = v___x_3832_;
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_a_3858_);
lean_dec(v___x_3832_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_3865_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3863_; 
if (v_isShared_3861_ == 0)
{
v___x_3863_ = v___x_3860_;
goto v_reusejp_3862_;
}
else
{
lean_object* v_reuseFailAlloc_3864_; 
v_reuseFailAlloc_3864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3864_, 0, v_a_3858_);
v___x_3863_ = v_reuseFailAlloc_3864_;
goto v_reusejp_3862_;
}
v_reusejp_3862_:
{
return v___x_3863_;
}
}
}
}
else
{
v___y_3737_ = v_isHEq_3825_;
v___y_3738_ = v___y_3824_;
v___y_3739_ = v___y_3826_;
v___y_3740_ = v___y_3827_;
v___y_3741_ = v___y_3828_;
v___y_3742_ = v___y_3829_;
goto v___jp_3736_;
}
}
}
v___jp_3866_:
{
lean_object* v___x_3872_; 
lean_inc_ref(v___x_3735_);
v___x_3872_ = l_Lean_Meta_matchHEq_x3f(v___x_3735_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v_a_3873_; 
v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
lean_inc(v_a_3873_);
lean_dec_ref_known(v___x_3872_, 1);
if (lean_obj_tag(v_a_3873_) == 1)
{
lean_object* v_val_3874_; lean_object* v_snd_3875_; lean_object* v_snd_3876_; lean_object* v_fst_3877_; lean_object* v_fst_3878_; lean_object* v_fst_3879_; lean_object* v_snd_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3980_; 
v_val_3874_ = lean_ctor_get(v_a_3873_, 0);
lean_inc(v_val_3874_);
lean_dec_ref_known(v_a_3873_, 1);
v_snd_3875_ = lean_ctor_get(v_val_3874_, 1);
lean_inc(v_snd_3875_);
v_snd_3876_ = lean_ctor_get(v_snd_3875_, 1);
lean_inc(v_snd_3876_);
v_fst_3877_ = lean_ctor_get(v_val_3874_, 0);
lean_inc(v_fst_3877_);
lean_dec(v_val_3874_);
v_fst_3878_ = lean_ctor_get(v_snd_3875_, 0);
lean_inc(v_fst_3878_);
lean_dec(v_snd_3875_);
v_fst_3879_ = lean_ctor_get(v_snd_3876_, 0);
v_snd_3880_ = lean_ctor_get(v_snd_3876_, 1);
v_isSharedCheck_3980_ = !lean_is_exclusive(v_snd_3876_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3882_ = v_snd_3876_;
v_isShared_3883_ = v_isSharedCheck_3980_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_snd_3880_);
lean_inc(v_fst_3879_);
lean_dec(v_snd_3876_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3980_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3884_; 
v___x_3884_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3878_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3884_) == 0)
{
lean_object* v_a_3885_; 
v_a_3885_ = lean_ctor_get(v___x_3884_, 0);
lean_inc(v_a_3885_);
lean_dec_ref_known(v___x_3884_, 1);
if (lean_obj_tag(v_a_3885_) == 1)
{
lean_object* v_val_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3971_; 
v_val_3886_ = lean_ctor_get(v_a_3885_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v_a_3885_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3888_ = v_a_3885_;
v_isShared_3889_ = v_isSharedCheck_3971_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_val_3886_);
lean_dec(v_a_3885_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3971_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3890_; 
v___x_3890_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3880_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3890_) == 0)
{
lean_object* v_a_3891_; 
v_a_3891_ = lean_ctor_get(v___x_3890_, 0);
lean_inc(v_a_3891_);
lean_dec_ref_known(v___x_3890_, 1);
if (lean_obj_tag(v_a_3891_) == 1)
{
lean_object* v_toConstantVal_3892_; lean_object* v_val_3893_; lean_object* v___x_3895_; uint8_t v_isShared_3896_; uint8_t v_isSharedCheck_3962_; 
v_toConstantVal_3892_ = lean_ctor_get(v_val_3886_, 0);
lean_inc_ref(v_toConstantVal_3892_);
lean_dec(v_val_3886_);
v_val_3893_ = lean_ctor_get(v_a_3891_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v_a_3891_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3895_ = v_a_3891_;
v_isShared_3896_ = v_isSharedCheck_3962_;
goto v_resetjp_3894_;
}
else
{
lean_inc(v_val_3893_);
lean_dec(v_a_3891_);
v___x_3895_ = lean_box(0);
v_isShared_3896_ = v_isSharedCheck_3962_;
goto v_resetjp_3894_;
}
v_resetjp_3894_:
{
lean_object* v_toConstantVal_3897_; lean_object* v_name_3898_; lean_object* v_name_3899_; uint8_t v___x_3900_; 
v_toConstantVal_3897_ = lean_ctor_get(v_val_3893_, 0);
lean_inc_ref(v_toConstantVal_3897_);
lean_dec(v_val_3893_);
v_name_3898_ = lean_ctor_get(v_toConstantVal_3892_, 0);
lean_inc(v_name_3898_);
lean_dec_ref(v_toConstantVal_3892_);
v_name_3899_ = lean_ctor_get(v_toConstantVal_3897_, 0);
lean_inc(v_name_3899_);
lean_dec_ref(v_toConstantVal_3897_);
v___x_3900_ = lean_name_eq(v_name_3898_, v_name_3899_);
lean_dec(v_name_3899_);
lean_dec(v_name_3898_);
if (v___x_3900_ == 0)
{
lean_object* v___x_3901_; 
v___x_3901_ = l_Lean_Meta_isExprDefEq(v_fst_3877_, v_fst_3879_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v_a_3902_; uint8_t v___x_3903_; 
v_a_3902_ = lean_ctor_get(v___x_3901_, 0);
lean_inc(v_a_3902_);
lean_dec_ref_known(v___x_3901_, 1);
v___x_3903_ = lean_unbox(v_a_3902_);
lean_dec(v_a_3902_);
if (v___x_3903_ == 0)
{
lean_del_object(v___x_3895_);
lean_del_object(v___x_3888_);
lean_del_object(v___x_3882_);
v___y_3824_ = v_isEq_3867_;
v_isHEq_3825_ = v___x_3680_;
v___y_3826_ = v___y_3868_;
v___y_3827_ = v___y_3869_;
v___y_3828_ = v___y_3870_;
v___y_3829_ = v___y_3871_;
goto v___jp_3823_;
}
else
{
lean_object* v___x_3904_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec_ref(v_config_3669_);
lean_inc(v_mvarId_3670_);
v___x_3904_ = l_Lean_MVarId_getType(v_mvarId_3670_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3904_) == 0)
{
lean_object* v_a_3905_; lean_object* v___x_3906_; lean_object* v___x_3907_; 
v_a_3905_ = lean_ctor_get(v___x_3904_, 0);
lean_inc(v_a_3905_);
lean_dec_ref_known(v___x_3904_, 1);
v___x_3906_ = l_Lean_LocalDecl_toExpr(v_val_3701_);
v___x_3907_ = l_Lean_Meta_mkEqOfHEq(v___x_3906_, v___x_3680_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___x_3909_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v___x_3909_ = l_Lean_Meta_mkNoConfusion(v_a_3905_, v_a_3908_, v___y_3868_, v___y_3869_, v___y_3870_, v___y_3871_);
if (lean_obj_tag(v___x_3909_) == 0)
{
lean_object* v_a_3910_; lean_object* v___x_3911_; 
v_a_3910_ = lean_ctor_get(v___x_3909_, 0);
lean_inc(v_a_3910_);
lean_dec_ref_known(v___x_3909_, 1);
v___x_3911_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3670_, v_a_3910_, v___y_3869_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v___x_3912_; lean_object* v___x_3914_; 
lean_dec_ref_known(v___x_3911_, 1);
v___x_3912_ = lean_box(v___x_3680_);
if (v_isShared_3896_ == 0)
{
lean_ctor_set(v___x_3895_, 0, v___x_3912_);
v___x_3914_ = v___x_3895_;
goto v_reusejp_3913_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3912_);
v___x_3914_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3913_;
}
v_reusejp_3913_:
{
lean_object* v___x_3916_; 
if (v_isShared_3883_ == 0)
{
lean_ctor_set(v___x_3882_, 1, v___x_3705_);
lean_ctor_set(v___x_3882_, 0, v___x_3914_);
v___x_3916_ = v___x_3882_;
goto v_reusejp_3915_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3914_);
lean_ctor_set(v_reuseFailAlloc_3920_, 1, v___x_3705_);
v___x_3916_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3915_;
}
v_reusejp_3915_:
{
lean_object* v___x_3918_; 
if (v_isShared_3889_ == 0)
{
lean_ctor_set_tag(v___x_3888_, 0);
lean_ctor_set(v___x_3888_, 0, v___x_3916_);
v___x_3918_ = v___x_3888_;
goto v_reusejp_3917_;
}
else
{
lean_object* v_reuseFailAlloc_3919_; 
v_reuseFailAlloc_3919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3919_, 0, v___x_3916_);
v___x_3918_ = v_reuseFailAlloc_3919_;
goto v_reusejp_3917_;
}
v_reusejp_3917_:
{
v_a_3687_ = v___x_3918_;
goto v___jp_3686_;
}
}
}
}
else
{
lean_object* v_a_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3929_; 
lean_del_object(v___x_3895_);
lean_del_object(v___x_3888_);
lean_del_object(v___x_3882_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
v_a_3922_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3929_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3929_ == 0)
{
v___x_3924_ = v___x_3911_;
v_isShared_3925_ = v_isSharedCheck_3929_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_a_3922_);
lean_dec(v___x_3911_);
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
else
{
lean_object* v_a_3930_; lean_object* v___x_3932_; uint8_t v_isShared_3933_; uint8_t v_isSharedCheck_3937_; 
lean_del_object(v___x_3895_);
lean_del_object(v___x_3888_);
lean_del_object(v___x_3882_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_3930_ = lean_ctor_get(v___x_3909_, 0);
v_isSharedCheck_3937_ = !lean_is_exclusive(v___x_3909_);
if (v_isSharedCheck_3937_ == 0)
{
v___x_3932_ = v___x_3909_;
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
else
{
lean_inc(v_a_3930_);
lean_dec(v___x_3909_);
v___x_3932_ = lean_box(0);
v_isShared_3933_ = v_isSharedCheck_3937_;
goto v_resetjp_3931_;
}
v_resetjp_3931_:
{
lean_object* v___x_3935_; 
if (v_isShared_3933_ == 0)
{
v___x_3935_ = v___x_3932_;
goto v_reusejp_3934_;
}
else
{
lean_object* v_reuseFailAlloc_3936_; 
v_reuseFailAlloc_3936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3936_, 0, v_a_3930_);
v___x_3935_ = v_reuseFailAlloc_3936_;
goto v_reusejp_3934_;
}
v_reusejp_3934_:
{
return v___x_3935_;
}
}
}
}
else
{
lean_object* v_a_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3945_; 
lean_dec(v_a_3905_);
lean_del_object(v___x_3895_);
lean_del_object(v___x_3888_);
lean_del_object(v___x_3882_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_3938_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3945_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3945_ == 0)
{
v___x_3940_ = v___x_3907_;
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_a_3938_);
lean_dec(v___x_3907_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3945_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3943_; 
if (v_isShared_3941_ == 0)
{
v___x_3943_ = v___x_3940_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3944_; 
v_reuseFailAlloc_3944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3938_);
v___x_3943_ = v_reuseFailAlloc_3944_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
return v___x_3943_;
}
}
}
}
else
{
lean_object* v_a_3946_; lean_object* v___x_3948_; uint8_t v_isShared_3949_; uint8_t v_isSharedCheck_3953_; 
lean_del_object(v___x_3895_);
lean_del_object(v___x_3888_);
lean_del_object(v___x_3882_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_3946_ = lean_ctor_get(v___x_3904_, 0);
v_isSharedCheck_3953_ = !lean_is_exclusive(v___x_3904_);
if (v_isSharedCheck_3953_ == 0)
{
v___x_3948_ = v___x_3904_;
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
else
{
lean_inc(v_a_3946_);
lean_dec(v___x_3904_);
v___x_3948_ = lean_box(0);
v_isShared_3949_ = v_isSharedCheck_3953_;
goto v_resetjp_3947_;
}
v_resetjp_3947_:
{
lean_object* v___x_3951_; 
if (v_isShared_3949_ == 0)
{
v___x_3951_ = v___x_3948_;
goto v_reusejp_3950_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v_a_3946_);
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
lean_object* v_a_3954_; lean_object* v___x_3956_; uint8_t v_isShared_3957_; uint8_t v_isSharedCheck_3961_; 
lean_del_object(v___x_3895_);
lean_del_object(v___x_3888_);
lean_del_object(v___x_3882_);
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_3954_ = lean_ctor_get(v___x_3901_, 0);
v_isSharedCheck_3961_ = !lean_is_exclusive(v___x_3901_);
if (v_isSharedCheck_3961_ == 0)
{
v___x_3956_ = v___x_3901_;
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
else
{
lean_inc(v_a_3954_);
lean_dec(v___x_3901_);
v___x_3956_ = lean_box(0);
v_isShared_3957_ = v_isSharedCheck_3961_;
goto v_resetjp_3955_;
}
v_resetjp_3955_:
{
lean_object* v___x_3959_; 
if (v_isShared_3957_ == 0)
{
v___x_3959_ = v___x_3956_;
goto v_reusejp_3958_;
}
else
{
lean_object* v_reuseFailAlloc_3960_; 
v_reuseFailAlloc_3960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_a_3954_);
v___x_3959_ = v_reuseFailAlloc_3960_;
goto v_reusejp_3958_;
}
v_reusejp_3958_:
{
return v___x_3959_;
}
}
}
}
else
{
lean_del_object(v___x_3895_);
lean_del_object(v___x_3888_);
lean_del_object(v___x_3882_);
lean_dec(v_fst_3879_);
lean_dec(v_fst_3877_);
v___y_3824_ = v_isEq_3867_;
v_isHEq_3825_ = v___x_3680_;
v___y_3826_ = v___y_3868_;
v___y_3827_ = v___y_3869_;
v___y_3828_ = v___y_3870_;
v___y_3829_ = v___y_3871_;
goto v___jp_3823_;
}
}
}
else
{
lean_dec(v_a_3891_);
lean_del_object(v___x_3888_);
lean_dec(v_val_3886_);
lean_del_object(v___x_3882_);
lean_dec(v_fst_3879_);
lean_dec(v_fst_3877_);
v___y_3824_ = v_isEq_3867_;
v_isHEq_3825_ = v___x_3680_;
v___y_3826_ = v___y_3868_;
v___y_3827_ = v___y_3869_;
v___y_3828_ = v___y_3870_;
v___y_3829_ = v___y_3871_;
goto v___jp_3823_;
}
}
else
{
lean_object* v_a_3963_; lean_object* v___x_3965_; uint8_t v_isShared_3966_; uint8_t v_isSharedCheck_3970_; 
lean_del_object(v___x_3888_);
lean_dec(v_val_3886_);
lean_del_object(v___x_3882_);
lean_dec(v_fst_3879_);
lean_dec(v_fst_3877_);
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_3963_ = lean_ctor_get(v___x_3890_, 0);
v_isSharedCheck_3970_ = !lean_is_exclusive(v___x_3890_);
if (v_isSharedCheck_3970_ == 0)
{
v___x_3965_ = v___x_3890_;
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
else
{
lean_inc(v_a_3963_);
lean_dec(v___x_3890_);
v___x_3965_ = lean_box(0);
v_isShared_3966_ = v_isSharedCheck_3970_;
goto v_resetjp_3964_;
}
v_resetjp_3964_:
{
lean_object* v___x_3968_; 
if (v_isShared_3966_ == 0)
{
v___x_3968_ = v___x_3965_;
goto v_reusejp_3967_;
}
else
{
lean_object* v_reuseFailAlloc_3969_; 
v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
v___x_3968_ = v_reuseFailAlloc_3969_;
goto v_reusejp_3967_;
}
v_reusejp_3967_:
{
return v___x_3968_;
}
}
}
}
}
else
{
lean_dec(v_a_3885_);
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_fst_3879_);
lean_dec(v_fst_3877_);
v___y_3824_ = v_isEq_3867_;
v_isHEq_3825_ = v___x_3680_;
v___y_3826_ = v___y_3868_;
v___y_3827_ = v___y_3869_;
v___y_3828_ = v___y_3870_;
v___y_3829_ = v___y_3871_;
goto v___jp_3823_;
}
}
else
{
lean_object* v_a_3972_; lean_object* v___x_3974_; uint8_t v_isShared_3975_; uint8_t v_isSharedCheck_3979_; 
lean_del_object(v___x_3882_);
lean_dec(v_snd_3880_);
lean_dec(v_fst_3879_);
lean_dec(v_fst_3877_);
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_3972_ = lean_ctor_get(v___x_3884_, 0);
v_isSharedCheck_3979_ = !lean_is_exclusive(v___x_3884_);
if (v_isSharedCheck_3979_ == 0)
{
v___x_3974_ = v___x_3884_;
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
else
{
lean_inc(v_a_3972_);
lean_dec(v___x_3884_);
v___x_3974_ = lean_box(0);
v_isShared_3975_ = v_isSharedCheck_3979_;
goto v_resetjp_3973_;
}
v_resetjp_3973_:
{
lean_object* v___x_3977_; 
if (v_isShared_3975_ == 0)
{
v___x_3977_ = v___x_3974_;
goto v_reusejp_3976_;
}
else
{
lean_object* v_reuseFailAlloc_3978_; 
v_reuseFailAlloc_3978_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3978_, 0, v_a_3972_);
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
lean_dec(v_a_3873_);
v___y_3824_ = v_isEq_3867_;
v_isHEq_3825_ = v___x_3734_;
v___y_3826_ = v___y_3868_;
v___y_3827_ = v___y_3869_;
v___y_3828_ = v___y_3870_;
v___y_3829_ = v___y_3871_;
goto v___jp_3823_;
}
}
else
{
lean_object* v_a_3981_; lean_object* v___x_3983_; uint8_t v_isShared_3984_; uint8_t v_isSharedCheck_3988_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_3981_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3988_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3988_ == 0)
{
v___x_3983_ = v___x_3872_;
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
else
{
lean_inc(v_a_3981_);
lean_dec(v___x_3872_);
v___x_3983_ = lean_box(0);
v_isShared_3984_ = v_isSharedCheck_3988_;
goto v_resetjp_3982_;
}
v_resetjp_3982_:
{
lean_object* v___x_3986_; 
if (v_isShared_3984_ == 0)
{
v___x_3986_ = v___x_3983_;
goto v_reusejp_3985_;
}
else
{
lean_object* v_reuseFailAlloc_3987_; 
v_reuseFailAlloc_3987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3987_, 0, v_a_3981_);
v___x_3986_ = v_reuseFailAlloc_3987_;
goto v_reusejp_3985_;
}
v_reusejp_3985_:
{
return v___x_3986_;
}
}
}
}
v___jp_3989_:
{
lean_object* v___x_3994_; 
lean_inc_ref(v___x_3735_);
v___x_3994_ = l_Lean_Meta_matchEq_x3f(v___x_3735_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_3994_) == 0)
{
lean_object* v_a_3995_; 
v_a_3995_ = lean_ctor_get(v___x_3994_, 0);
lean_inc(v_a_3995_);
lean_dec_ref_known(v___x_3994_, 1);
if (lean_obj_tag(v_a_3995_) == 1)
{
lean_object* v_val_3996_; lean_object* v_snd_3997_; lean_object* v_fst_3998_; lean_object* v_snd_3999_; lean_object* v___x_4001_; uint8_t v_isShared_4002_; uint8_t v_isSharedCheck_4078_; 
v_val_3996_ = lean_ctor_get(v_a_3995_, 0);
lean_inc(v_val_3996_);
lean_dec_ref_known(v_a_3995_, 1);
v_snd_3997_ = lean_ctor_get(v_val_3996_, 1);
lean_inc(v_snd_3997_);
lean_dec(v_val_3996_);
v_fst_3998_ = lean_ctor_get(v_snd_3997_, 0);
v_snd_3999_ = lean_ctor_get(v_snd_3997_, 1);
v_isSharedCheck_4078_ = !lean_is_exclusive(v_snd_3997_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4001_ = v_snd_3997_;
v_isShared_4002_ = v_isSharedCheck_4078_;
goto v_resetjp_4000_;
}
else
{
lean_inc(v_snd_3999_);
lean_inc(v_fst_3998_);
lean_dec(v_snd_3997_);
v___x_4001_ = lean_box(0);
v_isShared_4002_ = v_isSharedCheck_4078_;
goto v_resetjp_4000_;
}
v_resetjp_4000_:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3998_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_4003_) == 0)
{
lean_object* v_a_4004_; 
v_a_4004_ = lean_ctor_get(v___x_4003_, 0);
lean_inc(v_a_4004_);
lean_dec_ref_known(v___x_4003_, 1);
if (lean_obj_tag(v_a_4004_) == 1)
{
lean_object* v_val_4005_; lean_object* v___x_4007_; uint8_t v_isShared_4008_; uint8_t v_isSharedCheck_4069_; 
v_val_4005_ = lean_ctor_get(v_a_4004_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v_a_4004_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4007_ = v_a_4004_;
v_isShared_4008_ = v_isSharedCheck_4069_;
goto v_resetjp_4006_;
}
else
{
lean_inc(v_val_4005_);
lean_dec(v_a_4004_);
v___x_4007_ = lean_box(0);
v_isShared_4008_ = v_isSharedCheck_4069_;
goto v_resetjp_4006_;
}
v_resetjp_4006_:
{
lean_object* v___x_4009_; 
v___x_4009_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3999_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
if (lean_obj_tag(v_a_4010_) == 1)
{
lean_object* v_toConstantVal_4011_; lean_object* v_val_4012_; lean_object* v___x_4014_; uint8_t v_isShared_4015_; uint8_t v_isSharedCheck_4060_; 
v_toConstantVal_4011_ = lean_ctor_get(v_val_4005_, 0);
lean_inc_ref(v_toConstantVal_4011_);
lean_dec(v_val_4005_);
v_val_4012_ = lean_ctor_get(v_a_4010_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v_a_4010_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4014_ = v_a_4010_;
v_isShared_4015_ = v_isSharedCheck_4060_;
goto v_resetjp_4013_;
}
else
{
lean_inc(v_val_4012_);
lean_dec(v_a_4010_);
v___x_4014_ = lean_box(0);
v_isShared_4015_ = v_isSharedCheck_4060_;
goto v_resetjp_4013_;
}
v_resetjp_4013_:
{
lean_object* v_toConstantVal_4016_; lean_object* v_name_4017_; lean_object* v_name_4018_; uint8_t v___x_4019_; 
v_toConstantVal_4016_ = lean_ctor_get(v_val_4012_, 0);
lean_inc_ref(v_toConstantVal_4016_);
lean_dec(v_val_4012_);
v_name_4017_ = lean_ctor_get(v_toConstantVal_4011_, 0);
lean_inc(v_name_4017_);
lean_dec_ref(v_toConstantVal_4011_);
v_name_4018_ = lean_ctor_get(v_toConstantVal_4016_, 0);
lean_inc(v_name_4018_);
lean_dec_ref(v_toConstantVal_4016_);
v___x_4019_ = lean_name_eq(v_name_4017_, v_name_4018_);
lean_dec(v_name_4018_);
lean_dec(v_name_4017_);
if (v___x_4019_ == 0)
{
lean_object* v___x_4020_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec_ref(v_config_3669_);
lean_inc(v_mvarId_3670_);
v___x_4020_ = l_Lean_MVarId_getType(v_mvarId_3670_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_4020_) == 0)
{
lean_object* v_a_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v_a_4021_ = lean_ctor_get(v___x_4020_, 0);
lean_inc(v_a_4021_);
lean_dec_ref_known(v___x_4020_, 1);
v___x_4022_ = l_Lean_LocalDecl_toExpr(v_val_3701_);
v___x_4023_ = l_Lean_Meta_mkNoConfusion(v_a_4021_, v___x_4022_, v___y_3990_, v___y_3991_, v___y_3992_, v___y_3993_);
if (lean_obj_tag(v___x_4023_) == 0)
{
lean_object* v_a_4024_; lean_object* v___x_4025_; 
v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc(v_a_4024_);
lean_dec_ref_known(v___x_4023_, 1);
v___x_4025_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3670_, v_a_4024_, v___y_3991_);
if (lean_obj_tag(v___x_4025_) == 0)
{
lean_object* v___x_4026_; lean_object* v___x_4028_; 
lean_dec_ref_known(v___x_4025_, 1);
v___x_4026_ = lean_box(v___x_3680_);
if (v_isShared_4015_ == 0)
{
lean_ctor_set(v___x_4014_, 0, v___x_4026_);
v___x_4028_ = v___x_4014_;
goto v_reusejp_4027_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4026_);
v___x_4028_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4027_;
}
v_reusejp_4027_:
{
lean_object* v___x_4030_; 
if (v_isShared_4002_ == 0)
{
lean_ctor_set(v___x_4001_, 1, v___x_3705_);
lean_ctor_set(v___x_4001_, 0, v___x_4028_);
v___x_4030_ = v___x_4001_;
goto v_reusejp_4029_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4028_);
lean_ctor_set(v_reuseFailAlloc_4034_, 1, v___x_3705_);
v___x_4030_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4029_;
}
v_reusejp_4029_:
{
lean_object* v___x_4032_; 
if (v_isShared_4008_ == 0)
{
lean_ctor_set_tag(v___x_4007_, 0);
lean_ctor_set(v___x_4007_, 0, v___x_4030_);
v___x_4032_ = v___x_4007_;
goto v_reusejp_4031_;
}
else
{
lean_object* v_reuseFailAlloc_4033_; 
v_reuseFailAlloc_4033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4033_, 0, v___x_4030_);
v___x_4032_ = v_reuseFailAlloc_4033_;
goto v_reusejp_4031_;
}
v_reusejp_4031_:
{
v_a_3687_ = v___x_4032_;
goto v___jp_3686_;
}
}
}
}
else
{
lean_object* v_a_4036_; lean_object* v___x_4038_; uint8_t v_isShared_4039_; uint8_t v_isSharedCheck_4043_; 
lean_del_object(v___x_4014_);
lean_del_object(v___x_4007_);
lean_del_object(v___x_4001_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
v_a_4036_ = lean_ctor_get(v___x_4025_, 0);
v_isSharedCheck_4043_ = !lean_is_exclusive(v___x_4025_);
if (v_isSharedCheck_4043_ == 0)
{
v___x_4038_ = v___x_4025_;
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
else
{
lean_inc(v_a_4036_);
lean_dec(v___x_4025_);
v___x_4038_ = lean_box(0);
v_isShared_4039_ = v_isSharedCheck_4043_;
goto v_resetjp_4037_;
}
v_resetjp_4037_:
{
lean_object* v___x_4041_; 
if (v_isShared_4039_ == 0)
{
v___x_4041_ = v___x_4038_;
goto v_reusejp_4040_;
}
else
{
lean_object* v_reuseFailAlloc_4042_; 
v_reuseFailAlloc_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4042_, 0, v_a_4036_);
v___x_4041_ = v_reuseFailAlloc_4042_;
goto v_reusejp_4040_;
}
v_reusejp_4040_:
{
return v___x_4041_;
}
}
}
}
else
{
lean_object* v_a_4044_; lean_object* v___x_4046_; uint8_t v_isShared_4047_; uint8_t v_isSharedCheck_4051_; 
lean_del_object(v___x_4014_);
lean_del_object(v___x_4007_);
lean_del_object(v___x_4001_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_4044_ = lean_ctor_get(v___x_4023_, 0);
v_isSharedCheck_4051_ = !lean_is_exclusive(v___x_4023_);
if (v_isSharedCheck_4051_ == 0)
{
v___x_4046_ = v___x_4023_;
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
else
{
lean_inc(v_a_4044_);
lean_dec(v___x_4023_);
v___x_4046_ = lean_box(0);
v_isShared_4047_ = v_isSharedCheck_4051_;
goto v_resetjp_4045_;
}
v_resetjp_4045_:
{
lean_object* v___x_4049_; 
if (v_isShared_4047_ == 0)
{
v___x_4049_ = v___x_4046_;
goto v_reusejp_4048_;
}
else
{
lean_object* v_reuseFailAlloc_4050_; 
v_reuseFailAlloc_4050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4050_, 0, v_a_4044_);
v___x_4049_ = v_reuseFailAlloc_4050_;
goto v_reusejp_4048_;
}
v_reusejp_4048_:
{
return v___x_4049_;
}
}
}
}
else
{
lean_object* v_a_4052_; lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4059_; 
lean_del_object(v___x_4014_);
lean_del_object(v___x_4007_);
lean_del_object(v___x_4001_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_4052_ = lean_ctor_get(v___x_4020_, 0);
v_isSharedCheck_4059_ = !lean_is_exclusive(v___x_4020_);
if (v_isSharedCheck_4059_ == 0)
{
v___x_4054_ = v___x_4020_;
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
else
{
lean_inc(v_a_4052_);
lean_dec(v___x_4020_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4059_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4057_; 
if (v_isShared_4055_ == 0)
{
v___x_4057_ = v___x_4054_;
goto v_reusejp_4056_;
}
else
{
lean_object* v_reuseFailAlloc_4058_; 
v_reuseFailAlloc_4058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4058_, 0, v_a_4052_);
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
lean_del_object(v___x_4014_);
lean_del_object(v___x_4007_);
lean_del_object(v___x_4001_);
v_isEq_3867_ = v___x_3680_;
v___y_3868_ = v___y_3990_;
v___y_3869_ = v___y_3991_;
v___y_3870_ = v___y_3992_;
v___y_3871_ = v___y_3993_;
goto v___jp_3866_;
}
}
}
else
{
lean_dec(v_a_4010_);
lean_del_object(v___x_4007_);
lean_dec(v_val_4005_);
lean_del_object(v___x_4001_);
v_isEq_3867_ = v___x_3680_;
v___y_3868_ = v___y_3990_;
v___y_3869_ = v___y_3991_;
v___y_3870_ = v___y_3992_;
v___y_3871_ = v___y_3993_;
goto v___jp_3866_;
}
}
else
{
lean_object* v_a_4061_; lean_object* v___x_4063_; uint8_t v_isShared_4064_; uint8_t v_isSharedCheck_4068_; 
lean_del_object(v___x_4007_);
lean_dec(v_val_4005_);
lean_del_object(v___x_4001_);
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_4061_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4063_ = v___x_4009_;
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
else
{
lean_inc(v_a_4061_);
lean_dec(v___x_4009_);
v___x_4063_ = lean_box(0);
v_isShared_4064_ = v_isSharedCheck_4068_;
goto v_resetjp_4062_;
}
v_resetjp_4062_:
{
lean_object* v___x_4066_; 
if (v_isShared_4064_ == 0)
{
v___x_4066_ = v___x_4063_;
goto v_reusejp_4065_;
}
else
{
lean_object* v_reuseFailAlloc_4067_; 
v_reuseFailAlloc_4067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4067_, 0, v_a_4061_);
v___x_4066_ = v_reuseFailAlloc_4067_;
goto v_reusejp_4065_;
}
v_reusejp_4065_:
{
return v___x_4066_;
}
}
}
}
}
else
{
lean_dec(v_a_4004_);
lean_del_object(v___x_4001_);
lean_dec(v_snd_3999_);
v_isEq_3867_ = v___x_3680_;
v___y_3868_ = v___y_3990_;
v___y_3869_ = v___y_3991_;
v___y_3870_ = v___y_3992_;
v___y_3871_ = v___y_3993_;
goto v___jp_3866_;
}
}
else
{
lean_object* v_a_4070_; lean_object* v___x_4072_; uint8_t v_isShared_4073_; uint8_t v_isSharedCheck_4077_; 
lean_del_object(v___x_4001_);
lean_dec(v_snd_3999_);
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_4070_ = lean_ctor_get(v___x_4003_, 0);
v_isSharedCheck_4077_ = !lean_is_exclusive(v___x_4003_);
if (v_isSharedCheck_4077_ == 0)
{
v___x_4072_ = v___x_4003_;
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
else
{
lean_inc(v_a_4070_);
lean_dec(v___x_4003_);
v___x_4072_ = lean_box(0);
v_isShared_4073_ = v_isSharedCheck_4077_;
goto v_resetjp_4071_;
}
v_resetjp_4071_:
{
lean_object* v___x_4075_; 
if (v_isShared_4073_ == 0)
{
v___x_4075_ = v___x_4072_;
goto v_reusejp_4074_;
}
else
{
lean_object* v_reuseFailAlloc_4076_; 
v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
v___x_4075_ = v_reuseFailAlloc_4076_;
goto v_reusejp_4074_;
}
v_reusejp_4074_:
{
return v___x_4075_;
}
}
}
}
}
else
{
lean_dec(v_a_3995_);
v_isEq_3867_ = v___x_3734_;
v___y_3868_ = v___y_3990_;
v___y_3869_ = v___y_3991_;
v___y_3870_ = v___y_3992_;
v___y_3871_ = v___y_3993_;
goto v___jp_3866_;
}
}
else
{
lean_object* v_a_4079_; lean_object* v___x_4081_; uint8_t v_isShared_4082_; uint8_t v_isSharedCheck_4086_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_4079_ = lean_ctor_get(v___x_3994_, 0);
v_isSharedCheck_4086_ = !lean_is_exclusive(v___x_3994_);
if (v_isSharedCheck_4086_ == 0)
{
v___x_4081_ = v___x_3994_;
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
else
{
lean_inc(v_a_4079_);
lean_dec(v___x_3994_);
v___x_4081_ = lean_box(0);
v_isShared_4082_ = v_isSharedCheck_4086_;
goto v_resetjp_4080_;
}
v_resetjp_4080_:
{
lean_object* v___x_4084_; 
if (v_isShared_4082_ == 0)
{
v___x_4084_ = v___x_4081_;
goto v_reusejp_4083_;
}
else
{
lean_object* v_reuseFailAlloc_4085_; 
v_reuseFailAlloc_4085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4085_, 0, v_a_4079_);
v___x_4084_ = v_reuseFailAlloc_4085_;
goto v_reusejp_4083_;
}
v_reusejp_4083_:
{
return v___x_4084_;
}
}
}
}
v___jp_4087_:
{
lean_object* v___x_4092_; 
lean_inc_ref(v___x_3735_);
v___x_4092_ = l_Lean_refutableHasNotBit_x3f(v___x_3735_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4092_) == 0)
{
lean_object* v_a_4093_; 
v_a_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc(v_a_4093_);
lean_dec_ref_known(v___x_4092_, 1);
if (lean_obj_tag(v_a_4093_) == 1)
{
lean_object* v_val_4094_; lean_object* v___x_4096_; uint8_t v_isShared_4097_; uint8_t v_isSharedCheck_4134_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec_ref(v_config_3669_);
v_val_4094_ = lean_ctor_get(v_a_4093_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v_a_4093_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4096_ = v_a_4093_;
v_isShared_4097_ = v_isSharedCheck_4134_;
goto v_resetjp_4095_;
}
else
{
lean_inc(v_val_4094_);
lean_dec(v_a_4093_);
v___x_4096_ = lean_box(0);
v_isShared_4097_ = v_isSharedCheck_4134_;
goto v_resetjp_4095_;
}
v_resetjp_4095_:
{
lean_object* v___x_4098_; 
lean_inc(v_mvarId_3670_);
v___x_4098_ = l_Lean_MVarId_getType(v_mvarId_3670_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4098_) == 0)
{
lean_object* v_a_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; 
v_a_4099_ = lean_ctor_get(v___x_4098_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4098_, 1);
v___x_4100_ = l_Lean_LocalDecl_toExpr(v_val_3701_);
v___x_4101_ = l_Lean_Meta_mkAbsurd(v_a_4099_, v_val_4094_, v___x_4100_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; lean_object* v___x_4103_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4101_, 1);
v___x_4103_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3670_, v_a_4102_, v___y_4089_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4106_; 
lean_dec_ref_known(v___x_4103_, 1);
v___x_4104_ = lean_box(v___x_3680_);
if (v_isShared_4097_ == 0)
{
lean_ctor_set(v___x_4096_, 0, v___x_4104_);
v___x_4106_ = v___x_4096_;
goto v_reusejp_4105_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v___x_4104_);
v___x_4106_ = v_reuseFailAlloc_4109_;
goto v_reusejp_4105_;
}
v_reusejp_4105_:
{
lean_object* v___x_4107_; lean_object* v___x_4108_; 
v___x_4107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
lean_ctor_set(v___x_4107_, 1, v___x_3705_);
v___x_4108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
v_a_3687_ = v___x_4108_;
goto v___jp_3686_;
}
}
else
{
lean_object* v_a_4110_; lean_object* v___x_4112_; uint8_t v_isShared_4113_; uint8_t v_isSharedCheck_4117_; 
lean_del_object(v___x_4096_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
v_a_4110_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4117_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4117_ == 0)
{
v___x_4112_ = v___x_4103_;
v_isShared_4113_ = v_isSharedCheck_4117_;
goto v_resetjp_4111_;
}
else
{
lean_inc(v_a_4110_);
lean_dec(v___x_4103_);
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
else
{
lean_object* v_a_4118_; lean_object* v___x_4120_; uint8_t v_isShared_4121_; uint8_t v_isSharedCheck_4125_; 
lean_del_object(v___x_4096_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_4118_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4125_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4125_ == 0)
{
v___x_4120_ = v___x_4101_;
v_isShared_4121_ = v_isSharedCheck_4125_;
goto v_resetjp_4119_;
}
else
{
lean_inc(v_a_4118_);
lean_dec(v___x_4101_);
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
else
{
lean_object* v_a_4126_; lean_object* v___x_4128_; uint8_t v_isShared_4129_; uint8_t v_isSharedCheck_4133_; 
lean_del_object(v___x_4096_);
lean_dec(v_val_4094_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_4126_ = lean_ctor_get(v___x_4098_, 0);
v_isSharedCheck_4133_ = !lean_is_exclusive(v___x_4098_);
if (v_isSharedCheck_4133_ == 0)
{
v___x_4128_ = v___x_4098_;
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
else
{
lean_inc(v_a_4126_);
lean_dec(v___x_4098_);
v___x_4128_ = lean_box(0);
v_isShared_4129_ = v_isSharedCheck_4133_;
goto v_resetjp_4127_;
}
v_resetjp_4127_:
{
lean_object* v___x_4131_; 
if (v_isShared_4129_ == 0)
{
v___x_4131_ = v___x_4128_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v_a_4126_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
}
}
}
else
{
lean_object* v___x_4135_; 
lean_dec(v_a_4093_);
lean_inc_ref(v___x_3735_);
v___x_4135_ = l_Lean_Meta_matchNe_x3f(v___x_3735_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4135_, 1);
if (lean_obj_tag(v_a_4136_) == 1)
{
lean_object* v_val_4137_; lean_object* v___x_4139_; uint8_t v_isShared_4140_; uint8_t v_isSharedCheck_4207_; 
v_val_4137_ = lean_ctor_get(v_a_4136_, 0);
v_isSharedCheck_4207_ = !lean_is_exclusive(v_a_4136_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4139_ = v_a_4136_;
v_isShared_4140_ = v_isSharedCheck_4207_;
goto v_resetjp_4138_;
}
else
{
lean_inc(v_val_4137_);
lean_dec(v_a_4136_);
v___x_4139_ = lean_box(0);
v_isShared_4140_ = v_isSharedCheck_4207_;
goto v_resetjp_4138_;
}
v_resetjp_4138_:
{
lean_object* v_snd_4141_; lean_object* v_fst_4142_; lean_object* v_snd_4143_; lean_object* v___x_4145_; uint8_t v_isShared_4146_; uint8_t v_isSharedCheck_4206_; 
v_snd_4141_ = lean_ctor_get(v_val_4137_, 1);
lean_inc(v_snd_4141_);
lean_dec(v_val_4137_);
v_fst_4142_ = lean_ctor_get(v_snd_4141_, 0);
v_snd_4143_ = lean_ctor_get(v_snd_4141_, 1);
v_isSharedCheck_4206_ = !lean_is_exclusive(v_snd_4141_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4145_ = v_snd_4141_;
v_isShared_4146_ = v_isSharedCheck_4206_;
goto v_resetjp_4144_;
}
else
{
lean_inc(v_snd_4143_);
lean_inc(v_fst_4142_);
lean_dec(v_snd_4141_);
v___x_4145_ = lean_box(0);
v_isShared_4146_ = v_isSharedCheck_4206_;
goto v_resetjp_4144_;
}
v_resetjp_4144_:
{
lean_object* v___x_4147_; 
lean_inc(v_fst_4142_);
v___x_4147_ = l_Lean_Meta_isExprDefEq(v_fst_4142_, v_snd_4143_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v_a_4148_; uint8_t v___x_4149_; 
v_a_4148_ = lean_ctor_get(v___x_4147_, 0);
lean_inc(v_a_4148_);
lean_dec_ref_known(v___x_4147_, 1);
v___x_4149_ = lean_unbox(v_a_4148_);
lean_dec(v_a_4148_);
if (v___x_4149_ == 0)
{
lean_del_object(v___x_4145_);
lean_dec(v_fst_4142_);
lean_del_object(v___x_4139_);
v___y_3990_ = v___y_4088_;
v___y_3991_ = v___y_4089_;
v___y_3992_ = v___y_4090_;
v___y_3993_ = v___y_4091_;
goto v___jp_3989_;
}
else
{
lean_object* v___x_4150_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec_ref(v_config_3669_);
lean_inc(v_mvarId_3670_);
v___x_4150_ = l_Lean_MVarId_getType(v_mvarId_3670_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4150_) == 0)
{
lean_object* v_a_4151_; lean_object* v___x_4152_; 
v_a_4151_ = lean_ctor_get(v___x_4150_, 0);
lean_inc(v_a_4151_);
lean_dec_ref_known(v___x_4150_, 1);
v___x_4152_ = l_Lean_Meta_mkEqRefl(v_fst_4142_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4152_) == 0)
{
lean_object* v_a_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; 
v_a_4153_ = lean_ctor_get(v___x_4152_, 0);
lean_inc(v_a_4153_);
lean_dec_ref_known(v___x_4152_, 1);
v___x_4154_ = l_Lean_LocalDecl_toExpr(v_val_3701_);
v___x_4155_ = l_Lean_Meta_mkAbsurd(v_a_4151_, v_a_4153_, v___x_4154_, v___y_4088_, v___y_4089_, v___y_4090_, v___y_4091_);
if (lean_obj_tag(v___x_4155_) == 0)
{
lean_object* v_a_4156_; lean_object* v___x_4157_; 
v_a_4156_ = lean_ctor_get(v___x_4155_, 0);
lean_inc(v_a_4156_);
lean_dec_ref_known(v___x_4155_, 1);
v___x_4157_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3670_, v_a_4156_, v___y_4089_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v___x_4158_; lean_object* v___x_4160_; 
lean_dec_ref_known(v___x_4157_, 1);
v___x_4158_ = lean_box(v___x_3680_);
if (v_isShared_4140_ == 0)
{
lean_ctor_set(v___x_4139_, 0, v___x_4158_);
v___x_4160_ = v___x_4139_;
goto v_reusejp_4159_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4158_);
v___x_4160_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4159_;
}
v_reusejp_4159_:
{
lean_object* v___x_4162_; 
if (v_isShared_4146_ == 0)
{
lean_ctor_set(v___x_4145_, 1, v___x_3705_);
lean_ctor_set(v___x_4145_, 0, v___x_4160_);
v___x_4162_ = v___x_4145_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4164_; 
v_reuseFailAlloc_4164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4164_, 0, v___x_4160_);
lean_ctor_set(v_reuseFailAlloc_4164_, 1, v___x_3705_);
v___x_4162_ = v_reuseFailAlloc_4164_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
lean_object* v___x_4163_; 
v___x_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4163_, 0, v___x_4162_);
v_a_3687_ = v___x_4163_;
goto v___jp_3686_;
}
}
}
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_del_object(v___x_4145_);
lean_del_object(v___x_4139_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
v_a_4166_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4157_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4157_);
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
else
{
lean_object* v_a_4174_; lean_object* v___x_4176_; uint8_t v_isShared_4177_; uint8_t v_isSharedCheck_4181_; 
lean_del_object(v___x_4145_);
lean_del_object(v___x_4139_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_4174_ = lean_ctor_get(v___x_4155_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4155_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4155_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4155_);
v___x_4176_ = lean_box(0);
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
v_resetjp_4175_:
{
lean_object* v___x_4179_; 
if (v_isShared_4177_ == 0)
{
v___x_4179_ = v___x_4176_;
goto v_reusejp_4178_;
}
else
{
lean_object* v_reuseFailAlloc_4180_; 
v_reuseFailAlloc_4180_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4180_, 0, v_a_4174_);
v___x_4179_ = v_reuseFailAlloc_4180_;
goto v_reusejp_4178_;
}
v_reusejp_4178_:
{
return v___x_4179_;
}
}
}
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
lean_dec(v_a_4151_);
lean_del_object(v___x_4145_);
lean_del_object(v___x_4139_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_4182_ = lean_ctor_get(v___x_4152_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4152_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4152_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4152_);
v___x_4184_ = lean_box(0);
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
v_resetjp_4183_:
{
lean_object* v___x_4187_; 
if (v_isShared_4185_ == 0)
{
v___x_4187_ = v___x_4184_;
goto v_reusejp_4186_;
}
else
{
lean_object* v_reuseFailAlloc_4188_; 
v_reuseFailAlloc_4188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4188_, 0, v_a_4182_);
v___x_4187_ = v_reuseFailAlloc_4188_;
goto v_reusejp_4186_;
}
v_reusejp_4186_:
{
return v___x_4187_;
}
}
}
}
else
{
lean_object* v_a_4190_; lean_object* v___x_4192_; uint8_t v_isShared_4193_; uint8_t v_isSharedCheck_4197_; 
lean_del_object(v___x_4145_);
lean_dec(v_fst_4142_);
lean_del_object(v___x_4139_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
v_a_4190_ = lean_ctor_get(v___x_4150_, 0);
v_isSharedCheck_4197_ = !lean_is_exclusive(v___x_4150_);
if (v_isSharedCheck_4197_ == 0)
{
v___x_4192_ = v___x_4150_;
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
else
{
lean_inc(v_a_4190_);
lean_dec(v___x_4150_);
v___x_4192_ = lean_box(0);
v_isShared_4193_ = v_isSharedCheck_4197_;
goto v_resetjp_4191_;
}
v_resetjp_4191_:
{
lean_object* v___x_4195_; 
if (v_isShared_4193_ == 0)
{
v___x_4195_ = v___x_4192_;
goto v_reusejp_4194_;
}
else
{
lean_object* v_reuseFailAlloc_4196_; 
v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
v___x_4195_ = v_reuseFailAlloc_4196_;
goto v_reusejp_4194_;
}
v_reusejp_4194_:
{
return v___x_4195_;
}
}
}
}
}
else
{
lean_object* v_a_4198_; lean_object* v___x_4200_; uint8_t v_isShared_4201_; uint8_t v_isSharedCheck_4205_; 
lean_del_object(v___x_4145_);
lean_dec(v_fst_4142_);
lean_del_object(v___x_4139_);
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_4198_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4205_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4205_ == 0)
{
v___x_4200_ = v___x_4147_;
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
else
{
lean_inc(v_a_4198_);
lean_dec(v___x_4147_);
v___x_4200_ = lean_box(0);
v_isShared_4201_ = v_isSharedCheck_4205_;
goto v_resetjp_4199_;
}
v_resetjp_4199_:
{
lean_object* v___x_4203_; 
if (v_isShared_4201_ == 0)
{
v___x_4203_ = v___x_4200_;
goto v_reusejp_4202_;
}
else
{
lean_object* v_reuseFailAlloc_4204_; 
v_reuseFailAlloc_4204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4204_, 0, v_a_4198_);
v___x_4203_ = v_reuseFailAlloc_4204_;
goto v_reusejp_4202_;
}
v_reusejp_4202_:
{
return v___x_4203_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4136_);
v___y_3990_ = v___y_4088_;
v___y_3991_ = v___y_4089_;
v___y_3992_ = v___y_4090_;
v___y_3993_ = v___y_4091_;
goto v___jp_3989_;
}
}
else
{
lean_object* v_a_4208_; lean_object* v___x_4210_; uint8_t v_isShared_4211_; uint8_t v_isSharedCheck_4215_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_4208_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4215_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4215_ == 0)
{
v___x_4210_ = v___x_4135_;
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
else
{
lean_inc(v_a_4208_);
lean_dec(v___x_4135_);
v___x_4210_ = lean_box(0);
v_isShared_4211_ = v_isSharedCheck_4215_;
goto v_resetjp_4209_;
}
v_resetjp_4209_:
{
lean_object* v___x_4213_; 
if (v_isShared_4211_ == 0)
{
v___x_4213_ = v___x_4210_;
goto v_reusejp_4212_;
}
else
{
lean_object* v_reuseFailAlloc_4214_; 
v_reuseFailAlloc_4214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4214_, 0, v_a_4208_);
v___x_4213_ = v_reuseFailAlloc_4214_;
goto v_reusejp_4212_;
}
v_reusejp_4212_:
{
return v___x_4213_;
}
}
}
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec_ref(v___x_3735_);
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_4216_ = lean_ctor_get(v___x_4092_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4092_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4092_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4092_);
v___x_4218_ = lean_box(0);
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
v_resetjp_4217_:
{
lean_object* v___x_4221_; 
if (v_isShared_4219_ == 0)
{
v___x_4221_ = v___x_4218_;
goto v_reusejp_4220_;
}
else
{
lean_object* v_reuseFailAlloc_4222_; 
v_reuseFailAlloc_4222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4222_, 0, v_a_4216_);
v___x_4221_ = v_reuseFailAlloc_4222_;
goto v_reusejp_4220_;
}
v_reusejp_4220_:
{
return v___x_4221_;
}
}
}
}
}
else
{
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
v_a_3695_ = v___x_3706_;
goto v___jp_3694_;
}
v___jp_3707_:
{
uint8_t v_emptyType_3714_; 
v_emptyType_3714_ = lean_ctor_get_uint8(v_config_3669_, sizeof(void*)*1 + 1);
if (v_emptyType_3714_ == 0)
{
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
v_a_3695_ = v___x_3706_;
goto v___jp_3694_;
}
else
{
if (v___y_3709_ == 0)
{
if (v___y_3708_ == 0)
{
lean_object* v_searchFuel_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; 
v_searchFuel_3715_ = lean_ctor_get(v_config_3669_, 0);
v___x_3716_ = l_Lean_LocalDecl_fvarId(v_val_3701_);
lean_dec(v_val_3701_);
lean_inc(v_searchFuel_3715_);
lean_inc(v_mvarId_3670_);
v___x_3717_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3670_, v___x_3716_, v_searchFuel_3715_, v___y_3710_, v___y_3711_, v___y_3712_, v___y_3713_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v_a_3718_; uint8_t v___x_3719_; 
v_a_3718_ = lean_ctor_get(v___x_3717_, 0);
lean_inc(v_a_3718_);
lean_dec_ref_known(v___x_3717_, 1);
v___x_3719_ = lean_unbox(v_a_3718_);
lean_dec(v_a_3718_);
if (v___x_3719_ == 0)
{
lean_del_object(v___x_3703_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
v_a_3695_ = v___x_3706_;
goto v___jp_3694_;
}
else
{
lean_object* v___x_3720_; lean_object* v___x_3722_; 
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v___x_3720_ = lean_box(v___x_3680_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3720_);
v___x_3722_ = v___x_3703_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3720_);
v___x_3722_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3723_; lean_object* v___x_3724_; 
v___x_3723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
lean_ctor_set(v___x_3723_, 1, v___x_3705_);
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
v_a_3687_ = v___x_3724_;
goto v___jp_3686_;
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_del_object(v___x_3703_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
lean_dec(v_mvarId_3670_);
lean_dec_ref(v_config_3669_);
v_a_3726_ = lean_ctor_get(v___x_3717_, 0);
v_isSharedCheck_3733_ = !lean_is_exclusive(v___x_3717_);
if (v_isSharedCheck_3733_ == 0)
{
v___x_3728_ = v___x_3717_;
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
else
{
lean_inc(v_a_3726_);
lean_dec(v___x_3717_);
v___x_3728_ = lean_box(0);
v_isShared_3729_ = v_isSharedCheck_3733_;
goto v_resetjp_3727_;
}
v_resetjp_3727_:
{
lean_object* v___x_3731_; 
if (v_isShared_3729_ == 0)
{
v___x_3731_ = v___x_3728_;
goto v_reusejp_3730_;
}
else
{
lean_object* v_reuseFailAlloc_3732_; 
v_reuseFailAlloc_3732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3732_, 0, v_a_3726_);
v___x_3731_ = v_reuseFailAlloc_3732_;
goto v_reusejp_3730_;
}
v_reusejp_3730_:
{
return v___x_3731_;
}
}
}
}
else
{
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
v_a_3695_ = v___x_3706_;
goto v___jp_3694_;
}
}
else
{
lean_del_object(v___x_3703_);
lean_dec(v_val_3701_);
lean_del_object(v___x_3684_);
lean_dec(v_snd_3682_);
v_a_3695_ = v___x_3706_;
goto v___jp_3694_;
}
}
}
}
}
v___jp_3686_:
{
lean_object* v___x_3688_; lean_object* v___x_3690_; 
v___x_3688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3688_, 0, v_a_3687_);
if (v_isShared_3685_ == 0)
{
lean_ctor_set(v___x_3684_, 0, v___x_3688_);
v___x_3690_ = v___x_3684_;
goto v_reusejp_3689_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v___x_3688_);
lean_ctor_set(v_reuseFailAlloc_3692_, 1, v_snd_3682_);
v___x_3690_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3689_;
}
v_reusejp_3689_:
{
lean_object* v___x_3691_; 
v___x_3691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3691_, 0, v___x_3690_);
return v___x_3691_;
}
}
v___jp_3694_:
{
lean_object* v___x_3696_; size_t v___x_3697_; size_t v___x_3698_; lean_object* v___x_3699_; 
v___x_3696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3696_, 0, v___x_3693_);
lean_ctor_set(v___x_3696_, 1, v_a_3695_);
v___x_3697_ = ((size_t)1ULL);
v___x_3698_ = lean_usize_add(v_i_3673_, v___x_3697_);
v___x_3699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3669_, v_mvarId_3670_, v_as_3671_, v_sz_3672_, v___x_3698_, v___x_3696_, v___y_3675_, v___y_3676_, v___y_3677_, v___y_3678_);
return v___x_3699_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4297_, lean_object* v_mvarId_4298_, lean_object* v_as_4299_, lean_object* v_sz_4300_, lean_object* v_i_4301_, lean_object* v_b_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
size_t v_sz_boxed_4308_; size_t v_i_boxed_4309_; lean_object* v_res_4310_; 
v_sz_boxed_4308_ = lean_unbox_usize(v_sz_4300_);
lean_dec(v_sz_4300_);
v_i_boxed_4309_ = lean_unbox_usize(v_i_4301_);
lean_dec(v_i_4301_);
v_res_4310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4297_, v_mvarId_4298_, v_as_4299_, v_sz_boxed_4308_, v_i_boxed_4309_, v_b_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_);
lean_dec(v___y_4306_);
lean_dec_ref(v___y_4305_);
lean_dec(v___y_4304_);
lean_dec_ref(v___y_4303_);
lean_dec_ref(v_as_4299_);
return v_res_4310_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4311_, lean_object* v_config_4312_, lean_object* v_mvarId_4313_, lean_object* v_n_4314_, lean_object* v_b_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
if (lean_obj_tag(v_n_4314_) == 0)
{
lean_object* v_cs_4321_; lean_object* v___x_4322_; lean_object* v___x_4323_; size_t v_sz_4324_; size_t v___x_4325_; lean_object* v___x_4326_; 
v_cs_4321_ = lean_ctor_get(v_n_4314_, 0);
v___x_4322_ = lean_box(0);
v___x_4323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4323_, 0, v___x_4322_);
lean_ctor_set(v___x_4323_, 1, v_b_4315_);
v_sz_4324_ = lean_array_size(v_cs_4321_);
v___x_4325_ = ((size_t)0ULL);
v___x_4326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4311_, v_config_4312_, v_mvarId_4313_, v_cs_4321_, v_sz_4324_, v___x_4325_, v___x_4323_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4326_) == 0)
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4341_; 
v_a_4327_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4341_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4341_ == 0)
{
v___x_4329_ = v___x_4326_;
v_isShared_4330_ = v_isSharedCheck_4341_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4326_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4341_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v_fst_4331_; 
v_fst_4331_ = lean_ctor_get(v_a_4327_, 0);
if (lean_obj_tag(v_fst_4331_) == 0)
{
lean_object* v_snd_4332_; lean_object* v___x_4333_; lean_object* v___x_4335_; 
v_snd_4332_ = lean_ctor_get(v_a_4327_, 1);
lean_inc(v_snd_4332_);
lean_dec(v_a_4327_);
v___x_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4333_, 0, v_snd_4332_);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v___x_4333_);
v___x_4335_ = v___x_4329_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4333_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
else
{
lean_object* v_val_4337_; lean_object* v___x_4339_; 
lean_inc_ref(v_fst_4331_);
lean_dec(v_a_4327_);
v_val_4337_ = lean_ctor_get(v_fst_4331_, 0);
lean_inc(v_val_4337_);
lean_dec_ref_known(v_fst_4331_, 1);
if (v_isShared_4330_ == 0)
{
lean_ctor_set(v___x_4329_, 0, v_val_4337_);
v___x_4339_ = v___x_4329_;
goto v_reusejp_4338_;
}
else
{
lean_object* v_reuseFailAlloc_4340_; 
v_reuseFailAlloc_4340_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4340_, 0, v_val_4337_);
v___x_4339_ = v_reuseFailAlloc_4340_;
goto v_reusejp_4338_;
}
v_reusejp_4338_:
{
return v___x_4339_;
}
}
}
}
else
{
lean_object* v_a_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4349_; 
v_a_4342_ = lean_ctor_get(v___x_4326_, 0);
v_isSharedCheck_4349_ = !lean_is_exclusive(v___x_4326_);
if (v_isSharedCheck_4349_ == 0)
{
v___x_4344_ = v___x_4326_;
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_a_4342_);
lean_dec(v___x_4326_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4349_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4347_; 
if (v_isShared_4345_ == 0)
{
v___x_4347_ = v___x_4344_;
goto v_reusejp_4346_;
}
else
{
lean_object* v_reuseFailAlloc_4348_; 
v_reuseFailAlloc_4348_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4348_, 0, v_a_4342_);
v___x_4347_ = v_reuseFailAlloc_4348_;
goto v_reusejp_4346_;
}
v_reusejp_4346_:
{
return v___x_4347_;
}
}
}
}
else
{
lean_object* v_vs_4350_; lean_object* v___x_4351_; lean_object* v___x_4352_; size_t v_sz_4353_; size_t v___x_4354_; lean_object* v___x_4355_; 
v_vs_4350_ = lean_ctor_get(v_n_4314_, 0);
v___x_4351_ = lean_box(0);
v___x_4352_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4352_, 0, v___x_4351_);
lean_ctor_set(v___x_4352_, 1, v_b_4315_);
v_sz_4353_ = lean_array_size(v_vs_4350_);
v___x_4354_ = ((size_t)0ULL);
v___x_4355_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4312_, v_mvarId_4313_, v_vs_4350_, v_sz_4353_, v___x_4354_, v___x_4352_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4358_; uint8_t v_isShared_4359_; uint8_t v_isSharedCheck_4370_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4370_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4370_ == 0)
{
v___x_4358_ = v___x_4355_;
v_isShared_4359_ = v_isSharedCheck_4370_;
goto v_resetjp_4357_;
}
else
{
lean_inc(v_a_4356_);
lean_dec(v___x_4355_);
v___x_4358_ = lean_box(0);
v_isShared_4359_ = v_isSharedCheck_4370_;
goto v_resetjp_4357_;
}
v_resetjp_4357_:
{
lean_object* v_fst_4360_; 
v_fst_4360_ = lean_ctor_get(v_a_4356_, 0);
if (lean_obj_tag(v_fst_4360_) == 0)
{
lean_object* v_snd_4361_; lean_object* v___x_4362_; lean_object* v___x_4364_; 
v_snd_4361_ = lean_ctor_get(v_a_4356_, 1);
lean_inc(v_snd_4361_);
lean_dec(v_a_4356_);
v___x_4362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4362_, 0, v_snd_4361_);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v___x_4362_);
v___x_4364_ = v___x_4358_;
goto v_reusejp_4363_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4362_);
v___x_4364_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4363_;
}
v_reusejp_4363_:
{
return v___x_4364_;
}
}
else
{
lean_object* v_val_4366_; lean_object* v___x_4368_; 
lean_inc_ref(v_fst_4360_);
lean_dec(v_a_4356_);
v_val_4366_ = lean_ctor_get(v_fst_4360_, 0);
lean_inc(v_val_4366_);
lean_dec_ref_known(v_fst_4360_, 1);
if (v_isShared_4359_ == 0)
{
lean_ctor_set(v___x_4358_, 0, v_val_4366_);
v___x_4368_ = v___x_4358_;
goto v_reusejp_4367_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v_val_4366_);
v___x_4368_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4367_;
}
v_reusejp_4367_:
{
return v___x_4368_;
}
}
}
}
else
{
lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4378_; 
v_a_4371_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4378_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4378_ == 0)
{
v___x_4373_ = v___x_4355_;
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4355_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4378_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4376_; 
if (v_isShared_4374_ == 0)
{
v___x_4376_ = v___x_4373_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4377_; 
v_reuseFailAlloc_4377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4377_, 0, v_a_4371_);
v___x_4376_ = v_reuseFailAlloc_4377_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
return v___x_4376_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4379_, lean_object* v_config_4380_, lean_object* v_mvarId_4381_, lean_object* v_as_4382_, size_t v_sz_4383_, size_t v_i_4384_, lean_object* v_b_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_){
_start:
{
uint8_t v___x_4391_; 
v___x_4391_ = lean_usize_dec_lt(v_i_4384_, v_sz_4383_);
if (v___x_4391_ == 0)
{
lean_object* v___x_4392_; 
lean_dec(v_mvarId_4381_);
lean_dec_ref(v_config_4380_);
v___x_4392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4392_, 0, v_b_4385_);
return v___x_4392_;
}
else
{
lean_object* v_snd_4393_; lean_object* v___x_4395_; uint8_t v_isShared_4396_; uint8_t v_isSharedCheck_4427_; 
v_snd_4393_ = lean_ctor_get(v_b_4385_, 1);
v_isSharedCheck_4427_ = !lean_is_exclusive(v_b_4385_);
if (v_isSharedCheck_4427_ == 0)
{
lean_object* v_unused_4428_; 
v_unused_4428_ = lean_ctor_get(v_b_4385_, 0);
lean_dec(v_unused_4428_);
v___x_4395_ = v_b_4385_;
v_isShared_4396_ = v_isSharedCheck_4427_;
goto v_resetjp_4394_;
}
else
{
lean_inc(v_snd_4393_);
lean_dec(v_b_4385_);
v___x_4395_ = lean_box(0);
v_isShared_4396_ = v_isSharedCheck_4427_;
goto v_resetjp_4394_;
}
v_resetjp_4394_:
{
lean_object* v___x_4397_; lean_object* v_a_4398_; lean_object* v___x_4399_; 
v___x_4397_ = lean_box(0);
v_a_4398_ = lean_array_uget_borrowed(v_as_4382_, v_i_4384_);
lean_inc(v_snd_4393_);
lean_inc(v_mvarId_4381_);
lean_inc_ref(v_config_4380_);
v___x_4399_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4379_, v_config_4380_, v_mvarId_4381_, v_a_4398_, v_snd_4393_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
if (lean_obj_tag(v___x_4399_) == 0)
{
lean_object* v_a_4400_; lean_object* v___x_4402_; uint8_t v_isShared_4403_; uint8_t v_isSharedCheck_4418_; 
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4402_ = v___x_4399_;
v_isShared_4403_ = v_isSharedCheck_4418_;
goto v_resetjp_4401_;
}
else
{
lean_inc(v_a_4400_);
lean_dec(v___x_4399_);
v___x_4402_ = lean_box(0);
v_isShared_4403_ = v_isSharedCheck_4418_;
goto v_resetjp_4401_;
}
v_resetjp_4401_:
{
if (lean_obj_tag(v_a_4400_) == 0)
{
lean_object* v___x_4404_; lean_object* v___x_4406_; 
lean_dec(v_mvarId_4381_);
lean_dec_ref(v_config_4380_);
v___x_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4404_, 0, v_a_4400_);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 0, v___x_4404_);
v___x_4406_ = v___x_4395_;
goto v_reusejp_4405_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4404_);
lean_ctor_set(v_reuseFailAlloc_4410_, 1, v_snd_4393_);
v___x_4406_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4405_;
}
v_reusejp_4405_:
{
lean_object* v___x_4408_; 
if (v_isShared_4403_ == 0)
{
lean_ctor_set(v___x_4402_, 0, v___x_4406_);
v___x_4408_ = v___x_4402_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v___x_4406_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; 
lean_del_object(v___x_4402_);
lean_dec(v_snd_4393_);
v_a_4411_ = lean_ctor_get(v_a_4400_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v_a_4400_, 1);
if (v_isShared_4396_ == 0)
{
lean_ctor_set(v___x_4395_, 1, v_a_4411_);
lean_ctor_set(v___x_4395_, 0, v___x_4397_);
v___x_4413_ = v___x_4395_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v___x_4397_);
lean_ctor_set(v_reuseFailAlloc_4417_, 1, v_a_4411_);
v___x_4413_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
size_t v___x_4414_; size_t v___x_4415_; 
v___x_4414_ = ((size_t)1ULL);
v___x_4415_ = lean_usize_add(v_i_4384_, v___x_4414_);
v_i_4384_ = v___x_4415_;
v_b_4385_ = v___x_4413_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4419_; lean_object* v___x_4421_; uint8_t v_isShared_4422_; uint8_t v_isSharedCheck_4426_; 
lean_del_object(v___x_4395_);
lean_dec(v_snd_4393_);
lean_dec(v_mvarId_4381_);
lean_dec_ref(v_config_4380_);
v_a_4419_ = lean_ctor_get(v___x_4399_, 0);
v_isSharedCheck_4426_ = !lean_is_exclusive(v___x_4399_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4421_ = v___x_4399_;
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
else
{
lean_inc(v_a_4419_);
lean_dec(v___x_4399_);
v___x_4421_ = lean_box(0);
v_isShared_4422_ = v_isSharedCheck_4426_;
goto v_resetjp_4420_;
}
v_resetjp_4420_:
{
lean_object* v___x_4424_; 
if (v_isShared_4422_ == 0)
{
v___x_4424_ = v___x_4421_;
goto v_reusejp_4423_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v_a_4419_);
v___x_4424_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4423_;
}
v_reusejp_4423_:
{
return v___x_4424_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4429_, lean_object* v_config_4430_, lean_object* v_mvarId_4431_, lean_object* v_as_4432_, lean_object* v_sz_4433_, lean_object* v_i_4434_, lean_object* v_b_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_){
_start:
{
size_t v_sz_boxed_4441_; size_t v_i_boxed_4442_; lean_object* v_res_4443_; 
v_sz_boxed_4441_ = lean_unbox_usize(v_sz_4433_);
lean_dec(v_sz_4433_);
v_i_boxed_4442_ = lean_unbox_usize(v_i_4434_);
lean_dec(v_i_4434_);
v_res_4443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4429_, v_config_4430_, v_mvarId_4431_, v_as_4432_, v_sz_boxed_4441_, v_i_boxed_4442_, v_b_4435_, v___y_4436_, v___y_4437_, v___y_4438_, v___y_4439_);
lean_dec(v___y_4439_);
lean_dec_ref(v___y_4438_);
lean_dec(v___y_4437_);
lean_dec_ref(v___y_4436_);
lean_dec_ref(v_as_4432_);
lean_dec_ref(v_init_4429_);
return v_res_4443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4444_, lean_object* v_config_4445_, lean_object* v_mvarId_4446_, lean_object* v_n_4447_, lean_object* v_b_4448_, lean_object* v___y_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_){
_start:
{
lean_object* v_res_4454_; 
v_res_4454_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4444_, v_config_4445_, v_mvarId_4446_, v_n_4447_, v_b_4448_, v___y_4449_, v___y_4450_, v___y_4451_, v___y_4452_);
lean_dec(v___y_4452_);
lean_dec_ref(v___y_4451_);
lean_dec(v___y_4450_);
lean_dec_ref(v___y_4449_);
lean_dec_ref(v_n_4447_);
lean_dec_ref(v_init_4444_);
return v_res_4454_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4455_, lean_object* v_mvarId_4456_, lean_object* v_t_4457_, lean_object* v_init_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_){
_start:
{
lean_object* v_root_4464_; lean_object* v_tail_4465_; lean_object* v___x_4466_; 
v_root_4464_ = lean_ctor_get(v_t_4457_, 0);
v_tail_4465_ = lean_ctor_get(v_t_4457_, 1);
lean_inc(v_mvarId_4456_);
lean_inc_ref(v_config_4455_);
lean_inc_ref(v_init_4458_);
v___x_4466_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4458_, v_config_4455_, v_mvarId_4456_, v_root_4464_, v_init_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec_ref(v_init_4458_);
if (lean_obj_tag(v___x_4466_) == 0)
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4503_; 
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4469_ = v___x_4466_;
v_isShared_4470_ = v_isSharedCheck_4503_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4466_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4503_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
if (lean_obj_tag(v_a_4467_) == 0)
{
lean_object* v_a_4471_; lean_object* v___x_4473_; 
lean_dec(v_mvarId_4456_);
lean_dec_ref(v_config_4455_);
v_a_4471_ = lean_ctor_get(v_a_4467_, 0);
lean_inc(v_a_4471_);
lean_dec_ref_known(v_a_4467_, 1);
if (v_isShared_4470_ == 0)
{
lean_ctor_set(v___x_4469_, 0, v_a_4471_);
v___x_4473_ = v___x_4469_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4471_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4476_; lean_object* v___x_4477_; size_t v_sz_4478_; size_t v___x_4479_; lean_object* v___x_4480_; 
lean_del_object(v___x_4469_);
v_a_4475_ = lean_ctor_get(v_a_4467_, 0);
lean_inc(v_a_4475_);
lean_dec_ref_known(v_a_4467_, 1);
v___x_4476_ = lean_box(0);
v___x_4477_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4477_, 0, v___x_4476_);
lean_ctor_set(v___x_4477_, 1, v_a_4475_);
v_sz_4478_ = lean_array_size(v_tail_4465_);
v___x_4479_ = ((size_t)0ULL);
v___x_4480_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4455_, v_mvarId_4456_, v_tail_4465_, v_sz_4478_, v___x_4479_, v___x_4477_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
if (lean_obj_tag(v___x_4480_) == 0)
{
lean_object* v_a_4481_; lean_object* v___x_4483_; uint8_t v_isShared_4484_; uint8_t v_isSharedCheck_4494_; 
v_a_4481_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4483_ = v___x_4480_;
v_isShared_4484_ = v_isSharedCheck_4494_;
goto v_resetjp_4482_;
}
else
{
lean_inc(v_a_4481_);
lean_dec(v___x_4480_);
v___x_4483_ = lean_box(0);
v_isShared_4484_ = v_isSharedCheck_4494_;
goto v_resetjp_4482_;
}
v_resetjp_4482_:
{
lean_object* v_fst_4485_; 
v_fst_4485_ = lean_ctor_get(v_a_4481_, 0);
if (lean_obj_tag(v_fst_4485_) == 0)
{
lean_object* v_snd_4486_; lean_object* v___x_4488_; 
v_snd_4486_ = lean_ctor_get(v_a_4481_, 1);
lean_inc(v_snd_4486_);
lean_dec(v_a_4481_);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v_snd_4486_);
v___x_4488_ = v___x_4483_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_snd_4486_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
else
{
lean_object* v_val_4490_; lean_object* v___x_4492_; 
lean_inc_ref(v_fst_4485_);
lean_dec(v_a_4481_);
v_val_4490_ = lean_ctor_get(v_fst_4485_, 0);
lean_inc(v_val_4490_);
lean_dec_ref_known(v_fst_4485_, 1);
if (v_isShared_4484_ == 0)
{
lean_ctor_set(v___x_4483_, 0, v_val_4490_);
v___x_4492_ = v___x_4483_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_val_4490_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
}
else
{
lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4502_; 
v_a_4495_ = lean_ctor_get(v___x_4480_, 0);
v_isSharedCheck_4502_ = !lean_is_exclusive(v___x_4480_);
if (v_isSharedCheck_4502_ == 0)
{
v___x_4497_ = v___x_4480_;
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4480_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4502_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4500_; 
if (v_isShared_4498_ == 0)
{
v___x_4500_ = v___x_4497_;
goto v_reusejp_4499_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_a_4495_);
v___x_4500_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4499_;
}
v_reusejp_4499_:
{
return v___x_4500_;
}
}
}
}
}
}
else
{
lean_object* v_a_4504_; lean_object* v___x_4506_; uint8_t v_isShared_4507_; uint8_t v_isSharedCheck_4511_; 
lean_dec(v_mvarId_4456_);
lean_dec_ref(v_config_4455_);
v_a_4504_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4511_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4511_ == 0)
{
v___x_4506_ = v___x_4466_;
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
else
{
lean_inc(v_a_4504_);
lean_dec(v___x_4466_);
v___x_4506_ = lean_box(0);
v_isShared_4507_ = v_isSharedCheck_4511_;
goto v_resetjp_4505_;
}
v_resetjp_4505_:
{
lean_object* v___x_4509_; 
if (v_isShared_4507_ == 0)
{
v___x_4509_ = v___x_4506_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v_a_4504_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
return v___x_4509_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4512_, lean_object* v_mvarId_4513_, lean_object* v_t_4514_, lean_object* v_init_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
lean_object* v_res_4521_; 
v_res_4521_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4512_, v_mvarId_4513_, v_t_4514_, v_init_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v___y_4517_);
lean_dec_ref(v___y_4516_);
lean_dec_ref(v_t_4514_);
return v_res_4521_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4522_, lean_object* v___x_4523_, lean_object* v_config_4524_, lean_object* v___y_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_){
_start:
{
lean_object* v___x_4530_; 
lean_inc(v_mvarId_4522_);
v___x_4530_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4522_, v___x_4523_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
if (lean_obj_tag(v___x_4530_) == 0)
{
lean_object* v___x_4531_; 
lean_dec_ref_known(v___x_4530_, 1);
lean_inc(v_mvarId_4522_);
v___x_4531_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4522_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v_a_4532_; lean_object* v___x_4534_; uint8_t v_isShared_4535_; uint8_t v_isSharedCheck_4565_; 
v_a_4532_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4565_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4565_ == 0)
{
v___x_4534_ = v___x_4531_;
v_isShared_4535_ = v_isSharedCheck_4565_;
goto v_resetjp_4533_;
}
else
{
lean_inc(v_a_4532_);
lean_dec(v___x_4531_);
v___x_4534_ = lean_box(0);
v_isShared_4535_ = v_isSharedCheck_4565_;
goto v_resetjp_4533_;
}
v_resetjp_4533_:
{
uint8_t v___x_4536_; 
v___x_4536_ = lean_unbox(v_a_4532_);
if (v___x_4536_ == 0)
{
lean_object* v_lctx_4537_; lean_object* v_decls_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; 
lean_del_object(v___x_4534_);
v_lctx_4537_ = lean_ctor_get(v___y_4525_, 2);
v_decls_4538_ = lean_ctor_get(v_lctx_4537_, 1);
v___x_4539_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4540_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4524_, v_mvarId_4522_, v_decls_4538_, v___x_4539_, v___y_4525_, v___y_4526_, v___y_4527_, v___y_4528_);
if (lean_obj_tag(v___x_4540_) == 0)
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4553_; 
v_a_4541_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4543_ = v___x_4540_;
v_isShared_4544_ = v_isSharedCheck_4553_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4540_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4553_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v_fst_4545_; 
v_fst_4545_ = lean_ctor_get(v_a_4541_, 0);
lean_inc(v_fst_4545_);
lean_dec(v_a_4541_);
if (lean_obj_tag(v_fst_4545_) == 0)
{
lean_object* v___x_4547_; 
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v_a_4532_);
v___x_4547_ = v___x_4543_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4532_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
else
{
lean_object* v_val_4549_; lean_object* v___x_4551_; 
lean_dec(v_a_4532_);
v_val_4549_ = lean_ctor_get(v_fst_4545_, 0);
lean_inc(v_val_4549_);
lean_dec_ref_known(v_fst_4545_, 1);
if (v_isShared_4544_ == 0)
{
lean_ctor_set(v___x_4543_, 0, v_val_4549_);
v___x_4551_ = v___x_4543_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_val_4549_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
}
else
{
lean_object* v_a_4554_; lean_object* v___x_4556_; uint8_t v_isShared_4557_; uint8_t v_isSharedCheck_4561_; 
lean_dec(v_a_4532_);
v_a_4554_ = lean_ctor_get(v___x_4540_, 0);
v_isSharedCheck_4561_ = !lean_is_exclusive(v___x_4540_);
if (v_isSharedCheck_4561_ == 0)
{
v___x_4556_ = v___x_4540_;
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
else
{
lean_inc(v_a_4554_);
lean_dec(v___x_4540_);
v___x_4556_ = lean_box(0);
v_isShared_4557_ = v_isSharedCheck_4561_;
goto v_resetjp_4555_;
}
v_resetjp_4555_:
{
lean_object* v___x_4559_; 
if (v_isShared_4557_ == 0)
{
v___x_4559_ = v___x_4556_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4560_; 
v_reuseFailAlloc_4560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4560_, 0, v_a_4554_);
v___x_4559_ = v_reuseFailAlloc_4560_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
return v___x_4559_;
}
}
}
}
else
{
lean_object* v___x_4563_; 
lean_dec_ref(v_config_4524_);
lean_dec(v_mvarId_4522_);
if (v_isShared_4535_ == 0)
{
v___x_4563_ = v___x_4534_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v_a_4532_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
}
}
else
{
lean_dec_ref(v_config_4524_);
lean_dec(v_mvarId_4522_);
return v___x_4531_;
}
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec_ref(v_config_4524_);
lean_dec(v_mvarId_4522_);
v_a_4566_ = lean_ctor_get(v___x_4530_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4530_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4530_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4530_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4574_, lean_object* v___x_4575_, lean_object* v_config_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_){
_start:
{
lean_object* v_res_4582_; 
v_res_4582_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4574_, v___x_4575_, v_config_4576_, v___y_4577_, v___y_4578_, v___y_4579_, v___y_4580_);
lean_dec(v___y_4580_);
lean_dec_ref(v___y_4579_);
lean_dec(v___y_4578_);
lean_dec_ref(v___y_4577_);
return v_res_4582_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4585_, lean_object* v_config_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_){
_start:
{
lean_object* v___x_4592_; lean_object* v___f_4593_; lean_object* v___x_4594_; 
v___x_4592_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4585_);
v___f_4593_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4593_, 0, v_mvarId_4585_);
lean_closure_set(v___f_4593_, 1, v___x_4592_);
lean_closure_set(v___f_4593_, 2, v_config_4586_);
v___x_4594_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4585_, v___f_4593_, v_a_4587_, v_a_4588_, v_a_4589_, v_a_4590_);
return v___x_4594_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4595_, lean_object* v_config_4596_, lean_object* v_a_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_){
_start:
{
lean_object* v_res_4602_; 
v_res_4602_ = l_Lean_MVarId_contradictionCore(v_mvarId_4595_, v_config_4596_, v_a_4597_, v_a_4598_, v_a_4599_, v_a_4600_);
lean_dec(v_a_4600_);
lean_dec_ref(v_a_4599_);
lean_dec(v_a_4598_);
lean_dec_ref(v_a_4597_);
return v_res_4602_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4603_, lean_object* v_config_4604_, lean_object* v_a_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_){
_start:
{
lean_object* v___x_4610_; 
lean_inc(v_mvarId_4603_);
v___x_4610_ = l_Lean_MVarId_contradictionCore(v_mvarId_4603_, v_config_4604_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
if (lean_obj_tag(v___x_4610_) == 0)
{
lean_object* v_a_4611_; lean_object* v___x_4613_; uint8_t v_isShared_4614_; uint8_t v_isSharedCheck_4623_; 
v_a_4611_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4623_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4623_ == 0)
{
v___x_4613_ = v___x_4610_;
v_isShared_4614_ = v_isSharedCheck_4623_;
goto v_resetjp_4612_;
}
else
{
lean_inc(v_a_4611_);
lean_dec(v___x_4610_);
v___x_4613_ = lean_box(0);
v_isShared_4614_ = v_isSharedCheck_4623_;
goto v_resetjp_4612_;
}
v_resetjp_4612_:
{
uint8_t v___x_4615_; 
v___x_4615_ = lean_unbox(v_a_4611_);
lean_dec(v_a_4611_);
if (v___x_4615_ == 0)
{
lean_object* v___x_4616_; lean_object* v___x_4617_; lean_object* v___x_4618_; 
lean_del_object(v___x_4613_);
v___x_4616_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4617_ = lean_box(0);
v___x_4618_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4616_, v_mvarId_4603_, v___x_4617_, v_a_4605_, v_a_4606_, v_a_4607_, v_a_4608_);
return v___x_4618_;
}
else
{
lean_object* v___x_4619_; lean_object* v___x_4621_; 
lean_dec(v_mvarId_4603_);
v___x_4619_ = lean_box(0);
if (v_isShared_4614_ == 0)
{
lean_ctor_set(v___x_4613_, 0, v___x_4619_);
v___x_4621_ = v___x_4613_;
goto v_reusejp_4620_;
}
else
{
lean_object* v_reuseFailAlloc_4622_; 
v_reuseFailAlloc_4622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4622_, 0, v___x_4619_);
v___x_4621_ = v_reuseFailAlloc_4622_;
goto v_reusejp_4620_;
}
v_reusejp_4620_:
{
return v___x_4621_;
}
}
}
}
else
{
lean_object* v_a_4624_; lean_object* v___x_4626_; uint8_t v_isShared_4627_; uint8_t v_isSharedCheck_4631_; 
lean_dec(v_mvarId_4603_);
v_a_4624_ = lean_ctor_get(v___x_4610_, 0);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4610_);
if (v_isSharedCheck_4631_ == 0)
{
v___x_4626_ = v___x_4610_;
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
else
{
lean_inc(v_a_4624_);
lean_dec(v___x_4610_);
v___x_4626_ = lean_box(0);
v_isShared_4627_ = v_isSharedCheck_4631_;
goto v_resetjp_4625_;
}
v_resetjp_4625_:
{
lean_object* v___x_4629_; 
if (v_isShared_4627_ == 0)
{
v___x_4629_ = v___x_4626_;
goto v_reusejp_4628_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v_a_4624_);
v___x_4629_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4628_;
}
v_reusejp_4628_:
{
return v___x_4629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4632_, lean_object* v_config_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_){
_start:
{
lean_object* v_res_4639_; 
v_res_4639_ = l_Lean_MVarId_contradiction(v_mvarId_4632_, v_config_4633_, v_a_4634_, v_a_4635_, v_a_4636_, v_a_4637_);
lean_dec(v_a_4637_);
lean_dec_ref(v_a_4636_);
lean_dec(v_a_4635_);
lean_dec_ref(v_a_4634_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4702_; uint8_t v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; 
v___x_4702_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4703_ = 0;
v___x_4704_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4705_ = l_Lean_registerTraceClass(v___x_4702_, v___x_4703_, v___x_4704_);
return v___x_4705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4706_){
_start:
{
lean_object* v_res_4707_; 
v_res_4707_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4707_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Assumption(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Cases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_HasNotBit(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Contradiction(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Contradiction(builtin);
}
#ifdef __cplusplus
}
#endif
