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
size_t v_x_1124__boxed_155_; size_t v_x_1125__boxed_156_; lean_object* v_res_157_; 
v_x_1124__boxed_155_ = lean_unbox_usize(v_x_151_);
lean_dec(v_x_151_);
v_x_1125__boxed_156_ = lean_unbox_usize(v_x_152_);
lean_dec(v_x_152_);
v_res_157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_150_, v_x_1124__boxed_155_, v_x_1125__boxed_156_, v_x_153_, v_x_154_);
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
lean_object* v___x_169_; lean_object* v_mctx_170_; lean_object* v_cache_171_; lean_object* v_zetaDeltaFVarIds_172_; lean_object* v_postponed_173_; lean_object* v_diag_174_; lean_object* v___x_176_; uint8_t v_isShared_177_; uint8_t v_isSharedCheck_204_; 
v___x_169_ = lean_st_ref_take(v___y_167_);
v_mctx_170_ = lean_ctor_get(v___x_169_, 0);
v_cache_171_ = lean_ctor_get(v___x_169_, 1);
v_zetaDeltaFVarIds_172_ = lean_ctor_get(v___x_169_, 2);
v_postponed_173_ = lean_ctor_get(v___x_169_, 3);
v_diag_174_ = lean_ctor_get(v___x_169_, 4);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_204_ == 0)
{
v___x_176_ = v___x_169_;
v_isShared_177_ = v_isSharedCheck_204_;
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
v_isShared_177_ = v_isSharedCheck_204_;
goto v_resetjp_175_;
}
v_resetjp_175_:
{
lean_object* v_depth_178_; lean_object* v_levelAssignDepth_179_; lean_object* v_lmvarCounter_180_; lean_object* v_mvarCounter_181_; lean_object* v_lDecls_182_; lean_object* v_decls_183_; lean_object* v_userNames_184_; lean_object* v_lAssignment_185_; lean_object* v_eAssignment_186_; lean_object* v_dAssignment_187_; lean_object* v_instanceTypedMVars_188_; lean_object* v_synthNormMemo_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_203_; 
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
v_instanceTypedMVars_188_ = lean_ctor_get(v_mctx_170_, 10);
v_synthNormMemo_189_ = lean_ctor_get(v_mctx_170_, 11);
v_isSharedCheck_203_ = !lean_is_exclusive(v_mctx_170_);
if (v_isSharedCheck_203_ == 0)
{
v___x_191_ = v_mctx_170_;
v_isShared_192_ = v_isSharedCheck_203_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_synthNormMemo_189_);
lean_inc(v_instanceTypedMVars_188_);
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
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_203_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_193_ = lean_box(0);
v___x_194_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_186_, v_mvarId_165_, v_val_166_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 8, v___x_194_);
v___x_196_ = v___x_191_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_depth_178_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_levelAssignDepth_179_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_lmvarCounter_180_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v_mvarCounter_181_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v_lDecls_182_);
lean_ctor_set(v_reuseFailAlloc_202_, 5, v_decls_183_);
lean_ctor_set(v_reuseFailAlloc_202_, 6, v_userNames_184_);
lean_ctor_set(v_reuseFailAlloc_202_, 7, v_lAssignment_185_);
lean_ctor_set(v_reuseFailAlloc_202_, 8, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_202_, 9, v_dAssignment_187_);
lean_ctor_set(v_reuseFailAlloc_202_, 10, v_instanceTypedMVars_188_);
lean_ctor_set(v_reuseFailAlloc_202_, 11, v_synthNormMemo_189_);
v___x_196_ = v_reuseFailAlloc_202_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_196_);
v___x_198_ = v___x_176_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_cache_171_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_zetaDeltaFVarIds_172_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_postponed_173_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_diag_174_);
v___x_198_ = v_reuseFailAlloc_201_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_199_ = lean_st_ref_put(v___y_167_, v___x_198_);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_193_);
return v___x_200_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object* v_mvarId_205_, lean_object* v_val_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_205_, v_val_206_, v___y_207_);
lean_dec(v___y_207_);
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object* v_mvarId_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_){
_start:
{
lean_object* v___f_217_; lean_object* v___x_218_; 
v___f_217_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
lean_inc(v_mvarId_211_);
v___x_218_ = l_Lean_MVarId_getType(v_mvarId_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_262_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_262_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_262_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_262_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___x_223_; 
v___x_223_ = lean_find_expr(v___f_217_, v_a_219_);
lean_dec(v_a_219_);
if (lean_obj_tag(v___x_223_) == 1)
{
lean_object* v_val_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
lean_del_object(v___x_221_);
v_val_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = l_Lean_Expr_appArg_x21(v_val_224_);
lean_dec(v_val_224_);
lean_inc(v_mvarId_211_);
v___x_226_ = l_Lean_MVarId_getType(v_mvarId_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = l_Lean_Meta_mkFalseElim(v_a_227_, v___x_225_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_228_) == 0)
{
lean_object* v_a_229_; lean_object* v___x_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_239_; 
v_a_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc(v_a_229_);
lean_dec_ref_known(v___x_228_, 1);
v___x_230_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_211_, v_a_229_, v_a_213_);
v_isSharedCheck_239_ = !lean_is_exclusive(v___x_230_);
if (v_isSharedCheck_239_ == 0)
{
lean_object* v_unused_240_; 
v_unused_240_ = lean_ctor_get(v___x_230_, 0);
lean_dec(v_unused_240_);
v___x_232_ = v___x_230_;
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
else
{
lean_dec(v___x_230_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
uint8_t v___x_234_; lean_object* v___x_235_; lean_object* v___x_237_; 
v___x_234_ = 1;
v___x_235_ = lean_box(v___x_234_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_235_);
v___x_237_ = v___x_232_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
v___x_237_ = v_reuseFailAlloc_238_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
return v___x_237_;
}
}
}
else
{
lean_object* v_a_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_248_; 
lean_dec(v_mvarId_211_);
v_a_241_ = lean_ctor_get(v___x_228_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_228_);
if (v_isSharedCheck_248_ == 0)
{
v___x_243_ = v___x_228_;
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_a_241_);
lean_dec(v___x_228_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_248_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_246_; 
if (v_isShared_244_ == 0)
{
v___x_246_ = v___x_243_;
goto v_reusejp_245_;
}
else
{
lean_object* v_reuseFailAlloc_247_; 
v_reuseFailAlloc_247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_247_, 0, v_a_241_);
v___x_246_ = v_reuseFailAlloc_247_;
goto v_reusejp_245_;
}
v_reusejp_245_:
{
return v___x_246_;
}
}
}
}
else
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
lean_dec_ref(v___x_225_);
lean_dec(v_mvarId_211_);
v_a_249_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_226_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_226_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
else
{
uint8_t v___x_257_; lean_object* v___x_258_; lean_object* v___x_260_; 
lean_dec(v___x_223_);
lean_dec(v_mvarId_211_);
v___x_257_ = 0;
v___x_258_ = lean_box(v___x_257_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_258_);
v___x_260_ = v___x_221_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_258_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
else
{
lean_object* v_a_263_; lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_270_; 
lean_dec(v_mvarId_211_);
v_a_263_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_218_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_218_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_266_ == 0)
{
v___x_268_ = v___x_265_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___boxed(lean_object* v_mvarId_271_, lean_object* v_a_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_271_, v_a_272_, v_a_273_, v_a_274_, v_a_275_);
lean_dec(v_a_275_);
lean_dec_ref(v_a_274_);
lean_dec(v_a_273_);
lean_dec_ref(v_a_272_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object* v_mvarId_278_, lean_object* v_val_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_278_, v_val_279_, v___y_281_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object* v_mvarId_286_, lean_object* v_val_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v_res_293_; 
v_res_293_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(v_mvarId_286_, v_val_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
lean_dec(v___y_289_);
lean_dec_ref(v___y_288_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0(lean_object* v_00_u03b2_294_, lean_object* v_x_295_, lean_object* v_x_296_, lean_object* v_x_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_x_295_, v_x_296_, v_x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_299_, lean_object* v_x_300_, size_t v_x_301_, size_t v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_300_, v_x_301_, v_x_302_, v_x_303_, v_x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_){
_start:
{
size_t v_x_1475__boxed_312_; size_t v_x_1476__boxed_313_; lean_object* v_res_314_; 
v_x_1475__boxed_312_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_x_1476__boxed_313_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_res_314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_306_, v_x_307_, v_x_1475__boxed_312_, v_x_1476__boxed_313_, v_x_310_, v_x_311_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_315_, lean_object* v_n_316_, lean_object* v_k_317_, lean_object* v_v_318_){
_start:
{
lean_object* v___x_319_; 
v___x_319_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v_n_316_, v_k_317_, v_v_318_);
return v___x_319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_320_, size_t v_depth_321_, lean_object* v_keys_322_, lean_object* v_vals_323_, lean_object* v_heq_324_, lean_object* v_i_325_, lean_object* v_entries_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_321_, v_keys_322_, v_vals_323_, v_i_325_, v_entries_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_328_, lean_object* v_depth_329_, lean_object* v_keys_330_, lean_object* v_vals_331_, lean_object* v_heq_332_, lean_object* v_i_333_, lean_object* v_entries_334_){
_start:
{
size_t v_depth_boxed_335_; lean_object* v_res_336_; 
v_depth_boxed_335_ = lean_unbox_usize(v_depth_329_);
lean_dec(v_depth_329_);
v_res_336_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_328_, v_depth_boxed_335_, v_keys_330_, v_vals_331_, v_heq_332_, v_i_333_, v_entries_334_);
lean_dec_ref(v_vals_331_);
lean_dec_ref(v_keys_330_);
return v_res_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_337_, lean_object* v_x_338_, lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_338_, v_x_339_, v_x_340_, v_x_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object* v_fvarId_343_, lean_object* v_a_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
lean_object* v___x_353_; 
v___x_353_ = l_Lean_FVarId_getType___redArg(v_fvarId_343_, v_a_344_, v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_353_) == 0)
{
lean_object* v_a_354_; lean_object* v___x_355_; 
v_a_354_ = lean_ctor_get(v___x_353_, 0);
lean_inc(v_a_354_);
lean_dec_ref_known(v___x_353_, 1);
v___x_355_ = l_Lean_Meta_whnfD(v_a_354_, v_a_344_, v_a_345_, v_a_346_, v_a_347_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_382_; 
v_a_356_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_382_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_382_ == 0)
{
v___x_358_ = v___x_355_;
v_isShared_359_ = v_isSharedCheck_382_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_355_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_382_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_360_; 
v___x_360_ = l_Lean_Expr_getAppFn(v_a_356_);
lean_dec(v_a_356_);
if (lean_obj_tag(v___x_360_) == 4)
{
lean_object* v_declName_361_; lean_object* v___x_362_; lean_object* v_env_363_; uint8_t v___x_364_; lean_object* v___x_365_; 
v_declName_361_ = lean_ctor_get(v___x_360_, 0);
lean_inc(v_declName_361_);
lean_dec_ref_known(v___x_360_, 2);
v___x_362_ = lean_st_ref_get(v_a_347_);
v_env_363_ = lean_ctor_get(v___x_362_, 0);
lean_inc_ref(v_env_363_);
lean_dec(v___x_362_);
v___x_364_ = 0;
v___x_365_ = l_Lean_Environment_find_x3f(v_env_363_, v_declName_361_, v___x_364_);
if (lean_obj_tag(v___x_365_) == 0)
{
lean_del_object(v___x_358_);
goto v___jp_349_;
}
else
{
lean_object* v_val_366_; 
v_val_366_ = lean_ctor_get(v___x_365_, 0);
lean_inc(v_val_366_);
lean_dec_ref_known(v___x_365_, 1);
if (lean_obj_tag(v_val_366_) == 5)
{
lean_object* v_val_367_; lean_object* v_numIndices_368_; lean_object* v_ctors_369_; lean_object* v___x_370_; lean_object* v___x_371_; uint8_t v___x_372_; 
v_val_367_ = lean_ctor_get(v_val_366_, 0);
lean_inc_ref(v_val_367_);
lean_dec_ref_known(v_val_366_, 1);
v_numIndices_368_ = lean_ctor_get(v_val_367_, 2);
lean_inc(v_numIndices_368_);
v_ctors_369_ = lean_ctor_get(v_val_367_, 4);
lean_inc(v_ctors_369_);
lean_dec_ref(v_val_367_);
v___x_370_ = l_List_lengthTR___redArg(v_ctors_369_);
lean_dec(v_ctors_369_);
v___x_371_ = lean_unsigned_to_nat(0u);
v___x_372_ = lean_nat_dec_eq(v___x_370_, v___x_371_);
lean_dec(v___x_370_);
if (v___x_372_ == 0)
{
uint8_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_373_ = lean_nat_dec_lt(v___x_371_, v_numIndices_368_);
lean_dec(v_numIndices_368_);
v___x_374_ = lean_box(v___x_373_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_374_);
v___x_376_ = v___x_358_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_377_; 
v_reuseFailAlloc_377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_377_, 0, v___x_374_);
v___x_376_ = v_reuseFailAlloc_377_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
return v___x_376_;
}
}
else
{
lean_object* v___x_378_; lean_object* v___x_380_; 
lean_dec(v_numIndices_368_);
v___x_378_ = lean_box(v___x_372_);
if (v_isShared_359_ == 0)
{
lean_ctor_set(v___x_358_, 0, v___x_378_);
v___x_380_ = v___x_358_;
goto v_reusejp_379_;
}
else
{
lean_object* v_reuseFailAlloc_381_; 
v_reuseFailAlloc_381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_381_, 0, v___x_378_);
v___x_380_ = v_reuseFailAlloc_381_;
goto v_reusejp_379_;
}
v_reusejp_379_:
{
return v___x_380_;
}
}
}
else
{
lean_dec(v_val_366_);
lean_del_object(v___x_358_);
goto v___jp_349_;
}
}
}
else
{
lean_dec_ref(v___x_360_);
lean_del_object(v___x_358_);
goto v___jp_349_;
}
}
}
else
{
lean_object* v_a_383_; lean_object* v___x_385_; uint8_t v_isShared_386_; uint8_t v_isSharedCheck_390_; 
v_a_383_ = lean_ctor_get(v___x_355_, 0);
v_isSharedCheck_390_ = !lean_is_exclusive(v___x_355_);
if (v_isSharedCheck_390_ == 0)
{
v___x_385_ = v___x_355_;
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
else
{
lean_inc(v_a_383_);
lean_dec(v___x_355_);
v___x_385_ = lean_box(0);
v_isShared_386_ = v_isSharedCheck_390_;
goto v_resetjp_384_;
}
v_resetjp_384_:
{
lean_object* v___x_388_; 
if (v_isShared_386_ == 0)
{
v___x_388_ = v___x_385_;
goto v_reusejp_387_;
}
else
{
lean_object* v_reuseFailAlloc_389_; 
v_reuseFailAlloc_389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
v___x_388_ = v_reuseFailAlloc_389_;
goto v_reusejp_387_;
}
v_reusejp_387_:
{
return v___x_388_;
}
}
}
}
else
{
lean_object* v_a_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_398_; 
v_a_391_ = lean_ctor_get(v___x_353_, 0);
v_isSharedCheck_398_ = !lean_is_exclusive(v___x_353_);
if (v_isSharedCheck_398_ == 0)
{
v___x_393_ = v___x_353_;
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_a_391_);
lean_dec(v___x_353_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_398_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_396_; 
if (v_isShared_394_ == 0)
{
v___x_396_ = v___x_393_;
goto v_reusejp_395_;
}
else
{
lean_object* v_reuseFailAlloc_397_; 
v_reuseFailAlloc_397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_397_, 0, v_a_391_);
v___x_396_ = v_reuseFailAlloc_397_;
goto v_reusejp_395_;
}
v_reusejp_395_:
{
return v___x_396_;
}
}
}
v___jp_349_:
{
uint8_t v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_350_ = 0;
v___x_351_ = lean_box(v___x_350_);
v___x_352_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate___boxed(lean_object* v_fvarId_399_, lean_object* v_a_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_){
_start:
{
lean_object* v_res_405_; 
v_res_405_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_399_, v_a_400_, v_a_401_, v_a_402_, v_a_403_);
lean_dec(v_a_403_);
lean_dec_ref(v_a_402_);
lean_dec(v_a_401_);
lean_dec_ref(v_a_400_);
return v_res_405_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object* v_s_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v___x_413_; 
v___x_413_ = l_Lean_Meta_SavedState_restore___redArg(v_s_406_, v___y_409_, v___y_411_);
return v___x_413_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object* v_s_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_){
_start:
{
lean_object* v_res_421_; 
v_res_421_ = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(v_s_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_);
lean_dec(v___y_419_);
lean_dec_ref(v___y_418_);
lean_dec(v___y_417_);
lean_dec_ref(v___y_416_);
lean_dec(v___y_415_);
return v_res_421_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object* v_x_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
lean_object* v___x_437_; 
lean_inc(v___y_431_);
v___x_437_ = lean_apply_6(v_x_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, lean_box(0));
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object* v_x_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(v_x_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_);
lean_dec(v___y_439_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object* v_mvarId_446_, lean_object* v_x_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___f_454_; lean_object* v___x_455_; 
lean_inc(v___y_448_);
v___f_454_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_454_, 0, v_x_447_);
lean_closure_set(v___f_454_, 1, v___y_448_);
v___x_455_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_446_, v___f_454_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
if (lean_obj_tag(v___x_455_) == 0)
{
return v___x_455_;
}
else
{
lean_object* v_a_456_; lean_object* v___x_458_; uint8_t v_isShared_459_; uint8_t v_isSharedCheck_463_; 
v_a_456_ = lean_ctor_get(v___x_455_, 0);
v_isSharedCheck_463_ = !lean_is_exclusive(v___x_455_);
if (v_isSharedCheck_463_ == 0)
{
v___x_458_ = v___x_455_;
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
else
{
lean_inc(v_a_456_);
lean_dec(v___x_455_);
v___x_458_ = lean_box(0);
v_isShared_459_ = v_isSharedCheck_463_;
goto v_resetjp_457_;
}
v_resetjp_457_:
{
lean_object* v___x_461_; 
if (v_isShared_459_ == 0)
{
v___x_461_ = v___x_458_;
goto v_reusejp_460_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_a_456_);
v___x_461_ = v_reuseFailAlloc_462_;
goto v_reusejp_460_;
}
v_reusejp_460_:
{
return v___x_461_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___boxed(lean_object* v_mvarId_464_, lean_object* v_x_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_464_, v_x_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec(v___y_470_);
lean_dec_ref(v___y_469_);
lean_dec(v___y_468_);
lean_dec_ref(v___y_467_);
lean_dec(v___y_466_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object* v_00_u03b1_473_, lean_object* v_mvarId_474_, lean_object* v_x_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_){
_start:
{
lean_object* v___x_482_; 
v___x_482_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_474_, v_x_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___boxed(lean_object* v_00_u03b1_483_, lean_object* v_mvarId_484_, lean_object* v_x_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(v_00_u03b1_483_, v_mvarId_484_, v_x_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_);
lean_dec(v___y_490_);
lean_dec_ref(v___y_489_);
lean_dec(v___y_488_);
lean_dec_ref(v___y_487_);
lean_dec(v___y_486_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object* v_x_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_){
_start:
{
lean_object* v___x_500_; 
v___x_500_ = l_Lean_Meta_saveState___redArg(v___y_496_, v___y_498_);
if (lean_obj_tag(v___x_500_) == 0)
{
lean_object* v_a_501_; lean_object* v___y_503_; lean_object* v_a_504_; lean_object* v___x_524_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
v___x_524_ = lean_apply_6(v_x_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, lean_box(0));
if (lean_obj_tag(v___x_524_) == 0)
{
lean_object* v_a_525_; uint8_t v___x_526_; 
v_a_525_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_525_);
v___x_526_ = lean_unbox(v_a_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
lean_dec_ref_known(v___x_524_, 1);
lean_inc(v_a_501_);
v___x_527_ = l_Lean_Meta_SavedState_restore___redArg(v_a_501_, v___y_496_, v___y_498_);
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_534_; 
lean_dec(v_a_501_);
v_isSharedCheck_534_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_534_ == 0)
{
lean_object* v_unused_535_; 
v_unused_535_ = lean_ctor_get(v___x_527_, 0);
lean_dec(v_unused_535_);
v___x_529_ = v___x_527_;
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
else
{
lean_dec(v___x_527_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_534_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
lean_object* v___x_532_; 
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 0, v_a_525_);
v___x_532_ = v___x_529_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_a_525_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
return v___x_532_;
}
}
}
else
{
lean_object* v_a_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_543_; 
lean_dec(v_a_525_);
v_a_536_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_543_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_543_ == 0)
{
v___x_538_ = v___x_527_;
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_a_536_);
lean_dec(v___x_527_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_543_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
lean_inc(v_a_536_);
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_542_; 
v_reuseFailAlloc_542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_542_, 0, v_a_536_);
v___x_541_ = v_reuseFailAlloc_542_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
v___y_503_ = v___x_541_;
v_a_504_ = v_a_536_;
goto v___jp_502_;
}
}
}
}
else
{
lean_dec(v_a_525_);
lean_dec(v_a_501_);
return v___x_524_;
}
}
else
{
lean_object* v_a_544_; 
v_a_544_ = lean_ctor_get(v___x_524_, 0);
lean_inc(v_a_544_);
v___y_503_ = v___x_524_;
v_a_504_ = v_a_544_;
goto v___jp_502_;
}
v___jp_502_:
{
uint8_t v___x_505_; 
v___x_505_ = l_Lean_Exception_isInterrupt(v_a_504_);
if (v___x_505_ == 0)
{
uint8_t v___x_506_; 
lean_inc_ref(v_a_504_);
v___x_506_ = l_Lean_Exception_isRuntime(v_a_504_);
if (v___x_506_ == 0)
{
lean_object* v___x_507_; 
lean_dec_ref(v___y_503_);
v___x_507_ = l_Lean_Meta_SavedState_restore___redArg(v_a_501_, v___y_496_, v___y_498_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v___x_509_; uint8_t v_isShared_510_; uint8_t v_isSharedCheck_514_; 
v_isSharedCheck_514_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_514_ == 0)
{
lean_object* v_unused_515_; 
v_unused_515_ = lean_ctor_get(v___x_507_, 0);
lean_dec(v_unused_515_);
v___x_509_ = v___x_507_;
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
else
{
lean_dec(v___x_507_);
v___x_509_ = lean_box(0);
v_isShared_510_ = v_isSharedCheck_514_;
goto v_resetjp_508_;
}
v_resetjp_508_:
{
lean_object* v___x_512_; 
if (v_isShared_510_ == 0)
{
lean_ctor_set_tag(v___x_509_, 1);
lean_ctor_set(v___x_509_, 0, v_a_504_);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v_a_504_);
v___x_512_ = v_reuseFailAlloc_513_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
return v___x_512_;
}
}
}
else
{
lean_object* v_a_516_; lean_object* v___x_518_; uint8_t v_isShared_519_; uint8_t v_isSharedCheck_523_; 
lean_dec_ref(v_a_504_);
v_a_516_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_523_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_523_ == 0)
{
v___x_518_ = v___x_507_;
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
else
{
lean_inc(v_a_516_);
lean_dec(v___x_507_);
v___x_518_ = lean_box(0);
v_isShared_519_ = v_isSharedCheck_523_;
goto v_resetjp_517_;
}
v_resetjp_517_:
{
lean_object* v___x_521_; 
if (v_isShared_519_ == 0)
{
v___x_521_ = v___x_518_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v_a_516_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
else
{
lean_dec_ref(v_a_504_);
lean_dec(v_a_501_);
return v___y_503_;
}
}
else
{
lean_dec_ref(v_a_504_);
lean_dec(v_a_501_);
return v___y_503_;
}
}
}
else
{
lean_object* v_a_545_; lean_object* v___x_547_; uint8_t v_isShared_548_; uint8_t v_isSharedCheck_552_; 
lean_dec_ref(v_x_493_);
v_a_545_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_552_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_552_ == 0)
{
v___x_547_ = v___x_500_;
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
else
{
lean_inc(v_a_545_);
lean_dec(v___x_500_);
v___x_547_ = lean_box(0);
v_isShared_548_ = v_isSharedCheck_552_;
goto v_resetjp_546_;
}
v_resetjp_546_:
{
lean_object* v___x_550_; 
if (v_isShared_548_ == 0)
{
v___x_550_ = v___x_547_;
goto v_reusejp_549_;
}
else
{
lean_object* v_reuseFailAlloc_551_; 
v_reuseFailAlloc_551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_551_, 0, v_a_545_);
v___x_550_ = v_reuseFailAlloc_551_;
goto v_reusejp_549_;
}
v_reusejp_549_:
{
return v___x_550_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* v_x_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_){
_start:
{
lean_object* v_res_560_; 
v_res_560_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_x_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_);
lean_dec(v___y_558_);
lean_dec_ref(v___y_557_);
lean_dec(v___y_556_);
lean_dec_ref(v___y_555_);
lean_dec(v___y_554_);
return v_res_560_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(lean_object* v_msgData_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_){
_start:
{
lean_object* v___x_567_; lean_object* v_env_568_; uint8_t v___x_569_; lean_object* v_env_570_; lean_object* v___x_571_; lean_object* v_toCold_572_; lean_object* v_mctx_573_; lean_object* v_lctx_574_; lean_object* v_options_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_567_ = lean_st_ref_get(v___y_565_);
v_env_568_ = lean_ctor_get(v___x_567_, 0);
lean_inc_ref(v_env_568_);
lean_dec(v___x_567_);
v___x_569_ = 0;
v_env_570_ = l_Lean_Environment_setRecordingDeps(v_env_568_, v___x_569_);
v___x_571_ = lean_st_ref_get(v___y_563_);
v_toCold_572_ = lean_ctor_get(v___y_564_, 0);
v_mctx_573_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_mctx_573_);
lean_dec(v___x_571_);
v_lctx_574_ = lean_ctor_get(v___y_562_, 2);
v_options_575_ = lean_ctor_get(v_toCold_572_, 2);
lean_inc_ref(v_options_575_);
lean_inc_ref(v_lctx_574_);
v___x_576_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_576_, 0, v_env_570_);
lean_ctor_set(v___x_576_, 1, v_mctx_573_);
lean_ctor_set(v___x_576_, 2, v_lctx_574_);
lean_ctor_set(v___x_576_, 3, v_options_575_);
v___x_577_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_msgData_561_);
v___x_578_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
return v___x_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object* v_msgData_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_){
_start:
{
lean_object* v_res_585_; 
v_res_585_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_579_, v___y_580_, v___y_581_, v___y_582_, v___y_583_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
lean_dec(v___y_581_);
lean_dec_ref(v___y_580_);
return v_res_585_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_586_; double v___x_587_; 
v___x_586_ = lean_unsigned_to_nat(0u);
v___x_587_ = lean_float_of_nat(v___x_586_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_591_, lean_object* v_msg_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
lean_object* v_ref_598_; lean_object* v___x_599_; lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_645_; 
v_ref_598_ = lean_ctor_get(v___y_595_, 2);
v___x_599_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_645_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_645_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_645_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v_traceState_605_; lean_object* v_env_606_; lean_object* v_nextMacroScope_607_; lean_object* v_ngen_608_; lean_object* v_auxDeclNGen_609_; lean_object* v_cache_610_; lean_object* v_recordedDeps_611_; lean_object* v_messages_612_; lean_object* v_infoState_613_; lean_object* v_snapshotTasks_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_644_; 
v___x_604_ = lean_st_ref_take(v___y_596_);
v_traceState_605_ = lean_ctor_get(v___x_604_, 4);
v_env_606_ = lean_ctor_get(v___x_604_, 0);
v_nextMacroScope_607_ = lean_ctor_get(v___x_604_, 1);
v_ngen_608_ = lean_ctor_get(v___x_604_, 2);
v_auxDeclNGen_609_ = lean_ctor_get(v___x_604_, 3);
v_cache_610_ = lean_ctor_get(v___x_604_, 5);
v_recordedDeps_611_ = lean_ctor_get(v___x_604_, 6);
v_messages_612_ = lean_ctor_get(v___x_604_, 7);
v_infoState_613_ = lean_ctor_get(v___x_604_, 8);
v_snapshotTasks_614_ = lean_ctor_get(v___x_604_, 9);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_644_ == 0)
{
v___x_616_ = v___x_604_;
v_isShared_617_ = v_isSharedCheck_644_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_snapshotTasks_614_);
lean_inc(v_infoState_613_);
lean_inc(v_messages_612_);
lean_inc(v_recordedDeps_611_);
lean_inc(v_cache_610_);
lean_inc(v_traceState_605_);
lean_inc(v_auxDeclNGen_609_);
lean_inc(v_ngen_608_);
lean_inc(v_nextMacroScope_607_);
lean_inc(v_env_606_);
lean_dec(v___x_604_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_644_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint64_t v_tid_618_; lean_object* v_traces_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_643_; 
v_tid_618_ = lean_ctor_get_uint64(v_traceState_605_, sizeof(void*)*1);
v_traces_619_ = lean_ctor_get(v_traceState_605_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v_traceState_605_);
if (v_isSharedCheck_643_ == 0)
{
v___x_621_ = v_traceState_605_;
v_isShared_622_ = v_isSharedCheck_643_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_traces_619_);
lean_dec(v_traceState_605_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_643_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; lean_object* v___x_624_; double v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_623_ = lean_box(0);
v___x_624_ = lean_box(0);
v___x_625_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_626_ = 0;
v___x_627_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_628_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_628_, 0, v_cls_591_);
lean_ctor_set(v___x_628_, 1, v___x_624_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_ctor_set_float(v___x_628_, sizeof(void*)*3, v___x_625_);
lean_ctor_set_float(v___x_628_, sizeof(void*)*3 + 8, v___x_625_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*3 + 16, v___x_626_);
v___x_629_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_630_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v_a_600_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_inc(v_ref_598_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v_ref_598_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Lean_PersistentArray_push___redArg(v_traces_619_, v___x_631_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_632_);
v___x_634_ = v___x_621_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_632_);
lean_ctor_set_uint64(v_reuseFailAlloc_642_, sizeof(void*)*1, v_tid_618_);
v___x_634_ = v_reuseFailAlloc_642_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v___x_634_);
v___x_636_ = v___x_616_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_env_606_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_nextMacroScope_607_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_ngen_608_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_auxDeclNGen_609_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_641_, 5, v_cache_610_);
lean_ctor_set(v_reuseFailAlloc_641_, 6, v_recordedDeps_611_);
lean_ctor_set(v_reuseFailAlloc_641_, 7, v_messages_612_);
lean_ctor_set(v_reuseFailAlloc_641_, 8, v_infoState_613_);
lean_ctor_set(v_reuseFailAlloc_641_, 9, v_snapshotTasks_614_);
v___x_636_ = v_reuseFailAlloc_641_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_st_ref_put(v___y_596_, v___x_636_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_623_);
v___x_639_ = v___x_602_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_623_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_646_, lean_object* v_msg_647_, lean_object* v___y_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_646_, v_msg_647_, v___y_648_, v___y_649_, v___y_650_, v___y_651_);
lean_dec(v___y_651_);
lean_dec_ref(v___y_650_);
lean_dec(v___y_649_);
lean_dec_ref(v___y_648_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_661_, lean_object* v_mvarId_662_, lean_object* v_fields_663_, lean_object* v_sz_664_, lean_object* v___x_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_){
_start:
{
size_t v_sz_boxed_674_; size_t v___x_15984__boxed_675_; uint8_t v___x_15986__boxed_676_; lean_object* v_res_677_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v___x_15984__boxed_675_ = lean_unbox_usize(v___x_665_);
lean_dec(v___x_665_);
v___x_15986__boxed_676_ = lean_unbox(v___x_667_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_661_, v_mvarId_662_, v_fields_663_, v_sz_boxed_674_, v___x_15984__boxed_675_, v___x_666_, v___x_15986__boxed_676_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
lean_dec(v___y_672_);
lean_dec_ref(v___y_671_);
lean_dec(v___y_670_);
lean_dec_ref(v___y_669_);
lean_dec(v___y_668_);
lean_dec_ref(v_fields_663_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_678_, lean_object* v_as_679_, size_t v_sz_680_, size_t v_i_681_, lean_object* v_b_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_){
_start:
{
uint8_t v___x_689_; 
v___x_689_ = lean_usize_dec_lt(v_i_681_, v_sz_680_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
v___x_690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_690_, 0, v_b_682_);
return v___x_690_;
}
else
{
lean_object* v_a_691_; lean_object* v_toInductionSubgoal_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_733_; 
lean_dec_ref(v_b_682_);
v_a_691_ = lean_array_uget(v_as_679_, v_i_681_);
v_toInductionSubgoal_692_ = lean_ctor_get(v_a_691_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_a_691_);
if (v_isSharedCheck_733_ == 0)
{
lean_object* v_unused_734_; 
v_unused_734_ = lean_ctor_get(v_a_691_, 1);
lean_dec(v_unused_734_);
v___x_694_ = v_a_691_;
v_isShared_695_ = v_isSharedCheck_733_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_toInductionSubgoal_692_);
lean_dec(v_a_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_733_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v_mvarId_696_; lean_object* v_fields_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; uint8_t v___x_701_; size_t v_sz_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___f_706_; lean_object* v___x_707_; 
v_mvarId_696_ = lean_ctor_get(v_toInductionSubgoal_692_, 0);
lean_inc_n(v_mvarId_696_, 2);
v_fields_697_ = lean_ctor_get(v_toInductionSubgoal_692_, 1);
lean_inc_ref(v_fields_697_);
v___x_698_ = lean_box(0);
v___x_699_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_700_ = lean_unsigned_to_nat(0u);
v___x_701_ = lean_nat_dec_eq(v_val_678_, v___x_700_);
v_sz_702_ = lean_array_size(v_fields_697_);
v___x_703_ = lean_box_usize(v_sz_702_);
v___x_704_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_705_ = lean_box(v___x_701_);
v___f_706_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_706_, 0, v_toInductionSubgoal_692_);
lean_closure_set(v___f_706_, 1, v_mvarId_696_);
lean_closure_set(v___f_706_, 2, v_fields_697_);
lean_closure_set(v___f_706_, 3, v___x_703_);
lean_closure_set(v___f_706_, 4, v___x_704_);
lean_closure_set(v___f_706_, 5, v___x_699_);
lean_closure_set(v___f_706_, 6, v___x_705_);
v___x_707_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_696_, v___f_706_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_);
if (lean_obj_tag(v___x_707_) == 0)
{
lean_object* v_a_708_; lean_object* v___x_710_; uint8_t v_isShared_711_; uint8_t v_isSharedCheck_724_; 
v_a_708_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_724_ == 0)
{
v___x_710_ = v___x_707_;
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
else
{
lean_inc(v_a_708_);
lean_dec(v___x_707_);
v___x_710_ = lean_box(0);
v_isShared_711_ = v_isSharedCheck_724_;
goto v_resetjp_709_;
}
v_resetjp_709_:
{
uint8_t v___x_712_; 
v___x_712_ = lean_unbox(v_a_708_);
lean_dec(v_a_708_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_716_; 
v___x_713_ = lean_box(v___x_701_);
v___x_714_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v___x_698_);
lean_ctor_set(v___x_694_, 0, v___x_714_);
v___x_716_ = v___x_694_;
goto v_reusejp_715_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_714_);
lean_ctor_set(v_reuseFailAlloc_720_, 1, v___x_698_);
v___x_716_ = v_reuseFailAlloc_720_;
goto v_reusejp_715_;
}
v_reusejp_715_:
{
lean_object* v___x_718_; 
if (v_isShared_711_ == 0)
{
lean_ctor_set(v___x_710_, 0, v___x_716_);
v___x_718_ = v___x_710_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_719_; 
v_reuseFailAlloc_719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_719_, 0, v___x_716_);
v___x_718_ = v_reuseFailAlloc_719_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
return v___x_718_;
}
}
}
else
{
size_t v___x_721_; size_t v___x_722_; 
lean_del_object(v___x_710_);
lean_del_object(v___x_694_);
v___x_721_ = ((size_t)1ULL);
v___x_722_ = lean_usize_add(v_i_681_, v___x_721_);
v_i_681_ = v___x_722_;
v_b_682_ = v___x_699_;
goto _start;
}
}
}
else
{
lean_object* v_a_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_del_object(v___x_694_);
v_a_725_ = lean_ctor_get(v___x_707_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v___x_707_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v___x_707_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_a_725_);
lean_dec(v___x_707_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_a_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
return v___x_730_;
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
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; 
v___x_745_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_746_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__6));
v___x_747_ = l_Lean_Name_append(v___x_746_, v___x_745_);
return v___x_747_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_749_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_750_ = l_Lean_stringToMessageData(v___x_749_);
return v___x_750_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_751_, lean_object* v_fvarId_752_, lean_object* v___x_753_, uint8_t v___x_754_, lean_object* v___x_755_, lean_object* v_val_756_, uint8_t v___x_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_MVarId_cases(v_mvarId_751_, v_fvarId_752_, v___x_753_, v___x_754_, v___x_755_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v_a_765_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v_toCold_798_; lean_object* v_options_799_; uint8_t v_hasTrace_800_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v_toCold_798_ = lean_ctor_get(v___y_761_, 0);
v_options_799_ = lean_ctor_get(v_toCold_798_, 2);
v_hasTrace_800_ = lean_ctor_get_uint8(v_options_799_, sizeof(void*)*1);
if (v_hasTrace_800_ == 0)
{
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
goto v___jp_766_;
}
else
{
lean_object* v_inheritedTraceOptions_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_inheritedTraceOptions_801_ = lean_ctor_get(v_toCold_798_, 11);
v___x_802_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_803_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_801_, v_options_799_, v___x_803_);
if (v___x_804_ == 0)
{
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
goto v___jp_766_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_805_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_806_ = lean_array_get_size(v_a_765_);
v___x_807_ = l_Nat_reprFast(v___x_806_);
v___x_808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___x_809_ = l_Lean_MessageData_ofFormat(v___x_808_);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_805_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_802_, v___x_810_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_dec_ref_known(v___x_811_, 1);
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
goto v___jp_766_;
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_a_765_);
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
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
v___jp_766_:
{
lean_object* v___x_772_; size_t v_sz_773_; size_t v___x_774_; lean_object* v___x_775_; 
v___x_772_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_773_ = lean_array_size(v_a_765_);
v___x_774_ = ((size_t)0ULL);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_756_, v_a_765_, v_sz_773_, v___x_774_, v___x_772_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_);
lean_dec(v_a_765_);
if (lean_obj_tag(v___x_775_) == 0)
{
lean_object* v_a_776_; lean_object* v___x_778_; uint8_t v_isShared_779_; uint8_t v_isSharedCheck_789_; 
v_a_776_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_789_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_789_ == 0)
{
v___x_778_ = v___x_775_;
v_isShared_779_ = v_isSharedCheck_789_;
goto v_resetjp_777_;
}
else
{
lean_inc(v_a_776_);
lean_dec(v___x_775_);
v___x_778_ = lean_box(0);
v_isShared_779_ = v_isSharedCheck_789_;
goto v_resetjp_777_;
}
v_resetjp_777_:
{
lean_object* v_fst_780_; 
v_fst_780_ = lean_ctor_get(v_a_776_, 0);
lean_inc(v_fst_780_);
lean_dec(v_a_776_);
if (lean_obj_tag(v_fst_780_) == 0)
{
lean_object* v___x_781_; lean_object* v___x_783_; 
v___x_781_ = lean_box(v___x_757_);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v___x_781_);
v___x_783_ = v___x_778_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v___x_781_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
else
{
lean_object* v_val_785_; lean_object* v___x_787_; 
v_val_785_ = lean_ctor_get(v_fst_780_, 0);
lean_inc(v_val_785_);
lean_dec_ref_known(v_fst_780_, 1);
if (v_isShared_779_ == 0)
{
lean_ctor_set(v___x_778_, 0, v_val_785_);
v___x_787_ = v___x_778_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_val_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
else
{
lean_object* v_a_790_; lean_object* v___x_792_; uint8_t v_isShared_793_; uint8_t v_isSharedCheck_797_; 
v_a_790_ = lean_ctor_get(v___x_775_, 0);
v_isSharedCheck_797_ = !lean_is_exclusive(v___x_775_);
if (v_isSharedCheck_797_ == 0)
{
v___x_792_ = v___x_775_;
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
else
{
lean_inc(v_a_790_);
lean_dec(v___x_775_);
v___x_792_ = lean_box(0);
v_isShared_793_ = v_isSharedCheck_797_;
goto v_resetjp_791_;
}
v_resetjp_791_:
{
lean_object* v___x_795_; 
if (v_isShared_793_ == 0)
{
v___x_795_ = v___x_792_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v_a_790_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_866_; 
v_a_820_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_866_ == 0)
{
v___x_822_ = v___x_764_;
v_isShared_823_ = v_isSharedCheck_866_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_764_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_866_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v___x_824_; 
v___x_824_ = l_Lean_Exception_isInterrupt(v_a_820_);
if (v___x_824_ == 0)
{
uint8_t v___x_825_; 
lean_inc(v_a_820_);
v___x_825_ = l_Lean_Exception_isRuntime(v_a_820_);
if (v___x_825_ == 0)
{
lean_object* v_toCold_826_; lean_object* v_options_827_; uint8_t v_hasTrace_828_; 
v_toCold_826_ = lean_ctor_get(v___y_761_, 0);
v_options_827_ = lean_ctor_get(v_toCold_826_, 2);
v_hasTrace_828_ = lean_ctor_get_uint8(v_options_827_, sizeof(void*)*1);
if (v_hasTrace_828_ == 0)
{
lean_object* v___x_829_; lean_object* v___x_831_; 
lean_dec(v_a_820_);
v___x_829_ = lean_box(v___x_754_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_829_);
v___x_831_ = v___x_822_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v___x_829_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
else
{
lean_object* v_inheritedTraceOptions_833_; lean_object* v___x_834_; lean_object* v___x_835_; uint8_t v___x_836_; 
v_inheritedTraceOptions_833_ = lean_ctor_get(v_toCold_826_, 11);
v___x_834_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_835_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_836_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_833_, v_options_827_, v___x_835_);
if (v___x_836_ == 0)
{
lean_object* v___x_837_; lean_object* v___x_839_; 
lean_dec(v_a_820_);
v___x_837_ = lean_box(v___x_754_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_837_);
v___x_839_ = v___x_822_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_840_; 
v_reuseFailAlloc_840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_840_, 0, v___x_837_);
v___x_839_ = v_reuseFailAlloc_840_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
return v___x_839_;
}
}
else
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_del_object(v___x_822_);
v___x_841_ = l_Lean_Exception_toMessageData(v_a_820_);
v___x_842_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_834_, v___x_841_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_850_; 
v_isSharedCheck_850_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_850_ == 0)
{
lean_object* v_unused_851_; 
v_unused_851_ = lean_ctor_get(v___x_842_, 0);
lean_dec(v_unused_851_);
v___x_844_ = v___x_842_;
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
else
{
lean_dec(v___x_842_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_850_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v___x_846_; lean_object* v___x_848_; 
v___x_846_ = lean_box(v___x_754_);
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 0, v___x_846_);
v___x_848_ = v___x_844_;
goto v_reusejp_847_;
}
else
{
lean_object* v_reuseFailAlloc_849_; 
v_reuseFailAlloc_849_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_849_, 0, v___x_846_);
v___x_848_ = v_reuseFailAlloc_849_;
goto v_reusejp_847_;
}
v_reusejp_847_:
{
return v___x_848_;
}
}
}
else
{
lean_object* v_a_852_; lean_object* v___x_854_; uint8_t v_isShared_855_; uint8_t v_isSharedCheck_859_; 
v_a_852_ = lean_ctor_get(v___x_842_, 0);
v_isSharedCheck_859_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_859_ == 0)
{
v___x_854_ = v___x_842_;
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
else
{
lean_inc(v_a_852_);
lean_dec(v___x_842_);
v___x_854_ = lean_box(0);
v_isShared_855_ = v_isSharedCheck_859_;
goto v_resetjp_853_;
}
v_resetjp_853_:
{
lean_object* v___x_857_; 
if (v_isShared_855_ == 0)
{
v___x_857_ = v___x_854_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_858_; 
v_reuseFailAlloc_858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_858_, 0, v_a_852_);
v___x_857_ = v_reuseFailAlloc_858_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
return v___x_857_;
}
}
}
}
}
}
else
{
lean_object* v___x_861_; 
if (v_isShared_823_ == 0)
{
v___x_861_ = v___x_822_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_820_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
else
{
lean_object* v___x_864_; 
if (v_isShared_823_ == 0)
{
v___x_864_ = v___x_822_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_820_);
v___x_864_ = v_reuseFailAlloc_865_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
return v___x_864_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_867_, lean_object* v_fvarId_868_, lean_object* v___x_869_, lean_object* v___x_870_, lean_object* v___x_871_, lean_object* v_val_872_, lean_object* v___x_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_){
_start:
{
uint8_t v___x_16106__boxed_880_; uint8_t v___x_16109__boxed_881_; lean_object* v_res_882_; 
v___x_16106__boxed_880_ = lean_unbox(v___x_870_);
v___x_16109__boxed_881_ = lean_unbox(v___x_873_);
v_res_882_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_867_, v_fvarId_868_, v___x_869_, v___x_16106__boxed_880_, v___x_871_, v_val_872_, v___x_16109__boxed_881_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec(v_val_872_);
return v_res_882_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; 
v___x_884_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_885_ = l_Lean_stringToMessageData(v___x_884_);
return v___x_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_886_, lean_object* v_fvarId_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_){
_start:
{
lean_object* v___x_898_; lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_898_ = lean_st_ref_get(v_a_888_);
v___x_899_ = lean_unsigned_to_nat(0u);
v___x_900_ = lean_nat_dec_eq(v___x_898_, v___x_899_);
if (v___x_900_ == 0)
{
uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___f_910_; lean_object* v___x_911_; 
v___x_901_ = 1;
v___x_902_ = lean_st_ref_take(v_a_888_);
v___x_903_ = lean_unsigned_to_nat(1u);
v___x_904_ = lean_nat_sub(v___x_902_, v___x_903_);
lean_dec(v___x_902_);
v___x_905_ = lean_st_ref_put(v_a_888_, v___x_904_);
v___x_906_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_907_ = lean_box(0);
v___x_908_ = lean_box(v___x_900_);
v___x_909_ = lean_box(v___x_901_);
v___f_910_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_910_, 0, v_mvarId_886_);
lean_closure_set(v___f_910_, 1, v_fvarId_887_);
lean_closure_set(v___f_910_, 2, v___x_906_);
lean_closure_set(v___f_910_, 3, v___x_908_);
lean_closure_set(v___f_910_, 4, v___x_907_);
lean_closure_set(v___f_910_, 5, v___x_898_);
lean_closure_set(v___f_910_, 6, v___x_909_);
v___x_911_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_910_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
return v___x_911_;
}
else
{
lean_object* v_toCold_912_; lean_object* v_options_913_; uint8_t v_hasTrace_914_; 
lean_dec(v___x_898_);
lean_dec(v_fvarId_887_);
lean_dec(v_mvarId_886_);
v_toCold_912_ = lean_ctor_get(v_a_891_, 0);
v_options_913_ = lean_ctor_get(v_toCold_912_, 2);
v_hasTrace_914_ = lean_ctor_get_uint8(v_options_913_, sizeof(void*)*1);
if (v_hasTrace_914_ == 0)
{
goto v___jp_894_;
}
else
{
lean_object* v_inheritedTraceOptions_915_; lean_object* v___x_916_; lean_object* v___x_917_; uint8_t v___x_918_; 
v_inheritedTraceOptions_915_ = lean_ctor_get(v_toCold_912_, 11);
v___x_916_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_917_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_918_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_915_, v_options_913_, v___x_917_);
if (v___x_918_ == 0)
{
goto v___jp_894_;
}
else
{
lean_object* v___x_919_; lean_object* v___x_920_; 
v___x_919_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_920_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_916_, v___x_919_, v_a_889_, v_a_890_, v_a_891_, v_a_892_);
if (lean_obj_tag(v___x_920_) == 0)
{
lean_dec_ref_known(v___x_920_, 1);
goto v___jp_894_;
}
else
{
lean_object* v_a_921_; lean_object* v___x_923_; uint8_t v_isShared_924_; uint8_t v_isSharedCheck_928_; 
v_a_921_ = lean_ctor_get(v___x_920_, 0);
v_isSharedCheck_928_ = !lean_is_exclusive(v___x_920_);
if (v_isSharedCheck_928_ == 0)
{
v___x_923_ = v___x_920_;
v_isShared_924_ = v_isSharedCheck_928_;
goto v_resetjp_922_;
}
else
{
lean_inc(v_a_921_);
lean_dec(v___x_920_);
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
v___jp_894_:
{
uint8_t v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; 
v___x_895_ = 0;
v___x_896_ = lean_box(v___x_895_);
v___x_897_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_897_, 0, v___x_896_);
return v___x_897_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_929_, lean_object* v___x_930_, lean_object* v_as_931_, size_t v_sz_932_, size_t v_i_933_, lean_object* v_b_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_){
_start:
{
lean_object* v_a_942_; uint8_t v___x_946_; 
v___x_946_ = lean_usize_dec_lt(v_i_933_, v_sz_932_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
lean_dec(v___x_930_);
lean_dec_ref(v___x_929_);
v___x_947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_947_, 0, v_b_934_);
return v___x_947_;
}
else
{
lean_object* v_subst_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v_a_951_; lean_object* v___x_952_; uint8_t v___x_953_; 
lean_dec_ref(v_b_934_);
v_subst_948_ = lean_ctor_get(v___x_929_, 2);
v___x_949_ = lean_box(0);
v___x_950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_951_ = lean_array_uget_borrowed(v_as_931_, v_i_933_);
lean_inc(v_subst_948_);
v___x_952_ = l_Lean_Meta_FVarSubst_apply(v_subst_948_, v_a_951_);
v___x_953_ = l_Lean_Expr_isFVar(v___x_952_);
if (v___x_953_ == 0)
{
lean_dec_ref(v___x_952_);
v_a_942_ = v___x_950_;
goto v___jp_941_;
}
else
{
lean_object* v___x_954_; lean_object* v___x_955_; 
v___x_954_ = l_Lean_Expr_fvarId_x21(v___x_952_);
lean_dec_ref(v___x_952_);
lean_inc(v___x_954_);
v___x_955_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_954_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; uint8_t v___x_957_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
lean_inc(v_a_956_);
lean_dec_ref_known(v___x_955_, 1);
v___x_957_ = lean_unbox(v_a_956_);
lean_dec(v_a_956_);
if (v___x_957_ == 0)
{
lean_dec(v___x_954_);
v_a_942_ = v___x_950_;
goto v___jp_941_;
}
else
{
lean_object* v___x_958_; 
lean_inc(v___x_930_);
v___x_958_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_930_, v___x_954_, v___y_935_, v___y_936_, v___y_937_, v___y_938_, v___y_939_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; lean_object* v___x_961_; uint8_t v_isShared_962_; uint8_t v_isSharedCheck_970_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_970_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_970_ == 0)
{
v___x_961_ = v___x_958_;
v_isShared_962_ = v_isSharedCheck_970_;
goto v_resetjp_960_;
}
else
{
lean_inc(v_a_959_);
lean_dec(v___x_958_);
v___x_961_ = lean_box(0);
v_isShared_962_ = v_isSharedCheck_970_;
goto v_resetjp_960_;
}
v_resetjp_960_:
{
uint8_t v___x_963_; 
v___x_963_ = lean_unbox(v_a_959_);
lean_dec(v_a_959_);
if (v___x_963_ == 0)
{
lean_del_object(v___x_961_);
v_a_942_ = v___x_950_;
goto v___jp_941_;
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
lean_dec(v___x_930_);
lean_dec_ref(v___x_929_);
v___x_964_ = lean_box(v___x_953_);
v___x_965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_965_, 0, v___x_964_);
v___x_966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_949_);
if (v_isShared_962_ == 0)
{
lean_ctor_set(v___x_961_, 0, v___x_966_);
v___x_968_ = v___x_961_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
else
{
lean_object* v_a_971_; lean_object* v___x_973_; uint8_t v_isShared_974_; uint8_t v_isSharedCheck_978_; 
lean_dec(v___x_930_);
lean_dec_ref(v___x_929_);
v_a_971_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_978_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_978_ == 0)
{
v___x_973_ = v___x_958_;
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
else
{
lean_inc(v_a_971_);
lean_dec(v___x_958_);
v___x_973_ = lean_box(0);
v_isShared_974_ = v_isSharedCheck_978_;
goto v_resetjp_972_;
}
v_resetjp_972_:
{
lean_object* v___x_976_; 
if (v_isShared_974_ == 0)
{
v___x_976_ = v___x_973_;
goto v_reusejp_975_;
}
else
{
lean_object* v_reuseFailAlloc_977_; 
v_reuseFailAlloc_977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_977_, 0, v_a_971_);
v___x_976_ = v_reuseFailAlloc_977_;
goto v_reusejp_975_;
}
v_reusejp_975_:
{
return v___x_976_;
}
}
}
}
}
else
{
lean_object* v_a_979_; lean_object* v___x_981_; uint8_t v_isShared_982_; uint8_t v_isSharedCheck_986_; 
lean_dec(v___x_954_);
lean_dec(v___x_930_);
lean_dec_ref(v___x_929_);
v_a_979_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_986_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_986_ == 0)
{
v___x_981_ = v___x_955_;
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
else
{
lean_inc(v_a_979_);
lean_dec(v___x_955_);
v___x_981_ = lean_box(0);
v_isShared_982_ = v_isSharedCheck_986_;
goto v_resetjp_980_;
}
v_resetjp_980_:
{
lean_object* v___x_984_; 
if (v_isShared_982_ == 0)
{
v___x_984_ = v___x_981_;
goto v_reusejp_983_;
}
else
{
lean_object* v_reuseFailAlloc_985_; 
v_reuseFailAlloc_985_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_985_, 0, v_a_979_);
v___x_984_ = v_reuseFailAlloc_985_;
goto v_reusejp_983_;
}
v_reusejp_983_:
{
return v___x_984_;
}
}
}
}
}
v___jp_941_:
{
size_t v___x_943_; size_t v___x_944_; 
v___x_943_ = ((size_t)1ULL);
v___x_944_ = lean_usize_add(v_i_933_, v___x_943_);
lean_inc_ref(v_a_942_);
v_i_933_ = v___x_944_;
v_b_934_ = v_a_942_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_987_, lean_object* v_mvarId_988_, lean_object* v_fields_989_, size_t v_sz_990_, size_t v___x_991_, lean_object* v___x_992_, uint8_t v___x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_987_, v_mvarId_988_, v_fields_989_, v_sz_990_, v___x_991_, v___x_992_, v___y_994_, v___y_995_, v___y_996_, v___y_997_, v___y_998_);
if (lean_obj_tag(v___x_1000_) == 0)
{
lean_object* v_a_1001_; lean_object* v___x_1003_; uint8_t v_isShared_1004_; uint8_t v_isSharedCheck_1014_; 
v_a_1001_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1014_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1014_ == 0)
{
v___x_1003_ = v___x_1000_;
v_isShared_1004_ = v_isSharedCheck_1014_;
goto v_resetjp_1002_;
}
else
{
lean_inc(v_a_1001_);
lean_dec(v___x_1000_);
v___x_1003_ = lean_box(0);
v_isShared_1004_ = v_isSharedCheck_1014_;
goto v_resetjp_1002_;
}
v_resetjp_1002_:
{
lean_object* v_fst_1005_; 
v_fst_1005_ = lean_ctor_get(v_a_1001_, 0);
lean_inc(v_fst_1005_);
lean_dec(v_a_1001_);
if (lean_obj_tag(v_fst_1005_) == 0)
{
lean_object* v___x_1006_; lean_object* v___x_1008_; 
v___x_1006_ = lean_box(v___x_993_);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v___x_1006_);
v___x_1008_ = v___x_1003_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v___x_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
else
{
lean_object* v_val_1010_; lean_object* v___x_1012_; 
v_val_1010_ = lean_ctor_get(v_fst_1005_, 0);
lean_inc(v_val_1010_);
lean_dec_ref_known(v_fst_1005_, 1);
if (v_isShared_1004_ == 0)
{
lean_ctor_set(v___x_1003_, 0, v_val_1010_);
v___x_1012_ = v___x_1003_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1013_; 
v_reuseFailAlloc_1013_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_val_1010_);
v___x_1012_ = v_reuseFailAlloc_1013_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
return v___x_1012_;
}
}
}
}
else
{
lean_object* v_a_1015_; lean_object* v___x_1017_; uint8_t v_isShared_1018_; uint8_t v_isSharedCheck_1022_; 
v_a_1015_ = lean_ctor_get(v___x_1000_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v___x_1000_);
if (v_isSharedCheck_1022_ == 0)
{
v___x_1017_ = v___x_1000_;
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
else
{
lean_inc(v_a_1015_);
lean_dec(v___x_1000_);
v___x_1017_ = lean_box(0);
v_isShared_1018_ = v_isSharedCheck_1022_;
goto v_resetjp_1016_;
}
v_resetjp_1016_:
{
lean_object* v___x_1020_; 
if (v_isShared_1018_ == 0)
{
v___x_1020_ = v___x_1017_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v_a_1015_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1023_, lean_object* v_as_1024_, lean_object* v_sz_1025_, lean_object* v_i_1026_, lean_object* v_b_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
size_t v_sz_boxed_1034_; size_t v_i_boxed_1035_; lean_object* v_res_1036_; 
v_sz_boxed_1034_ = lean_unbox_usize(v_sz_1025_);
lean_dec(v_sz_1025_);
v_i_boxed_1035_ = lean_unbox_usize(v_i_1026_);
lean_dec(v_i_1026_);
v_res_1036_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1023_, v_as_1024_, v_sz_boxed_1034_, v_i_boxed_1035_, v_b_1027_, v___y_1028_, v___y_1029_, v___y_1030_, v___y_1031_, v___y_1032_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v___y_1029_);
lean_dec(v___y_1028_);
lean_dec_ref(v_as_1024_);
lean_dec(v_val_1023_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1037_, lean_object* v___x_1038_, lean_object* v_as_1039_, lean_object* v_sz_1040_, lean_object* v_i_1041_, lean_object* v_b_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_){
_start:
{
size_t v_sz_boxed_1049_; size_t v_i_boxed_1050_; lean_object* v_res_1051_; 
v_sz_boxed_1049_ = lean_unbox_usize(v_sz_1040_);
lean_dec(v_sz_1040_);
v_i_boxed_1050_ = lean_unbox_usize(v_i_1041_);
lean_dec(v_i_1041_);
v_res_1051_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1037_, v___x_1038_, v_as_1039_, v_sz_boxed_1049_, v_i_boxed_1050_, v_b_1042_, v___y_1043_, v___y_1044_, v___y_1045_, v___y_1046_, v___y_1047_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v___y_1044_);
lean_dec(v___y_1043_);
lean_dec_ref(v_as_1039_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1052_, lean_object* v_fvarId_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_){
_start:
{
lean_object* v_res_1060_; 
v_res_1060_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1052_, v_fvarId_1053_, v_a_1054_, v_a_1055_, v_a_1056_, v_a_1057_, v_a_1058_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
lean_dec_ref(v_a_1055_);
lean_dec(v_a_1054_);
return v_res_1060_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1061_, lean_object* v_msg_1062_, lean_object* v___y_1063_, lean_object* v___y_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_){
_start:
{
lean_object* v___x_1069_; 
v___x_1069_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1061_, v_msg_1062_, v___y_1064_, v___y_1065_, v___y_1066_, v___y_1067_);
return v___x_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1070_, lean_object* v_msg_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v_res_1078_; 
v_res_1078_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1070_, v_msg_1071_, v___y_1072_, v___y_1073_, v___y_1074_, v___y_1075_, v___y_1076_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
lean_dec_ref(v___y_1073_);
lean_dec(v___y_1072_);
return v_res_1078_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1079_, lean_object* v___y_1080_, lean_object* v___y_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_Meta_saveState___redArg(v___y_1081_, v___y_1083_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v_a_1086_; lean_object* v___y_1088_; lean_object* v_a_1089_; lean_object* v___x_1109_; 
v_a_1086_ = lean_ctor_get(v___x_1085_, 0);
lean_inc(v_a_1086_);
lean_dec_ref_known(v___x_1085_, 1);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
lean_inc(v___y_1081_);
lean_inc_ref(v___y_1080_);
v___x_1109_ = lean_apply_5(v_x_1079_, v___y_1080_, v___y_1081_, v___y_1082_, v___y_1083_, lean_box(0));
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; uint8_t v___x_1111_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
v___x_1111_ = lean_unbox(v_a_1110_);
if (v___x_1111_ == 0)
{
lean_object* v___x_1112_; 
lean_dec_ref_known(v___x_1109_, 1);
lean_inc(v_a_1086_);
v___x_1112_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1086_, v___y_1081_, v___y_1083_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v_a_1086_);
v_isSharedCheck_1119_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1119_ == 0)
{
lean_object* v_unused_1120_; 
v_unused_1120_ = lean_ctor_get(v___x_1112_, 0);
lean_dec(v_unused_1120_);
v___x_1114_ = v___x_1112_;
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
else
{
lean_dec(v___x_1112_);
v___x_1114_ = lean_box(0);
v_isShared_1115_ = v_isSharedCheck_1119_;
goto v_resetjp_1113_;
}
v_resetjp_1113_:
{
lean_object* v___x_1117_; 
if (v_isShared_1115_ == 0)
{
lean_ctor_set(v___x_1114_, 0, v_a_1110_);
v___x_1117_ = v___x_1114_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1118_; 
v_reuseFailAlloc_1118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_a_1110_);
v___x_1117_ = v_reuseFailAlloc_1118_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
return v___x_1117_;
}
}
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_a_1110_);
v_a_1121_ = lean_ctor_get(v___x_1112_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1112_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1112_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1112_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
lean_inc(v_a_1121_);
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
v___y_1088_ = v___x_1126_;
v_a_1089_ = v_a_1121_;
goto v___jp_1087_;
}
}
}
}
else
{
lean_dec(v_a_1110_);
lean_dec(v_a_1086_);
return v___x_1109_;
}
}
else
{
lean_object* v_a_1129_; 
v_a_1129_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1129_);
v___y_1088_ = v___x_1109_;
v_a_1089_ = v_a_1129_;
goto v___jp_1087_;
}
v___jp_1087_:
{
uint8_t v___x_1090_; 
v___x_1090_ = l_Lean_Exception_isInterrupt(v_a_1089_);
if (v___x_1090_ == 0)
{
uint8_t v___x_1091_; 
lean_inc_ref(v_a_1089_);
v___x_1091_ = l_Lean_Exception_isRuntime(v_a_1089_);
if (v___x_1091_ == 0)
{
lean_object* v___x_1092_; 
lean_dec_ref(v___y_1088_);
v___x_1092_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1086_, v___y_1081_, v___y_1083_);
if (lean_obj_tag(v___x_1092_) == 0)
{
lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1099_; 
v_isSharedCheck_1099_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1099_ == 0)
{
lean_object* v_unused_1100_; 
v_unused_1100_ = lean_ctor_get(v___x_1092_, 0);
lean_dec(v_unused_1100_);
v___x_1094_ = v___x_1092_;
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
else
{
lean_dec(v___x_1092_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1099_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1097_; 
if (v_isShared_1095_ == 0)
{
lean_ctor_set_tag(v___x_1094_, 1);
lean_ctor_set(v___x_1094_, 0, v_a_1089_);
v___x_1097_ = v___x_1094_;
goto v_reusejp_1096_;
}
else
{
lean_object* v_reuseFailAlloc_1098_; 
v_reuseFailAlloc_1098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1089_);
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
lean_object* v_a_1101_; lean_object* v___x_1103_; uint8_t v_isShared_1104_; uint8_t v_isSharedCheck_1108_; 
lean_dec_ref(v_a_1089_);
v_a_1101_ = lean_ctor_get(v___x_1092_, 0);
v_isSharedCheck_1108_ = !lean_is_exclusive(v___x_1092_);
if (v_isSharedCheck_1108_ == 0)
{
v___x_1103_ = v___x_1092_;
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
else
{
lean_inc(v_a_1101_);
lean_dec(v___x_1092_);
v___x_1103_ = lean_box(0);
v_isShared_1104_ = v_isSharedCheck_1108_;
goto v_resetjp_1102_;
}
v_resetjp_1102_:
{
lean_object* v___x_1106_; 
if (v_isShared_1104_ == 0)
{
v___x_1106_ = v___x_1103_;
goto v_reusejp_1105_;
}
else
{
lean_object* v_reuseFailAlloc_1107_; 
v_reuseFailAlloc_1107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1107_, 0, v_a_1101_);
v___x_1106_ = v_reuseFailAlloc_1107_;
goto v_reusejp_1105_;
}
v_reusejp_1105_:
{
return v___x_1106_;
}
}
}
}
else
{
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1086_);
return v___y_1088_;
}
}
else
{
lean_dec_ref(v_a_1089_);
lean_dec(v_a_1086_);
return v___y_1088_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v_x_1079_);
v_a_1130_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1085_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1085_);
v___x_1132_ = lean_box(0);
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
v_resetjp_1131_:
{
lean_object* v___x_1135_; 
if (v_isShared_1133_ == 0)
{
v___x_1135_ = v___x_1132_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_, lean_object* v___y_1142_, lean_object* v___y_1143_){
_start:
{
lean_object* v_res_1144_; 
v_res_1144_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1138_, v___y_1139_, v___y_1140_, v___y_1141_, v___y_1142_);
lean_dec(v___y_1142_);
lean_dec_ref(v___y_1141_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
return v_res_1144_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1145_, lean_object* v_x_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v___x_1152_; 
v___x_1152_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1145_, v_x_1146_, v___y_1147_, v___y_1148_, v___y_1149_, v___y_1150_);
if (lean_obj_tag(v___x_1152_) == 0)
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
v_a_1153_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1152_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
else
{
lean_object* v_a_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1168_; 
v_a_1161_ = lean_ctor_get(v___x_1152_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1152_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1163_ = v___x_1152_;
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_a_1161_);
lean_dec(v___x_1152_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1168_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1166_; 
if (v_isShared_1164_ == 0)
{
v___x_1166_ = v___x_1163_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_a_1161_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1169_, lean_object* v_x_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_, lean_object* v___y_1175_){
_start:
{
lean_object* v_res_1176_; 
v_res_1176_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1169_, v_x_1170_, v___y_1171_, v___y_1172_, v___y_1173_, v___y_1174_);
lean_dec(v___y_1174_);
lean_dec_ref(v___y_1173_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
return v_res_1176_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1177_, lean_object* v_mvarId_1178_, lean_object* v_x_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_, lean_object* v___y_1183_){
_start:
{
lean_object* v___x_1185_; 
v___x_1185_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1178_, v_x_1179_, v___y_1180_, v___y_1181_, v___y_1182_, v___y_1183_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1186_, lean_object* v_mvarId_1187_, lean_object* v_x_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1186_, v_mvarId_1187_, v_x_1188_, v___y_1189_, v___y_1190_, v___y_1191_, v___y_1192_);
lean_dec(v___y_1192_);
lean_dec_ref(v___y_1191_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
return v_res_1194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1195_, lean_object* v_fuel_1196_, lean_object* v_fvarId_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v___x_1203_; 
v___x_1203_ = l_Lean_MVarId_exfalso(v_mvarId_1195_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1203_) == 0)
{
lean_object* v_a_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
lean_inc(v_a_1204_);
lean_dec_ref_known(v___x_1203_, 1);
v___x_1205_ = lean_st_mk_ref(v_fuel_1196_);
v___x_1206_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1204_, v_fvarId_1197_, v___x_1205_, v___y_1198_, v___y_1199_, v___y_1200_, v___y_1201_);
if (lean_obj_tag(v___x_1206_) == 0)
{
lean_object* v_a_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1215_; 
v_a_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_a_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = lean_st_ref_get(v___x_1205_);
lean_dec(v___x_1205_);
lean_dec(v___x_1211_);
if (v_isShared_1210_ == 0)
{
v___x_1213_ = v___x_1209_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v_a_1207_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
else
{
lean_dec(v___x_1205_);
return v___x_1206_;
}
}
else
{
lean_object* v_a_1216_; lean_object* v___x_1218_; uint8_t v_isShared_1219_; uint8_t v_isSharedCheck_1223_; 
lean_dec(v_fvarId_1197_);
lean_dec(v_fuel_1196_);
v_a_1216_ = lean_ctor_get(v___x_1203_, 0);
v_isSharedCheck_1223_ = !lean_is_exclusive(v___x_1203_);
if (v_isSharedCheck_1223_ == 0)
{
v___x_1218_ = v___x_1203_;
v_isShared_1219_ = v_isSharedCheck_1223_;
goto v_resetjp_1217_;
}
else
{
lean_inc(v_a_1216_);
lean_dec(v___x_1203_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1224_, lean_object* v_fuel_1225_, lean_object* v_fvarId_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_){
_start:
{
lean_object* v_res_1232_; 
v_res_1232_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1224_, v_fuel_1225_, v_fvarId_1226_, v___y_1227_, v___y_1228_, v___y_1229_, v___y_1230_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
return v_res_1232_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1233_, lean_object* v___f_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1233_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
if (lean_obj_tag(v___x_1240_) == 0)
{
lean_object* v_a_1241_; uint8_t v___x_1242_; 
v_a_1241_ = lean_ctor_get(v___x_1240_, 0);
v___x_1242_ = lean_unbox(v_a_1241_);
if (v___x_1242_ == 0)
{
lean_dec_ref(v___f_1234_);
return v___x_1240_;
}
else
{
lean_object* v___x_1243_; 
lean_dec_ref_known(v___x_1240_, 1);
v___x_1243_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1234_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
return v___x_1243_;
}
}
else
{
lean_dec_ref(v___f_1234_);
return v___x_1240_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1244_, lean_object* v___f_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_){
_start:
{
lean_object* v_res_1251_; 
v_res_1251_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1244_, v___f_1245_, v___y_1246_, v___y_1247_, v___y_1248_, v___y_1249_);
lean_dec(v___y_1249_);
lean_dec_ref(v___y_1248_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
return v_res_1251_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1252_, lean_object* v_fvarId_1253_, lean_object* v_fuel_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_, lean_object* v_a_1257_, lean_object* v_a_1258_){
_start:
{
lean_object* v___f_1260_; lean_object* v___f_1261_; lean_object* v___x_1262_; 
lean_inc(v_fvarId_1253_);
lean_inc(v_mvarId_1252_);
v___f_1260_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1260_, 0, v_mvarId_1252_);
lean_closure_set(v___f_1260_, 1, v_fuel_1254_);
lean_closure_set(v___f_1260_, 2, v_fvarId_1253_);
v___f_1261_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1261_, 0, v_fvarId_1253_);
lean_closure_set(v___f_1261_, 1, v___f_1260_);
v___x_1262_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1252_, v___f_1261_, v_a_1255_, v_a_1256_, v_a_1257_, v_a_1258_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1263_, lean_object* v_fvarId_1264_, lean_object* v_fuel_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_){
_start:
{
lean_object* v_res_1271_; 
v_res_1271_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1263_, v_fvarId_1264_, v_fuel_1265_, v_a_1266_, v_a_1267_, v_a_1268_, v_a_1269_);
lean_dec(v_a_1269_);
lean_dec_ref(v_a_1268_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
return v_res_1271_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1272_){
_start:
{
uint8_t v___x_1273_; 
v___x_1273_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1272_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1274_){
_start:
{
uint8_t v_res_1275_; lean_object* v_r_1276_; 
v_res_1275_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1274_);
v_r_1276_ = lean_box(v_res_1275_);
return v_r_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1277_, lean_object* v_acc_1278_){
_start:
{
if (lean_obj_tag(v_e_1277_) == 7)
{
lean_object* v_binderType_1279_; lean_object* v_body_1280_; uint8_t v___y_1282_; lean_object* v___x_1286_; uint8_t v___x_1287_; 
v_binderType_1279_ = lean_ctor_get(v_e_1277_, 1);
v_body_1280_ = lean_ctor_get(v_e_1277_, 2);
v___x_1286_ = lean_unsigned_to_nat(0u);
v___x_1287_ = lean_expr_has_loose_bvar(v_body_1280_, v___x_1286_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1288_; 
v___x_1288_ = l_Lean_Expr_isEq(v_binderType_1279_);
if (v___x_1288_ == 0)
{
uint8_t v___x_1289_; 
v___x_1289_ = l_Lean_Expr_isHEq(v_binderType_1279_);
v___y_1282_ = v___x_1289_;
goto v___jp_1281_;
}
else
{
v___y_1282_ = v___x_1288_;
goto v___jp_1281_;
}
}
else
{
uint8_t v___x_1290_; 
v___x_1290_ = 0;
v___y_1282_ = v___x_1290_;
goto v___jp_1281_;
}
v___jp_1281_:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; 
v___x_1283_ = lean_box(v___y_1282_);
v___x_1284_ = lean_array_push(v_acc_1278_, v___x_1283_);
v_e_1277_ = v_body_1280_;
v_acc_1278_ = v___x_1284_;
goto _start;
}
}
else
{
return v_acc_1278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1291_, lean_object* v_acc_1292_){
_start:
{
lean_object* v_res_1293_; 
v_res_1293_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1291_, v_acc_1292_);
lean_dec_ref(v_e_1291_);
return v_res_1293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1296_){
_start:
{
lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1297_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1298_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1296_, v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l_Lean_Meta_mkGenDiseqMask(v_e_1299_);
lean_dec_ref(v_e_1299_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_){
_start:
{
lean_object* v___f_1308_; lean_object* v___x_4344__overap_1309_; lean_object* v___x_1310_; 
v___f_1308_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_4344__overap_1309_ = lean_panic_fn_borrowed(v___f_1308_, v_msg_1302_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
v___x_1310_ = lean_apply_5(v___x_4344__overap_1309_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, lean_box(0));
return v___x_1310_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_){
_start:
{
lean_object* v_res_1317_; 
v_res_1317_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1311_, v___y_1312_, v___y_1313_, v___y_1314_, v___y_1315_);
lean_dec(v___y_1315_);
lean_dec_ref(v___y_1314_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
return v_res_1317_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1318_, lean_object* v___y_1319_){
_start:
{
uint8_t v___x_1321_; 
v___x_1321_ = l_Lean_Expr_hasMVar(v_e_1318_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; 
v___x_1322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1322_, 0, v_e_1318_);
return v___x_1322_;
}
else
{
lean_object* v___x_1323_; lean_object* v_mctx_1324_; lean_object* v___x_1325_; lean_object* v_fst_1326_; lean_object* v_snd_1327_; lean_object* v___x_1328_; lean_object* v_cache_1329_; lean_object* v_zetaDeltaFVarIds_1330_; lean_object* v_postponed_1331_; lean_object* v_diag_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1341_; 
v___x_1323_ = lean_st_ref_get(v___y_1319_);
v_mctx_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc_ref(v_mctx_1324_);
lean_dec(v___x_1323_);
v___x_1325_ = l_Lean_instantiateMVarsCore(v_mctx_1324_, v_e_1318_);
v_fst_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc(v_fst_1326_);
v_snd_1327_ = lean_ctor_get(v___x_1325_, 1);
lean_inc(v_snd_1327_);
lean_dec_ref(v___x_1325_);
v___x_1328_ = lean_st_ref_take(v___y_1319_);
v_cache_1329_ = lean_ctor_get(v___x_1328_, 1);
v_zetaDeltaFVarIds_1330_ = lean_ctor_get(v___x_1328_, 2);
v_postponed_1331_ = lean_ctor_get(v___x_1328_, 3);
v_diag_1332_ = lean_ctor_get(v___x_1328_, 4);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1328_);
if (v_isSharedCheck_1341_ == 0)
{
lean_object* v_unused_1342_; 
v_unused_1342_ = lean_ctor_get(v___x_1328_, 0);
lean_dec(v_unused_1342_);
v___x_1334_ = v___x_1328_;
v_isShared_1335_ = v_isSharedCheck_1341_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_diag_1332_);
lean_inc(v_postponed_1331_);
lean_inc(v_zetaDeltaFVarIds_1330_);
lean_inc(v_cache_1329_);
lean_dec(v___x_1328_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1341_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
lean_ctor_set(v___x_1334_, 0, v_snd_1327_);
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_snd_1327_);
lean_ctor_set(v_reuseFailAlloc_1340_, 1, v_cache_1329_);
lean_ctor_set(v_reuseFailAlloc_1340_, 2, v_zetaDeltaFVarIds_1330_);
lean_ctor_set(v_reuseFailAlloc_1340_, 3, v_postponed_1331_);
lean_ctor_set(v_reuseFailAlloc_1340_, 4, v_diag_1332_);
v___x_1337_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
lean_object* v___x_1338_; lean_object* v___x_1339_; 
v___x_1338_ = lean_st_ref_put(v___y_1319_, v___x_1337_);
v___x_1339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1339_, 0, v_fst_1326_);
return v___x_1339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1343_, v___y_1344_);
lean_dec(v___y_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v___x_1353_; 
v___x_1353_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1347_, v___y_1349_);
return v___x_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
lean_object* v_res_1360_; 
v_res_1360_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1354_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1361_, uint8_t v_allowLevelAssignments_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1362_, v_k_1361_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
if (lean_obj_tag(v___x_1368_) == 0)
{
lean_object* v_a_1369_; lean_object* v___x_1371_; uint8_t v_isShared_1372_; uint8_t v_isSharedCheck_1376_; 
v_a_1369_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1376_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1376_ == 0)
{
v___x_1371_ = v___x_1368_;
v_isShared_1372_ = v_isSharedCheck_1376_;
goto v_resetjp_1370_;
}
else
{
lean_inc(v_a_1369_);
lean_dec(v___x_1368_);
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
v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1377_; lean_object* v___x_1379_; uint8_t v_isShared_1380_; uint8_t v_isSharedCheck_1384_; 
v_a_1377_ = lean_ctor_get(v___x_1368_, 0);
v_isSharedCheck_1384_ = !lean_is_exclusive(v___x_1368_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1379_ = v___x_1368_;
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
else
{
lean_inc(v_a_1377_);
lean_dec(v___x_1368_);
v___x_1379_ = lean_box(0);
v_isShared_1380_ = v_isSharedCheck_1384_;
goto v_resetjp_1378_;
}
v_resetjp_1378_:
{
lean_object* v___x_1382_; 
if (v_isShared_1380_ == 0)
{
v___x_1382_ = v___x_1379_;
goto v_reusejp_1381_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_a_1377_);
v___x_1382_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1381_;
}
v_reusejp_1381_:
{
return v___x_1382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1385_, lean_object* v_allowLevelAssignments_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1392_; lean_object* v_res_1393_; 
v_allowLevelAssignments_boxed_1392_ = lean_unbox(v_allowLevelAssignments_1386_);
v_res_1393_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1385_, v_allowLevelAssignments_boxed_1392_, v___y_1387_, v___y_1388_, v___y_1389_, v___y_1390_);
lean_dec(v___y_1390_);
lean_dec_ref(v___y_1389_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
return v_res_1393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1394_, lean_object* v_k_1395_, uint8_t v_allowLevelAssignments_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_, lean_object* v___y_1399_, lean_object* v___y_1400_){
_start:
{
lean_object* v___x_1402_; 
v___x_1402_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1395_, v_allowLevelAssignments_1396_, v___y_1397_, v___y_1398_, v___y_1399_, v___y_1400_);
return v___x_1402_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1403_, lean_object* v_k_1404_, lean_object* v_allowLevelAssignments_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_, lean_object* v___y_1409_, lean_object* v___y_1410_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1411_; lean_object* v_res_1412_; 
v_allowLevelAssignments_boxed_1411_ = lean_unbox(v_allowLevelAssignments_1405_);
v_res_1412_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1403_, v_k_1404_, v_allowLevelAssignments_boxed_1411_, v___y_1406_, v___y_1407_, v___y_1408_, v___y_1409_);
lean_dec(v___y_1409_);
lean_dec_ref(v___y_1408_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
return v_res_1412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1415_, size_t v_sz_1416_, size_t v_i_1417_, lean_object* v_b_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_, lean_object* v___y_1421_, lean_object* v___y_1422_){
_start:
{
lean_object* v_a_1425_; uint8_t v___x_1429_; 
v___x_1429_ = lean_usize_dec_lt(v_i_1417_, v_sz_1416_);
if (v___x_1429_ == 0)
{
lean_object* v___x_1430_; 
v___x_1430_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1430_, 0, v_b_1418_);
return v___x_1430_;
}
else
{
lean_object* v_snd_1431_; lean_object* v___x_1433_; uint8_t v_isShared_1434_; uint8_t v_isSharedCheck_1593_; 
v_snd_1431_ = lean_ctor_get(v_b_1418_, 1);
v_isSharedCheck_1593_ = !lean_is_exclusive(v_b_1418_);
if (v_isSharedCheck_1593_ == 0)
{
lean_object* v_unused_1594_; 
v_unused_1594_ = lean_ctor_get(v_b_1418_, 0);
lean_dec(v_unused_1594_);
v___x_1433_ = v_b_1418_;
v_isShared_1434_ = v_isSharedCheck_1593_;
goto v_resetjp_1432_;
}
else
{
lean_inc(v_snd_1431_);
lean_dec(v_b_1418_);
v___x_1433_ = lean_box(0);
v_isShared_1434_ = v_isSharedCheck_1593_;
goto v_resetjp_1432_;
}
v_resetjp_1432_:
{
lean_object* v_array_1435_; lean_object* v_start_1436_; lean_object* v_stop_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; 
v_array_1435_ = lean_ctor_get(v_snd_1431_, 0);
v_start_1436_ = lean_ctor_get(v_snd_1431_, 1);
v_stop_1437_ = lean_ctor_get(v_snd_1431_, 2);
v___x_1438_ = lean_box(0);
v___x_1439_ = lean_nat_dec_lt(v_start_1436_, v_stop_1437_);
if (v___x_1439_ == 0)
{
lean_object* v___x_1441_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 0, v___x_1438_);
v___x_1441_ = v___x_1433_;
goto v_reusejp_1440_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1443_, 1, v_snd_1431_);
v___x_1441_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1440_;
}
v_reusejp_1440_:
{
lean_object* v___x_1442_; 
v___x_1442_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1442_, 0, v___x_1441_);
return v___x_1442_;
}
}
else
{
lean_object* v___x_1445_; uint8_t v_isShared_1446_; uint8_t v_isSharedCheck_1589_; 
lean_inc(v_stop_1437_);
lean_inc(v_start_1436_);
lean_inc_ref(v_array_1435_);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_snd_1431_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; 
v_unused_1590_ = lean_ctor_get(v_snd_1431_, 2);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_snd_1431_, 1);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_snd_1431_, 0);
lean_dec(v_unused_1592_);
v___x_1445_ = v_snd_1431_;
v_isShared_1446_ = v_isSharedCheck_1589_;
goto v_resetjp_1444_;
}
else
{
lean_dec(v_snd_1431_);
v___x_1445_ = lean_box(0);
v_isShared_1446_ = v_isSharedCheck_1589_;
goto v_resetjp_1444_;
}
v_resetjp_1444_:
{
lean_object* v___x_1447_; lean_object* v___x_1448_; lean_object* v___x_1449_; lean_object* v___x_1451_; 
v___x_1447_ = lean_array_fget(v_array_1435_, v_start_1436_);
v___x_1448_ = lean_unsigned_to_nat(1u);
v___x_1449_ = lean_nat_add(v_start_1436_, v___x_1448_);
lean_dec(v_start_1436_);
if (v_isShared_1446_ == 0)
{
lean_ctor_set(v___x_1445_, 1, v___x_1449_);
v___x_1451_ = v___x_1445_;
goto v_reusejp_1450_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_array_1435_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1449_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_stop_1437_);
v___x_1451_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1450_;
}
v_reusejp_1450_:
{
uint8_t v___x_1452_; 
v___x_1452_ = lean_unbox(v___x_1447_);
lean_dec(v___x_1447_);
if (v___x_1452_ == 0)
{
lean_object* v___x_1454_; 
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 1, v___x_1451_);
lean_ctor_set(v___x_1433_, 0, v___x_1438_);
v___x_1454_ = v___x_1433_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1455_, 1, v___x_1451_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
v_a_1425_ = v___x_1454_;
goto v___jp_1424_;
}
}
else
{
lean_object* v_a_1456_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___y_1460_; lean_object* v___y_1461_; lean_object* v___x_1528_; 
v_a_1456_ = lean_array_uget_borrowed(v_as_1415_, v_i_1417_);
lean_inc(v___y_1422_);
lean_inc_ref(v___y_1421_);
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
lean_inc(v_a_1456_);
v___x_1528_ = lean_infer_type(v_a_1456_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; lean_object* v___x_1530_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
v___x_1530_ = l_Lean_Meta_matchEq_x3f(v_a_1529_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1530_) == 0)
{
lean_object* v_a_1531_; 
v_a_1531_ = lean_ctor_get(v___x_1530_, 0);
lean_inc(v_a_1531_);
lean_dec_ref_known(v___x_1530_, 1);
if (lean_obj_tag(v_a_1531_) == 1)
{
lean_object* v_val_1532_; lean_object* v_snd_1533_; lean_object* v_fst_1534_; lean_object* v___x_1536_; uint8_t v_isShared_1537_; uint8_t v_isSharedCheck_1570_; 
v_val_1532_ = lean_ctor_get(v_a_1531_, 0);
lean_inc(v_val_1532_);
lean_dec_ref_known(v_a_1531_, 1);
v_snd_1533_ = lean_ctor_get(v_val_1532_, 1);
lean_inc(v_snd_1533_);
lean_dec(v_val_1532_);
v_fst_1534_ = lean_ctor_get(v_snd_1533_, 0);
v_isSharedCheck_1570_ = !lean_is_exclusive(v_snd_1533_);
if (v_isSharedCheck_1570_ == 0)
{
lean_object* v_unused_1571_; 
v_unused_1571_ = lean_ctor_get(v_snd_1533_, 1);
lean_dec(v_unused_1571_);
v___x_1536_ = v_snd_1533_;
v_isShared_1537_ = v_isSharedCheck_1570_;
goto v_resetjp_1535_;
}
else
{
lean_inc(v_fst_1534_);
lean_dec(v_snd_1533_);
v___x_1536_ = lean_box(0);
v_isShared_1537_ = v_isSharedCheck_1570_;
goto v_resetjp_1535_;
}
v_resetjp_1535_:
{
lean_object* v___x_1538_; 
v___x_1538_ = l_Lean_Meta_mkEqRefl(v_fst_1534_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1540_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
lean_inc(v_a_1539_);
lean_dec_ref_known(v___x_1538_, 1);
lean_inc(v_a_1456_);
v___x_1540_ = l_Lean_Meta_isExprDefEq(v_a_1456_, v_a_1539_, v___y_1419_, v___y_1420_, v___y_1421_, v___y_1422_);
if (lean_obj_tag(v___x_1540_) == 0)
{
lean_object* v_a_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1553_; 
v_a_1541_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1543_ = v___x_1540_;
v_isShared_1544_ = v_isSharedCheck_1553_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_a_1541_);
lean_dec(v___x_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1553_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
uint8_t v___x_1545_; 
v___x_1545_ = lean_unbox(v_a_1541_);
lean_dec(v_a_1541_);
if (v___x_1545_ == 0)
{
lean_object* v___x_1546_; lean_object* v___x_1548_; 
lean_del_object(v___x_1433_);
v___x_1546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1537_ == 0)
{
lean_ctor_set(v___x_1536_, 1, v___x_1451_);
lean_ctor_set(v___x_1536_, 0, v___x_1546_);
v___x_1548_ = v___x_1536_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v___x_1546_);
lean_ctor_set(v_reuseFailAlloc_1552_, 1, v___x_1451_);
v___x_1548_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
lean_object* v___x_1550_; 
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 0, v___x_1548_);
v___x_1550_ = v___x_1543_;
goto v_reusejp_1549_;
}
else
{
lean_object* v_reuseFailAlloc_1551_; 
v_reuseFailAlloc_1551_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1551_, 0, v___x_1548_);
v___x_1550_ = v_reuseFailAlloc_1551_;
goto v_reusejp_1549_;
}
v_reusejp_1549_:
{
return v___x_1550_;
}
}
}
else
{
lean_del_object(v___x_1543_);
lean_del_object(v___x_1536_);
v___y_1458_ = v___y_1419_;
v___y_1459_ = v___y_1420_;
v___y_1460_ = v___y_1421_;
v___y_1461_ = v___y_1422_;
goto v___jp_1457_;
}
}
}
else
{
lean_object* v_a_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1561_; 
lean_del_object(v___x_1536_);
lean_dec_ref(v___x_1451_);
lean_del_object(v___x_1433_);
v_a_1554_ = lean_ctor_get(v___x_1540_, 0);
v_isSharedCheck_1561_ = !lean_is_exclusive(v___x_1540_);
if (v_isSharedCheck_1561_ == 0)
{
v___x_1556_ = v___x_1540_;
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
else
{
lean_inc(v_a_1554_);
lean_dec(v___x_1540_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1561_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1559_; 
if (v_isShared_1557_ == 0)
{
v___x_1559_ = v___x_1556_;
goto v_reusejp_1558_;
}
else
{
lean_object* v_reuseFailAlloc_1560_; 
v_reuseFailAlloc_1560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1560_, 0, v_a_1554_);
v___x_1559_ = v_reuseFailAlloc_1560_;
goto v_reusejp_1558_;
}
v_reusejp_1558_:
{
return v___x_1559_;
}
}
}
}
else
{
lean_object* v_a_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1569_; 
lean_del_object(v___x_1536_);
lean_dec_ref(v___x_1451_);
lean_del_object(v___x_1433_);
v_a_1562_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1569_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1569_ == 0)
{
v___x_1564_ = v___x_1538_;
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_a_1562_);
lean_dec(v___x_1538_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1569_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1567_; 
if (v_isShared_1565_ == 0)
{
v___x_1567_ = v___x_1564_;
goto v_reusejp_1566_;
}
else
{
lean_object* v_reuseFailAlloc_1568_; 
v_reuseFailAlloc_1568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1568_, 0, v_a_1562_);
v___x_1567_ = v_reuseFailAlloc_1568_;
goto v_reusejp_1566_;
}
v_reusejp_1566_:
{
return v___x_1567_;
}
}
}
}
}
else
{
lean_dec(v_a_1531_);
v___y_1458_ = v___y_1419_;
v___y_1459_ = v___y_1420_;
v___y_1460_ = v___y_1421_;
v___y_1461_ = v___y_1422_;
goto v___jp_1457_;
}
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
lean_dec_ref(v___x_1451_);
lean_del_object(v___x_1433_);
v_a_1572_ = lean_ctor_get(v___x_1530_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1530_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1530_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1530_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
else
{
lean_object* v_a_1580_; lean_object* v___x_1582_; uint8_t v_isShared_1583_; uint8_t v_isSharedCheck_1587_; 
lean_dec_ref(v___x_1451_);
lean_del_object(v___x_1433_);
v_a_1580_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1587_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1587_ == 0)
{
v___x_1582_ = v___x_1528_;
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
else
{
lean_inc(v_a_1580_);
lean_dec(v___x_1528_);
v___x_1582_ = lean_box(0);
v_isShared_1583_ = v_isSharedCheck_1587_;
goto v_resetjp_1581_;
}
v_resetjp_1581_:
{
lean_object* v___x_1585_; 
if (v_isShared_1583_ == 0)
{
v___x_1585_ = v___x_1582_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_a_1580_);
v___x_1585_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
return v___x_1585_;
}
}
}
v___jp_1457_:
{
lean_object* v___x_1462_; 
lean_inc(v___y_1461_);
lean_inc_ref(v___y_1460_);
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v_a_1456_);
v___x_1462_ = lean_infer_type(v_a_1456_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; lean_object* v___x_1464_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
v___x_1464_ = l_Lean_Meta_matchHEq_x3f(v_a_1463_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1464_) == 0)
{
lean_object* v_a_1465_; 
v_a_1465_ = lean_ctor_get(v___x_1464_, 0);
lean_inc(v_a_1465_);
lean_dec_ref_known(v___x_1464_, 1);
if (lean_obj_tag(v_a_1465_) == 1)
{
lean_object* v_val_1466_; lean_object* v_snd_1467_; lean_object* v_fst_1468_; lean_object* v___x_1470_; uint8_t v_isShared_1471_; uint8_t v_isSharedCheck_1507_; 
lean_del_object(v___x_1433_);
v_val_1466_ = lean_ctor_get(v_a_1465_, 0);
lean_inc(v_val_1466_);
lean_dec_ref_known(v_a_1465_, 1);
v_snd_1467_ = lean_ctor_get(v_val_1466_, 1);
lean_inc(v_snd_1467_);
lean_dec(v_val_1466_);
v_fst_1468_ = lean_ctor_get(v_snd_1467_, 0);
v_isSharedCheck_1507_ = !lean_is_exclusive(v_snd_1467_);
if (v_isSharedCheck_1507_ == 0)
{
lean_object* v_unused_1508_; 
v_unused_1508_ = lean_ctor_get(v_snd_1467_, 1);
lean_dec(v_unused_1508_);
v___x_1470_ = v_snd_1467_;
v_isShared_1471_ = v_isSharedCheck_1507_;
goto v_resetjp_1469_;
}
else
{
lean_inc(v_fst_1468_);
lean_dec(v_snd_1467_);
v___x_1470_ = lean_box(0);
v_isShared_1471_ = v_isSharedCheck_1507_;
goto v_resetjp_1469_;
}
v_resetjp_1469_:
{
lean_object* v___x_1472_; 
v___x_1472_ = l_Lean_Meta_mkHEqRefl(v_fst_1468_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1474_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
lean_inc(v_a_1473_);
lean_dec_ref_known(v___x_1472_, 1);
lean_inc(v_a_1456_);
v___x_1474_ = l_Lean_Meta_isExprDefEq(v_a_1456_, v_a_1473_, v___y_1458_, v___y_1459_, v___y_1460_, v___y_1461_);
if (lean_obj_tag(v___x_1474_) == 0)
{
lean_object* v_a_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1490_; 
v_a_1475_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1490_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1490_ == 0)
{
v___x_1477_ = v___x_1474_;
v_isShared_1478_ = v_isSharedCheck_1490_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_a_1475_);
lean_dec(v___x_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1490_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
uint8_t v___x_1479_; 
v___x_1479_ = lean_unbox(v_a_1475_);
lean_dec(v_a_1475_);
if (v___x_1479_ == 0)
{
lean_object* v___x_1480_; lean_object* v___x_1482_; 
v___x_1480_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 1, v___x_1451_);
lean_ctor_set(v___x_1470_, 0, v___x_1480_);
v___x_1482_ = v___x_1470_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1486_; 
v_reuseFailAlloc_1486_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1486_, 0, v___x_1480_);
lean_ctor_set(v_reuseFailAlloc_1486_, 1, v___x_1451_);
v___x_1482_ = v_reuseFailAlloc_1486_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
lean_object* v___x_1484_; 
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 0, v___x_1482_);
v___x_1484_ = v___x_1477_;
goto v_reusejp_1483_;
}
else
{
lean_object* v_reuseFailAlloc_1485_; 
v_reuseFailAlloc_1485_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1485_, 0, v___x_1482_);
v___x_1484_ = v_reuseFailAlloc_1485_;
goto v_reusejp_1483_;
}
v_reusejp_1483_:
{
return v___x_1484_;
}
}
}
else
{
lean_object* v___x_1488_; 
lean_del_object(v___x_1477_);
if (v_isShared_1471_ == 0)
{
lean_ctor_set(v___x_1470_, 1, v___x_1451_);
lean_ctor_set(v___x_1470_, 0, v___x_1438_);
v___x_1488_ = v___x_1470_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1489_; 
v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1489_, 1, v___x_1451_);
v___x_1488_ = v_reuseFailAlloc_1489_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
v_a_1425_ = v___x_1488_;
goto v___jp_1424_;
}
}
}
}
else
{
lean_object* v_a_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1498_; 
lean_del_object(v___x_1470_);
lean_dec_ref(v___x_1451_);
v_a_1491_ = lean_ctor_get(v___x_1474_, 0);
v_isSharedCheck_1498_ = !lean_is_exclusive(v___x_1474_);
if (v_isSharedCheck_1498_ == 0)
{
v___x_1493_ = v___x_1474_;
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
else
{
lean_inc(v_a_1491_);
lean_dec(v___x_1474_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1498_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1496_; 
if (v_isShared_1494_ == 0)
{
v___x_1496_ = v___x_1493_;
goto v_reusejp_1495_;
}
else
{
lean_object* v_reuseFailAlloc_1497_; 
v_reuseFailAlloc_1497_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1497_, 0, v_a_1491_);
v___x_1496_ = v_reuseFailAlloc_1497_;
goto v_reusejp_1495_;
}
v_reusejp_1495_:
{
return v___x_1496_;
}
}
}
}
else
{
lean_object* v_a_1499_; lean_object* v___x_1501_; uint8_t v_isShared_1502_; uint8_t v_isSharedCheck_1506_; 
lean_del_object(v___x_1470_);
lean_dec_ref(v___x_1451_);
v_a_1499_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1506_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1506_ == 0)
{
v___x_1501_ = v___x_1472_;
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
else
{
lean_inc(v_a_1499_);
lean_dec(v___x_1472_);
v___x_1501_ = lean_box(0);
v_isShared_1502_ = v_isSharedCheck_1506_;
goto v_resetjp_1500_;
}
v_resetjp_1500_:
{
lean_object* v___x_1504_; 
if (v_isShared_1502_ == 0)
{
v___x_1504_ = v___x_1501_;
goto v_reusejp_1503_;
}
else
{
lean_object* v_reuseFailAlloc_1505_; 
v_reuseFailAlloc_1505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1505_, 0, v_a_1499_);
v___x_1504_ = v_reuseFailAlloc_1505_;
goto v_reusejp_1503_;
}
v_reusejp_1503_:
{
return v___x_1504_;
}
}
}
}
}
else
{
lean_object* v___x_1510_; 
lean_dec(v_a_1465_);
if (v_isShared_1434_ == 0)
{
lean_ctor_set(v___x_1433_, 1, v___x_1451_);
lean_ctor_set(v___x_1433_, 0, v___x_1438_);
v___x_1510_ = v___x_1433_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v___x_1438_);
lean_ctor_set(v_reuseFailAlloc_1511_, 1, v___x_1451_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
v_a_1425_ = v___x_1510_;
goto v___jp_1424_;
}
}
}
else
{
lean_object* v_a_1512_; lean_object* v___x_1514_; uint8_t v_isShared_1515_; uint8_t v_isSharedCheck_1519_; 
lean_dec_ref(v___x_1451_);
lean_del_object(v___x_1433_);
v_a_1512_ = lean_ctor_get(v___x_1464_, 0);
v_isSharedCheck_1519_ = !lean_is_exclusive(v___x_1464_);
if (v_isSharedCheck_1519_ == 0)
{
v___x_1514_ = v___x_1464_;
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
else
{
lean_inc(v_a_1512_);
lean_dec(v___x_1464_);
v___x_1514_ = lean_box(0);
v_isShared_1515_ = v_isSharedCheck_1519_;
goto v_resetjp_1513_;
}
v_resetjp_1513_:
{
lean_object* v___x_1517_; 
if (v_isShared_1515_ == 0)
{
v___x_1517_ = v___x_1514_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v_a_1512_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
return v___x_1517_;
}
}
}
}
else
{
lean_object* v_a_1520_; lean_object* v___x_1522_; uint8_t v_isShared_1523_; uint8_t v_isSharedCheck_1527_; 
lean_dec_ref(v___x_1451_);
lean_del_object(v___x_1433_);
v_a_1520_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1527_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1527_ == 0)
{
v___x_1522_ = v___x_1462_;
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
else
{
lean_inc(v_a_1520_);
lean_dec(v___x_1462_);
v___x_1522_ = lean_box(0);
v_isShared_1523_ = v_isSharedCheck_1527_;
goto v_resetjp_1521_;
}
v_resetjp_1521_:
{
lean_object* v___x_1525_; 
if (v_isShared_1523_ == 0)
{
v___x_1525_ = v___x_1522_;
goto v_reusejp_1524_;
}
else
{
lean_object* v_reuseFailAlloc_1526_; 
v_reuseFailAlloc_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1526_, 0, v_a_1520_);
v___x_1525_ = v_reuseFailAlloc_1526_;
goto v_reusejp_1524_;
}
v_reusejp_1524_:
{
return v___x_1525_;
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
v___jp_1424_:
{
size_t v___x_1426_; size_t v___x_1427_; 
v___x_1426_ = ((size_t)1ULL);
v___x_1427_ = lean_usize_add(v_i_1417_, v___x_1426_);
v_i_1417_ = v___x_1427_;
v_b_1418_ = v_a_1425_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1595_, lean_object* v_sz_1596_, lean_object* v_i_1597_, lean_object* v_b_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
size_t v_sz_boxed_1604_; size_t v_i_boxed_1605_; lean_object* v_res_1606_; 
v_sz_boxed_1604_ = lean_unbox_usize(v_sz_1596_);
lean_dec(v_sz_1596_);
v_i_boxed_1605_ = lean_unbox_usize(v_i_1597_);
lean_dec(v_i_1597_);
v_res_1606_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1595_, v_sz_boxed_1604_, v_i_boxed_1605_, v_b_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec_ref(v_as_1595_);
return v_res_1606_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1607_, uint8_t v___x_1608_, lean_object* v_localDecl_1609_, lean_object* v_mvarId_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_, lean_object* v___y_1613_, lean_object* v___y_1614_){
_start:
{
lean_object* v___x_1616_; 
lean_inc_ref(v___x_1607_);
v___x_1616_ = l_Lean_Meta_forallMetaTelescope(v___x_1607_, v___x_1608_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1616_) == 0)
{
lean_object* v_a_1617_; lean_object* v_fst_1618_; lean_object* v___x_1620_; uint8_t v_isShared_1621_; uint8_t v_isSharedCheck_1707_; 
v_a_1617_ = lean_ctor_get(v___x_1616_, 0);
lean_inc(v_a_1617_);
lean_dec_ref_known(v___x_1616_, 1);
v_fst_1618_ = lean_ctor_get(v_a_1617_, 0);
v_isSharedCheck_1707_ = !lean_is_exclusive(v_a_1617_);
if (v_isSharedCheck_1707_ == 0)
{
lean_object* v_unused_1708_; 
v_unused_1708_ = lean_ctor_get(v_a_1617_, 1);
lean_dec(v_unused_1708_);
v___x_1620_ = v_a_1617_;
v_isShared_1621_ = v_isSharedCheck_1707_;
goto v_resetjp_1619_;
}
else
{
lean_inc(v_fst_1618_);
lean_dec(v_a_1617_);
v___x_1620_ = lean_box(0);
v_isShared_1621_ = v_isSharedCheck_1707_;
goto v_resetjp_1619_;
}
v_resetjp_1619_:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; lean_object* v___x_1628_; 
v___x_1622_ = l_Lean_Meta_mkGenDiseqMask(v___x_1607_);
lean_dec_ref(v___x_1607_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = lean_array_get_size(v___x_1622_);
v___x_1625_ = l_Array_toSubarray___redArg(v___x_1622_, v___x_1623_, v___x_1624_);
v___x_1626_ = lean_box(0);
if (v_isShared_1621_ == 0)
{
lean_ctor_set(v___x_1620_, 1, v___x_1625_);
lean_ctor_set(v___x_1620_, 0, v___x_1626_);
v___x_1628_ = v___x_1620_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1706_; 
v_reuseFailAlloc_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1706_, 0, v___x_1626_);
lean_ctor_set(v_reuseFailAlloc_1706_, 1, v___x_1625_);
v___x_1628_ = v_reuseFailAlloc_1706_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
size_t v_sz_1629_; size_t v___x_1630_; lean_object* v___x_1631_; 
v_sz_1629_ = lean_array_size(v_fst_1618_);
v___x_1630_ = ((size_t)0ULL);
v___x_1631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1618_, v_sz_1629_, v___x_1630_, v___x_1628_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1631_) == 0)
{
lean_object* v_a_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1697_; 
v_a_1632_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1634_ = v___x_1631_;
v_isShared_1635_ = v_isSharedCheck_1697_;
goto v_resetjp_1633_;
}
else
{
lean_inc(v_a_1632_);
lean_dec(v___x_1631_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1697_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v_fst_1636_; 
v_fst_1636_ = lean_ctor_get(v_a_1632_, 0);
lean_inc(v_fst_1636_);
lean_dec(v_a_1632_);
if (lean_obj_tag(v_fst_1636_) == 0)
{
lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v_a_1640_; lean_object* v___x_1642_; uint8_t v_isShared_1643_; uint8_t v_isSharedCheck_1692_; 
lean_del_object(v___x_1634_);
v___x_1637_ = l_Lean_LocalDecl_toExpr(v_localDecl_1609_);
v___x_1638_ = l_Lean_mkAppN(v___x_1637_, v_fst_1618_);
lean_dec(v_fst_1618_);
v___x_1639_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1638_, v___y_1612_);
v_a_1640_ = lean_ctor_get(v___x_1639_, 0);
v_isSharedCheck_1692_ = !lean_is_exclusive(v___x_1639_);
if (v_isSharedCheck_1692_ == 0)
{
v___x_1642_ = v___x_1639_;
v_isShared_1643_ = v_isSharedCheck_1692_;
goto v_resetjp_1641_;
}
else
{
lean_inc(v_a_1640_);
lean_dec(v___x_1639_);
v___x_1642_ = lean_box(0);
v_isShared_1643_ = v_isSharedCheck_1692_;
goto v_resetjp_1641_;
}
v_resetjp_1641_:
{
lean_object* v___x_1644_; 
lean_inc(v_a_1640_);
v___x_1644_ = l_Lean_Meta_hasAssignableMVar(v_a_1640_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1644_) == 0)
{
lean_object* v_a_1645_; lean_object* v___x_1647_; uint8_t v_isShared_1648_; uint8_t v_isSharedCheck_1683_; 
v_a_1645_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1683_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1683_ == 0)
{
v___x_1647_ = v___x_1644_;
v_isShared_1648_ = v_isSharedCheck_1683_;
goto v_resetjp_1646_;
}
else
{
lean_inc(v_a_1645_);
lean_dec(v___x_1644_);
v___x_1647_ = lean_box(0);
v_isShared_1648_ = v_isSharedCheck_1683_;
goto v_resetjp_1646_;
}
v_resetjp_1646_:
{
uint8_t v___x_1649_; 
v___x_1649_ = lean_unbox(v_a_1645_);
lean_dec(v_a_1645_);
if (v___x_1649_ == 0)
{
lean_object* v___x_1650_; 
lean_del_object(v___x_1647_);
v___x_1650_ = l_Lean_MVarId_getType(v_mvarId_1610_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1652_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_a_1651_);
lean_dec_ref_known(v___x_1650_, 1);
v___x_1652_ = l_Lean_Meta_mkFalseElim(v_a_1651_, v_a_1640_, v___y_1611_, v___y_1612_, v___y_1613_, v___y_1614_);
if (lean_obj_tag(v___x_1652_) == 0)
{
lean_object* v_a_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1663_; 
v_a_1653_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1655_ = v___x_1652_;
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_a_1653_);
lean_dec(v___x_1652_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1663_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1643_ == 0)
{
lean_ctor_set_tag(v___x_1642_, 1);
lean_ctor_set(v___x_1642_, 0, v_a_1653_);
v___x_1658_ = v___x_1642_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v_a_1653_);
v___x_1658_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v___x_1660_; 
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 0, v___x_1658_);
v___x_1660_ = v___x_1655_;
goto v_reusejp_1659_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v___x_1658_);
v___x_1660_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1659_;
}
v_reusejp_1659_:
{
return v___x_1660_;
}
}
}
}
else
{
lean_object* v_a_1664_; lean_object* v___x_1666_; uint8_t v_isShared_1667_; uint8_t v_isSharedCheck_1671_; 
lean_del_object(v___x_1642_);
v_a_1664_ = lean_ctor_get(v___x_1652_, 0);
v_isSharedCheck_1671_ = !lean_is_exclusive(v___x_1652_);
if (v_isSharedCheck_1671_ == 0)
{
v___x_1666_ = v___x_1652_;
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
else
{
lean_inc(v_a_1664_);
lean_dec(v___x_1652_);
v___x_1666_ = lean_box(0);
v_isShared_1667_ = v_isSharedCheck_1671_;
goto v_resetjp_1665_;
}
v_resetjp_1665_:
{
lean_object* v___x_1669_; 
if (v_isShared_1667_ == 0)
{
v___x_1669_ = v___x_1666_;
goto v_reusejp_1668_;
}
else
{
lean_object* v_reuseFailAlloc_1670_; 
v_reuseFailAlloc_1670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1670_, 0, v_a_1664_);
v___x_1669_ = v_reuseFailAlloc_1670_;
goto v_reusejp_1668_;
}
v_reusejp_1668_:
{
return v___x_1669_;
}
}
}
}
else
{
lean_object* v_a_1672_; lean_object* v___x_1674_; uint8_t v_isShared_1675_; uint8_t v_isSharedCheck_1679_; 
lean_del_object(v___x_1642_);
lean_dec(v_a_1640_);
v_a_1672_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1679_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1679_ == 0)
{
v___x_1674_ = v___x_1650_;
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
else
{
lean_inc(v_a_1672_);
lean_dec(v___x_1650_);
v___x_1674_ = lean_box(0);
v_isShared_1675_ = v_isSharedCheck_1679_;
goto v_resetjp_1673_;
}
v_resetjp_1673_:
{
lean_object* v___x_1677_; 
if (v_isShared_1675_ == 0)
{
v___x_1677_ = v___x_1674_;
goto v_reusejp_1676_;
}
else
{
lean_object* v_reuseFailAlloc_1678_; 
v_reuseFailAlloc_1678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1678_, 0, v_a_1672_);
v___x_1677_ = v_reuseFailAlloc_1678_;
goto v_reusejp_1676_;
}
v_reusejp_1676_:
{
return v___x_1677_;
}
}
}
}
else
{
lean_object* v___x_1681_; 
lean_del_object(v___x_1642_);
lean_dec(v_a_1640_);
lean_dec(v_mvarId_1610_);
if (v_isShared_1648_ == 0)
{
lean_ctor_set(v___x_1647_, 0, v___x_1626_);
v___x_1681_ = v___x_1647_;
goto v_reusejp_1680_;
}
else
{
lean_object* v_reuseFailAlloc_1682_; 
v_reuseFailAlloc_1682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1682_, 0, v___x_1626_);
v___x_1681_ = v_reuseFailAlloc_1682_;
goto v_reusejp_1680_;
}
v_reusejp_1680_:
{
return v___x_1681_;
}
}
}
}
else
{
lean_object* v_a_1684_; lean_object* v___x_1686_; uint8_t v_isShared_1687_; uint8_t v_isSharedCheck_1691_; 
lean_del_object(v___x_1642_);
lean_dec(v_a_1640_);
lean_dec(v_mvarId_1610_);
v_a_1684_ = lean_ctor_get(v___x_1644_, 0);
v_isSharedCheck_1691_ = !lean_is_exclusive(v___x_1644_);
if (v_isSharedCheck_1691_ == 0)
{
v___x_1686_ = v___x_1644_;
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
else
{
lean_inc(v_a_1684_);
lean_dec(v___x_1644_);
v___x_1686_ = lean_box(0);
v_isShared_1687_ = v_isSharedCheck_1691_;
goto v_resetjp_1685_;
}
v_resetjp_1685_:
{
lean_object* v___x_1689_; 
if (v_isShared_1687_ == 0)
{
v___x_1689_ = v___x_1686_;
goto v_reusejp_1688_;
}
else
{
lean_object* v_reuseFailAlloc_1690_; 
v_reuseFailAlloc_1690_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1690_, 0, v_a_1684_);
v___x_1689_ = v_reuseFailAlloc_1690_;
goto v_reusejp_1688_;
}
v_reusejp_1688_:
{
return v___x_1689_;
}
}
}
}
}
else
{
lean_object* v_val_1693_; lean_object* v___x_1695_; 
lean_dec(v_fst_1618_);
lean_dec(v_mvarId_1610_);
lean_dec_ref(v_localDecl_1609_);
v_val_1693_ = lean_ctor_get(v_fst_1636_, 0);
lean_inc(v_val_1693_);
lean_dec_ref_known(v_fst_1636_, 1);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 0, v_val_1693_);
v___x_1695_ = v___x_1634_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_val_1693_);
v___x_1695_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1694_;
}
v_reusejp_1694_:
{
return v___x_1695_;
}
}
}
}
else
{
lean_object* v_a_1698_; lean_object* v___x_1700_; uint8_t v_isShared_1701_; uint8_t v_isSharedCheck_1705_; 
lean_dec(v_fst_1618_);
lean_dec(v_mvarId_1610_);
lean_dec_ref(v_localDecl_1609_);
v_a_1698_ = lean_ctor_get(v___x_1631_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v___x_1631_);
if (v_isSharedCheck_1705_ == 0)
{
v___x_1700_ = v___x_1631_;
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
else
{
lean_inc(v_a_1698_);
lean_dec(v___x_1631_);
v___x_1700_ = lean_box(0);
v_isShared_1701_ = v_isSharedCheck_1705_;
goto v_resetjp_1699_;
}
v_resetjp_1699_:
{
lean_object* v___x_1703_; 
if (v_isShared_1701_ == 0)
{
v___x_1703_ = v___x_1700_;
goto v_reusejp_1702_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v_a_1698_);
v___x_1703_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1702_;
}
v_reusejp_1702_:
{
return v___x_1703_;
}
}
}
}
}
}
else
{
lean_object* v_a_1709_; lean_object* v___x_1711_; uint8_t v_isShared_1712_; uint8_t v_isSharedCheck_1716_; 
lean_dec(v_mvarId_1610_);
lean_dec_ref(v_localDecl_1609_);
lean_dec_ref(v___x_1607_);
v_a_1709_ = lean_ctor_get(v___x_1616_, 0);
v_isSharedCheck_1716_ = !lean_is_exclusive(v___x_1616_);
if (v_isSharedCheck_1716_ == 0)
{
v___x_1711_ = v___x_1616_;
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
else
{
lean_inc(v_a_1709_);
lean_dec(v___x_1616_);
v___x_1711_ = lean_box(0);
v_isShared_1712_ = v_isSharedCheck_1716_;
goto v_resetjp_1710_;
}
v_resetjp_1710_:
{
lean_object* v___x_1714_; 
if (v_isShared_1712_ == 0)
{
v___x_1714_ = v___x_1711_;
goto v_reusejp_1713_;
}
else
{
lean_object* v_reuseFailAlloc_1715_; 
v_reuseFailAlloc_1715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1715_, 0, v_a_1709_);
v___x_1714_ = v_reuseFailAlloc_1715_;
goto v_reusejp_1713_;
}
v_reusejp_1713_:
{
return v___x_1714_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1717_, lean_object* v___x_1718_, lean_object* v_localDecl_1719_, lean_object* v_mvarId_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_, lean_object* v___y_1724_, lean_object* v___y_1725_){
_start:
{
uint8_t v___x_6078__boxed_1726_; lean_object* v_res_1727_; 
v___x_6078__boxed_1726_ = lean_unbox(v___x_1718_);
v_res_1727_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1717_, v___x_6078__boxed_1726_, v_localDecl_1719_, v_mvarId_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
lean_dec(v___y_1724_);
lean_dec_ref(v___y_1723_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
return v_res_1727_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1731_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1732_ = lean_unsigned_to_nat(2u);
v___x_1733_ = lean_unsigned_to_nat(120u);
v___x_1734_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1735_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1736_ = l_mkPanicMessageWithDecl(v___x_1735_, v___x_1734_, v___x_1733_, v___x_1732_, v___x_1731_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1737_, lean_object* v_localDecl_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_, lean_object* v_a_1741_, lean_object* v_a_1742_){
_start:
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = l_Lean_LocalDecl_type(v_localDecl_1738_);
lean_inc_ref(v___x_1744_);
v___x_1745_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1744_);
if (v___x_1745_ == 0)
{
lean_object* v___x_1746_; lean_object* v___x_1747_; 
lean_dec_ref(v___x_1744_);
lean_dec_ref(v_localDecl_1738_);
lean_dec(v_mvarId_1737_);
v___x_1746_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1747_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1746_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
return v___x_1747_;
}
else
{
uint8_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___f_1750_; uint8_t v___x_1751_; lean_object* v___x_1752_; 
v___x_1748_ = 0;
v___x_1749_ = lean_box(v___x_1748_);
lean_inc(v_mvarId_1737_);
v___f_1750_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1750_, 0, v___x_1744_);
lean_closure_set(v___f_1750_, 1, v___x_1749_);
lean_closure_set(v___f_1750_, 2, v_localDecl_1738_);
lean_closure_set(v___f_1750_, 3, v_mvarId_1737_);
v___x_1751_ = 0;
v___x_1752_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1750_, v___x_1751_, v_a_1739_, v_a_1740_, v_a_1741_, v_a_1742_);
if (lean_obj_tag(v___x_1752_) == 0)
{
lean_object* v_a_1753_; lean_object* v___x_1755_; uint8_t v_isShared_1756_; uint8_t v_isSharedCheck_1772_; 
v_a_1753_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1772_ == 0)
{
v___x_1755_ = v___x_1752_;
v_isShared_1756_ = v_isSharedCheck_1772_;
goto v_resetjp_1754_;
}
else
{
lean_inc(v_a_1753_);
lean_dec(v___x_1752_);
v___x_1755_ = lean_box(0);
v_isShared_1756_ = v_isSharedCheck_1772_;
goto v_resetjp_1754_;
}
v_resetjp_1754_:
{
if (lean_obj_tag(v_a_1753_) == 1)
{
lean_object* v_val_1757_; lean_object* v___x_1758_; lean_object* v___x_1760_; uint8_t v_isShared_1761_; uint8_t v_isSharedCheck_1766_; 
lean_del_object(v___x_1755_);
v_val_1757_ = lean_ctor_get(v_a_1753_, 0);
lean_inc(v_val_1757_);
lean_dec_ref_known(v_a_1753_, 1);
v___x_1758_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1737_, v_val_1757_, v_a_1740_);
v_isSharedCheck_1766_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1766_ == 0)
{
lean_object* v_unused_1767_; 
v_unused_1767_ = lean_ctor_get(v___x_1758_, 0);
lean_dec(v_unused_1767_);
v___x_1760_ = v___x_1758_;
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
else
{
lean_dec(v___x_1758_);
v___x_1760_ = lean_box(0);
v_isShared_1761_ = v_isSharedCheck_1766_;
goto v_resetjp_1759_;
}
v_resetjp_1759_:
{
lean_object* v___x_1762_; lean_object* v___x_1764_; 
v___x_1762_ = lean_box(v___x_1745_);
if (v_isShared_1761_ == 0)
{
lean_ctor_set(v___x_1760_, 0, v___x_1762_);
v___x_1764_ = v___x_1760_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1765_; 
v_reuseFailAlloc_1765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1765_, 0, v___x_1762_);
v___x_1764_ = v_reuseFailAlloc_1765_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
return v___x_1764_;
}
}
}
else
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
lean_dec(v_a_1753_);
lean_dec(v_mvarId_1737_);
v___x_1768_ = lean_box(v___x_1751_);
if (v_isShared_1756_ == 0)
{
lean_ctor_set(v___x_1755_, 0, v___x_1768_);
v___x_1770_ = v___x_1755_;
goto v_reusejp_1769_;
}
else
{
lean_object* v_reuseFailAlloc_1771_; 
v_reuseFailAlloc_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1771_, 0, v___x_1768_);
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
else
{
lean_object* v_a_1773_; lean_object* v___x_1775_; uint8_t v_isShared_1776_; uint8_t v_isSharedCheck_1780_; 
lean_dec(v_mvarId_1737_);
v_a_1773_ = lean_ctor_get(v___x_1752_, 0);
v_isSharedCheck_1780_ = !lean_is_exclusive(v___x_1752_);
if (v_isSharedCheck_1780_ == 0)
{
v___x_1775_ = v___x_1752_;
v_isShared_1776_ = v_isSharedCheck_1780_;
goto v_resetjp_1774_;
}
else
{
lean_inc(v_a_1773_);
lean_dec(v___x_1752_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1781_, lean_object* v_localDecl_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_, lean_object* v_a_1787_){
_start:
{
lean_object* v_res_1788_; 
v_res_1788_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1781_, v_localDecl_1782_, v_a_1783_, v_a_1784_, v_a_1785_, v_a_1786_);
lean_dec(v_a_1786_);
lean_dec_ref(v_a_1785_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
return v_res_1788_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; 
v___x_1800_ = lean_box(0);
v___x_1801_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1802_ = l_Lean_mkConst(v___x_1801_, v___x_1800_);
return v___x_1802_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1803_; lean_object* v_dummy_1804_; 
v___x_1803_ = lean_box(0);
v_dummy_1804_ = l_Lean_Expr_sort___override(v___x_1803_);
return v_dummy_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1805_, lean_object* v_mvarId_1806_, lean_object* v_as_1807_, size_t v_sz_1808_, size_t v_i_1809_, lean_object* v_b_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_, lean_object* v___y_1813_, lean_object* v___y_1814_){
_start:
{
uint8_t v___x_1816_; 
v___x_1816_ = lean_usize_dec_lt(v_i_1809_, v_sz_1808_);
if (v___x_1816_ == 0)
{
lean_object* v___x_1817_; 
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v___x_1817_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1817_, 0, v_b_1810_);
return v___x_1817_;
}
else
{
lean_object* v_snd_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_2399_; 
v_snd_1818_ = lean_ctor_get(v_b_1810_, 1);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_b_1810_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; 
v_unused_2400_ = lean_ctor_get(v_b_1810_, 0);
lean_dec(v_unused_2400_);
v___x_1820_ = v_b_1810_;
v_isShared_1821_ = v_isSharedCheck_2399_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_snd_1818_);
lean_dec(v_b_1810_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_2399_;
goto v_resetjp_1819_;
}
v_resetjp_1819_:
{
lean_object* v_a_1823_; lean_object* v___x_1829_; lean_object* v_a_1831_; lean_object* v_a_1836_; 
v___x_1829_ = lean_box(0);
v_a_1836_ = lean_array_uget(v_as_1807_, v_i_1809_);
if (lean_obj_tag(v_a_1836_) == 0)
{
lean_del_object(v___x_1820_);
v_a_1831_ = v_snd_1818_;
goto v___jp_1830_;
}
else
{
lean_object* v_val_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_2398_; 
v_val_1837_ = lean_ctor_get(v_a_1836_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v_a_1836_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_1839_ = v_a_1836_;
v_isShared_1840_ = v_isSharedCheck_2398_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_val_1837_);
lean_dec(v_a_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_2398_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___x_1842_; uint8_t v___y_1844_; uint8_t v___y_1845_; lean_object* v___y_1846_; lean_object* v___y_1847_; lean_object* v___y_1848_; lean_object* v___y_1849_; uint8_t v___x_1869_; 
v___x_1841_ = lean_box(0);
v___x_1842_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1869_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1837_);
if (v___x_1869_ == 0)
{
lean_object* v___x_1870_; uint8_t v___y_1872_; uint8_t v___y_1873_; lean_object* v___y_1874_; lean_object* v___y_1875_; lean_object* v___y_1876_; lean_object* v___y_1877_; uint8_t v___y_1895_; lean_object* v___y_1896_; lean_object* v___y_1897_; lean_object* v___y_1898_; uint8_t v___y_1899_; lean_object* v___y_1900_; lean_object* v_a_1901_; uint8_t v___y_1907_; lean_object* v___y_1908_; lean_object* v___y_1909_; lean_object* v___y_1910_; lean_object* v___y_1911_; uint8_t v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; uint8_t v___y_1951_; uint8_t v_isHEq_1952_; lean_object* v___y_1953_; lean_object* v___y_1954_; lean_object* v___y_1955_; lean_object* v___y_1956_; uint8_t v_isEq_1994_; lean_object* v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2201_; lean_object* v___y_2202_; lean_object* v___y_2203_; lean_object* v___y_2204_; lean_object* v___x_2335_; 
v___x_1870_ = l_Lean_LocalDecl_type(v_val_1837_);
lean_inc_ref(v___x_1870_);
v___x_2335_ = l_Lean_Meta_matchNot_x3f(v___x_1870_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
if (lean_obj_tag(v_a_2336_) == 1)
{
lean_object* v_val_2337_; lean_object* v___x_2338_; 
v_val_2337_ = lean_ctor_get(v_a_2336_, 0);
lean_inc(v_val_2337_);
lean_dec_ref_known(v_a_2336_, 1);
v___x_2338_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2337_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
if (lean_obj_tag(v_a_2339_) == 1)
{
lean_object* v_val_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2381_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec_ref(v_config_1805_);
v_val_2340_ = lean_ctor_get(v_a_2339_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_a_2339_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2342_ = v_a_2339_;
v_isShared_2343_ = v_isSharedCheck_2381_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_val_2340_);
lean_dec(v_a_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2381_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2344_; 
lean_inc(v_mvarId_1806_);
v___x_2344_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v_a_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; 
v_a_2345_ = lean_ctor_get(v___x_2344_, 0);
lean_inc(v_a_2345_);
lean_dec_ref_known(v___x_2344_, 1);
v___x_2346_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_2347_ = l_Lean_mkFVar(v_val_2340_);
v___x_2348_ = l_Lean_Expr_app___override(v___x_2346_, v___x_2347_);
v___x_2349_ = l_Lean_Meta_mkFalseElim(v_a_2345_, v___x_2348_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v_a_2350_; lean_object* v___x_2351_; 
v_a_2350_ = lean_ctor_get(v___x_2349_, 0);
lean_inc(v_a_2350_);
lean_dec_ref_known(v___x_2349_, 1);
v___x_2351_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_2350_, v___y_1812_);
if (lean_obj_tag(v___x_2351_) == 0)
{
lean_object* v___x_2352_; lean_object* v___x_2354_; 
lean_dec_ref_known(v___x_2351_, 1);
v___x_2352_ = lean_box(v___x_1816_);
if (v_isShared_2343_ == 0)
{
lean_ctor_set(v___x_2342_, 0, v___x_2352_);
v___x_2354_ = v___x_2342_;
goto v_reusejp_2353_;
}
else
{
lean_object* v_reuseFailAlloc_2356_; 
v_reuseFailAlloc_2356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2356_, 0, v___x_2352_);
v___x_2354_ = v_reuseFailAlloc_2356_;
goto v_reusejp_2353_;
}
v_reusejp_2353_:
{
lean_object* v___x_2355_; 
v___x_2355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2355_, 0, v___x_2354_);
lean_ctor_set(v___x_2355_, 1, v___x_1841_);
v_a_1823_ = v___x_2355_;
goto v___jp_1822_;
}
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_del_object(v___x_2342_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_2357_ = lean_ctor_get(v___x_2351_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2351_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2351_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2351_);
v___x_2359_ = lean_box(0);
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
v_resetjp_2358_:
{
lean_object* v___x_2362_; 
if (v_isShared_2360_ == 0)
{
v___x_2362_ = v___x_2359_;
goto v_reusejp_2361_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v_a_2357_);
v___x_2362_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2361_;
}
v_reusejp_2361_:
{
return v___x_2362_;
}
}
}
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_del_object(v___x_2342_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2365_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2349_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2349_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_del_object(v___x_2342_);
lean_dec(v_val_2340_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2373_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2344_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2344_);
v___x_2375_ = lean_box(0);
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
v_resetjp_2374_:
{
lean_object* v___x_2378_; 
if (v_isShared_2376_ == 0)
{
v___x_2378_ = v___x_2375_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v_a_2373_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
}
}
else
{
lean_dec(v_a_2339_);
v___y_2201_ = v___y_1811_;
v___y_2202_ = v___y_1812_;
v___y_2203_ = v___y_1813_;
v___y_2204_ = v___y_1814_;
goto v___jp_2200_;
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2382_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2338_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2338_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_dec(v_a_2336_);
v___y_2201_ = v___y_1811_;
v___y_2202_ = v___y_1812_;
v___y_2203_ = v___y_1813_;
v___y_2204_ = v___y_1814_;
goto v___jp_2200_;
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2390_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2335_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2335_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
v___jp_1871_:
{
uint8_t v_genDiseq_1878_; 
v_genDiseq_1878_ = lean_ctor_get_uint8(v_config_1805_, sizeof(void*)*1 + 2);
if (v_genDiseq_1878_ == 0)
{
lean_dec_ref(v___x_1870_);
v___y_1844_ = v___y_1872_;
v___y_1845_ = v___y_1873_;
v___y_1846_ = v___y_1874_;
v___y_1847_ = v___y_1875_;
v___y_1848_ = v___y_1876_;
v___y_1849_ = v___y_1877_;
goto v___jp_1843_;
}
else
{
uint8_t v___x_1879_; 
v___x_1879_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1870_);
if (v___x_1879_ == 0)
{
v___y_1844_ = v___y_1872_;
v___y_1845_ = v___y_1873_;
v___y_1846_ = v___y_1874_;
v___y_1847_ = v___y_1875_;
v___y_1848_ = v___y_1876_;
v___y_1849_ = v___y_1877_;
goto v___jp_1843_;
}
else
{
lean_object* v___x_1880_; 
lean_inc(v_val_1837_);
lean_inc(v_mvarId_1806_);
v___x_1880_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1806_, v_val_1837_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
if (lean_obj_tag(v___x_1880_) == 0)
{
lean_object* v_a_1881_; uint8_t v___x_1882_; 
v_a_1881_ = lean_ctor_get(v___x_1880_, 0);
lean_inc(v_a_1881_);
lean_dec_ref_known(v___x_1880_, 1);
v___x_1882_ = lean_unbox(v_a_1881_);
lean_dec(v_a_1881_);
if (v___x_1882_ == 0)
{
v___y_1844_ = v___y_1872_;
v___y_1845_ = v___y_1873_;
v___y_1846_ = v___y_1874_;
v___y_1847_ = v___y_1875_;
v___y_1848_ = v___y_1876_;
v___y_1849_ = v___y_1877_;
goto v___jp_1843_;
}
else
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v___x_1883_ = lean_box(v___x_1816_);
v___x_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1884_, 0, v___x_1883_);
v___x_1885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v___x_1841_);
v_a_1823_ = v___x_1885_;
goto v___jp_1822_;
}
}
else
{
lean_object* v_a_1886_; lean_object* v___x_1888_; uint8_t v_isShared_1889_; uint8_t v_isSharedCheck_1893_; 
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_1886_ = lean_ctor_get(v___x_1880_, 0);
v_isSharedCheck_1893_ = !lean_is_exclusive(v___x_1880_);
if (v_isSharedCheck_1893_ == 0)
{
v___x_1888_ = v___x_1880_;
v_isShared_1889_ = v_isSharedCheck_1893_;
goto v_resetjp_1887_;
}
else
{
lean_inc(v_a_1886_);
lean_dec(v___x_1880_);
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
}
v___jp_1894_:
{
uint8_t v___x_1902_; 
v___x_1902_ = l_Lean_Exception_isInterrupt(v_a_1901_);
if (v___x_1902_ == 0)
{
uint8_t v___x_1903_; 
lean_inc_ref(v_a_1901_);
v___x_1903_ = l_Lean_Exception_isRuntime(v_a_1901_);
if (v___x_1903_ == 0)
{
lean_dec_ref(v_a_1901_);
v___y_1872_ = v___y_1895_;
v___y_1873_ = v___y_1899_;
v___y_1874_ = v___y_1900_;
v___y_1875_ = v___y_1898_;
v___y_1876_ = v___y_1897_;
v___y_1877_ = v___y_1896_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1904_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v___x_1904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1904_, 0, v_a_1901_);
return v___x_1904_;
}
}
else
{
lean_object* v___x_1905_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v___x_1905_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1905_, 0, v_a_1901_);
return v___x_1905_;
}
}
v___jp_1906_:
{
if (lean_obj_tag(v___y_1914_) == 0)
{
lean_object* v_a_1915_; lean_object* v___x_1916_; uint8_t v___x_1917_; 
v_a_1915_ = lean_ctor_get(v___y_1914_, 0);
lean_inc(v_a_1915_);
lean_dec_ref_known(v___y_1914_, 1);
v___x_1916_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_1917_ = l_Lean_Expr_isConstOf(v_a_1915_, v___x_1916_);
lean_dec(v_a_1915_);
if (v___x_1917_ == 0)
{
lean_dec_ref(v___y_1909_);
v___y_1872_ = v___y_1907_;
v___y_1873_ = v___y_1912_;
v___y_1874_ = v___y_1913_;
v___y_1875_ = v___y_1911_;
v___y_1876_ = v___y_1910_;
v___y_1877_ = v___y_1908_;
goto v___jp_1871_;
}
else
{
lean_object* v___x_1918_; 
lean_inc_ref(v___y_1909_);
v___x_1918_ = l_Lean_Meta_mkEqRefl(v___y_1909_, v___y_1913_, v___y_1911_, v___y_1910_, v___y_1908_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v_a_1919_; lean_object* v___x_1920_; lean_object* v_dummy_1921_; lean_object* v_nargs_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; 
v_a_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1919_);
lean_dec_ref_known(v___x_1918_, 1);
v___x_1920_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_1921_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_1922_ = l_Lean_Expr_getAppNumArgs(v___y_1909_);
lean_inc(v_nargs_1922_);
v___x_1923_ = lean_mk_array(v_nargs_1922_, v_dummy_1921_);
v___x_1924_ = lean_unsigned_to_nat(1u);
v___x_1925_ = lean_nat_sub(v_nargs_1922_, v___x_1924_);
lean_dec(v_nargs_1922_);
v___x_1926_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_1909_, v___x_1923_, v___x_1925_);
v___x_1927_ = lean_array_push(v___x_1926_, v_a_1919_);
v___x_1928_ = l_Lean_mkAppN(v___x_1920_, v___x_1927_);
lean_dec_ref(v___x_1927_);
lean_inc(v_mvarId_1806_);
v___x_1929_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_1913_, v___y_1911_, v___y_1910_, v___y_1908_);
if (lean_obj_tag(v___x_1929_) == 0)
{
lean_object* v_a_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v_a_1930_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1930_);
lean_dec_ref_known(v___x_1929_, 1);
lean_inc(v_val_1837_);
v___x_1931_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_1932_ = l_Lean_Meta_mkAbsurd(v_a_1930_, v___x_1931_, v___x_1928_, v___y_1913_, v___y_1911_, v___y_1910_, v___y_1908_);
if (lean_obj_tag(v___x_1932_) == 0)
{
lean_object* v_a_1933_; lean_object* v___x_1934_; 
v_a_1933_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1933_);
lean_dec_ref_known(v___x_1932_, 1);
lean_inc(v_mvarId_1806_);
v___x_1934_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_1933_, v___y_1911_);
if (lean_obj_tag(v___x_1934_) == 0)
{
lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1943_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_isSharedCheck_1943_ = !lean_is_exclusive(v___x_1934_);
if (v_isSharedCheck_1943_ == 0)
{
lean_object* v_unused_1944_; 
v_unused_1944_ = lean_ctor_get(v___x_1934_, 0);
lean_dec(v_unused_1944_);
v___x_1936_ = v___x_1934_;
v_isShared_1937_ = v_isSharedCheck_1943_;
goto v_resetjp_1935_;
}
else
{
lean_dec(v___x_1934_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1943_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1938_; lean_object* v___x_1940_; 
v___x_1938_ = lean_box(v___x_1816_);
if (v_isShared_1937_ == 0)
{
lean_ctor_set_tag(v___x_1936_, 1);
lean_ctor_set(v___x_1936_, 0, v___x_1938_);
v___x_1940_ = v___x_1936_;
goto v_reusejp_1939_;
}
else
{
lean_object* v_reuseFailAlloc_1942_; 
v_reuseFailAlloc_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1942_, 0, v___x_1938_);
v___x_1940_ = v_reuseFailAlloc_1942_;
goto v_reusejp_1939_;
}
v_reusejp_1939_:
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1941_, 0, v___x_1940_);
lean_ctor_set(v___x_1941_, 1, v___x_1841_);
v_a_1823_ = v___x_1941_;
goto v___jp_1822_;
}
}
}
else
{
lean_object* v_a_1945_; 
v_a_1945_ = lean_ctor_get(v___x_1934_, 0);
lean_inc(v_a_1945_);
lean_dec_ref_known(v___x_1934_, 1);
v___y_1895_ = v___y_1907_;
v___y_1896_ = v___y_1908_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v___y_1900_ = v___y_1913_;
v_a_1901_ = v_a_1945_;
goto v___jp_1894_;
}
}
else
{
lean_object* v_a_1946_; 
v_a_1946_ = lean_ctor_get(v___x_1932_, 0);
lean_inc(v_a_1946_);
lean_dec_ref_known(v___x_1932_, 1);
v___y_1895_ = v___y_1907_;
v___y_1896_ = v___y_1908_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v___y_1900_ = v___y_1913_;
v_a_1901_ = v_a_1946_;
goto v___jp_1894_;
}
}
else
{
lean_object* v_a_1947_; 
lean_dec_ref(v___x_1928_);
v_a_1947_ = lean_ctor_get(v___x_1929_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1929_, 1);
v___y_1895_ = v___y_1907_;
v___y_1896_ = v___y_1908_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v___y_1900_ = v___y_1913_;
v_a_1901_ = v_a_1947_;
goto v___jp_1894_;
}
}
else
{
lean_object* v_a_1948_; 
lean_dec_ref(v___y_1909_);
v_a_1948_ = lean_ctor_get(v___x_1918_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1918_, 1);
v___y_1895_ = v___y_1907_;
v___y_1896_ = v___y_1908_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v___y_1900_ = v___y_1913_;
v_a_1901_ = v_a_1948_;
goto v___jp_1894_;
}
}
}
else
{
lean_object* v_a_1949_; 
lean_dec_ref(v___y_1909_);
v_a_1949_ = lean_ctor_get(v___y_1914_, 0);
lean_inc(v_a_1949_);
lean_dec_ref_known(v___y_1914_, 1);
v___y_1895_ = v___y_1907_;
v___y_1896_ = v___y_1908_;
v___y_1897_ = v___y_1910_;
v___y_1898_ = v___y_1911_;
v___y_1899_ = v___y_1912_;
v___y_1900_ = v___y_1913_;
v_a_1901_ = v_a_1949_;
goto v___jp_1894_;
}
}
v___jp_1950_:
{
uint8_t v_useDecide_1957_; 
v_useDecide_1957_ = lean_ctor_get_uint8(v_config_1805_, sizeof(void*)*1);
if (v_useDecide_1957_ == 0)
{
v___y_1872_ = v_isHEq_1952_;
v___y_1873_ = v___y_1951_;
v___y_1874_ = v___y_1953_;
v___y_1875_ = v___y_1954_;
v___y_1876_ = v___y_1955_;
v___y_1877_ = v___y_1956_;
goto v___jp_1871_;
}
else
{
uint8_t v___x_1958_; 
v___x_1958_ = l_Lean_Expr_hasFVar(v___x_1870_);
if (v___x_1958_ == 0)
{
lean_object* v___x_1959_; 
lean_inc_ref(v___x_1870_);
v___x_1959_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1870_, v___y_1954_);
if (lean_obj_tag(v___x_1959_) == 0)
{
lean_object* v_a_1960_; uint8_t v___x_1961_; 
v_a_1960_ = lean_ctor_get(v___x_1959_, 0);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1959_, 1);
v___x_1961_ = l_Lean_Expr_hasMVar(v_a_1960_);
if (v___x_1961_ == 0)
{
uint8_t v___x_1962_; 
v___x_1962_ = l_Lean_Expr_hasFVar(v_a_1960_);
lean_dec(v_a_1960_);
if (v___x_1962_ == 0)
{
lean_object* v___x_1963_; 
lean_inc_ref(v___x_1870_);
v___x_1963_ = l_Lean_Meta_mkDecide(v___x_1870_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
if (lean_obj_tag(v___x_1963_) == 0)
{
lean_object* v_a_1964_; lean_object* v___x_1965_; uint8_t v_transparency_1966_; uint8_t v___x_1967_; uint8_t v___x_1968_; 
v_a_1964_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1964_);
lean_dec_ref_known(v___x_1963_, 1);
v___x_1965_ = l_Lean_Meta_Context_config(v___y_1953_);
v_transparency_1966_ = lean_ctor_get_uint8(v___x_1965_, 9);
lean_dec_ref(v___x_1965_);
v___x_1967_ = 1;
v___x_1968_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_1966_, v___x_1967_);
if (v___x_1968_ == 0)
{
lean_object* v_keyedConfig_1969_; uint8_t v_trackZetaDelta_1970_; lean_object* v_zetaDeltaSet_1971_; lean_object* v_lctx_1972_; lean_object* v_localInstances_1973_; lean_object* v_defEqCtx_x3f_1974_; lean_object* v_synthPendingDepth_1975_; lean_object* v_customCanUnfoldPredicate_x3f_1976_; uint8_t v_univApprox_1977_; uint8_t v_inTypeClassResolution_1978_; uint8_t v_cacheInferType_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v_keyedConfig_1969_ = lean_ctor_get(v___y_1953_, 0);
v_trackZetaDelta_1970_ = lean_ctor_get_uint8(v___y_1953_, sizeof(void*)*7);
v_zetaDeltaSet_1971_ = lean_ctor_get(v___y_1953_, 1);
v_lctx_1972_ = lean_ctor_get(v___y_1953_, 2);
v_localInstances_1973_ = lean_ctor_get(v___y_1953_, 3);
v_defEqCtx_x3f_1974_ = lean_ctor_get(v___y_1953_, 4);
v_synthPendingDepth_1975_ = lean_ctor_get(v___y_1953_, 5);
v_customCanUnfoldPredicate_x3f_1976_ = lean_ctor_get(v___y_1953_, 6);
v_univApprox_1977_ = lean_ctor_get_uint8(v___y_1953_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_1978_ = lean_ctor_get_uint8(v___y_1953_, sizeof(void*)*7 + 2);
v_cacheInferType_1979_ = lean_ctor_get_uint8(v___y_1953_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_1969_);
v___x_1980_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_1967_, v_keyedConfig_1969_);
lean_inc(v_customCanUnfoldPredicate_x3f_1976_);
lean_inc(v_synthPendingDepth_1975_);
lean_inc(v_defEqCtx_x3f_1974_);
lean_inc_ref(v_localInstances_1973_);
lean_inc_ref(v_lctx_1972_);
lean_inc(v_zetaDeltaSet_1971_);
v___x_1981_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v_zetaDeltaSet_1971_);
lean_ctor_set(v___x_1981_, 2, v_lctx_1972_);
lean_ctor_set(v___x_1981_, 3, v_localInstances_1973_);
lean_ctor_set(v___x_1981_, 4, v_defEqCtx_x3f_1974_);
lean_ctor_set(v___x_1981_, 5, v_synthPendingDepth_1975_);
lean_ctor_set(v___x_1981_, 6, v_customCanUnfoldPredicate_x3f_1976_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*7, v_trackZetaDelta_1970_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*7 + 1, v_univApprox_1977_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*7 + 2, v_inTypeClassResolution_1978_);
lean_ctor_set_uint8(v___x_1981_, sizeof(void*)*7 + 3, v_cacheInferType_1979_);
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
lean_inc(v___y_1954_);
lean_inc(v_a_1964_);
v___x_1982_ = lean_whnf(v_a_1964_, v___x_1981_, v___y_1954_, v___y_1955_, v___y_1956_);
v___y_1907_ = v_isHEq_1952_;
v___y_1908_ = v___y_1956_;
v___y_1909_ = v_a_1964_;
v___y_1910_ = v___y_1955_;
v___y_1911_ = v___y_1954_;
v___y_1912_ = v___y_1951_;
v___y_1913_ = v___y_1953_;
v___y_1914_ = v___x_1982_;
goto v___jp_1906_;
}
else
{
lean_object* v___x_1983_; 
lean_inc(v___y_1956_);
lean_inc_ref(v___y_1955_);
lean_inc(v___y_1954_);
lean_inc_ref(v___y_1953_);
lean_inc(v_a_1964_);
v___x_1983_ = lean_whnf(v_a_1964_, v___y_1953_, v___y_1954_, v___y_1955_, v___y_1956_);
v___y_1907_ = v_isHEq_1952_;
v___y_1908_ = v___y_1956_;
v___y_1909_ = v_a_1964_;
v___y_1910_ = v___y_1955_;
v___y_1911_ = v___y_1954_;
v___y_1912_ = v___y_1951_;
v___y_1913_ = v___y_1953_;
v___y_1914_ = v___x_1983_;
goto v___jp_1906_;
}
}
else
{
lean_object* v_a_1984_; 
v_a_1984_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_a_1984_);
lean_dec_ref_known(v___x_1963_, 1);
v___y_1895_ = v_isHEq_1952_;
v___y_1896_ = v___y_1956_;
v___y_1897_ = v___y_1955_;
v___y_1898_ = v___y_1954_;
v___y_1899_ = v___y_1951_;
v___y_1900_ = v___y_1953_;
v_a_1901_ = v_a_1984_;
goto v___jp_1894_;
}
}
else
{
v___y_1872_ = v_isHEq_1952_;
v___y_1873_ = v___y_1951_;
v___y_1874_ = v___y_1953_;
v___y_1875_ = v___y_1954_;
v___y_1876_ = v___y_1955_;
v___y_1877_ = v___y_1956_;
goto v___jp_1871_;
}
}
else
{
lean_dec(v_a_1960_);
v___y_1872_ = v_isHEq_1952_;
v___y_1873_ = v___y_1951_;
v___y_1874_ = v___y_1953_;
v___y_1875_ = v___y_1954_;
v___y_1876_ = v___y_1955_;
v___y_1877_ = v___y_1956_;
goto v___jp_1871_;
}
}
else
{
lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_1985_ = lean_ctor_get(v___x_1959_, 0);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1959_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1959_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_dec(v___x_1959_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
v___y_1872_ = v_isHEq_1952_;
v___y_1873_ = v___y_1951_;
v___y_1874_ = v___y_1953_;
v___y_1875_ = v___y_1954_;
v___y_1876_ = v___y_1955_;
v___y_1877_ = v___y_1956_;
goto v___jp_1871_;
}
}
}
v___jp_1993_:
{
lean_object* v___x_1999_; 
lean_inc_ref(v___x_1870_);
v___x_1999_ = l_Lean_Meta_matchHEq_x3f(v___x_1870_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_1999_) == 0)
{
lean_object* v_a_2000_; 
v_a_2000_ = lean_ctor_get(v___x_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___x_1999_, 1);
if (lean_obj_tag(v_a_2000_) == 1)
{
lean_object* v_val_2001_; lean_object* v_snd_2002_; lean_object* v_snd_2003_; lean_object* v_fst_2004_; lean_object* v_fst_2005_; lean_object* v_fst_2006_; lean_object* v_snd_2007_; lean_object* v___x_2009_; uint8_t v_isShared_2010_; uint8_t v_isSharedCheck_2100_; 
v_val_2001_ = lean_ctor_get(v_a_2000_, 0);
lean_inc(v_val_2001_);
lean_dec_ref_known(v_a_2000_, 1);
v_snd_2002_ = lean_ctor_get(v_val_2001_, 1);
lean_inc(v_snd_2002_);
v_snd_2003_ = lean_ctor_get(v_snd_2002_, 1);
lean_inc(v_snd_2003_);
v_fst_2004_ = lean_ctor_get(v_val_2001_, 0);
lean_inc(v_fst_2004_);
lean_dec(v_val_2001_);
v_fst_2005_ = lean_ctor_get(v_snd_2002_, 0);
lean_inc(v_fst_2005_);
lean_dec(v_snd_2002_);
v_fst_2006_ = lean_ctor_get(v_snd_2003_, 0);
v_snd_2007_ = lean_ctor_get(v_snd_2003_, 1);
v_isSharedCheck_2100_ = !lean_is_exclusive(v_snd_2003_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2009_ = v_snd_2003_;
v_isShared_2010_ = v_isSharedCheck_2100_;
goto v_resetjp_2008_;
}
else
{
lean_inc(v_snd_2007_);
lean_inc(v_fst_2006_);
lean_dec(v_snd_2003_);
v___x_2009_ = lean_box(0);
v_isShared_2010_ = v_isSharedCheck_2100_;
goto v_resetjp_2008_;
}
v_resetjp_2008_:
{
lean_object* v___x_2011_; 
v___x_2011_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2005_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
if (lean_obj_tag(v_a_2012_) == 1)
{
lean_object* v_val_2013_; lean_object* v___x_2014_; 
v_val_2013_ = lean_ctor_get(v_a_2012_, 0);
lean_inc(v_val_2013_);
lean_dec_ref_known(v_a_2012_, 1);
v___x_2014_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2007_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
if (lean_obj_tag(v_a_2015_) == 1)
{
lean_object* v_toConstantVal_2016_; lean_object* v_val_2017_; lean_object* v___x_2019_; uint8_t v_isShared_2020_; uint8_t v_isSharedCheck_2083_; 
v_toConstantVal_2016_ = lean_ctor_get(v_val_2013_, 0);
lean_inc_ref(v_toConstantVal_2016_);
lean_dec(v_val_2013_);
v_val_2017_ = lean_ctor_get(v_a_2015_, 0);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_a_2015_);
if (v_isSharedCheck_2083_ == 0)
{
v___x_2019_ = v_a_2015_;
v_isShared_2020_ = v_isSharedCheck_2083_;
goto v_resetjp_2018_;
}
else
{
lean_inc(v_val_2017_);
lean_dec(v_a_2015_);
v___x_2019_ = lean_box(0);
v_isShared_2020_ = v_isSharedCheck_2083_;
goto v_resetjp_2018_;
}
v_resetjp_2018_:
{
lean_object* v_toConstantVal_2021_; lean_object* v_name_2022_; lean_object* v_name_2023_; uint8_t v___x_2024_; 
v_toConstantVal_2021_ = lean_ctor_get(v_val_2017_, 0);
lean_inc_ref(v_toConstantVal_2021_);
lean_dec(v_val_2017_);
v_name_2022_ = lean_ctor_get(v_toConstantVal_2016_, 0);
lean_inc(v_name_2022_);
lean_dec_ref(v_toConstantVal_2016_);
v_name_2023_ = lean_ctor_get(v_toConstantVal_2021_, 0);
lean_inc(v_name_2023_);
lean_dec_ref(v_toConstantVal_2021_);
v___x_2024_ = lean_name_eq(v_name_2022_, v_name_2023_);
lean_dec(v_name_2023_);
lean_dec(v_name_2022_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; 
v___x_2025_ = l_Lean_Meta_isExprDefEq(v_fst_2004_, v_fst_2006_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
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
lean_del_object(v___x_2019_);
lean_del_object(v___x_2009_);
v___y_1951_ = v_isEq_1994_;
v_isHEq_1952_ = v___x_1816_;
v___y_1953_ = v___y_1995_;
v___y_1954_ = v___y_1996_;
v___y_1955_ = v___y_1997_;
v___y_1956_ = v___y_1998_;
goto v___jp_1950_;
}
else
{
lean_object* v___x_2028_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec_ref(v_config_1805_);
lean_inc(v_mvarId_1806_);
v___x_2028_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2028_) == 0)
{
lean_object* v_a_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v_a_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2028_, 1);
v___x_2030_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_2031_ = l_Lean_Meta_mkEqOfHEq(v___x_2030_, v___x_1816_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2031_) == 0)
{
lean_object* v_a_2032_; lean_object* v___x_2033_; 
v_a_2032_ = lean_ctor_get(v___x_2031_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2031_, 1);
v___x_2033_ = l_Lean_Meta_mkNoConfusion(v_a_2029_, v_a_2032_, v___y_1995_, v___y_1996_, v___y_1997_, v___y_1998_);
if (lean_obj_tag(v___x_2033_) == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; 
v_a_2034_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___x_2033_, 1);
v___x_2035_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_2034_, v___y_1996_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_object* v___x_2036_; lean_object* v___x_2038_; 
lean_dec_ref_known(v___x_2035_, 1);
v___x_2036_ = lean_box(v___x_1816_);
if (v_isShared_2020_ == 0)
{
lean_ctor_set(v___x_2019_, 0, v___x_2036_);
v___x_2038_ = v___x_2019_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v___x_2036_);
v___x_2038_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
lean_object* v___x_2040_; 
if (v_isShared_2010_ == 0)
{
lean_ctor_set(v___x_2009_, 1, v___x_1841_);
lean_ctor_set(v___x_2009_, 0, v___x_2038_);
v___x_2040_ = v___x_2009_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v___x_1841_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
v_a_1823_ = v___x_2040_;
goto v___jp_1822_;
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_del_object(v___x_2019_);
lean_del_object(v___x_2009_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_2043_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2035_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2035_);
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
lean_del_object(v___x_2019_);
lean_del_object(v___x_2009_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2051_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2058_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2058_ == 0)
{
v___x_2053_ = v___x_2033_;
v_isShared_2054_ = v_isSharedCheck_2058_;
goto v_resetjp_2052_;
}
else
{
lean_inc(v_a_2051_);
lean_dec(v___x_2033_);
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
lean_object* v_a_2059_; lean_object* v___x_2061_; uint8_t v_isShared_2062_; uint8_t v_isSharedCheck_2066_; 
lean_dec(v_a_2029_);
lean_del_object(v___x_2019_);
lean_del_object(v___x_2009_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2059_ = lean_ctor_get(v___x_2031_, 0);
v_isSharedCheck_2066_ = !lean_is_exclusive(v___x_2031_);
if (v_isSharedCheck_2066_ == 0)
{
v___x_2061_ = v___x_2031_;
v_isShared_2062_ = v_isSharedCheck_2066_;
goto v_resetjp_2060_;
}
else
{
lean_inc(v_a_2059_);
lean_dec(v___x_2031_);
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
lean_object* v_a_2067_; lean_object* v___x_2069_; uint8_t v_isShared_2070_; uint8_t v_isSharedCheck_2074_; 
lean_del_object(v___x_2019_);
lean_del_object(v___x_2009_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2067_ = lean_ctor_get(v___x_2028_, 0);
v_isSharedCheck_2074_ = !lean_is_exclusive(v___x_2028_);
if (v_isSharedCheck_2074_ == 0)
{
v___x_2069_ = v___x_2028_;
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
else
{
lean_inc(v_a_2067_);
lean_dec(v___x_2028_);
v___x_2069_ = lean_box(0);
v_isShared_2070_ = v_isSharedCheck_2074_;
goto v_resetjp_2068_;
}
v_resetjp_2068_:
{
lean_object* v___x_2072_; 
if (v_isShared_2070_ == 0)
{
v___x_2072_ = v___x_2069_;
goto v_reusejp_2071_;
}
else
{
lean_object* v_reuseFailAlloc_2073_; 
v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
v___x_2072_ = v_reuseFailAlloc_2073_;
goto v_reusejp_2071_;
}
v_reusejp_2071_:
{
return v___x_2072_;
}
}
}
}
}
else
{
lean_object* v_a_2075_; lean_object* v___x_2077_; uint8_t v_isShared_2078_; uint8_t v_isSharedCheck_2082_; 
lean_del_object(v___x_2019_);
lean_del_object(v___x_2009_);
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2075_ = lean_ctor_get(v___x_2025_, 0);
v_isSharedCheck_2082_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2082_ == 0)
{
v___x_2077_ = v___x_2025_;
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
else
{
lean_inc(v_a_2075_);
lean_dec(v___x_2025_);
v___x_2077_ = lean_box(0);
v_isShared_2078_ = v_isSharedCheck_2082_;
goto v_resetjp_2076_;
}
v_resetjp_2076_:
{
lean_object* v___x_2080_; 
if (v_isShared_2078_ == 0)
{
v___x_2080_ = v___x_2077_;
goto v_reusejp_2079_;
}
else
{
lean_object* v_reuseFailAlloc_2081_; 
v_reuseFailAlloc_2081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2081_, 0, v_a_2075_);
v___x_2080_ = v_reuseFailAlloc_2081_;
goto v_reusejp_2079_;
}
v_reusejp_2079_:
{
return v___x_2080_;
}
}
}
}
else
{
lean_del_object(v___x_2019_);
lean_del_object(v___x_2009_);
lean_dec(v_fst_2006_);
lean_dec(v_fst_2004_);
v___y_1951_ = v_isEq_1994_;
v_isHEq_1952_ = v___x_1816_;
v___y_1953_ = v___y_1995_;
v___y_1954_ = v___y_1996_;
v___y_1955_ = v___y_1997_;
v___y_1956_ = v___y_1998_;
goto v___jp_1950_;
}
}
}
else
{
lean_dec(v_a_2015_);
lean_dec(v_val_2013_);
lean_del_object(v___x_2009_);
lean_dec(v_fst_2006_);
lean_dec(v_fst_2004_);
v___y_1951_ = v_isEq_1994_;
v_isHEq_1952_ = v___x_1816_;
v___y_1953_ = v___y_1995_;
v___y_1954_ = v___y_1996_;
v___y_1955_ = v___y_1997_;
v___y_1956_ = v___y_1998_;
goto v___jp_1950_;
}
}
else
{
lean_object* v_a_2084_; lean_object* v___x_2086_; uint8_t v_isShared_2087_; uint8_t v_isSharedCheck_2091_; 
lean_dec(v_val_2013_);
lean_del_object(v___x_2009_);
lean_dec(v_fst_2006_);
lean_dec(v_fst_2004_);
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2084_ = lean_ctor_get(v___x_2014_, 0);
v_isSharedCheck_2091_ = !lean_is_exclusive(v___x_2014_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2086_ = v___x_2014_;
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
else
{
lean_inc(v_a_2084_);
lean_dec(v___x_2014_);
v___x_2086_ = lean_box(0);
v_isShared_2087_ = v_isSharedCheck_2091_;
goto v_resetjp_2085_;
}
v_resetjp_2085_:
{
lean_object* v___x_2089_; 
if (v_isShared_2087_ == 0)
{
v___x_2089_ = v___x_2086_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2090_; 
v_reuseFailAlloc_2090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2090_, 0, v_a_2084_);
v___x_2089_ = v_reuseFailAlloc_2090_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
return v___x_2089_;
}
}
}
}
else
{
lean_dec(v_a_2012_);
lean_del_object(v___x_2009_);
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
lean_dec(v_fst_2004_);
v___y_1951_ = v_isEq_1994_;
v_isHEq_1952_ = v___x_1816_;
v___y_1953_ = v___y_1995_;
v___y_1954_ = v___y_1996_;
v___y_1955_ = v___y_1997_;
v___y_1956_ = v___y_1998_;
goto v___jp_1950_;
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_del_object(v___x_2009_);
lean_dec(v_snd_2007_);
lean_dec(v_fst_2006_);
lean_dec(v_fst_2004_);
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2092_ = lean_ctor_get(v___x_2011_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2011_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2011_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2011_);
v___x_2094_ = lean_box(0);
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
v_resetjp_2093_:
{
lean_object* v___x_2097_; 
if (v_isShared_2095_ == 0)
{
v___x_2097_ = v___x_2094_;
goto v_reusejp_2096_;
}
else
{
lean_object* v_reuseFailAlloc_2098_; 
v_reuseFailAlloc_2098_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_a_2092_);
v___x_2097_ = v_reuseFailAlloc_2098_;
goto v_reusejp_2096_;
}
v_reusejp_2096_:
{
return v___x_2097_;
}
}
}
}
}
else
{
lean_dec(v_a_2000_);
v___y_1951_ = v_isEq_1994_;
v_isHEq_1952_ = v___x_1869_;
v___y_1953_ = v___y_1995_;
v___y_1954_ = v___y_1996_;
v___y_1955_ = v___y_1997_;
v___y_1956_ = v___y_1998_;
goto v___jp_1950_;
}
}
else
{
lean_object* v_a_2101_; lean_object* v___x_2103_; uint8_t v_isShared_2104_; uint8_t v_isSharedCheck_2108_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2101_ = lean_ctor_get(v___x_1999_, 0);
v_isSharedCheck_2108_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2108_ == 0)
{
v___x_2103_ = v___x_1999_;
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
else
{
lean_inc(v_a_2101_);
lean_dec(v___x_1999_);
v___x_2103_ = lean_box(0);
v_isShared_2104_ = v_isSharedCheck_2108_;
goto v_resetjp_2102_;
}
v_resetjp_2102_:
{
lean_object* v___x_2106_; 
if (v_isShared_2104_ == 0)
{
v___x_2106_ = v___x_2103_;
goto v_reusejp_2105_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v_a_2101_);
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
v___jp_2109_:
{
lean_object* v___x_2114_; 
lean_inc_ref(v___x_1870_);
v___x_2114_ = l_Lean_Meta_matchEq_x3f(v___x_1870_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
if (lean_obj_tag(v_a_2115_) == 1)
{
lean_object* v_val_2116_; lean_object* v_snd_2117_; lean_object* v_fst_2118_; lean_object* v_snd_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2191_; 
v_val_2116_ = lean_ctor_get(v_a_2115_, 0);
lean_inc(v_val_2116_);
lean_dec_ref_known(v_a_2115_, 1);
v_snd_2117_ = lean_ctor_get(v_val_2116_, 1);
lean_inc(v_snd_2117_);
lean_dec(v_val_2116_);
v_fst_2118_ = lean_ctor_get(v_snd_2117_, 0);
v_snd_2119_ = lean_ctor_get(v_snd_2117_, 1);
v_isSharedCheck_2191_ = !lean_is_exclusive(v_snd_2117_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2121_ = v_snd_2117_;
v_isShared_2122_ = v_isSharedCheck_2191_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_snd_2119_);
lean_inc(v_fst_2118_);
lean_dec(v_snd_2117_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2191_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2123_; 
v___x_2123_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2118_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2123_) == 0)
{
lean_object* v_a_2124_; 
v_a_2124_ = lean_ctor_get(v___x_2123_, 0);
lean_inc(v_a_2124_);
lean_dec_ref_known(v___x_2123_, 1);
if (lean_obj_tag(v_a_2124_) == 1)
{
lean_object* v_val_2125_; lean_object* v___x_2126_; 
v_val_2125_ = lean_ctor_get(v_a_2124_, 0);
lean_inc(v_val_2125_);
lean_dec_ref_known(v_a_2124_, 1);
v___x_2126_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2119_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
if (lean_obj_tag(v_a_2127_) == 1)
{
lean_object* v_toConstantVal_2128_; lean_object* v_val_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2174_; 
v_toConstantVal_2128_ = lean_ctor_get(v_val_2125_, 0);
lean_inc_ref(v_toConstantVal_2128_);
lean_dec(v_val_2125_);
v_val_2129_ = lean_ctor_get(v_a_2127_, 0);
v_isSharedCheck_2174_ = !lean_is_exclusive(v_a_2127_);
if (v_isSharedCheck_2174_ == 0)
{
v___x_2131_ = v_a_2127_;
v_isShared_2132_ = v_isSharedCheck_2174_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_val_2129_);
lean_dec(v_a_2127_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2174_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v_toConstantVal_2133_; lean_object* v_name_2134_; lean_object* v_name_2135_; uint8_t v___x_2136_; 
v_toConstantVal_2133_ = lean_ctor_get(v_val_2129_, 0);
lean_inc_ref(v_toConstantVal_2133_);
lean_dec(v_val_2129_);
v_name_2134_ = lean_ctor_get(v_toConstantVal_2128_, 0);
lean_inc(v_name_2134_);
lean_dec_ref(v_toConstantVal_2128_);
v_name_2135_ = lean_ctor_get(v_toConstantVal_2133_, 0);
lean_inc(v_name_2135_);
lean_dec_ref(v_toConstantVal_2133_);
v___x_2136_ = lean_name_eq(v_name_2134_, v_name_2135_);
lean_dec(v_name_2135_);
lean_dec(v_name_2134_);
if (v___x_2136_ == 0)
{
lean_object* v___x_2137_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec_ref(v_config_1805_);
lean_inc(v_mvarId_1806_);
v___x_2137_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2137_) == 0)
{
lean_object* v_a_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; 
v_a_2138_ = lean_ctor_get(v___x_2137_, 0);
lean_inc(v_a_2138_);
lean_dec_ref_known(v___x_2137_, 1);
v___x_2139_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_2140_ = l_Lean_Meta_mkNoConfusion(v_a_2138_, v___x_2139_, v___y_2110_, v___y_2111_, v___y_2112_, v___y_2113_);
if (lean_obj_tag(v___x_2140_) == 0)
{
lean_object* v_a_2141_; lean_object* v___x_2142_; 
v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
lean_inc(v_a_2141_);
lean_dec_ref_known(v___x_2140_, 1);
v___x_2142_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_2141_, v___y_2111_);
if (lean_obj_tag(v___x_2142_) == 0)
{
lean_object* v___x_2143_; lean_object* v___x_2145_; 
lean_dec_ref_known(v___x_2142_, 1);
v___x_2143_ = lean_box(v___x_1816_);
if (v_isShared_2132_ == 0)
{
lean_ctor_set(v___x_2131_, 0, v___x_2143_);
v___x_2145_ = v___x_2131_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2122_ == 0)
{
lean_ctor_set(v___x_2121_, 1, v___x_1841_);
lean_ctor_set(v___x_2121_, 0, v___x_2145_);
v___x_2147_ = v___x_2121_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2148_, 1, v___x_1841_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
v_a_1823_ = v___x_2147_;
goto v___jp_1822_;
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_del_object(v___x_2131_);
lean_del_object(v___x_2121_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_2150_ = lean_ctor_get(v___x_2142_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2142_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2142_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2142_);
v___x_2152_ = lean_box(0);
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
v_resetjp_2151_:
{
lean_object* v___x_2155_; 
if (v_isShared_2153_ == 0)
{
v___x_2155_ = v___x_2152_;
goto v_reusejp_2154_;
}
else
{
lean_object* v_reuseFailAlloc_2156_; 
v_reuseFailAlloc_2156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2156_, 0, v_a_2150_);
v___x_2155_ = v_reuseFailAlloc_2156_;
goto v_reusejp_2154_;
}
v_reusejp_2154_:
{
return v___x_2155_;
}
}
}
}
else
{
lean_object* v_a_2158_; lean_object* v___x_2160_; uint8_t v_isShared_2161_; uint8_t v_isSharedCheck_2165_; 
lean_del_object(v___x_2131_);
lean_del_object(v___x_2121_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2158_ = lean_ctor_get(v___x_2140_, 0);
v_isSharedCheck_2165_ = !lean_is_exclusive(v___x_2140_);
if (v_isSharedCheck_2165_ == 0)
{
v___x_2160_ = v___x_2140_;
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
else
{
lean_inc(v_a_2158_);
lean_dec(v___x_2140_);
v___x_2160_ = lean_box(0);
v_isShared_2161_ = v_isSharedCheck_2165_;
goto v_resetjp_2159_;
}
v_resetjp_2159_:
{
lean_object* v___x_2163_; 
if (v_isShared_2161_ == 0)
{
v___x_2163_ = v___x_2160_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_a_2158_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
}
}
else
{
lean_object* v_a_2166_; lean_object* v___x_2168_; uint8_t v_isShared_2169_; uint8_t v_isSharedCheck_2173_; 
lean_del_object(v___x_2131_);
lean_del_object(v___x_2121_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2166_ = lean_ctor_get(v___x_2137_, 0);
v_isSharedCheck_2173_ = !lean_is_exclusive(v___x_2137_);
if (v_isSharedCheck_2173_ == 0)
{
v___x_2168_ = v___x_2137_;
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
else
{
lean_inc(v_a_2166_);
lean_dec(v___x_2137_);
v___x_2168_ = lean_box(0);
v_isShared_2169_ = v_isSharedCheck_2173_;
goto v_resetjp_2167_;
}
v_resetjp_2167_:
{
lean_object* v___x_2171_; 
if (v_isShared_2169_ == 0)
{
v___x_2171_ = v___x_2168_;
goto v_reusejp_2170_;
}
else
{
lean_object* v_reuseFailAlloc_2172_; 
v_reuseFailAlloc_2172_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2166_);
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
lean_del_object(v___x_2131_);
lean_del_object(v___x_2121_);
v_isEq_1994_ = v___x_1816_;
v___y_1995_ = v___y_2110_;
v___y_1996_ = v___y_2111_;
v___y_1997_ = v___y_2112_;
v___y_1998_ = v___y_2113_;
goto v___jp_1993_;
}
}
}
else
{
lean_dec(v_a_2127_);
lean_dec(v_val_2125_);
lean_del_object(v___x_2121_);
v_isEq_1994_ = v___x_1816_;
v___y_1995_ = v___y_2110_;
v___y_1996_ = v___y_2111_;
v___y_1997_ = v___y_2112_;
v___y_1998_ = v___y_2113_;
goto v___jp_1993_;
}
}
else
{
lean_object* v_a_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2182_; 
lean_dec(v_val_2125_);
lean_del_object(v___x_2121_);
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2175_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2182_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2182_ == 0)
{
v___x_2177_ = v___x_2126_;
v_isShared_2178_ = v_isSharedCheck_2182_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_a_2175_);
lean_dec(v___x_2126_);
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
else
{
lean_dec(v_a_2124_);
lean_del_object(v___x_2121_);
lean_dec(v_snd_2119_);
v_isEq_1994_ = v___x_1816_;
v___y_1995_ = v___y_2110_;
v___y_1996_ = v___y_2111_;
v___y_1997_ = v___y_2112_;
v___y_1998_ = v___y_2113_;
goto v___jp_1993_;
}
}
else
{
lean_object* v_a_2183_; lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2190_; 
lean_del_object(v___x_2121_);
lean_dec(v_snd_2119_);
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2183_ = lean_ctor_get(v___x_2123_, 0);
v_isSharedCheck_2190_ = !lean_is_exclusive(v___x_2123_);
if (v_isSharedCheck_2190_ == 0)
{
v___x_2185_ = v___x_2123_;
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
else
{
lean_inc(v_a_2183_);
lean_dec(v___x_2123_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2190_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2188_; 
if (v_isShared_2186_ == 0)
{
v___x_2188_ = v___x_2185_;
goto v_reusejp_2187_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
v___x_2188_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2187_;
}
v_reusejp_2187_:
{
return v___x_2188_;
}
}
}
}
}
else
{
lean_dec(v_a_2115_);
v_isEq_1994_ = v___x_1869_;
v___y_1995_ = v___y_2110_;
v___y_1996_ = v___y_2111_;
v___y_1997_ = v___y_2112_;
v___y_1998_ = v___y_2113_;
goto v___jp_1993_;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2192_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2114_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2114_);
v___x_2194_ = lean_box(0);
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
v_resetjp_2193_:
{
lean_object* v___x_2197_; 
if (v_isShared_2195_ == 0)
{
v___x_2197_ = v___x_2194_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2198_; 
v_reuseFailAlloc_2198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2198_, 0, v_a_2192_);
v___x_2197_ = v_reuseFailAlloc_2198_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
return v___x_2197_;
}
}
}
}
v___jp_2200_:
{
lean_object* v___x_2205_; 
lean_inc_ref(v___x_1870_);
v___x_2205_ = l_Lean_refutableHasNotBit_x3f(v___x_1870_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2205_) == 0)
{
lean_object* v_a_2206_; 
v_a_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_a_2206_);
lean_dec_ref_known(v___x_2205_, 1);
if (lean_obj_tag(v_a_2206_) == 1)
{
lean_object* v_val_2207_; lean_object* v___x_2209_; uint8_t v_isShared_2210_; uint8_t v_isSharedCheck_2246_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec_ref(v_config_1805_);
v_val_2207_ = lean_ctor_get(v_a_2206_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v_a_2206_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2209_ = v_a_2206_;
v_isShared_2210_ = v_isSharedCheck_2246_;
goto v_resetjp_2208_;
}
else
{
lean_inc(v_val_2207_);
lean_dec(v_a_2206_);
v___x_2209_ = lean_box(0);
v_isShared_2210_ = v_isSharedCheck_2246_;
goto v_resetjp_2208_;
}
v_resetjp_2208_:
{
lean_object* v___x_2211_; 
lean_inc(v_mvarId_1806_);
v___x_2211_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2211_) == 0)
{
lean_object* v_a_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v_a_2212_ = lean_ctor_get(v___x_2211_, 0);
lean_inc(v_a_2212_);
lean_dec_ref_known(v___x_2211_, 1);
v___x_2213_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_2214_ = l_Lean_Meta_mkAbsurd(v_a_2212_, v_val_2207_, v___x_2213_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; lean_object* v___x_2216_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
v___x_2216_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_2215_, v___y_2202_);
if (lean_obj_tag(v___x_2216_) == 0)
{
lean_object* v___x_2217_; lean_object* v___x_2219_; 
lean_dec_ref_known(v___x_2216_, 1);
v___x_2217_ = lean_box(v___x_1816_);
if (v_isShared_2210_ == 0)
{
lean_ctor_set(v___x_2209_, 0, v___x_2217_);
v___x_2219_ = v___x_2209_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2221_; 
v_reuseFailAlloc_2221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2221_, 0, v___x_2217_);
v___x_2219_ = v_reuseFailAlloc_2221_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
lean_object* v___x_2220_; 
v___x_2220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
lean_ctor_set(v___x_2220_, 1, v___x_1841_);
v_a_1823_ = v___x_2220_;
goto v___jp_1822_;
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_del_object(v___x_2209_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_2222_ = lean_ctor_get(v___x_2216_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2216_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2216_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2216_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v___x_2227_; 
if (v_isShared_2225_ == 0)
{
v___x_2227_ = v___x_2224_;
goto v_reusejp_2226_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_a_2222_);
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
lean_del_object(v___x_2209_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2230_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2214_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2214_);
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
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_del_object(v___x_2209_);
lean_dec(v_val_2207_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2238_ = lean_ctor_get(v___x_2211_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2211_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2211_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2211_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2243_; 
if (v_isShared_2241_ == 0)
{
v___x_2243_ = v___x_2240_;
goto v_reusejp_2242_;
}
else
{
lean_object* v_reuseFailAlloc_2244_; 
v_reuseFailAlloc_2244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2244_, 0, v_a_2238_);
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
}
else
{
lean_object* v___x_2247_; 
lean_dec(v_a_2206_);
lean_inc_ref(v___x_1870_);
v___x_2247_ = l_Lean_Meta_matchNe_x3f(v___x_1870_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2247_) == 0)
{
lean_object* v_a_2248_; 
v_a_2248_ = lean_ctor_get(v___x_2247_, 0);
lean_inc(v_a_2248_);
lean_dec_ref_known(v___x_2247_, 1);
if (lean_obj_tag(v_a_2248_) == 1)
{
lean_object* v_val_2249_; lean_object* v___x_2251_; uint8_t v_isShared_2252_; uint8_t v_isSharedCheck_2318_; 
v_val_2249_ = lean_ctor_get(v_a_2248_, 0);
v_isSharedCheck_2318_ = !lean_is_exclusive(v_a_2248_);
if (v_isSharedCheck_2318_ == 0)
{
v___x_2251_ = v_a_2248_;
v_isShared_2252_ = v_isSharedCheck_2318_;
goto v_resetjp_2250_;
}
else
{
lean_inc(v_val_2249_);
lean_dec(v_a_2248_);
v___x_2251_ = lean_box(0);
v_isShared_2252_ = v_isSharedCheck_2318_;
goto v_resetjp_2250_;
}
v_resetjp_2250_:
{
lean_object* v_snd_2253_; lean_object* v_fst_2254_; lean_object* v_snd_2255_; lean_object* v___x_2257_; uint8_t v_isShared_2258_; uint8_t v_isSharedCheck_2317_; 
v_snd_2253_ = lean_ctor_get(v_val_2249_, 1);
lean_inc(v_snd_2253_);
lean_dec(v_val_2249_);
v_fst_2254_ = lean_ctor_get(v_snd_2253_, 0);
v_snd_2255_ = lean_ctor_get(v_snd_2253_, 1);
v_isSharedCheck_2317_ = !lean_is_exclusive(v_snd_2253_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2257_ = v_snd_2253_;
v_isShared_2258_ = v_isSharedCheck_2317_;
goto v_resetjp_2256_;
}
else
{
lean_inc(v_snd_2255_);
lean_inc(v_fst_2254_);
lean_dec(v_snd_2253_);
v___x_2257_ = lean_box(0);
v_isShared_2258_ = v_isSharedCheck_2317_;
goto v_resetjp_2256_;
}
v_resetjp_2256_:
{
lean_object* v___x_2259_; 
lean_inc(v_fst_2254_);
v___x_2259_ = l_Lean_Meta_isExprDefEq(v_fst_2254_, v_snd_2255_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; uint8_t v___x_2261_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2259_, 1);
v___x_2261_ = lean_unbox(v_a_2260_);
lean_dec(v_a_2260_);
if (v___x_2261_ == 0)
{
lean_del_object(v___x_2257_);
lean_dec(v_fst_2254_);
lean_del_object(v___x_2251_);
v___y_2110_ = v___y_2201_;
v___y_2111_ = v___y_2202_;
v___y_2112_ = v___y_2203_;
v___y_2113_ = v___y_2204_;
goto v___jp_2109_;
}
else
{
lean_object* v___x_2262_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec_ref(v_config_1805_);
lean_inc(v_mvarId_1806_);
v___x_2262_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2262_) == 0)
{
lean_object* v_a_2263_; lean_object* v___x_2264_; 
v_a_2263_ = lean_ctor_get(v___x_2262_, 0);
lean_inc(v_a_2263_);
lean_dec_ref_known(v___x_2262_, 1);
v___x_2264_ = l_Lean_Meta_mkEqRefl(v_fst_2254_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2264_) == 0)
{
lean_object* v_a_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
v_a_2265_ = lean_ctor_get(v___x_2264_, 0);
lean_inc(v_a_2265_);
lean_dec_ref_known(v___x_2264_, 1);
v___x_2266_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_2267_ = l_Lean_Meta_mkAbsurd(v_a_2263_, v_a_2265_, v___x_2266_, v___y_2201_, v___y_2202_, v___y_2203_, v___y_2204_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2269_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___x_2269_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_2268_, v___y_2202_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v___x_2270_; lean_object* v___x_2272_; 
lean_dec_ref_known(v___x_2269_, 1);
v___x_2270_ = lean_box(v___x_1816_);
if (v_isShared_2252_ == 0)
{
lean_ctor_set(v___x_2251_, 0, v___x_2270_);
v___x_2272_ = v___x_2251_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2270_);
v___x_2272_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
lean_object* v___x_2274_; 
if (v_isShared_2258_ == 0)
{
lean_ctor_set(v___x_2257_, 1, v___x_1841_);
lean_ctor_set(v___x_2257_, 0, v___x_2272_);
v___x_2274_ = v___x_2257_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2272_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v___x_1841_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
v_a_1823_ = v___x_2274_;
goto v___jp_1822_;
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_del_object(v___x_2257_);
lean_del_object(v___x_2251_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_2277_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2269_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2269_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_del_object(v___x_2257_);
lean_del_object(v___x_2251_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2285_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2267_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2267_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
else
{
lean_object* v_a_2293_; lean_object* v___x_2295_; uint8_t v_isShared_2296_; uint8_t v_isSharedCheck_2300_; 
lean_dec(v_a_2263_);
lean_del_object(v___x_2257_);
lean_del_object(v___x_2251_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2293_ = lean_ctor_get(v___x_2264_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2264_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2264_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2264_);
v___x_2295_ = lean_box(0);
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
v_resetjp_2294_:
{
lean_object* v___x_2298_; 
if (v_isShared_2296_ == 0)
{
v___x_2298_ = v___x_2295_;
goto v_reusejp_2297_;
}
else
{
lean_object* v_reuseFailAlloc_2299_; 
v_reuseFailAlloc_2299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2299_, 0, v_a_2293_);
v___x_2298_ = v_reuseFailAlloc_2299_;
goto v_reusejp_2297_;
}
v_reusejp_2297_:
{
return v___x_2298_;
}
}
}
}
else
{
lean_object* v_a_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2308_; 
lean_del_object(v___x_2257_);
lean_dec(v_fst_2254_);
lean_del_object(v___x_2251_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2301_ = lean_ctor_get(v___x_2262_, 0);
v_isSharedCheck_2308_ = !lean_is_exclusive(v___x_2262_);
if (v_isSharedCheck_2308_ == 0)
{
v___x_2303_ = v___x_2262_;
v_isShared_2304_ = v_isSharedCheck_2308_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_a_2301_);
lean_dec(v___x_2262_);
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
}
else
{
lean_object* v_a_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2316_; 
lean_del_object(v___x_2257_);
lean_dec(v_fst_2254_);
lean_del_object(v___x_2251_);
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2309_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2316_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2316_ == 0)
{
v___x_2311_ = v___x_2259_;
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_a_2309_);
lean_dec(v___x_2259_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2316_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2314_; 
if (v_isShared_2312_ == 0)
{
v___x_2314_ = v___x_2311_;
goto v_reusejp_2313_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_a_2309_);
v___x_2314_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2313_;
}
v_reusejp_2313_:
{
return v___x_2314_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2248_);
v___y_2110_ = v___y_2201_;
v___y_2111_ = v___y_2202_;
v___y_2112_ = v___y_2203_;
v___y_2113_ = v___y_2204_;
goto v___jp_2109_;
}
}
else
{
lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2326_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2319_ = lean_ctor_get(v___x_2247_, 0);
v_isSharedCheck_2326_ = !lean_is_exclusive(v___x_2247_);
if (v_isSharedCheck_2326_ == 0)
{
v___x_2321_ = v___x_2247_;
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_dec(v___x_2247_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2326_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2322_ == 0)
{
v___x_2324_ = v___x_2321_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2325_; 
v_reuseFailAlloc_2325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2325_, 0, v_a_2319_);
v___x_2324_ = v_reuseFailAlloc_2325_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
return v___x_2324_;
}
}
}
}
}
else
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2334_; 
lean_dec_ref(v___x_1870_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2327_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2334_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2334_ == 0)
{
v___x_2329_ = v___x_2205_;
v_isShared_2330_ = v_isSharedCheck_2334_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2205_);
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
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_1831_ = v___x_1842_;
goto v___jp_1830_;
}
v___jp_1843_:
{
uint8_t v_emptyType_1850_; 
v_emptyType_1850_ = lean_ctor_get_uint8(v_config_1805_, sizeof(void*)*1 + 1);
if (v_emptyType_1850_ == 0)
{
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_1831_ = v___x_1842_;
goto v___jp_1830_;
}
else
{
if (v___y_1845_ == 0)
{
if (v___y_1844_ == 0)
{
lean_object* v_searchFuel_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v_searchFuel_1851_ = lean_ctor_get(v_config_1805_, 0);
v___x_1852_ = l_Lean_LocalDecl_fvarId(v_val_1837_);
lean_dec(v_val_1837_);
lean_inc(v_searchFuel_1851_);
lean_inc(v_mvarId_1806_);
v___x_1853_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1806_, v___x_1852_, v_searchFuel_1851_, v___y_1846_, v___y_1847_, v___y_1848_, v___y_1849_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; uint8_t v___x_1855_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = lean_unbox(v_a_1854_);
lean_dec(v_a_1854_);
if (v___x_1855_ == 0)
{
lean_del_object(v___x_1839_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_1831_ = v___x_1842_;
goto v___jp_1830_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1858_; 
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v___x_1856_ = lean_box(v___x_1816_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1856_);
v___x_1858_ = v___x_1839_;
goto v_reusejp_1857_;
}
else
{
lean_object* v_reuseFailAlloc_1860_; 
v_reuseFailAlloc_1860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1860_, 0, v___x_1856_);
v___x_1858_ = v_reuseFailAlloc_1860_;
goto v_reusejp_1857_;
}
v_reusejp_1857_:
{
lean_object* v___x_1859_; 
v___x_1859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1859_, 0, v___x_1858_);
lean_ctor_set(v___x_1859_, 1, v___x_1841_);
v_a_1823_ = v___x_1859_;
goto v___jp_1822_;
}
}
}
else
{
lean_object* v_a_1861_; lean_object* v___x_1863_; uint8_t v_isShared_1864_; uint8_t v_isSharedCheck_1868_; 
lean_del_object(v___x_1839_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_1861_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1868_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1868_ == 0)
{
v___x_1863_ = v___x_1853_;
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
else
{
lean_inc(v_a_1861_);
lean_dec(v___x_1853_);
v___x_1863_ = lean_box(0);
v_isShared_1864_ = v_isSharedCheck_1868_;
goto v_resetjp_1862_;
}
v_resetjp_1862_:
{
lean_object* v___x_1866_; 
if (v_isShared_1864_ == 0)
{
v___x_1866_ = v___x_1863_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1867_; 
v_reuseFailAlloc_1867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1867_, 0, v_a_1861_);
v___x_1866_ = v_reuseFailAlloc_1867_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
return v___x_1866_;
}
}
}
}
else
{
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_1831_ = v___x_1842_;
goto v___jp_1830_;
}
}
else
{
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_1831_ = v___x_1842_;
goto v___jp_1830_;
}
}
}
}
}
v___jp_1822_:
{
lean_object* v___x_1824_; lean_object* v___x_1826_; 
v___x_1824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_a_1823_);
if (v_isShared_1821_ == 0)
{
lean_ctor_set(v___x_1820_, 0, v___x_1824_);
v___x_1826_ = v___x_1820_;
goto v_reusejp_1825_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v___x_1824_);
lean_ctor_set(v_reuseFailAlloc_1828_, 1, v_snd_1818_);
v___x_1826_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1825_;
}
v_reusejp_1825_:
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
return v___x_1827_;
}
}
v___jp_1830_:
{
lean_object* v___x_1832_; size_t v___x_1833_; size_t v___x_1834_; 
v___x_1832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1832_, 0, v___x_1829_);
lean_ctor_set(v___x_1832_, 1, v_a_1831_);
v___x_1833_ = ((size_t)1ULL);
v___x_1834_ = lean_usize_add(v_i_1809_, v___x_1833_);
v_i_1809_ = v___x_1834_;
v_b_1810_ = v___x_1832_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2401_, lean_object* v_mvarId_2402_, lean_object* v_as_2403_, lean_object* v_sz_2404_, lean_object* v_i_2405_, lean_object* v_b_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
size_t v_sz_boxed_2412_; size_t v_i_boxed_2413_; lean_object* v_res_2414_; 
v_sz_boxed_2412_ = lean_unbox_usize(v_sz_2404_);
lean_dec(v_sz_2404_);
v_i_boxed_2413_ = lean_unbox_usize(v_i_2405_);
lean_dec(v_i_2405_);
v_res_2414_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2401_, v_mvarId_2402_, v_as_2403_, v_sz_boxed_2412_, v_i_boxed_2413_, v_b_2406_, v___y_2407_, v___y_2408_, v___y_2409_, v___y_2410_);
lean_dec(v___y_2410_);
lean_dec_ref(v___y_2409_);
lean_dec(v___y_2408_);
lean_dec_ref(v___y_2407_);
lean_dec_ref(v_as_2403_);
return v_res_2414_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2415_, lean_object* v_mvarId_2416_, lean_object* v_as_2417_, size_t v_sz_2418_, size_t v_i_2419_, lean_object* v_b_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
uint8_t v___x_2426_; 
v___x_2426_ = lean_usize_dec_lt(v_i_2419_, v_sz_2418_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; 
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v___x_2427_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2427_, 0, v_b_2420_);
return v___x_2427_;
}
else
{
lean_object* v_snd_2428_; lean_object* v___x_2430_; uint8_t v_isShared_2431_; uint8_t v_isSharedCheck_3009_; 
v_snd_2428_ = lean_ctor_get(v_b_2420_, 1);
v_isSharedCheck_3009_ = !lean_is_exclusive(v_b_2420_);
if (v_isSharedCheck_3009_ == 0)
{
lean_object* v_unused_3010_; 
v_unused_3010_ = lean_ctor_get(v_b_2420_, 0);
lean_dec(v_unused_3010_);
v___x_2430_ = v_b_2420_;
v_isShared_2431_ = v_isSharedCheck_3009_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_snd_2428_);
lean_dec(v_b_2420_);
v___x_2430_ = lean_box(0);
v_isShared_2431_ = v_isSharedCheck_3009_;
goto v_resetjp_2429_;
}
v_resetjp_2429_:
{
lean_object* v_a_2433_; lean_object* v___x_2439_; lean_object* v_a_2441_; lean_object* v_a_2446_; 
v___x_2439_ = lean_box(0);
v_a_2446_ = lean_array_uget(v_as_2417_, v_i_2419_);
if (lean_obj_tag(v_a_2446_) == 0)
{
lean_del_object(v___x_2430_);
v_a_2441_ = v_snd_2428_;
goto v___jp_2440_;
}
else
{
lean_object* v_val_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_3008_; 
v_val_2447_ = lean_ctor_get(v_a_2446_, 0);
v_isSharedCheck_3008_ = !lean_is_exclusive(v_a_2446_);
if (v_isSharedCheck_3008_ == 0)
{
v___x_2449_ = v_a_2446_;
v_isShared_2450_ = v_isSharedCheck_3008_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_val_2447_);
lean_dec(v_a_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_3008_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2451_; lean_object* v___x_2452_; uint8_t v___y_2454_; uint8_t v___y_2455_; lean_object* v___y_2456_; lean_object* v___y_2457_; lean_object* v___y_2458_; lean_object* v___y_2459_; uint8_t v___x_2479_; 
v___x_2451_ = lean_box(0);
v___x_2452_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2479_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2447_);
if (v___x_2479_ == 0)
{
lean_object* v___x_2480_; uint8_t v___y_2482_; uint8_t v___y_2483_; lean_object* v___y_2484_; lean_object* v___y_2485_; lean_object* v___y_2486_; lean_object* v___y_2487_; lean_object* v___y_2505_; uint8_t v___y_2506_; lean_object* v___y_2507_; lean_object* v___y_2508_; uint8_t v___y_2509_; lean_object* v___y_2510_; lean_object* v_a_2511_; lean_object* v___y_2517_; uint8_t v___y_2518_; lean_object* v___y_2519_; lean_object* v___y_2520_; lean_object* v___y_2521_; uint8_t v___y_2522_; lean_object* v___y_2523_; lean_object* v___y_2524_; uint8_t v___y_2561_; uint8_t v_isHEq_2562_; lean_object* v___y_2563_; lean_object* v___y_2564_; lean_object* v___y_2565_; lean_object* v___y_2566_; uint8_t v_isEq_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; lean_object* v___y_2608_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; lean_object* v___y_2723_; lean_object* v___y_2811_; lean_object* v___y_2812_; lean_object* v___y_2813_; lean_object* v___y_2814_; lean_object* v___x_2945_; 
v___x_2480_ = l_Lean_LocalDecl_type(v_val_2447_);
lean_inc_ref(v___x_2480_);
v___x_2945_ = l_Lean_Meta_matchNot_x3f(v___x_2480_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2945_) == 0)
{
lean_object* v_a_2946_; 
v_a_2946_ = lean_ctor_get(v___x_2945_, 0);
lean_inc(v_a_2946_);
lean_dec_ref_known(v___x_2945_, 1);
if (lean_obj_tag(v_a_2946_) == 1)
{
lean_object* v_val_2947_; lean_object* v___x_2948_; 
v_val_2947_ = lean_ctor_get(v_a_2946_, 0);
lean_inc(v_val_2947_);
lean_dec_ref_known(v_a_2946_, 1);
v___x_2948_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2947_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2948_) == 0)
{
lean_object* v_a_2949_; 
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
lean_inc(v_a_2949_);
lean_dec_ref_known(v___x_2948_, 1);
if (lean_obj_tag(v_a_2949_) == 1)
{
lean_object* v_val_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2991_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec_ref(v_config_2415_);
v_val_2950_ = lean_ctor_get(v_a_2949_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v_a_2949_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2952_ = v_a_2949_;
v_isShared_2953_ = v_isSharedCheck_2991_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_val_2950_);
lean_dec(v_a_2949_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2991_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2954_; 
lean_inc(v_mvarId_2416_);
v___x_2954_ = l_Lean_MVarId_getType(v_mvarId_2416_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2954_) == 0)
{
lean_object* v_a_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; 
v_a_2955_ = lean_ctor_get(v___x_2954_, 0);
lean_inc(v_a_2955_);
lean_dec_ref_known(v___x_2954_, 1);
v___x_2956_ = l_Lean_LocalDecl_toExpr(v_val_2447_);
v___x_2957_ = l_Lean_mkFVar(v_val_2950_);
v___x_2958_ = l_Lean_Expr_app___override(v___x_2956_, v___x_2957_);
v___x_2959_ = l_Lean_Meta_mkFalseElim(v_a_2955_, v___x_2958_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; lean_object* v___x_2961_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
v___x_2961_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2416_, v_a_2960_, v___y_2422_);
if (lean_obj_tag(v___x_2961_) == 0)
{
lean_object* v___x_2962_; lean_object* v___x_2964_; 
lean_dec_ref_known(v___x_2961_, 1);
v___x_2962_ = lean_box(v___x_2426_);
if (v_isShared_2953_ == 0)
{
lean_ctor_set(v___x_2952_, 0, v___x_2962_);
v___x_2964_ = v___x_2952_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v___x_2962_);
v___x_2964_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
lean_object* v___x_2965_; 
v___x_2965_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2965_, 0, v___x_2964_);
lean_ctor_set(v___x_2965_, 1, v___x_2451_);
v_a_2433_ = v___x_2965_;
goto v___jp_2432_;
}
}
else
{
lean_object* v_a_2967_; lean_object* v___x_2969_; uint8_t v_isShared_2970_; uint8_t v_isSharedCheck_2974_; 
lean_del_object(v___x_2952_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
v_a_2967_ = lean_ctor_get(v___x_2961_, 0);
v_isSharedCheck_2974_ = !lean_is_exclusive(v___x_2961_);
if (v_isSharedCheck_2974_ == 0)
{
v___x_2969_ = v___x_2961_;
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
else
{
lean_inc(v_a_2967_);
lean_dec(v___x_2961_);
v___x_2969_ = lean_box(0);
v_isShared_2970_ = v_isSharedCheck_2974_;
goto v_resetjp_2968_;
}
v_resetjp_2968_:
{
lean_object* v___x_2972_; 
if (v_isShared_2970_ == 0)
{
v___x_2972_ = v___x_2969_;
goto v_reusejp_2971_;
}
else
{
lean_object* v_reuseFailAlloc_2973_; 
v_reuseFailAlloc_2973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2973_, 0, v_a_2967_);
v___x_2972_ = v_reuseFailAlloc_2973_;
goto v_reusejp_2971_;
}
v_reusejp_2971_:
{
return v___x_2972_;
}
}
}
}
else
{
lean_object* v_a_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_2982_; 
lean_del_object(v___x_2952_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2975_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_2982_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_2982_ == 0)
{
v___x_2977_ = v___x_2959_;
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_a_2975_);
lean_dec(v___x_2959_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_2982_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2980_; 
if (v_isShared_2978_ == 0)
{
v___x_2980_ = v___x_2977_;
goto v_reusejp_2979_;
}
else
{
lean_object* v_reuseFailAlloc_2981_; 
v_reuseFailAlloc_2981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2981_, 0, v_a_2975_);
v___x_2980_ = v_reuseFailAlloc_2981_;
goto v_reusejp_2979_;
}
v_reusejp_2979_:
{
return v___x_2980_;
}
}
}
}
else
{
lean_object* v_a_2983_; lean_object* v___x_2985_; uint8_t v_isShared_2986_; uint8_t v_isSharedCheck_2990_; 
lean_del_object(v___x_2952_);
lean_dec(v_val_2950_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2983_ = lean_ctor_get(v___x_2954_, 0);
v_isSharedCheck_2990_ = !lean_is_exclusive(v___x_2954_);
if (v_isSharedCheck_2990_ == 0)
{
v___x_2985_ = v___x_2954_;
v_isShared_2986_ = v_isSharedCheck_2990_;
goto v_resetjp_2984_;
}
else
{
lean_inc(v_a_2983_);
lean_dec(v___x_2954_);
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
}
}
else
{
lean_dec(v_a_2949_);
v___y_2811_ = v___y_2421_;
v___y_2812_ = v___y_2422_;
v___y_2813_ = v___y_2423_;
v___y_2814_ = v___y_2424_;
goto v___jp_2810_;
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2992_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2948_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2948_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_dec(v_a_2946_);
v___y_2811_ = v___y_2421_;
v___y_2812_ = v___y_2422_;
v___y_2813_ = v___y_2423_;
v___y_2814_ = v___y_2424_;
goto v___jp_2810_;
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_3000_ = lean_ctor_get(v___x_2945_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2945_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2945_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2945_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
v___jp_2481_:
{
uint8_t v_genDiseq_2488_; 
v_genDiseq_2488_ = lean_ctor_get_uint8(v_config_2415_, sizeof(void*)*1 + 2);
if (v_genDiseq_2488_ == 0)
{
lean_dec_ref(v___x_2480_);
v___y_2454_ = v___y_2482_;
v___y_2455_ = v___y_2483_;
v___y_2456_ = v___y_2484_;
v___y_2457_ = v___y_2485_;
v___y_2458_ = v___y_2486_;
v___y_2459_ = v___y_2487_;
goto v___jp_2453_;
}
else
{
uint8_t v___x_2489_; 
v___x_2489_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2480_);
if (v___x_2489_ == 0)
{
v___y_2454_ = v___y_2482_;
v___y_2455_ = v___y_2483_;
v___y_2456_ = v___y_2484_;
v___y_2457_ = v___y_2485_;
v___y_2458_ = v___y_2486_;
v___y_2459_ = v___y_2487_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2490_; 
lean_inc(v_val_2447_);
lean_inc(v_mvarId_2416_);
v___x_2490_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2416_, v_val_2447_, v___y_2484_, v___y_2485_, v___y_2486_, v___y_2487_);
if (lean_obj_tag(v___x_2490_) == 0)
{
lean_object* v_a_2491_; uint8_t v___x_2492_; 
v_a_2491_ = lean_ctor_get(v___x_2490_, 0);
lean_inc(v_a_2491_);
lean_dec_ref_known(v___x_2490_, 1);
v___x_2492_ = lean_unbox(v_a_2491_);
lean_dec(v_a_2491_);
if (v___x_2492_ == 0)
{
v___y_2454_ = v___y_2482_;
v___y_2455_ = v___y_2483_;
v___y_2456_ = v___y_2484_;
v___y_2457_ = v___y_2485_;
v___y_2458_ = v___y_2486_;
v___y_2459_ = v___y_2487_;
goto v___jp_2453_;
}
else
{
lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; 
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v___x_2493_ = lean_box(v___x_2426_);
v___x_2494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2494_, 0, v___x_2493_);
v___x_2495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2494_);
lean_ctor_set(v___x_2495_, 1, v___x_2451_);
v_a_2433_ = v___x_2495_;
goto v___jp_2432_;
}
}
else
{
lean_object* v_a_2496_; lean_object* v___x_2498_; uint8_t v_isShared_2499_; uint8_t v_isSharedCheck_2503_; 
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2496_ = lean_ctor_get(v___x_2490_, 0);
v_isSharedCheck_2503_ = !lean_is_exclusive(v___x_2490_);
if (v_isSharedCheck_2503_ == 0)
{
v___x_2498_ = v___x_2490_;
v_isShared_2499_ = v_isSharedCheck_2503_;
goto v_resetjp_2497_;
}
else
{
lean_inc(v_a_2496_);
lean_dec(v___x_2490_);
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
v___jp_2504_:
{
uint8_t v___x_2512_; 
v___x_2512_ = l_Lean_Exception_isInterrupt(v_a_2511_);
if (v___x_2512_ == 0)
{
uint8_t v___x_2513_; 
lean_inc_ref(v_a_2511_);
v___x_2513_ = l_Lean_Exception_isRuntime(v_a_2511_);
if (v___x_2513_ == 0)
{
lean_dec_ref(v_a_2511_);
v___y_2482_ = v___y_2506_;
v___y_2483_ = v___y_2509_;
v___y_2484_ = v___y_2508_;
v___y_2485_ = v___y_2507_;
v___y_2486_ = v___y_2505_;
v___y_2487_ = v___y_2510_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2514_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v___x_2514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2514_, 0, v_a_2511_);
return v___x_2514_;
}
}
else
{
lean_object* v___x_2515_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v___x_2515_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2515_, 0, v_a_2511_);
return v___x_2515_;
}
}
v___jp_2516_:
{
if (lean_obj_tag(v___y_2524_) == 0)
{
lean_object* v_a_2525_; lean_object* v___x_2526_; uint8_t v___x_2527_; 
v_a_2525_ = lean_ctor_get(v___y_2524_, 0);
lean_inc(v_a_2525_);
lean_dec_ref_known(v___y_2524_, 1);
v___x_2526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2527_ = l_Lean_Expr_isConstOf(v_a_2525_, v___x_2526_);
lean_dec(v_a_2525_);
if (v___x_2527_ == 0)
{
lean_dec_ref(v___y_2520_);
v___y_2482_ = v___y_2518_;
v___y_2483_ = v___y_2522_;
v___y_2484_ = v___y_2521_;
v___y_2485_ = v___y_2519_;
v___y_2486_ = v___y_2517_;
v___y_2487_ = v___y_2523_;
goto v___jp_2481_;
}
else
{
lean_object* v___x_2528_; 
lean_inc_ref(v___y_2520_);
v___x_2528_ = l_Lean_Meta_mkEqRefl(v___y_2520_, v___y_2521_, v___y_2519_, v___y_2517_, v___y_2523_);
if (lean_obj_tag(v___x_2528_) == 0)
{
lean_object* v_a_2529_; lean_object* v___x_2530_; lean_object* v_dummy_2531_; lean_object* v_nargs_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; 
v_a_2529_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2529_);
lean_dec_ref_known(v___x_2528_, 1);
v___x_2530_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2531_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2532_ = l_Lean_Expr_getAppNumArgs(v___y_2520_);
lean_inc(v_nargs_2532_);
v___x_2533_ = lean_mk_array(v_nargs_2532_, v_dummy_2531_);
v___x_2534_ = lean_unsigned_to_nat(1u);
v___x_2535_ = lean_nat_sub(v_nargs_2532_, v___x_2534_);
lean_dec(v_nargs_2532_);
v___x_2536_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2520_, v___x_2533_, v___x_2535_);
v___x_2537_ = lean_array_push(v___x_2536_, v_a_2529_);
v___x_2538_ = l_Lean_mkAppN(v___x_2530_, v___x_2537_);
lean_dec_ref(v___x_2537_);
lean_inc(v_mvarId_2416_);
v___x_2539_ = l_Lean_MVarId_getType(v_mvarId_2416_, v___y_2521_, v___y_2519_, v___y_2517_, v___y_2523_);
if (lean_obj_tag(v___x_2539_) == 0)
{
lean_object* v_a_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_a_2540_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2539_, 1);
lean_inc(v_val_2447_);
v___x_2541_ = l_Lean_LocalDecl_toExpr(v_val_2447_);
v___x_2542_ = l_Lean_Meta_mkAbsurd(v_a_2540_, v___x_2541_, v___x_2538_, v___y_2521_, v___y_2519_, v___y_2517_, v___y_2523_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_object* v_a_2543_; lean_object* v___x_2544_; 
v_a_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2543_);
lean_dec_ref_known(v___x_2542_, 1);
lean_inc(v_mvarId_2416_);
v___x_2544_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2416_, v_a_2543_, v___y_2519_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2553_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2553_ == 0)
{
lean_object* v_unused_2554_; 
v_unused_2554_ = lean_ctor_get(v___x_2544_, 0);
lean_dec(v_unused_2554_);
v___x_2546_ = v___x_2544_;
v_isShared_2547_ = v_isSharedCheck_2553_;
goto v_resetjp_2545_;
}
else
{
lean_dec(v___x_2544_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2553_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2548_ = lean_box(v___x_2426_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set_tag(v___x_2546_, 1);
lean_ctor_set(v___x_2546_, 0, v___x_2548_);
v___x_2550_ = v___x_2546_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
lean_object* v___x_2551_; 
v___x_2551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2550_);
lean_ctor_set(v___x_2551_, 1, v___x_2451_);
v_a_2433_ = v___x_2551_;
goto v___jp_2432_;
}
}
}
else
{
lean_object* v_a_2555_; 
v_a_2555_ = lean_ctor_get(v___x_2544_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2544_, 1);
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2518_;
v___y_2507_ = v___y_2519_;
v___y_2508_ = v___y_2521_;
v___y_2509_ = v___y_2522_;
v___y_2510_ = v___y_2523_;
v_a_2511_ = v_a_2555_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2556_; 
v_a_2556_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2542_, 1);
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2518_;
v___y_2507_ = v___y_2519_;
v___y_2508_ = v___y_2521_;
v___y_2509_ = v___y_2522_;
v___y_2510_ = v___y_2523_;
v_a_2511_ = v_a_2556_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2557_; 
lean_dec_ref(v___x_2538_);
v_a_2557_ = lean_ctor_get(v___x_2539_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2539_, 1);
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2518_;
v___y_2507_ = v___y_2519_;
v___y_2508_ = v___y_2521_;
v___y_2509_ = v___y_2522_;
v___y_2510_ = v___y_2523_;
v_a_2511_ = v_a_2557_;
goto v___jp_2504_;
}
}
else
{
lean_object* v_a_2558_; 
lean_dec_ref(v___y_2520_);
v_a_2558_ = lean_ctor_get(v___x_2528_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v___x_2528_, 1);
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2518_;
v___y_2507_ = v___y_2519_;
v___y_2508_ = v___y_2521_;
v___y_2509_ = v___y_2522_;
v___y_2510_ = v___y_2523_;
v_a_2511_ = v_a_2558_;
goto v___jp_2504_;
}
}
}
else
{
lean_object* v_a_2559_; 
lean_dec_ref(v___y_2520_);
v_a_2559_ = lean_ctor_get(v___y_2524_, 0);
lean_inc(v_a_2559_);
lean_dec_ref_known(v___y_2524_, 1);
v___y_2505_ = v___y_2517_;
v___y_2506_ = v___y_2518_;
v___y_2507_ = v___y_2519_;
v___y_2508_ = v___y_2521_;
v___y_2509_ = v___y_2522_;
v___y_2510_ = v___y_2523_;
v_a_2511_ = v_a_2559_;
goto v___jp_2504_;
}
}
v___jp_2560_:
{
uint8_t v_useDecide_2567_; 
v_useDecide_2567_ = lean_ctor_get_uint8(v_config_2415_, sizeof(void*)*1);
if (v_useDecide_2567_ == 0)
{
v___y_2482_ = v___y_2561_;
v___y_2483_ = v_isHEq_2562_;
v___y_2484_ = v___y_2563_;
v___y_2485_ = v___y_2564_;
v___y_2486_ = v___y_2565_;
v___y_2487_ = v___y_2566_;
goto v___jp_2481_;
}
else
{
uint8_t v___x_2568_; 
v___x_2568_ = l_Lean_Expr_hasFVar(v___x_2480_);
if (v___x_2568_ == 0)
{
lean_object* v___x_2569_; 
lean_inc_ref(v___x_2480_);
v___x_2569_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2480_, v___y_2564_);
if (lean_obj_tag(v___x_2569_) == 0)
{
lean_object* v_a_2570_; uint8_t v___x_2571_; 
v_a_2570_ = lean_ctor_get(v___x_2569_, 0);
lean_inc(v_a_2570_);
lean_dec_ref_known(v___x_2569_, 1);
v___x_2571_ = l_Lean_Expr_hasMVar(v_a_2570_);
if (v___x_2571_ == 0)
{
uint8_t v___x_2572_; 
v___x_2572_ = l_Lean_Expr_hasFVar(v_a_2570_);
lean_dec(v_a_2570_);
if (v___x_2572_ == 0)
{
lean_object* v___x_2573_; 
lean_inc_ref(v___x_2480_);
v___x_2573_ = l_Lean_Meta_mkDecide(v___x_2480_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2575_; uint8_t v_transparency_2576_; uint8_t v___x_2577_; uint8_t v___x_2578_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2575_ = l_Lean_Meta_Context_config(v___y_2563_);
v_transparency_2576_ = lean_ctor_get_uint8(v___x_2575_, 9);
lean_dec_ref(v___x_2575_);
v___x_2577_ = 1;
v___x_2578_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v_keyedConfig_2579_; uint8_t v_trackZetaDelta_2580_; lean_object* v_zetaDeltaSet_2581_; lean_object* v_lctx_2582_; lean_object* v_localInstances_2583_; lean_object* v_defEqCtx_x3f_2584_; lean_object* v_synthPendingDepth_2585_; lean_object* v_customCanUnfoldPredicate_x3f_2586_; uint8_t v_univApprox_2587_; uint8_t v_inTypeClassResolution_2588_; uint8_t v_cacheInferType_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v_keyedConfig_2579_ = lean_ctor_get(v___y_2563_, 0);
v_trackZetaDelta_2580_ = lean_ctor_get_uint8(v___y_2563_, sizeof(void*)*7);
v_zetaDeltaSet_2581_ = lean_ctor_get(v___y_2563_, 1);
v_lctx_2582_ = lean_ctor_get(v___y_2563_, 2);
v_localInstances_2583_ = lean_ctor_get(v___y_2563_, 3);
v_defEqCtx_x3f_2584_ = lean_ctor_get(v___y_2563_, 4);
v_synthPendingDepth_2585_ = lean_ctor_get(v___y_2563_, 5);
v_customCanUnfoldPredicate_x3f_2586_ = lean_ctor_get(v___y_2563_, 6);
v_univApprox_2587_ = lean_ctor_get_uint8(v___y_2563_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2588_ = lean_ctor_get_uint8(v___y_2563_, sizeof(void*)*7 + 2);
v_cacheInferType_2589_ = lean_ctor_get_uint8(v___y_2563_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2579_);
v___x_2590_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2577_, v_keyedConfig_2579_);
lean_inc(v_customCanUnfoldPredicate_x3f_2586_);
lean_inc(v_synthPendingDepth_2585_);
lean_inc(v_defEqCtx_x3f_2584_);
lean_inc_ref(v_localInstances_2583_);
lean_inc_ref(v_lctx_2582_);
lean_inc(v_zetaDeltaSet_2581_);
v___x_2591_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2591_, 0, v___x_2590_);
lean_ctor_set(v___x_2591_, 1, v_zetaDeltaSet_2581_);
lean_ctor_set(v___x_2591_, 2, v_lctx_2582_);
lean_ctor_set(v___x_2591_, 3, v_localInstances_2583_);
lean_ctor_set(v___x_2591_, 4, v_defEqCtx_x3f_2584_);
lean_ctor_set(v___x_2591_, 5, v_synthPendingDepth_2585_);
lean_ctor_set(v___x_2591_, 6, v_customCanUnfoldPredicate_x3f_2586_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*7, v_trackZetaDelta_2580_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*7 + 1, v_univApprox_2587_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2588_);
lean_ctor_set_uint8(v___x_2591_, sizeof(void*)*7 + 3, v_cacheInferType_2589_);
lean_inc(v___y_2566_);
lean_inc_ref(v___y_2565_);
lean_inc(v___y_2564_);
lean_inc(v_a_2574_);
v___x_2592_ = lean_whnf(v_a_2574_, v___x_2591_, v___y_2564_, v___y_2565_, v___y_2566_);
v___y_2517_ = v___y_2565_;
v___y_2518_ = v___y_2561_;
v___y_2519_ = v___y_2564_;
v___y_2520_ = v_a_2574_;
v___y_2521_ = v___y_2563_;
v___y_2522_ = v_isHEq_2562_;
v___y_2523_ = v___y_2566_;
v___y_2524_ = v___x_2592_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2593_; 
lean_inc(v___y_2566_);
lean_inc_ref(v___y_2565_);
lean_inc(v___y_2564_);
lean_inc_ref(v___y_2563_);
lean_inc(v_a_2574_);
v___x_2593_ = lean_whnf(v_a_2574_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
v___y_2517_ = v___y_2565_;
v___y_2518_ = v___y_2561_;
v___y_2519_ = v___y_2564_;
v___y_2520_ = v_a_2574_;
v___y_2521_ = v___y_2563_;
v___y_2522_ = v_isHEq_2562_;
v___y_2523_ = v___y_2566_;
v___y_2524_ = v___x_2593_;
goto v___jp_2516_;
}
}
else
{
lean_object* v_a_2594_; 
v_a_2594_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2573_, 1);
v___y_2505_ = v___y_2565_;
v___y_2506_ = v___y_2561_;
v___y_2507_ = v___y_2564_;
v___y_2508_ = v___y_2563_;
v___y_2509_ = v_isHEq_2562_;
v___y_2510_ = v___y_2566_;
v_a_2511_ = v_a_2594_;
goto v___jp_2504_;
}
}
else
{
v___y_2482_ = v___y_2561_;
v___y_2483_ = v_isHEq_2562_;
v___y_2484_ = v___y_2563_;
v___y_2485_ = v___y_2564_;
v___y_2486_ = v___y_2565_;
v___y_2487_ = v___y_2566_;
goto v___jp_2481_;
}
}
else
{
lean_dec(v_a_2570_);
v___y_2482_ = v___y_2561_;
v___y_2483_ = v_isHEq_2562_;
v___y_2484_ = v___y_2563_;
v___y_2485_ = v___y_2564_;
v___y_2486_ = v___y_2565_;
v___y_2487_ = v___y_2566_;
goto v___jp_2481_;
}
}
else
{
lean_object* v_a_2595_; lean_object* v___x_2597_; uint8_t v_isShared_2598_; uint8_t v_isSharedCheck_2602_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2595_ = lean_ctor_get(v___x_2569_, 0);
v_isSharedCheck_2602_ = !lean_is_exclusive(v___x_2569_);
if (v_isSharedCheck_2602_ == 0)
{
v___x_2597_ = v___x_2569_;
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
else
{
lean_inc(v_a_2595_);
lean_dec(v___x_2569_);
v___x_2597_ = lean_box(0);
v_isShared_2598_ = v_isSharedCheck_2602_;
goto v_resetjp_2596_;
}
v_resetjp_2596_:
{
lean_object* v___x_2600_; 
if (v_isShared_2598_ == 0)
{
v___x_2600_ = v___x_2597_;
goto v_reusejp_2599_;
}
else
{
lean_object* v_reuseFailAlloc_2601_; 
v_reuseFailAlloc_2601_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_a_2595_);
v___x_2600_ = v_reuseFailAlloc_2601_;
goto v_reusejp_2599_;
}
v_reusejp_2599_:
{
return v___x_2600_;
}
}
}
}
else
{
v___y_2482_ = v___y_2561_;
v___y_2483_ = v_isHEq_2562_;
v___y_2484_ = v___y_2563_;
v___y_2485_ = v___y_2564_;
v___y_2486_ = v___y_2565_;
v___y_2487_ = v___y_2566_;
goto v___jp_2481_;
}
}
}
v___jp_2603_:
{
lean_object* v___x_2609_; 
lean_inc_ref(v___x_2480_);
v___x_2609_ = l_Lean_Meta_matchHEq_x3f(v___x_2480_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref_known(v___x_2609_, 1);
if (lean_obj_tag(v_a_2610_) == 1)
{
lean_object* v_val_2611_; lean_object* v_snd_2612_; lean_object* v_snd_2613_; lean_object* v_fst_2614_; lean_object* v_fst_2615_; lean_object* v_fst_2616_; lean_object* v_snd_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2710_; 
v_val_2611_ = lean_ctor_get(v_a_2610_, 0);
lean_inc(v_val_2611_);
lean_dec_ref_known(v_a_2610_, 1);
v_snd_2612_ = lean_ctor_get(v_val_2611_, 1);
lean_inc(v_snd_2612_);
v_snd_2613_ = lean_ctor_get(v_snd_2612_, 1);
lean_inc(v_snd_2613_);
v_fst_2614_ = lean_ctor_get(v_val_2611_, 0);
lean_inc(v_fst_2614_);
lean_dec(v_val_2611_);
v_fst_2615_ = lean_ctor_get(v_snd_2612_, 0);
lean_inc(v_fst_2615_);
lean_dec(v_snd_2612_);
v_fst_2616_ = lean_ctor_get(v_snd_2613_, 0);
v_snd_2617_ = lean_ctor_get(v_snd_2613_, 1);
v_isSharedCheck_2710_ = !lean_is_exclusive(v_snd_2613_);
if (v_isSharedCheck_2710_ == 0)
{
v___x_2619_ = v_snd_2613_;
v_isShared_2620_ = v_isSharedCheck_2710_;
goto v_resetjp_2618_;
}
else
{
lean_inc(v_snd_2617_);
lean_inc(v_fst_2616_);
lean_dec(v_snd_2613_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2710_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; 
v___x_2621_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2615_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2621_) == 0)
{
lean_object* v_a_2622_; 
v_a_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_a_2622_);
lean_dec_ref_known(v___x_2621_, 1);
if (lean_obj_tag(v_a_2622_) == 1)
{
lean_object* v_val_2623_; lean_object* v___x_2624_; 
v_val_2623_ = lean_ctor_get(v_a_2622_, 0);
lean_inc(v_val_2623_);
lean_dec_ref_known(v_a_2622_, 1);
v___x_2624_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2617_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
if (lean_obj_tag(v_a_2625_) == 1)
{
lean_object* v_toConstantVal_2626_; lean_object* v_val_2627_; lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2693_; 
v_toConstantVal_2626_ = lean_ctor_get(v_val_2623_, 0);
lean_inc_ref(v_toConstantVal_2626_);
lean_dec(v_val_2623_);
v_val_2627_ = lean_ctor_get(v_a_2625_, 0);
v_isSharedCheck_2693_ = !lean_is_exclusive(v_a_2625_);
if (v_isSharedCheck_2693_ == 0)
{
v___x_2629_ = v_a_2625_;
v_isShared_2630_ = v_isSharedCheck_2693_;
goto v_resetjp_2628_;
}
else
{
lean_inc(v_val_2627_);
lean_dec(v_a_2625_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2693_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v_toConstantVal_2631_; lean_object* v_name_2632_; lean_object* v_name_2633_; uint8_t v___x_2634_; 
v_toConstantVal_2631_ = lean_ctor_get(v_val_2627_, 0);
lean_inc_ref(v_toConstantVal_2631_);
lean_dec(v_val_2627_);
v_name_2632_ = lean_ctor_get(v_toConstantVal_2626_, 0);
lean_inc(v_name_2632_);
lean_dec_ref(v_toConstantVal_2626_);
v_name_2633_ = lean_ctor_get(v_toConstantVal_2631_, 0);
lean_inc(v_name_2633_);
lean_dec_ref(v_toConstantVal_2631_);
v___x_2634_ = lean_name_eq(v_name_2632_, v_name_2633_);
lean_dec(v_name_2633_);
lean_dec(v_name_2632_);
if (v___x_2634_ == 0)
{
lean_object* v___x_2635_; 
v___x_2635_ = l_Lean_Meta_isExprDefEq(v_fst_2614_, v_fst_2616_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_object* v_a_2636_; uint8_t v___x_2637_; 
v_a_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_a_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = lean_unbox(v_a_2636_);
lean_dec(v_a_2636_);
if (v___x_2637_ == 0)
{
lean_del_object(v___x_2629_);
lean_del_object(v___x_2619_);
v___y_2561_ = v_isEq_2604_;
v_isHEq_2562_ = v___x_2426_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___y_2606_;
v___y_2565_ = v___y_2607_;
v___y_2566_ = v___y_2608_;
goto v___jp_2560_;
}
else
{
lean_object* v___x_2638_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec_ref(v_config_2415_);
lean_inc(v_mvarId_2416_);
v___x_2638_ = l_Lean_MVarId_getType(v_mvarId_2416_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2638_) == 0)
{
lean_object* v_a_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; 
v_a_2639_ = lean_ctor_get(v___x_2638_, 0);
lean_inc(v_a_2639_);
lean_dec_ref_known(v___x_2638_, 1);
v___x_2640_ = l_Lean_LocalDecl_toExpr(v_val_2447_);
v___x_2641_ = l_Lean_Meta_mkEqOfHEq(v___x_2640_, v___x_2426_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2641_) == 0)
{
lean_object* v_a_2642_; lean_object* v___x_2643_; 
v_a_2642_ = lean_ctor_get(v___x_2641_, 0);
lean_inc(v_a_2642_);
lean_dec_ref_known(v___x_2641_, 1);
v___x_2643_ = l_Lean_Meta_mkNoConfusion(v_a_2639_, v_a_2642_, v___y_2605_, v___y_2606_, v___y_2607_, v___y_2608_);
if (lean_obj_tag(v___x_2643_) == 0)
{
lean_object* v_a_2644_; lean_object* v___x_2645_; 
v_a_2644_ = lean_ctor_get(v___x_2643_, 0);
lean_inc(v_a_2644_);
lean_dec_ref_known(v___x_2643_, 1);
v___x_2645_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2416_, v_a_2644_, v___y_2606_);
if (lean_obj_tag(v___x_2645_) == 0)
{
lean_object* v___x_2646_; lean_object* v___x_2648_; 
lean_dec_ref_known(v___x_2645_, 1);
v___x_2646_ = lean_box(v___x_2426_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2646_);
v___x_2648_ = v___x_2629_;
goto v_reusejp_2647_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v___x_2646_);
v___x_2648_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2647_;
}
v_reusejp_2647_:
{
lean_object* v___x_2650_; 
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 1, v___x_2451_);
lean_ctor_set(v___x_2619_, 0, v___x_2648_);
v___x_2650_ = v___x_2619_;
goto v_reusejp_2649_;
}
else
{
lean_object* v_reuseFailAlloc_2651_; 
v_reuseFailAlloc_2651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2651_, 0, v___x_2648_);
lean_ctor_set(v_reuseFailAlloc_2651_, 1, v___x_2451_);
v___x_2650_ = v_reuseFailAlloc_2651_;
goto v_reusejp_2649_;
}
v_reusejp_2649_:
{
v_a_2433_ = v___x_2650_;
goto v___jp_2432_;
}
}
}
else
{
lean_object* v_a_2653_; lean_object* v___x_2655_; uint8_t v_isShared_2656_; uint8_t v_isSharedCheck_2660_; 
lean_del_object(v___x_2629_);
lean_del_object(v___x_2619_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
v_a_2653_ = lean_ctor_get(v___x_2645_, 0);
v_isSharedCheck_2660_ = !lean_is_exclusive(v___x_2645_);
if (v_isSharedCheck_2660_ == 0)
{
v___x_2655_ = v___x_2645_;
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
else
{
lean_inc(v_a_2653_);
lean_dec(v___x_2645_);
v___x_2655_ = lean_box(0);
v_isShared_2656_ = v_isSharedCheck_2660_;
goto v_resetjp_2654_;
}
v_resetjp_2654_:
{
lean_object* v___x_2658_; 
if (v_isShared_2656_ == 0)
{
v___x_2658_ = v___x_2655_;
goto v_reusejp_2657_;
}
else
{
lean_object* v_reuseFailAlloc_2659_; 
v_reuseFailAlloc_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2659_, 0, v_a_2653_);
v___x_2658_ = v_reuseFailAlloc_2659_;
goto v_reusejp_2657_;
}
v_reusejp_2657_:
{
return v___x_2658_;
}
}
}
}
else
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2668_; 
lean_del_object(v___x_2629_);
lean_del_object(v___x_2619_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2661_ = lean_ctor_get(v___x_2643_, 0);
v_isSharedCheck_2668_ = !lean_is_exclusive(v___x_2643_);
if (v_isSharedCheck_2668_ == 0)
{
v___x_2663_ = v___x_2643_;
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___x_2643_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2668_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2666_; 
if (v_isShared_2664_ == 0)
{
v___x_2666_ = v___x_2663_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2661_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
}
}
else
{
lean_object* v_a_2669_; lean_object* v___x_2671_; uint8_t v_isShared_2672_; uint8_t v_isSharedCheck_2676_; 
lean_dec(v_a_2639_);
lean_del_object(v___x_2629_);
lean_del_object(v___x_2619_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2669_ = lean_ctor_get(v___x_2641_, 0);
v_isSharedCheck_2676_ = !lean_is_exclusive(v___x_2641_);
if (v_isSharedCheck_2676_ == 0)
{
v___x_2671_ = v___x_2641_;
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
else
{
lean_inc(v_a_2669_);
lean_dec(v___x_2641_);
v___x_2671_ = lean_box(0);
v_isShared_2672_ = v_isSharedCheck_2676_;
goto v_resetjp_2670_;
}
v_resetjp_2670_:
{
lean_object* v___x_2674_; 
if (v_isShared_2672_ == 0)
{
v___x_2674_ = v___x_2671_;
goto v_reusejp_2673_;
}
else
{
lean_object* v_reuseFailAlloc_2675_; 
v_reuseFailAlloc_2675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_a_2669_);
v___x_2674_ = v_reuseFailAlloc_2675_;
goto v_reusejp_2673_;
}
v_reusejp_2673_:
{
return v___x_2674_;
}
}
}
}
else
{
lean_object* v_a_2677_; lean_object* v___x_2679_; uint8_t v_isShared_2680_; uint8_t v_isSharedCheck_2684_; 
lean_del_object(v___x_2629_);
lean_del_object(v___x_2619_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2677_ = lean_ctor_get(v___x_2638_, 0);
v_isSharedCheck_2684_ = !lean_is_exclusive(v___x_2638_);
if (v_isSharedCheck_2684_ == 0)
{
v___x_2679_ = v___x_2638_;
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
else
{
lean_inc(v_a_2677_);
lean_dec(v___x_2638_);
v___x_2679_ = lean_box(0);
v_isShared_2680_ = v_isSharedCheck_2684_;
goto v_resetjp_2678_;
}
v_resetjp_2678_:
{
lean_object* v___x_2682_; 
if (v_isShared_2680_ == 0)
{
v___x_2682_ = v___x_2679_;
goto v_reusejp_2681_;
}
else
{
lean_object* v_reuseFailAlloc_2683_; 
v_reuseFailAlloc_2683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2683_, 0, v_a_2677_);
v___x_2682_ = v_reuseFailAlloc_2683_;
goto v_reusejp_2681_;
}
v_reusejp_2681_:
{
return v___x_2682_;
}
}
}
}
}
else
{
lean_object* v_a_2685_; lean_object* v___x_2687_; uint8_t v_isShared_2688_; uint8_t v_isSharedCheck_2692_; 
lean_del_object(v___x_2629_);
lean_del_object(v___x_2619_);
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2685_ = lean_ctor_get(v___x_2635_, 0);
v_isSharedCheck_2692_ = !lean_is_exclusive(v___x_2635_);
if (v_isSharedCheck_2692_ == 0)
{
v___x_2687_ = v___x_2635_;
v_isShared_2688_ = v_isSharedCheck_2692_;
goto v_resetjp_2686_;
}
else
{
lean_inc(v_a_2685_);
lean_dec(v___x_2635_);
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
lean_del_object(v___x_2629_);
lean_del_object(v___x_2619_);
lean_dec(v_fst_2616_);
lean_dec(v_fst_2614_);
v___y_2561_ = v_isEq_2604_;
v_isHEq_2562_ = v___x_2426_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___y_2606_;
v___y_2565_ = v___y_2607_;
v___y_2566_ = v___y_2608_;
goto v___jp_2560_;
}
}
}
else
{
lean_dec(v_a_2625_);
lean_dec(v_val_2623_);
lean_del_object(v___x_2619_);
lean_dec(v_fst_2616_);
lean_dec(v_fst_2614_);
v___y_2561_ = v_isEq_2604_;
v_isHEq_2562_ = v___x_2426_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___y_2606_;
v___y_2565_ = v___y_2607_;
v___y_2566_ = v___y_2608_;
goto v___jp_2560_;
}
}
else
{
lean_object* v_a_2694_; lean_object* v___x_2696_; uint8_t v_isShared_2697_; uint8_t v_isSharedCheck_2701_; 
lean_dec(v_val_2623_);
lean_del_object(v___x_2619_);
lean_dec(v_fst_2616_);
lean_dec(v_fst_2614_);
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2694_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2701_ == 0)
{
v___x_2696_ = v___x_2624_;
v_isShared_2697_ = v_isSharedCheck_2701_;
goto v_resetjp_2695_;
}
else
{
lean_inc(v_a_2694_);
lean_dec(v___x_2624_);
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
lean_dec(v_a_2622_);
lean_del_object(v___x_2619_);
lean_dec(v_snd_2617_);
lean_dec(v_fst_2616_);
lean_dec(v_fst_2614_);
v___y_2561_ = v_isEq_2604_;
v_isHEq_2562_ = v___x_2426_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___y_2606_;
v___y_2565_ = v___y_2607_;
v___y_2566_ = v___y_2608_;
goto v___jp_2560_;
}
}
else
{
lean_object* v_a_2702_; lean_object* v___x_2704_; uint8_t v_isShared_2705_; uint8_t v_isSharedCheck_2709_; 
lean_del_object(v___x_2619_);
lean_dec(v_snd_2617_);
lean_dec(v_fst_2616_);
lean_dec(v_fst_2614_);
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2702_ = lean_ctor_get(v___x_2621_, 0);
v_isSharedCheck_2709_ = !lean_is_exclusive(v___x_2621_);
if (v_isSharedCheck_2709_ == 0)
{
v___x_2704_ = v___x_2621_;
v_isShared_2705_ = v_isSharedCheck_2709_;
goto v_resetjp_2703_;
}
else
{
lean_inc(v_a_2702_);
lean_dec(v___x_2621_);
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
else
{
lean_dec(v_a_2610_);
v___y_2561_ = v_isEq_2604_;
v_isHEq_2562_ = v___x_2479_;
v___y_2563_ = v___y_2605_;
v___y_2564_ = v___y_2606_;
v___y_2565_ = v___y_2607_;
v___y_2566_ = v___y_2608_;
goto v___jp_2560_;
}
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2711_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2609_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2609_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
v___jp_2719_:
{
lean_object* v___x_2724_; 
lean_inc_ref(v___x_2480_);
v___x_2724_ = l_Lean_Meta_matchEq_x3f(v___x_2480_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2724_) == 0)
{
lean_object* v_a_2725_; 
v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
lean_inc(v_a_2725_);
lean_dec_ref_known(v___x_2724_, 1);
if (lean_obj_tag(v_a_2725_) == 1)
{
lean_object* v_val_2726_; lean_object* v_snd_2727_; lean_object* v_fst_2728_; lean_object* v_snd_2729_; lean_object* v___x_2731_; uint8_t v_isShared_2732_; uint8_t v_isSharedCheck_2801_; 
v_val_2726_ = lean_ctor_get(v_a_2725_, 0);
lean_inc(v_val_2726_);
lean_dec_ref_known(v_a_2725_, 1);
v_snd_2727_ = lean_ctor_get(v_val_2726_, 1);
lean_inc(v_snd_2727_);
lean_dec(v_val_2726_);
v_fst_2728_ = lean_ctor_get(v_snd_2727_, 0);
v_snd_2729_ = lean_ctor_get(v_snd_2727_, 1);
v_isSharedCheck_2801_ = !lean_is_exclusive(v_snd_2727_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2731_ = v_snd_2727_;
v_isShared_2732_ = v_isSharedCheck_2801_;
goto v_resetjp_2730_;
}
else
{
lean_inc(v_snd_2729_);
lean_inc(v_fst_2728_);
lean_dec(v_snd_2727_);
v___x_2731_ = lean_box(0);
v_isShared_2732_ = v_isSharedCheck_2801_;
goto v_resetjp_2730_;
}
v_resetjp_2730_:
{
lean_object* v___x_2733_; 
v___x_2733_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2728_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2733_) == 0)
{
lean_object* v_a_2734_; 
v_a_2734_ = lean_ctor_get(v___x_2733_, 0);
lean_inc(v_a_2734_);
lean_dec_ref_known(v___x_2733_, 1);
if (lean_obj_tag(v_a_2734_) == 1)
{
lean_object* v_val_2735_; lean_object* v___x_2736_; 
v_val_2735_ = lean_ctor_get(v_a_2734_, 0);
lean_inc(v_val_2735_);
lean_dec_ref_known(v_a_2734_, 1);
v___x_2736_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2729_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
if (lean_obj_tag(v_a_2737_) == 1)
{
lean_object* v_toConstantVal_2738_; lean_object* v_val_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2784_; 
v_toConstantVal_2738_ = lean_ctor_get(v_val_2735_, 0);
lean_inc_ref(v_toConstantVal_2738_);
lean_dec(v_val_2735_);
v_val_2739_ = lean_ctor_get(v_a_2737_, 0);
v_isSharedCheck_2784_ = !lean_is_exclusive(v_a_2737_);
if (v_isSharedCheck_2784_ == 0)
{
v___x_2741_ = v_a_2737_;
v_isShared_2742_ = v_isSharedCheck_2784_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_val_2739_);
lean_dec(v_a_2737_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2784_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v_toConstantVal_2743_; lean_object* v_name_2744_; lean_object* v_name_2745_; uint8_t v___x_2746_; 
v_toConstantVal_2743_ = lean_ctor_get(v_val_2739_, 0);
lean_inc_ref(v_toConstantVal_2743_);
lean_dec(v_val_2739_);
v_name_2744_ = lean_ctor_get(v_toConstantVal_2738_, 0);
lean_inc(v_name_2744_);
lean_dec_ref(v_toConstantVal_2738_);
v_name_2745_ = lean_ctor_get(v_toConstantVal_2743_, 0);
lean_inc(v_name_2745_);
lean_dec_ref(v_toConstantVal_2743_);
v___x_2746_ = lean_name_eq(v_name_2744_, v_name_2745_);
lean_dec(v_name_2745_);
lean_dec(v_name_2744_);
if (v___x_2746_ == 0)
{
lean_object* v___x_2747_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec_ref(v_config_2415_);
lean_inc(v_mvarId_2416_);
v___x_2747_ = l_Lean_MVarId_getType(v_mvarId_2416_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2747_) == 0)
{
lean_object* v_a_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; 
v_a_2748_ = lean_ctor_get(v___x_2747_, 0);
lean_inc(v_a_2748_);
lean_dec_ref_known(v___x_2747_, 1);
v___x_2749_ = l_Lean_LocalDecl_toExpr(v_val_2447_);
v___x_2750_ = l_Lean_Meta_mkNoConfusion(v_a_2748_, v___x_2749_, v___y_2720_, v___y_2721_, v___y_2722_, v___y_2723_);
if (lean_obj_tag(v___x_2750_) == 0)
{
lean_object* v_a_2751_; lean_object* v___x_2752_; 
v_a_2751_ = lean_ctor_get(v___x_2750_, 0);
lean_inc(v_a_2751_);
lean_dec_ref_known(v___x_2750_, 1);
v___x_2752_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2416_, v_a_2751_, v___y_2721_);
if (lean_obj_tag(v___x_2752_) == 0)
{
lean_object* v___x_2753_; lean_object* v___x_2755_; 
lean_dec_ref_known(v___x_2752_, 1);
v___x_2753_ = lean_box(v___x_2426_);
if (v_isShared_2742_ == 0)
{
lean_ctor_set(v___x_2741_, 0, v___x_2753_);
v___x_2755_ = v___x_2741_;
goto v_reusejp_2754_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2753_);
v___x_2755_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2754_;
}
v_reusejp_2754_:
{
lean_object* v___x_2757_; 
if (v_isShared_2732_ == 0)
{
lean_ctor_set(v___x_2731_, 1, v___x_2451_);
lean_ctor_set(v___x_2731_, 0, v___x_2755_);
v___x_2757_ = v___x_2731_;
goto v_reusejp_2756_;
}
else
{
lean_object* v_reuseFailAlloc_2758_; 
v_reuseFailAlloc_2758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2758_, 0, v___x_2755_);
lean_ctor_set(v_reuseFailAlloc_2758_, 1, v___x_2451_);
v___x_2757_ = v_reuseFailAlloc_2758_;
goto v_reusejp_2756_;
}
v_reusejp_2756_:
{
v_a_2433_ = v___x_2757_;
goto v___jp_2432_;
}
}
}
else
{
lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2767_; 
lean_del_object(v___x_2741_);
lean_del_object(v___x_2731_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
v_a_2760_ = lean_ctor_get(v___x_2752_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v___x_2752_);
if (v_isSharedCheck_2767_ == 0)
{
v___x_2762_ = v___x_2752_;
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2752_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2767_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2765_; 
if (v_isShared_2763_ == 0)
{
v___x_2765_ = v___x_2762_;
goto v_reusejp_2764_;
}
else
{
lean_object* v_reuseFailAlloc_2766_; 
v_reuseFailAlloc_2766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2766_, 0, v_a_2760_);
v___x_2765_ = v_reuseFailAlloc_2766_;
goto v_reusejp_2764_;
}
v_reusejp_2764_:
{
return v___x_2765_;
}
}
}
}
else
{
lean_object* v_a_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2775_; 
lean_del_object(v___x_2741_);
lean_del_object(v___x_2731_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2768_ = lean_ctor_get(v___x_2750_, 0);
v_isSharedCheck_2775_ = !lean_is_exclusive(v___x_2750_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2770_ = v___x_2750_;
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
else
{
lean_inc(v_a_2768_);
lean_dec(v___x_2750_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2775_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2773_; 
if (v_isShared_2771_ == 0)
{
v___x_2773_ = v___x_2770_;
goto v_reusejp_2772_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
v___x_2773_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2772_;
}
v_reusejp_2772_:
{
return v___x_2773_;
}
}
}
}
else
{
lean_object* v_a_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2783_; 
lean_del_object(v___x_2741_);
lean_del_object(v___x_2731_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2776_ = lean_ctor_get(v___x_2747_, 0);
v_isSharedCheck_2783_ = !lean_is_exclusive(v___x_2747_);
if (v_isSharedCheck_2783_ == 0)
{
v___x_2778_ = v___x_2747_;
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_a_2776_);
lean_dec(v___x_2747_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2783_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2781_; 
if (v_isShared_2779_ == 0)
{
v___x_2781_ = v___x_2778_;
goto v_reusejp_2780_;
}
else
{
lean_object* v_reuseFailAlloc_2782_; 
v_reuseFailAlloc_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2782_, 0, v_a_2776_);
v___x_2781_ = v_reuseFailAlloc_2782_;
goto v_reusejp_2780_;
}
v_reusejp_2780_:
{
return v___x_2781_;
}
}
}
}
else
{
lean_del_object(v___x_2741_);
lean_del_object(v___x_2731_);
v_isEq_2604_ = v___x_2426_;
v___y_2605_ = v___y_2720_;
v___y_2606_ = v___y_2721_;
v___y_2607_ = v___y_2722_;
v___y_2608_ = v___y_2723_;
goto v___jp_2603_;
}
}
}
else
{
lean_dec(v_a_2737_);
lean_dec(v_val_2735_);
lean_del_object(v___x_2731_);
v_isEq_2604_ = v___x_2426_;
v___y_2605_ = v___y_2720_;
v___y_2606_ = v___y_2721_;
v___y_2607_ = v___y_2722_;
v___y_2608_ = v___y_2723_;
goto v___jp_2603_;
}
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_dec(v_val_2735_);
lean_del_object(v___x_2731_);
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2785_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2736_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2736_);
v___x_2787_ = lean_box(0);
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
v_resetjp_2786_:
{
lean_object* v___x_2790_; 
if (v_isShared_2788_ == 0)
{
v___x_2790_ = v___x_2787_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2791_; 
v_reuseFailAlloc_2791_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2791_, 0, v_a_2785_);
v___x_2790_ = v_reuseFailAlloc_2791_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
return v___x_2790_;
}
}
}
}
else
{
lean_dec(v_a_2734_);
lean_del_object(v___x_2731_);
lean_dec(v_snd_2729_);
v_isEq_2604_ = v___x_2426_;
v___y_2605_ = v___y_2720_;
v___y_2606_ = v___y_2721_;
v___y_2607_ = v___y_2722_;
v___y_2608_ = v___y_2723_;
goto v___jp_2603_;
}
}
else
{
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_del_object(v___x_2731_);
lean_dec(v_snd_2729_);
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2793_ = lean_ctor_get(v___x_2733_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2733_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2733_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2733_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2798_; 
if (v_isShared_2796_ == 0)
{
v___x_2798_ = v___x_2795_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_a_2793_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
else
{
lean_dec(v_a_2725_);
v_isEq_2604_ = v___x_2479_;
v___y_2605_ = v___y_2720_;
v___y_2606_ = v___y_2721_;
v___y_2607_ = v___y_2722_;
v___y_2608_ = v___y_2723_;
goto v___jp_2603_;
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2802_ = lean_ctor_get(v___x_2724_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2724_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2724_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2724_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
lean_object* v___x_2807_; 
if (v_isShared_2805_ == 0)
{
v___x_2807_ = v___x_2804_;
goto v_reusejp_2806_;
}
else
{
lean_object* v_reuseFailAlloc_2808_; 
v_reuseFailAlloc_2808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
v___x_2807_ = v_reuseFailAlloc_2808_;
goto v_reusejp_2806_;
}
v_reusejp_2806_:
{
return v___x_2807_;
}
}
}
}
v___jp_2810_:
{
lean_object* v___x_2815_; 
lean_inc_ref(v___x_2480_);
v___x_2815_ = l_Lean_refutableHasNotBit_x3f(v___x_2480_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v_a_2816_; 
v_a_2816_ = lean_ctor_get(v___x_2815_, 0);
lean_inc(v_a_2816_);
lean_dec_ref_known(v___x_2815_, 1);
if (lean_obj_tag(v_a_2816_) == 1)
{
lean_object* v_val_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2856_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec_ref(v_config_2415_);
v_val_2817_ = lean_ctor_get(v_a_2816_, 0);
v_isSharedCheck_2856_ = !lean_is_exclusive(v_a_2816_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2819_ = v_a_2816_;
v_isShared_2820_ = v_isSharedCheck_2856_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_val_2817_);
lean_dec(v_a_2816_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2856_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2821_; 
lean_inc(v_mvarId_2416_);
v___x_2821_ = l_Lean_MVarId_getType(v_mvarId_2416_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2821_) == 0)
{
lean_object* v_a_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v_a_2822_ = lean_ctor_get(v___x_2821_, 0);
lean_inc(v_a_2822_);
lean_dec_ref_known(v___x_2821_, 1);
v___x_2823_ = l_Lean_LocalDecl_toExpr(v_val_2447_);
v___x_2824_ = l_Lean_Meta_mkAbsurd(v_a_2822_, v_val_2817_, v___x_2823_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2824_) == 0)
{
lean_object* v_a_2825_; lean_object* v___x_2826_; 
v_a_2825_ = lean_ctor_get(v___x_2824_, 0);
lean_inc(v_a_2825_);
lean_dec_ref_known(v___x_2824_, 1);
v___x_2826_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2416_, v_a_2825_, v___y_2812_);
if (lean_obj_tag(v___x_2826_) == 0)
{
lean_object* v___x_2827_; lean_object* v___x_2829_; 
lean_dec_ref_known(v___x_2826_, 1);
v___x_2827_ = lean_box(v___x_2426_);
if (v_isShared_2820_ == 0)
{
lean_ctor_set(v___x_2819_, 0, v___x_2827_);
v___x_2829_ = v___x_2819_;
goto v_reusejp_2828_;
}
else
{
lean_object* v_reuseFailAlloc_2831_; 
v_reuseFailAlloc_2831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2831_, 0, v___x_2827_);
v___x_2829_ = v_reuseFailAlloc_2831_;
goto v_reusejp_2828_;
}
v_reusejp_2828_:
{
lean_object* v___x_2830_; 
v___x_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v___x_2451_);
v_a_2433_ = v___x_2830_;
goto v___jp_2432_;
}
}
else
{
lean_object* v_a_2832_; lean_object* v___x_2834_; uint8_t v_isShared_2835_; uint8_t v_isSharedCheck_2839_; 
lean_del_object(v___x_2819_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
v_a_2832_ = lean_ctor_get(v___x_2826_, 0);
v_isSharedCheck_2839_ = !lean_is_exclusive(v___x_2826_);
if (v_isSharedCheck_2839_ == 0)
{
v___x_2834_ = v___x_2826_;
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
else
{
lean_inc(v_a_2832_);
lean_dec(v___x_2826_);
v___x_2834_ = lean_box(0);
v_isShared_2835_ = v_isSharedCheck_2839_;
goto v_resetjp_2833_;
}
v_resetjp_2833_:
{
lean_object* v___x_2837_; 
if (v_isShared_2835_ == 0)
{
v___x_2837_ = v___x_2834_;
goto v_reusejp_2836_;
}
else
{
lean_object* v_reuseFailAlloc_2838_; 
v_reuseFailAlloc_2838_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2838_, 0, v_a_2832_);
v___x_2837_ = v_reuseFailAlloc_2838_;
goto v_reusejp_2836_;
}
v_reusejp_2836_:
{
return v___x_2837_;
}
}
}
}
else
{
lean_object* v_a_2840_; lean_object* v___x_2842_; uint8_t v_isShared_2843_; uint8_t v_isSharedCheck_2847_; 
lean_del_object(v___x_2819_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2840_ = lean_ctor_get(v___x_2824_, 0);
v_isSharedCheck_2847_ = !lean_is_exclusive(v___x_2824_);
if (v_isSharedCheck_2847_ == 0)
{
v___x_2842_ = v___x_2824_;
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
else
{
lean_inc(v_a_2840_);
lean_dec(v___x_2824_);
v___x_2842_ = lean_box(0);
v_isShared_2843_ = v_isSharedCheck_2847_;
goto v_resetjp_2841_;
}
v_resetjp_2841_:
{
lean_object* v___x_2845_; 
if (v_isShared_2843_ == 0)
{
v___x_2845_ = v___x_2842_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2846_; 
v_reuseFailAlloc_2846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2846_, 0, v_a_2840_);
v___x_2845_ = v_reuseFailAlloc_2846_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
return v___x_2845_;
}
}
}
}
else
{
lean_object* v_a_2848_; lean_object* v___x_2850_; uint8_t v_isShared_2851_; uint8_t v_isSharedCheck_2855_; 
lean_del_object(v___x_2819_);
lean_dec(v_val_2817_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2848_ = lean_ctor_get(v___x_2821_, 0);
v_isSharedCheck_2855_ = !lean_is_exclusive(v___x_2821_);
if (v_isSharedCheck_2855_ == 0)
{
v___x_2850_ = v___x_2821_;
v_isShared_2851_ = v_isSharedCheck_2855_;
goto v_resetjp_2849_;
}
else
{
lean_inc(v_a_2848_);
lean_dec(v___x_2821_);
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
}
else
{
lean_object* v___x_2857_; 
lean_dec(v_a_2816_);
lean_inc_ref(v___x_2480_);
v___x_2857_ = l_Lean_Meta_matchNe_x3f(v___x_2480_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v_a_2858_; 
v_a_2858_ = lean_ctor_get(v___x_2857_, 0);
lean_inc(v_a_2858_);
lean_dec_ref_known(v___x_2857_, 1);
if (lean_obj_tag(v_a_2858_) == 1)
{
lean_object* v_val_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2928_; 
v_val_2859_ = lean_ctor_get(v_a_2858_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v_a_2858_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2861_ = v_a_2858_;
v_isShared_2862_ = v_isSharedCheck_2928_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_val_2859_);
lean_dec(v_a_2858_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2928_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v_snd_2863_; lean_object* v_fst_2864_; lean_object* v_snd_2865_; lean_object* v___x_2867_; uint8_t v_isShared_2868_; uint8_t v_isSharedCheck_2927_; 
v_snd_2863_ = lean_ctor_get(v_val_2859_, 1);
lean_inc(v_snd_2863_);
lean_dec(v_val_2859_);
v_fst_2864_ = lean_ctor_get(v_snd_2863_, 0);
v_snd_2865_ = lean_ctor_get(v_snd_2863_, 1);
v_isSharedCheck_2927_ = !lean_is_exclusive(v_snd_2863_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2867_ = v_snd_2863_;
v_isShared_2868_ = v_isSharedCheck_2927_;
goto v_resetjp_2866_;
}
else
{
lean_inc(v_snd_2865_);
lean_inc(v_fst_2864_);
lean_dec(v_snd_2863_);
v___x_2867_ = lean_box(0);
v_isShared_2868_ = v_isSharedCheck_2927_;
goto v_resetjp_2866_;
}
v_resetjp_2866_:
{
lean_object* v___x_2869_; 
lean_inc(v_fst_2864_);
v___x_2869_ = l_Lean_Meta_isExprDefEq(v_fst_2864_, v_snd_2865_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; uint8_t v___x_2871_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
lean_inc(v_a_2870_);
lean_dec_ref_known(v___x_2869_, 1);
v___x_2871_ = lean_unbox(v_a_2870_);
lean_dec(v_a_2870_);
if (v___x_2871_ == 0)
{
lean_del_object(v___x_2867_);
lean_dec(v_fst_2864_);
lean_del_object(v___x_2861_);
v___y_2720_ = v___y_2811_;
v___y_2721_ = v___y_2812_;
v___y_2722_ = v___y_2813_;
v___y_2723_ = v___y_2814_;
goto v___jp_2719_;
}
else
{
lean_object* v___x_2872_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec_ref(v_config_2415_);
lean_inc(v_mvarId_2416_);
v___x_2872_ = l_Lean_MVarId_getType(v_mvarId_2416_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2872_) == 0)
{
lean_object* v_a_2873_; lean_object* v___x_2874_; 
v_a_2873_ = lean_ctor_get(v___x_2872_, 0);
lean_inc(v_a_2873_);
lean_dec_ref_known(v___x_2872_, 1);
v___x_2874_ = l_Lean_Meta_mkEqRefl(v_fst_2864_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
v___x_2876_ = l_Lean_LocalDecl_toExpr(v_val_2447_);
v___x_2877_ = l_Lean_Meta_mkAbsurd(v_a_2873_, v_a_2875_, v___x_2876_, v___y_2811_, v___y_2812_, v___y_2813_, v___y_2814_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v___x_2879_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v___x_2879_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2416_, v_a_2878_, v___y_2812_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v___x_2880_; lean_object* v___x_2882_; 
lean_dec_ref_known(v___x_2879_, 1);
v___x_2880_ = lean_box(v___x_2426_);
if (v_isShared_2862_ == 0)
{
lean_ctor_set(v___x_2861_, 0, v___x_2880_);
v___x_2882_ = v___x_2861_;
goto v_reusejp_2881_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2880_);
v___x_2882_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2881_;
}
v_reusejp_2881_:
{
lean_object* v___x_2884_; 
if (v_isShared_2868_ == 0)
{
lean_ctor_set(v___x_2867_, 1, v___x_2451_);
lean_ctor_set(v___x_2867_, 0, v___x_2882_);
v___x_2884_ = v___x_2867_;
goto v_reusejp_2883_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2882_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v___x_2451_);
v___x_2884_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2883_;
}
v_reusejp_2883_:
{
v_a_2433_ = v___x_2884_;
goto v___jp_2432_;
}
}
}
else
{
lean_object* v_a_2887_; lean_object* v___x_2889_; uint8_t v_isShared_2890_; uint8_t v_isSharedCheck_2894_; 
lean_del_object(v___x_2867_);
lean_del_object(v___x_2861_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
v_a_2887_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2894_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2894_ == 0)
{
v___x_2889_ = v___x_2879_;
v_isShared_2890_ = v_isSharedCheck_2894_;
goto v_resetjp_2888_;
}
else
{
lean_inc(v_a_2887_);
lean_dec(v___x_2879_);
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
else
{
lean_object* v_a_2895_; lean_object* v___x_2897_; uint8_t v_isShared_2898_; uint8_t v_isSharedCheck_2902_; 
lean_del_object(v___x_2867_);
lean_del_object(v___x_2861_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2895_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2902_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2902_ == 0)
{
v___x_2897_ = v___x_2877_;
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
else
{
lean_inc(v_a_2895_);
lean_dec(v___x_2877_);
v___x_2897_ = lean_box(0);
v_isShared_2898_ = v_isSharedCheck_2902_;
goto v_resetjp_2896_;
}
v_resetjp_2896_:
{
lean_object* v___x_2900_; 
if (v_isShared_2898_ == 0)
{
v___x_2900_ = v___x_2897_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2901_; 
v_reuseFailAlloc_2901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2901_, 0, v_a_2895_);
v___x_2900_ = v_reuseFailAlloc_2901_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
return v___x_2900_;
}
}
}
}
else
{
lean_object* v_a_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2910_; 
lean_dec(v_a_2873_);
lean_del_object(v___x_2867_);
lean_del_object(v___x_2861_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2903_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2910_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2910_ == 0)
{
v___x_2905_ = v___x_2874_;
v_isShared_2906_ = v_isSharedCheck_2910_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_a_2903_);
lean_dec(v___x_2874_);
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
lean_object* v_a_2911_; lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
lean_del_object(v___x_2867_);
lean_dec(v_fst_2864_);
lean_del_object(v___x_2861_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
v_a_2911_ = lean_ctor_get(v___x_2872_, 0);
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2872_);
if (v_isSharedCheck_2918_ == 0)
{
v___x_2913_ = v___x_2872_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_inc(v_a_2911_);
lean_dec(v___x_2872_);
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
}
else
{
lean_object* v_a_2919_; lean_object* v___x_2921_; uint8_t v_isShared_2922_; uint8_t v_isSharedCheck_2926_; 
lean_del_object(v___x_2867_);
lean_dec(v_fst_2864_);
lean_del_object(v___x_2861_);
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2919_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2926_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2926_ == 0)
{
v___x_2921_ = v___x_2869_;
v_isShared_2922_ = v_isSharedCheck_2926_;
goto v_resetjp_2920_;
}
else
{
lean_inc(v_a_2919_);
lean_dec(v___x_2869_);
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
}
}
else
{
lean_dec(v_a_2858_);
v___y_2720_ = v___y_2811_;
v___y_2721_ = v___y_2812_;
v___y_2722_ = v___y_2813_;
v___y_2723_ = v___y_2814_;
goto v___jp_2719_;
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2929_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2857_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2857_);
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
}
else
{
lean_object* v_a_2937_; lean_object* v___x_2939_; uint8_t v_isShared_2940_; uint8_t v_isSharedCheck_2944_; 
lean_dec_ref(v___x_2480_);
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2937_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2944_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2944_ == 0)
{
v___x_2939_ = v___x_2815_;
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
else
{
lean_inc(v_a_2937_);
lean_dec(v___x_2815_);
v___x_2939_ = lean_box(0);
v_isShared_2940_ = v_isSharedCheck_2944_;
goto v_resetjp_2938_;
}
v_resetjp_2938_:
{
lean_object* v___x_2942_; 
if (v_isShared_2940_ == 0)
{
v___x_2942_ = v___x_2939_;
goto v_reusejp_2941_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v_a_2937_);
v___x_2942_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2941_;
}
v_reusejp_2941_:
{
return v___x_2942_;
}
}
}
}
}
else
{
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
v_a_2441_ = v___x_2452_;
goto v___jp_2440_;
}
v___jp_2453_:
{
uint8_t v_emptyType_2460_; 
v_emptyType_2460_ = lean_ctor_get_uint8(v_config_2415_, sizeof(void*)*1 + 1);
if (v_emptyType_2460_ == 0)
{
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
v_a_2441_ = v___x_2452_;
goto v___jp_2440_;
}
else
{
if (v___y_2454_ == 0)
{
if (v___y_2455_ == 0)
{
lean_object* v_searchFuel_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; 
v_searchFuel_2461_ = lean_ctor_get(v_config_2415_, 0);
v___x_2462_ = l_Lean_LocalDecl_fvarId(v_val_2447_);
lean_dec(v_val_2447_);
lean_inc(v_searchFuel_2461_);
lean_inc(v_mvarId_2416_);
v___x_2463_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2416_, v___x_2462_, v_searchFuel_2461_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2463_) == 0)
{
lean_object* v_a_2464_; uint8_t v___x_2465_; 
v_a_2464_ = lean_ctor_get(v___x_2463_, 0);
lean_inc(v_a_2464_);
lean_dec_ref_known(v___x_2463_, 1);
v___x_2465_ = lean_unbox(v_a_2464_);
lean_dec(v_a_2464_);
if (v___x_2465_ == 0)
{
lean_del_object(v___x_2449_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
v_a_2441_ = v___x_2452_;
goto v___jp_2440_;
}
else
{
lean_object* v___x_2466_; lean_object* v___x_2468_; 
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v___x_2466_ = lean_box(v___x_2426_);
if (v_isShared_2450_ == 0)
{
lean_ctor_set(v___x_2449_, 0, v___x_2466_);
v___x_2468_ = v___x_2449_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2470_; 
v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2466_);
v___x_2468_ = v_reuseFailAlloc_2470_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
lean_object* v___x_2469_; 
v___x_2469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2469_, 0, v___x_2468_);
lean_ctor_set(v___x_2469_, 1, v___x_2451_);
v_a_2433_ = v___x_2469_;
goto v___jp_2432_;
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_del_object(v___x_2449_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
lean_dec(v_mvarId_2416_);
lean_dec_ref(v_config_2415_);
v_a_2471_ = lean_ctor_get(v___x_2463_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2463_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2463_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2463_);
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
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
v_a_2441_ = v___x_2452_;
goto v___jp_2440_;
}
}
else
{
lean_del_object(v___x_2449_);
lean_dec(v_val_2447_);
lean_del_object(v___x_2430_);
lean_dec(v_snd_2428_);
v_a_2441_ = v___x_2452_;
goto v___jp_2440_;
}
}
}
}
}
v___jp_2432_:
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
v___x_2434_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2434_, 0, v_a_2433_);
if (v_isShared_2431_ == 0)
{
lean_ctor_set(v___x_2430_, 0, v___x_2434_);
v___x_2436_ = v___x_2430_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v___x_2434_);
lean_ctor_set(v_reuseFailAlloc_2438_, 1, v_snd_2428_);
v___x_2436_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
lean_object* v___x_2437_; 
v___x_2437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
return v___x_2437_;
}
}
v___jp_2440_:
{
lean_object* v___x_2442_; size_t v___x_2443_; size_t v___x_2444_; lean_object* v___x_2445_; 
v___x_2442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2442_, 0, v___x_2439_);
lean_ctor_set(v___x_2442_, 1, v_a_2441_);
v___x_2443_ = ((size_t)1ULL);
v___x_2444_ = lean_usize_add(v_i_2419_, v___x_2443_);
v___x_2445_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2415_, v_mvarId_2416_, v_as_2417_, v_sz_2418_, v___x_2444_, v___x_2442_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
return v___x_2445_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3011_, lean_object* v_mvarId_3012_, lean_object* v_as_3013_, lean_object* v_sz_3014_, lean_object* v_i_3015_, lean_object* v_b_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_, lean_object* v___y_3021_){
_start:
{
size_t v_sz_boxed_3022_; size_t v_i_boxed_3023_; lean_object* v_res_3024_; 
v_sz_boxed_3022_ = lean_unbox_usize(v_sz_3014_);
lean_dec(v_sz_3014_);
v_i_boxed_3023_ = lean_unbox_usize(v_i_3015_);
lean_dec(v_i_3015_);
v_res_3024_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3011_, v_mvarId_3012_, v_as_3013_, v_sz_boxed_3022_, v_i_boxed_3023_, v_b_3016_, v___y_3017_, v___y_3018_, v___y_3019_, v___y_3020_);
lean_dec(v___y_3020_);
lean_dec_ref(v___y_3019_);
lean_dec(v___y_3018_);
lean_dec_ref(v___y_3017_);
lean_dec_ref(v_as_3013_);
return v_res_3024_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3028_, lean_object* v_mvarId_3029_, lean_object* v_as_3030_, size_t v_sz_3031_, size_t v_i_3032_, lean_object* v_b_3033_, lean_object* v___y_3034_, lean_object* v___y_3035_, lean_object* v___y_3036_, lean_object* v___y_3037_){
_start:
{
uint8_t v___x_3039_; 
v___x_3039_ = lean_usize_dec_lt(v_i_3032_, v_sz_3031_);
if (v___x_3039_ == 0)
{
lean_object* v___x_3040_; 
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v___x_3040_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3040_, 0, v_b_3033_);
return v___x_3040_;
}
else
{
lean_object* v_snd_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3654_; 
v_snd_3041_ = lean_ctor_get(v_b_3033_, 1);
v_isSharedCheck_3654_ = !lean_is_exclusive(v_b_3033_);
if (v_isSharedCheck_3654_ == 0)
{
lean_object* v_unused_3655_; 
v_unused_3655_ = lean_ctor_get(v_b_3033_, 0);
lean_dec(v_unused_3655_);
v___x_3043_ = v_b_3033_;
v_isShared_3044_ = v_isSharedCheck_3654_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_snd_3041_);
lean_dec(v_b_3033_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3654_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v_a_3046_; lean_object* v___x_3052_; lean_object* v_a_3054_; lean_object* v_a_3059_; 
v___x_3052_ = lean_box(0);
v_a_3059_ = lean_array_uget(v_as_3030_, v_i_3032_);
if (lean_obj_tag(v_a_3059_) == 0)
{
lean_del_object(v___x_3043_);
v_a_3054_ = v_snd_3041_;
goto v___jp_3053_;
}
else
{
lean_object* v_val_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3653_; 
v_val_3060_ = lean_ctor_get(v_a_3059_, 0);
v_isSharedCheck_3653_ = !lean_is_exclusive(v_a_3059_);
if (v_isSharedCheck_3653_ == 0)
{
v___x_3062_ = v_a_3059_;
v_isShared_3063_ = v_isSharedCheck_3653_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_val_3060_);
lean_dec(v_a_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3653_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3064_; lean_object* v___x_3065_; uint8_t v___y_3067_; uint8_t v___y_3068_; lean_object* v___y_3069_; lean_object* v___y_3070_; lean_object* v___y_3071_; lean_object* v___y_3072_; uint8_t v___x_3093_; 
v___x_3064_ = lean_box(0);
v___x_3065_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3093_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3060_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; uint8_t v___y_3096_; uint8_t v___y_3097_; lean_object* v___y_3098_; lean_object* v___y_3099_; lean_object* v___y_3100_; lean_object* v___y_3101_; lean_object* v___y_3120_; lean_object* v___y_3121_; lean_object* v___y_3122_; uint8_t v___y_3123_; uint8_t v___y_3124_; lean_object* v___y_3125_; lean_object* v_a_3126_; lean_object* v___y_3132_; lean_object* v___y_3133_; lean_object* v___y_3134_; lean_object* v___y_3135_; uint8_t v___y_3136_; uint8_t v___y_3137_; lean_object* v___y_3138_; lean_object* v___y_3139_; uint8_t v___y_3183_; uint8_t v_isHEq_3184_; lean_object* v___y_3185_; lean_object* v___y_3186_; lean_object* v___y_3187_; lean_object* v___y_3188_; uint8_t v_isEq_3226_; lean_object* v___y_3227_; lean_object* v___y_3228_; lean_object* v___y_3229_; lean_object* v___y_3230_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; lean_object* v___x_3583_; 
v___x_3094_ = l_Lean_LocalDecl_type(v_val_3060_);
lean_inc_ref(v___x_3094_);
v___x_3583_ = l_Lean_Meta_matchNot_x3f(v___x_3094_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
if (lean_obj_tag(v___x_3583_) == 0)
{
lean_object* v_a_3584_; 
v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
lean_inc(v_a_3584_);
lean_dec_ref_known(v___x_3583_, 1);
if (lean_obj_tag(v_a_3584_) == 1)
{
lean_object* v_val_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3644_; 
v_val_3585_ = lean_ctor_get(v_a_3584_, 0);
v_isSharedCheck_3644_ = !lean_is_exclusive(v_a_3584_);
if (v_isSharedCheck_3644_ == 0)
{
v___x_3587_ = v_a_3584_;
v_isShared_3588_ = v_isSharedCheck_3644_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_val_3585_);
lean_dec(v_a_3584_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3644_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3589_; 
v___x_3589_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3585_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
if (lean_obj_tag(v___x_3589_) == 0)
{
lean_object* v_a_3590_; 
v_a_3590_ = lean_ctor_get(v___x_3589_, 0);
lean_inc(v_a_3590_);
lean_dec_ref_known(v___x_3589_, 1);
if (lean_obj_tag(v_a_3590_) == 1)
{
lean_object* v_val_3591_; lean_object* v___x_3593_; uint8_t v_isShared_3594_; uint8_t v_isSharedCheck_3635_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec_ref(v_config_3028_);
v_val_3591_ = lean_ctor_get(v_a_3590_, 0);
v_isSharedCheck_3635_ = !lean_is_exclusive(v_a_3590_);
if (v_isSharedCheck_3635_ == 0)
{
v___x_3593_ = v_a_3590_;
v_isShared_3594_ = v_isSharedCheck_3635_;
goto v_resetjp_3592_;
}
else
{
lean_inc(v_val_3591_);
lean_dec(v_a_3590_);
v___x_3593_ = lean_box(0);
v_isShared_3594_ = v_isSharedCheck_3635_;
goto v_resetjp_3592_;
}
v_resetjp_3592_:
{
lean_object* v___x_3595_; 
lean_inc(v_mvarId_3029_);
v___x_3595_ = l_Lean_MVarId_getType(v_mvarId_3029_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
if (lean_obj_tag(v___x_3595_) == 0)
{
lean_object* v_a_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; lean_object* v___x_3599_; lean_object* v___x_3600_; 
v_a_3596_ = lean_ctor_get(v___x_3595_, 0);
lean_inc(v_a_3596_);
lean_dec_ref_known(v___x_3595_, 1);
v___x_3597_ = l_Lean_LocalDecl_toExpr(v_val_3060_);
v___x_3598_ = l_Lean_mkFVar(v_val_3591_);
v___x_3599_ = l_Lean_Expr_app___override(v___x_3597_, v___x_3598_);
v___x_3600_ = l_Lean_Meta_mkFalseElim(v_a_3596_, v___x_3599_, v___y_3034_, v___y_3035_, v___y_3036_, v___y_3037_);
if (lean_obj_tag(v___x_3600_) == 0)
{
lean_object* v_a_3601_; lean_object* v___x_3602_; 
v_a_3601_ = lean_ctor_get(v___x_3600_, 0);
lean_inc(v_a_3601_);
lean_dec_ref_known(v___x_3600_, 1);
v___x_3602_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3029_, v_a_3601_, v___y_3035_);
if (lean_obj_tag(v___x_3602_) == 0)
{
lean_object* v___x_3603_; lean_object* v___x_3605_; 
lean_dec_ref_known(v___x_3602_, 1);
v___x_3603_ = lean_box(v___x_3039_);
if (v_isShared_3594_ == 0)
{
lean_ctor_set(v___x_3593_, 0, v___x_3603_);
v___x_3605_ = v___x_3593_;
goto v_reusejp_3604_;
}
else
{
lean_object* v_reuseFailAlloc_3610_; 
v_reuseFailAlloc_3610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3610_, 0, v___x_3603_);
v___x_3605_ = v_reuseFailAlloc_3610_;
goto v_reusejp_3604_;
}
v_reusejp_3604_:
{
lean_object* v___x_3606_; lean_object* v___x_3608_; 
v___x_3606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___x_3605_);
lean_ctor_set(v___x_3606_, 1, v___x_3064_);
if (v_isShared_3588_ == 0)
{
lean_ctor_set_tag(v___x_3587_, 0);
lean_ctor_set(v___x_3587_, 0, v___x_3606_);
v___x_3608_ = v___x_3587_;
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
v_a_3046_ = v___x_3608_;
goto v___jp_3045_;
}
}
}
else
{
lean_object* v_a_3611_; lean_object* v___x_3613_; uint8_t v_isShared_3614_; uint8_t v_isSharedCheck_3618_; 
lean_del_object(v___x_3593_);
lean_del_object(v___x_3587_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
v_a_3611_ = lean_ctor_get(v___x_3602_, 0);
v_isSharedCheck_3618_ = !lean_is_exclusive(v___x_3602_);
if (v_isSharedCheck_3618_ == 0)
{
v___x_3613_ = v___x_3602_;
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
else
{
lean_inc(v_a_3611_);
lean_dec(v___x_3602_);
v___x_3613_ = lean_box(0);
v_isShared_3614_ = v_isSharedCheck_3618_;
goto v_resetjp_3612_;
}
v_resetjp_3612_:
{
lean_object* v___x_3616_; 
if (v_isShared_3614_ == 0)
{
v___x_3616_ = v___x_3613_;
goto v_reusejp_3615_;
}
else
{
lean_object* v_reuseFailAlloc_3617_; 
v_reuseFailAlloc_3617_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
v___x_3616_ = v_reuseFailAlloc_3617_;
goto v_reusejp_3615_;
}
v_reusejp_3615_:
{
return v___x_3616_;
}
}
}
}
else
{
lean_object* v_a_3619_; lean_object* v___x_3621_; uint8_t v_isShared_3622_; uint8_t v_isSharedCheck_3626_; 
lean_del_object(v___x_3593_);
lean_del_object(v___x_3587_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3619_ = lean_ctor_get(v___x_3600_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v___x_3600_);
if (v_isSharedCheck_3626_ == 0)
{
v___x_3621_ = v___x_3600_;
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
else
{
lean_inc(v_a_3619_);
lean_dec(v___x_3600_);
v___x_3621_ = lean_box(0);
v_isShared_3622_ = v_isSharedCheck_3626_;
goto v_resetjp_3620_;
}
v_resetjp_3620_:
{
lean_object* v___x_3624_; 
if (v_isShared_3622_ == 0)
{
v___x_3624_ = v___x_3621_;
goto v_reusejp_3623_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_a_3619_);
v___x_3624_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3623_;
}
v_reusejp_3623_:
{
return v___x_3624_;
}
}
}
}
else
{
lean_object* v_a_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3634_; 
lean_del_object(v___x_3593_);
lean_dec(v_val_3591_);
lean_del_object(v___x_3587_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3627_ = lean_ctor_get(v___x_3595_, 0);
v_isSharedCheck_3634_ = !lean_is_exclusive(v___x_3595_);
if (v_isSharedCheck_3634_ == 0)
{
v___x_3629_ = v___x_3595_;
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_a_3627_);
lean_dec(v___x_3595_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3634_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3632_; 
if (v_isShared_3630_ == 0)
{
v___x_3632_ = v___x_3629_;
goto v_reusejp_3631_;
}
else
{
lean_object* v_reuseFailAlloc_3633_; 
v_reuseFailAlloc_3633_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_a_3627_);
v___x_3632_ = v_reuseFailAlloc_3633_;
goto v_reusejp_3631_;
}
v_reusejp_3631_:
{
return v___x_3632_;
}
}
}
}
}
else
{
lean_dec(v_a_3590_);
lean_del_object(v___x_3587_);
v___y_3447_ = v___y_3034_;
v___y_3448_ = v___y_3035_;
v___y_3449_ = v___y_3036_;
v___y_3450_ = v___y_3037_;
goto v___jp_3446_;
}
}
else
{
lean_object* v_a_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3643_; 
lean_del_object(v___x_3587_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3636_ = lean_ctor_get(v___x_3589_, 0);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3589_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3638_ = v___x_3589_;
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_a_3636_);
lean_dec(v___x_3589_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3643_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3641_; 
if (v_isShared_3639_ == 0)
{
v___x_3641_ = v___x_3638_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v_a_3636_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
}
}
else
{
lean_dec(v_a_3584_);
v___y_3447_ = v___y_3034_;
v___y_3448_ = v___y_3035_;
v___y_3449_ = v___y_3036_;
v___y_3450_ = v___y_3037_;
goto v___jp_3446_;
}
}
else
{
lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3645_ = lean_ctor_get(v___x_3583_, 0);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3583_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3583_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_dec(v___x_3583_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
v___jp_3095_:
{
uint8_t v_genDiseq_3102_; 
v_genDiseq_3102_ = lean_ctor_get_uint8(v_config_3028_, sizeof(void*)*1 + 2);
if (v_genDiseq_3102_ == 0)
{
lean_dec_ref(v___x_3094_);
v___y_3067_ = v___y_3096_;
v___y_3068_ = v___y_3097_;
v___y_3069_ = v___y_3098_;
v___y_3070_ = v___y_3099_;
v___y_3071_ = v___y_3100_;
v___y_3072_ = v___y_3101_;
goto v___jp_3066_;
}
else
{
uint8_t v___x_3103_; 
v___x_3103_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3094_);
if (v___x_3103_ == 0)
{
v___y_3067_ = v___y_3096_;
v___y_3068_ = v___y_3097_;
v___y_3069_ = v___y_3098_;
v___y_3070_ = v___y_3099_;
v___y_3071_ = v___y_3100_;
v___y_3072_ = v___y_3101_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3104_; 
lean_inc(v_val_3060_);
lean_inc(v_mvarId_3029_);
v___x_3104_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3029_, v_val_3060_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; uint8_t v___x_3106_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3106_ = lean_unbox(v_a_3105_);
lean_dec(v_a_3105_);
if (v___x_3106_ == 0)
{
v___y_3067_ = v___y_3096_;
v___y_3068_ = v___y_3097_;
v___y_3069_ = v___y_3098_;
v___y_3070_ = v___y_3099_;
v___y_3071_ = v___y_3100_;
v___y_3072_ = v___y_3101_;
goto v___jp_3066_;
}
else
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v___x_3107_ = lean_box(v___x_3039_);
v___x_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3108_, 0, v___x_3107_);
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
lean_ctor_set(v___x_3109_, 1, v___x_3064_);
v___x_3110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
v_a_3046_ = v___x_3110_;
goto v___jp_3045_;
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3111_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3104_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3104_);
v___x_3113_ = lean_box(0);
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
v_resetjp_3112_:
{
lean_object* v___x_3116_; 
if (v_isShared_3114_ == 0)
{
v___x_3116_ = v___x_3113_;
goto v_reusejp_3115_;
}
else
{
lean_object* v_reuseFailAlloc_3117_; 
v_reuseFailAlloc_3117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3117_, 0, v_a_3111_);
v___x_3116_ = v_reuseFailAlloc_3117_;
goto v_reusejp_3115_;
}
v_reusejp_3115_:
{
return v___x_3116_;
}
}
}
}
}
}
v___jp_3119_:
{
uint8_t v___x_3127_; 
v___x_3127_ = l_Lean_Exception_isInterrupt(v_a_3126_);
if (v___x_3127_ == 0)
{
uint8_t v___x_3128_; 
lean_inc_ref(v_a_3126_);
v___x_3128_ = l_Lean_Exception_isRuntime(v_a_3126_);
if (v___x_3128_ == 0)
{
lean_dec_ref(v_a_3126_);
v___y_3096_ = v___y_3123_;
v___y_3097_ = v___y_3124_;
v___y_3098_ = v___y_3122_;
v___y_3099_ = v___y_3125_;
v___y_3100_ = v___y_3121_;
v___y_3101_ = v___y_3120_;
goto v___jp_3095_;
}
else
{
lean_object* v___x_3129_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v___x_3129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3129_, 0, v_a_3126_);
return v___x_3129_;
}
}
else
{
lean_object* v___x_3130_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v___x_3130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3130_, 0, v_a_3126_);
return v___x_3130_;
}
}
v___jp_3131_:
{
if (lean_obj_tag(v___y_3139_) == 0)
{
lean_object* v_a_3140_; lean_object* v___x_3141_; uint8_t v___x_3142_; 
v_a_3140_ = lean_ctor_get(v___y_3139_, 0);
lean_inc(v_a_3140_);
lean_dec_ref_known(v___y_3139_, 1);
v___x_3141_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3142_ = l_Lean_Expr_isConstOf(v_a_3140_, v___x_3141_);
lean_dec(v_a_3140_);
if (v___x_3142_ == 0)
{
lean_dec_ref(v___y_3132_);
v___y_3096_ = v___y_3136_;
v___y_3097_ = v___y_3137_;
v___y_3098_ = v___y_3135_;
v___y_3099_ = v___y_3138_;
v___y_3100_ = v___y_3134_;
v___y_3101_ = v___y_3133_;
goto v___jp_3095_;
}
else
{
lean_object* v___x_3143_; 
lean_inc_ref(v___y_3132_);
v___x_3143_ = l_Lean_Meta_mkEqRefl(v___y_3132_, v___y_3135_, v___y_3138_, v___y_3134_, v___y_3133_);
if (lean_obj_tag(v___x_3143_) == 0)
{
lean_object* v_a_3144_; lean_object* v___x_3145_; lean_object* v_dummy_3146_; lean_object* v_nargs_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; 
v_a_3144_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3144_);
lean_dec_ref_known(v___x_3143_, 1);
v___x_3145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3146_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3147_ = l_Lean_Expr_getAppNumArgs(v___y_3132_);
lean_inc(v_nargs_3147_);
v___x_3148_ = lean_mk_array(v_nargs_3147_, v_dummy_3146_);
v___x_3149_ = lean_unsigned_to_nat(1u);
v___x_3150_ = lean_nat_sub(v_nargs_3147_, v___x_3149_);
lean_dec(v_nargs_3147_);
v___x_3151_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3132_, v___x_3148_, v___x_3150_);
v___x_3152_ = lean_array_push(v___x_3151_, v_a_3144_);
v___x_3153_ = l_Lean_mkAppN(v___x_3145_, v___x_3152_);
lean_dec_ref(v___x_3152_);
lean_inc(v_mvarId_3029_);
v___x_3154_ = l_Lean_MVarId_getType(v_mvarId_3029_, v___y_3135_, v___y_3138_, v___y_3134_, v___y_3133_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v___x_3156_; lean_object* v___x_3157_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
lean_dec_ref_known(v___x_3154_, 1);
lean_inc(v_val_3060_);
v___x_3156_ = l_Lean_LocalDecl_toExpr(v_val_3060_);
v___x_3157_ = l_Lean_Meta_mkAbsurd(v_a_3155_, v___x_3156_, v___x_3153_, v___y_3135_, v___y_3138_, v___y_3134_, v___y_3133_);
if (lean_obj_tag(v___x_3157_) == 0)
{
lean_object* v_a_3158_; lean_object* v___x_3160_; uint8_t v_isShared_3161_; uint8_t v_isSharedCheck_3177_; 
v_a_3158_ = lean_ctor_get(v___x_3157_, 0);
v_isSharedCheck_3177_ = !lean_is_exclusive(v___x_3157_);
if (v_isSharedCheck_3177_ == 0)
{
v___x_3160_ = v___x_3157_;
v_isShared_3161_ = v_isSharedCheck_3177_;
goto v_resetjp_3159_;
}
else
{
lean_inc(v_a_3158_);
lean_dec(v___x_3157_);
v___x_3160_ = lean_box(0);
v_isShared_3161_ = v_isSharedCheck_3177_;
goto v_resetjp_3159_;
}
v_resetjp_3159_:
{
lean_object* v___x_3162_; 
lean_inc(v_mvarId_3029_);
v___x_3162_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3029_, v_a_3158_, v___y_3138_);
if (lean_obj_tag(v___x_3162_) == 0)
{
lean_object* v___x_3164_; uint8_t v_isShared_3165_; uint8_t v_isSharedCheck_3174_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___x_3162_);
if (v_isSharedCheck_3174_ == 0)
{
lean_object* v_unused_3175_; 
v_unused_3175_ = lean_ctor_get(v___x_3162_, 0);
lean_dec(v_unused_3175_);
v___x_3164_ = v___x_3162_;
v_isShared_3165_ = v_isSharedCheck_3174_;
goto v_resetjp_3163_;
}
else
{
lean_dec(v___x_3162_);
v___x_3164_ = lean_box(0);
v_isShared_3165_ = v_isSharedCheck_3174_;
goto v_resetjp_3163_;
}
v_resetjp_3163_:
{
lean_object* v___x_3166_; lean_object* v___x_3168_; 
v___x_3166_ = lean_box(v___x_3039_);
if (v_isShared_3165_ == 0)
{
lean_ctor_set_tag(v___x_3164_, 1);
lean_ctor_set(v___x_3164_, 0, v___x_3166_);
v___x_3168_ = v___x_3164_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v___x_3166_);
v___x_3168_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3171_; 
v___x_3169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3169_, 0, v___x_3168_);
lean_ctor_set(v___x_3169_, 1, v___x_3064_);
if (v_isShared_3161_ == 0)
{
lean_ctor_set(v___x_3160_, 0, v___x_3169_);
v___x_3171_ = v___x_3160_;
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
v_a_3046_ = v___x_3171_;
goto v___jp_3045_;
}
}
}
}
else
{
lean_object* v_a_3176_; 
lean_del_object(v___x_3160_);
v_a_3176_ = lean_ctor_get(v___x_3162_, 0);
lean_inc(v_a_3176_);
lean_dec_ref_known(v___x_3162_, 1);
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3134_;
v___y_3122_ = v___y_3135_;
v___y_3123_ = v___y_3136_;
v___y_3124_ = v___y_3137_;
v___y_3125_ = v___y_3138_;
v_a_3126_ = v_a_3176_;
goto v___jp_3119_;
}
}
}
else
{
lean_object* v_a_3178_; 
v_a_3178_ = lean_ctor_get(v___x_3157_, 0);
lean_inc(v_a_3178_);
lean_dec_ref_known(v___x_3157_, 1);
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3134_;
v___y_3122_ = v___y_3135_;
v___y_3123_ = v___y_3136_;
v___y_3124_ = v___y_3137_;
v___y_3125_ = v___y_3138_;
v_a_3126_ = v_a_3178_;
goto v___jp_3119_;
}
}
else
{
lean_object* v_a_3179_; 
lean_dec_ref(v___x_3153_);
v_a_3179_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3179_);
lean_dec_ref_known(v___x_3154_, 1);
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3134_;
v___y_3122_ = v___y_3135_;
v___y_3123_ = v___y_3136_;
v___y_3124_ = v___y_3137_;
v___y_3125_ = v___y_3138_;
v_a_3126_ = v_a_3179_;
goto v___jp_3119_;
}
}
else
{
lean_object* v_a_3180_; 
lean_dec_ref(v___y_3132_);
v_a_3180_ = lean_ctor_get(v___x_3143_, 0);
lean_inc(v_a_3180_);
lean_dec_ref_known(v___x_3143_, 1);
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3134_;
v___y_3122_ = v___y_3135_;
v___y_3123_ = v___y_3136_;
v___y_3124_ = v___y_3137_;
v___y_3125_ = v___y_3138_;
v_a_3126_ = v_a_3180_;
goto v___jp_3119_;
}
}
}
else
{
lean_object* v_a_3181_; 
lean_dec_ref(v___y_3132_);
v_a_3181_ = lean_ctor_get(v___y_3139_, 0);
lean_inc(v_a_3181_);
lean_dec_ref_known(v___y_3139_, 1);
v___y_3120_ = v___y_3133_;
v___y_3121_ = v___y_3134_;
v___y_3122_ = v___y_3135_;
v___y_3123_ = v___y_3136_;
v___y_3124_ = v___y_3137_;
v___y_3125_ = v___y_3138_;
v_a_3126_ = v_a_3181_;
goto v___jp_3119_;
}
}
v___jp_3182_:
{
uint8_t v_useDecide_3189_; 
v_useDecide_3189_ = lean_ctor_get_uint8(v_config_3028_, sizeof(void*)*1);
if (v_useDecide_3189_ == 0)
{
v___y_3096_ = v___y_3183_;
v___y_3097_ = v_isHEq_3184_;
v___y_3098_ = v___y_3185_;
v___y_3099_ = v___y_3186_;
v___y_3100_ = v___y_3187_;
v___y_3101_ = v___y_3188_;
goto v___jp_3095_;
}
else
{
uint8_t v___x_3190_; 
v___x_3190_ = l_Lean_Expr_hasFVar(v___x_3094_);
if (v___x_3190_ == 0)
{
lean_object* v___x_3191_; 
lean_inc_ref(v___x_3094_);
v___x_3191_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3094_, v___y_3186_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v_a_3192_; uint8_t v___x_3193_; 
v_a_3192_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_a_3192_);
lean_dec_ref_known(v___x_3191_, 1);
v___x_3193_ = l_Lean_Expr_hasMVar(v_a_3192_);
if (v___x_3193_ == 0)
{
uint8_t v___x_3194_; 
v___x_3194_ = l_Lean_Expr_hasFVar(v_a_3192_);
lean_dec(v_a_3192_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; 
lean_inc_ref(v___x_3094_);
v___x_3195_ = l_Lean_Meta_mkDecide(v___x_3094_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
if (lean_obj_tag(v___x_3195_) == 0)
{
lean_object* v_a_3196_; lean_object* v___x_3197_; uint8_t v_transparency_3198_; uint8_t v___x_3199_; uint8_t v___x_3200_; 
v_a_3196_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3196_);
lean_dec_ref_known(v___x_3195_, 1);
v___x_3197_ = l_Lean_Meta_Context_config(v___y_3185_);
v_transparency_3198_ = lean_ctor_get_uint8(v___x_3197_, 9);
lean_dec_ref(v___x_3197_);
v___x_3199_ = 1;
v___x_3200_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3198_, v___x_3199_);
if (v___x_3200_ == 0)
{
lean_object* v_keyedConfig_3201_; uint8_t v_trackZetaDelta_3202_; lean_object* v_zetaDeltaSet_3203_; lean_object* v_lctx_3204_; lean_object* v_localInstances_3205_; lean_object* v_defEqCtx_x3f_3206_; lean_object* v_synthPendingDepth_3207_; lean_object* v_customCanUnfoldPredicate_x3f_3208_; uint8_t v_univApprox_3209_; uint8_t v_inTypeClassResolution_3210_; uint8_t v_cacheInferType_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v_keyedConfig_3201_ = lean_ctor_get(v___y_3185_, 0);
v_trackZetaDelta_3202_ = lean_ctor_get_uint8(v___y_3185_, sizeof(void*)*7);
v_zetaDeltaSet_3203_ = lean_ctor_get(v___y_3185_, 1);
v_lctx_3204_ = lean_ctor_get(v___y_3185_, 2);
v_localInstances_3205_ = lean_ctor_get(v___y_3185_, 3);
v_defEqCtx_x3f_3206_ = lean_ctor_get(v___y_3185_, 4);
v_synthPendingDepth_3207_ = lean_ctor_get(v___y_3185_, 5);
v_customCanUnfoldPredicate_x3f_3208_ = lean_ctor_get(v___y_3185_, 6);
v_univApprox_3209_ = lean_ctor_get_uint8(v___y_3185_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3210_ = lean_ctor_get_uint8(v___y_3185_, sizeof(void*)*7 + 2);
v_cacheInferType_3211_ = lean_ctor_get_uint8(v___y_3185_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3201_);
v___x_3212_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3199_, v_keyedConfig_3201_);
lean_inc(v_customCanUnfoldPredicate_x3f_3208_);
lean_inc(v_synthPendingDepth_3207_);
lean_inc(v_defEqCtx_x3f_3206_);
lean_inc_ref(v_localInstances_3205_);
lean_inc_ref(v_lctx_3204_);
lean_inc(v_zetaDeltaSet_3203_);
v___x_3213_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v_zetaDeltaSet_3203_);
lean_ctor_set(v___x_3213_, 2, v_lctx_3204_);
lean_ctor_set(v___x_3213_, 3, v_localInstances_3205_);
lean_ctor_set(v___x_3213_, 4, v_defEqCtx_x3f_3206_);
lean_ctor_set(v___x_3213_, 5, v_synthPendingDepth_3207_);
lean_ctor_set(v___x_3213_, 6, v_customCanUnfoldPredicate_x3f_3208_);
lean_ctor_set_uint8(v___x_3213_, sizeof(void*)*7, v_trackZetaDelta_3202_);
lean_ctor_set_uint8(v___x_3213_, sizeof(void*)*7 + 1, v_univApprox_3209_);
lean_ctor_set_uint8(v___x_3213_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3210_);
lean_ctor_set_uint8(v___x_3213_, sizeof(void*)*7 + 3, v_cacheInferType_3211_);
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
lean_inc(v___y_3186_);
lean_inc(v_a_3196_);
v___x_3214_ = lean_whnf(v_a_3196_, v___x_3213_, v___y_3186_, v___y_3187_, v___y_3188_);
v___y_3132_ = v_a_3196_;
v___y_3133_ = v___y_3188_;
v___y_3134_ = v___y_3187_;
v___y_3135_ = v___y_3185_;
v___y_3136_ = v___y_3183_;
v___y_3137_ = v_isHEq_3184_;
v___y_3138_ = v___y_3186_;
v___y_3139_ = v___x_3214_;
goto v___jp_3131_;
}
else
{
lean_object* v___x_3215_; 
lean_inc(v___y_3188_);
lean_inc_ref(v___y_3187_);
lean_inc(v___y_3186_);
lean_inc_ref(v___y_3185_);
lean_inc(v_a_3196_);
v___x_3215_ = lean_whnf(v_a_3196_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
v___y_3132_ = v_a_3196_;
v___y_3133_ = v___y_3188_;
v___y_3134_ = v___y_3187_;
v___y_3135_ = v___y_3185_;
v___y_3136_ = v___y_3183_;
v___y_3137_ = v_isHEq_3184_;
v___y_3138_ = v___y_3186_;
v___y_3139_ = v___x_3215_;
goto v___jp_3131_;
}
}
else
{
lean_object* v_a_3216_; 
v_a_3216_ = lean_ctor_get(v___x_3195_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3195_, 1);
v___y_3120_ = v___y_3188_;
v___y_3121_ = v___y_3187_;
v___y_3122_ = v___y_3185_;
v___y_3123_ = v___y_3183_;
v___y_3124_ = v_isHEq_3184_;
v___y_3125_ = v___y_3186_;
v_a_3126_ = v_a_3216_;
goto v___jp_3119_;
}
}
else
{
v___y_3096_ = v___y_3183_;
v___y_3097_ = v_isHEq_3184_;
v___y_3098_ = v___y_3185_;
v___y_3099_ = v___y_3186_;
v___y_3100_ = v___y_3187_;
v___y_3101_ = v___y_3188_;
goto v___jp_3095_;
}
}
else
{
lean_dec(v_a_3192_);
v___y_3096_ = v___y_3183_;
v___y_3097_ = v_isHEq_3184_;
v___y_3098_ = v___y_3185_;
v___y_3099_ = v___y_3186_;
v___y_3100_ = v___y_3187_;
v___y_3101_ = v___y_3188_;
goto v___jp_3095_;
}
}
else
{
lean_object* v_a_3217_; lean_object* v___x_3219_; uint8_t v_isShared_3220_; uint8_t v_isSharedCheck_3224_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3217_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3224_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3224_ == 0)
{
v___x_3219_ = v___x_3191_;
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
else
{
lean_inc(v_a_3217_);
lean_dec(v___x_3191_);
v___x_3219_ = lean_box(0);
v_isShared_3220_ = v_isSharedCheck_3224_;
goto v_resetjp_3218_;
}
v_resetjp_3218_:
{
lean_object* v___x_3222_; 
if (v_isShared_3220_ == 0)
{
v___x_3222_ = v___x_3219_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3223_; 
v_reuseFailAlloc_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_a_3217_);
v___x_3222_ = v_reuseFailAlloc_3223_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
return v___x_3222_;
}
}
}
}
else
{
v___y_3096_ = v___y_3183_;
v___y_3097_ = v_isHEq_3184_;
v___y_3098_ = v___y_3185_;
v___y_3099_ = v___y_3186_;
v___y_3100_ = v___y_3187_;
v___y_3101_ = v___y_3188_;
goto v___jp_3095_;
}
}
}
v___jp_3225_:
{
lean_object* v___x_3231_; 
lean_inc_ref(v___x_3094_);
v___x_3231_ = l_Lean_Meta_matchHEq_x3f(v___x_3094_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
if (lean_obj_tag(v___x_3231_) == 0)
{
lean_object* v_a_3232_; 
v_a_3232_ = lean_ctor_get(v___x_3231_, 0);
lean_inc(v_a_3232_);
lean_dec_ref_known(v___x_3231_, 1);
if (lean_obj_tag(v_a_3232_) == 1)
{
lean_object* v_val_3233_; lean_object* v_snd_3234_; lean_object* v_snd_3235_; lean_object* v_fst_3236_; lean_object* v_fst_3237_; lean_object* v_fst_3238_; lean_object* v_snd_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3339_; 
v_val_3233_ = lean_ctor_get(v_a_3232_, 0);
lean_inc(v_val_3233_);
lean_dec_ref_known(v_a_3232_, 1);
v_snd_3234_ = lean_ctor_get(v_val_3233_, 1);
lean_inc(v_snd_3234_);
v_snd_3235_ = lean_ctor_get(v_snd_3234_, 1);
lean_inc(v_snd_3235_);
v_fst_3236_ = lean_ctor_get(v_val_3233_, 0);
lean_inc(v_fst_3236_);
lean_dec(v_val_3233_);
v_fst_3237_ = lean_ctor_get(v_snd_3234_, 0);
lean_inc(v_fst_3237_);
lean_dec(v_snd_3234_);
v_fst_3238_ = lean_ctor_get(v_snd_3235_, 0);
v_snd_3239_ = lean_ctor_get(v_snd_3235_, 1);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_snd_3235_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3241_ = v_snd_3235_;
v_isShared_3242_ = v_isSharedCheck_3339_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_snd_3239_);
lean_inc(v_fst_3238_);
lean_dec(v_snd_3235_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3339_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; 
v___x_3243_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3237_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
if (lean_obj_tag(v___x_3243_) == 0)
{
lean_object* v_a_3244_; 
v_a_3244_ = lean_ctor_get(v___x_3243_, 0);
lean_inc(v_a_3244_);
lean_dec_ref_known(v___x_3243_, 1);
if (lean_obj_tag(v_a_3244_) == 1)
{
lean_object* v_val_3245_; lean_object* v___x_3247_; uint8_t v_isShared_3248_; uint8_t v_isSharedCheck_3330_; 
v_val_3245_ = lean_ctor_get(v_a_3244_, 0);
v_isSharedCheck_3330_ = !lean_is_exclusive(v_a_3244_);
if (v_isSharedCheck_3330_ == 0)
{
v___x_3247_ = v_a_3244_;
v_isShared_3248_ = v_isSharedCheck_3330_;
goto v_resetjp_3246_;
}
else
{
lean_inc(v_val_3245_);
lean_dec(v_a_3244_);
v___x_3247_ = lean_box(0);
v_isShared_3248_ = v_isSharedCheck_3330_;
goto v_resetjp_3246_;
}
v_resetjp_3246_:
{
lean_object* v___x_3249_; 
v___x_3249_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3239_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
if (lean_obj_tag(v___x_3249_) == 0)
{
lean_object* v_a_3250_; 
v_a_3250_ = lean_ctor_get(v___x_3249_, 0);
lean_inc(v_a_3250_);
lean_dec_ref_known(v___x_3249_, 1);
if (lean_obj_tag(v_a_3250_) == 1)
{
lean_object* v_toConstantVal_3251_; lean_object* v_val_3252_; lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3321_; 
v_toConstantVal_3251_ = lean_ctor_get(v_val_3245_, 0);
lean_inc_ref(v_toConstantVal_3251_);
lean_dec(v_val_3245_);
v_val_3252_ = lean_ctor_get(v_a_3250_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v_a_3250_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3254_ = v_a_3250_;
v_isShared_3255_ = v_isSharedCheck_3321_;
goto v_resetjp_3253_;
}
else
{
lean_inc(v_val_3252_);
lean_dec(v_a_3250_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3321_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v_toConstantVal_3256_; lean_object* v_name_3257_; lean_object* v_name_3258_; uint8_t v___x_3259_; 
v_toConstantVal_3256_ = lean_ctor_get(v_val_3252_, 0);
lean_inc_ref(v_toConstantVal_3256_);
lean_dec(v_val_3252_);
v_name_3257_ = lean_ctor_get(v_toConstantVal_3251_, 0);
lean_inc(v_name_3257_);
lean_dec_ref(v_toConstantVal_3251_);
v_name_3258_ = lean_ctor_get(v_toConstantVal_3256_, 0);
lean_inc(v_name_3258_);
lean_dec_ref(v_toConstantVal_3256_);
v___x_3259_ = lean_name_eq(v_name_3257_, v_name_3258_);
lean_dec(v_name_3258_);
lean_dec(v_name_3257_);
if (v___x_3259_ == 0)
{
lean_object* v___x_3260_; 
v___x_3260_ = l_Lean_Meta_isExprDefEq(v_fst_3236_, v_fst_3238_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
if (lean_obj_tag(v___x_3260_) == 0)
{
lean_object* v_a_3261_; uint8_t v___x_3262_; 
v_a_3261_ = lean_ctor_get(v___x_3260_, 0);
lean_inc(v_a_3261_);
lean_dec_ref_known(v___x_3260_, 1);
v___x_3262_ = lean_unbox(v_a_3261_);
lean_dec(v_a_3261_);
if (v___x_3262_ == 0)
{
lean_del_object(v___x_3254_);
lean_del_object(v___x_3247_);
lean_del_object(v___x_3241_);
v___y_3183_ = v_isEq_3226_;
v_isHEq_3184_ = v___x_3039_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v___y_3228_;
v___y_3187_ = v___y_3229_;
v___y_3188_ = v___y_3230_;
goto v___jp_3182_;
}
else
{
lean_object* v___x_3263_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec_ref(v_config_3028_);
lean_inc(v_mvarId_3029_);
v___x_3263_ = l_Lean_MVarId_getType(v_mvarId_3029_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
if (lean_obj_tag(v___x_3263_) == 0)
{
lean_object* v_a_3264_; lean_object* v___x_3265_; lean_object* v___x_3266_; 
v_a_3264_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_a_3264_);
lean_dec_ref_known(v___x_3263_, 1);
v___x_3265_ = l_Lean_LocalDecl_toExpr(v_val_3060_);
v___x_3266_ = l_Lean_Meta_mkEqOfHEq(v___x_3265_, v___x_3039_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
if (lean_obj_tag(v___x_3266_) == 0)
{
lean_object* v_a_3267_; lean_object* v___x_3268_; 
v_a_3267_ = lean_ctor_get(v___x_3266_, 0);
lean_inc(v_a_3267_);
lean_dec_ref_known(v___x_3266_, 1);
v___x_3268_ = l_Lean_Meta_mkNoConfusion(v_a_3264_, v_a_3267_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3029_, v_a_3269_, v___y_3228_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v___x_3271_; lean_object* v___x_3273_; 
lean_dec_ref_known(v___x_3270_, 1);
v___x_3271_ = lean_box(v___x_3039_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 0, v___x_3271_);
v___x_3273_ = v___x_3254_;
goto v_reusejp_3272_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v___x_3271_);
v___x_3273_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3272_;
}
v_reusejp_3272_:
{
lean_object* v___x_3275_; 
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 1, v___x_3064_);
lean_ctor_set(v___x_3241_, 0, v___x_3273_);
v___x_3275_ = v___x_3241_;
goto v_reusejp_3274_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3273_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v___x_3064_);
v___x_3275_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3274_;
}
v_reusejp_3274_:
{
lean_object* v___x_3277_; 
if (v_isShared_3248_ == 0)
{
lean_ctor_set_tag(v___x_3247_, 0);
lean_ctor_set(v___x_3247_, 0, v___x_3275_);
v___x_3277_ = v___x_3247_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v___x_3275_);
v___x_3277_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
v_a_3046_ = v___x_3277_;
goto v___jp_3045_;
}
}
}
}
else
{
lean_object* v_a_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3288_; 
lean_del_object(v___x_3254_);
lean_del_object(v___x_3247_);
lean_del_object(v___x_3241_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
v_a_3281_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3288_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3288_ == 0)
{
v___x_3283_ = v___x_3270_;
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_a_3281_);
lean_dec(v___x_3270_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3288_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v___x_3286_; 
if (v_isShared_3284_ == 0)
{
v___x_3286_ = v___x_3283_;
goto v_reusejp_3285_;
}
else
{
lean_object* v_reuseFailAlloc_3287_; 
v_reuseFailAlloc_3287_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3287_, 0, v_a_3281_);
v___x_3286_ = v_reuseFailAlloc_3287_;
goto v_reusejp_3285_;
}
v_reusejp_3285_:
{
return v___x_3286_;
}
}
}
}
else
{
lean_object* v_a_3289_; lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3296_; 
lean_del_object(v___x_3254_);
lean_del_object(v___x_3247_);
lean_del_object(v___x_3241_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3289_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3296_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3296_ == 0)
{
v___x_3291_ = v___x_3268_;
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
else
{
lean_inc(v_a_3289_);
lean_dec(v___x_3268_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3296_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3294_; 
if (v_isShared_3292_ == 0)
{
v___x_3294_ = v___x_3291_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3295_; 
v_reuseFailAlloc_3295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3295_, 0, v_a_3289_);
v___x_3294_ = v_reuseFailAlloc_3295_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
return v___x_3294_;
}
}
}
}
else
{
lean_object* v_a_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3304_; 
lean_dec(v_a_3264_);
lean_del_object(v___x_3254_);
lean_del_object(v___x_3247_);
lean_del_object(v___x_3241_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3297_ = lean_ctor_get(v___x_3266_, 0);
v_isSharedCheck_3304_ = !lean_is_exclusive(v___x_3266_);
if (v_isSharedCheck_3304_ == 0)
{
v___x_3299_ = v___x_3266_;
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_a_3297_);
lean_dec(v___x_3266_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3304_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3302_; 
if (v_isShared_3300_ == 0)
{
v___x_3302_ = v___x_3299_;
goto v_reusejp_3301_;
}
else
{
lean_object* v_reuseFailAlloc_3303_; 
v_reuseFailAlloc_3303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3303_, 0, v_a_3297_);
v___x_3302_ = v_reuseFailAlloc_3303_;
goto v_reusejp_3301_;
}
v_reusejp_3301_:
{
return v___x_3302_;
}
}
}
}
else
{
lean_object* v_a_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3312_; 
lean_del_object(v___x_3254_);
lean_del_object(v___x_3247_);
lean_del_object(v___x_3241_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3305_ = lean_ctor_get(v___x_3263_, 0);
v_isSharedCheck_3312_ = !lean_is_exclusive(v___x_3263_);
if (v_isSharedCheck_3312_ == 0)
{
v___x_3307_ = v___x_3263_;
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
else
{
lean_inc(v_a_3305_);
lean_dec(v___x_3263_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3312_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3310_; 
if (v_isShared_3308_ == 0)
{
v___x_3310_ = v___x_3307_;
goto v_reusejp_3309_;
}
else
{
lean_object* v_reuseFailAlloc_3311_; 
v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3311_, 0, v_a_3305_);
v___x_3310_ = v_reuseFailAlloc_3311_;
goto v_reusejp_3309_;
}
v_reusejp_3309_:
{
return v___x_3310_;
}
}
}
}
}
else
{
lean_object* v_a_3313_; lean_object* v___x_3315_; uint8_t v_isShared_3316_; uint8_t v_isSharedCheck_3320_; 
lean_del_object(v___x_3254_);
lean_del_object(v___x_3247_);
lean_del_object(v___x_3241_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3313_ = lean_ctor_get(v___x_3260_, 0);
v_isSharedCheck_3320_ = !lean_is_exclusive(v___x_3260_);
if (v_isSharedCheck_3320_ == 0)
{
v___x_3315_ = v___x_3260_;
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
else
{
lean_inc(v_a_3313_);
lean_dec(v___x_3260_);
v___x_3315_ = lean_box(0);
v_isShared_3316_ = v_isSharedCheck_3320_;
goto v_resetjp_3314_;
}
v_resetjp_3314_:
{
lean_object* v___x_3318_; 
if (v_isShared_3316_ == 0)
{
v___x_3318_ = v___x_3315_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v_a_3313_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
return v___x_3318_;
}
}
}
}
else
{
lean_del_object(v___x_3254_);
lean_del_object(v___x_3247_);
lean_del_object(v___x_3241_);
lean_dec(v_fst_3238_);
lean_dec(v_fst_3236_);
v___y_3183_ = v_isEq_3226_;
v_isHEq_3184_ = v___x_3039_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v___y_3228_;
v___y_3187_ = v___y_3229_;
v___y_3188_ = v___y_3230_;
goto v___jp_3182_;
}
}
}
else
{
lean_dec(v_a_3250_);
lean_del_object(v___x_3247_);
lean_dec(v_val_3245_);
lean_del_object(v___x_3241_);
lean_dec(v_fst_3238_);
lean_dec(v_fst_3236_);
v___y_3183_ = v_isEq_3226_;
v_isHEq_3184_ = v___x_3039_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v___y_3228_;
v___y_3187_ = v___y_3229_;
v___y_3188_ = v___y_3230_;
goto v___jp_3182_;
}
}
else
{
lean_object* v_a_3322_; lean_object* v___x_3324_; uint8_t v_isShared_3325_; uint8_t v_isSharedCheck_3329_; 
lean_del_object(v___x_3247_);
lean_dec(v_val_3245_);
lean_del_object(v___x_3241_);
lean_dec(v_fst_3238_);
lean_dec(v_fst_3236_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3322_ = lean_ctor_get(v___x_3249_, 0);
v_isSharedCheck_3329_ = !lean_is_exclusive(v___x_3249_);
if (v_isSharedCheck_3329_ == 0)
{
v___x_3324_ = v___x_3249_;
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
else
{
lean_inc(v_a_3322_);
lean_dec(v___x_3249_);
v___x_3324_ = lean_box(0);
v_isShared_3325_ = v_isSharedCheck_3329_;
goto v_resetjp_3323_;
}
v_resetjp_3323_:
{
lean_object* v___x_3327_; 
if (v_isShared_3325_ == 0)
{
v___x_3327_ = v___x_3324_;
goto v_reusejp_3326_;
}
else
{
lean_object* v_reuseFailAlloc_3328_; 
v_reuseFailAlloc_3328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3328_, 0, v_a_3322_);
v___x_3327_ = v_reuseFailAlloc_3328_;
goto v_reusejp_3326_;
}
v_reusejp_3326_:
{
return v___x_3327_;
}
}
}
}
}
else
{
lean_dec(v_a_3244_);
lean_del_object(v___x_3241_);
lean_dec(v_snd_3239_);
lean_dec(v_fst_3238_);
lean_dec(v_fst_3236_);
v___y_3183_ = v_isEq_3226_;
v_isHEq_3184_ = v___x_3039_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v___y_3228_;
v___y_3187_ = v___y_3229_;
v___y_3188_ = v___y_3230_;
goto v___jp_3182_;
}
}
else
{
lean_object* v_a_3331_; lean_object* v___x_3333_; uint8_t v_isShared_3334_; uint8_t v_isSharedCheck_3338_; 
lean_del_object(v___x_3241_);
lean_dec(v_snd_3239_);
lean_dec(v_fst_3238_);
lean_dec(v_fst_3236_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3331_ = lean_ctor_get(v___x_3243_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v___x_3243_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3333_ = v___x_3243_;
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
else
{
lean_inc(v_a_3331_);
lean_dec(v___x_3243_);
v___x_3333_ = lean_box(0);
v_isShared_3334_ = v_isSharedCheck_3338_;
goto v_resetjp_3332_;
}
v_resetjp_3332_:
{
lean_object* v___x_3336_; 
if (v_isShared_3334_ == 0)
{
v___x_3336_ = v___x_3333_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_a_3331_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
return v___x_3336_;
}
}
}
}
}
else
{
lean_dec(v_a_3232_);
v___y_3183_ = v_isEq_3226_;
v_isHEq_3184_ = v___x_3093_;
v___y_3185_ = v___y_3227_;
v___y_3186_ = v___y_3228_;
v___y_3187_ = v___y_3229_;
v___y_3188_ = v___y_3230_;
goto v___jp_3182_;
}
}
else
{
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3340_ = lean_ctor_get(v___x_3231_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___x_3231_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___x_3231_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___x_3231_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
v___jp_3348_:
{
lean_object* v___x_3353_; 
lean_inc_ref(v___x_3094_);
v___x_3353_ = l_Lean_Meta_matchEq_x3f(v___x_3094_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3353_) == 0)
{
lean_object* v_a_3354_; 
v_a_3354_ = lean_ctor_get(v___x_3353_, 0);
lean_inc(v_a_3354_);
lean_dec_ref_known(v___x_3353_, 1);
if (lean_obj_tag(v_a_3354_) == 1)
{
lean_object* v_val_3355_; lean_object* v_snd_3356_; lean_object* v_fst_3357_; lean_object* v_snd_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3437_; 
v_val_3355_ = lean_ctor_get(v_a_3354_, 0);
lean_inc(v_val_3355_);
lean_dec_ref_known(v_a_3354_, 1);
v_snd_3356_ = lean_ctor_get(v_val_3355_, 1);
lean_inc(v_snd_3356_);
lean_dec(v_val_3355_);
v_fst_3357_ = lean_ctor_get(v_snd_3356_, 0);
v_snd_3358_ = lean_ctor_get(v_snd_3356_, 1);
v_isSharedCheck_3437_ = !lean_is_exclusive(v_snd_3356_);
if (v_isSharedCheck_3437_ == 0)
{
v___x_3360_ = v_snd_3356_;
v_isShared_3361_ = v_isSharedCheck_3437_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_snd_3358_);
lean_inc(v_fst_3357_);
lean_dec(v_snd_3356_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3437_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3362_; 
v___x_3362_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3357_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___x_3362_, 1);
if (lean_obj_tag(v_a_3363_) == 1)
{
lean_object* v_val_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3428_; 
v_val_3364_ = lean_ctor_get(v_a_3363_, 0);
v_isSharedCheck_3428_ = !lean_is_exclusive(v_a_3363_);
if (v_isSharedCheck_3428_ == 0)
{
v___x_3366_ = v_a_3363_;
v_isShared_3367_ = v_isSharedCheck_3428_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_val_3364_);
lean_dec(v_a_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3428_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; 
v___x_3368_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3358_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v_a_3369_; 
v_a_3369_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3369_);
lean_dec_ref_known(v___x_3368_, 1);
if (lean_obj_tag(v_a_3369_) == 1)
{
lean_object* v_toConstantVal_3370_; lean_object* v_val_3371_; lean_object* v___x_3373_; uint8_t v_isShared_3374_; uint8_t v_isSharedCheck_3419_; 
v_toConstantVal_3370_ = lean_ctor_get(v_val_3364_, 0);
lean_inc_ref(v_toConstantVal_3370_);
lean_dec(v_val_3364_);
v_val_3371_ = lean_ctor_get(v_a_3369_, 0);
v_isSharedCheck_3419_ = !lean_is_exclusive(v_a_3369_);
if (v_isSharedCheck_3419_ == 0)
{
v___x_3373_ = v_a_3369_;
v_isShared_3374_ = v_isSharedCheck_3419_;
goto v_resetjp_3372_;
}
else
{
lean_inc(v_val_3371_);
lean_dec(v_a_3369_);
v___x_3373_ = lean_box(0);
v_isShared_3374_ = v_isSharedCheck_3419_;
goto v_resetjp_3372_;
}
v_resetjp_3372_:
{
lean_object* v_toConstantVal_3375_; lean_object* v_name_3376_; lean_object* v_name_3377_; uint8_t v___x_3378_; 
v_toConstantVal_3375_ = lean_ctor_get(v_val_3371_, 0);
lean_inc_ref(v_toConstantVal_3375_);
lean_dec(v_val_3371_);
v_name_3376_ = lean_ctor_get(v_toConstantVal_3370_, 0);
lean_inc(v_name_3376_);
lean_dec_ref(v_toConstantVal_3370_);
v_name_3377_ = lean_ctor_get(v_toConstantVal_3375_, 0);
lean_inc(v_name_3377_);
lean_dec_ref(v_toConstantVal_3375_);
v___x_3378_ = lean_name_eq(v_name_3376_, v_name_3377_);
lean_dec(v_name_3377_);
lean_dec(v_name_3376_);
if (v___x_3378_ == 0)
{
lean_object* v___x_3379_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec_ref(v_config_3028_);
lean_inc(v_mvarId_3029_);
v___x_3379_ = l_Lean_MVarId_getType(v_mvarId_3029_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3379_) == 0)
{
lean_object* v_a_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; 
v_a_3380_ = lean_ctor_get(v___x_3379_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3379_, 1);
v___x_3381_ = l_Lean_LocalDecl_toExpr(v_val_3060_);
v___x_3382_ = l_Lean_Meta_mkNoConfusion(v_a_3380_, v___x_3381_, v___y_3349_, v___y_3350_, v___y_3351_, v___y_3352_);
if (lean_obj_tag(v___x_3382_) == 0)
{
lean_object* v_a_3383_; lean_object* v___x_3384_; 
v_a_3383_ = lean_ctor_get(v___x_3382_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3382_, 1);
v___x_3384_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3029_, v_a_3383_, v___y_3350_);
if (lean_obj_tag(v___x_3384_) == 0)
{
lean_object* v___x_3385_; lean_object* v___x_3387_; 
lean_dec_ref_known(v___x_3384_, 1);
v___x_3385_ = lean_box(v___x_3039_);
if (v_isShared_3374_ == 0)
{
lean_ctor_set(v___x_3373_, 0, v___x_3385_);
v___x_3387_ = v___x_3373_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3394_; 
v_reuseFailAlloc_3394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3394_, 0, v___x_3385_);
v___x_3387_ = v_reuseFailAlloc_3394_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
lean_object* v___x_3389_; 
if (v_isShared_3361_ == 0)
{
lean_ctor_set(v___x_3360_, 1, v___x_3064_);
lean_ctor_set(v___x_3360_, 0, v___x_3387_);
v___x_3389_ = v___x_3360_;
goto v_reusejp_3388_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v___x_3387_);
lean_ctor_set(v_reuseFailAlloc_3393_, 1, v___x_3064_);
v___x_3389_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3388_;
}
v_reusejp_3388_:
{
lean_object* v___x_3391_; 
if (v_isShared_3367_ == 0)
{
lean_ctor_set_tag(v___x_3366_, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3389_);
v___x_3391_ = v___x_3366_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3392_; 
v_reuseFailAlloc_3392_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3392_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3392_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
v_a_3046_ = v___x_3391_;
goto v___jp_3045_;
}
}
}
}
else
{
lean_object* v_a_3395_; lean_object* v___x_3397_; uint8_t v_isShared_3398_; uint8_t v_isSharedCheck_3402_; 
lean_del_object(v___x_3373_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3360_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
v_a_3395_ = lean_ctor_get(v___x_3384_, 0);
v_isSharedCheck_3402_ = !lean_is_exclusive(v___x_3384_);
if (v_isSharedCheck_3402_ == 0)
{
v___x_3397_ = v___x_3384_;
v_isShared_3398_ = v_isSharedCheck_3402_;
goto v_resetjp_3396_;
}
else
{
lean_inc(v_a_3395_);
lean_dec(v___x_3384_);
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
else
{
lean_object* v_a_3403_; lean_object* v___x_3405_; uint8_t v_isShared_3406_; uint8_t v_isSharedCheck_3410_; 
lean_del_object(v___x_3373_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3360_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3403_ = lean_ctor_get(v___x_3382_, 0);
v_isSharedCheck_3410_ = !lean_is_exclusive(v___x_3382_);
if (v_isSharedCheck_3410_ == 0)
{
v___x_3405_ = v___x_3382_;
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
else
{
lean_inc(v_a_3403_);
lean_dec(v___x_3382_);
v___x_3405_ = lean_box(0);
v_isShared_3406_ = v_isSharedCheck_3410_;
goto v_resetjp_3404_;
}
v_resetjp_3404_:
{
lean_object* v___x_3408_; 
if (v_isShared_3406_ == 0)
{
v___x_3408_ = v___x_3405_;
goto v_reusejp_3407_;
}
else
{
lean_object* v_reuseFailAlloc_3409_; 
v_reuseFailAlloc_3409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3409_, 0, v_a_3403_);
v___x_3408_ = v_reuseFailAlloc_3409_;
goto v_reusejp_3407_;
}
v_reusejp_3407_:
{
return v___x_3408_;
}
}
}
}
else
{
lean_object* v_a_3411_; lean_object* v___x_3413_; uint8_t v_isShared_3414_; uint8_t v_isSharedCheck_3418_; 
lean_del_object(v___x_3373_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3360_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3411_ = lean_ctor_get(v___x_3379_, 0);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3379_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3413_ = v___x_3379_;
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
else
{
lean_inc(v_a_3411_);
lean_dec(v___x_3379_);
v___x_3413_ = lean_box(0);
v_isShared_3414_ = v_isSharedCheck_3418_;
goto v_resetjp_3412_;
}
v_resetjp_3412_:
{
lean_object* v___x_3416_; 
if (v_isShared_3414_ == 0)
{
v___x_3416_ = v___x_3413_;
goto v_reusejp_3415_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_a_3411_);
v___x_3416_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3415_;
}
v_reusejp_3415_:
{
return v___x_3416_;
}
}
}
}
else
{
lean_del_object(v___x_3373_);
lean_del_object(v___x_3366_);
lean_del_object(v___x_3360_);
v_isEq_3226_ = v___x_3039_;
v___y_3227_ = v___y_3349_;
v___y_3228_ = v___y_3350_;
v___y_3229_ = v___y_3351_;
v___y_3230_ = v___y_3352_;
goto v___jp_3225_;
}
}
}
else
{
lean_dec(v_a_3369_);
lean_del_object(v___x_3366_);
lean_dec(v_val_3364_);
lean_del_object(v___x_3360_);
v_isEq_3226_ = v___x_3039_;
v___y_3227_ = v___y_3349_;
v___y_3228_ = v___y_3350_;
v___y_3229_ = v___y_3351_;
v___y_3230_ = v___y_3352_;
goto v___jp_3225_;
}
}
else
{
lean_object* v_a_3420_; lean_object* v___x_3422_; uint8_t v_isShared_3423_; uint8_t v_isSharedCheck_3427_; 
lean_del_object(v___x_3366_);
lean_dec(v_val_3364_);
lean_del_object(v___x_3360_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3420_ = lean_ctor_get(v___x_3368_, 0);
v_isSharedCheck_3427_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3427_ == 0)
{
v___x_3422_ = v___x_3368_;
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
else
{
lean_inc(v_a_3420_);
lean_dec(v___x_3368_);
v___x_3422_ = lean_box(0);
v_isShared_3423_ = v_isSharedCheck_3427_;
goto v_resetjp_3421_;
}
v_resetjp_3421_:
{
lean_object* v___x_3425_; 
if (v_isShared_3423_ == 0)
{
v___x_3425_ = v___x_3422_;
goto v_reusejp_3424_;
}
else
{
lean_object* v_reuseFailAlloc_3426_; 
v_reuseFailAlloc_3426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3426_, 0, v_a_3420_);
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
else
{
lean_dec(v_a_3363_);
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
v_isEq_3226_ = v___x_3039_;
v___y_3227_ = v___y_3349_;
v___y_3228_ = v___y_3350_;
v___y_3229_ = v___y_3351_;
v___y_3230_ = v___y_3352_;
goto v___jp_3225_;
}
}
else
{
lean_object* v_a_3429_; lean_object* v___x_3431_; uint8_t v_isShared_3432_; uint8_t v_isSharedCheck_3436_; 
lean_del_object(v___x_3360_);
lean_dec(v_snd_3358_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3429_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3436_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3436_ == 0)
{
v___x_3431_ = v___x_3362_;
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
else
{
lean_inc(v_a_3429_);
lean_dec(v___x_3362_);
v___x_3431_ = lean_box(0);
v_isShared_3432_ = v_isSharedCheck_3436_;
goto v_resetjp_3430_;
}
v_resetjp_3430_:
{
lean_object* v___x_3434_; 
if (v_isShared_3432_ == 0)
{
v___x_3434_ = v___x_3431_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3435_; 
v_reuseFailAlloc_3435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3435_, 0, v_a_3429_);
v___x_3434_ = v_reuseFailAlloc_3435_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
return v___x_3434_;
}
}
}
}
}
else
{
lean_dec(v_a_3354_);
v_isEq_3226_ = v___x_3093_;
v___y_3227_ = v___y_3349_;
v___y_3228_ = v___y_3350_;
v___y_3229_ = v___y_3351_;
v___y_3230_ = v___y_3352_;
goto v___jp_3225_;
}
}
else
{
lean_object* v_a_3438_; lean_object* v___x_3440_; uint8_t v_isShared_3441_; uint8_t v_isSharedCheck_3445_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3438_ = lean_ctor_get(v___x_3353_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3353_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3440_ = v___x_3353_;
v_isShared_3441_ = v_isSharedCheck_3445_;
goto v_resetjp_3439_;
}
else
{
lean_inc(v_a_3438_);
lean_dec(v___x_3353_);
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
v___jp_3446_:
{
lean_object* v___x_3451_; 
lean_inc_ref(v___x_3094_);
v___x_3451_ = l_Lean_refutableHasNotBit_x3f(v___x_3094_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
if (lean_obj_tag(v_a_3452_) == 1)
{
lean_object* v_val_3453_; lean_object* v___x_3455_; uint8_t v_isShared_3456_; uint8_t v_isSharedCheck_3493_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec_ref(v_config_3028_);
v_val_3453_ = lean_ctor_get(v_a_3452_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v_a_3452_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3455_ = v_a_3452_;
v_isShared_3456_ = v_isSharedCheck_3493_;
goto v_resetjp_3454_;
}
else
{
lean_inc(v_val_3453_);
lean_dec(v_a_3452_);
v___x_3455_ = lean_box(0);
v_isShared_3456_ = v_isSharedCheck_3493_;
goto v_resetjp_3454_;
}
v_resetjp_3454_:
{
lean_object* v___x_3457_; 
lean_inc(v_mvarId_3029_);
v___x_3457_ = l_Lean_MVarId_getType(v_mvarId_3029_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; lean_object* v___x_3460_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = l_Lean_LocalDecl_toExpr(v_val_3060_);
v___x_3460_ = l_Lean_Meta_mkAbsurd(v_a_3458_, v_val_3453_, v___x_3459_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; lean_object* v___x_3462_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v___x_3462_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3029_, v_a_3461_, v___y_3448_);
if (lean_obj_tag(v___x_3462_) == 0)
{
lean_object* v___x_3463_; lean_object* v___x_3465_; 
lean_dec_ref_known(v___x_3462_, 1);
v___x_3463_ = lean_box(v___x_3039_);
if (v_isShared_3456_ == 0)
{
lean_ctor_set(v___x_3455_, 0, v___x_3463_);
v___x_3465_ = v___x_3455_;
goto v_reusejp_3464_;
}
else
{
lean_object* v_reuseFailAlloc_3468_; 
v_reuseFailAlloc_3468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3463_);
v___x_3465_ = v_reuseFailAlloc_3468_;
goto v_reusejp_3464_;
}
v_reusejp_3464_:
{
lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3466_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3466_, 0, v___x_3465_);
lean_ctor_set(v___x_3466_, 1, v___x_3064_);
v___x_3467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
v_a_3046_ = v___x_3467_;
goto v___jp_3045_;
}
}
else
{
lean_object* v_a_3469_; lean_object* v___x_3471_; uint8_t v_isShared_3472_; uint8_t v_isSharedCheck_3476_; 
lean_del_object(v___x_3455_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
v_a_3469_ = lean_ctor_get(v___x_3462_, 0);
v_isSharedCheck_3476_ = !lean_is_exclusive(v___x_3462_);
if (v_isSharedCheck_3476_ == 0)
{
v___x_3471_ = v___x_3462_;
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
else
{
lean_inc(v_a_3469_);
lean_dec(v___x_3462_);
v___x_3471_ = lean_box(0);
v_isShared_3472_ = v_isSharedCheck_3476_;
goto v_resetjp_3470_;
}
v_resetjp_3470_:
{
lean_object* v___x_3474_; 
if (v_isShared_3472_ == 0)
{
v___x_3474_ = v___x_3471_;
goto v_reusejp_3473_;
}
else
{
lean_object* v_reuseFailAlloc_3475_; 
v_reuseFailAlloc_3475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3475_, 0, v_a_3469_);
v___x_3474_ = v_reuseFailAlloc_3475_;
goto v_reusejp_3473_;
}
v_reusejp_3473_:
{
return v___x_3474_;
}
}
}
}
else
{
lean_object* v_a_3477_; lean_object* v___x_3479_; uint8_t v_isShared_3480_; uint8_t v_isSharedCheck_3484_; 
lean_del_object(v___x_3455_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3477_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3484_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3484_ == 0)
{
v___x_3479_ = v___x_3460_;
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
else
{
lean_inc(v_a_3477_);
lean_dec(v___x_3460_);
v___x_3479_ = lean_box(0);
v_isShared_3480_ = v_isSharedCheck_3484_;
goto v_resetjp_3478_;
}
v_resetjp_3478_:
{
lean_object* v___x_3482_; 
if (v_isShared_3480_ == 0)
{
v___x_3482_ = v___x_3479_;
goto v_reusejp_3481_;
}
else
{
lean_object* v_reuseFailAlloc_3483_; 
v_reuseFailAlloc_3483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3483_, 0, v_a_3477_);
v___x_3482_ = v_reuseFailAlloc_3483_;
goto v_reusejp_3481_;
}
v_reusejp_3481_:
{
return v___x_3482_;
}
}
}
}
else
{
lean_object* v_a_3485_; lean_object* v___x_3487_; uint8_t v_isShared_3488_; uint8_t v_isSharedCheck_3492_; 
lean_del_object(v___x_3455_);
lean_dec(v_val_3453_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3485_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3487_ = v___x_3457_;
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
else
{
lean_inc(v_a_3485_);
lean_dec(v___x_3457_);
v___x_3487_ = lean_box(0);
v_isShared_3488_ = v_isSharedCheck_3492_;
goto v_resetjp_3486_;
}
v_resetjp_3486_:
{
lean_object* v___x_3490_; 
if (v_isShared_3488_ == 0)
{
v___x_3490_ = v___x_3487_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v_a_3485_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
}
}
}
else
{
lean_object* v___x_3494_; 
lean_dec(v_a_3452_);
lean_inc_ref(v___x_3094_);
v___x_3494_ = l_Lean_Meta_matchNe_x3f(v___x_3094_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3494_) == 0)
{
lean_object* v_a_3495_; 
v_a_3495_ = lean_ctor_get(v___x_3494_, 0);
lean_inc(v_a_3495_);
lean_dec_ref_known(v___x_3494_, 1);
if (lean_obj_tag(v_a_3495_) == 1)
{
lean_object* v_val_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3566_; 
v_val_3496_ = lean_ctor_get(v_a_3495_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v_a_3495_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3498_ = v_a_3495_;
v_isShared_3499_ = v_isSharedCheck_3566_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_val_3496_);
lean_dec(v_a_3495_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3566_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v_snd_3500_; lean_object* v_fst_3501_; lean_object* v_snd_3502_; lean_object* v___x_3504_; uint8_t v_isShared_3505_; uint8_t v_isSharedCheck_3565_; 
v_snd_3500_ = lean_ctor_get(v_val_3496_, 1);
lean_inc(v_snd_3500_);
lean_dec(v_val_3496_);
v_fst_3501_ = lean_ctor_get(v_snd_3500_, 0);
v_snd_3502_ = lean_ctor_get(v_snd_3500_, 1);
v_isSharedCheck_3565_ = !lean_is_exclusive(v_snd_3500_);
if (v_isSharedCheck_3565_ == 0)
{
v___x_3504_ = v_snd_3500_;
v_isShared_3505_ = v_isSharedCheck_3565_;
goto v_resetjp_3503_;
}
else
{
lean_inc(v_snd_3502_);
lean_inc(v_fst_3501_);
lean_dec(v_snd_3500_);
v___x_3504_ = lean_box(0);
v_isShared_3505_ = v_isSharedCheck_3565_;
goto v_resetjp_3503_;
}
v_resetjp_3503_:
{
lean_object* v___x_3506_; 
lean_inc(v_fst_3501_);
v___x_3506_ = l_Lean_Meta_isExprDefEq(v_fst_3501_, v_snd_3502_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v_a_3507_; uint8_t v___x_3508_; 
v_a_3507_ = lean_ctor_get(v___x_3506_, 0);
lean_inc(v_a_3507_);
lean_dec_ref_known(v___x_3506_, 1);
v___x_3508_ = lean_unbox(v_a_3507_);
lean_dec(v_a_3507_);
if (v___x_3508_ == 0)
{
lean_del_object(v___x_3504_);
lean_dec(v_fst_3501_);
lean_del_object(v___x_3498_);
v___y_3349_ = v___y_3447_;
v___y_3350_ = v___y_3448_;
v___y_3351_ = v___y_3449_;
v___y_3352_ = v___y_3450_;
goto v___jp_3348_;
}
else
{
lean_object* v___x_3509_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec_ref(v_config_3028_);
lean_inc(v_mvarId_3029_);
v___x_3509_ = l_Lean_MVarId_getType(v_mvarId_3029_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3511_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = l_Lean_Meta_mkEqRefl(v_fst_3501_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
v___x_3513_ = l_Lean_LocalDecl_toExpr(v_val_3060_);
v___x_3514_ = l_Lean_Meta_mkAbsurd(v_a_3510_, v_a_3512_, v___x_3513_, v___y_3447_, v___y_3448_, v___y_3449_, v___y_3450_);
if (lean_obj_tag(v___x_3514_) == 0)
{
lean_object* v_a_3515_; lean_object* v___x_3516_; 
v_a_3515_ = lean_ctor_get(v___x_3514_, 0);
lean_inc(v_a_3515_);
lean_dec_ref_known(v___x_3514_, 1);
v___x_3516_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3029_, v_a_3515_, v___y_3448_);
if (lean_obj_tag(v___x_3516_) == 0)
{
lean_object* v___x_3517_; lean_object* v___x_3519_; 
lean_dec_ref_known(v___x_3516_, 1);
v___x_3517_ = lean_box(v___x_3039_);
if (v_isShared_3499_ == 0)
{
lean_ctor_set(v___x_3498_, 0, v___x_3517_);
v___x_3519_ = v___x_3498_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3521_; 
if (v_isShared_3505_ == 0)
{
lean_ctor_set(v___x_3504_, 1, v___x_3064_);
lean_ctor_set(v___x_3504_, 0, v___x_3519_);
v___x_3521_ = v___x_3504_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v___x_3519_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v___x_3064_);
v___x_3521_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3522_; 
v___x_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
v_a_3046_ = v___x_3522_;
goto v___jp_3045_;
}
}
}
else
{
lean_object* v_a_3525_; lean_object* v___x_3527_; uint8_t v_isShared_3528_; uint8_t v_isSharedCheck_3532_; 
lean_del_object(v___x_3504_);
lean_del_object(v___x_3498_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
v_a_3525_ = lean_ctor_get(v___x_3516_, 0);
v_isSharedCheck_3532_ = !lean_is_exclusive(v___x_3516_);
if (v_isSharedCheck_3532_ == 0)
{
v___x_3527_ = v___x_3516_;
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
else
{
lean_inc(v_a_3525_);
lean_dec(v___x_3516_);
v___x_3527_ = lean_box(0);
v_isShared_3528_ = v_isSharedCheck_3532_;
goto v_resetjp_3526_;
}
v_resetjp_3526_:
{
lean_object* v___x_3530_; 
if (v_isShared_3528_ == 0)
{
v___x_3530_ = v___x_3527_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v_a_3525_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
return v___x_3530_;
}
}
}
}
else
{
lean_object* v_a_3533_; lean_object* v___x_3535_; uint8_t v_isShared_3536_; uint8_t v_isSharedCheck_3540_; 
lean_del_object(v___x_3504_);
lean_del_object(v___x_3498_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3533_ = lean_ctor_get(v___x_3514_, 0);
v_isSharedCheck_3540_ = !lean_is_exclusive(v___x_3514_);
if (v_isSharedCheck_3540_ == 0)
{
v___x_3535_ = v___x_3514_;
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
else
{
lean_inc(v_a_3533_);
lean_dec(v___x_3514_);
v___x_3535_ = lean_box(0);
v_isShared_3536_ = v_isSharedCheck_3540_;
goto v_resetjp_3534_;
}
v_resetjp_3534_:
{
lean_object* v___x_3538_; 
if (v_isShared_3536_ == 0)
{
v___x_3538_ = v___x_3535_;
goto v_reusejp_3537_;
}
else
{
lean_object* v_reuseFailAlloc_3539_; 
v_reuseFailAlloc_3539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3539_, 0, v_a_3533_);
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
lean_dec(v_a_3510_);
lean_del_object(v___x_3504_);
lean_del_object(v___x_3498_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3541_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3548_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3548_ == 0)
{
v___x_3543_ = v___x_3511_;
v_isShared_3544_ = v_isSharedCheck_3548_;
goto v_resetjp_3542_;
}
else
{
lean_inc(v_a_3541_);
lean_dec(v___x_3511_);
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
else
{
lean_object* v_a_3549_; lean_object* v___x_3551_; uint8_t v_isShared_3552_; uint8_t v_isSharedCheck_3556_; 
lean_del_object(v___x_3504_);
lean_dec(v_fst_3501_);
lean_del_object(v___x_3498_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
v_a_3549_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3556_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3556_ == 0)
{
v___x_3551_ = v___x_3509_;
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
else
{
lean_inc(v_a_3549_);
lean_dec(v___x_3509_);
v___x_3551_ = lean_box(0);
v_isShared_3552_ = v_isSharedCheck_3556_;
goto v_resetjp_3550_;
}
v_resetjp_3550_:
{
lean_object* v___x_3554_; 
if (v_isShared_3552_ == 0)
{
v___x_3554_ = v___x_3551_;
goto v_reusejp_3553_;
}
else
{
lean_object* v_reuseFailAlloc_3555_; 
v_reuseFailAlloc_3555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_a_3549_);
v___x_3554_ = v_reuseFailAlloc_3555_;
goto v_reusejp_3553_;
}
v_reusejp_3553_:
{
return v___x_3554_;
}
}
}
}
}
else
{
lean_object* v_a_3557_; lean_object* v___x_3559_; uint8_t v_isShared_3560_; uint8_t v_isSharedCheck_3564_; 
lean_del_object(v___x_3504_);
lean_dec(v_fst_3501_);
lean_del_object(v___x_3498_);
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3557_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3564_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3564_ == 0)
{
v___x_3559_ = v___x_3506_;
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
else
{
lean_inc(v_a_3557_);
lean_dec(v___x_3506_);
v___x_3559_ = lean_box(0);
v_isShared_3560_ = v_isSharedCheck_3564_;
goto v_resetjp_3558_;
}
v_resetjp_3558_:
{
lean_object* v___x_3562_; 
if (v_isShared_3560_ == 0)
{
v___x_3562_ = v___x_3559_;
goto v_reusejp_3561_;
}
else
{
lean_object* v_reuseFailAlloc_3563_; 
v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
v___x_3562_ = v_reuseFailAlloc_3563_;
goto v_reusejp_3561_;
}
v_reusejp_3561_:
{
return v___x_3562_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3495_);
v___y_3349_ = v___y_3447_;
v___y_3350_ = v___y_3448_;
v___y_3351_ = v___y_3449_;
v___y_3352_ = v___y_3450_;
goto v___jp_3348_;
}
}
else
{
lean_object* v_a_3567_; lean_object* v___x_3569_; uint8_t v_isShared_3570_; uint8_t v_isSharedCheck_3574_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3567_ = lean_ctor_get(v___x_3494_, 0);
v_isSharedCheck_3574_ = !lean_is_exclusive(v___x_3494_);
if (v_isSharedCheck_3574_ == 0)
{
v___x_3569_ = v___x_3494_;
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
else
{
lean_inc(v_a_3567_);
lean_dec(v___x_3494_);
v___x_3569_ = lean_box(0);
v_isShared_3570_ = v_isSharedCheck_3574_;
goto v_resetjp_3568_;
}
v_resetjp_3568_:
{
lean_object* v___x_3572_; 
if (v_isShared_3570_ == 0)
{
v___x_3572_ = v___x_3569_;
goto v_reusejp_3571_;
}
else
{
lean_object* v_reuseFailAlloc_3573_; 
v_reuseFailAlloc_3573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3573_, 0, v_a_3567_);
v___x_3572_ = v_reuseFailAlloc_3573_;
goto v_reusejp_3571_;
}
v_reusejp_3571_:
{
return v___x_3572_;
}
}
}
}
}
else
{
lean_object* v_a_3575_; lean_object* v___x_3577_; uint8_t v_isShared_3578_; uint8_t v_isSharedCheck_3582_; 
lean_dec_ref(v___x_3094_);
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3575_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3577_ = v___x_3451_;
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
else
{
lean_inc(v_a_3575_);
lean_dec(v___x_3451_);
v___x_3577_ = lean_box(0);
v_isShared_3578_ = v_isSharedCheck_3582_;
goto v_resetjp_3576_;
}
v_resetjp_3576_:
{
lean_object* v___x_3580_; 
if (v_isShared_3578_ == 0)
{
v___x_3580_ = v___x_3577_;
goto v_reusejp_3579_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v_a_3575_);
v___x_3580_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3579_;
}
v_reusejp_3579_:
{
return v___x_3580_;
}
}
}
}
}
else
{
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
v_a_3054_ = v___x_3065_;
goto v___jp_3053_;
}
v___jp_3066_:
{
uint8_t v_emptyType_3073_; 
v_emptyType_3073_ = lean_ctor_get_uint8(v_config_3028_, sizeof(void*)*1 + 1);
if (v_emptyType_3073_ == 0)
{
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
v_a_3054_ = v___x_3065_;
goto v___jp_3053_;
}
else
{
if (v___y_3067_ == 0)
{
if (v___y_3068_ == 0)
{
lean_object* v_searchFuel_3074_; lean_object* v___x_3075_; lean_object* v___x_3076_; 
v_searchFuel_3074_ = lean_ctor_get(v_config_3028_, 0);
v___x_3075_ = l_Lean_LocalDecl_fvarId(v_val_3060_);
lean_dec(v_val_3060_);
lean_inc(v_searchFuel_3074_);
lean_inc(v_mvarId_3029_);
v___x_3076_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3029_, v___x_3075_, v_searchFuel_3074_, v___y_3069_, v___y_3070_, v___y_3071_, v___y_3072_);
if (lean_obj_tag(v___x_3076_) == 0)
{
lean_object* v_a_3077_; uint8_t v___x_3078_; 
v_a_3077_ = lean_ctor_get(v___x_3076_, 0);
lean_inc(v_a_3077_);
lean_dec_ref_known(v___x_3076_, 1);
v___x_3078_ = lean_unbox(v_a_3077_);
lean_dec(v_a_3077_);
if (v___x_3078_ == 0)
{
lean_del_object(v___x_3062_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
v_a_3054_ = v___x_3065_;
goto v___jp_3053_;
}
else
{
lean_object* v___x_3079_; lean_object* v___x_3081_; 
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v___x_3079_ = lean_box(v___x_3039_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v___x_3079_);
v___x_3081_ = v___x_3062_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v___x_3079_);
v___x_3081_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3082_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3082_, 0, v___x_3081_);
lean_ctor_set(v___x_3082_, 1, v___x_3064_);
v___x_3083_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3083_, 0, v___x_3082_);
v_a_3046_ = v___x_3083_;
goto v___jp_3045_;
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_del_object(v___x_3062_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
lean_dec(v_mvarId_3029_);
lean_dec_ref(v_config_3028_);
v_a_3085_ = lean_ctor_get(v___x_3076_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3076_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3076_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3076_);
v___x_3087_ = lean_box(0);
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
v_resetjp_3086_:
{
lean_object* v___x_3090_; 
if (v_isShared_3088_ == 0)
{
v___x_3090_ = v___x_3087_;
goto v_reusejp_3089_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v_a_3085_);
v___x_3090_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3089_;
}
v_reusejp_3089_:
{
return v___x_3090_;
}
}
}
}
else
{
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
v_a_3054_ = v___x_3065_;
goto v___jp_3053_;
}
}
else
{
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_del_object(v___x_3043_);
lean_dec(v_snd_3041_);
v_a_3054_ = v___x_3065_;
goto v___jp_3053_;
}
}
}
}
}
v___jp_3045_:
{
lean_object* v___x_3047_; lean_object* v___x_3049_; 
v___x_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3047_, 0, v_a_3046_);
if (v_isShared_3044_ == 0)
{
lean_ctor_set(v___x_3043_, 0, v___x_3047_);
v___x_3049_ = v___x_3043_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3047_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_snd_3041_);
v___x_3049_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
lean_object* v___x_3050_; 
v___x_3050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3050_, 0, v___x_3049_);
return v___x_3050_;
}
}
v___jp_3053_:
{
lean_object* v___x_3055_; size_t v___x_3056_; size_t v___x_3057_; 
v___x_3055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3052_);
lean_ctor_set(v___x_3055_, 1, v_a_3054_);
v___x_3056_ = ((size_t)1ULL);
v___x_3057_ = lean_usize_add(v_i_3032_, v___x_3056_);
v_i_3032_ = v___x_3057_;
v_b_3033_ = v___x_3055_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3656_, lean_object* v_mvarId_3657_, lean_object* v_as_3658_, lean_object* v_sz_3659_, lean_object* v_i_3660_, lean_object* v_b_3661_, lean_object* v___y_3662_, lean_object* v___y_3663_, lean_object* v___y_3664_, lean_object* v___y_3665_, lean_object* v___y_3666_){
_start:
{
size_t v_sz_boxed_3667_; size_t v_i_boxed_3668_; lean_object* v_res_3669_; 
v_sz_boxed_3667_ = lean_unbox_usize(v_sz_3659_);
lean_dec(v_sz_3659_);
v_i_boxed_3668_ = lean_unbox_usize(v_i_3660_);
lean_dec(v_i_3660_);
v_res_3669_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3656_, v_mvarId_3657_, v_as_3658_, v_sz_boxed_3667_, v_i_boxed_3668_, v_b_3661_, v___y_3662_, v___y_3663_, v___y_3664_, v___y_3665_);
lean_dec(v___y_3665_);
lean_dec_ref(v___y_3664_);
lean_dec(v___y_3663_);
lean_dec_ref(v___y_3662_);
lean_dec_ref(v_as_3658_);
return v_res_3669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3670_, lean_object* v_mvarId_3671_, lean_object* v_as_3672_, size_t v_sz_3673_, size_t v_i_3674_, lean_object* v_b_3675_, lean_object* v___y_3676_, lean_object* v___y_3677_, lean_object* v___y_3678_, lean_object* v___y_3679_){
_start:
{
uint8_t v___x_3681_; 
v___x_3681_ = lean_usize_dec_lt(v_i_3674_, v_sz_3673_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; 
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v___x_3682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3682_, 0, v_b_3675_);
return v___x_3682_;
}
else
{
lean_object* v_snd_3683_; lean_object* v___x_3685_; uint8_t v_isShared_3686_; uint8_t v_isSharedCheck_4296_; 
v_snd_3683_ = lean_ctor_get(v_b_3675_, 1);
v_isSharedCheck_4296_ = !lean_is_exclusive(v_b_3675_);
if (v_isSharedCheck_4296_ == 0)
{
lean_object* v_unused_4297_; 
v_unused_4297_ = lean_ctor_get(v_b_3675_, 0);
lean_dec(v_unused_4297_);
v___x_3685_ = v_b_3675_;
v_isShared_3686_ = v_isSharedCheck_4296_;
goto v_resetjp_3684_;
}
else
{
lean_inc(v_snd_3683_);
lean_dec(v_b_3675_);
v___x_3685_ = lean_box(0);
v_isShared_3686_ = v_isSharedCheck_4296_;
goto v_resetjp_3684_;
}
v_resetjp_3684_:
{
lean_object* v_a_3688_; lean_object* v___x_3694_; lean_object* v_a_3696_; lean_object* v_a_3701_; 
v___x_3694_ = lean_box(0);
v_a_3701_ = lean_array_uget(v_as_3672_, v_i_3674_);
if (lean_obj_tag(v_a_3701_) == 0)
{
lean_del_object(v___x_3685_);
v_a_3696_ = v_snd_3683_;
goto v___jp_3695_;
}
else
{
lean_object* v_val_3702_; lean_object* v___x_3704_; uint8_t v_isShared_3705_; uint8_t v_isSharedCheck_4295_; 
v_val_3702_ = lean_ctor_get(v_a_3701_, 0);
v_isSharedCheck_4295_ = !lean_is_exclusive(v_a_3701_);
if (v_isSharedCheck_4295_ == 0)
{
v___x_3704_ = v_a_3701_;
v_isShared_3705_ = v_isSharedCheck_4295_;
goto v_resetjp_3703_;
}
else
{
lean_inc(v_val_3702_);
lean_dec(v_a_3701_);
v___x_3704_ = lean_box(0);
v_isShared_3705_ = v_isSharedCheck_4295_;
goto v_resetjp_3703_;
}
v_resetjp_3703_:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; uint8_t v___y_3709_; uint8_t v___y_3710_; lean_object* v___y_3711_; lean_object* v___y_3712_; lean_object* v___y_3713_; lean_object* v___y_3714_; uint8_t v___x_3735_; 
v___x_3706_ = lean_box(0);
v___x_3707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3735_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3702_);
if (v___x_3735_ == 0)
{
lean_object* v___x_3736_; uint8_t v___y_3738_; uint8_t v___y_3739_; lean_object* v___y_3740_; lean_object* v___y_3741_; lean_object* v___y_3742_; lean_object* v___y_3743_; lean_object* v___y_3762_; lean_object* v___y_3763_; lean_object* v___y_3764_; uint8_t v___y_3765_; uint8_t v___y_3766_; lean_object* v___y_3767_; lean_object* v_a_3768_; lean_object* v___y_3774_; lean_object* v___y_3775_; lean_object* v___y_3776_; uint8_t v___y_3777_; uint8_t v___y_3778_; lean_object* v___y_3779_; lean_object* v___y_3780_; lean_object* v___y_3781_; uint8_t v___y_3825_; uint8_t v_isHEq_3826_; lean_object* v___y_3827_; lean_object* v___y_3828_; lean_object* v___y_3829_; lean_object* v___y_3830_; uint8_t v_isEq_3868_; lean_object* v___y_3869_; lean_object* v___y_3870_; lean_object* v___y_3871_; lean_object* v___y_3872_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; lean_object* v___y_4089_; lean_object* v___y_4090_; lean_object* v___y_4091_; lean_object* v___y_4092_; lean_object* v___x_4225_; 
v___x_3736_ = l_Lean_LocalDecl_type(v_val_3702_);
lean_inc_ref(v___x_3736_);
v___x_4225_ = l_Lean_Meta_matchNot_x3f(v___x_3736_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_4225_) == 0)
{
lean_object* v_a_4226_; 
v_a_4226_ = lean_ctor_get(v___x_4225_, 0);
lean_inc(v_a_4226_);
lean_dec_ref_known(v___x_4225_, 1);
if (lean_obj_tag(v_a_4226_) == 1)
{
lean_object* v_val_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4286_; 
v_val_4227_ = lean_ctor_get(v_a_4226_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v_a_4226_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4229_ = v_a_4226_;
v_isShared_4230_ = v_isSharedCheck_4286_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_val_4227_);
lean_dec(v_a_4226_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4286_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4231_; 
v___x_4231_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4227_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v_a_4232_; 
v_a_4232_ = lean_ctor_get(v___x_4231_, 0);
lean_inc(v_a_4232_);
lean_dec_ref_known(v___x_4231_, 1);
if (lean_obj_tag(v_a_4232_) == 1)
{
lean_object* v_val_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4277_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec_ref(v_config_3670_);
v_val_4233_ = lean_ctor_get(v_a_4232_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v_a_4232_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4235_ = v_a_4232_;
v_isShared_4236_ = v_isSharedCheck_4277_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_val_4233_);
lean_dec(v_a_4232_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4277_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4237_; 
lean_inc(v_mvarId_3671_);
v___x_4237_ = l_Lean_MVarId_getType(v_mvarId_3671_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_4237_) == 0)
{
lean_object* v_a_4238_; lean_object* v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; 
v_a_4238_ = lean_ctor_get(v___x_4237_, 0);
lean_inc(v_a_4238_);
lean_dec_ref_known(v___x_4237_, 1);
v___x_4239_ = l_Lean_LocalDecl_toExpr(v_val_3702_);
v___x_4240_ = l_Lean_mkFVar(v_val_4233_);
v___x_4241_ = l_Lean_Expr_app___override(v___x_4239_, v___x_4240_);
v___x_4242_ = l_Lean_Meta_mkFalseElim(v_a_4238_, v___x_4241_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
if (lean_obj_tag(v___x_4242_) == 0)
{
lean_object* v_a_4243_; lean_object* v___x_4244_; 
v_a_4243_ = lean_ctor_get(v___x_4242_, 0);
lean_inc(v_a_4243_);
lean_dec_ref_known(v___x_4242_, 1);
v___x_4244_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3671_, v_a_4243_, v___y_3677_);
if (lean_obj_tag(v___x_4244_) == 0)
{
lean_object* v___x_4245_; lean_object* v___x_4247_; 
lean_dec_ref_known(v___x_4244_, 1);
v___x_4245_ = lean_box(v___x_3681_);
if (v_isShared_4236_ == 0)
{
lean_ctor_set(v___x_4235_, 0, v___x_4245_);
v___x_4247_ = v___x_4235_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4252_; 
v_reuseFailAlloc_4252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4252_, 0, v___x_4245_);
v___x_4247_ = v_reuseFailAlloc_4252_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
lean_object* v___x_4248_; lean_object* v___x_4250_; 
v___x_4248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
lean_ctor_set(v___x_4248_, 1, v___x_3706_);
if (v_isShared_4230_ == 0)
{
lean_ctor_set_tag(v___x_4229_, 0);
lean_ctor_set(v___x_4229_, 0, v___x_4248_);
v___x_4250_ = v___x_4229_;
goto v_reusejp_4249_;
}
else
{
lean_object* v_reuseFailAlloc_4251_; 
v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4251_, 0, v___x_4248_);
v___x_4250_ = v_reuseFailAlloc_4251_;
goto v_reusejp_4249_;
}
v_reusejp_4249_:
{
v_a_3688_ = v___x_4250_;
goto v___jp_3687_;
}
}
}
else
{
lean_object* v_a_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_del_object(v___x_4235_);
lean_del_object(v___x_4229_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
v_a_4253_ = lean_ctor_get(v___x_4244_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4244_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4244_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_a_4253_);
lean_dec(v___x_4244_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
else
{
lean_object* v_a_4261_; lean_object* v___x_4263_; uint8_t v_isShared_4264_; uint8_t v_isSharedCheck_4268_; 
lean_del_object(v___x_4235_);
lean_del_object(v___x_4229_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_4261_ = lean_ctor_get(v___x_4242_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4242_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4263_ = v___x_4242_;
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
else
{
lean_inc(v_a_4261_);
lean_dec(v___x_4242_);
v___x_4263_ = lean_box(0);
v_isShared_4264_ = v_isSharedCheck_4268_;
goto v_resetjp_4262_;
}
v_resetjp_4262_:
{
lean_object* v___x_4266_; 
if (v_isShared_4264_ == 0)
{
v___x_4266_ = v___x_4263_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v_a_4261_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
else
{
lean_object* v_a_4269_; lean_object* v___x_4271_; uint8_t v_isShared_4272_; uint8_t v_isSharedCheck_4276_; 
lean_del_object(v___x_4235_);
lean_dec(v_val_4233_);
lean_del_object(v___x_4229_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_4269_ = lean_ctor_get(v___x_4237_, 0);
v_isSharedCheck_4276_ = !lean_is_exclusive(v___x_4237_);
if (v_isSharedCheck_4276_ == 0)
{
v___x_4271_ = v___x_4237_;
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
else
{
lean_inc(v_a_4269_);
lean_dec(v___x_4237_);
v___x_4271_ = lean_box(0);
v_isShared_4272_ = v_isSharedCheck_4276_;
goto v_resetjp_4270_;
}
v_resetjp_4270_:
{
lean_object* v___x_4274_; 
if (v_isShared_4272_ == 0)
{
v___x_4274_ = v___x_4271_;
goto v_reusejp_4273_;
}
else
{
lean_object* v_reuseFailAlloc_4275_; 
v_reuseFailAlloc_4275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4275_, 0, v_a_4269_);
v___x_4274_ = v_reuseFailAlloc_4275_;
goto v_reusejp_4273_;
}
v_reusejp_4273_:
{
return v___x_4274_;
}
}
}
}
}
else
{
lean_dec(v_a_4232_);
lean_del_object(v___x_4229_);
v___y_4089_ = v___y_3676_;
v___y_4090_ = v___y_3677_;
v___y_4091_ = v___y_3678_;
v___y_4092_ = v___y_3679_;
goto v___jp_4088_;
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_del_object(v___x_4229_);
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_4278_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4231_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4231_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_a_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
}
else
{
lean_dec(v_a_4226_);
v___y_4089_ = v___y_3676_;
v___y_4090_ = v___y_3677_;
v___y_4091_ = v___y_3678_;
v___y_4092_ = v___y_3679_;
goto v___jp_4088_;
}
}
else
{
lean_object* v_a_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4294_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_4287_ = lean_ctor_get(v___x_4225_, 0);
v_isSharedCheck_4294_ = !lean_is_exclusive(v___x_4225_);
if (v_isSharedCheck_4294_ == 0)
{
v___x_4289_ = v___x_4225_;
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_a_4287_);
lean_dec(v___x_4225_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4294_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4292_; 
if (v_isShared_4290_ == 0)
{
v___x_4292_ = v___x_4289_;
goto v_reusejp_4291_;
}
else
{
lean_object* v_reuseFailAlloc_4293_; 
v_reuseFailAlloc_4293_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4293_, 0, v_a_4287_);
v___x_4292_ = v_reuseFailAlloc_4293_;
goto v_reusejp_4291_;
}
v_reusejp_4291_:
{
return v___x_4292_;
}
}
}
v___jp_3737_:
{
uint8_t v_genDiseq_3744_; 
v_genDiseq_3744_ = lean_ctor_get_uint8(v_config_3670_, sizeof(void*)*1 + 2);
if (v_genDiseq_3744_ == 0)
{
lean_dec_ref(v___x_3736_);
v___y_3709_ = v___y_3738_;
v___y_3710_ = v___y_3739_;
v___y_3711_ = v___y_3740_;
v___y_3712_ = v___y_3741_;
v___y_3713_ = v___y_3742_;
v___y_3714_ = v___y_3743_;
goto v___jp_3708_;
}
else
{
uint8_t v___x_3745_; 
v___x_3745_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3736_);
if (v___x_3745_ == 0)
{
v___y_3709_ = v___y_3738_;
v___y_3710_ = v___y_3739_;
v___y_3711_ = v___y_3740_;
v___y_3712_ = v___y_3741_;
v___y_3713_ = v___y_3742_;
v___y_3714_ = v___y_3743_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3746_; 
lean_inc(v_val_3702_);
lean_inc(v_mvarId_3671_);
v___x_3746_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3671_, v_val_3702_, v___y_3740_, v___y_3741_, v___y_3742_, v___y_3743_);
if (lean_obj_tag(v___x_3746_) == 0)
{
lean_object* v_a_3747_; uint8_t v___x_3748_; 
v_a_3747_ = lean_ctor_get(v___x_3746_, 0);
lean_inc(v_a_3747_);
lean_dec_ref_known(v___x_3746_, 1);
v___x_3748_ = lean_unbox(v_a_3747_);
lean_dec(v_a_3747_);
if (v___x_3748_ == 0)
{
v___y_3709_ = v___y_3738_;
v___y_3710_ = v___y_3739_;
v___y_3711_ = v___y_3740_;
v___y_3712_ = v___y_3741_;
v___y_3713_ = v___y_3742_;
v___y_3714_ = v___y_3743_;
goto v___jp_3708_;
}
else
{
lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; 
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v___x_3749_ = lean_box(v___x_3681_);
v___x_3750_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
v___x_3751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3751_, 0, v___x_3750_);
lean_ctor_set(v___x_3751_, 1, v___x_3706_);
v___x_3752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3751_);
v_a_3688_ = v___x_3752_;
goto v___jp_3687_;
}
}
else
{
lean_object* v_a_3753_; lean_object* v___x_3755_; uint8_t v_isShared_3756_; uint8_t v_isSharedCheck_3760_; 
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_3753_ = lean_ctor_get(v___x_3746_, 0);
v_isSharedCheck_3760_ = !lean_is_exclusive(v___x_3746_);
if (v_isSharedCheck_3760_ == 0)
{
v___x_3755_ = v___x_3746_;
v_isShared_3756_ = v_isSharedCheck_3760_;
goto v_resetjp_3754_;
}
else
{
lean_inc(v_a_3753_);
lean_dec(v___x_3746_);
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
}
v___jp_3761_:
{
uint8_t v___x_3769_; 
v___x_3769_ = l_Lean_Exception_isInterrupt(v_a_3768_);
if (v___x_3769_ == 0)
{
uint8_t v___x_3770_; 
lean_inc_ref(v_a_3768_);
v___x_3770_ = l_Lean_Exception_isRuntime(v_a_3768_);
if (v___x_3770_ == 0)
{
lean_dec_ref(v_a_3768_);
v___y_3738_ = v___y_3765_;
v___y_3739_ = v___y_3766_;
v___y_3740_ = v___y_3763_;
v___y_3741_ = v___y_3764_;
v___y_3742_ = v___y_3767_;
v___y_3743_ = v___y_3762_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3771_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v___x_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3771_, 0, v_a_3768_);
return v___x_3771_;
}
}
else
{
lean_object* v___x_3772_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v___x_3772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3772_, 0, v_a_3768_);
return v___x_3772_;
}
}
v___jp_3773_:
{
if (lean_obj_tag(v___y_3781_) == 0)
{
lean_object* v_a_3782_; lean_object* v___x_3783_; uint8_t v___x_3784_; 
v_a_3782_ = lean_ctor_get(v___y_3781_, 0);
lean_inc(v_a_3782_);
lean_dec_ref_known(v___y_3781_, 1);
v___x_3783_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3784_ = l_Lean_Expr_isConstOf(v_a_3782_, v___x_3783_);
lean_dec(v_a_3782_);
if (v___x_3784_ == 0)
{
lean_dec_ref(v___y_3779_);
v___y_3738_ = v___y_3777_;
v___y_3739_ = v___y_3778_;
v___y_3740_ = v___y_3775_;
v___y_3741_ = v___y_3776_;
v___y_3742_ = v___y_3780_;
v___y_3743_ = v___y_3774_;
goto v___jp_3737_;
}
else
{
lean_object* v___x_3785_; 
lean_inc_ref(v___y_3779_);
v___x_3785_ = l_Lean_Meta_mkEqRefl(v___y_3779_, v___y_3775_, v___y_3776_, v___y_3780_, v___y_3774_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; lean_object* v___x_3787_; lean_object* v_dummy_3788_; lean_object* v_nargs_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
v___x_3787_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3788_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3789_ = l_Lean_Expr_getAppNumArgs(v___y_3779_);
lean_inc(v_nargs_3789_);
v___x_3790_ = lean_mk_array(v_nargs_3789_, v_dummy_3788_);
v___x_3791_ = lean_unsigned_to_nat(1u);
v___x_3792_ = lean_nat_sub(v_nargs_3789_, v___x_3791_);
lean_dec(v_nargs_3789_);
v___x_3793_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3779_, v___x_3790_, v___x_3792_);
v___x_3794_ = lean_array_push(v___x_3793_, v_a_3786_);
v___x_3795_ = l_Lean_mkAppN(v___x_3787_, v___x_3794_);
lean_dec_ref(v___x_3794_);
lean_inc(v_mvarId_3671_);
v___x_3796_ = l_Lean_MVarId_getType(v_mvarId_3671_, v___y_3775_, v___y_3776_, v___y_3780_, v___y_3774_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
lean_inc(v_val_3702_);
v___x_3798_ = l_Lean_LocalDecl_toExpr(v_val_3702_);
v___x_3799_ = l_Lean_Meta_mkAbsurd(v_a_3797_, v___x_3798_, v___x_3795_, v___y_3775_, v___y_3776_, v___y_3780_, v___y_3774_);
if (lean_obj_tag(v___x_3799_) == 0)
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3819_; 
v_a_3800_ = lean_ctor_get(v___x_3799_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3799_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3802_ = v___x_3799_;
v_isShared_3803_ = v_isSharedCheck_3819_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3799_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3819_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3804_; 
lean_inc(v_mvarId_3671_);
v___x_3804_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3671_, v_a_3800_, v___y_3776_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3816_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_isSharedCheck_3816_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3816_ == 0)
{
lean_object* v_unused_3817_; 
v_unused_3817_ = lean_ctor_get(v___x_3804_, 0);
lean_dec(v_unused_3817_);
v___x_3806_ = v___x_3804_;
v_isShared_3807_ = v_isSharedCheck_3816_;
goto v_resetjp_3805_;
}
else
{
lean_dec(v___x_3804_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3816_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3808_ = lean_box(v___x_3681_);
if (v_isShared_3807_ == 0)
{
lean_ctor_set_tag(v___x_3806_, 1);
lean_ctor_set(v___x_3806_, 0, v___x_3808_);
v___x_3810_ = v___x_3806_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3815_; 
v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3815_, 0, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3815_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
lean_object* v___x_3811_; lean_object* v___x_3813_; 
v___x_3811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3810_);
lean_ctor_set(v___x_3811_, 1, v___x_3706_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3811_);
v___x_3813_ = v___x_3802_;
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
v_a_3688_ = v___x_3813_;
goto v___jp_3687_;
}
}
}
}
else
{
lean_object* v_a_3818_; 
lean_del_object(v___x_3802_);
v_a_3818_ = lean_ctor_get(v___x_3804_, 0);
lean_inc(v_a_3818_);
lean_dec_ref_known(v___x_3804_, 1);
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3778_;
v___y_3767_ = v___y_3780_;
v_a_3768_ = v_a_3818_;
goto v___jp_3761_;
}
}
}
else
{
lean_object* v_a_3820_; 
v_a_3820_ = lean_ctor_get(v___x_3799_, 0);
lean_inc(v_a_3820_);
lean_dec_ref_known(v___x_3799_, 1);
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3778_;
v___y_3767_ = v___y_3780_;
v_a_3768_ = v_a_3820_;
goto v___jp_3761_;
}
}
else
{
lean_object* v_a_3821_; 
lean_dec_ref(v___x_3795_);
v_a_3821_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3821_);
lean_dec_ref_known(v___x_3796_, 1);
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3778_;
v___y_3767_ = v___y_3780_;
v_a_3768_ = v_a_3821_;
goto v___jp_3761_;
}
}
else
{
lean_object* v_a_3822_; 
lean_dec_ref(v___y_3779_);
v_a_3822_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3822_);
lean_dec_ref_known(v___x_3785_, 1);
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3778_;
v___y_3767_ = v___y_3780_;
v_a_3768_ = v_a_3822_;
goto v___jp_3761_;
}
}
}
else
{
lean_object* v_a_3823_; 
lean_dec_ref(v___y_3779_);
v_a_3823_ = lean_ctor_get(v___y_3781_, 0);
lean_inc(v_a_3823_);
lean_dec_ref_known(v___y_3781_, 1);
v___y_3762_ = v___y_3774_;
v___y_3763_ = v___y_3775_;
v___y_3764_ = v___y_3776_;
v___y_3765_ = v___y_3777_;
v___y_3766_ = v___y_3778_;
v___y_3767_ = v___y_3780_;
v_a_3768_ = v_a_3823_;
goto v___jp_3761_;
}
}
v___jp_3824_:
{
uint8_t v_useDecide_3831_; 
v_useDecide_3831_ = lean_ctor_get_uint8(v_config_3670_, sizeof(void*)*1);
if (v_useDecide_3831_ == 0)
{
v___y_3738_ = v_isHEq_3826_;
v___y_3739_ = v___y_3825_;
v___y_3740_ = v___y_3827_;
v___y_3741_ = v___y_3828_;
v___y_3742_ = v___y_3829_;
v___y_3743_ = v___y_3830_;
goto v___jp_3737_;
}
else
{
uint8_t v___x_3832_; 
v___x_3832_ = l_Lean_Expr_hasFVar(v___x_3736_);
if (v___x_3832_ == 0)
{
lean_object* v___x_3833_; 
lean_inc_ref(v___x_3736_);
v___x_3833_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3736_, v___y_3828_);
if (lean_obj_tag(v___x_3833_) == 0)
{
lean_object* v_a_3834_; uint8_t v___x_3835_; 
v_a_3834_ = lean_ctor_get(v___x_3833_, 0);
lean_inc(v_a_3834_);
lean_dec_ref_known(v___x_3833_, 1);
v___x_3835_ = l_Lean_Expr_hasMVar(v_a_3834_);
if (v___x_3835_ == 0)
{
uint8_t v___x_3836_; 
v___x_3836_ = l_Lean_Expr_hasFVar(v_a_3834_);
lean_dec(v_a_3834_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; 
lean_inc_ref(v___x_3736_);
v___x_3837_ = l_Lean_Meta_mkDecide(v___x_3736_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
if (lean_obj_tag(v___x_3837_) == 0)
{
lean_object* v_a_3838_; lean_object* v___x_3839_; uint8_t v_transparency_3840_; uint8_t v___x_3841_; uint8_t v___x_3842_; 
v_a_3838_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3838_);
lean_dec_ref_known(v___x_3837_, 1);
v___x_3839_ = l_Lean_Meta_Context_config(v___y_3827_);
v_transparency_3840_ = lean_ctor_get_uint8(v___x_3839_, 9);
lean_dec_ref(v___x_3839_);
v___x_3841_ = 1;
v___x_3842_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3840_, v___x_3841_);
if (v___x_3842_ == 0)
{
lean_object* v_keyedConfig_3843_; uint8_t v_trackZetaDelta_3844_; lean_object* v_zetaDeltaSet_3845_; lean_object* v_lctx_3846_; lean_object* v_localInstances_3847_; lean_object* v_defEqCtx_x3f_3848_; lean_object* v_synthPendingDepth_3849_; lean_object* v_customCanUnfoldPredicate_x3f_3850_; uint8_t v_univApprox_3851_; uint8_t v_inTypeClassResolution_3852_; uint8_t v_cacheInferType_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; 
v_keyedConfig_3843_ = lean_ctor_get(v___y_3827_, 0);
v_trackZetaDelta_3844_ = lean_ctor_get_uint8(v___y_3827_, sizeof(void*)*7);
v_zetaDeltaSet_3845_ = lean_ctor_get(v___y_3827_, 1);
v_lctx_3846_ = lean_ctor_get(v___y_3827_, 2);
v_localInstances_3847_ = lean_ctor_get(v___y_3827_, 3);
v_defEqCtx_x3f_3848_ = lean_ctor_get(v___y_3827_, 4);
v_synthPendingDepth_3849_ = lean_ctor_get(v___y_3827_, 5);
v_customCanUnfoldPredicate_x3f_3850_ = lean_ctor_get(v___y_3827_, 6);
v_univApprox_3851_ = lean_ctor_get_uint8(v___y_3827_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3852_ = lean_ctor_get_uint8(v___y_3827_, sizeof(void*)*7 + 2);
v_cacheInferType_3853_ = lean_ctor_get_uint8(v___y_3827_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3843_);
v___x_3854_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3841_, v_keyedConfig_3843_);
lean_inc(v_customCanUnfoldPredicate_x3f_3850_);
lean_inc(v_synthPendingDepth_3849_);
lean_inc(v_defEqCtx_x3f_3848_);
lean_inc_ref(v_localInstances_3847_);
lean_inc_ref(v_lctx_3846_);
lean_inc(v_zetaDeltaSet_3845_);
v___x_3855_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3855_, 0, v___x_3854_);
lean_ctor_set(v___x_3855_, 1, v_zetaDeltaSet_3845_);
lean_ctor_set(v___x_3855_, 2, v_lctx_3846_);
lean_ctor_set(v___x_3855_, 3, v_localInstances_3847_);
lean_ctor_set(v___x_3855_, 4, v_defEqCtx_x3f_3848_);
lean_ctor_set(v___x_3855_, 5, v_synthPendingDepth_3849_);
lean_ctor_set(v___x_3855_, 6, v_customCanUnfoldPredicate_x3f_3850_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*7, v_trackZetaDelta_3844_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*7 + 1, v_univApprox_3851_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3852_);
lean_ctor_set_uint8(v___x_3855_, sizeof(void*)*7 + 3, v_cacheInferType_3853_);
lean_inc(v___y_3830_);
lean_inc_ref(v___y_3829_);
lean_inc(v___y_3828_);
lean_inc(v_a_3838_);
v___x_3856_ = lean_whnf(v_a_3838_, v___x_3855_, v___y_3828_, v___y_3829_, v___y_3830_);
v___y_3774_ = v___y_3830_;
v___y_3775_ = v___y_3827_;
v___y_3776_ = v___y_3828_;
v___y_3777_ = v_isHEq_3826_;
v___y_3778_ = v___y_3825_;
v___y_3779_ = v_a_3838_;
v___y_3780_ = v___y_3829_;
v___y_3781_ = v___x_3856_;
goto v___jp_3773_;
}
else
{
lean_object* v___x_3857_; 
lean_inc(v___y_3830_);
lean_inc_ref(v___y_3829_);
lean_inc(v___y_3828_);
lean_inc_ref(v___y_3827_);
lean_inc(v_a_3838_);
v___x_3857_ = lean_whnf(v_a_3838_, v___y_3827_, v___y_3828_, v___y_3829_, v___y_3830_);
v___y_3774_ = v___y_3830_;
v___y_3775_ = v___y_3827_;
v___y_3776_ = v___y_3828_;
v___y_3777_ = v_isHEq_3826_;
v___y_3778_ = v___y_3825_;
v___y_3779_ = v_a_3838_;
v___y_3780_ = v___y_3829_;
v___y_3781_ = v___x_3857_;
goto v___jp_3773_;
}
}
else
{
lean_object* v_a_3858_; 
v_a_3858_ = lean_ctor_get(v___x_3837_, 0);
lean_inc(v_a_3858_);
lean_dec_ref_known(v___x_3837_, 1);
v___y_3762_ = v___y_3830_;
v___y_3763_ = v___y_3827_;
v___y_3764_ = v___y_3828_;
v___y_3765_ = v_isHEq_3826_;
v___y_3766_ = v___y_3825_;
v___y_3767_ = v___y_3829_;
v_a_3768_ = v_a_3858_;
goto v___jp_3761_;
}
}
else
{
v___y_3738_ = v_isHEq_3826_;
v___y_3739_ = v___y_3825_;
v___y_3740_ = v___y_3827_;
v___y_3741_ = v___y_3828_;
v___y_3742_ = v___y_3829_;
v___y_3743_ = v___y_3830_;
goto v___jp_3737_;
}
}
else
{
lean_dec(v_a_3834_);
v___y_3738_ = v_isHEq_3826_;
v___y_3739_ = v___y_3825_;
v___y_3740_ = v___y_3827_;
v___y_3741_ = v___y_3828_;
v___y_3742_ = v___y_3829_;
v___y_3743_ = v___y_3830_;
goto v___jp_3737_;
}
}
else
{
lean_object* v_a_3859_; lean_object* v___x_3861_; uint8_t v_isShared_3862_; uint8_t v_isSharedCheck_3866_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_3859_ = lean_ctor_get(v___x_3833_, 0);
v_isSharedCheck_3866_ = !lean_is_exclusive(v___x_3833_);
if (v_isSharedCheck_3866_ == 0)
{
v___x_3861_ = v___x_3833_;
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
else
{
lean_inc(v_a_3859_);
lean_dec(v___x_3833_);
v___x_3861_ = lean_box(0);
v_isShared_3862_ = v_isSharedCheck_3866_;
goto v_resetjp_3860_;
}
v_resetjp_3860_:
{
lean_object* v___x_3864_; 
if (v_isShared_3862_ == 0)
{
v___x_3864_ = v___x_3861_;
goto v_reusejp_3863_;
}
else
{
lean_object* v_reuseFailAlloc_3865_; 
v_reuseFailAlloc_3865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3865_, 0, v_a_3859_);
v___x_3864_ = v_reuseFailAlloc_3865_;
goto v_reusejp_3863_;
}
v_reusejp_3863_:
{
return v___x_3864_;
}
}
}
}
else
{
v___y_3738_ = v_isHEq_3826_;
v___y_3739_ = v___y_3825_;
v___y_3740_ = v___y_3827_;
v___y_3741_ = v___y_3828_;
v___y_3742_ = v___y_3829_;
v___y_3743_ = v___y_3830_;
goto v___jp_3737_;
}
}
}
v___jp_3867_:
{
lean_object* v___x_3873_; 
lean_inc_ref(v___x_3736_);
v___x_3873_ = l_Lean_Meta_matchHEq_x3f(v___x_3736_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v_a_3874_; 
v_a_3874_ = lean_ctor_get(v___x_3873_, 0);
lean_inc(v_a_3874_);
lean_dec_ref_known(v___x_3873_, 1);
if (lean_obj_tag(v_a_3874_) == 1)
{
lean_object* v_val_3875_; lean_object* v_snd_3876_; lean_object* v_snd_3877_; lean_object* v_fst_3878_; lean_object* v_fst_3879_; lean_object* v_fst_3880_; lean_object* v_snd_3881_; lean_object* v___x_3883_; uint8_t v_isShared_3884_; uint8_t v_isSharedCheck_3981_; 
v_val_3875_ = lean_ctor_get(v_a_3874_, 0);
lean_inc(v_val_3875_);
lean_dec_ref_known(v_a_3874_, 1);
v_snd_3876_ = lean_ctor_get(v_val_3875_, 1);
lean_inc(v_snd_3876_);
v_snd_3877_ = lean_ctor_get(v_snd_3876_, 1);
lean_inc(v_snd_3877_);
v_fst_3878_ = lean_ctor_get(v_val_3875_, 0);
lean_inc(v_fst_3878_);
lean_dec(v_val_3875_);
v_fst_3879_ = lean_ctor_get(v_snd_3876_, 0);
lean_inc(v_fst_3879_);
lean_dec(v_snd_3876_);
v_fst_3880_ = lean_ctor_get(v_snd_3877_, 0);
v_snd_3881_ = lean_ctor_get(v_snd_3877_, 1);
v_isSharedCheck_3981_ = !lean_is_exclusive(v_snd_3877_);
if (v_isSharedCheck_3981_ == 0)
{
v___x_3883_ = v_snd_3877_;
v_isShared_3884_ = v_isSharedCheck_3981_;
goto v_resetjp_3882_;
}
else
{
lean_inc(v_snd_3881_);
lean_inc(v_fst_3880_);
lean_dec(v_snd_3877_);
v___x_3883_ = lean_box(0);
v_isShared_3884_ = v_isSharedCheck_3981_;
goto v_resetjp_3882_;
}
v_resetjp_3882_:
{
lean_object* v___x_3885_; 
v___x_3885_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3879_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3885_) == 0)
{
lean_object* v_a_3886_; 
v_a_3886_ = lean_ctor_get(v___x_3885_, 0);
lean_inc(v_a_3886_);
lean_dec_ref_known(v___x_3885_, 1);
if (lean_obj_tag(v_a_3886_) == 1)
{
lean_object* v_val_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3972_; 
v_val_3887_ = lean_ctor_get(v_a_3886_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v_a_3886_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3889_ = v_a_3886_;
v_isShared_3890_ = v_isSharedCheck_3972_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_val_3887_);
lean_dec(v_a_3886_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3972_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3881_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3891_) == 0)
{
lean_object* v_a_3892_; 
v_a_3892_ = lean_ctor_get(v___x_3891_, 0);
lean_inc(v_a_3892_);
lean_dec_ref_known(v___x_3891_, 1);
if (lean_obj_tag(v_a_3892_) == 1)
{
lean_object* v_toConstantVal_3893_; lean_object* v_val_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3963_; 
v_toConstantVal_3893_ = lean_ctor_get(v_val_3887_, 0);
lean_inc_ref(v_toConstantVal_3893_);
lean_dec(v_val_3887_);
v_val_3894_ = lean_ctor_get(v_a_3892_, 0);
v_isSharedCheck_3963_ = !lean_is_exclusive(v_a_3892_);
if (v_isSharedCheck_3963_ == 0)
{
v___x_3896_ = v_a_3892_;
v_isShared_3897_ = v_isSharedCheck_3963_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_val_3894_);
lean_dec(v_a_3892_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3963_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v_toConstantVal_3898_; lean_object* v_name_3899_; lean_object* v_name_3900_; uint8_t v___x_3901_; 
v_toConstantVal_3898_ = lean_ctor_get(v_val_3894_, 0);
lean_inc_ref(v_toConstantVal_3898_);
lean_dec(v_val_3894_);
v_name_3899_ = lean_ctor_get(v_toConstantVal_3893_, 0);
lean_inc(v_name_3899_);
lean_dec_ref(v_toConstantVal_3893_);
v_name_3900_ = lean_ctor_get(v_toConstantVal_3898_, 0);
lean_inc(v_name_3900_);
lean_dec_ref(v_toConstantVal_3898_);
v___x_3901_ = lean_name_eq(v_name_3899_, v_name_3900_);
lean_dec(v_name_3900_);
lean_dec(v_name_3899_);
if (v___x_3901_ == 0)
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_Meta_isExprDefEq(v_fst_3878_, v_fst_3880_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3902_) == 0)
{
lean_object* v_a_3903_; uint8_t v___x_3904_; 
v_a_3903_ = lean_ctor_get(v___x_3902_, 0);
lean_inc(v_a_3903_);
lean_dec_ref_known(v___x_3902_, 1);
v___x_3904_ = lean_unbox(v_a_3903_);
lean_dec(v_a_3903_);
if (v___x_3904_ == 0)
{
lean_del_object(v___x_3896_);
lean_del_object(v___x_3889_);
lean_del_object(v___x_3883_);
v___y_3825_ = v_isEq_3868_;
v_isHEq_3826_ = v___x_3681_;
v___y_3827_ = v___y_3869_;
v___y_3828_ = v___y_3870_;
v___y_3829_ = v___y_3871_;
v___y_3830_ = v___y_3872_;
goto v___jp_3824_;
}
else
{
lean_object* v___x_3905_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec_ref(v_config_3670_);
lean_inc(v_mvarId_3671_);
v___x_3905_ = l_Lean_MVarId_getType(v_mvarId_3671_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v_a_3906_; lean_object* v___x_3907_; lean_object* v___x_3908_; 
v_a_3906_ = lean_ctor_get(v___x_3905_, 0);
lean_inc(v_a_3906_);
lean_dec_ref_known(v___x_3905_, 1);
v___x_3907_ = l_Lean_LocalDecl_toExpr(v_val_3702_);
v___x_3908_ = l_Lean_Meta_mkEqOfHEq(v___x_3907_, v___x_3681_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3908_) == 0)
{
lean_object* v_a_3909_; lean_object* v___x_3910_; 
v_a_3909_ = lean_ctor_get(v___x_3908_, 0);
lean_inc(v_a_3909_);
lean_dec_ref_known(v___x_3908_, 1);
v___x_3910_ = l_Lean_Meta_mkNoConfusion(v_a_3906_, v_a_3909_, v___y_3869_, v___y_3870_, v___y_3871_, v___y_3872_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3912_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3671_, v_a_3911_, v___y_3870_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v___x_3913_; lean_object* v___x_3915_; 
lean_dec_ref_known(v___x_3912_, 1);
v___x_3913_ = lean_box(v___x_3681_);
if (v_isShared_3897_ == 0)
{
lean_ctor_set(v___x_3896_, 0, v___x_3913_);
v___x_3915_ = v___x_3896_;
goto v_reusejp_3914_;
}
else
{
lean_object* v_reuseFailAlloc_3922_; 
v_reuseFailAlloc_3922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3922_, 0, v___x_3913_);
v___x_3915_ = v_reuseFailAlloc_3922_;
goto v_reusejp_3914_;
}
v_reusejp_3914_:
{
lean_object* v___x_3917_; 
if (v_isShared_3884_ == 0)
{
lean_ctor_set(v___x_3883_, 1, v___x_3706_);
lean_ctor_set(v___x_3883_, 0, v___x_3915_);
v___x_3917_ = v___x_3883_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3921_; 
v_reuseFailAlloc_3921_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3921_, 0, v___x_3915_);
lean_ctor_set(v_reuseFailAlloc_3921_, 1, v___x_3706_);
v___x_3917_ = v_reuseFailAlloc_3921_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
lean_object* v___x_3919_; 
if (v_isShared_3890_ == 0)
{
lean_ctor_set_tag(v___x_3889_, 0);
lean_ctor_set(v___x_3889_, 0, v___x_3917_);
v___x_3919_ = v___x_3889_;
goto v_reusejp_3918_;
}
else
{
lean_object* v_reuseFailAlloc_3920_; 
v_reuseFailAlloc_3920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3920_, 0, v___x_3917_);
v___x_3919_ = v_reuseFailAlloc_3920_;
goto v_reusejp_3918_;
}
v_reusejp_3918_:
{
v_a_3688_ = v___x_3919_;
goto v___jp_3687_;
}
}
}
}
else
{
lean_object* v_a_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3930_; 
lean_del_object(v___x_3896_);
lean_del_object(v___x_3889_);
lean_del_object(v___x_3883_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
v_a_3923_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3930_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3930_ == 0)
{
v___x_3925_ = v___x_3912_;
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_a_3923_);
lean_dec(v___x_3912_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3930_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3928_; 
if (v_isShared_3926_ == 0)
{
v___x_3928_ = v___x_3925_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3929_; 
v_reuseFailAlloc_3929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3929_, 0, v_a_3923_);
v___x_3928_ = v_reuseFailAlloc_3929_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
return v___x_3928_;
}
}
}
}
else
{
lean_object* v_a_3931_; lean_object* v___x_3933_; uint8_t v_isShared_3934_; uint8_t v_isSharedCheck_3938_; 
lean_del_object(v___x_3896_);
lean_del_object(v___x_3889_);
lean_del_object(v___x_3883_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_3931_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3933_ = v___x_3910_;
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
else
{
lean_inc(v_a_3931_);
lean_dec(v___x_3910_);
v___x_3933_ = lean_box(0);
v_isShared_3934_ = v_isSharedCheck_3938_;
goto v_resetjp_3932_;
}
v_resetjp_3932_:
{
lean_object* v___x_3936_; 
if (v_isShared_3934_ == 0)
{
v___x_3936_ = v___x_3933_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v_a_3931_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3946_; 
lean_dec(v_a_3906_);
lean_del_object(v___x_3896_);
lean_del_object(v___x_3889_);
lean_del_object(v___x_3883_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_3939_ = lean_ctor_get(v___x_3908_, 0);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3908_);
if (v_isSharedCheck_3946_ == 0)
{
v___x_3941_ = v___x_3908_;
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3908_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3946_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
lean_object* v___x_3944_; 
if (v_isShared_3942_ == 0)
{
v___x_3944_ = v___x_3941_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_a_3939_);
v___x_3944_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
return v___x_3944_;
}
}
}
}
else
{
lean_object* v_a_3947_; lean_object* v___x_3949_; uint8_t v_isShared_3950_; uint8_t v_isSharedCheck_3954_; 
lean_del_object(v___x_3896_);
lean_del_object(v___x_3889_);
lean_del_object(v___x_3883_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_3947_ = lean_ctor_get(v___x_3905_, 0);
v_isSharedCheck_3954_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3954_ == 0)
{
v___x_3949_ = v___x_3905_;
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
else
{
lean_inc(v_a_3947_);
lean_dec(v___x_3905_);
v___x_3949_ = lean_box(0);
v_isShared_3950_ = v_isSharedCheck_3954_;
goto v_resetjp_3948_;
}
v_resetjp_3948_:
{
lean_object* v___x_3952_; 
if (v_isShared_3950_ == 0)
{
v___x_3952_ = v___x_3949_;
goto v_reusejp_3951_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
v___x_3952_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3951_;
}
v_reusejp_3951_:
{
return v___x_3952_;
}
}
}
}
}
else
{
lean_object* v_a_3955_; lean_object* v___x_3957_; uint8_t v_isShared_3958_; uint8_t v_isSharedCheck_3962_; 
lean_del_object(v___x_3896_);
lean_del_object(v___x_3889_);
lean_del_object(v___x_3883_);
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_3955_ = lean_ctor_get(v___x_3902_, 0);
v_isSharedCheck_3962_ = !lean_is_exclusive(v___x_3902_);
if (v_isSharedCheck_3962_ == 0)
{
v___x_3957_ = v___x_3902_;
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
else
{
lean_inc(v_a_3955_);
lean_dec(v___x_3902_);
v___x_3957_ = lean_box(0);
v_isShared_3958_ = v_isSharedCheck_3962_;
goto v_resetjp_3956_;
}
v_resetjp_3956_:
{
lean_object* v___x_3960_; 
if (v_isShared_3958_ == 0)
{
v___x_3960_ = v___x_3957_;
goto v_reusejp_3959_;
}
else
{
lean_object* v_reuseFailAlloc_3961_; 
v_reuseFailAlloc_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
v___x_3960_ = v_reuseFailAlloc_3961_;
goto v_reusejp_3959_;
}
v_reusejp_3959_:
{
return v___x_3960_;
}
}
}
}
else
{
lean_del_object(v___x_3896_);
lean_del_object(v___x_3889_);
lean_del_object(v___x_3883_);
lean_dec(v_fst_3880_);
lean_dec(v_fst_3878_);
v___y_3825_ = v_isEq_3868_;
v_isHEq_3826_ = v___x_3681_;
v___y_3827_ = v___y_3869_;
v___y_3828_ = v___y_3870_;
v___y_3829_ = v___y_3871_;
v___y_3830_ = v___y_3872_;
goto v___jp_3824_;
}
}
}
else
{
lean_dec(v_a_3892_);
lean_del_object(v___x_3889_);
lean_dec(v_val_3887_);
lean_del_object(v___x_3883_);
lean_dec(v_fst_3880_);
lean_dec(v_fst_3878_);
v___y_3825_ = v_isEq_3868_;
v_isHEq_3826_ = v___x_3681_;
v___y_3827_ = v___y_3869_;
v___y_3828_ = v___y_3870_;
v___y_3829_ = v___y_3871_;
v___y_3830_ = v___y_3872_;
goto v___jp_3824_;
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_del_object(v___x_3889_);
lean_dec(v_val_3887_);
lean_del_object(v___x_3883_);
lean_dec(v_fst_3880_);
lean_dec(v_fst_3878_);
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_3964_ = lean_ctor_get(v___x_3891_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3891_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3891_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3891_);
v___x_3966_ = lean_box(0);
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
v_resetjp_3965_:
{
lean_object* v___x_3969_; 
if (v_isShared_3967_ == 0)
{
v___x_3969_ = v___x_3966_;
goto v_reusejp_3968_;
}
else
{
lean_object* v_reuseFailAlloc_3970_; 
v_reuseFailAlloc_3970_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3970_, 0, v_a_3964_);
v___x_3969_ = v_reuseFailAlloc_3970_;
goto v_reusejp_3968_;
}
v_reusejp_3968_:
{
return v___x_3969_;
}
}
}
}
}
else
{
lean_dec(v_a_3886_);
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_fst_3880_);
lean_dec(v_fst_3878_);
v___y_3825_ = v_isEq_3868_;
v_isHEq_3826_ = v___x_3681_;
v___y_3827_ = v___y_3869_;
v___y_3828_ = v___y_3870_;
v___y_3829_ = v___y_3871_;
v___y_3830_ = v___y_3872_;
goto v___jp_3824_;
}
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_del_object(v___x_3883_);
lean_dec(v_snd_3881_);
lean_dec(v_fst_3880_);
lean_dec(v_fst_3878_);
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_3973_ = lean_ctor_get(v___x_3885_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3885_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3885_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3885_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
v___x_3978_ = v_reuseFailAlloc_3979_;
goto v_reusejp_3977_;
}
v_reusejp_3977_:
{
return v___x_3978_;
}
}
}
}
}
else
{
lean_dec(v_a_3874_);
v___y_3825_ = v_isEq_3868_;
v_isHEq_3826_ = v___x_3735_;
v___y_3827_ = v___y_3869_;
v___y_3828_ = v___y_3870_;
v___y_3829_ = v___y_3871_;
v___y_3830_ = v___y_3872_;
goto v___jp_3824_;
}
}
else
{
lean_object* v_a_3982_; lean_object* v___x_3984_; uint8_t v_isShared_3985_; uint8_t v_isSharedCheck_3989_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_3982_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3989_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3989_ == 0)
{
v___x_3984_ = v___x_3873_;
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
else
{
lean_inc(v_a_3982_);
lean_dec(v___x_3873_);
v___x_3984_ = lean_box(0);
v_isShared_3985_ = v_isSharedCheck_3989_;
goto v_resetjp_3983_;
}
v_resetjp_3983_:
{
lean_object* v___x_3987_; 
if (v_isShared_3985_ == 0)
{
v___x_3987_ = v___x_3984_;
goto v_reusejp_3986_;
}
else
{
lean_object* v_reuseFailAlloc_3988_; 
v_reuseFailAlloc_3988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3988_, 0, v_a_3982_);
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
v___jp_3990_:
{
lean_object* v___x_3995_; 
lean_inc_ref(v___x_3736_);
v___x_3995_ = l_Lean_Meta_matchEq_x3f(v___x_3736_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_3995_) == 0)
{
lean_object* v_a_3996_; 
v_a_3996_ = lean_ctor_get(v___x_3995_, 0);
lean_inc(v_a_3996_);
lean_dec_ref_known(v___x_3995_, 1);
if (lean_obj_tag(v_a_3996_) == 1)
{
lean_object* v_val_3997_; lean_object* v_snd_3998_; lean_object* v_fst_3999_; lean_object* v_snd_4000_; lean_object* v___x_4002_; uint8_t v_isShared_4003_; uint8_t v_isSharedCheck_4079_; 
v_val_3997_ = lean_ctor_get(v_a_3996_, 0);
lean_inc(v_val_3997_);
lean_dec_ref_known(v_a_3996_, 1);
v_snd_3998_ = lean_ctor_get(v_val_3997_, 1);
lean_inc(v_snd_3998_);
lean_dec(v_val_3997_);
v_fst_3999_ = lean_ctor_get(v_snd_3998_, 0);
v_snd_4000_ = lean_ctor_get(v_snd_3998_, 1);
v_isSharedCheck_4079_ = !lean_is_exclusive(v_snd_3998_);
if (v_isSharedCheck_4079_ == 0)
{
v___x_4002_ = v_snd_3998_;
v_isShared_4003_ = v_isSharedCheck_4079_;
goto v_resetjp_4001_;
}
else
{
lean_inc(v_snd_4000_);
lean_inc(v_fst_3999_);
lean_dec(v_snd_3998_);
v___x_4002_ = lean_box(0);
v_isShared_4003_ = v_isSharedCheck_4079_;
goto v_resetjp_4001_;
}
v_resetjp_4001_:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3999_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_4004_) == 0)
{
lean_object* v_a_4005_; 
v_a_4005_ = lean_ctor_get(v___x_4004_, 0);
lean_inc(v_a_4005_);
lean_dec_ref_known(v___x_4004_, 1);
if (lean_obj_tag(v_a_4005_) == 1)
{
lean_object* v_val_4006_; lean_object* v___x_4008_; uint8_t v_isShared_4009_; uint8_t v_isSharedCheck_4070_; 
v_val_4006_ = lean_ctor_get(v_a_4005_, 0);
v_isSharedCheck_4070_ = !lean_is_exclusive(v_a_4005_);
if (v_isSharedCheck_4070_ == 0)
{
v___x_4008_ = v_a_4005_;
v_isShared_4009_ = v_isSharedCheck_4070_;
goto v_resetjp_4007_;
}
else
{
lean_inc(v_val_4006_);
lean_dec(v_a_4005_);
v___x_4008_ = lean_box(0);
v_isShared_4009_ = v_isSharedCheck_4070_;
goto v_resetjp_4007_;
}
v_resetjp_4007_:
{
lean_object* v___x_4010_; 
v___x_4010_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4000_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_4010_) == 0)
{
lean_object* v_a_4011_; 
v_a_4011_ = lean_ctor_get(v___x_4010_, 0);
lean_inc(v_a_4011_);
lean_dec_ref_known(v___x_4010_, 1);
if (lean_obj_tag(v_a_4011_) == 1)
{
lean_object* v_toConstantVal_4012_; lean_object* v_val_4013_; lean_object* v___x_4015_; uint8_t v_isShared_4016_; uint8_t v_isSharedCheck_4061_; 
v_toConstantVal_4012_ = lean_ctor_get(v_val_4006_, 0);
lean_inc_ref(v_toConstantVal_4012_);
lean_dec(v_val_4006_);
v_val_4013_ = lean_ctor_get(v_a_4011_, 0);
v_isSharedCheck_4061_ = !lean_is_exclusive(v_a_4011_);
if (v_isSharedCheck_4061_ == 0)
{
v___x_4015_ = v_a_4011_;
v_isShared_4016_ = v_isSharedCheck_4061_;
goto v_resetjp_4014_;
}
else
{
lean_inc(v_val_4013_);
lean_dec(v_a_4011_);
v___x_4015_ = lean_box(0);
v_isShared_4016_ = v_isSharedCheck_4061_;
goto v_resetjp_4014_;
}
v_resetjp_4014_:
{
lean_object* v_toConstantVal_4017_; lean_object* v_name_4018_; lean_object* v_name_4019_; uint8_t v___x_4020_; 
v_toConstantVal_4017_ = lean_ctor_get(v_val_4013_, 0);
lean_inc_ref(v_toConstantVal_4017_);
lean_dec(v_val_4013_);
v_name_4018_ = lean_ctor_get(v_toConstantVal_4012_, 0);
lean_inc(v_name_4018_);
lean_dec_ref(v_toConstantVal_4012_);
v_name_4019_ = lean_ctor_get(v_toConstantVal_4017_, 0);
lean_inc(v_name_4019_);
lean_dec_ref(v_toConstantVal_4017_);
v___x_4020_ = lean_name_eq(v_name_4018_, v_name_4019_);
lean_dec(v_name_4019_);
lean_dec(v_name_4018_);
if (v___x_4020_ == 0)
{
lean_object* v___x_4021_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec_ref(v_config_3670_);
lean_inc(v_mvarId_3671_);
v___x_4021_ = l_Lean_MVarId_getType(v_mvarId_3671_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_4021_) == 0)
{
lean_object* v_a_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; 
v_a_4022_ = lean_ctor_get(v___x_4021_, 0);
lean_inc(v_a_4022_);
lean_dec_ref_known(v___x_4021_, 1);
v___x_4023_ = l_Lean_LocalDecl_toExpr(v_val_3702_);
v___x_4024_ = l_Lean_Meta_mkNoConfusion(v_a_4022_, v___x_4023_, v___y_3991_, v___y_3992_, v___y_3993_, v___y_3994_);
if (lean_obj_tag(v___x_4024_) == 0)
{
lean_object* v_a_4025_; lean_object* v___x_4026_; 
v_a_4025_ = lean_ctor_get(v___x_4024_, 0);
lean_inc(v_a_4025_);
lean_dec_ref_known(v___x_4024_, 1);
v___x_4026_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3671_, v_a_4025_, v___y_3992_);
if (lean_obj_tag(v___x_4026_) == 0)
{
lean_object* v___x_4027_; lean_object* v___x_4029_; 
lean_dec_ref_known(v___x_4026_, 1);
v___x_4027_ = lean_box(v___x_3681_);
if (v_isShared_4016_ == 0)
{
lean_ctor_set(v___x_4015_, 0, v___x_4027_);
v___x_4029_ = v___x_4015_;
goto v_reusejp_4028_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4027_);
v___x_4029_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4028_;
}
v_reusejp_4028_:
{
lean_object* v___x_4031_; 
if (v_isShared_4003_ == 0)
{
lean_ctor_set(v___x_4002_, 1, v___x_3706_);
lean_ctor_set(v___x_4002_, 0, v___x_4029_);
v___x_4031_ = v___x_4002_;
goto v_reusejp_4030_;
}
else
{
lean_object* v_reuseFailAlloc_4035_; 
v_reuseFailAlloc_4035_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4035_, 0, v___x_4029_);
lean_ctor_set(v_reuseFailAlloc_4035_, 1, v___x_3706_);
v___x_4031_ = v_reuseFailAlloc_4035_;
goto v_reusejp_4030_;
}
v_reusejp_4030_:
{
lean_object* v___x_4033_; 
if (v_isShared_4009_ == 0)
{
lean_ctor_set_tag(v___x_4008_, 0);
lean_ctor_set(v___x_4008_, 0, v___x_4031_);
v___x_4033_ = v___x_4008_;
goto v_reusejp_4032_;
}
else
{
lean_object* v_reuseFailAlloc_4034_; 
v_reuseFailAlloc_4034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4034_, 0, v___x_4031_);
v___x_4033_ = v_reuseFailAlloc_4034_;
goto v_reusejp_4032_;
}
v_reusejp_4032_:
{
v_a_3688_ = v___x_4033_;
goto v___jp_3687_;
}
}
}
}
else
{
lean_object* v_a_4037_; lean_object* v___x_4039_; uint8_t v_isShared_4040_; uint8_t v_isSharedCheck_4044_; 
lean_del_object(v___x_4015_);
lean_del_object(v___x_4008_);
lean_del_object(v___x_4002_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
v_a_4037_ = lean_ctor_get(v___x_4026_, 0);
v_isSharedCheck_4044_ = !lean_is_exclusive(v___x_4026_);
if (v_isSharedCheck_4044_ == 0)
{
v___x_4039_ = v___x_4026_;
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
else
{
lean_inc(v_a_4037_);
lean_dec(v___x_4026_);
v___x_4039_ = lean_box(0);
v_isShared_4040_ = v_isSharedCheck_4044_;
goto v_resetjp_4038_;
}
v_resetjp_4038_:
{
lean_object* v___x_4042_; 
if (v_isShared_4040_ == 0)
{
v___x_4042_ = v___x_4039_;
goto v_reusejp_4041_;
}
else
{
lean_object* v_reuseFailAlloc_4043_; 
v_reuseFailAlloc_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4043_, 0, v_a_4037_);
v___x_4042_ = v_reuseFailAlloc_4043_;
goto v_reusejp_4041_;
}
v_reusejp_4041_:
{
return v___x_4042_;
}
}
}
}
else
{
lean_object* v_a_4045_; lean_object* v___x_4047_; uint8_t v_isShared_4048_; uint8_t v_isSharedCheck_4052_; 
lean_del_object(v___x_4015_);
lean_del_object(v___x_4008_);
lean_del_object(v___x_4002_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_4045_ = lean_ctor_get(v___x_4024_, 0);
v_isSharedCheck_4052_ = !lean_is_exclusive(v___x_4024_);
if (v_isSharedCheck_4052_ == 0)
{
v___x_4047_ = v___x_4024_;
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
else
{
lean_inc(v_a_4045_);
lean_dec(v___x_4024_);
v___x_4047_ = lean_box(0);
v_isShared_4048_ = v_isSharedCheck_4052_;
goto v_resetjp_4046_;
}
v_resetjp_4046_:
{
lean_object* v___x_4050_; 
if (v_isShared_4048_ == 0)
{
v___x_4050_ = v___x_4047_;
goto v_reusejp_4049_;
}
else
{
lean_object* v_reuseFailAlloc_4051_; 
v_reuseFailAlloc_4051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4051_, 0, v_a_4045_);
v___x_4050_ = v_reuseFailAlloc_4051_;
goto v_reusejp_4049_;
}
v_reusejp_4049_:
{
return v___x_4050_;
}
}
}
}
else
{
lean_object* v_a_4053_; lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4060_; 
lean_del_object(v___x_4015_);
lean_del_object(v___x_4008_);
lean_del_object(v___x_4002_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_4053_ = lean_ctor_get(v___x_4021_, 0);
v_isSharedCheck_4060_ = !lean_is_exclusive(v___x_4021_);
if (v_isSharedCheck_4060_ == 0)
{
v___x_4055_ = v___x_4021_;
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
else
{
lean_inc(v_a_4053_);
lean_dec(v___x_4021_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4060_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4058_; 
if (v_isShared_4056_ == 0)
{
v___x_4058_ = v___x_4055_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4059_; 
v_reuseFailAlloc_4059_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4059_, 0, v_a_4053_);
v___x_4058_ = v_reuseFailAlloc_4059_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
return v___x_4058_;
}
}
}
}
else
{
lean_del_object(v___x_4015_);
lean_del_object(v___x_4008_);
lean_del_object(v___x_4002_);
v_isEq_3868_ = v___x_3681_;
v___y_3869_ = v___y_3991_;
v___y_3870_ = v___y_3992_;
v___y_3871_ = v___y_3993_;
v___y_3872_ = v___y_3994_;
goto v___jp_3867_;
}
}
}
else
{
lean_dec(v_a_4011_);
lean_del_object(v___x_4008_);
lean_dec(v_val_4006_);
lean_del_object(v___x_4002_);
v_isEq_3868_ = v___x_3681_;
v___y_3869_ = v___y_3991_;
v___y_3870_ = v___y_3992_;
v___y_3871_ = v___y_3993_;
v___y_3872_ = v___y_3994_;
goto v___jp_3867_;
}
}
else
{
lean_object* v_a_4062_; lean_object* v___x_4064_; uint8_t v_isShared_4065_; uint8_t v_isSharedCheck_4069_; 
lean_del_object(v___x_4008_);
lean_dec(v_val_4006_);
lean_del_object(v___x_4002_);
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_4062_ = lean_ctor_get(v___x_4010_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4010_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4064_ = v___x_4010_;
v_isShared_4065_ = v_isSharedCheck_4069_;
goto v_resetjp_4063_;
}
else
{
lean_inc(v_a_4062_);
lean_dec(v___x_4010_);
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
else
{
lean_dec(v_a_4005_);
lean_del_object(v___x_4002_);
lean_dec(v_snd_4000_);
v_isEq_3868_ = v___x_3681_;
v___y_3869_ = v___y_3991_;
v___y_3870_ = v___y_3992_;
v___y_3871_ = v___y_3993_;
v___y_3872_ = v___y_3994_;
goto v___jp_3867_;
}
}
else
{
lean_object* v_a_4071_; lean_object* v___x_4073_; uint8_t v_isShared_4074_; uint8_t v_isSharedCheck_4078_; 
lean_del_object(v___x_4002_);
lean_dec(v_snd_4000_);
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_4071_ = lean_ctor_get(v___x_4004_, 0);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4004_);
if (v_isSharedCheck_4078_ == 0)
{
v___x_4073_ = v___x_4004_;
v_isShared_4074_ = v_isSharedCheck_4078_;
goto v_resetjp_4072_;
}
else
{
lean_inc(v_a_4071_);
lean_dec(v___x_4004_);
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
else
{
lean_dec(v_a_3996_);
v_isEq_3868_ = v___x_3735_;
v___y_3869_ = v___y_3991_;
v___y_3870_ = v___y_3992_;
v___y_3871_ = v___y_3993_;
v___y_3872_ = v___y_3994_;
goto v___jp_3867_;
}
}
else
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4087_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_4080_ = lean_ctor_get(v___x_3995_, 0);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_3995_);
if (v_isSharedCheck_4087_ == 0)
{
v___x_4082_ = v___x_3995_;
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_3995_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4087_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4085_; 
if (v_isShared_4083_ == 0)
{
v___x_4085_ = v___x_4082_;
goto v_reusejp_4084_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v_a_4080_);
v___x_4085_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4084_;
}
v_reusejp_4084_:
{
return v___x_4085_;
}
}
}
}
v___jp_4088_:
{
lean_object* v___x_4093_; 
lean_inc_ref(v___x_3736_);
v___x_4093_ = l_Lean_refutableHasNotBit_x3f(v___x_3736_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4093_) == 0)
{
lean_object* v_a_4094_; 
v_a_4094_ = lean_ctor_get(v___x_4093_, 0);
lean_inc(v_a_4094_);
lean_dec_ref_known(v___x_4093_, 1);
if (lean_obj_tag(v_a_4094_) == 1)
{
lean_object* v_val_4095_; lean_object* v___x_4097_; uint8_t v_isShared_4098_; uint8_t v_isSharedCheck_4135_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec_ref(v_config_3670_);
v_val_4095_ = lean_ctor_get(v_a_4094_, 0);
v_isSharedCheck_4135_ = !lean_is_exclusive(v_a_4094_);
if (v_isSharedCheck_4135_ == 0)
{
v___x_4097_ = v_a_4094_;
v_isShared_4098_ = v_isSharedCheck_4135_;
goto v_resetjp_4096_;
}
else
{
lean_inc(v_val_4095_);
lean_dec(v_a_4094_);
v___x_4097_ = lean_box(0);
v_isShared_4098_ = v_isSharedCheck_4135_;
goto v_resetjp_4096_;
}
v_resetjp_4096_:
{
lean_object* v___x_4099_; 
lean_inc(v_mvarId_3671_);
v___x_4099_ = l_Lean_MVarId_getType(v_mvarId_3671_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref_known(v___x_4099_, 1);
v___x_4101_ = l_Lean_LocalDecl_toExpr(v_val_3702_);
v___x_4102_ = l_Lean_Meta_mkAbsurd(v_a_4100_, v_val_4095_, v___x_4101_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4102_) == 0)
{
lean_object* v_a_4103_; lean_object* v___x_4104_; 
v_a_4103_ = lean_ctor_get(v___x_4102_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v___x_4102_, 1);
v___x_4104_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3671_, v_a_4103_, v___y_4090_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v___x_4105_; lean_object* v___x_4107_; 
lean_dec_ref_known(v___x_4104_, 1);
v___x_4105_ = lean_box(v___x_3681_);
if (v_isShared_4098_ == 0)
{
lean_ctor_set(v___x_4097_, 0, v___x_4105_);
v___x_4107_ = v___x_4097_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4105_);
v___x_4107_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
lean_ctor_set(v___x_4108_, 1, v___x_3706_);
v___x_4109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4108_);
v_a_3688_ = v___x_4109_;
goto v___jp_3687_;
}
}
else
{
lean_object* v_a_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4118_; 
lean_del_object(v___x_4097_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
v_a_4111_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4118_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4118_ == 0)
{
v___x_4113_ = v___x_4104_;
v_isShared_4114_ = v_isSharedCheck_4118_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_a_4111_);
lean_dec(v___x_4104_);
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
else
{
lean_object* v_a_4119_; lean_object* v___x_4121_; uint8_t v_isShared_4122_; uint8_t v_isSharedCheck_4126_; 
lean_del_object(v___x_4097_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_4119_ = lean_ctor_get(v___x_4102_, 0);
v_isSharedCheck_4126_ = !lean_is_exclusive(v___x_4102_);
if (v_isSharedCheck_4126_ == 0)
{
v___x_4121_ = v___x_4102_;
v_isShared_4122_ = v_isSharedCheck_4126_;
goto v_resetjp_4120_;
}
else
{
lean_inc(v_a_4119_);
lean_dec(v___x_4102_);
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
else
{
lean_object* v_a_4127_; lean_object* v___x_4129_; uint8_t v_isShared_4130_; uint8_t v_isSharedCheck_4134_; 
lean_del_object(v___x_4097_);
lean_dec(v_val_4095_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_4127_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4134_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4134_ == 0)
{
v___x_4129_ = v___x_4099_;
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
else
{
lean_inc(v_a_4127_);
lean_dec(v___x_4099_);
v___x_4129_ = lean_box(0);
v_isShared_4130_ = v_isSharedCheck_4134_;
goto v_resetjp_4128_;
}
v_resetjp_4128_:
{
lean_object* v___x_4132_; 
if (v_isShared_4130_ == 0)
{
v___x_4132_ = v___x_4129_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v_a_4127_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
}
}
}
else
{
lean_object* v___x_4136_; 
lean_dec(v_a_4094_);
lean_inc_ref(v___x_3736_);
v___x_4136_ = l_Lean_Meta_matchNe_x3f(v___x_3736_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v___x_4136_, 1);
if (lean_obj_tag(v_a_4137_) == 1)
{
lean_object* v_val_4138_; lean_object* v___x_4140_; uint8_t v_isShared_4141_; uint8_t v_isSharedCheck_4208_; 
v_val_4138_ = lean_ctor_get(v_a_4137_, 0);
v_isSharedCheck_4208_ = !lean_is_exclusive(v_a_4137_);
if (v_isSharedCheck_4208_ == 0)
{
v___x_4140_ = v_a_4137_;
v_isShared_4141_ = v_isSharedCheck_4208_;
goto v_resetjp_4139_;
}
else
{
lean_inc(v_val_4138_);
lean_dec(v_a_4137_);
v___x_4140_ = lean_box(0);
v_isShared_4141_ = v_isSharedCheck_4208_;
goto v_resetjp_4139_;
}
v_resetjp_4139_:
{
lean_object* v_snd_4142_; lean_object* v_fst_4143_; lean_object* v_snd_4144_; lean_object* v___x_4146_; uint8_t v_isShared_4147_; uint8_t v_isSharedCheck_4207_; 
v_snd_4142_ = lean_ctor_get(v_val_4138_, 1);
lean_inc(v_snd_4142_);
lean_dec(v_val_4138_);
v_fst_4143_ = lean_ctor_get(v_snd_4142_, 0);
v_snd_4144_ = lean_ctor_get(v_snd_4142_, 1);
v_isSharedCheck_4207_ = !lean_is_exclusive(v_snd_4142_);
if (v_isSharedCheck_4207_ == 0)
{
v___x_4146_ = v_snd_4142_;
v_isShared_4147_ = v_isSharedCheck_4207_;
goto v_resetjp_4145_;
}
else
{
lean_inc(v_snd_4144_);
lean_inc(v_fst_4143_);
lean_dec(v_snd_4142_);
v___x_4146_ = lean_box(0);
v_isShared_4147_ = v_isSharedCheck_4207_;
goto v_resetjp_4145_;
}
v_resetjp_4145_:
{
lean_object* v___x_4148_; 
lean_inc(v_fst_4143_);
v___x_4148_ = l_Lean_Meta_isExprDefEq(v_fst_4143_, v_snd_4144_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4148_) == 0)
{
lean_object* v_a_4149_; uint8_t v___x_4150_; 
v_a_4149_ = lean_ctor_get(v___x_4148_, 0);
lean_inc(v_a_4149_);
lean_dec_ref_known(v___x_4148_, 1);
v___x_4150_ = lean_unbox(v_a_4149_);
lean_dec(v_a_4149_);
if (v___x_4150_ == 0)
{
lean_del_object(v___x_4146_);
lean_dec(v_fst_4143_);
lean_del_object(v___x_4140_);
v___y_3991_ = v___y_4089_;
v___y_3992_ = v___y_4090_;
v___y_3993_ = v___y_4091_;
v___y_3994_ = v___y_4092_;
goto v___jp_3990_;
}
else
{
lean_object* v___x_4151_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec_ref(v_config_3670_);
lean_inc(v_mvarId_3671_);
v___x_4151_ = l_Lean_MVarId_getType(v_mvarId_3671_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4151_) == 0)
{
lean_object* v_a_4152_; lean_object* v___x_4153_; 
v_a_4152_ = lean_ctor_get(v___x_4151_, 0);
lean_inc(v_a_4152_);
lean_dec_ref_known(v___x_4151_, 1);
v___x_4153_ = l_Lean_Meta_mkEqRefl(v_fst_4143_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4153_) == 0)
{
lean_object* v_a_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; 
v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
lean_inc(v_a_4154_);
lean_dec_ref_known(v___x_4153_, 1);
v___x_4155_ = l_Lean_LocalDecl_toExpr(v_val_3702_);
v___x_4156_ = l_Lean_Meta_mkAbsurd(v_a_4152_, v_a_4154_, v___x_4155_, v___y_4089_, v___y_4090_, v___y_4091_, v___y_4092_);
if (lean_obj_tag(v___x_4156_) == 0)
{
lean_object* v_a_4157_; lean_object* v___x_4158_; 
v_a_4157_ = lean_ctor_get(v___x_4156_, 0);
lean_inc(v_a_4157_);
lean_dec_ref_known(v___x_4156_, 1);
v___x_4158_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3671_, v_a_4157_, v___y_4090_);
if (lean_obj_tag(v___x_4158_) == 0)
{
lean_object* v___x_4159_; lean_object* v___x_4161_; 
lean_dec_ref_known(v___x_4158_, 1);
v___x_4159_ = lean_box(v___x_3681_);
if (v_isShared_4141_ == 0)
{
lean_ctor_set(v___x_4140_, 0, v___x_4159_);
v___x_4161_ = v___x_4140_;
goto v_reusejp_4160_;
}
else
{
lean_object* v_reuseFailAlloc_4166_; 
v_reuseFailAlloc_4166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4166_, 0, v___x_4159_);
v___x_4161_ = v_reuseFailAlloc_4166_;
goto v_reusejp_4160_;
}
v_reusejp_4160_:
{
lean_object* v___x_4163_; 
if (v_isShared_4147_ == 0)
{
lean_ctor_set(v___x_4146_, 1, v___x_3706_);
lean_ctor_set(v___x_4146_, 0, v___x_4161_);
v___x_4163_ = v___x_4146_;
goto v_reusejp_4162_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v___x_4161_);
lean_ctor_set(v_reuseFailAlloc_4165_, 1, v___x_3706_);
v___x_4163_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4162_;
}
v_reusejp_4162_:
{
lean_object* v___x_4164_; 
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
v_a_3688_ = v___x_4164_;
goto v___jp_3687_;
}
}
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_del_object(v___x_4146_);
lean_del_object(v___x_4140_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
v_a_4167_ = lean_ctor_get(v___x_4158_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4158_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4158_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4158_);
v___x_4169_ = lean_box(0);
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
v_resetjp_4168_:
{
lean_object* v___x_4172_; 
if (v_isShared_4170_ == 0)
{
v___x_4172_ = v___x_4169_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v_a_4167_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
else
{
lean_object* v_a_4175_; lean_object* v___x_4177_; uint8_t v_isShared_4178_; uint8_t v_isSharedCheck_4182_; 
lean_del_object(v___x_4146_);
lean_del_object(v___x_4140_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_4175_ = lean_ctor_get(v___x_4156_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4156_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4156_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4156_);
v___x_4177_ = lean_box(0);
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
v_resetjp_4176_:
{
lean_object* v___x_4180_; 
if (v_isShared_4178_ == 0)
{
v___x_4180_ = v___x_4177_;
goto v_reusejp_4179_;
}
else
{
lean_object* v_reuseFailAlloc_4181_; 
v_reuseFailAlloc_4181_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4181_, 0, v_a_4175_);
v___x_4180_ = v_reuseFailAlloc_4181_;
goto v_reusejp_4179_;
}
v_reusejp_4179_:
{
return v___x_4180_;
}
}
}
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
lean_dec(v_a_4152_);
lean_del_object(v___x_4146_);
lean_del_object(v___x_4140_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_4183_ = lean_ctor_get(v___x_4153_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4153_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4153_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4153_);
v___x_4185_ = lean_box(0);
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
v_resetjp_4184_:
{
lean_object* v___x_4188_; 
if (v_isShared_4186_ == 0)
{
v___x_4188_ = v___x_4185_;
goto v_reusejp_4187_;
}
else
{
lean_object* v_reuseFailAlloc_4189_; 
v_reuseFailAlloc_4189_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4189_, 0, v_a_4183_);
v___x_4188_ = v_reuseFailAlloc_4189_;
goto v_reusejp_4187_;
}
v_reusejp_4187_:
{
return v___x_4188_;
}
}
}
}
else
{
lean_object* v_a_4191_; lean_object* v___x_4193_; uint8_t v_isShared_4194_; uint8_t v_isSharedCheck_4198_; 
lean_del_object(v___x_4146_);
lean_dec(v_fst_4143_);
lean_del_object(v___x_4140_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
v_a_4191_ = lean_ctor_get(v___x_4151_, 0);
v_isSharedCheck_4198_ = !lean_is_exclusive(v___x_4151_);
if (v_isSharedCheck_4198_ == 0)
{
v___x_4193_ = v___x_4151_;
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
else
{
lean_inc(v_a_4191_);
lean_dec(v___x_4151_);
v___x_4193_ = lean_box(0);
v_isShared_4194_ = v_isSharedCheck_4198_;
goto v_resetjp_4192_;
}
v_resetjp_4192_:
{
lean_object* v___x_4196_; 
if (v_isShared_4194_ == 0)
{
v___x_4196_ = v___x_4193_;
goto v_reusejp_4195_;
}
else
{
lean_object* v_reuseFailAlloc_4197_; 
v_reuseFailAlloc_4197_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4197_, 0, v_a_4191_);
v___x_4196_ = v_reuseFailAlloc_4197_;
goto v_reusejp_4195_;
}
v_reusejp_4195_:
{
return v___x_4196_;
}
}
}
}
}
else
{
lean_object* v_a_4199_; lean_object* v___x_4201_; uint8_t v_isShared_4202_; uint8_t v_isSharedCheck_4206_; 
lean_del_object(v___x_4146_);
lean_dec(v_fst_4143_);
lean_del_object(v___x_4140_);
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_4199_ = lean_ctor_get(v___x_4148_, 0);
v_isSharedCheck_4206_ = !lean_is_exclusive(v___x_4148_);
if (v_isSharedCheck_4206_ == 0)
{
v___x_4201_ = v___x_4148_;
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
else
{
lean_inc(v_a_4199_);
lean_dec(v___x_4148_);
v___x_4201_ = lean_box(0);
v_isShared_4202_ = v_isSharedCheck_4206_;
goto v_resetjp_4200_;
}
v_resetjp_4200_:
{
lean_object* v___x_4204_; 
if (v_isShared_4202_ == 0)
{
v___x_4204_ = v___x_4201_;
goto v_reusejp_4203_;
}
else
{
lean_object* v_reuseFailAlloc_4205_; 
v_reuseFailAlloc_4205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4205_, 0, v_a_4199_);
v___x_4204_ = v_reuseFailAlloc_4205_;
goto v_reusejp_4203_;
}
v_reusejp_4203_:
{
return v___x_4204_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4137_);
v___y_3991_ = v___y_4089_;
v___y_3992_ = v___y_4090_;
v___y_3993_ = v___y_4091_;
v___y_3994_ = v___y_4092_;
goto v___jp_3990_;
}
}
else
{
lean_object* v_a_4209_; lean_object* v___x_4211_; uint8_t v_isShared_4212_; uint8_t v_isSharedCheck_4216_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_4209_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4216_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4216_ == 0)
{
v___x_4211_ = v___x_4136_;
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
else
{
lean_inc(v_a_4209_);
lean_dec(v___x_4136_);
v___x_4211_ = lean_box(0);
v_isShared_4212_ = v_isSharedCheck_4216_;
goto v_resetjp_4210_;
}
v_resetjp_4210_:
{
lean_object* v___x_4214_; 
if (v_isShared_4212_ == 0)
{
v___x_4214_ = v___x_4211_;
goto v_reusejp_4213_;
}
else
{
lean_object* v_reuseFailAlloc_4215_; 
v_reuseFailAlloc_4215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4215_, 0, v_a_4209_);
v___x_4214_ = v_reuseFailAlloc_4215_;
goto v_reusejp_4213_;
}
v_reusejp_4213_:
{
return v___x_4214_;
}
}
}
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec_ref(v___x_3736_);
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_4217_ = lean_ctor_get(v___x_4093_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4093_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4093_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4093_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4222_; 
if (v_isShared_4220_ == 0)
{
v___x_4222_ = v___x_4219_;
goto v_reusejp_4221_;
}
else
{
lean_object* v_reuseFailAlloc_4223_; 
v_reuseFailAlloc_4223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4223_, 0, v_a_4217_);
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
}
else
{
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
v_a_3696_ = v___x_3707_;
goto v___jp_3695_;
}
v___jp_3708_:
{
uint8_t v_emptyType_3715_; 
v_emptyType_3715_ = lean_ctor_get_uint8(v_config_3670_, sizeof(void*)*1 + 1);
if (v_emptyType_3715_ == 0)
{
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
v_a_3696_ = v___x_3707_;
goto v___jp_3695_;
}
else
{
if (v___y_3710_ == 0)
{
if (v___y_3709_ == 0)
{
lean_object* v_searchFuel_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; 
v_searchFuel_3716_ = lean_ctor_get(v_config_3670_, 0);
v___x_3717_ = l_Lean_LocalDecl_fvarId(v_val_3702_);
lean_dec(v_val_3702_);
lean_inc(v_searchFuel_3716_);
lean_inc(v_mvarId_3671_);
v___x_3718_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3671_, v___x_3717_, v_searchFuel_3716_, v___y_3711_, v___y_3712_, v___y_3713_, v___y_3714_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v_a_3719_; uint8_t v___x_3720_; 
v_a_3719_ = lean_ctor_get(v___x_3718_, 0);
lean_inc(v_a_3719_);
lean_dec_ref_known(v___x_3718_, 1);
v___x_3720_ = lean_unbox(v_a_3719_);
lean_dec(v_a_3719_);
if (v___x_3720_ == 0)
{
lean_del_object(v___x_3704_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
v_a_3696_ = v___x_3707_;
goto v___jp_3695_;
}
else
{
lean_object* v___x_3721_; lean_object* v___x_3723_; 
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v___x_3721_ = lean_box(v___x_3681_);
if (v_isShared_3705_ == 0)
{
lean_ctor_set(v___x_3704_, 0, v___x_3721_);
v___x_3723_ = v___x_3704_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3721_);
v___x_3723_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; lean_object* v___x_3725_; 
v___x_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
lean_ctor_set(v___x_3724_, 1, v___x_3706_);
v___x_3725_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3725_, 0, v___x_3724_);
v_a_3688_ = v___x_3725_;
goto v___jp_3687_;
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_del_object(v___x_3704_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
lean_dec(v_mvarId_3671_);
lean_dec_ref(v_config_3670_);
v_a_3727_ = lean_ctor_get(v___x_3718_, 0);
v_isSharedCheck_3734_ = !lean_is_exclusive(v___x_3718_);
if (v_isSharedCheck_3734_ == 0)
{
v___x_3729_ = v___x_3718_;
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
else
{
lean_inc(v_a_3727_);
lean_dec(v___x_3718_);
v___x_3729_ = lean_box(0);
v_isShared_3730_ = v_isSharedCheck_3734_;
goto v_resetjp_3728_;
}
v_resetjp_3728_:
{
lean_object* v___x_3732_; 
if (v_isShared_3730_ == 0)
{
v___x_3732_ = v___x_3729_;
goto v_reusejp_3731_;
}
else
{
lean_object* v_reuseFailAlloc_3733_; 
v_reuseFailAlloc_3733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3733_, 0, v_a_3727_);
v___x_3732_ = v_reuseFailAlloc_3733_;
goto v_reusejp_3731_;
}
v_reusejp_3731_:
{
return v___x_3732_;
}
}
}
}
else
{
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
v_a_3696_ = v___x_3707_;
goto v___jp_3695_;
}
}
else
{
lean_del_object(v___x_3704_);
lean_dec(v_val_3702_);
lean_del_object(v___x_3685_);
lean_dec(v_snd_3683_);
v_a_3696_ = v___x_3707_;
goto v___jp_3695_;
}
}
}
}
}
v___jp_3687_:
{
lean_object* v___x_3689_; lean_object* v___x_3691_; 
v___x_3689_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3689_, 0, v_a_3688_);
if (v_isShared_3686_ == 0)
{
lean_ctor_set(v___x_3685_, 0, v___x_3689_);
v___x_3691_ = v___x_3685_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v___x_3689_);
lean_ctor_set(v_reuseFailAlloc_3693_, 1, v_snd_3683_);
v___x_3691_ = v_reuseFailAlloc_3693_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
lean_object* v___x_3692_; 
v___x_3692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3692_, 0, v___x_3691_);
return v___x_3692_;
}
}
v___jp_3695_:
{
lean_object* v___x_3697_; size_t v___x_3698_; size_t v___x_3699_; lean_object* v___x_3700_; 
v___x_3697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3697_, 0, v___x_3694_);
lean_ctor_set(v___x_3697_, 1, v_a_3696_);
v___x_3698_ = ((size_t)1ULL);
v___x_3699_ = lean_usize_add(v_i_3674_, v___x_3698_);
v___x_3700_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3670_, v_mvarId_3671_, v_as_3672_, v_sz_3673_, v___x_3699_, v___x_3697_, v___y_3676_, v___y_3677_, v___y_3678_, v___y_3679_);
return v___x_3700_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4298_, lean_object* v_mvarId_4299_, lean_object* v_as_4300_, lean_object* v_sz_4301_, lean_object* v_i_4302_, lean_object* v_b_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_){
_start:
{
size_t v_sz_boxed_4309_; size_t v_i_boxed_4310_; lean_object* v_res_4311_; 
v_sz_boxed_4309_ = lean_unbox_usize(v_sz_4301_);
lean_dec(v_sz_4301_);
v_i_boxed_4310_ = lean_unbox_usize(v_i_4302_);
lean_dec(v_i_4302_);
v_res_4311_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4298_, v_mvarId_4299_, v_as_4300_, v_sz_boxed_4309_, v_i_boxed_4310_, v_b_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
lean_dec(v___y_4307_);
lean_dec_ref(v___y_4306_);
lean_dec(v___y_4305_);
lean_dec_ref(v___y_4304_);
lean_dec_ref(v_as_4300_);
return v_res_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4312_, lean_object* v_config_4313_, lean_object* v_mvarId_4314_, lean_object* v_n_4315_, lean_object* v_b_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
if (lean_obj_tag(v_n_4315_) == 0)
{
lean_object* v_cs_4322_; lean_object* v___x_4323_; lean_object* v___x_4324_; size_t v_sz_4325_; size_t v___x_4326_; lean_object* v___x_4327_; 
v_cs_4322_ = lean_ctor_get(v_n_4315_, 0);
v___x_4323_ = lean_box(0);
v___x_4324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4324_, 0, v___x_4323_);
lean_ctor_set(v___x_4324_, 1, v_b_4316_);
v_sz_4325_ = lean_array_size(v_cs_4322_);
v___x_4326_ = ((size_t)0ULL);
v___x_4327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4312_, v_config_4313_, v_mvarId_4314_, v_cs_4322_, v_sz_4325_, v___x_4326_, v___x_4324_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
if (lean_obj_tag(v___x_4327_) == 0)
{
lean_object* v_a_4328_; lean_object* v___x_4330_; uint8_t v_isShared_4331_; uint8_t v_isSharedCheck_4342_; 
v_a_4328_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4342_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4342_ == 0)
{
v___x_4330_ = v___x_4327_;
v_isShared_4331_ = v_isSharedCheck_4342_;
goto v_resetjp_4329_;
}
else
{
lean_inc(v_a_4328_);
lean_dec(v___x_4327_);
v___x_4330_ = lean_box(0);
v_isShared_4331_ = v_isSharedCheck_4342_;
goto v_resetjp_4329_;
}
v_resetjp_4329_:
{
lean_object* v_fst_4332_; 
v_fst_4332_ = lean_ctor_get(v_a_4328_, 0);
if (lean_obj_tag(v_fst_4332_) == 0)
{
lean_object* v_snd_4333_; lean_object* v___x_4334_; lean_object* v___x_4336_; 
v_snd_4333_ = lean_ctor_get(v_a_4328_, 1);
lean_inc(v_snd_4333_);
lean_dec(v_a_4328_);
v___x_4334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4334_, 0, v_snd_4333_);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 0, v___x_4334_);
v___x_4336_ = v___x_4330_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v___x_4334_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
else
{
lean_object* v_val_4338_; lean_object* v___x_4340_; 
lean_inc_ref(v_fst_4332_);
lean_dec(v_a_4328_);
v_val_4338_ = lean_ctor_get(v_fst_4332_, 0);
lean_inc(v_val_4338_);
lean_dec_ref_known(v_fst_4332_, 1);
if (v_isShared_4331_ == 0)
{
lean_ctor_set(v___x_4330_, 0, v_val_4338_);
v___x_4340_ = v___x_4330_;
goto v_reusejp_4339_;
}
else
{
lean_object* v_reuseFailAlloc_4341_; 
v_reuseFailAlloc_4341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4341_, 0, v_val_4338_);
v___x_4340_ = v_reuseFailAlloc_4341_;
goto v_reusejp_4339_;
}
v_reusejp_4339_:
{
return v___x_4340_;
}
}
}
}
else
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4350_; 
v_a_4343_ = lean_ctor_get(v___x_4327_, 0);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4327_);
if (v_isSharedCheck_4350_ == 0)
{
v___x_4345_ = v___x_4327_;
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4327_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4350_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4348_; 
if (v_isShared_4346_ == 0)
{
v___x_4348_ = v___x_4345_;
goto v_reusejp_4347_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_a_4343_);
v___x_4348_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4347_;
}
v_reusejp_4347_:
{
return v___x_4348_;
}
}
}
}
else
{
lean_object* v_vs_4351_; lean_object* v___x_4352_; lean_object* v___x_4353_; size_t v_sz_4354_; size_t v___x_4355_; lean_object* v___x_4356_; 
v_vs_4351_ = lean_ctor_get(v_n_4315_, 0);
v___x_4352_ = lean_box(0);
v___x_4353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4353_, 0, v___x_4352_);
lean_ctor_set(v___x_4353_, 1, v_b_4316_);
v_sz_4354_ = lean_array_size(v_vs_4351_);
v___x_4355_ = ((size_t)0ULL);
v___x_4356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4313_, v_mvarId_4314_, v_vs_4351_, v_sz_4354_, v___x_4355_, v___x_4353_, v___y_4317_, v___y_4318_, v___y_4319_, v___y_4320_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v___x_4359_; uint8_t v_isShared_4360_; uint8_t v_isSharedCheck_4371_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4371_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4371_ == 0)
{
v___x_4359_ = v___x_4356_;
v_isShared_4360_ = v_isSharedCheck_4371_;
goto v_resetjp_4358_;
}
else
{
lean_inc(v_a_4357_);
lean_dec(v___x_4356_);
v___x_4359_ = lean_box(0);
v_isShared_4360_ = v_isSharedCheck_4371_;
goto v_resetjp_4358_;
}
v_resetjp_4358_:
{
lean_object* v_fst_4361_; 
v_fst_4361_ = lean_ctor_get(v_a_4357_, 0);
if (lean_obj_tag(v_fst_4361_) == 0)
{
lean_object* v_snd_4362_; lean_object* v___x_4363_; lean_object* v___x_4365_; 
v_snd_4362_ = lean_ctor_get(v_a_4357_, 1);
lean_inc(v_snd_4362_);
lean_dec(v_a_4357_);
v___x_4363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4363_, 0, v_snd_4362_);
if (v_isShared_4360_ == 0)
{
lean_ctor_set(v___x_4359_, 0, v___x_4363_);
v___x_4365_ = v___x_4359_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4363_);
v___x_4365_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
return v___x_4365_;
}
}
else
{
lean_object* v_val_4367_; lean_object* v___x_4369_; 
lean_inc_ref(v_fst_4361_);
lean_dec(v_a_4357_);
v_val_4367_ = lean_ctor_get(v_fst_4361_, 0);
lean_inc(v_val_4367_);
lean_dec_ref_known(v_fst_4361_, 1);
if (v_isShared_4360_ == 0)
{
lean_ctor_set(v___x_4359_, 0, v_val_4367_);
v___x_4369_ = v___x_4359_;
goto v_reusejp_4368_;
}
else
{
lean_object* v_reuseFailAlloc_4370_; 
v_reuseFailAlloc_4370_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_val_4367_);
v___x_4369_ = v_reuseFailAlloc_4370_;
goto v_reusejp_4368_;
}
v_reusejp_4368_:
{
return v___x_4369_;
}
}
}
}
else
{
lean_object* v_a_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
v_a_4372_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4356_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_a_4372_);
lean_dec(v___x_4356_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_a_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4380_, lean_object* v_config_4381_, lean_object* v_mvarId_4382_, lean_object* v_as_4383_, size_t v_sz_4384_, size_t v_i_4385_, lean_object* v_b_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
uint8_t v___x_4392_; 
v___x_4392_ = lean_usize_dec_lt(v_i_4385_, v_sz_4384_);
if (v___x_4392_ == 0)
{
lean_object* v___x_4393_; 
lean_dec(v_mvarId_4382_);
lean_dec_ref(v_config_4381_);
v___x_4393_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4393_, 0, v_b_4386_);
return v___x_4393_;
}
else
{
lean_object* v_snd_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4428_; 
v_snd_4394_ = lean_ctor_get(v_b_4386_, 1);
v_isSharedCheck_4428_ = !lean_is_exclusive(v_b_4386_);
if (v_isSharedCheck_4428_ == 0)
{
lean_object* v_unused_4429_; 
v_unused_4429_ = lean_ctor_get(v_b_4386_, 0);
lean_dec(v_unused_4429_);
v___x_4396_ = v_b_4386_;
v_isShared_4397_ = v_isSharedCheck_4428_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_snd_4394_);
lean_dec(v_b_4386_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4428_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; lean_object* v_a_4399_; lean_object* v___x_4400_; 
v___x_4398_ = lean_box(0);
v_a_4399_ = lean_array_uget_borrowed(v_as_4383_, v_i_4385_);
lean_inc(v_snd_4394_);
lean_inc(v_mvarId_4382_);
lean_inc_ref(v_config_4381_);
v___x_4400_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4380_, v_config_4381_, v_mvarId_4382_, v_a_4399_, v_snd_4394_, v___y_4387_, v___y_4388_, v___y_4389_, v___y_4390_);
if (lean_obj_tag(v___x_4400_) == 0)
{
lean_object* v_a_4401_; lean_object* v___x_4403_; uint8_t v_isShared_4404_; uint8_t v_isSharedCheck_4419_; 
v_a_4401_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4403_ = v___x_4400_;
v_isShared_4404_ = v_isSharedCheck_4419_;
goto v_resetjp_4402_;
}
else
{
lean_inc(v_a_4401_);
lean_dec(v___x_4400_);
v___x_4403_ = lean_box(0);
v_isShared_4404_ = v_isSharedCheck_4419_;
goto v_resetjp_4402_;
}
v_resetjp_4402_:
{
if (lean_obj_tag(v_a_4401_) == 0)
{
lean_object* v___x_4405_; lean_object* v___x_4407_; 
lean_dec(v_mvarId_4382_);
lean_dec_ref(v_config_4381_);
v___x_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4405_, 0, v_a_4401_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 0, v___x_4405_);
v___x_4407_ = v___x_4396_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4411_; 
v_reuseFailAlloc_4411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4411_, 0, v___x_4405_);
lean_ctor_set(v_reuseFailAlloc_4411_, 1, v_snd_4394_);
v___x_4407_ = v_reuseFailAlloc_4411_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
lean_object* v___x_4409_; 
if (v_isShared_4404_ == 0)
{
lean_ctor_set(v___x_4403_, 0, v___x_4407_);
v___x_4409_ = v___x_4403_;
goto v_reusejp_4408_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v___x_4407_);
v___x_4409_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4408_;
}
v_reusejp_4408_:
{
return v___x_4409_;
}
}
}
else
{
lean_object* v_a_4412_; lean_object* v___x_4414_; 
lean_del_object(v___x_4403_);
lean_dec(v_snd_4394_);
v_a_4412_ = lean_ctor_get(v_a_4401_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v_a_4401_, 1);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 1, v_a_4412_);
lean_ctor_set(v___x_4396_, 0, v___x_4398_);
v___x_4414_ = v___x_4396_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4418_; 
v_reuseFailAlloc_4418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4418_, 0, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4418_, 1, v_a_4412_);
v___x_4414_ = v_reuseFailAlloc_4418_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
size_t v___x_4415_; size_t v___x_4416_; 
v___x_4415_ = ((size_t)1ULL);
v___x_4416_ = lean_usize_add(v_i_4385_, v___x_4415_);
v_i_4385_ = v___x_4416_;
v_b_4386_ = v___x_4414_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4420_; lean_object* v___x_4422_; uint8_t v_isShared_4423_; uint8_t v_isSharedCheck_4427_; 
lean_del_object(v___x_4396_);
lean_dec(v_snd_4394_);
lean_dec(v_mvarId_4382_);
lean_dec_ref(v_config_4381_);
v_a_4420_ = lean_ctor_get(v___x_4400_, 0);
v_isSharedCheck_4427_ = !lean_is_exclusive(v___x_4400_);
if (v_isSharedCheck_4427_ == 0)
{
v___x_4422_ = v___x_4400_;
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
else
{
lean_inc(v_a_4420_);
lean_dec(v___x_4400_);
v___x_4422_ = lean_box(0);
v_isShared_4423_ = v_isSharedCheck_4427_;
goto v_resetjp_4421_;
}
v_resetjp_4421_:
{
lean_object* v___x_4425_; 
if (v_isShared_4423_ == 0)
{
v___x_4425_ = v___x_4422_;
goto v_reusejp_4424_;
}
else
{
lean_object* v_reuseFailAlloc_4426_; 
v_reuseFailAlloc_4426_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4426_, 0, v_a_4420_);
v___x_4425_ = v_reuseFailAlloc_4426_;
goto v_reusejp_4424_;
}
v_reusejp_4424_:
{
return v___x_4425_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4430_, lean_object* v_config_4431_, lean_object* v_mvarId_4432_, lean_object* v_as_4433_, lean_object* v_sz_4434_, lean_object* v_i_4435_, lean_object* v_b_4436_, lean_object* v___y_4437_, lean_object* v___y_4438_, lean_object* v___y_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_){
_start:
{
size_t v_sz_boxed_4442_; size_t v_i_boxed_4443_; lean_object* v_res_4444_; 
v_sz_boxed_4442_ = lean_unbox_usize(v_sz_4434_);
lean_dec(v_sz_4434_);
v_i_boxed_4443_ = lean_unbox_usize(v_i_4435_);
lean_dec(v_i_4435_);
v_res_4444_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4430_, v_config_4431_, v_mvarId_4432_, v_as_4433_, v_sz_boxed_4442_, v_i_boxed_4443_, v_b_4436_, v___y_4437_, v___y_4438_, v___y_4439_, v___y_4440_);
lean_dec(v___y_4440_);
lean_dec_ref(v___y_4439_);
lean_dec(v___y_4438_);
lean_dec_ref(v___y_4437_);
lean_dec_ref(v_as_4433_);
lean_dec_ref(v_init_4430_);
return v_res_4444_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4445_, lean_object* v_config_4446_, lean_object* v_mvarId_4447_, lean_object* v_n_4448_, lean_object* v_b_4449_, lean_object* v___y_4450_, lean_object* v___y_4451_, lean_object* v___y_4452_, lean_object* v___y_4453_, lean_object* v___y_4454_){
_start:
{
lean_object* v_res_4455_; 
v_res_4455_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4445_, v_config_4446_, v_mvarId_4447_, v_n_4448_, v_b_4449_, v___y_4450_, v___y_4451_, v___y_4452_, v___y_4453_);
lean_dec(v___y_4453_);
lean_dec_ref(v___y_4452_);
lean_dec(v___y_4451_);
lean_dec_ref(v___y_4450_);
lean_dec_ref(v_n_4448_);
lean_dec_ref(v_init_4445_);
return v_res_4455_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4456_, lean_object* v_mvarId_4457_, lean_object* v_t_4458_, lean_object* v_init_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_root_4465_; lean_object* v_tail_4466_; lean_object* v___x_4467_; 
v_root_4465_ = lean_ctor_get(v_t_4458_, 0);
v_tail_4466_ = lean_ctor_get(v_t_4458_, 1);
lean_inc(v_mvarId_4457_);
lean_inc_ref(v_config_4456_);
lean_inc_ref(v_init_4459_);
v___x_4467_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4459_, v_config_4456_, v_mvarId_4457_, v_root_4465_, v_init_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
lean_dec_ref(v_init_4459_);
if (lean_obj_tag(v___x_4467_) == 0)
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4504_; 
v_a_4468_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4504_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4504_ == 0)
{
v___x_4470_ = v___x_4467_;
v_isShared_4471_ = v_isSharedCheck_4504_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4467_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4504_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
if (lean_obj_tag(v_a_4468_) == 0)
{
lean_object* v_a_4472_; lean_object* v___x_4474_; 
lean_dec(v_mvarId_4457_);
lean_dec_ref(v_config_4456_);
v_a_4472_ = lean_ctor_get(v_a_4468_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v_a_4468_, 1);
if (v_isShared_4471_ == 0)
{
lean_ctor_set(v___x_4470_, 0, v_a_4472_);
v___x_4474_ = v___x_4470_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4472_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4477_; lean_object* v___x_4478_; size_t v_sz_4479_; size_t v___x_4480_; lean_object* v___x_4481_; 
lean_del_object(v___x_4470_);
v_a_4476_ = lean_ctor_get(v_a_4468_, 0);
lean_inc(v_a_4476_);
lean_dec_ref_known(v_a_4468_, 1);
v___x_4477_ = lean_box(0);
v___x_4478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4478_, 0, v___x_4477_);
lean_ctor_set(v___x_4478_, 1, v_a_4476_);
v_sz_4479_ = lean_array_size(v_tail_4466_);
v___x_4480_ = ((size_t)0ULL);
v___x_4481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4456_, v_mvarId_4457_, v_tail_4466_, v_sz_4479_, v___x_4480_, v___x_4478_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___x_4484_; uint8_t v_isShared_4485_; uint8_t v_isSharedCheck_4495_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_4484_ = v___x_4481_;
v_isShared_4485_ = v_isSharedCheck_4495_;
goto v_resetjp_4483_;
}
else
{
lean_inc(v_a_4482_);
lean_dec(v___x_4481_);
v___x_4484_ = lean_box(0);
v_isShared_4485_ = v_isSharedCheck_4495_;
goto v_resetjp_4483_;
}
v_resetjp_4483_:
{
lean_object* v_fst_4486_; 
v_fst_4486_ = lean_ctor_get(v_a_4482_, 0);
if (lean_obj_tag(v_fst_4486_) == 0)
{
lean_object* v_snd_4487_; lean_object* v___x_4489_; 
v_snd_4487_ = lean_ctor_get(v_a_4482_, 1);
lean_inc(v_snd_4487_);
lean_dec(v_a_4482_);
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v_snd_4487_);
v___x_4489_ = v___x_4484_;
goto v_reusejp_4488_;
}
else
{
lean_object* v_reuseFailAlloc_4490_; 
v_reuseFailAlloc_4490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4490_, 0, v_snd_4487_);
v___x_4489_ = v_reuseFailAlloc_4490_;
goto v_reusejp_4488_;
}
v_reusejp_4488_:
{
return v___x_4489_;
}
}
else
{
lean_object* v_val_4491_; lean_object* v___x_4493_; 
lean_inc_ref(v_fst_4486_);
lean_dec(v_a_4482_);
v_val_4491_ = lean_ctor_get(v_fst_4486_, 0);
lean_inc(v_val_4491_);
lean_dec_ref_known(v_fst_4486_, 1);
if (v_isShared_4485_ == 0)
{
lean_ctor_set(v___x_4484_, 0, v_val_4491_);
v___x_4493_ = v___x_4484_;
goto v_reusejp_4492_;
}
else
{
lean_object* v_reuseFailAlloc_4494_; 
v_reuseFailAlloc_4494_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_val_4491_);
v___x_4493_ = v_reuseFailAlloc_4494_;
goto v_reusejp_4492_;
}
v_reusejp_4492_:
{
return v___x_4493_;
}
}
}
}
else
{
lean_object* v_a_4496_; lean_object* v___x_4498_; uint8_t v_isShared_4499_; uint8_t v_isSharedCheck_4503_; 
v_a_4496_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4503_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4503_ == 0)
{
v___x_4498_ = v___x_4481_;
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
else
{
lean_inc(v_a_4496_);
lean_dec(v___x_4481_);
v___x_4498_ = lean_box(0);
v_isShared_4499_ = v_isSharedCheck_4503_;
goto v_resetjp_4497_;
}
v_resetjp_4497_:
{
lean_object* v___x_4501_; 
if (v_isShared_4499_ == 0)
{
v___x_4501_ = v___x_4498_;
goto v_reusejp_4500_;
}
else
{
lean_object* v_reuseFailAlloc_4502_; 
v_reuseFailAlloc_4502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4502_, 0, v_a_4496_);
v___x_4501_ = v_reuseFailAlloc_4502_;
goto v_reusejp_4500_;
}
v_reusejp_4500_:
{
return v___x_4501_;
}
}
}
}
}
}
else
{
lean_object* v_a_4505_; lean_object* v___x_4507_; uint8_t v_isShared_4508_; uint8_t v_isSharedCheck_4512_; 
lean_dec(v_mvarId_4457_);
lean_dec_ref(v_config_4456_);
v_a_4505_ = lean_ctor_get(v___x_4467_, 0);
v_isSharedCheck_4512_ = !lean_is_exclusive(v___x_4467_);
if (v_isSharedCheck_4512_ == 0)
{
v___x_4507_ = v___x_4467_;
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
else
{
lean_inc(v_a_4505_);
lean_dec(v___x_4467_);
v___x_4507_ = lean_box(0);
v_isShared_4508_ = v_isSharedCheck_4512_;
goto v_resetjp_4506_;
}
v_resetjp_4506_:
{
lean_object* v___x_4510_; 
if (v_isShared_4508_ == 0)
{
v___x_4510_ = v___x_4507_;
goto v_reusejp_4509_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v_a_4505_);
v___x_4510_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4509_;
}
v_reusejp_4509_:
{
return v___x_4510_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4513_, lean_object* v_mvarId_4514_, lean_object* v_t_4515_, lean_object* v_init_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_){
_start:
{
lean_object* v_res_4522_; 
v_res_4522_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4513_, v_mvarId_4514_, v_t_4515_, v_init_4516_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v___y_4518_);
lean_dec_ref(v___y_4517_);
lean_dec_ref(v_t_4515_);
return v_res_4522_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4523_, lean_object* v___x_4524_, lean_object* v_config_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v___x_4531_; 
lean_inc(v_mvarId_4523_);
v___x_4531_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4523_, v___x_4524_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4531_) == 0)
{
lean_object* v___x_4532_; 
lean_dec_ref_known(v___x_4531_, 1);
lean_inc(v_mvarId_4523_);
v___x_4532_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4523_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4532_) == 0)
{
lean_object* v_a_4533_; lean_object* v___x_4535_; uint8_t v_isShared_4536_; uint8_t v_isSharedCheck_4566_; 
v_a_4533_ = lean_ctor_get(v___x_4532_, 0);
v_isSharedCheck_4566_ = !lean_is_exclusive(v___x_4532_);
if (v_isSharedCheck_4566_ == 0)
{
v___x_4535_ = v___x_4532_;
v_isShared_4536_ = v_isSharedCheck_4566_;
goto v_resetjp_4534_;
}
else
{
lean_inc(v_a_4533_);
lean_dec(v___x_4532_);
v___x_4535_ = lean_box(0);
v_isShared_4536_ = v_isSharedCheck_4566_;
goto v_resetjp_4534_;
}
v_resetjp_4534_:
{
uint8_t v___x_4537_; 
v___x_4537_ = lean_unbox(v_a_4533_);
if (v___x_4537_ == 0)
{
lean_object* v_lctx_4538_; lean_object* v_decls_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; 
lean_del_object(v___x_4535_);
v_lctx_4538_ = lean_ctor_get(v___y_4526_, 2);
v_decls_4539_ = lean_ctor_get(v_lctx_4538_, 1);
v___x_4540_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4541_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4525_, v_mvarId_4523_, v_decls_4539_, v___x_4540_, v___y_4526_, v___y_4527_, v___y_4528_, v___y_4529_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4554_; 
v_a_4542_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_4544_ = v___x_4541_;
v_isShared_4545_ = v_isSharedCheck_4554_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4541_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4554_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v_fst_4546_; 
v_fst_4546_ = lean_ctor_get(v_a_4542_, 0);
lean_inc(v_fst_4546_);
lean_dec(v_a_4542_);
if (lean_obj_tag(v_fst_4546_) == 0)
{
lean_object* v___x_4548_; 
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v_a_4533_);
v___x_4548_ = v___x_4544_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4533_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
else
{
lean_object* v_val_4550_; lean_object* v___x_4552_; 
lean_dec(v_a_4533_);
v_val_4550_ = lean_ctor_get(v_fst_4546_, 0);
lean_inc(v_val_4550_);
lean_dec_ref_known(v_fst_4546_, 1);
if (v_isShared_4545_ == 0)
{
lean_ctor_set(v___x_4544_, 0, v_val_4550_);
v___x_4552_ = v___x_4544_;
goto v_reusejp_4551_;
}
else
{
lean_object* v_reuseFailAlloc_4553_; 
v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4553_, 0, v_val_4550_);
v___x_4552_ = v_reuseFailAlloc_4553_;
goto v_reusejp_4551_;
}
v_reusejp_4551_:
{
return v___x_4552_;
}
}
}
}
else
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4562_; 
lean_dec(v_a_4533_);
v_a_4555_ = lean_ctor_get(v___x_4541_, 0);
v_isSharedCheck_4562_ = !lean_is_exclusive(v___x_4541_);
if (v_isSharedCheck_4562_ == 0)
{
v___x_4557_ = v___x_4541_;
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4541_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4562_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v___x_4560_; 
if (v_isShared_4558_ == 0)
{
v___x_4560_ = v___x_4557_;
goto v_reusejp_4559_;
}
else
{
lean_object* v_reuseFailAlloc_4561_; 
v_reuseFailAlloc_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4561_, 0, v_a_4555_);
v___x_4560_ = v_reuseFailAlloc_4561_;
goto v_reusejp_4559_;
}
v_reusejp_4559_:
{
return v___x_4560_;
}
}
}
}
else
{
lean_object* v___x_4564_; 
lean_dec_ref(v_config_4525_);
lean_dec(v_mvarId_4523_);
if (v_isShared_4536_ == 0)
{
v___x_4564_ = v___x_4535_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v_a_4533_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
}
}
else
{
lean_dec_ref(v_config_4525_);
lean_dec(v_mvarId_4523_);
return v___x_4532_;
}
}
else
{
lean_object* v_a_4567_; lean_object* v___x_4569_; uint8_t v_isShared_4570_; uint8_t v_isSharedCheck_4574_; 
lean_dec_ref(v_config_4525_);
lean_dec(v_mvarId_4523_);
v_a_4567_ = lean_ctor_get(v___x_4531_, 0);
v_isSharedCheck_4574_ = !lean_is_exclusive(v___x_4531_);
if (v_isSharedCheck_4574_ == 0)
{
v___x_4569_ = v___x_4531_;
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
else
{
lean_inc(v_a_4567_);
lean_dec(v___x_4531_);
v___x_4569_ = lean_box(0);
v_isShared_4570_ = v_isSharedCheck_4574_;
goto v_resetjp_4568_;
}
v_resetjp_4568_:
{
lean_object* v___x_4572_; 
if (v_isShared_4570_ == 0)
{
v___x_4572_ = v___x_4569_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4573_; 
v_reuseFailAlloc_4573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4573_, 0, v_a_4567_);
v___x_4572_ = v_reuseFailAlloc_4573_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
return v___x_4572_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4575_, lean_object* v___x_4576_, lean_object* v_config_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_, lean_object* v___y_4580_, lean_object* v___y_4581_, lean_object* v___y_4582_){
_start:
{
lean_object* v_res_4583_; 
v_res_4583_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4575_, v___x_4576_, v_config_4577_, v___y_4578_, v___y_4579_, v___y_4580_, v___y_4581_);
lean_dec(v___y_4581_);
lean_dec_ref(v___y_4580_);
lean_dec(v___y_4579_);
lean_dec_ref(v___y_4578_);
return v_res_4583_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4586_, lean_object* v_config_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_){
_start:
{
lean_object* v___x_4593_; lean_object* v___f_4594_; lean_object* v___x_4595_; 
v___x_4593_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4586_);
v___f_4594_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4594_, 0, v_mvarId_4586_);
lean_closure_set(v___f_4594_, 1, v___x_4593_);
lean_closure_set(v___f_4594_, 2, v_config_4587_);
v___x_4595_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4586_, v___f_4594_, v_a_4588_, v_a_4589_, v_a_4590_, v_a_4591_);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4596_, lean_object* v_config_4597_, lean_object* v_a_4598_, lean_object* v_a_4599_, lean_object* v_a_4600_, lean_object* v_a_4601_, lean_object* v_a_4602_){
_start:
{
lean_object* v_res_4603_; 
v_res_4603_ = l_Lean_MVarId_contradictionCore(v_mvarId_4596_, v_config_4597_, v_a_4598_, v_a_4599_, v_a_4600_, v_a_4601_);
lean_dec(v_a_4601_);
lean_dec_ref(v_a_4600_);
lean_dec(v_a_4599_);
lean_dec_ref(v_a_4598_);
return v_res_4603_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4604_, lean_object* v_config_4605_, lean_object* v_a_4606_, lean_object* v_a_4607_, lean_object* v_a_4608_, lean_object* v_a_4609_){
_start:
{
lean_object* v___x_4611_; 
lean_inc(v_mvarId_4604_);
v___x_4611_ = l_Lean_MVarId_contradictionCore(v_mvarId_4604_, v_config_4605_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
if (lean_obj_tag(v___x_4611_) == 0)
{
lean_object* v_a_4612_; lean_object* v___x_4614_; uint8_t v_isShared_4615_; uint8_t v_isSharedCheck_4624_; 
v_a_4612_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4624_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4624_ == 0)
{
v___x_4614_ = v___x_4611_;
v_isShared_4615_ = v_isSharedCheck_4624_;
goto v_resetjp_4613_;
}
else
{
lean_inc(v_a_4612_);
lean_dec(v___x_4611_);
v___x_4614_ = lean_box(0);
v_isShared_4615_ = v_isSharedCheck_4624_;
goto v_resetjp_4613_;
}
v_resetjp_4613_:
{
uint8_t v___x_4616_; 
v___x_4616_ = lean_unbox(v_a_4612_);
lean_dec(v_a_4612_);
if (v___x_4616_ == 0)
{
lean_object* v___x_4617_; lean_object* v___x_4618_; lean_object* v___x_4619_; 
lean_del_object(v___x_4614_);
v___x_4617_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4618_ = lean_box(0);
v___x_4619_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4617_, v_mvarId_4604_, v___x_4618_, v_a_4606_, v_a_4607_, v_a_4608_, v_a_4609_);
return v___x_4619_;
}
else
{
lean_object* v___x_4620_; lean_object* v___x_4622_; 
lean_dec(v_mvarId_4604_);
v___x_4620_ = lean_box(0);
if (v_isShared_4615_ == 0)
{
lean_ctor_set(v___x_4614_, 0, v___x_4620_);
v___x_4622_ = v___x_4614_;
goto v_reusejp_4621_;
}
else
{
lean_object* v_reuseFailAlloc_4623_; 
v_reuseFailAlloc_4623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4623_, 0, v___x_4620_);
v___x_4622_ = v_reuseFailAlloc_4623_;
goto v_reusejp_4621_;
}
v_reusejp_4621_:
{
return v___x_4622_;
}
}
}
}
else
{
lean_object* v_a_4625_; lean_object* v___x_4627_; uint8_t v_isShared_4628_; uint8_t v_isSharedCheck_4632_; 
lean_dec(v_mvarId_4604_);
v_a_4625_ = lean_ctor_get(v___x_4611_, 0);
v_isSharedCheck_4632_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4632_ == 0)
{
v___x_4627_ = v___x_4611_;
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
else
{
lean_inc(v_a_4625_);
lean_dec(v___x_4611_);
v___x_4627_ = lean_box(0);
v_isShared_4628_ = v_isSharedCheck_4632_;
goto v_resetjp_4626_;
}
v_resetjp_4626_:
{
lean_object* v___x_4630_; 
if (v_isShared_4628_ == 0)
{
v___x_4630_ = v___x_4627_;
goto v_reusejp_4629_;
}
else
{
lean_object* v_reuseFailAlloc_4631_; 
v_reuseFailAlloc_4631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4631_, 0, v_a_4625_);
v___x_4630_ = v_reuseFailAlloc_4631_;
goto v_reusejp_4629_;
}
v_reusejp_4629_:
{
return v___x_4630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4633_, lean_object* v_config_4634_, lean_object* v_a_4635_, lean_object* v_a_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_){
_start:
{
lean_object* v_res_4640_; 
v_res_4640_ = l_Lean_MVarId_contradiction(v_mvarId_4633_, v_config_4634_, v_a_4635_, v_a_4636_, v_a_4637_, v_a_4638_);
lean_dec(v_a_4638_);
lean_dec_ref(v_a_4637_);
lean_dec(v_a_4636_);
lean_dec_ref(v_a_4635_);
return v_res_4640_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4703_; uint8_t v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; 
v___x_4703_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4704_ = 0;
v___x_4705_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4706_ = l_Lean_registerTraceClass(v___x_4703_, v___x_4704_, v___x_4705_);
return v___x_4706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4707_){
_start:
{
lean_object* v_res_4708_; 
v_res_4708_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4708_;
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
