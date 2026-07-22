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
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_type(lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Exception_toMessageData(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
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
static const lean_closure_object l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
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
v___x_51_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
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
lean_object* v_ks_103_; lean_object* v_vs_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_124_; 
v_ks_103_ = lean_ctor_get(v_x_52_, 0);
v_vs_104_ = lean_ctor_get(v_x_52_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v_x_52_);
if (v_isSharedCheck_124_ == 0)
{
v___x_106_ = v_x_52_;
v_isShared_107_ = v_isSharedCheck_124_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_vs_104_);
lean_inc(v_ks_103_);
lean_dec(v_x_52_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_124_;
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
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v_ks_103_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v_vs_104_);
v___x_109_ = v_reuseFailAlloc_123_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
lean_object* v_newNode_110_; uint8_t v___y_112_; size_t v___x_118_; uint8_t v___x_119_; 
v_newNode_110_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v___x_109_, v_x_55_, v_x_56_);
v___x_118_ = ((size_t)7ULL);
v___x_119_ = lean_usize_dec_le(v___x_118_, v_x_54_);
if (v___x_119_ == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_110_);
v___x_121_ = lean_unsigned_to_nat(4u);
v___x_122_ = lean_nat_dec_lt(v___x_120_, v___x_121_);
lean_dec(v___x_120_);
v___y_112_ = v___x_122_;
goto v___jp_111_;
}
else
{
v___y_112_ = v___x_119_;
goto v___jp_111_;
}
v___jp_111_:
{
if (v___y_112_ == 0)
{
lean_object* v_ks_113_; lean_object* v_vs_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v_ks_113_ = lean_ctor_get(v_newNode_110_, 0);
lean_inc_ref(v_ks_113_);
v_vs_114_ = lean_ctor_get(v_newNode_110_, 1);
lean_inc_ref(v_vs_114_);
lean_dec_ref(v_newNode_110_);
v___x_115_ = lean_unsigned_to_nat(0u);
v___x_116_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_117_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_x_54_, v_ks_113_, v_vs_114_, v___x_115_, v___x_116_);
lean_dec_ref(v_vs_114_);
lean_dec_ref(v_ks_113_);
return v___x_117_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_125_, lean_object* v_keys_126_, lean_object* v_vals_127_, lean_object* v_i_128_, lean_object* v_entries_129_){
_start:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_array_get_size(v_keys_126_);
v___x_131_ = lean_nat_dec_lt(v_i_128_, v___x_130_);
if (v___x_131_ == 0)
{
lean_dec(v_i_128_);
return v_entries_129_;
}
else
{
lean_object* v_k_132_; lean_object* v_v_133_; uint64_t v___x_134_; size_t v_h_135_; size_t v___x_136_; lean_object* v___x_137_; size_t v___x_138_; size_t v___x_139_; size_t v___x_140_; size_t v_h_141_; lean_object* v___x_142_; lean_object* v___x_143_; 
v_k_132_ = lean_array_fget_borrowed(v_keys_126_, v_i_128_);
v_v_133_ = lean_array_fget_borrowed(v_vals_127_, v_i_128_);
v___x_134_ = l_Lean_instHashableMVarId_hash(v_k_132_);
v_h_135_ = lean_uint64_to_usize(v___x_134_);
v___x_136_ = ((size_t)5ULL);
v___x_137_ = lean_unsigned_to_nat(1u);
v___x_138_ = ((size_t)1ULL);
v___x_139_ = lean_usize_sub(v_depth_125_, v___x_138_);
v___x_140_ = lean_usize_mul(v___x_136_, v___x_139_);
v_h_141_ = lean_usize_shift_right(v_h_135_, v___x_140_);
v___x_142_ = lean_nat_add(v_i_128_, v___x_137_);
lean_dec(v_i_128_);
lean_inc(v_v_133_);
lean_inc(v_k_132_);
v___x_143_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_entries_129_, v_h_141_, v_depth_125_, v_k_132_, v_v_133_);
v_i_128_ = v___x_142_;
v_entries_129_ = v___x_143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_145_, lean_object* v_keys_146_, lean_object* v_vals_147_, lean_object* v_i_148_, lean_object* v_entries_149_){
_start:
{
size_t v_depth_boxed_150_; lean_object* v_res_151_; 
v_depth_boxed_150_ = lean_unbox_usize(v_depth_145_);
lean_dec(v_depth_145_);
v_res_151_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_150_, v_keys_146_, v_vals_147_, v_i_148_, v_entries_149_);
lean_dec_ref(v_vals_147_);
lean_dec_ref(v_keys_146_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_152_, lean_object* v_x_153_, lean_object* v_x_154_, lean_object* v_x_155_, lean_object* v_x_156_){
_start:
{
size_t v_x_1108__boxed_157_; size_t v_x_1109__boxed_158_; lean_object* v_res_159_; 
v_x_1108__boxed_157_ = lean_unbox_usize(v_x_153_);
lean_dec(v_x_153_);
v_x_1109__boxed_158_ = lean_unbox_usize(v_x_154_);
lean_dec(v_x_154_);
v_res_159_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_152_, v_x_1108__boxed_157_, v_x_1109__boxed_158_, v_x_155_, v_x_156_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(lean_object* v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
uint64_t v___x_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v___x_166_; 
v___x_163_ = l_Lean_instHashableMVarId_hash(v_x_161_);
v___x_164_ = lean_uint64_to_usize(v___x_163_);
v___x_165_ = ((size_t)1ULL);
v___x_166_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_160_, v___x_164_, v___x_165_, v_x_161_, v_x_162_);
return v___x_166_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(lean_object* v_mvarId_167_, lean_object* v_val_168_, lean_object* v___y_169_){
_start:
{
lean_object* v___x_171_; lean_object* v_mctx_172_; lean_object* v_cache_173_; lean_object* v_zetaDeltaFVarIds_174_; lean_object* v_postponed_175_; lean_object* v_diag_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_204_; 
v___x_171_ = lean_st_ref_take(v___y_169_);
v_mctx_172_ = lean_ctor_get(v___x_171_, 0);
v_cache_173_ = lean_ctor_get(v___x_171_, 1);
v_zetaDeltaFVarIds_174_ = lean_ctor_get(v___x_171_, 2);
v_postponed_175_ = lean_ctor_get(v___x_171_, 3);
v_diag_176_ = lean_ctor_get(v___x_171_, 4);
v_isSharedCheck_204_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_204_ == 0)
{
v___x_178_ = v___x_171_;
v_isShared_179_ = v_isSharedCheck_204_;
goto v_resetjp_177_;
}
else
{
lean_inc(v_diag_176_);
lean_inc(v_postponed_175_);
lean_inc(v_zetaDeltaFVarIds_174_);
lean_inc(v_cache_173_);
lean_inc(v_mctx_172_);
lean_dec(v___x_171_);
v___x_178_ = lean_box(0);
v_isShared_179_ = v_isSharedCheck_204_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_depth_180_; lean_object* v_levelAssignDepth_181_; lean_object* v_lmvarCounter_182_; lean_object* v_mvarCounter_183_; lean_object* v_lDecls_184_; lean_object* v_decls_185_; lean_object* v_userNames_186_; lean_object* v_lAssignment_187_; lean_object* v_eAssignment_188_; lean_object* v_dAssignment_189_; lean_object* v___x_191_; uint8_t v_isShared_192_; uint8_t v_isSharedCheck_203_; 
v_depth_180_ = lean_ctor_get(v_mctx_172_, 0);
v_levelAssignDepth_181_ = lean_ctor_get(v_mctx_172_, 1);
v_lmvarCounter_182_ = lean_ctor_get(v_mctx_172_, 2);
v_mvarCounter_183_ = lean_ctor_get(v_mctx_172_, 3);
v_lDecls_184_ = lean_ctor_get(v_mctx_172_, 4);
v_decls_185_ = lean_ctor_get(v_mctx_172_, 5);
v_userNames_186_ = lean_ctor_get(v_mctx_172_, 6);
v_lAssignment_187_ = lean_ctor_get(v_mctx_172_, 7);
v_eAssignment_188_ = lean_ctor_get(v_mctx_172_, 8);
v_dAssignment_189_ = lean_ctor_get(v_mctx_172_, 9);
v_isSharedCheck_203_ = !lean_is_exclusive(v_mctx_172_);
if (v_isSharedCheck_203_ == 0)
{
v___x_191_ = v_mctx_172_;
v_isShared_192_ = v_isSharedCheck_203_;
goto v_resetjp_190_;
}
else
{
lean_inc(v_dAssignment_189_);
lean_inc(v_eAssignment_188_);
lean_inc(v_lAssignment_187_);
lean_inc(v_userNames_186_);
lean_inc(v_decls_185_);
lean_inc(v_lDecls_184_);
lean_inc(v_mvarCounter_183_);
lean_inc(v_lmvarCounter_182_);
lean_inc(v_levelAssignDepth_181_);
lean_inc(v_depth_180_);
lean_dec(v_mctx_172_);
v___x_191_ = lean_box(0);
v_isShared_192_ = v_isSharedCheck_203_;
goto v_resetjp_190_;
}
v_resetjp_190_:
{
lean_object* v___x_193_; lean_object* v___x_195_; 
v___x_193_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_188_, v_mvarId_167_, v_val_168_);
if (v_isShared_192_ == 0)
{
lean_ctor_set(v___x_191_, 8, v___x_193_);
v___x_195_ = v___x_191_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_depth_180_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_levelAssignDepth_181_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_lmvarCounter_182_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v_mvarCounter_183_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v_lDecls_184_);
lean_ctor_set(v_reuseFailAlloc_202_, 5, v_decls_185_);
lean_ctor_set(v_reuseFailAlloc_202_, 6, v_userNames_186_);
lean_ctor_set(v_reuseFailAlloc_202_, 7, v_lAssignment_187_);
lean_ctor_set(v_reuseFailAlloc_202_, 8, v___x_193_);
lean_ctor_set(v_reuseFailAlloc_202_, 9, v_dAssignment_189_);
v___x_195_ = v_reuseFailAlloc_202_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
lean_object* v___x_197_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_195_);
v___x_197_ = v___x_178_;
goto v_reusejp_196_;
}
else
{
lean_object* v_reuseFailAlloc_201_; 
v_reuseFailAlloc_201_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_201_, 0, v___x_195_);
lean_ctor_set(v_reuseFailAlloc_201_, 1, v_cache_173_);
lean_ctor_set(v_reuseFailAlloc_201_, 2, v_zetaDeltaFVarIds_174_);
lean_ctor_set(v_reuseFailAlloc_201_, 3, v_postponed_175_);
lean_ctor_set(v_reuseFailAlloc_201_, 4, v_diag_176_);
v___x_197_ = v_reuseFailAlloc_201_;
goto v_reusejp_196_;
}
v_reusejp_196_:
{
lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___x_198_ = lean_st_ref_set(v___y_169_, v___x_197_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_200_, 0, v___x_199_);
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
lean_object* v___x_217_; 
lean_inc(v_mvarId_211_);
v___x_217_ = l_Lean_MVarId_getType(v_mvarId_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_262_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_262_ == 0)
{
v___x_220_ = v___x_217_;
v_isShared_221_ = v_isSharedCheck_262_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_217_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_262_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___f_222_; lean_object* v___x_223_; 
v___f_222_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
v___x_223_ = lean_find_expr(v___f_222_, v_a_218_);
lean_dec(v_a_218_);
if (lean_obj_tag(v___x_223_) == 1)
{
lean_object* v_val_224_; lean_object* v___x_225_; 
lean_del_object(v___x_220_);
v_val_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_val_224_);
lean_dec_ref_known(v___x_223_, 1);
lean_inc(v_mvarId_211_);
v___x_225_ = l_Lean_MVarId_getType(v_mvarId_211_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
if (lean_obj_tag(v___x_225_) == 0)
{
lean_object* v_a_226_; lean_object* v___x_227_; lean_object* v___x_228_; 
v_a_226_ = lean_ctor_get(v___x_225_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v___x_225_, 1);
v___x_227_ = l_Lean_Expr_appArg_x21(v_val_224_);
lean_dec(v_val_224_);
v___x_228_ = l_Lean_Meta_mkFalseElim(v_a_226_, v___x_227_, v_a_212_, v_a_213_, v_a_214_, v_a_215_);
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
lean_dec(v_val_224_);
lean_dec(v_mvarId_211_);
v_a_249_ = lean_ctor_get(v___x_225_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_225_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_225_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_225_);
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
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_258_);
v___x_260_ = v___x_220_;
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
v_a_263_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_270_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_270_ == 0)
{
v___x_265_ = v___x_217_;
v_isShared_266_ = v_isSharedCheck_270_;
goto v_resetjp_264_;
}
else
{
lean_inc(v_a_263_);
lean_dec(v___x_217_);
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
size_t v_x_1463__boxed_312_; size_t v_x_1464__boxed_313_; lean_object* v_res_314_; 
v_x_1463__boxed_312_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_x_1464__boxed_313_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_res_314_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_306_, v_x_307_, v_x_1463__boxed_312_, v_x_1464__boxed_313_, v_x_310_, v_x_311_);
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
lean_dec_ref(v_s_414_);
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
lean_object* v_a_501_; lean_object* v___y_503_; lean_object* v___y_504_; uint8_t v___y_505_; lean_object* v___y_524_; lean_object* v_a_525_; lean_object* v___x_528_; 
v_a_501_ = lean_ctor_get(v___x_500_, 0);
lean_inc(v_a_501_);
lean_dec_ref_known(v___x_500_, 1);
lean_inc(v___y_498_);
lean_inc_ref(v___y_497_);
lean_inc(v___y_496_);
lean_inc_ref(v___y_495_);
lean_inc(v___y_494_);
v___x_528_ = lean_apply_6(v_x_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, lean_box(0));
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v_a_529_; uint8_t v___x_530_; 
v_a_529_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_529_);
v___x_530_ = lean_unbox(v_a_529_);
if (v___x_530_ == 0)
{
lean_object* v___x_531_; 
lean_dec_ref_known(v___x_528_, 1);
v___x_531_ = l_Lean_Meta_SavedState_restore___redArg(v_a_501_, v___y_496_, v___y_498_);
if (lean_obj_tag(v___x_531_) == 0)
{
lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_538_; 
lean_dec(v_a_501_);
v_isSharedCheck_538_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_538_ == 0)
{
lean_object* v_unused_539_; 
v_unused_539_ = lean_ctor_get(v___x_531_, 0);
lean_dec(v_unused_539_);
v___x_533_ = v___x_531_;
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
else
{
lean_dec(v___x_531_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_538_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_536_; 
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v_a_529_);
v___x_536_ = v___x_533_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_537_; 
v_reuseFailAlloc_537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_537_, 0, v_a_529_);
v___x_536_ = v_reuseFailAlloc_537_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
return v___x_536_;
}
}
}
else
{
lean_object* v_a_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_547_; 
lean_dec(v_a_529_);
v_a_540_ = lean_ctor_get(v___x_531_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v___x_531_);
if (v_isSharedCheck_547_ == 0)
{
v___x_542_ = v___x_531_;
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_a_540_);
lean_dec(v___x_531_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_547_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
lean_object* v___x_545_; 
lean_inc(v_a_540_);
if (v_isShared_543_ == 0)
{
v___x_545_ = v___x_542_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_a_540_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
v___y_524_ = v___x_545_;
v_a_525_ = v_a_540_;
goto v___jp_523_;
}
}
}
}
else
{
lean_dec(v_a_529_);
lean_dec(v_a_501_);
return v___x_528_;
}
}
else
{
lean_object* v_a_548_; 
v_a_548_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_a_548_);
v___y_524_ = v___x_528_;
v_a_525_ = v_a_548_;
goto v___jp_523_;
}
v___jp_502_:
{
if (v___y_505_ == 0)
{
lean_object* v___x_506_; 
lean_dec_ref(v___y_503_);
v___x_506_ = l_Lean_Meta_SavedState_restore___redArg(v_a_501_, v___y_496_, v___y_498_);
lean_dec(v_a_501_);
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
lean_ctor_set(v___x_508_, 0, v___y_504_);
v___x_511_ = v___x_508_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___y_504_);
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
lean_dec_ref(v___y_504_);
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
lean_dec_ref(v___y_504_);
lean_dec(v_a_501_);
return v___y_503_;
}
}
v___jp_523_:
{
uint8_t v___x_526_; 
v___x_526_ = l_Lean_Exception_isInterrupt(v_a_525_);
if (v___x_526_ == 0)
{
uint8_t v___x_527_; 
lean_inc_ref(v_a_525_);
v___x_527_ = l_Lean_Exception_isRuntime(v_a_525_);
v___y_503_ = v___y_524_;
v___y_504_ = v_a_525_;
v___y_505_ = v___x_527_;
goto v___jp_502_;
}
else
{
v___y_503_ = v___y_524_;
v___y_504_ = v_a_525_;
v___y_505_ = v___x_526_;
goto v___jp_502_;
}
}
}
else
{
lean_object* v_a_549_; lean_object* v___x_551_; uint8_t v_isShared_552_; uint8_t v_isSharedCheck_556_; 
lean_dec_ref(v_x_493_);
v_a_549_ = lean_ctor_get(v___x_500_, 0);
v_isSharedCheck_556_ = !lean_is_exclusive(v___x_500_);
if (v_isSharedCheck_556_ == 0)
{
v___x_551_ = v___x_500_;
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
else
{
lean_inc(v_a_549_);
lean_dec(v___x_500_);
v___x_551_ = lean_box(0);
v_isShared_552_ = v_isSharedCheck_556_;
goto v_resetjp_550_;
}
v_resetjp_550_:
{
lean_object* v___x_554_; 
if (v_isShared_552_ == 0)
{
v___x_554_ = v___x_551_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_555_; 
v_reuseFailAlloc_555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_555_, 0, v_a_549_);
v___x_554_ = v_reuseFailAlloc_555_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
return v___x_554_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* v_x_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_){
_start:
{
lean_object* v_res_564_; 
v_res_564_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_x_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_);
lean_dec(v___y_562_);
lean_dec_ref(v___y_561_);
lean_dec(v___y_560_);
lean_dec_ref(v___y_559_);
lean_dec(v___y_558_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(lean_object* v_msgData_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_){
_start:
{
lean_object* v___x_571_; lean_object* v_env_572_; lean_object* v___x_573_; lean_object* v_mctx_574_; lean_object* v_lctx_575_; lean_object* v_options_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_571_ = lean_st_ref_get(v___y_569_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_env_572_);
lean_dec(v___x_571_);
v___x_573_ = lean_st_ref_get(v___y_567_);
v_mctx_574_ = lean_ctor_get(v___x_573_, 0);
lean_inc_ref(v_mctx_574_);
lean_dec(v___x_573_);
v_lctx_575_ = lean_ctor_get(v___y_566_, 2);
v_options_576_ = lean_ctor_get(v___y_568_, 2);
lean_inc_ref(v_options_576_);
lean_inc_ref(v_lctx_575_);
v___x_577_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_577_, 0, v_env_572_);
lean_ctor_set(v___x_577_, 1, v_mctx_574_);
lean_ctor_set(v___x_577_, 2, v_lctx_575_);
lean_ctor_set(v___x_577_, 3, v_options_576_);
v___x_578_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_578_, 0, v___x_577_);
lean_ctor_set(v___x_578_, 1, v_msgData_565_);
v___x_579_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object* v_msgData_580_, lean_object* v___y_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_580_, v___y_581_, v___y_582_, v___y_583_, v___y_584_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
lean_dec(v___y_582_);
lean_dec_ref(v___y_581_);
return v_res_586_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_587_; double v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = lean_float_of_nat(v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_592_, lean_object* v_msg_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_){
_start:
{
lean_object* v_ref_599_; lean_object* v___x_600_; lean_object* v_a_601_; lean_object* v___x_603_; uint8_t v_isShared_604_; uint8_t v_isSharedCheck_645_; 
v_ref_599_ = lean_ctor_get(v___y_596_, 5);
v___x_600_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_593_, v___y_594_, v___y_595_, v___y_596_, v___y_597_);
v_a_601_ = lean_ctor_get(v___x_600_, 0);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_600_);
if (v_isSharedCheck_645_ == 0)
{
v___x_603_ = v___x_600_;
v_isShared_604_ = v_isSharedCheck_645_;
goto v_resetjp_602_;
}
else
{
lean_inc(v_a_601_);
lean_dec(v___x_600_);
v___x_603_ = lean_box(0);
v_isShared_604_ = v_isSharedCheck_645_;
goto v_resetjp_602_;
}
v_resetjp_602_:
{
lean_object* v___x_605_; lean_object* v_traceState_606_; lean_object* v_env_607_; lean_object* v_nextMacroScope_608_; lean_object* v_ngen_609_; lean_object* v_auxDeclNGen_610_; lean_object* v_cache_611_; lean_object* v_messages_612_; lean_object* v_infoState_613_; lean_object* v_snapshotTasks_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_644_; 
v___x_605_ = lean_st_ref_take(v___y_597_);
v_traceState_606_ = lean_ctor_get(v___x_605_, 4);
v_env_607_ = lean_ctor_get(v___x_605_, 0);
v_nextMacroScope_608_ = lean_ctor_get(v___x_605_, 1);
v_ngen_609_ = lean_ctor_get(v___x_605_, 2);
v_auxDeclNGen_610_ = lean_ctor_get(v___x_605_, 3);
v_cache_611_ = lean_ctor_get(v___x_605_, 5);
v_messages_612_ = lean_ctor_get(v___x_605_, 6);
v_infoState_613_ = lean_ctor_get(v___x_605_, 7);
v_snapshotTasks_614_ = lean_ctor_get(v___x_605_, 8);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_605_);
if (v_isSharedCheck_644_ == 0)
{
v___x_616_ = v___x_605_;
v_isShared_617_ = v_isSharedCheck_644_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_snapshotTasks_614_);
lean_inc(v_infoState_613_);
lean_inc(v_messages_612_);
lean_inc(v_cache_611_);
lean_inc(v_traceState_606_);
lean_inc(v_auxDeclNGen_610_);
lean_inc(v_ngen_609_);
lean_inc(v_nextMacroScope_608_);
lean_inc(v_env_607_);
lean_dec(v___x_605_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_644_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
uint64_t v_tid_618_; lean_object* v_traces_619_; lean_object* v___x_621_; uint8_t v_isShared_622_; uint8_t v_isSharedCheck_643_; 
v_tid_618_ = lean_ctor_get_uint64(v_traceState_606_, sizeof(void*)*1);
v_traces_619_ = lean_ctor_get(v_traceState_606_, 0);
v_isSharedCheck_643_ = !lean_is_exclusive(v_traceState_606_);
if (v_isSharedCheck_643_ == 0)
{
v___x_621_ = v_traceState_606_;
v_isShared_622_ = v_isSharedCheck_643_;
goto v_resetjp_620_;
}
else
{
lean_inc(v_traces_619_);
lean_dec(v_traceState_606_);
v___x_621_ = lean_box(0);
v_isShared_622_ = v_isSharedCheck_643_;
goto v_resetjp_620_;
}
v_resetjp_620_:
{
lean_object* v___x_623_; double v___x_624_; uint8_t v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_633_; 
v___x_623_ = lean_box(0);
v___x_624_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_625_ = 0;
v___x_626_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_627_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_627_, 0, v_cls_592_);
lean_ctor_set(v___x_627_, 1, v___x_623_);
lean_ctor_set(v___x_627_, 2, v___x_626_);
lean_ctor_set_float(v___x_627_, sizeof(void*)*3, v___x_624_);
lean_ctor_set_float(v___x_627_, sizeof(void*)*3 + 8, v___x_624_);
lean_ctor_set_uint8(v___x_627_, sizeof(void*)*3 + 16, v___x_625_);
v___x_628_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_629_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_629_, 0, v___x_627_);
lean_ctor_set(v___x_629_, 1, v_a_601_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
lean_inc(v_ref_599_);
v___x_630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_630_, 0, v_ref_599_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
v___x_631_ = l_Lean_PersistentArray_push___redArg(v_traces_619_, v___x_630_);
if (v_isShared_622_ == 0)
{
lean_ctor_set(v___x_621_, 0, v___x_631_);
v___x_633_ = v___x_621_;
goto v_reusejp_632_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v___x_631_);
lean_ctor_set_uint64(v_reuseFailAlloc_642_, sizeof(void*)*1, v_tid_618_);
v___x_633_ = v_reuseFailAlloc_642_;
goto v_reusejp_632_;
}
v_reusejp_632_:
{
lean_object* v___x_635_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 4, v___x_633_);
v___x_635_ = v___x_616_;
goto v_reusejp_634_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v_env_607_);
lean_ctor_set(v_reuseFailAlloc_641_, 1, v_nextMacroScope_608_);
lean_ctor_set(v_reuseFailAlloc_641_, 2, v_ngen_609_);
lean_ctor_set(v_reuseFailAlloc_641_, 3, v_auxDeclNGen_610_);
lean_ctor_set(v_reuseFailAlloc_641_, 4, v___x_633_);
lean_ctor_set(v_reuseFailAlloc_641_, 5, v_cache_611_);
lean_ctor_set(v_reuseFailAlloc_641_, 6, v_messages_612_);
lean_ctor_set(v_reuseFailAlloc_641_, 7, v_infoState_613_);
lean_ctor_set(v_reuseFailAlloc_641_, 8, v_snapshotTasks_614_);
v___x_635_ = v_reuseFailAlloc_641_;
goto v_reusejp_634_;
}
v_reusejp_634_:
{
lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_636_ = lean_st_ref_set(v___y_597_, v___x_635_);
v___x_637_ = lean_box(0);
if (v_isShared_604_ == 0)
{
lean_ctor_set(v___x_603_, 0, v___x_637_);
v___x_639_ = v___x_603_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
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
size_t v_sz_boxed_674_; size_t v___x_18284__boxed_675_; uint8_t v___x_18286__boxed_676_; lean_object* v_res_677_; 
v_sz_boxed_674_ = lean_unbox_usize(v_sz_664_);
lean_dec(v_sz_664_);
v___x_18284__boxed_675_ = lean_unbox_usize(v___x_665_);
lean_dec(v___x_665_);
v___x_18286__boxed_676_ = lean_unbox(v___x_667_);
v_res_677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_661_, v_mvarId_662_, v_fields_663_, v_sz_boxed_674_, v___x_18284__boxed_675_, v___x_666_, v___x_18286__boxed_676_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_);
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
lean_object* v_a_765_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v_options_798_; uint8_t v_hasTrace_799_; 
v_a_765_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_a_765_);
lean_dec_ref_known(v___x_764_, 1);
v_options_798_ = lean_ctor_get(v___y_761_, 2);
v_hasTrace_799_ = lean_ctor_get_uint8(v_options_798_, sizeof(void*)*1);
if (v_hasTrace_799_ == 0)
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
lean_object* v_inheritedTraceOptions_800_; lean_object* v___x_801_; lean_object* v___x_802_; uint8_t v___x_803_; 
v_inheritedTraceOptions_800_ = lean_ctor_get(v___y_761_, 13);
v___x_801_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_802_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_803_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_800_, v_options_798_, v___x_802_);
if (v___x_803_ == 0)
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
lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_804_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_805_ = lean_array_get_size(v_a_765_);
v___x_806_ = l_Nat_reprFast(v___x_805_);
v___x_807_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
v___x_808_ = l_Lean_MessageData_ofFormat(v___x_807_);
v___x_809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_804_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_801_, v___x_809_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_810_) == 0)
{
lean_dec_ref_known(v___x_810_, 1);
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
goto v___jp_766_;
}
else
{
lean_object* v_a_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_818_; 
lean_dec(v_a_765_);
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
lean_object* v_a_819_; lean_object* v___x_821_; uint8_t v_isShared_822_; uint8_t v_isSharedCheck_863_; 
v_a_819_ = lean_ctor_get(v___x_764_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_764_);
if (v_isSharedCheck_863_ == 0)
{
v___x_821_ = v___x_764_;
v_isShared_822_ = v_isSharedCheck_863_;
goto v_resetjp_820_;
}
else
{
lean_inc(v_a_819_);
lean_dec(v___x_764_);
v___x_821_ = lean_box(0);
v_isShared_822_ = v_isSharedCheck_863_;
goto v_resetjp_820_;
}
v_resetjp_820_:
{
uint8_t v___y_824_; uint8_t v___x_861_; 
v___x_861_ = l_Lean_Exception_isInterrupt(v_a_819_);
if (v___x_861_ == 0)
{
uint8_t v___x_862_; 
lean_inc(v_a_819_);
v___x_862_ = l_Lean_Exception_isRuntime(v_a_819_);
v___y_824_ = v___x_862_;
goto v___jp_823_;
}
else
{
v___y_824_ = v___x_861_;
goto v___jp_823_;
}
v___jp_823_:
{
if (v___y_824_ == 0)
{
lean_object* v_options_825_; uint8_t v_hasTrace_826_; 
v_options_825_ = lean_ctor_get(v___y_761_, 2);
v_hasTrace_826_ = lean_ctor_get_uint8(v_options_825_, sizeof(void*)*1);
if (v_hasTrace_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_829_; 
lean_dec(v_a_819_);
v___x_827_ = lean_box(v___x_754_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
lean_ctor_set(v___x_821_, 0, v___x_827_);
v___x_829_ = v___x_821_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_830_; 
v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_827_);
v___x_829_ = v_reuseFailAlloc_830_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
return v___x_829_;
}
}
else
{
lean_object* v_inheritedTraceOptions_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v_inheritedTraceOptions_831_ = lean_ctor_get(v___y_761_, 13);
v___x_832_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_833_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_834_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_831_, v_options_825_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_837_; 
lean_dec(v_a_819_);
v___x_835_ = lean_box(v___x_754_);
if (v_isShared_822_ == 0)
{
lean_ctor_set_tag(v___x_821_, 0);
lean_ctor_set(v___x_821_, 0, v___x_835_);
v___x_837_ = v___x_821_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v___x_835_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
else
{
lean_object* v___x_839_; lean_object* v___x_840_; 
lean_del_object(v___x_821_);
v___x_839_ = l_Lean_Exception_toMessageData(v_a_819_);
v___x_840_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_832_, v___x_839_, v___y_759_, v___y_760_, v___y_761_, v___y_762_);
if (lean_obj_tag(v___x_840_) == 0)
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
v_isSharedCheck_848_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v___x_840_, 0);
lean_dec(v_unused_849_);
v___x_842_ = v___x_840_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_dec(v___x_840_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = lean_box(v___x_754_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
else
{
lean_object* v_a_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_857_; 
v_a_850_ = lean_ctor_get(v___x_840_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_840_);
if (v_isSharedCheck_857_ == 0)
{
v___x_852_ = v___x_840_;
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_a_850_);
lean_dec(v___x_840_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_857_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_855_; 
if (v_isShared_853_ == 0)
{
v___x_855_ = v___x_852_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
v___x_855_ = v_reuseFailAlloc_856_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
return v___x_855_;
}
}
}
}
}
}
else
{
lean_object* v___x_859_; 
if (v_isShared_822_ == 0)
{
v___x_859_ = v___x_821_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_a_819_);
v___x_859_ = v_reuseFailAlloc_860_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
return v___x_859_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_864_, lean_object* v_fvarId_865_, lean_object* v___x_866_, lean_object* v___x_867_, lean_object* v___x_868_, lean_object* v_val_869_, lean_object* v___x_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_){
_start:
{
uint8_t v___x_18406__boxed_877_; uint8_t v___x_18409__boxed_878_; lean_object* v_res_879_; 
v___x_18406__boxed_877_ = lean_unbox(v___x_867_);
v___x_18409__boxed_878_ = lean_unbox(v___x_870_);
v_res_879_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_864_, v_fvarId_865_, v___x_866_, v___x_18406__boxed_877_, v___x_868_, v_val_869_, v___x_18409__boxed_878_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_);
lean_dec(v___y_875_);
lean_dec_ref(v___y_874_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec(v_val_869_);
return v_res_879_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_882_ = l_Lean_stringToMessageData(v___x_881_);
return v___x_882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_883_, lean_object* v_fvarId_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; uint8_t v___x_897_; 
v___x_895_ = lean_st_ref_get(v_a_885_);
v___x_896_ = lean_unsigned_to_nat(0u);
v___x_897_ = lean_nat_dec_eq(v___x_895_, v___x_896_);
if (v___x_897_ == 0)
{
lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___f_907_; lean_object* v___x_908_; 
v___x_898_ = lean_st_ref_take(v_a_885_);
v___x_899_ = lean_unsigned_to_nat(1u);
v___x_900_ = lean_nat_sub(v___x_898_, v___x_899_);
lean_dec(v___x_898_);
v___x_901_ = lean_st_ref_set(v_a_885_, v___x_900_);
v___x_902_ = 1;
v___x_903_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_904_ = lean_box(0);
v___x_905_ = lean_box(v___x_897_);
v___x_906_ = lean_box(v___x_902_);
v___f_907_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_907_, 0, v_mvarId_883_);
lean_closure_set(v___f_907_, 1, v_fvarId_884_);
lean_closure_set(v___f_907_, 2, v___x_903_);
lean_closure_set(v___f_907_, 3, v___x_905_);
lean_closure_set(v___f_907_, 4, v___x_904_);
lean_closure_set(v___f_907_, 5, v___x_895_);
lean_closure_set(v___f_907_, 6, v___x_906_);
v___x_908_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_907_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
return v___x_908_;
}
else
{
lean_object* v_options_909_; uint8_t v_hasTrace_910_; 
lean_dec(v___x_895_);
lean_dec(v_fvarId_884_);
lean_dec(v_mvarId_883_);
v_options_909_ = lean_ctor_get(v_a_888_, 2);
v_hasTrace_910_ = lean_ctor_get_uint8(v_options_909_, sizeof(void*)*1);
if (v_hasTrace_910_ == 0)
{
goto v___jp_891_;
}
else
{
lean_object* v_inheritedTraceOptions_911_; lean_object* v___x_912_; lean_object* v___x_913_; uint8_t v___x_914_; 
v_inheritedTraceOptions_911_ = lean_ctor_get(v_a_888_, 13);
v___x_912_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_913_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_914_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_911_, v_options_909_, v___x_913_);
if (v___x_914_ == 0)
{
goto v___jp_891_;
}
else
{
lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_915_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_916_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_912_, v___x_915_, v_a_886_, v_a_887_, v_a_888_, v_a_889_);
if (lean_obj_tag(v___x_916_) == 0)
{
lean_dec_ref_known(v___x_916_, 1);
goto v___jp_891_;
}
else
{
lean_object* v_a_917_; lean_object* v___x_919_; uint8_t v_isShared_920_; uint8_t v_isSharedCheck_924_; 
v_a_917_ = lean_ctor_get(v___x_916_, 0);
v_isSharedCheck_924_ = !lean_is_exclusive(v___x_916_);
if (v_isSharedCheck_924_ == 0)
{
v___x_919_ = v___x_916_;
v_isShared_920_ = v_isSharedCheck_924_;
goto v_resetjp_918_;
}
else
{
lean_inc(v_a_917_);
lean_dec(v___x_916_);
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
}
v___jp_891_:
{
uint8_t v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; 
v___x_892_ = 0;
v___x_893_ = lean_box(v___x_892_);
v___x_894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_894_, 0, v___x_893_);
return v___x_894_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_925_, lean_object* v___x_926_, lean_object* v_as_927_, size_t v_sz_928_, size_t v_i_929_, lean_object* v_b_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_){
_start:
{
lean_object* v_a_938_; uint8_t v___x_942_; 
v___x_942_ = lean_usize_dec_lt(v_i_929_, v_sz_928_);
if (v___x_942_ == 0)
{
lean_object* v___x_943_; 
lean_dec(v___x_926_);
lean_dec_ref(v___x_925_);
v___x_943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_943_, 0, v_b_930_);
return v___x_943_;
}
else
{
lean_object* v_subst_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v_a_947_; lean_object* v___x_948_; uint8_t v___x_949_; 
lean_dec_ref(v_b_930_);
v_subst_944_ = lean_ctor_get(v___x_925_, 2);
v___x_945_ = lean_box(0);
v___x_946_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_947_ = lean_array_uget_borrowed(v_as_927_, v_i_929_);
lean_inc(v_subst_944_);
v___x_948_ = l_Lean_Meta_FVarSubst_apply(v_subst_944_, v_a_947_);
v___x_949_ = l_Lean_Expr_isFVar(v___x_948_);
if (v___x_949_ == 0)
{
lean_dec_ref(v___x_948_);
v_a_938_ = v___x_946_;
goto v___jp_937_;
}
else
{
lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_950_ = l_Lean_Expr_fvarId_x21(v___x_948_);
lean_dec_ref(v___x_948_);
lean_inc(v___x_950_);
v___x_951_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_950_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_951_) == 0)
{
lean_object* v_a_952_; uint8_t v___x_953_; 
v_a_952_ = lean_ctor_get(v___x_951_, 0);
lean_inc(v_a_952_);
lean_dec_ref_known(v___x_951_, 1);
v___x_953_ = lean_unbox(v_a_952_);
lean_dec(v_a_952_);
if (v___x_953_ == 0)
{
lean_dec(v___x_950_);
v_a_938_ = v___x_946_;
goto v___jp_937_;
}
else
{
lean_object* v___x_954_; 
lean_inc(v___x_926_);
v___x_954_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_926_, v___x_950_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_);
if (lean_obj_tag(v___x_954_) == 0)
{
lean_object* v_a_955_; lean_object* v___x_957_; uint8_t v_isShared_958_; uint8_t v_isSharedCheck_965_; 
v_a_955_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_965_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_965_ == 0)
{
v___x_957_ = v___x_954_;
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
else
{
lean_inc(v_a_955_);
lean_dec(v___x_954_);
v___x_957_ = lean_box(0);
v_isShared_958_ = v_isSharedCheck_965_;
goto v_resetjp_956_;
}
v_resetjp_956_:
{
uint8_t v___x_959_; 
v___x_959_ = lean_unbox(v_a_955_);
if (v___x_959_ == 0)
{
lean_del_object(v___x_957_);
lean_dec(v_a_955_);
v_a_938_ = v___x_946_;
goto v___jp_937_;
}
else
{
lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_963_; 
lean_dec(v___x_926_);
lean_dec_ref(v___x_925_);
v___x_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_960_, 0, v_a_955_);
v___x_961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_961_, 0, v___x_960_);
lean_ctor_set(v___x_961_, 1, v___x_945_);
if (v_isShared_958_ == 0)
{
lean_ctor_set(v___x_957_, 0, v___x_961_);
v___x_963_ = v___x_957_;
goto v_reusejp_962_;
}
else
{
lean_object* v_reuseFailAlloc_964_; 
v_reuseFailAlloc_964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_964_, 0, v___x_961_);
v___x_963_ = v_reuseFailAlloc_964_;
goto v_reusejp_962_;
}
v_reusejp_962_:
{
return v___x_963_;
}
}
}
}
else
{
lean_object* v_a_966_; lean_object* v___x_968_; uint8_t v_isShared_969_; uint8_t v_isSharedCheck_973_; 
lean_dec(v___x_926_);
lean_dec_ref(v___x_925_);
v_a_966_ = lean_ctor_get(v___x_954_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_954_);
if (v_isSharedCheck_973_ == 0)
{
v___x_968_ = v___x_954_;
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
else
{
lean_inc(v_a_966_);
lean_dec(v___x_954_);
v___x_968_ = lean_box(0);
v_isShared_969_ = v_isSharedCheck_973_;
goto v_resetjp_967_;
}
v_resetjp_967_:
{
lean_object* v___x_971_; 
if (v_isShared_969_ == 0)
{
v___x_971_ = v___x_968_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
}
}
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v___x_950_);
lean_dec(v___x_926_);
lean_dec_ref(v___x_925_);
v_a_974_ = lean_ctor_get(v___x_951_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_951_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_951_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_951_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_979_; 
if (v_isShared_977_ == 0)
{
v___x_979_ = v___x_976_;
goto v_reusejp_978_;
}
else
{
lean_object* v_reuseFailAlloc_980_; 
v_reuseFailAlloc_980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_980_, 0, v_a_974_);
v___x_979_ = v_reuseFailAlloc_980_;
goto v_reusejp_978_;
}
v_reusejp_978_:
{
return v___x_979_;
}
}
}
}
}
v___jp_937_:
{
size_t v___x_939_; size_t v___x_940_; 
v___x_939_ = ((size_t)1ULL);
v___x_940_ = lean_usize_add(v_i_929_, v___x_939_);
lean_inc_ref(v_a_938_);
v_i_929_ = v___x_940_;
v_b_930_ = v_a_938_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_982_, lean_object* v_mvarId_983_, lean_object* v_fields_984_, size_t v_sz_985_, size_t v___x_986_, lean_object* v___x_987_, uint8_t v___x_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_){
_start:
{
lean_object* v___x_995_; 
v___x_995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_982_, v_mvarId_983_, v_fields_984_, v_sz_985_, v___x_986_, v___x_987_, v___y_989_, v___y_990_, v___y_991_, v___y_992_, v___y_993_);
if (lean_obj_tag(v___x_995_) == 0)
{
lean_object* v_a_996_; lean_object* v___x_998_; uint8_t v_isShared_999_; uint8_t v_isSharedCheck_1009_; 
v_a_996_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1009_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1009_ == 0)
{
v___x_998_ = v___x_995_;
v_isShared_999_ = v_isSharedCheck_1009_;
goto v_resetjp_997_;
}
else
{
lean_inc(v_a_996_);
lean_dec(v___x_995_);
v___x_998_ = lean_box(0);
v_isShared_999_ = v_isSharedCheck_1009_;
goto v_resetjp_997_;
}
v_resetjp_997_:
{
lean_object* v_fst_1000_; 
v_fst_1000_ = lean_ctor_get(v_a_996_, 0);
lean_inc(v_fst_1000_);
lean_dec(v_a_996_);
if (lean_obj_tag(v_fst_1000_) == 0)
{
lean_object* v___x_1001_; lean_object* v___x_1003_; 
v___x_1001_ = lean_box(v___x_988_);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v___x_1001_);
v___x_1003_ = v___x_998_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v___x_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
else
{
lean_object* v_val_1005_; lean_object* v___x_1007_; 
v_val_1005_ = lean_ctor_get(v_fst_1000_, 0);
lean_inc(v_val_1005_);
lean_dec_ref_known(v_fst_1000_, 1);
if (v_isShared_999_ == 0)
{
lean_ctor_set(v___x_998_, 0, v_val_1005_);
v___x_1007_ = v___x_998_;
goto v_reusejp_1006_;
}
else
{
lean_object* v_reuseFailAlloc_1008_; 
v_reuseFailAlloc_1008_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_val_1005_);
v___x_1007_ = v_reuseFailAlloc_1008_;
goto v_reusejp_1006_;
}
v_reusejp_1006_:
{
return v___x_1007_;
}
}
}
}
else
{
lean_object* v_a_1010_; lean_object* v___x_1012_; uint8_t v_isShared_1013_; uint8_t v_isSharedCheck_1017_; 
v_a_1010_ = lean_ctor_get(v___x_995_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_995_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1012_ = v___x_995_;
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
else
{
lean_inc(v_a_1010_);
lean_dec(v___x_995_);
v___x_1012_ = lean_box(0);
v_isShared_1013_ = v_isSharedCheck_1017_;
goto v_resetjp_1011_;
}
v_resetjp_1011_:
{
lean_object* v___x_1015_; 
if (v_isShared_1013_ == 0)
{
v___x_1015_ = v___x_1012_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
v___x_1015_ = v_reuseFailAlloc_1016_;
goto v_reusejp_1014_;
}
v_reusejp_1014_:
{
return v___x_1015_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1018_, lean_object* v_as_1019_, lean_object* v_sz_1020_, lean_object* v_i_1021_, lean_object* v_b_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_){
_start:
{
size_t v_sz_boxed_1029_; size_t v_i_boxed_1030_; lean_object* v_res_1031_; 
v_sz_boxed_1029_ = lean_unbox_usize(v_sz_1020_);
lean_dec(v_sz_1020_);
v_i_boxed_1030_ = lean_unbox_usize(v_i_1021_);
lean_dec(v_i_1021_);
v_res_1031_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1018_, v_as_1019_, v_sz_boxed_1029_, v_i_boxed_1030_, v_b_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_);
lean_dec(v___y_1027_);
lean_dec_ref(v___y_1026_);
lean_dec(v___y_1025_);
lean_dec_ref(v___y_1024_);
lean_dec(v___y_1023_);
lean_dec_ref(v_as_1019_);
lean_dec(v_val_1018_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1032_, lean_object* v___x_1033_, lean_object* v_as_1034_, lean_object* v_sz_1035_, lean_object* v_i_1036_, lean_object* v_b_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
size_t v_sz_boxed_1044_; size_t v_i_boxed_1045_; lean_object* v_res_1046_; 
v_sz_boxed_1044_ = lean_unbox_usize(v_sz_1035_);
lean_dec(v_sz_1035_);
v_i_boxed_1045_ = lean_unbox_usize(v_i_1036_);
lean_dec(v_i_1036_);
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1032_, v___x_1033_, v_as_1034_, v_sz_boxed_1044_, v_i_boxed_1045_, v_b_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v_as_1034_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1047_, lean_object* v_fvarId_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1047_, v_fvarId_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_);
lean_dec(v_a_1053_);
lean_dec_ref(v_a_1052_);
lean_dec(v_a_1051_);
lean_dec_ref(v_a_1050_);
lean_dec(v_a_1049_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1056_, lean_object* v_msg_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1056_, v_msg_1057_, v___y_1059_, v___y_1060_, v___y_1061_, v___y_1062_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1065_, lean_object* v_msg_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_res_1073_; 
v_res_1073_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1065_, v_msg_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_);
lean_dec(v___y_1071_);
lean_dec_ref(v___y_1070_);
lean_dec(v___y_1069_);
lean_dec_ref(v___y_1068_);
lean_dec(v___y_1067_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_Meta_saveState___redArg(v___y_1076_, v___y_1078_);
if (lean_obj_tag(v___x_1080_) == 0)
{
lean_object* v_a_1081_; lean_object* v___y_1083_; lean_object* v___y_1084_; uint8_t v___y_1085_; lean_object* v___y_1104_; lean_object* v_a_1105_; lean_object* v___x_1108_; 
v_a_1081_ = lean_ctor_get(v___x_1080_, 0);
lean_inc(v_a_1081_);
lean_dec_ref_known(v___x_1080_, 1);
lean_inc(v___y_1078_);
lean_inc_ref(v___y_1077_);
lean_inc(v___y_1076_);
lean_inc_ref(v___y_1075_);
v___x_1108_ = lean_apply_5(v_x_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, lean_box(0));
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
v___x_1111_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1081_, v___y_1076_, v___y_1078_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1118_; 
lean_dec(v_a_1081_);
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
v___y_1104_ = v___x_1125_;
v_a_1105_ = v_a_1120_;
goto v___jp_1103_;
}
}
}
}
else
{
lean_dec(v_a_1109_);
lean_dec(v_a_1081_);
return v___x_1108_;
}
}
else
{
lean_object* v_a_1128_; 
v_a_1128_ = lean_ctor_get(v___x_1108_, 0);
lean_inc(v_a_1128_);
v___y_1104_ = v___x_1108_;
v_a_1105_ = v_a_1128_;
goto v___jp_1103_;
}
v___jp_1082_:
{
if (v___y_1085_ == 0)
{
lean_object* v___x_1086_; 
lean_dec_ref(v___y_1084_);
v___x_1086_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1081_, v___y_1076_, v___y_1078_);
lean_dec(v_a_1081_);
if (lean_obj_tag(v___x_1086_) == 0)
{
lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1093_; 
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v___x_1086_, 0);
lean_dec(v_unused_1094_);
v___x_1088_ = v___x_1086_;
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
else
{
lean_dec(v___x_1086_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1093_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1091_; 
if (v_isShared_1089_ == 0)
{
lean_ctor_set_tag(v___x_1088_, 1);
lean_ctor_set(v___x_1088_, 0, v___y_1083_);
v___x_1091_ = v___x_1088_;
goto v_reusejp_1090_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v___y_1083_);
v___x_1091_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1090_;
}
v_reusejp_1090_:
{
return v___x_1091_;
}
}
}
else
{
lean_object* v_a_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1102_; 
lean_dec_ref(v___y_1083_);
v_a_1095_ = lean_ctor_get(v___x_1086_, 0);
v_isSharedCheck_1102_ = !lean_is_exclusive(v___x_1086_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1097_ = v___x_1086_;
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_a_1095_);
lean_dec(v___x_1086_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1102_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1098_ == 0)
{
v___x_1100_ = v___x_1097_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_a_1095_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
else
{
lean_dec_ref(v___y_1083_);
lean_dec(v_a_1081_);
return v___y_1084_;
}
}
v___jp_1103_:
{
uint8_t v___x_1106_; 
v___x_1106_ = l_Lean_Exception_isInterrupt(v_a_1105_);
if (v___x_1106_ == 0)
{
uint8_t v___x_1107_; 
lean_inc_ref(v_a_1105_);
v___x_1107_ = l_Lean_Exception_isRuntime(v_a_1105_);
v___y_1083_ = v_a_1105_;
v___y_1084_ = v___y_1104_;
v___y_1085_ = v___x_1107_;
goto v___jp_1082_;
}
else
{
v___y_1083_ = v_a_1105_;
v___y_1084_ = v___y_1104_;
v___y_1085_ = v___x_1106_;
goto v___jp_1082_;
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec_ref(v_x_1074_);
v_a_1129_ = lean_ctor_get(v___x_1080_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1080_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1080_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1080_);
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
lean_inc(v_a_1240_);
v___x_1241_ = lean_unbox(v_a_1240_);
lean_dec(v_a_1240_);
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
lean_object* v___f_1307_; lean_object* v___x_5509__overap_1308_; lean_object* v___x_1309_; 
v___f_1307_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_5509__overap_1308_ = lean_panic_fn_borrowed(v___f_1307_, v_msg_1301_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
v___x_1309_ = lean_apply_5(v___x_5509__overap_1308_, v___y_1302_, v___y_1303_, v___y_1304_, v___y_1305_, lean_box(0));
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
v___x_1337_ = lean_st_ref_set(v___y_1318_, v___x_1336_);
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
uint8_t v___x_7190__boxed_1725_; lean_object* v_res_1726_; 
v___x_7190__boxed_1725_ = lean_unbox(v___x_1717_);
v_res_1726_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1716_, v___x_7190__boxed_1725_, v_localDecl_1718_, v_mvarId_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_);
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
lean_object* v_snd_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_2454_; 
v_snd_1817_ = lean_ctor_get(v_b_1809_, 1);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_b_1809_);
if (v_isSharedCheck_2454_ == 0)
{
lean_object* v_unused_2455_; 
v_unused_2455_ = lean_ctor_get(v_b_1809_, 0);
lean_dec(v_unused_2455_);
v___x_1819_ = v_b_1809_;
v_isShared_1820_ = v_isSharedCheck_2454_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_snd_1817_);
lean_dec(v_b_1809_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_2454_;
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
lean_object* v_val_1836_; lean_object* v___x_1838_; uint8_t v_isShared_1839_; uint8_t v_isSharedCheck_2453_; 
v_val_1836_ = lean_ctor_get(v_a_1835_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_a_1835_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_1838_ = v_a_1835_;
v_isShared_1839_ = v_isSharedCheck_2453_;
goto v_resetjp_1837_;
}
else
{
lean_inc(v_val_1836_);
lean_dec(v_a_1835_);
v___x_1838_ = lean_box(0);
v_isShared_1839_ = v_isSharedCheck_2453_;
goto v_resetjp_1837_;
}
v_resetjp_1837_:
{
lean_object* v___x_1840_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___x_1881_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; uint8_t v___y_1908_; uint8_t v___x_1909_; lean_object* v___y_1911_; lean_object* v___y_1912_; uint8_t v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; lean_object* v___y_1917_; lean_object* v___y_1918_; uint8_t v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; uint8_t v___y_1922_; uint8_t v___y_1924_; uint8_t v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; uint8_t v___y_1932_; lean_object* v___y_1933_; uint8_t v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; uint8_t v___y_1938_; 
v___x_1840_ = lean_box(0);
v___x_1881_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1909_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1836_);
if (v___x_1909_ == 0)
{
lean_object* v___x_1953_; uint8_t v___y_1955_; uint8_t v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; uint8_t v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; uint8_t v___y_1967_; lean_object* v___y_1968_; lean_object* v___y_1969_; lean_object* v___y_1970_; uint8_t v___y_1971_; lean_object* v___y_1974_; uint8_t v___y_1975_; lean_object* v___y_1976_; uint8_t v___y_1977_; lean_object* v___y_1978_; lean_object* v___y_1979_; lean_object* v_a_1980_; uint8_t v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; uint8_t v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; uint8_t v___y_2044_; lean_object* v___y_2045_; lean_object* v___y_2046_; uint8_t v___y_2047_; lean_object* v___y_2048_; lean_object* v___y_2049_; uint8_t v___y_2050_; lean_object* v___y_2052_; uint8_t v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; uint8_t v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; uint8_t v___y_2059_; lean_object* v___y_2062_; uint8_t v___y_2063_; lean_object* v___y_2064_; uint8_t v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; uint8_t v___y_2081_; lean_object* v___y_2082_; lean_object* v___y_2083_; uint8_t v___y_2084_; lean_object* v___y_2085_; lean_object* v___y_2086_; uint8_t v___y_2087_; uint8_t v___y_2089_; uint8_t v_isHEq_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; uint8_t v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; uint8_t v_isEq_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___x_2390_; 
v___x_1953_ = l_Lean_LocalDecl_type(v_val_1836_);
lean_inc_ref(v___x_1953_);
v___x_2390_ = l_Lean_Meta_matchNot_x3f(v___x_1953_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_2390_) == 0)
{
lean_object* v_a_2391_; 
v_a_2391_ = lean_ctor_get(v___x_2390_, 0);
lean_inc(v_a_2391_);
lean_dec_ref_known(v___x_2390_, 1);
if (lean_obj_tag(v_a_2391_) == 1)
{
lean_object* v_val_2392_; lean_object* v___x_2393_; 
v_val_2392_ = lean_ctor_get(v_a_2391_, 0);
lean_inc(v_val_2392_);
lean_dec_ref_known(v_a_2391_, 1);
v___x_2393_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2392_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_2393_) == 0)
{
lean_object* v_a_2394_; 
v_a_2394_ = lean_ctor_get(v___x_2393_, 0);
lean_inc(v_a_2394_);
lean_dec_ref_known(v___x_2393_, 1);
if (lean_obj_tag(v_a_2394_) == 1)
{
lean_object* v_val_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2436_; 
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec_ref(v_config_1804_);
v_val_2395_ = lean_ctor_get(v_a_2394_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v_a_2394_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2397_ = v_a_2394_;
v_isShared_2398_ = v_isSharedCheck_2436_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_val_2395_);
lean_dec(v_a_2394_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2436_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2399_; 
lean_inc(v_mvarId_1805_);
v___x_2399_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_2399_) == 0)
{
lean_object* v_a_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; 
v_a_2400_ = lean_ctor_get(v___x_2399_, 0);
lean_inc(v_a_2400_);
lean_dec_ref_known(v___x_2399_, 1);
v___x_2401_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_2402_ = l_Lean_mkFVar(v_val_2395_);
v___x_2403_ = l_Lean_Expr_app___override(v___x_2401_, v___x_2402_);
v___x_2404_ = l_Lean_Meta_mkFalseElim(v_a_2400_, v___x_2403_, v___y_1810_, v___y_1811_, v___y_1812_, v___y_1813_);
if (lean_obj_tag(v___x_2404_) == 0)
{
lean_object* v_a_2405_; lean_object* v___x_2406_; 
v_a_2405_ = lean_ctor_get(v___x_2404_, 0);
lean_inc(v_a_2405_);
lean_dec_ref_known(v___x_2404_, 1);
v___x_2406_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_2405_, v___y_1811_);
if (lean_obj_tag(v___x_2406_) == 0)
{
lean_object* v___x_2407_; lean_object* v___x_2409_; 
lean_dec_ref_known(v___x_2406_, 1);
v___x_2407_ = lean_box(v___x_1815_);
if (v_isShared_2398_ == 0)
{
lean_ctor_set(v___x_2397_, 0, v___x_2407_);
v___x_2409_ = v___x_2397_;
goto v_reusejp_2408_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v___x_2407_);
v___x_2409_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2408_;
}
v_reusejp_2408_:
{
lean_object* v___x_2410_; 
v___x_2410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2410_, 0, v___x_2409_);
lean_ctor_set(v___x_2410_, 1, v___x_1840_);
v_a_1822_ = v___x_2410_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_2412_; lean_object* v___x_2414_; uint8_t v_isShared_2415_; uint8_t v_isSharedCheck_2419_; 
lean_del_object(v___x_2397_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_2412_ = lean_ctor_get(v___x_2406_, 0);
v_isSharedCheck_2419_ = !lean_is_exclusive(v___x_2406_);
if (v_isSharedCheck_2419_ == 0)
{
v___x_2414_ = v___x_2406_;
v_isShared_2415_ = v_isSharedCheck_2419_;
goto v_resetjp_2413_;
}
else
{
lean_inc(v_a_2412_);
lean_dec(v___x_2406_);
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
lean_del_object(v___x_2397_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2420_ = lean_ctor_get(v___x_2404_, 0);
v_isSharedCheck_2427_ = !lean_is_exclusive(v___x_2404_);
if (v_isSharedCheck_2427_ == 0)
{
v___x_2422_ = v___x_2404_;
v_isShared_2423_ = v_isSharedCheck_2427_;
goto v_resetjp_2421_;
}
else
{
lean_inc(v_a_2420_);
lean_dec(v___x_2404_);
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
lean_del_object(v___x_2397_);
lean_dec(v_val_2395_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2428_ = lean_ctor_get(v___x_2399_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v___x_2399_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2430_ = v___x_2399_;
v_isShared_2431_ = v_isSharedCheck_2435_;
goto v_resetjp_2429_;
}
else
{
lean_inc(v_a_2428_);
lean_dec(v___x_2399_);
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
lean_dec(v_a_2394_);
v___y_2256_ = v___y_1810_;
v___y_2257_ = v___y_1811_;
v___y_2258_ = v___y_1812_;
v___y_2259_ = v___y_1813_;
goto v___jp_2255_;
}
}
else
{
lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2444_; 
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2437_ = lean_ctor_get(v___x_2393_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2393_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2439_ = v___x_2393_;
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2393_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2444_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2442_; 
if (v_isShared_2440_ == 0)
{
v___x_2442_ = v___x_2439_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v_a_2437_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
else
{
lean_dec(v_a_2391_);
v___y_2256_ = v___y_1810_;
v___y_2257_ = v___y_1811_;
v___y_2258_ = v___y_1812_;
v___y_2259_ = v___y_1813_;
goto v___jp_2255_;
}
}
else
{
lean_object* v_a_2445_; lean_object* v___x_2447_; uint8_t v_isShared_2448_; uint8_t v_isSharedCheck_2452_; 
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2445_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2447_ = v___x_2390_;
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
else
{
lean_inc(v_a_2445_);
lean_dec(v___x_2390_);
v___x_2447_ = lean_box(0);
v_isShared_2448_ = v_isSharedCheck_2452_;
goto v_resetjp_2446_;
}
v_resetjp_2446_:
{
lean_object* v___x_2450_; 
if (v_isShared_2448_ == 0)
{
v___x_2450_ = v___x_2447_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_a_2445_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
v___jp_1954_:
{
uint8_t v_genDiseq_1961_; 
v_genDiseq_1961_ = lean_ctor_get_uint8(v_config_1804_, sizeof(void*)*1 + 2);
if (v_genDiseq_1961_ == 0)
{
lean_dec_ref(v___x_1953_);
v___y_1932_ = v___y_1955_;
v___y_1933_ = v___y_1960_;
v___y_1934_ = v___y_1956_;
v___y_1935_ = v___y_1958_;
v___y_1936_ = v___y_1959_;
v___y_1937_ = v___y_1957_;
v___y_1938_ = v___x_1909_;
goto v___jp_1931_;
}
else
{
uint8_t v___x_1962_; 
v___x_1962_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1953_);
v___y_1932_ = v___y_1955_;
v___y_1933_ = v___y_1960_;
v___y_1934_ = v___y_1956_;
v___y_1935_ = v___y_1958_;
v___y_1936_ = v___y_1959_;
v___y_1937_ = v___y_1957_;
v___y_1938_ = v___x_1962_;
goto v___jp_1931_;
}
}
v___jp_1963_:
{
if (v___y_1971_ == 0)
{
lean_dec_ref(v___y_1969_);
v___y_1955_ = v___y_1964_;
v___y_1956_ = v___y_1967_;
v___y_1957_ = v___y_1968_;
v___y_1958_ = v___y_1970_;
v___y_1959_ = v___y_1965_;
v___y_1960_ = v___y_1966_;
goto v___jp_1954_;
}
else
{
lean_object* v___x_1972_; 
lean_dec_ref(v___x_1953_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v___x_1972_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1972_, 0, v___y_1969_);
return v___x_1972_;
}
}
v___jp_1973_:
{
uint8_t v___x_1981_; 
v___x_1981_ = l_Lean_Exception_isInterrupt(v_a_1980_);
if (v___x_1981_ == 0)
{
uint8_t v___x_1982_; 
lean_inc_ref(v_a_1980_);
v___x_1982_ = l_Lean_Exception_isRuntime(v_a_1980_);
v___y_1964_ = v___y_1975_;
v___y_1965_ = v___y_1974_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___y_1977_;
v___y_1968_ = v___y_1978_;
v___y_1969_ = v_a_1980_;
v___y_1970_ = v___y_1979_;
v___y_1971_ = v___x_1982_;
goto v___jp_1963_;
}
else
{
v___y_1964_ = v___y_1975_;
v___y_1965_ = v___y_1974_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___y_1977_;
v___y_1968_ = v___y_1978_;
v___y_1969_ = v_a_1980_;
v___y_1970_ = v___y_1979_;
v___y_1971_ = v___x_1981_;
goto v___jp_1963_;
}
}
v___jp_1983_:
{
lean_object* v___x_1990_; 
lean_inc_ref(v___x_1953_);
v___x_1990_ = l_Lean_Meta_mkDecide(v___x_1953_, v___y_1988_, v___y_1989_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_1990_) == 0)
{
lean_object* v_a_1991_; lean_object* v_keyedConfig_1992_; uint8_t v_trackZetaDelta_1993_; lean_object* v_zetaDeltaSet_1994_; lean_object* v_lctx_1995_; lean_object* v_localInstances_1996_; lean_object* v_defEqCtx_x3f_1997_; lean_object* v_synthPendingDepth_1998_; lean_object* v_customCanUnfoldPredicate_x3f_1999_; uint8_t v_univApprox_2000_; uint8_t v_inTypeClassResolution_2001_; uint8_t v_cacheInferType_2002_; uint8_t v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; 
v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
lean_inc_n(v_a_1991_, 2);
lean_dec_ref_known(v___x_1990_, 1);
v_keyedConfig_1992_ = lean_ctor_get(v___y_1988_, 0);
v_trackZetaDelta_1993_ = lean_ctor_get_uint8(v___y_1988_, sizeof(void*)*7);
v_zetaDeltaSet_1994_ = lean_ctor_get(v___y_1988_, 1);
v_lctx_1995_ = lean_ctor_get(v___y_1988_, 2);
v_localInstances_1996_ = lean_ctor_get(v___y_1988_, 3);
v_defEqCtx_x3f_1997_ = lean_ctor_get(v___y_1988_, 4);
v_synthPendingDepth_1998_ = lean_ctor_get(v___y_1988_, 5);
v_customCanUnfoldPredicate_x3f_1999_ = lean_ctor_get(v___y_1988_, 6);
v_univApprox_2000_ = lean_ctor_get_uint8(v___y_1988_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2001_ = lean_ctor_get_uint8(v___y_1988_, sizeof(void*)*7 + 2);
v_cacheInferType_2002_ = lean_ctor_get_uint8(v___y_1988_, sizeof(void*)*7 + 3);
v___x_2003_ = 1;
lean_inc_ref(v_keyedConfig_1992_);
v___x_2004_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2003_, v_keyedConfig_1992_);
lean_inc(v_customCanUnfoldPredicate_x3f_1999_);
lean_inc(v_synthPendingDepth_1998_);
lean_inc(v_defEqCtx_x3f_1997_);
lean_inc_ref(v_localInstances_1996_);
lean_inc_ref(v_lctx_1995_);
lean_inc(v_zetaDeltaSet_1994_);
v___x_2005_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2005_, 0, v___x_2004_);
lean_ctor_set(v___x_2005_, 1, v_zetaDeltaSet_1994_);
lean_ctor_set(v___x_2005_, 2, v_lctx_1995_);
lean_ctor_set(v___x_2005_, 3, v_localInstances_1996_);
lean_ctor_set(v___x_2005_, 4, v_defEqCtx_x3f_1997_);
lean_ctor_set(v___x_2005_, 5, v_synthPendingDepth_1998_);
lean_ctor_set(v___x_2005_, 6, v_customCanUnfoldPredicate_x3f_1999_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*7, v_trackZetaDelta_1993_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*7 + 1, v_univApprox_2000_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2001_);
lean_ctor_set_uint8(v___x_2005_, sizeof(void*)*7 + 3, v_cacheInferType_2002_);
lean_inc(v___y_1986_);
lean_inc_ref(v___y_1985_);
lean_inc(v___y_1989_);
v___x_2006_ = lean_whnf(v_a_1991_, v___x_2005_, v___y_1989_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_2006_) == 0)
{
lean_object* v_a_2007_; lean_object* v___x_2008_; uint8_t v___x_2009_; 
v_a_2007_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2007_);
lean_dec_ref_known(v___x_2006_, 1);
v___x_2008_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2009_ = l_Lean_Expr_isConstOf(v_a_2007_, v___x_2008_);
lean_dec(v_a_2007_);
if (v___x_2009_ == 0)
{
lean_dec(v_a_1991_);
v___y_1955_ = v___y_1984_;
v___y_1956_ = v___y_1987_;
v___y_1957_ = v___y_1988_;
v___y_1958_ = v___y_1989_;
v___y_1959_ = v___y_1985_;
v___y_1960_ = v___y_1986_;
goto v___jp_1954_;
}
else
{
lean_object* v___x_2010_; 
lean_inc(v_a_1991_);
v___x_2010_ = l_Lean_Meta_mkEqRefl(v_a_1991_, v___y_1988_, v___y_1989_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_2010_) == 0)
{
lean_object* v_a_2011_; lean_object* v___x_2012_; 
v_a_2011_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2011_);
lean_dec_ref_known(v___x_2010_, 1);
lean_inc(v_mvarId_1805_);
v___x_2012_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_1988_, v___y_1989_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_2012_) == 0)
{
lean_object* v_a_2013_; lean_object* v_nargs_2014_; lean_object* v___x_2015_; lean_object* v_dummy_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v_a_2013_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2013_);
lean_dec_ref_known(v___x_2012_, 1);
v_nargs_2014_ = l_Lean_Expr_getAppNumArgs(v_a_1991_);
v___x_2015_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2016_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_2014_);
v___x_2017_ = lean_mk_array(v_nargs_2014_, v_dummy_2016_);
v___x_2018_ = lean_unsigned_to_nat(1u);
v___x_2019_ = lean_nat_sub(v_nargs_2014_, v___x_2018_);
lean_dec(v_nargs_2014_);
v___x_2020_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1991_, v___x_2017_, v___x_2019_);
v___x_2021_ = lean_array_push(v___x_2020_, v_a_2011_);
v___x_2022_ = l_Lean_mkAppN(v___x_2015_, v___x_2021_);
lean_dec_ref(v___x_2021_);
lean_inc(v_val_1836_);
v___x_2023_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_2024_ = l_Lean_Meta_mkAbsurd(v_a_2013_, v___x_2023_, v___x_2022_, v___y_1988_, v___y_1989_, v___y_1985_, v___y_1986_);
if (lean_obj_tag(v___x_2024_) == 0)
{
lean_object* v_a_2025_; lean_object* v___x_2026_; 
v_a_2025_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2025_);
lean_dec_ref_known(v___x_2024_, 1);
lean_inc(v_mvarId_1805_);
v___x_2026_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_2025_, v___y_1989_);
if (lean_obj_tag(v___x_2026_) == 0)
{
lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2035_; 
lean_dec_ref(v___x_1953_);
lean_dec(v_val_1836_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_isSharedCheck_2035_ = !lean_is_exclusive(v___x_2026_);
if (v_isSharedCheck_2035_ == 0)
{
lean_object* v_unused_2036_; 
v_unused_2036_ = lean_ctor_get(v___x_2026_, 0);
lean_dec(v_unused_2036_);
v___x_2028_ = v___x_2026_;
v_isShared_2029_ = v_isSharedCheck_2035_;
goto v_resetjp_2027_;
}
else
{
lean_dec(v___x_2026_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2035_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2030_; lean_object* v___x_2032_; 
v___x_2030_ = lean_box(v___x_1815_);
if (v_isShared_2029_ == 0)
{
lean_ctor_set_tag(v___x_2028_, 1);
lean_ctor_set(v___x_2028_, 0, v___x_2030_);
v___x_2032_ = v___x_2028_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2034_; 
v_reuseFailAlloc_2034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2034_, 0, v___x_2030_);
v___x_2032_ = v_reuseFailAlloc_2034_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2033_, 0, v___x_2032_);
lean_ctor_set(v___x_2033_, 1, v___x_1840_);
v_a_1822_ = v___x_2033_;
goto v___jp_1821_;
}
}
}
else
{
lean_object* v_a_2037_; 
v_a_2037_ = lean_ctor_get(v___x_2026_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2026_, 1);
v___y_1974_ = v___y_1985_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1989_;
v_a_1980_ = v_a_2037_;
goto v___jp_1973_;
}
}
else
{
lean_object* v_a_2038_; 
v_a_2038_ = lean_ctor_get(v___x_2024_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2024_, 1);
v___y_1974_ = v___y_1985_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1989_;
v_a_1980_ = v_a_2038_;
goto v___jp_1973_;
}
}
else
{
lean_object* v_a_2039_; 
lean_dec(v_a_2011_);
lean_dec(v_a_1991_);
v_a_2039_ = lean_ctor_get(v___x_2012_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2012_, 1);
v___y_1974_ = v___y_1985_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1989_;
v_a_1980_ = v_a_2039_;
goto v___jp_1973_;
}
}
else
{
lean_object* v_a_2040_; 
lean_dec(v_a_1991_);
v_a_2040_ = lean_ctor_get(v___x_2010_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2010_, 1);
v___y_1974_ = v___y_1985_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1989_;
v_a_1980_ = v_a_2040_;
goto v___jp_1973_;
}
}
}
else
{
lean_object* v_a_2041_; 
lean_dec(v_a_1991_);
v_a_2041_ = lean_ctor_get(v___x_2006_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2006_, 1);
v___y_1974_ = v___y_1985_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1989_;
v_a_1980_ = v_a_2041_;
goto v___jp_1973_;
}
}
else
{
lean_object* v_a_2042_; 
v_a_2042_ = lean_ctor_get(v___x_1990_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_1990_, 1);
v___y_1974_ = v___y_1985_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v___y_1979_ = v___y_1989_;
v_a_1980_ = v_a_2042_;
goto v___jp_1973_;
}
}
v___jp_2043_:
{
if (v___y_2050_ == 0)
{
v___y_1955_ = v___y_2044_;
v___y_1956_ = v___y_2047_;
v___y_1957_ = v___y_2048_;
v___y_1958_ = v___y_2049_;
v___y_1959_ = v___y_2045_;
v___y_1960_ = v___y_2046_;
goto v___jp_1954_;
}
else
{
v___y_1984_ = v___y_2044_;
v___y_1985_ = v___y_2045_;
v___y_1986_ = v___y_2046_;
v___y_1987_ = v___y_2047_;
v___y_1988_ = v___y_2048_;
v___y_1989_ = v___y_2049_;
goto v___jp_1983_;
}
}
v___jp_2051_:
{
if (v___y_2059_ == 0)
{
lean_dec_ref(v___y_2055_);
v___y_2044_ = v___y_2053_;
v___y_2045_ = v___y_2052_;
v___y_2046_ = v___y_2054_;
v___y_2047_ = v___y_2056_;
v___y_2048_ = v___y_2057_;
v___y_2049_ = v___y_2058_;
v___y_2050_ = v___x_1909_;
goto v___jp_2043_;
}
else
{
uint8_t v___x_2060_; 
v___x_2060_ = l_Lean_Expr_hasFVar(v___y_2055_);
lean_dec_ref(v___y_2055_);
if (v___x_2060_ == 0)
{
v___y_1984_ = v___y_2053_;
v___y_1985_ = v___y_2052_;
v___y_1986_ = v___y_2054_;
v___y_1987_ = v___y_2056_;
v___y_1988_ = v___y_2057_;
v___y_1989_ = v___y_2058_;
goto v___jp_1983_;
}
else
{
v___y_2044_ = v___y_2053_;
v___y_2045_ = v___y_2052_;
v___y_2046_ = v___y_2054_;
v___y_2047_ = v___y_2056_;
v___y_2048_ = v___y_2057_;
v___y_2049_ = v___y_2058_;
v___y_2050_ = v___x_1909_;
goto v___jp_2043_;
}
}
}
v___jp_2061_:
{
lean_object* v___x_2069_; 
lean_inc_ref(v___x_1953_);
v___x_2069_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1953_, v___y_2067_);
if (lean_obj_tag(v___x_2069_) == 0)
{
lean_object* v_a_2070_; uint8_t v___x_2071_; 
v_a_2070_ = lean_ctor_get(v___x_2069_, 0);
lean_inc(v_a_2070_);
lean_dec_ref_known(v___x_2069_, 1);
v___x_2071_ = l_Lean_Expr_hasMVar(v_a_2070_);
if (v___x_2071_ == 0)
{
v___y_2052_ = v___y_2062_;
v___y_2053_ = v___y_2063_;
v___y_2054_ = v___y_2064_;
v___y_2055_ = v_a_2070_;
v___y_2056_ = v___y_2065_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___y_2067_;
v___y_2059_ = v___y_2068_;
goto v___jp_2051_;
}
else
{
v___y_2052_ = v___y_2062_;
v___y_2053_ = v___y_2063_;
v___y_2054_ = v___y_2064_;
v___y_2055_ = v_a_2070_;
v___y_2056_ = v___y_2065_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___y_2067_;
v___y_2059_ = v___x_1909_;
goto v___jp_2051_;
}
}
else
{
lean_object* v_a_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2079_; 
lean_dec_ref(v___x_1953_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2072_ = lean_ctor_get(v___x_2069_, 0);
v_isSharedCheck_2079_ = !lean_is_exclusive(v___x_2069_);
if (v_isSharedCheck_2079_ == 0)
{
v___x_2074_ = v___x_2069_;
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_a_2072_);
lean_dec(v___x_2069_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2079_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2077_; 
if (v_isShared_2075_ == 0)
{
v___x_2077_ = v___x_2074_;
goto v_reusejp_2076_;
}
else
{
lean_object* v_reuseFailAlloc_2078_; 
v_reuseFailAlloc_2078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2078_, 0, v_a_2072_);
v___x_2077_ = v_reuseFailAlloc_2078_;
goto v_reusejp_2076_;
}
v_reusejp_2076_:
{
return v___x_2077_;
}
}
}
}
v___jp_2080_:
{
if (v___y_2087_ == 0)
{
v___y_1955_ = v___y_2081_;
v___y_1956_ = v___y_2084_;
v___y_1957_ = v___y_2085_;
v___y_1958_ = v___y_2086_;
v___y_1959_ = v___y_2082_;
v___y_1960_ = v___y_2083_;
goto v___jp_1954_;
}
else
{
v___y_2062_ = v___y_2082_;
v___y_2063_ = v___y_2081_;
v___y_2064_ = v___y_2083_;
v___y_2065_ = v___y_2084_;
v___y_2066_ = v___y_2085_;
v___y_2067_ = v___y_2086_;
v___y_2068_ = v___y_2087_;
goto v___jp_2061_;
}
}
v___jp_2088_:
{
uint8_t v_useDecide_2095_; 
v_useDecide_2095_ = lean_ctor_get_uint8(v_config_1804_, sizeof(void*)*1);
if (v_useDecide_2095_ == 0)
{
v___y_2081_ = v___y_2089_;
v___y_2082_ = v___y_2093_;
v___y_2083_ = v___y_2094_;
v___y_2084_ = v_isHEq_2090_;
v___y_2085_ = v___y_2091_;
v___y_2086_ = v___y_2092_;
v___y_2087_ = v___x_1909_;
goto v___jp_2080_;
}
else
{
uint8_t v___x_2096_; 
v___x_2096_ = l_Lean_Expr_hasFVar(v___x_1953_);
if (v___x_2096_ == 0)
{
v___y_2062_ = v___y_2093_;
v___y_2063_ = v___y_2089_;
v___y_2064_ = v___y_2094_;
v___y_2065_ = v_isHEq_2090_;
v___y_2066_ = v___y_2091_;
v___y_2067_ = v___y_2092_;
v___y_2068_ = v_useDecide_2095_;
goto v___jp_2061_;
}
else
{
v___y_2081_ = v___y_2089_;
v___y_2082_ = v___y_2093_;
v___y_2083_ = v___y_2094_;
v___y_2084_ = v_isHEq_2090_;
v___y_2085_ = v___y_2091_;
v___y_2086_ = v___y_2092_;
v___y_2087_ = v___x_1909_;
goto v___jp_2080_;
}
}
}
v___jp_2097_:
{
lean_object* v___x_2105_; 
v___x_2105_ = l_Lean_Meta_isExprDefEq(v___y_2103_, v___y_2100_, v___y_2102_, v___y_2101_, v___y_2104_, v___y_2099_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v_a_2106_; uint8_t v___x_2107_; 
v_a_2106_ = lean_ctor_get(v___x_2105_, 0);
lean_inc(v_a_2106_);
lean_dec_ref_known(v___x_2105_, 1);
v___x_2107_ = lean_unbox(v_a_2106_);
lean_dec(v_a_2106_);
if (v___x_2107_ == 0)
{
v___y_2089_ = v___y_2098_;
v_isHEq_2090_ = v___x_1815_;
v___y_2091_ = v___y_2102_;
v___y_2092_ = v___y_2101_;
v___y_2093_ = v___y_2104_;
v___y_2094_ = v___y_2099_;
goto v___jp_2088_;
}
else
{
lean_object* v___x_2108_; 
lean_dec_ref(v___x_1953_);
lean_dec_ref(v_config_1804_);
lean_inc(v_mvarId_1805_);
v___x_2108_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_2102_, v___y_2101_, v___y_2104_, v___y_2099_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_2111_ = l_Lean_Meta_mkEqOfHEq(v___x_2110_, v___x_1815_, v___y_2102_, v___y_2101_, v___y_2104_, v___y_2099_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v_a_2112_; lean_object* v___x_2113_; 
v_a_2112_ = lean_ctor_get(v___x_2111_, 0);
lean_inc(v_a_2112_);
lean_dec_ref_known(v___x_2111_, 1);
v___x_2113_ = l_Lean_Meta_mkNoConfusion(v_a_2109_, v_a_2112_, v___y_2102_, v___y_2101_, v___y_2104_, v___y_2099_);
if (lean_obj_tag(v___x_2113_) == 0)
{
lean_object* v_a_2114_; lean_object* v___x_2115_; 
v_a_2114_ = lean_ctor_get(v___x_2113_, 0);
lean_inc(v_a_2114_);
lean_dec_ref_known(v___x_2113_, 1);
v___x_2115_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_2114_, v___y_2101_);
if (lean_obj_tag(v___x_2115_) == 0)
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; 
lean_dec_ref_known(v___x_2115_, 1);
v___x_2116_ = lean_box(v___x_1815_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
lean_ctor_set(v___x_2118_, 1, v___x_1840_);
v_a_1822_ = v___x_2118_;
goto v___jp_1821_;
}
else
{
lean_object* v_a_2119_; lean_object* v___x_2121_; uint8_t v_isShared_2122_; uint8_t v_isSharedCheck_2126_; 
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_2119_ = lean_ctor_get(v___x_2115_, 0);
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2115_);
if (v_isSharedCheck_2126_ == 0)
{
v___x_2121_ = v___x_2115_;
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
else
{
lean_inc(v_a_2119_);
lean_dec(v___x_2115_);
v___x_2121_ = lean_box(0);
v_isShared_2122_ = v_isSharedCheck_2126_;
goto v_resetjp_2120_;
}
v_resetjp_2120_:
{
lean_object* v___x_2124_; 
if (v_isShared_2122_ == 0)
{
v___x_2124_ = v___x_2121_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v_a_2119_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
}
else
{
lean_object* v_a_2127_; lean_object* v___x_2129_; uint8_t v_isShared_2130_; uint8_t v_isSharedCheck_2134_; 
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2127_ = lean_ctor_get(v___x_2113_, 0);
v_isSharedCheck_2134_ = !lean_is_exclusive(v___x_2113_);
if (v_isSharedCheck_2134_ == 0)
{
v___x_2129_ = v___x_2113_;
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
else
{
lean_inc(v_a_2127_);
lean_dec(v___x_2113_);
v___x_2129_ = lean_box(0);
v_isShared_2130_ = v_isSharedCheck_2134_;
goto v_resetjp_2128_;
}
v_resetjp_2128_:
{
lean_object* v___x_2132_; 
if (v_isShared_2130_ == 0)
{
v___x_2132_ = v___x_2129_;
goto v_reusejp_2131_;
}
else
{
lean_object* v_reuseFailAlloc_2133_; 
v_reuseFailAlloc_2133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2127_);
v___x_2132_ = v_reuseFailAlloc_2133_;
goto v_reusejp_2131_;
}
v_reusejp_2131_:
{
return v___x_2132_;
}
}
}
}
else
{
lean_object* v_a_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2142_; 
lean_dec(v_a_2109_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2135_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2142_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2142_ == 0)
{
v___x_2137_ = v___x_2111_;
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_a_2135_);
lean_dec(v___x_2111_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2142_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
lean_object* v___x_2140_; 
if (v_isShared_2138_ == 0)
{
v___x_2140_ = v___x_2137_;
goto v_reusejp_2139_;
}
else
{
lean_object* v_reuseFailAlloc_2141_; 
v_reuseFailAlloc_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2141_, 0, v_a_2135_);
v___x_2140_ = v_reuseFailAlloc_2141_;
goto v_reusejp_2139_;
}
v_reusejp_2139_:
{
return v___x_2140_;
}
}
}
}
else
{
lean_object* v_a_2143_; lean_object* v___x_2145_; uint8_t v_isShared_2146_; uint8_t v_isSharedCheck_2150_; 
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2143_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2150_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2145_ = v___x_2108_;
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
else
{
lean_inc(v_a_2143_);
lean_dec(v___x_2108_);
v___x_2145_ = lean_box(0);
v_isShared_2146_ = v_isSharedCheck_2150_;
goto v_resetjp_2144_;
}
v_resetjp_2144_:
{
lean_object* v___x_2148_; 
if (v_isShared_2146_ == 0)
{
v___x_2148_ = v___x_2145_;
goto v_reusejp_2147_;
}
else
{
lean_object* v_reuseFailAlloc_2149_; 
v_reuseFailAlloc_2149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_a_2143_);
v___x_2148_ = v_reuseFailAlloc_2149_;
goto v_reusejp_2147_;
}
v_reusejp_2147_:
{
return v___x_2148_;
}
}
}
}
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v___x_1953_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2151_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2105_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2105_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
v___jp_2159_:
{
lean_object* v___x_2165_; 
lean_inc_ref(v___x_1953_);
v___x_2165_ = l_Lean_Meta_matchHEq_x3f(v___x_1953_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2165_) == 0)
{
lean_object* v_a_2166_; 
v_a_2166_ = lean_ctor_get(v___x_2165_, 0);
lean_inc(v_a_2166_);
lean_dec_ref_known(v___x_2165_, 1);
if (lean_obj_tag(v_a_2166_) == 1)
{
lean_object* v_val_2167_; lean_object* v_snd_2168_; lean_object* v_snd_2169_; lean_object* v_fst_2170_; lean_object* v_fst_2171_; lean_object* v_fst_2172_; lean_object* v_snd_2173_; lean_object* v___x_2174_; 
v_val_2167_ = lean_ctor_get(v_a_2166_, 0);
lean_inc(v_val_2167_);
lean_dec_ref_known(v_a_2166_, 1);
v_snd_2168_ = lean_ctor_get(v_val_2167_, 1);
lean_inc(v_snd_2168_);
v_snd_2169_ = lean_ctor_get(v_snd_2168_, 1);
lean_inc(v_snd_2169_);
v_fst_2170_ = lean_ctor_get(v_val_2167_, 0);
lean_inc(v_fst_2170_);
lean_dec(v_val_2167_);
v_fst_2171_ = lean_ctor_get(v_snd_2168_, 0);
lean_inc(v_fst_2171_);
lean_dec(v_snd_2168_);
v_fst_2172_ = lean_ctor_get(v_snd_2169_, 0);
lean_inc(v_fst_2172_);
v_snd_2173_ = lean_ctor_get(v_snd_2169_, 1);
lean_inc(v_snd_2173_);
lean_dec(v_snd_2169_);
v___x_2174_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2171_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2174_) == 0)
{
lean_object* v_a_2175_; 
v_a_2175_ = lean_ctor_get(v___x_2174_, 0);
lean_inc(v_a_2175_);
lean_dec_ref_known(v___x_2174_, 1);
if (lean_obj_tag(v_a_2175_) == 1)
{
lean_object* v_val_2176_; lean_object* v___x_2177_; 
v_val_2176_ = lean_ctor_get(v_a_2175_, 0);
lean_inc(v_val_2176_);
lean_dec_ref_known(v_a_2175_, 1);
v___x_2177_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2173_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
if (lean_obj_tag(v___x_2177_) == 0)
{
lean_object* v_a_2178_; 
v_a_2178_ = lean_ctor_get(v___x_2177_, 0);
lean_inc(v_a_2178_);
lean_dec_ref_known(v___x_2177_, 1);
if (lean_obj_tag(v_a_2178_) == 1)
{
lean_object* v_toConstantVal_2179_; lean_object* v_val_2180_; lean_object* v_toConstantVal_2181_; lean_object* v_name_2182_; lean_object* v_name_2183_; uint8_t v___x_2184_; 
v_toConstantVal_2179_ = lean_ctor_get(v_val_2176_, 0);
lean_inc_ref(v_toConstantVal_2179_);
lean_dec(v_val_2176_);
v_val_2180_ = lean_ctor_get(v_a_2178_, 0);
lean_inc(v_val_2180_);
lean_dec_ref_known(v_a_2178_, 1);
v_toConstantVal_2181_ = lean_ctor_get(v_val_2180_, 0);
lean_inc_ref(v_toConstantVal_2181_);
lean_dec(v_val_2180_);
v_name_2182_ = lean_ctor_get(v_toConstantVal_2179_, 0);
lean_inc(v_name_2182_);
lean_dec_ref(v_toConstantVal_2179_);
v_name_2183_ = lean_ctor_get(v_toConstantVal_2181_, 0);
lean_inc(v_name_2183_);
lean_dec_ref(v_toConstantVal_2181_);
v___x_2184_ = lean_name_eq(v_name_2182_, v_name_2183_);
lean_dec(v_name_2183_);
lean_dec(v_name_2182_);
if (v___x_2184_ == 0)
{
v___y_2098_ = v_isEq_2160_;
v___y_2099_ = v___y_2164_;
v___y_2100_ = v_fst_2172_;
v___y_2101_ = v___y_2162_;
v___y_2102_ = v___y_2161_;
v___y_2103_ = v_fst_2170_;
v___y_2104_ = v___y_2163_;
goto v___jp_2097_;
}
else
{
if (v___x_1909_ == 0)
{
lean_dec(v_fst_2172_);
lean_dec(v_fst_2170_);
v___y_2089_ = v_isEq_2160_;
v_isHEq_2090_ = v___x_1815_;
v___y_2091_ = v___y_2161_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
v___y_2094_ = v___y_2164_;
goto v___jp_2088_;
}
else
{
v___y_2098_ = v_isEq_2160_;
v___y_2099_ = v___y_2164_;
v___y_2100_ = v_fst_2172_;
v___y_2101_ = v___y_2162_;
v___y_2102_ = v___y_2161_;
v___y_2103_ = v_fst_2170_;
v___y_2104_ = v___y_2163_;
goto v___jp_2097_;
}
}
}
else
{
lean_dec(v_a_2178_);
lean_dec(v_val_2176_);
lean_dec(v_fst_2172_);
lean_dec(v_fst_2170_);
v___y_2089_ = v_isEq_2160_;
v_isHEq_2090_ = v___x_1815_;
v___y_2091_ = v___y_2161_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
v___y_2094_ = v___y_2164_;
goto v___jp_2088_;
}
}
else
{
lean_object* v_a_2185_; lean_object* v___x_2187_; uint8_t v_isShared_2188_; uint8_t v_isSharedCheck_2192_; 
lean_dec(v_val_2176_);
lean_dec(v_fst_2172_);
lean_dec(v_fst_2170_);
lean_dec_ref(v___x_1953_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2185_ = lean_ctor_get(v___x_2177_, 0);
v_isSharedCheck_2192_ = !lean_is_exclusive(v___x_2177_);
if (v_isSharedCheck_2192_ == 0)
{
v___x_2187_ = v___x_2177_;
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
else
{
lean_inc(v_a_2185_);
lean_dec(v___x_2177_);
v___x_2187_ = lean_box(0);
v_isShared_2188_ = v_isSharedCheck_2192_;
goto v_resetjp_2186_;
}
v_resetjp_2186_:
{
lean_object* v___x_2190_; 
if (v_isShared_2188_ == 0)
{
v___x_2190_ = v___x_2187_;
goto v_reusejp_2189_;
}
else
{
lean_object* v_reuseFailAlloc_2191_; 
v_reuseFailAlloc_2191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2191_, 0, v_a_2185_);
v___x_2190_ = v_reuseFailAlloc_2191_;
goto v_reusejp_2189_;
}
v_reusejp_2189_:
{
return v___x_2190_;
}
}
}
}
else
{
lean_dec(v_a_2175_);
lean_dec(v_snd_2173_);
lean_dec(v_fst_2172_);
lean_dec(v_fst_2170_);
v___y_2089_ = v_isEq_2160_;
v_isHEq_2090_ = v___x_1815_;
v___y_2091_ = v___y_2161_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
v___y_2094_ = v___y_2164_;
goto v___jp_2088_;
}
}
else
{
lean_object* v_a_2193_; lean_object* v___x_2195_; uint8_t v_isShared_2196_; uint8_t v_isSharedCheck_2200_; 
lean_dec(v_snd_2173_);
lean_dec(v_fst_2172_);
lean_dec(v_fst_2170_);
lean_dec_ref(v___x_1953_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2193_ = lean_ctor_get(v___x_2174_, 0);
v_isSharedCheck_2200_ = !lean_is_exclusive(v___x_2174_);
if (v_isSharedCheck_2200_ == 0)
{
v___x_2195_ = v___x_2174_;
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
else
{
lean_inc(v_a_2193_);
lean_dec(v___x_2174_);
v___x_2195_ = lean_box(0);
v_isShared_2196_ = v_isSharedCheck_2200_;
goto v_resetjp_2194_;
}
v_resetjp_2194_:
{
lean_object* v___x_2198_; 
if (v_isShared_2196_ == 0)
{
v___x_2198_ = v___x_2195_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2199_; 
v_reuseFailAlloc_2199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2199_, 0, v_a_2193_);
v___x_2198_ = v_reuseFailAlloc_2199_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
return v___x_2198_;
}
}
}
}
else
{
lean_dec(v_a_2166_);
v___y_2089_ = v_isEq_2160_;
v_isHEq_2090_ = v___x_1909_;
v___y_2091_ = v___y_2161_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
v___y_2094_ = v___y_2164_;
goto v___jp_2088_;
}
}
else
{
lean_object* v_a_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2208_; 
lean_dec_ref(v___x_1953_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2201_ = lean_ctor_get(v___x_2165_, 0);
v_isSharedCheck_2208_ = !lean_is_exclusive(v___x_2165_);
if (v_isSharedCheck_2208_ == 0)
{
v___x_2203_ = v___x_2165_;
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_a_2201_);
lean_dec(v___x_2165_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2208_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2206_; 
if (v_isShared_2204_ == 0)
{
v___x_2206_ = v___x_2203_;
goto v_reusejp_2205_;
}
else
{
lean_object* v_reuseFailAlloc_2207_; 
v_reuseFailAlloc_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2207_, 0, v_a_2201_);
v___x_2206_ = v_reuseFailAlloc_2207_;
goto v_reusejp_2205_;
}
v_reusejp_2205_:
{
return v___x_2206_;
}
}
}
}
v___jp_2209_:
{
lean_object* v___x_2214_; 
lean_inc_ref(v___x_1953_);
v___x_2214_ = l_Lean_Meta_matchEq_x3f(v___x_1953_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
if (lean_obj_tag(v___x_2214_) == 0)
{
lean_object* v_a_2215_; 
v_a_2215_ = lean_ctor_get(v___x_2214_, 0);
lean_inc(v_a_2215_);
lean_dec_ref_known(v___x_2214_, 1);
if (lean_obj_tag(v_a_2215_) == 1)
{
lean_object* v_val_2216_; lean_object* v_snd_2217_; lean_object* v_fst_2218_; lean_object* v_snd_2219_; lean_object* v___x_2220_; 
v_val_2216_ = lean_ctor_get(v_a_2215_, 0);
lean_inc(v_val_2216_);
lean_dec_ref_known(v_a_2215_, 1);
v_snd_2217_ = lean_ctor_get(v_val_2216_, 1);
lean_inc(v_snd_2217_);
lean_dec(v_val_2216_);
v_fst_2218_ = lean_ctor_get(v_snd_2217_, 0);
lean_inc(v_fst_2218_);
v_snd_2219_ = lean_ctor_get(v_snd_2217_, 1);
lean_inc(v_snd_2219_);
lean_dec(v_snd_2217_);
v___x_2220_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2218_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v_a_2221_; 
v_a_2221_ = lean_ctor_get(v___x_2220_, 0);
lean_inc(v_a_2221_);
lean_dec_ref_known(v___x_2220_, 1);
if (lean_obj_tag(v_a_2221_) == 1)
{
lean_object* v_val_2222_; lean_object* v___x_2223_; 
v_val_2222_ = lean_ctor_get(v_a_2221_, 0);
lean_inc(v_val_2222_);
lean_dec_ref_known(v_a_2221_, 1);
v___x_2223_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2219_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_);
if (lean_obj_tag(v___x_2223_) == 0)
{
lean_object* v_a_2224_; 
v_a_2224_ = lean_ctor_get(v___x_2223_, 0);
lean_inc(v_a_2224_);
lean_dec_ref_known(v___x_2223_, 1);
if (lean_obj_tag(v_a_2224_) == 1)
{
lean_object* v_toConstantVal_2225_; lean_object* v_val_2226_; lean_object* v_toConstantVal_2227_; lean_object* v_name_2228_; lean_object* v_name_2229_; uint8_t v___x_2230_; 
v_toConstantVal_2225_ = lean_ctor_get(v_val_2222_, 0);
lean_inc_ref(v_toConstantVal_2225_);
lean_dec(v_val_2222_);
v_val_2226_ = lean_ctor_get(v_a_2224_, 0);
lean_inc(v_val_2226_);
lean_dec_ref_known(v_a_2224_, 1);
v_toConstantVal_2227_ = lean_ctor_get(v_val_2226_, 0);
lean_inc_ref(v_toConstantVal_2227_);
lean_dec(v_val_2226_);
v_name_2228_ = lean_ctor_get(v_toConstantVal_2225_, 0);
lean_inc(v_name_2228_);
lean_dec_ref(v_toConstantVal_2225_);
v_name_2229_ = lean_ctor_get(v_toConstantVal_2227_, 0);
lean_inc(v_name_2229_);
lean_dec_ref(v_toConstantVal_2227_);
v___x_2230_ = lean_name_eq(v_name_2228_, v_name_2229_);
lean_dec(v_name_2229_);
lean_dec(v_name_2228_);
if (v___x_2230_ == 0)
{
lean_dec_ref(v___x_1953_);
lean_dec_ref(v_config_1804_);
v___y_1842_ = v___y_2213_;
v___y_1843_ = v___y_2212_;
v___y_1844_ = v___y_2211_;
v___y_1845_ = v___y_2210_;
goto v___jp_1841_;
}
else
{
if (v___x_1909_ == 0)
{
lean_del_object(v___x_1838_);
v_isEq_2160_ = v___x_1815_;
v___y_2161_ = v___y_2210_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
v___y_2164_ = v___y_2213_;
goto v___jp_2159_;
}
else
{
lean_dec_ref(v___x_1953_);
lean_dec_ref(v_config_1804_);
v___y_1842_ = v___y_2213_;
v___y_1843_ = v___y_2212_;
v___y_1844_ = v___y_2211_;
v___y_1845_ = v___y_2210_;
goto v___jp_1841_;
}
}
}
else
{
lean_dec(v_a_2224_);
lean_dec(v_val_2222_);
lean_del_object(v___x_1838_);
v_isEq_2160_ = v___x_1815_;
v___y_2161_ = v___y_2210_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
v___y_2164_ = v___y_2213_;
goto v___jp_2159_;
}
}
else
{
lean_object* v_a_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2238_; 
lean_dec(v_val_2222_);
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2231_ = lean_ctor_get(v___x_2223_, 0);
v_isSharedCheck_2238_ = !lean_is_exclusive(v___x_2223_);
if (v_isSharedCheck_2238_ == 0)
{
v___x_2233_ = v___x_2223_;
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_a_2231_);
lean_dec(v___x_2223_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2238_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2234_ == 0)
{
v___x_2236_ = v___x_2233_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_a_2231_);
v___x_2236_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
return v___x_2236_;
}
}
}
}
else
{
lean_dec(v_a_2221_);
lean_dec(v_snd_2219_);
lean_del_object(v___x_1838_);
v_isEq_2160_ = v___x_1815_;
v___y_2161_ = v___y_2210_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
v___y_2164_ = v___y_2213_;
goto v___jp_2159_;
}
}
else
{
lean_object* v_a_2239_; lean_object* v___x_2241_; uint8_t v_isShared_2242_; uint8_t v_isSharedCheck_2246_; 
lean_dec(v_snd_2219_);
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2239_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2246_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2246_ == 0)
{
v___x_2241_ = v___x_2220_;
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
else
{
lean_inc(v_a_2239_);
lean_dec(v___x_2220_);
v___x_2241_ = lean_box(0);
v_isShared_2242_ = v_isSharedCheck_2246_;
goto v_resetjp_2240_;
}
v_resetjp_2240_:
{
lean_object* v___x_2244_; 
if (v_isShared_2242_ == 0)
{
v___x_2244_ = v___x_2241_;
goto v_reusejp_2243_;
}
else
{
lean_object* v_reuseFailAlloc_2245_; 
v_reuseFailAlloc_2245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_a_2239_);
v___x_2244_ = v_reuseFailAlloc_2245_;
goto v_reusejp_2243_;
}
v_reusejp_2243_:
{
return v___x_2244_;
}
}
}
}
else
{
lean_dec(v_a_2215_);
lean_del_object(v___x_1838_);
v_isEq_2160_ = v___x_1909_;
v___y_2161_ = v___y_2210_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
v___y_2164_ = v___y_2213_;
goto v___jp_2159_;
}
}
else
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2254_; 
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2247_ = lean_ctor_get(v___x_2214_, 0);
v_isSharedCheck_2254_ = !lean_is_exclusive(v___x_2214_);
if (v_isSharedCheck_2254_ == 0)
{
v___x_2249_ = v___x_2214_;
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2214_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2254_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2252_; 
if (v_isShared_2250_ == 0)
{
v___x_2252_ = v___x_2249_;
goto v_reusejp_2251_;
}
else
{
lean_object* v_reuseFailAlloc_2253_; 
v_reuseFailAlloc_2253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2253_, 0, v_a_2247_);
v___x_2252_ = v_reuseFailAlloc_2253_;
goto v_reusejp_2251_;
}
v_reusejp_2251_:
{
return v___x_2252_;
}
}
}
}
v___jp_2255_:
{
lean_object* v___x_2260_; 
lean_inc_ref(v___x_1953_);
v___x_2260_ = l_Lean_refutableHasNotBit_x3f(v___x_1953_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2260_) == 0)
{
lean_object* v_a_2261_; 
v_a_2261_ = lean_ctor_get(v___x_2260_, 0);
lean_inc(v_a_2261_);
lean_dec_ref_known(v___x_2260_, 1);
if (lean_obj_tag(v_a_2261_) == 1)
{
lean_object* v_val_2262_; lean_object* v___x_2264_; uint8_t v_isShared_2265_; uint8_t v_isSharedCheck_2301_; 
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec_ref(v_config_1804_);
v_val_2262_ = lean_ctor_get(v_a_2261_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v_a_2261_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2264_ = v_a_2261_;
v_isShared_2265_ = v_isSharedCheck_2301_;
goto v_resetjp_2263_;
}
else
{
lean_inc(v_val_2262_);
lean_dec(v_a_2261_);
v___x_2264_ = lean_box(0);
v_isShared_2265_ = v_isSharedCheck_2301_;
goto v_resetjp_2263_;
}
v_resetjp_2263_:
{
lean_object* v___x_2266_; 
lean_inc(v_mvarId_1805_);
v___x_2266_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_object* v_a_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
lean_inc(v_a_2267_);
lean_dec_ref_known(v___x_2266_, 1);
v___x_2268_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_2269_ = l_Lean_Meta_mkAbsurd(v_a_2267_, v_val_2262_, v___x_2268_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2269_) == 0)
{
lean_object* v_a_2270_; lean_object* v___x_2271_; 
v_a_2270_ = lean_ctor_get(v___x_2269_, 0);
lean_inc(v_a_2270_);
lean_dec_ref_known(v___x_2269_, 1);
v___x_2271_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_2270_, v___y_2257_);
if (lean_obj_tag(v___x_2271_) == 0)
{
lean_object* v___x_2272_; lean_object* v___x_2274_; 
lean_dec_ref_known(v___x_2271_, 1);
v___x_2272_ = lean_box(v___x_1815_);
if (v_isShared_2265_ == 0)
{
lean_ctor_set(v___x_2264_, 0, v___x_2272_);
v___x_2274_ = v___x_2264_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v___x_2272_);
v___x_2274_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
lean_object* v___x_2275_; 
v___x_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2275_, 0, v___x_2274_);
lean_ctor_set(v___x_2275_, 1, v___x_1840_);
v_a_1822_ = v___x_2275_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_del_object(v___x_2264_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_2277_ = lean_ctor_get(v___x_2271_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2271_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2271_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2271_);
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
lean_del_object(v___x_2264_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2285_ = lean_ctor_get(v___x_2269_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2269_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2269_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2269_);
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
lean_del_object(v___x_2264_);
lean_dec(v_val_2262_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2293_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2295_ = v___x_2266_;
v_isShared_2296_ = v_isSharedCheck_2300_;
goto v_resetjp_2294_;
}
else
{
lean_inc(v_a_2293_);
lean_dec(v___x_2266_);
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
}
else
{
lean_object* v___x_2302_; 
lean_dec(v_a_2261_);
lean_inc_ref(v___x_1953_);
v___x_2302_ = l_Lean_Meta_matchNe_x3f(v___x_1953_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2302_) == 0)
{
lean_object* v_a_2303_; 
v_a_2303_ = lean_ctor_get(v___x_2302_, 0);
lean_inc(v_a_2303_);
lean_dec_ref_known(v___x_2302_, 1);
if (lean_obj_tag(v_a_2303_) == 1)
{
lean_object* v_val_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2373_; 
v_val_2304_ = lean_ctor_get(v_a_2303_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_a_2303_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2306_ = v_a_2303_;
v_isShared_2307_ = v_isSharedCheck_2373_;
goto v_resetjp_2305_;
}
else
{
lean_inc(v_val_2304_);
lean_dec(v_a_2303_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2373_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v_snd_2308_; lean_object* v_fst_2309_; lean_object* v_snd_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2372_; 
v_snd_2308_ = lean_ctor_get(v_val_2304_, 1);
lean_inc(v_snd_2308_);
lean_dec(v_val_2304_);
v_fst_2309_ = lean_ctor_get(v_snd_2308_, 0);
v_snd_2310_ = lean_ctor_get(v_snd_2308_, 1);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_snd_2308_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2312_ = v_snd_2308_;
v_isShared_2313_ = v_isSharedCheck_2372_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_snd_2310_);
lean_inc(v_fst_2309_);
lean_dec(v_snd_2308_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2372_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2314_; 
lean_inc(v_fst_2309_);
v___x_2314_ = l_Lean_Meta_isExprDefEq(v_fst_2309_, v_snd_2310_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2314_) == 0)
{
lean_object* v_a_2315_; uint8_t v___x_2316_; 
v_a_2315_ = lean_ctor_get(v___x_2314_, 0);
lean_inc(v_a_2315_);
lean_dec_ref_known(v___x_2314_, 1);
v___x_2316_ = lean_unbox(v_a_2315_);
lean_dec(v_a_2315_);
if (v___x_2316_ == 0)
{
lean_del_object(v___x_2312_);
lean_dec(v_fst_2309_);
lean_del_object(v___x_2306_);
v___y_2210_ = v___y_2256_;
v___y_2211_ = v___y_2257_;
v___y_2212_ = v___y_2258_;
v___y_2213_ = v___y_2259_;
goto v___jp_2209_;
}
else
{
lean_object* v___x_2317_; 
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec_ref(v_config_1804_);
lean_inc(v_mvarId_1805_);
v___x_2317_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v___x_2319_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
lean_inc(v_a_2318_);
lean_dec_ref_known(v___x_2317_, 1);
v___x_2319_ = l_Lean_Meta_mkEqRefl(v_fst_2309_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2319_) == 0)
{
lean_object* v_a_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; 
v_a_2320_ = lean_ctor_get(v___x_2319_, 0);
lean_inc(v_a_2320_);
lean_dec_ref_known(v___x_2319_, 1);
v___x_2321_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_2322_ = l_Lean_Meta_mkAbsurd(v_a_2318_, v_a_2320_, v___x_2321_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; lean_object* v___x_2324_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
v___x_2324_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_2323_, v___y_2257_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v___x_2325_; lean_object* v___x_2327_; 
lean_dec_ref_known(v___x_2324_, 1);
v___x_2325_ = lean_box(v___x_1815_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 0, v___x_2325_);
v___x_2327_ = v___x_2306_;
goto v_reusejp_2326_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2325_);
v___x_2327_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2326_;
}
v_reusejp_2326_:
{
lean_object* v___x_2329_; 
if (v_isShared_2313_ == 0)
{
lean_ctor_set(v___x_2312_, 1, v___x_1840_);
lean_ctor_set(v___x_2312_, 0, v___x_2327_);
v___x_2329_ = v___x_2312_;
goto v_reusejp_2328_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2327_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v___x_1840_);
v___x_2329_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2328_;
}
v_reusejp_2328_:
{
v_a_1822_ = v___x_2329_;
goto v___jp_1821_;
}
}
}
else
{
lean_object* v_a_2332_; lean_object* v___x_2334_; uint8_t v_isShared_2335_; uint8_t v_isSharedCheck_2339_; 
lean_del_object(v___x_2312_);
lean_del_object(v___x_2306_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_2332_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2334_ = v___x_2324_;
v_isShared_2335_ = v_isSharedCheck_2339_;
goto v_resetjp_2333_;
}
else
{
lean_inc(v_a_2332_);
lean_dec(v___x_2324_);
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
else
{
lean_object* v_a_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
lean_del_object(v___x_2312_);
lean_del_object(v___x_2306_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2340_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2322_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_a_2340_);
lean_dec(v___x_2322_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_a_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_dec(v_a_2318_);
lean_del_object(v___x_2312_);
lean_del_object(v___x_2306_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2348_ = lean_ctor_get(v___x_2319_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___x_2319_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___x_2319_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___x_2319_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
else
{
lean_object* v_a_2356_; lean_object* v___x_2358_; uint8_t v_isShared_2359_; uint8_t v_isSharedCheck_2363_; 
lean_del_object(v___x_2312_);
lean_dec(v_fst_2309_);
lean_del_object(v___x_2306_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_2356_ = lean_ctor_get(v___x_2317_, 0);
v_isSharedCheck_2363_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2363_ == 0)
{
v___x_2358_ = v___x_2317_;
v_isShared_2359_ = v_isSharedCheck_2363_;
goto v_resetjp_2357_;
}
else
{
lean_inc(v_a_2356_);
lean_dec(v___x_2317_);
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
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_del_object(v___x_2312_);
lean_dec(v_fst_2309_);
lean_del_object(v___x_2306_);
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2364_ = lean_ctor_get(v___x_2314_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2314_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2314_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2314_);
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
}
}
else
{
lean_dec(v_a_2303_);
v___y_2210_ = v___y_2256_;
v___y_2211_ = v___y_2257_;
v___y_2212_ = v___y_2258_;
v___y_2213_ = v___y_2259_;
goto v___jp_2209_;
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2374_ = lean_ctor_get(v___x_2302_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2302_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2302_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2302_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v___x_1953_);
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_2382_ = lean_ctor_get(v___x_2260_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2260_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2260_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2260_);
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
}
else
{
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_1830_ = v___x_1881_;
goto v___jp_1829_;
}
v___jp_1841_:
{
lean_object* v___x_1846_; 
lean_inc(v_mvarId_1805_);
v___x_1846_ = l_Lean_MVarId_getType(v_mvarId_1805_, v___y_1845_, v___y_1844_, v___y_1843_, v___y_1842_);
if (lean_obj_tag(v___x_1846_) == 0)
{
lean_object* v_a_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v_a_1847_ = lean_ctor_get(v___x_1846_, 0);
lean_inc(v_a_1847_);
lean_dec_ref_known(v___x_1846_, 1);
v___x_1848_ = l_Lean_LocalDecl_toExpr(v_val_1836_);
v___x_1849_ = l_Lean_Meta_mkNoConfusion(v_a_1847_, v___x_1848_, v___y_1845_, v___y_1844_, v___y_1843_, v___y_1842_);
if (lean_obj_tag(v___x_1849_) == 0)
{
lean_object* v_a_1850_; lean_object* v___x_1851_; 
v_a_1850_ = lean_ctor_get(v___x_1849_, 0);
lean_inc(v_a_1850_);
lean_dec_ref_known(v___x_1849_, 1);
v___x_1851_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1805_, v_a_1850_, v___y_1844_);
if (lean_obj_tag(v___x_1851_) == 0)
{
lean_object* v___x_1852_; lean_object* v___x_1854_; 
lean_dec_ref_known(v___x_1851_, 1);
v___x_1852_ = lean_box(v___x_1815_);
if (v_isShared_1839_ == 0)
{
lean_ctor_set(v___x_1838_, 0, v___x_1852_);
v___x_1854_ = v___x_1838_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v___x_1852_);
v___x_1854_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; 
v___x_1855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1855_, 0, v___x_1854_);
lean_ctor_set(v___x_1855_, 1, v___x_1840_);
v_a_1822_ = v___x_1855_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_del_object(v___x_1838_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_1857_ = lean_ctor_get(v___x_1851_, 0);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1851_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1851_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_dec(v___x_1851_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_del_object(v___x_1838_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_1865_ = lean_ctor_get(v___x_1849_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1849_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1849_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1849_);
v___x_1867_ = lean_box(0);
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
v_resetjp_1866_:
{
lean_object* v___x_1870_; 
if (v_isShared_1868_ == 0)
{
v___x_1870_ = v___x_1867_;
goto v_reusejp_1869_;
}
else
{
lean_object* v_reuseFailAlloc_1871_; 
v_reuseFailAlloc_1871_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1871_, 0, v_a_1865_);
v___x_1870_ = v_reuseFailAlloc_1871_;
goto v_reusejp_1869_;
}
v_reusejp_1869_:
{
return v___x_1870_;
}
}
}
}
else
{
lean_object* v_a_1873_; lean_object* v___x_1875_; uint8_t v_isShared_1876_; uint8_t v_isSharedCheck_1880_; 
lean_del_object(v___x_1838_);
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
v_a_1873_ = lean_ctor_get(v___x_1846_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1846_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1846_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1846_);
v___x_1875_ = lean_box(0);
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
v_resetjp_1874_:
{
lean_object* v___x_1878_; 
if (v_isShared_1876_ == 0)
{
v___x_1878_ = v___x_1875_;
goto v_reusejp_1877_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_a_1873_);
v___x_1878_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1877_;
}
v_reusejp_1877_:
{
return v___x_1878_;
}
}
}
}
v___jp_1882_:
{
lean_object* v_searchFuel_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; 
v_searchFuel_1887_ = lean_ctor_get(v_config_1804_, 0);
v___x_1888_ = l_Lean_LocalDecl_fvarId(v_val_1836_);
lean_dec(v_val_1836_);
lean_inc(v_searchFuel_1887_);
lean_inc(v_mvarId_1805_);
v___x_1889_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1805_, v___x_1888_, v_searchFuel_1887_, v___y_1886_, v___y_1885_, v___y_1884_, v___y_1883_);
if (lean_obj_tag(v___x_1889_) == 0)
{
lean_object* v_a_1890_; uint8_t v___x_1891_; 
v_a_1890_ = lean_ctor_get(v___x_1889_, 0);
lean_inc(v_a_1890_);
lean_dec_ref_known(v___x_1889_, 1);
v___x_1891_ = lean_unbox(v_a_1890_);
lean_dec(v_a_1890_);
if (v___x_1891_ == 0)
{
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_1830_ = v___x_1881_;
goto v___jp_1829_;
}
else
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v___x_1892_ = lean_box(v___x_1815_);
v___x_1893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
v___x_1894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
lean_ctor_set(v___x_1894_, 1, v___x_1840_);
v_a_1822_ = v___x_1894_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_1895_; lean_object* v___x_1897_; uint8_t v_isShared_1898_; uint8_t v_isSharedCheck_1902_; 
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_1895_ = lean_ctor_get(v___x_1889_, 0);
v_isSharedCheck_1902_ = !lean_is_exclusive(v___x_1889_);
if (v_isSharedCheck_1902_ == 0)
{
v___x_1897_ = v___x_1889_;
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
else
{
lean_inc(v_a_1895_);
lean_dec(v___x_1889_);
v___x_1897_ = lean_box(0);
v_isShared_1898_ = v_isSharedCheck_1902_;
goto v_resetjp_1896_;
}
v_resetjp_1896_:
{
lean_object* v___x_1900_; 
if (v_isShared_1898_ == 0)
{
v___x_1900_ = v___x_1897_;
goto v_reusejp_1899_;
}
else
{
lean_object* v_reuseFailAlloc_1901_; 
v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1895_);
v___x_1900_ = v_reuseFailAlloc_1901_;
goto v_reusejp_1899_;
}
v_reusejp_1899_:
{
return v___x_1900_;
}
}
}
}
v___jp_1903_:
{
if (v___y_1908_ == 0)
{
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
v_a_1830_ = v___x_1881_;
goto v___jp_1829_;
}
else
{
v___y_1883_ = v___y_1905_;
v___y_1884_ = v___y_1904_;
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___y_1907_;
goto v___jp_1882_;
}
}
v___jp_1910_:
{
if (v___y_1913_ == 0)
{
v___y_1883_ = v___y_1912_;
v___y_1884_ = v___y_1911_;
v___y_1885_ = v___y_1914_;
v___y_1886_ = v___y_1915_;
goto v___jp_1882_;
}
else
{
v___y_1904_ = v___y_1911_;
v___y_1905_ = v___y_1912_;
v___y_1906_ = v___y_1914_;
v___y_1907_ = v___y_1915_;
v___y_1908_ = v___x_1909_;
goto v___jp_1903_;
}
}
v___jp_1916_:
{
if (v___y_1922_ == 0)
{
v___y_1904_ = v___y_1918_;
v___y_1905_ = v___y_1917_;
v___y_1906_ = v___y_1920_;
v___y_1907_ = v___y_1921_;
v___y_1908_ = v___x_1909_;
goto v___jp_1903_;
}
else
{
v___y_1911_ = v___y_1918_;
v___y_1912_ = v___y_1917_;
v___y_1913_ = v___y_1919_;
v___y_1914_ = v___y_1920_;
v___y_1915_ = v___y_1921_;
goto v___jp_1910_;
}
}
v___jp_1923_:
{
uint8_t v_emptyType_1930_; 
v_emptyType_1930_ = lean_ctor_get_uint8(v_config_1804_, sizeof(void*)*1 + 1);
if (v_emptyType_1930_ == 0)
{
v___y_1917_ = v___y_1929_;
v___y_1918_ = v___y_1928_;
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___y_1927_;
v___y_1921_ = v___y_1926_;
v___y_1922_ = v___x_1909_;
goto v___jp_1916_;
}
else
{
if (v___y_1924_ == 0)
{
v___y_1911_ = v___y_1928_;
v___y_1912_ = v___y_1929_;
v___y_1913_ = v___y_1925_;
v___y_1914_ = v___y_1927_;
v___y_1915_ = v___y_1926_;
goto v___jp_1910_;
}
else
{
v___y_1917_ = v___y_1929_;
v___y_1918_ = v___y_1928_;
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___y_1927_;
v___y_1921_ = v___y_1926_;
v___y_1922_ = v___x_1909_;
goto v___jp_1916_;
}
}
}
v___jp_1931_:
{
if (v___y_1938_ == 0)
{
v___y_1924_ = v___y_1932_;
v___y_1925_ = v___y_1934_;
v___y_1926_ = v___y_1937_;
v___y_1927_ = v___y_1935_;
v___y_1928_ = v___y_1936_;
v___y_1929_ = v___y_1933_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1939_; 
lean_inc(v_val_1836_);
lean_inc(v_mvarId_1805_);
v___x_1939_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1805_, v_val_1836_, v___y_1937_, v___y_1935_, v___y_1936_, v___y_1933_);
if (lean_obj_tag(v___x_1939_) == 0)
{
lean_object* v_a_1940_; uint8_t v___x_1941_; 
v_a_1940_ = lean_ctor_get(v___x_1939_, 0);
lean_inc(v_a_1940_);
lean_dec_ref_known(v___x_1939_, 1);
v___x_1941_ = lean_unbox(v_a_1940_);
lean_dec(v_a_1940_);
if (v___x_1941_ == 0)
{
v___y_1924_ = v___y_1932_;
v___y_1925_ = v___y_1934_;
v___y_1926_ = v___y_1937_;
v___y_1927_ = v___y_1935_;
v___y_1928_ = v___y_1936_;
v___y_1929_ = v___y_1933_;
goto v___jp_1923_;
}
else
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
lean_dec(v_val_1836_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v___x_1942_ = lean_box(v___x_1815_);
v___x_1943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
v___x_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
lean_ctor_set(v___x_1944_, 1, v___x_1840_);
v_a_1822_ = v___x_1944_;
goto v___jp_1821_;
}
}
else
{
lean_object* v_a_1945_; lean_object* v___x_1947_; uint8_t v_isShared_1948_; uint8_t v_isSharedCheck_1952_; 
lean_dec(v_val_1836_);
lean_del_object(v___x_1819_);
lean_dec(v_snd_1817_);
lean_dec(v_mvarId_1805_);
lean_dec_ref(v_config_1804_);
v_a_1945_ = lean_ctor_get(v___x_1939_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1939_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1947_ = v___x_1939_;
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
else
{
lean_inc(v_a_1945_);
lean_dec(v___x_1939_);
v___x_1947_ = lean_box(0);
v_isShared_1948_ = v_isSharedCheck_1952_;
goto v_resetjp_1946_;
}
v_resetjp_1946_:
{
lean_object* v___x_1950_; 
if (v_isShared_1948_ == 0)
{
v___x_1950_ = v___x_1947_;
goto v_reusejp_1949_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_a_1945_);
v___x_1950_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1949_;
}
v_reusejp_1949_:
{
return v___x_1950_;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2456_, lean_object* v_mvarId_2457_, lean_object* v_as_2458_, lean_object* v_sz_2459_, lean_object* v_i_2460_, lean_object* v_b_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_){
_start:
{
size_t v_sz_boxed_2467_; size_t v_i_boxed_2468_; lean_object* v_res_2469_; 
v_sz_boxed_2467_ = lean_unbox_usize(v_sz_2459_);
lean_dec(v_sz_2459_);
v_i_boxed_2468_ = lean_unbox_usize(v_i_2460_);
lean_dec(v_i_2460_);
v_res_2469_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2456_, v_mvarId_2457_, v_as_2458_, v_sz_boxed_2467_, v_i_boxed_2468_, v_b_2461_, v___y_2462_, v___y_2463_, v___y_2464_, v___y_2465_);
lean_dec(v___y_2465_);
lean_dec_ref(v___y_2464_);
lean_dec(v___y_2463_);
lean_dec_ref(v___y_2462_);
lean_dec_ref(v_as_2458_);
return v_res_2469_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2470_, lean_object* v_mvarId_2471_, lean_object* v_as_2472_, size_t v_sz_2473_, size_t v_i_2474_, lean_object* v_b_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_){
_start:
{
uint8_t v___x_2481_; 
v___x_2481_ = lean_usize_dec_lt(v_i_2474_, v_sz_2473_);
if (v___x_2481_ == 0)
{
lean_object* v___x_2482_; 
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v___x_2482_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2482_, 0, v_b_2475_);
return v___x_2482_;
}
else
{
lean_object* v_snd_2483_; lean_object* v___x_2485_; uint8_t v_isShared_2486_; uint8_t v_isSharedCheck_3120_; 
v_snd_2483_ = lean_ctor_get(v_b_2475_, 1);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_b_2475_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; 
v_unused_3121_ = lean_ctor_get(v_b_2475_, 0);
lean_dec(v_unused_3121_);
v___x_2485_ = v_b_2475_;
v_isShared_2486_ = v_isSharedCheck_3120_;
goto v_resetjp_2484_;
}
else
{
lean_inc(v_snd_2483_);
lean_dec(v_b_2475_);
v___x_2485_ = lean_box(0);
v_isShared_2486_ = v_isSharedCheck_3120_;
goto v_resetjp_2484_;
}
v_resetjp_2484_:
{
lean_object* v_a_2488_; lean_object* v___x_2494_; lean_object* v_a_2496_; lean_object* v_a_2501_; 
v___x_2494_ = lean_box(0);
v_a_2501_ = lean_array_uget(v_as_2472_, v_i_2474_);
if (lean_obj_tag(v_a_2501_) == 0)
{
lean_del_object(v___x_2485_);
v_a_2496_ = v_snd_2483_;
goto v___jp_2495_;
}
else
{
lean_object* v_val_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_3119_; 
v_val_2502_ = lean_ctor_get(v_a_2501_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_a_2501_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_2504_ = v_a_2501_;
v_isShared_2505_ = v_isSharedCheck_3119_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_val_2502_);
lean_dec(v_a_2501_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_3119_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v___x_2506_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___x_2547_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; uint8_t v___y_2574_; uint8_t v___x_2575_; lean_object* v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; uint8_t v___y_2581_; lean_object* v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; uint8_t v___y_2587_; uint8_t v___y_2588_; uint8_t v___y_2590_; uint8_t v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; uint8_t v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; lean_object* v___y_2602_; uint8_t v___y_2603_; uint8_t v___y_2604_; 
v___x_2506_ = lean_box(0);
v___x_2547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2575_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2502_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2619_; uint8_t v___y_2621_; uint8_t v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2630_; uint8_t v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; lean_object* v___y_2634_; uint8_t v___y_2635_; lean_object* v___y_2636_; uint8_t v___y_2637_; uint8_t v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; uint8_t v___y_2645_; lean_object* v_a_2646_; uint8_t v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; uint8_t v___y_2654_; lean_object* v___y_2655_; uint8_t v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; lean_object* v___y_2713_; uint8_t v___y_2714_; lean_object* v___y_2715_; uint8_t v___y_2716_; uint8_t v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; uint8_t v___y_2723_; lean_object* v___y_2724_; uint8_t v___y_2725_; uint8_t v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; lean_object* v___y_2732_; uint8_t v___y_2733_; uint8_t v___y_2734_; uint8_t v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; lean_object* v___y_2750_; uint8_t v___y_2751_; lean_object* v___y_2752_; uint8_t v___y_2753_; uint8_t v___y_2755_; uint8_t v_isHEq_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; uint8_t v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; uint8_t v_isEq_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___x_3056_; 
v___x_2619_ = l_Lean_LocalDecl_type(v_val_2502_);
lean_inc_ref(v___x_2619_);
v___x_3056_ = l_Lean_Meta_matchNot_x3f(v___x_2619_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
if (lean_obj_tag(v___x_3056_) == 0)
{
lean_object* v_a_3057_; 
v_a_3057_ = lean_ctor_get(v___x_3056_, 0);
lean_inc(v_a_3057_);
lean_dec_ref_known(v___x_3056_, 1);
if (lean_obj_tag(v_a_3057_) == 1)
{
lean_object* v_val_3058_; lean_object* v___x_3059_; 
v_val_3058_ = lean_ctor_get(v_a_3057_, 0);
lean_inc(v_val_3058_);
lean_dec_ref_known(v_a_3057_, 1);
v___x_3059_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3058_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
if (lean_obj_tag(v___x_3059_) == 0)
{
lean_object* v_a_3060_; 
v_a_3060_ = lean_ctor_get(v___x_3059_, 0);
lean_inc(v_a_3060_);
lean_dec_ref_known(v___x_3059_, 1);
if (lean_obj_tag(v_a_3060_) == 1)
{
lean_object* v_val_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3102_; 
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec_ref(v_config_2470_);
v_val_3061_ = lean_ctor_get(v_a_3060_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v_a_3060_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3063_ = v_a_3060_;
v_isShared_3064_ = v_isSharedCheck_3102_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_val_3061_);
lean_dec(v_a_3060_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3102_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; 
lean_inc(v_mvarId_2471_);
v___x_3065_ = l_Lean_MVarId_getType(v_mvarId_2471_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
if (lean_obj_tag(v___x_3065_) == 0)
{
lean_object* v_a_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; 
v_a_3066_ = lean_ctor_get(v___x_3065_, 0);
lean_inc(v_a_3066_);
lean_dec_ref_known(v___x_3065_, 1);
v___x_3067_ = l_Lean_LocalDecl_toExpr(v_val_2502_);
v___x_3068_ = l_Lean_mkFVar(v_val_3061_);
v___x_3069_ = l_Lean_Expr_app___override(v___x_3067_, v___x_3068_);
v___x_3070_ = l_Lean_Meta_mkFalseElim(v_a_3066_, v___x_3069_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
if (lean_obj_tag(v___x_3070_) == 0)
{
lean_object* v_a_3071_; lean_object* v___x_3072_; 
v_a_3071_ = lean_ctor_get(v___x_3070_, 0);
lean_inc(v_a_3071_);
lean_dec_ref_known(v___x_3070_, 1);
v___x_3072_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2471_, v_a_3071_, v___y_2477_);
if (lean_obj_tag(v___x_3072_) == 0)
{
lean_object* v___x_3073_; lean_object* v___x_3075_; 
lean_dec_ref_known(v___x_3072_, 1);
v___x_3073_ = lean_box(v___x_2481_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 0, v___x_3073_);
v___x_3075_ = v___x_3063_;
goto v_reusejp_3074_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3073_);
v___x_3075_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3074_;
}
v_reusejp_3074_:
{
lean_object* v___x_3076_; 
v___x_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3076_, 0, v___x_3075_);
lean_ctor_set(v___x_3076_, 1, v___x_2506_);
v_a_2488_ = v___x_3076_;
goto v___jp_2487_;
}
}
else
{
lean_object* v_a_3078_; lean_object* v___x_3080_; uint8_t v_isShared_3081_; uint8_t v_isSharedCheck_3085_; 
lean_del_object(v___x_3063_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
v_a_3078_ = lean_ctor_get(v___x_3072_, 0);
v_isSharedCheck_3085_ = !lean_is_exclusive(v___x_3072_);
if (v_isSharedCheck_3085_ == 0)
{
v___x_3080_ = v___x_3072_;
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
else
{
lean_inc(v_a_3078_);
lean_dec(v___x_3072_);
v___x_3080_ = lean_box(0);
v_isShared_3081_ = v_isSharedCheck_3085_;
goto v_resetjp_3079_;
}
v_resetjp_3079_:
{
lean_object* v___x_3083_; 
if (v_isShared_3081_ == 0)
{
v___x_3083_ = v___x_3080_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3084_; 
v_reuseFailAlloc_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3084_, 0, v_a_3078_);
v___x_3083_ = v_reuseFailAlloc_3084_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
return v___x_3083_;
}
}
}
}
else
{
lean_object* v_a_3086_; lean_object* v___x_3088_; uint8_t v_isShared_3089_; uint8_t v_isSharedCheck_3093_; 
lean_del_object(v___x_3063_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_3086_ = lean_ctor_get(v___x_3070_, 0);
v_isSharedCheck_3093_ = !lean_is_exclusive(v___x_3070_);
if (v_isSharedCheck_3093_ == 0)
{
v___x_3088_ = v___x_3070_;
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
else
{
lean_inc(v_a_3086_);
lean_dec(v___x_3070_);
v___x_3088_ = lean_box(0);
v_isShared_3089_ = v_isSharedCheck_3093_;
goto v_resetjp_3087_;
}
v_resetjp_3087_:
{
lean_object* v___x_3091_; 
if (v_isShared_3089_ == 0)
{
v___x_3091_ = v___x_3088_;
goto v_reusejp_3090_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v_a_3086_);
v___x_3091_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3090_;
}
v_reusejp_3090_:
{
return v___x_3091_;
}
}
}
}
else
{
lean_object* v_a_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3101_; 
lean_del_object(v___x_3063_);
lean_dec(v_val_3061_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_3094_ = lean_ctor_get(v___x_3065_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v___x_3065_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3096_ = v___x_3065_;
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_a_3094_);
lean_dec(v___x_3065_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3101_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3099_; 
if (v_isShared_3097_ == 0)
{
v___x_3099_ = v___x_3096_;
goto v_reusejp_3098_;
}
else
{
lean_object* v_reuseFailAlloc_3100_; 
v_reuseFailAlloc_3100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3100_, 0, v_a_3094_);
v___x_3099_ = v_reuseFailAlloc_3100_;
goto v_reusejp_3098_;
}
v_reusejp_3098_:
{
return v___x_3099_;
}
}
}
}
}
else
{
lean_dec(v_a_3060_);
v___y_2922_ = v___y_2476_;
v___y_2923_ = v___y_2477_;
v___y_2924_ = v___y_2478_;
v___y_2925_ = v___y_2479_;
goto v___jp_2921_;
}
}
else
{
lean_object* v_a_3103_; lean_object* v___x_3105_; uint8_t v_isShared_3106_; uint8_t v_isSharedCheck_3110_; 
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_3103_ = lean_ctor_get(v___x_3059_, 0);
v_isSharedCheck_3110_ = !lean_is_exclusive(v___x_3059_);
if (v_isSharedCheck_3110_ == 0)
{
v___x_3105_ = v___x_3059_;
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
else
{
lean_inc(v_a_3103_);
lean_dec(v___x_3059_);
v___x_3105_ = lean_box(0);
v_isShared_3106_ = v_isSharedCheck_3110_;
goto v_resetjp_3104_;
}
v_resetjp_3104_:
{
lean_object* v___x_3108_; 
if (v_isShared_3106_ == 0)
{
v___x_3108_ = v___x_3105_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3109_; 
v_reuseFailAlloc_3109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3109_, 0, v_a_3103_);
v___x_3108_ = v_reuseFailAlloc_3109_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
return v___x_3108_;
}
}
}
}
else
{
lean_dec(v_a_3057_);
v___y_2922_ = v___y_2476_;
v___y_2923_ = v___y_2477_;
v___y_2924_ = v___y_2478_;
v___y_2925_ = v___y_2479_;
goto v___jp_2921_;
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_3111_ = lean_ctor_get(v___x_3056_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3056_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3056_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3056_);
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
v___jp_2620_:
{
uint8_t v_genDiseq_2627_; 
v_genDiseq_2627_ = lean_ctor_get_uint8(v_config_2470_, sizeof(void*)*1 + 2);
if (v_genDiseq_2627_ == 0)
{
lean_dec_ref(v___x_2619_);
v___y_2598_ = v___y_2621_;
v___y_2599_ = v___y_2626_;
v___y_2600_ = v___y_2623_;
v___y_2601_ = v___y_2624_;
v___y_2602_ = v___y_2625_;
v___y_2603_ = v___y_2622_;
v___y_2604_ = v___x_2575_;
goto v___jp_2597_;
}
else
{
uint8_t v___x_2628_; 
v___x_2628_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2619_);
v___y_2598_ = v___y_2621_;
v___y_2599_ = v___y_2626_;
v___y_2600_ = v___y_2623_;
v___y_2601_ = v___y_2624_;
v___y_2602_ = v___y_2625_;
v___y_2603_ = v___y_2622_;
v___y_2604_ = v___x_2628_;
goto v___jp_2597_;
}
}
v___jp_2629_:
{
if (v___y_2637_ == 0)
{
lean_dec_ref(v___y_2630_);
v___y_2621_ = v___y_2631_;
v___y_2622_ = v___y_2635_;
v___y_2623_ = v___y_2634_;
v___y_2624_ = v___y_2633_;
v___y_2625_ = v___y_2632_;
v___y_2626_ = v___y_2636_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2638_; 
lean_dec_ref(v___x_2619_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v___x_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2638_, 0, v___y_2630_);
return v___x_2638_;
}
}
v___jp_2639_:
{
uint8_t v___x_2647_; 
v___x_2647_ = l_Lean_Exception_isInterrupt(v_a_2646_);
if (v___x_2647_ == 0)
{
uint8_t v___x_2648_; 
lean_inc_ref(v_a_2646_);
v___x_2648_ = l_Lean_Exception_isRuntime(v_a_2646_);
v___y_2630_ = v_a_2646_;
v___y_2631_ = v___y_2640_;
v___y_2632_ = v___y_2642_;
v___y_2633_ = v___y_2641_;
v___y_2634_ = v___y_2643_;
v___y_2635_ = v___y_2645_;
v___y_2636_ = v___y_2644_;
v___y_2637_ = v___x_2648_;
goto v___jp_2629_;
}
else
{
v___y_2630_ = v_a_2646_;
v___y_2631_ = v___y_2640_;
v___y_2632_ = v___y_2642_;
v___y_2633_ = v___y_2641_;
v___y_2634_ = v___y_2643_;
v___y_2635_ = v___y_2645_;
v___y_2636_ = v___y_2644_;
v___y_2637_ = v___x_2647_;
goto v___jp_2629_;
}
}
v___jp_2649_:
{
lean_object* v___x_2656_; 
lean_inc_ref(v___x_2619_);
v___x_2656_ = l_Lean_Meta_mkDecide(v___x_2619_, v___y_2653_, v___y_2652_, v___y_2651_, v___y_2655_);
if (lean_obj_tag(v___x_2656_) == 0)
{
lean_object* v_a_2657_; lean_object* v_keyedConfig_2658_; uint8_t v_trackZetaDelta_2659_; lean_object* v_zetaDeltaSet_2660_; lean_object* v_lctx_2661_; lean_object* v_localInstances_2662_; lean_object* v_defEqCtx_x3f_2663_; lean_object* v_synthPendingDepth_2664_; lean_object* v_customCanUnfoldPredicate_x3f_2665_; uint8_t v_univApprox_2666_; uint8_t v_inTypeClassResolution_2667_; uint8_t v_cacheInferType_2668_; uint8_t v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; 
v_a_2657_ = lean_ctor_get(v___x_2656_, 0);
lean_inc_n(v_a_2657_, 2);
lean_dec_ref_known(v___x_2656_, 1);
v_keyedConfig_2658_ = lean_ctor_get(v___y_2653_, 0);
v_trackZetaDelta_2659_ = lean_ctor_get_uint8(v___y_2653_, sizeof(void*)*7);
v_zetaDeltaSet_2660_ = lean_ctor_get(v___y_2653_, 1);
v_lctx_2661_ = lean_ctor_get(v___y_2653_, 2);
v_localInstances_2662_ = lean_ctor_get(v___y_2653_, 3);
v_defEqCtx_x3f_2663_ = lean_ctor_get(v___y_2653_, 4);
v_synthPendingDepth_2664_ = lean_ctor_get(v___y_2653_, 5);
v_customCanUnfoldPredicate_x3f_2665_ = lean_ctor_get(v___y_2653_, 6);
v_univApprox_2666_ = lean_ctor_get_uint8(v___y_2653_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2667_ = lean_ctor_get_uint8(v___y_2653_, sizeof(void*)*7 + 2);
v_cacheInferType_2668_ = lean_ctor_get_uint8(v___y_2653_, sizeof(void*)*7 + 3);
v___x_2669_ = 1;
lean_inc_ref(v_keyedConfig_2658_);
v___x_2670_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2669_, v_keyedConfig_2658_);
lean_inc(v_customCanUnfoldPredicate_x3f_2665_);
lean_inc(v_synthPendingDepth_2664_);
lean_inc(v_defEqCtx_x3f_2663_);
lean_inc_ref(v_localInstances_2662_);
lean_inc_ref(v_lctx_2661_);
lean_inc(v_zetaDeltaSet_2660_);
v___x_2671_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2671_, 0, v___x_2670_);
lean_ctor_set(v___x_2671_, 1, v_zetaDeltaSet_2660_);
lean_ctor_set(v___x_2671_, 2, v_lctx_2661_);
lean_ctor_set(v___x_2671_, 3, v_localInstances_2662_);
lean_ctor_set(v___x_2671_, 4, v_defEqCtx_x3f_2663_);
lean_ctor_set(v___x_2671_, 5, v_synthPendingDepth_2664_);
lean_ctor_set(v___x_2671_, 6, v_customCanUnfoldPredicate_x3f_2665_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7, v_trackZetaDelta_2659_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 1, v_univApprox_2666_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2667_);
lean_ctor_set_uint8(v___x_2671_, sizeof(void*)*7 + 3, v_cacheInferType_2668_);
lean_inc(v___y_2655_);
lean_inc_ref(v___y_2651_);
lean_inc(v___y_2652_);
v___x_2672_ = lean_whnf(v_a_2657_, v___x_2671_, v___y_2652_, v___y_2651_, v___y_2655_);
if (lean_obj_tag(v___x_2672_) == 0)
{
lean_object* v_a_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; 
v_a_2673_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2673_);
lean_dec_ref_known(v___x_2672_, 1);
v___x_2674_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2675_ = l_Lean_Expr_isConstOf(v_a_2673_, v___x_2674_);
lean_dec(v_a_2673_);
if (v___x_2675_ == 0)
{
lean_dec(v_a_2657_);
v___y_2621_ = v___y_2650_;
v___y_2622_ = v___y_2654_;
v___y_2623_ = v___y_2653_;
v___y_2624_ = v___y_2652_;
v___y_2625_ = v___y_2651_;
v___y_2626_ = v___y_2655_;
goto v___jp_2620_;
}
else
{
lean_object* v___x_2676_; 
lean_inc(v_a_2657_);
v___x_2676_ = l_Lean_Meta_mkEqRefl(v_a_2657_, v___y_2653_, v___y_2652_, v___y_2651_, v___y_2655_);
if (lean_obj_tag(v___x_2676_) == 0)
{
lean_object* v_a_2677_; lean_object* v___x_2678_; 
v_a_2677_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2677_);
lean_dec_ref_known(v___x_2676_, 1);
lean_inc(v_mvarId_2471_);
v___x_2678_ = l_Lean_MVarId_getType(v_mvarId_2471_, v___y_2653_, v___y_2652_, v___y_2651_, v___y_2655_);
if (lean_obj_tag(v___x_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v_nargs_2680_; lean_object* v___x_2681_; lean_object* v_dummy_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; 
v_a_2679_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___x_2678_, 1);
v_nargs_2680_ = l_Lean_Expr_getAppNumArgs(v_a_2657_);
v___x_2681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2682_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_2680_);
v___x_2683_ = lean_mk_array(v_nargs_2680_, v_dummy_2682_);
v___x_2684_ = lean_unsigned_to_nat(1u);
v___x_2685_ = lean_nat_sub(v_nargs_2680_, v___x_2684_);
lean_dec(v_nargs_2680_);
v___x_2686_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2657_, v___x_2683_, v___x_2685_);
v___x_2687_ = lean_array_push(v___x_2686_, v_a_2677_);
v___x_2688_ = l_Lean_mkAppN(v___x_2681_, v___x_2687_);
lean_dec_ref(v___x_2687_);
lean_inc(v_val_2502_);
v___x_2689_ = l_Lean_LocalDecl_toExpr(v_val_2502_);
v___x_2690_ = l_Lean_Meta_mkAbsurd(v_a_2679_, v___x_2689_, v___x_2688_, v___y_2653_, v___y_2652_, v___y_2651_, v___y_2655_);
if (lean_obj_tag(v___x_2690_) == 0)
{
lean_object* v_a_2691_; lean_object* v___x_2692_; 
v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2691_);
lean_dec_ref_known(v___x_2690_, 1);
lean_inc(v_mvarId_2471_);
v___x_2692_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2471_, v_a_2691_, v___y_2652_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v___x_2694_; uint8_t v_isShared_2695_; uint8_t v_isSharedCheck_2701_; 
lean_dec_ref(v___x_2619_);
lean_dec(v_val_2502_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_isSharedCheck_2701_ = !lean_is_exclusive(v___x_2692_);
if (v_isSharedCheck_2701_ == 0)
{
lean_object* v_unused_2702_; 
v_unused_2702_ = lean_ctor_get(v___x_2692_, 0);
lean_dec(v_unused_2702_);
v___x_2694_ = v___x_2692_;
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
else
{
lean_dec(v___x_2692_);
v___x_2694_ = lean_box(0);
v_isShared_2695_ = v_isSharedCheck_2701_;
goto v_resetjp_2693_;
}
v_resetjp_2693_:
{
lean_object* v___x_2696_; lean_object* v___x_2698_; 
v___x_2696_ = lean_box(v___x_2481_);
if (v_isShared_2695_ == 0)
{
lean_ctor_set_tag(v___x_2694_, 1);
lean_ctor_set(v___x_2694_, 0, v___x_2696_);
v___x_2698_ = v___x_2694_;
goto v_reusejp_2697_;
}
else
{
lean_object* v_reuseFailAlloc_2700_; 
v_reuseFailAlloc_2700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2696_);
v___x_2698_ = v_reuseFailAlloc_2700_;
goto v_reusejp_2697_;
}
v_reusejp_2697_:
{
lean_object* v___x_2699_; 
v___x_2699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2699_, 0, v___x_2698_);
lean_ctor_set(v___x_2699_, 1, v___x_2506_);
v_a_2488_ = v___x_2699_;
goto v___jp_2487_;
}
}
}
else
{
lean_object* v_a_2703_; 
v_a_2703_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2692_, 1);
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2652_;
v___y_2642_ = v___y_2651_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2655_;
v___y_2645_ = v___y_2654_;
v_a_2646_ = v_a_2703_;
goto v___jp_2639_;
}
}
else
{
lean_object* v_a_2704_; 
v_a_2704_ = lean_ctor_get(v___x_2690_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2690_, 1);
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2652_;
v___y_2642_ = v___y_2651_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2655_;
v___y_2645_ = v___y_2654_;
v_a_2646_ = v_a_2704_;
goto v___jp_2639_;
}
}
else
{
lean_object* v_a_2705_; 
lean_dec(v_a_2677_);
lean_dec(v_a_2657_);
v_a_2705_ = lean_ctor_get(v___x_2678_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2678_, 1);
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2652_;
v___y_2642_ = v___y_2651_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2655_;
v___y_2645_ = v___y_2654_;
v_a_2646_ = v_a_2705_;
goto v___jp_2639_;
}
}
else
{
lean_object* v_a_2706_; 
lean_dec(v_a_2657_);
v_a_2706_ = lean_ctor_get(v___x_2676_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2676_, 1);
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2652_;
v___y_2642_ = v___y_2651_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2655_;
v___y_2645_ = v___y_2654_;
v_a_2646_ = v_a_2706_;
goto v___jp_2639_;
}
}
}
else
{
lean_object* v_a_2707_; 
lean_dec(v_a_2657_);
v_a_2707_ = lean_ctor_get(v___x_2672_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2672_, 1);
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2652_;
v___y_2642_ = v___y_2651_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2655_;
v___y_2645_ = v___y_2654_;
v_a_2646_ = v_a_2707_;
goto v___jp_2639_;
}
}
else
{
lean_object* v_a_2708_; 
v_a_2708_ = lean_ctor_get(v___x_2656_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2656_, 1);
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2652_;
v___y_2642_ = v___y_2651_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2655_;
v___y_2645_ = v___y_2654_;
v_a_2646_ = v_a_2708_;
goto v___jp_2639_;
}
}
v___jp_2709_:
{
if (v___y_2716_ == 0)
{
v___y_2621_ = v___y_2710_;
v___y_2622_ = v___y_2714_;
v___y_2623_ = v___y_2713_;
v___y_2624_ = v___y_2712_;
v___y_2625_ = v___y_2711_;
v___y_2626_ = v___y_2715_;
goto v___jp_2620_;
}
else
{
v___y_2650_ = v___y_2710_;
v___y_2651_ = v___y_2711_;
v___y_2652_ = v___y_2712_;
v___y_2653_ = v___y_2713_;
v___y_2654_ = v___y_2714_;
v___y_2655_ = v___y_2715_;
goto v___jp_2649_;
}
}
v___jp_2717_:
{
if (v___y_2725_ == 0)
{
lean_dec_ref(v___y_2724_);
v___y_2710_ = v___y_2718_;
v___y_2711_ = v___y_2720_;
v___y_2712_ = v___y_2719_;
v___y_2713_ = v___y_2721_;
v___y_2714_ = v___y_2723_;
v___y_2715_ = v___y_2722_;
v___y_2716_ = v___x_2575_;
goto v___jp_2709_;
}
else
{
uint8_t v___x_2726_; 
v___x_2726_ = l_Lean_Expr_hasFVar(v___y_2724_);
lean_dec_ref(v___y_2724_);
if (v___x_2726_ == 0)
{
v___y_2650_ = v___y_2718_;
v___y_2651_ = v___y_2720_;
v___y_2652_ = v___y_2719_;
v___y_2653_ = v___y_2721_;
v___y_2654_ = v___y_2723_;
v___y_2655_ = v___y_2722_;
goto v___jp_2649_;
}
else
{
v___y_2710_ = v___y_2718_;
v___y_2711_ = v___y_2720_;
v___y_2712_ = v___y_2719_;
v___y_2713_ = v___y_2721_;
v___y_2714_ = v___y_2723_;
v___y_2715_ = v___y_2722_;
v___y_2716_ = v___x_2575_;
goto v___jp_2709_;
}
}
}
v___jp_2727_:
{
lean_object* v___x_2735_; 
lean_inc_ref(v___x_2619_);
v___x_2735_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2619_, v___y_2730_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; uint8_t v___x_2737_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v___x_2737_ = l_Lean_Expr_hasMVar(v_a_2736_);
if (v___x_2737_ == 0)
{
v___y_2718_ = v___y_2728_;
v___y_2719_ = v___y_2730_;
v___y_2720_ = v___y_2729_;
v___y_2721_ = v___y_2731_;
v___y_2722_ = v___y_2732_;
v___y_2723_ = v___y_2733_;
v___y_2724_ = v_a_2736_;
v___y_2725_ = v___y_2734_;
goto v___jp_2717_;
}
else
{
v___y_2718_ = v___y_2728_;
v___y_2719_ = v___y_2730_;
v___y_2720_ = v___y_2729_;
v___y_2721_ = v___y_2731_;
v___y_2722_ = v___y_2732_;
v___y_2723_ = v___y_2733_;
v___y_2724_ = v_a_2736_;
v___y_2725_ = v___x_2575_;
goto v___jp_2717_;
}
}
else
{
lean_object* v_a_2738_; lean_object* v___x_2740_; uint8_t v_isShared_2741_; uint8_t v_isSharedCheck_2745_; 
lean_dec_ref(v___x_2619_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_2738_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2740_ = v___x_2735_;
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
else
{
lean_inc(v_a_2738_);
lean_dec(v___x_2735_);
v___x_2740_ = lean_box(0);
v_isShared_2741_ = v_isSharedCheck_2745_;
goto v_resetjp_2739_;
}
v_resetjp_2739_:
{
lean_object* v___x_2743_; 
if (v_isShared_2741_ == 0)
{
v___x_2743_ = v___x_2740_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v_a_2738_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
}
v___jp_2746_:
{
if (v___y_2753_ == 0)
{
v___y_2621_ = v___y_2747_;
v___y_2622_ = v___y_2751_;
v___y_2623_ = v___y_2750_;
v___y_2624_ = v___y_2749_;
v___y_2625_ = v___y_2748_;
v___y_2626_ = v___y_2752_;
goto v___jp_2620_;
}
else
{
v___y_2728_ = v___y_2747_;
v___y_2729_ = v___y_2748_;
v___y_2730_ = v___y_2749_;
v___y_2731_ = v___y_2750_;
v___y_2732_ = v___y_2752_;
v___y_2733_ = v___y_2751_;
v___y_2734_ = v___y_2753_;
goto v___jp_2727_;
}
}
v___jp_2754_:
{
uint8_t v_useDecide_2761_; 
v_useDecide_2761_ = lean_ctor_get_uint8(v_config_2470_, sizeof(void*)*1);
if (v_useDecide_2761_ == 0)
{
v___y_2747_ = v___y_2755_;
v___y_2748_ = v___y_2759_;
v___y_2749_ = v___y_2758_;
v___y_2750_ = v___y_2757_;
v___y_2751_ = v_isHEq_2756_;
v___y_2752_ = v___y_2760_;
v___y_2753_ = v___x_2575_;
goto v___jp_2746_;
}
else
{
uint8_t v___x_2762_; 
v___x_2762_ = l_Lean_Expr_hasFVar(v___x_2619_);
if (v___x_2762_ == 0)
{
v___y_2728_ = v___y_2755_;
v___y_2729_ = v___y_2759_;
v___y_2730_ = v___y_2758_;
v___y_2731_ = v___y_2757_;
v___y_2732_ = v___y_2760_;
v___y_2733_ = v_isHEq_2756_;
v___y_2734_ = v_useDecide_2761_;
goto v___jp_2727_;
}
else
{
v___y_2747_ = v___y_2755_;
v___y_2748_ = v___y_2759_;
v___y_2749_ = v___y_2758_;
v___y_2750_ = v___y_2757_;
v___y_2751_ = v_isHEq_2756_;
v___y_2752_ = v___y_2760_;
v___y_2753_ = v___x_2575_;
goto v___jp_2746_;
}
}
}
v___jp_2763_:
{
lean_object* v___x_2771_; 
v___x_2771_ = l_Lean_Meta_isExprDefEq(v___y_2765_, v___y_2770_, v___y_2767_, v___y_2766_, v___y_2769_, v___y_2768_);
if (lean_obj_tag(v___x_2771_) == 0)
{
lean_object* v_a_2772_; uint8_t v___x_2773_; 
v_a_2772_ = lean_ctor_get(v___x_2771_, 0);
lean_inc(v_a_2772_);
lean_dec_ref_known(v___x_2771_, 1);
v___x_2773_ = lean_unbox(v_a_2772_);
lean_dec(v_a_2772_);
if (v___x_2773_ == 0)
{
v___y_2755_ = v___y_2764_;
v_isHEq_2756_ = v___x_2481_;
v___y_2757_ = v___y_2767_;
v___y_2758_ = v___y_2766_;
v___y_2759_ = v___y_2769_;
v___y_2760_ = v___y_2768_;
goto v___jp_2754_;
}
else
{
lean_object* v___x_2774_; 
lean_dec_ref(v___x_2619_);
lean_dec_ref(v_config_2470_);
lean_inc(v_mvarId_2471_);
v___x_2774_ = l_Lean_MVarId_getType(v_mvarId_2471_, v___y_2767_, v___y_2766_, v___y_2769_, v___y_2768_);
if (lean_obj_tag(v___x_2774_) == 0)
{
lean_object* v_a_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; 
v_a_2775_ = lean_ctor_get(v___x_2774_, 0);
lean_inc(v_a_2775_);
lean_dec_ref_known(v___x_2774_, 1);
v___x_2776_ = l_Lean_LocalDecl_toExpr(v_val_2502_);
v___x_2777_ = l_Lean_Meta_mkEqOfHEq(v___x_2776_, v___x_2481_, v___y_2767_, v___y_2766_, v___y_2769_, v___y_2768_);
if (lean_obj_tag(v___x_2777_) == 0)
{
lean_object* v_a_2778_; lean_object* v___x_2779_; 
v_a_2778_ = lean_ctor_get(v___x_2777_, 0);
lean_inc(v_a_2778_);
lean_dec_ref_known(v___x_2777_, 1);
v___x_2779_ = l_Lean_Meta_mkNoConfusion(v_a_2775_, v_a_2778_, v___y_2767_, v___y_2766_, v___y_2769_, v___y_2768_);
if (lean_obj_tag(v___x_2779_) == 0)
{
lean_object* v_a_2780_; lean_object* v___x_2781_; 
v_a_2780_ = lean_ctor_get(v___x_2779_, 0);
lean_inc(v_a_2780_);
lean_dec_ref_known(v___x_2779_, 1);
v___x_2781_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2471_, v_a_2780_, v___y_2766_);
if (lean_obj_tag(v___x_2781_) == 0)
{
lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; 
lean_dec_ref_known(v___x_2781_, 1);
v___x_2782_ = lean_box(v___x_2481_);
v___x_2783_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
v___x_2784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
lean_ctor_set(v___x_2784_, 1, v___x_2506_);
v_a_2488_ = v___x_2784_;
goto v___jp_2487_;
}
else
{
lean_object* v_a_2785_; lean_object* v___x_2787_; uint8_t v_isShared_2788_; uint8_t v_isSharedCheck_2792_; 
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
v_a_2785_ = lean_ctor_get(v___x_2781_, 0);
v_isSharedCheck_2792_ = !lean_is_exclusive(v___x_2781_);
if (v_isSharedCheck_2792_ == 0)
{
v___x_2787_ = v___x_2781_;
v_isShared_2788_ = v_isSharedCheck_2792_;
goto v_resetjp_2786_;
}
else
{
lean_inc(v_a_2785_);
lean_dec(v___x_2781_);
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
lean_object* v_a_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2800_; 
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_2793_ = lean_ctor_get(v___x_2779_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2779_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2795_ = v___x_2779_;
v_isShared_2796_ = v_isSharedCheck_2800_;
goto v_resetjp_2794_;
}
else
{
lean_inc(v_a_2793_);
lean_dec(v___x_2779_);
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
else
{
lean_object* v_a_2801_; lean_object* v___x_2803_; uint8_t v_isShared_2804_; uint8_t v_isSharedCheck_2808_; 
lean_dec(v_a_2775_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_2801_ = lean_ctor_get(v___x_2777_, 0);
v_isSharedCheck_2808_ = !lean_is_exclusive(v___x_2777_);
if (v_isSharedCheck_2808_ == 0)
{
v___x_2803_ = v___x_2777_;
v_isShared_2804_ = v_isSharedCheck_2808_;
goto v_resetjp_2802_;
}
else
{
lean_inc(v_a_2801_);
lean_dec(v___x_2777_);
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
else
{
lean_object* v_a_2809_; lean_object* v___x_2811_; uint8_t v_isShared_2812_; uint8_t v_isSharedCheck_2816_; 
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_2809_ = lean_ctor_get(v___x_2774_, 0);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2774_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2811_ = v___x_2774_;
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
else
{
lean_inc(v_a_2809_);
lean_dec(v___x_2774_);
v___x_2811_ = lean_box(0);
v_isShared_2812_ = v_isSharedCheck_2816_;
goto v_resetjp_2810_;
}
v_resetjp_2810_:
{
lean_object* v___x_2814_; 
if (v_isShared_2812_ == 0)
{
v___x_2814_ = v___x_2811_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v___x_2819_; uint8_t v_isShared_2820_; uint8_t v_isSharedCheck_2824_; 
lean_dec_ref(v___x_2619_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_2817_ = lean_ctor_get(v___x_2771_, 0);
v_isSharedCheck_2824_ = !lean_is_exclusive(v___x_2771_);
if (v_isSharedCheck_2824_ == 0)
{
v___x_2819_ = v___x_2771_;
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
else
{
lean_inc(v_a_2817_);
lean_dec(v___x_2771_);
v___x_2819_ = lean_box(0);
v_isShared_2820_ = v_isSharedCheck_2824_;
goto v_resetjp_2818_;
}
v_resetjp_2818_:
{
lean_object* v___x_2822_; 
if (v_isShared_2820_ == 0)
{
v___x_2822_ = v___x_2819_;
goto v_reusejp_2821_;
}
else
{
lean_object* v_reuseFailAlloc_2823_; 
v_reuseFailAlloc_2823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
v___x_2822_ = v_reuseFailAlloc_2823_;
goto v_reusejp_2821_;
}
v_reusejp_2821_:
{
return v___x_2822_;
}
}
}
}
v___jp_2825_:
{
lean_object* v___x_2831_; 
lean_inc_ref(v___x_2619_);
v___x_2831_ = l_Lean_Meta_matchHEq_x3f(v___x_2619_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
if (lean_obj_tag(v___x_2831_) == 0)
{
lean_object* v_a_2832_; 
v_a_2832_ = lean_ctor_get(v___x_2831_, 0);
lean_inc(v_a_2832_);
lean_dec_ref_known(v___x_2831_, 1);
if (lean_obj_tag(v_a_2832_) == 1)
{
lean_object* v_val_2833_; lean_object* v_snd_2834_; lean_object* v_snd_2835_; lean_object* v_fst_2836_; lean_object* v_fst_2837_; lean_object* v_fst_2838_; lean_object* v_snd_2839_; lean_object* v___x_2840_; 
v_val_2833_ = lean_ctor_get(v_a_2832_, 0);
lean_inc(v_val_2833_);
lean_dec_ref_known(v_a_2832_, 1);
v_snd_2834_ = lean_ctor_get(v_val_2833_, 1);
lean_inc(v_snd_2834_);
v_snd_2835_ = lean_ctor_get(v_snd_2834_, 1);
lean_inc(v_snd_2835_);
v_fst_2836_ = lean_ctor_get(v_val_2833_, 0);
lean_inc(v_fst_2836_);
lean_dec(v_val_2833_);
v_fst_2837_ = lean_ctor_get(v_snd_2834_, 0);
lean_inc(v_fst_2837_);
lean_dec(v_snd_2834_);
v_fst_2838_ = lean_ctor_get(v_snd_2835_, 0);
lean_inc(v_fst_2838_);
v_snd_2839_ = lean_ctor_get(v_snd_2835_, 1);
lean_inc(v_snd_2839_);
lean_dec(v_snd_2835_);
v___x_2840_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2837_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
if (lean_obj_tag(v___x_2840_) == 0)
{
lean_object* v_a_2841_; 
v_a_2841_ = lean_ctor_get(v___x_2840_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2840_, 1);
if (lean_obj_tag(v_a_2841_) == 1)
{
lean_object* v_val_2842_; lean_object* v___x_2843_; 
v_val_2842_ = lean_ctor_get(v_a_2841_, 0);
lean_inc(v_val_2842_);
lean_dec_ref_known(v_a_2841_, 1);
v___x_2843_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2839_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
lean_inc(v_a_2844_);
lean_dec_ref_known(v___x_2843_, 1);
if (lean_obj_tag(v_a_2844_) == 1)
{
lean_object* v_toConstantVal_2845_; lean_object* v_val_2846_; lean_object* v_toConstantVal_2847_; lean_object* v_name_2848_; lean_object* v_name_2849_; uint8_t v___x_2850_; 
v_toConstantVal_2845_ = lean_ctor_get(v_val_2842_, 0);
lean_inc_ref(v_toConstantVal_2845_);
lean_dec(v_val_2842_);
v_val_2846_ = lean_ctor_get(v_a_2844_, 0);
lean_inc(v_val_2846_);
lean_dec_ref_known(v_a_2844_, 1);
v_toConstantVal_2847_ = lean_ctor_get(v_val_2846_, 0);
lean_inc_ref(v_toConstantVal_2847_);
lean_dec(v_val_2846_);
v_name_2848_ = lean_ctor_get(v_toConstantVal_2845_, 0);
lean_inc(v_name_2848_);
lean_dec_ref(v_toConstantVal_2845_);
v_name_2849_ = lean_ctor_get(v_toConstantVal_2847_, 0);
lean_inc(v_name_2849_);
lean_dec_ref(v_toConstantVal_2847_);
v___x_2850_ = lean_name_eq(v_name_2848_, v_name_2849_);
lean_dec(v_name_2849_);
lean_dec(v_name_2848_);
if (v___x_2850_ == 0)
{
v___y_2764_ = v_isEq_2826_;
v___y_2765_ = v_fst_2836_;
v___y_2766_ = v___y_2828_;
v___y_2767_ = v___y_2827_;
v___y_2768_ = v___y_2830_;
v___y_2769_ = v___y_2829_;
v___y_2770_ = v_fst_2838_;
goto v___jp_2763_;
}
else
{
if (v___x_2575_ == 0)
{
lean_dec(v_fst_2838_);
lean_dec(v_fst_2836_);
v___y_2755_ = v_isEq_2826_;
v_isHEq_2756_ = v___x_2481_;
v___y_2757_ = v___y_2827_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
v___y_2760_ = v___y_2830_;
goto v___jp_2754_;
}
else
{
v___y_2764_ = v_isEq_2826_;
v___y_2765_ = v_fst_2836_;
v___y_2766_ = v___y_2828_;
v___y_2767_ = v___y_2827_;
v___y_2768_ = v___y_2830_;
v___y_2769_ = v___y_2829_;
v___y_2770_ = v_fst_2838_;
goto v___jp_2763_;
}
}
}
else
{
lean_dec(v_a_2844_);
lean_dec(v_val_2842_);
lean_dec(v_fst_2838_);
lean_dec(v_fst_2836_);
v___y_2755_ = v_isEq_2826_;
v_isHEq_2756_ = v___x_2481_;
v___y_2757_ = v___y_2827_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
v___y_2760_ = v___y_2830_;
goto v___jp_2754_;
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec(v_val_2842_);
lean_dec(v_fst_2838_);
lean_dec(v_fst_2836_);
lean_dec_ref(v___x_2619_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_2851_ = lean_ctor_get(v___x_2843_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2843_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2843_);
v___x_2853_ = lean_box(0);
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
v_resetjp_2852_:
{
lean_object* v___x_2856_; 
if (v_isShared_2854_ == 0)
{
v___x_2856_ = v___x_2853_;
goto v_reusejp_2855_;
}
else
{
lean_object* v_reuseFailAlloc_2857_; 
v_reuseFailAlloc_2857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2857_, 0, v_a_2851_);
v___x_2856_ = v_reuseFailAlloc_2857_;
goto v_reusejp_2855_;
}
v_reusejp_2855_:
{
return v___x_2856_;
}
}
}
}
else
{
lean_dec(v_a_2841_);
lean_dec(v_snd_2839_);
lean_dec(v_fst_2838_);
lean_dec(v_fst_2836_);
v___y_2755_ = v_isEq_2826_;
v_isHEq_2756_ = v___x_2481_;
v___y_2757_ = v___y_2827_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
v___y_2760_ = v___y_2830_;
goto v___jp_2754_;
}
}
else
{
lean_object* v_a_2859_; lean_object* v___x_2861_; uint8_t v_isShared_2862_; uint8_t v_isSharedCheck_2866_; 
lean_dec(v_snd_2839_);
lean_dec(v_fst_2838_);
lean_dec(v_fst_2836_);
lean_dec_ref(v___x_2619_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_2859_ = lean_ctor_get(v___x_2840_, 0);
v_isSharedCheck_2866_ = !lean_is_exclusive(v___x_2840_);
if (v_isSharedCheck_2866_ == 0)
{
v___x_2861_ = v___x_2840_;
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
else
{
lean_inc(v_a_2859_);
lean_dec(v___x_2840_);
v___x_2861_ = lean_box(0);
v_isShared_2862_ = v_isSharedCheck_2866_;
goto v_resetjp_2860_;
}
v_resetjp_2860_:
{
lean_object* v___x_2864_; 
if (v_isShared_2862_ == 0)
{
v___x_2864_ = v___x_2861_;
goto v_reusejp_2863_;
}
else
{
lean_object* v_reuseFailAlloc_2865_; 
v_reuseFailAlloc_2865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2865_, 0, v_a_2859_);
v___x_2864_ = v_reuseFailAlloc_2865_;
goto v_reusejp_2863_;
}
v_reusejp_2863_:
{
return v___x_2864_;
}
}
}
}
else
{
lean_dec(v_a_2832_);
v___y_2755_ = v_isEq_2826_;
v_isHEq_2756_ = v___x_2575_;
v___y_2757_ = v___y_2827_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
v___y_2760_ = v___y_2830_;
goto v___jp_2754_;
}
}
else
{
lean_object* v_a_2867_; lean_object* v___x_2869_; uint8_t v_isShared_2870_; uint8_t v_isSharedCheck_2874_; 
lean_dec_ref(v___x_2619_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_2867_ = lean_ctor_get(v___x_2831_, 0);
v_isSharedCheck_2874_ = !lean_is_exclusive(v___x_2831_);
if (v_isSharedCheck_2874_ == 0)
{
v___x_2869_ = v___x_2831_;
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
else
{
lean_inc(v_a_2867_);
lean_dec(v___x_2831_);
v___x_2869_ = lean_box(0);
v_isShared_2870_ = v_isSharedCheck_2874_;
goto v_resetjp_2868_;
}
v_resetjp_2868_:
{
lean_object* v___x_2872_; 
if (v_isShared_2870_ == 0)
{
v___x_2872_ = v___x_2869_;
goto v_reusejp_2871_;
}
else
{
lean_object* v_reuseFailAlloc_2873_; 
v_reuseFailAlloc_2873_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2873_, 0, v_a_2867_);
v___x_2872_ = v_reuseFailAlloc_2873_;
goto v_reusejp_2871_;
}
v_reusejp_2871_:
{
return v___x_2872_;
}
}
}
}
v___jp_2875_:
{
lean_object* v___x_2880_; 
lean_inc_ref(v___x_2619_);
v___x_2880_ = l_Lean_Meta_matchEq_x3f(v___x_2619_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2880_) == 0)
{
lean_object* v_a_2881_; 
v_a_2881_ = lean_ctor_get(v___x_2880_, 0);
lean_inc(v_a_2881_);
lean_dec_ref_known(v___x_2880_, 1);
if (lean_obj_tag(v_a_2881_) == 1)
{
lean_object* v_val_2882_; lean_object* v_snd_2883_; lean_object* v_fst_2884_; lean_object* v_snd_2885_; lean_object* v___x_2886_; 
v_val_2882_ = lean_ctor_get(v_a_2881_, 0);
lean_inc(v_val_2882_);
lean_dec_ref_known(v_a_2881_, 1);
v_snd_2883_ = lean_ctor_get(v_val_2882_, 1);
lean_inc(v_snd_2883_);
lean_dec(v_val_2882_);
v_fst_2884_ = lean_ctor_get(v_snd_2883_, 0);
lean_inc(v_fst_2884_);
v_snd_2885_ = lean_ctor_get(v_snd_2883_, 1);
lean_inc(v_snd_2885_);
lean_dec(v_snd_2883_);
v___x_2886_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2884_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2886_) == 0)
{
lean_object* v_a_2887_; 
v_a_2887_ = lean_ctor_get(v___x_2886_, 0);
lean_inc(v_a_2887_);
lean_dec_ref_known(v___x_2886_, 1);
if (lean_obj_tag(v_a_2887_) == 1)
{
lean_object* v_val_2888_; lean_object* v___x_2889_; 
v_val_2888_ = lean_ctor_get(v_a_2887_, 0);
lean_inc(v_val_2888_);
lean_dec_ref_known(v_a_2887_, 1);
v___x_2889_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2885_, v___y_2876_, v___y_2877_, v___y_2878_, v___y_2879_);
if (lean_obj_tag(v___x_2889_) == 0)
{
lean_object* v_a_2890_; 
v_a_2890_ = lean_ctor_get(v___x_2889_, 0);
lean_inc(v_a_2890_);
lean_dec_ref_known(v___x_2889_, 1);
if (lean_obj_tag(v_a_2890_) == 1)
{
lean_object* v_toConstantVal_2891_; lean_object* v_val_2892_; lean_object* v_toConstantVal_2893_; lean_object* v_name_2894_; lean_object* v_name_2895_; uint8_t v___x_2896_; 
v_toConstantVal_2891_ = lean_ctor_get(v_val_2888_, 0);
lean_inc_ref(v_toConstantVal_2891_);
lean_dec(v_val_2888_);
v_val_2892_ = lean_ctor_get(v_a_2890_, 0);
lean_inc(v_val_2892_);
lean_dec_ref_known(v_a_2890_, 1);
v_toConstantVal_2893_ = lean_ctor_get(v_val_2892_, 0);
lean_inc_ref(v_toConstantVal_2893_);
lean_dec(v_val_2892_);
v_name_2894_ = lean_ctor_get(v_toConstantVal_2891_, 0);
lean_inc(v_name_2894_);
lean_dec_ref(v_toConstantVal_2891_);
v_name_2895_ = lean_ctor_get(v_toConstantVal_2893_, 0);
lean_inc(v_name_2895_);
lean_dec_ref(v_toConstantVal_2893_);
v___x_2896_ = lean_name_eq(v_name_2894_, v_name_2895_);
lean_dec(v_name_2895_);
lean_dec(v_name_2894_);
if (v___x_2896_ == 0)
{
lean_dec_ref(v___x_2619_);
lean_dec_ref(v_config_2470_);
v___y_2508_ = v___y_2879_;
v___y_2509_ = v___y_2877_;
v___y_2510_ = v___y_2878_;
v___y_2511_ = v___y_2876_;
goto v___jp_2507_;
}
else
{
if (v___x_2575_ == 0)
{
lean_del_object(v___x_2504_);
v_isEq_2826_ = v___x_2481_;
v___y_2827_ = v___y_2876_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v___y_2879_;
goto v___jp_2825_;
}
else
{
lean_dec_ref(v___x_2619_);
lean_dec_ref(v_config_2470_);
v___y_2508_ = v___y_2879_;
v___y_2509_ = v___y_2877_;
v___y_2510_ = v___y_2878_;
v___y_2511_ = v___y_2876_;
goto v___jp_2507_;
}
}
}
else
{
lean_dec(v_a_2890_);
lean_dec(v_val_2888_);
lean_del_object(v___x_2504_);
v_isEq_2826_ = v___x_2481_;
v___y_2827_ = v___y_2876_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v___y_2879_;
goto v___jp_2825_;
}
}
else
{
lean_object* v_a_2897_; lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2904_; 
lean_dec(v_val_2888_);
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_2897_ = lean_ctor_get(v___x_2889_, 0);
v_isSharedCheck_2904_ = !lean_is_exclusive(v___x_2889_);
if (v_isSharedCheck_2904_ == 0)
{
v___x_2899_ = v___x_2889_;
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
else
{
lean_inc(v_a_2897_);
lean_dec(v___x_2889_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2904_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
if (v_isShared_2900_ == 0)
{
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_a_2897_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
else
{
lean_dec(v_a_2887_);
lean_dec(v_snd_2885_);
lean_del_object(v___x_2504_);
v_isEq_2826_ = v___x_2481_;
v___y_2827_ = v___y_2876_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v___y_2879_;
goto v___jp_2825_;
}
}
else
{
lean_object* v_a_2905_; lean_object* v___x_2907_; uint8_t v_isShared_2908_; uint8_t v_isSharedCheck_2912_; 
lean_dec(v_snd_2885_);
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_2905_ = lean_ctor_get(v___x_2886_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v___x_2886_);
if (v_isSharedCheck_2912_ == 0)
{
v___x_2907_ = v___x_2886_;
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
else
{
lean_inc(v_a_2905_);
lean_dec(v___x_2886_);
v___x_2907_ = lean_box(0);
v_isShared_2908_ = v_isSharedCheck_2912_;
goto v_resetjp_2906_;
}
v_resetjp_2906_:
{
lean_object* v___x_2910_; 
if (v_isShared_2908_ == 0)
{
v___x_2910_ = v___x_2907_;
goto v_reusejp_2909_;
}
else
{
lean_object* v_reuseFailAlloc_2911_; 
v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
v___x_2910_ = v_reuseFailAlloc_2911_;
goto v_reusejp_2909_;
}
v_reusejp_2909_:
{
return v___x_2910_;
}
}
}
}
else
{
lean_dec(v_a_2881_);
lean_del_object(v___x_2504_);
v_isEq_2826_ = v___x_2575_;
v___y_2827_ = v___y_2876_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v___y_2879_;
goto v___jp_2825_;
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_2913_ = lean_ctor_get(v___x_2880_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2880_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2880_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2880_);
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
lean_object* v___x_2926_; 
lean_inc_ref(v___x_2619_);
v___x_2926_ = l_Lean_refutableHasNotBit_x3f(v___x_2619_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2926_) == 0)
{
lean_object* v_a_2927_; 
v_a_2927_ = lean_ctor_get(v___x_2926_, 0);
lean_inc(v_a_2927_);
lean_dec_ref_known(v___x_2926_, 1);
if (lean_obj_tag(v_a_2927_) == 1)
{
lean_object* v_val_2928_; lean_object* v___x_2930_; uint8_t v_isShared_2931_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec_ref(v_config_2470_);
v_val_2928_ = lean_ctor_get(v_a_2927_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v_a_2927_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2930_ = v_a_2927_;
v_isShared_2931_ = v_isSharedCheck_2967_;
goto v_resetjp_2929_;
}
else
{
lean_inc(v_val_2928_);
lean_dec(v_a_2927_);
v___x_2930_ = lean_box(0);
v_isShared_2931_ = v_isSharedCheck_2967_;
goto v_resetjp_2929_;
}
v_resetjp_2929_:
{
lean_object* v___x_2932_; 
lean_inc(v_mvarId_2471_);
v___x_2932_ = l_Lean_MVarId_getType(v_mvarId_2471_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2932_) == 0)
{
lean_object* v_a_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; 
v_a_2933_ = lean_ctor_get(v___x_2932_, 0);
lean_inc(v_a_2933_);
lean_dec_ref_known(v___x_2932_, 1);
v___x_2934_ = l_Lean_LocalDecl_toExpr(v_val_2502_);
v___x_2935_ = l_Lean_Meta_mkAbsurd(v_a_2933_, v_val_2928_, v___x_2934_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2935_) == 0)
{
lean_object* v_a_2936_; lean_object* v___x_2937_; 
v_a_2936_ = lean_ctor_get(v___x_2935_, 0);
lean_inc(v_a_2936_);
lean_dec_ref_known(v___x_2935_, 1);
v___x_2937_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2471_, v_a_2936_, v___y_2923_);
if (lean_obj_tag(v___x_2937_) == 0)
{
lean_object* v___x_2938_; lean_object* v___x_2940_; 
lean_dec_ref_known(v___x_2937_, 1);
v___x_2938_ = lean_box(v___x_2481_);
if (v_isShared_2931_ == 0)
{
lean_ctor_set(v___x_2930_, 0, v___x_2938_);
v___x_2940_ = v___x_2930_;
goto v_reusejp_2939_;
}
else
{
lean_object* v_reuseFailAlloc_2942_; 
v_reuseFailAlloc_2942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2942_, 0, v___x_2938_);
v___x_2940_ = v_reuseFailAlloc_2942_;
goto v_reusejp_2939_;
}
v_reusejp_2939_:
{
lean_object* v___x_2941_; 
v___x_2941_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2941_, 0, v___x_2940_);
lean_ctor_set(v___x_2941_, 1, v___x_2506_);
v_a_2488_ = v___x_2941_;
goto v___jp_2487_;
}
}
else
{
lean_object* v_a_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
lean_del_object(v___x_2930_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
v_a_2943_ = lean_ctor_get(v___x_2937_, 0);
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2937_);
if (v_isSharedCheck_2950_ == 0)
{
v___x_2945_ = v___x_2937_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_a_2943_);
lean_dec(v___x_2937_);
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
}
else
{
lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_del_object(v___x_2930_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_2951_ = lean_ctor_get(v___x_2935_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2935_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2935_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2935_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
else
{
lean_object* v_a_2959_; lean_object* v___x_2961_; uint8_t v_isShared_2962_; uint8_t v_isSharedCheck_2966_; 
lean_del_object(v___x_2930_);
lean_dec(v_val_2928_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_2959_ = lean_ctor_get(v___x_2932_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v___x_2932_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2961_ = v___x_2932_;
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
else
{
lean_inc(v_a_2959_);
lean_dec(v___x_2932_);
v___x_2961_ = lean_box(0);
v_isShared_2962_ = v_isSharedCheck_2966_;
goto v_resetjp_2960_;
}
v_resetjp_2960_:
{
lean_object* v___x_2964_; 
if (v_isShared_2962_ == 0)
{
v___x_2964_ = v___x_2961_;
goto v_reusejp_2963_;
}
else
{
lean_object* v_reuseFailAlloc_2965_; 
v_reuseFailAlloc_2965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2965_, 0, v_a_2959_);
v___x_2964_ = v_reuseFailAlloc_2965_;
goto v_reusejp_2963_;
}
v_reusejp_2963_:
{
return v___x_2964_;
}
}
}
}
}
else
{
lean_object* v___x_2968_; 
lean_dec(v_a_2927_);
lean_inc_ref(v___x_2619_);
v___x_2968_ = l_Lean_Meta_matchNe_x3f(v___x_2619_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
if (lean_obj_tag(v_a_2969_) == 1)
{
lean_object* v_val_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_3039_; 
v_val_2970_ = lean_ctor_get(v_a_2969_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_a_2969_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_2972_ = v_a_2969_;
v_isShared_2973_ = v_isSharedCheck_3039_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_val_2970_);
lean_dec(v_a_2969_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_3039_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v_snd_2974_; lean_object* v_fst_2975_; lean_object* v_snd_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_3038_; 
v_snd_2974_ = lean_ctor_get(v_val_2970_, 1);
lean_inc(v_snd_2974_);
lean_dec(v_val_2970_);
v_fst_2975_ = lean_ctor_get(v_snd_2974_, 0);
v_snd_2976_ = lean_ctor_get(v_snd_2974_, 1);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_snd_2974_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_2978_ = v_snd_2974_;
v_isShared_2979_ = v_isSharedCheck_3038_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_snd_2976_);
lean_inc(v_fst_2975_);
lean_dec(v_snd_2974_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_3038_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2980_; 
lean_inc(v_fst_2975_);
v___x_2980_ = l_Lean_Meta_isExprDefEq(v_fst_2975_, v_snd_2976_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; uint8_t v___x_2982_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
lean_inc(v_a_2981_);
lean_dec_ref_known(v___x_2980_, 1);
v___x_2982_ = lean_unbox(v_a_2981_);
lean_dec(v_a_2981_);
if (v___x_2982_ == 0)
{
lean_del_object(v___x_2978_);
lean_dec(v_fst_2975_);
lean_del_object(v___x_2972_);
v___y_2876_ = v___y_2922_;
v___y_2877_ = v___y_2923_;
v___y_2878_ = v___y_2924_;
v___y_2879_ = v___y_2925_;
goto v___jp_2875_;
}
else
{
lean_object* v___x_2983_; 
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec_ref(v_config_2470_);
lean_inc(v_mvarId_2471_);
v___x_2983_ = l_Lean_MVarId_getType(v_mvarId_2471_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2983_) == 0)
{
lean_object* v_a_2984_; lean_object* v___x_2985_; 
v_a_2984_ = lean_ctor_get(v___x_2983_, 0);
lean_inc(v_a_2984_);
lean_dec_ref_known(v___x_2983_, 1);
v___x_2985_ = l_Lean_Meta_mkEqRefl(v_fst_2975_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2985_) == 0)
{
lean_object* v_a_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; 
v_a_2986_ = lean_ctor_get(v___x_2985_, 0);
lean_inc(v_a_2986_);
lean_dec_ref_known(v___x_2985_, 1);
v___x_2987_ = l_Lean_LocalDecl_toExpr(v_val_2502_);
v___x_2988_ = l_Lean_Meta_mkAbsurd(v_a_2984_, v_a_2986_, v___x_2987_, v___y_2922_, v___y_2923_, v___y_2924_, v___y_2925_);
if (lean_obj_tag(v___x_2988_) == 0)
{
lean_object* v_a_2989_; lean_object* v___x_2990_; 
v_a_2989_ = lean_ctor_get(v___x_2988_, 0);
lean_inc(v_a_2989_);
lean_dec_ref_known(v___x_2988_, 1);
v___x_2990_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2471_, v_a_2989_, v___y_2923_);
if (lean_obj_tag(v___x_2990_) == 0)
{
lean_object* v___x_2991_; lean_object* v___x_2993_; 
lean_dec_ref_known(v___x_2990_, 1);
v___x_2991_ = lean_box(v___x_2481_);
if (v_isShared_2973_ == 0)
{
lean_ctor_set(v___x_2972_, 0, v___x_2991_);
v___x_2993_ = v___x_2972_;
goto v_reusejp_2992_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2991_);
v___x_2993_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2992_;
}
v_reusejp_2992_:
{
lean_object* v___x_2995_; 
if (v_isShared_2979_ == 0)
{
lean_ctor_set(v___x_2978_, 1, v___x_2506_);
lean_ctor_set(v___x_2978_, 0, v___x_2993_);
v___x_2995_ = v___x_2978_;
goto v_reusejp_2994_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2993_);
lean_ctor_set(v_reuseFailAlloc_2996_, 1, v___x_2506_);
v___x_2995_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2994_;
}
v_reusejp_2994_:
{
v_a_2488_ = v___x_2995_;
goto v___jp_2487_;
}
}
}
else
{
lean_object* v_a_2998_; lean_object* v___x_3000_; uint8_t v_isShared_3001_; uint8_t v_isSharedCheck_3005_; 
lean_del_object(v___x_2978_);
lean_del_object(v___x_2972_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
v_a_2998_ = lean_ctor_get(v___x_2990_, 0);
v_isSharedCheck_3005_ = !lean_is_exclusive(v___x_2990_);
if (v_isSharedCheck_3005_ == 0)
{
v___x_3000_ = v___x_2990_;
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
else
{
lean_inc(v_a_2998_);
lean_dec(v___x_2990_);
v___x_3000_ = lean_box(0);
v_isShared_3001_ = v_isSharedCheck_3005_;
goto v_resetjp_2999_;
}
v_resetjp_2999_:
{
lean_object* v___x_3003_; 
if (v_isShared_3001_ == 0)
{
v___x_3003_ = v___x_3000_;
goto v_reusejp_3002_;
}
else
{
lean_object* v_reuseFailAlloc_3004_; 
v_reuseFailAlloc_3004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
v___x_3003_ = v_reuseFailAlloc_3004_;
goto v_reusejp_3002_;
}
v_reusejp_3002_:
{
return v___x_3003_;
}
}
}
}
else
{
lean_object* v_a_3006_; lean_object* v___x_3008_; uint8_t v_isShared_3009_; uint8_t v_isSharedCheck_3013_; 
lean_del_object(v___x_2978_);
lean_del_object(v___x_2972_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_3006_ = lean_ctor_get(v___x_2988_, 0);
v_isSharedCheck_3013_ = !lean_is_exclusive(v___x_2988_);
if (v_isSharedCheck_3013_ == 0)
{
v___x_3008_ = v___x_2988_;
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
else
{
lean_inc(v_a_3006_);
lean_dec(v___x_2988_);
v___x_3008_ = lean_box(0);
v_isShared_3009_ = v_isSharedCheck_3013_;
goto v_resetjp_3007_;
}
v_resetjp_3007_:
{
lean_object* v___x_3011_; 
if (v_isShared_3009_ == 0)
{
v___x_3011_ = v___x_3008_;
goto v_reusejp_3010_;
}
else
{
lean_object* v_reuseFailAlloc_3012_; 
v_reuseFailAlloc_3012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3012_, 0, v_a_3006_);
v___x_3011_ = v_reuseFailAlloc_3012_;
goto v_reusejp_3010_;
}
v_reusejp_3010_:
{
return v___x_3011_;
}
}
}
}
else
{
lean_object* v_a_3014_; lean_object* v___x_3016_; uint8_t v_isShared_3017_; uint8_t v_isSharedCheck_3021_; 
lean_dec(v_a_2984_);
lean_del_object(v___x_2978_);
lean_del_object(v___x_2972_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_3014_ = lean_ctor_get(v___x_2985_, 0);
v_isSharedCheck_3021_ = !lean_is_exclusive(v___x_2985_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3016_ = v___x_2985_;
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
else
{
lean_inc(v_a_3014_);
lean_dec(v___x_2985_);
v___x_3016_ = lean_box(0);
v_isShared_3017_ = v_isSharedCheck_3021_;
goto v_resetjp_3015_;
}
v_resetjp_3015_:
{
lean_object* v___x_3019_; 
if (v_isShared_3017_ == 0)
{
v___x_3019_ = v___x_3016_;
goto v_reusejp_3018_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
v___x_3019_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3018_;
}
v_reusejp_3018_:
{
return v___x_3019_;
}
}
}
}
else
{
lean_object* v_a_3022_; lean_object* v___x_3024_; uint8_t v_isShared_3025_; uint8_t v_isSharedCheck_3029_; 
lean_del_object(v___x_2978_);
lean_dec(v_fst_2975_);
lean_del_object(v___x_2972_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_3022_ = lean_ctor_get(v___x_2983_, 0);
v_isSharedCheck_3029_ = !lean_is_exclusive(v___x_2983_);
if (v_isSharedCheck_3029_ == 0)
{
v___x_3024_ = v___x_2983_;
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
else
{
lean_inc(v_a_3022_);
lean_dec(v___x_2983_);
v___x_3024_ = lean_box(0);
v_isShared_3025_ = v_isSharedCheck_3029_;
goto v_resetjp_3023_;
}
v_resetjp_3023_:
{
lean_object* v___x_3027_; 
if (v_isShared_3025_ == 0)
{
v___x_3027_ = v___x_3024_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3028_; 
v_reuseFailAlloc_3028_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3028_, 0, v_a_3022_);
v___x_3027_ = v_reuseFailAlloc_3028_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
return v___x_3027_;
}
}
}
}
}
else
{
lean_object* v_a_3030_; lean_object* v___x_3032_; uint8_t v_isShared_3033_; uint8_t v_isSharedCheck_3037_; 
lean_del_object(v___x_2978_);
lean_dec(v_fst_2975_);
lean_del_object(v___x_2972_);
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_3030_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_3037_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_3032_ = v___x_2980_;
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
else
{
lean_inc(v_a_3030_);
lean_dec(v___x_2980_);
v___x_3032_ = lean_box(0);
v_isShared_3033_ = v_isSharedCheck_3037_;
goto v_resetjp_3031_;
}
v_resetjp_3031_:
{
lean_object* v___x_3035_; 
if (v_isShared_3033_ == 0)
{
v___x_3035_ = v___x_3032_;
goto v_reusejp_3034_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v_a_3030_);
v___x_3035_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3034_;
}
v_reusejp_3034_:
{
return v___x_3035_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2969_);
v___y_2876_ = v___y_2922_;
v___y_2877_ = v___y_2923_;
v___y_2878_ = v___y_2924_;
v___y_2879_ = v___y_2925_;
goto v___jp_2875_;
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_3040_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_2968_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_2968_);
v___x_3042_ = lean_box(0);
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
v_resetjp_3041_:
{
lean_object* v___x_3045_; 
if (v_isShared_3043_ == 0)
{
v___x_3045_ = v___x_3042_;
goto v_reusejp_3044_;
}
else
{
lean_object* v_reuseFailAlloc_3046_; 
v_reuseFailAlloc_3046_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3046_, 0, v_a_3040_);
v___x_3045_ = v_reuseFailAlloc_3046_;
goto v_reusejp_3044_;
}
v_reusejp_3044_:
{
return v___x_3045_;
}
}
}
}
}
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec_ref(v___x_2619_);
lean_del_object(v___x_2504_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_3048_ = lean_ctor_get(v___x_2926_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_2926_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_2926_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_2926_);
v___x_3050_ = lean_box(0);
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
v_resetjp_3049_:
{
lean_object* v___x_3053_; 
if (v_isShared_3051_ == 0)
{
v___x_3053_ = v___x_3050_;
goto v_reusejp_3052_;
}
else
{
lean_object* v_reuseFailAlloc_3054_; 
v_reuseFailAlloc_3054_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3054_, 0, v_a_3048_);
v___x_3053_ = v_reuseFailAlloc_3054_;
goto v_reusejp_3052_;
}
v_reusejp_3052_:
{
return v___x_3053_;
}
}
}
}
}
else
{
lean_del_object(v___x_2504_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
v_a_2496_ = v___x_2547_;
goto v___jp_2495_;
}
v___jp_2507_:
{
lean_object* v___x_2512_; 
lean_inc(v_mvarId_2471_);
v___x_2512_ = l_Lean_MVarId_getType(v_mvarId_2471_, v___y_2511_, v___y_2509_, v___y_2510_, v___y_2508_);
if (lean_obj_tag(v___x_2512_) == 0)
{
lean_object* v_a_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_a_2513_ = lean_ctor_get(v___x_2512_, 0);
lean_inc(v_a_2513_);
lean_dec_ref_known(v___x_2512_, 1);
v___x_2514_ = l_Lean_LocalDecl_toExpr(v_val_2502_);
v___x_2515_ = l_Lean_Meta_mkNoConfusion(v_a_2513_, v___x_2514_, v___y_2511_, v___y_2509_, v___y_2510_, v___y_2508_);
if (lean_obj_tag(v___x_2515_) == 0)
{
lean_object* v_a_2516_; lean_object* v___x_2517_; 
v_a_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_a_2516_);
lean_dec_ref_known(v___x_2515_, 1);
v___x_2517_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2471_, v_a_2516_, v___y_2509_);
if (lean_obj_tag(v___x_2517_) == 0)
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
lean_dec_ref_known(v___x_2517_, 1);
v___x_2518_ = lean_box(v___x_2481_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 0, v___x_2518_);
v___x_2520_ = v___x_2504_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
lean_object* v___x_2521_; 
v___x_2521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v___x_2506_);
v_a_2488_ = v___x_2521_;
goto v___jp_2487_;
}
}
else
{
lean_object* v_a_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_2530_; 
lean_del_object(v___x_2504_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
v_a_2523_ = lean_ctor_get(v___x_2517_, 0);
v_isSharedCheck_2530_ = !lean_is_exclusive(v___x_2517_);
if (v_isSharedCheck_2530_ == 0)
{
v___x_2525_ = v___x_2517_;
v_isShared_2526_ = v_isSharedCheck_2530_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_a_2523_);
lean_dec(v___x_2517_);
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
else
{
lean_object* v_a_2531_; lean_object* v___x_2533_; uint8_t v_isShared_2534_; uint8_t v_isSharedCheck_2538_; 
lean_del_object(v___x_2504_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_2531_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2538_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2538_ == 0)
{
v___x_2533_ = v___x_2515_;
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
else
{
lean_inc(v_a_2531_);
lean_dec(v___x_2515_);
v___x_2533_ = lean_box(0);
v_isShared_2534_ = v_isSharedCheck_2538_;
goto v_resetjp_2532_;
}
v_resetjp_2532_:
{
lean_object* v___x_2536_; 
if (v_isShared_2534_ == 0)
{
v___x_2536_ = v___x_2533_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2537_; 
v_reuseFailAlloc_2537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2537_, 0, v_a_2531_);
v___x_2536_ = v_reuseFailAlloc_2537_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
return v___x_2536_;
}
}
}
}
else
{
lean_object* v_a_2539_; lean_object* v___x_2541_; uint8_t v_isShared_2542_; uint8_t v_isSharedCheck_2546_; 
lean_del_object(v___x_2504_);
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
v_a_2539_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2546_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2546_ == 0)
{
v___x_2541_ = v___x_2512_;
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
else
{
lean_inc(v_a_2539_);
lean_dec(v___x_2512_);
v___x_2541_ = lean_box(0);
v_isShared_2542_ = v_isSharedCheck_2546_;
goto v_resetjp_2540_;
}
v_resetjp_2540_:
{
lean_object* v___x_2544_; 
if (v_isShared_2542_ == 0)
{
v___x_2544_ = v___x_2541_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2545_; 
v_reuseFailAlloc_2545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2545_, 0, v_a_2539_);
v___x_2544_ = v_reuseFailAlloc_2545_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
return v___x_2544_;
}
}
}
}
v___jp_2548_:
{
lean_object* v_searchFuel_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; 
v_searchFuel_2553_ = lean_ctor_get(v_config_2470_, 0);
v___x_2554_ = l_Lean_LocalDecl_fvarId(v_val_2502_);
lean_dec(v_val_2502_);
lean_inc(v_searchFuel_2553_);
lean_inc(v_mvarId_2471_);
v___x_2555_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2471_, v___x_2554_, v_searchFuel_2553_, v___y_2551_, v___y_2549_, v___y_2552_, v___y_2550_);
if (lean_obj_tag(v___x_2555_) == 0)
{
lean_object* v_a_2556_; uint8_t v___x_2557_; 
v_a_2556_ = lean_ctor_get(v___x_2555_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v___x_2555_, 1);
v___x_2557_ = lean_unbox(v_a_2556_);
lean_dec(v_a_2556_);
if (v___x_2557_ == 0)
{
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
v_a_2496_ = v___x_2547_;
goto v___jp_2495_;
}
else
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; 
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v___x_2558_ = lean_box(v___x_2481_);
v___x_2559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
lean_ctor_set(v___x_2560_, 1, v___x_2506_);
v_a_2488_ = v___x_2560_;
goto v___jp_2487_;
}
}
else
{
lean_object* v_a_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2568_; 
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_2561_ = lean_ctor_get(v___x_2555_, 0);
v_isSharedCheck_2568_ = !lean_is_exclusive(v___x_2555_);
if (v_isSharedCheck_2568_ == 0)
{
v___x_2563_ = v___x_2555_;
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_a_2561_);
lean_dec(v___x_2555_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2568_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v___x_2566_; 
if (v_isShared_2564_ == 0)
{
v___x_2566_ = v___x_2563_;
goto v_reusejp_2565_;
}
else
{
lean_object* v_reuseFailAlloc_2567_; 
v_reuseFailAlloc_2567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2567_, 0, v_a_2561_);
v___x_2566_ = v_reuseFailAlloc_2567_;
goto v_reusejp_2565_;
}
v_reusejp_2565_:
{
return v___x_2566_;
}
}
}
}
v___jp_2569_:
{
if (v___y_2574_ == 0)
{
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
v_a_2496_ = v___x_2547_;
goto v___jp_2495_;
}
else
{
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___y_2572_;
v___y_2551_ = v___y_2571_;
v___y_2552_ = v___y_2573_;
goto v___jp_2548_;
}
}
v___jp_2576_:
{
if (v___y_2581_ == 0)
{
v___y_2549_ = v___y_2577_;
v___y_2550_ = v___y_2579_;
v___y_2551_ = v___y_2578_;
v___y_2552_ = v___y_2580_;
goto v___jp_2548_;
}
else
{
v___y_2570_ = v___y_2577_;
v___y_2571_ = v___y_2578_;
v___y_2572_ = v___y_2579_;
v___y_2573_ = v___y_2580_;
v___y_2574_ = v___x_2575_;
goto v___jp_2569_;
}
}
v___jp_2582_:
{
if (v___y_2588_ == 0)
{
v___y_2570_ = v___y_2583_;
v___y_2571_ = v___y_2585_;
v___y_2572_ = v___y_2584_;
v___y_2573_ = v___y_2586_;
v___y_2574_ = v___x_2575_;
goto v___jp_2569_;
}
else
{
v___y_2577_ = v___y_2583_;
v___y_2578_ = v___y_2585_;
v___y_2579_ = v___y_2584_;
v___y_2580_ = v___y_2586_;
v___y_2581_ = v___y_2587_;
goto v___jp_2576_;
}
}
v___jp_2589_:
{
uint8_t v_emptyType_2596_; 
v_emptyType_2596_ = lean_ctor_get_uint8(v_config_2470_, sizeof(void*)*1 + 1);
if (v_emptyType_2596_ == 0)
{
v___y_2583_ = v___y_2593_;
v___y_2584_ = v___y_2595_;
v___y_2585_ = v___y_2592_;
v___y_2586_ = v___y_2594_;
v___y_2587_ = v___y_2591_;
v___y_2588_ = v___x_2575_;
goto v___jp_2582_;
}
else
{
if (v___y_2590_ == 0)
{
v___y_2577_ = v___y_2593_;
v___y_2578_ = v___y_2592_;
v___y_2579_ = v___y_2595_;
v___y_2580_ = v___y_2594_;
v___y_2581_ = v___y_2591_;
goto v___jp_2576_;
}
else
{
v___y_2583_ = v___y_2593_;
v___y_2584_ = v___y_2595_;
v___y_2585_ = v___y_2592_;
v___y_2586_ = v___y_2594_;
v___y_2587_ = v___y_2591_;
v___y_2588_ = v___x_2575_;
goto v___jp_2582_;
}
}
}
v___jp_2597_:
{
if (v___y_2604_ == 0)
{
v___y_2590_ = v___y_2598_;
v___y_2591_ = v___y_2603_;
v___y_2592_ = v___y_2600_;
v___y_2593_ = v___y_2601_;
v___y_2594_ = v___y_2602_;
v___y_2595_ = v___y_2599_;
goto v___jp_2589_;
}
else
{
lean_object* v___x_2605_; 
lean_inc(v_val_2502_);
lean_inc(v_mvarId_2471_);
v___x_2605_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2471_, v_val_2502_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2599_);
if (lean_obj_tag(v___x_2605_) == 0)
{
lean_object* v_a_2606_; uint8_t v___x_2607_; 
v_a_2606_ = lean_ctor_get(v___x_2605_, 0);
lean_inc(v_a_2606_);
lean_dec_ref_known(v___x_2605_, 1);
v___x_2607_ = lean_unbox(v_a_2606_);
lean_dec(v_a_2606_);
if (v___x_2607_ == 0)
{
v___y_2590_ = v___y_2598_;
v___y_2591_ = v___y_2603_;
v___y_2592_ = v___y_2600_;
v___y_2593_ = v___y_2601_;
v___y_2594_ = v___y_2602_;
v___y_2595_ = v___y_2599_;
goto v___jp_2589_;
}
else
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
lean_dec(v_val_2502_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v___x_2608_ = lean_box(v___x_2481_);
v___x_2609_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2506_);
v_a_2488_ = v___x_2610_;
goto v___jp_2487_;
}
}
else
{
lean_object* v_a_2611_; lean_object* v___x_2613_; uint8_t v_isShared_2614_; uint8_t v_isSharedCheck_2618_; 
lean_dec(v_val_2502_);
lean_del_object(v___x_2485_);
lean_dec(v_snd_2483_);
lean_dec(v_mvarId_2471_);
lean_dec_ref(v_config_2470_);
v_a_2611_ = lean_ctor_get(v___x_2605_, 0);
v_isSharedCheck_2618_ = !lean_is_exclusive(v___x_2605_);
if (v_isSharedCheck_2618_ == 0)
{
v___x_2613_ = v___x_2605_;
v_isShared_2614_ = v_isSharedCheck_2618_;
goto v_resetjp_2612_;
}
else
{
lean_inc(v_a_2611_);
lean_dec(v___x_2605_);
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
}
}
v___jp_2487_:
{
lean_object* v___x_2489_; lean_object* v___x_2491_; 
v___x_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2489_, 0, v_a_2488_);
if (v_isShared_2486_ == 0)
{
lean_ctor_set(v___x_2485_, 0, v___x_2489_);
v___x_2491_ = v___x_2485_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v___x_2489_);
lean_ctor_set(v_reuseFailAlloc_2493_, 1, v_snd_2483_);
v___x_2491_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
lean_object* v___x_2492_; 
v___x_2492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2492_, 0, v___x_2491_);
return v___x_2492_;
}
}
v___jp_2495_:
{
lean_object* v___x_2497_; size_t v___x_2498_; size_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2497_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2494_);
lean_ctor_set(v___x_2497_, 1, v_a_2496_);
v___x_2498_ = ((size_t)1ULL);
v___x_2499_ = lean_usize_add(v_i_2474_, v___x_2498_);
v___x_2500_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2470_, v_mvarId_2471_, v_as_2472_, v_sz_2473_, v___x_2499_, v___x_2497_, v___y_2476_, v___y_2477_, v___y_2478_, v___y_2479_);
return v___x_2500_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3122_, lean_object* v_mvarId_3123_, lean_object* v_as_3124_, lean_object* v_sz_3125_, lean_object* v_i_3126_, lean_object* v_b_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_){
_start:
{
size_t v_sz_boxed_3133_; size_t v_i_boxed_3134_; lean_object* v_res_3135_; 
v_sz_boxed_3133_ = lean_unbox_usize(v_sz_3125_);
lean_dec(v_sz_3125_);
v_i_boxed_3134_ = lean_unbox_usize(v_i_3126_);
lean_dec(v_i_3126_);
v_res_3135_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3122_, v_mvarId_3123_, v_as_3124_, v_sz_boxed_3133_, v_i_boxed_3134_, v_b_3127_, v___y_3128_, v___y_3129_, v___y_3130_, v___y_3131_);
lean_dec(v___y_3131_);
lean_dec_ref(v___y_3130_);
lean_dec(v___y_3129_);
lean_dec_ref(v___y_3128_);
lean_dec_ref(v_as_3124_);
return v_res_3135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3139_, lean_object* v_mvarId_3140_, lean_object* v_as_3141_, size_t v_sz_3142_, size_t v_i_3143_, lean_object* v_b_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
uint8_t v___x_3150_; 
v___x_3150_ = lean_usize_dec_lt(v_i_3143_, v_sz_3142_);
if (v___x_3150_ == 0)
{
lean_object* v___x_3151_; 
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v___x_3151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3151_, 0, v_b_3144_);
return v___x_3151_;
}
else
{
lean_object* v_snd_3152_; lean_object* v___x_3154_; uint8_t v_isShared_3155_; uint8_t v_isSharedCheck_3809_; 
v_snd_3152_ = lean_ctor_get(v_b_3144_, 1);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_b_3144_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; 
v_unused_3810_ = lean_ctor_get(v_b_3144_, 0);
lean_dec(v_unused_3810_);
v___x_3154_ = v_b_3144_;
v_isShared_3155_ = v_isSharedCheck_3809_;
goto v_resetjp_3153_;
}
else
{
lean_inc(v_snd_3152_);
lean_dec(v_b_3144_);
v___x_3154_ = lean_box(0);
v_isShared_3155_ = v_isSharedCheck_3809_;
goto v_resetjp_3153_;
}
v_resetjp_3153_:
{
lean_object* v_a_3157_; lean_object* v___x_3163_; lean_object* v_a_3165_; lean_object* v_a_3170_; 
v___x_3163_ = lean_box(0);
v_a_3170_ = lean_array_uget(v_as_3141_, v_i_3143_);
if (lean_obj_tag(v_a_3170_) == 0)
{
lean_del_object(v___x_3154_);
v_a_3165_ = v_snd_3152_;
goto v___jp_3164_;
}
else
{
lean_object* v_val_3171_; lean_object* v___x_3173_; uint8_t v_isShared_3174_; uint8_t v_isSharedCheck_3808_; 
v_val_3171_ = lean_ctor_get(v_a_3170_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_a_3170_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3173_ = v_a_3170_;
v_isShared_3174_ = v_isSharedCheck_3808_;
goto v_resetjp_3172_;
}
else
{
lean_inc(v_val_3171_);
lean_dec(v_a_3170_);
v___x_3173_ = lean_box(0);
v_isShared_3174_ = v_isSharedCheck_3808_;
goto v_resetjp_3172_;
}
v_resetjp_3172_:
{
lean_object* v___x_3175_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___x_3217_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; uint8_t v___y_3245_; uint8_t v___x_3246_; lean_object* v___y_3248_; lean_object* v___y_3249_; uint8_t v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3254_; lean_object* v___y_3255_; uint8_t v___y_3256_; lean_object* v___y_3257_; lean_object* v___y_3258_; uint8_t v___y_3259_; uint8_t v___y_3261_; uint8_t v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3271_; uint8_t v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; uint8_t v___y_3275_; 
v___x_3175_ = lean_box(0);
v___x_3217_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3246_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3171_);
if (v___x_3246_ == 0)
{
lean_object* v___x_3291_; uint8_t v___y_3293_; uint8_t v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3302_; uint8_t v___y_3303_; uint8_t v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; uint8_t v___y_3309_; lean_object* v___y_3312_; uint8_t v___y_3313_; lean_object* v___y_3314_; uint8_t v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; lean_object* v_a_3318_; lean_object* v___y_3322_; uint8_t v___y_3323_; uint8_t v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; lean_object* v___y_3389_; uint8_t v___y_3390_; uint8_t v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; uint8_t v___y_3395_; lean_object* v___y_3397_; uint8_t v___y_3398_; lean_object* v___y_3399_; uint8_t v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; uint8_t v___y_3404_; lean_object* v___y_3407_; uint8_t v___y_3408_; uint8_t v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; uint8_t v___y_3413_; lean_object* v___y_3426_; uint8_t v___y_3427_; uint8_t v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; uint8_t v___y_3432_; uint8_t v___y_3434_; uint8_t v_isHEq_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3443_; lean_object* v___y_3444_; uint8_t v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; uint8_t v_isEq_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___x_3738_; 
v___x_3291_ = l_Lean_LocalDecl_type(v_val_3171_);
lean_inc_ref(v___x_3291_);
v___x_3738_ = l_Lean_Meta_matchNot_x3f(v___x_3291_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
lean_dec_ref_known(v___x_3738_, 1);
if (lean_obj_tag(v_a_3739_) == 1)
{
lean_object* v_val_3740_; lean_object* v___x_3742_; uint8_t v_isShared_3743_; uint8_t v_isSharedCheck_3799_; 
v_val_3740_ = lean_ctor_get(v_a_3739_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v_a_3739_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3742_ = v_a_3739_;
v_isShared_3743_ = v_isSharedCheck_3799_;
goto v_resetjp_3741_;
}
else
{
lean_inc(v_val_3740_);
lean_dec(v_a_3739_);
v___x_3742_ = lean_box(0);
v_isShared_3743_ = v_isSharedCheck_3799_;
goto v_resetjp_3741_;
}
v_resetjp_3741_:
{
lean_object* v___x_3744_; 
v___x_3744_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3740_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3744_) == 0)
{
lean_object* v_a_3745_; 
v_a_3745_ = lean_ctor_get(v___x_3744_, 0);
lean_inc(v_a_3745_);
lean_dec_ref_known(v___x_3744_, 1);
if (lean_obj_tag(v_a_3745_) == 1)
{
lean_object* v_val_3746_; lean_object* v___x_3748_; uint8_t v_isShared_3749_; uint8_t v_isSharedCheck_3790_; 
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec_ref(v_config_3139_);
v_val_3746_ = lean_ctor_get(v_a_3745_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_a_3745_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3748_ = v_a_3745_;
v_isShared_3749_ = v_isSharedCheck_3790_;
goto v_resetjp_3747_;
}
else
{
lean_inc(v_val_3746_);
lean_dec(v_a_3745_);
v___x_3748_ = lean_box(0);
v_isShared_3749_ = v_isSharedCheck_3790_;
goto v_resetjp_3747_;
}
v_resetjp_3747_:
{
lean_object* v___x_3750_; 
lean_inc(v_mvarId_3140_);
v___x_3750_ = l_Lean_MVarId_getType(v_mvarId_3140_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3750_) == 0)
{
lean_object* v_a_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; 
v_a_3751_ = lean_ctor_get(v___x_3750_, 0);
lean_inc(v_a_3751_);
lean_dec_ref_known(v___x_3750_, 1);
v___x_3752_ = l_Lean_LocalDecl_toExpr(v_val_3171_);
v___x_3753_ = l_Lean_mkFVar(v_val_3746_);
v___x_3754_ = l_Lean_Expr_app___override(v___x_3752_, v___x_3753_);
v___x_3755_ = l_Lean_Meta_mkFalseElim(v_a_3751_, v___x_3754_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
if (lean_obj_tag(v___x_3755_) == 0)
{
lean_object* v_a_3756_; lean_object* v___x_3757_; 
v_a_3756_ = lean_ctor_get(v___x_3755_, 0);
lean_inc(v_a_3756_);
lean_dec_ref_known(v___x_3755_, 1);
v___x_3757_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3140_, v_a_3756_, v___y_3146_);
if (lean_obj_tag(v___x_3757_) == 0)
{
lean_object* v___x_3758_; lean_object* v___x_3760_; 
lean_dec_ref_known(v___x_3757_, 1);
v___x_3758_ = lean_box(v___x_3150_);
if (v_isShared_3749_ == 0)
{
lean_ctor_set(v___x_3748_, 0, v___x_3758_);
v___x_3760_ = v___x_3748_;
goto v_reusejp_3759_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3758_);
v___x_3760_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3759_;
}
v_reusejp_3759_:
{
lean_object* v___x_3761_; lean_object* v___x_3763_; 
v___x_3761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3760_);
lean_ctor_set(v___x_3761_, 1, v___x_3175_);
if (v_isShared_3743_ == 0)
{
lean_ctor_set_tag(v___x_3742_, 0);
lean_ctor_set(v___x_3742_, 0, v___x_3761_);
v___x_3763_ = v___x_3742_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3761_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
v_a_3157_ = v___x_3763_;
goto v___jp_3156_;
}
}
}
else
{
lean_object* v_a_3766_; lean_object* v___x_3768_; uint8_t v_isShared_3769_; uint8_t v_isSharedCheck_3773_; 
lean_del_object(v___x_3748_);
lean_del_object(v___x_3742_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
v_a_3766_ = lean_ctor_get(v___x_3757_, 0);
v_isSharedCheck_3773_ = !lean_is_exclusive(v___x_3757_);
if (v_isSharedCheck_3773_ == 0)
{
v___x_3768_ = v___x_3757_;
v_isShared_3769_ = v_isSharedCheck_3773_;
goto v_resetjp_3767_;
}
else
{
lean_inc(v_a_3766_);
lean_dec(v___x_3757_);
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
else
{
lean_object* v_a_3774_; lean_object* v___x_3776_; uint8_t v_isShared_3777_; uint8_t v_isSharedCheck_3781_; 
lean_del_object(v___x_3748_);
lean_del_object(v___x_3742_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3774_ = lean_ctor_get(v___x_3755_, 0);
v_isSharedCheck_3781_ = !lean_is_exclusive(v___x_3755_);
if (v_isSharedCheck_3781_ == 0)
{
v___x_3776_ = v___x_3755_;
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
else
{
lean_inc(v_a_3774_);
lean_dec(v___x_3755_);
v___x_3776_ = lean_box(0);
v_isShared_3777_ = v_isSharedCheck_3781_;
goto v_resetjp_3775_;
}
v_resetjp_3775_:
{
lean_object* v___x_3779_; 
if (v_isShared_3777_ == 0)
{
v___x_3779_ = v___x_3776_;
goto v_reusejp_3778_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_a_3774_);
v___x_3779_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3778_;
}
v_reusejp_3778_:
{
return v___x_3779_;
}
}
}
}
else
{
lean_object* v_a_3782_; lean_object* v___x_3784_; uint8_t v_isShared_3785_; uint8_t v_isSharedCheck_3789_; 
lean_del_object(v___x_3748_);
lean_dec(v_val_3746_);
lean_del_object(v___x_3742_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3782_ = lean_ctor_get(v___x_3750_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v___x_3750_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3784_ = v___x_3750_;
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
else
{
lean_inc(v_a_3782_);
lean_dec(v___x_3750_);
v___x_3784_ = lean_box(0);
v_isShared_3785_ = v_isSharedCheck_3789_;
goto v_resetjp_3783_;
}
v_resetjp_3783_:
{
lean_object* v___x_3787_; 
if (v_isShared_3785_ == 0)
{
v___x_3787_ = v___x_3784_;
goto v_reusejp_3786_;
}
else
{
lean_object* v_reuseFailAlloc_3788_; 
v_reuseFailAlloc_3788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3788_, 0, v_a_3782_);
v___x_3787_ = v_reuseFailAlloc_3788_;
goto v_reusejp_3786_;
}
v_reusejp_3786_:
{
return v___x_3787_;
}
}
}
}
}
else
{
lean_dec(v_a_3745_);
lean_del_object(v___x_3742_);
v___y_3602_ = v___y_3145_;
v___y_3603_ = v___y_3146_;
v___y_3604_ = v___y_3147_;
v___y_3605_ = v___y_3148_;
goto v___jp_3601_;
}
}
else
{
lean_object* v_a_3791_; lean_object* v___x_3793_; uint8_t v_isShared_3794_; uint8_t v_isSharedCheck_3798_; 
lean_del_object(v___x_3742_);
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3791_ = lean_ctor_get(v___x_3744_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v___x_3744_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3793_ = v___x_3744_;
v_isShared_3794_ = v_isSharedCheck_3798_;
goto v_resetjp_3792_;
}
else
{
lean_inc(v_a_3791_);
lean_dec(v___x_3744_);
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
}
else
{
lean_dec(v_a_3739_);
v___y_3602_ = v___y_3145_;
v___y_3603_ = v___y_3146_;
v___y_3604_ = v___y_3147_;
v___y_3605_ = v___y_3148_;
goto v___jp_3601_;
}
}
else
{
lean_object* v_a_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3807_; 
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3800_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3802_ = v___x_3738_;
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_a_3800_);
lean_dec(v___x_3738_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3807_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v___x_3805_; 
if (v_isShared_3803_ == 0)
{
v___x_3805_ = v___x_3802_;
goto v_reusejp_3804_;
}
else
{
lean_object* v_reuseFailAlloc_3806_; 
v_reuseFailAlloc_3806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3800_);
v___x_3805_ = v_reuseFailAlloc_3806_;
goto v_reusejp_3804_;
}
v_reusejp_3804_:
{
return v___x_3805_;
}
}
}
v___jp_3292_:
{
uint8_t v_genDiseq_3299_; 
v_genDiseq_3299_ = lean_ctor_get_uint8(v_config_3139_, sizeof(void*)*1 + 2);
if (v_genDiseq_3299_ == 0)
{
lean_dec_ref(v___x_3291_);
v___y_3269_ = v___y_3295_;
v___y_3270_ = v___y_3296_;
v___y_3271_ = v___y_3293_;
v___y_3272_ = v___y_3294_;
v___y_3273_ = v___y_3297_;
v___y_3274_ = v___y_3298_;
v___y_3275_ = v___x_3246_;
goto v___jp_3268_;
}
else
{
uint8_t v___x_3300_; 
v___x_3300_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3291_);
v___y_3269_ = v___y_3295_;
v___y_3270_ = v___y_3296_;
v___y_3271_ = v___y_3293_;
v___y_3272_ = v___y_3294_;
v___y_3273_ = v___y_3297_;
v___y_3274_ = v___y_3298_;
v___y_3275_ = v___x_3300_;
goto v___jp_3268_;
}
}
v___jp_3301_:
{
if (v___y_3309_ == 0)
{
lean_dec_ref(v___y_3307_);
v___y_3293_ = v___y_3303_;
v___y_3294_ = v___y_3304_;
v___y_3295_ = v___y_3302_;
v___y_3296_ = v___y_3305_;
v___y_3297_ = v___y_3306_;
v___y_3298_ = v___y_3308_;
goto v___jp_3292_;
}
else
{
lean_object* v___x_3310_; 
lean_dec_ref(v___x_3291_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v___x_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3310_, 0, v___y_3307_);
return v___x_3310_;
}
}
v___jp_3311_:
{
uint8_t v___x_3319_; 
v___x_3319_ = l_Lean_Exception_isInterrupt(v_a_3318_);
if (v___x_3319_ == 0)
{
uint8_t v___x_3320_; 
lean_inc_ref(v_a_3318_);
v___x_3320_ = l_Lean_Exception_isRuntime(v_a_3318_);
v___y_3302_ = v___y_3312_;
v___y_3303_ = v___y_3313_;
v___y_3304_ = v___y_3315_;
v___y_3305_ = v___y_3314_;
v___y_3306_ = v___y_3316_;
v___y_3307_ = v_a_3318_;
v___y_3308_ = v___y_3317_;
v___y_3309_ = v___x_3320_;
goto v___jp_3301_;
}
else
{
v___y_3302_ = v___y_3312_;
v___y_3303_ = v___y_3313_;
v___y_3304_ = v___y_3315_;
v___y_3305_ = v___y_3314_;
v___y_3306_ = v___y_3316_;
v___y_3307_ = v_a_3318_;
v___y_3308_ = v___y_3317_;
v___y_3309_ = v___x_3319_;
goto v___jp_3301_;
}
}
v___jp_3321_:
{
lean_object* v___x_3328_; 
lean_inc_ref(v___x_3291_);
v___x_3328_ = l_Lean_Meta_mkDecide(v___x_3291_, v___y_3322_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v_a_3329_; lean_object* v_keyedConfig_3330_; uint8_t v_trackZetaDelta_3331_; lean_object* v_zetaDeltaSet_3332_; lean_object* v_lctx_3333_; lean_object* v_localInstances_3334_; lean_object* v_defEqCtx_x3f_3335_; lean_object* v_synthPendingDepth_3336_; lean_object* v_customCanUnfoldPredicate_x3f_3337_; uint8_t v_univApprox_3338_; uint8_t v_inTypeClassResolution_3339_; uint8_t v_cacheInferType_3340_; uint8_t v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_a_3329_ = lean_ctor_get(v___x_3328_, 0);
lean_inc_n(v_a_3329_, 2);
lean_dec_ref_known(v___x_3328_, 1);
v_keyedConfig_3330_ = lean_ctor_get(v___y_3322_, 0);
v_trackZetaDelta_3331_ = lean_ctor_get_uint8(v___y_3322_, sizeof(void*)*7);
v_zetaDeltaSet_3332_ = lean_ctor_get(v___y_3322_, 1);
v_lctx_3333_ = lean_ctor_get(v___y_3322_, 2);
v_localInstances_3334_ = lean_ctor_get(v___y_3322_, 3);
v_defEqCtx_x3f_3335_ = lean_ctor_get(v___y_3322_, 4);
v_synthPendingDepth_3336_ = lean_ctor_get(v___y_3322_, 5);
v_customCanUnfoldPredicate_x3f_3337_ = lean_ctor_get(v___y_3322_, 6);
v_univApprox_3338_ = lean_ctor_get_uint8(v___y_3322_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3339_ = lean_ctor_get_uint8(v___y_3322_, sizeof(void*)*7 + 2);
v_cacheInferType_3340_ = lean_ctor_get_uint8(v___y_3322_, sizeof(void*)*7 + 3);
v___x_3341_ = 1;
lean_inc_ref(v_keyedConfig_3330_);
v___x_3342_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3341_, v_keyedConfig_3330_);
lean_inc(v_customCanUnfoldPredicate_x3f_3337_);
lean_inc(v_synthPendingDepth_3336_);
lean_inc(v_defEqCtx_x3f_3335_);
lean_inc_ref(v_localInstances_3334_);
lean_inc_ref(v_lctx_3333_);
lean_inc(v_zetaDeltaSet_3332_);
v___x_3343_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3343_, 0, v___x_3342_);
lean_ctor_set(v___x_3343_, 1, v_zetaDeltaSet_3332_);
lean_ctor_set(v___x_3343_, 2, v_lctx_3333_);
lean_ctor_set(v___x_3343_, 3, v_localInstances_3334_);
lean_ctor_set(v___x_3343_, 4, v_defEqCtx_x3f_3335_);
lean_ctor_set(v___x_3343_, 5, v_synthPendingDepth_3336_);
lean_ctor_set(v___x_3343_, 6, v_customCanUnfoldPredicate_x3f_3337_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7, v_trackZetaDelta_3331_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7 + 1, v_univApprox_3338_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3339_);
lean_ctor_set_uint8(v___x_3343_, sizeof(void*)*7 + 3, v_cacheInferType_3340_);
lean_inc(v___y_3327_);
lean_inc_ref(v___y_3326_);
lean_inc(v___y_3325_);
v___x_3344_ = lean_whnf(v_a_3329_, v___x_3343_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v_a_3345_; lean_object* v___x_3346_; uint8_t v___x_3347_; 
v_a_3345_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3345_);
lean_dec_ref_known(v___x_3344_, 1);
v___x_3346_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3347_ = l_Lean_Expr_isConstOf(v_a_3345_, v___x_3346_);
lean_dec(v_a_3345_);
if (v___x_3347_ == 0)
{
lean_dec(v_a_3329_);
v___y_3293_ = v___y_3323_;
v___y_3294_ = v___y_3324_;
v___y_3295_ = v___y_3322_;
v___y_3296_ = v___y_3325_;
v___y_3297_ = v___y_3326_;
v___y_3298_ = v___y_3327_;
goto v___jp_3292_;
}
else
{
lean_object* v___x_3348_; 
lean_inc(v_a_3329_);
v___x_3348_ = l_Lean_Meta_mkEqRefl(v_a_3329_, v___y_3322_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3348_) == 0)
{
lean_object* v_a_3349_; lean_object* v___x_3350_; 
v_a_3349_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3349_);
lean_dec_ref_known(v___x_3348_, 1);
lean_inc(v_mvarId_3140_);
v___x_3350_ = l_Lean_MVarId_getType(v_mvarId_3140_, v___y_3322_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; lean_object* v_nargs_3352_; lean_object* v___x_3353_; lean_object* v_dummy_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
v_nargs_3352_ = l_Lean_Expr_getAppNumArgs(v_a_3329_);
v___x_3353_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3354_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_3352_);
v___x_3355_ = lean_mk_array(v_nargs_3352_, v_dummy_3354_);
v___x_3356_ = lean_unsigned_to_nat(1u);
v___x_3357_ = lean_nat_sub(v_nargs_3352_, v___x_3356_);
lean_dec(v_nargs_3352_);
v___x_3358_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3329_, v___x_3355_, v___x_3357_);
v___x_3359_ = lean_array_push(v___x_3358_, v_a_3349_);
v___x_3360_ = l_Lean_mkAppN(v___x_3353_, v___x_3359_);
lean_dec_ref(v___x_3359_);
lean_inc(v_val_3171_);
v___x_3361_ = l_Lean_LocalDecl_toExpr(v_val_3171_);
v___x_3362_ = l_Lean_Meta_mkAbsurd(v_a_3351_, v___x_3361_, v___x_3360_, v___y_3322_, v___y_3325_, v___y_3326_, v___y_3327_);
if (lean_obj_tag(v___x_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3365_; uint8_t v_isShared_3366_; uint8_t v_isSharedCheck_3382_; 
v_a_3363_ = lean_ctor_get(v___x_3362_, 0);
v_isSharedCheck_3382_ = !lean_is_exclusive(v___x_3362_);
if (v_isSharedCheck_3382_ == 0)
{
v___x_3365_ = v___x_3362_;
v_isShared_3366_ = v_isSharedCheck_3382_;
goto v_resetjp_3364_;
}
else
{
lean_inc(v_a_3363_);
lean_dec(v___x_3362_);
v___x_3365_ = lean_box(0);
v_isShared_3366_ = v_isSharedCheck_3382_;
goto v_resetjp_3364_;
}
v_resetjp_3364_:
{
lean_object* v___x_3367_; 
lean_inc(v_mvarId_3140_);
v___x_3367_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3140_, v_a_3363_, v___y_3325_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v___x_3369_; uint8_t v_isShared_3370_; uint8_t v_isSharedCheck_3379_; 
lean_dec_ref(v___x_3291_);
lean_dec(v_val_3171_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_isSharedCheck_3379_ = !lean_is_exclusive(v___x_3367_);
if (v_isSharedCheck_3379_ == 0)
{
lean_object* v_unused_3380_; 
v_unused_3380_ = lean_ctor_get(v___x_3367_, 0);
lean_dec(v_unused_3380_);
v___x_3369_ = v___x_3367_;
v_isShared_3370_ = v_isSharedCheck_3379_;
goto v_resetjp_3368_;
}
else
{
lean_dec(v___x_3367_);
v___x_3369_ = lean_box(0);
v_isShared_3370_ = v_isSharedCheck_3379_;
goto v_resetjp_3368_;
}
v_resetjp_3368_:
{
lean_object* v___x_3371_; lean_object* v___x_3373_; 
v___x_3371_ = lean_box(v___x_3150_);
if (v_isShared_3370_ == 0)
{
lean_ctor_set_tag(v___x_3369_, 1);
lean_ctor_set(v___x_3369_, 0, v___x_3371_);
v___x_3373_ = v___x_3369_;
goto v_reusejp_3372_;
}
else
{
lean_object* v_reuseFailAlloc_3378_; 
v_reuseFailAlloc_3378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3378_, 0, v___x_3371_);
v___x_3373_ = v_reuseFailAlloc_3378_;
goto v_reusejp_3372_;
}
v_reusejp_3372_:
{
lean_object* v___x_3374_; lean_object* v___x_3376_; 
v___x_3374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v___x_3175_);
if (v_isShared_3366_ == 0)
{
lean_ctor_set(v___x_3365_, 0, v___x_3374_);
v___x_3376_ = v___x_3365_;
goto v_reusejp_3375_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3374_);
v___x_3376_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3375_;
}
v_reusejp_3375_:
{
v_a_3157_ = v___x_3376_;
goto v___jp_3156_;
}
}
}
}
else
{
lean_object* v_a_3381_; 
lean_del_object(v___x_3365_);
v_a_3381_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3381_);
lean_dec_ref_known(v___x_3367_, 1);
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3325_;
v___y_3315_ = v___y_3324_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v_a_3318_ = v_a_3381_;
goto v___jp_3311_;
}
}
}
else
{
lean_object* v_a_3383_; 
v_a_3383_ = lean_ctor_get(v___x_3362_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3362_, 1);
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3325_;
v___y_3315_ = v___y_3324_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v_a_3318_ = v_a_3383_;
goto v___jp_3311_;
}
}
else
{
lean_object* v_a_3384_; 
lean_dec(v_a_3349_);
lean_dec(v_a_3329_);
v_a_3384_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3350_, 1);
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3325_;
v___y_3315_ = v___y_3324_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v_a_3318_ = v_a_3384_;
goto v___jp_3311_;
}
}
else
{
lean_object* v_a_3385_; 
lean_dec(v_a_3329_);
v_a_3385_ = lean_ctor_get(v___x_3348_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3348_, 1);
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3325_;
v___y_3315_ = v___y_3324_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v_a_3318_ = v_a_3385_;
goto v___jp_3311_;
}
}
}
else
{
lean_object* v_a_3386_; 
lean_dec(v_a_3329_);
v_a_3386_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3344_, 1);
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3325_;
v___y_3315_ = v___y_3324_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v_a_3318_ = v_a_3386_;
goto v___jp_3311_;
}
}
else
{
lean_object* v_a_3387_; 
v_a_3387_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3328_, 1);
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3325_;
v___y_3315_ = v___y_3324_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v_a_3318_ = v_a_3387_;
goto v___jp_3311_;
}
}
v___jp_3388_:
{
if (v___y_3395_ == 0)
{
v___y_3293_ = v___y_3390_;
v___y_3294_ = v___y_3391_;
v___y_3295_ = v___y_3389_;
v___y_3296_ = v___y_3392_;
v___y_3297_ = v___y_3393_;
v___y_3298_ = v___y_3394_;
goto v___jp_3292_;
}
else
{
v___y_3322_ = v___y_3389_;
v___y_3323_ = v___y_3390_;
v___y_3324_ = v___y_3391_;
v___y_3325_ = v___y_3392_;
v___y_3326_ = v___y_3393_;
v___y_3327_ = v___y_3394_;
goto v___jp_3321_;
}
}
v___jp_3396_:
{
if (v___y_3404_ == 0)
{
lean_dec_ref(v___y_3402_);
v___y_3389_ = v___y_3397_;
v___y_3390_ = v___y_3398_;
v___y_3391_ = v___y_3400_;
v___y_3392_ = v___y_3399_;
v___y_3393_ = v___y_3401_;
v___y_3394_ = v___y_3403_;
v___y_3395_ = v___x_3246_;
goto v___jp_3388_;
}
else
{
uint8_t v___x_3405_; 
v___x_3405_ = l_Lean_Expr_hasFVar(v___y_3402_);
lean_dec_ref(v___y_3402_);
if (v___x_3405_ == 0)
{
v___y_3322_ = v___y_3397_;
v___y_3323_ = v___y_3398_;
v___y_3324_ = v___y_3400_;
v___y_3325_ = v___y_3399_;
v___y_3326_ = v___y_3401_;
v___y_3327_ = v___y_3403_;
goto v___jp_3321_;
}
else
{
v___y_3389_ = v___y_3397_;
v___y_3390_ = v___y_3398_;
v___y_3391_ = v___y_3400_;
v___y_3392_ = v___y_3399_;
v___y_3393_ = v___y_3401_;
v___y_3394_ = v___y_3403_;
v___y_3395_ = v___x_3246_;
goto v___jp_3388_;
}
}
}
v___jp_3406_:
{
lean_object* v___x_3414_; 
lean_inc_ref(v___x_3291_);
v___x_3414_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3291_, v___y_3410_);
if (lean_obj_tag(v___x_3414_) == 0)
{
lean_object* v_a_3415_; uint8_t v___x_3416_; 
v_a_3415_ = lean_ctor_get(v___x_3414_, 0);
lean_inc(v_a_3415_);
lean_dec_ref_known(v___x_3414_, 1);
v___x_3416_ = l_Lean_Expr_hasMVar(v_a_3415_);
if (v___x_3416_ == 0)
{
v___y_3397_ = v___y_3407_;
v___y_3398_ = v___y_3408_;
v___y_3399_ = v___y_3410_;
v___y_3400_ = v___y_3409_;
v___y_3401_ = v___y_3411_;
v___y_3402_ = v_a_3415_;
v___y_3403_ = v___y_3412_;
v___y_3404_ = v___y_3413_;
goto v___jp_3396_;
}
else
{
v___y_3397_ = v___y_3407_;
v___y_3398_ = v___y_3408_;
v___y_3399_ = v___y_3410_;
v___y_3400_ = v___y_3409_;
v___y_3401_ = v___y_3411_;
v___y_3402_ = v_a_3415_;
v___y_3403_ = v___y_3412_;
v___y_3404_ = v___x_3246_;
goto v___jp_3396_;
}
}
else
{
lean_object* v_a_3417_; lean_object* v___x_3419_; uint8_t v_isShared_3420_; uint8_t v_isSharedCheck_3424_; 
lean_dec_ref(v___x_3291_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3417_ = lean_ctor_get(v___x_3414_, 0);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3419_ = v___x_3414_;
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
else
{
lean_inc(v_a_3417_);
lean_dec(v___x_3414_);
v___x_3419_ = lean_box(0);
v_isShared_3420_ = v_isSharedCheck_3424_;
goto v_resetjp_3418_;
}
v_resetjp_3418_:
{
lean_object* v___x_3422_; 
if (v_isShared_3420_ == 0)
{
v___x_3422_ = v___x_3419_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v_a_3417_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
}
v___jp_3425_:
{
if (v___y_3432_ == 0)
{
v___y_3293_ = v___y_3427_;
v___y_3294_ = v___y_3428_;
v___y_3295_ = v___y_3426_;
v___y_3296_ = v___y_3429_;
v___y_3297_ = v___y_3430_;
v___y_3298_ = v___y_3431_;
goto v___jp_3292_;
}
else
{
v___y_3407_ = v___y_3426_;
v___y_3408_ = v___y_3427_;
v___y_3409_ = v___y_3428_;
v___y_3410_ = v___y_3429_;
v___y_3411_ = v___y_3430_;
v___y_3412_ = v___y_3431_;
v___y_3413_ = v___y_3432_;
goto v___jp_3406_;
}
}
v___jp_3433_:
{
uint8_t v_useDecide_3440_; 
v_useDecide_3440_ = lean_ctor_get_uint8(v_config_3139_, sizeof(void*)*1);
if (v_useDecide_3440_ == 0)
{
v___y_3426_ = v___y_3436_;
v___y_3427_ = v___y_3434_;
v___y_3428_ = v_isHEq_3435_;
v___y_3429_ = v___y_3437_;
v___y_3430_ = v___y_3438_;
v___y_3431_ = v___y_3439_;
v___y_3432_ = v___x_3246_;
goto v___jp_3425_;
}
else
{
uint8_t v___x_3441_; 
v___x_3441_ = l_Lean_Expr_hasFVar(v___x_3291_);
if (v___x_3441_ == 0)
{
v___y_3407_ = v___y_3436_;
v___y_3408_ = v___y_3434_;
v___y_3409_ = v_isHEq_3435_;
v___y_3410_ = v___y_3437_;
v___y_3411_ = v___y_3438_;
v___y_3412_ = v___y_3439_;
v___y_3413_ = v_useDecide_3440_;
goto v___jp_3406_;
}
else
{
v___y_3426_ = v___y_3436_;
v___y_3427_ = v___y_3434_;
v___y_3428_ = v_isHEq_3435_;
v___y_3429_ = v___y_3437_;
v___y_3430_ = v___y_3438_;
v___y_3431_ = v___y_3439_;
v___y_3432_ = v___x_3246_;
goto v___jp_3425_;
}
}
}
v___jp_3442_:
{
lean_object* v___x_3450_; 
v___x_3450_ = l_Lean_Meta_isExprDefEq(v___y_3443_, v___y_3449_, v___y_3444_, v___y_3446_, v___y_3448_, v___y_3447_);
if (lean_obj_tag(v___x_3450_) == 0)
{
lean_object* v_a_3451_; uint8_t v___x_3452_; 
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
lean_inc(v_a_3451_);
lean_dec_ref_known(v___x_3450_, 1);
v___x_3452_ = lean_unbox(v_a_3451_);
lean_dec(v_a_3451_);
if (v___x_3452_ == 0)
{
v___y_3434_ = v___y_3445_;
v_isHEq_3435_ = v___x_3150_;
v___y_3436_ = v___y_3444_;
v___y_3437_ = v___y_3446_;
v___y_3438_ = v___y_3448_;
v___y_3439_ = v___y_3447_;
goto v___jp_3433_;
}
else
{
lean_object* v___x_3453_; 
lean_dec_ref(v___x_3291_);
lean_dec_ref(v_config_3139_);
lean_inc(v_mvarId_3140_);
v___x_3453_ = l_Lean_MVarId_getType(v_mvarId_3140_, v___y_3444_, v___y_3446_, v___y_3448_, v___y_3447_);
if (lean_obj_tag(v___x_3453_) == 0)
{
lean_object* v_a_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v_a_3454_ = lean_ctor_get(v___x_3453_, 0);
lean_inc(v_a_3454_);
lean_dec_ref_known(v___x_3453_, 1);
v___x_3455_ = l_Lean_LocalDecl_toExpr(v_val_3171_);
v___x_3456_ = l_Lean_Meta_mkEqOfHEq(v___x_3455_, v___x_3150_, v___y_3444_, v___y_3446_, v___y_3448_, v___y_3447_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3458_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
lean_inc(v_a_3457_);
lean_dec_ref_known(v___x_3456_, 1);
v___x_3458_ = l_Lean_Meta_mkNoConfusion(v_a_3454_, v_a_3457_, v___y_3444_, v___y_3446_, v___y_3448_, v___y_3447_);
if (lean_obj_tag(v___x_3458_) == 0)
{
lean_object* v_a_3459_; lean_object* v___x_3460_; 
v_a_3459_ = lean_ctor_get(v___x_3458_, 0);
lean_inc(v_a_3459_);
lean_dec_ref_known(v___x_3458_, 1);
v___x_3460_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3140_, v_a_3459_, v___y_3446_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; 
lean_dec_ref_known(v___x_3460_, 1);
v___x_3461_ = lean_box(v___x_3150_);
v___x_3462_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
v___x_3463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
lean_ctor_set(v___x_3463_, 1, v___x_3175_);
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
v_a_3157_ = v___x_3464_;
goto v___jp_3156_;
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
v_a_3465_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3460_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3460_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
else
{
lean_object* v_a_3473_; lean_object* v___x_3475_; uint8_t v_isShared_3476_; uint8_t v_isSharedCheck_3480_; 
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3473_ = lean_ctor_get(v___x_3458_, 0);
v_isSharedCheck_3480_ = !lean_is_exclusive(v___x_3458_);
if (v_isSharedCheck_3480_ == 0)
{
v___x_3475_ = v___x_3458_;
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
else
{
lean_inc(v_a_3473_);
lean_dec(v___x_3458_);
v___x_3475_ = lean_box(0);
v_isShared_3476_ = v_isSharedCheck_3480_;
goto v_resetjp_3474_;
}
v_resetjp_3474_:
{
lean_object* v___x_3478_; 
if (v_isShared_3476_ == 0)
{
v___x_3478_ = v___x_3475_;
goto v_reusejp_3477_;
}
else
{
lean_object* v_reuseFailAlloc_3479_; 
v_reuseFailAlloc_3479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3479_, 0, v_a_3473_);
v___x_3478_ = v_reuseFailAlloc_3479_;
goto v_reusejp_3477_;
}
v_reusejp_3477_:
{
return v___x_3478_;
}
}
}
}
else
{
lean_object* v_a_3481_; lean_object* v___x_3483_; uint8_t v_isShared_3484_; uint8_t v_isSharedCheck_3488_; 
lean_dec(v_a_3454_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3481_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3488_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3488_ == 0)
{
v___x_3483_ = v___x_3456_;
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
else
{
lean_inc(v_a_3481_);
lean_dec(v___x_3456_);
v___x_3483_ = lean_box(0);
v_isShared_3484_ = v_isSharedCheck_3488_;
goto v_resetjp_3482_;
}
v_resetjp_3482_:
{
lean_object* v___x_3486_; 
if (v_isShared_3484_ == 0)
{
v___x_3486_ = v___x_3483_;
goto v_reusejp_3485_;
}
else
{
lean_object* v_reuseFailAlloc_3487_; 
v_reuseFailAlloc_3487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3487_, 0, v_a_3481_);
v___x_3486_ = v_reuseFailAlloc_3487_;
goto v_reusejp_3485_;
}
v_reusejp_3485_:
{
return v___x_3486_;
}
}
}
}
else
{
lean_object* v_a_3489_; lean_object* v___x_3491_; uint8_t v_isShared_3492_; uint8_t v_isSharedCheck_3496_; 
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3489_ = lean_ctor_get(v___x_3453_, 0);
v_isSharedCheck_3496_ = !lean_is_exclusive(v___x_3453_);
if (v_isSharedCheck_3496_ == 0)
{
v___x_3491_ = v___x_3453_;
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
else
{
lean_inc(v_a_3489_);
lean_dec(v___x_3453_);
v___x_3491_ = lean_box(0);
v_isShared_3492_ = v_isSharedCheck_3496_;
goto v_resetjp_3490_;
}
v_resetjp_3490_:
{
lean_object* v___x_3494_; 
if (v_isShared_3492_ == 0)
{
v___x_3494_ = v___x_3491_;
goto v_reusejp_3493_;
}
else
{
lean_object* v_reuseFailAlloc_3495_; 
v_reuseFailAlloc_3495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3495_, 0, v_a_3489_);
v___x_3494_ = v_reuseFailAlloc_3495_;
goto v_reusejp_3493_;
}
v_reusejp_3493_:
{
return v___x_3494_;
}
}
}
}
}
else
{
lean_object* v_a_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3504_; 
lean_dec_ref(v___x_3291_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3497_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3504_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3504_ == 0)
{
v___x_3499_ = v___x_3450_;
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_a_3497_);
lean_dec(v___x_3450_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3504_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v___x_3502_; 
if (v_isShared_3500_ == 0)
{
v___x_3502_ = v___x_3499_;
goto v_reusejp_3501_;
}
else
{
lean_object* v_reuseFailAlloc_3503_; 
v_reuseFailAlloc_3503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
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
v___jp_3505_:
{
lean_object* v___x_3511_; 
lean_inc_ref(v___x_3291_);
v___x_3511_ = l_Lean_Meta_matchHEq_x3f(v___x_3291_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3511_) == 0)
{
lean_object* v_a_3512_; 
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
lean_inc(v_a_3512_);
lean_dec_ref_known(v___x_3511_, 1);
if (lean_obj_tag(v_a_3512_) == 1)
{
lean_object* v_val_3513_; lean_object* v_snd_3514_; lean_object* v_snd_3515_; lean_object* v_fst_3516_; lean_object* v_fst_3517_; lean_object* v_fst_3518_; lean_object* v_snd_3519_; lean_object* v___x_3520_; 
v_val_3513_ = lean_ctor_get(v_a_3512_, 0);
lean_inc(v_val_3513_);
lean_dec_ref_known(v_a_3512_, 1);
v_snd_3514_ = lean_ctor_get(v_val_3513_, 1);
lean_inc(v_snd_3514_);
v_snd_3515_ = lean_ctor_get(v_snd_3514_, 1);
lean_inc(v_snd_3515_);
v_fst_3516_ = lean_ctor_get(v_val_3513_, 0);
lean_inc(v_fst_3516_);
lean_dec(v_val_3513_);
v_fst_3517_ = lean_ctor_get(v_snd_3514_, 0);
lean_inc(v_fst_3517_);
lean_dec(v_snd_3514_);
v_fst_3518_ = lean_ctor_get(v_snd_3515_, 0);
lean_inc(v_fst_3518_);
v_snd_3519_ = lean_ctor_get(v_snd_3515_, 1);
lean_inc(v_snd_3519_);
lean_dec(v_snd_3515_);
v___x_3520_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3517_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3520_) == 0)
{
lean_object* v_a_3521_; 
v_a_3521_ = lean_ctor_get(v___x_3520_, 0);
lean_inc(v_a_3521_);
lean_dec_ref_known(v___x_3520_, 1);
if (lean_obj_tag(v_a_3521_) == 1)
{
lean_object* v_val_3522_; lean_object* v___x_3523_; 
v_val_3522_ = lean_ctor_get(v_a_3521_, 0);
lean_inc(v_val_3522_);
lean_dec_ref_known(v_a_3521_, 1);
v___x_3523_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3519_, v___y_3507_, v___y_3508_, v___y_3509_, v___y_3510_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
if (lean_obj_tag(v_a_3524_) == 1)
{
lean_object* v_toConstantVal_3525_; lean_object* v_val_3526_; lean_object* v_toConstantVal_3527_; lean_object* v_name_3528_; lean_object* v_name_3529_; uint8_t v___x_3530_; 
v_toConstantVal_3525_ = lean_ctor_get(v_val_3522_, 0);
lean_inc_ref(v_toConstantVal_3525_);
lean_dec(v_val_3522_);
v_val_3526_ = lean_ctor_get(v_a_3524_, 0);
lean_inc(v_val_3526_);
lean_dec_ref_known(v_a_3524_, 1);
v_toConstantVal_3527_ = lean_ctor_get(v_val_3526_, 0);
lean_inc_ref(v_toConstantVal_3527_);
lean_dec(v_val_3526_);
v_name_3528_ = lean_ctor_get(v_toConstantVal_3525_, 0);
lean_inc(v_name_3528_);
lean_dec_ref(v_toConstantVal_3525_);
v_name_3529_ = lean_ctor_get(v_toConstantVal_3527_, 0);
lean_inc(v_name_3529_);
lean_dec_ref(v_toConstantVal_3527_);
v___x_3530_ = lean_name_eq(v_name_3528_, v_name_3529_);
lean_dec(v_name_3529_);
lean_dec(v_name_3528_);
if (v___x_3530_ == 0)
{
v___y_3443_ = v_fst_3516_;
v___y_3444_ = v___y_3507_;
v___y_3445_ = v_isEq_3506_;
v___y_3446_ = v___y_3508_;
v___y_3447_ = v___y_3510_;
v___y_3448_ = v___y_3509_;
v___y_3449_ = v_fst_3518_;
goto v___jp_3442_;
}
else
{
if (v___x_3246_ == 0)
{
lean_dec(v_fst_3518_);
lean_dec(v_fst_3516_);
v___y_3434_ = v_isEq_3506_;
v_isHEq_3435_ = v___x_3150_;
v___y_3436_ = v___y_3507_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
v___y_3439_ = v___y_3510_;
goto v___jp_3433_;
}
else
{
v___y_3443_ = v_fst_3516_;
v___y_3444_ = v___y_3507_;
v___y_3445_ = v_isEq_3506_;
v___y_3446_ = v___y_3508_;
v___y_3447_ = v___y_3510_;
v___y_3448_ = v___y_3509_;
v___y_3449_ = v_fst_3518_;
goto v___jp_3442_;
}
}
}
else
{
lean_dec(v_a_3524_);
lean_dec(v_val_3522_);
lean_dec(v_fst_3518_);
lean_dec(v_fst_3516_);
v___y_3434_ = v_isEq_3506_;
v_isHEq_3435_ = v___x_3150_;
v___y_3436_ = v___y_3507_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
v___y_3439_ = v___y_3510_;
goto v___jp_3433_;
}
}
else
{
lean_object* v_a_3531_; lean_object* v___x_3533_; uint8_t v_isShared_3534_; uint8_t v_isSharedCheck_3538_; 
lean_dec(v_val_3522_);
lean_dec(v_fst_3518_);
lean_dec(v_fst_3516_);
lean_dec_ref(v___x_3291_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3531_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3538_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3538_ == 0)
{
v___x_3533_ = v___x_3523_;
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
else
{
lean_inc(v_a_3531_);
lean_dec(v___x_3523_);
v___x_3533_ = lean_box(0);
v_isShared_3534_ = v_isSharedCheck_3538_;
goto v_resetjp_3532_;
}
v_resetjp_3532_:
{
lean_object* v___x_3536_; 
if (v_isShared_3534_ == 0)
{
v___x_3536_ = v___x_3533_;
goto v_reusejp_3535_;
}
else
{
lean_object* v_reuseFailAlloc_3537_; 
v_reuseFailAlloc_3537_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3537_, 0, v_a_3531_);
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
lean_dec(v_a_3521_);
lean_dec(v_snd_3519_);
lean_dec(v_fst_3518_);
lean_dec(v_fst_3516_);
v___y_3434_ = v_isEq_3506_;
v_isHEq_3435_ = v___x_3150_;
v___y_3436_ = v___y_3507_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
v___y_3439_ = v___y_3510_;
goto v___jp_3433_;
}
}
else
{
lean_object* v_a_3539_; lean_object* v___x_3541_; uint8_t v_isShared_3542_; uint8_t v_isSharedCheck_3546_; 
lean_dec(v_snd_3519_);
lean_dec(v_fst_3518_);
lean_dec(v_fst_3516_);
lean_dec_ref(v___x_3291_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3539_ = lean_ctor_get(v___x_3520_, 0);
v_isSharedCheck_3546_ = !lean_is_exclusive(v___x_3520_);
if (v_isSharedCheck_3546_ == 0)
{
v___x_3541_ = v___x_3520_;
v_isShared_3542_ = v_isSharedCheck_3546_;
goto v_resetjp_3540_;
}
else
{
lean_inc(v_a_3539_);
lean_dec(v___x_3520_);
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
else
{
lean_dec(v_a_3512_);
v___y_3434_ = v_isEq_3506_;
v_isHEq_3435_ = v___x_3246_;
v___y_3436_ = v___y_3507_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
v___y_3439_ = v___y_3510_;
goto v___jp_3433_;
}
}
else
{
lean_object* v_a_3547_; lean_object* v___x_3549_; uint8_t v_isShared_3550_; uint8_t v_isSharedCheck_3554_; 
lean_dec_ref(v___x_3291_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3547_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3554_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3554_ == 0)
{
v___x_3549_ = v___x_3511_;
v_isShared_3550_ = v_isSharedCheck_3554_;
goto v_resetjp_3548_;
}
else
{
lean_inc(v_a_3547_);
lean_dec(v___x_3511_);
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
v___jp_3555_:
{
lean_object* v___x_3560_; 
lean_inc_ref(v___x_3291_);
v___x_3560_ = l_Lean_Meta_matchEq_x3f(v___x_3291_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
if (lean_obj_tag(v___x_3560_) == 0)
{
lean_object* v_a_3561_; 
v_a_3561_ = lean_ctor_get(v___x_3560_, 0);
lean_inc(v_a_3561_);
lean_dec_ref_known(v___x_3560_, 1);
if (lean_obj_tag(v_a_3561_) == 1)
{
lean_object* v_val_3562_; lean_object* v_snd_3563_; lean_object* v_fst_3564_; lean_object* v_snd_3565_; lean_object* v___x_3566_; 
v_val_3562_ = lean_ctor_get(v_a_3561_, 0);
lean_inc(v_val_3562_);
lean_dec_ref_known(v_a_3561_, 1);
v_snd_3563_ = lean_ctor_get(v_val_3562_, 1);
lean_inc(v_snd_3563_);
lean_dec(v_val_3562_);
v_fst_3564_ = lean_ctor_get(v_snd_3563_, 0);
lean_inc(v_fst_3564_);
v_snd_3565_ = lean_ctor_get(v_snd_3563_, 1);
lean_inc(v_snd_3565_);
lean_dec(v_snd_3563_);
v___x_3566_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3564_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
if (lean_obj_tag(v___x_3566_) == 0)
{
lean_object* v_a_3567_; 
v_a_3567_ = lean_ctor_get(v___x_3566_, 0);
lean_inc(v_a_3567_);
lean_dec_ref_known(v___x_3566_, 1);
if (lean_obj_tag(v_a_3567_) == 1)
{
lean_object* v_val_3568_; lean_object* v___x_3569_; 
v_val_3568_ = lean_ctor_get(v_a_3567_, 0);
lean_inc(v_val_3568_);
lean_dec_ref_known(v_a_3567_, 1);
v___x_3569_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3565_, v___y_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
if (lean_obj_tag(v___x_3569_) == 0)
{
lean_object* v_a_3570_; 
v_a_3570_ = lean_ctor_get(v___x_3569_, 0);
lean_inc(v_a_3570_);
lean_dec_ref_known(v___x_3569_, 1);
if (lean_obj_tag(v_a_3570_) == 1)
{
lean_object* v_toConstantVal_3571_; lean_object* v_val_3572_; lean_object* v_toConstantVal_3573_; lean_object* v_name_3574_; lean_object* v_name_3575_; uint8_t v___x_3576_; 
v_toConstantVal_3571_ = lean_ctor_get(v_val_3568_, 0);
lean_inc_ref(v_toConstantVal_3571_);
lean_dec(v_val_3568_);
v_val_3572_ = lean_ctor_get(v_a_3570_, 0);
lean_inc(v_val_3572_);
lean_dec_ref_known(v_a_3570_, 1);
v_toConstantVal_3573_ = lean_ctor_get(v_val_3572_, 0);
lean_inc_ref(v_toConstantVal_3573_);
lean_dec(v_val_3572_);
v_name_3574_ = lean_ctor_get(v_toConstantVal_3571_, 0);
lean_inc(v_name_3574_);
lean_dec_ref(v_toConstantVal_3571_);
v_name_3575_ = lean_ctor_get(v_toConstantVal_3573_, 0);
lean_inc(v_name_3575_);
lean_dec_ref(v_toConstantVal_3573_);
v___x_3576_ = lean_name_eq(v_name_3574_, v_name_3575_);
lean_dec(v_name_3575_);
lean_dec(v_name_3574_);
if (v___x_3576_ == 0)
{
lean_dec_ref(v___x_3291_);
lean_dec_ref(v_config_3139_);
v___y_3177_ = v___y_3558_;
v___y_3178_ = v___y_3556_;
v___y_3179_ = v___y_3557_;
v___y_3180_ = v___y_3559_;
goto v___jp_3176_;
}
else
{
if (v___x_3246_ == 0)
{
lean_del_object(v___x_3173_);
v_isEq_3506_ = v___x_3150_;
v___y_3507_ = v___y_3556_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
v___y_3510_ = v___y_3559_;
goto v___jp_3505_;
}
else
{
lean_dec_ref(v___x_3291_);
lean_dec_ref(v_config_3139_);
v___y_3177_ = v___y_3558_;
v___y_3178_ = v___y_3556_;
v___y_3179_ = v___y_3557_;
v___y_3180_ = v___y_3559_;
goto v___jp_3176_;
}
}
}
else
{
lean_dec(v_a_3570_);
lean_dec(v_val_3568_);
lean_del_object(v___x_3173_);
v_isEq_3506_ = v___x_3150_;
v___y_3507_ = v___y_3556_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
v___y_3510_ = v___y_3559_;
goto v___jp_3505_;
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_val_3568_);
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3577_ = lean_ctor_get(v___x_3569_, 0);
v_isSharedCheck_3584_ = !lean_is_exclusive(v___x_3569_);
if (v_isSharedCheck_3584_ == 0)
{
v___x_3579_ = v___x_3569_;
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
else
{
lean_inc(v_a_3577_);
lean_dec(v___x_3569_);
v___x_3579_ = lean_box(0);
v_isShared_3580_ = v_isSharedCheck_3584_;
goto v_resetjp_3578_;
}
v_resetjp_3578_:
{
lean_object* v___x_3582_; 
if (v_isShared_3580_ == 0)
{
v___x_3582_ = v___x_3579_;
goto v_reusejp_3581_;
}
else
{
lean_object* v_reuseFailAlloc_3583_; 
v_reuseFailAlloc_3583_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3583_, 0, v_a_3577_);
v___x_3582_ = v_reuseFailAlloc_3583_;
goto v_reusejp_3581_;
}
v_reusejp_3581_:
{
return v___x_3582_;
}
}
}
}
else
{
lean_dec(v_a_3567_);
lean_dec(v_snd_3565_);
lean_del_object(v___x_3173_);
v_isEq_3506_ = v___x_3150_;
v___y_3507_ = v___y_3556_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
v___y_3510_ = v___y_3559_;
goto v___jp_3505_;
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec(v_snd_3565_);
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3585_ = lean_ctor_get(v___x_3566_, 0);
v_isSharedCheck_3592_ = !lean_is_exclusive(v___x_3566_);
if (v_isSharedCheck_3592_ == 0)
{
v___x_3587_ = v___x_3566_;
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
else
{
lean_inc(v_a_3585_);
lean_dec(v___x_3566_);
v___x_3587_ = lean_box(0);
v_isShared_3588_ = v_isSharedCheck_3592_;
goto v_resetjp_3586_;
}
v_resetjp_3586_:
{
lean_object* v___x_3590_; 
if (v_isShared_3588_ == 0)
{
v___x_3590_ = v___x_3587_;
goto v_reusejp_3589_;
}
else
{
lean_object* v_reuseFailAlloc_3591_; 
v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
v___x_3590_ = v_reuseFailAlloc_3591_;
goto v_reusejp_3589_;
}
v_reusejp_3589_:
{
return v___x_3590_;
}
}
}
}
else
{
lean_dec(v_a_3561_);
lean_del_object(v___x_3173_);
v_isEq_3506_ = v___x_3246_;
v___y_3507_ = v___y_3556_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
v___y_3510_ = v___y_3559_;
goto v___jp_3505_;
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3593_ = lean_ctor_get(v___x_3560_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3560_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3560_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3560_);
v___x_3595_ = lean_box(0);
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
v_resetjp_3594_:
{
lean_object* v___x_3598_; 
if (v_isShared_3596_ == 0)
{
v___x_3598_ = v___x_3595_;
goto v_reusejp_3597_;
}
else
{
lean_object* v_reuseFailAlloc_3599_; 
v_reuseFailAlloc_3599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3599_, 0, v_a_3593_);
v___x_3598_ = v_reuseFailAlloc_3599_;
goto v_reusejp_3597_;
}
v_reusejp_3597_:
{
return v___x_3598_;
}
}
}
}
v___jp_3601_:
{
lean_object* v___x_3606_; 
lean_inc_ref(v___x_3291_);
v___x_3606_ = l_Lean_refutableHasNotBit_x3f(v___x_3291_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
if (lean_obj_tag(v_a_3607_) == 1)
{
lean_object* v_val_3608_; lean_object* v___x_3610_; uint8_t v_isShared_3611_; uint8_t v_isSharedCheck_3648_; 
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec_ref(v_config_3139_);
v_val_3608_ = lean_ctor_get(v_a_3607_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v_a_3607_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3610_ = v_a_3607_;
v_isShared_3611_ = v_isSharedCheck_3648_;
goto v_resetjp_3609_;
}
else
{
lean_inc(v_val_3608_);
lean_dec(v_a_3607_);
v___x_3610_ = lean_box(0);
v_isShared_3611_ = v_isSharedCheck_3648_;
goto v_resetjp_3609_;
}
v_resetjp_3609_:
{
lean_object* v___x_3612_; 
lean_inc(v_mvarId_3140_);
v___x_3612_ = l_Lean_MVarId_getType(v_mvarId_3140_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
v___x_3614_ = l_Lean_LocalDecl_toExpr(v_val_3171_);
v___x_3615_ = l_Lean_Meta_mkAbsurd(v_a_3613_, v_val_3608_, v___x_3614_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; lean_object* v___x_3617_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
v___x_3617_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3140_, v_a_3616_, v___y_3603_);
if (lean_obj_tag(v___x_3617_) == 0)
{
lean_object* v___x_3618_; lean_object* v___x_3620_; 
lean_dec_ref_known(v___x_3617_, 1);
v___x_3618_ = lean_box(v___x_3150_);
if (v_isShared_3611_ == 0)
{
lean_ctor_set(v___x_3610_, 0, v___x_3618_);
v___x_3620_ = v___x_3610_;
goto v_reusejp_3619_;
}
else
{
lean_object* v_reuseFailAlloc_3623_; 
v_reuseFailAlloc_3623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3623_, 0, v___x_3618_);
v___x_3620_ = v_reuseFailAlloc_3623_;
goto v_reusejp_3619_;
}
v_reusejp_3619_:
{
lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
lean_ctor_set(v___x_3621_, 1, v___x_3175_);
v___x_3622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
v_a_3157_ = v___x_3622_;
goto v___jp_3156_;
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_del_object(v___x_3610_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
v_a_3624_ = lean_ctor_get(v___x_3617_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3617_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3617_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v___x_3629_; 
if (v_isShared_3627_ == 0)
{
v___x_3629_ = v___x_3626_;
goto v_reusejp_3628_;
}
else
{
lean_object* v_reuseFailAlloc_3630_; 
v_reuseFailAlloc_3630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3630_, 0, v_a_3624_);
v___x_3629_ = v_reuseFailAlloc_3630_;
goto v_reusejp_3628_;
}
v_reusejp_3628_:
{
return v___x_3629_;
}
}
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_del_object(v___x_3610_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3632_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3615_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3615_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v___x_3637_; 
if (v_isShared_3635_ == 0)
{
v___x_3637_ = v___x_3634_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3638_; 
v_reuseFailAlloc_3638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3638_, 0, v_a_3632_);
v___x_3637_ = v_reuseFailAlloc_3638_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
return v___x_3637_;
}
}
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_del_object(v___x_3610_);
lean_dec(v_val_3608_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3640_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3612_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3612_);
v___x_3642_ = lean_box(0);
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
v_resetjp_3641_:
{
lean_object* v___x_3645_; 
if (v_isShared_3643_ == 0)
{
v___x_3645_ = v___x_3642_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3646_; 
v_reuseFailAlloc_3646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3646_, 0, v_a_3640_);
v___x_3645_ = v_reuseFailAlloc_3646_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
return v___x_3645_;
}
}
}
}
}
else
{
lean_object* v___x_3649_; 
lean_dec(v_a_3607_);
lean_inc_ref(v___x_3291_);
v___x_3649_ = l_Lean_Meta_matchNe_x3f(v___x_3291_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3649_) == 0)
{
lean_object* v_a_3650_; 
v_a_3650_ = lean_ctor_get(v___x_3649_, 0);
lean_inc(v_a_3650_);
lean_dec_ref_known(v___x_3649_, 1);
if (lean_obj_tag(v_a_3650_) == 1)
{
lean_object* v_val_3651_; lean_object* v___x_3653_; uint8_t v_isShared_3654_; uint8_t v_isSharedCheck_3721_; 
v_val_3651_ = lean_ctor_get(v_a_3650_, 0);
v_isSharedCheck_3721_ = !lean_is_exclusive(v_a_3650_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3653_ = v_a_3650_;
v_isShared_3654_ = v_isSharedCheck_3721_;
goto v_resetjp_3652_;
}
else
{
lean_inc(v_val_3651_);
lean_dec(v_a_3650_);
v___x_3653_ = lean_box(0);
v_isShared_3654_ = v_isSharedCheck_3721_;
goto v_resetjp_3652_;
}
v_resetjp_3652_:
{
lean_object* v_snd_3655_; lean_object* v_fst_3656_; lean_object* v_snd_3657_; lean_object* v___x_3659_; uint8_t v_isShared_3660_; uint8_t v_isSharedCheck_3720_; 
v_snd_3655_ = lean_ctor_get(v_val_3651_, 1);
lean_inc(v_snd_3655_);
lean_dec(v_val_3651_);
v_fst_3656_ = lean_ctor_get(v_snd_3655_, 0);
v_snd_3657_ = lean_ctor_get(v_snd_3655_, 1);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_snd_3655_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3659_ = v_snd_3655_;
v_isShared_3660_ = v_isSharedCheck_3720_;
goto v_resetjp_3658_;
}
else
{
lean_inc(v_snd_3657_);
lean_inc(v_fst_3656_);
lean_dec(v_snd_3655_);
v___x_3659_ = lean_box(0);
v_isShared_3660_ = v_isSharedCheck_3720_;
goto v_resetjp_3658_;
}
v_resetjp_3658_:
{
lean_object* v___x_3661_; 
lean_inc(v_fst_3656_);
v___x_3661_ = l_Lean_Meta_isExprDefEq(v_fst_3656_, v_snd_3657_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; uint8_t v___x_3663_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
v___x_3663_ = lean_unbox(v_a_3662_);
lean_dec(v_a_3662_);
if (v___x_3663_ == 0)
{
lean_del_object(v___x_3659_);
lean_dec(v_fst_3656_);
lean_del_object(v___x_3653_);
v___y_3556_ = v___y_3602_;
v___y_3557_ = v___y_3603_;
v___y_3558_ = v___y_3604_;
v___y_3559_ = v___y_3605_;
goto v___jp_3555_;
}
else
{
lean_object* v___x_3664_; 
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec_ref(v_config_3139_);
lean_inc(v_mvarId_3140_);
v___x_3664_ = l_Lean_MVarId_getType(v_mvarId_3140_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v_a_3665_; lean_object* v___x_3666_; 
v_a_3665_ = lean_ctor_get(v___x_3664_, 0);
lean_inc(v_a_3665_);
lean_dec_ref_known(v___x_3664_, 1);
v___x_3666_ = l_Lean_Meta_mkEqRefl(v_fst_3656_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3666_) == 0)
{
lean_object* v_a_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; 
v_a_3667_ = lean_ctor_get(v___x_3666_, 0);
lean_inc(v_a_3667_);
lean_dec_ref_known(v___x_3666_, 1);
v___x_3668_ = l_Lean_LocalDecl_toExpr(v_val_3171_);
v___x_3669_ = l_Lean_Meta_mkAbsurd(v_a_3665_, v_a_3667_, v___x_3668_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3669_) == 0)
{
lean_object* v_a_3670_; lean_object* v___x_3671_; 
v_a_3670_ = lean_ctor_get(v___x_3669_, 0);
lean_inc(v_a_3670_);
lean_dec_ref_known(v___x_3669_, 1);
v___x_3671_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3140_, v_a_3670_, v___y_3603_);
if (lean_obj_tag(v___x_3671_) == 0)
{
lean_object* v___x_3672_; lean_object* v___x_3674_; 
lean_dec_ref_known(v___x_3671_, 1);
v___x_3672_ = lean_box(v___x_3150_);
if (v_isShared_3654_ == 0)
{
lean_ctor_set(v___x_3653_, 0, v___x_3672_);
v___x_3674_ = v___x_3653_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3672_);
v___x_3674_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
lean_object* v___x_3676_; 
if (v_isShared_3660_ == 0)
{
lean_ctor_set(v___x_3659_, 1, v___x_3175_);
lean_ctor_set(v___x_3659_, 0, v___x_3674_);
v___x_3676_ = v___x_3659_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3674_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v___x_3175_);
v___x_3676_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
lean_object* v___x_3677_; 
v___x_3677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3677_, 0, v___x_3676_);
v_a_3157_ = v___x_3677_;
goto v___jp_3156_;
}
}
}
else
{
lean_object* v_a_3680_; lean_object* v___x_3682_; uint8_t v_isShared_3683_; uint8_t v_isSharedCheck_3687_; 
lean_del_object(v___x_3659_);
lean_del_object(v___x_3653_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
v_a_3680_ = lean_ctor_get(v___x_3671_, 0);
v_isSharedCheck_3687_ = !lean_is_exclusive(v___x_3671_);
if (v_isSharedCheck_3687_ == 0)
{
v___x_3682_ = v___x_3671_;
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
else
{
lean_inc(v_a_3680_);
lean_dec(v___x_3671_);
v___x_3682_ = lean_box(0);
v_isShared_3683_ = v_isSharedCheck_3687_;
goto v_resetjp_3681_;
}
v_resetjp_3681_:
{
lean_object* v___x_3685_; 
if (v_isShared_3683_ == 0)
{
v___x_3685_ = v___x_3682_;
goto v_reusejp_3684_;
}
else
{
lean_object* v_reuseFailAlloc_3686_; 
v_reuseFailAlloc_3686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3686_, 0, v_a_3680_);
v___x_3685_ = v_reuseFailAlloc_3686_;
goto v_reusejp_3684_;
}
v_reusejp_3684_:
{
return v___x_3685_;
}
}
}
}
else
{
lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_del_object(v___x_3659_);
lean_del_object(v___x_3653_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3688_ = lean_ctor_get(v___x_3669_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3669_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3669_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_dec(v___x_3669_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3688_);
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
else
{
lean_object* v_a_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3703_; 
lean_dec(v_a_3665_);
lean_del_object(v___x_3659_);
lean_del_object(v___x_3653_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3696_ = lean_ctor_get(v___x_3666_, 0);
v_isSharedCheck_3703_ = !lean_is_exclusive(v___x_3666_);
if (v_isSharedCheck_3703_ == 0)
{
v___x_3698_ = v___x_3666_;
v_isShared_3699_ = v_isSharedCheck_3703_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_a_3696_);
lean_dec(v___x_3666_);
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
else
{
lean_object* v_a_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3711_; 
lean_del_object(v___x_3659_);
lean_dec(v_fst_3656_);
lean_del_object(v___x_3653_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3704_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3711_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3711_ == 0)
{
v___x_3706_ = v___x_3664_;
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_a_3704_);
lean_dec(v___x_3664_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3711_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3709_; 
if (v_isShared_3707_ == 0)
{
v___x_3709_ = v___x_3706_;
goto v_reusejp_3708_;
}
else
{
lean_object* v_reuseFailAlloc_3710_; 
v_reuseFailAlloc_3710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3710_, 0, v_a_3704_);
v___x_3709_ = v_reuseFailAlloc_3710_;
goto v_reusejp_3708_;
}
v_reusejp_3708_:
{
return v___x_3709_;
}
}
}
}
}
else
{
lean_object* v_a_3712_; lean_object* v___x_3714_; uint8_t v_isShared_3715_; uint8_t v_isSharedCheck_3719_; 
lean_del_object(v___x_3659_);
lean_dec(v_fst_3656_);
lean_del_object(v___x_3653_);
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3712_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3719_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3714_ = v___x_3661_;
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
else
{
lean_inc(v_a_3712_);
lean_dec(v___x_3661_);
v___x_3714_ = lean_box(0);
v_isShared_3715_ = v_isSharedCheck_3719_;
goto v_resetjp_3713_;
}
v_resetjp_3713_:
{
lean_object* v___x_3717_; 
if (v_isShared_3715_ == 0)
{
v___x_3717_ = v___x_3714_;
goto v_reusejp_3716_;
}
else
{
lean_object* v_reuseFailAlloc_3718_; 
v_reuseFailAlloc_3718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3718_, 0, v_a_3712_);
v___x_3717_ = v_reuseFailAlloc_3718_;
goto v_reusejp_3716_;
}
v_reusejp_3716_:
{
return v___x_3717_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3650_);
v___y_3556_ = v___y_3602_;
v___y_3557_ = v___y_3603_;
v___y_3558_ = v___y_3604_;
v___y_3559_ = v___y_3605_;
goto v___jp_3555_;
}
}
else
{
lean_object* v_a_3722_; lean_object* v___x_3724_; uint8_t v_isShared_3725_; uint8_t v_isSharedCheck_3729_; 
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3722_ = lean_ctor_get(v___x_3649_, 0);
v_isSharedCheck_3729_ = !lean_is_exclusive(v___x_3649_);
if (v_isSharedCheck_3729_ == 0)
{
v___x_3724_ = v___x_3649_;
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
else
{
lean_inc(v_a_3722_);
lean_dec(v___x_3649_);
v___x_3724_ = lean_box(0);
v_isShared_3725_ = v_isSharedCheck_3729_;
goto v_resetjp_3723_;
}
v_resetjp_3723_:
{
lean_object* v___x_3727_; 
if (v_isShared_3725_ == 0)
{
v___x_3727_ = v___x_3724_;
goto v_reusejp_3726_;
}
else
{
lean_object* v_reuseFailAlloc_3728_; 
v_reuseFailAlloc_3728_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3728_, 0, v_a_3722_);
v___x_3727_ = v_reuseFailAlloc_3728_;
goto v_reusejp_3726_;
}
v_reusejp_3726_:
{
return v___x_3727_;
}
}
}
}
}
else
{
lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec_ref(v___x_3291_);
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3730_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3606_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_dec(v___x_3606_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
}
else
{
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
v_a_3165_ = v___x_3217_;
goto v___jp_3164_;
}
v___jp_3176_:
{
lean_object* v___x_3181_; 
lean_inc(v_mvarId_3140_);
v___x_3181_ = l_Lean_MVarId_getType(v_mvarId_3140_, v___y_3178_, v___y_3179_, v___y_3177_, v___y_3180_);
if (lean_obj_tag(v___x_3181_) == 0)
{
lean_object* v_a_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; 
v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
lean_inc(v_a_3182_);
lean_dec_ref_known(v___x_3181_, 1);
v___x_3183_ = l_Lean_LocalDecl_toExpr(v_val_3171_);
v___x_3184_ = l_Lean_Meta_mkNoConfusion(v_a_3182_, v___x_3183_, v___y_3178_, v___y_3179_, v___y_3177_, v___y_3180_);
if (lean_obj_tag(v___x_3184_) == 0)
{
lean_object* v_a_3185_; lean_object* v___x_3186_; 
v_a_3185_ = lean_ctor_get(v___x_3184_, 0);
lean_inc(v_a_3185_);
lean_dec_ref_known(v___x_3184_, 1);
v___x_3186_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3140_, v_a_3185_, v___y_3179_);
if (lean_obj_tag(v___x_3186_) == 0)
{
lean_object* v___x_3187_; lean_object* v___x_3189_; 
lean_dec_ref_known(v___x_3186_, 1);
v___x_3187_ = lean_box(v___x_3150_);
if (v_isShared_3174_ == 0)
{
lean_ctor_set(v___x_3173_, 0, v___x_3187_);
v___x_3189_ = v___x_3173_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v___x_3187_);
v___x_3189_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
lean_ctor_set(v___x_3190_, 1, v___x_3175_);
v___x_3191_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
v_a_3157_ = v___x_3191_;
goto v___jp_3156_;
}
}
else
{
lean_object* v_a_3193_; lean_object* v___x_3195_; uint8_t v_isShared_3196_; uint8_t v_isSharedCheck_3200_; 
lean_del_object(v___x_3173_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
v_a_3193_ = lean_ctor_get(v___x_3186_, 0);
v_isSharedCheck_3200_ = !lean_is_exclusive(v___x_3186_);
if (v_isSharedCheck_3200_ == 0)
{
v___x_3195_ = v___x_3186_;
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
else
{
lean_inc(v_a_3193_);
lean_dec(v___x_3186_);
v___x_3195_ = lean_box(0);
v_isShared_3196_ = v_isSharedCheck_3200_;
goto v_resetjp_3194_;
}
v_resetjp_3194_:
{
lean_object* v___x_3198_; 
if (v_isShared_3196_ == 0)
{
v___x_3198_ = v___x_3195_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3199_; 
v_reuseFailAlloc_3199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3199_, 0, v_a_3193_);
v___x_3198_ = v_reuseFailAlloc_3199_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
return v___x_3198_;
}
}
}
}
else
{
lean_object* v_a_3201_; lean_object* v___x_3203_; uint8_t v_isShared_3204_; uint8_t v_isSharedCheck_3208_; 
lean_del_object(v___x_3173_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3201_ = lean_ctor_get(v___x_3184_, 0);
v_isSharedCheck_3208_ = !lean_is_exclusive(v___x_3184_);
if (v_isSharedCheck_3208_ == 0)
{
v___x_3203_ = v___x_3184_;
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
else
{
lean_inc(v_a_3201_);
lean_dec(v___x_3184_);
v___x_3203_ = lean_box(0);
v_isShared_3204_ = v_isSharedCheck_3208_;
goto v_resetjp_3202_;
}
v_resetjp_3202_:
{
lean_object* v___x_3206_; 
if (v_isShared_3204_ == 0)
{
v___x_3206_ = v___x_3203_;
goto v_reusejp_3205_;
}
else
{
lean_object* v_reuseFailAlloc_3207_; 
v_reuseFailAlloc_3207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3207_, 0, v_a_3201_);
v___x_3206_ = v_reuseFailAlloc_3207_;
goto v_reusejp_3205_;
}
v_reusejp_3205_:
{
return v___x_3206_;
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_del_object(v___x_3173_);
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
v_a_3209_ = lean_ctor_get(v___x_3181_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3181_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3181_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3181_);
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
v___jp_3218_:
{
lean_object* v_searchFuel_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; 
v_searchFuel_3223_ = lean_ctor_get(v_config_3139_, 0);
v___x_3224_ = l_Lean_LocalDecl_fvarId(v_val_3171_);
lean_dec(v_val_3171_);
lean_inc(v_searchFuel_3223_);
lean_inc(v_mvarId_3140_);
v___x_3225_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3140_, v___x_3224_, v_searchFuel_3223_, v___y_3222_, v___y_3219_, v___y_3221_, v___y_3220_);
if (lean_obj_tag(v___x_3225_) == 0)
{
lean_object* v_a_3226_; uint8_t v___x_3227_; 
v_a_3226_ = lean_ctor_get(v___x_3225_, 0);
lean_inc(v_a_3226_);
lean_dec_ref_known(v___x_3225_, 1);
v___x_3227_ = lean_unbox(v_a_3226_);
lean_dec(v_a_3226_);
if (v___x_3227_ == 0)
{
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
v_a_3165_ = v___x_3217_;
goto v___jp_3164_;
}
else
{
lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; 
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v___x_3228_ = lean_box(v___x_3150_);
v___x_3229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
v___x_3230_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
lean_ctor_set(v___x_3230_, 1, v___x_3175_);
v___x_3231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
v_a_3157_ = v___x_3231_;
goto v___jp_3156_;
}
}
else
{
lean_object* v_a_3232_; lean_object* v___x_3234_; uint8_t v_isShared_3235_; uint8_t v_isSharedCheck_3239_; 
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3232_ = lean_ctor_get(v___x_3225_, 0);
v_isSharedCheck_3239_ = !lean_is_exclusive(v___x_3225_);
if (v_isSharedCheck_3239_ == 0)
{
v___x_3234_ = v___x_3225_;
v_isShared_3235_ = v_isSharedCheck_3239_;
goto v_resetjp_3233_;
}
else
{
lean_inc(v_a_3232_);
lean_dec(v___x_3225_);
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
v___jp_3240_:
{
if (v___y_3245_ == 0)
{
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
v_a_3165_ = v___x_3217_;
goto v___jp_3164_;
}
else
{
v___y_3219_ = v___y_3241_;
v___y_3220_ = v___y_3242_;
v___y_3221_ = v___y_3243_;
v___y_3222_ = v___y_3244_;
goto v___jp_3218_;
}
}
v___jp_3247_:
{
if (v___y_3250_ == 0)
{
v___y_3219_ = v___y_3248_;
v___y_3220_ = v___y_3249_;
v___y_3221_ = v___y_3251_;
v___y_3222_ = v___y_3252_;
goto v___jp_3218_;
}
else
{
v___y_3241_ = v___y_3248_;
v___y_3242_ = v___y_3249_;
v___y_3243_ = v___y_3251_;
v___y_3244_ = v___y_3252_;
v___y_3245_ = v___x_3246_;
goto v___jp_3240_;
}
}
v___jp_3253_:
{
if (v___y_3259_ == 0)
{
v___y_3241_ = v___y_3254_;
v___y_3242_ = v___y_3255_;
v___y_3243_ = v___y_3257_;
v___y_3244_ = v___y_3258_;
v___y_3245_ = v___x_3246_;
goto v___jp_3240_;
}
else
{
v___y_3248_ = v___y_3254_;
v___y_3249_ = v___y_3255_;
v___y_3250_ = v___y_3256_;
v___y_3251_ = v___y_3257_;
v___y_3252_ = v___y_3258_;
goto v___jp_3247_;
}
}
v___jp_3260_:
{
uint8_t v_emptyType_3267_; 
v_emptyType_3267_ = lean_ctor_get_uint8(v_config_3139_, sizeof(void*)*1 + 1);
if (v_emptyType_3267_ == 0)
{
v___y_3254_ = v___y_3264_;
v___y_3255_ = v___y_3266_;
v___y_3256_ = v___y_3262_;
v___y_3257_ = v___y_3265_;
v___y_3258_ = v___y_3263_;
v___y_3259_ = v___x_3246_;
goto v___jp_3253_;
}
else
{
if (v___y_3261_ == 0)
{
v___y_3248_ = v___y_3264_;
v___y_3249_ = v___y_3266_;
v___y_3250_ = v___y_3262_;
v___y_3251_ = v___y_3265_;
v___y_3252_ = v___y_3263_;
goto v___jp_3247_;
}
else
{
v___y_3254_ = v___y_3264_;
v___y_3255_ = v___y_3266_;
v___y_3256_ = v___y_3262_;
v___y_3257_ = v___y_3265_;
v___y_3258_ = v___y_3263_;
v___y_3259_ = v___x_3246_;
goto v___jp_3253_;
}
}
}
v___jp_3268_:
{
if (v___y_3275_ == 0)
{
v___y_3261_ = v___y_3271_;
v___y_3262_ = v___y_3272_;
v___y_3263_ = v___y_3269_;
v___y_3264_ = v___y_3270_;
v___y_3265_ = v___y_3273_;
v___y_3266_ = v___y_3274_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3276_; 
lean_inc(v_val_3171_);
lean_inc(v_mvarId_3140_);
v___x_3276_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3140_, v_val_3171_, v___y_3269_, v___y_3270_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; uint8_t v___x_3278_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc(v_a_3277_);
lean_dec_ref_known(v___x_3276_, 1);
v___x_3278_ = lean_unbox(v_a_3277_);
lean_dec(v_a_3277_);
if (v___x_3278_ == 0)
{
v___y_3261_ = v___y_3271_;
v___y_3262_ = v___y_3272_;
v___y_3263_ = v___y_3269_;
v___y_3264_ = v___y_3270_;
v___y_3265_ = v___y_3273_;
v___y_3266_ = v___y_3274_;
goto v___jp_3260_;
}
else
{
lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; 
lean_dec(v_val_3171_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v___x_3279_ = lean_box(v___x_3150_);
v___x_3280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
v___x_3281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
lean_ctor_set(v___x_3281_, 1, v___x_3175_);
v___x_3282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
v_a_3157_ = v___x_3282_;
goto v___jp_3156_;
}
}
else
{
lean_object* v_a_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3290_; 
lean_dec(v_val_3171_);
lean_del_object(v___x_3154_);
lean_dec(v_snd_3152_);
lean_dec(v_mvarId_3140_);
lean_dec_ref(v_config_3139_);
v_a_3283_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3290_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3290_ == 0)
{
v___x_3285_ = v___x_3276_;
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_a_3283_);
lean_dec(v___x_3276_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3290_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v___x_3288_; 
if (v_isShared_3286_ == 0)
{
v___x_3288_ = v___x_3285_;
goto v_reusejp_3287_;
}
else
{
lean_object* v_reuseFailAlloc_3289_; 
v_reuseFailAlloc_3289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3289_, 0, v_a_3283_);
v___x_3288_ = v_reuseFailAlloc_3289_;
goto v_reusejp_3287_;
}
v_reusejp_3287_:
{
return v___x_3288_;
}
}
}
}
}
}
}
v___jp_3156_:
{
lean_object* v___x_3158_; lean_object* v___x_3160_; 
v___x_3158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3158_, 0, v_a_3157_);
if (v_isShared_3155_ == 0)
{
lean_ctor_set(v___x_3154_, 0, v___x_3158_);
v___x_3160_ = v___x_3154_;
goto v_reusejp_3159_;
}
else
{
lean_object* v_reuseFailAlloc_3162_; 
v_reuseFailAlloc_3162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3162_, 0, v___x_3158_);
lean_ctor_set(v_reuseFailAlloc_3162_, 1, v_snd_3152_);
v___x_3160_ = v_reuseFailAlloc_3162_;
goto v_reusejp_3159_;
}
v_reusejp_3159_:
{
lean_object* v___x_3161_; 
v___x_3161_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
return v___x_3161_;
}
}
v___jp_3164_:
{
lean_object* v___x_3166_; size_t v___x_3167_; size_t v___x_3168_; 
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3163_);
lean_ctor_set(v___x_3166_, 1, v_a_3165_);
v___x_3167_ = ((size_t)1ULL);
v___x_3168_ = lean_usize_add(v_i_3143_, v___x_3167_);
v_i_3143_ = v___x_3168_;
v_b_3144_ = v___x_3166_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3811_, lean_object* v_mvarId_3812_, lean_object* v_as_3813_, lean_object* v_sz_3814_, lean_object* v_i_3815_, lean_object* v_b_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_){
_start:
{
size_t v_sz_boxed_3822_; size_t v_i_boxed_3823_; lean_object* v_res_3824_; 
v_sz_boxed_3822_ = lean_unbox_usize(v_sz_3814_);
lean_dec(v_sz_3814_);
v_i_boxed_3823_ = lean_unbox_usize(v_i_3815_);
lean_dec(v_i_3815_);
v_res_3824_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3811_, v_mvarId_3812_, v_as_3813_, v_sz_boxed_3822_, v_i_boxed_3823_, v_b_3816_, v___y_3817_, v___y_3818_, v___y_3819_, v___y_3820_);
lean_dec(v___y_3820_);
lean_dec_ref(v___y_3819_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec_ref(v_as_3813_);
return v_res_3824_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3825_, lean_object* v_mvarId_3826_, lean_object* v_as_3827_, size_t v_sz_3828_, size_t v_i_3829_, lean_object* v_b_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
uint8_t v___x_3836_; 
v___x_3836_ = lean_usize_dec_lt(v_i_3829_, v_sz_3828_);
if (v___x_3836_ == 0)
{
lean_object* v___x_3837_; 
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v___x_3837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3837_, 0, v_b_3830_);
return v___x_3837_;
}
else
{
lean_object* v_snd_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_4495_; 
v_snd_3838_ = lean_ctor_get(v_b_3830_, 1);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_b_3830_);
if (v_isSharedCheck_4495_ == 0)
{
lean_object* v_unused_4496_; 
v_unused_4496_ = lean_ctor_get(v_b_3830_, 0);
lean_dec(v_unused_4496_);
v___x_3840_ = v_b_3830_;
v_isShared_3841_ = v_isSharedCheck_4495_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_snd_3838_);
lean_dec(v_b_3830_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_4495_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v_a_3843_; lean_object* v___x_3849_; lean_object* v_a_3851_; lean_object* v_a_3856_; 
v___x_3849_ = lean_box(0);
v_a_3856_ = lean_array_uget(v_as_3827_, v_i_3829_);
if (lean_obj_tag(v_a_3856_) == 0)
{
lean_del_object(v___x_3840_);
v_a_3851_ = v_snd_3838_;
goto v___jp_3850_;
}
else
{
lean_object* v_val_3857_; lean_object* v___x_3859_; uint8_t v_isShared_3860_; uint8_t v_isSharedCheck_4494_; 
v_val_3857_ = lean_ctor_get(v_a_3856_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v_a_3856_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_3859_ = v_a_3856_;
v_isShared_3860_ = v_isSharedCheck_4494_;
goto v_resetjp_3858_;
}
else
{
lean_inc(v_val_3857_);
lean_dec(v_a_3856_);
v___x_3859_ = lean_box(0);
v_isShared_3860_ = v_isSharedCheck_4494_;
goto v_resetjp_3858_;
}
v_resetjp_3858_:
{
lean_object* v___x_3861_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___x_3903_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; uint8_t v___y_3931_; uint8_t v___x_3932_; uint8_t v___y_3934_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; uint8_t v___y_3940_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; uint8_t v___y_3945_; uint8_t v___y_3947_; uint8_t v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; uint8_t v___y_3955_; uint8_t v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; uint8_t v___y_3961_; 
v___x_3861_ = lean_box(0);
v___x_3903_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3932_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3857_);
if (v___x_3932_ == 0)
{
lean_object* v___x_3977_; uint8_t v___y_3979_; uint8_t v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; uint8_t v___y_3988_; lean_object* v___y_3989_; uint8_t v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; lean_object* v___y_3994_; uint8_t v___y_3995_; lean_object* v___y_3998_; uint8_t v___y_3999_; uint8_t v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; lean_object* v___y_4003_; lean_object* v_a_4004_; uint8_t v___y_4008_; lean_object* v___y_4009_; uint8_t v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; lean_object* v___y_4013_; uint8_t v___y_4075_; lean_object* v___y_4076_; uint8_t v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; lean_object* v___y_4080_; uint8_t v___y_4081_; lean_object* v___y_4083_; lean_object* v___y_4084_; uint8_t v___y_4085_; uint8_t v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; lean_object* v___y_4089_; uint8_t v___y_4090_; lean_object* v___y_4093_; uint8_t v___y_4094_; uint8_t v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; lean_object* v___y_4098_; uint8_t v___y_4099_; uint8_t v___y_4112_; lean_object* v___y_4113_; uint8_t v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; lean_object* v___y_4117_; uint8_t v___y_4118_; uint8_t v___y_4120_; uint8_t v_isHEq_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4129_; uint8_t v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; uint8_t v_isEq_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___x_4424_; 
v___x_3977_ = l_Lean_LocalDecl_type(v_val_3857_);
lean_inc_ref(v___x_3977_);
v___x_4424_ = l_Lean_Meta_matchNot_x3f(v___x_3977_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_object* v_a_4425_; 
v_a_4425_ = lean_ctor_get(v___x_4424_, 0);
lean_inc(v_a_4425_);
lean_dec_ref_known(v___x_4424_, 1);
if (lean_obj_tag(v_a_4425_) == 1)
{
lean_object* v_val_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4485_; 
v_val_4426_ = lean_ctor_get(v_a_4425_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v_a_4425_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4428_ = v_a_4425_;
v_isShared_4429_ = v_isSharedCheck_4485_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_val_4426_);
lean_dec(v_a_4425_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4485_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4430_; 
v___x_4430_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4426_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
if (lean_obj_tag(v___x_4430_) == 0)
{
lean_object* v_a_4431_; 
v_a_4431_ = lean_ctor_get(v___x_4430_, 0);
lean_inc(v_a_4431_);
lean_dec_ref_known(v___x_4430_, 1);
if (lean_obj_tag(v_a_4431_) == 1)
{
lean_object* v_val_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4476_; 
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec_ref(v_config_3825_);
v_val_4432_ = lean_ctor_get(v_a_4431_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v_a_4431_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4434_ = v_a_4431_;
v_isShared_4435_ = v_isSharedCheck_4476_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_val_4432_);
lean_dec(v_a_4431_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4476_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4436_; 
lean_inc(v_mvarId_3826_);
v___x_4436_ = l_Lean_MVarId_getType(v_mvarId_3826_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
if (lean_obj_tag(v___x_4436_) == 0)
{
lean_object* v_a_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; 
v_a_4437_ = lean_ctor_get(v___x_4436_, 0);
lean_inc(v_a_4437_);
lean_dec_ref_known(v___x_4436_, 1);
v___x_4438_ = l_Lean_LocalDecl_toExpr(v_val_3857_);
v___x_4439_ = l_Lean_mkFVar(v_val_4432_);
v___x_4440_ = l_Lean_Expr_app___override(v___x_4438_, v___x_4439_);
v___x_4441_ = l_Lean_Meta_mkFalseElim(v_a_4437_, v___x_4440_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v_a_4442_; lean_object* v___x_4443_; 
v_a_4442_ = lean_ctor_get(v___x_4441_, 0);
lean_inc(v_a_4442_);
lean_dec_ref_known(v___x_4441_, 1);
v___x_4443_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3826_, v_a_4442_, v___y_3832_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v___x_4444_; lean_object* v___x_4446_; 
lean_dec_ref_known(v___x_4443_, 1);
v___x_4444_ = lean_box(v___x_3836_);
if (v_isShared_4435_ == 0)
{
lean_ctor_set(v___x_4434_, 0, v___x_4444_);
v___x_4446_ = v___x_4434_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4444_);
v___x_4446_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
lean_object* v___x_4447_; lean_object* v___x_4449_; 
v___x_4447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4447_, 0, v___x_4446_);
lean_ctor_set(v___x_4447_, 1, v___x_3861_);
if (v_isShared_4429_ == 0)
{
lean_ctor_set_tag(v___x_4428_, 0);
lean_ctor_set(v___x_4428_, 0, v___x_4447_);
v___x_4449_ = v___x_4428_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4447_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
v_a_3843_ = v___x_4449_;
goto v___jp_3842_;
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_del_object(v___x_4434_);
lean_del_object(v___x_4428_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
v_a_4452_ = lean_ctor_get(v___x_4443_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4443_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4443_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4443_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
else
{
lean_object* v_a_4460_; lean_object* v___x_4462_; uint8_t v_isShared_4463_; uint8_t v_isSharedCheck_4467_; 
lean_del_object(v___x_4434_);
lean_del_object(v___x_4428_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_4460_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4462_ = v___x_4441_;
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
else
{
lean_inc(v_a_4460_);
lean_dec(v___x_4441_);
v___x_4462_ = lean_box(0);
v_isShared_4463_ = v_isSharedCheck_4467_;
goto v_resetjp_4461_;
}
v_resetjp_4461_:
{
lean_object* v___x_4465_; 
if (v_isShared_4463_ == 0)
{
v___x_4465_ = v___x_4462_;
goto v_reusejp_4464_;
}
else
{
lean_object* v_reuseFailAlloc_4466_; 
v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
v___x_4465_ = v_reuseFailAlloc_4466_;
goto v_reusejp_4464_;
}
v_reusejp_4464_:
{
return v___x_4465_;
}
}
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_del_object(v___x_4434_);
lean_dec(v_val_4432_);
lean_del_object(v___x_4428_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_4468_ = lean_ctor_get(v___x_4436_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4436_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4436_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4436_);
v___x_4470_ = lean_box(0);
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
v_resetjp_4469_:
{
lean_object* v___x_4473_; 
if (v_isShared_4471_ == 0)
{
v___x_4473_ = v___x_4470_;
goto v_reusejp_4472_;
}
else
{
lean_object* v_reuseFailAlloc_4474_; 
v_reuseFailAlloc_4474_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4474_, 0, v_a_4468_);
v___x_4473_ = v_reuseFailAlloc_4474_;
goto v_reusejp_4472_;
}
v_reusejp_4472_:
{
return v___x_4473_;
}
}
}
}
}
else
{
lean_dec(v_a_4431_);
lean_del_object(v___x_4428_);
v___y_4288_ = v___y_3831_;
v___y_4289_ = v___y_3832_;
v___y_4290_ = v___y_3833_;
v___y_4291_ = v___y_3834_;
goto v___jp_4287_;
}
}
else
{
lean_object* v_a_4477_; lean_object* v___x_4479_; uint8_t v_isShared_4480_; uint8_t v_isSharedCheck_4484_; 
lean_del_object(v___x_4428_);
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4477_ = lean_ctor_get(v___x_4430_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v___x_4430_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4479_ = v___x_4430_;
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
else
{
lean_inc(v_a_4477_);
lean_dec(v___x_4430_);
v___x_4479_ = lean_box(0);
v_isShared_4480_ = v_isSharedCheck_4484_;
goto v_resetjp_4478_;
}
v_resetjp_4478_:
{
lean_object* v___x_4482_; 
if (v_isShared_4480_ == 0)
{
v___x_4482_ = v___x_4479_;
goto v_reusejp_4481_;
}
else
{
lean_object* v_reuseFailAlloc_4483_; 
v_reuseFailAlloc_4483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4483_, 0, v_a_4477_);
v___x_4482_ = v_reuseFailAlloc_4483_;
goto v_reusejp_4481_;
}
v_reusejp_4481_:
{
return v___x_4482_;
}
}
}
}
}
else
{
lean_dec(v_a_4425_);
v___y_4288_ = v___y_3831_;
v___y_4289_ = v___y_3832_;
v___y_4290_ = v___y_3833_;
v___y_4291_ = v___y_3834_;
goto v___jp_4287_;
}
}
else
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4493_; 
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4486_ = lean_ctor_get(v___x_4424_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v___x_4424_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_4488_ = v___x_4424_;
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4424_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4493_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4491_; 
if (v_isShared_4489_ == 0)
{
v___x_4491_ = v___x_4488_;
goto v_reusejp_4490_;
}
else
{
lean_object* v_reuseFailAlloc_4492_; 
v_reuseFailAlloc_4492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4492_, 0, v_a_4486_);
v___x_4491_ = v_reuseFailAlloc_4492_;
goto v_reusejp_4490_;
}
v_reusejp_4490_:
{
return v___x_4491_;
}
}
}
v___jp_3978_:
{
uint8_t v_genDiseq_3985_; 
v_genDiseq_3985_ = lean_ctor_get_uint8(v_config_3825_, sizeof(void*)*1 + 2);
if (v_genDiseq_3985_ == 0)
{
lean_dec_ref(v___x_3977_);
v___y_3955_ = v___y_3979_;
v___y_3956_ = v___y_3980_;
v___y_3957_ = v___y_3981_;
v___y_3958_ = v___y_3983_;
v___y_3959_ = v___y_3984_;
v___y_3960_ = v___y_3982_;
v___y_3961_ = v___x_3932_;
goto v___jp_3954_;
}
else
{
uint8_t v___x_3986_; 
v___x_3986_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3977_);
v___y_3955_ = v___y_3979_;
v___y_3956_ = v___y_3980_;
v___y_3957_ = v___y_3981_;
v___y_3958_ = v___y_3983_;
v___y_3959_ = v___y_3984_;
v___y_3960_ = v___y_3982_;
v___y_3961_ = v___x_3986_;
goto v___jp_3954_;
}
}
v___jp_3987_:
{
if (v___y_3995_ == 0)
{
lean_dec_ref(v___y_3993_);
v___y_3979_ = v___y_3988_;
v___y_3980_ = v___y_3990_;
v___y_3981_ = v___y_3989_;
v___y_3982_ = v___y_3994_;
v___y_3983_ = v___y_3991_;
v___y_3984_ = v___y_3992_;
goto v___jp_3978_;
}
else
{
lean_object* v___x_3996_; 
lean_dec_ref(v___x_3977_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v___x_3996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3996_, 0, v___y_3993_);
return v___x_3996_;
}
}
v___jp_3997_:
{
uint8_t v___x_4005_; 
v___x_4005_ = l_Lean_Exception_isInterrupt(v_a_4004_);
if (v___x_4005_ == 0)
{
uint8_t v___x_4006_; 
lean_inc_ref(v_a_4004_);
v___x_4006_ = l_Lean_Exception_isRuntime(v_a_4004_);
v___y_3988_ = v___y_3999_;
v___y_3989_ = v___y_3998_;
v___y_3990_ = v___y_4000_;
v___y_3991_ = v___y_4001_;
v___y_3992_ = v___y_4002_;
v___y_3993_ = v_a_4004_;
v___y_3994_ = v___y_4003_;
v___y_3995_ = v___x_4006_;
goto v___jp_3987_;
}
else
{
v___y_3988_ = v___y_3999_;
v___y_3989_ = v___y_3998_;
v___y_3990_ = v___y_4000_;
v___y_3991_ = v___y_4001_;
v___y_3992_ = v___y_4002_;
v___y_3993_ = v_a_4004_;
v___y_3994_ = v___y_4003_;
v___y_3995_ = v___x_4005_;
goto v___jp_3987_;
}
}
v___jp_4007_:
{
lean_object* v___x_4014_; 
lean_inc_ref(v___x_3977_);
v___x_4014_ = l_Lean_Meta_mkDecide(v___x_3977_, v___y_4009_, v___y_4013_, v___y_4011_, v___y_4012_);
if (lean_obj_tag(v___x_4014_) == 0)
{
lean_object* v_a_4015_; lean_object* v_keyedConfig_4016_; uint8_t v_trackZetaDelta_4017_; lean_object* v_zetaDeltaSet_4018_; lean_object* v_lctx_4019_; lean_object* v_localInstances_4020_; lean_object* v_defEqCtx_x3f_4021_; lean_object* v_synthPendingDepth_4022_; lean_object* v_customCanUnfoldPredicate_x3f_4023_; uint8_t v_univApprox_4024_; uint8_t v_inTypeClassResolution_4025_; uint8_t v_cacheInferType_4026_; uint8_t v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v_a_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc_n(v_a_4015_, 2);
lean_dec_ref_known(v___x_4014_, 1);
v_keyedConfig_4016_ = lean_ctor_get(v___y_4009_, 0);
v_trackZetaDelta_4017_ = lean_ctor_get_uint8(v___y_4009_, sizeof(void*)*7);
v_zetaDeltaSet_4018_ = lean_ctor_get(v___y_4009_, 1);
v_lctx_4019_ = lean_ctor_get(v___y_4009_, 2);
v_localInstances_4020_ = lean_ctor_get(v___y_4009_, 3);
v_defEqCtx_x3f_4021_ = lean_ctor_get(v___y_4009_, 4);
v_synthPendingDepth_4022_ = lean_ctor_get(v___y_4009_, 5);
v_customCanUnfoldPredicate_x3f_4023_ = lean_ctor_get(v___y_4009_, 6);
v_univApprox_4024_ = lean_ctor_get_uint8(v___y_4009_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4025_ = lean_ctor_get_uint8(v___y_4009_, sizeof(void*)*7 + 2);
v_cacheInferType_4026_ = lean_ctor_get_uint8(v___y_4009_, sizeof(void*)*7 + 3);
v___x_4027_ = 1;
lean_inc_ref(v_keyedConfig_4016_);
v___x_4028_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4027_, v_keyedConfig_4016_);
lean_inc(v_customCanUnfoldPredicate_x3f_4023_);
lean_inc(v_synthPendingDepth_4022_);
lean_inc(v_defEqCtx_x3f_4021_);
lean_inc_ref(v_localInstances_4020_);
lean_inc_ref(v_lctx_4019_);
lean_inc(v_zetaDeltaSet_4018_);
v___x_4029_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4029_, 0, v___x_4028_);
lean_ctor_set(v___x_4029_, 1, v_zetaDeltaSet_4018_);
lean_ctor_set(v___x_4029_, 2, v_lctx_4019_);
lean_ctor_set(v___x_4029_, 3, v_localInstances_4020_);
lean_ctor_set(v___x_4029_, 4, v_defEqCtx_x3f_4021_);
lean_ctor_set(v___x_4029_, 5, v_synthPendingDepth_4022_);
lean_ctor_set(v___x_4029_, 6, v_customCanUnfoldPredicate_x3f_4023_);
lean_ctor_set_uint8(v___x_4029_, sizeof(void*)*7, v_trackZetaDelta_4017_);
lean_ctor_set_uint8(v___x_4029_, sizeof(void*)*7 + 1, v_univApprox_4024_);
lean_ctor_set_uint8(v___x_4029_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4025_);
lean_ctor_set_uint8(v___x_4029_, sizeof(void*)*7 + 3, v_cacheInferType_4026_);
lean_inc(v___y_4012_);
lean_inc_ref(v___y_4011_);
lean_inc(v___y_4013_);
v___x_4030_ = lean_whnf(v_a_4015_, v___x_4029_, v___y_4013_, v___y_4011_, v___y_4012_);
if (lean_obj_tag(v___x_4030_) == 0)
{
lean_object* v_a_4031_; lean_object* v___x_4032_; uint8_t v___x_4033_; 
v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4031_);
lean_dec_ref_known(v___x_4030_, 1);
v___x_4032_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_4033_ = l_Lean_Expr_isConstOf(v_a_4031_, v___x_4032_);
lean_dec(v_a_4031_);
if (v___x_4033_ == 0)
{
lean_dec(v_a_4015_);
v___y_3979_ = v___y_4008_;
v___y_3980_ = v___y_4010_;
v___y_3981_ = v___y_4009_;
v___y_3982_ = v___y_4013_;
v___y_3983_ = v___y_4011_;
v___y_3984_ = v___y_4012_;
goto v___jp_3978_;
}
else
{
lean_object* v___x_4034_; 
lean_inc(v_a_4015_);
v___x_4034_ = l_Lean_Meta_mkEqRefl(v_a_4015_, v___y_4009_, v___y_4013_, v___y_4011_, v___y_4012_);
if (lean_obj_tag(v___x_4034_) == 0)
{
lean_object* v_a_4035_; lean_object* v___x_4036_; 
v_a_4035_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4035_);
lean_dec_ref_known(v___x_4034_, 1);
lean_inc(v_mvarId_3826_);
v___x_4036_ = l_Lean_MVarId_getType(v_mvarId_3826_, v___y_4009_, v___y_4013_, v___y_4011_, v___y_4012_);
if (lean_obj_tag(v___x_4036_) == 0)
{
lean_object* v_a_4037_; lean_object* v_nargs_4038_; lean_object* v___x_4039_; lean_object* v_dummy_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; 
v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4037_);
lean_dec_ref_known(v___x_4036_, 1);
v_nargs_4038_ = l_Lean_Expr_getAppNumArgs(v_a_4015_);
v___x_4039_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_4040_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_4038_);
v___x_4041_ = lean_mk_array(v_nargs_4038_, v_dummy_4040_);
v___x_4042_ = lean_unsigned_to_nat(1u);
v___x_4043_ = lean_nat_sub(v_nargs_4038_, v___x_4042_);
lean_dec(v_nargs_4038_);
v___x_4044_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4015_, v___x_4041_, v___x_4043_);
v___x_4045_ = lean_array_push(v___x_4044_, v_a_4035_);
v___x_4046_ = l_Lean_mkAppN(v___x_4039_, v___x_4045_);
lean_dec_ref(v___x_4045_);
lean_inc(v_val_3857_);
v___x_4047_ = l_Lean_LocalDecl_toExpr(v_val_3857_);
v___x_4048_ = l_Lean_Meta_mkAbsurd(v_a_4037_, v___x_4047_, v___x_4046_, v___y_4009_, v___y_4013_, v___y_4011_, v___y_4012_);
if (lean_obj_tag(v___x_4048_) == 0)
{
lean_object* v_a_4049_; lean_object* v___x_4051_; uint8_t v_isShared_4052_; uint8_t v_isSharedCheck_4068_; 
v_a_4049_ = lean_ctor_get(v___x_4048_, 0);
v_isSharedCheck_4068_ = !lean_is_exclusive(v___x_4048_);
if (v_isSharedCheck_4068_ == 0)
{
v___x_4051_ = v___x_4048_;
v_isShared_4052_ = v_isSharedCheck_4068_;
goto v_resetjp_4050_;
}
else
{
lean_inc(v_a_4049_);
lean_dec(v___x_4048_);
v___x_4051_ = lean_box(0);
v_isShared_4052_ = v_isSharedCheck_4068_;
goto v_resetjp_4050_;
}
v_resetjp_4050_:
{
lean_object* v___x_4053_; 
lean_inc(v_mvarId_3826_);
v___x_4053_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3826_, v_a_4049_, v___y_4013_);
if (lean_obj_tag(v___x_4053_) == 0)
{
lean_object* v___x_4055_; uint8_t v_isShared_4056_; uint8_t v_isSharedCheck_4065_; 
lean_dec_ref(v___x_3977_);
lean_dec(v_val_3857_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_isSharedCheck_4065_ = !lean_is_exclusive(v___x_4053_);
if (v_isSharedCheck_4065_ == 0)
{
lean_object* v_unused_4066_; 
v_unused_4066_ = lean_ctor_get(v___x_4053_, 0);
lean_dec(v_unused_4066_);
v___x_4055_ = v___x_4053_;
v_isShared_4056_ = v_isSharedCheck_4065_;
goto v_resetjp_4054_;
}
else
{
lean_dec(v___x_4053_);
v___x_4055_ = lean_box(0);
v_isShared_4056_ = v_isSharedCheck_4065_;
goto v_resetjp_4054_;
}
v_resetjp_4054_:
{
lean_object* v___x_4057_; lean_object* v___x_4059_; 
v___x_4057_ = lean_box(v___x_3836_);
if (v_isShared_4056_ == 0)
{
lean_ctor_set_tag(v___x_4055_, 1);
lean_ctor_set(v___x_4055_, 0, v___x_4057_);
v___x_4059_ = v___x_4055_;
goto v_reusejp_4058_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4057_);
v___x_4059_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4058_;
}
v_reusejp_4058_:
{
lean_object* v___x_4060_; lean_object* v___x_4062_; 
v___x_4060_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
lean_ctor_set(v___x_4060_, 1, v___x_3861_);
if (v_isShared_4052_ == 0)
{
lean_ctor_set(v___x_4051_, 0, v___x_4060_);
v___x_4062_ = v___x_4051_;
goto v_reusejp_4061_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4060_);
v___x_4062_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4061_;
}
v_reusejp_4061_:
{
v_a_3843_ = v___x_4062_;
goto v___jp_3842_;
}
}
}
}
else
{
lean_object* v_a_4067_; 
lean_del_object(v___x_4051_);
v_a_4067_ = lean_ctor_get(v___x_4053_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4053_, 1);
v___y_3998_ = v___y_4009_;
v___y_3999_ = v___y_4008_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4011_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v_a_4004_ = v_a_4067_;
goto v___jp_3997_;
}
}
}
else
{
lean_object* v_a_4069_; 
v_a_4069_ = lean_ctor_get(v___x_4048_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4048_, 1);
v___y_3998_ = v___y_4009_;
v___y_3999_ = v___y_4008_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4011_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v_a_4004_ = v_a_4069_;
goto v___jp_3997_;
}
}
else
{
lean_object* v_a_4070_; 
lean_dec(v_a_4035_);
lean_dec(v_a_4015_);
v_a_4070_ = lean_ctor_get(v___x_4036_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4036_, 1);
v___y_3998_ = v___y_4009_;
v___y_3999_ = v___y_4008_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4011_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v_a_4004_ = v_a_4070_;
goto v___jp_3997_;
}
}
else
{
lean_object* v_a_4071_; 
lean_dec(v_a_4015_);
v_a_4071_ = lean_ctor_get(v___x_4034_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4034_, 1);
v___y_3998_ = v___y_4009_;
v___y_3999_ = v___y_4008_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4011_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v_a_4004_ = v_a_4071_;
goto v___jp_3997_;
}
}
}
else
{
lean_object* v_a_4072_; 
lean_dec(v_a_4015_);
v_a_4072_ = lean_ctor_get(v___x_4030_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4030_, 1);
v___y_3998_ = v___y_4009_;
v___y_3999_ = v___y_4008_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4011_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v_a_4004_ = v_a_4072_;
goto v___jp_3997_;
}
}
else
{
lean_object* v_a_4073_; 
v_a_4073_ = lean_ctor_get(v___x_4014_, 0);
lean_inc(v_a_4073_);
lean_dec_ref_known(v___x_4014_, 1);
v___y_3998_ = v___y_4009_;
v___y_3999_ = v___y_4008_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4011_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v_a_4004_ = v_a_4073_;
goto v___jp_3997_;
}
}
v___jp_4074_:
{
if (v___y_4081_ == 0)
{
v___y_3979_ = v___y_4075_;
v___y_3980_ = v___y_4077_;
v___y_3981_ = v___y_4076_;
v___y_3982_ = v___y_4080_;
v___y_3983_ = v___y_4078_;
v___y_3984_ = v___y_4079_;
goto v___jp_3978_;
}
else
{
v___y_4008_ = v___y_4075_;
v___y_4009_ = v___y_4076_;
v___y_4010_ = v___y_4077_;
v___y_4011_ = v___y_4078_;
v___y_4012_ = v___y_4079_;
v___y_4013_ = v___y_4080_;
goto v___jp_4007_;
}
}
v___jp_4082_:
{
if (v___y_4090_ == 0)
{
lean_dec_ref(v___y_4083_);
v___y_4075_ = v___y_4085_;
v___y_4076_ = v___y_4084_;
v___y_4077_ = v___y_4086_;
v___y_4078_ = v___y_4087_;
v___y_4079_ = v___y_4088_;
v___y_4080_ = v___y_4089_;
v___y_4081_ = v___x_3932_;
goto v___jp_4074_;
}
else
{
uint8_t v___x_4091_; 
v___x_4091_ = l_Lean_Expr_hasFVar(v___y_4083_);
lean_dec_ref(v___y_4083_);
if (v___x_4091_ == 0)
{
v___y_4008_ = v___y_4085_;
v___y_4009_ = v___y_4084_;
v___y_4010_ = v___y_4086_;
v___y_4011_ = v___y_4087_;
v___y_4012_ = v___y_4088_;
v___y_4013_ = v___y_4089_;
goto v___jp_4007_;
}
else
{
v___y_4075_ = v___y_4085_;
v___y_4076_ = v___y_4084_;
v___y_4077_ = v___y_4086_;
v___y_4078_ = v___y_4087_;
v___y_4079_ = v___y_4088_;
v___y_4080_ = v___y_4089_;
v___y_4081_ = v___x_3932_;
goto v___jp_4074_;
}
}
}
v___jp_4092_:
{
lean_object* v___x_4100_; 
lean_inc_ref(v___x_3977_);
v___x_4100_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3977_, v___y_4098_);
if (lean_obj_tag(v___x_4100_) == 0)
{
lean_object* v_a_4101_; uint8_t v___x_4102_; 
v_a_4101_ = lean_ctor_get(v___x_4100_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___x_4100_, 1);
v___x_4102_ = l_Lean_Expr_hasMVar(v_a_4101_);
if (v___x_4102_ == 0)
{
v___y_4083_ = v_a_4101_;
v___y_4084_ = v___y_4093_;
v___y_4085_ = v___y_4094_;
v___y_4086_ = v___y_4095_;
v___y_4087_ = v___y_4096_;
v___y_4088_ = v___y_4097_;
v___y_4089_ = v___y_4098_;
v___y_4090_ = v___y_4099_;
goto v___jp_4082_;
}
else
{
v___y_4083_ = v_a_4101_;
v___y_4084_ = v___y_4093_;
v___y_4085_ = v___y_4094_;
v___y_4086_ = v___y_4095_;
v___y_4087_ = v___y_4096_;
v___y_4088_ = v___y_4097_;
v___y_4089_ = v___y_4098_;
v___y_4090_ = v___x_3932_;
goto v___jp_4082_;
}
}
else
{
lean_object* v_a_4103_; lean_object* v___x_4105_; uint8_t v_isShared_4106_; uint8_t v_isSharedCheck_4110_; 
lean_dec_ref(v___x_3977_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4103_ = lean_ctor_get(v___x_4100_, 0);
v_isSharedCheck_4110_ = !lean_is_exclusive(v___x_4100_);
if (v_isSharedCheck_4110_ == 0)
{
v___x_4105_ = v___x_4100_;
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
else
{
lean_inc(v_a_4103_);
lean_dec(v___x_4100_);
v___x_4105_ = lean_box(0);
v_isShared_4106_ = v_isSharedCheck_4110_;
goto v_resetjp_4104_;
}
v_resetjp_4104_:
{
lean_object* v___x_4108_; 
if (v_isShared_4106_ == 0)
{
v___x_4108_ = v___x_4105_;
goto v_reusejp_4107_;
}
else
{
lean_object* v_reuseFailAlloc_4109_; 
v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
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
v___jp_4111_:
{
if (v___y_4118_ == 0)
{
v___y_3979_ = v___y_4112_;
v___y_3980_ = v___y_4114_;
v___y_3981_ = v___y_4113_;
v___y_3982_ = v___y_4117_;
v___y_3983_ = v___y_4115_;
v___y_3984_ = v___y_4116_;
goto v___jp_3978_;
}
else
{
v___y_4093_ = v___y_4113_;
v___y_4094_ = v___y_4112_;
v___y_4095_ = v___y_4114_;
v___y_4096_ = v___y_4115_;
v___y_4097_ = v___y_4116_;
v___y_4098_ = v___y_4117_;
v___y_4099_ = v___y_4118_;
goto v___jp_4092_;
}
}
v___jp_4119_:
{
uint8_t v_useDecide_4126_; 
v_useDecide_4126_ = lean_ctor_get_uint8(v_config_3825_, sizeof(void*)*1);
if (v_useDecide_4126_ == 0)
{
v___y_4112_ = v_isHEq_4121_;
v___y_4113_ = v___y_4122_;
v___y_4114_ = v___y_4120_;
v___y_4115_ = v___y_4124_;
v___y_4116_ = v___y_4125_;
v___y_4117_ = v___y_4123_;
v___y_4118_ = v___x_3932_;
goto v___jp_4111_;
}
else
{
uint8_t v___x_4127_; 
v___x_4127_ = l_Lean_Expr_hasFVar(v___x_3977_);
if (v___x_4127_ == 0)
{
v___y_4093_ = v___y_4122_;
v___y_4094_ = v_isHEq_4121_;
v___y_4095_ = v___y_4120_;
v___y_4096_ = v___y_4124_;
v___y_4097_ = v___y_4125_;
v___y_4098_ = v___y_4123_;
v___y_4099_ = v_useDecide_4126_;
goto v___jp_4092_;
}
else
{
v___y_4112_ = v_isHEq_4121_;
v___y_4113_ = v___y_4122_;
v___y_4114_ = v___y_4120_;
v___y_4115_ = v___y_4124_;
v___y_4116_ = v___y_4125_;
v___y_4117_ = v___y_4123_;
v___y_4118_ = v___x_3932_;
goto v___jp_4111_;
}
}
}
v___jp_4128_:
{
lean_object* v___x_4136_; 
v___x_4136_ = l_Lean_Meta_isExprDefEq(v___y_4132_, v___y_4134_, v___y_4129_, v___y_4135_, v___y_4133_, v___y_4131_);
if (lean_obj_tag(v___x_4136_) == 0)
{
lean_object* v_a_4137_; uint8_t v___x_4138_; 
v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
lean_inc(v_a_4137_);
lean_dec_ref_known(v___x_4136_, 1);
v___x_4138_ = lean_unbox(v_a_4137_);
lean_dec(v_a_4137_);
if (v___x_4138_ == 0)
{
v___y_4120_ = v___y_4130_;
v_isHEq_4121_ = v___x_3836_;
v___y_4122_ = v___y_4129_;
v___y_4123_ = v___y_4135_;
v___y_4124_ = v___y_4133_;
v___y_4125_ = v___y_4131_;
goto v___jp_4119_;
}
else
{
lean_object* v___x_4139_; 
lean_dec_ref(v___x_3977_);
lean_dec_ref(v_config_3825_);
lean_inc(v_mvarId_3826_);
v___x_4139_ = l_Lean_MVarId_getType(v_mvarId_3826_, v___y_4129_, v___y_4135_, v___y_4133_, v___y_4131_);
if (lean_obj_tag(v___x_4139_) == 0)
{
lean_object* v_a_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; 
v_a_4140_ = lean_ctor_get(v___x_4139_, 0);
lean_inc(v_a_4140_);
lean_dec_ref_known(v___x_4139_, 1);
v___x_4141_ = l_Lean_LocalDecl_toExpr(v_val_3857_);
v___x_4142_ = l_Lean_Meta_mkEqOfHEq(v___x_4141_, v___x_3836_, v___y_4129_, v___y_4135_, v___y_4133_, v___y_4131_);
if (lean_obj_tag(v___x_4142_) == 0)
{
lean_object* v_a_4143_; lean_object* v___x_4144_; 
v_a_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc(v_a_4143_);
lean_dec_ref_known(v___x_4142_, 1);
v___x_4144_ = l_Lean_Meta_mkNoConfusion(v_a_4140_, v_a_4143_, v___y_4129_, v___y_4135_, v___y_4133_, v___y_4131_);
if (lean_obj_tag(v___x_4144_) == 0)
{
lean_object* v_a_4145_; lean_object* v___x_4146_; 
v_a_4145_ = lean_ctor_get(v___x_4144_, 0);
lean_inc(v_a_4145_);
lean_dec_ref_known(v___x_4144_, 1);
v___x_4146_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3826_, v_a_4145_, v___y_4135_);
if (lean_obj_tag(v___x_4146_) == 0)
{
lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; 
lean_dec_ref_known(v___x_4146_, 1);
v___x_4147_ = lean_box(v___x_3836_);
v___x_4148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
v___x_4149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
lean_ctor_set(v___x_4149_, 1, v___x_3861_);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
v_a_3843_ = v___x_4150_;
goto v___jp_3842_;
}
else
{
lean_object* v_a_4151_; lean_object* v___x_4153_; uint8_t v_isShared_4154_; uint8_t v_isSharedCheck_4158_; 
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
v_a_4151_ = lean_ctor_get(v___x_4146_, 0);
v_isSharedCheck_4158_ = !lean_is_exclusive(v___x_4146_);
if (v_isSharedCheck_4158_ == 0)
{
v___x_4153_ = v___x_4146_;
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
else
{
lean_inc(v_a_4151_);
lean_dec(v___x_4146_);
v___x_4153_ = lean_box(0);
v_isShared_4154_ = v_isSharedCheck_4158_;
goto v_resetjp_4152_;
}
v_resetjp_4152_:
{
lean_object* v___x_4156_; 
if (v_isShared_4154_ == 0)
{
v___x_4156_ = v___x_4153_;
goto v_reusejp_4155_;
}
else
{
lean_object* v_reuseFailAlloc_4157_; 
v_reuseFailAlloc_4157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4157_, 0, v_a_4151_);
v___x_4156_ = v_reuseFailAlloc_4157_;
goto v_reusejp_4155_;
}
v_reusejp_4155_:
{
return v___x_4156_;
}
}
}
}
else
{
lean_object* v_a_4159_; lean_object* v___x_4161_; uint8_t v_isShared_4162_; uint8_t v_isSharedCheck_4166_; 
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_4159_ = lean_ctor_get(v___x_4144_, 0);
v_isSharedCheck_4166_ = !lean_is_exclusive(v___x_4144_);
if (v_isSharedCheck_4166_ == 0)
{
v___x_4161_ = v___x_4144_;
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
else
{
lean_inc(v_a_4159_);
lean_dec(v___x_4144_);
v___x_4161_ = lean_box(0);
v_isShared_4162_ = v_isSharedCheck_4166_;
goto v_resetjp_4160_;
}
v_resetjp_4160_:
{
lean_object* v___x_4164_; 
if (v_isShared_4162_ == 0)
{
v___x_4164_ = v___x_4161_;
goto v_reusejp_4163_;
}
else
{
lean_object* v_reuseFailAlloc_4165_; 
v_reuseFailAlloc_4165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4165_, 0, v_a_4159_);
v___x_4164_ = v_reuseFailAlloc_4165_;
goto v_reusejp_4163_;
}
v_reusejp_4163_:
{
return v___x_4164_;
}
}
}
}
else
{
lean_object* v_a_4167_; lean_object* v___x_4169_; uint8_t v_isShared_4170_; uint8_t v_isSharedCheck_4174_; 
lean_dec(v_a_4140_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_4167_ = lean_ctor_get(v___x_4142_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4142_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4169_ = v___x_4142_;
v_isShared_4170_ = v_isSharedCheck_4174_;
goto v_resetjp_4168_;
}
else
{
lean_inc(v_a_4167_);
lean_dec(v___x_4142_);
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
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_4175_ = lean_ctor_get(v___x_4139_, 0);
v_isSharedCheck_4182_ = !lean_is_exclusive(v___x_4139_);
if (v_isSharedCheck_4182_ == 0)
{
v___x_4177_ = v___x_4139_;
v_isShared_4178_ = v_isSharedCheck_4182_;
goto v_resetjp_4176_;
}
else
{
lean_inc(v_a_4175_);
lean_dec(v___x_4139_);
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
}
else
{
lean_object* v_a_4183_; lean_object* v___x_4185_; uint8_t v_isShared_4186_; uint8_t v_isSharedCheck_4190_; 
lean_dec_ref(v___x_3977_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4183_ = lean_ctor_get(v___x_4136_, 0);
v_isSharedCheck_4190_ = !lean_is_exclusive(v___x_4136_);
if (v_isSharedCheck_4190_ == 0)
{
v___x_4185_ = v___x_4136_;
v_isShared_4186_ = v_isSharedCheck_4190_;
goto v_resetjp_4184_;
}
else
{
lean_inc(v_a_4183_);
lean_dec(v___x_4136_);
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
v___jp_4191_:
{
lean_object* v___x_4197_; 
lean_inc_ref(v___x_3977_);
v___x_4197_ = l_Lean_Meta_matchHEq_x3f(v___x_3977_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
if (lean_obj_tag(v___x_4197_) == 0)
{
lean_object* v_a_4198_; 
v_a_4198_ = lean_ctor_get(v___x_4197_, 0);
lean_inc(v_a_4198_);
lean_dec_ref_known(v___x_4197_, 1);
if (lean_obj_tag(v_a_4198_) == 1)
{
lean_object* v_val_4199_; lean_object* v_snd_4200_; lean_object* v_snd_4201_; lean_object* v_fst_4202_; lean_object* v_fst_4203_; lean_object* v_fst_4204_; lean_object* v_snd_4205_; lean_object* v___x_4206_; 
v_val_4199_ = lean_ctor_get(v_a_4198_, 0);
lean_inc(v_val_4199_);
lean_dec_ref_known(v_a_4198_, 1);
v_snd_4200_ = lean_ctor_get(v_val_4199_, 1);
lean_inc(v_snd_4200_);
v_snd_4201_ = lean_ctor_get(v_snd_4200_, 1);
lean_inc(v_snd_4201_);
v_fst_4202_ = lean_ctor_get(v_val_4199_, 0);
lean_inc(v_fst_4202_);
lean_dec(v_val_4199_);
v_fst_4203_ = lean_ctor_get(v_snd_4200_, 0);
lean_inc(v_fst_4203_);
lean_dec(v_snd_4200_);
v_fst_4204_ = lean_ctor_get(v_snd_4201_, 0);
lean_inc(v_fst_4204_);
v_snd_4205_ = lean_ctor_get(v_snd_4201_, 1);
lean_inc(v_snd_4205_);
lean_dec(v_snd_4201_);
v___x_4206_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4203_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v_a_4207_; 
v_a_4207_ = lean_ctor_get(v___x_4206_, 0);
lean_inc(v_a_4207_);
lean_dec_ref_known(v___x_4206_, 1);
if (lean_obj_tag(v_a_4207_) == 1)
{
lean_object* v_val_4208_; lean_object* v___x_4209_; 
v_val_4208_ = lean_ctor_get(v_a_4207_, 0);
lean_inc(v_val_4208_);
lean_dec_ref_known(v_a_4207_, 1);
v___x_4209_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4205_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
if (lean_obj_tag(v___x_4209_) == 0)
{
lean_object* v_a_4210_; 
v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
lean_inc(v_a_4210_);
lean_dec_ref_known(v___x_4209_, 1);
if (lean_obj_tag(v_a_4210_) == 1)
{
lean_object* v_toConstantVal_4211_; lean_object* v_val_4212_; lean_object* v_toConstantVal_4213_; lean_object* v_name_4214_; lean_object* v_name_4215_; uint8_t v___x_4216_; 
v_toConstantVal_4211_ = lean_ctor_get(v_val_4208_, 0);
lean_inc_ref(v_toConstantVal_4211_);
lean_dec(v_val_4208_);
v_val_4212_ = lean_ctor_get(v_a_4210_, 0);
lean_inc(v_val_4212_);
lean_dec_ref_known(v_a_4210_, 1);
v_toConstantVal_4213_ = lean_ctor_get(v_val_4212_, 0);
lean_inc_ref(v_toConstantVal_4213_);
lean_dec(v_val_4212_);
v_name_4214_ = lean_ctor_get(v_toConstantVal_4211_, 0);
lean_inc(v_name_4214_);
lean_dec_ref(v_toConstantVal_4211_);
v_name_4215_ = lean_ctor_get(v_toConstantVal_4213_, 0);
lean_inc(v_name_4215_);
lean_dec_ref(v_toConstantVal_4213_);
v___x_4216_ = lean_name_eq(v_name_4214_, v_name_4215_);
lean_dec(v_name_4215_);
lean_dec(v_name_4214_);
if (v___x_4216_ == 0)
{
v___y_4129_ = v___y_4193_;
v___y_4130_ = v_isEq_4192_;
v___y_4131_ = v___y_4196_;
v___y_4132_ = v_fst_4202_;
v___y_4133_ = v___y_4195_;
v___y_4134_ = v_fst_4204_;
v___y_4135_ = v___y_4194_;
goto v___jp_4128_;
}
else
{
if (v___x_3932_ == 0)
{
lean_dec(v_fst_4204_);
lean_dec(v_fst_4202_);
v___y_4120_ = v_isEq_4192_;
v_isHEq_4121_ = v___x_3836_;
v___y_4122_ = v___y_4193_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
v___y_4125_ = v___y_4196_;
goto v___jp_4119_;
}
else
{
v___y_4129_ = v___y_4193_;
v___y_4130_ = v_isEq_4192_;
v___y_4131_ = v___y_4196_;
v___y_4132_ = v_fst_4202_;
v___y_4133_ = v___y_4195_;
v___y_4134_ = v_fst_4204_;
v___y_4135_ = v___y_4194_;
goto v___jp_4128_;
}
}
}
else
{
lean_dec(v_a_4210_);
lean_dec(v_val_4208_);
lean_dec(v_fst_4204_);
lean_dec(v_fst_4202_);
v___y_4120_ = v_isEq_4192_;
v_isHEq_4121_ = v___x_3836_;
v___y_4122_ = v___y_4193_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
v___y_4125_ = v___y_4196_;
goto v___jp_4119_;
}
}
else
{
lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4224_; 
lean_dec(v_val_4208_);
lean_dec(v_fst_4204_);
lean_dec(v_fst_4202_);
lean_dec_ref(v___x_3977_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4217_ = lean_ctor_get(v___x_4209_, 0);
v_isSharedCheck_4224_ = !lean_is_exclusive(v___x_4209_);
if (v_isSharedCheck_4224_ == 0)
{
v___x_4219_ = v___x_4209_;
v_isShared_4220_ = v_isSharedCheck_4224_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4209_);
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
else
{
lean_dec(v_a_4207_);
lean_dec(v_snd_4205_);
lean_dec(v_fst_4204_);
lean_dec(v_fst_4202_);
v___y_4120_ = v_isEq_4192_;
v_isHEq_4121_ = v___x_3836_;
v___y_4122_ = v___y_4193_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
v___y_4125_ = v___y_4196_;
goto v___jp_4119_;
}
}
else
{
lean_object* v_a_4225_; lean_object* v___x_4227_; uint8_t v_isShared_4228_; uint8_t v_isSharedCheck_4232_; 
lean_dec(v_snd_4205_);
lean_dec(v_fst_4204_);
lean_dec(v_fst_4202_);
lean_dec_ref(v___x_3977_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4225_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4232_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4232_ == 0)
{
v___x_4227_ = v___x_4206_;
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
else
{
lean_inc(v_a_4225_);
lean_dec(v___x_4206_);
v___x_4227_ = lean_box(0);
v_isShared_4228_ = v_isSharedCheck_4232_;
goto v_resetjp_4226_;
}
v_resetjp_4226_:
{
lean_object* v___x_4230_; 
if (v_isShared_4228_ == 0)
{
v___x_4230_ = v___x_4227_;
goto v_reusejp_4229_;
}
else
{
lean_object* v_reuseFailAlloc_4231_; 
v_reuseFailAlloc_4231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4231_, 0, v_a_4225_);
v___x_4230_ = v_reuseFailAlloc_4231_;
goto v_reusejp_4229_;
}
v_reusejp_4229_:
{
return v___x_4230_;
}
}
}
}
else
{
lean_dec(v_a_4198_);
v___y_4120_ = v_isEq_4192_;
v_isHEq_4121_ = v___x_3932_;
v___y_4122_ = v___y_4193_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
v___y_4125_ = v___y_4196_;
goto v___jp_4119_;
}
}
else
{
lean_object* v_a_4233_; lean_object* v___x_4235_; uint8_t v_isShared_4236_; uint8_t v_isSharedCheck_4240_; 
lean_dec_ref(v___x_3977_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4233_ = lean_ctor_get(v___x_4197_, 0);
v_isSharedCheck_4240_ = !lean_is_exclusive(v___x_4197_);
if (v_isSharedCheck_4240_ == 0)
{
v___x_4235_ = v___x_4197_;
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
else
{
lean_inc(v_a_4233_);
lean_dec(v___x_4197_);
v___x_4235_ = lean_box(0);
v_isShared_4236_ = v_isSharedCheck_4240_;
goto v_resetjp_4234_;
}
v_resetjp_4234_:
{
lean_object* v___x_4238_; 
if (v_isShared_4236_ == 0)
{
v___x_4238_ = v___x_4235_;
goto v_reusejp_4237_;
}
else
{
lean_object* v_reuseFailAlloc_4239_; 
v_reuseFailAlloc_4239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4239_, 0, v_a_4233_);
v___x_4238_ = v_reuseFailAlloc_4239_;
goto v_reusejp_4237_;
}
v_reusejp_4237_:
{
return v___x_4238_;
}
}
}
}
v___jp_4241_:
{
lean_object* v___x_4246_; 
lean_inc_ref(v___x_3977_);
v___x_4246_ = l_Lean_Meta_matchEq_x3f(v___x_3977_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
if (lean_obj_tag(v___x_4246_) == 0)
{
lean_object* v_a_4247_; 
v_a_4247_ = lean_ctor_get(v___x_4246_, 0);
lean_inc(v_a_4247_);
lean_dec_ref_known(v___x_4246_, 1);
if (lean_obj_tag(v_a_4247_) == 1)
{
lean_object* v_val_4248_; lean_object* v_snd_4249_; lean_object* v_fst_4250_; lean_object* v_snd_4251_; lean_object* v___x_4252_; 
v_val_4248_ = lean_ctor_get(v_a_4247_, 0);
lean_inc(v_val_4248_);
lean_dec_ref_known(v_a_4247_, 1);
v_snd_4249_ = lean_ctor_get(v_val_4248_, 1);
lean_inc(v_snd_4249_);
lean_dec(v_val_4248_);
v_fst_4250_ = lean_ctor_get(v_snd_4249_, 0);
lean_inc(v_fst_4250_);
v_snd_4251_ = lean_ctor_get(v_snd_4249_, 1);
lean_inc(v_snd_4251_);
lean_dec(v_snd_4249_);
v___x_4252_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4250_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
if (lean_obj_tag(v___x_4252_) == 0)
{
lean_object* v_a_4253_; 
v_a_4253_ = lean_ctor_get(v___x_4252_, 0);
lean_inc(v_a_4253_);
lean_dec_ref_known(v___x_4252_, 1);
if (lean_obj_tag(v_a_4253_) == 1)
{
lean_object* v_val_4254_; lean_object* v___x_4255_; 
v_val_4254_ = lean_ctor_get(v_a_4253_, 0);
lean_inc(v_val_4254_);
lean_dec_ref_known(v_a_4253_, 1);
v___x_4255_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4251_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
if (lean_obj_tag(v___x_4255_) == 0)
{
lean_object* v_a_4256_; 
v_a_4256_ = lean_ctor_get(v___x_4255_, 0);
lean_inc(v_a_4256_);
lean_dec_ref_known(v___x_4255_, 1);
if (lean_obj_tag(v_a_4256_) == 1)
{
lean_object* v_toConstantVal_4257_; lean_object* v_val_4258_; lean_object* v_toConstantVal_4259_; lean_object* v_name_4260_; lean_object* v_name_4261_; uint8_t v___x_4262_; 
v_toConstantVal_4257_ = lean_ctor_get(v_val_4254_, 0);
lean_inc_ref(v_toConstantVal_4257_);
lean_dec(v_val_4254_);
v_val_4258_ = lean_ctor_get(v_a_4256_, 0);
lean_inc(v_val_4258_);
lean_dec_ref_known(v_a_4256_, 1);
v_toConstantVal_4259_ = lean_ctor_get(v_val_4258_, 0);
lean_inc_ref(v_toConstantVal_4259_);
lean_dec(v_val_4258_);
v_name_4260_ = lean_ctor_get(v_toConstantVal_4257_, 0);
lean_inc(v_name_4260_);
lean_dec_ref(v_toConstantVal_4257_);
v_name_4261_ = lean_ctor_get(v_toConstantVal_4259_, 0);
lean_inc(v_name_4261_);
lean_dec_ref(v_toConstantVal_4259_);
v___x_4262_ = lean_name_eq(v_name_4260_, v_name_4261_);
lean_dec(v_name_4261_);
lean_dec(v_name_4260_);
if (v___x_4262_ == 0)
{
lean_dec_ref(v___x_3977_);
lean_dec_ref(v_config_3825_);
v___y_3863_ = v___y_4244_;
v___y_3864_ = v___y_4245_;
v___y_3865_ = v___y_4243_;
v___y_3866_ = v___y_4242_;
goto v___jp_3862_;
}
else
{
if (v___x_3932_ == 0)
{
lean_del_object(v___x_3859_);
v_isEq_4192_ = v___x_3836_;
v___y_4193_ = v___y_4242_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
v___y_4196_ = v___y_4245_;
goto v___jp_4191_;
}
else
{
lean_dec_ref(v___x_3977_);
lean_dec_ref(v_config_3825_);
v___y_3863_ = v___y_4244_;
v___y_3864_ = v___y_4245_;
v___y_3865_ = v___y_4243_;
v___y_3866_ = v___y_4242_;
goto v___jp_3862_;
}
}
}
else
{
lean_dec(v_a_4256_);
lean_dec(v_val_4254_);
lean_del_object(v___x_3859_);
v_isEq_4192_ = v___x_3836_;
v___y_4193_ = v___y_4242_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
v___y_4196_ = v___y_4245_;
goto v___jp_4191_;
}
}
else
{
lean_object* v_a_4263_; lean_object* v___x_4265_; uint8_t v_isShared_4266_; uint8_t v_isSharedCheck_4270_; 
lean_dec(v_val_4254_);
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4263_ = lean_ctor_get(v___x_4255_, 0);
v_isSharedCheck_4270_ = !lean_is_exclusive(v___x_4255_);
if (v_isSharedCheck_4270_ == 0)
{
v___x_4265_ = v___x_4255_;
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
else
{
lean_inc(v_a_4263_);
lean_dec(v___x_4255_);
v___x_4265_ = lean_box(0);
v_isShared_4266_ = v_isSharedCheck_4270_;
goto v_resetjp_4264_;
}
v_resetjp_4264_:
{
lean_object* v___x_4268_; 
if (v_isShared_4266_ == 0)
{
v___x_4268_ = v___x_4265_;
goto v_reusejp_4267_;
}
else
{
lean_object* v_reuseFailAlloc_4269_; 
v_reuseFailAlloc_4269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4269_, 0, v_a_4263_);
v___x_4268_ = v_reuseFailAlloc_4269_;
goto v_reusejp_4267_;
}
v_reusejp_4267_:
{
return v___x_4268_;
}
}
}
}
else
{
lean_dec(v_a_4253_);
lean_dec(v_snd_4251_);
lean_del_object(v___x_3859_);
v_isEq_4192_ = v___x_3836_;
v___y_4193_ = v___y_4242_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
v___y_4196_ = v___y_4245_;
goto v___jp_4191_;
}
}
else
{
lean_object* v_a_4271_; lean_object* v___x_4273_; uint8_t v_isShared_4274_; uint8_t v_isSharedCheck_4278_; 
lean_dec(v_snd_4251_);
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4271_ = lean_ctor_get(v___x_4252_, 0);
v_isSharedCheck_4278_ = !lean_is_exclusive(v___x_4252_);
if (v_isSharedCheck_4278_ == 0)
{
v___x_4273_ = v___x_4252_;
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
else
{
lean_inc(v_a_4271_);
lean_dec(v___x_4252_);
v___x_4273_ = lean_box(0);
v_isShared_4274_ = v_isSharedCheck_4278_;
goto v_resetjp_4272_;
}
v_resetjp_4272_:
{
lean_object* v___x_4276_; 
if (v_isShared_4274_ == 0)
{
v___x_4276_ = v___x_4273_;
goto v_reusejp_4275_;
}
else
{
lean_object* v_reuseFailAlloc_4277_; 
v_reuseFailAlloc_4277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4277_, 0, v_a_4271_);
v___x_4276_ = v_reuseFailAlloc_4277_;
goto v_reusejp_4275_;
}
v_reusejp_4275_:
{
return v___x_4276_;
}
}
}
}
else
{
lean_dec(v_a_4247_);
lean_del_object(v___x_3859_);
v_isEq_4192_ = v___x_3932_;
v___y_4193_ = v___y_4242_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
v___y_4196_ = v___y_4245_;
goto v___jp_4191_;
}
}
else
{
lean_object* v_a_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4279_ = lean_ctor_get(v___x_4246_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4246_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4246_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_a_4279_);
lean_dec(v___x_4246_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_a_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
v___jp_4287_:
{
lean_object* v___x_4292_; 
lean_inc_ref(v___x_3977_);
v___x_4292_ = l_Lean_refutableHasNotBit_x3f(v___x_3977_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4292_) == 0)
{
lean_object* v_a_4293_; 
v_a_4293_ = lean_ctor_get(v___x_4292_, 0);
lean_inc(v_a_4293_);
lean_dec_ref_known(v___x_4292_, 1);
if (lean_obj_tag(v_a_4293_) == 1)
{
lean_object* v_val_4294_; lean_object* v___x_4296_; uint8_t v_isShared_4297_; uint8_t v_isSharedCheck_4334_; 
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec_ref(v_config_3825_);
v_val_4294_ = lean_ctor_get(v_a_4293_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v_a_4293_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4296_ = v_a_4293_;
v_isShared_4297_ = v_isSharedCheck_4334_;
goto v_resetjp_4295_;
}
else
{
lean_inc(v_val_4294_);
lean_dec(v_a_4293_);
v___x_4296_ = lean_box(0);
v_isShared_4297_ = v_isSharedCheck_4334_;
goto v_resetjp_4295_;
}
v_resetjp_4295_:
{
lean_object* v___x_4298_; 
lean_inc(v_mvarId_3826_);
v___x_4298_ = l_Lean_MVarId_getType(v_mvarId_3826_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4298_) == 0)
{
lean_object* v_a_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; 
v_a_4299_ = lean_ctor_get(v___x_4298_, 0);
lean_inc(v_a_4299_);
lean_dec_ref_known(v___x_4298_, 1);
v___x_4300_ = l_Lean_LocalDecl_toExpr(v_val_3857_);
v___x_4301_ = l_Lean_Meta_mkAbsurd(v_a_4299_, v_val_4294_, v___x_4300_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4301_) == 0)
{
lean_object* v_a_4302_; lean_object* v___x_4303_; 
v_a_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc(v_a_4302_);
lean_dec_ref_known(v___x_4301_, 1);
v___x_4303_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3826_, v_a_4302_, v___y_4289_);
if (lean_obj_tag(v___x_4303_) == 0)
{
lean_object* v___x_4304_; lean_object* v___x_4306_; 
lean_dec_ref_known(v___x_4303_, 1);
v___x_4304_ = lean_box(v___x_3836_);
if (v_isShared_4297_ == 0)
{
lean_ctor_set(v___x_4296_, 0, v___x_4304_);
v___x_4306_ = v___x_4296_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4309_; 
v_reuseFailAlloc_4309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4309_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4309_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
lean_object* v___x_4307_; lean_object* v___x_4308_; 
v___x_4307_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
lean_ctor_set(v___x_4307_, 1, v___x_3861_);
v___x_4308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
v_a_3843_ = v___x_4308_;
goto v___jp_3842_;
}
}
else
{
lean_object* v_a_4310_; lean_object* v___x_4312_; uint8_t v_isShared_4313_; uint8_t v_isSharedCheck_4317_; 
lean_del_object(v___x_4296_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
v_a_4310_ = lean_ctor_get(v___x_4303_, 0);
v_isSharedCheck_4317_ = !lean_is_exclusive(v___x_4303_);
if (v_isSharedCheck_4317_ == 0)
{
v___x_4312_ = v___x_4303_;
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
else
{
lean_inc(v_a_4310_);
lean_dec(v___x_4303_);
v___x_4312_ = lean_box(0);
v_isShared_4313_ = v_isSharedCheck_4317_;
goto v_resetjp_4311_;
}
v_resetjp_4311_:
{
lean_object* v___x_4315_; 
if (v_isShared_4313_ == 0)
{
v___x_4315_ = v___x_4312_;
goto v_reusejp_4314_;
}
else
{
lean_object* v_reuseFailAlloc_4316_; 
v_reuseFailAlloc_4316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4316_, 0, v_a_4310_);
v___x_4315_ = v_reuseFailAlloc_4316_;
goto v_reusejp_4314_;
}
v_reusejp_4314_:
{
return v___x_4315_;
}
}
}
}
else
{
lean_object* v_a_4318_; lean_object* v___x_4320_; uint8_t v_isShared_4321_; uint8_t v_isSharedCheck_4325_; 
lean_del_object(v___x_4296_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_4318_ = lean_ctor_get(v___x_4301_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4301_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4320_ = v___x_4301_;
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
else
{
lean_inc(v_a_4318_);
lean_dec(v___x_4301_);
v___x_4320_ = lean_box(0);
v_isShared_4321_ = v_isSharedCheck_4325_;
goto v_resetjp_4319_;
}
v_resetjp_4319_:
{
lean_object* v___x_4323_; 
if (v_isShared_4321_ == 0)
{
v___x_4323_ = v___x_4320_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v_a_4318_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_del_object(v___x_4296_);
lean_dec(v_val_4294_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_4326_ = lean_ctor_get(v___x_4298_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4298_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4298_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4298_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
}
else
{
lean_object* v___x_4335_; 
lean_dec(v_a_4293_);
lean_inc_ref(v___x_3977_);
v___x_4335_ = l_Lean_Meta_matchNe_x3f(v___x_3977_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4335_) == 0)
{
lean_object* v_a_4336_; 
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
lean_inc(v_a_4336_);
lean_dec_ref_known(v___x_4335_, 1);
if (lean_obj_tag(v_a_4336_) == 1)
{
lean_object* v_val_4337_; lean_object* v___x_4339_; uint8_t v_isShared_4340_; uint8_t v_isSharedCheck_4407_; 
v_val_4337_ = lean_ctor_get(v_a_4336_, 0);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_a_4336_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4339_ = v_a_4336_;
v_isShared_4340_ = v_isSharedCheck_4407_;
goto v_resetjp_4338_;
}
else
{
lean_inc(v_val_4337_);
lean_dec(v_a_4336_);
v___x_4339_ = lean_box(0);
v_isShared_4340_ = v_isSharedCheck_4407_;
goto v_resetjp_4338_;
}
v_resetjp_4338_:
{
lean_object* v_snd_4341_; lean_object* v_fst_4342_; lean_object* v_snd_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4406_; 
v_snd_4341_ = lean_ctor_get(v_val_4337_, 1);
lean_inc(v_snd_4341_);
lean_dec(v_val_4337_);
v_fst_4342_ = lean_ctor_get(v_snd_4341_, 0);
v_snd_4343_ = lean_ctor_get(v_snd_4341_, 1);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_snd_4341_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4345_ = v_snd_4341_;
v_isShared_4346_ = v_isSharedCheck_4406_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_snd_4343_);
lean_inc(v_fst_4342_);
lean_dec(v_snd_4341_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4406_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v___x_4347_; 
lean_inc(v_fst_4342_);
v___x_4347_ = l_Lean_Meta_isExprDefEq(v_fst_4342_, v_snd_4343_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4347_) == 0)
{
lean_object* v_a_4348_; uint8_t v___x_4349_; 
v_a_4348_ = lean_ctor_get(v___x_4347_, 0);
lean_inc(v_a_4348_);
lean_dec_ref_known(v___x_4347_, 1);
v___x_4349_ = lean_unbox(v_a_4348_);
lean_dec(v_a_4348_);
if (v___x_4349_ == 0)
{
lean_del_object(v___x_4345_);
lean_dec(v_fst_4342_);
lean_del_object(v___x_4339_);
v___y_4242_ = v___y_4288_;
v___y_4243_ = v___y_4289_;
v___y_4244_ = v___y_4290_;
v___y_4245_ = v___y_4291_;
goto v___jp_4241_;
}
else
{
lean_object* v___x_4350_; 
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec_ref(v_config_3825_);
lean_inc(v_mvarId_3826_);
v___x_4350_ = l_Lean_MVarId_getType(v_mvarId_3826_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4350_) == 0)
{
lean_object* v_a_4351_; lean_object* v___x_4352_; 
v_a_4351_ = lean_ctor_get(v___x_4350_, 0);
lean_inc(v_a_4351_);
lean_dec_ref_known(v___x_4350_, 1);
v___x_4352_ = l_Lean_Meta_mkEqRefl(v_fst_4342_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; lean_object* v___x_4354_; lean_object* v___x_4355_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
v___x_4354_ = l_Lean_LocalDecl_toExpr(v_val_3857_);
v___x_4355_ = l_Lean_Meta_mkAbsurd(v_a_4351_, v_a_4353_, v___x_4354_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
if (lean_obj_tag(v___x_4355_) == 0)
{
lean_object* v_a_4356_; lean_object* v___x_4357_; 
v_a_4356_ = lean_ctor_get(v___x_4355_, 0);
lean_inc(v_a_4356_);
lean_dec_ref_known(v___x_4355_, 1);
v___x_4357_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3826_, v_a_4356_, v___y_4289_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v___x_4358_; lean_object* v___x_4360_; 
lean_dec_ref_known(v___x_4357_, 1);
v___x_4358_ = lean_box(v___x_3836_);
if (v_isShared_4340_ == 0)
{
lean_ctor_set(v___x_4339_, 0, v___x_4358_);
v___x_4360_ = v___x_4339_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4358_);
v___x_4360_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
lean_object* v___x_4362_; 
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 1, v___x_3861_);
lean_ctor_set(v___x_4345_, 0, v___x_4360_);
v___x_4362_ = v___x_4345_;
goto v_reusejp_4361_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4360_);
lean_ctor_set(v_reuseFailAlloc_4364_, 1, v___x_3861_);
v___x_4362_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4361_;
}
v_reusejp_4361_:
{
lean_object* v___x_4363_; 
v___x_4363_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4363_, 0, v___x_4362_);
v_a_3843_ = v___x_4363_;
goto v___jp_3842_;
}
}
}
else
{
lean_object* v_a_4366_; lean_object* v___x_4368_; uint8_t v_isShared_4369_; uint8_t v_isSharedCheck_4373_; 
lean_del_object(v___x_4345_);
lean_del_object(v___x_4339_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
v_a_4366_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4373_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4373_ == 0)
{
v___x_4368_ = v___x_4357_;
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
else
{
lean_inc(v_a_4366_);
lean_dec(v___x_4357_);
v___x_4368_ = lean_box(0);
v_isShared_4369_ = v_isSharedCheck_4373_;
goto v_resetjp_4367_;
}
v_resetjp_4367_:
{
lean_object* v___x_4371_; 
if (v_isShared_4369_ == 0)
{
v___x_4371_ = v___x_4368_;
goto v_reusejp_4370_;
}
else
{
lean_object* v_reuseFailAlloc_4372_; 
v_reuseFailAlloc_4372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4372_, 0, v_a_4366_);
v___x_4371_ = v_reuseFailAlloc_4372_;
goto v_reusejp_4370_;
}
v_reusejp_4370_:
{
return v___x_4371_;
}
}
}
}
else
{
lean_object* v_a_4374_; lean_object* v___x_4376_; uint8_t v_isShared_4377_; uint8_t v_isSharedCheck_4381_; 
lean_del_object(v___x_4345_);
lean_del_object(v___x_4339_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_4374_ = lean_ctor_get(v___x_4355_, 0);
v_isSharedCheck_4381_ = !lean_is_exclusive(v___x_4355_);
if (v_isSharedCheck_4381_ == 0)
{
v___x_4376_ = v___x_4355_;
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
else
{
lean_inc(v_a_4374_);
lean_dec(v___x_4355_);
v___x_4376_ = lean_box(0);
v_isShared_4377_ = v_isSharedCheck_4381_;
goto v_resetjp_4375_;
}
v_resetjp_4375_:
{
lean_object* v___x_4379_; 
if (v_isShared_4377_ == 0)
{
v___x_4379_ = v___x_4376_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_a_4374_);
v___x_4379_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
return v___x_4379_;
}
}
}
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
lean_dec(v_a_4351_);
lean_del_object(v___x_4345_);
lean_del_object(v___x_4339_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_4382_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4352_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4352_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
else
{
lean_object* v_a_4390_; lean_object* v___x_4392_; uint8_t v_isShared_4393_; uint8_t v_isSharedCheck_4397_; 
lean_del_object(v___x_4345_);
lean_dec(v_fst_4342_);
lean_del_object(v___x_4339_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_4390_ = lean_ctor_get(v___x_4350_, 0);
v_isSharedCheck_4397_ = !lean_is_exclusive(v___x_4350_);
if (v_isSharedCheck_4397_ == 0)
{
v___x_4392_ = v___x_4350_;
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
else
{
lean_inc(v_a_4390_);
lean_dec(v___x_4350_);
v___x_4392_ = lean_box(0);
v_isShared_4393_ = v_isSharedCheck_4397_;
goto v_resetjp_4391_;
}
v_resetjp_4391_:
{
lean_object* v___x_4395_; 
if (v_isShared_4393_ == 0)
{
v___x_4395_ = v___x_4392_;
goto v_reusejp_4394_;
}
else
{
lean_object* v_reuseFailAlloc_4396_; 
v_reuseFailAlloc_4396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4396_, 0, v_a_4390_);
v___x_4395_ = v_reuseFailAlloc_4396_;
goto v_reusejp_4394_;
}
v_reusejp_4394_:
{
return v___x_4395_;
}
}
}
}
}
else
{
lean_object* v_a_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
lean_del_object(v___x_4345_);
lean_dec(v_fst_4342_);
lean_del_object(v___x_4339_);
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4398_ = lean_ctor_get(v___x_4347_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4347_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4347_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_a_4398_);
lean_dec(v___x_4347_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_a_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4336_);
v___y_4242_ = v___y_4288_;
v___y_4243_ = v___y_4289_;
v___y_4244_ = v___y_4290_;
v___y_4245_ = v___y_4291_;
goto v___jp_4241_;
}
}
else
{
lean_object* v_a_4408_; lean_object* v___x_4410_; uint8_t v_isShared_4411_; uint8_t v_isSharedCheck_4415_; 
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4408_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4415_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4415_ == 0)
{
v___x_4410_ = v___x_4335_;
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
else
{
lean_inc(v_a_4408_);
lean_dec(v___x_4335_);
v___x_4410_ = lean_box(0);
v_isShared_4411_ = v_isSharedCheck_4415_;
goto v_resetjp_4409_;
}
v_resetjp_4409_:
{
lean_object* v___x_4413_; 
if (v_isShared_4411_ == 0)
{
v___x_4413_ = v___x_4410_;
goto v_reusejp_4412_;
}
else
{
lean_object* v_reuseFailAlloc_4414_; 
v_reuseFailAlloc_4414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4414_, 0, v_a_4408_);
v___x_4413_ = v_reuseFailAlloc_4414_;
goto v_reusejp_4412_;
}
v_reusejp_4412_:
{
return v___x_4413_;
}
}
}
}
}
else
{
lean_object* v_a_4416_; lean_object* v___x_4418_; uint8_t v_isShared_4419_; uint8_t v_isSharedCheck_4423_; 
lean_dec_ref(v___x_3977_);
lean_del_object(v___x_3859_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_4416_ = lean_ctor_get(v___x_4292_, 0);
v_isSharedCheck_4423_ = !lean_is_exclusive(v___x_4292_);
if (v_isSharedCheck_4423_ == 0)
{
v___x_4418_ = v___x_4292_;
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
else
{
lean_inc(v_a_4416_);
lean_dec(v___x_4292_);
v___x_4418_ = lean_box(0);
v_isShared_4419_ = v_isSharedCheck_4423_;
goto v_resetjp_4417_;
}
v_resetjp_4417_:
{
lean_object* v___x_4421_; 
if (v_isShared_4419_ == 0)
{
v___x_4421_ = v___x_4418_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4422_; 
v_reuseFailAlloc_4422_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4422_, 0, v_a_4416_);
v___x_4421_ = v_reuseFailAlloc_4422_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
return v___x_4421_;
}
}
}
}
}
else
{
lean_del_object(v___x_3859_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
v_a_3851_ = v___x_3903_;
goto v___jp_3850_;
}
v___jp_3862_:
{
lean_object* v___x_3867_; 
lean_inc(v_mvarId_3826_);
v___x_3867_ = l_Lean_MVarId_getType(v_mvarId_3826_, v___y_3866_, v___y_3865_, v___y_3863_, v___y_3864_);
if (lean_obj_tag(v___x_3867_) == 0)
{
lean_object* v_a_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; 
v_a_3868_ = lean_ctor_get(v___x_3867_, 0);
lean_inc(v_a_3868_);
lean_dec_ref_known(v___x_3867_, 1);
v___x_3869_ = l_Lean_LocalDecl_toExpr(v_val_3857_);
v___x_3870_ = l_Lean_Meta_mkNoConfusion(v_a_3868_, v___x_3869_, v___y_3866_, v___y_3865_, v___y_3863_, v___y_3864_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v___x_3872_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
lean_inc(v_a_3871_);
lean_dec_ref_known(v___x_3870_, 1);
v___x_3872_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3826_, v_a_3871_, v___y_3865_);
if (lean_obj_tag(v___x_3872_) == 0)
{
lean_object* v___x_3873_; lean_object* v___x_3875_; 
lean_dec_ref_known(v___x_3872_, 1);
v___x_3873_ = lean_box(v___x_3836_);
if (v_isShared_3860_ == 0)
{
lean_ctor_set(v___x_3859_, 0, v___x_3873_);
v___x_3875_ = v___x_3859_;
goto v_reusejp_3874_;
}
else
{
lean_object* v_reuseFailAlloc_3878_; 
v_reuseFailAlloc_3878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3878_, 0, v___x_3873_);
v___x_3875_ = v_reuseFailAlloc_3878_;
goto v_reusejp_3874_;
}
v_reusejp_3874_:
{
lean_object* v___x_3876_; lean_object* v___x_3877_; 
v___x_3876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
lean_ctor_set(v___x_3876_, 1, v___x_3861_);
v___x_3877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3876_);
v_a_3843_ = v___x_3877_;
goto v___jp_3842_;
}
}
else
{
lean_object* v_a_3879_; lean_object* v___x_3881_; uint8_t v_isShared_3882_; uint8_t v_isSharedCheck_3886_; 
lean_del_object(v___x_3859_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
v_a_3879_ = lean_ctor_get(v___x_3872_, 0);
v_isSharedCheck_3886_ = !lean_is_exclusive(v___x_3872_);
if (v_isSharedCheck_3886_ == 0)
{
v___x_3881_ = v___x_3872_;
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
else
{
lean_inc(v_a_3879_);
lean_dec(v___x_3872_);
v___x_3881_ = lean_box(0);
v_isShared_3882_ = v_isSharedCheck_3886_;
goto v_resetjp_3880_;
}
v_resetjp_3880_:
{
lean_object* v___x_3884_; 
if (v_isShared_3882_ == 0)
{
v___x_3884_ = v___x_3881_;
goto v_reusejp_3883_;
}
else
{
lean_object* v_reuseFailAlloc_3885_; 
v_reuseFailAlloc_3885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_a_3879_);
v___x_3884_ = v_reuseFailAlloc_3885_;
goto v_reusejp_3883_;
}
v_reusejp_3883_:
{
return v___x_3884_;
}
}
}
}
else
{
lean_object* v_a_3887_; lean_object* v___x_3889_; uint8_t v_isShared_3890_; uint8_t v_isSharedCheck_3894_; 
lean_del_object(v___x_3859_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_3887_ = lean_ctor_get(v___x_3870_, 0);
v_isSharedCheck_3894_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3894_ == 0)
{
v___x_3889_ = v___x_3870_;
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
else
{
lean_inc(v_a_3887_);
lean_dec(v___x_3870_);
v___x_3889_ = lean_box(0);
v_isShared_3890_ = v_isSharedCheck_3894_;
goto v_resetjp_3888_;
}
v_resetjp_3888_:
{
lean_object* v___x_3892_; 
if (v_isShared_3890_ == 0)
{
v___x_3892_ = v___x_3889_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3893_; 
v_reuseFailAlloc_3893_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3893_, 0, v_a_3887_);
v___x_3892_ = v_reuseFailAlloc_3893_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
return v___x_3892_;
}
}
}
}
else
{
lean_object* v_a_3895_; lean_object* v___x_3897_; uint8_t v_isShared_3898_; uint8_t v_isSharedCheck_3902_; 
lean_del_object(v___x_3859_);
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
v_a_3895_ = lean_ctor_get(v___x_3867_, 0);
v_isSharedCheck_3902_ = !lean_is_exclusive(v___x_3867_);
if (v_isSharedCheck_3902_ == 0)
{
v___x_3897_ = v___x_3867_;
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
else
{
lean_inc(v_a_3895_);
lean_dec(v___x_3867_);
v___x_3897_ = lean_box(0);
v_isShared_3898_ = v_isSharedCheck_3902_;
goto v_resetjp_3896_;
}
v_resetjp_3896_:
{
lean_object* v___x_3900_; 
if (v_isShared_3898_ == 0)
{
v___x_3900_ = v___x_3897_;
goto v_reusejp_3899_;
}
else
{
lean_object* v_reuseFailAlloc_3901_; 
v_reuseFailAlloc_3901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3901_, 0, v_a_3895_);
v___x_3900_ = v_reuseFailAlloc_3901_;
goto v_reusejp_3899_;
}
v_reusejp_3899_:
{
return v___x_3900_;
}
}
}
}
v___jp_3904_:
{
lean_object* v_searchFuel_3909_; lean_object* v___x_3910_; lean_object* v___x_3911_; 
v_searchFuel_3909_ = lean_ctor_get(v_config_3825_, 0);
v___x_3910_ = l_Lean_LocalDecl_fvarId(v_val_3857_);
lean_dec(v_val_3857_);
lean_inc(v_searchFuel_3909_);
lean_inc(v_mvarId_3826_);
v___x_3911_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3826_, v___x_3910_, v_searchFuel_3909_, v___y_3908_, v___y_3905_, v___y_3907_, v___y_3906_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; uint8_t v___x_3913_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
lean_inc(v_a_3912_);
lean_dec_ref_known(v___x_3911_, 1);
v___x_3913_ = lean_unbox(v_a_3912_);
lean_dec(v_a_3912_);
if (v___x_3913_ == 0)
{
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
v_a_3851_ = v___x_3903_;
goto v___jp_3850_;
}
else
{
lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v___x_3914_ = lean_box(v___x_3836_);
v___x_3915_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
v___x_3916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
lean_ctor_set(v___x_3916_, 1, v___x_3861_);
v___x_3917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
v_a_3843_ = v___x_3917_;
goto v___jp_3842_;
}
}
else
{
lean_object* v_a_3918_; lean_object* v___x_3920_; uint8_t v_isShared_3921_; uint8_t v_isSharedCheck_3925_; 
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_3918_ = lean_ctor_get(v___x_3911_, 0);
v_isSharedCheck_3925_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3925_ == 0)
{
v___x_3920_ = v___x_3911_;
v_isShared_3921_ = v_isSharedCheck_3925_;
goto v_resetjp_3919_;
}
else
{
lean_inc(v_a_3918_);
lean_dec(v___x_3911_);
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
v___jp_3926_:
{
if (v___y_3931_ == 0)
{
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
v_a_3851_ = v___x_3903_;
goto v___jp_3850_;
}
else
{
v___y_3905_ = v___y_3927_;
v___y_3906_ = v___y_3928_;
v___y_3907_ = v___y_3929_;
v___y_3908_ = v___y_3930_;
goto v___jp_3904_;
}
}
v___jp_3933_:
{
if (v___y_3934_ == 0)
{
v___y_3905_ = v___y_3935_;
v___y_3906_ = v___y_3936_;
v___y_3907_ = v___y_3937_;
v___y_3908_ = v___y_3938_;
goto v___jp_3904_;
}
else
{
v___y_3927_ = v___y_3935_;
v___y_3928_ = v___y_3936_;
v___y_3929_ = v___y_3937_;
v___y_3930_ = v___y_3938_;
v___y_3931_ = v___x_3932_;
goto v___jp_3926_;
}
}
v___jp_3939_:
{
if (v___y_3945_ == 0)
{
v___y_3927_ = v___y_3941_;
v___y_3928_ = v___y_3942_;
v___y_3929_ = v___y_3943_;
v___y_3930_ = v___y_3944_;
v___y_3931_ = v___x_3932_;
goto v___jp_3926_;
}
else
{
v___y_3934_ = v___y_3940_;
v___y_3935_ = v___y_3941_;
v___y_3936_ = v___y_3942_;
v___y_3937_ = v___y_3943_;
v___y_3938_ = v___y_3944_;
goto v___jp_3933_;
}
}
v___jp_3946_:
{
uint8_t v_emptyType_3953_; 
v_emptyType_3953_ = lean_ctor_get_uint8(v_config_3825_, sizeof(void*)*1 + 1);
if (v_emptyType_3953_ == 0)
{
v___y_3940_ = v___y_3947_;
v___y_3941_ = v___y_3950_;
v___y_3942_ = v___y_3952_;
v___y_3943_ = v___y_3951_;
v___y_3944_ = v___y_3949_;
v___y_3945_ = v___x_3932_;
goto v___jp_3939_;
}
else
{
if (v___y_3948_ == 0)
{
v___y_3934_ = v___y_3947_;
v___y_3935_ = v___y_3950_;
v___y_3936_ = v___y_3952_;
v___y_3937_ = v___y_3951_;
v___y_3938_ = v___y_3949_;
goto v___jp_3933_;
}
else
{
v___y_3940_ = v___y_3947_;
v___y_3941_ = v___y_3950_;
v___y_3942_ = v___y_3952_;
v___y_3943_ = v___y_3951_;
v___y_3944_ = v___y_3949_;
v___y_3945_ = v___x_3932_;
goto v___jp_3939_;
}
}
}
v___jp_3954_:
{
if (v___y_3961_ == 0)
{
v___y_3947_ = v___y_3955_;
v___y_3948_ = v___y_3956_;
v___y_3949_ = v___y_3957_;
v___y_3950_ = v___y_3960_;
v___y_3951_ = v___y_3958_;
v___y_3952_ = v___y_3959_;
goto v___jp_3946_;
}
else
{
lean_object* v___x_3962_; 
lean_inc(v_val_3857_);
lean_inc(v_mvarId_3826_);
v___x_3962_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3826_, v_val_3857_, v___y_3957_, v___y_3960_, v___y_3958_, v___y_3959_);
if (lean_obj_tag(v___x_3962_) == 0)
{
lean_object* v_a_3963_; uint8_t v___x_3964_; 
v_a_3963_ = lean_ctor_get(v___x_3962_, 0);
lean_inc(v_a_3963_);
lean_dec_ref_known(v___x_3962_, 1);
v___x_3964_ = lean_unbox(v_a_3963_);
lean_dec(v_a_3963_);
if (v___x_3964_ == 0)
{
v___y_3947_ = v___y_3955_;
v___y_3948_ = v___y_3956_;
v___y_3949_ = v___y_3957_;
v___y_3950_ = v___y_3960_;
v___y_3951_ = v___y_3958_;
v___y_3952_ = v___y_3959_;
goto v___jp_3946_;
}
else
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; 
lean_dec(v_val_3857_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v___x_3965_ = lean_box(v___x_3836_);
v___x_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
v___x_3967_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
lean_ctor_set(v___x_3967_, 1, v___x_3861_);
v___x_3968_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
v_a_3843_ = v___x_3968_;
goto v___jp_3842_;
}
}
else
{
lean_object* v_a_3969_; lean_object* v___x_3971_; uint8_t v_isShared_3972_; uint8_t v_isSharedCheck_3976_; 
lean_dec(v_val_3857_);
lean_del_object(v___x_3840_);
lean_dec(v_snd_3838_);
lean_dec(v_mvarId_3826_);
lean_dec_ref(v_config_3825_);
v_a_3969_ = lean_ctor_get(v___x_3962_, 0);
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3962_);
if (v_isSharedCheck_3976_ == 0)
{
v___x_3971_ = v___x_3962_;
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
else
{
lean_inc(v_a_3969_);
lean_dec(v___x_3962_);
v___x_3971_ = lean_box(0);
v_isShared_3972_ = v_isSharedCheck_3976_;
goto v_resetjp_3970_;
}
v_resetjp_3970_:
{
lean_object* v___x_3974_; 
if (v_isShared_3972_ == 0)
{
v___x_3974_ = v___x_3971_;
goto v_reusejp_3973_;
}
else
{
lean_object* v_reuseFailAlloc_3975_; 
v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
v___x_3974_ = v_reuseFailAlloc_3975_;
goto v_reusejp_3973_;
}
v_reusejp_3973_:
{
return v___x_3974_;
}
}
}
}
}
}
}
v___jp_3842_:
{
lean_object* v___x_3844_; lean_object* v___x_3846_; 
v___x_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3844_, 0, v_a_3843_);
if (v_isShared_3841_ == 0)
{
lean_ctor_set(v___x_3840_, 0, v___x_3844_);
v___x_3846_ = v___x_3840_;
goto v_reusejp_3845_;
}
else
{
lean_object* v_reuseFailAlloc_3848_; 
v_reuseFailAlloc_3848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3848_, 0, v___x_3844_);
lean_ctor_set(v_reuseFailAlloc_3848_, 1, v_snd_3838_);
v___x_3846_ = v_reuseFailAlloc_3848_;
goto v_reusejp_3845_;
}
v_reusejp_3845_:
{
lean_object* v___x_3847_; 
v___x_3847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3846_);
return v___x_3847_;
}
}
v___jp_3850_:
{
lean_object* v___x_3852_; size_t v___x_3853_; size_t v___x_3854_; lean_object* v___x_3855_; 
v___x_3852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3849_);
lean_ctor_set(v___x_3852_, 1, v_a_3851_);
v___x_3853_ = ((size_t)1ULL);
v___x_3854_ = lean_usize_add(v_i_3829_, v___x_3853_);
v___x_3855_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3825_, v_mvarId_3826_, v_as_3827_, v_sz_3828_, v___x_3854_, v___x_3852_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
return v___x_3855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4497_, lean_object* v_mvarId_4498_, lean_object* v_as_4499_, lean_object* v_sz_4500_, lean_object* v_i_4501_, lean_object* v_b_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_){
_start:
{
size_t v_sz_boxed_4508_; size_t v_i_boxed_4509_; lean_object* v_res_4510_; 
v_sz_boxed_4508_ = lean_unbox_usize(v_sz_4500_);
lean_dec(v_sz_4500_);
v_i_boxed_4509_ = lean_unbox_usize(v_i_4501_);
lean_dec(v_i_4501_);
v_res_4510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4497_, v_mvarId_4498_, v_as_4499_, v_sz_boxed_4508_, v_i_boxed_4509_, v_b_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
lean_dec(v___y_4506_);
lean_dec_ref(v___y_4505_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec_ref(v_as_4499_);
return v_res_4510_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4511_, lean_object* v_config_4512_, lean_object* v_mvarId_4513_, lean_object* v_n_4514_, lean_object* v_b_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_){
_start:
{
if (lean_obj_tag(v_n_4514_) == 0)
{
lean_object* v_cs_4521_; lean_object* v___x_4522_; lean_object* v___x_4523_; size_t v_sz_4524_; size_t v___x_4525_; lean_object* v___x_4526_; 
v_cs_4521_ = lean_ctor_get(v_n_4514_, 0);
v___x_4522_ = lean_box(0);
v___x_4523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4523_, 0, v___x_4522_);
lean_ctor_set(v___x_4523_, 1, v_b_4515_);
v_sz_4524_ = lean_array_size(v_cs_4521_);
v___x_4525_ = ((size_t)0ULL);
v___x_4526_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4511_, v_config_4512_, v_mvarId_4513_, v_cs_4521_, v_sz_4524_, v___x_4525_, v___x_4523_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4526_) == 0)
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4541_; 
v_a_4527_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4541_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4541_ == 0)
{
v___x_4529_ = v___x_4526_;
v_isShared_4530_ = v_isSharedCheck_4541_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4526_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4541_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v_fst_4531_; 
v_fst_4531_ = lean_ctor_get(v_a_4527_, 0);
if (lean_obj_tag(v_fst_4531_) == 0)
{
lean_object* v_snd_4532_; lean_object* v___x_4533_; lean_object* v___x_4535_; 
v_snd_4532_ = lean_ctor_get(v_a_4527_, 1);
lean_inc(v_snd_4532_);
lean_dec(v_a_4527_);
v___x_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4533_, 0, v_snd_4532_);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v___x_4533_);
v___x_4535_ = v___x_4529_;
goto v_reusejp_4534_;
}
else
{
lean_object* v_reuseFailAlloc_4536_; 
v_reuseFailAlloc_4536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4536_, 0, v___x_4533_);
v___x_4535_ = v_reuseFailAlloc_4536_;
goto v_reusejp_4534_;
}
v_reusejp_4534_:
{
return v___x_4535_;
}
}
else
{
lean_object* v_val_4537_; lean_object* v___x_4539_; 
lean_inc_ref(v_fst_4531_);
lean_dec(v_a_4527_);
v_val_4537_ = lean_ctor_get(v_fst_4531_, 0);
lean_inc(v_val_4537_);
lean_dec_ref_known(v_fst_4531_, 1);
if (v_isShared_4530_ == 0)
{
lean_ctor_set(v___x_4529_, 0, v_val_4537_);
v___x_4539_ = v___x_4529_;
goto v_reusejp_4538_;
}
else
{
lean_object* v_reuseFailAlloc_4540_; 
v_reuseFailAlloc_4540_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4540_, 0, v_val_4537_);
v___x_4539_ = v_reuseFailAlloc_4540_;
goto v_reusejp_4538_;
}
v_reusejp_4538_:
{
return v___x_4539_;
}
}
}
}
else
{
lean_object* v_a_4542_; lean_object* v___x_4544_; uint8_t v_isShared_4545_; uint8_t v_isSharedCheck_4549_; 
v_a_4542_ = lean_ctor_get(v___x_4526_, 0);
v_isSharedCheck_4549_ = !lean_is_exclusive(v___x_4526_);
if (v_isSharedCheck_4549_ == 0)
{
v___x_4544_ = v___x_4526_;
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
else
{
lean_inc(v_a_4542_);
lean_dec(v___x_4526_);
v___x_4544_ = lean_box(0);
v_isShared_4545_ = v_isSharedCheck_4549_;
goto v_resetjp_4543_;
}
v_resetjp_4543_:
{
lean_object* v___x_4547_; 
if (v_isShared_4545_ == 0)
{
v___x_4547_ = v___x_4544_;
goto v_reusejp_4546_;
}
else
{
lean_object* v_reuseFailAlloc_4548_; 
v_reuseFailAlloc_4548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4548_, 0, v_a_4542_);
v___x_4547_ = v_reuseFailAlloc_4548_;
goto v_reusejp_4546_;
}
v_reusejp_4546_:
{
return v___x_4547_;
}
}
}
}
else
{
lean_object* v_vs_4550_; lean_object* v___x_4551_; lean_object* v___x_4552_; size_t v_sz_4553_; size_t v___x_4554_; lean_object* v___x_4555_; 
v_vs_4550_ = lean_ctor_get(v_n_4514_, 0);
v___x_4551_ = lean_box(0);
v___x_4552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4552_, 0, v___x_4551_);
lean_ctor_set(v___x_4552_, 1, v_b_4515_);
v_sz_4553_ = lean_array_size(v_vs_4550_);
v___x_4554_ = ((size_t)0ULL);
v___x_4555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4512_, v_mvarId_4513_, v_vs_4550_, v_sz_4553_, v___x_4554_, v___x_4552_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
if (lean_obj_tag(v___x_4555_) == 0)
{
lean_object* v_a_4556_; lean_object* v___x_4558_; uint8_t v_isShared_4559_; uint8_t v_isSharedCheck_4570_; 
v_a_4556_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4570_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4570_ == 0)
{
v___x_4558_ = v___x_4555_;
v_isShared_4559_ = v_isSharedCheck_4570_;
goto v_resetjp_4557_;
}
else
{
lean_inc(v_a_4556_);
lean_dec(v___x_4555_);
v___x_4558_ = lean_box(0);
v_isShared_4559_ = v_isSharedCheck_4570_;
goto v_resetjp_4557_;
}
v_resetjp_4557_:
{
lean_object* v_fst_4560_; 
v_fst_4560_ = lean_ctor_get(v_a_4556_, 0);
if (lean_obj_tag(v_fst_4560_) == 0)
{
lean_object* v_snd_4561_; lean_object* v___x_4562_; lean_object* v___x_4564_; 
v_snd_4561_ = lean_ctor_get(v_a_4556_, 1);
lean_inc(v_snd_4561_);
lean_dec(v_a_4556_);
v___x_4562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4562_, 0, v_snd_4561_);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 0, v___x_4562_);
v___x_4564_ = v___x_4558_;
goto v_reusejp_4563_;
}
else
{
lean_object* v_reuseFailAlloc_4565_; 
v_reuseFailAlloc_4565_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4565_, 0, v___x_4562_);
v___x_4564_ = v_reuseFailAlloc_4565_;
goto v_reusejp_4563_;
}
v_reusejp_4563_:
{
return v___x_4564_;
}
}
else
{
lean_object* v_val_4566_; lean_object* v___x_4568_; 
lean_inc_ref(v_fst_4560_);
lean_dec(v_a_4556_);
v_val_4566_ = lean_ctor_get(v_fst_4560_, 0);
lean_inc(v_val_4566_);
lean_dec_ref_known(v_fst_4560_, 1);
if (v_isShared_4559_ == 0)
{
lean_ctor_set(v___x_4558_, 0, v_val_4566_);
v___x_4568_ = v___x_4558_;
goto v_reusejp_4567_;
}
else
{
lean_object* v_reuseFailAlloc_4569_; 
v_reuseFailAlloc_4569_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4569_, 0, v_val_4566_);
v___x_4568_ = v_reuseFailAlloc_4569_;
goto v_reusejp_4567_;
}
v_reusejp_4567_:
{
return v___x_4568_;
}
}
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
v_a_4571_ = lean_ctor_get(v___x_4555_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4555_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4555_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4555_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4579_, lean_object* v_config_4580_, lean_object* v_mvarId_4581_, lean_object* v_as_4582_, size_t v_sz_4583_, size_t v_i_4584_, lean_object* v_b_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_){
_start:
{
uint8_t v___x_4591_; 
v___x_4591_ = lean_usize_dec_lt(v_i_4584_, v_sz_4583_);
if (v___x_4591_ == 0)
{
lean_object* v___x_4592_; 
lean_dec(v_mvarId_4581_);
lean_dec_ref(v_config_4580_);
v___x_4592_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4592_, 0, v_b_4585_);
return v___x_4592_;
}
else
{
lean_object* v_snd_4593_; lean_object* v___x_4595_; uint8_t v_isShared_4596_; uint8_t v_isSharedCheck_4627_; 
v_snd_4593_ = lean_ctor_get(v_b_4585_, 1);
v_isSharedCheck_4627_ = !lean_is_exclusive(v_b_4585_);
if (v_isSharedCheck_4627_ == 0)
{
lean_object* v_unused_4628_; 
v_unused_4628_ = lean_ctor_get(v_b_4585_, 0);
lean_dec(v_unused_4628_);
v___x_4595_ = v_b_4585_;
v_isShared_4596_ = v_isSharedCheck_4627_;
goto v_resetjp_4594_;
}
else
{
lean_inc(v_snd_4593_);
lean_dec(v_b_4585_);
v___x_4595_ = lean_box(0);
v_isShared_4596_ = v_isSharedCheck_4627_;
goto v_resetjp_4594_;
}
v_resetjp_4594_:
{
lean_object* v_a_4597_; lean_object* v___x_4598_; 
v_a_4597_ = lean_array_uget_borrowed(v_as_4582_, v_i_4584_);
lean_inc(v_snd_4593_);
lean_inc(v_mvarId_4581_);
lean_inc_ref(v_config_4580_);
v___x_4598_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4579_, v_config_4580_, v_mvarId_4581_, v_a_4597_, v_snd_4593_, v___y_4586_, v___y_4587_, v___y_4588_, v___y_4589_);
if (lean_obj_tag(v___x_4598_) == 0)
{
lean_object* v_a_4599_; lean_object* v___x_4601_; uint8_t v_isShared_4602_; uint8_t v_isSharedCheck_4618_; 
v_a_4599_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4618_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4618_ == 0)
{
v___x_4601_ = v___x_4598_;
v_isShared_4602_ = v_isSharedCheck_4618_;
goto v_resetjp_4600_;
}
else
{
lean_inc(v_a_4599_);
lean_dec(v___x_4598_);
v___x_4601_ = lean_box(0);
v_isShared_4602_ = v_isSharedCheck_4618_;
goto v_resetjp_4600_;
}
v_resetjp_4600_:
{
if (lean_obj_tag(v_a_4599_) == 0)
{
lean_object* v___x_4603_; lean_object* v___x_4605_; 
lean_dec(v_mvarId_4581_);
lean_dec_ref(v_config_4580_);
v___x_4603_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4603_, 0, v_a_4599_);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 0, v___x_4603_);
v___x_4605_ = v___x_4595_;
goto v_reusejp_4604_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4603_);
lean_ctor_set(v_reuseFailAlloc_4609_, 1, v_snd_4593_);
v___x_4605_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4604_;
}
v_reusejp_4604_:
{
lean_object* v___x_4607_; 
if (v_isShared_4602_ == 0)
{
lean_ctor_set(v___x_4601_, 0, v___x_4605_);
v___x_4607_ = v___x_4601_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4605_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
else
{
lean_object* v_a_4610_; lean_object* v___x_4611_; lean_object* v___x_4613_; 
lean_del_object(v___x_4601_);
lean_dec(v_snd_4593_);
v_a_4610_ = lean_ctor_get(v_a_4599_, 0);
lean_inc(v_a_4610_);
lean_dec_ref_known(v_a_4599_, 1);
v___x_4611_ = lean_box(0);
if (v_isShared_4596_ == 0)
{
lean_ctor_set(v___x_4595_, 1, v_a_4610_);
lean_ctor_set(v___x_4595_, 0, v___x_4611_);
v___x_4613_ = v___x_4595_;
goto v_reusejp_4612_;
}
else
{
lean_object* v_reuseFailAlloc_4617_; 
v_reuseFailAlloc_4617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4617_, 0, v___x_4611_);
lean_ctor_set(v_reuseFailAlloc_4617_, 1, v_a_4610_);
v___x_4613_ = v_reuseFailAlloc_4617_;
goto v_reusejp_4612_;
}
v_reusejp_4612_:
{
size_t v___x_4614_; size_t v___x_4615_; 
v___x_4614_ = ((size_t)1ULL);
v___x_4615_ = lean_usize_add(v_i_4584_, v___x_4614_);
v_i_4584_ = v___x_4615_;
v_b_4585_ = v___x_4613_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4626_; 
lean_del_object(v___x_4595_);
lean_dec(v_snd_4593_);
lean_dec(v_mvarId_4581_);
lean_dec_ref(v_config_4580_);
v_a_4619_ = lean_ctor_get(v___x_4598_, 0);
v_isSharedCheck_4626_ = !lean_is_exclusive(v___x_4598_);
if (v_isSharedCheck_4626_ == 0)
{
v___x_4621_ = v___x_4598_;
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_a_4619_);
lean_dec(v___x_4598_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4626_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
lean_object* v___x_4624_; 
if (v_isShared_4622_ == 0)
{
v___x_4624_ = v___x_4621_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_a_4619_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4629_, lean_object* v_config_4630_, lean_object* v_mvarId_4631_, lean_object* v_as_4632_, lean_object* v_sz_4633_, lean_object* v_i_4634_, lean_object* v_b_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_){
_start:
{
size_t v_sz_boxed_4641_; size_t v_i_boxed_4642_; lean_object* v_res_4643_; 
v_sz_boxed_4641_ = lean_unbox_usize(v_sz_4633_);
lean_dec(v_sz_4633_);
v_i_boxed_4642_ = lean_unbox_usize(v_i_4634_);
lean_dec(v_i_4634_);
v_res_4643_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4629_, v_config_4630_, v_mvarId_4631_, v_as_4632_, v_sz_boxed_4641_, v_i_boxed_4642_, v_b_4635_, v___y_4636_, v___y_4637_, v___y_4638_, v___y_4639_);
lean_dec(v___y_4639_);
lean_dec_ref(v___y_4638_);
lean_dec(v___y_4637_);
lean_dec_ref(v___y_4636_);
lean_dec_ref(v_as_4632_);
lean_dec_ref(v_init_4629_);
return v_res_4643_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4644_, lean_object* v_config_4645_, lean_object* v_mvarId_4646_, lean_object* v_n_4647_, lean_object* v_b_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4644_, v_config_4645_, v_mvarId_4646_, v_n_4647_, v_b_4648_, v___y_4649_, v___y_4650_, v___y_4651_, v___y_4652_);
lean_dec(v___y_4652_);
lean_dec_ref(v___y_4651_);
lean_dec(v___y_4650_);
lean_dec_ref(v___y_4649_);
lean_dec_ref(v_n_4647_);
lean_dec_ref(v_init_4644_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4655_, lean_object* v_mvarId_4656_, lean_object* v_t_4657_, lean_object* v_init_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v_root_4664_; lean_object* v_tail_4665_; lean_object* v___x_4666_; 
v_root_4664_ = lean_ctor_get(v_t_4657_, 0);
v_tail_4665_ = lean_ctor_get(v_t_4657_, 1);
lean_inc(v_mvarId_4656_);
lean_inc_ref(v_config_4655_);
lean_inc_ref(v_init_4658_);
v___x_4666_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4658_, v_config_4655_, v_mvarId_4656_, v_root_4664_, v_init_4658_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
lean_dec_ref(v_init_4658_);
if (lean_obj_tag(v___x_4666_) == 0)
{
lean_object* v_a_4667_; lean_object* v___x_4669_; uint8_t v_isShared_4670_; uint8_t v_isSharedCheck_4703_; 
v_a_4667_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4669_ = v___x_4666_;
v_isShared_4670_ = v_isSharedCheck_4703_;
goto v_resetjp_4668_;
}
else
{
lean_inc(v_a_4667_);
lean_dec(v___x_4666_);
v___x_4669_ = lean_box(0);
v_isShared_4670_ = v_isSharedCheck_4703_;
goto v_resetjp_4668_;
}
v_resetjp_4668_:
{
if (lean_obj_tag(v_a_4667_) == 0)
{
lean_object* v_a_4671_; lean_object* v___x_4673_; 
lean_dec(v_mvarId_4656_);
lean_dec_ref(v_config_4655_);
v_a_4671_ = lean_ctor_get(v_a_4667_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v_a_4667_, 1);
if (v_isShared_4670_ == 0)
{
lean_ctor_set(v___x_4669_, 0, v_a_4671_);
v___x_4673_ = v___x_4669_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4674_; 
v_reuseFailAlloc_4674_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4674_, 0, v_a_4671_);
v___x_4673_ = v_reuseFailAlloc_4674_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
return v___x_4673_;
}
}
else
{
lean_object* v_a_4675_; lean_object* v___x_4676_; lean_object* v___x_4677_; size_t v_sz_4678_; size_t v___x_4679_; lean_object* v___x_4680_; 
lean_del_object(v___x_4669_);
v_a_4675_ = lean_ctor_get(v_a_4667_, 0);
lean_inc(v_a_4675_);
lean_dec_ref_known(v_a_4667_, 1);
v___x_4676_ = lean_box(0);
v___x_4677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4677_, 0, v___x_4676_);
lean_ctor_set(v___x_4677_, 1, v_a_4675_);
v_sz_4678_ = lean_array_size(v_tail_4665_);
v___x_4679_ = ((size_t)0ULL);
v___x_4680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4655_, v_mvarId_4656_, v_tail_4665_, v_sz_4678_, v___x_4679_, v___x_4677_, v___y_4659_, v___y_4660_, v___y_4661_, v___y_4662_);
if (lean_obj_tag(v___x_4680_) == 0)
{
lean_object* v_a_4681_; lean_object* v___x_4683_; uint8_t v_isShared_4684_; uint8_t v_isSharedCheck_4694_; 
v_a_4681_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4683_ = v___x_4680_;
v_isShared_4684_ = v_isSharedCheck_4694_;
goto v_resetjp_4682_;
}
else
{
lean_inc(v_a_4681_);
lean_dec(v___x_4680_);
v___x_4683_ = lean_box(0);
v_isShared_4684_ = v_isSharedCheck_4694_;
goto v_resetjp_4682_;
}
v_resetjp_4682_:
{
lean_object* v_fst_4685_; 
v_fst_4685_ = lean_ctor_get(v_a_4681_, 0);
if (lean_obj_tag(v_fst_4685_) == 0)
{
lean_object* v_snd_4686_; lean_object* v___x_4688_; 
v_snd_4686_ = lean_ctor_get(v_a_4681_, 1);
lean_inc(v_snd_4686_);
lean_dec(v_a_4681_);
if (v_isShared_4684_ == 0)
{
lean_ctor_set(v___x_4683_, 0, v_snd_4686_);
v___x_4688_ = v___x_4683_;
goto v_reusejp_4687_;
}
else
{
lean_object* v_reuseFailAlloc_4689_; 
v_reuseFailAlloc_4689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4689_, 0, v_snd_4686_);
v___x_4688_ = v_reuseFailAlloc_4689_;
goto v_reusejp_4687_;
}
v_reusejp_4687_:
{
return v___x_4688_;
}
}
else
{
lean_object* v_val_4690_; lean_object* v___x_4692_; 
lean_inc_ref(v_fst_4685_);
lean_dec(v_a_4681_);
v_val_4690_ = lean_ctor_get(v_fst_4685_, 0);
lean_inc(v_val_4690_);
lean_dec_ref_known(v_fst_4685_, 1);
if (v_isShared_4684_ == 0)
{
lean_ctor_set(v___x_4683_, 0, v_val_4690_);
v___x_4692_ = v___x_4683_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_val_4690_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
else
{
lean_object* v_a_4695_; lean_object* v___x_4697_; uint8_t v_isShared_4698_; uint8_t v_isSharedCheck_4702_; 
v_a_4695_ = lean_ctor_get(v___x_4680_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4680_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4697_ = v___x_4680_;
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
else
{
lean_inc(v_a_4695_);
lean_dec(v___x_4680_);
v___x_4697_ = lean_box(0);
v_isShared_4698_ = v_isSharedCheck_4702_;
goto v_resetjp_4696_;
}
v_resetjp_4696_:
{
lean_object* v___x_4700_; 
if (v_isShared_4698_ == 0)
{
v___x_4700_ = v___x_4697_;
goto v_reusejp_4699_;
}
else
{
lean_object* v_reuseFailAlloc_4701_; 
v_reuseFailAlloc_4701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4701_, 0, v_a_4695_);
v___x_4700_ = v_reuseFailAlloc_4701_;
goto v_reusejp_4699_;
}
v_reusejp_4699_:
{
return v___x_4700_;
}
}
}
}
}
}
else
{
lean_object* v_a_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4711_; 
lean_dec(v_mvarId_4656_);
lean_dec_ref(v_config_4655_);
v_a_4704_ = lean_ctor_get(v___x_4666_, 0);
v_isSharedCheck_4711_ = !lean_is_exclusive(v___x_4666_);
if (v_isSharedCheck_4711_ == 0)
{
v___x_4706_ = v___x_4666_;
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_a_4704_);
lean_dec(v___x_4666_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4711_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
lean_object* v___x_4709_; 
if (v_isShared_4707_ == 0)
{
v___x_4709_ = v___x_4706_;
goto v_reusejp_4708_;
}
else
{
lean_object* v_reuseFailAlloc_4710_; 
v_reuseFailAlloc_4710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4710_, 0, v_a_4704_);
v___x_4709_ = v_reuseFailAlloc_4710_;
goto v_reusejp_4708_;
}
v_reusejp_4708_:
{
return v___x_4709_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4712_, lean_object* v_mvarId_4713_, lean_object* v_t_4714_, lean_object* v_init_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4712_, v_mvarId_4713_, v_t_4714_, v_init_4715_, v___y_4716_, v___y_4717_, v___y_4718_, v___y_4719_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
lean_dec(v___y_4717_);
lean_dec_ref(v___y_4716_);
lean_dec_ref(v_t_4714_);
return v_res_4721_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4722_, lean_object* v___x_4723_, lean_object* v_config_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_){
_start:
{
lean_object* v___x_4730_; 
lean_inc(v_mvarId_4722_);
v___x_4730_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4722_, v___x_4723_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v___x_4731_; 
lean_dec_ref_known(v___x_4730_, 1);
lean_inc(v_mvarId_4722_);
v___x_4731_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4722_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v_a_4732_; lean_object* v___x_4734_; uint8_t v_isShared_4735_; uint8_t v_isSharedCheck_4765_; 
v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4765_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4765_ == 0)
{
v___x_4734_ = v___x_4731_;
v_isShared_4735_ = v_isSharedCheck_4765_;
goto v_resetjp_4733_;
}
else
{
lean_inc(v_a_4732_);
lean_dec(v___x_4731_);
v___x_4734_ = lean_box(0);
v_isShared_4735_ = v_isSharedCheck_4765_;
goto v_resetjp_4733_;
}
v_resetjp_4733_:
{
uint8_t v___x_4736_; 
v___x_4736_ = lean_unbox(v_a_4732_);
if (v___x_4736_ == 0)
{
lean_object* v_lctx_4737_; lean_object* v_decls_4738_; lean_object* v___x_4739_; lean_object* v___x_4740_; 
lean_del_object(v___x_4734_);
v_lctx_4737_ = lean_ctor_get(v___y_4725_, 2);
v_decls_4738_ = lean_ctor_get(v_lctx_4737_, 1);
v___x_4739_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4740_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4724_, v_mvarId_4722_, v_decls_4738_, v___x_4739_, v___y_4725_, v___y_4726_, v___y_4727_, v___y_4728_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4753_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4743_ = v___x_4740_;
v_isShared_4744_ = v_isSharedCheck_4753_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4740_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4753_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v_fst_4745_; 
v_fst_4745_ = lean_ctor_get(v_a_4741_, 0);
lean_inc(v_fst_4745_);
lean_dec(v_a_4741_);
if (lean_obj_tag(v_fst_4745_) == 0)
{
lean_object* v___x_4747_; 
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v_a_4732_);
v___x_4747_ = v___x_4743_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_a_4732_);
v___x_4747_ = v_reuseFailAlloc_4748_;
goto v_reusejp_4746_;
}
v_reusejp_4746_:
{
return v___x_4747_;
}
}
else
{
lean_object* v_val_4749_; lean_object* v___x_4751_; 
lean_dec(v_a_4732_);
v_val_4749_ = lean_ctor_get(v_fst_4745_, 0);
lean_inc(v_val_4749_);
lean_dec_ref_known(v_fst_4745_, 1);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v_val_4749_);
v___x_4751_ = v___x_4743_;
goto v_reusejp_4750_;
}
else
{
lean_object* v_reuseFailAlloc_4752_; 
v_reuseFailAlloc_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4752_, 0, v_val_4749_);
v___x_4751_ = v_reuseFailAlloc_4752_;
goto v_reusejp_4750_;
}
v_reusejp_4750_:
{
return v___x_4751_;
}
}
}
}
else
{
lean_object* v_a_4754_; lean_object* v___x_4756_; uint8_t v_isShared_4757_; uint8_t v_isSharedCheck_4761_; 
lean_dec(v_a_4732_);
v_a_4754_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4756_ = v___x_4740_;
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4740_);
v___x_4756_ = lean_box(0);
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
v_resetjp_4755_:
{
lean_object* v___x_4759_; 
if (v_isShared_4757_ == 0)
{
v___x_4759_ = v___x_4756_;
goto v_reusejp_4758_;
}
else
{
lean_object* v_reuseFailAlloc_4760_; 
v_reuseFailAlloc_4760_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4760_, 0, v_a_4754_);
v___x_4759_ = v_reuseFailAlloc_4760_;
goto v_reusejp_4758_;
}
v_reusejp_4758_:
{
return v___x_4759_;
}
}
}
}
else
{
lean_object* v___x_4763_; 
lean_dec_ref(v_config_4724_);
lean_dec(v_mvarId_4722_);
if (v_isShared_4735_ == 0)
{
v___x_4763_ = v___x_4734_;
goto v_reusejp_4762_;
}
else
{
lean_object* v_reuseFailAlloc_4764_; 
v_reuseFailAlloc_4764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_a_4732_);
v___x_4763_ = v_reuseFailAlloc_4764_;
goto v_reusejp_4762_;
}
v_reusejp_4762_:
{
return v___x_4763_;
}
}
}
}
else
{
lean_dec_ref(v_config_4724_);
lean_dec(v_mvarId_4722_);
return v___x_4731_;
}
}
else
{
lean_object* v_a_4766_; lean_object* v___x_4768_; uint8_t v_isShared_4769_; uint8_t v_isSharedCheck_4773_; 
lean_dec_ref(v_config_4724_);
lean_dec(v_mvarId_4722_);
v_a_4766_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4773_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4773_ == 0)
{
v___x_4768_ = v___x_4730_;
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
else
{
lean_inc(v_a_4766_);
lean_dec(v___x_4730_);
v___x_4768_ = lean_box(0);
v_isShared_4769_ = v_isSharedCheck_4773_;
goto v_resetjp_4767_;
}
v_resetjp_4767_:
{
lean_object* v___x_4771_; 
if (v_isShared_4769_ == 0)
{
v___x_4771_ = v___x_4768_;
goto v_reusejp_4770_;
}
else
{
lean_object* v_reuseFailAlloc_4772_; 
v_reuseFailAlloc_4772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4772_, 0, v_a_4766_);
v___x_4771_ = v_reuseFailAlloc_4772_;
goto v_reusejp_4770_;
}
v_reusejp_4770_:
{
return v___x_4771_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4774_, lean_object* v___x_4775_, lean_object* v_config_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_){
_start:
{
lean_object* v_res_4782_; 
v_res_4782_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4774_, v___x_4775_, v_config_4776_, v___y_4777_, v___y_4778_, v___y_4779_, v___y_4780_);
lean_dec(v___y_4780_);
lean_dec_ref(v___y_4779_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
return v_res_4782_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4785_, lean_object* v_config_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_){
_start:
{
lean_object* v___x_4792_; lean_object* v___f_4793_; lean_object* v___x_4794_; 
v___x_4792_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4785_);
v___f_4793_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4793_, 0, v_mvarId_4785_);
lean_closure_set(v___f_4793_, 1, v___x_4792_);
lean_closure_set(v___f_4793_, 2, v_config_4786_);
v___x_4794_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4785_, v___f_4793_, v_a_4787_, v_a_4788_, v_a_4789_, v_a_4790_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4795_, lean_object* v_config_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_){
_start:
{
lean_object* v_res_4802_; 
v_res_4802_ = l_Lean_MVarId_contradictionCore(v_mvarId_4795_, v_config_4796_, v_a_4797_, v_a_4798_, v_a_4799_, v_a_4800_);
lean_dec(v_a_4800_);
lean_dec_ref(v_a_4799_);
lean_dec(v_a_4798_);
lean_dec_ref(v_a_4797_);
return v_res_4802_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4803_, lean_object* v_config_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_){
_start:
{
lean_object* v___x_4810_; 
lean_inc(v_mvarId_4803_);
v___x_4810_ = l_Lean_MVarId_contradictionCore(v_mvarId_4803_, v_config_4804_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
if (lean_obj_tag(v___x_4810_) == 0)
{
lean_object* v_a_4811_; lean_object* v___x_4813_; uint8_t v_isShared_4814_; uint8_t v_isSharedCheck_4823_; 
v_a_4811_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4813_ = v___x_4810_;
v_isShared_4814_ = v_isSharedCheck_4823_;
goto v_resetjp_4812_;
}
else
{
lean_inc(v_a_4811_);
lean_dec(v___x_4810_);
v___x_4813_ = lean_box(0);
v_isShared_4814_ = v_isSharedCheck_4823_;
goto v_resetjp_4812_;
}
v_resetjp_4812_:
{
uint8_t v___x_4815_; 
v___x_4815_ = lean_unbox(v_a_4811_);
lean_dec(v_a_4811_);
if (v___x_4815_ == 0)
{
lean_object* v___x_4816_; lean_object* v___x_4817_; lean_object* v___x_4818_; 
lean_del_object(v___x_4813_);
v___x_4816_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4817_ = lean_box(0);
v___x_4818_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4816_, v_mvarId_4803_, v___x_4817_, v_a_4805_, v_a_4806_, v_a_4807_, v_a_4808_);
return v___x_4818_;
}
else
{
lean_object* v___x_4819_; lean_object* v___x_4821_; 
lean_dec(v_mvarId_4803_);
v___x_4819_ = lean_box(0);
if (v_isShared_4814_ == 0)
{
lean_ctor_set(v___x_4813_, 0, v___x_4819_);
v___x_4821_ = v___x_4813_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v___x_4819_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
else
{
lean_object* v_a_4824_; lean_object* v___x_4826_; uint8_t v_isShared_4827_; uint8_t v_isSharedCheck_4831_; 
lean_dec(v_mvarId_4803_);
v_a_4824_ = lean_ctor_get(v___x_4810_, 0);
v_isSharedCheck_4831_ = !lean_is_exclusive(v___x_4810_);
if (v_isSharedCheck_4831_ == 0)
{
v___x_4826_ = v___x_4810_;
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
else
{
lean_inc(v_a_4824_);
lean_dec(v___x_4810_);
v___x_4826_ = lean_box(0);
v_isShared_4827_ = v_isSharedCheck_4831_;
goto v_resetjp_4825_;
}
v_resetjp_4825_:
{
lean_object* v___x_4829_; 
if (v_isShared_4827_ == 0)
{
v___x_4829_ = v___x_4826_;
goto v_reusejp_4828_;
}
else
{
lean_object* v_reuseFailAlloc_4830_; 
v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
v___x_4829_ = v_reuseFailAlloc_4830_;
goto v_reusejp_4828_;
}
v_reusejp_4828_:
{
return v___x_4829_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4832_, lean_object* v_config_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_){
_start:
{
lean_object* v_res_4839_; 
v_res_4839_ = l_Lean_MVarId_contradiction(v_mvarId_4832_, v_config_4833_, v_a_4834_, v_a_4835_, v_a_4836_, v_a_4837_);
lean_dec(v_a_4837_);
lean_dec_ref(v_a_4836_);
lean_dec(v_a_4835_);
lean_dec_ref(v_a_4834_);
return v_res_4839_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4902_; uint8_t v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; 
v___x_4902_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4903_ = 0;
v___x_4904_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4905_ = l_Lean_registerTraceClass(v___x_4902_, v___x_4903_, v___x_4904_);
return v___x_4905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4906_){
_start:
{
lean_object* v_res_4907_; 
v_res_4907_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4907_;
}
}
lean_object* runtime_initialize_Lean_Meta_Tactic_Assumption(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Cases(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_HasNotBit(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Contradiction(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
