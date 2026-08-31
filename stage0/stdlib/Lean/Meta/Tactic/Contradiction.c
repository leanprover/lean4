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
size_t v_x_1117__boxed_155_; size_t v_x_1118__boxed_156_; lean_object* v_res_157_; 
v_x_1117__boxed_155_ = lean_unbox_usize(v_x_151_);
lean_dec(v_x_151_);
v_x_1118__boxed_156_ = lean_unbox_usize(v_x_152_);
lean_dec(v_x_152_);
v_res_157_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_150_, v_x_1117__boxed_155_, v_x_1118__boxed_156_, v_x_153_, v_x_154_);
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
lean_object* v_depth_178_; lean_object* v_levelAssignDepth_179_; lean_object* v_lmvarCounter_180_; lean_object* v_mvarCounter_181_; lean_object* v_lDecls_182_; lean_object* v_decls_183_; lean_object* v_userNames_184_; lean_object* v_lAssignment_185_; lean_object* v_eAssignment_186_; lean_object* v_dAssignment_187_; lean_object* v_instanceTypedMVars_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_202_; 
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
v_isSharedCheck_202_ = !lean_is_exclusive(v_mctx_170_);
if (v_isSharedCheck_202_ == 0)
{
v___x_190_ = v_mctx_170_;
v_isShared_191_ = v_isSharedCheck_202_;
goto v_resetjp_189_;
}
else
{
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
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_202_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_192_; lean_object* v___x_194_; 
v___x_192_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_186_, v_mvarId_165_, v_val_166_);
if (v_isShared_191_ == 0)
{
lean_ctor_set(v___x_190_, 8, v___x_192_);
v___x_194_ = v___x_190_;
goto v_reusejp_193_;
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
lean_ctor_set(v_reuseFailAlloc_201_, 8, v___x_192_);
lean_ctor_set(v_reuseFailAlloc_201_, 9, v_dAssignment_187_);
lean_ctor_set(v_reuseFailAlloc_201_, 10, v_instanceTypedMVars_188_);
v___x_194_ = v_reuseFailAlloc_201_;
goto v_reusejp_193_;
}
v_reusejp_193_:
{
lean_object* v___x_196_; 
if (v_isShared_177_ == 0)
{
lean_ctor_set(v___x_176_, 0, v___x_194_);
v___x_196_ = v___x_176_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_200_, 1, v_cache_171_);
lean_ctor_set(v_reuseFailAlloc_200_, 2, v_zetaDeltaFVarIds_172_);
lean_ctor_set(v_reuseFailAlloc_200_, 3, v_postponed_173_);
lean_ctor_set(v_reuseFailAlloc_200_, 4, v_diag_174_);
v___x_196_ = v_reuseFailAlloc_200_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_197_ = lean_st_ref_put(v___y_167_, v___x_196_);
v___x_198_ = lean_box(0);
v___x_199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_199_, 0, v___x_198_);
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
lean_object* v___x_216_; 
lean_inc(v_mvarId_210_);
v___x_216_ = l_Lean_MVarId_getType(v_mvarId_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_216_) == 0)
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_261_; 
v_a_217_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_261_ == 0)
{
v___x_219_ = v___x_216_;
v_isShared_220_ = v_isSharedCheck_261_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_216_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_261_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___f_221_; lean_object* v___x_222_; 
v___f_221_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
v___x_222_ = lean_find_expr(v___f_221_, v_a_217_);
lean_dec(v_a_217_);
if (lean_obj_tag(v___x_222_) == 1)
{
lean_object* v_val_223_; lean_object* v___x_224_; 
lean_del_object(v___x_219_);
v_val_223_ = lean_ctor_get(v___x_222_, 0);
lean_inc(v_val_223_);
lean_dec_ref_known(v___x_222_, 1);
lean_inc(v_mvarId_210_);
v___x_224_ = l_Lean_MVarId_getType(v_mvarId_210_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
if (lean_obj_tag(v___x_224_) == 0)
{
lean_object* v_a_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v_a_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_a_225_);
lean_dec_ref_known(v___x_224_, 1);
v___x_226_ = l_Lean_Expr_appArg_x21(v_val_223_);
lean_dec(v_val_223_);
v___x_227_ = l_Lean_Meta_mkFalseElim(v_a_225_, v___x_226_, v_a_211_, v_a_212_, v_a_213_, v_a_214_);
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
lean_dec(v_val_223_);
lean_dec(v_mvarId_210_);
v_a_248_ = lean_ctor_get(v___x_224_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_224_);
if (v_isSharedCheck_255_ == 0)
{
v___x_250_ = v___x_224_;
v_isShared_251_ = v_isSharedCheck_255_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_a_248_);
lean_dec(v___x_224_);
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
if (v_isShared_220_ == 0)
{
lean_ctor_set(v___x_219_, 0, v___x_257_);
v___x_259_ = v___x_219_;
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
v_a_262_ = lean_ctor_get(v___x_216_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_216_);
if (v_isSharedCheck_269_ == 0)
{
v___x_264_ = v___x_216_;
v_isShared_265_ = v_isSharedCheck_269_;
goto v_resetjp_263_;
}
else
{
lean_inc(v_a_262_);
lean_dec(v___x_216_);
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
size_t v_x_1468__boxed_311_; size_t v_x_1469__boxed_312_; lean_object* v_res_313_; 
v_x_1468__boxed_311_ = lean_unbox_usize(v_x_307_);
lean_dec(v_x_307_);
v_x_1469__boxed_312_ = lean_unbox_usize(v_x_308_);
lean_dec(v_x_308_);
v_res_313_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_305_, v_x_306_, v_x_1468__boxed_311_, v_x_1469__boxed_312_, v_x_309_, v_x_310_);
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
lean_dec_ref(v_s_413_);
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
lean_object* v_a_500_; lean_object* v___y_502_; lean_object* v___y_503_; uint8_t v___y_504_; lean_object* v___y_523_; lean_object* v_a_524_; lean_object* v___x_527_; 
v_a_500_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_a_500_);
lean_dec_ref_known(v___x_499_, 1);
lean_inc(v___y_497_);
lean_inc_ref(v___y_496_);
lean_inc(v___y_495_);
lean_inc_ref(v___y_494_);
lean_inc(v___y_493_);
v___x_527_ = lean_apply_6(v_x_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, lean_box(0));
if (lean_obj_tag(v___x_527_) == 0)
{
lean_object* v_a_528_; uint8_t v___x_529_; 
v_a_528_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_528_);
v___x_529_ = lean_unbox(v_a_528_);
if (v___x_529_ == 0)
{
lean_object* v___x_530_; 
lean_dec_ref_known(v___x_527_, 1);
v___x_530_ = l_Lean_Meta_SavedState_restore___redArg(v_a_500_, v___y_495_, v___y_497_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_537_; 
lean_dec(v_a_500_);
v_isSharedCheck_537_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_537_ == 0)
{
lean_object* v_unused_538_; 
v_unused_538_ = lean_ctor_get(v___x_530_, 0);
lean_dec(v_unused_538_);
v___x_532_ = v___x_530_;
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
else
{
lean_dec(v___x_530_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_537_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_535_; 
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 0, v_a_528_);
v___x_535_ = v___x_532_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_a_528_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
return v___x_535_;
}
}
}
else
{
lean_object* v_a_539_; lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_546_; 
lean_dec(v_a_528_);
v_a_539_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_546_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_546_ == 0)
{
v___x_541_ = v___x_530_;
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
else
{
lean_inc(v_a_539_);
lean_dec(v___x_530_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_546_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_544_; 
lean_inc(v_a_539_);
if (v_isShared_542_ == 0)
{
v___x_544_ = v___x_541_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v_a_539_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
v___y_523_ = v___x_544_;
v_a_524_ = v_a_539_;
goto v___jp_522_;
}
}
}
}
else
{
lean_dec(v_a_528_);
lean_dec(v_a_500_);
return v___x_527_;
}
}
else
{
lean_object* v_a_547_; 
v_a_547_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_a_547_);
v___y_523_ = v___x_527_;
v_a_524_ = v_a_547_;
goto v___jp_522_;
}
v___jp_501_:
{
if (v___y_504_ == 0)
{
lean_object* v___x_505_; 
lean_dec_ref(v___y_502_);
v___x_505_ = l_Lean_Meta_SavedState_restore___redArg(v_a_500_, v___y_495_, v___y_497_);
lean_dec(v_a_500_);
if (lean_obj_tag(v___x_505_) == 0)
{
lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_512_; 
v_isSharedCheck_512_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_512_ == 0)
{
lean_object* v_unused_513_; 
v_unused_513_ = lean_ctor_get(v___x_505_, 0);
lean_dec(v_unused_513_);
v___x_507_ = v___x_505_;
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
else
{
lean_dec(v___x_505_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_512_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set_tag(v___x_507_, 1);
lean_ctor_set(v___x_507_, 0, v___y_503_);
v___x_510_ = v___x_507_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_511_; 
v_reuseFailAlloc_511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_511_, 0, v___y_503_);
v___x_510_ = v_reuseFailAlloc_511_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
return v___x_510_;
}
}
}
else
{
lean_object* v_a_514_; lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_521_; 
lean_dec_ref(v___y_503_);
v_a_514_ = lean_ctor_get(v___x_505_, 0);
v_isSharedCheck_521_ = !lean_is_exclusive(v___x_505_);
if (v_isSharedCheck_521_ == 0)
{
v___x_516_ = v___x_505_;
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
else
{
lean_inc(v_a_514_);
lean_dec(v___x_505_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_521_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v___x_519_; 
if (v_isShared_517_ == 0)
{
v___x_519_ = v___x_516_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_a_514_);
v___x_519_ = v_reuseFailAlloc_520_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
return v___x_519_;
}
}
}
}
else
{
lean_dec_ref(v___y_503_);
lean_dec(v_a_500_);
return v___y_502_;
}
}
v___jp_522_:
{
uint8_t v___x_525_; 
v___x_525_ = l_Lean_Exception_isInterrupt(v_a_524_);
if (v___x_525_ == 0)
{
uint8_t v___x_526_; 
lean_inc_ref(v_a_524_);
v___x_526_ = l_Lean_Exception_isRuntime(v_a_524_);
v___y_502_ = v___y_523_;
v___y_503_ = v_a_524_;
v___y_504_ = v___x_526_;
goto v___jp_501_;
}
else
{
v___y_502_ = v___y_523_;
v___y_503_ = v_a_524_;
v___y_504_ = v___x_525_;
goto v___jp_501_;
}
}
}
else
{
lean_object* v_a_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_555_; 
lean_dec_ref(v_x_492_);
v_a_548_ = lean_ctor_get(v___x_499_, 0);
v_isSharedCheck_555_ = !lean_is_exclusive(v___x_499_);
if (v_isSharedCheck_555_ == 0)
{
v___x_550_ = v___x_499_;
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_a_548_);
lean_dec(v___x_499_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_555_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_553_; 
if (v_isShared_551_ == 0)
{
v___x_553_ = v___x_550_;
goto v_reusejp_552_;
}
else
{
lean_object* v_reuseFailAlloc_554_; 
v_reuseFailAlloc_554_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_554_, 0, v_a_548_);
v___x_553_ = v_reuseFailAlloc_554_;
goto v_reusejp_552_;
}
v_reusejp_552_:
{
return v___x_553_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* v_x_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_){
_start:
{
lean_object* v_res_563_; 
v_res_563_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_x_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
return v_res_563_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(lean_object* v_msgData_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
lean_object* v___x_570_; lean_object* v_env_571_; lean_object* v___x_572_; lean_object* v_mctx_573_; lean_object* v_lctx_574_; lean_object* v_options_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_570_ = lean_st_ref_get(v___y_568_);
v_env_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_env_571_);
lean_dec(v___x_570_);
v___x_572_ = lean_st_ref_get(v___y_566_);
v_mctx_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc_ref(v_mctx_573_);
lean_dec(v___x_572_);
v_lctx_574_ = lean_ctor_get(v___y_565_, 2);
v_options_575_ = lean_ctor_get(v___y_567_, 2);
lean_inc_ref(v_options_575_);
lean_inc_ref(v_lctx_574_);
v___x_576_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_576_, 0, v_env_571_);
lean_ctor_set(v___x_576_, 1, v_mctx_573_);
lean_ctor_set(v___x_576_, 2, v_lctx_574_);
lean_ctor_set(v___x_576_, 3, v_options_575_);
v___x_577_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_576_);
lean_ctor_set(v___x_577_, 1, v_msgData_564_);
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
lean_object* v_ref_598_; lean_object* v___x_599_; lean_object* v_a_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_644_; 
v_ref_598_ = lean_ctor_get(v___y_595_, 5);
v___x_599_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_592_, v___y_593_, v___y_594_, v___y_595_, v___y_596_);
v_a_600_ = lean_ctor_get(v___x_599_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v___x_599_);
if (v_isSharedCheck_644_ == 0)
{
v___x_602_ = v___x_599_;
v_isShared_603_ = v_isSharedCheck_644_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_a_600_);
lean_dec(v___x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_644_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v_traceState_605_; lean_object* v_env_606_; lean_object* v_nextMacroScope_607_; lean_object* v_ngen_608_; lean_object* v_auxDeclNGen_609_; lean_object* v_cache_610_; lean_object* v_messages_611_; lean_object* v_infoState_612_; lean_object* v_snapshotTasks_613_; lean_object* v___x_615_; uint8_t v_isShared_616_; uint8_t v_isSharedCheck_643_; 
v___x_604_ = lean_st_ref_take(v___y_596_);
v_traceState_605_ = lean_ctor_get(v___x_604_, 4);
v_env_606_ = lean_ctor_get(v___x_604_, 0);
v_nextMacroScope_607_ = lean_ctor_get(v___x_604_, 1);
v_ngen_608_ = lean_ctor_get(v___x_604_, 2);
v_auxDeclNGen_609_ = lean_ctor_get(v___x_604_, 3);
v_cache_610_ = lean_ctor_get(v___x_604_, 5);
v_messages_611_ = lean_ctor_get(v___x_604_, 6);
v_infoState_612_ = lean_ctor_get(v___x_604_, 7);
v_snapshotTasks_613_ = lean_ctor_get(v___x_604_, 8);
v_isSharedCheck_643_ = !lean_is_exclusive(v___x_604_);
if (v_isSharedCheck_643_ == 0)
{
v___x_615_ = v___x_604_;
v_isShared_616_ = v_isSharedCheck_643_;
goto v_resetjp_614_;
}
else
{
lean_inc(v_snapshotTasks_613_);
lean_inc(v_infoState_612_);
lean_inc(v_messages_611_);
lean_inc(v_cache_610_);
lean_inc(v_traceState_605_);
lean_inc(v_auxDeclNGen_609_);
lean_inc(v_ngen_608_);
lean_inc(v_nextMacroScope_607_);
lean_inc(v_env_606_);
lean_dec(v___x_604_);
v___x_615_ = lean_box(0);
v_isShared_616_ = v_isSharedCheck_643_;
goto v_resetjp_614_;
}
v_resetjp_614_:
{
uint64_t v_tid_617_; lean_object* v_traces_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_642_; 
v_tid_617_ = lean_ctor_get_uint64(v_traceState_605_, sizeof(void*)*1);
v_traces_618_ = lean_ctor_get(v_traceState_605_, 0);
v_isSharedCheck_642_ = !lean_is_exclusive(v_traceState_605_);
if (v_isSharedCheck_642_ == 0)
{
v___x_620_ = v_traceState_605_;
v_isShared_621_ = v_isSharedCheck_642_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_traces_618_);
lean_dec(v_traceState_605_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_642_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
lean_object* v___x_622_; double v___x_623_; uint8_t v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_632_; 
v___x_622_ = lean_box(0);
v___x_623_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_624_ = 0;
v___x_625_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_626_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_626_, 0, v_cls_591_);
lean_ctor_set(v___x_626_, 1, v___x_622_);
lean_ctor_set(v___x_626_, 2, v___x_625_);
lean_ctor_set_float(v___x_626_, sizeof(void*)*3, v___x_623_);
lean_ctor_set_float(v___x_626_, sizeof(void*)*3 + 8, v___x_623_);
lean_ctor_set_uint8(v___x_626_, sizeof(void*)*3 + 16, v___x_624_);
v___x_627_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_628_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_628_, 0, v___x_626_);
lean_ctor_set(v___x_628_, 1, v_a_600_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_inc(v_ref_598_);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v_ref_598_);
lean_ctor_set(v___x_629_, 1, v___x_628_);
v___x_630_ = l_Lean_PersistentArray_push___redArg(v_traces_618_, v___x_629_);
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 0, v___x_630_);
v___x_632_ = v___x_620_;
goto v_reusejp_631_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_630_);
lean_ctor_set_uint64(v_reuseFailAlloc_641_, sizeof(void*)*1, v_tid_617_);
v___x_632_ = v_reuseFailAlloc_641_;
goto v_reusejp_631_;
}
v_reusejp_631_:
{
lean_object* v___x_634_; 
if (v_isShared_616_ == 0)
{
lean_ctor_set(v___x_615_, 4, v___x_632_);
v___x_634_ = v___x_615_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v_env_606_);
lean_ctor_set(v_reuseFailAlloc_640_, 1, v_nextMacroScope_607_);
lean_ctor_set(v_reuseFailAlloc_640_, 2, v_ngen_608_);
lean_ctor_set(v_reuseFailAlloc_640_, 3, v_auxDeclNGen_609_);
lean_ctor_set(v_reuseFailAlloc_640_, 4, v___x_632_);
lean_ctor_set(v_reuseFailAlloc_640_, 5, v_cache_610_);
lean_ctor_set(v_reuseFailAlloc_640_, 6, v_messages_611_);
lean_ctor_set(v_reuseFailAlloc_640_, 7, v_infoState_612_);
lean_ctor_set(v_reuseFailAlloc_640_, 8, v_snapshotTasks_613_);
v___x_634_ = v_reuseFailAlloc_640_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_635_ = lean_st_ref_put(v___y_596_, v___x_634_);
v___x_636_ = lean_box(0);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 0, v___x_636_);
v___x_638_ = v___x_602_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_639_; 
v_reuseFailAlloc_639_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_639_, 0, v___x_636_);
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
size_t v_sz_boxed_673_; size_t v___x_15851__boxed_674_; uint8_t v___x_15853__boxed_675_; lean_object* v_res_676_; 
v_sz_boxed_673_ = lean_unbox_usize(v_sz_663_);
lean_dec(v_sz_663_);
v___x_15851__boxed_674_ = lean_unbox_usize(v___x_664_);
lean_dec(v___x_664_);
v___x_15853__boxed_675_ = lean_unbox(v___x_666_);
v_res_676_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_660_, v_mvarId_661_, v_fields_662_, v_sz_boxed_673_, v___x_15851__boxed_674_, v___x_665_, v___x_15853__boxed_675_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_);
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
lean_object* v_a_764_; lean_object* v___y_766_; lean_object* v___y_767_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v_options_797_; uint8_t v_hasTrace_798_; 
v_a_764_ = lean_ctor_get(v___x_763_, 0);
lean_inc(v_a_764_);
lean_dec_ref_known(v___x_763_, 1);
v_options_797_ = lean_ctor_get(v___y_760_, 2);
v_hasTrace_798_ = lean_ctor_get_uint8(v_options_797_, sizeof(void*)*1);
if (v_hasTrace_798_ == 0)
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
lean_object* v_inheritedTraceOptions_799_; lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v_inheritedTraceOptions_799_ = lean_ctor_get(v___y_760_, 13);
v___x_800_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_801_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_802_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_799_, v_options_797_, v___x_801_);
if (v___x_802_ == 0)
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
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_803_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_804_ = lean_array_get_size(v_a_764_);
v___x_805_ = l_Nat_reprFast(v___x_804_);
v___x_806_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
v___x_807_ = l_Lean_MessageData_ofFormat(v___x_806_);
v___x_808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_803_);
lean_ctor_set(v___x_808_, 1, v___x_807_);
v___x_809_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_800_, v___x_808_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_dec_ref_known(v___x_809_, 1);
v___y_766_ = v___y_757_;
v___y_767_ = v___y_758_;
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
goto v___jp_765_;
}
else
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
lean_dec(v_a_764_);
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
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
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_862_; 
v_a_818_ = lean_ctor_get(v___x_763_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_763_);
if (v_isSharedCheck_862_ == 0)
{
v___x_820_ = v___x_763_;
v_isShared_821_ = v_isSharedCheck_862_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_763_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_862_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
uint8_t v___y_823_; uint8_t v___x_860_; 
v___x_860_ = l_Lean_Exception_isInterrupt(v_a_818_);
if (v___x_860_ == 0)
{
uint8_t v___x_861_; 
lean_inc(v_a_818_);
v___x_861_ = l_Lean_Exception_isRuntime(v_a_818_);
v___y_823_ = v___x_861_;
goto v___jp_822_;
}
else
{
v___y_823_ = v___x_860_;
goto v___jp_822_;
}
v___jp_822_:
{
if (v___y_823_ == 0)
{
lean_object* v_options_824_; uint8_t v_hasTrace_825_; 
v_options_824_ = lean_ctor_get(v___y_760_, 2);
v_hasTrace_825_ = lean_ctor_get_uint8(v_options_824_, sizeof(void*)*1);
if (v_hasTrace_825_ == 0)
{
lean_object* v___x_826_; lean_object* v___x_828_; 
lean_dec(v_a_818_);
v___x_826_ = lean_box(v___x_753_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 0);
lean_ctor_set(v___x_820_, 0, v___x_826_);
v___x_828_ = v___x_820_;
goto v_reusejp_827_;
}
else
{
lean_object* v_reuseFailAlloc_829_; 
v_reuseFailAlloc_829_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_829_, 0, v___x_826_);
v___x_828_ = v_reuseFailAlloc_829_;
goto v_reusejp_827_;
}
v_reusejp_827_:
{
return v___x_828_;
}
}
else
{
lean_object* v_inheritedTraceOptions_830_; lean_object* v___x_831_; lean_object* v___x_832_; uint8_t v___x_833_; 
v_inheritedTraceOptions_830_ = lean_ctor_get(v___y_760_, 13);
v___x_831_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_832_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_833_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_830_, v_options_824_, v___x_832_);
if (v___x_833_ == 0)
{
lean_object* v___x_834_; lean_object* v___x_836_; 
lean_dec(v_a_818_);
v___x_834_ = lean_box(v___x_753_);
if (v_isShared_821_ == 0)
{
lean_ctor_set_tag(v___x_820_, 0);
lean_ctor_set(v___x_820_, 0, v___x_834_);
v___x_836_ = v___x_820_;
goto v_reusejp_835_;
}
else
{
lean_object* v_reuseFailAlloc_837_; 
v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
v___x_836_ = v_reuseFailAlloc_837_;
goto v_reusejp_835_;
}
v_reusejp_835_:
{
return v___x_836_;
}
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_del_object(v___x_820_);
v___x_838_ = l_Lean_Exception_toMessageData(v_a_818_);
v___x_839_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_831_, v___x_838_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
if (lean_obj_tag(v___x_839_) == 0)
{
lean_object* v___x_841_; uint8_t v_isShared_842_; uint8_t v_isSharedCheck_847_; 
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_847_ == 0)
{
lean_object* v_unused_848_; 
v_unused_848_ = lean_ctor_get(v___x_839_, 0);
lean_dec(v_unused_848_);
v___x_841_ = v___x_839_;
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
else
{
lean_dec(v___x_839_);
v___x_841_ = lean_box(0);
v_isShared_842_ = v_isSharedCheck_847_;
goto v_resetjp_840_;
}
v_resetjp_840_:
{
lean_object* v___x_843_; lean_object* v___x_845_; 
v___x_843_ = lean_box(v___x_753_);
if (v_isShared_842_ == 0)
{
lean_ctor_set(v___x_841_, 0, v___x_843_);
v___x_845_ = v___x_841_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
else
{
lean_object* v_a_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_856_; 
v_a_849_ = lean_ctor_get(v___x_839_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v___x_839_);
if (v_isSharedCheck_856_ == 0)
{
v___x_851_ = v___x_839_;
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_a_849_);
lean_dec(v___x_839_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_856_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_854_; 
if (v_isShared_852_ == 0)
{
v___x_854_ = v___x_851_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_a_849_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
}
else
{
lean_object* v___x_858_; 
if (v_isShared_821_ == 0)
{
v___x_858_ = v___x_820_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v_a_818_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_863_, lean_object* v_fvarId_864_, lean_object* v___x_865_, lean_object* v___x_866_, lean_object* v___x_867_, lean_object* v_val_868_, lean_object* v___x_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_){
_start:
{
uint8_t v___x_15973__boxed_876_; uint8_t v___x_15976__boxed_877_; lean_object* v_res_878_; 
v___x_15973__boxed_876_ = lean_unbox(v___x_866_);
v___x_15976__boxed_877_ = lean_unbox(v___x_869_);
v_res_878_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_863_, v_fvarId_864_, v___x_865_, v___x_15973__boxed_876_, v___x_867_, v_val_868_, v___x_15976__boxed_877_, v___y_870_, v___y_871_, v___y_872_, v___y_873_, v___y_874_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec_ref(v___y_871_);
lean_dec(v___y_870_);
lean_dec(v_val_868_);
return v_res_878_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_880_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_881_ = l_Lean_stringToMessageData(v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_882_, lean_object* v_fvarId_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v___x_894_; lean_object* v___x_895_; uint8_t v___x_896_; 
v___x_894_ = lean_st_ref_get(v_a_884_);
v___x_895_ = lean_unsigned_to_nat(0u);
v___x_896_ = lean_nat_dec_eq(v___x_894_, v___x_895_);
if (v___x_896_ == 0)
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___f_906_; lean_object* v___x_907_; 
v___x_897_ = lean_st_ref_take(v_a_884_);
v___x_898_ = lean_unsigned_to_nat(1u);
v___x_899_ = lean_nat_sub(v___x_897_, v___x_898_);
lean_dec(v___x_897_);
v___x_900_ = lean_st_ref_put(v_a_884_, v___x_899_);
v___x_901_ = 1;
v___x_902_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_903_ = lean_box(0);
v___x_904_ = lean_box(v___x_896_);
v___x_905_ = lean_box(v___x_901_);
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_906_, 0, v_mvarId_882_);
lean_closure_set(v___f_906_, 1, v_fvarId_883_);
lean_closure_set(v___f_906_, 2, v___x_902_);
lean_closure_set(v___f_906_, 3, v___x_904_);
lean_closure_set(v___f_906_, 4, v___x_903_);
lean_closure_set(v___f_906_, 5, v___x_894_);
lean_closure_set(v___f_906_, 6, v___x_905_);
v___x_907_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_906_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
return v___x_907_;
}
else
{
lean_object* v_options_908_; uint8_t v_hasTrace_909_; 
lean_dec(v___x_894_);
lean_dec(v_fvarId_883_);
lean_dec(v_mvarId_882_);
v_options_908_ = lean_ctor_get(v_a_887_, 2);
v_hasTrace_909_ = lean_ctor_get_uint8(v_options_908_, sizeof(void*)*1);
if (v_hasTrace_909_ == 0)
{
goto v___jp_890_;
}
else
{
lean_object* v_inheritedTraceOptions_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v_inheritedTraceOptions_910_ = lean_ctor_get(v_a_887_, 13);
v___x_911_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_912_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_913_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_910_, v_options_908_, v___x_912_);
if (v___x_913_ == 0)
{
goto v___jp_890_;
}
else
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_915_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_911_, v___x_914_, v_a_885_, v_a_886_, v_a_887_, v_a_888_);
if (lean_obj_tag(v___x_915_) == 0)
{
lean_dec_ref_known(v___x_915_, 1);
goto v___jp_890_;
}
else
{
lean_object* v_a_916_; lean_object* v___x_918_; uint8_t v_isShared_919_; uint8_t v_isSharedCheck_923_; 
v_a_916_ = lean_ctor_get(v___x_915_, 0);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_915_);
if (v_isSharedCheck_923_ == 0)
{
v___x_918_ = v___x_915_;
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
else
{
lean_inc(v_a_916_);
lean_dec(v___x_915_);
v___x_918_ = lean_box(0);
v_isShared_919_ = v_isSharedCheck_923_;
goto v_resetjp_917_;
}
v_resetjp_917_:
{
lean_object* v___x_921_; 
if (v_isShared_919_ == 0)
{
v___x_921_ = v___x_918_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_922_; 
v_reuseFailAlloc_922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_922_, 0, v_a_916_);
v___x_921_ = v_reuseFailAlloc_922_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
return v___x_921_;
}
}
}
}
}
}
v___jp_890_:
{
uint8_t v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; 
v___x_891_ = 0;
v___x_892_ = lean_box(v___x_891_);
v___x_893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_893_, 0, v___x_892_);
return v___x_893_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_924_, lean_object* v___x_925_, lean_object* v_as_926_, size_t v_sz_927_, size_t v_i_928_, lean_object* v_b_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_){
_start:
{
lean_object* v_a_937_; uint8_t v___x_941_; 
v___x_941_ = lean_usize_dec_lt(v_i_928_, v_sz_927_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; 
lean_dec(v___x_925_);
lean_dec_ref(v___x_924_);
v___x_942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_942_, 0, v_b_929_);
return v___x_942_;
}
else
{
lean_object* v_subst_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v_a_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
lean_dec_ref(v_b_929_);
v_subst_943_ = lean_ctor_get(v___x_924_, 2);
v___x_944_ = lean_box(0);
v___x_945_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_946_ = lean_array_uget_borrowed(v_as_926_, v_i_928_);
lean_inc(v_subst_943_);
v___x_947_ = l_Lean_Meta_FVarSubst_apply(v_subst_943_, v_a_946_);
v___x_948_ = l_Lean_Expr_isFVar(v___x_947_);
if (v___x_948_ == 0)
{
lean_dec_ref(v___x_947_);
v_a_937_ = v___x_945_;
goto v___jp_936_;
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; 
v___x_949_ = l_Lean_Expr_fvarId_x21(v___x_947_);
lean_dec_ref(v___x_947_);
lean_inc(v___x_949_);
v___x_950_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_949_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_950_) == 0)
{
lean_object* v_a_951_; uint8_t v___x_952_; 
v_a_951_ = lean_ctor_get(v___x_950_, 0);
lean_inc(v_a_951_);
lean_dec_ref_known(v___x_950_, 1);
v___x_952_ = lean_unbox(v_a_951_);
lean_dec(v_a_951_);
if (v___x_952_ == 0)
{
lean_dec(v___x_949_);
v_a_937_ = v___x_945_;
goto v___jp_936_;
}
else
{
lean_object* v___x_953_; 
lean_inc(v___x_925_);
v___x_953_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_925_, v___x_949_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_);
if (lean_obj_tag(v___x_953_) == 0)
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_964_; 
v_a_954_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_964_ == 0)
{
v___x_956_ = v___x_953_;
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_953_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_964_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
uint8_t v___x_958_; 
v___x_958_ = lean_unbox(v_a_954_);
if (v___x_958_ == 0)
{
lean_del_object(v___x_956_);
lean_dec(v_a_954_);
v_a_937_ = v___x_945_;
goto v___jp_936_;
}
else
{
lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
lean_dec(v___x_925_);
lean_dec_ref(v___x_924_);
v___x_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_959_, 0, v_a_954_);
v___x_960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_960_, 0, v___x_959_);
lean_ctor_set(v___x_960_, 1, v___x_944_);
if (v_isShared_957_ == 0)
{
lean_ctor_set(v___x_956_, 0, v___x_960_);
v___x_962_ = v___x_956_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
}
}
else
{
lean_object* v_a_965_; lean_object* v___x_967_; uint8_t v_isShared_968_; uint8_t v_isSharedCheck_972_; 
lean_dec(v___x_925_);
lean_dec_ref(v___x_924_);
v_a_965_ = lean_ctor_get(v___x_953_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_953_);
if (v_isSharedCheck_972_ == 0)
{
v___x_967_ = v___x_953_;
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
else
{
lean_inc(v_a_965_);
lean_dec(v___x_953_);
v___x_967_ = lean_box(0);
v_isShared_968_ = v_isSharedCheck_972_;
goto v_resetjp_966_;
}
v_resetjp_966_:
{
lean_object* v___x_970_; 
if (v_isShared_968_ == 0)
{
v___x_970_ = v___x_967_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v_a_965_);
v___x_970_ = v_reuseFailAlloc_971_;
goto v_reusejp_969_;
}
v_reusejp_969_:
{
return v___x_970_;
}
}
}
}
}
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v___x_949_);
lean_dec(v___x_925_);
lean_dec_ref(v___x_924_);
v_a_973_ = lean_ctor_get(v___x_950_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_950_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_950_);
v___x_975_ = lean_box(0);
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
v_resetjp_974_:
{
lean_object* v___x_978_; 
if (v_isShared_976_ == 0)
{
v___x_978_ = v___x_975_;
goto v_reusejp_977_;
}
else
{
lean_object* v_reuseFailAlloc_979_; 
v_reuseFailAlloc_979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_979_, 0, v_a_973_);
v___x_978_ = v_reuseFailAlloc_979_;
goto v_reusejp_977_;
}
v_reusejp_977_:
{
return v___x_978_;
}
}
}
}
}
v___jp_936_:
{
size_t v___x_938_; size_t v___x_939_; 
v___x_938_ = ((size_t)1ULL);
v___x_939_ = lean_usize_add(v_i_928_, v___x_938_);
lean_inc_ref(v_a_937_);
v_i_928_ = v___x_939_;
v_b_929_ = v_a_937_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_981_, lean_object* v_mvarId_982_, lean_object* v_fields_983_, size_t v_sz_984_, size_t v___x_985_, lean_object* v___x_986_, uint8_t v___x_987_, lean_object* v___y_988_, lean_object* v___y_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_981_, v_mvarId_982_, v_fields_983_, v_sz_984_, v___x_985_, v___x_986_, v___y_988_, v___y_989_, v___y_990_, v___y_991_, v___y_992_);
if (lean_obj_tag(v___x_994_) == 0)
{
lean_object* v_a_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1008_; 
v_a_995_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1008_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1008_ == 0)
{
v___x_997_ = v___x_994_;
v_isShared_998_ = v_isSharedCheck_1008_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_a_995_);
lean_dec(v___x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1008_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v_fst_999_; 
v_fst_999_ = lean_ctor_get(v_a_995_, 0);
lean_inc(v_fst_999_);
lean_dec(v_a_995_);
if (lean_obj_tag(v_fst_999_) == 0)
{
lean_object* v___x_1000_; lean_object* v___x_1002_; 
v___x_1000_ = lean_box(v___x_987_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v___x_1000_);
v___x_1002_ = v___x_997_;
goto v_reusejp_1001_;
}
else
{
lean_object* v_reuseFailAlloc_1003_; 
v_reuseFailAlloc_1003_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1003_, 0, v___x_1000_);
v___x_1002_ = v_reuseFailAlloc_1003_;
goto v_reusejp_1001_;
}
v_reusejp_1001_:
{
return v___x_1002_;
}
}
else
{
lean_object* v_val_1004_; lean_object* v___x_1006_; 
v_val_1004_ = lean_ctor_get(v_fst_999_, 0);
lean_inc(v_val_1004_);
lean_dec_ref_known(v_fst_999_, 1);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 0, v_val_1004_);
v___x_1006_ = v___x_997_;
goto v_reusejp_1005_;
}
else
{
lean_object* v_reuseFailAlloc_1007_; 
v_reuseFailAlloc_1007_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1007_, 0, v_val_1004_);
v___x_1006_ = v_reuseFailAlloc_1007_;
goto v_reusejp_1005_;
}
v_reusejp_1005_:
{
return v___x_1006_;
}
}
}
}
else
{
lean_object* v_a_1009_; lean_object* v___x_1011_; uint8_t v_isShared_1012_; uint8_t v_isSharedCheck_1016_; 
v_a_1009_ = lean_ctor_get(v___x_994_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_994_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1011_ = v___x_994_;
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
else
{
lean_inc(v_a_1009_);
lean_dec(v___x_994_);
v___x_1011_ = lean_box(0);
v_isShared_1012_ = v_isSharedCheck_1016_;
goto v_resetjp_1010_;
}
v_resetjp_1010_:
{
lean_object* v___x_1014_; 
if (v_isShared_1012_ == 0)
{
v___x_1014_ = v___x_1011_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_a_1009_);
v___x_1014_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1013_;
}
v_reusejp_1013_:
{
return v___x_1014_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1017_, lean_object* v_as_1018_, lean_object* v_sz_1019_, lean_object* v_i_1020_, lean_object* v_b_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_){
_start:
{
size_t v_sz_boxed_1028_; size_t v_i_boxed_1029_; lean_object* v_res_1030_; 
v_sz_boxed_1028_ = lean_unbox_usize(v_sz_1019_);
lean_dec(v_sz_1019_);
v_i_boxed_1029_ = lean_unbox_usize(v_i_1020_);
lean_dec(v_i_1020_);
v_res_1030_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1017_, v_as_1018_, v_sz_boxed_1028_, v_i_boxed_1029_, v_b_1021_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_, v___y_1026_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v___y_1023_);
lean_dec(v___y_1022_);
lean_dec_ref(v_as_1018_);
lean_dec(v_val_1017_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1031_, lean_object* v___x_1032_, lean_object* v_as_1033_, lean_object* v_sz_1034_, lean_object* v_i_1035_, lean_object* v_b_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_){
_start:
{
size_t v_sz_boxed_1043_; size_t v_i_boxed_1044_; lean_object* v_res_1045_; 
v_sz_boxed_1043_ = lean_unbox_usize(v_sz_1034_);
lean_dec(v_sz_1034_);
v_i_boxed_1044_ = lean_unbox_usize(v_i_1035_);
lean_dec(v_i_1035_);
v_res_1045_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1031_, v___x_1032_, v_as_1033_, v_sz_boxed_1043_, v_i_boxed_1044_, v_b_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v___y_1038_);
lean_dec(v___y_1037_);
lean_dec_ref(v_as_1033_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1046_, lean_object* v_fvarId_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_){
_start:
{
lean_object* v_res_1054_; 
v_res_1054_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1046_, v_fvarId_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1055_, lean_object* v_msg_1056_, lean_object* v___y_1057_, lean_object* v___y_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_){
_start:
{
lean_object* v___x_1063_; 
v___x_1063_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1055_, v_msg_1056_, v___y_1058_, v___y_1059_, v___y_1060_, v___y_1061_);
return v___x_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1064_, lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v_res_1072_; 
v_res_1072_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1064_, v_msg_1065_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
return v_res_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_Meta_saveState___redArg(v___y_1075_, v___y_1077_);
if (lean_obj_tag(v___x_1079_) == 0)
{
lean_object* v_a_1080_; lean_object* v___y_1082_; lean_object* v___y_1083_; uint8_t v___y_1084_; lean_object* v___y_1103_; lean_object* v_a_1104_; lean_object* v___x_1107_; 
v_a_1080_ = lean_ctor_get(v___x_1079_, 0);
lean_inc(v_a_1080_);
lean_dec_ref_known(v___x_1079_, 1);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
lean_inc(v___y_1075_);
lean_inc_ref(v___y_1074_);
v___x_1107_ = lean_apply_5(v_x_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, lean_box(0));
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; uint8_t v___x_1109_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
v___x_1109_ = lean_unbox(v_a_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
lean_dec_ref_known(v___x_1107_, 1);
v___x_1110_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1080_, v___y_1075_, v___y_1077_);
if (lean_obj_tag(v___x_1110_) == 0)
{
lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1117_; 
lean_dec(v_a_1080_);
v_isSharedCheck_1117_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1117_ == 0)
{
lean_object* v_unused_1118_; 
v_unused_1118_ = lean_ctor_get(v___x_1110_, 0);
lean_dec(v_unused_1118_);
v___x_1112_ = v___x_1110_;
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
else
{
lean_dec(v___x_1110_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1117_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v___x_1115_; 
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 0, v_a_1108_);
v___x_1115_ = v___x_1112_;
goto v_reusejp_1114_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_a_1108_);
v___x_1115_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1114_;
}
v_reusejp_1114_:
{
return v___x_1115_;
}
}
}
else
{
lean_object* v_a_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_a_1108_);
v_a_1119_ = lean_ctor_get(v___x_1110_, 0);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1110_);
if (v_isSharedCheck_1126_ == 0)
{
v___x_1121_ = v___x_1110_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_a_1119_);
lean_dec(v___x_1110_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
lean_inc(v_a_1119_);
if (v_isShared_1122_ == 0)
{
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1119_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
v___y_1103_ = v___x_1124_;
v_a_1104_ = v_a_1119_;
goto v___jp_1102_;
}
}
}
}
else
{
lean_dec(v_a_1108_);
lean_dec(v_a_1080_);
return v___x_1107_;
}
}
else
{
lean_object* v_a_1127_; 
v_a_1127_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1127_);
v___y_1103_ = v___x_1107_;
v_a_1104_ = v_a_1127_;
goto v___jp_1102_;
}
v___jp_1081_:
{
if (v___y_1084_ == 0)
{
lean_object* v___x_1085_; 
lean_dec_ref(v___y_1083_);
v___x_1085_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1080_, v___y_1075_, v___y_1077_);
lean_dec(v_a_1080_);
if (lean_obj_tag(v___x_1085_) == 0)
{
lean_object* v___x_1087_; uint8_t v_isShared_1088_; uint8_t v_isSharedCheck_1092_; 
v_isSharedCheck_1092_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1092_ == 0)
{
lean_object* v_unused_1093_; 
v_unused_1093_ = lean_ctor_get(v___x_1085_, 0);
lean_dec(v_unused_1093_);
v___x_1087_ = v___x_1085_;
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
else
{
lean_dec(v___x_1085_);
v___x_1087_ = lean_box(0);
v_isShared_1088_ = v_isSharedCheck_1092_;
goto v_resetjp_1086_;
}
v_resetjp_1086_:
{
lean_object* v___x_1090_; 
if (v_isShared_1088_ == 0)
{
lean_ctor_set_tag(v___x_1087_, 1);
lean_ctor_set(v___x_1087_, 0, v___y_1082_);
v___x_1090_ = v___x_1087_;
goto v_reusejp_1089_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v___y_1082_);
v___x_1090_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1089_;
}
v_reusejp_1089_:
{
return v___x_1090_;
}
}
}
else
{
lean_object* v_a_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
lean_dec_ref(v___y_1082_);
v_a_1094_ = lean_ctor_get(v___x_1085_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1085_);
if (v_isSharedCheck_1101_ == 0)
{
v___x_1096_ = v___x_1085_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_a_1094_);
lean_dec(v___x_1085_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
else
{
lean_dec_ref(v___y_1082_);
lean_dec(v_a_1080_);
return v___y_1083_;
}
}
v___jp_1102_:
{
uint8_t v___x_1105_; 
v___x_1105_ = l_Lean_Exception_isInterrupt(v_a_1104_);
if (v___x_1105_ == 0)
{
uint8_t v___x_1106_; 
lean_inc_ref(v_a_1104_);
v___x_1106_ = l_Lean_Exception_isRuntime(v_a_1104_);
v___y_1082_ = v_a_1104_;
v___y_1083_ = v___y_1103_;
v___y_1084_ = v___x_1106_;
goto v___jp_1081_;
}
else
{
v___y_1082_ = v_a_1104_;
v___y_1083_ = v___y_1103_;
v___y_1084_ = v___x_1105_;
goto v___jp_1081_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec_ref(v_x_1073_);
v_a_1128_ = lean_ctor_get(v___x_1079_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1079_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1079_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1079_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
if (v_isShared_1131_ == 0)
{
v___x_1133_ = v___x_1130_;
goto v_reusejp_1132_;
}
else
{
lean_object* v_reuseFailAlloc_1134_; 
v_reuseFailAlloc_1134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1134_, 0, v_a_1128_);
v___x_1133_ = v_reuseFailAlloc_1134_;
goto v_reusejp_1132_;
}
v_reusejp_1132_:
{
return v___x_1133_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1136_, lean_object* v___y_1137_, lean_object* v___y_1138_, lean_object* v___y_1139_, lean_object* v___y_1140_, lean_object* v___y_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1136_, v___y_1137_, v___y_1138_, v___y_1139_, v___y_1140_);
lean_dec(v___y_1140_);
lean_dec_ref(v___y_1139_);
lean_dec(v___y_1138_);
lean_dec_ref(v___y_1137_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1143_, lean_object* v_x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1143_, v_x_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v_a_1151_; lean_object* v___x_1153_; uint8_t v_isShared_1154_; uint8_t v_isSharedCheck_1158_; 
v_a_1151_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1153_ = v___x_1150_;
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
else
{
lean_inc(v_a_1151_);
lean_dec(v___x_1150_);
v___x_1153_ = lean_box(0);
v_isShared_1154_ = v_isSharedCheck_1158_;
goto v_resetjp_1152_;
}
v_resetjp_1152_:
{
lean_object* v___x_1156_; 
if (v_isShared_1154_ == 0)
{
v___x_1156_ = v___x_1153_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_a_1151_);
v___x_1156_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
return v___x_1156_;
}
}
}
else
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_a_1159_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1150_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1150_);
v___x_1161_ = lean_box(0);
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
v_resetjp_1160_:
{
lean_object* v___x_1164_; 
if (v_isShared_1162_ == 0)
{
v___x_1164_ = v___x_1161_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1165_; 
v_reuseFailAlloc_1165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1165_, 0, v_a_1159_);
v___x_1164_ = v_reuseFailAlloc_1165_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
return v___x_1164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1167_, lean_object* v_x_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1167_, v_x_1168_, v___y_1169_, v___y_1170_, v___y_1171_, v___y_1172_);
lean_dec(v___y_1172_);
lean_dec_ref(v___y_1171_);
lean_dec(v___y_1170_);
lean_dec_ref(v___y_1169_);
return v_res_1174_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1175_, lean_object* v_mvarId_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1176_, v_x_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1184_, lean_object* v_mvarId_1185_, lean_object* v_x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1184_, v_mvarId_1185_, v_x_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
lean_dec(v___y_1190_);
lean_dec_ref(v___y_1189_);
lean_dec(v___y_1188_);
lean_dec_ref(v___y_1187_);
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1193_, lean_object* v_fuel_1194_, lean_object* v_fvarId_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v___x_1201_; 
v___x_1201_ = l_Lean_MVarId_exfalso(v_mvarId_1193_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1201_) == 0)
{
lean_object* v_a_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; 
v_a_1202_ = lean_ctor_get(v___x_1201_, 0);
lean_inc(v_a_1202_);
lean_dec_ref_known(v___x_1201_, 1);
v___x_1203_ = lean_st_mk_ref(v_fuel_1194_);
v___x_1204_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1202_, v_fvarId_1195_, v___x_1203_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
if (lean_obj_tag(v___x_1204_) == 0)
{
lean_object* v_a_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1213_; 
v_a_1205_ = lean_ctor_get(v___x_1204_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1204_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1207_ = v___x_1204_;
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_a_1205_);
lean_dec(v___x_1204_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1213_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_st_ref_get(v___x_1203_);
lean_dec(v___x_1203_);
lean_dec(v___x_1209_);
if (v_isShared_1208_ == 0)
{
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1205_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
else
{
lean_dec(v___x_1203_);
return v___x_1204_;
}
}
else
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1221_; 
lean_dec(v_fvarId_1195_);
lean_dec(v_fuel_1194_);
v_a_1214_ = lean_ctor_get(v___x_1201_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1201_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1216_ = v___x_1201_;
v_isShared_1217_ = v_isSharedCheck_1221_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1201_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1222_, lean_object* v_fuel_1223_, lean_object* v_fvarId_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v_res_1230_; 
v_res_1230_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1222_, v_fuel_1223_, v_fvarId_1224_, v___y_1225_, v___y_1226_, v___y_1227_, v___y_1228_);
lean_dec(v___y_1228_);
lean_dec_ref(v___y_1227_);
lean_dec(v___y_1226_);
lean_dec_ref(v___y_1225_);
return v_res_1230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1231_, lean_object* v___f_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_){
_start:
{
lean_object* v___x_1238_; 
v___x_1238_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1231_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
if (lean_obj_tag(v___x_1238_) == 0)
{
lean_object* v_a_1239_; uint8_t v___x_1240_; 
v_a_1239_ = lean_ctor_get(v___x_1238_, 0);
lean_inc(v_a_1239_);
v___x_1240_ = lean_unbox(v_a_1239_);
lean_dec(v_a_1239_);
if (v___x_1240_ == 0)
{
lean_dec_ref(v___f_1232_);
return v___x_1238_;
}
else
{
lean_object* v___x_1241_; 
lean_dec_ref_known(v___x_1238_, 1);
v___x_1241_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
return v___x_1241_;
}
}
else
{
lean_dec_ref(v___f_1232_);
return v___x_1238_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1242_, lean_object* v___f_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1242_, v___f_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
lean_dec(v___y_1247_);
lean_dec_ref(v___y_1246_);
lean_dec(v___y_1245_);
lean_dec_ref(v___y_1244_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1250_, lean_object* v_fvarId_1251_, lean_object* v_fuel_1252_, lean_object* v_a_1253_, lean_object* v_a_1254_, lean_object* v_a_1255_, lean_object* v_a_1256_){
_start:
{
lean_object* v___f_1258_; lean_object* v___f_1259_; lean_object* v___x_1260_; 
lean_inc(v_fvarId_1251_);
lean_inc(v_mvarId_1250_);
v___f_1258_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1258_, 0, v_mvarId_1250_);
lean_closure_set(v___f_1258_, 1, v_fuel_1252_);
lean_closure_set(v___f_1258_, 2, v_fvarId_1251_);
v___f_1259_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1259_, 0, v_fvarId_1251_);
lean_closure_set(v___f_1259_, 1, v___f_1258_);
v___x_1260_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1250_, v___f_1259_, v_a_1253_, v_a_1254_, v_a_1255_, v_a_1256_);
return v___x_1260_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1261_, lean_object* v_fvarId_1262_, lean_object* v_fuel_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_, lean_object* v_a_1266_, lean_object* v_a_1267_, lean_object* v_a_1268_){
_start:
{
lean_object* v_res_1269_; 
v_res_1269_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1261_, v_fvarId_1262_, v_fuel_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_);
lean_dec(v_a_1267_);
lean_dec_ref(v_a_1266_);
lean_dec(v_a_1265_);
lean_dec_ref(v_a_1264_);
return v_res_1269_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1270_){
_start:
{
uint8_t v___x_1271_; 
v___x_1271_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1270_);
return v___x_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1272_){
_start:
{
uint8_t v_res_1273_; lean_object* v_r_1274_; 
v_res_1273_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1272_);
v_r_1274_ = lean_box(v_res_1273_);
return v_r_1274_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1275_, lean_object* v_acc_1276_){
_start:
{
if (lean_obj_tag(v_e_1275_) == 7)
{
lean_object* v_binderType_1277_; lean_object* v_body_1278_; uint8_t v___y_1280_; lean_object* v___x_1284_; uint8_t v___x_1285_; 
v_binderType_1277_ = lean_ctor_get(v_e_1275_, 1);
v_body_1278_ = lean_ctor_get(v_e_1275_, 2);
v___x_1284_ = lean_unsigned_to_nat(0u);
v___x_1285_ = lean_expr_has_loose_bvar(v_body_1278_, v___x_1284_);
if (v___x_1285_ == 0)
{
uint8_t v___x_1286_; 
v___x_1286_ = l_Lean_Expr_isEq(v_binderType_1277_);
if (v___x_1286_ == 0)
{
uint8_t v___x_1287_; 
v___x_1287_ = l_Lean_Expr_isHEq(v_binderType_1277_);
v___y_1280_ = v___x_1287_;
goto v___jp_1279_;
}
else
{
v___y_1280_ = v___x_1286_;
goto v___jp_1279_;
}
}
else
{
uint8_t v___x_1288_; 
v___x_1288_ = 0;
v___y_1280_ = v___x_1288_;
goto v___jp_1279_;
}
v___jp_1279_:
{
lean_object* v___x_1281_; lean_object* v___x_1282_; 
v___x_1281_ = lean_box(v___y_1280_);
v___x_1282_ = lean_array_push(v_acc_1276_, v___x_1281_);
v_e_1275_ = v_body_1278_;
v_acc_1276_ = v___x_1282_;
goto _start;
}
}
else
{
return v_acc_1276_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1289_, lean_object* v_acc_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1289_, v_acc_1290_);
lean_dec_ref(v_e_1289_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1294_){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1296_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1294_, v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l_Lean_Meta_mkGenDiseqMask(v_e_1297_);
lean_dec_ref(v_e_1297_);
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___f_1306_; lean_object* v___x_4344__overap_1307_; lean_object* v___x_1308_; 
v___f_1306_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_4344__overap_1307_ = lean_panic_fn_borrowed(v___f_1306_, v_msg_1300_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
lean_inc(v___y_1302_);
lean_inc_ref(v___y_1301_);
v___x_1308_ = lean_apply_5(v___x_4344__overap_1307_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_, lean_box(0));
return v___x_1308_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_){
_start:
{
lean_object* v_res_1315_; 
v_res_1315_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1309_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_);
lean_dec(v___y_1313_);
lean_dec_ref(v___y_1312_);
lean_dec(v___y_1311_);
lean_dec_ref(v___y_1310_);
return v_res_1315_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1316_, lean_object* v___y_1317_){
_start:
{
uint8_t v___x_1319_; 
v___x_1319_ = l_Lean_Expr_hasMVar(v_e_1316_);
if (v___x_1319_ == 0)
{
lean_object* v___x_1320_; 
v___x_1320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1320_, 0, v_e_1316_);
return v___x_1320_;
}
else
{
lean_object* v___x_1321_; lean_object* v_mctx_1322_; lean_object* v___x_1323_; lean_object* v_fst_1324_; lean_object* v_snd_1325_; lean_object* v___x_1326_; lean_object* v_cache_1327_; lean_object* v_zetaDeltaFVarIds_1328_; lean_object* v_postponed_1329_; lean_object* v_diag_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1339_; 
v___x_1321_ = lean_st_ref_get(v___y_1317_);
v_mctx_1322_ = lean_ctor_get(v___x_1321_, 0);
lean_inc_ref(v_mctx_1322_);
lean_dec(v___x_1321_);
v___x_1323_ = l_Lean_instantiateMVarsCore(v_mctx_1322_, v_e_1316_);
v_fst_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_fst_1324_);
v_snd_1325_ = lean_ctor_get(v___x_1323_, 1);
lean_inc(v_snd_1325_);
lean_dec_ref(v___x_1323_);
v___x_1326_ = lean_st_ref_take(v___y_1317_);
v_cache_1327_ = lean_ctor_get(v___x_1326_, 1);
v_zetaDeltaFVarIds_1328_ = lean_ctor_get(v___x_1326_, 2);
v_postponed_1329_ = lean_ctor_get(v___x_1326_, 3);
v_diag_1330_ = lean_ctor_get(v___x_1326_, 4);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1326_);
if (v_isSharedCheck_1339_ == 0)
{
lean_object* v_unused_1340_; 
v_unused_1340_ = lean_ctor_get(v___x_1326_, 0);
lean_dec(v_unused_1340_);
v___x_1332_ = v___x_1326_;
v_isShared_1333_ = v_isSharedCheck_1339_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_diag_1330_);
lean_inc(v_postponed_1329_);
lean_inc(v_zetaDeltaFVarIds_1328_);
lean_inc(v_cache_1327_);
lean_dec(v___x_1326_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1339_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
lean_ctor_set(v___x_1332_, 0, v_snd_1325_);
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_snd_1325_);
lean_ctor_set(v_reuseFailAlloc_1338_, 1, v_cache_1327_);
lean_ctor_set(v_reuseFailAlloc_1338_, 2, v_zetaDeltaFVarIds_1328_);
lean_ctor_set(v_reuseFailAlloc_1338_, 3, v_postponed_1329_);
lean_ctor_set(v_reuseFailAlloc_1338_, 4, v_diag_1330_);
v___x_1335_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
v___x_1336_ = lean_st_ref_put(v___y_1317_, v___x_1335_);
v___x_1337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1337_, 0, v_fst_1324_);
return v___x_1337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1341_, lean_object* v___y_1342_, lean_object* v___y_1343_){
_start:
{
lean_object* v_res_1344_; 
v_res_1344_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1341_, v___y_1342_);
lean_dec(v___y_1342_);
return v_res_1344_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_){
_start:
{
lean_object* v___x_1351_; 
v___x_1351_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1345_, v___y_1347_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v_res_1358_; 
v_res_1358_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1352_, v___y_1353_, v___y_1354_, v___y_1355_, v___y_1356_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
lean_dec(v___y_1354_);
lean_dec_ref(v___y_1353_);
return v_res_1358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1359_, uint8_t v_allowLevelAssignments_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1360_, v_k_1359_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
if (lean_obj_tag(v___x_1366_) == 0)
{
lean_object* v_a_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1374_; 
v_a_1367_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1374_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1374_ == 0)
{
v___x_1369_ = v___x_1366_;
v_isShared_1370_ = v_isSharedCheck_1374_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_a_1367_);
lean_dec(v___x_1366_);
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
v_reuseFailAlloc_1373_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_a_1375_ = lean_ctor_get(v___x_1366_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1366_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1366_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1366_);
v___x_1377_ = lean_box(0);
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
v_resetjp_1376_:
{
lean_object* v___x_1380_; 
if (v_isShared_1378_ == 0)
{
v___x_1380_ = v___x_1377_;
goto v_reusejp_1379_;
}
else
{
lean_object* v_reuseFailAlloc_1381_; 
v_reuseFailAlloc_1381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1381_, 0, v_a_1375_);
v___x_1380_ = v_reuseFailAlloc_1381_;
goto v_reusejp_1379_;
}
v_reusejp_1379_:
{
return v___x_1380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1383_, lean_object* v_allowLevelAssignments_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_, lean_object* v___y_1389_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1390_; lean_object* v_res_1391_; 
v_allowLevelAssignments_boxed_1390_ = lean_unbox(v_allowLevelAssignments_1384_);
v_res_1391_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1383_, v_allowLevelAssignments_boxed_1390_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
lean_dec(v___y_1388_);
lean_dec_ref(v___y_1387_);
lean_dec(v___y_1386_);
lean_dec_ref(v___y_1385_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1392_, lean_object* v_k_1393_, uint8_t v_allowLevelAssignments_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
lean_object* v___x_1400_; 
v___x_1400_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1393_, v_allowLevelAssignments_1394_, v___y_1395_, v___y_1396_, v___y_1397_, v___y_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1401_, lean_object* v_k_1402_, lean_object* v_allowLevelAssignments_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_, lean_object* v___y_1408_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1409_; lean_object* v_res_1410_; 
v_allowLevelAssignments_boxed_1409_ = lean_unbox(v_allowLevelAssignments_1403_);
v_res_1410_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1401_, v_k_1402_, v_allowLevelAssignments_boxed_1409_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
lean_dec(v___y_1407_);
lean_dec_ref(v___y_1406_);
lean_dec(v___y_1405_);
lean_dec_ref(v___y_1404_);
return v_res_1410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1413_, size_t v_sz_1414_, size_t v_i_1415_, lean_object* v_b_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_, lean_object* v___y_1419_, lean_object* v___y_1420_){
_start:
{
lean_object* v_a_1423_; uint8_t v___x_1427_; 
v___x_1427_ = lean_usize_dec_lt(v_i_1415_, v_sz_1414_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1428_, 0, v_b_1416_);
return v___x_1428_;
}
else
{
lean_object* v_snd_1429_; lean_object* v___x_1431_; uint8_t v_isShared_1432_; uint8_t v_isSharedCheck_1591_; 
v_snd_1429_ = lean_ctor_get(v_b_1416_, 1);
v_isSharedCheck_1591_ = !lean_is_exclusive(v_b_1416_);
if (v_isSharedCheck_1591_ == 0)
{
lean_object* v_unused_1592_; 
v_unused_1592_ = lean_ctor_get(v_b_1416_, 0);
lean_dec(v_unused_1592_);
v___x_1431_ = v_b_1416_;
v_isShared_1432_ = v_isSharedCheck_1591_;
goto v_resetjp_1430_;
}
else
{
lean_inc(v_snd_1429_);
lean_dec(v_b_1416_);
v___x_1431_ = lean_box(0);
v_isShared_1432_ = v_isSharedCheck_1591_;
goto v_resetjp_1430_;
}
v_resetjp_1430_:
{
lean_object* v_array_1433_; lean_object* v_start_1434_; lean_object* v_stop_1435_; lean_object* v___x_1436_; uint8_t v___x_1437_; 
v_array_1433_ = lean_ctor_get(v_snd_1429_, 0);
v_start_1434_ = lean_ctor_get(v_snd_1429_, 1);
v_stop_1435_ = lean_ctor_get(v_snd_1429_, 2);
v___x_1436_ = lean_box(0);
v___x_1437_ = lean_nat_dec_lt(v_start_1434_, v_stop_1435_);
if (v___x_1437_ == 0)
{
lean_object* v___x_1439_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 0, v___x_1436_);
v___x_1439_ = v___x_1431_;
goto v_reusejp_1438_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1441_, 1, v_snd_1429_);
v___x_1439_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1438_;
}
v_reusejp_1438_:
{
lean_object* v___x_1440_; 
v___x_1440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
}
}
else
{
lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1587_; 
lean_inc(v_stop_1435_);
lean_inc(v_start_1434_);
lean_inc_ref(v_array_1433_);
v_isSharedCheck_1587_ = !lean_is_exclusive(v_snd_1429_);
if (v_isSharedCheck_1587_ == 0)
{
lean_object* v_unused_1588_; lean_object* v_unused_1589_; lean_object* v_unused_1590_; 
v_unused_1588_ = lean_ctor_get(v_snd_1429_, 2);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_snd_1429_, 1);
lean_dec(v_unused_1589_);
v_unused_1590_ = lean_ctor_get(v_snd_1429_, 0);
lean_dec(v_unused_1590_);
v___x_1443_ = v_snd_1429_;
v_isShared_1444_ = v_isSharedCheck_1587_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v_snd_1429_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1587_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v___x_1449_; 
v___x_1445_ = lean_array_fget(v_array_1433_, v_start_1434_);
v___x_1446_ = lean_unsigned_to_nat(1u);
v___x_1447_ = lean_nat_add(v_start_1434_, v___x_1446_);
lean_dec(v_start_1434_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v___x_1447_);
v___x_1449_ = v___x_1443_;
goto v_reusejp_1448_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_array_1433_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v___x_1447_);
lean_ctor_set(v_reuseFailAlloc_1586_, 2, v_stop_1435_);
v___x_1449_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1448_;
}
v_reusejp_1448_:
{
uint8_t v___x_1450_; 
v___x_1450_ = lean_unbox(v___x_1445_);
lean_dec(v___x_1445_);
if (v___x_1450_ == 0)
{
lean_object* v___x_1452_; 
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1449_);
lean_ctor_set(v___x_1431_, 0, v___x_1436_);
v___x_1452_ = v___x_1431_;
goto v_reusejp_1451_;
}
else
{
lean_object* v_reuseFailAlloc_1453_; 
v_reuseFailAlloc_1453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1453_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1453_, 1, v___x_1449_);
v___x_1452_ = v_reuseFailAlloc_1453_;
goto v_reusejp_1451_;
}
v_reusejp_1451_:
{
v_a_1423_ = v___x_1452_;
goto v___jp_1422_;
}
}
else
{
lean_object* v_a_1454_; lean_object* v___y_1456_; lean_object* v___y_1457_; lean_object* v___y_1458_; lean_object* v___y_1459_; lean_object* v___x_1526_; 
v_a_1454_ = lean_array_uget_borrowed(v_as_1413_, v_i_1415_);
lean_inc(v___y_1420_);
lean_inc_ref(v___y_1419_);
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
lean_inc(v_a_1454_);
v___x_1526_ = lean_infer_type(v_a_1454_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1526_) == 0)
{
lean_object* v_a_1527_; lean_object* v___x_1528_; 
v_a_1527_ = lean_ctor_get(v___x_1526_, 0);
lean_inc(v_a_1527_);
lean_dec_ref_known(v___x_1526_, 1);
v___x_1528_ = l_Lean_Meta_matchEq_x3f(v_a_1527_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1528_) == 0)
{
lean_object* v_a_1529_; 
v_a_1529_ = lean_ctor_get(v___x_1528_, 0);
lean_inc(v_a_1529_);
lean_dec_ref_known(v___x_1528_, 1);
if (lean_obj_tag(v_a_1529_) == 1)
{
lean_object* v_val_1530_; lean_object* v_snd_1531_; lean_object* v_fst_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1568_; 
v_val_1530_ = lean_ctor_get(v_a_1529_, 0);
lean_inc(v_val_1530_);
lean_dec_ref_known(v_a_1529_, 1);
v_snd_1531_ = lean_ctor_get(v_val_1530_, 1);
lean_inc(v_snd_1531_);
lean_dec(v_val_1530_);
v_fst_1532_ = lean_ctor_get(v_snd_1531_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v_snd_1531_);
if (v_isSharedCheck_1568_ == 0)
{
lean_object* v_unused_1569_; 
v_unused_1569_ = lean_ctor_get(v_snd_1531_, 1);
lean_dec(v_unused_1569_);
v___x_1534_ = v_snd_1531_;
v_isShared_1535_ = v_isSharedCheck_1568_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_fst_1532_);
lean_dec(v_snd_1531_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1568_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1536_; 
v___x_1536_ = l_Lean_Meta_mkEqRefl(v_fst_1532_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; lean_object* v___x_1538_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
lean_inc(v_a_1454_);
v___x_1538_ = l_Lean_Meta_isExprDefEq(v_a_1454_, v_a_1537_, v___y_1417_, v___y_1418_, v___y_1419_, v___y_1420_);
if (lean_obj_tag(v___x_1538_) == 0)
{
lean_object* v_a_1539_; lean_object* v___x_1541_; uint8_t v_isShared_1542_; uint8_t v_isSharedCheck_1551_; 
v_a_1539_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1551_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1551_ == 0)
{
v___x_1541_ = v___x_1538_;
v_isShared_1542_ = v_isSharedCheck_1551_;
goto v_resetjp_1540_;
}
else
{
lean_inc(v_a_1539_);
lean_dec(v___x_1538_);
v___x_1541_ = lean_box(0);
v_isShared_1542_ = v_isSharedCheck_1551_;
goto v_resetjp_1540_;
}
v_resetjp_1540_:
{
uint8_t v___x_1543_; 
v___x_1543_ = lean_unbox(v_a_1539_);
lean_dec(v_a_1539_);
if (v___x_1543_ == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1546_; 
lean_del_object(v___x_1431_);
v___x_1544_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1535_ == 0)
{
lean_ctor_set(v___x_1534_, 1, v___x_1449_);
lean_ctor_set(v___x_1534_, 0, v___x_1544_);
v___x_1546_ = v___x_1534_;
goto v_reusejp_1545_;
}
else
{
lean_object* v_reuseFailAlloc_1550_; 
v_reuseFailAlloc_1550_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1550_, 0, v___x_1544_);
lean_ctor_set(v_reuseFailAlloc_1550_, 1, v___x_1449_);
v___x_1546_ = v_reuseFailAlloc_1550_;
goto v_reusejp_1545_;
}
v_reusejp_1545_:
{
lean_object* v___x_1548_; 
if (v_isShared_1542_ == 0)
{
lean_ctor_set(v___x_1541_, 0, v___x_1546_);
v___x_1548_ = v___x_1541_;
goto v_reusejp_1547_;
}
else
{
lean_object* v_reuseFailAlloc_1549_; 
v_reuseFailAlloc_1549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1549_, 0, v___x_1546_);
v___x_1548_ = v_reuseFailAlloc_1549_;
goto v_reusejp_1547_;
}
v_reusejp_1547_:
{
return v___x_1548_;
}
}
}
else
{
lean_del_object(v___x_1541_);
lean_del_object(v___x_1534_);
v___y_1456_ = v___y_1417_;
v___y_1457_ = v___y_1418_;
v___y_1458_ = v___y_1419_;
v___y_1459_ = v___y_1420_;
goto v___jp_1455_;
}
}
}
else
{
lean_object* v_a_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1559_; 
lean_del_object(v___x_1534_);
lean_dec_ref(v___x_1449_);
lean_del_object(v___x_1431_);
v_a_1552_ = lean_ctor_get(v___x_1538_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1538_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1554_ = v___x_1538_;
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
else
{
lean_inc(v_a_1552_);
lean_dec(v___x_1538_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1559_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1557_; 
if (v_isShared_1555_ == 0)
{
v___x_1557_ = v___x_1554_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v_a_1552_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1534_);
lean_dec_ref(v___x_1449_);
lean_del_object(v___x_1431_);
v_a_1560_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1536_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1536_);
v___x_1562_ = lean_box(0);
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
v_resetjp_1561_:
{
lean_object* v___x_1565_; 
if (v_isShared_1563_ == 0)
{
v___x_1565_ = v___x_1562_;
goto v_reusejp_1564_;
}
else
{
lean_object* v_reuseFailAlloc_1566_; 
v_reuseFailAlloc_1566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_a_1560_);
v___x_1565_ = v_reuseFailAlloc_1566_;
goto v_reusejp_1564_;
}
v_reusejp_1564_:
{
return v___x_1565_;
}
}
}
}
}
else
{
lean_dec(v_a_1529_);
v___y_1456_ = v___y_1417_;
v___y_1457_ = v___y_1418_;
v___y_1458_ = v___y_1419_;
v___y_1459_ = v___y_1420_;
goto v___jp_1455_;
}
}
else
{
lean_object* v_a_1570_; lean_object* v___x_1572_; uint8_t v_isShared_1573_; uint8_t v_isSharedCheck_1577_; 
lean_dec_ref(v___x_1449_);
lean_del_object(v___x_1431_);
v_a_1570_ = lean_ctor_get(v___x_1528_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v___x_1528_);
if (v_isSharedCheck_1577_ == 0)
{
v___x_1572_ = v___x_1528_;
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
else
{
lean_inc(v_a_1570_);
lean_dec(v___x_1528_);
v___x_1572_ = lean_box(0);
v_isShared_1573_ = v_isSharedCheck_1577_;
goto v_resetjp_1571_;
}
v_resetjp_1571_:
{
lean_object* v___x_1575_; 
if (v_isShared_1573_ == 0)
{
v___x_1575_ = v___x_1572_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v_a_1570_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v___x_1449_);
lean_del_object(v___x_1431_);
v_a_1578_ = lean_ctor_get(v___x_1526_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1526_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1526_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1526_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1583_; 
if (v_isShared_1581_ == 0)
{
v___x_1583_ = v___x_1580_;
goto v_reusejp_1582_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_a_1578_);
v___x_1583_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1582_;
}
v_reusejp_1582_:
{
return v___x_1583_;
}
}
}
v___jp_1455_:
{
lean_object* v___x_1460_; 
lean_inc(v___y_1459_);
lean_inc_ref(v___y_1458_);
lean_inc(v___y_1457_);
lean_inc_ref(v___y_1456_);
lean_inc(v_a_1454_);
v___x_1460_ = lean_infer_type(v_a_1454_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1460_) == 0)
{
lean_object* v_a_1461_; lean_object* v___x_1462_; 
v_a_1461_ = lean_ctor_get(v___x_1460_, 0);
lean_inc(v_a_1461_);
lean_dec_ref_known(v___x_1460_, 1);
v___x_1462_ = l_Lean_Meta_matchHEq_x3f(v_a_1461_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1462_) == 0)
{
lean_object* v_a_1463_; 
v_a_1463_ = lean_ctor_get(v___x_1462_, 0);
lean_inc(v_a_1463_);
lean_dec_ref_known(v___x_1462_, 1);
if (lean_obj_tag(v_a_1463_) == 1)
{
lean_object* v_val_1464_; lean_object* v_snd_1465_; lean_object* v_fst_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1505_; 
lean_del_object(v___x_1431_);
v_val_1464_ = lean_ctor_get(v_a_1463_, 0);
lean_inc(v_val_1464_);
lean_dec_ref_known(v_a_1463_, 1);
v_snd_1465_ = lean_ctor_get(v_val_1464_, 1);
lean_inc(v_snd_1465_);
lean_dec(v_val_1464_);
v_fst_1466_ = lean_ctor_get(v_snd_1465_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v_snd_1465_);
if (v_isSharedCheck_1505_ == 0)
{
lean_object* v_unused_1506_; 
v_unused_1506_ = lean_ctor_get(v_snd_1465_, 1);
lean_dec(v_unused_1506_);
v___x_1468_ = v_snd_1465_;
v_isShared_1469_ = v_isSharedCheck_1505_;
goto v_resetjp_1467_;
}
else
{
lean_inc(v_fst_1466_);
lean_dec(v_snd_1465_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1505_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_Lean_Meta_mkHEqRefl(v_fst_1466_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; lean_object* v___x_1472_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
lean_inc(v_a_1454_);
v___x_1472_ = l_Lean_Meta_isExprDefEq(v_a_1454_, v_a_1471_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
if (lean_obj_tag(v___x_1472_) == 0)
{
lean_object* v_a_1473_; lean_object* v___x_1475_; uint8_t v_isShared_1476_; uint8_t v_isSharedCheck_1488_; 
v_a_1473_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1475_ = v___x_1472_;
v_isShared_1476_ = v_isSharedCheck_1488_;
goto v_resetjp_1474_;
}
else
{
lean_inc(v_a_1473_);
lean_dec(v___x_1472_);
v___x_1475_ = lean_box(0);
v_isShared_1476_ = v_isSharedCheck_1488_;
goto v_resetjp_1474_;
}
v_resetjp_1474_:
{
uint8_t v___x_1477_; 
v___x_1477_ = lean_unbox(v_a_1473_);
lean_dec(v_a_1473_);
if (v___x_1477_ == 0)
{
lean_object* v___x_1478_; lean_object* v___x_1480_; 
v___x_1478_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 1, v___x_1449_);
lean_ctor_set(v___x_1468_, 0, v___x_1478_);
v___x_1480_ = v___x_1468_;
goto v_reusejp_1479_;
}
else
{
lean_object* v_reuseFailAlloc_1484_; 
v_reuseFailAlloc_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1484_, 0, v___x_1478_);
lean_ctor_set(v_reuseFailAlloc_1484_, 1, v___x_1449_);
v___x_1480_ = v_reuseFailAlloc_1484_;
goto v_reusejp_1479_;
}
v_reusejp_1479_:
{
lean_object* v___x_1482_; 
if (v_isShared_1476_ == 0)
{
lean_ctor_set(v___x_1475_, 0, v___x_1480_);
v___x_1482_ = v___x_1475_;
goto v_reusejp_1481_;
}
else
{
lean_object* v_reuseFailAlloc_1483_; 
v_reuseFailAlloc_1483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1480_);
v___x_1482_ = v_reuseFailAlloc_1483_;
goto v_reusejp_1481_;
}
v_reusejp_1481_:
{
return v___x_1482_;
}
}
}
else
{
lean_object* v___x_1486_; 
lean_del_object(v___x_1475_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 1, v___x_1449_);
lean_ctor_set(v___x_1468_, 0, v___x_1436_);
v___x_1486_ = v___x_1468_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1487_, 1, v___x_1449_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
v_a_1423_ = v___x_1486_;
goto v___jp_1422_;
}
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
lean_del_object(v___x_1468_);
lean_dec_ref(v___x_1449_);
v_a_1489_ = lean_ctor_get(v___x_1472_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1472_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1472_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1472_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_del_object(v___x_1468_);
lean_dec_ref(v___x_1449_);
v_a_1497_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1470_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1470_);
v___x_1499_ = lean_box(0);
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
v_resetjp_1498_:
{
lean_object* v___x_1502_; 
if (v_isShared_1500_ == 0)
{
v___x_1502_ = v___x_1499_;
goto v_reusejp_1501_;
}
else
{
lean_object* v_reuseFailAlloc_1503_; 
v_reuseFailAlloc_1503_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1503_, 0, v_a_1497_);
v___x_1502_ = v_reuseFailAlloc_1503_;
goto v_reusejp_1501_;
}
v_reusejp_1501_:
{
return v___x_1502_;
}
}
}
}
}
else
{
lean_object* v___x_1508_; 
lean_dec(v_a_1463_);
if (v_isShared_1432_ == 0)
{
lean_ctor_set(v___x_1431_, 1, v___x_1449_);
lean_ctor_set(v___x_1431_, 0, v___x_1436_);
v___x_1508_ = v___x_1431_;
goto v_reusejp_1507_;
}
else
{
lean_object* v_reuseFailAlloc_1509_; 
v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1436_);
lean_ctor_set(v_reuseFailAlloc_1509_, 1, v___x_1449_);
v___x_1508_ = v_reuseFailAlloc_1509_;
goto v_reusejp_1507_;
}
v_reusejp_1507_:
{
v_a_1423_ = v___x_1508_;
goto v___jp_1422_;
}
}
}
else
{
lean_object* v_a_1510_; lean_object* v___x_1512_; uint8_t v_isShared_1513_; uint8_t v_isSharedCheck_1517_; 
lean_dec_ref(v___x_1449_);
lean_del_object(v___x_1431_);
v_a_1510_ = lean_ctor_get(v___x_1462_, 0);
v_isSharedCheck_1517_ = !lean_is_exclusive(v___x_1462_);
if (v_isSharedCheck_1517_ == 0)
{
v___x_1512_ = v___x_1462_;
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
else
{
lean_inc(v_a_1510_);
lean_dec(v___x_1462_);
v___x_1512_ = lean_box(0);
v_isShared_1513_ = v_isSharedCheck_1517_;
goto v_resetjp_1511_;
}
v_resetjp_1511_:
{
lean_object* v___x_1515_; 
if (v_isShared_1513_ == 0)
{
v___x_1515_ = v___x_1512_;
goto v_reusejp_1514_;
}
else
{
lean_object* v_reuseFailAlloc_1516_; 
v_reuseFailAlloc_1516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1516_, 0, v_a_1510_);
v___x_1515_ = v_reuseFailAlloc_1516_;
goto v_reusejp_1514_;
}
v_reusejp_1514_:
{
return v___x_1515_;
}
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec_ref(v___x_1449_);
lean_del_object(v___x_1431_);
v_a_1518_ = lean_ctor_get(v___x_1460_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1460_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1460_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1460_);
v___x_1520_ = lean_box(0);
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
v_resetjp_1519_:
{
lean_object* v___x_1523_; 
if (v_isShared_1521_ == 0)
{
v___x_1523_ = v___x_1520_;
goto v_reusejp_1522_;
}
else
{
lean_object* v_reuseFailAlloc_1524_; 
v_reuseFailAlloc_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1524_, 0, v_a_1518_);
v___x_1523_ = v_reuseFailAlloc_1524_;
goto v_reusejp_1522_;
}
v_reusejp_1522_:
{
return v___x_1523_;
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
v___jp_1422_:
{
size_t v___x_1424_; size_t v___x_1425_; 
v___x_1424_ = ((size_t)1ULL);
v___x_1425_ = lean_usize_add(v_i_1415_, v___x_1424_);
v_i_1415_ = v___x_1425_;
v_b_1416_ = v_a_1423_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1593_, lean_object* v_sz_1594_, lean_object* v_i_1595_, lean_object* v_b_1596_, lean_object* v___y_1597_, lean_object* v___y_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_){
_start:
{
size_t v_sz_boxed_1602_; size_t v_i_boxed_1603_; lean_object* v_res_1604_; 
v_sz_boxed_1602_ = lean_unbox_usize(v_sz_1594_);
lean_dec(v_sz_1594_);
v_i_boxed_1603_ = lean_unbox_usize(v_i_1595_);
lean_dec(v_i_1595_);
v_res_1604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1593_, v_sz_boxed_1602_, v_i_boxed_1603_, v_b_1596_, v___y_1597_, v___y_1598_, v___y_1599_, v___y_1600_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
lean_dec(v___y_1598_);
lean_dec_ref(v___y_1597_);
lean_dec_ref(v_as_1593_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1605_, uint8_t v___x_1606_, lean_object* v_localDecl_1607_, lean_object* v_mvarId_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___x_1614_; 
lean_inc_ref(v___x_1605_);
v___x_1614_ = l_Lean_Meta_forallMetaTelescope(v___x_1605_, v___x_1606_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1614_) == 0)
{
lean_object* v_a_1615_; lean_object* v_fst_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1705_; 
v_a_1615_ = lean_ctor_get(v___x_1614_, 0);
lean_inc(v_a_1615_);
lean_dec_ref_known(v___x_1614_, 1);
v_fst_1616_ = lean_ctor_get(v_a_1615_, 0);
v_isSharedCheck_1705_ = !lean_is_exclusive(v_a_1615_);
if (v_isSharedCheck_1705_ == 0)
{
lean_object* v_unused_1706_; 
v_unused_1706_ = lean_ctor_get(v_a_1615_, 1);
lean_dec(v_unused_1706_);
v___x_1618_ = v_a_1615_;
v_isShared_1619_ = v_isSharedCheck_1705_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_fst_1616_);
lean_dec(v_a_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1705_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; 
v___x_1620_ = l_Lean_Meta_mkGenDiseqMask(v___x_1605_);
lean_dec_ref(v___x_1605_);
v___x_1621_ = lean_unsigned_to_nat(0u);
v___x_1622_ = lean_array_get_size(v___x_1620_);
v___x_1623_ = l_Array_toSubarray___redArg(v___x_1620_, v___x_1621_, v___x_1622_);
v___x_1624_ = lean_box(0);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v___x_1623_);
lean_ctor_set(v___x_1618_, 0, v___x_1624_);
v___x_1626_ = v___x_1618_;
goto v_reusejp_1625_;
}
else
{
lean_object* v_reuseFailAlloc_1704_; 
v_reuseFailAlloc_1704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1704_, 0, v___x_1624_);
lean_ctor_set(v_reuseFailAlloc_1704_, 1, v___x_1623_);
v___x_1626_ = v_reuseFailAlloc_1704_;
goto v_reusejp_1625_;
}
v_reusejp_1625_:
{
size_t v_sz_1627_; size_t v___x_1628_; lean_object* v___x_1629_; 
v_sz_1627_ = lean_array_size(v_fst_1616_);
v___x_1628_ = ((size_t)0ULL);
v___x_1629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1616_, v_sz_1627_, v___x_1628_, v___x_1626_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1629_) == 0)
{
lean_object* v_a_1630_; lean_object* v___x_1632_; uint8_t v_isShared_1633_; uint8_t v_isSharedCheck_1695_; 
v_a_1630_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1632_ = v___x_1629_;
v_isShared_1633_ = v_isSharedCheck_1695_;
goto v_resetjp_1631_;
}
else
{
lean_inc(v_a_1630_);
lean_dec(v___x_1629_);
v___x_1632_ = lean_box(0);
v_isShared_1633_ = v_isSharedCheck_1695_;
goto v_resetjp_1631_;
}
v_resetjp_1631_:
{
lean_object* v_fst_1634_; 
v_fst_1634_ = lean_ctor_get(v_a_1630_, 0);
lean_inc(v_fst_1634_);
lean_dec(v_a_1630_);
if (lean_obj_tag(v_fst_1634_) == 0)
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1690_; 
lean_del_object(v___x_1632_);
v___x_1635_ = l_Lean_LocalDecl_toExpr(v_localDecl_1607_);
v___x_1636_ = l_Lean_mkAppN(v___x_1635_, v_fst_1616_);
lean_dec(v_fst_1616_);
v___x_1637_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1636_, v___y_1610_);
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1690_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1690_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1642_; 
lean_inc(v_a_1638_);
v___x_1642_ = l_Lean_Meta_hasAssignableMVar(v_a_1638_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1642_) == 0)
{
lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1681_; 
v_a_1643_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1681_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1681_ == 0)
{
v___x_1645_ = v___x_1642_;
v_isShared_1646_ = v_isSharedCheck_1681_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_dec(v___x_1642_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1681_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
uint8_t v___x_1647_; 
v___x_1647_ = lean_unbox(v_a_1643_);
lean_dec(v_a_1643_);
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; 
lean_del_object(v___x_1645_);
v___x_1648_ = l_Lean_MVarId_getType(v_mvarId_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1648_) == 0)
{
lean_object* v_a_1649_; lean_object* v___x_1650_; 
v_a_1649_ = lean_ctor_get(v___x_1648_, 0);
lean_inc(v_a_1649_);
lean_dec_ref_known(v___x_1648_, 1);
v___x_1650_ = l_Lean_Meta_mkFalseElim(v_a_1649_, v_a_1638_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1661_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1661_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1661_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1661_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1661_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1656_; 
if (v_isShared_1641_ == 0)
{
lean_ctor_set_tag(v___x_1640_, 1);
lean_ctor_set(v___x_1640_, 0, v_a_1651_);
v___x_1656_ = v___x_1640_;
goto v_reusejp_1655_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_a_1651_);
v___x_1656_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1655_;
}
v_reusejp_1655_:
{
lean_object* v___x_1658_; 
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1656_);
v___x_1658_ = v___x_1653_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1659_; 
v_reuseFailAlloc_1659_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1659_, 0, v___x_1656_);
v___x_1658_ = v_reuseFailAlloc_1659_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
return v___x_1658_;
}
}
}
}
else
{
lean_object* v_a_1662_; lean_object* v___x_1664_; uint8_t v_isShared_1665_; uint8_t v_isSharedCheck_1669_; 
lean_del_object(v___x_1640_);
v_a_1662_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1664_ = v___x_1650_;
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
else
{
lean_inc(v_a_1662_);
lean_dec(v___x_1650_);
v___x_1664_ = lean_box(0);
v_isShared_1665_ = v_isSharedCheck_1669_;
goto v_resetjp_1663_;
}
v_resetjp_1663_:
{
lean_object* v___x_1667_; 
if (v_isShared_1665_ == 0)
{
v___x_1667_ = v___x_1664_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1662_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
v_a_1670_ = lean_ctor_get(v___x_1648_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1648_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1648_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1648_);
v___x_1672_ = lean_box(0);
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
v_resetjp_1671_:
{
lean_object* v___x_1675_; 
if (v_isShared_1673_ == 0)
{
v___x_1675_ = v___x_1672_;
goto v_reusejp_1674_;
}
else
{
lean_object* v_reuseFailAlloc_1676_; 
v_reuseFailAlloc_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1676_, 0, v_a_1670_);
v___x_1675_ = v_reuseFailAlloc_1676_;
goto v_reusejp_1674_;
}
v_reusejp_1674_:
{
return v___x_1675_;
}
}
}
}
else
{
lean_object* v___x_1679_; 
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
lean_dec(v_mvarId_1608_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1624_);
v___x_1679_ = v___x_1645_;
goto v_reusejp_1678_;
}
else
{
lean_object* v_reuseFailAlloc_1680_; 
v_reuseFailAlloc_1680_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1624_);
v___x_1679_ = v_reuseFailAlloc_1680_;
goto v_reusejp_1678_;
}
v_reusejp_1678_:
{
return v___x_1679_;
}
}
}
}
else
{
lean_object* v_a_1682_; lean_object* v___x_1684_; uint8_t v_isShared_1685_; uint8_t v_isSharedCheck_1689_; 
lean_del_object(v___x_1640_);
lean_dec(v_a_1638_);
lean_dec(v_mvarId_1608_);
v_a_1682_ = lean_ctor_get(v___x_1642_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1642_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1684_ = v___x_1642_;
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
else
{
lean_inc(v_a_1682_);
lean_dec(v___x_1642_);
v___x_1684_ = lean_box(0);
v_isShared_1685_ = v_isSharedCheck_1689_;
goto v_resetjp_1683_;
}
v_resetjp_1683_:
{
lean_object* v___x_1687_; 
if (v_isShared_1685_ == 0)
{
v___x_1687_ = v___x_1684_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
v___x_1687_ = v_reuseFailAlloc_1688_;
goto v_reusejp_1686_;
}
v_reusejp_1686_:
{
return v___x_1687_;
}
}
}
}
}
else
{
lean_object* v_val_1691_; lean_object* v___x_1693_; 
lean_dec(v_fst_1616_);
lean_dec(v_mvarId_1608_);
lean_dec_ref(v_localDecl_1607_);
v_val_1691_ = lean_ctor_get(v_fst_1634_, 0);
lean_inc(v_val_1691_);
lean_dec_ref_known(v_fst_1634_, 1);
if (v_isShared_1633_ == 0)
{
lean_ctor_set(v___x_1632_, 0, v_val_1691_);
v___x_1693_ = v___x_1632_;
goto v_reusejp_1692_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v_val_1691_);
v___x_1693_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1692_;
}
v_reusejp_1692_:
{
return v___x_1693_;
}
}
}
}
else
{
lean_object* v_a_1696_; lean_object* v___x_1698_; uint8_t v_isShared_1699_; uint8_t v_isSharedCheck_1703_; 
lean_dec(v_fst_1616_);
lean_dec(v_mvarId_1608_);
lean_dec_ref(v_localDecl_1607_);
v_a_1696_ = lean_ctor_get(v___x_1629_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1629_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1698_ = v___x_1629_;
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
else
{
lean_inc(v_a_1696_);
lean_dec(v___x_1629_);
v___x_1698_ = lean_box(0);
v_isShared_1699_ = v_isSharedCheck_1703_;
goto v_resetjp_1697_;
}
v_resetjp_1697_:
{
lean_object* v___x_1701_; 
if (v_isShared_1699_ == 0)
{
v___x_1701_ = v___x_1698_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_a_1696_);
v___x_1701_ = v_reuseFailAlloc_1702_;
goto v_reusejp_1700_;
}
v_reusejp_1700_:
{
return v___x_1701_;
}
}
}
}
}
}
else
{
lean_object* v_a_1707_; lean_object* v___x_1709_; uint8_t v_isShared_1710_; uint8_t v_isSharedCheck_1714_; 
lean_dec(v_mvarId_1608_);
lean_dec_ref(v_localDecl_1607_);
lean_dec_ref(v___x_1605_);
v_a_1707_ = lean_ctor_get(v___x_1614_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v___x_1614_);
if (v_isSharedCheck_1714_ == 0)
{
v___x_1709_ = v___x_1614_;
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
else
{
lean_inc(v_a_1707_);
lean_dec(v___x_1614_);
v___x_1709_ = lean_box(0);
v_isShared_1710_ = v_isSharedCheck_1714_;
goto v_resetjp_1708_;
}
v_resetjp_1708_:
{
lean_object* v___x_1712_; 
if (v_isShared_1710_ == 0)
{
v___x_1712_ = v___x_1709_;
goto v_reusejp_1711_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v_a_1707_);
v___x_1712_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1711_;
}
v_reusejp_1711_:
{
return v___x_1712_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1715_, lean_object* v___x_1716_, lean_object* v_localDecl_1717_, lean_object* v_mvarId_1718_, lean_object* v___y_1719_, lean_object* v___y_1720_, lean_object* v___y_1721_, lean_object* v___y_1722_, lean_object* v___y_1723_){
_start:
{
uint8_t v___x_6076__boxed_1724_; lean_object* v_res_1725_; 
v___x_6076__boxed_1724_ = lean_unbox(v___x_1716_);
v_res_1725_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1715_, v___x_6076__boxed_1724_, v_localDecl_1717_, v_mvarId_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_);
lean_dec(v___y_1722_);
lean_dec_ref(v___y_1721_);
lean_dec(v___y_1720_);
lean_dec_ref(v___y_1719_);
return v_res_1725_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; 
v___x_1729_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1730_ = lean_unsigned_to_nat(2u);
v___x_1731_ = lean_unsigned_to_nat(120u);
v___x_1732_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1733_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1734_ = l_mkPanicMessageWithDecl(v___x_1733_, v___x_1732_, v___x_1731_, v___x_1730_, v___x_1729_);
return v___x_1734_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1735_, lean_object* v_localDecl_1736_, lean_object* v_a_1737_, lean_object* v_a_1738_, lean_object* v_a_1739_, lean_object* v_a_1740_){
_start:
{
lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = l_Lean_LocalDecl_type(v_localDecl_1736_);
lean_inc_ref(v___x_1742_);
v___x_1743_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1742_);
if (v___x_1743_ == 0)
{
lean_object* v___x_1744_; lean_object* v___x_1745_; 
lean_dec_ref(v___x_1742_);
lean_dec_ref(v_localDecl_1736_);
lean_dec(v_mvarId_1735_);
v___x_1744_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1745_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1744_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
return v___x_1745_;
}
else
{
uint8_t v___x_1746_; lean_object* v___x_1747_; lean_object* v___f_1748_; uint8_t v___x_1749_; lean_object* v___x_1750_; 
v___x_1746_ = 0;
v___x_1747_ = lean_box(v___x_1746_);
lean_inc(v_mvarId_1735_);
v___f_1748_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1748_, 0, v___x_1742_);
lean_closure_set(v___f_1748_, 1, v___x_1747_);
lean_closure_set(v___f_1748_, 2, v_localDecl_1736_);
lean_closure_set(v___f_1748_, 3, v_mvarId_1735_);
v___x_1749_ = 0;
v___x_1750_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1748_, v___x_1749_, v_a_1737_, v_a_1738_, v_a_1739_, v_a_1740_);
if (lean_obj_tag(v___x_1750_) == 0)
{
lean_object* v_a_1751_; lean_object* v___x_1753_; uint8_t v_isShared_1754_; uint8_t v_isSharedCheck_1770_; 
v_a_1751_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1770_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1770_ == 0)
{
v___x_1753_ = v___x_1750_;
v_isShared_1754_ = v_isSharedCheck_1770_;
goto v_resetjp_1752_;
}
else
{
lean_inc(v_a_1751_);
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v_isShared_1754_ = v_isSharedCheck_1770_;
goto v_resetjp_1752_;
}
v_resetjp_1752_:
{
if (lean_obj_tag(v_a_1751_) == 1)
{
lean_object* v_val_1755_; lean_object* v___x_1756_; lean_object* v___x_1758_; uint8_t v_isShared_1759_; uint8_t v_isSharedCheck_1764_; 
lean_del_object(v___x_1753_);
v_val_1755_ = lean_ctor_get(v_a_1751_, 0);
lean_inc(v_val_1755_);
lean_dec_ref_known(v_a_1751_, 1);
v___x_1756_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1735_, v_val_1755_, v_a_1738_);
v_isSharedCheck_1764_ = !lean_is_exclusive(v___x_1756_);
if (v_isSharedCheck_1764_ == 0)
{
lean_object* v_unused_1765_; 
v_unused_1765_ = lean_ctor_get(v___x_1756_, 0);
lean_dec(v_unused_1765_);
v___x_1758_ = v___x_1756_;
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
else
{
lean_dec(v___x_1756_);
v___x_1758_ = lean_box(0);
v_isShared_1759_ = v_isSharedCheck_1764_;
goto v_resetjp_1757_;
}
v_resetjp_1757_:
{
lean_object* v___x_1760_; lean_object* v___x_1762_; 
v___x_1760_ = lean_box(v___x_1743_);
if (v_isShared_1759_ == 0)
{
lean_ctor_set(v___x_1758_, 0, v___x_1760_);
v___x_1762_ = v___x_1758_;
goto v_reusejp_1761_;
}
else
{
lean_object* v_reuseFailAlloc_1763_; 
v_reuseFailAlloc_1763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1763_, 0, v___x_1760_);
v___x_1762_ = v_reuseFailAlloc_1763_;
goto v_reusejp_1761_;
}
v_reusejp_1761_:
{
return v___x_1762_;
}
}
}
else
{
lean_object* v___x_1766_; lean_object* v___x_1768_; 
lean_dec(v_a_1751_);
lean_dec(v_mvarId_1735_);
v___x_1766_ = lean_box(v___x_1749_);
if (v_isShared_1754_ == 0)
{
lean_ctor_set(v___x_1753_, 0, v___x_1766_);
v___x_1768_ = v___x_1753_;
goto v_reusejp_1767_;
}
else
{
lean_object* v_reuseFailAlloc_1769_; 
v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
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
else
{
lean_object* v_a_1771_; lean_object* v___x_1773_; uint8_t v_isShared_1774_; uint8_t v_isSharedCheck_1778_; 
lean_dec(v_mvarId_1735_);
v_a_1771_ = lean_ctor_get(v___x_1750_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1750_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1773_ = v___x_1750_;
v_isShared_1774_ = v_isSharedCheck_1778_;
goto v_resetjp_1772_;
}
else
{
lean_inc(v_a_1771_);
lean_dec(v___x_1750_);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1779_, lean_object* v_localDecl_1780_, lean_object* v_a_1781_, lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_){
_start:
{
lean_object* v_res_1786_; 
v_res_1786_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1779_, v_localDecl_1780_, v_a_1781_, v_a_1782_, v_a_1783_, v_a_1784_);
lean_dec(v_a_1784_);
lean_dec_ref(v_a_1783_);
lean_dec(v_a_1782_);
lean_dec_ref(v_a_1781_);
return v_res_1786_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; 
v___x_1798_ = lean_box(0);
v___x_1799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1800_ = l_Lean_mkConst(v___x_1799_, v___x_1798_);
return v___x_1800_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1801_; lean_object* v_dummy_1802_; 
v___x_1801_ = lean_box(0);
v_dummy_1802_ = l_Lean_Expr_sort___override(v___x_1801_);
return v_dummy_1802_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1803_, lean_object* v_mvarId_1804_, lean_object* v_as_1805_, size_t v_sz_1806_, size_t v_i_1807_, lean_object* v_b_1808_, lean_object* v___y_1809_, lean_object* v___y_1810_, lean_object* v___y_1811_, lean_object* v___y_1812_){
_start:
{
uint8_t v___x_1814_; 
v___x_1814_ = lean_usize_dec_lt(v_i_1807_, v_sz_1806_);
if (v___x_1814_ == 0)
{
lean_object* v___x_1815_; 
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v___x_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1815_, 0, v_b_1808_);
return v___x_1815_;
}
else
{
lean_object* v_snd_1816_; lean_object* v___x_1818_; uint8_t v_isShared_1819_; uint8_t v_isSharedCheck_2453_; 
v_snd_1816_ = lean_ctor_get(v_b_1808_, 1);
v_isSharedCheck_2453_ = !lean_is_exclusive(v_b_1808_);
if (v_isSharedCheck_2453_ == 0)
{
lean_object* v_unused_2454_; 
v_unused_2454_ = lean_ctor_get(v_b_1808_, 0);
lean_dec(v_unused_2454_);
v___x_1818_ = v_b_1808_;
v_isShared_1819_ = v_isSharedCheck_2453_;
goto v_resetjp_1817_;
}
else
{
lean_inc(v_snd_1816_);
lean_dec(v_b_1808_);
v___x_1818_ = lean_box(0);
v_isShared_1819_ = v_isSharedCheck_2453_;
goto v_resetjp_1817_;
}
v_resetjp_1817_:
{
lean_object* v_a_1821_; lean_object* v___x_1827_; lean_object* v_a_1829_; lean_object* v_a_1834_; 
v___x_1827_ = lean_box(0);
v_a_1834_ = lean_array_uget(v_as_1805_, v_i_1807_);
if (lean_obj_tag(v_a_1834_) == 0)
{
lean_del_object(v___x_1818_);
v_a_1829_ = v_snd_1816_;
goto v___jp_1828_;
}
else
{
lean_object* v_val_1835_; lean_object* v___x_1837_; uint8_t v_isShared_1838_; uint8_t v_isSharedCheck_2452_; 
v_val_1835_ = lean_ctor_get(v_a_1834_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v_a_1834_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_1837_ = v_a_1834_;
v_isShared_1838_ = v_isSharedCheck_2452_;
goto v_resetjp_1836_;
}
else
{
lean_inc(v_val_1835_);
lean_dec(v_a_1834_);
v___x_1837_ = lean_box(0);
v_isShared_1838_ = v_isSharedCheck_2452_;
goto v_resetjp_1836_;
}
v_resetjp_1836_:
{
lean_object* v___x_1839_; lean_object* v___y_1841_; lean_object* v___y_1842_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___x_1880_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1903_; lean_object* v___y_1904_; lean_object* v___y_1905_; lean_object* v___y_1906_; uint8_t v___y_1907_; uint8_t v___x_1908_; lean_object* v___y_1910_; lean_object* v___y_1911_; lean_object* v___y_1912_; uint8_t v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1916_; lean_object* v___y_1917_; lean_object* v___y_1918_; uint8_t v___y_1919_; lean_object* v___y_1920_; uint8_t v___y_1921_; uint8_t v___y_1923_; uint8_t v___y_1924_; lean_object* v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; uint8_t v___y_1931_; lean_object* v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; uint8_t v___y_1936_; uint8_t v___y_1937_; 
v___x_1839_ = lean_box(0);
v___x_1880_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1908_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1835_);
if (v___x_1908_ == 0)
{
lean_object* v___x_1952_; uint8_t v___y_1954_; uint8_t v___y_1955_; lean_object* v___y_1956_; lean_object* v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; uint8_t v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; uint8_t v___y_1969_; uint8_t v___y_1970_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; uint8_t v___y_1976_; lean_object* v___y_1977_; uint8_t v___y_1978_; lean_object* v_a_1979_; lean_object* v___y_1983_; lean_object* v___y_1984_; lean_object* v___y_1985_; uint8_t v___y_1986_; lean_object* v___y_1987_; uint8_t v___y_1988_; lean_object* v___y_2043_; lean_object* v___y_2044_; lean_object* v___y_2045_; uint8_t v___y_2046_; lean_object* v___y_2047_; uint8_t v___y_2048_; uint8_t v___y_2049_; lean_object* v___y_2051_; lean_object* v___y_2052_; lean_object* v___y_2053_; uint8_t v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; uint8_t v___y_2057_; uint8_t v___y_2058_; lean_object* v___y_2061_; lean_object* v___y_2062_; lean_object* v___y_2063_; uint8_t v___y_2064_; lean_object* v___y_2065_; uint8_t v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2080_; lean_object* v___y_2081_; lean_object* v___y_2082_; uint8_t v___y_2083_; lean_object* v___y_2084_; uint8_t v___y_2085_; uint8_t v___y_2086_; uint8_t v___y_2088_; uint8_t v_isHEq_2089_; lean_object* v___y_2090_; lean_object* v___y_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2097_; uint8_t v___y_2098_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; lean_object* v___y_2102_; lean_object* v___y_2103_; uint8_t v_isEq_2159_; lean_object* v___y_2160_; lean_object* v___y_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2209_; lean_object* v___y_2210_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2255_; lean_object* v___y_2256_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___x_2389_; 
v___x_1952_ = l_Lean_LocalDecl_type(v_val_1835_);
lean_inc_ref(v___x_1952_);
v___x_2389_ = l_Lean_Meta_matchNot_x3f(v___x_1952_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_2389_) == 0)
{
lean_object* v_a_2390_; 
v_a_2390_ = lean_ctor_get(v___x_2389_, 0);
lean_inc(v_a_2390_);
lean_dec_ref_known(v___x_2389_, 1);
if (lean_obj_tag(v_a_2390_) == 1)
{
lean_object* v_val_2391_; lean_object* v___x_2392_; 
v_val_2391_ = lean_ctor_get(v_a_2390_, 0);
lean_inc(v_val_2391_);
lean_dec_ref_known(v_a_2390_, 1);
v___x_2392_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2391_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
lean_inc(v_a_2393_);
lean_dec_ref_known(v___x_2392_, 1);
if (lean_obj_tag(v_a_2393_) == 1)
{
lean_object* v_val_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2435_; 
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec_ref(v_config_1803_);
v_val_2394_ = lean_ctor_get(v_a_2393_, 0);
v_isSharedCheck_2435_ = !lean_is_exclusive(v_a_2393_);
if (v_isSharedCheck_2435_ == 0)
{
v___x_2396_ = v_a_2393_;
v_isShared_2397_ = v_isSharedCheck_2435_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_val_2394_);
lean_dec(v_a_2393_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2435_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2398_; 
lean_inc(v_mvarId_1804_);
v___x_2398_ = l_Lean_MVarId_getType(v_mvarId_1804_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_2398_) == 0)
{
lean_object* v_a_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; 
v_a_2399_ = lean_ctor_get(v___x_2398_, 0);
lean_inc(v_a_2399_);
lean_dec_ref_known(v___x_2398_, 1);
v___x_2400_ = l_Lean_LocalDecl_toExpr(v_val_1835_);
v___x_2401_ = l_Lean_mkFVar(v_val_2394_);
v___x_2402_ = l_Lean_Expr_app___override(v___x_2400_, v___x_2401_);
v___x_2403_ = l_Lean_Meta_mkFalseElim(v_a_2399_, v___x_2402_, v___y_1809_, v___y_1810_, v___y_1811_, v___y_1812_);
if (lean_obj_tag(v___x_2403_) == 0)
{
lean_object* v_a_2404_; lean_object* v___x_2405_; 
v_a_2404_ = lean_ctor_get(v___x_2403_, 0);
lean_inc(v_a_2404_);
lean_dec_ref_known(v___x_2403_, 1);
v___x_2405_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1804_, v_a_2404_, v___y_1810_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v___x_2406_; lean_object* v___x_2408_; 
lean_dec_ref_known(v___x_2405_, 1);
v___x_2406_ = lean_box(v___x_1814_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2406_);
v___x_2408_ = v___x_2396_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2410_; 
v_reuseFailAlloc_2410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2410_, 0, v___x_2406_);
v___x_2408_ = v_reuseFailAlloc_2410_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
lean_object* v___x_2409_; 
v___x_2409_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2408_);
lean_ctor_set(v___x_2409_, 1, v___x_1839_);
v_a_1821_ = v___x_2409_;
goto v___jp_1820_;
}
}
else
{
lean_object* v_a_2411_; lean_object* v___x_2413_; uint8_t v_isShared_2414_; uint8_t v_isSharedCheck_2418_; 
lean_del_object(v___x_2396_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
v_a_2411_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2418_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2418_ == 0)
{
v___x_2413_ = v___x_2405_;
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
else
{
lean_inc(v_a_2411_);
lean_dec(v___x_2405_);
v___x_2413_ = lean_box(0);
v_isShared_2414_ = v_isSharedCheck_2418_;
goto v_resetjp_2412_;
}
v_resetjp_2412_:
{
lean_object* v___x_2416_; 
if (v_isShared_2414_ == 0)
{
v___x_2416_ = v___x_2413_;
goto v_reusejp_2415_;
}
else
{
lean_object* v_reuseFailAlloc_2417_; 
v_reuseFailAlloc_2417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2417_, 0, v_a_2411_);
v___x_2416_ = v_reuseFailAlloc_2417_;
goto v_reusejp_2415_;
}
v_reusejp_2415_:
{
return v___x_2416_;
}
}
}
}
else
{
lean_object* v_a_2419_; lean_object* v___x_2421_; uint8_t v_isShared_2422_; uint8_t v_isSharedCheck_2426_; 
lean_del_object(v___x_2396_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_2419_ = lean_ctor_get(v___x_2403_, 0);
v_isSharedCheck_2426_ = !lean_is_exclusive(v___x_2403_);
if (v_isSharedCheck_2426_ == 0)
{
v___x_2421_ = v___x_2403_;
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
else
{
lean_inc(v_a_2419_);
lean_dec(v___x_2403_);
v___x_2421_ = lean_box(0);
v_isShared_2422_ = v_isSharedCheck_2426_;
goto v_resetjp_2420_;
}
v_resetjp_2420_:
{
lean_object* v___x_2424_; 
if (v_isShared_2422_ == 0)
{
v___x_2424_ = v___x_2421_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_a_2419_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
else
{
lean_object* v_a_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_del_object(v___x_2396_);
lean_dec(v_val_2394_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_2427_ = lean_ctor_get(v___x_2398_, 0);
v_isSharedCheck_2434_ = !lean_is_exclusive(v___x_2398_);
if (v_isSharedCheck_2434_ == 0)
{
v___x_2429_ = v___x_2398_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_a_2427_);
lean_dec(v___x_2398_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_a_2427_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
}
}
else
{
lean_dec(v_a_2393_);
v___y_2255_ = v___y_1809_;
v___y_2256_ = v___y_1810_;
v___y_2257_ = v___y_1811_;
v___y_2258_ = v___y_1812_;
goto v___jp_2254_;
}
}
else
{
lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2436_ = lean_ctor_get(v___x_2392_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2392_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2392_);
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
lean_dec(v_a_2390_);
v___y_2255_ = v___y_1809_;
v___y_2256_ = v___y_1810_;
v___y_2257_ = v___y_1811_;
v___y_2258_ = v___y_1812_;
goto v___jp_2254_;
}
}
else
{
lean_object* v_a_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2451_; 
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2444_ = lean_ctor_get(v___x_2389_, 0);
v_isSharedCheck_2451_ = !lean_is_exclusive(v___x_2389_);
if (v_isSharedCheck_2451_ == 0)
{
v___x_2446_ = v___x_2389_;
v_isShared_2447_ = v_isSharedCheck_2451_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_a_2444_);
lean_dec(v___x_2389_);
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
v___jp_1953_:
{
uint8_t v_genDiseq_1960_; 
v_genDiseq_1960_ = lean_ctor_get_uint8(v_config_1803_, sizeof(void*)*1 + 2);
if (v_genDiseq_1960_ == 0)
{
lean_dec_ref(v___x_1952_);
v___y_1931_ = v___y_1954_;
v___y_1932_ = v___y_1959_;
v___y_1933_ = v___y_1958_;
v___y_1934_ = v___y_1956_;
v___y_1935_ = v___y_1957_;
v___y_1936_ = v___y_1955_;
v___y_1937_ = v___x_1908_;
goto v___jp_1930_;
}
else
{
uint8_t v___x_1961_; 
v___x_1961_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1952_);
v___y_1931_ = v___y_1954_;
v___y_1932_ = v___y_1959_;
v___y_1933_ = v___y_1958_;
v___y_1934_ = v___y_1956_;
v___y_1935_ = v___y_1957_;
v___y_1936_ = v___y_1955_;
v___y_1937_ = v___x_1961_;
goto v___jp_1930_;
}
}
v___jp_1962_:
{
if (v___y_1970_ == 0)
{
lean_dec_ref(v___y_1967_);
v___y_1954_ = v___y_1966_;
v___y_1955_ = v___y_1969_;
v___y_1956_ = v___y_1965_;
v___y_1957_ = v___y_1964_;
v___y_1958_ = v___y_1968_;
v___y_1959_ = v___y_1963_;
goto v___jp_1953_;
}
else
{
lean_object* v___x_1971_; 
lean_dec_ref(v___x_1952_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v___x_1971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1971_, 0, v___y_1967_);
return v___x_1971_;
}
}
v___jp_1972_:
{
uint8_t v___x_1980_; 
v___x_1980_ = l_Lean_Exception_isInterrupt(v_a_1979_);
if (v___x_1980_ == 0)
{
uint8_t v___x_1981_; 
lean_inc_ref(v_a_1979_);
v___x_1981_ = l_Lean_Exception_isRuntime(v_a_1979_);
v___y_1963_ = v___y_1975_;
v___y_1964_ = v___y_1974_;
v___y_1965_ = v___y_1973_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v_a_1979_;
v___y_1968_ = v___y_1977_;
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___x_1981_;
goto v___jp_1962_;
}
else
{
v___y_1963_ = v___y_1975_;
v___y_1964_ = v___y_1974_;
v___y_1965_ = v___y_1973_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v_a_1979_;
v___y_1968_ = v___y_1977_;
v___y_1969_ = v___y_1978_;
v___y_1970_ = v___x_1980_;
goto v___jp_1962_;
}
}
v___jp_1982_:
{
lean_object* v___x_1989_; 
lean_inc_ref(v___x_1952_);
v___x_1989_ = l_Lean_Meta_mkDecide(v___x_1952_, v___y_1985_, v___y_1984_, v___y_1987_, v___y_1983_);
if (lean_obj_tag(v___x_1989_) == 0)
{
lean_object* v_a_1990_; lean_object* v_keyedConfig_1991_; uint8_t v_trackZetaDelta_1992_; lean_object* v_zetaDeltaSet_1993_; lean_object* v_lctx_1994_; lean_object* v_localInstances_1995_; lean_object* v_defEqCtx_x3f_1996_; lean_object* v_synthPendingDepth_1997_; lean_object* v_customCanUnfoldPredicate_x3f_1998_; uint8_t v_univApprox_1999_; uint8_t v_inTypeClassResolution_2000_; uint8_t v_cacheInferType_2001_; uint8_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v_a_1990_ = lean_ctor_get(v___x_1989_, 0);
lean_inc_n(v_a_1990_, 2);
lean_dec_ref_known(v___x_1989_, 1);
v_keyedConfig_1991_ = lean_ctor_get(v___y_1985_, 0);
v_trackZetaDelta_1992_ = lean_ctor_get_uint8(v___y_1985_, sizeof(void*)*7);
v_zetaDeltaSet_1993_ = lean_ctor_get(v___y_1985_, 1);
v_lctx_1994_ = lean_ctor_get(v___y_1985_, 2);
v_localInstances_1995_ = lean_ctor_get(v___y_1985_, 3);
v_defEqCtx_x3f_1996_ = lean_ctor_get(v___y_1985_, 4);
v_synthPendingDepth_1997_ = lean_ctor_get(v___y_1985_, 5);
v_customCanUnfoldPredicate_x3f_1998_ = lean_ctor_get(v___y_1985_, 6);
v_univApprox_1999_ = lean_ctor_get_uint8(v___y_1985_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2000_ = lean_ctor_get_uint8(v___y_1985_, sizeof(void*)*7 + 2);
v_cacheInferType_2001_ = lean_ctor_get_uint8(v___y_1985_, sizeof(void*)*7 + 3);
v___x_2002_ = 1;
lean_inc_ref(v_keyedConfig_1991_);
v___x_2003_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2002_, v_keyedConfig_1991_);
lean_inc(v_customCanUnfoldPredicate_x3f_1998_);
lean_inc(v_synthPendingDepth_1997_);
lean_inc(v_defEqCtx_x3f_1996_);
lean_inc_ref(v_localInstances_1995_);
lean_inc_ref(v_lctx_1994_);
lean_inc(v_zetaDeltaSet_1993_);
v___x_2004_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2004_, 0, v___x_2003_);
lean_ctor_set(v___x_2004_, 1, v_zetaDeltaSet_1993_);
lean_ctor_set(v___x_2004_, 2, v_lctx_1994_);
lean_ctor_set(v___x_2004_, 3, v_localInstances_1995_);
lean_ctor_set(v___x_2004_, 4, v_defEqCtx_x3f_1996_);
lean_ctor_set(v___x_2004_, 5, v_synthPendingDepth_1997_);
lean_ctor_set(v___x_2004_, 6, v_customCanUnfoldPredicate_x3f_1998_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*7, v_trackZetaDelta_1992_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*7 + 1, v_univApprox_1999_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2000_);
lean_ctor_set_uint8(v___x_2004_, sizeof(void*)*7 + 3, v_cacheInferType_2001_);
lean_inc(v___y_1983_);
lean_inc_ref(v___y_1987_);
lean_inc(v___y_1984_);
v___x_2005_ = lean_whnf(v_a_1990_, v___x_2004_, v___y_1984_, v___y_1987_, v___y_1983_);
if (lean_obj_tag(v___x_2005_) == 0)
{
lean_object* v_a_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; 
v_a_2006_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2006_);
lean_dec_ref_known(v___x_2005_, 1);
v___x_2007_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2008_ = l_Lean_Expr_isConstOf(v_a_2006_, v___x_2007_);
lean_dec(v_a_2006_);
if (v___x_2008_ == 0)
{
lean_dec(v_a_1990_);
v___y_1954_ = v___y_1986_;
v___y_1955_ = v___y_1988_;
v___y_1956_ = v___y_1985_;
v___y_1957_ = v___y_1984_;
v___y_1958_ = v___y_1987_;
v___y_1959_ = v___y_1983_;
goto v___jp_1953_;
}
else
{
lean_object* v___x_2009_; 
lean_inc(v_a_1990_);
v___x_2009_ = l_Lean_Meta_mkEqRefl(v_a_1990_, v___y_1985_, v___y_1984_, v___y_1987_, v___y_1983_);
if (lean_obj_tag(v___x_2009_) == 0)
{
lean_object* v_a_2010_; lean_object* v___x_2011_; 
v_a_2010_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2010_);
lean_dec_ref_known(v___x_2009_, 1);
lean_inc(v_mvarId_1804_);
v___x_2011_ = l_Lean_MVarId_getType(v_mvarId_1804_, v___y_1985_, v___y_1984_, v___y_1987_, v___y_1983_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v_nargs_2013_; lean_object* v___x_2014_; lean_object* v_dummy_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
v_nargs_2013_ = l_Lean_Expr_getAppNumArgs(v_a_1990_);
v___x_2014_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2015_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_2013_);
v___x_2016_ = lean_mk_array(v_nargs_2013_, v_dummy_2015_);
v___x_2017_ = lean_unsigned_to_nat(1u);
v___x_2018_ = lean_nat_sub(v_nargs_2013_, v___x_2017_);
lean_dec(v_nargs_2013_);
v___x_2019_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1990_, v___x_2016_, v___x_2018_);
v___x_2020_ = lean_array_push(v___x_2019_, v_a_2010_);
v___x_2021_ = l_Lean_mkAppN(v___x_2014_, v___x_2020_);
lean_dec_ref(v___x_2020_);
lean_inc(v_val_1835_);
v___x_2022_ = l_Lean_LocalDecl_toExpr(v_val_1835_);
v___x_2023_ = l_Lean_Meta_mkAbsurd(v_a_2012_, v___x_2022_, v___x_2021_, v___y_1985_, v___y_1984_, v___y_1987_, v___y_1983_);
if (lean_obj_tag(v___x_2023_) == 0)
{
lean_object* v_a_2024_; lean_object* v___x_2025_; 
v_a_2024_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2024_);
lean_dec_ref_known(v___x_2023_, 1);
lean_inc(v_mvarId_1804_);
v___x_2025_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1804_, v_a_2024_, v___y_1984_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2034_; 
lean_dec_ref(v___x_1952_);
lean_dec(v_val_1835_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_isSharedCheck_2034_ = !lean_is_exclusive(v___x_2025_);
if (v_isSharedCheck_2034_ == 0)
{
lean_object* v_unused_2035_; 
v_unused_2035_ = lean_ctor_get(v___x_2025_, 0);
lean_dec(v_unused_2035_);
v___x_2027_ = v___x_2025_;
v_isShared_2028_ = v_isSharedCheck_2034_;
goto v_resetjp_2026_;
}
else
{
lean_dec(v___x_2025_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2034_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
lean_object* v___x_2029_; lean_object* v___x_2031_; 
v___x_2029_ = lean_box(v___x_1814_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set_tag(v___x_2027_, 1);
lean_ctor_set(v___x_2027_, 0, v___x_2029_);
v___x_2031_ = v___x_2027_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2033_; 
v_reuseFailAlloc_2033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2033_, 0, v___x_2029_);
v___x_2031_ = v_reuseFailAlloc_2033_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2032_; 
v___x_2032_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2032_, 0, v___x_2031_);
lean_ctor_set(v___x_2032_, 1, v___x_1839_);
v_a_1821_ = v___x_2032_;
goto v___jp_1820_;
}
}
}
else
{
lean_object* v_a_2036_; 
v_a_2036_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2036_);
lean_dec_ref_known(v___x_2025_, 1);
v___y_1973_ = v___y_1985_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1983_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v_a_1979_ = v_a_2036_;
goto v___jp_1972_;
}
}
else
{
lean_object* v_a_2037_; 
v_a_2037_ = lean_ctor_get(v___x_2023_, 0);
lean_inc(v_a_2037_);
lean_dec_ref_known(v___x_2023_, 1);
v___y_1973_ = v___y_1985_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1983_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v_a_1979_ = v_a_2037_;
goto v___jp_1972_;
}
}
else
{
lean_object* v_a_2038_; 
lean_dec(v_a_2010_);
lean_dec(v_a_1990_);
v_a_2038_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2011_, 1);
v___y_1973_ = v___y_1985_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1983_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v_a_1979_ = v_a_2038_;
goto v___jp_1972_;
}
}
else
{
lean_object* v_a_2039_; 
lean_dec(v_a_1990_);
v_a_2039_ = lean_ctor_get(v___x_2009_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2009_, 1);
v___y_1973_ = v___y_1985_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1983_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v_a_1979_ = v_a_2039_;
goto v___jp_1972_;
}
}
}
else
{
lean_object* v_a_2040_; 
lean_dec(v_a_1990_);
v_a_2040_ = lean_ctor_get(v___x_2005_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2005_, 1);
v___y_1973_ = v___y_1985_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1983_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v_a_1979_ = v_a_2040_;
goto v___jp_1972_;
}
}
else
{
lean_object* v_a_2041_; 
v_a_2041_ = lean_ctor_get(v___x_1989_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_1989_, 1);
v___y_1973_ = v___y_1985_;
v___y_1974_ = v___y_1984_;
v___y_1975_ = v___y_1983_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1988_;
v_a_1979_ = v_a_2041_;
goto v___jp_1972_;
}
}
v___jp_2042_:
{
if (v___y_2049_ == 0)
{
v___y_1954_ = v___y_2046_;
v___y_1955_ = v___y_2048_;
v___y_1956_ = v___y_2045_;
v___y_1957_ = v___y_2044_;
v___y_1958_ = v___y_2047_;
v___y_1959_ = v___y_2043_;
goto v___jp_1953_;
}
else
{
v___y_1983_ = v___y_2043_;
v___y_1984_ = v___y_2044_;
v___y_1985_ = v___y_2045_;
v___y_1986_ = v___y_2046_;
v___y_1987_ = v___y_2047_;
v___y_1988_ = v___y_2048_;
goto v___jp_1982_;
}
}
v___jp_2050_:
{
if (v___y_2058_ == 0)
{
lean_dec_ref(v___y_2056_);
v___y_2043_ = v___y_2053_;
v___y_2044_ = v___y_2052_;
v___y_2045_ = v___y_2051_;
v___y_2046_ = v___y_2054_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___y_2057_;
v___y_2049_ = v___x_1908_;
goto v___jp_2042_;
}
else
{
uint8_t v___x_2059_; 
v___x_2059_ = l_Lean_Expr_hasFVar(v___y_2056_);
lean_dec_ref(v___y_2056_);
if (v___x_2059_ == 0)
{
v___y_1983_ = v___y_2053_;
v___y_1984_ = v___y_2052_;
v___y_1985_ = v___y_2051_;
v___y_1986_ = v___y_2054_;
v___y_1987_ = v___y_2055_;
v___y_1988_ = v___y_2057_;
goto v___jp_1982_;
}
else
{
v___y_2043_ = v___y_2053_;
v___y_2044_ = v___y_2052_;
v___y_2045_ = v___y_2051_;
v___y_2046_ = v___y_2054_;
v___y_2047_ = v___y_2055_;
v___y_2048_ = v___y_2057_;
v___y_2049_ = v___x_1908_;
goto v___jp_2042_;
}
}
}
v___jp_2060_:
{
lean_object* v___x_2068_; 
lean_inc_ref(v___x_1952_);
v___x_2068_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1952_, v___y_2063_);
if (lean_obj_tag(v___x_2068_) == 0)
{
lean_object* v_a_2069_; uint8_t v___x_2070_; 
v_a_2069_ = lean_ctor_get(v___x_2068_, 0);
lean_inc(v_a_2069_);
lean_dec_ref_known(v___x_2068_, 1);
v___x_2070_ = l_Lean_Expr_hasMVar(v_a_2069_);
if (v___x_2070_ == 0)
{
v___y_2051_ = v___y_2061_;
v___y_2052_ = v___y_2063_;
v___y_2053_ = v___y_2062_;
v___y_2054_ = v___y_2064_;
v___y_2055_ = v___y_2065_;
v___y_2056_ = v_a_2069_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___y_2067_;
goto v___jp_2050_;
}
else
{
v___y_2051_ = v___y_2061_;
v___y_2052_ = v___y_2063_;
v___y_2053_ = v___y_2062_;
v___y_2054_ = v___y_2064_;
v___y_2055_ = v___y_2065_;
v___y_2056_ = v_a_2069_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___x_1908_;
goto v___jp_2050_;
}
}
else
{
lean_object* v_a_2071_; lean_object* v___x_2073_; uint8_t v_isShared_2074_; uint8_t v_isSharedCheck_2078_; 
lean_dec_ref(v___x_1952_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2071_ = lean_ctor_get(v___x_2068_, 0);
v_isSharedCheck_2078_ = !lean_is_exclusive(v___x_2068_);
if (v_isSharedCheck_2078_ == 0)
{
v___x_2073_ = v___x_2068_;
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
else
{
lean_inc(v_a_2071_);
lean_dec(v___x_2068_);
v___x_2073_ = lean_box(0);
v_isShared_2074_ = v_isSharedCheck_2078_;
goto v_resetjp_2072_;
}
v_resetjp_2072_:
{
lean_object* v___x_2076_; 
if (v_isShared_2074_ == 0)
{
v___x_2076_ = v___x_2073_;
goto v_reusejp_2075_;
}
else
{
lean_object* v_reuseFailAlloc_2077_; 
v_reuseFailAlloc_2077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2077_, 0, v_a_2071_);
v___x_2076_ = v_reuseFailAlloc_2077_;
goto v_reusejp_2075_;
}
v_reusejp_2075_:
{
return v___x_2076_;
}
}
}
}
v___jp_2079_:
{
if (v___y_2086_ == 0)
{
v___y_1954_ = v___y_2083_;
v___y_1955_ = v___y_2085_;
v___y_1956_ = v___y_2082_;
v___y_1957_ = v___y_2081_;
v___y_1958_ = v___y_2084_;
v___y_1959_ = v___y_2080_;
goto v___jp_1953_;
}
else
{
v___y_2061_ = v___y_2082_;
v___y_2062_ = v___y_2080_;
v___y_2063_ = v___y_2081_;
v___y_2064_ = v___y_2083_;
v___y_2065_ = v___y_2084_;
v___y_2066_ = v___y_2085_;
v___y_2067_ = v___y_2086_;
goto v___jp_2060_;
}
}
v___jp_2087_:
{
uint8_t v_useDecide_2094_; 
v_useDecide_2094_ = lean_ctor_get_uint8(v_config_1803_, sizeof(void*)*1);
if (v_useDecide_2094_ == 0)
{
v___y_2080_ = v___y_2093_;
v___y_2081_ = v___y_2091_;
v___y_2082_ = v___y_2090_;
v___y_2083_ = v___y_2088_;
v___y_2084_ = v___y_2092_;
v___y_2085_ = v_isHEq_2089_;
v___y_2086_ = v___x_1908_;
goto v___jp_2079_;
}
else
{
uint8_t v___x_2095_; 
v___x_2095_ = l_Lean_Expr_hasFVar(v___x_1952_);
if (v___x_2095_ == 0)
{
v___y_2061_ = v___y_2090_;
v___y_2062_ = v___y_2093_;
v___y_2063_ = v___y_2091_;
v___y_2064_ = v___y_2088_;
v___y_2065_ = v___y_2092_;
v___y_2066_ = v_isHEq_2089_;
v___y_2067_ = v_useDecide_2094_;
goto v___jp_2060_;
}
else
{
v___y_2080_ = v___y_2093_;
v___y_2081_ = v___y_2091_;
v___y_2082_ = v___y_2090_;
v___y_2083_ = v___y_2088_;
v___y_2084_ = v___y_2092_;
v___y_2085_ = v_isHEq_2089_;
v___y_2086_ = v___x_1908_;
goto v___jp_2079_;
}
}
}
v___jp_2096_:
{
lean_object* v___x_2104_; 
v___x_2104_ = l_Lean_Meta_isExprDefEq(v___y_2101_, v___y_2097_, v___y_2103_, v___y_2099_, v___y_2100_, v___y_2102_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v_a_2105_; uint8_t v___x_2106_; 
v_a_2105_ = lean_ctor_get(v___x_2104_, 0);
lean_inc(v_a_2105_);
lean_dec_ref_known(v___x_2104_, 1);
v___x_2106_ = lean_unbox(v_a_2105_);
lean_dec(v_a_2105_);
if (v___x_2106_ == 0)
{
v___y_2088_ = v___y_2098_;
v_isHEq_2089_ = v___x_1814_;
v___y_2090_ = v___y_2103_;
v___y_2091_ = v___y_2099_;
v___y_2092_ = v___y_2100_;
v___y_2093_ = v___y_2102_;
goto v___jp_2087_;
}
else
{
lean_object* v___x_2107_; 
lean_dec_ref(v___x_1952_);
lean_dec_ref(v_config_1803_);
lean_inc(v_mvarId_1804_);
v___x_2107_ = l_Lean_MVarId_getType(v_mvarId_1804_, v___y_2103_, v___y_2099_, v___y_2100_, v___y_2102_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l_Lean_LocalDecl_toExpr(v_val_1835_);
v___x_2110_ = l_Lean_Meta_mkEqOfHEq(v___x_2109_, v___x_1814_, v___y_2103_, v___y_2099_, v___y_2100_, v___y_2102_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v_a_2111_; lean_object* v___x_2112_; 
v_a_2111_ = lean_ctor_get(v___x_2110_, 0);
lean_inc(v_a_2111_);
lean_dec_ref_known(v___x_2110_, 1);
v___x_2112_ = l_Lean_Meta_mkNoConfusion(v_a_2108_, v_a_2111_, v___y_2103_, v___y_2099_, v___y_2100_, v___y_2102_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1804_, v_a_2113_, v___y_2099_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; 
lean_dec_ref_known(v___x_2114_, 1);
v___x_2115_ = lean_box(v___x_1814_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
v___x_2117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
lean_ctor_set(v___x_2117_, 1, v___x_1839_);
v_a_1821_ = v___x_2117_;
goto v___jp_1820_;
}
else
{
lean_object* v_a_2118_; lean_object* v___x_2120_; uint8_t v_isShared_2121_; uint8_t v_isSharedCheck_2125_; 
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
v_a_2118_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2125_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2125_ == 0)
{
v___x_2120_ = v___x_2114_;
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
else
{
lean_inc(v_a_2118_);
lean_dec(v___x_2114_);
v___x_2120_ = lean_box(0);
v_isShared_2121_ = v_isSharedCheck_2125_;
goto v_resetjp_2119_;
}
v_resetjp_2119_:
{
lean_object* v___x_2123_; 
if (v_isShared_2121_ == 0)
{
v___x_2123_ = v___x_2120_;
goto v_reusejp_2122_;
}
else
{
lean_object* v_reuseFailAlloc_2124_; 
v_reuseFailAlloc_2124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2124_, 0, v_a_2118_);
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
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
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
else
{
lean_object* v_a_2134_; lean_object* v___x_2136_; uint8_t v_isShared_2137_; uint8_t v_isSharedCheck_2141_; 
lean_dec(v_a_2108_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_2134_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2141_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2141_ == 0)
{
v___x_2136_ = v___x_2110_;
v_isShared_2137_ = v_isSharedCheck_2141_;
goto v_resetjp_2135_;
}
else
{
lean_inc(v_a_2134_);
lean_dec(v___x_2110_);
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
else
{
lean_object* v_a_2142_; lean_object* v___x_2144_; uint8_t v_isShared_2145_; uint8_t v_isSharedCheck_2149_; 
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_2142_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2149_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2149_ == 0)
{
v___x_2144_ = v___x_2107_;
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
else
{
lean_inc(v_a_2142_);
lean_dec(v___x_2107_);
v___x_2144_ = lean_box(0);
v_isShared_2145_ = v_isSharedCheck_2149_;
goto v_resetjp_2143_;
}
v_resetjp_2143_:
{
lean_object* v___x_2147_; 
if (v_isShared_2145_ == 0)
{
v___x_2147_ = v___x_2144_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2148_; 
v_reuseFailAlloc_2148_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2148_, 0, v_a_2142_);
v___x_2147_ = v_reuseFailAlloc_2148_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
return v___x_2147_;
}
}
}
}
}
else
{
lean_object* v_a_2150_; lean_object* v___x_2152_; uint8_t v_isShared_2153_; uint8_t v_isSharedCheck_2157_; 
lean_dec_ref(v___x_1952_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2150_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2157_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2157_ == 0)
{
v___x_2152_ = v___x_2104_;
v_isShared_2153_ = v_isSharedCheck_2157_;
goto v_resetjp_2151_;
}
else
{
lean_inc(v_a_2150_);
lean_dec(v___x_2104_);
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
v___jp_2158_:
{
lean_object* v___x_2164_; 
lean_inc_ref(v___x_1952_);
v___x_2164_ = l_Lean_Meta_matchHEq_x3f(v___x_1952_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2164_) == 0)
{
lean_object* v_a_2165_; 
v_a_2165_ = lean_ctor_get(v___x_2164_, 0);
lean_inc(v_a_2165_);
lean_dec_ref_known(v___x_2164_, 1);
if (lean_obj_tag(v_a_2165_) == 1)
{
lean_object* v_val_2166_; lean_object* v_snd_2167_; lean_object* v_snd_2168_; lean_object* v_fst_2169_; lean_object* v_fst_2170_; lean_object* v_fst_2171_; lean_object* v_snd_2172_; lean_object* v___x_2173_; 
v_val_2166_ = lean_ctor_get(v_a_2165_, 0);
lean_inc(v_val_2166_);
lean_dec_ref_known(v_a_2165_, 1);
v_snd_2167_ = lean_ctor_get(v_val_2166_, 1);
lean_inc(v_snd_2167_);
v_snd_2168_ = lean_ctor_get(v_snd_2167_, 1);
lean_inc(v_snd_2168_);
v_fst_2169_ = lean_ctor_get(v_val_2166_, 0);
lean_inc(v_fst_2169_);
lean_dec(v_val_2166_);
v_fst_2170_ = lean_ctor_get(v_snd_2167_, 0);
lean_inc(v_fst_2170_);
lean_dec(v_snd_2167_);
v_fst_2171_ = lean_ctor_get(v_snd_2168_, 0);
lean_inc(v_fst_2171_);
v_snd_2172_ = lean_ctor_get(v_snd_2168_, 1);
lean_inc(v_snd_2172_);
lean_dec(v_snd_2168_);
v___x_2173_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2170_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2173_) == 0)
{
lean_object* v_a_2174_; 
v_a_2174_ = lean_ctor_get(v___x_2173_, 0);
lean_inc(v_a_2174_);
lean_dec_ref_known(v___x_2173_, 1);
if (lean_obj_tag(v_a_2174_) == 1)
{
lean_object* v_val_2175_; lean_object* v___x_2176_; 
v_val_2175_ = lean_ctor_get(v_a_2174_, 0);
lean_inc(v_val_2175_);
lean_dec_ref_known(v_a_2174_, 1);
v___x_2176_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2172_, v___y_2160_, v___y_2161_, v___y_2162_, v___y_2163_);
if (lean_obj_tag(v___x_2176_) == 0)
{
lean_object* v_a_2177_; 
v_a_2177_ = lean_ctor_get(v___x_2176_, 0);
lean_inc(v_a_2177_);
lean_dec_ref_known(v___x_2176_, 1);
if (lean_obj_tag(v_a_2177_) == 1)
{
lean_object* v_toConstantVal_2178_; lean_object* v_val_2179_; lean_object* v_toConstantVal_2180_; lean_object* v_name_2181_; lean_object* v_name_2182_; uint8_t v___x_2183_; 
v_toConstantVal_2178_ = lean_ctor_get(v_val_2175_, 0);
lean_inc_ref(v_toConstantVal_2178_);
lean_dec(v_val_2175_);
v_val_2179_ = lean_ctor_get(v_a_2177_, 0);
lean_inc(v_val_2179_);
lean_dec_ref_known(v_a_2177_, 1);
v_toConstantVal_2180_ = lean_ctor_get(v_val_2179_, 0);
lean_inc_ref(v_toConstantVal_2180_);
lean_dec(v_val_2179_);
v_name_2181_ = lean_ctor_get(v_toConstantVal_2178_, 0);
lean_inc(v_name_2181_);
lean_dec_ref(v_toConstantVal_2178_);
v_name_2182_ = lean_ctor_get(v_toConstantVal_2180_, 0);
lean_inc(v_name_2182_);
lean_dec_ref(v_toConstantVal_2180_);
v___x_2183_ = lean_name_eq(v_name_2181_, v_name_2182_);
lean_dec(v_name_2182_);
lean_dec(v_name_2181_);
if (v___x_2183_ == 0)
{
v___y_2097_ = v_fst_2171_;
v___y_2098_ = v_isEq_2159_;
v___y_2099_ = v___y_2161_;
v___y_2100_ = v___y_2162_;
v___y_2101_ = v_fst_2169_;
v___y_2102_ = v___y_2163_;
v___y_2103_ = v___y_2160_;
goto v___jp_2096_;
}
else
{
if (v___x_1908_ == 0)
{
lean_dec(v_fst_2171_);
lean_dec(v_fst_2169_);
v___y_2088_ = v_isEq_2159_;
v_isHEq_2089_ = v___x_1814_;
v___y_2090_ = v___y_2160_;
v___y_2091_ = v___y_2161_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
goto v___jp_2087_;
}
else
{
v___y_2097_ = v_fst_2171_;
v___y_2098_ = v_isEq_2159_;
v___y_2099_ = v___y_2161_;
v___y_2100_ = v___y_2162_;
v___y_2101_ = v_fst_2169_;
v___y_2102_ = v___y_2163_;
v___y_2103_ = v___y_2160_;
goto v___jp_2096_;
}
}
}
else
{
lean_dec(v_a_2177_);
lean_dec(v_val_2175_);
lean_dec(v_fst_2171_);
lean_dec(v_fst_2169_);
v___y_2088_ = v_isEq_2159_;
v_isHEq_2089_ = v___x_1814_;
v___y_2090_ = v___y_2160_;
v___y_2091_ = v___y_2161_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
goto v___jp_2087_;
}
}
else
{
lean_object* v_a_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2191_; 
lean_dec(v_val_2175_);
lean_dec(v_fst_2171_);
lean_dec(v_fst_2169_);
lean_dec_ref(v___x_1952_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2184_ = lean_ctor_get(v___x_2176_, 0);
v_isSharedCheck_2191_ = !lean_is_exclusive(v___x_2176_);
if (v_isSharedCheck_2191_ == 0)
{
v___x_2186_ = v___x_2176_;
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_a_2184_);
lean_dec(v___x_2176_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2191_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v___x_2189_; 
if (v_isShared_2187_ == 0)
{
v___x_2189_ = v___x_2186_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2190_; 
v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2184_);
v___x_2189_ = v_reuseFailAlloc_2190_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
return v___x_2189_;
}
}
}
}
else
{
lean_dec(v_a_2174_);
lean_dec(v_snd_2172_);
lean_dec(v_fst_2171_);
lean_dec(v_fst_2169_);
v___y_2088_ = v_isEq_2159_;
v_isHEq_2089_ = v___x_1814_;
v___y_2090_ = v___y_2160_;
v___y_2091_ = v___y_2161_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
goto v___jp_2087_;
}
}
else
{
lean_object* v_a_2192_; lean_object* v___x_2194_; uint8_t v_isShared_2195_; uint8_t v_isSharedCheck_2199_; 
lean_dec(v_snd_2172_);
lean_dec(v_fst_2171_);
lean_dec(v_fst_2169_);
lean_dec_ref(v___x_1952_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2192_ = lean_ctor_get(v___x_2173_, 0);
v_isSharedCheck_2199_ = !lean_is_exclusive(v___x_2173_);
if (v_isSharedCheck_2199_ == 0)
{
v___x_2194_ = v___x_2173_;
v_isShared_2195_ = v_isSharedCheck_2199_;
goto v_resetjp_2193_;
}
else
{
lean_inc(v_a_2192_);
lean_dec(v___x_2173_);
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
else
{
lean_dec(v_a_2165_);
v___y_2088_ = v_isEq_2159_;
v_isHEq_2089_ = v___x_1908_;
v___y_2090_ = v___y_2160_;
v___y_2091_ = v___y_2161_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
goto v___jp_2087_;
}
}
else
{
lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2207_; 
lean_dec_ref(v___x_1952_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2200_ = lean_ctor_get(v___x_2164_, 0);
v_isSharedCheck_2207_ = !lean_is_exclusive(v___x_2164_);
if (v_isSharedCheck_2207_ == 0)
{
v___x_2202_ = v___x_2164_;
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_dec(v___x_2164_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2207_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2205_; 
if (v_isShared_2203_ == 0)
{
v___x_2205_ = v___x_2202_;
goto v_reusejp_2204_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_a_2200_);
v___x_2205_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2204_;
}
v_reusejp_2204_:
{
return v___x_2205_;
}
}
}
}
v___jp_2208_:
{
lean_object* v___x_2213_; 
lean_inc_ref(v___x_1952_);
v___x_2213_ = l_Lean_Meta_matchEq_x3f(v___x_1952_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
if (lean_obj_tag(v___x_2213_) == 0)
{
lean_object* v_a_2214_; 
v_a_2214_ = lean_ctor_get(v___x_2213_, 0);
lean_inc(v_a_2214_);
lean_dec_ref_known(v___x_2213_, 1);
if (lean_obj_tag(v_a_2214_) == 1)
{
lean_object* v_val_2215_; lean_object* v_snd_2216_; lean_object* v_fst_2217_; lean_object* v_snd_2218_; lean_object* v___x_2219_; 
v_val_2215_ = lean_ctor_get(v_a_2214_, 0);
lean_inc(v_val_2215_);
lean_dec_ref_known(v_a_2214_, 1);
v_snd_2216_ = lean_ctor_get(v_val_2215_, 1);
lean_inc(v_snd_2216_);
lean_dec(v_val_2215_);
v_fst_2217_ = lean_ctor_get(v_snd_2216_, 0);
lean_inc(v_fst_2217_);
v_snd_2218_ = lean_ctor_get(v_snd_2216_, 1);
lean_inc(v_snd_2218_);
lean_dec(v_snd_2216_);
v___x_2219_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2217_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
if (lean_obj_tag(v___x_2219_) == 0)
{
lean_object* v_a_2220_; 
v_a_2220_ = lean_ctor_get(v___x_2219_, 0);
lean_inc(v_a_2220_);
lean_dec_ref_known(v___x_2219_, 1);
if (lean_obj_tag(v_a_2220_) == 1)
{
lean_object* v_val_2221_; lean_object* v___x_2222_; 
v_val_2221_ = lean_ctor_get(v_a_2220_, 0);
lean_inc(v_val_2221_);
lean_dec_ref_known(v_a_2220_, 1);
v___x_2222_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2218_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_);
if (lean_obj_tag(v___x_2222_) == 0)
{
lean_object* v_a_2223_; 
v_a_2223_ = lean_ctor_get(v___x_2222_, 0);
lean_inc(v_a_2223_);
lean_dec_ref_known(v___x_2222_, 1);
if (lean_obj_tag(v_a_2223_) == 1)
{
lean_object* v_toConstantVal_2224_; lean_object* v_val_2225_; lean_object* v_toConstantVal_2226_; lean_object* v_name_2227_; lean_object* v_name_2228_; uint8_t v___x_2229_; 
v_toConstantVal_2224_ = lean_ctor_get(v_val_2221_, 0);
lean_inc_ref(v_toConstantVal_2224_);
lean_dec(v_val_2221_);
v_val_2225_ = lean_ctor_get(v_a_2223_, 0);
lean_inc(v_val_2225_);
lean_dec_ref_known(v_a_2223_, 1);
v_toConstantVal_2226_ = lean_ctor_get(v_val_2225_, 0);
lean_inc_ref(v_toConstantVal_2226_);
lean_dec(v_val_2225_);
v_name_2227_ = lean_ctor_get(v_toConstantVal_2224_, 0);
lean_inc(v_name_2227_);
lean_dec_ref(v_toConstantVal_2224_);
v_name_2228_ = lean_ctor_get(v_toConstantVal_2226_, 0);
lean_inc(v_name_2228_);
lean_dec_ref(v_toConstantVal_2226_);
v___x_2229_ = lean_name_eq(v_name_2227_, v_name_2228_);
lean_dec(v_name_2228_);
lean_dec(v_name_2227_);
if (v___x_2229_ == 0)
{
lean_dec_ref(v___x_1952_);
lean_dec_ref(v_config_1803_);
v___y_1841_ = v___y_2211_;
v___y_1842_ = v___y_2212_;
v___y_1843_ = v___y_2210_;
v___y_1844_ = v___y_2209_;
goto v___jp_1840_;
}
else
{
if (v___x_1908_ == 0)
{
lean_del_object(v___x_1837_);
v_isEq_2159_ = v___x_1814_;
v___y_2160_ = v___y_2209_;
v___y_2161_ = v___y_2210_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
goto v___jp_2158_;
}
else
{
lean_dec_ref(v___x_1952_);
lean_dec_ref(v_config_1803_);
v___y_1841_ = v___y_2211_;
v___y_1842_ = v___y_2212_;
v___y_1843_ = v___y_2210_;
v___y_1844_ = v___y_2209_;
goto v___jp_1840_;
}
}
}
else
{
lean_dec(v_a_2223_);
lean_dec(v_val_2221_);
lean_del_object(v___x_1837_);
v_isEq_2159_ = v___x_1814_;
v___y_2160_ = v___y_2209_;
v___y_2161_ = v___y_2210_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
goto v___jp_2158_;
}
}
else
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2237_; 
lean_dec(v_val_2221_);
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2230_ = lean_ctor_get(v___x_2222_, 0);
v_isSharedCheck_2237_ = !lean_is_exclusive(v___x_2222_);
if (v_isSharedCheck_2237_ == 0)
{
v___x_2232_ = v___x_2222_;
v_isShared_2233_ = v_isSharedCheck_2237_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2222_);
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
lean_dec(v_a_2220_);
lean_dec(v_snd_2218_);
lean_del_object(v___x_1837_);
v_isEq_2159_ = v___x_1814_;
v___y_2160_ = v___y_2209_;
v___y_2161_ = v___y_2210_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
goto v___jp_2158_;
}
}
else
{
lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2245_; 
lean_dec(v_snd_2218_);
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2238_ = lean_ctor_get(v___x_2219_, 0);
v_isSharedCheck_2245_ = !lean_is_exclusive(v___x_2219_);
if (v_isSharedCheck_2245_ == 0)
{
v___x_2240_ = v___x_2219_;
v_isShared_2241_ = v_isSharedCheck_2245_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_dec(v___x_2219_);
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
else
{
lean_dec(v_a_2214_);
lean_del_object(v___x_1837_);
v_isEq_2159_ = v___x_1908_;
v___y_2160_ = v___y_2209_;
v___y_2161_ = v___y_2210_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
goto v___jp_2158_;
}
}
else
{
lean_object* v_a_2246_; lean_object* v___x_2248_; uint8_t v_isShared_2249_; uint8_t v_isSharedCheck_2253_; 
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2246_ = lean_ctor_get(v___x_2213_, 0);
v_isSharedCheck_2253_ = !lean_is_exclusive(v___x_2213_);
if (v_isSharedCheck_2253_ == 0)
{
v___x_2248_ = v___x_2213_;
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
else
{
lean_inc(v_a_2246_);
lean_dec(v___x_2213_);
v___x_2248_ = lean_box(0);
v_isShared_2249_ = v_isSharedCheck_2253_;
goto v_resetjp_2247_;
}
v_resetjp_2247_:
{
lean_object* v___x_2251_; 
if (v_isShared_2249_ == 0)
{
v___x_2251_ = v___x_2248_;
goto v_reusejp_2250_;
}
else
{
lean_object* v_reuseFailAlloc_2252_; 
v_reuseFailAlloc_2252_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2252_, 0, v_a_2246_);
v___x_2251_ = v_reuseFailAlloc_2252_;
goto v_reusejp_2250_;
}
v_reusejp_2250_:
{
return v___x_2251_;
}
}
}
}
v___jp_2254_:
{
lean_object* v___x_2259_; 
lean_inc_ref(v___x_1952_);
v___x_2259_ = l_Lean_refutableHasNotBit_x3f(v___x_1952_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2259_) == 0)
{
lean_object* v_a_2260_; 
v_a_2260_ = lean_ctor_get(v___x_2259_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v___x_2259_, 1);
if (lean_obj_tag(v_a_2260_) == 1)
{
lean_object* v_val_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2300_; 
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec_ref(v_config_1803_);
v_val_2261_ = lean_ctor_get(v_a_2260_, 0);
v_isSharedCheck_2300_ = !lean_is_exclusive(v_a_2260_);
if (v_isSharedCheck_2300_ == 0)
{
v___x_2263_ = v_a_2260_;
v_isShared_2264_ = v_isSharedCheck_2300_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_val_2261_);
lean_dec(v_a_2260_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2300_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2265_; 
lean_inc(v_mvarId_1804_);
v___x_2265_ = l_Lean_MVarId_getType(v_mvarId_1804_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
lean_inc(v_a_2266_);
lean_dec_ref_known(v___x_2265_, 1);
v___x_2267_ = l_Lean_LocalDecl_toExpr(v_val_1835_);
v___x_2268_ = l_Lean_Meta_mkAbsurd(v_a_2266_, v_val_2261_, v___x_2267_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2268_) == 0)
{
lean_object* v_a_2269_; lean_object* v___x_2270_; 
v_a_2269_ = lean_ctor_get(v___x_2268_, 0);
lean_inc(v_a_2269_);
lean_dec_ref_known(v___x_2268_, 1);
v___x_2270_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1804_, v_a_2269_, v___y_2256_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2273_; 
lean_dec_ref_known(v___x_2270_, 1);
v___x_2271_ = lean_box(v___x_1814_);
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 0, v___x_2271_);
v___x_2273_ = v___x_2263_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
lean_object* v___x_2274_; 
v___x_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2274_, 0, v___x_2273_);
lean_ctor_set(v___x_2274_, 1, v___x_1839_);
v_a_1821_ = v___x_2274_;
goto v___jp_1820_;
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_del_object(v___x_2263_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
v_a_2276_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2270_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2270_);
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
lean_del_object(v___x_2263_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_2284_ = lean_ctor_get(v___x_2268_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2268_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2268_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2268_);
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
lean_del_object(v___x_2263_);
lean_dec(v_val_2261_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_2292_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2299_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2299_ == 0)
{
v___x_2294_ = v___x_2265_;
v_isShared_2295_ = v_isSharedCheck_2299_;
goto v_resetjp_2293_;
}
else
{
lean_inc(v_a_2292_);
lean_dec(v___x_2265_);
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
}
else
{
lean_object* v___x_2301_; 
lean_dec(v_a_2260_);
lean_inc_ref(v___x_1952_);
v___x_2301_ = l_Lean_Meta_matchNe_x3f(v___x_1952_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2301_) == 0)
{
lean_object* v_a_2302_; 
v_a_2302_ = lean_ctor_get(v___x_2301_, 0);
lean_inc(v_a_2302_);
lean_dec_ref_known(v___x_2301_, 1);
if (lean_obj_tag(v_a_2302_) == 1)
{
lean_object* v_val_2303_; lean_object* v___x_2305_; uint8_t v_isShared_2306_; uint8_t v_isSharedCheck_2372_; 
v_val_2303_ = lean_ctor_get(v_a_2302_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v_a_2302_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2305_ = v_a_2302_;
v_isShared_2306_ = v_isSharedCheck_2372_;
goto v_resetjp_2304_;
}
else
{
lean_inc(v_val_2303_);
lean_dec(v_a_2302_);
v___x_2305_ = lean_box(0);
v_isShared_2306_ = v_isSharedCheck_2372_;
goto v_resetjp_2304_;
}
v_resetjp_2304_:
{
lean_object* v_snd_2307_; lean_object* v_fst_2308_; lean_object* v_snd_2309_; lean_object* v___x_2311_; uint8_t v_isShared_2312_; uint8_t v_isSharedCheck_2371_; 
v_snd_2307_ = lean_ctor_get(v_val_2303_, 1);
lean_inc(v_snd_2307_);
lean_dec(v_val_2303_);
v_fst_2308_ = lean_ctor_get(v_snd_2307_, 0);
v_snd_2309_ = lean_ctor_get(v_snd_2307_, 1);
v_isSharedCheck_2371_ = !lean_is_exclusive(v_snd_2307_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2311_ = v_snd_2307_;
v_isShared_2312_ = v_isSharedCheck_2371_;
goto v_resetjp_2310_;
}
else
{
lean_inc(v_snd_2309_);
lean_inc(v_fst_2308_);
lean_dec(v_snd_2307_);
v___x_2311_ = lean_box(0);
v_isShared_2312_ = v_isSharedCheck_2371_;
goto v_resetjp_2310_;
}
v_resetjp_2310_:
{
lean_object* v___x_2313_; 
lean_inc(v_fst_2308_);
v___x_2313_ = l_Lean_Meta_isExprDefEq(v_fst_2308_, v_snd_2309_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2313_) == 0)
{
lean_object* v_a_2314_; uint8_t v___x_2315_; 
v_a_2314_ = lean_ctor_get(v___x_2313_, 0);
lean_inc(v_a_2314_);
lean_dec_ref_known(v___x_2313_, 1);
v___x_2315_ = lean_unbox(v_a_2314_);
lean_dec(v_a_2314_);
if (v___x_2315_ == 0)
{
lean_del_object(v___x_2311_);
lean_dec(v_fst_2308_);
lean_del_object(v___x_2305_);
v___y_2209_ = v___y_2255_;
v___y_2210_ = v___y_2256_;
v___y_2211_ = v___y_2257_;
v___y_2212_ = v___y_2258_;
goto v___jp_2208_;
}
else
{
lean_object* v___x_2316_; 
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec_ref(v_config_1803_);
lean_inc(v_mvarId_1804_);
v___x_2316_ = l_Lean_MVarId_getType(v_mvarId_1804_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v_a_2317_; lean_object* v___x_2318_; 
v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_a_2317_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2318_ = l_Lean_Meta_mkEqRefl(v_fst_2308_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = l_Lean_LocalDecl_toExpr(v_val_1835_);
v___x_2321_ = l_Lean_Meta_mkAbsurd(v_a_2317_, v_a_2319_, v___x_2320_, v___y_2255_, v___y_2256_, v___y_2257_, v___y_2258_);
if (lean_obj_tag(v___x_2321_) == 0)
{
lean_object* v_a_2322_; lean_object* v___x_2323_; 
v_a_2322_ = lean_ctor_get(v___x_2321_, 0);
lean_inc(v_a_2322_);
lean_dec_ref_known(v___x_2321_, 1);
v___x_2323_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1804_, v_a_2322_, v___y_2256_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v___x_2324_; lean_object* v___x_2326_; 
lean_dec_ref_known(v___x_2323_, 1);
v___x_2324_ = lean_box(v___x_1814_);
if (v_isShared_2306_ == 0)
{
lean_ctor_set(v___x_2305_, 0, v___x_2324_);
v___x_2326_ = v___x_2305_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2328_; 
if (v_isShared_2312_ == 0)
{
lean_ctor_set(v___x_2311_, 1, v___x_1839_);
lean_ctor_set(v___x_2311_, 0, v___x_2326_);
v___x_2328_ = v___x_2311_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2326_);
lean_ctor_set(v_reuseFailAlloc_2329_, 1, v___x_1839_);
v___x_2328_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
v_a_1821_ = v___x_2328_;
goto v___jp_1820_;
}
}
}
else
{
lean_object* v_a_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2338_; 
lean_del_object(v___x_2311_);
lean_del_object(v___x_2305_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
v_a_2331_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2338_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2338_ == 0)
{
v___x_2333_ = v___x_2323_;
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_a_2331_);
lean_dec(v___x_2323_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2338_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2336_; 
if (v_isShared_2334_ == 0)
{
v___x_2336_ = v___x_2333_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v_a_2331_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
}
}
else
{
lean_object* v_a_2339_; lean_object* v___x_2341_; uint8_t v_isShared_2342_; uint8_t v_isSharedCheck_2346_; 
lean_del_object(v___x_2311_);
lean_del_object(v___x_2305_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_2339_ = lean_ctor_get(v___x_2321_, 0);
v_isSharedCheck_2346_ = !lean_is_exclusive(v___x_2321_);
if (v_isSharedCheck_2346_ == 0)
{
v___x_2341_ = v___x_2321_;
v_isShared_2342_ = v_isSharedCheck_2346_;
goto v_resetjp_2340_;
}
else
{
lean_inc(v_a_2339_);
lean_dec(v___x_2321_);
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
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_dec(v_a_2317_);
lean_del_object(v___x_2311_);
lean_del_object(v___x_2305_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_2347_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___x_2318_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___x_2318_);
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
}
else
{
lean_object* v_a_2355_; lean_object* v___x_2357_; uint8_t v_isShared_2358_; uint8_t v_isSharedCheck_2362_; 
lean_del_object(v___x_2311_);
lean_dec(v_fst_2308_);
lean_del_object(v___x_2305_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_2355_ = lean_ctor_get(v___x_2316_, 0);
v_isSharedCheck_2362_ = !lean_is_exclusive(v___x_2316_);
if (v_isSharedCheck_2362_ == 0)
{
v___x_2357_ = v___x_2316_;
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
else
{
lean_inc(v_a_2355_);
lean_dec(v___x_2316_);
v___x_2357_ = lean_box(0);
v_isShared_2358_ = v_isSharedCheck_2362_;
goto v_resetjp_2356_;
}
v_resetjp_2356_:
{
lean_object* v___x_2360_; 
if (v_isShared_2358_ == 0)
{
v___x_2360_ = v___x_2357_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2361_; 
v_reuseFailAlloc_2361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2361_, 0, v_a_2355_);
v___x_2360_ = v_reuseFailAlloc_2361_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
return v___x_2360_;
}
}
}
}
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_del_object(v___x_2311_);
lean_dec(v_fst_2308_);
lean_del_object(v___x_2305_);
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2363_ = lean_ctor_get(v___x_2313_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2313_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2313_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2313_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2302_);
v___y_2209_ = v___y_2255_;
v___y_2210_ = v___y_2256_;
v___y_2211_ = v___y_2257_;
v___y_2212_ = v___y_2258_;
goto v___jp_2208_;
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2373_ = lean_ctor_get(v___x_2301_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2301_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2301_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2301_);
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
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec_ref(v___x_1952_);
lean_del_object(v___x_1837_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_2381_ = lean_ctor_get(v___x_2259_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2259_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2259_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2259_);
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
}
else
{
lean_del_object(v___x_1837_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
v_a_1829_ = v___x_1880_;
goto v___jp_1828_;
}
v___jp_1840_:
{
lean_object* v___x_1845_; 
lean_inc(v_mvarId_1804_);
v___x_1845_ = l_Lean_MVarId_getType(v_mvarId_1804_, v___y_1844_, v___y_1843_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1845_) == 0)
{
lean_object* v_a_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v_a_1846_ = lean_ctor_get(v___x_1845_, 0);
lean_inc(v_a_1846_);
lean_dec_ref_known(v___x_1845_, 1);
v___x_1847_ = l_Lean_LocalDecl_toExpr(v_val_1835_);
v___x_1848_ = l_Lean_Meta_mkNoConfusion(v_a_1846_, v___x_1847_, v___y_1844_, v___y_1843_, v___y_1841_, v___y_1842_);
if (lean_obj_tag(v___x_1848_) == 0)
{
lean_object* v_a_1849_; lean_object* v___x_1850_; 
v_a_1849_ = lean_ctor_get(v___x_1848_, 0);
lean_inc(v_a_1849_);
lean_dec_ref_known(v___x_1848_, 1);
v___x_1850_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1804_, v_a_1849_, v___y_1843_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v___x_1851_; lean_object* v___x_1853_; 
lean_dec_ref_known(v___x_1850_, 1);
v___x_1851_ = lean_box(v___x_1814_);
if (v_isShared_1838_ == 0)
{
lean_ctor_set(v___x_1837_, 0, v___x_1851_);
v___x_1853_ = v___x_1837_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1851_);
v___x_1853_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
lean_object* v___x_1854_; 
v___x_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1853_);
lean_ctor_set(v___x_1854_, 1, v___x_1839_);
v_a_1821_ = v___x_1854_;
goto v___jp_1820_;
}
}
else
{
lean_object* v_a_1856_; lean_object* v___x_1858_; uint8_t v_isShared_1859_; uint8_t v_isSharedCheck_1863_; 
lean_del_object(v___x_1837_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
v_a_1856_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1863_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1863_ == 0)
{
v___x_1858_ = v___x_1850_;
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
else
{
lean_inc(v_a_1856_);
lean_dec(v___x_1850_);
v___x_1858_ = lean_box(0);
v_isShared_1859_ = v_isSharedCheck_1863_;
goto v_resetjp_1857_;
}
v_resetjp_1857_:
{
lean_object* v___x_1861_; 
if (v_isShared_1859_ == 0)
{
v___x_1861_ = v___x_1858_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v_a_1856_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_del_object(v___x_1837_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_1864_ = lean_ctor_get(v___x_1848_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1848_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1848_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1848_);
v___x_1866_ = lean_box(0);
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
v_resetjp_1865_:
{
lean_object* v___x_1869_; 
if (v_isShared_1867_ == 0)
{
v___x_1869_ = v___x_1866_;
goto v_reusejp_1868_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_a_1864_);
v___x_1869_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1868_;
}
v_reusejp_1868_:
{
return v___x_1869_;
}
}
}
}
else
{
lean_object* v_a_1872_; lean_object* v___x_1874_; uint8_t v_isShared_1875_; uint8_t v_isSharedCheck_1879_; 
lean_del_object(v___x_1837_);
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
v_a_1872_ = lean_ctor_get(v___x_1845_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1845_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1845_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1845_);
v___x_1874_ = lean_box(0);
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
v_resetjp_1873_:
{
lean_object* v___x_1877_; 
if (v_isShared_1875_ == 0)
{
v___x_1877_ = v___x_1874_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1878_; 
v_reuseFailAlloc_1878_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1878_, 0, v_a_1872_);
v___x_1877_ = v_reuseFailAlloc_1878_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
return v___x_1877_;
}
}
}
}
v___jp_1881_:
{
lean_object* v_searchFuel_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v_searchFuel_1886_ = lean_ctor_get(v_config_1803_, 0);
v___x_1887_ = l_Lean_LocalDecl_fvarId(v_val_1835_);
lean_dec(v_val_1835_);
lean_inc(v_searchFuel_1886_);
lean_inc(v_mvarId_1804_);
v___x_1888_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1804_, v___x_1887_, v_searchFuel_1886_, v___y_1884_, v___y_1882_, v___y_1883_, v___y_1885_);
if (lean_obj_tag(v___x_1888_) == 0)
{
lean_object* v_a_1889_; uint8_t v___x_1890_; 
v_a_1889_ = lean_ctor_get(v___x_1888_, 0);
lean_inc(v_a_1889_);
lean_dec_ref_known(v___x_1888_, 1);
v___x_1890_ = lean_unbox(v_a_1889_);
lean_dec(v_a_1889_);
if (v___x_1890_ == 0)
{
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
v_a_1829_ = v___x_1880_;
goto v___jp_1828_;
}
else
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v___x_1891_ = lean_box(v___x_1814_);
v___x_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1892_, 0, v___x_1891_);
v___x_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1893_, 0, v___x_1892_);
lean_ctor_set(v___x_1893_, 1, v___x_1839_);
v_a_1821_ = v___x_1893_;
goto v___jp_1820_;
}
}
else
{
lean_object* v_a_1894_; lean_object* v___x_1896_; uint8_t v_isShared_1897_; uint8_t v_isSharedCheck_1901_; 
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_1894_ = lean_ctor_get(v___x_1888_, 0);
v_isSharedCheck_1901_ = !lean_is_exclusive(v___x_1888_);
if (v_isSharedCheck_1901_ == 0)
{
v___x_1896_ = v___x_1888_;
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
else
{
lean_inc(v_a_1894_);
lean_dec(v___x_1888_);
v___x_1896_ = lean_box(0);
v_isShared_1897_ = v_isSharedCheck_1901_;
goto v_resetjp_1895_;
}
v_resetjp_1895_:
{
lean_object* v___x_1899_; 
if (v_isShared_1897_ == 0)
{
v___x_1899_ = v___x_1896_;
goto v_reusejp_1898_;
}
else
{
lean_object* v_reuseFailAlloc_1900_; 
v_reuseFailAlloc_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1900_, 0, v_a_1894_);
v___x_1899_ = v_reuseFailAlloc_1900_;
goto v_reusejp_1898_;
}
v_reusejp_1898_:
{
return v___x_1899_;
}
}
}
}
v___jp_1902_:
{
if (v___y_1907_ == 0)
{
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
v_a_1829_ = v___x_1880_;
goto v___jp_1828_;
}
else
{
v___y_1882_ = v___y_1903_;
v___y_1883_ = v___y_1904_;
v___y_1884_ = v___y_1905_;
v___y_1885_ = v___y_1906_;
goto v___jp_1881_;
}
}
v___jp_1909_:
{
if (v___y_1913_ == 0)
{
v___y_1882_ = v___y_1910_;
v___y_1883_ = v___y_1911_;
v___y_1884_ = v___y_1912_;
v___y_1885_ = v___y_1914_;
goto v___jp_1881_;
}
else
{
v___y_1903_ = v___y_1910_;
v___y_1904_ = v___y_1911_;
v___y_1905_ = v___y_1912_;
v___y_1906_ = v___y_1914_;
v___y_1907_ = v___x_1908_;
goto v___jp_1902_;
}
}
v___jp_1915_:
{
if (v___y_1921_ == 0)
{
v___y_1903_ = v___y_1916_;
v___y_1904_ = v___y_1917_;
v___y_1905_ = v___y_1918_;
v___y_1906_ = v___y_1920_;
v___y_1907_ = v___x_1908_;
goto v___jp_1902_;
}
else
{
v___y_1910_ = v___y_1916_;
v___y_1911_ = v___y_1917_;
v___y_1912_ = v___y_1918_;
v___y_1913_ = v___y_1919_;
v___y_1914_ = v___y_1920_;
goto v___jp_1909_;
}
}
v___jp_1922_:
{
uint8_t v_emptyType_1929_; 
v_emptyType_1929_ = lean_ctor_get_uint8(v_config_1803_, sizeof(void*)*1 + 1);
if (v_emptyType_1929_ == 0)
{
v___y_1916_ = v___y_1926_;
v___y_1917_ = v___y_1927_;
v___y_1918_ = v___y_1925_;
v___y_1919_ = v___y_1924_;
v___y_1920_ = v___y_1928_;
v___y_1921_ = v___x_1908_;
goto v___jp_1915_;
}
else
{
if (v___y_1923_ == 0)
{
v___y_1910_ = v___y_1926_;
v___y_1911_ = v___y_1927_;
v___y_1912_ = v___y_1925_;
v___y_1913_ = v___y_1924_;
v___y_1914_ = v___y_1928_;
goto v___jp_1909_;
}
else
{
v___y_1916_ = v___y_1926_;
v___y_1917_ = v___y_1927_;
v___y_1918_ = v___y_1925_;
v___y_1919_ = v___y_1924_;
v___y_1920_ = v___y_1928_;
v___y_1921_ = v___x_1908_;
goto v___jp_1915_;
}
}
}
v___jp_1930_:
{
if (v___y_1937_ == 0)
{
v___y_1923_ = v___y_1931_;
v___y_1924_ = v___y_1936_;
v___y_1925_ = v___y_1934_;
v___y_1926_ = v___y_1935_;
v___y_1927_ = v___y_1933_;
v___y_1928_ = v___y_1932_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1938_; 
lean_inc(v_val_1835_);
lean_inc(v_mvarId_1804_);
v___x_1938_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1804_, v_val_1835_, v___y_1934_, v___y_1935_, v___y_1933_, v___y_1932_);
if (lean_obj_tag(v___x_1938_) == 0)
{
lean_object* v_a_1939_; uint8_t v___x_1940_; 
v_a_1939_ = lean_ctor_get(v___x_1938_, 0);
lean_inc(v_a_1939_);
lean_dec_ref_known(v___x_1938_, 1);
v___x_1940_ = lean_unbox(v_a_1939_);
lean_dec(v_a_1939_);
if (v___x_1940_ == 0)
{
v___y_1923_ = v___y_1931_;
v___y_1924_ = v___y_1936_;
v___y_1925_ = v___y_1934_;
v___y_1926_ = v___y_1935_;
v___y_1927_ = v___y_1933_;
v___y_1928_ = v___y_1932_;
goto v___jp_1922_;
}
else
{
lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; 
lean_dec(v_val_1835_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v___x_1941_ = lean_box(v___x_1814_);
v___x_1942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1942_, 0, v___x_1941_);
v___x_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1943_, 0, v___x_1942_);
lean_ctor_set(v___x_1943_, 1, v___x_1839_);
v_a_1821_ = v___x_1943_;
goto v___jp_1820_;
}
}
else
{
lean_object* v_a_1944_; lean_object* v___x_1946_; uint8_t v_isShared_1947_; uint8_t v_isSharedCheck_1951_; 
lean_dec(v_val_1835_);
lean_del_object(v___x_1818_);
lean_dec(v_snd_1816_);
lean_dec(v_mvarId_1804_);
lean_dec_ref(v_config_1803_);
v_a_1944_ = lean_ctor_get(v___x_1938_, 0);
v_isSharedCheck_1951_ = !lean_is_exclusive(v___x_1938_);
if (v_isSharedCheck_1951_ == 0)
{
v___x_1946_ = v___x_1938_;
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
else
{
lean_inc(v_a_1944_);
lean_dec(v___x_1938_);
v___x_1946_ = lean_box(0);
v_isShared_1947_ = v_isSharedCheck_1951_;
goto v_resetjp_1945_;
}
v_resetjp_1945_:
{
lean_object* v___x_1949_; 
if (v_isShared_1947_ == 0)
{
v___x_1949_ = v___x_1946_;
goto v_reusejp_1948_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v_a_1944_);
v___x_1949_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1948_;
}
v_reusejp_1948_:
{
return v___x_1949_;
}
}
}
}
}
}
}
v___jp_1820_:
{
lean_object* v___x_1822_; lean_object* v___x_1824_; 
v___x_1822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1822_, 0, v_a_1821_);
if (v_isShared_1819_ == 0)
{
lean_ctor_set(v___x_1818_, 0, v___x_1822_);
v___x_1824_ = v___x_1818_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1826_; 
v_reuseFailAlloc_1826_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1822_);
lean_ctor_set(v_reuseFailAlloc_1826_, 1, v_snd_1816_);
v___x_1824_ = v_reuseFailAlloc_1826_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
lean_object* v___x_1825_; 
v___x_1825_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1825_, 0, v___x_1824_);
return v___x_1825_;
}
}
v___jp_1828_:
{
lean_object* v___x_1830_; size_t v___x_1831_; size_t v___x_1832_; 
v___x_1830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1827_);
lean_ctor_set(v___x_1830_, 1, v_a_1829_);
v___x_1831_ = ((size_t)1ULL);
v___x_1832_ = lean_usize_add(v_i_1807_, v___x_1831_);
v_i_1807_ = v___x_1832_;
v_b_1808_ = v___x_1830_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2455_, lean_object* v_mvarId_2456_, lean_object* v_as_2457_, lean_object* v_sz_2458_, lean_object* v_i_2459_, lean_object* v_b_2460_, lean_object* v___y_2461_, lean_object* v___y_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_){
_start:
{
size_t v_sz_boxed_2466_; size_t v_i_boxed_2467_; lean_object* v_res_2468_; 
v_sz_boxed_2466_ = lean_unbox_usize(v_sz_2458_);
lean_dec(v_sz_2458_);
v_i_boxed_2467_ = lean_unbox_usize(v_i_2459_);
lean_dec(v_i_2459_);
v_res_2468_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2455_, v_mvarId_2456_, v_as_2457_, v_sz_boxed_2466_, v_i_boxed_2467_, v_b_2460_, v___y_2461_, v___y_2462_, v___y_2463_, v___y_2464_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec(v___y_2462_);
lean_dec_ref(v___y_2461_);
lean_dec_ref(v_as_2457_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2469_, lean_object* v_mvarId_2470_, lean_object* v_as_2471_, size_t v_sz_2472_, size_t v_i_2473_, lean_object* v_b_2474_, lean_object* v___y_2475_, lean_object* v___y_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_){
_start:
{
uint8_t v___x_2480_; 
v___x_2480_ = lean_usize_dec_lt(v_i_2473_, v_sz_2472_);
if (v___x_2480_ == 0)
{
lean_object* v___x_2481_; 
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v___x_2481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2481_, 0, v_b_2474_);
return v___x_2481_;
}
else
{
lean_object* v_snd_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_3119_; 
v_snd_2482_ = lean_ctor_get(v_b_2474_, 1);
v_isSharedCheck_3119_ = !lean_is_exclusive(v_b_2474_);
if (v_isSharedCheck_3119_ == 0)
{
lean_object* v_unused_3120_; 
v_unused_3120_ = lean_ctor_get(v_b_2474_, 0);
lean_dec(v_unused_3120_);
v___x_2484_ = v_b_2474_;
v_isShared_2485_ = v_isSharedCheck_3119_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_snd_2482_);
lean_dec(v_b_2474_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_3119_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v_a_2487_; lean_object* v___x_2493_; lean_object* v_a_2495_; lean_object* v_a_2500_; 
v___x_2493_ = lean_box(0);
v_a_2500_ = lean_array_uget(v_as_2471_, v_i_2473_);
if (lean_obj_tag(v_a_2500_) == 0)
{
lean_del_object(v___x_2484_);
v_a_2495_ = v_snd_2482_;
goto v___jp_2494_;
}
else
{
lean_object* v_val_2501_; lean_object* v___x_2503_; uint8_t v_isShared_2504_; uint8_t v_isSharedCheck_3118_; 
v_val_2501_ = lean_ctor_get(v_a_2500_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_a_2500_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_2503_ = v_a_2500_;
v_isShared_2504_ = v_isSharedCheck_3118_;
goto v_resetjp_2502_;
}
else
{
lean_inc(v_val_2501_);
lean_dec(v_a_2500_);
v___x_2503_ = lean_box(0);
v_isShared_2504_ = v_isSharedCheck_3118_;
goto v_resetjp_2502_;
}
v_resetjp_2502_:
{
lean_object* v___x_2505_; lean_object* v___y_2507_; lean_object* v___y_2508_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___x_2546_; lean_object* v___y_2548_; lean_object* v___y_2549_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; uint8_t v___y_2573_; uint8_t v___x_2574_; lean_object* v___y_2576_; uint8_t v___y_2577_; lean_object* v___y_2578_; lean_object* v___y_2579_; lean_object* v___y_2580_; lean_object* v___y_2582_; uint8_t v___y_2583_; lean_object* v___y_2584_; lean_object* v___y_2585_; lean_object* v___y_2586_; uint8_t v___y_2587_; uint8_t v___y_2589_; uint8_t v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2597_; lean_object* v___y_2598_; uint8_t v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; uint8_t v___y_2602_; uint8_t v___y_2603_; 
v___x_2505_ = lean_box(0);
v___x_2546_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2574_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2501_);
if (v___x_2574_ == 0)
{
lean_object* v___x_2618_; uint8_t v___y_2620_; uint8_t v___y_2621_; lean_object* v___y_2622_; lean_object* v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2629_; uint8_t v___y_2630_; lean_object* v___y_2631_; lean_object* v___y_2632_; lean_object* v___y_2633_; uint8_t v___y_2634_; lean_object* v___y_2635_; uint8_t v___y_2636_; uint8_t v___y_2639_; lean_object* v___y_2640_; lean_object* v___y_2641_; lean_object* v___y_2642_; lean_object* v___y_2643_; uint8_t v___y_2644_; lean_object* v_a_2645_; uint8_t v___y_2649_; lean_object* v___y_2650_; lean_object* v___y_2651_; lean_object* v___y_2652_; uint8_t v___y_2653_; lean_object* v___y_2654_; uint8_t v___y_2709_; lean_object* v___y_2710_; lean_object* v___y_2711_; lean_object* v___y_2712_; uint8_t v___y_2713_; lean_object* v___y_2714_; uint8_t v___y_2715_; lean_object* v___y_2717_; uint8_t v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; lean_object* v___y_2722_; uint8_t v___y_2723_; uint8_t v___y_2724_; uint8_t v___y_2727_; lean_object* v___y_2728_; lean_object* v___y_2729_; lean_object* v___y_2730_; lean_object* v___y_2731_; uint8_t v___y_2732_; uint8_t v___y_2733_; uint8_t v___y_2746_; lean_object* v___y_2747_; lean_object* v___y_2748_; lean_object* v___y_2749_; uint8_t v___y_2750_; lean_object* v___y_2751_; uint8_t v___y_2752_; uint8_t v___y_2754_; uint8_t v_isHEq_2755_; lean_object* v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; lean_object* v___y_2766_; lean_object* v___y_2767_; lean_object* v___y_2768_; uint8_t v___y_2769_; uint8_t v_isEq_2825_; lean_object* v___y_2826_; lean_object* v___y_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2921_; lean_object* v___y_2922_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___x_3055_; 
v___x_2618_ = l_Lean_LocalDecl_type(v_val_2501_);
lean_inc_ref(v___x_2618_);
v___x_3055_ = l_Lean_Meta_matchNot_x3f(v___x_2618_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
if (lean_obj_tag(v___x_3055_) == 0)
{
lean_object* v_a_3056_; 
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
lean_inc(v_a_3056_);
lean_dec_ref_known(v___x_3055_, 1);
if (lean_obj_tag(v_a_3056_) == 1)
{
lean_object* v_val_3057_; lean_object* v___x_3058_; 
v_val_3057_ = lean_ctor_get(v_a_3056_, 0);
lean_inc(v_val_3057_);
lean_dec_ref_known(v_a_3056_, 1);
v___x_3058_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3057_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
if (lean_obj_tag(v___x_3058_) == 0)
{
lean_object* v_a_3059_; 
v_a_3059_ = lean_ctor_get(v___x_3058_, 0);
lean_inc(v_a_3059_);
lean_dec_ref_known(v___x_3058_, 1);
if (lean_obj_tag(v_a_3059_) == 1)
{
lean_object* v_val_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3101_; 
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec_ref(v_config_2469_);
v_val_3060_ = lean_ctor_get(v_a_3059_, 0);
v_isSharedCheck_3101_ = !lean_is_exclusive(v_a_3059_);
if (v_isSharedCheck_3101_ == 0)
{
v___x_3062_ = v_a_3059_;
v_isShared_3063_ = v_isSharedCheck_3101_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_val_3060_);
lean_dec(v_a_3059_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3101_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v___x_3064_; 
lean_inc(v_mvarId_2470_);
v___x_3064_ = l_Lean_MVarId_getType(v_mvarId_2470_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
if (lean_obj_tag(v___x_3064_) == 0)
{
lean_object* v_a_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; 
v_a_3065_ = lean_ctor_get(v___x_3064_, 0);
lean_inc(v_a_3065_);
lean_dec_ref_known(v___x_3064_, 1);
v___x_3066_ = l_Lean_LocalDecl_toExpr(v_val_2501_);
v___x_3067_ = l_Lean_mkFVar(v_val_3060_);
v___x_3068_ = l_Lean_Expr_app___override(v___x_3066_, v___x_3067_);
v___x_3069_ = l_Lean_Meta_mkFalseElim(v_a_3065_, v___x_3068_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
if (lean_obj_tag(v___x_3069_) == 0)
{
lean_object* v_a_3070_; lean_object* v___x_3071_; 
v_a_3070_ = lean_ctor_get(v___x_3069_, 0);
lean_inc(v_a_3070_);
lean_dec_ref_known(v___x_3069_, 1);
v___x_3071_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2470_, v_a_3070_, v___y_2476_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v___x_3072_; lean_object* v___x_3074_; 
lean_dec_ref_known(v___x_3071_, 1);
v___x_3072_ = lean_box(v___x_2480_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 0, v___x_3072_);
v___x_3074_ = v___x_3062_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3075_, 0, v___x_3074_);
lean_ctor_set(v___x_3075_, 1, v___x_2505_);
v_a_2487_ = v___x_3075_;
goto v___jp_2486_;
}
}
else
{
lean_object* v_a_3077_; lean_object* v___x_3079_; uint8_t v_isShared_3080_; uint8_t v_isSharedCheck_3084_; 
lean_del_object(v___x_3062_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
v_a_3077_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3084_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3084_ == 0)
{
v___x_3079_ = v___x_3071_;
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
else
{
lean_inc(v_a_3077_);
lean_dec(v___x_3071_);
v___x_3079_ = lean_box(0);
v_isShared_3080_ = v_isSharedCheck_3084_;
goto v_resetjp_3078_;
}
v_resetjp_3078_:
{
lean_object* v___x_3082_; 
if (v_isShared_3080_ == 0)
{
v___x_3082_ = v___x_3079_;
goto v_reusejp_3081_;
}
else
{
lean_object* v_reuseFailAlloc_3083_; 
v_reuseFailAlloc_3083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3083_, 0, v_a_3077_);
v___x_3082_ = v_reuseFailAlloc_3083_;
goto v_reusejp_3081_;
}
v_reusejp_3081_:
{
return v___x_3082_;
}
}
}
}
else
{
lean_object* v_a_3085_; lean_object* v___x_3087_; uint8_t v_isShared_3088_; uint8_t v_isSharedCheck_3092_; 
lean_del_object(v___x_3062_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_3085_ = lean_ctor_get(v___x_3069_, 0);
v_isSharedCheck_3092_ = !lean_is_exclusive(v___x_3069_);
if (v_isSharedCheck_3092_ == 0)
{
v___x_3087_ = v___x_3069_;
v_isShared_3088_ = v_isSharedCheck_3092_;
goto v_resetjp_3086_;
}
else
{
lean_inc(v_a_3085_);
lean_dec(v___x_3069_);
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
lean_object* v_a_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3100_; 
lean_del_object(v___x_3062_);
lean_dec(v_val_3060_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_3093_ = lean_ctor_get(v___x_3064_, 0);
v_isSharedCheck_3100_ = !lean_is_exclusive(v___x_3064_);
if (v_isSharedCheck_3100_ == 0)
{
v___x_3095_ = v___x_3064_;
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_a_3093_);
lean_dec(v___x_3064_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3100_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3098_; 
if (v_isShared_3096_ == 0)
{
v___x_3098_ = v___x_3095_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v_a_3093_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
}
else
{
lean_dec(v_a_3059_);
v___y_2921_ = v___y_2475_;
v___y_2922_ = v___y_2476_;
v___y_2923_ = v___y_2477_;
v___y_2924_ = v___y_2478_;
goto v___jp_2920_;
}
}
else
{
lean_object* v_a_3102_; lean_object* v___x_3104_; uint8_t v_isShared_3105_; uint8_t v_isSharedCheck_3109_; 
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_3102_ = lean_ctor_get(v___x_3058_, 0);
v_isSharedCheck_3109_ = !lean_is_exclusive(v___x_3058_);
if (v_isSharedCheck_3109_ == 0)
{
v___x_3104_ = v___x_3058_;
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
else
{
lean_inc(v_a_3102_);
lean_dec(v___x_3058_);
v___x_3104_ = lean_box(0);
v_isShared_3105_ = v_isSharedCheck_3109_;
goto v_resetjp_3103_;
}
v_resetjp_3103_:
{
lean_object* v___x_3107_; 
if (v_isShared_3105_ == 0)
{
v___x_3107_ = v___x_3104_;
goto v_reusejp_3106_;
}
else
{
lean_object* v_reuseFailAlloc_3108_; 
v_reuseFailAlloc_3108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3108_, 0, v_a_3102_);
v___x_3107_ = v_reuseFailAlloc_3108_;
goto v_reusejp_3106_;
}
v_reusejp_3106_:
{
return v___x_3107_;
}
}
}
}
else
{
lean_dec(v_a_3056_);
v___y_2921_ = v___y_2475_;
v___y_2922_ = v___y_2476_;
v___y_2923_ = v___y_2477_;
v___y_2924_ = v___y_2478_;
goto v___jp_2920_;
}
}
else
{
lean_object* v_a_3110_; lean_object* v___x_3112_; uint8_t v_isShared_3113_; uint8_t v_isSharedCheck_3117_; 
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_3110_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3117_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3117_ == 0)
{
v___x_3112_ = v___x_3055_;
v_isShared_3113_ = v_isSharedCheck_3117_;
goto v_resetjp_3111_;
}
else
{
lean_inc(v_a_3110_);
lean_dec(v___x_3055_);
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
v___jp_2619_:
{
uint8_t v_genDiseq_2626_; 
v_genDiseq_2626_ = lean_ctor_get_uint8(v_config_2469_, sizeof(void*)*1 + 2);
if (v_genDiseq_2626_ == 0)
{
lean_dec_ref(v___x_2618_);
v___y_2597_ = v___y_2623_;
v___y_2598_ = v___y_2622_;
v___y_2599_ = v___y_2620_;
v___y_2600_ = v___y_2624_;
v___y_2601_ = v___y_2625_;
v___y_2602_ = v___y_2621_;
v___y_2603_ = v___x_2574_;
goto v___jp_2596_;
}
else
{
uint8_t v___x_2627_; 
v___x_2627_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2618_);
v___y_2597_ = v___y_2623_;
v___y_2598_ = v___y_2622_;
v___y_2599_ = v___y_2620_;
v___y_2600_ = v___y_2624_;
v___y_2601_ = v___y_2625_;
v___y_2602_ = v___y_2621_;
v___y_2603_ = v___x_2627_;
goto v___jp_2596_;
}
}
v___jp_2628_:
{
if (v___y_2636_ == 0)
{
lean_dec_ref(v___y_2629_);
v___y_2620_ = v___y_2630_;
v___y_2621_ = v___y_2634_;
v___y_2622_ = v___y_2632_;
v___y_2623_ = v___y_2633_;
v___y_2624_ = v___y_2635_;
v___y_2625_ = v___y_2631_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2637_; 
lean_dec_ref(v___x_2618_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v___x_2637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2637_, 0, v___y_2629_);
return v___x_2637_;
}
}
v___jp_2638_:
{
uint8_t v___x_2646_; 
v___x_2646_ = l_Lean_Exception_isInterrupt(v_a_2645_);
if (v___x_2646_ == 0)
{
uint8_t v___x_2647_; 
lean_inc_ref(v_a_2645_);
v___x_2647_ = l_Lean_Exception_isRuntime(v_a_2645_);
v___y_2629_ = v_a_2645_;
v___y_2630_ = v___y_2639_;
v___y_2631_ = v___y_2640_;
v___y_2632_ = v___y_2641_;
v___y_2633_ = v___y_2642_;
v___y_2634_ = v___y_2644_;
v___y_2635_ = v___y_2643_;
v___y_2636_ = v___x_2647_;
goto v___jp_2628_;
}
else
{
v___y_2629_ = v_a_2645_;
v___y_2630_ = v___y_2639_;
v___y_2631_ = v___y_2640_;
v___y_2632_ = v___y_2641_;
v___y_2633_ = v___y_2642_;
v___y_2634_ = v___y_2644_;
v___y_2635_ = v___y_2643_;
v___y_2636_ = v___x_2646_;
goto v___jp_2628_;
}
}
v___jp_2648_:
{
lean_object* v___x_2655_; 
lean_inc_ref(v___x_2618_);
v___x_2655_ = l_Lean_Meta_mkDecide(v___x_2618_, v___y_2651_, v___y_2652_, v___y_2654_, v___y_2650_);
if (lean_obj_tag(v___x_2655_) == 0)
{
lean_object* v_a_2656_; lean_object* v_keyedConfig_2657_; uint8_t v_trackZetaDelta_2658_; lean_object* v_zetaDeltaSet_2659_; lean_object* v_lctx_2660_; lean_object* v_localInstances_2661_; lean_object* v_defEqCtx_x3f_2662_; lean_object* v_synthPendingDepth_2663_; lean_object* v_customCanUnfoldPredicate_x3f_2664_; uint8_t v_univApprox_2665_; uint8_t v_inTypeClassResolution_2666_; uint8_t v_cacheInferType_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_a_2656_ = lean_ctor_get(v___x_2655_, 0);
lean_inc_n(v_a_2656_, 2);
lean_dec_ref_known(v___x_2655_, 1);
v_keyedConfig_2657_ = lean_ctor_get(v___y_2651_, 0);
v_trackZetaDelta_2658_ = lean_ctor_get_uint8(v___y_2651_, sizeof(void*)*7);
v_zetaDeltaSet_2659_ = lean_ctor_get(v___y_2651_, 1);
v_lctx_2660_ = lean_ctor_get(v___y_2651_, 2);
v_localInstances_2661_ = lean_ctor_get(v___y_2651_, 3);
v_defEqCtx_x3f_2662_ = lean_ctor_get(v___y_2651_, 4);
v_synthPendingDepth_2663_ = lean_ctor_get(v___y_2651_, 5);
v_customCanUnfoldPredicate_x3f_2664_ = lean_ctor_get(v___y_2651_, 6);
v_univApprox_2665_ = lean_ctor_get_uint8(v___y_2651_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2666_ = lean_ctor_get_uint8(v___y_2651_, sizeof(void*)*7 + 2);
v_cacheInferType_2667_ = lean_ctor_get_uint8(v___y_2651_, sizeof(void*)*7 + 3);
v___x_2668_ = 1;
lean_inc_ref(v_keyedConfig_2657_);
v___x_2669_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2668_, v_keyedConfig_2657_);
lean_inc(v_customCanUnfoldPredicate_x3f_2664_);
lean_inc(v_synthPendingDepth_2663_);
lean_inc(v_defEqCtx_x3f_2662_);
lean_inc_ref(v_localInstances_2661_);
lean_inc_ref(v_lctx_2660_);
lean_inc(v_zetaDeltaSet_2659_);
v___x_2670_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2670_, 0, v___x_2669_);
lean_ctor_set(v___x_2670_, 1, v_zetaDeltaSet_2659_);
lean_ctor_set(v___x_2670_, 2, v_lctx_2660_);
lean_ctor_set(v___x_2670_, 3, v_localInstances_2661_);
lean_ctor_set(v___x_2670_, 4, v_defEqCtx_x3f_2662_);
lean_ctor_set(v___x_2670_, 5, v_synthPendingDepth_2663_);
lean_ctor_set(v___x_2670_, 6, v_customCanUnfoldPredicate_x3f_2664_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7, v_trackZetaDelta_2658_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7 + 1, v_univApprox_2665_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2666_);
lean_ctor_set_uint8(v___x_2670_, sizeof(void*)*7 + 3, v_cacheInferType_2667_);
lean_inc(v___y_2650_);
lean_inc_ref(v___y_2654_);
lean_inc(v___y_2652_);
v___x_2671_ = lean_whnf(v_a_2656_, v___x_2670_, v___y_2652_, v___y_2654_, v___y_2650_);
if (lean_obj_tag(v___x_2671_) == 0)
{
lean_object* v_a_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
v_a_2672_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2672_);
lean_dec_ref_known(v___x_2671_, 1);
v___x_2673_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2674_ = l_Lean_Expr_isConstOf(v_a_2672_, v___x_2673_);
lean_dec(v_a_2672_);
if (v___x_2674_ == 0)
{
lean_dec(v_a_2656_);
v___y_2620_ = v___y_2649_;
v___y_2621_ = v___y_2653_;
v___y_2622_ = v___y_2651_;
v___y_2623_ = v___y_2652_;
v___y_2624_ = v___y_2654_;
v___y_2625_ = v___y_2650_;
goto v___jp_2619_;
}
else
{
lean_object* v___x_2675_; 
lean_inc(v_a_2656_);
v___x_2675_ = l_Lean_Meta_mkEqRefl(v_a_2656_, v___y_2651_, v___y_2652_, v___y_2654_, v___y_2650_);
if (lean_obj_tag(v___x_2675_) == 0)
{
lean_object* v_a_2676_; lean_object* v___x_2677_; 
v_a_2676_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2676_);
lean_dec_ref_known(v___x_2675_, 1);
lean_inc(v_mvarId_2470_);
v___x_2677_ = l_Lean_MVarId_getType(v_mvarId_2470_, v___y_2651_, v___y_2652_, v___y_2654_, v___y_2650_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v_nargs_2679_; lean_object* v___x_2680_; lean_object* v_dummy_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2677_, 1);
v_nargs_2679_ = l_Lean_Expr_getAppNumArgs(v_a_2656_);
v___x_2680_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2681_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_2679_);
v___x_2682_ = lean_mk_array(v_nargs_2679_, v_dummy_2681_);
v___x_2683_ = lean_unsigned_to_nat(1u);
v___x_2684_ = lean_nat_sub(v_nargs_2679_, v___x_2683_);
lean_dec(v_nargs_2679_);
v___x_2685_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2656_, v___x_2682_, v___x_2684_);
v___x_2686_ = lean_array_push(v___x_2685_, v_a_2676_);
v___x_2687_ = l_Lean_mkAppN(v___x_2680_, v___x_2686_);
lean_dec_ref(v___x_2686_);
lean_inc(v_val_2501_);
v___x_2688_ = l_Lean_LocalDecl_toExpr(v_val_2501_);
v___x_2689_ = l_Lean_Meta_mkAbsurd(v_a_2678_, v___x_2688_, v___x_2687_, v___y_2651_, v___y_2652_, v___y_2654_, v___y_2650_);
if (lean_obj_tag(v___x_2689_) == 0)
{
lean_object* v_a_2690_; lean_object* v___x_2691_; 
v_a_2690_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2690_);
lean_dec_ref_known(v___x_2689_, 1);
lean_inc(v_mvarId_2470_);
v___x_2691_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2470_, v_a_2690_, v___y_2652_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v___x_2693_; uint8_t v_isShared_2694_; uint8_t v_isSharedCheck_2700_; 
lean_dec_ref(v___x_2618_);
lean_dec(v_val_2501_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_isSharedCheck_2700_ = !lean_is_exclusive(v___x_2691_);
if (v_isSharedCheck_2700_ == 0)
{
lean_object* v_unused_2701_; 
v_unused_2701_ = lean_ctor_get(v___x_2691_, 0);
lean_dec(v_unused_2701_);
v___x_2693_ = v___x_2691_;
v_isShared_2694_ = v_isSharedCheck_2700_;
goto v_resetjp_2692_;
}
else
{
lean_dec(v___x_2691_);
v___x_2693_ = lean_box(0);
v_isShared_2694_ = v_isSharedCheck_2700_;
goto v_resetjp_2692_;
}
v_resetjp_2692_:
{
lean_object* v___x_2695_; lean_object* v___x_2697_; 
v___x_2695_ = lean_box(v___x_2480_);
if (v_isShared_2694_ == 0)
{
lean_ctor_set_tag(v___x_2693_, 1);
lean_ctor_set(v___x_2693_, 0, v___x_2695_);
v___x_2697_ = v___x_2693_;
goto v_reusejp_2696_;
}
else
{
lean_object* v_reuseFailAlloc_2699_; 
v_reuseFailAlloc_2699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2699_, 0, v___x_2695_);
v___x_2697_ = v_reuseFailAlloc_2699_;
goto v_reusejp_2696_;
}
v_reusejp_2696_:
{
lean_object* v___x_2698_; 
v___x_2698_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
lean_ctor_set(v___x_2698_, 1, v___x_2505_);
v_a_2487_ = v___x_2698_;
goto v___jp_2486_;
}
}
}
else
{
lean_object* v_a_2702_; 
v_a_2702_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2691_, 1);
v___y_2639_ = v___y_2649_;
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2652_;
v___y_2643_ = v___y_2654_;
v___y_2644_ = v___y_2653_;
v_a_2645_ = v_a_2702_;
goto v___jp_2638_;
}
}
else
{
lean_object* v_a_2703_; 
v_a_2703_ = lean_ctor_get(v___x_2689_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2689_, 1);
v___y_2639_ = v___y_2649_;
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2652_;
v___y_2643_ = v___y_2654_;
v___y_2644_ = v___y_2653_;
v_a_2645_ = v_a_2703_;
goto v___jp_2638_;
}
}
else
{
lean_object* v_a_2704_; 
lean_dec(v_a_2676_);
lean_dec(v_a_2656_);
v_a_2704_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2677_, 1);
v___y_2639_ = v___y_2649_;
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2652_;
v___y_2643_ = v___y_2654_;
v___y_2644_ = v___y_2653_;
v_a_2645_ = v_a_2704_;
goto v___jp_2638_;
}
}
else
{
lean_object* v_a_2705_; 
lean_dec(v_a_2656_);
v_a_2705_ = lean_ctor_get(v___x_2675_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2675_, 1);
v___y_2639_ = v___y_2649_;
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2652_;
v___y_2643_ = v___y_2654_;
v___y_2644_ = v___y_2653_;
v_a_2645_ = v_a_2705_;
goto v___jp_2638_;
}
}
}
else
{
lean_object* v_a_2706_; 
lean_dec(v_a_2656_);
v_a_2706_ = lean_ctor_get(v___x_2671_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2671_, 1);
v___y_2639_ = v___y_2649_;
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2652_;
v___y_2643_ = v___y_2654_;
v___y_2644_ = v___y_2653_;
v_a_2645_ = v_a_2706_;
goto v___jp_2638_;
}
}
else
{
lean_object* v_a_2707_; 
v_a_2707_ = lean_ctor_get(v___x_2655_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2655_, 1);
v___y_2639_ = v___y_2649_;
v___y_2640_ = v___y_2650_;
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2652_;
v___y_2643_ = v___y_2654_;
v___y_2644_ = v___y_2653_;
v_a_2645_ = v_a_2707_;
goto v___jp_2638_;
}
}
v___jp_2708_:
{
if (v___y_2715_ == 0)
{
v___y_2620_ = v___y_2709_;
v___y_2621_ = v___y_2713_;
v___y_2622_ = v___y_2711_;
v___y_2623_ = v___y_2712_;
v___y_2624_ = v___y_2714_;
v___y_2625_ = v___y_2710_;
goto v___jp_2619_;
}
else
{
v___y_2649_ = v___y_2709_;
v___y_2650_ = v___y_2710_;
v___y_2651_ = v___y_2711_;
v___y_2652_ = v___y_2712_;
v___y_2653_ = v___y_2713_;
v___y_2654_ = v___y_2714_;
goto v___jp_2648_;
}
}
v___jp_2716_:
{
if (v___y_2724_ == 0)
{
lean_dec_ref(v___y_2717_);
v___y_2709_ = v___y_2718_;
v___y_2710_ = v___y_2719_;
v___y_2711_ = v___y_2720_;
v___y_2712_ = v___y_2721_;
v___y_2713_ = v___y_2723_;
v___y_2714_ = v___y_2722_;
v___y_2715_ = v___x_2574_;
goto v___jp_2708_;
}
else
{
uint8_t v___x_2725_; 
v___x_2725_ = l_Lean_Expr_hasFVar(v___y_2717_);
lean_dec_ref(v___y_2717_);
if (v___x_2725_ == 0)
{
v___y_2649_ = v___y_2718_;
v___y_2650_ = v___y_2719_;
v___y_2651_ = v___y_2720_;
v___y_2652_ = v___y_2721_;
v___y_2653_ = v___y_2723_;
v___y_2654_ = v___y_2722_;
goto v___jp_2648_;
}
else
{
v___y_2709_ = v___y_2718_;
v___y_2710_ = v___y_2719_;
v___y_2711_ = v___y_2720_;
v___y_2712_ = v___y_2721_;
v___y_2713_ = v___y_2723_;
v___y_2714_ = v___y_2722_;
v___y_2715_ = v___x_2574_;
goto v___jp_2708_;
}
}
}
v___jp_2726_:
{
lean_object* v___x_2734_; 
lean_inc_ref(v___x_2618_);
v___x_2734_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2618_, v___y_2730_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; uint8_t v___x_2736_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v___x_2736_ = l_Lean_Expr_hasMVar(v_a_2735_);
if (v___x_2736_ == 0)
{
v___y_2717_ = v_a_2735_;
v___y_2718_ = v___y_2727_;
v___y_2719_ = v___y_2728_;
v___y_2720_ = v___y_2729_;
v___y_2721_ = v___y_2730_;
v___y_2722_ = v___y_2731_;
v___y_2723_ = v___y_2732_;
v___y_2724_ = v___y_2733_;
goto v___jp_2716_;
}
else
{
v___y_2717_ = v_a_2735_;
v___y_2718_ = v___y_2727_;
v___y_2719_ = v___y_2728_;
v___y_2720_ = v___y_2729_;
v___y_2721_ = v___y_2730_;
v___y_2722_ = v___y_2731_;
v___y_2723_ = v___y_2732_;
v___y_2724_ = v___x_2574_;
goto v___jp_2716_;
}
}
else
{
lean_object* v_a_2737_; lean_object* v___x_2739_; uint8_t v_isShared_2740_; uint8_t v_isSharedCheck_2744_; 
lean_dec_ref(v___x_2618_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_2737_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2744_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2739_ = v___x_2734_;
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
else
{
lean_inc(v_a_2737_);
lean_dec(v___x_2734_);
v___x_2739_ = lean_box(0);
v_isShared_2740_ = v_isSharedCheck_2744_;
goto v_resetjp_2738_;
}
v_resetjp_2738_:
{
lean_object* v___x_2742_; 
if (v_isShared_2740_ == 0)
{
v___x_2742_ = v___x_2739_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v_a_2737_);
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
v___jp_2745_:
{
if (v___y_2752_ == 0)
{
v___y_2620_ = v___y_2746_;
v___y_2621_ = v___y_2750_;
v___y_2622_ = v___y_2748_;
v___y_2623_ = v___y_2749_;
v___y_2624_ = v___y_2751_;
v___y_2625_ = v___y_2747_;
goto v___jp_2619_;
}
else
{
v___y_2727_ = v___y_2746_;
v___y_2728_ = v___y_2747_;
v___y_2729_ = v___y_2748_;
v___y_2730_ = v___y_2749_;
v___y_2731_ = v___y_2751_;
v___y_2732_ = v___y_2750_;
v___y_2733_ = v___y_2752_;
goto v___jp_2726_;
}
}
v___jp_2753_:
{
uint8_t v_useDecide_2760_; 
v_useDecide_2760_ = lean_ctor_get_uint8(v_config_2469_, sizeof(void*)*1);
if (v_useDecide_2760_ == 0)
{
v___y_2746_ = v_isHEq_2755_;
v___y_2747_ = v___y_2759_;
v___y_2748_ = v___y_2756_;
v___y_2749_ = v___y_2757_;
v___y_2750_ = v___y_2754_;
v___y_2751_ = v___y_2758_;
v___y_2752_ = v___x_2574_;
goto v___jp_2745_;
}
else
{
uint8_t v___x_2761_; 
v___x_2761_ = l_Lean_Expr_hasFVar(v___x_2618_);
if (v___x_2761_ == 0)
{
v___y_2727_ = v_isHEq_2755_;
v___y_2728_ = v___y_2759_;
v___y_2729_ = v___y_2756_;
v___y_2730_ = v___y_2757_;
v___y_2731_ = v___y_2758_;
v___y_2732_ = v___y_2754_;
v___y_2733_ = v_useDecide_2760_;
goto v___jp_2726_;
}
else
{
v___y_2746_ = v_isHEq_2755_;
v___y_2747_ = v___y_2759_;
v___y_2748_ = v___y_2756_;
v___y_2749_ = v___y_2757_;
v___y_2750_ = v___y_2754_;
v___y_2751_ = v___y_2758_;
v___y_2752_ = v___x_2574_;
goto v___jp_2745_;
}
}
}
v___jp_2762_:
{
lean_object* v___x_2770_; 
v___x_2770_ = l_Lean_Meta_isExprDefEq(v___y_2767_, v___y_2765_, v___y_2763_, v___y_2764_, v___y_2766_, v___y_2768_);
if (lean_obj_tag(v___x_2770_) == 0)
{
lean_object* v_a_2771_; uint8_t v___x_2772_; 
v_a_2771_ = lean_ctor_get(v___x_2770_, 0);
lean_inc(v_a_2771_);
lean_dec_ref_known(v___x_2770_, 1);
v___x_2772_ = lean_unbox(v_a_2771_);
lean_dec(v_a_2771_);
if (v___x_2772_ == 0)
{
v___y_2754_ = v___y_2769_;
v_isHEq_2755_ = v___x_2480_;
v___y_2756_ = v___y_2763_;
v___y_2757_ = v___y_2764_;
v___y_2758_ = v___y_2766_;
v___y_2759_ = v___y_2768_;
goto v___jp_2753_;
}
else
{
lean_object* v___x_2773_; 
lean_dec_ref(v___x_2618_);
lean_dec_ref(v_config_2469_);
lean_inc(v_mvarId_2470_);
v___x_2773_ = l_Lean_MVarId_getType(v_mvarId_2470_, v___y_2763_, v___y_2764_, v___y_2766_, v___y_2768_);
if (lean_obj_tag(v___x_2773_) == 0)
{
lean_object* v_a_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; 
v_a_2774_ = lean_ctor_get(v___x_2773_, 0);
lean_inc(v_a_2774_);
lean_dec_ref_known(v___x_2773_, 1);
v___x_2775_ = l_Lean_LocalDecl_toExpr(v_val_2501_);
v___x_2776_ = l_Lean_Meta_mkEqOfHEq(v___x_2775_, v___x_2480_, v___y_2763_, v___y_2764_, v___y_2766_, v___y_2768_);
if (lean_obj_tag(v___x_2776_) == 0)
{
lean_object* v_a_2777_; lean_object* v___x_2778_; 
v_a_2777_ = lean_ctor_get(v___x_2776_, 0);
lean_inc(v_a_2777_);
lean_dec_ref_known(v___x_2776_, 1);
v___x_2778_ = l_Lean_Meta_mkNoConfusion(v_a_2774_, v_a_2777_, v___y_2763_, v___y_2764_, v___y_2766_, v___y_2768_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2470_, v_a_2779_, v___y_2764_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
lean_dec_ref_known(v___x_2780_, 1);
v___x_2781_ = lean_box(v___x_2480_);
v___x_2782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2782_, 0, v___x_2781_);
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2505_);
v_a_2487_ = v___x_2783_;
goto v___jp_2486_;
}
else
{
lean_object* v_a_2784_; lean_object* v___x_2786_; uint8_t v_isShared_2787_; uint8_t v_isSharedCheck_2791_; 
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
v_a_2784_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2791_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2791_ == 0)
{
v___x_2786_ = v___x_2780_;
v_isShared_2787_ = v_isSharedCheck_2791_;
goto v_resetjp_2785_;
}
else
{
lean_inc(v_a_2784_);
lean_dec(v___x_2780_);
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
lean_object* v_a_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2799_; 
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_2792_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2794_ = v___x_2778_;
v_isShared_2795_ = v_isSharedCheck_2799_;
goto v_resetjp_2793_;
}
else
{
lean_inc(v_a_2792_);
lean_dec(v___x_2778_);
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
else
{
lean_object* v_a_2800_; lean_object* v___x_2802_; uint8_t v_isShared_2803_; uint8_t v_isSharedCheck_2807_; 
lean_dec(v_a_2774_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_2800_ = lean_ctor_get(v___x_2776_, 0);
v_isSharedCheck_2807_ = !lean_is_exclusive(v___x_2776_);
if (v_isSharedCheck_2807_ == 0)
{
v___x_2802_ = v___x_2776_;
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
else
{
lean_inc(v_a_2800_);
lean_dec(v___x_2776_);
v___x_2802_ = lean_box(0);
v_isShared_2803_ = v_isSharedCheck_2807_;
goto v_resetjp_2801_;
}
v_resetjp_2801_:
{
lean_object* v___x_2805_; 
if (v_isShared_2803_ == 0)
{
v___x_2805_ = v___x_2802_;
goto v_reusejp_2804_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2800_);
v___x_2805_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2804_;
}
v_reusejp_2804_:
{
return v___x_2805_;
}
}
}
}
else
{
lean_object* v_a_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2815_; 
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_2808_ = lean_ctor_get(v___x_2773_, 0);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2773_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2810_ = v___x_2773_;
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
else
{
lean_inc(v_a_2808_);
lean_dec(v___x_2773_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2815_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2813_; 
if (v_isShared_2811_ == 0)
{
v___x_2813_ = v___x_2810_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v_a_2808_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
}
}
else
{
lean_object* v_a_2816_; lean_object* v___x_2818_; uint8_t v_isShared_2819_; uint8_t v_isSharedCheck_2823_; 
lean_dec_ref(v___x_2618_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_2816_ = lean_ctor_get(v___x_2770_, 0);
v_isSharedCheck_2823_ = !lean_is_exclusive(v___x_2770_);
if (v_isSharedCheck_2823_ == 0)
{
v___x_2818_ = v___x_2770_;
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
else
{
lean_inc(v_a_2816_);
lean_dec(v___x_2770_);
v___x_2818_ = lean_box(0);
v_isShared_2819_ = v_isSharedCheck_2823_;
goto v_resetjp_2817_;
}
v_resetjp_2817_:
{
lean_object* v___x_2821_; 
if (v_isShared_2819_ == 0)
{
v___x_2821_ = v___x_2818_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
v___jp_2824_:
{
lean_object* v___x_2830_; 
lean_inc_ref(v___x_2618_);
v___x_2830_ = l_Lean_Meta_matchHEq_x3f(v___x_2618_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2830_) == 0)
{
lean_object* v_a_2831_; 
v_a_2831_ = lean_ctor_get(v___x_2830_, 0);
lean_inc(v_a_2831_);
lean_dec_ref_known(v___x_2830_, 1);
if (lean_obj_tag(v_a_2831_) == 1)
{
lean_object* v_val_2832_; lean_object* v_snd_2833_; lean_object* v_snd_2834_; lean_object* v_fst_2835_; lean_object* v_fst_2836_; lean_object* v_fst_2837_; lean_object* v_snd_2838_; lean_object* v___x_2839_; 
v_val_2832_ = lean_ctor_get(v_a_2831_, 0);
lean_inc(v_val_2832_);
lean_dec_ref_known(v_a_2831_, 1);
v_snd_2833_ = lean_ctor_get(v_val_2832_, 1);
lean_inc(v_snd_2833_);
v_snd_2834_ = lean_ctor_get(v_snd_2833_, 1);
lean_inc(v_snd_2834_);
v_fst_2835_ = lean_ctor_get(v_val_2832_, 0);
lean_inc(v_fst_2835_);
lean_dec(v_val_2832_);
v_fst_2836_ = lean_ctor_get(v_snd_2833_, 0);
lean_inc(v_fst_2836_);
lean_dec(v_snd_2833_);
v_fst_2837_ = lean_ctor_get(v_snd_2834_, 0);
lean_inc(v_fst_2837_);
v_snd_2838_ = lean_ctor_get(v_snd_2834_, 1);
lean_inc(v_snd_2838_);
lean_dec(v_snd_2834_);
v___x_2839_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2836_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
lean_dec_ref_known(v___x_2839_, 1);
if (lean_obj_tag(v_a_2840_) == 1)
{
lean_object* v_val_2841_; lean_object* v___x_2842_; 
v_val_2841_ = lean_ctor_get(v_a_2840_, 0);
lean_inc(v_val_2841_);
lean_dec_ref_known(v_a_2840_, 1);
v___x_2842_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2838_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2842_) == 0)
{
lean_object* v_a_2843_; 
v_a_2843_ = lean_ctor_get(v___x_2842_, 0);
lean_inc(v_a_2843_);
lean_dec_ref_known(v___x_2842_, 1);
if (lean_obj_tag(v_a_2843_) == 1)
{
lean_object* v_toConstantVal_2844_; lean_object* v_val_2845_; lean_object* v_toConstantVal_2846_; lean_object* v_name_2847_; lean_object* v_name_2848_; uint8_t v___x_2849_; 
v_toConstantVal_2844_ = lean_ctor_get(v_val_2841_, 0);
lean_inc_ref(v_toConstantVal_2844_);
lean_dec(v_val_2841_);
v_val_2845_ = lean_ctor_get(v_a_2843_, 0);
lean_inc(v_val_2845_);
lean_dec_ref_known(v_a_2843_, 1);
v_toConstantVal_2846_ = lean_ctor_get(v_val_2845_, 0);
lean_inc_ref(v_toConstantVal_2846_);
lean_dec(v_val_2845_);
v_name_2847_ = lean_ctor_get(v_toConstantVal_2844_, 0);
lean_inc(v_name_2847_);
lean_dec_ref(v_toConstantVal_2844_);
v_name_2848_ = lean_ctor_get(v_toConstantVal_2846_, 0);
lean_inc(v_name_2848_);
lean_dec_ref(v_toConstantVal_2846_);
v___x_2849_ = lean_name_eq(v_name_2847_, v_name_2848_);
lean_dec(v_name_2848_);
lean_dec(v_name_2847_);
if (v___x_2849_ == 0)
{
v___y_2763_ = v___y_2826_;
v___y_2764_ = v___y_2827_;
v___y_2765_ = v_fst_2837_;
v___y_2766_ = v___y_2828_;
v___y_2767_ = v_fst_2835_;
v___y_2768_ = v___y_2829_;
v___y_2769_ = v_isEq_2825_;
goto v___jp_2762_;
}
else
{
if (v___x_2574_ == 0)
{
lean_dec(v_fst_2837_);
lean_dec(v_fst_2835_);
v___y_2754_ = v_isEq_2825_;
v_isHEq_2755_ = v___x_2480_;
v___y_2756_ = v___y_2826_;
v___y_2757_ = v___y_2827_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
goto v___jp_2753_;
}
else
{
v___y_2763_ = v___y_2826_;
v___y_2764_ = v___y_2827_;
v___y_2765_ = v_fst_2837_;
v___y_2766_ = v___y_2828_;
v___y_2767_ = v_fst_2835_;
v___y_2768_ = v___y_2829_;
v___y_2769_ = v_isEq_2825_;
goto v___jp_2762_;
}
}
}
else
{
lean_dec(v_a_2843_);
lean_dec(v_val_2841_);
lean_dec(v_fst_2837_);
lean_dec(v_fst_2835_);
v___y_2754_ = v_isEq_2825_;
v_isHEq_2755_ = v___x_2480_;
v___y_2756_ = v___y_2826_;
v___y_2757_ = v___y_2827_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
goto v___jp_2753_;
}
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec(v_val_2841_);
lean_dec(v_fst_2837_);
lean_dec(v_fst_2835_);
lean_dec_ref(v___x_2618_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_2850_ = lean_ctor_get(v___x_2842_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2842_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2842_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2842_);
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
lean_dec(v_a_2840_);
lean_dec(v_snd_2838_);
lean_dec(v_fst_2837_);
lean_dec(v_fst_2835_);
v___y_2754_ = v_isEq_2825_;
v_isHEq_2755_ = v___x_2480_;
v___y_2756_ = v___y_2826_;
v___y_2757_ = v___y_2827_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
goto v___jp_2753_;
}
}
else
{
lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v_snd_2838_);
lean_dec(v_fst_2837_);
lean_dec(v_fst_2835_);
lean_dec_ref(v___x_2618_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_2858_ = lean_ctor_get(v___x_2839_, 0);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2839_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_dec(v___x_2839_);
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
lean_dec(v_a_2831_);
v___y_2754_ = v_isEq_2825_;
v_isHEq_2755_ = v___x_2574_;
v___y_2756_ = v___y_2826_;
v___y_2757_ = v___y_2827_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
goto v___jp_2753_;
}
}
else
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2873_; 
lean_dec_ref(v___x_2618_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_2866_ = lean_ctor_get(v___x_2830_, 0);
v_isSharedCheck_2873_ = !lean_is_exclusive(v___x_2830_);
if (v_isSharedCheck_2873_ == 0)
{
v___x_2868_ = v___x_2830_;
v_isShared_2869_ = v_isSharedCheck_2873_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2830_);
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
lean_object* v___x_2879_; 
lean_inc_ref(v___x_2618_);
v___x_2879_ = l_Lean_Meta_matchEq_x3f(v___x_2618_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2879_) == 0)
{
lean_object* v_a_2880_; 
v_a_2880_ = lean_ctor_get(v___x_2879_, 0);
lean_inc(v_a_2880_);
lean_dec_ref_known(v___x_2879_, 1);
if (lean_obj_tag(v_a_2880_) == 1)
{
lean_object* v_val_2881_; lean_object* v_snd_2882_; lean_object* v_fst_2883_; lean_object* v_snd_2884_; lean_object* v___x_2885_; 
v_val_2881_ = lean_ctor_get(v_a_2880_, 0);
lean_inc(v_val_2881_);
lean_dec_ref_known(v_a_2880_, 1);
v_snd_2882_ = lean_ctor_get(v_val_2881_, 1);
lean_inc(v_snd_2882_);
lean_dec(v_val_2881_);
v_fst_2883_ = lean_ctor_get(v_snd_2882_, 0);
lean_inc(v_fst_2883_);
v_snd_2884_ = lean_ctor_get(v_snd_2882_, 1);
lean_inc(v_snd_2884_);
lean_dec(v_snd_2882_);
v___x_2885_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2883_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
if (lean_obj_tag(v_a_2886_) == 1)
{
lean_object* v_val_2887_; lean_object* v___x_2888_; 
v_val_2887_ = lean_ctor_get(v_a_2886_, 0);
lean_inc(v_val_2887_);
lean_dec_ref_known(v_a_2886_, 1);
v___x_2888_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2884_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2878_);
if (lean_obj_tag(v___x_2888_) == 0)
{
lean_object* v_a_2889_; 
v_a_2889_ = lean_ctor_get(v___x_2888_, 0);
lean_inc(v_a_2889_);
lean_dec_ref_known(v___x_2888_, 1);
if (lean_obj_tag(v_a_2889_) == 1)
{
lean_object* v_toConstantVal_2890_; lean_object* v_val_2891_; lean_object* v_toConstantVal_2892_; lean_object* v_name_2893_; lean_object* v_name_2894_; uint8_t v___x_2895_; 
v_toConstantVal_2890_ = lean_ctor_get(v_val_2887_, 0);
lean_inc_ref(v_toConstantVal_2890_);
lean_dec(v_val_2887_);
v_val_2891_ = lean_ctor_get(v_a_2889_, 0);
lean_inc(v_val_2891_);
lean_dec_ref_known(v_a_2889_, 1);
v_toConstantVal_2892_ = lean_ctor_get(v_val_2891_, 0);
lean_inc_ref(v_toConstantVal_2892_);
lean_dec(v_val_2891_);
v_name_2893_ = lean_ctor_get(v_toConstantVal_2890_, 0);
lean_inc(v_name_2893_);
lean_dec_ref(v_toConstantVal_2890_);
v_name_2894_ = lean_ctor_get(v_toConstantVal_2892_, 0);
lean_inc(v_name_2894_);
lean_dec_ref(v_toConstantVal_2892_);
v___x_2895_ = lean_name_eq(v_name_2893_, v_name_2894_);
lean_dec(v_name_2894_);
lean_dec(v_name_2893_);
if (v___x_2895_ == 0)
{
lean_dec_ref(v___x_2618_);
lean_dec_ref(v_config_2469_);
v___y_2507_ = v___y_2875_;
v___y_2508_ = v___y_2876_;
v___y_2509_ = v___y_2878_;
v___y_2510_ = v___y_2877_;
goto v___jp_2506_;
}
else
{
if (v___x_2574_ == 0)
{
lean_del_object(v___x_2503_);
v_isEq_2825_ = v___x_2480_;
v___y_2826_ = v___y_2875_;
v___y_2827_ = v___y_2876_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
goto v___jp_2824_;
}
else
{
lean_dec_ref(v___x_2618_);
lean_dec_ref(v_config_2469_);
v___y_2507_ = v___y_2875_;
v___y_2508_ = v___y_2876_;
v___y_2509_ = v___y_2878_;
v___y_2510_ = v___y_2877_;
goto v___jp_2506_;
}
}
}
else
{
lean_dec(v_a_2889_);
lean_dec(v_val_2887_);
lean_del_object(v___x_2503_);
v_isEq_2825_ = v___x_2480_;
v___y_2826_ = v___y_2875_;
v___y_2827_ = v___y_2876_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
goto v___jp_2824_;
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec(v_val_2887_);
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_2896_ = lean_ctor_get(v___x_2888_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2888_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2888_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2888_);
v___x_2898_ = lean_box(0);
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
v_resetjp_2897_:
{
lean_object* v___x_2901_; 
if (v_isShared_2899_ == 0)
{
v___x_2901_ = v___x_2898_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v_a_2896_);
v___x_2901_ = v_reuseFailAlloc_2902_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
return v___x_2901_;
}
}
}
}
else
{
lean_dec(v_a_2886_);
lean_dec(v_snd_2884_);
lean_del_object(v___x_2503_);
v_isEq_2825_ = v___x_2480_;
v___y_2826_ = v___y_2875_;
v___y_2827_ = v___y_2876_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
goto v___jp_2824_;
}
}
else
{
lean_object* v_a_2904_; lean_object* v___x_2906_; uint8_t v_isShared_2907_; uint8_t v_isSharedCheck_2911_; 
lean_dec(v_snd_2884_);
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_2904_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2911_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2911_ == 0)
{
v___x_2906_ = v___x_2885_;
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
else
{
lean_inc(v_a_2904_);
lean_dec(v___x_2885_);
v___x_2906_ = lean_box(0);
v_isShared_2907_ = v_isSharedCheck_2911_;
goto v_resetjp_2905_;
}
v_resetjp_2905_:
{
lean_object* v___x_2909_; 
if (v_isShared_2907_ == 0)
{
v___x_2909_ = v___x_2906_;
goto v_reusejp_2908_;
}
else
{
lean_object* v_reuseFailAlloc_2910_; 
v_reuseFailAlloc_2910_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2910_, 0, v_a_2904_);
v___x_2909_ = v_reuseFailAlloc_2910_;
goto v_reusejp_2908_;
}
v_reusejp_2908_:
{
return v___x_2909_;
}
}
}
}
else
{
lean_dec(v_a_2880_);
lean_del_object(v___x_2503_);
v_isEq_2825_ = v___x_2574_;
v___y_2826_ = v___y_2875_;
v___y_2827_ = v___y_2876_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
goto v___jp_2824_;
}
}
else
{
lean_object* v_a_2912_; lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_2912_ = lean_ctor_get(v___x_2879_, 0);
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2879_);
if (v_isSharedCheck_2919_ == 0)
{
v___x_2914_ = v___x_2879_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_inc(v_a_2912_);
lean_dec(v___x_2879_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_a_2912_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
}
v___jp_2920_:
{
lean_object* v___x_2925_; 
lean_inc_ref(v___x_2618_);
v___x_2925_ = l_Lean_refutableHasNotBit_x3f(v___x_2618_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
if (lean_obj_tag(v_a_2926_) == 1)
{
lean_object* v_val_2927_; lean_object* v___x_2929_; uint8_t v_isShared_2930_; uint8_t v_isSharedCheck_2966_; 
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec_ref(v_config_2469_);
v_val_2927_ = lean_ctor_get(v_a_2926_, 0);
v_isSharedCheck_2966_ = !lean_is_exclusive(v_a_2926_);
if (v_isSharedCheck_2966_ == 0)
{
v___x_2929_ = v_a_2926_;
v_isShared_2930_ = v_isSharedCheck_2966_;
goto v_resetjp_2928_;
}
else
{
lean_inc(v_val_2927_);
lean_dec(v_a_2926_);
v___x_2929_ = lean_box(0);
v_isShared_2930_ = v_isSharedCheck_2966_;
goto v_resetjp_2928_;
}
v_resetjp_2928_:
{
lean_object* v___x_2931_; 
lean_inc(v_mvarId_2470_);
v___x_2931_ = l_Lean_MVarId_getType(v_mvarId_2470_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2931_) == 0)
{
lean_object* v_a_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; 
v_a_2932_ = lean_ctor_get(v___x_2931_, 0);
lean_inc(v_a_2932_);
lean_dec_ref_known(v___x_2931_, 1);
v___x_2933_ = l_Lean_LocalDecl_toExpr(v_val_2501_);
v___x_2934_ = l_Lean_Meta_mkAbsurd(v_a_2932_, v_val_2927_, v___x_2933_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v___x_2936_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
lean_inc(v_a_2935_);
lean_dec_ref_known(v___x_2934_, 1);
v___x_2936_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2470_, v_a_2935_, v___y_2922_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v___x_2937_; lean_object* v___x_2939_; 
lean_dec_ref_known(v___x_2936_, 1);
v___x_2937_ = lean_box(v___x_2480_);
if (v_isShared_2930_ == 0)
{
lean_ctor_set(v___x_2929_, 0, v___x_2937_);
v___x_2939_ = v___x_2929_;
goto v_reusejp_2938_;
}
else
{
lean_object* v_reuseFailAlloc_2941_; 
v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2941_, 0, v___x_2937_);
v___x_2939_ = v_reuseFailAlloc_2941_;
goto v_reusejp_2938_;
}
v_reusejp_2938_:
{
lean_object* v___x_2940_; 
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
lean_ctor_set(v___x_2940_, 1, v___x_2505_);
v_a_2487_ = v___x_2940_;
goto v___jp_2486_;
}
}
else
{
lean_object* v_a_2942_; lean_object* v___x_2944_; uint8_t v_isShared_2945_; uint8_t v_isSharedCheck_2949_; 
lean_del_object(v___x_2929_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
v_a_2942_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2949_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2949_ == 0)
{
v___x_2944_ = v___x_2936_;
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
else
{
lean_inc(v_a_2942_);
lean_dec(v___x_2936_);
v___x_2944_ = lean_box(0);
v_isShared_2945_ = v_isSharedCheck_2949_;
goto v_resetjp_2943_;
}
v_resetjp_2943_:
{
lean_object* v___x_2947_; 
if (v_isShared_2945_ == 0)
{
v___x_2947_ = v___x_2944_;
goto v_reusejp_2946_;
}
else
{
lean_object* v_reuseFailAlloc_2948_; 
v_reuseFailAlloc_2948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2948_, 0, v_a_2942_);
v___x_2947_ = v_reuseFailAlloc_2948_;
goto v_reusejp_2946_;
}
v_reusejp_2946_:
{
return v___x_2947_;
}
}
}
}
else
{
lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_del_object(v___x_2929_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_2950_ = lean_ctor_get(v___x_2934_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2934_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2934_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
else
{
lean_object* v_a_2958_; lean_object* v___x_2960_; uint8_t v_isShared_2961_; uint8_t v_isSharedCheck_2965_; 
lean_del_object(v___x_2929_);
lean_dec(v_val_2927_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_2958_ = lean_ctor_get(v___x_2931_, 0);
v_isSharedCheck_2965_ = !lean_is_exclusive(v___x_2931_);
if (v_isSharedCheck_2965_ == 0)
{
v___x_2960_ = v___x_2931_;
v_isShared_2961_ = v_isSharedCheck_2965_;
goto v_resetjp_2959_;
}
else
{
lean_inc(v_a_2958_);
lean_dec(v___x_2931_);
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
}
else
{
lean_object* v___x_2967_; 
lean_dec(v_a_2926_);
lean_inc_ref(v___x_2618_);
v___x_2967_ = l_Lean_Meta_matchNe_x3f(v___x_2618_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2967_) == 0)
{
lean_object* v_a_2968_; 
v_a_2968_ = lean_ctor_get(v___x_2967_, 0);
lean_inc(v_a_2968_);
lean_dec_ref_known(v___x_2967_, 1);
if (lean_obj_tag(v_a_2968_) == 1)
{
lean_object* v_val_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_3038_; 
v_val_2969_ = lean_ctor_get(v_a_2968_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v_a_2968_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_2971_ = v_a_2968_;
v_isShared_2972_ = v_isSharedCheck_3038_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_val_2969_);
lean_dec(v_a_2968_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_3038_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v_snd_2973_; lean_object* v_fst_2974_; lean_object* v_snd_2975_; lean_object* v___x_2977_; uint8_t v_isShared_2978_; uint8_t v_isSharedCheck_3037_; 
v_snd_2973_ = lean_ctor_get(v_val_2969_, 1);
lean_inc(v_snd_2973_);
lean_dec(v_val_2969_);
v_fst_2974_ = lean_ctor_get(v_snd_2973_, 0);
v_snd_2975_ = lean_ctor_get(v_snd_2973_, 1);
v_isSharedCheck_3037_ = !lean_is_exclusive(v_snd_2973_);
if (v_isSharedCheck_3037_ == 0)
{
v___x_2977_ = v_snd_2973_;
v_isShared_2978_ = v_isSharedCheck_3037_;
goto v_resetjp_2976_;
}
else
{
lean_inc(v_snd_2975_);
lean_inc(v_fst_2974_);
lean_dec(v_snd_2973_);
v___x_2977_ = lean_box(0);
v_isShared_2978_ = v_isSharedCheck_3037_;
goto v_resetjp_2976_;
}
v_resetjp_2976_:
{
lean_object* v___x_2979_; 
lean_inc(v_fst_2974_);
v___x_2979_ = l_Lean_Meta_isExprDefEq(v_fst_2974_, v_snd_2975_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; uint8_t v___x_2981_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = lean_unbox(v_a_2980_);
lean_dec(v_a_2980_);
if (v___x_2981_ == 0)
{
lean_del_object(v___x_2977_);
lean_dec(v_fst_2974_);
lean_del_object(v___x_2971_);
v___y_2875_ = v___y_2921_;
v___y_2876_ = v___y_2922_;
v___y_2877_ = v___y_2923_;
v___y_2878_ = v___y_2924_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2982_; 
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec_ref(v_config_2469_);
lean_inc(v_mvarId_2470_);
v___x_2982_ = l_Lean_MVarId_getType(v_mvarId_2470_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2982_) == 0)
{
lean_object* v_a_2983_; lean_object* v___x_2984_; 
v_a_2983_ = lean_ctor_get(v___x_2982_, 0);
lean_inc(v_a_2983_);
lean_dec_ref_known(v___x_2982_, 1);
v___x_2984_ = l_Lean_Meta_mkEqRefl(v_fst_2974_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2986_; lean_object* v___x_2987_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v___x_2984_, 1);
v___x_2986_ = l_Lean_LocalDecl_toExpr(v_val_2501_);
v___x_2987_ = l_Lean_Meta_mkAbsurd(v_a_2983_, v_a_2985_, v___x_2986_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
if (lean_obj_tag(v___x_2987_) == 0)
{
lean_object* v_a_2988_; lean_object* v___x_2989_; 
v_a_2988_ = lean_ctor_get(v___x_2987_, 0);
lean_inc(v_a_2988_);
lean_dec_ref_known(v___x_2987_, 1);
v___x_2989_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2470_, v_a_2988_, v___y_2922_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v___x_2990_; lean_object* v___x_2992_; 
lean_dec_ref_known(v___x_2989_, 1);
v___x_2990_ = lean_box(v___x_2480_);
if (v_isShared_2972_ == 0)
{
lean_ctor_set(v___x_2971_, 0, v___x_2990_);
v___x_2992_ = v___x_2971_;
goto v_reusejp_2991_;
}
else
{
lean_object* v_reuseFailAlloc_2996_; 
v_reuseFailAlloc_2996_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2996_, 0, v___x_2990_);
v___x_2992_ = v_reuseFailAlloc_2996_;
goto v_reusejp_2991_;
}
v_reusejp_2991_:
{
lean_object* v___x_2994_; 
if (v_isShared_2978_ == 0)
{
lean_ctor_set(v___x_2977_, 1, v___x_2505_);
lean_ctor_set(v___x_2977_, 0, v___x_2992_);
v___x_2994_ = v___x_2977_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2995_; 
v_reuseFailAlloc_2995_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2995_, 0, v___x_2992_);
lean_ctor_set(v_reuseFailAlloc_2995_, 1, v___x_2505_);
v___x_2994_ = v_reuseFailAlloc_2995_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
v_a_2487_ = v___x_2994_;
goto v___jp_2486_;
}
}
}
else
{
lean_object* v_a_2997_; lean_object* v___x_2999_; uint8_t v_isShared_3000_; uint8_t v_isSharedCheck_3004_; 
lean_del_object(v___x_2977_);
lean_del_object(v___x_2971_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
v_a_2997_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3004_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3004_ == 0)
{
v___x_2999_ = v___x_2989_;
v_isShared_3000_ = v_isSharedCheck_3004_;
goto v_resetjp_2998_;
}
else
{
lean_inc(v_a_2997_);
lean_dec(v___x_2989_);
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
}
else
{
lean_object* v_a_3005_; lean_object* v___x_3007_; uint8_t v_isShared_3008_; uint8_t v_isSharedCheck_3012_; 
lean_del_object(v___x_2977_);
lean_del_object(v___x_2971_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_3005_ = lean_ctor_get(v___x_2987_, 0);
v_isSharedCheck_3012_ = !lean_is_exclusive(v___x_2987_);
if (v_isSharedCheck_3012_ == 0)
{
v___x_3007_ = v___x_2987_;
v_isShared_3008_ = v_isSharedCheck_3012_;
goto v_resetjp_3006_;
}
else
{
lean_inc(v_a_3005_);
lean_dec(v___x_2987_);
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
lean_object* v_a_3013_; lean_object* v___x_3015_; uint8_t v_isShared_3016_; uint8_t v_isSharedCheck_3020_; 
lean_dec(v_a_2983_);
lean_del_object(v___x_2977_);
lean_del_object(v___x_2971_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_3013_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3020_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3020_ == 0)
{
v___x_3015_ = v___x_2984_;
v_isShared_3016_ = v_isSharedCheck_3020_;
goto v_resetjp_3014_;
}
else
{
lean_inc(v_a_3013_);
lean_dec(v___x_2984_);
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
lean_object* v_a_3021_; lean_object* v___x_3023_; uint8_t v_isShared_3024_; uint8_t v_isSharedCheck_3028_; 
lean_del_object(v___x_2977_);
lean_dec(v_fst_2974_);
lean_del_object(v___x_2971_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_3021_ = lean_ctor_get(v___x_2982_, 0);
v_isSharedCheck_3028_ = !lean_is_exclusive(v___x_2982_);
if (v_isSharedCheck_3028_ == 0)
{
v___x_3023_ = v___x_2982_;
v_isShared_3024_ = v_isSharedCheck_3028_;
goto v_resetjp_3022_;
}
else
{
lean_inc(v_a_3021_);
lean_dec(v___x_2982_);
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
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_del_object(v___x_2977_);
lean_dec(v_fst_2974_);
lean_del_object(v___x_2971_);
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_3029_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_2979_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_2979_);
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
}
else
{
lean_dec(v_a_2968_);
v___y_2875_ = v___y_2921_;
v___y_2876_ = v___y_2922_;
v___y_2877_ = v___y_2923_;
v___y_2878_ = v___y_2924_;
goto v___jp_2874_;
}
}
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_3039_ = lean_ctor_get(v___x_2967_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_2967_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_2967_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_2967_);
v___x_3041_ = lean_box(0);
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
v_resetjp_3040_:
{
lean_object* v___x_3044_; 
if (v_isShared_3042_ == 0)
{
v___x_3044_ = v___x_3041_;
goto v_reusejp_3043_;
}
else
{
lean_object* v_reuseFailAlloc_3045_; 
v_reuseFailAlloc_3045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3045_, 0, v_a_3039_);
v___x_3044_ = v_reuseFailAlloc_3045_;
goto v_reusejp_3043_;
}
v_reusejp_3043_:
{
return v___x_3044_;
}
}
}
}
}
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec_ref(v___x_2618_);
lean_del_object(v___x_2503_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_3047_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_2925_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_2925_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
if (v_isShared_3050_ == 0)
{
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3053_; 
v_reuseFailAlloc_3053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3053_, 0, v_a_3047_);
v___x_3052_ = v_reuseFailAlloc_3053_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
return v___x_3052_;
}
}
}
}
}
else
{
lean_del_object(v___x_2503_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
v_a_2495_ = v___x_2546_;
goto v___jp_2494_;
}
v___jp_2506_:
{
lean_object* v___x_2511_; 
lean_inc(v_mvarId_2470_);
v___x_2511_ = l_Lean_MVarId_getType(v_mvarId_2470_, v___y_2507_, v___y_2508_, v___y_2510_, v___y_2509_);
if (lean_obj_tag(v___x_2511_) == 0)
{
lean_object* v_a_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v_a_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_a_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v___x_2513_ = l_Lean_LocalDecl_toExpr(v_val_2501_);
v___x_2514_ = l_Lean_Meta_mkNoConfusion(v_a_2512_, v___x_2513_, v___y_2507_, v___y_2508_, v___y_2510_, v___y_2509_);
if (lean_obj_tag(v___x_2514_) == 0)
{
lean_object* v_a_2515_; lean_object* v___x_2516_; 
v_a_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc(v_a_2515_);
lean_dec_ref_known(v___x_2514_, 1);
v___x_2516_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2470_, v_a_2515_, v___y_2508_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
lean_dec_ref_known(v___x_2516_, 1);
v___x_2517_ = lean_box(v___x_2480_);
if (v_isShared_2504_ == 0)
{
lean_ctor_set(v___x_2503_, 0, v___x_2517_);
v___x_2519_ = v___x_2503_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
lean_object* v___x_2520_; 
v___x_2520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2520_, 0, v___x_2519_);
lean_ctor_set(v___x_2520_, 1, v___x_2505_);
v_a_2487_ = v___x_2520_;
goto v___jp_2486_;
}
}
else
{
lean_object* v_a_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_2529_; 
lean_del_object(v___x_2503_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
v_a_2522_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2529_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2529_ == 0)
{
v___x_2524_ = v___x_2516_;
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_a_2522_);
lean_dec(v___x_2516_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_2529_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2527_; 
if (v_isShared_2525_ == 0)
{
v___x_2527_ = v___x_2524_;
goto v_reusejp_2526_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_a_2522_);
v___x_2527_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2526_;
}
v_reusejp_2526_:
{
return v___x_2527_;
}
}
}
}
else
{
lean_object* v_a_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2537_; 
lean_del_object(v___x_2503_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_2530_ = lean_ctor_get(v___x_2514_, 0);
v_isSharedCheck_2537_ = !lean_is_exclusive(v___x_2514_);
if (v_isSharedCheck_2537_ == 0)
{
v___x_2532_ = v___x_2514_;
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_a_2530_);
lean_dec(v___x_2514_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2537_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2535_; 
if (v_isShared_2533_ == 0)
{
v___x_2535_ = v___x_2532_;
goto v_reusejp_2534_;
}
else
{
lean_object* v_reuseFailAlloc_2536_; 
v_reuseFailAlloc_2536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2536_, 0, v_a_2530_);
v___x_2535_ = v_reuseFailAlloc_2536_;
goto v_reusejp_2534_;
}
v_reusejp_2534_:
{
return v___x_2535_;
}
}
}
}
else
{
lean_object* v_a_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2545_; 
lean_del_object(v___x_2503_);
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
v_a_2538_ = lean_ctor_get(v___x_2511_, 0);
v_isSharedCheck_2545_ = !lean_is_exclusive(v___x_2511_);
if (v_isSharedCheck_2545_ == 0)
{
v___x_2540_ = v___x_2511_;
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_a_2538_);
lean_dec(v___x_2511_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2545_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2543_; 
if (v_isShared_2541_ == 0)
{
v___x_2543_ = v___x_2540_;
goto v_reusejp_2542_;
}
else
{
lean_object* v_reuseFailAlloc_2544_; 
v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2538_);
v___x_2543_ = v_reuseFailAlloc_2544_;
goto v_reusejp_2542_;
}
v_reusejp_2542_:
{
return v___x_2543_;
}
}
}
}
v___jp_2547_:
{
lean_object* v_searchFuel_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; 
v_searchFuel_2552_ = lean_ctor_get(v_config_2469_, 0);
v___x_2553_ = l_Lean_LocalDecl_fvarId(v_val_2501_);
lean_dec(v_val_2501_);
lean_inc(v_searchFuel_2552_);
lean_inc(v_mvarId_2470_);
v___x_2554_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2470_, v___x_2553_, v_searchFuel_2552_, v___y_2551_, v___y_2549_, v___y_2550_, v___y_2548_);
if (lean_obj_tag(v___x_2554_) == 0)
{
lean_object* v_a_2555_; uint8_t v___x_2556_; 
v_a_2555_ = lean_ctor_get(v___x_2554_, 0);
lean_inc(v_a_2555_);
lean_dec_ref_known(v___x_2554_, 1);
v___x_2556_ = lean_unbox(v_a_2555_);
lean_dec(v_a_2555_);
if (v___x_2556_ == 0)
{
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
v_a_2495_ = v___x_2546_;
goto v___jp_2494_;
}
else
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v___x_2557_ = lean_box(v___x_2480_);
v___x_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2558_, 0, v___x_2557_);
v___x_2559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2559_, 0, v___x_2558_);
lean_ctor_set(v___x_2559_, 1, v___x_2505_);
v_a_2487_ = v___x_2559_;
goto v___jp_2486_;
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_2560_ = lean_ctor_get(v___x_2554_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2554_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2554_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2554_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
v___jp_2568_:
{
if (v___y_2573_ == 0)
{
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
v_a_2495_ = v___x_2546_;
goto v___jp_2494_;
}
else
{
v___y_2548_ = v___y_2569_;
v___y_2549_ = v___y_2570_;
v___y_2550_ = v___y_2572_;
v___y_2551_ = v___y_2571_;
goto v___jp_2547_;
}
}
v___jp_2575_:
{
if (v___y_2577_ == 0)
{
v___y_2548_ = v___y_2576_;
v___y_2549_ = v___y_2578_;
v___y_2550_ = v___y_2580_;
v___y_2551_ = v___y_2579_;
goto v___jp_2547_;
}
else
{
v___y_2569_ = v___y_2576_;
v___y_2570_ = v___y_2578_;
v___y_2571_ = v___y_2579_;
v___y_2572_ = v___y_2580_;
v___y_2573_ = v___x_2574_;
goto v___jp_2568_;
}
}
v___jp_2581_:
{
if (v___y_2587_ == 0)
{
v___y_2569_ = v___y_2582_;
v___y_2570_ = v___y_2584_;
v___y_2571_ = v___y_2586_;
v___y_2572_ = v___y_2585_;
v___y_2573_ = v___x_2574_;
goto v___jp_2568_;
}
else
{
v___y_2576_ = v___y_2582_;
v___y_2577_ = v___y_2583_;
v___y_2578_ = v___y_2584_;
v___y_2579_ = v___y_2586_;
v___y_2580_ = v___y_2585_;
goto v___jp_2575_;
}
}
v___jp_2588_:
{
uint8_t v_emptyType_2595_; 
v_emptyType_2595_ = lean_ctor_get_uint8(v_config_2469_, sizeof(void*)*1 + 1);
if (v_emptyType_2595_ == 0)
{
v___y_2582_ = v___y_2594_;
v___y_2583_ = v___y_2589_;
v___y_2584_ = v___y_2592_;
v___y_2585_ = v___y_2593_;
v___y_2586_ = v___y_2591_;
v___y_2587_ = v___x_2574_;
goto v___jp_2581_;
}
else
{
if (v___y_2590_ == 0)
{
v___y_2576_ = v___y_2594_;
v___y_2577_ = v___y_2589_;
v___y_2578_ = v___y_2592_;
v___y_2579_ = v___y_2591_;
v___y_2580_ = v___y_2593_;
goto v___jp_2575_;
}
else
{
v___y_2582_ = v___y_2594_;
v___y_2583_ = v___y_2589_;
v___y_2584_ = v___y_2592_;
v___y_2585_ = v___y_2593_;
v___y_2586_ = v___y_2591_;
v___y_2587_ = v___x_2574_;
goto v___jp_2581_;
}
}
}
v___jp_2596_:
{
if (v___y_2603_ == 0)
{
v___y_2589_ = v___y_2599_;
v___y_2590_ = v___y_2602_;
v___y_2591_ = v___y_2598_;
v___y_2592_ = v___y_2597_;
v___y_2593_ = v___y_2600_;
v___y_2594_ = v___y_2601_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2604_; 
lean_inc(v_val_2501_);
lean_inc(v_mvarId_2470_);
v___x_2604_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2470_, v_val_2501_, v___y_2598_, v___y_2597_, v___y_2600_, v___y_2601_);
if (lean_obj_tag(v___x_2604_) == 0)
{
lean_object* v_a_2605_; uint8_t v___x_2606_; 
v_a_2605_ = lean_ctor_get(v___x_2604_, 0);
lean_inc(v_a_2605_);
lean_dec_ref_known(v___x_2604_, 1);
v___x_2606_ = lean_unbox(v_a_2605_);
lean_dec(v_a_2605_);
if (v___x_2606_ == 0)
{
v___y_2589_ = v___y_2599_;
v___y_2590_ = v___y_2602_;
v___y_2591_ = v___y_2598_;
v___y_2592_ = v___y_2597_;
v___y_2593_ = v___y_2600_;
v___y_2594_ = v___y_2601_;
goto v___jp_2588_;
}
else
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
lean_dec(v_val_2501_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v___x_2607_ = lean_box(v___x_2480_);
v___x_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
v___x_2609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2608_);
lean_ctor_set(v___x_2609_, 1, v___x_2505_);
v_a_2487_ = v___x_2609_;
goto v___jp_2486_;
}
}
else
{
lean_object* v_a_2610_; lean_object* v___x_2612_; uint8_t v_isShared_2613_; uint8_t v_isSharedCheck_2617_; 
lean_dec(v_val_2501_);
lean_del_object(v___x_2484_);
lean_dec(v_snd_2482_);
lean_dec(v_mvarId_2470_);
lean_dec_ref(v_config_2469_);
v_a_2610_ = lean_ctor_get(v___x_2604_, 0);
v_isSharedCheck_2617_ = !lean_is_exclusive(v___x_2604_);
if (v_isSharedCheck_2617_ == 0)
{
v___x_2612_ = v___x_2604_;
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
else
{
lean_inc(v_a_2610_);
lean_dec(v___x_2604_);
v___x_2612_ = lean_box(0);
v_isShared_2613_ = v_isSharedCheck_2617_;
goto v_resetjp_2611_;
}
v_resetjp_2611_:
{
lean_object* v___x_2615_; 
if (v_isShared_2613_ == 0)
{
v___x_2615_ = v___x_2612_;
goto v_reusejp_2614_;
}
else
{
lean_object* v_reuseFailAlloc_2616_; 
v_reuseFailAlloc_2616_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_a_2610_);
v___x_2615_ = v_reuseFailAlloc_2616_;
goto v_reusejp_2614_;
}
v_reusejp_2614_:
{
return v___x_2615_;
}
}
}
}
}
}
}
v___jp_2486_:
{
lean_object* v___x_2488_; lean_object* v___x_2490_; 
v___x_2488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_a_2487_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2488_);
v___x_2490_ = v___x_2484_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v___x_2488_);
lean_ctor_set(v_reuseFailAlloc_2492_, 1, v_snd_2482_);
v___x_2490_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
lean_object* v___x_2491_; 
v___x_2491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2490_);
return v___x_2491_;
}
}
v___jp_2494_:
{
lean_object* v___x_2496_; size_t v___x_2497_; size_t v___x_2498_; lean_object* v___x_2499_; 
v___x_2496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2493_);
lean_ctor_set(v___x_2496_, 1, v_a_2495_);
v___x_2497_ = ((size_t)1ULL);
v___x_2498_ = lean_usize_add(v_i_2473_, v___x_2497_);
v___x_2499_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2469_, v_mvarId_2470_, v_as_2471_, v_sz_2472_, v___x_2498_, v___x_2496_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
return v___x_2499_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3121_, lean_object* v_mvarId_3122_, lean_object* v_as_3123_, lean_object* v_sz_3124_, lean_object* v_i_3125_, lean_object* v_b_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_){
_start:
{
size_t v_sz_boxed_3132_; size_t v_i_boxed_3133_; lean_object* v_res_3134_; 
v_sz_boxed_3132_ = lean_unbox_usize(v_sz_3124_);
lean_dec(v_sz_3124_);
v_i_boxed_3133_ = lean_unbox_usize(v_i_3125_);
lean_dec(v_i_3125_);
v_res_3134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3121_, v_mvarId_3122_, v_as_3123_, v_sz_boxed_3132_, v_i_boxed_3133_, v_b_3126_, v___y_3127_, v___y_3128_, v___y_3129_, v___y_3130_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec_ref(v_as_3123_);
return v_res_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3138_, lean_object* v_mvarId_3139_, lean_object* v_as_3140_, size_t v_sz_3141_, size_t v_i_3142_, lean_object* v_b_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
uint8_t v___x_3149_; 
v___x_3149_ = lean_usize_dec_lt(v_i_3142_, v_sz_3141_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; 
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v___x_3150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3150_, 0, v_b_3143_);
return v___x_3150_;
}
else
{
lean_object* v_snd_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3808_; 
v_snd_3151_ = lean_ctor_get(v_b_3143_, 1);
v_isSharedCheck_3808_ = !lean_is_exclusive(v_b_3143_);
if (v_isSharedCheck_3808_ == 0)
{
lean_object* v_unused_3809_; 
v_unused_3809_ = lean_ctor_get(v_b_3143_, 0);
lean_dec(v_unused_3809_);
v___x_3153_ = v_b_3143_;
v_isShared_3154_ = v_isSharedCheck_3808_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_snd_3151_);
lean_dec(v_b_3143_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3808_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v_a_3156_; lean_object* v___x_3162_; lean_object* v_a_3164_; lean_object* v_a_3169_; 
v___x_3162_ = lean_box(0);
v_a_3169_ = lean_array_uget(v_as_3140_, v_i_3142_);
if (lean_obj_tag(v_a_3169_) == 0)
{
lean_del_object(v___x_3153_);
v_a_3164_ = v_snd_3151_;
goto v___jp_3163_;
}
else
{
lean_object* v_val_3170_; lean_object* v___x_3172_; uint8_t v_isShared_3173_; uint8_t v_isSharedCheck_3807_; 
v_val_3170_ = lean_ctor_get(v_a_3169_, 0);
v_isSharedCheck_3807_ = !lean_is_exclusive(v_a_3169_);
if (v_isSharedCheck_3807_ == 0)
{
v___x_3172_ = v_a_3169_;
v_isShared_3173_ = v_isSharedCheck_3807_;
goto v_resetjp_3171_;
}
else
{
lean_inc(v_val_3170_);
lean_dec(v_a_3169_);
v___x_3172_ = lean_box(0);
v_isShared_3173_ = v_isSharedCheck_3807_;
goto v_resetjp_3171_;
}
v_resetjp_3171_:
{
lean_object* v___x_3174_; lean_object* v___y_3176_; lean_object* v___y_3177_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___x_3216_; lean_object* v___y_3218_; lean_object* v___y_3219_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3240_; lean_object* v___y_3241_; lean_object* v___y_3242_; lean_object* v___y_3243_; uint8_t v___y_3244_; uint8_t v___x_3245_; lean_object* v___y_3247_; lean_object* v___y_3248_; lean_object* v___y_3249_; uint8_t v___y_3250_; lean_object* v___y_3251_; lean_object* v___y_3253_; lean_object* v___y_3254_; uint8_t v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3257_; uint8_t v___y_3258_; uint8_t v___y_3260_; uint8_t v___y_3261_; lean_object* v___y_3262_; lean_object* v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3268_; uint8_t v___y_3269_; lean_object* v___y_3270_; uint8_t v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; uint8_t v___y_3274_; 
v___x_3174_ = lean_box(0);
v___x_3216_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3245_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3170_);
if (v___x_3245_ == 0)
{
lean_object* v___x_3290_; uint8_t v___y_3292_; uint8_t v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3301_; lean_object* v___y_3302_; uint8_t v___y_3303_; lean_object* v___y_3304_; lean_object* v___y_3305_; uint8_t v___y_3306_; lean_object* v___y_3307_; uint8_t v___y_3308_; lean_object* v___y_3311_; lean_object* v___y_3312_; uint8_t v___y_3313_; lean_object* v___y_3314_; lean_object* v___y_3315_; uint8_t v___y_3316_; lean_object* v_a_3317_; lean_object* v___y_3321_; lean_object* v___y_3322_; uint8_t v___y_3323_; lean_object* v___y_3324_; uint8_t v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3388_; lean_object* v___y_3389_; uint8_t v___y_3390_; lean_object* v___y_3391_; uint8_t v___y_3392_; lean_object* v___y_3393_; uint8_t v___y_3394_; lean_object* v___y_3396_; lean_object* v___y_3397_; uint8_t v___y_3398_; lean_object* v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; uint8_t v___y_3402_; uint8_t v___y_3403_; lean_object* v___y_3406_; lean_object* v___y_3407_; uint8_t v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; uint8_t v___y_3411_; uint8_t v___y_3412_; lean_object* v___y_3425_; lean_object* v___y_3426_; uint8_t v___y_3427_; lean_object* v___y_3428_; uint8_t v___y_3429_; lean_object* v___y_3430_; uint8_t v___y_3431_; uint8_t v___y_3433_; uint8_t v_isHEq_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; uint8_t v___y_3447_; lean_object* v___y_3448_; uint8_t v_isEq_3505_; lean_object* v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3601_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___x_3737_; 
v___x_3290_ = l_Lean_LocalDecl_type(v_val_3170_);
lean_inc_ref(v___x_3290_);
v___x_3737_ = l_Lean_Meta_matchNot_x3f(v___x_3290_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3737_) == 0)
{
lean_object* v_a_3738_; 
v_a_3738_ = lean_ctor_get(v___x_3737_, 0);
lean_inc(v_a_3738_);
lean_dec_ref_known(v___x_3737_, 1);
if (lean_obj_tag(v_a_3738_) == 1)
{
lean_object* v_val_3739_; lean_object* v___x_3741_; uint8_t v_isShared_3742_; uint8_t v_isSharedCheck_3798_; 
v_val_3739_ = lean_ctor_get(v_a_3738_, 0);
v_isSharedCheck_3798_ = !lean_is_exclusive(v_a_3738_);
if (v_isSharedCheck_3798_ == 0)
{
v___x_3741_ = v_a_3738_;
v_isShared_3742_ = v_isSharedCheck_3798_;
goto v_resetjp_3740_;
}
else
{
lean_inc(v_val_3739_);
lean_dec(v_a_3738_);
v___x_3741_ = lean_box(0);
v_isShared_3742_ = v_isSharedCheck_3798_;
goto v_resetjp_3740_;
}
v_resetjp_3740_:
{
lean_object* v___x_3743_; 
v___x_3743_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3739_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
if (lean_obj_tag(v_a_3744_) == 1)
{
lean_object* v_val_3745_; lean_object* v___x_3747_; uint8_t v_isShared_3748_; uint8_t v_isSharedCheck_3789_; 
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec_ref(v_config_3138_);
v_val_3745_ = lean_ctor_get(v_a_3744_, 0);
v_isSharedCheck_3789_ = !lean_is_exclusive(v_a_3744_);
if (v_isSharedCheck_3789_ == 0)
{
v___x_3747_ = v_a_3744_;
v_isShared_3748_ = v_isSharedCheck_3789_;
goto v_resetjp_3746_;
}
else
{
lean_inc(v_val_3745_);
lean_dec(v_a_3744_);
v___x_3747_ = lean_box(0);
v_isShared_3748_ = v_isSharedCheck_3789_;
goto v_resetjp_3746_;
}
v_resetjp_3746_:
{
lean_object* v___x_3749_; 
lean_inc(v_mvarId_3139_);
v___x_3749_ = l_Lean_MVarId_getType(v_mvarId_3139_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3749_) == 0)
{
lean_object* v_a_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; 
v_a_3750_ = lean_ctor_get(v___x_3749_, 0);
lean_inc(v_a_3750_);
lean_dec_ref_known(v___x_3749_, 1);
v___x_3751_ = l_Lean_LocalDecl_toExpr(v_val_3170_);
v___x_3752_ = l_Lean_mkFVar(v_val_3745_);
v___x_3753_ = l_Lean_Expr_app___override(v___x_3751_, v___x_3752_);
v___x_3754_ = l_Lean_Meta_mkFalseElim(v_a_3750_, v___x_3753_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
if (lean_obj_tag(v___x_3754_) == 0)
{
lean_object* v_a_3755_; lean_object* v___x_3756_; 
v_a_3755_ = lean_ctor_get(v___x_3754_, 0);
lean_inc(v_a_3755_);
lean_dec_ref_known(v___x_3754_, 1);
v___x_3756_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3139_, v_a_3755_, v___y_3145_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v___x_3757_; lean_object* v___x_3759_; 
lean_dec_ref_known(v___x_3756_, 1);
v___x_3757_ = lean_box(v___x_3149_);
if (v_isShared_3748_ == 0)
{
lean_ctor_set(v___x_3747_, 0, v___x_3757_);
v___x_3759_ = v___x_3747_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; lean_object* v___x_3762_; 
v___x_3760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3760_, 0, v___x_3759_);
lean_ctor_set(v___x_3760_, 1, v___x_3174_);
if (v_isShared_3742_ == 0)
{
lean_ctor_set_tag(v___x_3741_, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3760_);
v___x_3762_ = v___x_3741_;
goto v_reusejp_3761_;
}
else
{
lean_object* v_reuseFailAlloc_3763_; 
v_reuseFailAlloc_3763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3763_, 0, v___x_3760_);
v___x_3762_ = v_reuseFailAlloc_3763_;
goto v_reusejp_3761_;
}
v_reusejp_3761_:
{
v_a_3156_ = v___x_3762_;
goto v___jp_3155_;
}
}
}
else
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3772_; 
lean_del_object(v___x_3747_);
lean_del_object(v___x_3741_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
v_a_3765_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3772_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3772_ == 0)
{
v___x_3767_ = v___x_3756_;
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3756_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3772_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v___x_3770_; 
if (v_isShared_3768_ == 0)
{
v___x_3770_ = v___x_3767_;
goto v_reusejp_3769_;
}
else
{
lean_object* v_reuseFailAlloc_3771_; 
v_reuseFailAlloc_3771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3771_, 0, v_a_3765_);
v___x_3770_ = v_reuseFailAlloc_3771_;
goto v_reusejp_3769_;
}
v_reusejp_3769_:
{
return v___x_3770_;
}
}
}
}
else
{
lean_object* v_a_3773_; lean_object* v___x_3775_; uint8_t v_isShared_3776_; uint8_t v_isSharedCheck_3780_; 
lean_del_object(v___x_3747_);
lean_del_object(v___x_3741_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3773_ = lean_ctor_get(v___x_3754_, 0);
v_isSharedCheck_3780_ = !lean_is_exclusive(v___x_3754_);
if (v_isSharedCheck_3780_ == 0)
{
v___x_3775_ = v___x_3754_;
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
else
{
lean_inc(v_a_3773_);
lean_dec(v___x_3754_);
v___x_3775_ = lean_box(0);
v_isShared_3776_ = v_isSharedCheck_3780_;
goto v_resetjp_3774_;
}
v_resetjp_3774_:
{
lean_object* v___x_3778_; 
if (v_isShared_3776_ == 0)
{
v___x_3778_ = v___x_3775_;
goto v_reusejp_3777_;
}
else
{
lean_object* v_reuseFailAlloc_3779_; 
v_reuseFailAlloc_3779_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3779_, 0, v_a_3773_);
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
lean_del_object(v___x_3747_);
lean_dec(v_val_3745_);
lean_del_object(v___x_3741_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3781_ = lean_ctor_get(v___x_3749_, 0);
v_isSharedCheck_3788_ = !lean_is_exclusive(v___x_3749_);
if (v_isSharedCheck_3788_ == 0)
{
v___x_3783_ = v___x_3749_;
v_isShared_3784_ = v_isSharedCheck_3788_;
goto v_resetjp_3782_;
}
else
{
lean_inc(v_a_3781_);
lean_dec(v___x_3749_);
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
else
{
lean_dec(v_a_3744_);
lean_del_object(v___x_3741_);
v___y_3601_ = v___y_3144_;
v___y_3602_ = v___y_3145_;
v___y_3603_ = v___y_3146_;
v___y_3604_ = v___y_3147_;
goto v___jp_3600_;
}
}
else
{
lean_object* v_a_3790_; lean_object* v___x_3792_; uint8_t v_isShared_3793_; uint8_t v_isSharedCheck_3797_; 
lean_del_object(v___x_3741_);
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3790_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3797_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3797_ == 0)
{
v___x_3792_ = v___x_3743_;
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
else
{
lean_inc(v_a_3790_);
lean_dec(v___x_3743_);
v___x_3792_ = lean_box(0);
v_isShared_3793_ = v_isSharedCheck_3797_;
goto v_resetjp_3791_;
}
v_resetjp_3791_:
{
lean_object* v___x_3795_; 
if (v_isShared_3793_ == 0)
{
v___x_3795_ = v___x_3792_;
goto v_reusejp_3794_;
}
else
{
lean_object* v_reuseFailAlloc_3796_; 
v_reuseFailAlloc_3796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3796_, 0, v_a_3790_);
v___x_3795_ = v_reuseFailAlloc_3796_;
goto v_reusejp_3794_;
}
v_reusejp_3794_:
{
return v___x_3795_;
}
}
}
}
}
else
{
lean_dec(v_a_3738_);
v___y_3601_ = v___y_3144_;
v___y_3602_ = v___y_3145_;
v___y_3603_ = v___y_3146_;
v___y_3604_ = v___y_3147_;
goto v___jp_3600_;
}
}
else
{
lean_object* v_a_3799_; lean_object* v___x_3801_; uint8_t v_isShared_3802_; uint8_t v_isSharedCheck_3806_; 
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3799_ = lean_ctor_get(v___x_3737_, 0);
v_isSharedCheck_3806_ = !lean_is_exclusive(v___x_3737_);
if (v_isSharedCheck_3806_ == 0)
{
v___x_3801_ = v___x_3737_;
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
else
{
lean_inc(v_a_3799_);
lean_dec(v___x_3737_);
v___x_3801_ = lean_box(0);
v_isShared_3802_ = v_isSharedCheck_3806_;
goto v_resetjp_3800_;
}
v_resetjp_3800_:
{
lean_object* v___x_3804_; 
if (v_isShared_3802_ == 0)
{
v___x_3804_ = v___x_3801_;
goto v_reusejp_3803_;
}
else
{
lean_object* v_reuseFailAlloc_3805_; 
v_reuseFailAlloc_3805_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3805_, 0, v_a_3799_);
v___x_3804_ = v_reuseFailAlloc_3805_;
goto v_reusejp_3803_;
}
v_reusejp_3803_:
{
return v___x_3804_;
}
}
}
v___jp_3291_:
{
uint8_t v_genDiseq_3298_; 
v_genDiseq_3298_ = lean_ctor_get_uint8(v_config_3138_, sizeof(void*)*1 + 2);
if (v_genDiseq_3298_ == 0)
{
lean_dec_ref(v___x_3290_);
v___y_3268_ = v___y_3296_;
v___y_3269_ = v___y_3292_;
v___y_3270_ = v___y_3294_;
v___y_3271_ = v___y_3293_;
v___y_3272_ = v___y_3297_;
v___y_3273_ = v___y_3295_;
v___y_3274_ = v___x_3245_;
goto v___jp_3267_;
}
else
{
uint8_t v___x_3299_; 
v___x_3299_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3290_);
v___y_3268_ = v___y_3296_;
v___y_3269_ = v___y_3292_;
v___y_3270_ = v___y_3294_;
v___y_3271_ = v___y_3293_;
v___y_3272_ = v___y_3297_;
v___y_3273_ = v___y_3295_;
v___y_3274_ = v___x_3299_;
goto v___jp_3267_;
}
}
v___jp_3300_:
{
if (v___y_3308_ == 0)
{
lean_dec_ref(v___y_3304_);
v___y_3292_ = v___y_3303_;
v___y_3293_ = v___y_3306_;
v___y_3294_ = v___y_3307_;
v___y_3295_ = v___y_3302_;
v___y_3296_ = v___y_3305_;
v___y_3297_ = v___y_3301_;
goto v___jp_3291_;
}
else
{
lean_object* v___x_3309_; 
lean_dec_ref(v___x_3290_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v___x_3309_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___y_3304_);
return v___x_3309_;
}
}
v___jp_3310_:
{
uint8_t v___x_3318_; 
v___x_3318_ = l_Lean_Exception_isInterrupt(v_a_3317_);
if (v___x_3318_ == 0)
{
uint8_t v___x_3319_; 
lean_inc_ref(v_a_3317_);
v___x_3319_ = l_Lean_Exception_isRuntime(v_a_3317_);
v___y_3301_ = v___y_3311_;
v___y_3302_ = v___y_3312_;
v___y_3303_ = v___y_3313_;
v___y_3304_ = v_a_3317_;
v___y_3305_ = v___y_3314_;
v___y_3306_ = v___y_3316_;
v___y_3307_ = v___y_3315_;
v___y_3308_ = v___x_3319_;
goto v___jp_3300_;
}
else
{
v___y_3301_ = v___y_3311_;
v___y_3302_ = v___y_3312_;
v___y_3303_ = v___y_3313_;
v___y_3304_ = v_a_3317_;
v___y_3305_ = v___y_3314_;
v___y_3306_ = v___y_3316_;
v___y_3307_ = v___y_3315_;
v___y_3308_ = v___x_3318_;
goto v___jp_3300_;
}
}
v___jp_3320_:
{
lean_object* v___x_3327_; 
lean_inc_ref(v___x_3290_);
v___x_3327_ = l_Lean_Meta_mkDecide(v___x_3290_, v___y_3326_, v___y_3322_, v___y_3324_, v___y_3321_);
if (lean_obj_tag(v___x_3327_) == 0)
{
lean_object* v_a_3328_; lean_object* v_keyedConfig_3329_; uint8_t v_trackZetaDelta_3330_; lean_object* v_zetaDeltaSet_3331_; lean_object* v_lctx_3332_; lean_object* v_localInstances_3333_; lean_object* v_defEqCtx_x3f_3334_; lean_object* v_synthPendingDepth_3335_; lean_object* v_customCanUnfoldPredicate_x3f_3336_; uint8_t v_univApprox_3337_; uint8_t v_inTypeClassResolution_3338_; uint8_t v_cacheInferType_3339_; uint8_t v___x_3340_; lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; 
v_a_3328_ = lean_ctor_get(v___x_3327_, 0);
lean_inc_n(v_a_3328_, 2);
lean_dec_ref_known(v___x_3327_, 1);
v_keyedConfig_3329_ = lean_ctor_get(v___y_3326_, 0);
v_trackZetaDelta_3330_ = lean_ctor_get_uint8(v___y_3326_, sizeof(void*)*7);
v_zetaDeltaSet_3331_ = lean_ctor_get(v___y_3326_, 1);
v_lctx_3332_ = lean_ctor_get(v___y_3326_, 2);
v_localInstances_3333_ = lean_ctor_get(v___y_3326_, 3);
v_defEqCtx_x3f_3334_ = lean_ctor_get(v___y_3326_, 4);
v_synthPendingDepth_3335_ = lean_ctor_get(v___y_3326_, 5);
v_customCanUnfoldPredicate_x3f_3336_ = lean_ctor_get(v___y_3326_, 6);
v_univApprox_3337_ = lean_ctor_get_uint8(v___y_3326_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3338_ = lean_ctor_get_uint8(v___y_3326_, sizeof(void*)*7 + 2);
v_cacheInferType_3339_ = lean_ctor_get_uint8(v___y_3326_, sizeof(void*)*7 + 3);
v___x_3340_ = 1;
lean_inc_ref(v_keyedConfig_3329_);
v___x_3341_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3340_, v_keyedConfig_3329_);
lean_inc(v_customCanUnfoldPredicate_x3f_3336_);
lean_inc(v_synthPendingDepth_3335_);
lean_inc(v_defEqCtx_x3f_3334_);
lean_inc_ref(v_localInstances_3333_);
lean_inc_ref(v_lctx_3332_);
lean_inc(v_zetaDeltaSet_3331_);
v___x_3342_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3342_, 0, v___x_3341_);
lean_ctor_set(v___x_3342_, 1, v_zetaDeltaSet_3331_);
lean_ctor_set(v___x_3342_, 2, v_lctx_3332_);
lean_ctor_set(v___x_3342_, 3, v_localInstances_3333_);
lean_ctor_set(v___x_3342_, 4, v_defEqCtx_x3f_3334_);
lean_ctor_set(v___x_3342_, 5, v_synthPendingDepth_3335_);
lean_ctor_set(v___x_3342_, 6, v_customCanUnfoldPredicate_x3f_3336_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*7, v_trackZetaDelta_3330_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*7 + 1, v_univApprox_3337_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3338_);
lean_ctor_set_uint8(v___x_3342_, sizeof(void*)*7 + 3, v_cacheInferType_3339_);
lean_inc(v___y_3321_);
lean_inc_ref(v___y_3324_);
lean_inc(v___y_3322_);
v___x_3343_ = lean_whnf(v_a_3328_, v___x_3342_, v___y_3322_, v___y_3324_, v___y_3321_);
if (lean_obj_tag(v___x_3343_) == 0)
{
lean_object* v_a_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
v_a_3344_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3344_);
lean_dec_ref_known(v___x_3343_, 1);
v___x_3345_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3346_ = l_Lean_Expr_isConstOf(v_a_3344_, v___x_3345_);
lean_dec(v_a_3344_);
if (v___x_3346_ == 0)
{
lean_dec(v_a_3328_);
v___y_3292_ = v___y_3323_;
v___y_3293_ = v___y_3325_;
v___y_3294_ = v___y_3326_;
v___y_3295_ = v___y_3322_;
v___y_3296_ = v___y_3324_;
v___y_3297_ = v___y_3321_;
goto v___jp_3291_;
}
else
{
lean_object* v___x_3347_; 
lean_inc(v_a_3328_);
v___x_3347_ = l_Lean_Meta_mkEqRefl(v_a_3328_, v___y_3326_, v___y_3322_, v___y_3324_, v___y_3321_);
if (lean_obj_tag(v___x_3347_) == 0)
{
lean_object* v_a_3348_; lean_object* v___x_3349_; 
v_a_3348_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3348_);
lean_dec_ref_known(v___x_3347_, 1);
lean_inc(v_mvarId_3139_);
v___x_3349_ = l_Lean_MVarId_getType(v_mvarId_3139_, v___y_3326_, v___y_3322_, v___y_3324_, v___y_3321_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v_nargs_3351_; lean_object* v___x_3352_; lean_object* v_dummy_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
v_nargs_3351_ = l_Lean_Expr_getAppNumArgs(v_a_3328_);
v___x_3352_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3353_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_3351_);
v___x_3354_ = lean_mk_array(v_nargs_3351_, v_dummy_3353_);
v___x_3355_ = lean_unsigned_to_nat(1u);
v___x_3356_ = lean_nat_sub(v_nargs_3351_, v___x_3355_);
lean_dec(v_nargs_3351_);
v___x_3357_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3328_, v___x_3354_, v___x_3356_);
v___x_3358_ = lean_array_push(v___x_3357_, v_a_3348_);
v___x_3359_ = l_Lean_mkAppN(v___x_3352_, v___x_3358_);
lean_dec_ref(v___x_3358_);
lean_inc(v_val_3170_);
v___x_3360_ = l_Lean_LocalDecl_toExpr(v_val_3170_);
v___x_3361_ = l_Lean_Meta_mkAbsurd(v_a_3350_, v___x_3360_, v___x_3359_, v___y_3326_, v___y_3322_, v___y_3324_, v___y_3321_);
if (lean_obj_tag(v___x_3361_) == 0)
{
lean_object* v_a_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3381_; 
v_a_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3381_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3381_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3381_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_a_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3381_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; 
lean_inc(v_mvarId_3139_);
v___x_3366_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3139_, v_a_3362_, v___y_3322_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v___x_3368_; uint8_t v_isShared_3369_; uint8_t v_isSharedCheck_3378_; 
lean_dec_ref(v___x_3290_);
lean_dec(v_val_3170_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_isSharedCheck_3378_ = !lean_is_exclusive(v___x_3366_);
if (v_isSharedCheck_3378_ == 0)
{
lean_object* v_unused_3379_; 
v_unused_3379_ = lean_ctor_get(v___x_3366_, 0);
lean_dec(v_unused_3379_);
v___x_3368_ = v___x_3366_;
v_isShared_3369_ = v_isSharedCheck_3378_;
goto v_resetjp_3367_;
}
else
{
lean_dec(v___x_3366_);
v___x_3368_ = lean_box(0);
v_isShared_3369_ = v_isSharedCheck_3378_;
goto v_resetjp_3367_;
}
v_resetjp_3367_:
{
lean_object* v___x_3370_; lean_object* v___x_3372_; 
v___x_3370_ = lean_box(v___x_3149_);
if (v_isShared_3369_ == 0)
{
lean_ctor_set_tag(v___x_3368_, 1);
lean_ctor_set(v___x_3368_, 0, v___x_3370_);
v___x_3372_ = v___x_3368_;
goto v_reusejp_3371_;
}
else
{
lean_object* v_reuseFailAlloc_3377_; 
v_reuseFailAlloc_3377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3377_, 0, v___x_3370_);
v___x_3372_ = v_reuseFailAlloc_3377_;
goto v_reusejp_3371_;
}
v_reusejp_3371_:
{
lean_object* v___x_3373_; lean_object* v___x_3375_; 
v___x_3373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3372_);
lean_ctor_set(v___x_3373_, 1, v___x_3174_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set(v___x_3364_, 0, v___x_3373_);
v___x_3375_ = v___x_3364_;
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
v_a_3156_ = v___x_3375_;
goto v___jp_3155_;
}
}
}
}
else
{
lean_object* v_a_3380_; 
lean_del_object(v___x_3364_);
v_a_3380_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3380_);
lean_dec_ref_known(v___x_3366_, 1);
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3326_;
v___y_3316_ = v___y_3325_;
v_a_3317_ = v_a_3380_;
goto v___jp_3310_;
}
}
}
else
{
lean_object* v_a_3382_; 
v_a_3382_ = lean_ctor_get(v___x_3361_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3361_, 1);
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3326_;
v___y_3316_ = v___y_3325_;
v_a_3317_ = v_a_3382_;
goto v___jp_3310_;
}
}
else
{
lean_object* v_a_3383_; 
lean_dec(v_a_3348_);
lean_dec(v_a_3328_);
v_a_3383_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3383_);
lean_dec_ref_known(v___x_3349_, 1);
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3326_;
v___y_3316_ = v___y_3325_;
v_a_3317_ = v_a_3383_;
goto v___jp_3310_;
}
}
else
{
lean_object* v_a_3384_; 
lean_dec(v_a_3328_);
v_a_3384_ = lean_ctor_get(v___x_3347_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3347_, 1);
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3326_;
v___y_3316_ = v___y_3325_;
v_a_3317_ = v_a_3384_;
goto v___jp_3310_;
}
}
}
else
{
lean_object* v_a_3385_; 
lean_dec(v_a_3328_);
v_a_3385_ = lean_ctor_get(v___x_3343_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3343_, 1);
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3326_;
v___y_3316_ = v___y_3325_;
v_a_3317_ = v_a_3385_;
goto v___jp_3310_;
}
}
else
{
lean_object* v_a_3386_; 
v_a_3386_ = lean_ctor_get(v___x_3327_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3327_, 1);
v___y_3311_ = v___y_3321_;
v___y_3312_ = v___y_3322_;
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3326_;
v___y_3316_ = v___y_3325_;
v_a_3317_ = v_a_3386_;
goto v___jp_3310_;
}
}
v___jp_3387_:
{
if (v___y_3394_ == 0)
{
v___y_3292_ = v___y_3390_;
v___y_3293_ = v___y_3392_;
v___y_3294_ = v___y_3393_;
v___y_3295_ = v___y_3389_;
v___y_3296_ = v___y_3391_;
v___y_3297_ = v___y_3388_;
goto v___jp_3291_;
}
else
{
v___y_3321_ = v___y_3388_;
v___y_3322_ = v___y_3389_;
v___y_3323_ = v___y_3390_;
v___y_3324_ = v___y_3391_;
v___y_3325_ = v___y_3392_;
v___y_3326_ = v___y_3393_;
goto v___jp_3320_;
}
}
v___jp_3395_:
{
if (v___y_3403_ == 0)
{
lean_dec_ref(v___y_3400_);
v___y_3388_ = v___y_3396_;
v___y_3389_ = v___y_3397_;
v___y_3390_ = v___y_3398_;
v___y_3391_ = v___y_3399_;
v___y_3392_ = v___y_3402_;
v___y_3393_ = v___y_3401_;
v___y_3394_ = v___x_3245_;
goto v___jp_3387_;
}
else
{
uint8_t v___x_3404_; 
v___x_3404_ = l_Lean_Expr_hasFVar(v___y_3400_);
lean_dec_ref(v___y_3400_);
if (v___x_3404_ == 0)
{
v___y_3321_ = v___y_3396_;
v___y_3322_ = v___y_3397_;
v___y_3323_ = v___y_3398_;
v___y_3324_ = v___y_3399_;
v___y_3325_ = v___y_3402_;
v___y_3326_ = v___y_3401_;
goto v___jp_3320_;
}
else
{
v___y_3388_ = v___y_3396_;
v___y_3389_ = v___y_3397_;
v___y_3390_ = v___y_3398_;
v___y_3391_ = v___y_3399_;
v___y_3392_ = v___y_3402_;
v___y_3393_ = v___y_3401_;
v___y_3394_ = v___x_3245_;
goto v___jp_3387_;
}
}
}
v___jp_3405_:
{
lean_object* v___x_3413_; 
lean_inc_ref(v___x_3290_);
v___x_3413_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3290_, v___y_3407_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; uint8_t v___x_3415_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v___x_3415_ = l_Lean_Expr_hasMVar(v_a_3414_);
if (v___x_3415_ == 0)
{
v___y_3396_ = v___y_3406_;
v___y_3397_ = v___y_3407_;
v___y_3398_ = v___y_3408_;
v___y_3399_ = v___y_3409_;
v___y_3400_ = v_a_3414_;
v___y_3401_ = v___y_3410_;
v___y_3402_ = v___y_3411_;
v___y_3403_ = v___y_3412_;
goto v___jp_3395_;
}
else
{
v___y_3396_ = v___y_3406_;
v___y_3397_ = v___y_3407_;
v___y_3398_ = v___y_3408_;
v___y_3399_ = v___y_3409_;
v___y_3400_ = v_a_3414_;
v___y_3401_ = v___y_3410_;
v___y_3402_ = v___y_3411_;
v___y_3403_ = v___x_3245_;
goto v___jp_3395_;
}
}
else
{
lean_object* v_a_3416_; lean_object* v___x_3418_; uint8_t v_isShared_3419_; uint8_t v_isSharedCheck_3423_; 
lean_dec_ref(v___x_3290_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3416_ = lean_ctor_get(v___x_3413_, 0);
v_isSharedCheck_3423_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3423_ == 0)
{
v___x_3418_ = v___x_3413_;
v_isShared_3419_ = v_isSharedCheck_3423_;
goto v_resetjp_3417_;
}
else
{
lean_inc(v_a_3416_);
lean_dec(v___x_3413_);
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
v___jp_3424_:
{
if (v___y_3431_ == 0)
{
v___y_3292_ = v___y_3427_;
v___y_3293_ = v___y_3429_;
v___y_3294_ = v___y_3430_;
v___y_3295_ = v___y_3426_;
v___y_3296_ = v___y_3428_;
v___y_3297_ = v___y_3425_;
goto v___jp_3291_;
}
else
{
v___y_3406_ = v___y_3425_;
v___y_3407_ = v___y_3426_;
v___y_3408_ = v___y_3427_;
v___y_3409_ = v___y_3428_;
v___y_3410_ = v___y_3430_;
v___y_3411_ = v___y_3429_;
v___y_3412_ = v___y_3431_;
goto v___jp_3405_;
}
}
v___jp_3432_:
{
uint8_t v_useDecide_3439_; 
v_useDecide_3439_ = lean_ctor_get_uint8(v_config_3138_, sizeof(void*)*1);
if (v_useDecide_3439_ == 0)
{
v___y_3425_ = v___y_3438_;
v___y_3426_ = v___y_3436_;
v___y_3427_ = v_isHEq_3434_;
v___y_3428_ = v___y_3437_;
v___y_3429_ = v___y_3433_;
v___y_3430_ = v___y_3435_;
v___y_3431_ = v___x_3245_;
goto v___jp_3424_;
}
else
{
uint8_t v___x_3440_; 
v___x_3440_ = l_Lean_Expr_hasFVar(v___x_3290_);
if (v___x_3440_ == 0)
{
v___y_3406_ = v___y_3438_;
v___y_3407_ = v___y_3436_;
v___y_3408_ = v_isHEq_3434_;
v___y_3409_ = v___y_3437_;
v___y_3410_ = v___y_3435_;
v___y_3411_ = v___y_3433_;
v___y_3412_ = v_useDecide_3439_;
goto v___jp_3405_;
}
else
{
v___y_3425_ = v___y_3438_;
v___y_3426_ = v___y_3436_;
v___y_3427_ = v_isHEq_3434_;
v___y_3428_ = v___y_3437_;
v___y_3429_ = v___y_3433_;
v___y_3430_ = v___y_3435_;
v___y_3431_ = v___x_3245_;
goto v___jp_3424_;
}
}
}
v___jp_3441_:
{
lean_object* v___x_3449_; 
v___x_3449_ = l_Lean_Meta_isExprDefEq(v___y_3446_, v___y_3443_, v___y_3448_, v___y_3445_, v___y_3444_, v___y_3442_);
if (lean_obj_tag(v___x_3449_) == 0)
{
lean_object* v_a_3450_; uint8_t v___x_3451_; 
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
lean_inc(v_a_3450_);
lean_dec_ref_known(v___x_3449_, 1);
v___x_3451_ = lean_unbox(v_a_3450_);
lean_dec(v_a_3450_);
if (v___x_3451_ == 0)
{
v___y_3433_ = v___y_3447_;
v_isHEq_3434_ = v___x_3149_;
v___y_3435_ = v___y_3448_;
v___y_3436_ = v___y_3445_;
v___y_3437_ = v___y_3444_;
v___y_3438_ = v___y_3442_;
goto v___jp_3432_;
}
else
{
lean_object* v___x_3452_; 
lean_dec_ref(v___x_3290_);
lean_dec_ref(v_config_3138_);
lean_inc(v_mvarId_3139_);
v___x_3452_ = l_Lean_MVarId_getType(v_mvarId_3139_, v___y_3448_, v___y_3445_, v___y_3444_, v___y_3442_);
if (lean_obj_tag(v___x_3452_) == 0)
{
lean_object* v_a_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; 
v_a_3453_ = lean_ctor_get(v___x_3452_, 0);
lean_inc(v_a_3453_);
lean_dec_ref_known(v___x_3452_, 1);
v___x_3454_ = l_Lean_LocalDecl_toExpr(v_val_3170_);
v___x_3455_ = l_Lean_Meta_mkEqOfHEq(v___x_3454_, v___x_3149_, v___y_3448_, v___y_3445_, v___y_3444_, v___y_3442_);
if (lean_obj_tag(v___x_3455_) == 0)
{
lean_object* v_a_3456_; lean_object* v___x_3457_; 
v_a_3456_ = lean_ctor_get(v___x_3455_, 0);
lean_inc(v_a_3456_);
lean_dec_ref_known(v___x_3455_, 1);
v___x_3457_ = l_Lean_Meta_mkNoConfusion(v_a_3453_, v_a_3456_, v___y_3448_, v___y_3445_, v___y_3444_, v___y_3442_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3139_, v_a_3458_, v___y_3445_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; lean_object* v___x_3463_; 
lean_dec_ref_known(v___x_3459_, 1);
v___x_3460_ = lean_box(v___x_3149_);
v___x_3461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3461_, 0, v___x_3460_);
v___x_3462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3462_, 0, v___x_3461_);
lean_ctor_set(v___x_3462_, 1, v___x_3174_);
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
v_a_3156_ = v___x_3463_;
goto v___jp_3155_;
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
v_a_3464_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3459_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3459_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v_a_3472_; lean_object* v___x_3474_; uint8_t v_isShared_3475_; uint8_t v_isSharedCheck_3479_; 
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3472_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3479_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3479_ == 0)
{
v___x_3474_ = v___x_3457_;
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
else
{
lean_inc(v_a_3472_);
lean_dec(v___x_3457_);
v___x_3474_ = lean_box(0);
v_isShared_3475_ = v_isSharedCheck_3479_;
goto v_resetjp_3473_;
}
v_resetjp_3473_:
{
lean_object* v___x_3477_; 
if (v_isShared_3475_ == 0)
{
v___x_3477_ = v___x_3474_;
goto v_reusejp_3476_;
}
else
{
lean_object* v_reuseFailAlloc_3478_; 
v_reuseFailAlloc_3478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3478_, 0, v_a_3472_);
v___x_3477_ = v_reuseFailAlloc_3478_;
goto v_reusejp_3476_;
}
v_reusejp_3476_:
{
return v___x_3477_;
}
}
}
}
else
{
lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3487_; 
lean_dec(v_a_3453_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3480_ = lean_ctor_get(v___x_3455_, 0);
v_isSharedCheck_3487_ = !lean_is_exclusive(v___x_3455_);
if (v_isSharedCheck_3487_ == 0)
{
v___x_3482_ = v___x_3455_;
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3455_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3487_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3485_; 
if (v_isShared_3483_ == 0)
{
v___x_3485_ = v___x_3482_;
goto v_reusejp_3484_;
}
else
{
lean_object* v_reuseFailAlloc_3486_; 
v_reuseFailAlloc_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3486_, 0, v_a_3480_);
v___x_3485_ = v_reuseFailAlloc_3486_;
goto v_reusejp_3484_;
}
v_reusejp_3484_:
{
return v___x_3485_;
}
}
}
}
else
{
lean_object* v_a_3488_; lean_object* v___x_3490_; uint8_t v_isShared_3491_; uint8_t v_isSharedCheck_3495_; 
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3488_ = lean_ctor_get(v___x_3452_, 0);
v_isSharedCheck_3495_ = !lean_is_exclusive(v___x_3452_);
if (v_isSharedCheck_3495_ == 0)
{
v___x_3490_ = v___x_3452_;
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
else
{
lean_inc(v_a_3488_);
lean_dec(v___x_3452_);
v___x_3490_ = lean_box(0);
v_isShared_3491_ = v_isSharedCheck_3495_;
goto v_resetjp_3489_;
}
v_resetjp_3489_:
{
lean_object* v___x_3493_; 
if (v_isShared_3491_ == 0)
{
v___x_3493_ = v___x_3490_;
goto v_reusejp_3492_;
}
else
{
lean_object* v_reuseFailAlloc_3494_; 
v_reuseFailAlloc_3494_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3494_, 0, v_a_3488_);
v___x_3493_ = v_reuseFailAlloc_3494_;
goto v_reusejp_3492_;
}
v_reusejp_3492_:
{
return v___x_3493_;
}
}
}
}
}
else
{
lean_object* v_a_3496_; lean_object* v___x_3498_; uint8_t v_isShared_3499_; uint8_t v_isSharedCheck_3503_; 
lean_dec_ref(v___x_3290_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3496_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3498_ = v___x_3449_;
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
else
{
lean_inc(v_a_3496_);
lean_dec(v___x_3449_);
v___x_3498_ = lean_box(0);
v_isShared_3499_ = v_isSharedCheck_3503_;
goto v_resetjp_3497_;
}
v_resetjp_3497_:
{
lean_object* v___x_3501_; 
if (v_isShared_3499_ == 0)
{
v___x_3501_ = v___x_3498_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v_a_3496_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
}
v___jp_3504_:
{
lean_object* v___x_3510_; 
lean_inc_ref(v___x_3290_);
v___x_3510_ = l_Lean_Meta_matchHEq_x3f(v___x_3290_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3510_) == 0)
{
lean_object* v_a_3511_; 
v_a_3511_ = lean_ctor_get(v___x_3510_, 0);
lean_inc(v_a_3511_);
lean_dec_ref_known(v___x_3510_, 1);
if (lean_obj_tag(v_a_3511_) == 1)
{
lean_object* v_val_3512_; lean_object* v_snd_3513_; lean_object* v_snd_3514_; lean_object* v_fst_3515_; lean_object* v_fst_3516_; lean_object* v_fst_3517_; lean_object* v_snd_3518_; lean_object* v___x_3519_; 
v_val_3512_ = lean_ctor_get(v_a_3511_, 0);
lean_inc(v_val_3512_);
lean_dec_ref_known(v_a_3511_, 1);
v_snd_3513_ = lean_ctor_get(v_val_3512_, 1);
lean_inc(v_snd_3513_);
v_snd_3514_ = lean_ctor_get(v_snd_3513_, 1);
lean_inc(v_snd_3514_);
v_fst_3515_ = lean_ctor_get(v_val_3512_, 0);
lean_inc(v_fst_3515_);
lean_dec(v_val_3512_);
v_fst_3516_ = lean_ctor_get(v_snd_3513_, 0);
lean_inc(v_fst_3516_);
lean_dec(v_snd_3513_);
v_fst_3517_ = lean_ctor_get(v_snd_3514_, 0);
lean_inc(v_fst_3517_);
v_snd_3518_ = lean_ctor_get(v_snd_3514_, 1);
lean_inc(v_snd_3518_);
lean_dec(v_snd_3514_);
v___x_3519_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3516_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3519_) == 0)
{
lean_object* v_a_3520_; 
v_a_3520_ = lean_ctor_get(v___x_3519_, 0);
lean_inc(v_a_3520_);
lean_dec_ref_known(v___x_3519_, 1);
if (lean_obj_tag(v_a_3520_) == 1)
{
lean_object* v_val_3521_; lean_object* v___x_3522_; 
v_val_3521_ = lean_ctor_get(v_a_3520_, 0);
lean_inc(v_val_3521_);
lean_dec_ref_known(v_a_3520_, 1);
v___x_3522_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3518_, v___y_3506_, v___y_3507_, v___y_3508_, v___y_3509_);
if (lean_obj_tag(v___x_3522_) == 0)
{
lean_object* v_a_3523_; 
v_a_3523_ = lean_ctor_get(v___x_3522_, 0);
lean_inc(v_a_3523_);
lean_dec_ref_known(v___x_3522_, 1);
if (lean_obj_tag(v_a_3523_) == 1)
{
lean_object* v_toConstantVal_3524_; lean_object* v_val_3525_; lean_object* v_toConstantVal_3526_; lean_object* v_name_3527_; lean_object* v_name_3528_; uint8_t v___x_3529_; 
v_toConstantVal_3524_ = lean_ctor_get(v_val_3521_, 0);
lean_inc_ref(v_toConstantVal_3524_);
lean_dec(v_val_3521_);
v_val_3525_ = lean_ctor_get(v_a_3523_, 0);
lean_inc(v_val_3525_);
lean_dec_ref_known(v_a_3523_, 1);
v_toConstantVal_3526_ = lean_ctor_get(v_val_3525_, 0);
lean_inc_ref(v_toConstantVal_3526_);
lean_dec(v_val_3525_);
v_name_3527_ = lean_ctor_get(v_toConstantVal_3524_, 0);
lean_inc(v_name_3527_);
lean_dec_ref(v_toConstantVal_3524_);
v_name_3528_ = lean_ctor_get(v_toConstantVal_3526_, 0);
lean_inc(v_name_3528_);
lean_dec_ref(v_toConstantVal_3526_);
v___x_3529_ = lean_name_eq(v_name_3527_, v_name_3528_);
lean_dec(v_name_3528_);
lean_dec(v_name_3527_);
if (v___x_3529_ == 0)
{
v___y_3442_ = v___y_3509_;
v___y_3443_ = v_fst_3517_;
v___y_3444_ = v___y_3508_;
v___y_3445_ = v___y_3507_;
v___y_3446_ = v_fst_3515_;
v___y_3447_ = v_isEq_3505_;
v___y_3448_ = v___y_3506_;
goto v___jp_3441_;
}
else
{
if (v___x_3245_ == 0)
{
lean_dec(v_fst_3517_);
lean_dec(v_fst_3515_);
v___y_3433_ = v_isEq_3505_;
v_isHEq_3434_ = v___x_3149_;
v___y_3435_ = v___y_3506_;
v___y_3436_ = v___y_3507_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
goto v___jp_3432_;
}
else
{
v___y_3442_ = v___y_3509_;
v___y_3443_ = v_fst_3517_;
v___y_3444_ = v___y_3508_;
v___y_3445_ = v___y_3507_;
v___y_3446_ = v_fst_3515_;
v___y_3447_ = v_isEq_3505_;
v___y_3448_ = v___y_3506_;
goto v___jp_3441_;
}
}
}
else
{
lean_dec(v_a_3523_);
lean_dec(v_val_3521_);
lean_dec(v_fst_3517_);
lean_dec(v_fst_3515_);
v___y_3433_ = v_isEq_3505_;
v_isHEq_3434_ = v___x_3149_;
v___y_3435_ = v___y_3506_;
v___y_3436_ = v___y_3507_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
goto v___jp_3432_;
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec(v_val_3521_);
lean_dec(v_fst_3517_);
lean_dec(v_fst_3515_);
lean_dec_ref(v___x_3290_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3530_ = lean_ctor_get(v___x_3522_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3522_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3522_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3522_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
else
{
lean_dec(v_a_3520_);
lean_dec(v_snd_3518_);
lean_dec(v_fst_3517_);
lean_dec(v_fst_3515_);
v___y_3433_ = v_isEq_3505_;
v_isHEq_3434_ = v___x_3149_;
v___y_3435_ = v___y_3506_;
v___y_3436_ = v___y_3507_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
goto v___jp_3432_;
}
}
else
{
lean_object* v_a_3538_; lean_object* v___x_3540_; uint8_t v_isShared_3541_; uint8_t v_isSharedCheck_3545_; 
lean_dec(v_snd_3518_);
lean_dec(v_fst_3517_);
lean_dec(v_fst_3515_);
lean_dec_ref(v___x_3290_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3538_ = lean_ctor_get(v___x_3519_, 0);
v_isSharedCheck_3545_ = !lean_is_exclusive(v___x_3519_);
if (v_isSharedCheck_3545_ == 0)
{
v___x_3540_ = v___x_3519_;
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
else
{
lean_inc(v_a_3538_);
lean_dec(v___x_3519_);
v___x_3540_ = lean_box(0);
v_isShared_3541_ = v_isSharedCheck_3545_;
goto v_resetjp_3539_;
}
v_resetjp_3539_:
{
lean_object* v___x_3543_; 
if (v_isShared_3541_ == 0)
{
v___x_3543_ = v___x_3540_;
goto v_reusejp_3542_;
}
else
{
lean_object* v_reuseFailAlloc_3544_; 
v_reuseFailAlloc_3544_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3544_, 0, v_a_3538_);
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
lean_dec(v_a_3511_);
v___y_3433_ = v_isEq_3505_;
v_isHEq_3434_ = v___x_3245_;
v___y_3435_ = v___y_3506_;
v___y_3436_ = v___y_3507_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
goto v___jp_3432_;
}
}
else
{
lean_object* v_a_3546_; lean_object* v___x_3548_; uint8_t v_isShared_3549_; uint8_t v_isSharedCheck_3553_; 
lean_dec_ref(v___x_3290_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3546_ = lean_ctor_get(v___x_3510_, 0);
v_isSharedCheck_3553_ = !lean_is_exclusive(v___x_3510_);
if (v_isSharedCheck_3553_ == 0)
{
v___x_3548_ = v___x_3510_;
v_isShared_3549_ = v_isSharedCheck_3553_;
goto v_resetjp_3547_;
}
else
{
lean_inc(v_a_3546_);
lean_dec(v___x_3510_);
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
v___jp_3554_:
{
lean_object* v___x_3559_; 
lean_inc_ref(v___x_3290_);
v___x_3559_ = l_Lean_Meta_matchEq_x3f(v___x_3290_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
if (lean_obj_tag(v___x_3559_) == 0)
{
lean_object* v_a_3560_; 
v_a_3560_ = lean_ctor_get(v___x_3559_, 0);
lean_inc(v_a_3560_);
lean_dec_ref_known(v___x_3559_, 1);
if (lean_obj_tag(v_a_3560_) == 1)
{
lean_object* v_val_3561_; lean_object* v_snd_3562_; lean_object* v_fst_3563_; lean_object* v_snd_3564_; lean_object* v___x_3565_; 
v_val_3561_ = lean_ctor_get(v_a_3560_, 0);
lean_inc(v_val_3561_);
lean_dec_ref_known(v_a_3560_, 1);
v_snd_3562_ = lean_ctor_get(v_val_3561_, 1);
lean_inc(v_snd_3562_);
lean_dec(v_val_3561_);
v_fst_3563_ = lean_ctor_get(v_snd_3562_, 0);
lean_inc(v_fst_3563_);
v_snd_3564_ = lean_ctor_get(v_snd_3562_, 1);
lean_inc(v_snd_3564_);
lean_dec(v_snd_3562_);
v___x_3565_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3563_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
if (lean_obj_tag(v___x_3565_) == 0)
{
lean_object* v_a_3566_; 
v_a_3566_ = lean_ctor_get(v___x_3565_, 0);
lean_inc(v_a_3566_);
lean_dec_ref_known(v___x_3565_, 1);
if (lean_obj_tag(v_a_3566_) == 1)
{
lean_object* v_val_3567_; lean_object* v___x_3568_; 
v_val_3567_ = lean_ctor_get(v_a_3566_, 0);
lean_inc(v_val_3567_);
lean_dec_ref_known(v_a_3566_, 1);
v___x_3568_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3564_, v___y_3555_, v___y_3556_, v___y_3557_, v___y_3558_);
if (lean_obj_tag(v___x_3568_) == 0)
{
lean_object* v_a_3569_; 
v_a_3569_ = lean_ctor_get(v___x_3568_, 0);
lean_inc(v_a_3569_);
lean_dec_ref_known(v___x_3568_, 1);
if (lean_obj_tag(v_a_3569_) == 1)
{
lean_object* v_toConstantVal_3570_; lean_object* v_val_3571_; lean_object* v_toConstantVal_3572_; lean_object* v_name_3573_; lean_object* v_name_3574_; uint8_t v___x_3575_; 
v_toConstantVal_3570_ = lean_ctor_get(v_val_3567_, 0);
lean_inc_ref(v_toConstantVal_3570_);
lean_dec(v_val_3567_);
v_val_3571_ = lean_ctor_get(v_a_3569_, 0);
lean_inc(v_val_3571_);
lean_dec_ref_known(v_a_3569_, 1);
v_toConstantVal_3572_ = lean_ctor_get(v_val_3571_, 0);
lean_inc_ref(v_toConstantVal_3572_);
lean_dec(v_val_3571_);
v_name_3573_ = lean_ctor_get(v_toConstantVal_3570_, 0);
lean_inc(v_name_3573_);
lean_dec_ref(v_toConstantVal_3570_);
v_name_3574_ = lean_ctor_get(v_toConstantVal_3572_, 0);
lean_inc(v_name_3574_);
lean_dec_ref(v_toConstantVal_3572_);
v___x_3575_ = lean_name_eq(v_name_3573_, v_name_3574_);
lean_dec(v_name_3574_);
lean_dec(v_name_3573_);
if (v___x_3575_ == 0)
{
lean_dec_ref(v___x_3290_);
lean_dec_ref(v_config_3138_);
v___y_3176_ = v___y_3557_;
v___y_3177_ = v___y_3558_;
v___y_3178_ = v___y_3555_;
v___y_3179_ = v___y_3556_;
goto v___jp_3175_;
}
else
{
if (v___x_3245_ == 0)
{
lean_del_object(v___x_3172_);
v_isEq_3505_ = v___x_3149_;
v___y_3506_ = v___y_3555_;
v___y_3507_ = v___y_3556_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
goto v___jp_3504_;
}
else
{
lean_dec_ref(v___x_3290_);
lean_dec_ref(v_config_3138_);
v___y_3176_ = v___y_3557_;
v___y_3177_ = v___y_3558_;
v___y_3178_ = v___y_3555_;
v___y_3179_ = v___y_3556_;
goto v___jp_3175_;
}
}
}
else
{
lean_dec(v_a_3569_);
lean_dec(v_val_3567_);
lean_del_object(v___x_3172_);
v_isEq_3505_ = v___x_3149_;
v___y_3506_ = v___y_3555_;
v___y_3507_ = v___y_3556_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
goto v___jp_3504_;
}
}
else
{
lean_object* v_a_3576_; lean_object* v___x_3578_; uint8_t v_isShared_3579_; uint8_t v_isSharedCheck_3583_; 
lean_dec(v_val_3567_);
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3576_ = lean_ctor_get(v___x_3568_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v___x_3568_);
if (v_isSharedCheck_3583_ == 0)
{
v___x_3578_ = v___x_3568_;
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
else
{
lean_inc(v_a_3576_);
lean_dec(v___x_3568_);
v___x_3578_ = lean_box(0);
v_isShared_3579_ = v_isSharedCheck_3583_;
goto v_resetjp_3577_;
}
v_resetjp_3577_:
{
lean_object* v___x_3581_; 
if (v_isShared_3579_ == 0)
{
v___x_3581_ = v___x_3578_;
goto v_reusejp_3580_;
}
else
{
lean_object* v_reuseFailAlloc_3582_; 
v_reuseFailAlloc_3582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3582_, 0, v_a_3576_);
v___x_3581_ = v_reuseFailAlloc_3582_;
goto v_reusejp_3580_;
}
v_reusejp_3580_:
{
return v___x_3581_;
}
}
}
}
else
{
lean_dec(v_a_3566_);
lean_dec(v_snd_3564_);
lean_del_object(v___x_3172_);
v_isEq_3505_ = v___x_3149_;
v___y_3506_ = v___y_3555_;
v___y_3507_ = v___y_3556_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
goto v___jp_3504_;
}
}
else
{
lean_object* v_a_3584_; lean_object* v___x_3586_; uint8_t v_isShared_3587_; uint8_t v_isSharedCheck_3591_; 
lean_dec(v_snd_3564_);
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3584_ = lean_ctor_get(v___x_3565_, 0);
v_isSharedCheck_3591_ = !lean_is_exclusive(v___x_3565_);
if (v_isSharedCheck_3591_ == 0)
{
v___x_3586_ = v___x_3565_;
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
else
{
lean_inc(v_a_3584_);
lean_dec(v___x_3565_);
v___x_3586_ = lean_box(0);
v_isShared_3587_ = v_isSharedCheck_3591_;
goto v_resetjp_3585_;
}
v_resetjp_3585_:
{
lean_object* v___x_3589_; 
if (v_isShared_3587_ == 0)
{
v___x_3589_ = v___x_3586_;
goto v_reusejp_3588_;
}
else
{
lean_object* v_reuseFailAlloc_3590_; 
v_reuseFailAlloc_3590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3590_, 0, v_a_3584_);
v___x_3589_ = v_reuseFailAlloc_3590_;
goto v_reusejp_3588_;
}
v_reusejp_3588_:
{
return v___x_3589_;
}
}
}
}
else
{
lean_dec(v_a_3560_);
lean_del_object(v___x_3172_);
v_isEq_3505_ = v___x_3245_;
v___y_3506_ = v___y_3555_;
v___y_3507_ = v___y_3556_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
goto v___jp_3504_;
}
}
else
{
lean_object* v_a_3592_; lean_object* v___x_3594_; uint8_t v_isShared_3595_; uint8_t v_isSharedCheck_3599_; 
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3592_ = lean_ctor_get(v___x_3559_, 0);
v_isSharedCheck_3599_ = !lean_is_exclusive(v___x_3559_);
if (v_isSharedCheck_3599_ == 0)
{
v___x_3594_ = v___x_3559_;
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
else
{
lean_inc(v_a_3592_);
lean_dec(v___x_3559_);
v___x_3594_ = lean_box(0);
v_isShared_3595_ = v_isSharedCheck_3599_;
goto v_resetjp_3593_;
}
v_resetjp_3593_:
{
lean_object* v___x_3597_; 
if (v_isShared_3595_ == 0)
{
v___x_3597_ = v___x_3594_;
goto v_reusejp_3596_;
}
else
{
lean_object* v_reuseFailAlloc_3598_; 
v_reuseFailAlloc_3598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3598_, 0, v_a_3592_);
v___x_3597_ = v_reuseFailAlloc_3598_;
goto v_reusejp_3596_;
}
v_reusejp_3596_:
{
return v___x_3597_;
}
}
}
}
v___jp_3600_:
{
lean_object* v___x_3605_; 
lean_inc_ref(v___x_3290_);
v___x_3605_ = l_Lean_refutableHasNotBit_x3f(v___x_3290_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3605_) == 0)
{
lean_object* v_a_3606_; 
v_a_3606_ = lean_ctor_get(v___x_3605_, 0);
lean_inc(v_a_3606_);
lean_dec_ref_known(v___x_3605_, 1);
if (lean_obj_tag(v_a_3606_) == 1)
{
lean_object* v_val_3607_; lean_object* v___x_3609_; uint8_t v_isShared_3610_; uint8_t v_isSharedCheck_3647_; 
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec_ref(v_config_3138_);
v_val_3607_ = lean_ctor_get(v_a_3606_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v_a_3606_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3609_ = v_a_3606_;
v_isShared_3610_ = v_isSharedCheck_3647_;
goto v_resetjp_3608_;
}
else
{
lean_inc(v_val_3607_);
lean_dec(v_a_3606_);
v___x_3609_ = lean_box(0);
v_isShared_3610_ = v_isSharedCheck_3647_;
goto v_resetjp_3608_;
}
v_resetjp_3608_:
{
lean_object* v___x_3611_; 
lean_inc(v_mvarId_3139_);
v___x_3611_ = l_Lean_MVarId_getType(v_mvarId_3139_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3611_) == 0)
{
lean_object* v_a_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; 
v_a_3612_ = lean_ctor_get(v___x_3611_, 0);
lean_inc(v_a_3612_);
lean_dec_ref_known(v___x_3611_, 1);
v___x_3613_ = l_Lean_LocalDecl_toExpr(v_val_3170_);
v___x_3614_ = l_Lean_Meta_mkAbsurd(v_a_3612_, v_val_3607_, v___x_3613_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3614_) == 0)
{
lean_object* v_a_3615_; lean_object* v___x_3616_; 
v_a_3615_ = lean_ctor_get(v___x_3614_, 0);
lean_inc(v_a_3615_);
lean_dec_ref_known(v___x_3614_, 1);
v___x_3616_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3139_, v_a_3615_, v___y_3602_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v___x_3617_; lean_object* v___x_3619_; 
lean_dec_ref_known(v___x_3616_, 1);
v___x_3617_ = lean_box(v___x_3149_);
if (v_isShared_3610_ == 0)
{
lean_ctor_set(v___x_3609_, 0, v___x_3617_);
v___x_3619_ = v___x_3609_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3622_; 
v_reuseFailAlloc_3622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3622_, 0, v___x_3617_);
v___x_3619_ = v_reuseFailAlloc_3622_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
lean_ctor_set(v___x_3620_, 1, v___x_3174_);
v___x_3621_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3620_);
v_a_3156_ = v___x_3621_;
goto v___jp_3155_;
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_del_object(v___x_3609_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
v_a_3623_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3616_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3616_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v___x_3628_; 
if (v_isShared_3626_ == 0)
{
v___x_3628_ = v___x_3625_;
goto v_reusejp_3627_;
}
else
{
lean_object* v_reuseFailAlloc_3629_; 
v_reuseFailAlloc_3629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3629_, 0, v_a_3623_);
v___x_3628_ = v_reuseFailAlloc_3629_;
goto v_reusejp_3627_;
}
v_reusejp_3627_:
{
return v___x_3628_;
}
}
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_del_object(v___x_3609_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3631_ = lean_ctor_get(v___x_3614_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3614_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3614_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3614_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v___x_3636_; 
if (v_isShared_3634_ == 0)
{
v___x_3636_ = v___x_3633_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_a_3631_);
v___x_3636_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
return v___x_3636_;
}
}
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_del_object(v___x_3609_);
lean_dec(v_val_3607_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3639_ = lean_ctor_get(v___x_3611_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3611_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3611_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3611_);
v___x_3641_ = lean_box(0);
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
v_resetjp_3640_:
{
lean_object* v___x_3644_; 
if (v_isShared_3642_ == 0)
{
v___x_3644_ = v___x_3641_;
goto v_reusejp_3643_;
}
else
{
lean_object* v_reuseFailAlloc_3645_; 
v_reuseFailAlloc_3645_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_a_3639_);
v___x_3644_ = v_reuseFailAlloc_3645_;
goto v_reusejp_3643_;
}
v_reusejp_3643_:
{
return v___x_3644_;
}
}
}
}
}
else
{
lean_object* v___x_3648_; 
lean_dec(v_a_3606_);
lean_inc_ref(v___x_3290_);
v___x_3648_ = l_Lean_Meta_matchNe_x3f(v___x_3290_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3648_) == 0)
{
lean_object* v_a_3649_; 
v_a_3649_ = lean_ctor_get(v___x_3648_, 0);
lean_inc(v_a_3649_);
lean_dec_ref_known(v___x_3648_, 1);
if (lean_obj_tag(v_a_3649_) == 1)
{
lean_object* v_val_3650_; lean_object* v___x_3652_; uint8_t v_isShared_3653_; uint8_t v_isSharedCheck_3720_; 
v_val_3650_ = lean_ctor_get(v_a_3649_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v_a_3649_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3652_ = v_a_3649_;
v_isShared_3653_ = v_isSharedCheck_3720_;
goto v_resetjp_3651_;
}
else
{
lean_inc(v_val_3650_);
lean_dec(v_a_3649_);
v___x_3652_ = lean_box(0);
v_isShared_3653_ = v_isSharedCheck_3720_;
goto v_resetjp_3651_;
}
v_resetjp_3651_:
{
lean_object* v_snd_3654_; lean_object* v_fst_3655_; lean_object* v_snd_3656_; lean_object* v___x_3658_; uint8_t v_isShared_3659_; uint8_t v_isSharedCheck_3719_; 
v_snd_3654_ = lean_ctor_get(v_val_3650_, 1);
lean_inc(v_snd_3654_);
lean_dec(v_val_3650_);
v_fst_3655_ = lean_ctor_get(v_snd_3654_, 0);
v_snd_3656_ = lean_ctor_get(v_snd_3654_, 1);
v_isSharedCheck_3719_ = !lean_is_exclusive(v_snd_3654_);
if (v_isSharedCheck_3719_ == 0)
{
v___x_3658_ = v_snd_3654_;
v_isShared_3659_ = v_isSharedCheck_3719_;
goto v_resetjp_3657_;
}
else
{
lean_inc(v_snd_3656_);
lean_inc(v_fst_3655_);
lean_dec(v_snd_3654_);
v___x_3658_ = lean_box(0);
v_isShared_3659_ = v_isSharedCheck_3719_;
goto v_resetjp_3657_;
}
v_resetjp_3657_:
{
lean_object* v___x_3660_; 
lean_inc(v_fst_3655_);
v___x_3660_ = l_Lean_Meta_isExprDefEq(v_fst_3655_, v_snd_3656_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3660_) == 0)
{
lean_object* v_a_3661_; uint8_t v___x_3662_; 
v_a_3661_ = lean_ctor_get(v___x_3660_, 0);
lean_inc(v_a_3661_);
lean_dec_ref_known(v___x_3660_, 1);
v___x_3662_ = lean_unbox(v_a_3661_);
lean_dec(v_a_3661_);
if (v___x_3662_ == 0)
{
lean_del_object(v___x_3658_);
lean_dec(v_fst_3655_);
lean_del_object(v___x_3652_);
v___y_3555_ = v___y_3601_;
v___y_3556_ = v___y_3602_;
v___y_3557_ = v___y_3603_;
v___y_3558_ = v___y_3604_;
goto v___jp_3554_;
}
else
{
lean_object* v___x_3663_; 
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec_ref(v_config_3138_);
lean_inc(v_mvarId_3139_);
v___x_3663_ = l_Lean_MVarId_getType(v_mvarId_3139_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v_a_3664_; lean_object* v___x_3665_; 
v_a_3664_ = lean_ctor_get(v___x_3663_, 0);
lean_inc(v_a_3664_);
lean_dec_ref_known(v___x_3663_, 1);
v___x_3665_ = l_Lean_Meta_mkEqRefl(v_fst_3655_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3665_, 1);
v___x_3667_ = l_Lean_LocalDecl_toExpr(v_val_3170_);
v___x_3668_ = l_Lean_Meta_mkAbsurd(v_a_3664_, v_a_3666_, v___x_3667_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3668_) == 0)
{
lean_object* v_a_3669_; lean_object* v___x_3670_; 
v_a_3669_ = lean_ctor_get(v___x_3668_, 0);
lean_inc(v_a_3669_);
lean_dec_ref_known(v___x_3668_, 1);
v___x_3670_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3139_, v_a_3669_, v___y_3602_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v___x_3671_; lean_object* v___x_3673_; 
lean_dec_ref_known(v___x_3670_, 1);
v___x_3671_ = lean_box(v___x_3149_);
if (v_isShared_3653_ == 0)
{
lean_ctor_set(v___x_3652_, 0, v___x_3671_);
v___x_3673_ = v___x_3652_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3671_);
v___x_3673_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
lean_object* v___x_3675_; 
if (v_isShared_3659_ == 0)
{
lean_ctor_set(v___x_3658_, 1, v___x_3174_);
lean_ctor_set(v___x_3658_, 0, v___x_3673_);
v___x_3675_ = v___x_3658_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v___x_3174_);
v___x_3675_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3676_; 
v___x_3676_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3675_);
v_a_3156_ = v___x_3676_;
goto v___jp_3155_;
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_del_object(v___x_3658_);
lean_del_object(v___x_3652_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
v_a_3679_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3670_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3670_);
v___x_3681_ = lean_box(0);
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
v_resetjp_3680_:
{
lean_object* v___x_3684_; 
if (v_isShared_3682_ == 0)
{
v___x_3684_ = v___x_3681_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v_a_3679_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v___x_3689_; uint8_t v_isShared_3690_; uint8_t v_isSharedCheck_3694_; 
lean_del_object(v___x_3658_);
lean_del_object(v___x_3652_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3687_ = lean_ctor_get(v___x_3668_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3668_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3668_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3668_);
v___x_3689_ = lean_box(0);
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
v_resetjp_3688_:
{
lean_object* v___x_3692_; 
if (v_isShared_3690_ == 0)
{
v___x_3692_ = v___x_3689_;
goto v_reusejp_3691_;
}
else
{
lean_object* v_reuseFailAlloc_3693_; 
v_reuseFailAlloc_3693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3693_, 0, v_a_3687_);
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
else
{
lean_object* v_a_3695_; lean_object* v___x_3697_; uint8_t v_isShared_3698_; uint8_t v_isSharedCheck_3702_; 
lean_dec(v_a_3664_);
lean_del_object(v___x_3658_);
lean_del_object(v___x_3652_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3695_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3702_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3702_ == 0)
{
v___x_3697_ = v___x_3665_;
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
else
{
lean_inc(v_a_3695_);
lean_dec(v___x_3665_);
v___x_3697_ = lean_box(0);
v_isShared_3698_ = v_isSharedCheck_3702_;
goto v_resetjp_3696_;
}
v_resetjp_3696_:
{
lean_object* v___x_3700_; 
if (v_isShared_3698_ == 0)
{
v___x_3700_ = v___x_3697_;
goto v_reusejp_3699_;
}
else
{
lean_object* v_reuseFailAlloc_3701_; 
v_reuseFailAlloc_3701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3701_, 0, v_a_3695_);
v___x_3700_ = v_reuseFailAlloc_3701_;
goto v_reusejp_3699_;
}
v_reusejp_3699_:
{
return v___x_3700_;
}
}
}
}
else
{
lean_object* v_a_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3710_; 
lean_del_object(v___x_3658_);
lean_dec(v_fst_3655_);
lean_del_object(v___x_3652_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3703_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3710_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3710_ == 0)
{
v___x_3705_ = v___x_3663_;
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_a_3703_);
lean_dec(v___x_3663_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3710_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3708_; 
if (v_isShared_3706_ == 0)
{
v___x_3708_ = v___x_3705_;
goto v_reusejp_3707_;
}
else
{
lean_object* v_reuseFailAlloc_3709_; 
v_reuseFailAlloc_3709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3709_, 0, v_a_3703_);
v___x_3708_ = v_reuseFailAlloc_3709_;
goto v_reusejp_3707_;
}
v_reusejp_3707_:
{
return v___x_3708_;
}
}
}
}
}
else
{
lean_object* v_a_3711_; lean_object* v___x_3713_; uint8_t v_isShared_3714_; uint8_t v_isSharedCheck_3718_; 
lean_del_object(v___x_3658_);
lean_dec(v_fst_3655_);
lean_del_object(v___x_3652_);
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3711_ = lean_ctor_get(v___x_3660_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v___x_3660_);
if (v_isSharedCheck_3718_ == 0)
{
v___x_3713_ = v___x_3660_;
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
else
{
lean_inc(v_a_3711_);
lean_dec(v___x_3660_);
v___x_3713_ = lean_box(0);
v_isShared_3714_ = v_isSharedCheck_3718_;
goto v_resetjp_3712_;
}
v_resetjp_3712_:
{
lean_object* v___x_3716_; 
if (v_isShared_3714_ == 0)
{
v___x_3716_ = v___x_3713_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v_a_3711_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3649_);
v___y_3555_ = v___y_3601_;
v___y_3556_ = v___y_3602_;
v___y_3557_ = v___y_3603_;
v___y_3558_ = v___y_3604_;
goto v___jp_3554_;
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3721_ = lean_ctor_get(v___x_3648_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3648_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3648_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3648_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
lean_dec_ref(v___x_3290_);
lean_del_object(v___x_3172_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3729_ = lean_ctor_get(v___x_3605_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3605_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3605_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3605_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
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
}
else
{
lean_del_object(v___x_3172_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
v_a_3164_ = v___x_3216_;
goto v___jp_3163_;
}
v___jp_3175_:
{
lean_object* v___x_3180_; 
lean_inc(v_mvarId_3139_);
v___x_3180_ = l_Lean_MVarId_getType(v_mvarId_3139_, v___y_3178_, v___y_3179_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3180_) == 0)
{
lean_object* v_a_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; 
v_a_3181_ = lean_ctor_get(v___x_3180_, 0);
lean_inc(v_a_3181_);
lean_dec_ref_known(v___x_3180_, 1);
v___x_3182_ = l_Lean_LocalDecl_toExpr(v_val_3170_);
v___x_3183_ = l_Lean_Meta_mkNoConfusion(v_a_3181_, v___x_3182_, v___y_3178_, v___y_3179_, v___y_3176_, v___y_3177_);
if (lean_obj_tag(v___x_3183_) == 0)
{
lean_object* v_a_3184_; lean_object* v___x_3185_; 
v_a_3184_ = lean_ctor_get(v___x_3183_, 0);
lean_inc(v_a_3184_);
lean_dec_ref_known(v___x_3183_, 1);
v___x_3185_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3139_, v_a_3184_, v___y_3179_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3188_; 
lean_dec_ref_known(v___x_3185_, 1);
v___x_3186_ = lean_box(v___x_3149_);
if (v_isShared_3173_ == 0)
{
lean_ctor_set(v___x_3172_, 0, v___x_3186_);
v___x_3188_ = v___x_3172_;
goto v_reusejp_3187_;
}
else
{
lean_object* v_reuseFailAlloc_3191_; 
v_reuseFailAlloc_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3191_, 0, v___x_3186_);
v___x_3188_ = v_reuseFailAlloc_3191_;
goto v_reusejp_3187_;
}
v_reusejp_3187_:
{
lean_object* v___x_3189_; lean_object* v___x_3190_; 
v___x_3189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3189_, 0, v___x_3188_);
lean_ctor_set(v___x_3189_, 1, v___x_3174_);
v___x_3190_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3189_);
v_a_3156_ = v___x_3190_;
goto v___jp_3155_;
}
}
else
{
lean_object* v_a_3192_; lean_object* v___x_3194_; uint8_t v_isShared_3195_; uint8_t v_isSharedCheck_3199_; 
lean_del_object(v___x_3172_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
v_a_3192_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3199_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3199_ == 0)
{
v___x_3194_ = v___x_3185_;
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
else
{
lean_inc(v_a_3192_);
lean_dec(v___x_3185_);
v___x_3194_ = lean_box(0);
v_isShared_3195_ = v_isSharedCheck_3199_;
goto v_resetjp_3193_;
}
v_resetjp_3193_:
{
lean_object* v___x_3197_; 
if (v_isShared_3195_ == 0)
{
v___x_3197_ = v___x_3194_;
goto v_reusejp_3196_;
}
else
{
lean_object* v_reuseFailAlloc_3198_; 
v_reuseFailAlloc_3198_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3198_, 0, v_a_3192_);
v___x_3197_ = v_reuseFailAlloc_3198_;
goto v_reusejp_3196_;
}
v_reusejp_3196_:
{
return v___x_3197_;
}
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_del_object(v___x_3172_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3200_ = lean_ctor_get(v___x_3183_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3183_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3183_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3183_);
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
else
{
lean_object* v_a_3208_; lean_object* v___x_3210_; uint8_t v_isShared_3211_; uint8_t v_isSharedCheck_3215_; 
lean_del_object(v___x_3172_);
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
v_a_3208_ = lean_ctor_get(v___x_3180_, 0);
v_isSharedCheck_3215_ = !lean_is_exclusive(v___x_3180_);
if (v_isSharedCheck_3215_ == 0)
{
v___x_3210_ = v___x_3180_;
v_isShared_3211_ = v_isSharedCheck_3215_;
goto v_resetjp_3209_;
}
else
{
lean_inc(v_a_3208_);
lean_dec(v___x_3180_);
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
v___jp_3217_:
{
lean_object* v_searchFuel_3222_; lean_object* v___x_3223_; lean_object* v___x_3224_; 
v_searchFuel_3222_ = lean_ctor_get(v_config_3138_, 0);
v___x_3223_ = l_Lean_LocalDecl_fvarId(v_val_3170_);
lean_dec(v_val_3170_);
lean_inc(v_searchFuel_3222_);
lean_inc(v_mvarId_3139_);
v___x_3224_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3139_, v___x_3223_, v_searchFuel_3222_, v___y_3218_, v___y_3221_, v___y_3219_, v___y_3220_);
if (lean_obj_tag(v___x_3224_) == 0)
{
lean_object* v_a_3225_; uint8_t v___x_3226_; 
v_a_3225_ = lean_ctor_get(v___x_3224_, 0);
lean_inc(v_a_3225_);
lean_dec_ref_known(v___x_3224_, 1);
v___x_3226_ = lean_unbox(v_a_3225_);
lean_dec(v_a_3225_);
if (v___x_3226_ == 0)
{
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
v_a_3164_ = v___x_3216_;
goto v___jp_3163_;
}
else
{
lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; 
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v___x_3227_ = lean_box(v___x_3149_);
v___x_3228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3228_, 0, v___x_3227_);
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3228_);
lean_ctor_set(v___x_3229_, 1, v___x_3174_);
v___x_3230_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
v_a_3156_ = v___x_3230_;
goto v___jp_3155_;
}
}
else
{
lean_object* v_a_3231_; lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3238_; 
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3231_ = lean_ctor_get(v___x_3224_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3224_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3233_ = v___x_3224_;
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
else
{
lean_inc(v_a_3231_);
lean_dec(v___x_3224_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3238_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3236_; 
if (v_isShared_3234_ == 0)
{
v___x_3236_ = v___x_3233_;
goto v_reusejp_3235_;
}
else
{
lean_object* v_reuseFailAlloc_3237_; 
v_reuseFailAlloc_3237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3237_, 0, v_a_3231_);
v___x_3236_ = v_reuseFailAlloc_3237_;
goto v_reusejp_3235_;
}
v_reusejp_3235_:
{
return v___x_3236_;
}
}
}
}
v___jp_3239_:
{
if (v___y_3244_ == 0)
{
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
v_a_3164_ = v___x_3216_;
goto v___jp_3163_;
}
else
{
v___y_3218_ = v___y_3240_;
v___y_3219_ = v___y_3241_;
v___y_3220_ = v___y_3242_;
v___y_3221_ = v___y_3243_;
goto v___jp_3217_;
}
}
v___jp_3246_:
{
if (v___y_3250_ == 0)
{
v___y_3218_ = v___y_3247_;
v___y_3219_ = v___y_3248_;
v___y_3220_ = v___y_3249_;
v___y_3221_ = v___y_3251_;
goto v___jp_3217_;
}
else
{
v___y_3240_ = v___y_3247_;
v___y_3241_ = v___y_3248_;
v___y_3242_ = v___y_3249_;
v___y_3243_ = v___y_3251_;
v___y_3244_ = v___x_3245_;
goto v___jp_3239_;
}
}
v___jp_3252_:
{
if (v___y_3258_ == 0)
{
v___y_3240_ = v___y_3253_;
v___y_3241_ = v___y_3254_;
v___y_3242_ = v___y_3256_;
v___y_3243_ = v___y_3257_;
v___y_3244_ = v___x_3245_;
goto v___jp_3239_;
}
else
{
v___y_3247_ = v___y_3253_;
v___y_3248_ = v___y_3254_;
v___y_3249_ = v___y_3256_;
v___y_3250_ = v___y_3255_;
v___y_3251_ = v___y_3257_;
goto v___jp_3246_;
}
}
v___jp_3259_:
{
uint8_t v_emptyType_3266_; 
v_emptyType_3266_ = lean_ctor_get_uint8(v_config_3138_, sizeof(void*)*1 + 1);
if (v_emptyType_3266_ == 0)
{
v___y_3253_ = v___y_3262_;
v___y_3254_ = v___y_3264_;
v___y_3255_ = v___y_3260_;
v___y_3256_ = v___y_3265_;
v___y_3257_ = v___y_3263_;
v___y_3258_ = v___x_3245_;
goto v___jp_3252_;
}
else
{
if (v___y_3261_ == 0)
{
v___y_3247_ = v___y_3262_;
v___y_3248_ = v___y_3264_;
v___y_3249_ = v___y_3265_;
v___y_3250_ = v___y_3260_;
v___y_3251_ = v___y_3263_;
goto v___jp_3246_;
}
else
{
v___y_3253_ = v___y_3262_;
v___y_3254_ = v___y_3264_;
v___y_3255_ = v___y_3260_;
v___y_3256_ = v___y_3265_;
v___y_3257_ = v___y_3263_;
v___y_3258_ = v___x_3245_;
goto v___jp_3252_;
}
}
}
v___jp_3267_:
{
if (v___y_3274_ == 0)
{
v___y_3260_ = v___y_3269_;
v___y_3261_ = v___y_3271_;
v___y_3262_ = v___y_3270_;
v___y_3263_ = v___y_3273_;
v___y_3264_ = v___y_3268_;
v___y_3265_ = v___y_3272_;
goto v___jp_3259_;
}
else
{
lean_object* v___x_3275_; 
lean_inc(v_val_3170_);
lean_inc(v_mvarId_3139_);
v___x_3275_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3139_, v_val_3170_, v___y_3270_, v___y_3273_, v___y_3268_, v___y_3272_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v_a_3276_; uint8_t v___x_3277_; 
v_a_3276_ = lean_ctor_get(v___x_3275_, 0);
lean_inc(v_a_3276_);
lean_dec_ref_known(v___x_3275_, 1);
v___x_3277_ = lean_unbox(v_a_3276_);
lean_dec(v_a_3276_);
if (v___x_3277_ == 0)
{
v___y_3260_ = v___y_3269_;
v___y_3261_ = v___y_3271_;
v___y_3262_ = v___y_3270_;
v___y_3263_ = v___y_3273_;
v___y_3264_ = v___y_3268_;
v___y_3265_ = v___y_3272_;
goto v___jp_3259_;
}
else
{
lean_object* v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
lean_dec(v_val_3170_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v___x_3278_ = lean_box(v___x_3149_);
v___x_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
v___x_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3280_, 0, v___x_3279_);
lean_ctor_set(v___x_3280_, 1, v___x_3174_);
v___x_3281_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
v_a_3156_ = v___x_3281_;
goto v___jp_3155_;
}
}
else
{
lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3289_; 
lean_dec(v_val_3170_);
lean_del_object(v___x_3153_);
lean_dec(v_snd_3151_);
lean_dec(v_mvarId_3139_);
lean_dec_ref(v_config_3138_);
v_a_3282_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3289_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3289_ == 0)
{
v___x_3284_ = v___x_3275_;
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_dec(v___x_3275_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3289_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3287_; 
if (v_isShared_3285_ == 0)
{
v___x_3287_ = v___x_3284_;
goto v_reusejp_3286_;
}
else
{
lean_object* v_reuseFailAlloc_3288_; 
v_reuseFailAlloc_3288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3288_, 0, v_a_3282_);
v___x_3287_ = v_reuseFailAlloc_3288_;
goto v_reusejp_3286_;
}
v_reusejp_3286_:
{
return v___x_3287_;
}
}
}
}
}
}
}
v___jp_3155_:
{
lean_object* v___x_3157_; lean_object* v___x_3159_; 
v___x_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3157_, 0, v_a_3156_);
if (v_isShared_3154_ == 0)
{
lean_ctor_set(v___x_3153_, 0, v___x_3157_);
v___x_3159_ = v___x_3153_;
goto v_reusejp_3158_;
}
else
{
lean_object* v_reuseFailAlloc_3161_; 
v_reuseFailAlloc_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3161_, 0, v___x_3157_);
lean_ctor_set(v_reuseFailAlloc_3161_, 1, v_snd_3151_);
v___x_3159_ = v_reuseFailAlloc_3161_;
goto v_reusejp_3158_;
}
v_reusejp_3158_:
{
lean_object* v___x_3160_; 
v___x_3160_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3160_, 0, v___x_3159_);
return v___x_3160_;
}
}
v___jp_3163_:
{
lean_object* v___x_3165_; size_t v___x_3166_; size_t v___x_3167_; 
v___x_3165_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3165_, 0, v___x_3162_);
lean_ctor_set(v___x_3165_, 1, v_a_3164_);
v___x_3166_ = ((size_t)1ULL);
v___x_3167_ = lean_usize_add(v_i_3142_, v___x_3166_);
v_i_3142_ = v___x_3167_;
v_b_3143_ = v___x_3165_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3810_, lean_object* v_mvarId_3811_, lean_object* v_as_3812_, lean_object* v_sz_3813_, lean_object* v_i_3814_, lean_object* v_b_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_){
_start:
{
size_t v_sz_boxed_3821_; size_t v_i_boxed_3822_; lean_object* v_res_3823_; 
v_sz_boxed_3821_ = lean_unbox_usize(v_sz_3813_);
lean_dec(v_sz_3813_);
v_i_boxed_3822_ = lean_unbox_usize(v_i_3814_);
lean_dec(v_i_3814_);
v_res_3823_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3810_, v_mvarId_3811_, v_as_3812_, v_sz_boxed_3821_, v_i_boxed_3822_, v_b_3815_, v___y_3816_, v___y_3817_, v___y_3818_, v___y_3819_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec(v___y_3817_);
lean_dec_ref(v___y_3816_);
lean_dec_ref(v_as_3812_);
return v_res_3823_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3824_, lean_object* v_mvarId_3825_, lean_object* v_as_3826_, size_t v_sz_3827_, size_t v_i_3828_, lean_object* v_b_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_){
_start:
{
uint8_t v___x_3835_; 
v___x_3835_ = lean_usize_dec_lt(v_i_3828_, v_sz_3827_);
if (v___x_3835_ == 0)
{
lean_object* v___x_3836_; 
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v___x_3836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3836_, 0, v_b_3829_);
return v___x_3836_;
}
else
{
lean_object* v_snd_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_4494_; 
v_snd_3837_ = lean_ctor_get(v_b_3829_, 1);
v_isSharedCheck_4494_ = !lean_is_exclusive(v_b_3829_);
if (v_isSharedCheck_4494_ == 0)
{
lean_object* v_unused_4495_; 
v_unused_4495_ = lean_ctor_get(v_b_3829_, 0);
lean_dec(v_unused_4495_);
v___x_3839_ = v_b_3829_;
v_isShared_3840_ = v_isSharedCheck_4494_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_snd_3837_);
lean_dec(v_b_3829_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_4494_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v_a_3842_; lean_object* v___x_3848_; lean_object* v_a_3850_; lean_object* v_a_3855_; 
v___x_3848_ = lean_box(0);
v_a_3855_ = lean_array_uget(v_as_3826_, v_i_3828_);
if (lean_obj_tag(v_a_3855_) == 0)
{
lean_del_object(v___x_3839_);
v_a_3850_ = v_snd_3837_;
goto v___jp_3849_;
}
else
{
lean_object* v_val_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_4493_; 
v_val_3856_ = lean_ctor_get(v_a_3855_, 0);
v_isSharedCheck_4493_ = !lean_is_exclusive(v_a_3855_);
if (v_isSharedCheck_4493_ == 0)
{
v___x_3858_ = v_a_3855_;
v_isShared_3859_ = v_isSharedCheck_4493_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_val_3856_);
lean_dec(v_a_3855_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_4493_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3860_; lean_object* v___y_3862_; lean_object* v___y_3863_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___x_3902_; lean_object* v___y_3904_; lean_object* v___y_3905_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3926_; lean_object* v___y_3927_; lean_object* v___y_3928_; lean_object* v___y_3929_; uint8_t v___y_3930_; uint8_t v___x_3931_; lean_object* v___y_3933_; lean_object* v___y_3934_; lean_object* v___y_3935_; uint8_t v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3939_; lean_object* v___y_3940_; lean_object* v___y_3941_; uint8_t v___y_3942_; lean_object* v___y_3943_; uint8_t v___y_3944_; uint8_t v___y_3946_; uint8_t v___y_3947_; lean_object* v___y_3948_; lean_object* v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3954_; lean_object* v___y_3955_; uint8_t v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; uint8_t v___y_3959_; uint8_t v___y_3960_; 
v___x_3860_ = lean_box(0);
v___x_3902_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3931_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3856_);
if (v___x_3931_ == 0)
{
lean_object* v___x_3976_; uint8_t v___y_3978_; uint8_t v___y_3979_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3987_; lean_object* v___y_3988_; uint8_t v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; uint8_t v___y_3993_; uint8_t v___y_3994_; lean_object* v___y_3997_; uint8_t v___y_3998_; lean_object* v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; uint8_t v___y_4002_; lean_object* v_a_4003_; lean_object* v___y_4007_; uint8_t v___y_4008_; lean_object* v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; uint8_t v___y_4012_; lean_object* v___y_4074_; uint8_t v___y_4075_; lean_object* v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; uint8_t v___y_4079_; uint8_t v___y_4080_; lean_object* v___y_4082_; lean_object* v___y_4083_; uint8_t v___y_4084_; lean_object* v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; uint8_t v___y_4088_; uint8_t v___y_4089_; lean_object* v___y_4092_; uint8_t v___y_4093_; lean_object* v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; uint8_t v___y_4097_; uint8_t v___y_4098_; lean_object* v___y_4111_; uint8_t v___y_4112_; lean_object* v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; uint8_t v___y_4116_; uint8_t v___y_4117_; uint8_t v___y_4119_; uint8_t v_isHEq_4120_; lean_object* v___y_4121_; lean_object* v___y_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4128_; lean_object* v___y_4129_; lean_object* v___y_4130_; uint8_t v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; uint8_t v_isEq_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4241_; lean_object* v___y_4242_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4287_; lean_object* v___y_4288_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___x_4423_; 
v___x_3976_ = l_Lean_LocalDecl_type(v_val_3856_);
lean_inc_ref(v___x_3976_);
v___x_4423_ = l_Lean_Meta_matchNot_x3f(v___x_3976_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_object* v_a_4424_; 
v_a_4424_ = lean_ctor_get(v___x_4423_, 0);
lean_inc(v_a_4424_);
lean_dec_ref_known(v___x_4423_, 1);
if (lean_obj_tag(v_a_4424_) == 1)
{
lean_object* v_val_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4484_; 
v_val_4425_ = lean_ctor_get(v_a_4424_, 0);
v_isSharedCheck_4484_ = !lean_is_exclusive(v_a_4424_);
if (v_isSharedCheck_4484_ == 0)
{
v___x_4427_ = v_a_4424_;
v_isShared_4428_ = v_isSharedCheck_4484_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_val_4425_);
lean_dec(v_a_4424_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4484_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4429_; 
v___x_4429_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4425_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_4429_) == 0)
{
lean_object* v_a_4430_; 
v_a_4430_ = lean_ctor_get(v___x_4429_, 0);
lean_inc(v_a_4430_);
lean_dec_ref_known(v___x_4429_, 1);
if (lean_obj_tag(v_a_4430_) == 1)
{
lean_object* v_val_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4475_; 
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec_ref(v_config_3824_);
v_val_4431_ = lean_ctor_get(v_a_4430_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v_a_4430_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4433_ = v_a_4430_;
v_isShared_4434_ = v_isSharedCheck_4475_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_val_4431_);
lean_dec(v_a_4430_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4475_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4435_; 
lean_inc(v_mvarId_3825_);
v___x_4435_ = l_Lean_MVarId_getType(v_mvarId_3825_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_4435_) == 0)
{
lean_object* v_a_4436_; lean_object* v___x_4437_; lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; 
v_a_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc(v_a_4436_);
lean_dec_ref_known(v___x_4435_, 1);
v___x_4437_ = l_Lean_LocalDecl_toExpr(v_val_3856_);
v___x_4438_ = l_Lean_mkFVar(v_val_4431_);
v___x_4439_ = l_Lean_Expr_app___override(v___x_4437_, v___x_4438_);
v___x_4440_ = l_Lean_Meta_mkFalseElim(v_a_4436_, v___x_4439_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; lean_object* v___x_4442_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref_known(v___x_4440_, 1);
v___x_4442_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3825_, v_a_4441_, v___y_3831_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v___x_4443_; lean_object* v___x_4445_; 
lean_dec_ref_known(v___x_4442_, 1);
v___x_4443_ = lean_box(v___x_3835_);
if (v_isShared_4434_ == 0)
{
lean_ctor_set(v___x_4433_, 0, v___x_4443_);
v___x_4445_ = v___x_4433_;
goto v_reusejp_4444_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v___x_4443_);
v___x_4445_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4444_;
}
v_reusejp_4444_:
{
lean_object* v___x_4446_; lean_object* v___x_4448_; 
v___x_4446_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4446_, 0, v___x_4445_);
lean_ctor_set(v___x_4446_, 1, v___x_3860_);
if (v_isShared_4428_ == 0)
{
lean_ctor_set_tag(v___x_4427_, 0);
lean_ctor_set(v___x_4427_, 0, v___x_4446_);
v___x_4448_ = v___x_4427_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
v_a_3842_ = v___x_4448_;
goto v___jp_3841_;
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_del_object(v___x_4433_);
lean_del_object(v___x_4427_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
v_a_4451_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4442_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4442_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
else
{
lean_object* v_a_4459_; lean_object* v___x_4461_; uint8_t v_isShared_4462_; uint8_t v_isSharedCheck_4466_; 
lean_del_object(v___x_4433_);
lean_del_object(v___x_4427_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_4459_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4461_ = v___x_4440_;
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
else
{
lean_inc(v_a_4459_);
lean_dec(v___x_4440_);
v___x_4461_ = lean_box(0);
v_isShared_4462_ = v_isSharedCheck_4466_;
goto v_resetjp_4460_;
}
v_resetjp_4460_:
{
lean_object* v___x_4464_; 
if (v_isShared_4462_ == 0)
{
v___x_4464_ = v___x_4461_;
goto v_reusejp_4463_;
}
else
{
lean_object* v_reuseFailAlloc_4465_; 
v_reuseFailAlloc_4465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4465_, 0, v_a_4459_);
v___x_4464_ = v_reuseFailAlloc_4465_;
goto v_reusejp_4463_;
}
v_reusejp_4463_:
{
return v___x_4464_;
}
}
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_del_object(v___x_4433_);
lean_dec(v_val_4431_);
lean_del_object(v___x_4427_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_4467_ = lean_ctor_get(v___x_4435_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4435_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4435_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4435_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4472_; 
if (v_isShared_4470_ == 0)
{
v___x_4472_ = v___x_4469_;
goto v_reusejp_4471_;
}
else
{
lean_object* v_reuseFailAlloc_4473_; 
v_reuseFailAlloc_4473_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4473_, 0, v_a_4467_);
v___x_4472_ = v_reuseFailAlloc_4473_;
goto v_reusejp_4471_;
}
v_reusejp_4471_:
{
return v___x_4472_;
}
}
}
}
}
else
{
lean_dec(v_a_4430_);
lean_del_object(v___x_4427_);
v___y_4287_ = v___y_3830_;
v___y_4288_ = v___y_3831_;
v___y_4289_ = v___y_3832_;
v___y_4290_ = v___y_3833_;
goto v___jp_4286_;
}
}
else
{
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_del_object(v___x_4427_);
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4476_ = lean_ctor_get(v___x_4429_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4429_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4429_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4429_);
v___x_4478_ = lean_box(0);
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
v_resetjp_4477_:
{
lean_object* v___x_4481_; 
if (v_isShared_4479_ == 0)
{
v___x_4481_ = v___x_4478_;
goto v_reusejp_4480_;
}
else
{
lean_object* v_reuseFailAlloc_4482_; 
v_reuseFailAlloc_4482_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4482_, 0, v_a_4476_);
v___x_4481_ = v_reuseFailAlloc_4482_;
goto v_reusejp_4480_;
}
v_reusejp_4480_:
{
return v___x_4481_;
}
}
}
}
}
else
{
lean_dec(v_a_4424_);
v___y_4287_ = v___y_3830_;
v___y_4288_ = v___y_3831_;
v___y_4289_ = v___y_3832_;
v___y_4290_ = v___y_3833_;
goto v___jp_4286_;
}
}
else
{
lean_object* v_a_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4492_; 
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4485_ = lean_ctor_get(v___x_4423_, 0);
v_isSharedCheck_4492_ = !lean_is_exclusive(v___x_4423_);
if (v_isSharedCheck_4492_ == 0)
{
v___x_4487_ = v___x_4423_;
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_a_4485_);
lean_dec(v___x_4423_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4492_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4490_; 
if (v_isShared_4488_ == 0)
{
v___x_4490_ = v___x_4487_;
goto v_reusejp_4489_;
}
else
{
lean_object* v_reuseFailAlloc_4491_; 
v_reuseFailAlloc_4491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4491_, 0, v_a_4485_);
v___x_4490_ = v_reuseFailAlloc_4491_;
goto v_reusejp_4489_;
}
v_reusejp_4489_:
{
return v___x_4490_;
}
}
}
v___jp_3977_:
{
uint8_t v_genDiseq_3984_; 
v_genDiseq_3984_ = lean_ctor_get_uint8(v_config_3824_, sizeof(void*)*1 + 2);
if (v_genDiseq_3984_ == 0)
{
lean_dec_ref(v___x_3976_);
v___y_3954_ = v___y_3983_;
v___y_3955_ = v___y_3982_;
v___y_3956_ = v___y_3978_;
v___y_3957_ = v___y_3981_;
v___y_3958_ = v___y_3980_;
v___y_3959_ = v___y_3979_;
v___y_3960_ = v___x_3931_;
goto v___jp_3953_;
}
else
{
uint8_t v___x_3985_; 
v___x_3985_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3976_);
v___y_3954_ = v___y_3983_;
v___y_3955_ = v___y_3982_;
v___y_3956_ = v___y_3978_;
v___y_3957_ = v___y_3981_;
v___y_3958_ = v___y_3980_;
v___y_3959_ = v___y_3979_;
v___y_3960_ = v___x_3985_;
goto v___jp_3953_;
}
}
v___jp_3986_:
{
if (v___y_3994_ == 0)
{
lean_dec_ref(v___y_3988_);
v___y_3978_ = v___y_3989_;
v___y_3979_ = v___y_3993_;
v___y_3980_ = v___y_3987_;
v___y_3981_ = v___y_3992_;
v___y_3982_ = v___y_3991_;
v___y_3983_ = v___y_3990_;
goto v___jp_3977_;
}
else
{
lean_object* v___x_3995_; 
lean_dec_ref(v___x_3976_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v___x_3995_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___y_3988_);
return v___x_3995_;
}
}
v___jp_3996_:
{
uint8_t v___x_4004_; 
v___x_4004_ = l_Lean_Exception_isInterrupt(v_a_4003_);
if (v___x_4004_ == 0)
{
uint8_t v___x_4005_; 
lean_inc_ref(v_a_4003_);
v___x_4005_ = l_Lean_Exception_isRuntime(v_a_4003_);
v___y_3987_ = v___y_3997_;
v___y_3988_ = v_a_4003_;
v___y_3989_ = v___y_3998_;
v___y_3990_ = v___y_4001_;
v___y_3991_ = v___y_4000_;
v___y_3992_ = v___y_3999_;
v___y_3993_ = v___y_4002_;
v___y_3994_ = v___x_4005_;
goto v___jp_3986_;
}
else
{
v___y_3987_ = v___y_3997_;
v___y_3988_ = v_a_4003_;
v___y_3989_ = v___y_3998_;
v___y_3990_ = v___y_4001_;
v___y_3991_ = v___y_4000_;
v___y_3992_ = v___y_3999_;
v___y_3993_ = v___y_4002_;
v___y_3994_ = v___x_4004_;
goto v___jp_3986_;
}
}
v___jp_4006_:
{
lean_object* v___x_4013_; 
lean_inc_ref(v___x_3976_);
v___x_4013_ = l_Lean_Meta_mkDecide(v___x_3976_, v___y_4007_, v___y_4011_, v___y_4010_, v___y_4009_);
if (lean_obj_tag(v___x_4013_) == 0)
{
lean_object* v_a_4014_; lean_object* v_keyedConfig_4015_; uint8_t v_trackZetaDelta_4016_; lean_object* v_zetaDeltaSet_4017_; lean_object* v_lctx_4018_; lean_object* v_localInstances_4019_; lean_object* v_defEqCtx_x3f_4020_; lean_object* v_synthPendingDepth_4021_; lean_object* v_customCanUnfoldPredicate_x3f_4022_; uint8_t v_univApprox_4023_; uint8_t v_inTypeClassResolution_4024_; uint8_t v_cacheInferType_4025_; uint8_t v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; 
v_a_4014_ = lean_ctor_get(v___x_4013_, 0);
lean_inc_n(v_a_4014_, 2);
lean_dec_ref_known(v___x_4013_, 1);
v_keyedConfig_4015_ = lean_ctor_get(v___y_4007_, 0);
v_trackZetaDelta_4016_ = lean_ctor_get_uint8(v___y_4007_, sizeof(void*)*7);
v_zetaDeltaSet_4017_ = lean_ctor_get(v___y_4007_, 1);
v_lctx_4018_ = lean_ctor_get(v___y_4007_, 2);
v_localInstances_4019_ = lean_ctor_get(v___y_4007_, 3);
v_defEqCtx_x3f_4020_ = lean_ctor_get(v___y_4007_, 4);
v_synthPendingDepth_4021_ = lean_ctor_get(v___y_4007_, 5);
v_customCanUnfoldPredicate_x3f_4022_ = lean_ctor_get(v___y_4007_, 6);
v_univApprox_4023_ = lean_ctor_get_uint8(v___y_4007_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4024_ = lean_ctor_get_uint8(v___y_4007_, sizeof(void*)*7 + 2);
v_cacheInferType_4025_ = lean_ctor_get_uint8(v___y_4007_, sizeof(void*)*7 + 3);
v___x_4026_ = 1;
lean_inc_ref(v_keyedConfig_4015_);
v___x_4027_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4026_, v_keyedConfig_4015_);
lean_inc(v_customCanUnfoldPredicate_x3f_4022_);
lean_inc(v_synthPendingDepth_4021_);
lean_inc(v_defEqCtx_x3f_4020_);
lean_inc_ref(v_localInstances_4019_);
lean_inc_ref(v_lctx_4018_);
lean_inc(v_zetaDeltaSet_4017_);
v___x_4028_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4028_, 0, v___x_4027_);
lean_ctor_set(v___x_4028_, 1, v_zetaDeltaSet_4017_);
lean_ctor_set(v___x_4028_, 2, v_lctx_4018_);
lean_ctor_set(v___x_4028_, 3, v_localInstances_4019_);
lean_ctor_set(v___x_4028_, 4, v_defEqCtx_x3f_4020_);
lean_ctor_set(v___x_4028_, 5, v_synthPendingDepth_4021_);
lean_ctor_set(v___x_4028_, 6, v_customCanUnfoldPredicate_x3f_4022_);
lean_ctor_set_uint8(v___x_4028_, sizeof(void*)*7, v_trackZetaDelta_4016_);
lean_ctor_set_uint8(v___x_4028_, sizeof(void*)*7 + 1, v_univApprox_4023_);
lean_ctor_set_uint8(v___x_4028_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4024_);
lean_ctor_set_uint8(v___x_4028_, sizeof(void*)*7 + 3, v_cacheInferType_4025_);
lean_inc(v___y_4009_);
lean_inc_ref(v___y_4010_);
lean_inc(v___y_4011_);
v___x_4029_ = lean_whnf(v_a_4014_, v___x_4028_, v___y_4011_, v___y_4010_, v___y_4009_);
if (lean_obj_tag(v___x_4029_) == 0)
{
lean_object* v_a_4030_; lean_object* v___x_4031_; uint8_t v___x_4032_; 
v_a_4030_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4030_);
lean_dec_ref_known(v___x_4029_, 1);
v___x_4031_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_4032_ = l_Lean_Expr_isConstOf(v_a_4030_, v___x_4031_);
lean_dec(v_a_4030_);
if (v___x_4032_ == 0)
{
lean_dec(v_a_4014_);
v___y_3978_ = v___y_4008_;
v___y_3979_ = v___y_4012_;
v___y_3980_ = v___y_4007_;
v___y_3981_ = v___y_4011_;
v___y_3982_ = v___y_4010_;
v___y_3983_ = v___y_4009_;
goto v___jp_3977_;
}
else
{
lean_object* v___x_4033_; 
lean_inc(v_a_4014_);
v___x_4033_ = l_Lean_Meta_mkEqRefl(v_a_4014_, v___y_4007_, v___y_4011_, v___y_4010_, v___y_4009_);
if (lean_obj_tag(v___x_4033_) == 0)
{
lean_object* v_a_4034_; lean_object* v___x_4035_; 
v_a_4034_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4034_);
lean_dec_ref_known(v___x_4033_, 1);
lean_inc(v_mvarId_3825_);
v___x_4035_ = l_Lean_MVarId_getType(v_mvarId_3825_, v___y_4007_, v___y_4011_, v___y_4010_, v___y_4009_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v_nargs_4037_; lean_object* v___x_4038_; lean_object* v_dummy_4039_; lean_object* v___x_4040_; lean_object* v___x_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref_known(v___x_4035_, 1);
v_nargs_4037_ = l_Lean_Expr_getAppNumArgs(v_a_4014_);
v___x_4038_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_4039_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_4037_);
v___x_4040_ = lean_mk_array(v_nargs_4037_, v_dummy_4039_);
v___x_4041_ = lean_unsigned_to_nat(1u);
v___x_4042_ = lean_nat_sub(v_nargs_4037_, v___x_4041_);
lean_dec(v_nargs_4037_);
v___x_4043_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4014_, v___x_4040_, v___x_4042_);
v___x_4044_ = lean_array_push(v___x_4043_, v_a_4034_);
v___x_4045_ = l_Lean_mkAppN(v___x_4038_, v___x_4044_);
lean_dec_ref(v___x_4044_);
lean_inc(v_val_3856_);
v___x_4046_ = l_Lean_LocalDecl_toExpr(v_val_3856_);
v___x_4047_ = l_Lean_Meta_mkAbsurd(v_a_4036_, v___x_4046_, v___x_4045_, v___y_4007_, v___y_4011_, v___y_4010_, v___y_4009_);
if (lean_obj_tag(v___x_4047_) == 0)
{
lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4067_; 
v_a_4048_ = lean_ctor_get(v___x_4047_, 0);
v_isSharedCheck_4067_ = !lean_is_exclusive(v___x_4047_);
if (v_isSharedCheck_4067_ == 0)
{
v___x_4050_ = v___x_4047_;
v_isShared_4051_ = v_isSharedCheck_4067_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_dec(v___x_4047_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4067_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4052_; 
lean_inc(v_mvarId_3825_);
v___x_4052_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3825_, v_a_4048_, v___y_4011_);
if (lean_obj_tag(v___x_4052_) == 0)
{
lean_object* v___x_4054_; uint8_t v_isShared_4055_; uint8_t v_isSharedCheck_4064_; 
lean_dec_ref(v___x_3976_);
lean_dec(v_val_3856_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_isSharedCheck_4064_ = !lean_is_exclusive(v___x_4052_);
if (v_isSharedCheck_4064_ == 0)
{
lean_object* v_unused_4065_; 
v_unused_4065_ = lean_ctor_get(v___x_4052_, 0);
lean_dec(v_unused_4065_);
v___x_4054_ = v___x_4052_;
v_isShared_4055_ = v_isSharedCheck_4064_;
goto v_resetjp_4053_;
}
else
{
lean_dec(v___x_4052_);
v___x_4054_ = lean_box(0);
v_isShared_4055_ = v_isSharedCheck_4064_;
goto v_resetjp_4053_;
}
v_resetjp_4053_:
{
lean_object* v___x_4056_; lean_object* v___x_4058_; 
v___x_4056_ = lean_box(v___x_3835_);
if (v_isShared_4055_ == 0)
{
lean_ctor_set_tag(v___x_4054_, 1);
lean_ctor_set(v___x_4054_, 0, v___x_4056_);
v___x_4058_ = v___x_4054_;
goto v_reusejp_4057_;
}
else
{
lean_object* v_reuseFailAlloc_4063_; 
v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4063_, 0, v___x_4056_);
v___x_4058_ = v_reuseFailAlloc_4063_;
goto v_reusejp_4057_;
}
v_reusejp_4057_:
{
lean_object* v___x_4059_; lean_object* v___x_4061_; 
v___x_4059_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
lean_ctor_set(v___x_4059_, 1, v___x_3860_);
if (v_isShared_4051_ == 0)
{
lean_ctor_set(v___x_4050_, 0, v___x_4059_);
v___x_4061_ = v___x_4050_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4062_; 
v_reuseFailAlloc_4062_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4062_, 0, v___x_4059_);
v___x_4061_ = v_reuseFailAlloc_4062_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
v_a_3842_ = v___x_4061_;
goto v___jp_3841_;
}
}
}
}
else
{
lean_object* v_a_4066_; 
lean_del_object(v___x_4050_);
v_a_4066_ = lean_ctor_get(v___x_4052_, 0);
lean_inc(v_a_4066_);
lean_dec_ref_known(v___x_4052_, 1);
v___y_3997_ = v___y_4007_;
v___y_3998_ = v___y_4008_;
v___y_3999_ = v___y_4011_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4009_;
v___y_4002_ = v___y_4012_;
v_a_4003_ = v_a_4066_;
goto v___jp_3996_;
}
}
}
else
{
lean_object* v_a_4068_; 
v_a_4068_ = lean_ctor_get(v___x_4047_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4047_, 1);
v___y_3997_ = v___y_4007_;
v___y_3998_ = v___y_4008_;
v___y_3999_ = v___y_4011_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4009_;
v___y_4002_ = v___y_4012_;
v_a_4003_ = v_a_4068_;
goto v___jp_3996_;
}
}
else
{
lean_object* v_a_4069_; 
lean_dec(v_a_4034_);
lean_dec(v_a_4014_);
v_a_4069_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4069_);
lean_dec_ref_known(v___x_4035_, 1);
v___y_3997_ = v___y_4007_;
v___y_3998_ = v___y_4008_;
v___y_3999_ = v___y_4011_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4009_;
v___y_4002_ = v___y_4012_;
v_a_4003_ = v_a_4069_;
goto v___jp_3996_;
}
}
else
{
lean_object* v_a_4070_; 
lean_dec(v_a_4014_);
v_a_4070_ = lean_ctor_get(v___x_4033_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4033_, 1);
v___y_3997_ = v___y_4007_;
v___y_3998_ = v___y_4008_;
v___y_3999_ = v___y_4011_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4009_;
v___y_4002_ = v___y_4012_;
v_a_4003_ = v_a_4070_;
goto v___jp_3996_;
}
}
}
else
{
lean_object* v_a_4071_; 
lean_dec(v_a_4014_);
v_a_4071_ = lean_ctor_get(v___x_4029_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4029_, 1);
v___y_3997_ = v___y_4007_;
v___y_3998_ = v___y_4008_;
v___y_3999_ = v___y_4011_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4009_;
v___y_4002_ = v___y_4012_;
v_a_4003_ = v_a_4071_;
goto v___jp_3996_;
}
}
else
{
lean_object* v_a_4072_; 
v_a_4072_ = lean_ctor_get(v___x_4013_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4013_, 1);
v___y_3997_ = v___y_4007_;
v___y_3998_ = v___y_4008_;
v___y_3999_ = v___y_4011_;
v___y_4000_ = v___y_4010_;
v___y_4001_ = v___y_4009_;
v___y_4002_ = v___y_4012_;
v_a_4003_ = v_a_4072_;
goto v___jp_3996_;
}
}
v___jp_4073_:
{
if (v___y_4080_ == 0)
{
v___y_3978_ = v___y_4075_;
v___y_3979_ = v___y_4079_;
v___y_3980_ = v___y_4074_;
v___y_3981_ = v___y_4078_;
v___y_3982_ = v___y_4077_;
v___y_3983_ = v___y_4076_;
goto v___jp_3977_;
}
else
{
v___y_4007_ = v___y_4074_;
v___y_4008_ = v___y_4075_;
v___y_4009_ = v___y_4076_;
v___y_4010_ = v___y_4077_;
v___y_4011_ = v___y_4078_;
v___y_4012_ = v___y_4079_;
goto v___jp_4006_;
}
}
v___jp_4081_:
{
if (v___y_4089_ == 0)
{
lean_dec_ref(v___y_4083_);
v___y_4074_ = v___y_4082_;
v___y_4075_ = v___y_4084_;
v___y_4076_ = v___y_4087_;
v___y_4077_ = v___y_4086_;
v___y_4078_ = v___y_4085_;
v___y_4079_ = v___y_4088_;
v___y_4080_ = v___x_3931_;
goto v___jp_4073_;
}
else
{
uint8_t v___x_4090_; 
v___x_4090_ = l_Lean_Expr_hasFVar(v___y_4083_);
lean_dec_ref(v___y_4083_);
if (v___x_4090_ == 0)
{
v___y_4007_ = v___y_4082_;
v___y_4008_ = v___y_4084_;
v___y_4009_ = v___y_4087_;
v___y_4010_ = v___y_4086_;
v___y_4011_ = v___y_4085_;
v___y_4012_ = v___y_4088_;
goto v___jp_4006_;
}
else
{
v___y_4074_ = v___y_4082_;
v___y_4075_ = v___y_4084_;
v___y_4076_ = v___y_4087_;
v___y_4077_ = v___y_4086_;
v___y_4078_ = v___y_4085_;
v___y_4079_ = v___y_4088_;
v___y_4080_ = v___x_3931_;
goto v___jp_4073_;
}
}
}
v___jp_4091_:
{
lean_object* v___x_4099_; 
lean_inc_ref(v___x_3976_);
v___x_4099_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3976_, v___y_4096_);
if (lean_obj_tag(v___x_4099_) == 0)
{
lean_object* v_a_4100_; uint8_t v___x_4101_; 
v_a_4100_ = lean_ctor_get(v___x_4099_, 0);
lean_inc(v_a_4100_);
lean_dec_ref_known(v___x_4099_, 1);
v___x_4101_ = l_Lean_Expr_hasMVar(v_a_4100_);
if (v___x_4101_ == 0)
{
v___y_4082_ = v___y_4092_;
v___y_4083_ = v_a_4100_;
v___y_4084_ = v___y_4093_;
v___y_4085_ = v___y_4096_;
v___y_4086_ = v___y_4094_;
v___y_4087_ = v___y_4095_;
v___y_4088_ = v___y_4097_;
v___y_4089_ = v___y_4098_;
goto v___jp_4081_;
}
else
{
v___y_4082_ = v___y_4092_;
v___y_4083_ = v_a_4100_;
v___y_4084_ = v___y_4093_;
v___y_4085_ = v___y_4096_;
v___y_4086_ = v___y_4094_;
v___y_4087_ = v___y_4095_;
v___y_4088_ = v___y_4097_;
v___y_4089_ = v___x_3931_;
goto v___jp_4081_;
}
}
else
{
lean_object* v_a_4102_; lean_object* v___x_4104_; uint8_t v_isShared_4105_; uint8_t v_isSharedCheck_4109_; 
lean_dec_ref(v___x_3976_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4102_ = lean_ctor_get(v___x_4099_, 0);
v_isSharedCheck_4109_ = !lean_is_exclusive(v___x_4099_);
if (v_isSharedCheck_4109_ == 0)
{
v___x_4104_ = v___x_4099_;
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
else
{
lean_inc(v_a_4102_);
lean_dec(v___x_4099_);
v___x_4104_ = lean_box(0);
v_isShared_4105_ = v_isSharedCheck_4109_;
goto v_resetjp_4103_;
}
v_resetjp_4103_:
{
lean_object* v___x_4107_; 
if (v_isShared_4105_ == 0)
{
v___x_4107_ = v___x_4104_;
goto v_reusejp_4106_;
}
else
{
lean_object* v_reuseFailAlloc_4108_; 
v_reuseFailAlloc_4108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4108_, 0, v_a_4102_);
v___x_4107_ = v_reuseFailAlloc_4108_;
goto v_reusejp_4106_;
}
v_reusejp_4106_:
{
return v___x_4107_;
}
}
}
}
v___jp_4110_:
{
if (v___y_4117_ == 0)
{
v___y_3978_ = v___y_4112_;
v___y_3979_ = v___y_4116_;
v___y_3980_ = v___y_4111_;
v___y_3981_ = v___y_4115_;
v___y_3982_ = v___y_4114_;
v___y_3983_ = v___y_4113_;
goto v___jp_3977_;
}
else
{
v___y_4092_ = v___y_4111_;
v___y_4093_ = v___y_4112_;
v___y_4094_ = v___y_4114_;
v___y_4095_ = v___y_4113_;
v___y_4096_ = v___y_4115_;
v___y_4097_ = v___y_4116_;
v___y_4098_ = v___y_4117_;
goto v___jp_4091_;
}
}
v___jp_4118_:
{
uint8_t v_useDecide_4125_; 
v_useDecide_4125_ = lean_ctor_get_uint8(v_config_3824_, sizeof(void*)*1);
if (v_useDecide_4125_ == 0)
{
v___y_4111_ = v___y_4121_;
v___y_4112_ = v___y_4119_;
v___y_4113_ = v___y_4124_;
v___y_4114_ = v___y_4123_;
v___y_4115_ = v___y_4122_;
v___y_4116_ = v_isHEq_4120_;
v___y_4117_ = v___x_3931_;
goto v___jp_4110_;
}
else
{
uint8_t v___x_4126_; 
v___x_4126_ = l_Lean_Expr_hasFVar(v___x_3976_);
if (v___x_4126_ == 0)
{
v___y_4092_ = v___y_4121_;
v___y_4093_ = v___y_4119_;
v___y_4094_ = v___y_4123_;
v___y_4095_ = v___y_4124_;
v___y_4096_ = v___y_4122_;
v___y_4097_ = v_isHEq_4120_;
v___y_4098_ = v_useDecide_4125_;
goto v___jp_4091_;
}
else
{
v___y_4111_ = v___y_4121_;
v___y_4112_ = v___y_4119_;
v___y_4113_ = v___y_4124_;
v___y_4114_ = v___y_4123_;
v___y_4115_ = v___y_4122_;
v___y_4116_ = v_isHEq_4120_;
v___y_4117_ = v___x_3931_;
goto v___jp_4110_;
}
}
}
v___jp_4127_:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Lean_Meta_isExprDefEq(v___y_4134_, v___y_4129_, v___y_4130_, v___y_4133_, v___y_4132_, v___y_4128_);
if (lean_obj_tag(v___x_4135_) == 0)
{
lean_object* v_a_4136_; uint8_t v___x_4137_; 
v_a_4136_ = lean_ctor_get(v___x_4135_, 0);
lean_inc(v_a_4136_);
lean_dec_ref_known(v___x_4135_, 1);
v___x_4137_ = lean_unbox(v_a_4136_);
lean_dec(v_a_4136_);
if (v___x_4137_ == 0)
{
v___y_4119_ = v___y_4131_;
v_isHEq_4120_ = v___x_3835_;
v___y_4121_ = v___y_4130_;
v___y_4122_ = v___y_4133_;
v___y_4123_ = v___y_4132_;
v___y_4124_ = v___y_4128_;
goto v___jp_4118_;
}
else
{
lean_object* v___x_4138_; 
lean_dec_ref(v___x_3976_);
lean_dec_ref(v_config_3824_);
lean_inc(v_mvarId_3825_);
v___x_4138_ = l_Lean_MVarId_getType(v_mvarId_3825_, v___y_4130_, v___y_4133_, v___y_4132_, v___y_4128_);
if (lean_obj_tag(v___x_4138_) == 0)
{
lean_object* v_a_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
v_a_4139_ = lean_ctor_get(v___x_4138_, 0);
lean_inc(v_a_4139_);
lean_dec_ref_known(v___x_4138_, 1);
v___x_4140_ = l_Lean_LocalDecl_toExpr(v_val_3856_);
v___x_4141_ = l_Lean_Meta_mkEqOfHEq(v___x_4140_, v___x_3835_, v___y_4130_, v___y_4133_, v___y_4132_, v___y_4128_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; lean_object* v___x_4143_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
v___x_4143_ = l_Lean_Meta_mkNoConfusion(v_a_4139_, v_a_4142_, v___y_4130_, v___y_4133_, v___y_4132_, v___y_4128_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4145_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4143_, 1);
v___x_4145_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3825_, v_a_4144_, v___y_4133_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v___x_4149_; 
lean_dec_ref_known(v___x_4145_, 1);
v___x_4146_ = lean_box(v___x_3835_);
v___x_4147_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4147_, 0, v___x_4146_);
v___x_4148_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4148_, 0, v___x_4147_);
lean_ctor_set(v___x_4148_, 1, v___x_3860_);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
v_a_3842_ = v___x_4149_;
goto v___jp_3841_;
}
else
{
lean_object* v_a_4150_; lean_object* v___x_4152_; uint8_t v_isShared_4153_; uint8_t v_isSharedCheck_4157_; 
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
v_a_4150_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4157_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4157_ == 0)
{
v___x_4152_ = v___x_4145_;
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
else
{
lean_inc(v_a_4150_);
lean_dec(v___x_4145_);
v___x_4152_ = lean_box(0);
v_isShared_4153_ = v_isSharedCheck_4157_;
goto v_resetjp_4151_;
}
v_resetjp_4151_:
{
lean_object* v___x_4155_; 
if (v_isShared_4153_ == 0)
{
v___x_4155_ = v___x_4152_;
goto v_reusejp_4154_;
}
else
{
lean_object* v_reuseFailAlloc_4156_; 
v_reuseFailAlloc_4156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4156_, 0, v_a_4150_);
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
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_4158_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4165_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4165_ == 0)
{
v___x_4160_ = v___x_4143_;
v_isShared_4161_ = v_isSharedCheck_4165_;
goto v_resetjp_4159_;
}
else
{
lean_inc(v_a_4158_);
lean_dec(v___x_4143_);
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
else
{
lean_object* v_a_4166_; lean_object* v___x_4168_; uint8_t v_isShared_4169_; uint8_t v_isSharedCheck_4173_; 
lean_dec(v_a_4139_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_4166_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4168_ = v___x_4141_;
v_isShared_4169_ = v_isSharedCheck_4173_;
goto v_resetjp_4167_;
}
else
{
lean_inc(v_a_4166_);
lean_dec(v___x_4141_);
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
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_4174_ = lean_ctor_get(v___x_4138_, 0);
v_isSharedCheck_4181_ = !lean_is_exclusive(v___x_4138_);
if (v_isSharedCheck_4181_ == 0)
{
v___x_4176_ = v___x_4138_;
v_isShared_4177_ = v_isSharedCheck_4181_;
goto v_resetjp_4175_;
}
else
{
lean_inc(v_a_4174_);
lean_dec(v___x_4138_);
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
}
else
{
lean_object* v_a_4182_; lean_object* v___x_4184_; uint8_t v_isShared_4185_; uint8_t v_isSharedCheck_4189_; 
lean_dec_ref(v___x_3976_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4182_ = lean_ctor_get(v___x_4135_, 0);
v_isSharedCheck_4189_ = !lean_is_exclusive(v___x_4135_);
if (v_isSharedCheck_4189_ == 0)
{
v___x_4184_ = v___x_4135_;
v_isShared_4185_ = v_isSharedCheck_4189_;
goto v_resetjp_4183_;
}
else
{
lean_inc(v_a_4182_);
lean_dec(v___x_4135_);
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
v___jp_4190_:
{
lean_object* v___x_4196_; 
lean_inc_ref(v___x_3976_);
v___x_4196_ = l_Lean_Meta_matchHEq_x3f(v___x_3976_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
if (lean_obj_tag(v_a_4197_) == 1)
{
lean_object* v_val_4198_; lean_object* v_snd_4199_; lean_object* v_snd_4200_; lean_object* v_fst_4201_; lean_object* v_fst_4202_; lean_object* v_fst_4203_; lean_object* v_snd_4204_; lean_object* v___x_4205_; 
v_val_4198_ = lean_ctor_get(v_a_4197_, 0);
lean_inc(v_val_4198_);
lean_dec_ref_known(v_a_4197_, 1);
v_snd_4199_ = lean_ctor_get(v_val_4198_, 1);
lean_inc(v_snd_4199_);
v_snd_4200_ = lean_ctor_get(v_snd_4199_, 1);
lean_inc(v_snd_4200_);
v_fst_4201_ = lean_ctor_get(v_val_4198_, 0);
lean_inc(v_fst_4201_);
lean_dec(v_val_4198_);
v_fst_4202_ = lean_ctor_get(v_snd_4199_, 0);
lean_inc(v_fst_4202_);
lean_dec(v_snd_4199_);
v_fst_4203_ = lean_ctor_get(v_snd_4200_, 0);
lean_inc(v_fst_4203_);
v_snd_4204_ = lean_ctor_get(v_snd_4200_, 1);
lean_inc(v_snd_4204_);
lean_dec(v_snd_4200_);
v___x_4205_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4202_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v_a_4206_; 
v_a_4206_ = lean_ctor_get(v___x_4205_, 0);
lean_inc(v_a_4206_);
lean_dec_ref_known(v___x_4205_, 1);
if (lean_obj_tag(v_a_4206_) == 1)
{
lean_object* v_val_4207_; lean_object* v___x_4208_; 
v_val_4207_ = lean_ctor_get(v_a_4206_, 0);
lean_inc(v_val_4207_);
lean_dec_ref_known(v_a_4206_, 1);
v___x_4208_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4204_, v___y_4192_, v___y_4193_, v___y_4194_, v___y_4195_);
if (lean_obj_tag(v___x_4208_) == 0)
{
lean_object* v_a_4209_; 
v_a_4209_ = lean_ctor_get(v___x_4208_, 0);
lean_inc(v_a_4209_);
lean_dec_ref_known(v___x_4208_, 1);
if (lean_obj_tag(v_a_4209_) == 1)
{
lean_object* v_toConstantVal_4210_; lean_object* v_val_4211_; lean_object* v_toConstantVal_4212_; lean_object* v_name_4213_; lean_object* v_name_4214_; uint8_t v___x_4215_; 
v_toConstantVal_4210_ = lean_ctor_get(v_val_4207_, 0);
lean_inc_ref(v_toConstantVal_4210_);
lean_dec(v_val_4207_);
v_val_4211_ = lean_ctor_get(v_a_4209_, 0);
lean_inc(v_val_4211_);
lean_dec_ref_known(v_a_4209_, 1);
v_toConstantVal_4212_ = lean_ctor_get(v_val_4211_, 0);
lean_inc_ref(v_toConstantVal_4212_);
lean_dec(v_val_4211_);
v_name_4213_ = lean_ctor_get(v_toConstantVal_4210_, 0);
lean_inc(v_name_4213_);
lean_dec_ref(v_toConstantVal_4210_);
v_name_4214_ = lean_ctor_get(v_toConstantVal_4212_, 0);
lean_inc(v_name_4214_);
lean_dec_ref(v_toConstantVal_4212_);
v___x_4215_ = lean_name_eq(v_name_4213_, v_name_4214_);
lean_dec(v_name_4214_);
lean_dec(v_name_4213_);
if (v___x_4215_ == 0)
{
v___y_4128_ = v___y_4195_;
v___y_4129_ = v_fst_4203_;
v___y_4130_ = v___y_4192_;
v___y_4131_ = v_isEq_4191_;
v___y_4132_ = v___y_4194_;
v___y_4133_ = v___y_4193_;
v___y_4134_ = v_fst_4201_;
goto v___jp_4127_;
}
else
{
if (v___x_3931_ == 0)
{
lean_dec(v_fst_4203_);
lean_dec(v_fst_4201_);
v___y_4119_ = v_isEq_4191_;
v_isHEq_4120_ = v___x_3835_;
v___y_4121_ = v___y_4192_;
v___y_4122_ = v___y_4193_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
goto v___jp_4118_;
}
else
{
v___y_4128_ = v___y_4195_;
v___y_4129_ = v_fst_4203_;
v___y_4130_ = v___y_4192_;
v___y_4131_ = v_isEq_4191_;
v___y_4132_ = v___y_4194_;
v___y_4133_ = v___y_4193_;
v___y_4134_ = v_fst_4201_;
goto v___jp_4127_;
}
}
}
else
{
lean_dec(v_a_4209_);
lean_dec(v_val_4207_);
lean_dec(v_fst_4203_);
lean_dec(v_fst_4201_);
v___y_4119_ = v_isEq_4191_;
v_isHEq_4120_ = v___x_3835_;
v___y_4121_ = v___y_4192_;
v___y_4122_ = v___y_4193_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
goto v___jp_4118_;
}
}
else
{
lean_object* v_a_4216_; lean_object* v___x_4218_; uint8_t v_isShared_4219_; uint8_t v_isSharedCheck_4223_; 
lean_dec(v_val_4207_);
lean_dec(v_fst_4203_);
lean_dec(v_fst_4201_);
lean_dec_ref(v___x_3976_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4216_ = lean_ctor_get(v___x_4208_, 0);
v_isSharedCheck_4223_ = !lean_is_exclusive(v___x_4208_);
if (v_isSharedCheck_4223_ == 0)
{
v___x_4218_ = v___x_4208_;
v_isShared_4219_ = v_isSharedCheck_4223_;
goto v_resetjp_4217_;
}
else
{
lean_inc(v_a_4216_);
lean_dec(v___x_4208_);
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
else
{
lean_dec(v_a_4206_);
lean_dec(v_snd_4204_);
lean_dec(v_fst_4203_);
lean_dec(v_fst_4201_);
v___y_4119_ = v_isEq_4191_;
v_isHEq_4120_ = v___x_3835_;
v___y_4121_ = v___y_4192_;
v___y_4122_ = v___y_4193_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
goto v___jp_4118_;
}
}
else
{
lean_object* v_a_4224_; lean_object* v___x_4226_; uint8_t v_isShared_4227_; uint8_t v_isSharedCheck_4231_; 
lean_dec(v_snd_4204_);
lean_dec(v_fst_4203_);
lean_dec(v_fst_4201_);
lean_dec_ref(v___x_3976_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4224_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4231_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4231_ == 0)
{
v___x_4226_ = v___x_4205_;
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
else
{
lean_inc(v_a_4224_);
lean_dec(v___x_4205_);
v___x_4226_ = lean_box(0);
v_isShared_4227_ = v_isSharedCheck_4231_;
goto v_resetjp_4225_;
}
v_resetjp_4225_:
{
lean_object* v___x_4229_; 
if (v_isShared_4227_ == 0)
{
v___x_4229_ = v___x_4226_;
goto v_reusejp_4228_;
}
else
{
lean_object* v_reuseFailAlloc_4230_; 
v_reuseFailAlloc_4230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4230_, 0, v_a_4224_);
v___x_4229_ = v_reuseFailAlloc_4230_;
goto v_reusejp_4228_;
}
v_reusejp_4228_:
{
return v___x_4229_;
}
}
}
}
else
{
lean_dec(v_a_4197_);
v___y_4119_ = v_isEq_4191_;
v_isHEq_4120_ = v___x_3931_;
v___y_4121_ = v___y_4192_;
v___y_4122_ = v___y_4193_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
goto v___jp_4118_;
}
}
else
{
lean_object* v_a_4232_; lean_object* v___x_4234_; uint8_t v_isShared_4235_; uint8_t v_isSharedCheck_4239_; 
lean_dec_ref(v___x_3976_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4232_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4239_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4239_ == 0)
{
v___x_4234_ = v___x_4196_;
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
else
{
lean_inc(v_a_4232_);
lean_dec(v___x_4196_);
v___x_4234_ = lean_box(0);
v_isShared_4235_ = v_isSharedCheck_4239_;
goto v_resetjp_4233_;
}
v_resetjp_4233_:
{
lean_object* v___x_4237_; 
if (v_isShared_4235_ == 0)
{
v___x_4237_ = v___x_4234_;
goto v_reusejp_4236_;
}
else
{
lean_object* v_reuseFailAlloc_4238_; 
v_reuseFailAlloc_4238_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4238_, 0, v_a_4232_);
v___x_4237_ = v_reuseFailAlloc_4238_;
goto v_reusejp_4236_;
}
v_reusejp_4236_:
{
return v___x_4237_;
}
}
}
}
v___jp_4240_:
{
lean_object* v___x_4245_; 
lean_inc_ref(v___x_3976_);
v___x_4245_ = l_Lean_Meta_matchEq_x3f(v___x_3976_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
if (lean_obj_tag(v___x_4245_) == 0)
{
lean_object* v_a_4246_; 
v_a_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc(v_a_4246_);
lean_dec_ref_known(v___x_4245_, 1);
if (lean_obj_tag(v_a_4246_) == 1)
{
lean_object* v_val_4247_; lean_object* v_snd_4248_; lean_object* v_fst_4249_; lean_object* v_snd_4250_; lean_object* v___x_4251_; 
v_val_4247_ = lean_ctor_get(v_a_4246_, 0);
lean_inc(v_val_4247_);
lean_dec_ref_known(v_a_4246_, 1);
v_snd_4248_ = lean_ctor_get(v_val_4247_, 1);
lean_inc(v_snd_4248_);
lean_dec(v_val_4247_);
v_fst_4249_ = lean_ctor_get(v_snd_4248_, 0);
lean_inc(v_fst_4249_);
v_snd_4250_ = lean_ctor_get(v_snd_4248_, 1);
lean_inc(v_snd_4250_);
lean_dec(v_snd_4248_);
v___x_4251_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4249_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v_a_4252_; 
v_a_4252_ = lean_ctor_get(v___x_4251_, 0);
lean_inc(v_a_4252_);
lean_dec_ref_known(v___x_4251_, 1);
if (lean_obj_tag(v_a_4252_) == 1)
{
lean_object* v_val_4253_; lean_object* v___x_4254_; 
v_val_4253_ = lean_ctor_get(v_a_4252_, 0);
lean_inc(v_val_4253_);
lean_dec_ref_known(v_a_4252_, 1);
v___x_4254_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4250_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
if (lean_obj_tag(v___x_4254_) == 0)
{
lean_object* v_a_4255_; 
v_a_4255_ = lean_ctor_get(v___x_4254_, 0);
lean_inc(v_a_4255_);
lean_dec_ref_known(v___x_4254_, 1);
if (lean_obj_tag(v_a_4255_) == 1)
{
lean_object* v_toConstantVal_4256_; lean_object* v_val_4257_; lean_object* v_toConstantVal_4258_; lean_object* v_name_4259_; lean_object* v_name_4260_; uint8_t v___x_4261_; 
v_toConstantVal_4256_ = lean_ctor_get(v_val_4253_, 0);
lean_inc_ref(v_toConstantVal_4256_);
lean_dec(v_val_4253_);
v_val_4257_ = lean_ctor_get(v_a_4255_, 0);
lean_inc(v_val_4257_);
lean_dec_ref_known(v_a_4255_, 1);
v_toConstantVal_4258_ = lean_ctor_get(v_val_4257_, 0);
lean_inc_ref(v_toConstantVal_4258_);
lean_dec(v_val_4257_);
v_name_4259_ = lean_ctor_get(v_toConstantVal_4256_, 0);
lean_inc(v_name_4259_);
lean_dec_ref(v_toConstantVal_4256_);
v_name_4260_ = lean_ctor_get(v_toConstantVal_4258_, 0);
lean_inc(v_name_4260_);
lean_dec_ref(v_toConstantVal_4258_);
v___x_4261_ = lean_name_eq(v_name_4259_, v_name_4260_);
lean_dec(v_name_4260_);
lean_dec(v_name_4259_);
if (v___x_4261_ == 0)
{
lean_dec_ref(v___x_3976_);
lean_dec_ref(v_config_3824_);
v___y_3862_ = v___y_4241_;
v___y_3863_ = v___y_4243_;
v___y_3864_ = v___y_4242_;
v___y_3865_ = v___y_4244_;
goto v___jp_3861_;
}
else
{
if (v___x_3931_ == 0)
{
lean_del_object(v___x_3858_);
v_isEq_4191_ = v___x_3835_;
v___y_4192_ = v___y_4241_;
v___y_4193_ = v___y_4242_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
goto v___jp_4190_;
}
else
{
lean_dec_ref(v___x_3976_);
lean_dec_ref(v_config_3824_);
v___y_3862_ = v___y_4241_;
v___y_3863_ = v___y_4243_;
v___y_3864_ = v___y_4242_;
v___y_3865_ = v___y_4244_;
goto v___jp_3861_;
}
}
}
else
{
lean_dec(v_a_4255_);
lean_dec(v_val_4253_);
lean_del_object(v___x_3858_);
v_isEq_4191_ = v___x_3835_;
v___y_4192_ = v___y_4241_;
v___y_4193_ = v___y_4242_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
goto v___jp_4190_;
}
}
else
{
lean_object* v_a_4262_; lean_object* v___x_4264_; uint8_t v_isShared_4265_; uint8_t v_isSharedCheck_4269_; 
lean_dec(v_val_4253_);
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4262_ = lean_ctor_get(v___x_4254_, 0);
v_isSharedCheck_4269_ = !lean_is_exclusive(v___x_4254_);
if (v_isSharedCheck_4269_ == 0)
{
v___x_4264_ = v___x_4254_;
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
else
{
lean_inc(v_a_4262_);
lean_dec(v___x_4254_);
v___x_4264_ = lean_box(0);
v_isShared_4265_ = v_isSharedCheck_4269_;
goto v_resetjp_4263_;
}
v_resetjp_4263_:
{
lean_object* v___x_4267_; 
if (v_isShared_4265_ == 0)
{
v___x_4267_ = v___x_4264_;
goto v_reusejp_4266_;
}
else
{
lean_object* v_reuseFailAlloc_4268_; 
v_reuseFailAlloc_4268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4268_, 0, v_a_4262_);
v___x_4267_ = v_reuseFailAlloc_4268_;
goto v_reusejp_4266_;
}
v_reusejp_4266_:
{
return v___x_4267_;
}
}
}
}
else
{
lean_dec(v_a_4252_);
lean_dec(v_snd_4250_);
lean_del_object(v___x_3858_);
v_isEq_4191_ = v___x_3835_;
v___y_4192_ = v___y_4241_;
v___y_4193_ = v___y_4242_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
goto v___jp_4190_;
}
}
else
{
lean_object* v_a_4270_; lean_object* v___x_4272_; uint8_t v_isShared_4273_; uint8_t v_isSharedCheck_4277_; 
lean_dec(v_snd_4250_);
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4270_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4277_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4277_ == 0)
{
v___x_4272_ = v___x_4251_;
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
else
{
lean_inc(v_a_4270_);
lean_dec(v___x_4251_);
v___x_4272_ = lean_box(0);
v_isShared_4273_ = v_isSharedCheck_4277_;
goto v_resetjp_4271_;
}
v_resetjp_4271_:
{
lean_object* v___x_4275_; 
if (v_isShared_4273_ == 0)
{
v___x_4275_ = v___x_4272_;
goto v_reusejp_4274_;
}
else
{
lean_object* v_reuseFailAlloc_4276_; 
v_reuseFailAlloc_4276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4276_, 0, v_a_4270_);
v___x_4275_ = v_reuseFailAlloc_4276_;
goto v_reusejp_4274_;
}
v_reusejp_4274_:
{
return v___x_4275_;
}
}
}
}
else
{
lean_dec(v_a_4246_);
lean_del_object(v___x_3858_);
v_isEq_4191_ = v___x_3931_;
v___y_4192_ = v___y_4241_;
v___y_4193_ = v___y_4242_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
goto v___jp_4190_;
}
}
else
{
lean_object* v_a_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4278_ = lean_ctor_get(v___x_4245_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4245_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4245_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_a_4278_);
lean_dec(v___x_4245_);
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
v___jp_4286_:
{
lean_object* v___x_4291_; 
lean_inc_ref(v___x_3976_);
v___x_4291_ = l_Lean_refutableHasNotBit_x3f(v___x_3976_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4291_) == 0)
{
lean_object* v_a_4292_; 
v_a_4292_ = lean_ctor_get(v___x_4291_, 0);
lean_inc(v_a_4292_);
lean_dec_ref_known(v___x_4291_, 1);
if (lean_obj_tag(v_a_4292_) == 1)
{
lean_object* v_val_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4333_; 
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec_ref(v_config_3824_);
v_val_4293_ = lean_ctor_get(v_a_4292_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v_a_4292_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4295_ = v_a_4292_;
v_isShared_4296_ = v_isSharedCheck_4333_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_val_4293_);
lean_dec(v_a_4292_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4333_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4297_; 
lean_inc(v_mvarId_3825_);
v___x_4297_ = l_Lean_MVarId_getType(v_mvarId_3825_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4297_) == 0)
{
lean_object* v_a_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; 
v_a_4298_ = lean_ctor_get(v___x_4297_, 0);
lean_inc(v_a_4298_);
lean_dec_ref_known(v___x_4297_, 1);
v___x_4299_ = l_Lean_LocalDecl_toExpr(v_val_3856_);
v___x_4300_ = l_Lean_Meta_mkAbsurd(v_a_4298_, v_val_4293_, v___x_4299_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4300_) == 0)
{
lean_object* v_a_4301_; lean_object* v___x_4302_; 
v_a_4301_ = lean_ctor_get(v___x_4300_, 0);
lean_inc(v_a_4301_);
lean_dec_ref_known(v___x_4300_, 1);
v___x_4302_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3825_, v_a_4301_, v___y_4288_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v___x_4303_; lean_object* v___x_4305_; 
lean_dec_ref_known(v___x_4302_, 1);
v___x_4303_ = lean_box(v___x_3835_);
if (v_isShared_4296_ == 0)
{
lean_ctor_set(v___x_4295_, 0, v___x_4303_);
v___x_4305_ = v___x_4295_;
goto v_reusejp_4304_;
}
else
{
lean_object* v_reuseFailAlloc_4308_; 
v_reuseFailAlloc_4308_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4308_, 0, v___x_4303_);
v___x_4305_ = v_reuseFailAlloc_4308_;
goto v_reusejp_4304_;
}
v_reusejp_4304_:
{
lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4306_, 0, v___x_4305_);
lean_ctor_set(v___x_4306_, 1, v___x_3860_);
v___x_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
v_a_3842_ = v___x_4307_;
goto v___jp_3841_;
}
}
else
{
lean_object* v_a_4309_; lean_object* v___x_4311_; uint8_t v_isShared_4312_; uint8_t v_isSharedCheck_4316_; 
lean_del_object(v___x_4295_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
v_a_4309_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4316_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4316_ == 0)
{
v___x_4311_ = v___x_4302_;
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
else
{
lean_inc(v_a_4309_);
lean_dec(v___x_4302_);
v___x_4311_ = lean_box(0);
v_isShared_4312_ = v_isSharedCheck_4316_;
goto v_resetjp_4310_;
}
v_resetjp_4310_:
{
lean_object* v___x_4314_; 
if (v_isShared_4312_ == 0)
{
v___x_4314_ = v___x_4311_;
goto v_reusejp_4313_;
}
else
{
lean_object* v_reuseFailAlloc_4315_; 
v_reuseFailAlloc_4315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4315_, 0, v_a_4309_);
v___x_4314_ = v_reuseFailAlloc_4315_;
goto v_reusejp_4313_;
}
v_reusejp_4313_:
{
return v___x_4314_;
}
}
}
}
else
{
lean_object* v_a_4317_; lean_object* v___x_4319_; uint8_t v_isShared_4320_; uint8_t v_isSharedCheck_4324_; 
lean_del_object(v___x_4295_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_4317_ = lean_ctor_get(v___x_4300_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4300_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4319_ = v___x_4300_;
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
else
{
lean_inc(v_a_4317_);
lean_dec(v___x_4300_);
v___x_4319_ = lean_box(0);
v_isShared_4320_ = v_isSharedCheck_4324_;
goto v_resetjp_4318_;
}
v_resetjp_4318_:
{
lean_object* v___x_4322_; 
if (v_isShared_4320_ == 0)
{
v___x_4322_ = v___x_4319_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v_a_4317_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_del_object(v___x_4295_);
lean_dec(v_val_4293_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_4325_ = lean_ctor_get(v___x_4297_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4297_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4297_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4297_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
}
else
{
lean_object* v___x_4334_; 
lean_dec(v_a_4292_);
lean_inc_ref(v___x_3976_);
v___x_4334_ = l_Lean_Meta_matchNe_x3f(v___x_3976_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4334_) == 0)
{
lean_object* v_a_4335_; 
v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
lean_inc(v_a_4335_);
lean_dec_ref_known(v___x_4334_, 1);
if (lean_obj_tag(v_a_4335_) == 1)
{
lean_object* v_val_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4406_; 
v_val_4336_ = lean_ctor_get(v_a_4335_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v_a_4335_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4338_ = v_a_4335_;
v_isShared_4339_ = v_isSharedCheck_4406_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_val_4336_);
lean_dec(v_a_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4406_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v_snd_4340_; lean_object* v_fst_4341_; lean_object* v_snd_4342_; lean_object* v___x_4344_; uint8_t v_isShared_4345_; uint8_t v_isSharedCheck_4405_; 
v_snd_4340_ = lean_ctor_get(v_val_4336_, 1);
lean_inc(v_snd_4340_);
lean_dec(v_val_4336_);
v_fst_4341_ = lean_ctor_get(v_snd_4340_, 0);
v_snd_4342_ = lean_ctor_get(v_snd_4340_, 1);
v_isSharedCheck_4405_ = !lean_is_exclusive(v_snd_4340_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4344_ = v_snd_4340_;
v_isShared_4345_ = v_isSharedCheck_4405_;
goto v_resetjp_4343_;
}
else
{
lean_inc(v_snd_4342_);
lean_inc(v_fst_4341_);
lean_dec(v_snd_4340_);
v___x_4344_ = lean_box(0);
v_isShared_4345_ = v_isSharedCheck_4405_;
goto v_resetjp_4343_;
}
v_resetjp_4343_:
{
lean_object* v___x_4346_; 
lean_inc(v_fst_4341_);
v___x_4346_ = l_Lean_Meta_isExprDefEq(v_fst_4341_, v_snd_4342_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4346_) == 0)
{
lean_object* v_a_4347_; uint8_t v___x_4348_; 
v_a_4347_ = lean_ctor_get(v___x_4346_, 0);
lean_inc(v_a_4347_);
lean_dec_ref_known(v___x_4346_, 1);
v___x_4348_ = lean_unbox(v_a_4347_);
lean_dec(v_a_4347_);
if (v___x_4348_ == 0)
{
lean_del_object(v___x_4344_);
lean_dec(v_fst_4341_);
lean_del_object(v___x_4338_);
v___y_4241_ = v___y_4287_;
v___y_4242_ = v___y_4288_;
v___y_4243_ = v___y_4289_;
v___y_4244_ = v___y_4290_;
goto v___jp_4240_;
}
else
{
lean_object* v___x_4349_; 
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec_ref(v_config_3824_);
lean_inc(v_mvarId_3825_);
v___x_4349_ = l_Lean_MVarId_getType(v_mvarId_3825_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4349_) == 0)
{
lean_object* v_a_4350_; lean_object* v___x_4351_; 
v_a_4350_ = lean_ctor_get(v___x_4349_, 0);
lean_inc(v_a_4350_);
lean_dec_ref_known(v___x_4349_, 1);
v___x_4351_ = l_Lean_Meta_mkEqRefl(v_fst_4341_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4353_; lean_object* v___x_4354_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4351_, 1);
v___x_4353_ = l_Lean_LocalDecl_toExpr(v_val_3856_);
v___x_4354_ = l_Lean_Meta_mkAbsurd(v_a_4350_, v_a_4352_, v___x_4353_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
if (lean_obj_tag(v___x_4354_) == 0)
{
lean_object* v_a_4355_; lean_object* v___x_4356_; 
v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
lean_inc(v_a_4355_);
lean_dec_ref_known(v___x_4354_, 1);
v___x_4356_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3825_, v_a_4355_, v___y_4288_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v___x_4357_; lean_object* v___x_4359_; 
lean_dec_ref_known(v___x_4356_, 1);
v___x_4357_ = lean_box(v___x_3835_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 0, v___x_4357_);
v___x_4359_ = v___x_4338_;
goto v_reusejp_4358_;
}
else
{
lean_object* v_reuseFailAlloc_4364_; 
v_reuseFailAlloc_4364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4364_, 0, v___x_4357_);
v___x_4359_ = v_reuseFailAlloc_4364_;
goto v_reusejp_4358_;
}
v_reusejp_4358_:
{
lean_object* v___x_4361_; 
if (v_isShared_4345_ == 0)
{
lean_ctor_set(v___x_4344_, 1, v___x_3860_);
lean_ctor_set(v___x_4344_, 0, v___x_4359_);
v___x_4361_ = v___x_4344_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4363_; 
v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4359_);
lean_ctor_set(v_reuseFailAlloc_4363_, 1, v___x_3860_);
v___x_4361_ = v_reuseFailAlloc_4363_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4362_; 
v___x_4362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4362_, 0, v___x_4361_);
v_a_3842_ = v___x_4362_;
goto v___jp_3841_;
}
}
}
else
{
lean_object* v_a_4365_; lean_object* v___x_4367_; uint8_t v_isShared_4368_; uint8_t v_isSharedCheck_4372_; 
lean_del_object(v___x_4344_);
lean_del_object(v___x_4338_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
v_a_4365_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4372_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4372_ == 0)
{
v___x_4367_ = v___x_4356_;
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
else
{
lean_inc(v_a_4365_);
lean_dec(v___x_4356_);
v___x_4367_ = lean_box(0);
v_isShared_4368_ = v_isSharedCheck_4372_;
goto v_resetjp_4366_;
}
v_resetjp_4366_:
{
lean_object* v___x_4370_; 
if (v_isShared_4368_ == 0)
{
v___x_4370_ = v___x_4367_;
goto v_reusejp_4369_;
}
else
{
lean_object* v_reuseFailAlloc_4371_; 
v_reuseFailAlloc_4371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4371_, 0, v_a_4365_);
v___x_4370_ = v_reuseFailAlloc_4371_;
goto v_reusejp_4369_;
}
v_reusejp_4369_:
{
return v___x_4370_;
}
}
}
}
else
{
lean_object* v_a_4373_; lean_object* v___x_4375_; uint8_t v_isShared_4376_; uint8_t v_isSharedCheck_4380_; 
lean_del_object(v___x_4344_);
lean_del_object(v___x_4338_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_4373_ = lean_ctor_get(v___x_4354_, 0);
v_isSharedCheck_4380_ = !lean_is_exclusive(v___x_4354_);
if (v_isSharedCheck_4380_ == 0)
{
v___x_4375_ = v___x_4354_;
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
else
{
lean_inc(v_a_4373_);
lean_dec(v___x_4354_);
v___x_4375_ = lean_box(0);
v_isShared_4376_ = v_isSharedCheck_4380_;
goto v_resetjp_4374_;
}
v_resetjp_4374_:
{
lean_object* v___x_4378_; 
if (v_isShared_4376_ == 0)
{
v___x_4378_ = v___x_4375_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_a_4373_);
v___x_4378_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
return v___x_4378_;
}
}
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_dec(v_a_4350_);
lean_del_object(v___x_4344_);
lean_del_object(v___x_4338_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_4381_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4351_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4351_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
else
{
lean_object* v_a_4389_; lean_object* v___x_4391_; uint8_t v_isShared_4392_; uint8_t v_isSharedCheck_4396_; 
lean_del_object(v___x_4344_);
lean_dec(v_fst_4341_);
lean_del_object(v___x_4338_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_4389_ = lean_ctor_get(v___x_4349_, 0);
v_isSharedCheck_4396_ = !lean_is_exclusive(v___x_4349_);
if (v_isSharedCheck_4396_ == 0)
{
v___x_4391_ = v___x_4349_;
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
else
{
lean_inc(v_a_4389_);
lean_dec(v___x_4349_);
v___x_4391_ = lean_box(0);
v_isShared_4392_ = v_isSharedCheck_4396_;
goto v_resetjp_4390_;
}
v_resetjp_4390_:
{
lean_object* v___x_4394_; 
if (v_isShared_4392_ == 0)
{
v___x_4394_ = v___x_4391_;
goto v_reusejp_4393_;
}
else
{
lean_object* v_reuseFailAlloc_4395_; 
v_reuseFailAlloc_4395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4395_, 0, v_a_4389_);
v___x_4394_ = v_reuseFailAlloc_4395_;
goto v_reusejp_4393_;
}
v_reusejp_4393_:
{
return v___x_4394_;
}
}
}
}
}
else
{
lean_object* v_a_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4404_; 
lean_del_object(v___x_4344_);
lean_dec(v_fst_4341_);
lean_del_object(v___x_4338_);
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4397_ = lean_ctor_get(v___x_4346_, 0);
v_isSharedCheck_4404_ = !lean_is_exclusive(v___x_4346_);
if (v_isSharedCheck_4404_ == 0)
{
v___x_4399_ = v___x_4346_;
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_a_4397_);
lean_dec(v___x_4346_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4404_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v___x_4402_; 
if (v_isShared_4400_ == 0)
{
v___x_4402_ = v___x_4399_;
goto v_reusejp_4401_;
}
else
{
lean_object* v_reuseFailAlloc_4403_; 
v_reuseFailAlloc_4403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4403_, 0, v_a_4397_);
v___x_4402_ = v_reuseFailAlloc_4403_;
goto v_reusejp_4401_;
}
v_reusejp_4401_:
{
return v___x_4402_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4335_);
v___y_4241_ = v___y_4287_;
v___y_4242_ = v___y_4288_;
v___y_4243_ = v___y_4289_;
v___y_4244_ = v___y_4290_;
goto v___jp_4240_;
}
}
else
{
lean_object* v_a_4407_; lean_object* v___x_4409_; uint8_t v_isShared_4410_; uint8_t v_isSharedCheck_4414_; 
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4407_ = lean_ctor_get(v___x_4334_, 0);
v_isSharedCheck_4414_ = !lean_is_exclusive(v___x_4334_);
if (v_isSharedCheck_4414_ == 0)
{
v___x_4409_ = v___x_4334_;
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
else
{
lean_inc(v_a_4407_);
lean_dec(v___x_4334_);
v___x_4409_ = lean_box(0);
v_isShared_4410_ = v_isSharedCheck_4414_;
goto v_resetjp_4408_;
}
v_resetjp_4408_:
{
lean_object* v___x_4412_; 
if (v_isShared_4410_ == 0)
{
v___x_4412_ = v___x_4409_;
goto v_reusejp_4411_;
}
else
{
lean_object* v_reuseFailAlloc_4413_; 
v_reuseFailAlloc_4413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4413_, 0, v_a_4407_);
v___x_4412_ = v_reuseFailAlloc_4413_;
goto v_reusejp_4411_;
}
v_reusejp_4411_:
{
return v___x_4412_;
}
}
}
}
}
else
{
lean_object* v_a_4415_; lean_object* v___x_4417_; uint8_t v_isShared_4418_; uint8_t v_isSharedCheck_4422_; 
lean_dec_ref(v___x_3976_);
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_4415_ = lean_ctor_get(v___x_4291_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4291_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4417_ = v___x_4291_;
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
else
{
lean_inc(v_a_4415_);
lean_dec(v___x_4291_);
v___x_4417_ = lean_box(0);
v_isShared_4418_ = v_isSharedCheck_4422_;
goto v_resetjp_4416_;
}
v_resetjp_4416_:
{
lean_object* v___x_4420_; 
if (v_isShared_4418_ == 0)
{
v___x_4420_ = v___x_4417_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v_a_4415_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
}
}
else
{
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
v_a_3850_ = v___x_3902_;
goto v___jp_3849_;
}
v___jp_3861_:
{
lean_object* v___x_3866_; 
lean_inc(v_mvarId_3825_);
v___x_3866_ = l_Lean_MVarId_getType(v_mvarId_3825_, v___y_3862_, v___y_3864_, v___y_3863_, v___y_3865_);
if (lean_obj_tag(v___x_3866_) == 0)
{
lean_object* v_a_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; 
v_a_3867_ = lean_ctor_get(v___x_3866_, 0);
lean_inc(v_a_3867_);
lean_dec_ref_known(v___x_3866_, 1);
v___x_3868_ = l_Lean_LocalDecl_toExpr(v_val_3856_);
v___x_3869_ = l_Lean_Meta_mkNoConfusion(v_a_3867_, v___x_3868_, v___y_3862_, v___y_3864_, v___y_3863_, v___y_3865_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v_a_3870_; lean_object* v___x_3871_; 
v_a_3870_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_a_3870_);
lean_dec_ref_known(v___x_3869_, 1);
v___x_3871_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3825_, v_a_3870_, v___y_3864_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v___x_3872_; lean_object* v___x_3874_; 
lean_dec_ref_known(v___x_3871_, 1);
v___x_3872_ = lean_box(v___x_3835_);
if (v_isShared_3859_ == 0)
{
lean_ctor_set(v___x_3858_, 0, v___x_3872_);
v___x_3874_ = v___x_3858_;
goto v_reusejp_3873_;
}
else
{
lean_object* v_reuseFailAlloc_3877_; 
v_reuseFailAlloc_3877_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3877_, 0, v___x_3872_);
v___x_3874_ = v_reuseFailAlloc_3877_;
goto v_reusejp_3873_;
}
v_reusejp_3873_:
{
lean_object* v___x_3875_; lean_object* v___x_3876_; 
v___x_3875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3874_);
lean_ctor_set(v___x_3875_, 1, v___x_3860_);
v___x_3876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3876_, 0, v___x_3875_);
v_a_3842_ = v___x_3876_;
goto v___jp_3841_;
}
}
else
{
lean_object* v_a_3878_; lean_object* v___x_3880_; uint8_t v_isShared_3881_; uint8_t v_isSharedCheck_3885_; 
lean_del_object(v___x_3858_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
v_a_3878_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3885_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3885_ == 0)
{
v___x_3880_ = v___x_3871_;
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
else
{
lean_inc(v_a_3878_);
lean_dec(v___x_3871_);
v___x_3880_ = lean_box(0);
v_isShared_3881_ = v_isSharedCheck_3885_;
goto v_resetjp_3879_;
}
v_resetjp_3879_:
{
lean_object* v___x_3883_; 
if (v_isShared_3881_ == 0)
{
v___x_3883_ = v___x_3880_;
goto v_reusejp_3882_;
}
else
{
lean_object* v_reuseFailAlloc_3884_; 
v_reuseFailAlloc_3884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3884_, 0, v_a_3878_);
v___x_3883_ = v_reuseFailAlloc_3884_;
goto v_reusejp_3882_;
}
v_reusejp_3882_:
{
return v___x_3883_;
}
}
}
}
else
{
lean_object* v_a_3886_; lean_object* v___x_3888_; uint8_t v_isShared_3889_; uint8_t v_isSharedCheck_3893_; 
lean_del_object(v___x_3858_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_3886_ = lean_ctor_get(v___x_3869_, 0);
v_isSharedCheck_3893_ = !lean_is_exclusive(v___x_3869_);
if (v_isSharedCheck_3893_ == 0)
{
v___x_3888_ = v___x_3869_;
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
else
{
lean_inc(v_a_3886_);
lean_dec(v___x_3869_);
v___x_3888_ = lean_box(0);
v_isShared_3889_ = v_isSharedCheck_3893_;
goto v_resetjp_3887_;
}
v_resetjp_3887_:
{
lean_object* v___x_3891_; 
if (v_isShared_3889_ == 0)
{
v___x_3891_ = v___x_3888_;
goto v_reusejp_3890_;
}
else
{
lean_object* v_reuseFailAlloc_3892_; 
v_reuseFailAlloc_3892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3892_, 0, v_a_3886_);
v___x_3891_ = v_reuseFailAlloc_3892_;
goto v_reusejp_3890_;
}
v_reusejp_3890_:
{
return v___x_3891_;
}
}
}
}
else
{
lean_object* v_a_3894_; lean_object* v___x_3896_; uint8_t v_isShared_3897_; uint8_t v_isSharedCheck_3901_; 
lean_del_object(v___x_3858_);
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
v_a_3894_ = lean_ctor_get(v___x_3866_, 0);
v_isSharedCheck_3901_ = !lean_is_exclusive(v___x_3866_);
if (v_isSharedCheck_3901_ == 0)
{
v___x_3896_ = v___x_3866_;
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
else
{
lean_inc(v_a_3894_);
lean_dec(v___x_3866_);
v___x_3896_ = lean_box(0);
v_isShared_3897_ = v_isSharedCheck_3901_;
goto v_resetjp_3895_;
}
v_resetjp_3895_:
{
lean_object* v___x_3899_; 
if (v_isShared_3897_ == 0)
{
v___x_3899_ = v___x_3896_;
goto v_reusejp_3898_;
}
else
{
lean_object* v_reuseFailAlloc_3900_; 
v_reuseFailAlloc_3900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3900_, 0, v_a_3894_);
v___x_3899_ = v_reuseFailAlloc_3900_;
goto v_reusejp_3898_;
}
v_reusejp_3898_:
{
return v___x_3899_;
}
}
}
}
v___jp_3903_:
{
lean_object* v_searchFuel_3908_; lean_object* v___x_3909_; lean_object* v___x_3910_; 
v_searchFuel_3908_ = lean_ctor_get(v_config_3824_, 0);
v___x_3909_ = l_Lean_LocalDecl_fvarId(v_val_3856_);
lean_dec(v_val_3856_);
lean_inc(v_searchFuel_3908_);
lean_inc(v_mvarId_3825_);
v___x_3910_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3825_, v___x_3909_, v_searchFuel_3908_, v___y_3906_, v___y_3907_, v___y_3905_, v___y_3904_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; uint8_t v___x_3912_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = lean_unbox(v_a_3911_);
lean_dec(v_a_3911_);
if (v___x_3912_ == 0)
{
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
v_a_3850_ = v___x_3902_;
goto v___jp_3849_;
}
else
{
lean_object* v___x_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v___x_3913_ = lean_box(v___x_3835_);
v___x_3914_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3914_, 0, v___x_3913_);
v___x_3915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
lean_ctor_set(v___x_3915_, 1, v___x_3860_);
v___x_3916_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
v_a_3842_ = v___x_3916_;
goto v___jp_3841_;
}
}
else
{
lean_object* v_a_3917_; lean_object* v___x_3919_; uint8_t v_isShared_3920_; uint8_t v_isSharedCheck_3924_; 
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_3917_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3924_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3924_ == 0)
{
v___x_3919_ = v___x_3910_;
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
else
{
lean_inc(v_a_3917_);
lean_dec(v___x_3910_);
v___x_3919_ = lean_box(0);
v_isShared_3920_ = v_isSharedCheck_3924_;
goto v_resetjp_3918_;
}
v_resetjp_3918_:
{
lean_object* v___x_3922_; 
if (v_isShared_3920_ == 0)
{
v___x_3922_ = v___x_3919_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3923_; 
v_reuseFailAlloc_3923_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3923_, 0, v_a_3917_);
v___x_3922_ = v_reuseFailAlloc_3923_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
return v___x_3922_;
}
}
}
}
v___jp_3925_:
{
if (v___y_3930_ == 0)
{
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
v_a_3850_ = v___x_3902_;
goto v___jp_3849_;
}
else
{
v___y_3904_ = v___y_3926_;
v___y_3905_ = v___y_3927_;
v___y_3906_ = v___y_3928_;
v___y_3907_ = v___y_3929_;
goto v___jp_3903_;
}
}
v___jp_3932_:
{
if (v___y_3936_ == 0)
{
v___y_3904_ = v___y_3933_;
v___y_3905_ = v___y_3934_;
v___y_3906_ = v___y_3935_;
v___y_3907_ = v___y_3937_;
goto v___jp_3903_;
}
else
{
v___y_3926_ = v___y_3933_;
v___y_3927_ = v___y_3934_;
v___y_3928_ = v___y_3935_;
v___y_3929_ = v___y_3937_;
v___y_3930_ = v___x_3931_;
goto v___jp_3925_;
}
}
v___jp_3938_:
{
if (v___y_3944_ == 0)
{
v___y_3926_ = v___y_3939_;
v___y_3927_ = v___y_3940_;
v___y_3928_ = v___y_3941_;
v___y_3929_ = v___y_3943_;
v___y_3930_ = v___x_3931_;
goto v___jp_3925_;
}
else
{
v___y_3933_ = v___y_3939_;
v___y_3934_ = v___y_3940_;
v___y_3935_ = v___y_3941_;
v___y_3936_ = v___y_3942_;
v___y_3937_ = v___y_3943_;
goto v___jp_3932_;
}
}
v___jp_3945_:
{
uint8_t v_emptyType_3952_; 
v_emptyType_3952_ = lean_ctor_get_uint8(v_config_3824_, sizeof(void*)*1 + 1);
if (v_emptyType_3952_ == 0)
{
v___y_3939_ = v___y_3951_;
v___y_3940_ = v___y_3950_;
v___y_3941_ = v___y_3948_;
v___y_3942_ = v___y_3947_;
v___y_3943_ = v___y_3949_;
v___y_3944_ = v___x_3931_;
goto v___jp_3938_;
}
else
{
if (v___y_3946_ == 0)
{
v___y_3933_ = v___y_3951_;
v___y_3934_ = v___y_3950_;
v___y_3935_ = v___y_3948_;
v___y_3936_ = v___y_3947_;
v___y_3937_ = v___y_3949_;
goto v___jp_3932_;
}
else
{
v___y_3939_ = v___y_3951_;
v___y_3940_ = v___y_3950_;
v___y_3941_ = v___y_3948_;
v___y_3942_ = v___y_3947_;
v___y_3943_ = v___y_3949_;
v___y_3944_ = v___x_3931_;
goto v___jp_3938_;
}
}
}
v___jp_3953_:
{
if (v___y_3960_ == 0)
{
v___y_3946_ = v___y_3956_;
v___y_3947_ = v___y_3959_;
v___y_3948_ = v___y_3958_;
v___y_3949_ = v___y_3957_;
v___y_3950_ = v___y_3955_;
v___y_3951_ = v___y_3954_;
goto v___jp_3945_;
}
else
{
lean_object* v___x_3961_; 
lean_inc(v_val_3856_);
lean_inc(v_mvarId_3825_);
v___x_3961_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3825_, v_val_3856_, v___y_3958_, v___y_3957_, v___y_3955_, v___y_3954_);
if (lean_obj_tag(v___x_3961_) == 0)
{
lean_object* v_a_3962_; uint8_t v___x_3963_; 
v_a_3962_ = lean_ctor_get(v___x_3961_, 0);
lean_inc(v_a_3962_);
lean_dec_ref_known(v___x_3961_, 1);
v___x_3963_ = lean_unbox(v_a_3962_);
lean_dec(v_a_3962_);
if (v___x_3963_ == 0)
{
v___y_3946_ = v___y_3956_;
v___y_3947_ = v___y_3959_;
v___y_3948_ = v___y_3958_;
v___y_3949_ = v___y_3957_;
v___y_3950_ = v___y_3955_;
v___y_3951_ = v___y_3954_;
goto v___jp_3945_;
}
else
{
lean_object* v___x_3964_; lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
lean_dec(v_val_3856_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v___x_3964_ = lean_box(v___x_3835_);
v___x_3965_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3965_, 0, v___x_3964_);
v___x_3966_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3966_, 0, v___x_3965_);
lean_ctor_set(v___x_3966_, 1, v___x_3860_);
v___x_3967_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
v_a_3842_ = v___x_3967_;
goto v___jp_3841_;
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_dec(v_val_3856_);
lean_del_object(v___x_3839_);
lean_dec(v_snd_3837_);
lean_dec(v_mvarId_3825_);
lean_dec_ref(v_config_3824_);
v_a_3968_ = lean_ctor_get(v___x_3961_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3961_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3961_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3961_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
}
}
}
v___jp_3841_:
{
lean_object* v___x_3843_; lean_object* v___x_3845_; 
v___x_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3843_, 0, v_a_3842_);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3843_);
v___x_3845_ = v___x_3839_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3847_; 
v_reuseFailAlloc_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3847_, 0, v___x_3843_);
lean_ctor_set(v_reuseFailAlloc_3847_, 1, v_snd_3837_);
v___x_3845_ = v_reuseFailAlloc_3847_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
lean_object* v___x_3846_; 
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
return v___x_3846_;
}
}
v___jp_3849_:
{
lean_object* v___x_3851_; size_t v___x_3852_; size_t v___x_3853_; lean_object* v___x_3854_; 
v___x_3851_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3851_, 0, v___x_3848_);
lean_ctor_set(v___x_3851_, 1, v_a_3850_);
v___x_3852_ = ((size_t)1ULL);
v___x_3853_ = lean_usize_add(v_i_3828_, v___x_3852_);
v___x_3854_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3824_, v_mvarId_3825_, v_as_3826_, v_sz_3827_, v___x_3853_, v___x_3851_, v___y_3830_, v___y_3831_, v___y_3832_, v___y_3833_);
return v___x_3854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4496_, lean_object* v_mvarId_4497_, lean_object* v_as_4498_, lean_object* v_sz_4499_, lean_object* v_i_4500_, lean_object* v_b_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
size_t v_sz_boxed_4507_; size_t v_i_boxed_4508_; lean_object* v_res_4509_; 
v_sz_boxed_4507_ = lean_unbox_usize(v_sz_4499_);
lean_dec(v_sz_4499_);
v_i_boxed_4508_ = lean_unbox_usize(v_i_4500_);
lean_dec(v_i_4500_);
v_res_4509_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4496_, v_mvarId_4497_, v_as_4498_, v_sz_boxed_4507_, v_i_boxed_4508_, v_b_4501_, v___y_4502_, v___y_4503_, v___y_4504_, v___y_4505_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec_ref(v_as_4498_);
return v_res_4509_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4510_, lean_object* v_config_4511_, lean_object* v_mvarId_4512_, lean_object* v_n_4513_, lean_object* v_b_4514_, lean_object* v___y_4515_, lean_object* v___y_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_){
_start:
{
if (lean_obj_tag(v_n_4513_) == 0)
{
lean_object* v_cs_4520_; lean_object* v___x_4521_; lean_object* v___x_4522_; size_t v_sz_4523_; size_t v___x_4524_; lean_object* v___x_4525_; 
v_cs_4520_ = lean_ctor_get(v_n_4513_, 0);
v___x_4521_ = lean_box(0);
v___x_4522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
lean_ctor_set(v___x_4522_, 1, v_b_4514_);
v_sz_4523_ = lean_array_size(v_cs_4520_);
v___x_4524_ = ((size_t)0ULL);
v___x_4525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4510_, v_config_4511_, v_mvarId_4512_, v_cs_4520_, v_sz_4523_, v___x_4524_, v___x_4522_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
if (lean_obj_tag(v___x_4525_) == 0)
{
lean_object* v_a_4526_; lean_object* v___x_4528_; uint8_t v_isShared_4529_; uint8_t v_isSharedCheck_4540_; 
v_a_4526_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4540_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4540_ == 0)
{
v___x_4528_ = v___x_4525_;
v_isShared_4529_ = v_isSharedCheck_4540_;
goto v_resetjp_4527_;
}
else
{
lean_inc(v_a_4526_);
lean_dec(v___x_4525_);
v___x_4528_ = lean_box(0);
v_isShared_4529_ = v_isSharedCheck_4540_;
goto v_resetjp_4527_;
}
v_resetjp_4527_:
{
lean_object* v_fst_4530_; 
v_fst_4530_ = lean_ctor_get(v_a_4526_, 0);
if (lean_obj_tag(v_fst_4530_) == 0)
{
lean_object* v_snd_4531_; lean_object* v___x_4532_; lean_object* v___x_4534_; 
v_snd_4531_ = lean_ctor_get(v_a_4526_, 1);
lean_inc(v_snd_4531_);
lean_dec(v_a_4526_);
v___x_4532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4532_, 0, v_snd_4531_);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 0, v___x_4532_);
v___x_4534_ = v___x_4528_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v___x_4532_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
else
{
lean_object* v_val_4536_; lean_object* v___x_4538_; 
lean_inc_ref(v_fst_4530_);
lean_dec(v_a_4526_);
v_val_4536_ = lean_ctor_get(v_fst_4530_, 0);
lean_inc(v_val_4536_);
lean_dec_ref_known(v_fst_4530_, 1);
if (v_isShared_4529_ == 0)
{
lean_ctor_set(v___x_4528_, 0, v_val_4536_);
v___x_4538_ = v___x_4528_;
goto v_reusejp_4537_;
}
else
{
lean_object* v_reuseFailAlloc_4539_; 
v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4539_, 0, v_val_4536_);
v___x_4538_ = v_reuseFailAlloc_4539_;
goto v_reusejp_4537_;
}
v_reusejp_4537_:
{
return v___x_4538_;
}
}
}
}
else
{
lean_object* v_a_4541_; lean_object* v___x_4543_; uint8_t v_isShared_4544_; uint8_t v_isSharedCheck_4548_; 
v_a_4541_ = lean_ctor_get(v___x_4525_, 0);
v_isSharedCheck_4548_ = !lean_is_exclusive(v___x_4525_);
if (v_isSharedCheck_4548_ == 0)
{
v___x_4543_ = v___x_4525_;
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
else
{
lean_inc(v_a_4541_);
lean_dec(v___x_4525_);
v___x_4543_ = lean_box(0);
v_isShared_4544_ = v_isSharedCheck_4548_;
goto v_resetjp_4542_;
}
v_resetjp_4542_:
{
lean_object* v___x_4546_; 
if (v_isShared_4544_ == 0)
{
v___x_4546_ = v___x_4543_;
goto v_reusejp_4545_;
}
else
{
lean_object* v_reuseFailAlloc_4547_; 
v_reuseFailAlloc_4547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_a_4541_);
v___x_4546_ = v_reuseFailAlloc_4547_;
goto v_reusejp_4545_;
}
v_reusejp_4545_:
{
return v___x_4546_;
}
}
}
}
else
{
lean_object* v_vs_4549_; lean_object* v___x_4550_; lean_object* v___x_4551_; size_t v_sz_4552_; size_t v___x_4553_; lean_object* v___x_4554_; 
v_vs_4549_ = lean_ctor_get(v_n_4513_, 0);
v___x_4550_ = lean_box(0);
v___x_4551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4551_, 0, v___x_4550_);
lean_ctor_set(v___x_4551_, 1, v_b_4514_);
v_sz_4552_ = lean_array_size(v_vs_4549_);
v___x_4553_ = ((size_t)0ULL);
v___x_4554_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4511_, v_mvarId_4512_, v_vs_4549_, v_sz_4552_, v___x_4553_, v___x_4551_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_);
if (lean_obj_tag(v___x_4554_) == 0)
{
lean_object* v_a_4555_; lean_object* v___x_4557_; uint8_t v_isShared_4558_; uint8_t v_isSharedCheck_4569_; 
v_a_4555_ = lean_ctor_get(v___x_4554_, 0);
v_isSharedCheck_4569_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4569_ == 0)
{
v___x_4557_ = v___x_4554_;
v_isShared_4558_ = v_isSharedCheck_4569_;
goto v_resetjp_4556_;
}
else
{
lean_inc(v_a_4555_);
lean_dec(v___x_4554_);
v___x_4557_ = lean_box(0);
v_isShared_4558_ = v_isSharedCheck_4569_;
goto v_resetjp_4556_;
}
v_resetjp_4556_:
{
lean_object* v_fst_4559_; 
v_fst_4559_ = lean_ctor_get(v_a_4555_, 0);
if (lean_obj_tag(v_fst_4559_) == 0)
{
lean_object* v_snd_4560_; lean_object* v___x_4561_; lean_object* v___x_4563_; 
v_snd_4560_ = lean_ctor_get(v_a_4555_, 1);
lean_inc(v_snd_4560_);
lean_dec(v_a_4555_);
v___x_4561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4561_, 0, v_snd_4560_);
if (v_isShared_4558_ == 0)
{
lean_ctor_set(v___x_4557_, 0, v___x_4561_);
v___x_4563_ = v___x_4557_;
goto v_reusejp_4562_;
}
else
{
lean_object* v_reuseFailAlloc_4564_; 
v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
v___x_4563_ = v_reuseFailAlloc_4564_;
goto v_reusejp_4562_;
}
v_reusejp_4562_:
{
return v___x_4563_;
}
}
else
{
lean_object* v_val_4565_; lean_object* v___x_4567_; 
lean_inc_ref(v_fst_4559_);
lean_dec(v_a_4555_);
v_val_4565_ = lean_ctor_get(v_fst_4559_, 0);
lean_inc(v_val_4565_);
lean_dec_ref_known(v_fst_4559_, 1);
if (v_isShared_4558_ == 0)
{
lean_ctor_set(v___x_4557_, 0, v_val_4565_);
v___x_4567_ = v___x_4557_;
goto v_reusejp_4566_;
}
else
{
lean_object* v_reuseFailAlloc_4568_; 
v_reuseFailAlloc_4568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4568_, 0, v_val_4565_);
v___x_4567_ = v_reuseFailAlloc_4568_;
goto v_reusejp_4566_;
}
v_reusejp_4566_:
{
return v___x_4567_;
}
}
}
}
else
{
lean_object* v_a_4570_; lean_object* v___x_4572_; uint8_t v_isShared_4573_; uint8_t v_isSharedCheck_4577_; 
v_a_4570_ = lean_ctor_get(v___x_4554_, 0);
v_isSharedCheck_4577_ = !lean_is_exclusive(v___x_4554_);
if (v_isSharedCheck_4577_ == 0)
{
v___x_4572_ = v___x_4554_;
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
else
{
lean_inc(v_a_4570_);
lean_dec(v___x_4554_);
v___x_4572_ = lean_box(0);
v_isShared_4573_ = v_isSharedCheck_4577_;
goto v_resetjp_4571_;
}
v_resetjp_4571_:
{
lean_object* v___x_4575_; 
if (v_isShared_4573_ == 0)
{
v___x_4575_ = v___x_4572_;
goto v_reusejp_4574_;
}
else
{
lean_object* v_reuseFailAlloc_4576_; 
v_reuseFailAlloc_4576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4576_, 0, v_a_4570_);
v___x_4575_ = v_reuseFailAlloc_4576_;
goto v_reusejp_4574_;
}
v_reusejp_4574_:
{
return v___x_4575_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4578_, lean_object* v_config_4579_, lean_object* v_mvarId_4580_, lean_object* v_as_4581_, size_t v_sz_4582_, size_t v_i_4583_, lean_object* v_b_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_){
_start:
{
uint8_t v___x_4590_; 
v___x_4590_ = lean_usize_dec_lt(v_i_4583_, v_sz_4582_);
if (v___x_4590_ == 0)
{
lean_object* v___x_4591_; 
lean_dec(v_mvarId_4580_);
lean_dec_ref(v_config_4579_);
v___x_4591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4591_, 0, v_b_4584_);
return v___x_4591_;
}
else
{
lean_object* v_snd_4592_; lean_object* v___x_4594_; uint8_t v_isShared_4595_; uint8_t v_isSharedCheck_4626_; 
v_snd_4592_ = lean_ctor_get(v_b_4584_, 1);
v_isSharedCheck_4626_ = !lean_is_exclusive(v_b_4584_);
if (v_isSharedCheck_4626_ == 0)
{
lean_object* v_unused_4627_; 
v_unused_4627_ = lean_ctor_get(v_b_4584_, 0);
lean_dec(v_unused_4627_);
v___x_4594_ = v_b_4584_;
v_isShared_4595_ = v_isSharedCheck_4626_;
goto v_resetjp_4593_;
}
else
{
lean_inc(v_snd_4592_);
lean_dec(v_b_4584_);
v___x_4594_ = lean_box(0);
v_isShared_4595_ = v_isSharedCheck_4626_;
goto v_resetjp_4593_;
}
v_resetjp_4593_:
{
lean_object* v_a_4596_; lean_object* v___x_4597_; 
v_a_4596_ = lean_array_uget_borrowed(v_as_4581_, v_i_4583_);
lean_inc(v_snd_4592_);
lean_inc(v_mvarId_4580_);
lean_inc_ref(v_config_4579_);
v___x_4597_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4578_, v_config_4579_, v_mvarId_4580_, v_a_4596_, v_snd_4592_, v___y_4585_, v___y_4586_, v___y_4587_, v___y_4588_);
if (lean_obj_tag(v___x_4597_) == 0)
{
lean_object* v_a_4598_; lean_object* v___x_4600_; uint8_t v_isShared_4601_; uint8_t v_isSharedCheck_4617_; 
v_a_4598_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4617_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4617_ == 0)
{
v___x_4600_ = v___x_4597_;
v_isShared_4601_ = v_isSharedCheck_4617_;
goto v_resetjp_4599_;
}
else
{
lean_inc(v_a_4598_);
lean_dec(v___x_4597_);
v___x_4600_ = lean_box(0);
v_isShared_4601_ = v_isSharedCheck_4617_;
goto v_resetjp_4599_;
}
v_resetjp_4599_:
{
if (lean_obj_tag(v_a_4598_) == 0)
{
lean_object* v___x_4602_; lean_object* v___x_4604_; 
lean_dec(v_mvarId_4580_);
lean_dec_ref(v_config_4579_);
v___x_4602_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4602_, 0, v_a_4598_);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 0, v___x_4602_);
v___x_4604_ = v___x_4594_;
goto v_reusejp_4603_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v___x_4602_);
lean_ctor_set(v_reuseFailAlloc_4608_, 1, v_snd_4592_);
v___x_4604_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4603_;
}
v_reusejp_4603_:
{
lean_object* v___x_4606_; 
if (v_isShared_4601_ == 0)
{
lean_ctor_set(v___x_4600_, 0, v___x_4604_);
v___x_4606_ = v___x_4600_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v___x_4604_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
else
{
lean_object* v_a_4609_; lean_object* v___x_4610_; lean_object* v___x_4612_; 
lean_del_object(v___x_4600_);
lean_dec(v_snd_4592_);
v_a_4609_ = lean_ctor_get(v_a_4598_, 0);
lean_inc(v_a_4609_);
lean_dec_ref_known(v_a_4598_, 1);
v___x_4610_ = lean_box(0);
if (v_isShared_4595_ == 0)
{
lean_ctor_set(v___x_4594_, 1, v_a_4609_);
lean_ctor_set(v___x_4594_, 0, v___x_4610_);
v___x_4612_ = v___x_4594_;
goto v_reusejp_4611_;
}
else
{
lean_object* v_reuseFailAlloc_4616_; 
v_reuseFailAlloc_4616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4616_, 0, v___x_4610_);
lean_ctor_set(v_reuseFailAlloc_4616_, 1, v_a_4609_);
v___x_4612_ = v_reuseFailAlloc_4616_;
goto v_reusejp_4611_;
}
v_reusejp_4611_:
{
size_t v___x_4613_; size_t v___x_4614_; 
v___x_4613_ = ((size_t)1ULL);
v___x_4614_ = lean_usize_add(v_i_4583_, v___x_4613_);
v_i_4583_ = v___x_4614_;
v_b_4584_ = v___x_4612_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4618_; lean_object* v___x_4620_; uint8_t v_isShared_4621_; uint8_t v_isSharedCheck_4625_; 
lean_del_object(v___x_4594_);
lean_dec(v_snd_4592_);
lean_dec(v_mvarId_4580_);
lean_dec_ref(v_config_4579_);
v_a_4618_ = lean_ctor_get(v___x_4597_, 0);
v_isSharedCheck_4625_ = !lean_is_exclusive(v___x_4597_);
if (v_isSharedCheck_4625_ == 0)
{
v___x_4620_ = v___x_4597_;
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
else
{
lean_inc(v_a_4618_);
lean_dec(v___x_4597_);
v___x_4620_ = lean_box(0);
v_isShared_4621_ = v_isSharedCheck_4625_;
goto v_resetjp_4619_;
}
v_resetjp_4619_:
{
lean_object* v___x_4623_; 
if (v_isShared_4621_ == 0)
{
v___x_4623_ = v___x_4620_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v_a_4618_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4628_, lean_object* v_config_4629_, lean_object* v_mvarId_4630_, lean_object* v_as_4631_, lean_object* v_sz_4632_, lean_object* v_i_4633_, lean_object* v_b_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_){
_start:
{
size_t v_sz_boxed_4640_; size_t v_i_boxed_4641_; lean_object* v_res_4642_; 
v_sz_boxed_4640_ = lean_unbox_usize(v_sz_4632_);
lean_dec(v_sz_4632_);
v_i_boxed_4641_ = lean_unbox_usize(v_i_4633_);
lean_dec(v_i_4633_);
v_res_4642_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4628_, v_config_4629_, v_mvarId_4630_, v_as_4631_, v_sz_boxed_4640_, v_i_boxed_4641_, v_b_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec(v___y_4636_);
lean_dec_ref(v___y_4635_);
lean_dec_ref(v_as_4631_);
lean_dec_ref(v_init_4628_);
return v_res_4642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4643_, lean_object* v_config_4644_, lean_object* v_mvarId_4645_, lean_object* v_n_4646_, lean_object* v_b_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4643_, v_config_4644_, v_mvarId_4645_, v_n_4646_, v_b_4647_, v___y_4648_, v___y_4649_, v___y_4650_, v___y_4651_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v___y_4649_);
lean_dec_ref(v___y_4648_);
lean_dec_ref(v_n_4646_);
lean_dec_ref(v_init_4643_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4654_, lean_object* v_mvarId_4655_, lean_object* v_t_4656_, lean_object* v_init_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v_root_4663_; lean_object* v_tail_4664_; lean_object* v___x_4665_; 
v_root_4663_ = lean_ctor_get(v_t_4656_, 0);
v_tail_4664_ = lean_ctor_get(v_t_4656_, 1);
lean_inc(v_mvarId_4655_);
lean_inc_ref(v_config_4654_);
lean_inc_ref(v_init_4657_);
v___x_4665_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4657_, v_config_4654_, v_mvarId_4655_, v_root_4663_, v_init_4657_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
lean_dec_ref(v_init_4657_);
if (lean_obj_tag(v___x_4665_) == 0)
{
lean_object* v_a_4666_; lean_object* v___x_4668_; uint8_t v_isShared_4669_; uint8_t v_isSharedCheck_4702_; 
v_a_4666_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4702_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4702_ == 0)
{
v___x_4668_ = v___x_4665_;
v_isShared_4669_ = v_isSharedCheck_4702_;
goto v_resetjp_4667_;
}
else
{
lean_inc(v_a_4666_);
lean_dec(v___x_4665_);
v___x_4668_ = lean_box(0);
v_isShared_4669_ = v_isSharedCheck_4702_;
goto v_resetjp_4667_;
}
v_resetjp_4667_:
{
if (lean_obj_tag(v_a_4666_) == 0)
{
lean_object* v_a_4670_; lean_object* v___x_4672_; 
lean_dec(v_mvarId_4655_);
lean_dec_ref(v_config_4654_);
v_a_4670_ = lean_ctor_get(v_a_4666_, 0);
lean_inc(v_a_4670_);
lean_dec_ref_known(v_a_4666_, 1);
if (v_isShared_4669_ == 0)
{
lean_ctor_set(v___x_4668_, 0, v_a_4670_);
v___x_4672_ = v___x_4668_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4673_; 
v_reuseFailAlloc_4673_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4673_, 0, v_a_4670_);
v___x_4672_ = v_reuseFailAlloc_4673_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
return v___x_4672_;
}
}
else
{
lean_object* v_a_4674_; lean_object* v___x_4675_; lean_object* v___x_4676_; size_t v_sz_4677_; size_t v___x_4678_; lean_object* v___x_4679_; 
lean_del_object(v___x_4668_);
v_a_4674_ = lean_ctor_get(v_a_4666_, 0);
lean_inc(v_a_4674_);
lean_dec_ref_known(v_a_4666_, 1);
v___x_4675_ = lean_box(0);
v___x_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4676_, 0, v___x_4675_);
lean_ctor_set(v___x_4676_, 1, v_a_4674_);
v_sz_4677_ = lean_array_size(v_tail_4664_);
v___x_4678_ = ((size_t)0ULL);
v___x_4679_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4654_, v_mvarId_4655_, v_tail_4664_, v_sz_4677_, v___x_4678_, v___x_4676_, v___y_4658_, v___y_4659_, v___y_4660_, v___y_4661_);
if (lean_obj_tag(v___x_4679_) == 0)
{
lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4693_; 
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4693_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4693_ == 0)
{
v___x_4682_ = v___x_4679_;
v_isShared_4683_ = v_isSharedCheck_4693_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4679_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4693_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v_fst_4684_; 
v_fst_4684_ = lean_ctor_get(v_a_4680_, 0);
if (lean_obj_tag(v_fst_4684_) == 0)
{
lean_object* v_snd_4685_; lean_object* v___x_4687_; 
v_snd_4685_ = lean_ctor_get(v_a_4680_, 1);
lean_inc(v_snd_4685_);
lean_dec(v_a_4680_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v_snd_4685_);
v___x_4687_ = v___x_4682_;
goto v_reusejp_4686_;
}
else
{
lean_object* v_reuseFailAlloc_4688_; 
v_reuseFailAlloc_4688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4688_, 0, v_snd_4685_);
v___x_4687_ = v_reuseFailAlloc_4688_;
goto v_reusejp_4686_;
}
v_reusejp_4686_:
{
return v___x_4687_;
}
}
else
{
lean_object* v_val_4689_; lean_object* v___x_4691_; 
lean_inc_ref(v_fst_4684_);
lean_dec(v_a_4680_);
v_val_4689_ = lean_ctor_get(v_fst_4684_, 0);
lean_inc(v_val_4689_);
lean_dec_ref_known(v_fst_4684_, 1);
if (v_isShared_4683_ == 0)
{
lean_ctor_set(v___x_4682_, 0, v_val_4689_);
v___x_4691_ = v___x_4682_;
goto v_reusejp_4690_;
}
else
{
lean_object* v_reuseFailAlloc_4692_; 
v_reuseFailAlloc_4692_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4692_, 0, v_val_4689_);
v___x_4691_ = v_reuseFailAlloc_4692_;
goto v_reusejp_4690_;
}
v_reusejp_4690_:
{
return v___x_4691_;
}
}
}
}
else
{
lean_object* v_a_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4701_; 
v_a_4694_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4701_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4701_ == 0)
{
v___x_4696_ = v___x_4679_;
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_a_4694_);
lean_dec(v___x_4679_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4701_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
lean_object* v___x_4699_; 
if (v_isShared_4697_ == 0)
{
v___x_4699_ = v___x_4696_;
goto v_reusejp_4698_;
}
else
{
lean_object* v_reuseFailAlloc_4700_; 
v_reuseFailAlloc_4700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
v___x_4699_ = v_reuseFailAlloc_4700_;
goto v_reusejp_4698_;
}
v_reusejp_4698_:
{
return v___x_4699_;
}
}
}
}
}
}
else
{
lean_object* v_a_4703_; lean_object* v___x_4705_; uint8_t v_isShared_4706_; uint8_t v_isSharedCheck_4710_; 
lean_dec(v_mvarId_4655_);
lean_dec_ref(v_config_4654_);
v_a_4703_ = lean_ctor_get(v___x_4665_, 0);
v_isSharedCheck_4710_ = !lean_is_exclusive(v___x_4665_);
if (v_isSharedCheck_4710_ == 0)
{
v___x_4705_ = v___x_4665_;
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
else
{
lean_inc(v_a_4703_);
lean_dec(v___x_4665_);
v___x_4705_ = lean_box(0);
v_isShared_4706_ = v_isSharedCheck_4710_;
goto v_resetjp_4704_;
}
v_resetjp_4704_:
{
lean_object* v___x_4708_; 
if (v_isShared_4706_ == 0)
{
v___x_4708_ = v___x_4705_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4709_; 
v_reuseFailAlloc_4709_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4709_, 0, v_a_4703_);
v___x_4708_ = v_reuseFailAlloc_4709_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
return v___x_4708_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4711_, lean_object* v_mvarId_4712_, lean_object* v_t_4713_, lean_object* v_init_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_){
_start:
{
lean_object* v_res_4720_; 
v_res_4720_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4711_, v_mvarId_4712_, v_t_4713_, v_init_4714_, v___y_4715_, v___y_4716_, v___y_4717_, v___y_4718_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
lean_dec_ref(v_t_4713_);
return v_res_4720_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4721_, lean_object* v___x_4722_, lean_object* v_config_4723_, lean_object* v___y_4724_, lean_object* v___y_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_){
_start:
{
lean_object* v___x_4729_; 
lean_inc(v_mvarId_4721_);
v___x_4729_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4721_, v___x_4722_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_);
if (lean_obj_tag(v___x_4729_) == 0)
{
lean_object* v___x_4730_; 
lean_dec_ref_known(v___x_4729_, 1);
lean_inc(v_mvarId_4721_);
v___x_4730_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4721_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_);
if (lean_obj_tag(v___x_4730_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4733_; uint8_t v_isShared_4734_; uint8_t v_isSharedCheck_4764_; 
v_a_4731_ = lean_ctor_get(v___x_4730_, 0);
v_isSharedCheck_4764_ = !lean_is_exclusive(v___x_4730_);
if (v_isSharedCheck_4764_ == 0)
{
v___x_4733_ = v___x_4730_;
v_isShared_4734_ = v_isSharedCheck_4764_;
goto v_resetjp_4732_;
}
else
{
lean_inc(v_a_4731_);
lean_dec(v___x_4730_);
v___x_4733_ = lean_box(0);
v_isShared_4734_ = v_isSharedCheck_4764_;
goto v_resetjp_4732_;
}
v_resetjp_4732_:
{
uint8_t v___x_4735_; 
v___x_4735_ = lean_unbox(v_a_4731_);
if (v___x_4735_ == 0)
{
lean_object* v_lctx_4736_; lean_object* v_decls_4737_; lean_object* v___x_4738_; lean_object* v___x_4739_; 
lean_del_object(v___x_4733_);
v_lctx_4736_ = lean_ctor_get(v___y_4724_, 2);
v_decls_4737_ = lean_ctor_get(v_lctx_4736_, 1);
v___x_4738_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4739_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4723_, v_mvarId_4721_, v_decls_4737_, v___x_4738_, v___y_4724_, v___y_4725_, v___y_4726_, v___y_4727_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4752_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4752_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4752_ == 0)
{
v___x_4742_ = v___x_4739_;
v_isShared_4743_ = v_isSharedCheck_4752_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4739_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4752_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v_fst_4744_; 
v_fst_4744_ = lean_ctor_get(v_a_4740_, 0);
lean_inc(v_fst_4744_);
lean_dec(v_a_4740_);
if (lean_obj_tag(v_fst_4744_) == 0)
{
lean_object* v___x_4746_; 
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v_a_4731_);
v___x_4746_ = v___x_4742_;
goto v_reusejp_4745_;
}
else
{
lean_object* v_reuseFailAlloc_4747_; 
v_reuseFailAlloc_4747_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4747_, 0, v_a_4731_);
v___x_4746_ = v_reuseFailAlloc_4747_;
goto v_reusejp_4745_;
}
v_reusejp_4745_:
{
return v___x_4746_;
}
}
else
{
lean_object* v_val_4748_; lean_object* v___x_4750_; 
lean_dec(v_a_4731_);
v_val_4748_ = lean_ctor_get(v_fst_4744_, 0);
lean_inc(v_val_4748_);
lean_dec_ref_known(v_fst_4744_, 1);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v_val_4748_);
v___x_4750_ = v___x_4742_;
goto v_reusejp_4749_;
}
else
{
lean_object* v_reuseFailAlloc_4751_; 
v_reuseFailAlloc_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4751_, 0, v_val_4748_);
v___x_4750_ = v_reuseFailAlloc_4751_;
goto v_reusejp_4749_;
}
v_reusejp_4749_:
{
return v___x_4750_;
}
}
}
}
else
{
lean_object* v_a_4753_; lean_object* v___x_4755_; uint8_t v_isShared_4756_; uint8_t v_isSharedCheck_4760_; 
lean_dec(v_a_4731_);
v_a_4753_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4760_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4760_ == 0)
{
v___x_4755_ = v___x_4739_;
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
else
{
lean_inc(v_a_4753_);
lean_dec(v___x_4739_);
v___x_4755_ = lean_box(0);
v_isShared_4756_ = v_isSharedCheck_4760_;
goto v_resetjp_4754_;
}
v_resetjp_4754_:
{
lean_object* v___x_4758_; 
if (v_isShared_4756_ == 0)
{
v___x_4758_ = v___x_4755_;
goto v_reusejp_4757_;
}
else
{
lean_object* v_reuseFailAlloc_4759_; 
v_reuseFailAlloc_4759_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4759_, 0, v_a_4753_);
v___x_4758_ = v_reuseFailAlloc_4759_;
goto v_reusejp_4757_;
}
v_reusejp_4757_:
{
return v___x_4758_;
}
}
}
}
else
{
lean_object* v___x_4762_; 
lean_dec_ref(v_config_4723_);
lean_dec(v_mvarId_4721_);
if (v_isShared_4734_ == 0)
{
v___x_4762_ = v___x_4733_;
goto v_reusejp_4761_;
}
else
{
lean_object* v_reuseFailAlloc_4763_; 
v_reuseFailAlloc_4763_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4763_, 0, v_a_4731_);
v___x_4762_ = v_reuseFailAlloc_4763_;
goto v_reusejp_4761_;
}
v_reusejp_4761_:
{
return v___x_4762_;
}
}
}
}
else
{
lean_dec_ref(v_config_4723_);
lean_dec(v_mvarId_4721_);
return v___x_4730_;
}
}
else
{
lean_object* v_a_4765_; lean_object* v___x_4767_; uint8_t v_isShared_4768_; uint8_t v_isSharedCheck_4772_; 
lean_dec_ref(v_config_4723_);
lean_dec(v_mvarId_4721_);
v_a_4765_ = lean_ctor_get(v___x_4729_, 0);
v_isSharedCheck_4772_ = !lean_is_exclusive(v___x_4729_);
if (v_isSharedCheck_4772_ == 0)
{
v___x_4767_ = v___x_4729_;
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
else
{
lean_inc(v_a_4765_);
lean_dec(v___x_4729_);
v___x_4767_ = lean_box(0);
v_isShared_4768_ = v_isSharedCheck_4772_;
goto v_resetjp_4766_;
}
v_resetjp_4766_:
{
lean_object* v___x_4770_; 
if (v_isShared_4768_ == 0)
{
v___x_4770_ = v___x_4767_;
goto v_reusejp_4769_;
}
else
{
lean_object* v_reuseFailAlloc_4771_; 
v_reuseFailAlloc_4771_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4771_, 0, v_a_4765_);
v___x_4770_ = v_reuseFailAlloc_4771_;
goto v_reusejp_4769_;
}
v_reusejp_4769_:
{
return v___x_4770_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4773_, lean_object* v___x_4774_, lean_object* v_config_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4773_, v___x_4774_, v_config_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
lean_dec(v___y_4777_);
lean_dec_ref(v___y_4776_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4784_, lean_object* v_config_4785_, lean_object* v_a_4786_, lean_object* v_a_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_){
_start:
{
lean_object* v___x_4791_; lean_object* v___f_4792_; lean_object* v___x_4793_; 
v___x_4791_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4784_);
v___f_4792_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4792_, 0, v_mvarId_4784_);
lean_closure_set(v___f_4792_, 1, v___x_4791_);
lean_closure_set(v___f_4792_, 2, v_config_4785_);
v___x_4793_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4784_, v___f_4792_, v_a_4786_, v_a_4787_, v_a_4788_, v_a_4789_);
return v___x_4793_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4794_, lean_object* v_config_4795_, lean_object* v_a_4796_, lean_object* v_a_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_){
_start:
{
lean_object* v_res_4801_; 
v_res_4801_ = l_Lean_MVarId_contradictionCore(v_mvarId_4794_, v_config_4795_, v_a_4796_, v_a_4797_, v_a_4798_, v_a_4799_);
lean_dec(v_a_4799_);
lean_dec_ref(v_a_4798_);
lean_dec(v_a_4797_);
lean_dec_ref(v_a_4796_);
return v_res_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4802_, lean_object* v_config_4803_, lean_object* v_a_4804_, lean_object* v_a_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_){
_start:
{
lean_object* v___x_4809_; 
lean_inc(v_mvarId_4802_);
v___x_4809_ = l_Lean_MVarId_contradictionCore(v_mvarId_4802_, v_config_4803_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
if (lean_obj_tag(v___x_4809_) == 0)
{
lean_object* v_a_4810_; lean_object* v___x_4812_; uint8_t v_isShared_4813_; uint8_t v_isSharedCheck_4822_; 
v_a_4810_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4822_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4822_ == 0)
{
v___x_4812_ = v___x_4809_;
v_isShared_4813_ = v_isSharedCheck_4822_;
goto v_resetjp_4811_;
}
else
{
lean_inc(v_a_4810_);
lean_dec(v___x_4809_);
v___x_4812_ = lean_box(0);
v_isShared_4813_ = v_isSharedCheck_4822_;
goto v_resetjp_4811_;
}
v_resetjp_4811_:
{
uint8_t v___x_4814_; 
v___x_4814_ = lean_unbox(v_a_4810_);
lean_dec(v_a_4810_);
if (v___x_4814_ == 0)
{
lean_object* v___x_4815_; lean_object* v___x_4816_; lean_object* v___x_4817_; 
lean_del_object(v___x_4812_);
v___x_4815_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4816_ = lean_box(0);
v___x_4817_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4815_, v_mvarId_4802_, v___x_4816_, v_a_4804_, v_a_4805_, v_a_4806_, v_a_4807_);
return v___x_4817_;
}
else
{
lean_object* v___x_4818_; lean_object* v___x_4820_; 
lean_dec(v_mvarId_4802_);
v___x_4818_ = lean_box(0);
if (v_isShared_4813_ == 0)
{
lean_ctor_set(v___x_4812_, 0, v___x_4818_);
v___x_4820_ = v___x_4812_;
goto v_reusejp_4819_;
}
else
{
lean_object* v_reuseFailAlloc_4821_; 
v_reuseFailAlloc_4821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4821_, 0, v___x_4818_);
v___x_4820_ = v_reuseFailAlloc_4821_;
goto v_reusejp_4819_;
}
v_reusejp_4819_:
{
return v___x_4820_;
}
}
}
}
else
{
lean_object* v_a_4823_; lean_object* v___x_4825_; uint8_t v_isShared_4826_; uint8_t v_isSharedCheck_4830_; 
lean_dec(v_mvarId_4802_);
v_a_4823_ = lean_ctor_get(v___x_4809_, 0);
v_isSharedCheck_4830_ = !lean_is_exclusive(v___x_4809_);
if (v_isSharedCheck_4830_ == 0)
{
v___x_4825_ = v___x_4809_;
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
else
{
lean_inc(v_a_4823_);
lean_dec(v___x_4809_);
v___x_4825_ = lean_box(0);
v_isShared_4826_ = v_isSharedCheck_4830_;
goto v_resetjp_4824_;
}
v_resetjp_4824_:
{
lean_object* v___x_4828_; 
if (v_isShared_4826_ == 0)
{
v___x_4828_ = v___x_4825_;
goto v_reusejp_4827_;
}
else
{
lean_object* v_reuseFailAlloc_4829_; 
v_reuseFailAlloc_4829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4829_, 0, v_a_4823_);
v___x_4828_ = v_reuseFailAlloc_4829_;
goto v_reusejp_4827_;
}
v_reusejp_4827_:
{
return v___x_4828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4831_, lean_object* v_config_4832_, lean_object* v_a_4833_, lean_object* v_a_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_){
_start:
{
lean_object* v_res_4838_; 
v_res_4838_ = l_Lean_MVarId_contradiction(v_mvarId_4831_, v_config_4832_, v_a_4833_, v_a_4834_, v_a_4835_, v_a_4836_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
lean_dec(v_a_4834_);
lean_dec_ref(v_a_4833_);
return v_res_4838_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4901_; uint8_t v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; 
v___x_4901_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4902_ = 0;
v___x_4903_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4904_ = l_Lean_registerTraceClass(v___x_4901_, v___x_4902_, v___x_4903_);
return v___x_4904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4905_){
_start:
{
lean_object* v_res_4906_; 
v_res_4906_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4906_;
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
