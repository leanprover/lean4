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
size_t v_x_1112__boxed_157_; size_t v_x_1113__boxed_158_; lean_object* v_res_159_; 
v_x_1112__boxed_157_ = lean_unbox_usize(v_x_153_);
lean_dec(v_x_153_);
v_x_1113__boxed_158_ = lean_unbox_usize(v_x_154_);
lean_dec(v_x_154_);
v_res_159_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_152_, v_x_1112__boxed_157_, v_x_1113__boxed_158_, v_x_155_, v_x_156_);
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
lean_object* v___x_171_; lean_object* v_mctx_172_; lean_object* v_cache_173_; lean_object* v_zetaDeltaFVarIds_174_; lean_object* v_postponed_175_; lean_object* v_diag_176_; lean_object* v___x_178_; uint8_t v_isShared_179_; uint8_t v_isSharedCheck_205_; 
v___x_171_ = lean_st_ref_take(v___y_169_);
v_mctx_172_ = lean_ctor_get(v___x_171_, 0);
v_cache_173_ = lean_ctor_get(v___x_171_, 1);
v_zetaDeltaFVarIds_174_ = lean_ctor_get(v___x_171_, 2);
v_postponed_175_ = lean_ctor_get(v___x_171_, 3);
v_diag_176_ = lean_ctor_get(v___x_171_, 4);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_205_ == 0)
{
v___x_178_ = v___x_171_;
v_isShared_179_ = v_isSharedCheck_205_;
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
v_isShared_179_ = v_isSharedCheck_205_;
goto v_resetjp_177_;
}
v_resetjp_177_:
{
lean_object* v_depth_180_; lean_object* v_levelAssignDepth_181_; lean_object* v_lmvarCounter_182_; lean_object* v_mvarCounter_183_; lean_object* v_lDecls_184_; lean_object* v_decls_185_; lean_object* v_userNames_186_; lean_object* v_lAssignment_187_; lean_object* v_eAssignment_188_; lean_object* v_dAssignment_189_; lean_object* v_instanceTypedMVars_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_204_; 
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
v_instanceTypedMVars_190_ = lean_ctor_get(v_mctx_172_, 10);
v_isSharedCheck_204_ = !lean_is_exclusive(v_mctx_172_);
if (v_isSharedCheck_204_ == 0)
{
v___x_192_ = v_mctx_172_;
v_isShared_193_ = v_isSharedCheck_204_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_instanceTypedMVars_190_);
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
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_204_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_194_; lean_object* v___x_196_; 
v___x_194_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_eAssignment_188_, v_mvarId_167_, v_val_168_);
if (v_isShared_193_ == 0)
{
lean_ctor_set(v___x_192_, 8, v___x_194_);
v___x_196_ = v___x_192_;
goto v_reusejp_195_;
}
else
{
lean_object* v_reuseFailAlloc_203_; 
v_reuseFailAlloc_203_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_203_, 0, v_depth_180_);
lean_ctor_set(v_reuseFailAlloc_203_, 1, v_levelAssignDepth_181_);
lean_ctor_set(v_reuseFailAlloc_203_, 2, v_lmvarCounter_182_);
lean_ctor_set(v_reuseFailAlloc_203_, 3, v_mvarCounter_183_);
lean_ctor_set(v_reuseFailAlloc_203_, 4, v_lDecls_184_);
lean_ctor_set(v_reuseFailAlloc_203_, 5, v_decls_185_);
lean_ctor_set(v_reuseFailAlloc_203_, 6, v_userNames_186_);
lean_ctor_set(v_reuseFailAlloc_203_, 7, v_lAssignment_187_);
lean_ctor_set(v_reuseFailAlloc_203_, 8, v___x_194_);
lean_ctor_set(v_reuseFailAlloc_203_, 9, v_dAssignment_189_);
lean_ctor_set(v_reuseFailAlloc_203_, 10, v_instanceTypedMVars_190_);
v___x_196_ = v_reuseFailAlloc_203_;
goto v_reusejp_195_;
}
v_reusejp_195_:
{
lean_object* v___x_198_; 
if (v_isShared_179_ == 0)
{
lean_ctor_set(v___x_178_, 0, v___x_196_);
v___x_198_ = v___x_178_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_196_);
lean_ctor_set(v_reuseFailAlloc_202_, 1, v_cache_173_);
lean_ctor_set(v_reuseFailAlloc_202_, 2, v_zetaDeltaFVarIds_174_);
lean_ctor_set(v_reuseFailAlloc_202_, 3, v_postponed_175_);
lean_ctor_set(v_reuseFailAlloc_202_, 4, v_diag_176_);
v___x_198_ = v_reuseFailAlloc_202_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_199_ = lean_st_ref_put(v___y_169_, v___x_198_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_201_, 0, v___x_200_);
return v___x_201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg___boxed(lean_object* v_mvarId_206_, lean_object* v_val_207_, lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_206_, v_val_207_, v___y_208_);
lean_dec(v___y_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(lean_object* v_mvarId_212_, lean_object* v_a_213_, lean_object* v_a_214_, lean_object* v_a_215_, lean_object* v_a_216_){
_start:
{
lean_object* v___x_218_; 
lean_inc(v_mvarId_212_);
v___x_218_ = l_Lean_MVarId_getType(v_mvarId_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_218_) == 0)
{
lean_object* v_a_219_; lean_object* v___x_221_; uint8_t v_isShared_222_; uint8_t v_isSharedCheck_263_; 
v_a_219_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_263_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_263_ == 0)
{
v___x_221_ = v___x_218_;
v_isShared_222_ = v_isSharedCheck_263_;
goto v_resetjp_220_;
}
else
{
lean_inc(v_a_219_);
lean_dec(v___x_218_);
v___x_221_ = lean_box(0);
v_isShared_222_ = v_isSharedCheck_263_;
goto v_resetjp_220_;
}
v_resetjp_220_:
{
lean_object* v___f_223_; lean_object* v___x_224_; 
v___f_223_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___closed__0));
v___x_224_ = lean_find_expr(v___f_223_, v_a_219_);
lean_dec(v_a_219_);
if (lean_obj_tag(v___x_224_) == 1)
{
lean_object* v_val_225_; lean_object* v___x_226_; 
lean_del_object(v___x_221_);
v_val_225_ = lean_ctor_get(v___x_224_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v___x_224_, 1);
lean_inc(v_mvarId_212_);
v___x_226_ = l_Lean_MVarId_getType(v_mvarId_212_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = l_Lean_Expr_appArg_x21(v_val_225_);
lean_dec(v_val_225_);
v___x_229_ = l_Lean_Meta_mkFalseElim(v_a_227_, v___x_228_, v_a_213_, v_a_214_, v_a_215_, v_a_216_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_240_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
v___x_231_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_212_, v_a_230_, v_a_214_);
v_isSharedCheck_240_ = !lean_is_exclusive(v___x_231_);
if (v_isSharedCheck_240_ == 0)
{
lean_object* v_unused_241_; 
v_unused_241_ = lean_ctor_get(v___x_231_, 0);
lean_dec(v_unused_241_);
v___x_233_ = v___x_231_;
v_isShared_234_ = v_isSharedCheck_240_;
goto v_resetjp_232_;
}
else
{
lean_dec(v___x_231_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_240_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
uint8_t v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_235_ = 1;
v___x_236_ = lean_box(v___x_235_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 0, v___x_236_);
v___x_238_ = v___x_233_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v___x_236_);
v___x_238_ = v_reuseFailAlloc_239_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
return v___x_238_;
}
}
}
else
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
lean_dec(v_mvarId_212_);
v_a_242_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_229_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_229_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
lean_dec(v_val_225_);
lean_dec(v_mvarId_212_);
v_a_250_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_226_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_226_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
else
{
uint8_t v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
lean_dec(v___x_224_);
lean_dec(v_mvarId_212_);
v___x_258_ = 0;
v___x_259_ = lean_box(v___x_258_);
if (v_isShared_222_ == 0)
{
lean_ctor_set(v___x_221_, 0, v___x_259_);
v___x_261_ = v___x_221_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
}
}
else
{
lean_object* v_a_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_271_; 
lean_dec(v_mvarId_212_);
v_a_264_ = lean_ctor_get(v___x_218_, 0);
v_isSharedCheck_271_ = !lean_is_exclusive(v___x_218_);
if (v_isSharedCheck_271_ == 0)
{
v___x_266_ = v___x_218_;
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_a_264_);
lean_dec(v___x_218_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_271_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_269_; 
if (v_isShared_267_ == 0)
{
v___x_269_ = v___x_266_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_a_264_);
v___x_269_ = v_reuseFailAlloc_270_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
return v___x_269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim___boxed(lean_object* v_mvarId_272_, lean_object* v_a_273_, lean_object* v_a_274_, lean_object* v_a_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v_res_278_; 
v_res_278_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_272_, v_a_273_, v_a_274_, v_a_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_a_275_);
lean_dec(v_a_274_);
lean_dec_ref(v_a_273_);
return v_res_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(lean_object* v_mvarId_279_, lean_object* v_val_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_279_, v_val_280_, v___y_282_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___boxed(lean_object* v_mvarId_287_, lean_object* v_val_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0(v_mvarId_287_, v_val_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_);
lean_dec(v___y_292_);
lean_dec_ref(v___y_291_);
lean_dec(v___y_290_);
lean_dec_ref(v___y_289_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0(lean_object* v_00_u03b2_295_, lean_object* v_x_296_, lean_object* v_x_297_, lean_object* v_x_298_){
_start:
{
lean_object* v___x_299_; 
v___x_299_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0___redArg(v_x_296_, v_x_297_, v_x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_300_, lean_object* v_x_301_, size_t v_x_302_, size_t v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v___x_306_; 
v___x_306_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___redArg(v_x_301_, v_x_302_, v_x_303_, v_x_304_, v_x_305_);
return v___x_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_307_, lean_object* v_x_308_, lean_object* v_x_309_, lean_object* v_x_310_, lean_object* v_x_311_, lean_object* v_x_312_){
_start:
{
size_t v_x_1467__boxed_313_; size_t v_x_1468__boxed_314_; lean_object* v_res_315_; 
v_x_1467__boxed_313_ = lean_unbox_usize(v_x_309_);
lean_dec(v_x_309_);
v_x_1468__boxed_314_ = lean_unbox_usize(v_x_310_);
lean_dec(v_x_310_);
v_res_315_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1(v_00_u03b2_307_, v_x_308_, v_x_1467__boxed_313_, v_x_1468__boxed_314_, v_x_311_, v_x_312_);
return v_res_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_316_, lean_object* v_n_317_, lean_object* v_k_318_, lean_object* v_v_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2___redArg(v_n_317_, v_k_318_, v_v_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_321_, size_t v_depth_322_, lean_object* v_keys_323_, lean_object* v_vals_324_, lean_object* v_heq_325_, lean_object* v_i_326_, lean_object* v_entries_327_){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_322_, v_keys_323_, v_vals_324_, v_i_326_, v_entries_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_329_, lean_object* v_depth_330_, lean_object* v_keys_331_, lean_object* v_vals_332_, lean_object* v_heq_333_, lean_object* v_i_334_, lean_object* v_entries_335_){
_start:
{
size_t v_depth_boxed_336_; lean_object* v_res_337_; 
v_depth_boxed_336_ = lean_unbox_usize(v_depth_330_);
lean_dec(v_depth_330_);
v_res_337_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_329_, v_depth_boxed_336_, v_keys_331_, v_vals_332_, v_heq_333_, v_i_334_, v_entries_335_);
lean_dec_ref(v_vals_332_);
lean_dec_ref(v_keys_331_);
return v_res_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_338_, lean_object* v_x_339_, lean_object* v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_339_, v_x_340_, v_x_341_, v_x_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(lean_object* v_fvarId_344_, lean_object* v_a_345_, lean_object* v_a_346_, lean_object* v_a_347_, lean_object* v_a_348_){
_start:
{
lean_object* v___x_354_; 
v___x_354_ = l_Lean_FVarId_getType___redArg(v_fvarId_344_, v_a_345_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_354_) == 0)
{
lean_object* v_a_355_; lean_object* v___x_356_; 
v_a_355_ = lean_ctor_get(v___x_354_, 0);
lean_inc(v_a_355_);
lean_dec_ref_known(v___x_354_, 1);
v___x_356_ = l_Lean_Meta_whnfD(v_a_355_, v_a_345_, v_a_346_, v_a_347_, v_a_348_);
if (lean_obj_tag(v___x_356_) == 0)
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_383_; 
v_a_357_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_383_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_383_ == 0)
{
v___x_359_ = v___x_356_;
v_isShared_360_ = v_isSharedCheck_383_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_356_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_383_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_361_; 
v___x_361_ = l_Lean_Expr_getAppFn(v_a_357_);
lean_dec(v_a_357_);
if (lean_obj_tag(v___x_361_) == 4)
{
lean_object* v_declName_362_; lean_object* v___x_363_; lean_object* v_env_364_; uint8_t v___x_365_; lean_object* v___x_366_; 
v_declName_362_ = lean_ctor_get(v___x_361_, 0);
lean_inc(v_declName_362_);
lean_dec_ref_known(v___x_361_, 2);
v___x_363_ = lean_st_ref_get(v_a_348_);
v_env_364_ = lean_ctor_get(v___x_363_, 0);
lean_inc_ref(v_env_364_);
lean_dec(v___x_363_);
v___x_365_ = 0;
v___x_366_ = l_Lean_Environment_find_x3f(v_env_364_, v_declName_362_, v___x_365_);
if (lean_obj_tag(v___x_366_) == 0)
{
lean_del_object(v___x_359_);
goto v___jp_350_;
}
else
{
lean_object* v_val_367_; 
v_val_367_ = lean_ctor_get(v___x_366_, 0);
lean_inc(v_val_367_);
lean_dec_ref_known(v___x_366_, 1);
if (lean_obj_tag(v_val_367_) == 5)
{
lean_object* v_val_368_; lean_object* v_numIndices_369_; lean_object* v_ctors_370_; lean_object* v___x_371_; lean_object* v___x_372_; uint8_t v___x_373_; 
v_val_368_ = lean_ctor_get(v_val_367_, 0);
lean_inc_ref(v_val_368_);
lean_dec_ref_known(v_val_367_, 1);
v_numIndices_369_ = lean_ctor_get(v_val_368_, 2);
lean_inc(v_numIndices_369_);
v_ctors_370_ = lean_ctor_get(v_val_368_, 4);
lean_inc(v_ctors_370_);
lean_dec_ref(v_val_368_);
v___x_371_ = l_List_lengthTR___redArg(v_ctors_370_);
lean_dec(v_ctors_370_);
v___x_372_ = lean_unsigned_to_nat(0u);
v___x_373_ = lean_nat_dec_eq(v___x_371_, v___x_372_);
lean_dec(v___x_371_);
if (v___x_373_ == 0)
{
uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_377_; 
v___x_374_ = lean_nat_dec_lt(v___x_372_, v_numIndices_369_);
lean_dec(v_numIndices_369_);
v___x_375_ = lean_box(v___x_374_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_375_);
v___x_377_ = v___x_359_;
goto v_reusejp_376_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
v___x_377_ = v_reuseFailAlloc_378_;
goto v_reusejp_376_;
}
v_reusejp_376_:
{
return v___x_377_;
}
}
else
{
lean_object* v___x_379_; lean_object* v___x_381_; 
lean_dec(v_numIndices_369_);
v___x_379_ = lean_box(v___x_373_);
if (v_isShared_360_ == 0)
{
lean_ctor_set(v___x_359_, 0, v___x_379_);
v___x_381_ = v___x_359_;
goto v_reusejp_380_;
}
else
{
lean_object* v_reuseFailAlloc_382_; 
v_reuseFailAlloc_382_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_382_, 0, v___x_379_);
v___x_381_ = v_reuseFailAlloc_382_;
goto v_reusejp_380_;
}
v_reusejp_380_:
{
return v___x_381_;
}
}
}
else
{
lean_dec(v_val_367_);
lean_del_object(v___x_359_);
goto v___jp_350_;
}
}
}
else
{
lean_dec_ref(v___x_361_);
lean_del_object(v___x_359_);
goto v___jp_350_;
}
}
}
else
{
lean_object* v_a_384_; lean_object* v___x_386_; uint8_t v_isShared_387_; uint8_t v_isSharedCheck_391_; 
v_a_384_ = lean_ctor_get(v___x_356_, 0);
v_isSharedCheck_391_ = !lean_is_exclusive(v___x_356_);
if (v_isSharedCheck_391_ == 0)
{
v___x_386_ = v___x_356_;
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
else
{
lean_inc(v_a_384_);
lean_dec(v___x_356_);
v___x_386_ = lean_box(0);
v_isShared_387_ = v_isSharedCheck_391_;
goto v_resetjp_385_;
}
v_resetjp_385_:
{
lean_object* v___x_389_; 
if (v_isShared_387_ == 0)
{
v___x_389_ = v___x_386_;
goto v_reusejp_388_;
}
else
{
lean_object* v_reuseFailAlloc_390_; 
v_reuseFailAlloc_390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_390_, 0, v_a_384_);
v___x_389_ = v_reuseFailAlloc_390_;
goto v_reusejp_388_;
}
v_reusejp_388_:
{
return v___x_389_;
}
}
}
}
else
{
lean_object* v_a_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_399_; 
v_a_392_ = lean_ctor_get(v___x_354_, 0);
v_isSharedCheck_399_ = !lean_is_exclusive(v___x_354_);
if (v_isSharedCheck_399_ == 0)
{
v___x_394_ = v___x_354_;
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_a_392_);
lean_dec(v___x_354_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_399_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_398_; 
v_reuseFailAlloc_398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_398_, 0, v_a_392_);
v___x_397_ = v_reuseFailAlloc_398_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
return v___x_397_;
}
}
}
v___jp_350_:
{
uint8_t v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_351_ = 0;
v___x_352_ = lean_box(v___x_351_);
v___x_353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_353_, 0, v___x_352_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate___boxed(lean_object* v_fvarId_400_, lean_object* v_a_401_, lean_object* v_a_402_, lean_object* v_a_403_, lean_object* v_a_404_, lean_object* v_a_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_400_, v_a_401_, v_a_402_, v_a_403_, v_a_404_);
lean_dec(v_a_404_);
lean_dec_ref(v_a_403_);
lean_dec(v_a_402_);
lean_dec_ref(v_a_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(lean_object* v_s_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_){
_start:
{
lean_object* v___x_414_; 
v___x_414_ = l_Lean_Meta_SavedState_restore___redArg(v_s_407_, v___y_410_, v___y_412_);
return v___x_414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0___boxed(lean_object* v_s_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l_Lean_Meta_ElimEmptyInductive_instMonadBacktrackSavedStateM___lam__0(v_s_415_, v___y_416_, v___y_417_, v___y_418_, v___y_419_, v___y_420_);
lean_dec(v___y_420_);
lean_dec_ref(v___y_419_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v_s_415_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(lean_object* v_x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_){
_start:
{
lean_object* v___x_438_; 
lean_inc(v___y_432_);
v___x_438_ = lean_apply_6(v_x_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, lean_box(0));
return v___x_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed(lean_object* v_x_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0(v_x_439_, v___y_440_, v___y_441_, v___y_442_, v___y_443_, v___y_444_);
lean_dec(v___y_440_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(lean_object* v_mvarId_447_, lean_object* v_x_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___f_455_; lean_object* v___x_456_; 
lean_inc(v___y_449_);
v___f_455_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___lam__0___boxed), 7, 2);
lean_closure_set(v___f_455_, 0, v_x_448_);
lean_closure_set(v___f_455_, 1, v___y_449_);
v___x_456_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_447_, v___f_455_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
if (lean_obj_tag(v___x_456_) == 0)
{
return v___x_456_;
}
else
{
lean_object* v_a_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_464_; 
v_a_457_ = lean_ctor_get(v___x_456_, 0);
v_isSharedCheck_464_ = !lean_is_exclusive(v___x_456_);
if (v_isSharedCheck_464_ == 0)
{
v___x_459_ = v___x_456_;
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_a_457_);
lean_dec(v___x_456_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_464_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_462_; 
if (v_isShared_460_ == 0)
{
v___x_462_ = v___x_459_;
goto v_reusejp_461_;
}
else
{
lean_object* v_reuseFailAlloc_463_; 
v_reuseFailAlloc_463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_463_, 0, v_a_457_);
v___x_462_ = v_reuseFailAlloc_463_;
goto v_reusejp_461_;
}
v_reusejp_461_:
{
return v___x_462_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg___boxed(lean_object* v_mvarId_465_, lean_object* v_x_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_, lean_object* v___y_471_, lean_object* v___y_472_){
_start:
{
lean_object* v_res_473_; 
v_res_473_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_465_, v_x_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_, v___y_471_);
lean_dec(v___y_471_);
lean_dec_ref(v___y_470_);
lean_dec(v___y_469_);
lean_dec_ref(v___y_468_);
lean_dec(v___y_467_);
return v_res_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(lean_object* v_00_u03b1_474_, lean_object* v_mvarId_475_, lean_object* v_x_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_){
_start:
{
lean_object* v___x_483_; 
v___x_483_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_475_, v_x_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___boxed(lean_object* v_00_u03b1_484_, lean_object* v_mvarId_485_, lean_object* v_x_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1(v_00_u03b1_484_, v_mvarId_485_, v_x_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_);
lean_dec(v___y_491_);
lean_dec_ref(v___y_490_);
lean_dec(v___y_489_);
lean_dec_ref(v___y_488_);
lean_dec(v___y_487_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(lean_object* v_x_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_Lean_Meta_saveState___redArg(v___y_497_, v___y_499_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v_a_502_; lean_object* v___y_504_; lean_object* v___y_505_; uint8_t v___y_506_; lean_object* v___y_525_; lean_object* v_a_526_; lean_object* v___x_529_; 
v_a_502_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_a_502_);
lean_dec_ref_known(v___x_501_, 1);
lean_inc(v___y_499_);
lean_inc_ref(v___y_498_);
lean_inc(v___y_497_);
lean_inc_ref(v___y_496_);
lean_inc(v___y_495_);
v___x_529_ = lean_apply_6(v_x_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, lean_box(0));
if (lean_obj_tag(v___x_529_) == 0)
{
lean_object* v_a_530_; uint8_t v___x_531_; 
v_a_530_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_530_);
v___x_531_ = lean_unbox(v_a_530_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; 
lean_dec_ref_known(v___x_529_, 1);
v___x_532_ = l_Lean_Meta_SavedState_restore___redArg(v_a_502_, v___y_497_, v___y_499_);
if (lean_obj_tag(v___x_532_) == 0)
{
lean_object* v___x_534_; uint8_t v_isShared_535_; uint8_t v_isSharedCheck_539_; 
lean_dec(v_a_502_);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_539_ == 0)
{
lean_object* v_unused_540_; 
v_unused_540_ = lean_ctor_get(v___x_532_, 0);
lean_dec(v_unused_540_);
v___x_534_ = v___x_532_;
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
else
{
lean_dec(v___x_532_);
v___x_534_ = lean_box(0);
v_isShared_535_ = v_isSharedCheck_539_;
goto v_resetjp_533_;
}
v_resetjp_533_:
{
lean_object* v___x_537_; 
if (v_isShared_535_ == 0)
{
lean_ctor_set(v___x_534_, 0, v_a_530_);
v___x_537_ = v___x_534_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v_a_530_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
else
{
lean_object* v_a_541_; lean_object* v___x_543_; uint8_t v_isShared_544_; uint8_t v_isSharedCheck_548_; 
lean_dec(v_a_530_);
v_a_541_ = lean_ctor_get(v___x_532_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_532_);
if (v_isSharedCheck_548_ == 0)
{
v___x_543_ = v___x_532_;
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
else
{
lean_inc(v_a_541_);
lean_dec(v___x_532_);
v___x_543_ = lean_box(0);
v_isShared_544_ = v_isSharedCheck_548_;
goto v_resetjp_542_;
}
v_resetjp_542_:
{
lean_object* v___x_546_; 
lean_inc(v_a_541_);
if (v_isShared_544_ == 0)
{
v___x_546_ = v___x_543_;
goto v_reusejp_545_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_a_541_);
v___x_546_ = v_reuseFailAlloc_547_;
goto v_reusejp_545_;
}
v_reusejp_545_:
{
v___y_525_ = v___x_546_;
v_a_526_ = v_a_541_;
goto v___jp_524_;
}
}
}
}
else
{
lean_dec(v_a_530_);
lean_dec(v_a_502_);
return v___x_529_;
}
}
else
{
lean_object* v_a_549_; 
v_a_549_ = lean_ctor_get(v___x_529_, 0);
lean_inc(v_a_549_);
v___y_525_ = v___x_529_;
v_a_526_ = v_a_549_;
goto v___jp_524_;
}
v___jp_503_:
{
if (v___y_506_ == 0)
{
lean_object* v___x_507_; 
lean_dec_ref(v___y_504_);
v___x_507_ = l_Lean_Meta_SavedState_restore___redArg(v_a_502_, v___y_497_, v___y_499_);
lean_dec(v_a_502_);
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
lean_ctor_set(v___x_509_, 0, v___y_505_);
v___x_512_ = v___x_509_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_513_; 
v_reuseFailAlloc_513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_513_, 0, v___y_505_);
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
lean_dec_ref(v___y_505_);
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
lean_dec_ref(v___y_505_);
lean_dec(v_a_502_);
return v___y_504_;
}
}
v___jp_524_:
{
uint8_t v___x_527_; 
v___x_527_ = l_Lean_Exception_isInterrupt(v_a_526_);
if (v___x_527_ == 0)
{
uint8_t v___x_528_; 
lean_inc_ref(v_a_526_);
v___x_528_ = l_Lean_Exception_isRuntime(v_a_526_);
v___y_504_ = v___y_525_;
v___y_505_ = v_a_526_;
v___y_506_ = v___x_528_;
goto v___jp_503_;
}
else
{
v___y_504_ = v___y_525_;
v___y_505_ = v_a_526_;
v___y_506_ = v___x_527_;
goto v___jp_503_;
}
}
}
else
{
lean_object* v_a_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_557_; 
lean_dec_ref(v_x_494_);
v_a_550_ = lean_ctor_get(v___x_501_, 0);
v_isSharedCheck_557_ = !lean_is_exclusive(v___x_501_);
if (v_isSharedCheck_557_ == 0)
{
v___x_552_ = v___x_501_;
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_a_550_);
lean_dec(v___x_501_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_557_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_555_; 
if (v_isShared_553_ == 0)
{
v___x_555_ = v___x_552_;
goto v_reusejp_554_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v_a_550_);
v___x_555_ = v_reuseFailAlloc_556_;
goto v_reusejp_554_;
}
v_reusejp_554_:
{
return v___x_555_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4___boxed(lean_object* v_x_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v_x_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(lean_object* v_msgData_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_572_; lean_object* v_env_573_; lean_object* v___x_574_; lean_object* v_mctx_575_; lean_object* v_lctx_576_; lean_object* v_options_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
v___x_572_ = lean_st_ref_get(v___y_570_);
v_env_573_ = lean_ctor_get(v___x_572_, 0);
lean_inc_ref(v_env_573_);
lean_dec(v___x_572_);
v___x_574_ = lean_st_ref_get(v___y_568_);
v_mctx_575_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_mctx_575_);
lean_dec(v___x_574_);
v_lctx_576_ = lean_ctor_get(v___y_567_, 2);
v_options_577_ = lean_ctor_get(v___y_569_, 2);
lean_inc_ref(v_options_577_);
lean_inc_ref(v_lctx_576_);
v___x_578_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_578_, 0, v_env_573_);
lean_ctor_set(v___x_578_, 1, v_mctx_575_);
lean_ctor_set(v___x_578_, 2, v_lctx_576_);
lean_ctor_set(v___x_578_, 3, v_options_577_);
v___x_579_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_579_, 0, v___x_578_);
lean_ctor_set(v___x_579_, 1, v_msgData_566_);
v___x_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object* v_msgData_581_, lean_object* v___y_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_){
_start:
{
lean_object* v_res_587_; 
v_res_587_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_581_, v___y_582_, v___y_583_, v___y_584_, v___y_585_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
lean_dec(v___y_583_);
lean_dec_ref(v___y_582_);
return v_res_587_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_588_; double v___x_589_; 
v___x_588_ = lean_unsigned_to_nat(0u);
v___x_589_ = lean_float_of_nat(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_593_, lean_object* v_msg_594_, lean_object* v___y_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_){
_start:
{
lean_object* v_ref_600_; lean_object* v___x_601_; lean_object* v_a_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_646_; 
v_ref_600_ = lean_ctor_get(v___y_597_, 5);
v___x_601_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_594_, v___y_595_, v___y_596_, v___y_597_, v___y_598_);
v_a_602_ = lean_ctor_get(v___x_601_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v___x_601_);
if (v_isSharedCheck_646_ == 0)
{
v___x_604_ = v___x_601_;
v_isShared_605_ = v_isSharedCheck_646_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_a_602_);
lean_dec(v___x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_646_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v_traceState_607_; lean_object* v_env_608_; lean_object* v_nextMacroScope_609_; lean_object* v_ngen_610_; lean_object* v_auxDeclNGen_611_; lean_object* v_cache_612_; lean_object* v_messages_613_; lean_object* v_infoState_614_; lean_object* v_snapshotTasks_615_; lean_object* v___x_617_; uint8_t v_isShared_618_; uint8_t v_isSharedCheck_645_; 
v___x_606_ = lean_st_ref_take(v___y_598_);
v_traceState_607_ = lean_ctor_get(v___x_606_, 4);
v_env_608_ = lean_ctor_get(v___x_606_, 0);
v_nextMacroScope_609_ = lean_ctor_get(v___x_606_, 1);
v_ngen_610_ = lean_ctor_get(v___x_606_, 2);
v_auxDeclNGen_611_ = lean_ctor_get(v___x_606_, 3);
v_cache_612_ = lean_ctor_get(v___x_606_, 5);
v_messages_613_ = lean_ctor_get(v___x_606_, 6);
v_infoState_614_ = lean_ctor_get(v___x_606_, 7);
v_snapshotTasks_615_ = lean_ctor_get(v___x_606_, 8);
v_isSharedCheck_645_ = !lean_is_exclusive(v___x_606_);
if (v_isSharedCheck_645_ == 0)
{
v___x_617_ = v___x_606_;
v_isShared_618_ = v_isSharedCheck_645_;
goto v_resetjp_616_;
}
else
{
lean_inc(v_snapshotTasks_615_);
lean_inc(v_infoState_614_);
lean_inc(v_messages_613_);
lean_inc(v_cache_612_);
lean_inc(v_traceState_607_);
lean_inc(v_auxDeclNGen_611_);
lean_inc(v_ngen_610_);
lean_inc(v_nextMacroScope_609_);
lean_inc(v_env_608_);
lean_dec(v___x_606_);
v___x_617_ = lean_box(0);
v_isShared_618_ = v_isSharedCheck_645_;
goto v_resetjp_616_;
}
v_resetjp_616_:
{
uint64_t v_tid_619_; lean_object* v_traces_620_; lean_object* v___x_622_; uint8_t v_isShared_623_; uint8_t v_isSharedCheck_644_; 
v_tid_619_ = lean_ctor_get_uint64(v_traceState_607_, sizeof(void*)*1);
v_traces_620_ = lean_ctor_get(v_traceState_607_, 0);
v_isSharedCheck_644_ = !lean_is_exclusive(v_traceState_607_);
if (v_isSharedCheck_644_ == 0)
{
v___x_622_ = v_traceState_607_;
v_isShared_623_ = v_isSharedCheck_644_;
goto v_resetjp_621_;
}
else
{
lean_inc(v_traces_620_);
lean_dec(v_traceState_607_);
v___x_622_ = lean_box(0);
v_isShared_623_ = v_isSharedCheck_644_;
goto v_resetjp_621_;
}
v_resetjp_621_:
{
lean_object* v___x_624_; double v___x_625_; uint8_t v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_634_; 
v___x_624_ = lean_box(0);
v___x_625_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_626_ = 0;
v___x_627_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_628_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_628_, 0, v_cls_593_);
lean_ctor_set(v___x_628_, 1, v___x_624_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
lean_ctor_set_float(v___x_628_, sizeof(void*)*3, v___x_625_);
lean_ctor_set_float(v___x_628_, sizeof(void*)*3 + 8, v___x_625_);
lean_ctor_set_uint8(v___x_628_, sizeof(void*)*3 + 16, v___x_626_);
v___x_629_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_630_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_630_, 0, v___x_628_);
lean_ctor_set(v___x_630_, 1, v_a_602_);
lean_ctor_set(v___x_630_, 2, v___x_629_);
lean_inc(v_ref_600_);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v_ref_600_);
lean_ctor_set(v___x_631_, 1, v___x_630_);
v___x_632_ = l_Lean_PersistentArray_push___redArg(v_traces_620_, v___x_631_);
if (v_isShared_623_ == 0)
{
lean_ctor_set(v___x_622_, 0, v___x_632_);
v___x_634_ = v___x_622_;
goto v_reusejp_633_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_632_);
lean_ctor_set_uint64(v_reuseFailAlloc_643_, sizeof(void*)*1, v_tid_619_);
v___x_634_ = v_reuseFailAlloc_643_;
goto v_reusejp_633_;
}
v_reusejp_633_:
{
lean_object* v___x_636_; 
if (v_isShared_618_ == 0)
{
lean_ctor_set(v___x_617_, 4, v___x_634_);
v___x_636_ = v___x_617_;
goto v_reusejp_635_;
}
else
{
lean_object* v_reuseFailAlloc_642_; 
v_reuseFailAlloc_642_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_642_, 0, v_env_608_);
lean_ctor_set(v_reuseFailAlloc_642_, 1, v_nextMacroScope_609_);
lean_ctor_set(v_reuseFailAlloc_642_, 2, v_ngen_610_);
lean_ctor_set(v_reuseFailAlloc_642_, 3, v_auxDeclNGen_611_);
lean_ctor_set(v_reuseFailAlloc_642_, 4, v___x_634_);
lean_ctor_set(v_reuseFailAlloc_642_, 5, v_cache_612_);
lean_ctor_set(v_reuseFailAlloc_642_, 6, v_messages_613_);
lean_ctor_set(v_reuseFailAlloc_642_, 7, v_infoState_614_);
lean_ctor_set(v_reuseFailAlloc_642_, 8, v_snapshotTasks_615_);
v___x_636_ = v_reuseFailAlloc_642_;
goto v_reusejp_635_;
}
v_reusejp_635_:
{
lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_640_; 
v___x_637_ = lean_st_ref_put(v___y_598_, v___x_636_);
v___x_638_ = lean_box(0);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 0, v___x_638_);
v___x_640_ = v___x_604_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_641_; 
v_reuseFailAlloc_641_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_641_, 0, v___x_638_);
v___x_640_ = v_reuseFailAlloc_641_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
return v___x_640_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_647_, lean_object* v_msg_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_647_, v_msg_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_662_, lean_object* v_mvarId_663_, lean_object* v_fields_664_, lean_object* v_sz_665_, lean_object* v___x_666_, lean_object* v___x_667_, lean_object* v___x_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_){
_start:
{
size_t v_sz_boxed_675_; size_t v___x_18284__boxed_676_; uint8_t v___x_18286__boxed_677_; lean_object* v_res_678_; 
v_sz_boxed_675_ = lean_unbox_usize(v_sz_665_);
lean_dec(v_sz_665_);
v___x_18284__boxed_676_ = lean_unbox_usize(v___x_666_);
lean_dec(v___x_666_);
v___x_18286__boxed_677_ = lean_unbox(v___x_668_);
v_res_678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_662_, v_mvarId_663_, v_fields_664_, v_sz_boxed_675_, v___x_18284__boxed_676_, v___x_667_, v___x_18286__boxed_677_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v___y_670_);
lean_dec(v___y_669_);
lean_dec_ref(v_fields_664_);
return v_res_678_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_679_, lean_object* v_as_680_, size_t v_sz_681_, size_t v_i_682_, lean_object* v_b_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_){
_start:
{
uint8_t v___x_690_; 
v___x_690_ = lean_usize_dec_lt(v_i_682_, v_sz_681_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; 
v___x_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_691_, 0, v_b_683_);
return v___x_691_;
}
else
{
lean_object* v_a_692_; lean_object* v_toInductionSubgoal_693_; lean_object* v___x_695_; uint8_t v_isShared_696_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v_b_683_);
v_a_692_ = lean_array_uget(v_as_680_, v_i_682_);
v_toInductionSubgoal_693_ = lean_ctor_get(v_a_692_, 0);
v_isSharedCheck_734_ = !lean_is_exclusive(v_a_692_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v_a_692_, 1);
lean_dec(v_unused_735_);
v___x_695_ = v_a_692_;
v_isShared_696_ = v_isSharedCheck_734_;
goto v_resetjp_694_;
}
else
{
lean_inc(v_toInductionSubgoal_693_);
lean_dec(v_a_692_);
v___x_695_ = lean_box(0);
v_isShared_696_ = v_isSharedCheck_734_;
goto v_resetjp_694_;
}
v_resetjp_694_:
{
lean_object* v_mvarId_697_; lean_object* v_fields_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; uint8_t v___x_702_; size_t v_sz_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___f_707_; lean_object* v___x_708_; 
v_mvarId_697_ = lean_ctor_get(v_toInductionSubgoal_693_, 0);
lean_inc_n(v_mvarId_697_, 2);
v_fields_698_ = lean_ctor_get(v_toInductionSubgoal_693_, 1);
lean_inc_ref(v_fields_698_);
v___x_699_ = lean_box(0);
v___x_700_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_701_ = lean_unsigned_to_nat(0u);
v___x_702_ = lean_nat_dec_eq(v_val_679_, v___x_701_);
v_sz_703_ = lean_array_size(v_fields_698_);
v___x_704_ = lean_box_usize(v_sz_703_);
v___x_705_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_706_ = lean_box(v___x_702_);
v___f_707_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_707_, 0, v_toInductionSubgoal_693_);
lean_closure_set(v___f_707_, 1, v_mvarId_697_);
lean_closure_set(v___f_707_, 2, v_fields_698_);
lean_closure_set(v___f_707_, 3, v___x_704_);
lean_closure_set(v___f_707_, 4, v___x_705_);
lean_closure_set(v___f_707_, 5, v___x_700_);
lean_closure_set(v___f_707_, 6, v___x_706_);
v___x_708_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_697_, v___f_707_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
if (lean_obj_tag(v___x_708_) == 0)
{
lean_object* v_a_709_; lean_object* v___x_711_; uint8_t v_isShared_712_; uint8_t v_isSharedCheck_725_; 
v_a_709_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_725_ == 0)
{
v___x_711_ = v___x_708_;
v_isShared_712_ = v_isSharedCheck_725_;
goto v_resetjp_710_;
}
else
{
lean_inc(v_a_709_);
lean_dec(v___x_708_);
v___x_711_ = lean_box(0);
v_isShared_712_ = v_isSharedCheck_725_;
goto v_resetjp_710_;
}
v_resetjp_710_:
{
uint8_t v___x_713_; 
v___x_713_ = lean_unbox(v_a_709_);
lean_dec(v_a_709_);
if (v___x_713_ == 0)
{
lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_717_; 
v___x_714_ = lean_box(v___x_702_);
v___x_715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_715_, 0, v___x_714_);
if (v_isShared_696_ == 0)
{
lean_ctor_set(v___x_695_, 1, v___x_699_);
lean_ctor_set(v___x_695_, 0, v___x_715_);
v___x_717_ = v___x_695_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_715_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v___x_699_);
v___x_717_ = v_reuseFailAlloc_721_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
lean_object* v___x_719_; 
if (v_isShared_712_ == 0)
{
lean_ctor_set(v___x_711_, 0, v___x_717_);
v___x_719_ = v___x_711_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_720_; 
v_reuseFailAlloc_720_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_720_, 0, v___x_717_);
v___x_719_ = v_reuseFailAlloc_720_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
return v___x_719_;
}
}
}
else
{
size_t v___x_722_; size_t v___x_723_; 
lean_del_object(v___x_711_);
lean_del_object(v___x_695_);
v___x_722_ = ((size_t)1ULL);
v___x_723_ = lean_usize_add(v_i_682_, v___x_722_);
v_i_682_ = v___x_723_;
v_b_683_ = v___x_700_;
goto _start;
}
}
}
else
{
lean_object* v_a_726_; lean_object* v___x_728_; uint8_t v_isShared_729_; uint8_t v_isSharedCheck_733_; 
lean_del_object(v___x_695_);
v_a_726_ = lean_ctor_get(v___x_708_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_708_);
if (v_isSharedCheck_733_ == 0)
{
v___x_728_ = v___x_708_;
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
else
{
lean_inc(v_a_726_);
lean_dec(v___x_708_);
v___x_728_ = lean_box(0);
v_isShared_729_ = v_isSharedCheck_733_;
goto v_resetjp_727_;
}
v_resetjp_727_:
{
lean_object* v___x_731_; 
if (v_isShared_729_ == 0)
{
v___x_731_ = v___x_728_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_732_; 
v_reuseFailAlloc_732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_732_, 0, v_a_726_);
v___x_731_ = v_reuseFailAlloc_732_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
return v___x_731_;
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
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_747_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__6));
v___x_748_ = l_Lean_Name_append(v___x_747_, v___x_746_);
return v___x_748_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_751_ = l_Lean_stringToMessageData(v___x_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_752_, lean_object* v_fvarId_753_, lean_object* v___x_754_, uint8_t v___x_755_, lean_object* v___x_756_, lean_object* v_val_757_, uint8_t v___x_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_){
_start:
{
lean_object* v___x_765_; 
v___x_765_ = l_Lean_MVarId_cases(v_mvarId_752_, v_fvarId_753_, v___x_754_, v___x_755_, v___x_756_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_765_) == 0)
{
lean_object* v_a_766_; lean_object* v___y_768_; lean_object* v___y_769_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v_options_799_; uint8_t v_hasTrace_800_; 
v_a_766_ = lean_ctor_get(v___x_765_, 0);
lean_inc(v_a_766_);
lean_dec_ref_known(v___x_765_, 1);
v_options_799_ = lean_ctor_get(v___y_762_, 2);
v_hasTrace_800_ = lean_ctor_get_uint8(v_options_799_, sizeof(void*)*1);
if (v_hasTrace_800_ == 0)
{
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
v___y_772_ = v___y_763_;
goto v___jp_767_;
}
else
{
lean_object* v_inheritedTraceOptions_801_; lean_object* v___x_802_; lean_object* v___x_803_; uint8_t v___x_804_; 
v_inheritedTraceOptions_801_ = lean_ctor_get(v___y_762_, 13);
v___x_802_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_803_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_804_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_801_, v_options_799_, v___x_803_);
if (v___x_804_ == 0)
{
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
v___y_772_ = v___y_763_;
goto v___jp_767_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_805_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_806_ = lean_array_get_size(v_a_766_);
v___x_807_ = l_Nat_reprFast(v___x_806_);
v___x_808_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_808_, 0, v___x_807_);
v___x_809_ = l_Lean_MessageData_ofFormat(v___x_808_);
v___x_810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_810_, 0, v___x_805_);
lean_ctor_set(v___x_810_, 1, v___x_809_);
v___x_811_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_802_, v___x_810_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_dec_ref_known(v___x_811_, 1);
v___y_768_ = v___y_759_;
v___y_769_ = v___y_760_;
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
v___y_772_ = v___y_763_;
goto v___jp_767_;
}
else
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
lean_dec(v_a_766_);
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
v___jp_767_:
{
lean_object* v___x_773_; size_t v_sz_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_773_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_774_ = lean_array_size(v_a_766_);
v___x_775_ = ((size_t)0ULL);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_757_, v_a_766_, v_sz_774_, v___x_775_, v___x_773_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_);
lean_dec(v_a_766_);
if (lean_obj_tag(v___x_776_) == 0)
{
lean_object* v_a_777_; lean_object* v___x_779_; uint8_t v_isShared_780_; uint8_t v_isSharedCheck_790_; 
v_a_777_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_790_ == 0)
{
v___x_779_ = v___x_776_;
v_isShared_780_ = v_isSharedCheck_790_;
goto v_resetjp_778_;
}
else
{
lean_inc(v_a_777_);
lean_dec(v___x_776_);
v___x_779_ = lean_box(0);
v_isShared_780_ = v_isSharedCheck_790_;
goto v_resetjp_778_;
}
v_resetjp_778_:
{
lean_object* v_fst_781_; 
v_fst_781_ = lean_ctor_get(v_a_777_, 0);
lean_inc(v_fst_781_);
lean_dec(v_a_777_);
if (lean_obj_tag(v_fst_781_) == 0)
{
lean_object* v___x_782_; lean_object* v___x_784_; 
v___x_782_ = lean_box(v___x_758_);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v___x_782_);
v___x_784_ = v___x_779_;
goto v_reusejp_783_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v___x_782_);
v___x_784_ = v_reuseFailAlloc_785_;
goto v_reusejp_783_;
}
v_reusejp_783_:
{
return v___x_784_;
}
}
else
{
lean_object* v_val_786_; lean_object* v___x_788_; 
v_val_786_ = lean_ctor_get(v_fst_781_, 0);
lean_inc(v_val_786_);
lean_dec_ref_known(v_fst_781_, 1);
if (v_isShared_780_ == 0)
{
lean_ctor_set(v___x_779_, 0, v_val_786_);
v___x_788_ = v___x_779_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_val_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
else
{
lean_object* v_a_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_798_; 
v_a_791_ = lean_ctor_get(v___x_776_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_776_);
if (v_isSharedCheck_798_ == 0)
{
v___x_793_ = v___x_776_;
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_a_791_);
lean_dec(v___x_776_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_798_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v___x_796_; 
if (v_isShared_794_ == 0)
{
v___x_796_ = v___x_793_;
goto v_reusejp_795_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_a_791_);
v___x_796_ = v_reuseFailAlloc_797_;
goto v_reusejp_795_;
}
v_reusejp_795_:
{
return v___x_796_;
}
}
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_864_; 
v_a_820_ = lean_ctor_get(v___x_765_, 0);
v_isSharedCheck_864_ = !lean_is_exclusive(v___x_765_);
if (v_isSharedCheck_864_ == 0)
{
v___x_822_ = v___x_765_;
v_isShared_823_ = v_isSharedCheck_864_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_765_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_864_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
uint8_t v___y_825_; uint8_t v___x_862_; 
v___x_862_ = l_Lean_Exception_isInterrupt(v_a_820_);
if (v___x_862_ == 0)
{
uint8_t v___x_863_; 
lean_inc(v_a_820_);
v___x_863_ = l_Lean_Exception_isRuntime(v_a_820_);
v___y_825_ = v___x_863_;
goto v___jp_824_;
}
else
{
v___y_825_ = v___x_862_;
goto v___jp_824_;
}
v___jp_824_:
{
if (v___y_825_ == 0)
{
lean_object* v_options_826_; uint8_t v_hasTrace_827_; 
v_options_826_ = lean_ctor_get(v___y_762_, 2);
v_hasTrace_827_ = lean_ctor_get_uint8(v_options_826_, sizeof(void*)*1);
if (v_hasTrace_827_ == 0)
{
lean_object* v___x_828_; lean_object* v___x_830_; 
lean_dec(v_a_820_);
v___x_828_ = lean_box(v___x_755_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_828_);
v___x_830_ = v___x_822_;
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
v_inheritedTraceOptions_832_ = lean_ctor_get(v___y_762_, 13);
v___x_833_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_834_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_835_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_832_, v_options_826_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v___x_836_; lean_object* v___x_838_; 
lean_dec(v_a_820_);
v___x_836_ = lean_box(v___x_755_);
if (v_isShared_823_ == 0)
{
lean_ctor_set_tag(v___x_822_, 0);
lean_ctor_set(v___x_822_, 0, v___x_836_);
v___x_838_ = v___x_822_;
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
lean_del_object(v___x_822_);
v___x_840_ = l_Lean_Exception_toMessageData(v_a_820_);
v___x_841_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_833_, v___x_840_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
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
v___x_845_ = lean_box(v___x_755_);
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
if (v_isShared_823_ == 0)
{
v___x_860_ = v___x_822_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_820_);
v___x_860_ = v_reuseFailAlloc_861_;
goto v_reusejp_859_;
}
v_reusejp_859_:
{
return v___x_860_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_865_, lean_object* v_fvarId_866_, lean_object* v___x_867_, lean_object* v___x_868_, lean_object* v___x_869_, lean_object* v_val_870_, lean_object* v___x_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_, lean_object* v___y_875_, lean_object* v___y_876_, lean_object* v___y_877_){
_start:
{
uint8_t v___x_18406__boxed_878_; uint8_t v___x_18409__boxed_879_; lean_object* v_res_880_; 
v___x_18406__boxed_878_ = lean_unbox(v___x_868_);
v___x_18409__boxed_879_ = lean_unbox(v___x_871_);
v_res_880_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_865_, v_fvarId_866_, v___x_867_, v___x_18406__boxed_878_, v___x_869_, v_val_870_, v___x_18409__boxed_879_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_);
lean_dec(v___y_876_);
lean_dec_ref(v___y_875_);
lean_dec(v___y_874_);
lean_dec_ref(v___y_873_);
lean_dec(v___y_872_);
lean_dec(v_val_870_);
return v_res_880_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_883_ = l_Lean_stringToMessageData(v___x_882_);
return v___x_883_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_884_, lean_object* v_fvarId_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_){
_start:
{
lean_object* v___x_896_; lean_object* v___x_897_; uint8_t v___x_898_; 
v___x_896_ = lean_st_ref_get(v_a_886_);
v___x_897_ = lean_unsigned_to_nat(0u);
v___x_898_ = lean_nat_dec_eq(v___x_896_, v___x_897_);
if (v___x_898_ == 0)
{
lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___f_908_; lean_object* v___x_909_; 
v___x_899_ = lean_st_ref_take(v_a_886_);
v___x_900_ = lean_unsigned_to_nat(1u);
v___x_901_ = lean_nat_sub(v___x_899_, v___x_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_st_ref_put(v_a_886_, v___x_901_);
v___x_903_ = 1;
v___x_904_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_905_ = lean_box(0);
v___x_906_ = lean_box(v___x_898_);
v___x_907_ = lean_box(v___x_903_);
v___f_908_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_908_, 0, v_mvarId_884_);
lean_closure_set(v___f_908_, 1, v_fvarId_885_);
lean_closure_set(v___f_908_, 2, v___x_904_);
lean_closure_set(v___f_908_, 3, v___x_906_);
lean_closure_set(v___f_908_, 4, v___x_905_);
lean_closure_set(v___f_908_, 5, v___x_896_);
lean_closure_set(v___f_908_, 6, v___x_907_);
v___x_909_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_908_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
return v___x_909_;
}
else
{
lean_object* v_options_910_; uint8_t v_hasTrace_911_; 
lean_dec(v___x_896_);
lean_dec(v_fvarId_885_);
lean_dec(v_mvarId_884_);
v_options_910_ = lean_ctor_get(v_a_889_, 2);
v_hasTrace_911_ = lean_ctor_get_uint8(v_options_910_, sizeof(void*)*1);
if (v_hasTrace_911_ == 0)
{
goto v___jp_892_;
}
else
{
lean_object* v_inheritedTraceOptions_912_; lean_object* v___x_913_; lean_object* v___x_914_; uint8_t v___x_915_; 
v_inheritedTraceOptions_912_ = lean_ctor_get(v_a_889_, 13);
v___x_913_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_914_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_915_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_912_, v_options_910_, v___x_914_);
if (v___x_915_ == 0)
{
goto v___jp_892_;
}
else
{
lean_object* v___x_916_; lean_object* v___x_917_; 
v___x_916_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_917_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_913_, v___x_916_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
if (lean_obj_tag(v___x_917_) == 0)
{
lean_dec_ref_known(v___x_917_, 1);
goto v___jp_892_;
}
else
{
lean_object* v_a_918_; lean_object* v___x_920_; uint8_t v_isShared_921_; uint8_t v_isSharedCheck_925_; 
v_a_918_ = lean_ctor_get(v___x_917_, 0);
v_isSharedCheck_925_ = !lean_is_exclusive(v___x_917_);
if (v_isSharedCheck_925_ == 0)
{
v___x_920_ = v___x_917_;
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
else
{
lean_inc(v_a_918_);
lean_dec(v___x_917_);
v___x_920_ = lean_box(0);
v_isShared_921_ = v_isSharedCheck_925_;
goto v_resetjp_919_;
}
v_resetjp_919_:
{
lean_object* v___x_923_; 
if (v_isShared_921_ == 0)
{
v___x_923_ = v___x_920_;
goto v_reusejp_922_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
v___x_923_ = v_reuseFailAlloc_924_;
goto v_reusejp_922_;
}
v_reusejp_922_:
{
return v___x_923_;
}
}
}
}
}
}
v___jp_892_:
{
uint8_t v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; 
v___x_893_ = 0;
v___x_894_ = lean_box(v___x_893_);
v___x_895_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_895_, 0, v___x_894_);
return v___x_895_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_926_, lean_object* v___x_927_, lean_object* v_as_928_, size_t v_sz_929_, size_t v_i_930_, lean_object* v_b_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_){
_start:
{
lean_object* v_a_939_; uint8_t v___x_943_; 
v___x_943_ = lean_usize_dec_lt(v_i_930_, v_sz_929_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; 
lean_dec(v___x_927_);
lean_dec_ref(v___x_926_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v_b_931_);
return v___x_944_;
}
else
{
lean_object* v_subst_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v_a_948_; lean_object* v___x_949_; uint8_t v___x_950_; 
lean_dec_ref(v_b_931_);
v_subst_945_ = lean_ctor_get(v___x_926_, 2);
v___x_946_ = lean_box(0);
v___x_947_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_948_ = lean_array_uget_borrowed(v_as_928_, v_i_930_);
lean_inc(v_subst_945_);
v___x_949_ = l_Lean_Meta_FVarSubst_apply(v_subst_945_, v_a_948_);
v___x_950_ = l_Lean_Expr_isFVar(v___x_949_);
if (v___x_950_ == 0)
{
lean_dec_ref(v___x_949_);
v_a_939_ = v___x_947_;
goto v___jp_938_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_951_ = l_Lean_Expr_fvarId_x21(v___x_949_);
lean_dec_ref(v___x_949_);
lean_inc(v___x_951_);
v___x_952_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_951_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_952_) == 0)
{
lean_object* v_a_953_; uint8_t v___x_954_; 
v_a_953_ = lean_ctor_get(v___x_952_, 0);
lean_inc(v_a_953_);
lean_dec_ref_known(v___x_952_, 1);
v___x_954_ = lean_unbox(v_a_953_);
lean_dec(v_a_953_);
if (v___x_954_ == 0)
{
lean_dec(v___x_951_);
v_a_939_ = v___x_947_;
goto v___jp_938_;
}
else
{
lean_object* v___x_955_; 
lean_inc(v___x_927_);
v___x_955_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_927_, v___x_951_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_);
if (lean_obj_tag(v___x_955_) == 0)
{
lean_object* v_a_956_; lean_object* v___x_958_; uint8_t v_isShared_959_; uint8_t v_isSharedCheck_966_; 
v_a_956_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_966_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_966_ == 0)
{
v___x_958_ = v___x_955_;
v_isShared_959_ = v_isSharedCheck_966_;
goto v_resetjp_957_;
}
else
{
lean_inc(v_a_956_);
lean_dec(v___x_955_);
v___x_958_ = lean_box(0);
v_isShared_959_ = v_isSharedCheck_966_;
goto v_resetjp_957_;
}
v_resetjp_957_:
{
uint8_t v___x_960_; 
v___x_960_ = lean_unbox(v_a_956_);
if (v___x_960_ == 0)
{
lean_del_object(v___x_958_);
lean_dec(v_a_956_);
v_a_939_ = v___x_947_;
goto v___jp_938_;
}
else
{
lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_964_; 
lean_dec(v___x_927_);
lean_dec_ref(v___x_926_);
v___x_961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_961_, 0, v_a_956_);
v___x_962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_962_, 0, v___x_961_);
lean_ctor_set(v___x_962_, 1, v___x_946_);
if (v_isShared_959_ == 0)
{
lean_ctor_set(v___x_958_, 0, v___x_962_);
v___x_964_ = v___x_958_;
goto v_reusejp_963_;
}
else
{
lean_object* v_reuseFailAlloc_965_; 
v_reuseFailAlloc_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_965_, 0, v___x_962_);
v___x_964_ = v_reuseFailAlloc_965_;
goto v_reusejp_963_;
}
v_reusejp_963_:
{
return v___x_964_;
}
}
}
}
else
{
lean_object* v_a_967_; lean_object* v___x_969_; uint8_t v_isShared_970_; uint8_t v_isSharedCheck_974_; 
lean_dec(v___x_927_);
lean_dec_ref(v___x_926_);
v_a_967_ = lean_ctor_get(v___x_955_, 0);
v_isSharedCheck_974_ = !lean_is_exclusive(v___x_955_);
if (v_isSharedCheck_974_ == 0)
{
v___x_969_ = v___x_955_;
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
else
{
lean_inc(v_a_967_);
lean_dec(v___x_955_);
v___x_969_ = lean_box(0);
v_isShared_970_ = v_isSharedCheck_974_;
goto v_resetjp_968_;
}
v_resetjp_968_:
{
lean_object* v___x_972_; 
if (v_isShared_970_ == 0)
{
v___x_972_ = v___x_969_;
goto v_reusejp_971_;
}
else
{
lean_object* v_reuseFailAlloc_973_; 
v_reuseFailAlloc_973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_973_, 0, v_a_967_);
v___x_972_ = v_reuseFailAlloc_973_;
goto v_reusejp_971_;
}
v_reusejp_971_:
{
return v___x_972_;
}
}
}
}
}
else
{
lean_object* v_a_975_; lean_object* v___x_977_; uint8_t v_isShared_978_; uint8_t v_isSharedCheck_982_; 
lean_dec(v___x_951_);
lean_dec(v___x_927_);
lean_dec_ref(v___x_926_);
v_a_975_ = lean_ctor_get(v___x_952_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v___x_952_);
if (v_isSharedCheck_982_ == 0)
{
v___x_977_ = v___x_952_;
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
else
{
lean_inc(v_a_975_);
lean_dec(v___x_952_);
v___x_977_ = lean_box(0);
v_isShared_978_ = v_isSharedCheck_982_;
goto v_resetjp_976_;
}
v_resetjp_976_:
{
lean_object* v___x_980_; 
if (v_isShared_978_ == 0)
{
v___x_980_ = v___x_977_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v_a_975_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
v___jp_938_:
{
size_t v___x_940_; size_t v___x_941_; 
v___x_940_ = ((size_t)1ULL);
v___x_941_ = lean_usize_add(v_i_930_, v___x_940_);
lean_inc_ref(v_a_939_);
v_i_930_ = v___x_941_;
v_b_931_ = v_a_939_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_983_, lean_object* v_mvarId_984_, lean_object* v_fields_985_, size_t v_sz_986_, size_t v___x_987_, lean_object* v___x_988_, uint8_t v___x_989_, lean_object* v___y_990_, lean_object* v___y_991_, lean_object* v___y_992_, lean_object* v___y_993_, lean_object* v___y_994_){
_start:
{
lean_object* v___x_996_; 
v___x_996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_983_, v_mvarId_984_, v_fields_985_, v_sz_986_, v___x_987_, v___x_988_, v___y_990_, v___y_991_, v___y_992_, v___y_993_, v___y_994_);
if (lean_obj_tag(v___x_996_) == 0)
{
lean_object* v_a_997_; lean_object* v___x_999_; uint8_t v_isShared_1000_; uint8_t v_isSharedCheck_1010_; 
v_a_997_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_999_ = v___x_996_;
v_isShared_1000_ = v_isSharedCheck_1010_;
goto v_resetjp_998_;
}
else
{
lean_inc(v_a_997_);
lean_dec(v___x_996_);
v___x_999_ = lean_box(0);
v_isShared_1000_ = v_isSharedCheck_1010_;
goto v_resetjp_998_;
}
v_resetjp_998_:
{
lean_object* v_fst_1001_; 
v_fst_1001_ = lean_ctor_get(v_a_997_, 0);
lean_inc(v_fst_1001_);
lean_dec(v_a_997_);
if (lean_obj_tag(v_fst_1001_) == 0)
{
lean_object* v___x_1002_; lean_object* v___x_1004_; 
v___x_1002_ = lean_box(v___x_989_);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v___x_1002_);
v___x_1004_ = v___x_999_;
goto v_reusejp_1003_;
}
else
{
lean_object* v_reuseFailAlloc_1005_; 
v_reuseFailAlloc_1005_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1005_, 0, v___x_1002_);
v___x_1004_ = v_reuseFailAlloc_1005_;
goto v_reusejp_1003_;
}
v_reusejp_1003_:
{
return v___x_1004_;
}
}
else
{
lean_object* v_val_1006_; lean_object* v___x_1008_; 
v_val_1006_ = lean_ctor_get(v_fst_1001_, 0);
lean_inc(v_val_1006_);
lean_dec_ref_known(v_fst_1001_, 1);
if (v_isShared_1000_ == 0)
{
lean_ctor_set(v___x_999_, 0, v_val_1006_);
v___x_1008_ = v___x_999_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_val_1006_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
else
{
lean_object* v_a_1011_; lean_object* v___x_1013_; uint8_t v_isShared_1014_; uint8_t v_isSharedCheck_1018_; 
v_a_1011_ = lean_ctor_get(v___x_996_, 0);
v_isSharedCheck_1018_ = !lean_is_exclusive(v___x_996_);
if (v_isSharedCheck_1018_ == 0)
{
v___x_1013_ = v___x_996_;
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
else
{
lean_inc(v_a_1011_);
lean_dec(v___x_996_);
v___x_1013_ = lean_box(0);
v_isShared_1014_ = v_isSharedCheck_1018_;
goto v_resetjp_1012_;
}
v_resetjp_1012_:
{
lean_object* v___x_1016_; 
if (v_isShared_1014_ == 0)
{
v___x_1016_ = v___x_1013_;
goto v_reusejp_1015_;
}
else
{
lean_object* v_reuseFailAlloc_1017_; 
v_reuseFailAlloc_1017_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1017_, 0, v_a_1011_);
v___x_1016_ = v_reuseFailAlloc_1017_;
goto v_reusejp_1015_;
}
v_reusejp_1015_:
{
return v___x_1016_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1019_, lean_object* v_as_1020_, lean_object* v_sz_1021_, lean_object* v_i_1022_, lean_object* v_b_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_, lean_object* v___y_1026_, lean_object* v___y_1027_, lean_object* v___y_1028_, lean_object* v___y_1029_){
_start:
{
size_t v_sz_boxed_1030_; size_t v_i_boxed_1031_; lean_object* v_res_1032_; 
v_sz_boxed_1030_ = lean_unbox_usize(v_sz_1021_);
lean_dec(v_sz_1021_);
v_i_boxed_1031_ = lean_unbox_usize(v_i_1022_);
lean_dec(v_i_1022_);
v_res_1032_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1019_, v_as_1020_, v_sz_boxed_1030_, v_i_boxed_1031_, v_b_1023_, v___y_1024_, v___y_1025_, v___y_1026_, v___y_1027_, v___y_1028_);
lean_dec(v___y_1028_);
lean_dec_ref(v___y_1027_);
lean_dec(v___y_1026_);
lean_dec_ref(v___y_1025_);
lean_dec(v___y_1024_);
lean_dec_ref(v_as_1020_);
lean_dec(v_val_1019_);
return v_res_1032_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1033_, lean_object* v___x_1034_, lean_object* v_as_1035_, lean_object* v_sz_1036_, lean_object* v_i_1037_, lean_object* v_b_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_, lean_object* v___y_1044_){
_start:
{
size_t v_sz_boxed_1045_; size_t v_i_boxed_1046_; lean_object* v_res_1047_; 
v_sz_boxed_1045_ = lean_unbox_usize(v_sz_1036_);
lean_dec(v_sz_1036_);
v_i_boxed_1046_ = lean_unbox_usize(v_i_1037_);
lean_dec(v_i_1037_);
v_res_1047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1033_, v___x_1034_, v_as_1035_, v_sz_boxed_1045_, v_i_boxed_1046_, v_b_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_, v___y_1043_);
lean_dec(v___y_1043_);
lean_dec_ref(v___y_1042_);
lean_dec(v___y_1041_);
lean_dec_ref(v___y_1040_);
lean_dec(v___y_1039_);
lean_dec_ref(v_as_1035_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1048_, lean_object* v_fvarId_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1048_, v_fvarId_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1057_, lean_object* v_msg_1058_, lean_object* v___y_1059_, lean_object* v___y_1060_, lean_object* v___y_1061_, lean_object* v___y_1062_, lean_object* v___y_1063_){
_start:
{
lean_object* v___x_1065_; 
v___x_1065_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1057_, v_msg_1058_, v___y_1060_, v___y_1061_, v___y_1062_, v___y_1063_);
return v___x_1065_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1066_, lean_object* v_msg_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_, lean_object* v___y_1072_, lean_object* v___y_1073_){
_start:
{
lean_object* v_res_1074_; 
v_res_1074_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1066_, v_msg_1067_, v___y_1068_, v___y_1069_, v___y_1070_, v___y_1071_, v___y_1072_);
lean_dec(v___y_1072_);
lean_dec_ref(v___y_1071_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
return v_res_1074_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_Meta_saveState___redArg(v___y_1077_, v___y_1079_);
if (lean_obj_tag(v___x_1081_) == 0)
{
lean_object* v_a_1082_; lean_object* v___y_1084_; lean_object* v___y_1085_; uint8_t v___y_1086_; lean_object* v___y_1105_; lean_object* v_a_1106_; lean_object* v___x_1109_; 
v_a_1082_ = lean_ctor_get(v___x_1081_, 0);
lean_inc(v_a_1082_);
lean_dec_ref_known(v___x_1081_, 1);
lean_inc(v___y_1079_);
lean_inc_ref(v___y_1078_);
lean_inc(v___y_1077_);
lean_inc_ref(v___y_1076_);
v___x_1109_ = lean_apply_5(v_x_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_, lean_box(0));
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
v___x_1112_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1082_, v___y_1077_, v___y_1079_);
if (lean_obj_tag(v___x_1112_) == 0)
{
lean_object* v___x_1114_; uint8_t v_isShared_1115_; uint8_t v_isSharedCheck_1119_; 
lean_dec(v_a_1082_);
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
v___y_1105_ = v___x_1126_;
v_a_1106_ = v_a_1121_;
goto v___jp_1104_;
}
}
}
}
else
{
lean_dec(v_a_1110_);
lean_dec(v_a_1082_);
return v___x_1109_;
}
}
else
{
lean_object* v_a_1129_; 
v_a_1129_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1129_);
v___y_1105_ = v___x_1109_;
v_a_1106_ = v_a_1129_;
goto v___jp_1104_;
}
v___jp_1083_:
{
if (v___y_1086_ == 0)
{
lean_object* v___x_1087_; 
lean_dec_ref(v___y_1084_);
v___x_1087_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1082_, v___y_1077_, v___y_1079_);
lean_dec(v_a_1082_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v___x_1089_; uint8_t v_isShared_1090_; uint8_t v_isSharedCheck_1094_; 
v_isSharedCheck_1094_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1094_ == 0)
{
lean_object* v_unused_1095_; 
v_unused_1095_ = lean_ctor_get(v___x_1087_, 0);
lean_dec(v_unused_1095_);
v___x_1089_ = v___x_1087_;
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
else
{
lean_dec(v___x_1087_);
v___x_1089_ = lean_box(0);
v_isShared_1090_ = v_isSharedCheck_1094_;
goto v_resetjp_1088_;
}
v_resetjp_1088_:
{
lean_object* v___x_1092_; 
if (v_isShared_1090_ == 0)
{
lean_ctor_set_tag(v___x_1089_, 1);
lean_ctor_set(v___x_1089_, 0, v___y_1085_);
v___x_1092_ = v___x_1089_;
goto v_reusejp_1091_;
}
else
{
lean_object* v_reuseFailAlloc_1093_; 
v_reuseFailAlloc_1093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1093_, 0, v___y_1085_);
v___x_1092_ = v_reuseFailAlloc_1093_;
goto v_reusejp_1091_;
}
v_reusejp_1091_:
{
return v___x_1092_;
}
}
}
else
{
lean_object* v_a_1096_; lean_object* v___x_1098_; uint8_t v_isShared_1099_; uint8_t v_isSharedCheck_1103_; 
lean_dec_ref(v___y_1085_);
v_a_1096_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1103_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1103_ == 0)
{
v___x_1098_ = v___x_1087_;
v_isShared_1099_ = v_isSharedCheck_1103_;
goto v_resetjp_1097_;
}
else
{
lean_inc(v_a_1096_);
lean_dec(v___x_1087_);
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
lean_dec_ref(v___y_1085_);
lean_dec(v_a_1082_);
return v___y_1084_;
}
}
v___jp_1104_:
{
uint8_t v___x_1107_; 
v___x_1107_ = l_Lean_Exception_isInterrupt(v_a_1106_);
if (v___x_1107_ == 0)
{
uint8_t v___x_1108_; 
lean_inc_ref(v_a_1106_);
v___x_1108_ = l_Lean_Exception_isRuntime(v_a_1106_);
v___y_1084_ = v___y_1105_;
v___y_1085_ = v_a_1106_;
v___y_1086_ = v___x_1108_;
goto v___jp_1083_;
}
else
{
v___y_1084_ = v___y_1105_;
v___y_1085_ = v_a_1106_;
v___y_1086_ = v___x_1107_;
goto v___jp_1083_;
}
}
}
else
{
lean_object* v_a_1130_; lean_object* v___x_1132_; uint8_t v_isShared_1133_; uint8_t v_isSharedCheck_1137_; 
lean_dec_ref(v_x_1075_);
v_a_1130_ = lean_ctor_get(v___x_1081_, 0);
v_isSharedCheck_1137_ = !lean_is_exclusive(v___x_1081_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1132_ = v___x_1081_;
v_isShared_1133_ = v_isSharedCheck_1137_;
goto v_resetjp_1131_;
}
else
{
lean_inc(v_a_1130_);
lean_dec(v___x_1081_);
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
lean_inc(v_a_1241_);
v___x_1242_ = lean_unbox(v_a_1241_);
lean_dec(v_a_1241_);
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
lean_object* v___f_1308_; lean_object* v___x_5509__overap_1309_; lean_object* v___x_1310_; 
v___f_1308_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_5509__overap_1309_ = lean_panic_fn_borrowed(v___f_1308_, v_msg_1302_);
lean_inc(v___y_1306_);
lean_inc_ref(v___y_1305_);
lean_inc(v___y_1304_);
lean_inc_ref(v___y_1303_);
v___x_1310_ = lean_apply_5(v___x_5509__overap_1309_, v___y_1303_, v___y_1304_, v___y_1305_, v___y_1306_, lean_box(0));
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
uint8_t v___x_7190__boxed_1726_; lean_object* v_res_1727_; 
v___x_7190__boxed_1726_ = lean_unbox(v___x_1718_);
v_res_1727_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1717_, v___x_7190__boxed_1726_, v_localDecl_1719_, v_mvarId_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_);
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
lean_object* v_snd_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_2455_; 
v_snd_1818_ = lean_ctor_get(v_b_1810_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_b_1810_);
if (v_isSharedCheck_2455_ == 0)
{
lean_object* v_unused_2456_; 
v_unused_2456_ = lean_ctor_get(v_b_1810_, 0);
lean_dec(v_unused_2456_);
v___x_1820_ = v_b_1810_;
v_isShared_1821_ = v_isSharedCheck_2455_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_snd_1818_);
lean_dec(v_b_1810_);
v___x_1820_ = lean_box(0);
v_isShared_1821_ = v_isSharedCheck_2455_;
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
lean_object* v_val_1837_; lean_object* v___x_1839_; uint8_t v_isShared_1840_; uint8_t v_isSharedCheck_2454_; 
v_val_1837_ = lean_ctor_get(v_a_1836_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v_a_1836_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_1839_ = v_a_1836_;
v_isShared_1840_ = v_isSharedCheck_2454_;
goto v_resetjp_1838_;
}
else
{
lean_inc(v_val_1837_);
lean_dec(v_a_1836_);
v___x_1839_ = lean_box(0);
v_isShared_1840_ = v_isSharedCheck_2454_;
goto v_resetjp_1838_;
}
v_resetjp_1838_:
{
lean_object* v___x_1841_; lean_object* v___y_1843_; lean_object* v___y_1844_; lean_object* v___y_1845_; lean_object* v___y_1846_; lean_object* v___x_1882_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___y_1886_; lean_object* v___y_1887_; lean_object* v___y_1905_; lean_object* v___y_1906_; lean_object* v___y_1907_; lean_object* v___y_1908_; uint8_t v___y_1909_; uint8_t v___x_1910_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; uint8_t v___y_1915_; lean_object* v___y_1916_; lean_object* v___y_1918_; lean_object* v___y_1919_; lean_object* v___y_1920_; uint8_t v___y_1921_; lean_object* v___y_1922_; uint8_t v___y_1923_; uint8_t v___y_1925_; uint8_t v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; lean_object* v___y_1930_; lean_object* v___y_1933_; lean_object* v___y_1934_; uint8_t v___y_1935_; lean_object* v___y_1936_; uint8_t v___y_1937_; lean_object* v___y_1938_; uint8_t v___y_1939_; 
v___x_1841_ = lean_box(0);
v___x_1882_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1910_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1837_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1954_; uint8_t v___y_1956_; uint8_t v___y_1957_; lean_object* v___y_1958_; lean_object* v___y_1959_; lean_object* v___y_1960_; lean_object* v___y_1961_; lean_object* v___y_1965_; lean_object* v___y_1966_; uint8_t v___y_1967_; lean_object* v___y_1968_; uint8_t v___y_1969_; lean_object* v___y_1970_; lean_object* v___y_1971_; uint8_t v___y_1972_; lean_object* v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; uint8_t v___y_1978_; uint8_t v___y_1979_; lean_object* v___y_1980_; lean_object* v_a_1981_; lean_object* v___y_1985_; lean_object* v___y_1986_; uint8_t v___y_1987_; lean_object* v___y_1988_; uint8_t v___y_1989_; lean_object* v___y_1990_; lean_object* v___y_2045_; lean_object* v___y_2046_; uint8_t v___y_2047_; lean_object* v___y_2048_; uint8_t v___y_2049_; lean_object* v___y_2050_; uint8_t v___y_2051_; lean_object* v___y_2053_; lean_object* v___y_2054_; lean_object* v___y_2055_; lean_object* v___y_2056_; uint8_t v___y_2057_; uint8_t v___y_2058_; lean_object* v___y_2059_; uint8_t v___y_2060_; lean_object* v___y_2063_; lean_object* v___y_2064_; lean_object* v___y_2065_; uint8_t v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2068_; uint8_t v___y_2069_; lean_object* v___y_2082_; lean_object* v___y_2083_; uint8_t v___y_2084_; lean_object* v___y_2085_; uint8_t v___y_2086_; lean_object* v___y_2087_; uint8_t v___y_2088_; uint8_t v___y_2090_; uint8_t v_isHEq_2091_; lean_object* v___y_2092_; lean_object* v___y_2093_; lean_object* v___y_2094_; lean_object* v___y_2095_; lean_object* v___y_2099_; lean_object* v___y_2100_; lean_object* v___y_2101_; uint8_t v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; lean_object* v___y_2105_; uint8_t v_isEq_2161_; lean_object* v___y_2162_; lean_object* v___y_2163_; lean_object* v___y_2164_; lean_object* v___y_2165_; lean_object* v___y_2211_; lean_object* v___y_2212_; lean_object* v___y_2213_; lean_object* v___y_2214_; lean_object* v___y_2257_; lean_object* v___y_2258_; lean_object* v___y_2259_; lean_object* v___y_2260_; lean_object* v___x_2391_; 
v___x_1954_ = l_Lean_LocalDecl_type(v_val_1837_);
lean_inc_ref(v___x_1954_);
v___x_2391_ = l_Lean_Meta_matchNot_x3f(v___x_1954_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_2391_) == 0)
{
lean_object* v_a_2392_; 
v_a_2392_ = lean_ctor_get(v___x_2391_, 0);
lean_inc(v_a_2392_);
lean_dec_ref_known(v___x_2391_, 1);
if (lean_obj_tag(v_a_2392_) == 1)
{
lean_object* v_val_2393_; lean_object* v___x_2394_; 
v_val_2393_ = lean_ctor_get(v_a_2392_, 0);
lean_inc(v_val_2393_);
lean_dec_ref_known(v_a_2392_, 1);
v___x_2394_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2393_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_2394_) == 0)
{
lean_object* v_a_2395_; 
v_a_2395_ = lean_ctor_get(v___x_2394_, 0);
lean_inc(v_a_2395_);
lean_dec_ref_known(v___x_2394_, 1);
if (lean_obj_tag(v_a_2395_) == 1)
{
lean_object* v_val_2396_; lean_object* v___x_2398_; uint8_t v_isShared_2399_; uint8_t v_isSharedCheck_2437_; 
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec_ref(v_config_1805_);
v_val_2396_ = lean_ctor_get(v_a_2395_, 0);
v_isSharedCheck_2437_ = !lean_is_exclusive(v_a_2395_);
if (v_isSharedCheck_2437_ == 0)
{
v___x_2398_ = v_a_2395_;
v_isShared_2399_ = v_isSharedCheck_2437_;
goto v_resetjp_2397_;
}
else
{
lean_inc(v_val_2396_);
lean_dec(v_a_2395_);
v___x_2398_ = lean_box(0);
v_isShared_2399_ = v_isSharedCheck_2437_;
goto v_resetjp_2397_;
}
v_resetjp_2397_:
{
lean_object* v___x_2400_; 
lean_inc(v_mvarId_1806_);
v___x_2400_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_2400_) == 0)
{
lean_object* v_a_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; 
v_a_2401_ = lean_ctor_get(v___x_2400_, 0);
lean_inc(v_a_2401_);
lean_dec_ref_known(v___x_2400_, 1);
v___x_2402_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_2403_ = l_Lean_mkFVar(v_val_2396_);
v___x_2404_ = l_Lean_Expr_app___override(v___x_2402_, v___x_2403_);
v___x_2405_ = l_Lean_Meta_mkFalseElim(v_a_2401_, v___x_2404_, v___y_1811_, v___y_1812_, v___y_1813_, v___y_1814_);
if (lean_obj_tag(v___x_2405_) == 0)
{
lean_object* v_a_2406_; lean_object* v___x_2407_; 
v_a_2406_ = lean_ctor_get(v___x_2405_, 0);
lean_inc(v_a_2406_);
lean_dec_ref_known(v___x_2405_, 1);
v___x_2407_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_2406_, v___y_1812_);
if (lean_obj_tag(v___x_2407_) == 0)
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
lean_dec_ref_known(v___x_2407_, 1);
v___x_2408_ = lean_box(v___x_1816_);
if (v_isShared_2399_ == 0)
{
lean_ctor_set(v___x_2398_, 0, v___x_2408_);
v___x_2410_ = v___x_2398_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v___x_2408_);
v___x_2410_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; 
v___x_2411_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2410_);
lean_ctor_set(v___x_2411_, 1, v___x_1841_);
v_a_1823_ = v___x_2411_;
goto v___jp_1822_;
}
}
else
{
lean_object* v_a_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2420_; 
lean_del_object(v___x_2398_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_2413_ = lean_ctor_get(v___x_2407_, 0);
v_isSharedCheck_2420_ = !lean_is_exclusive(v___x_2407_);
if (v_isSharedCheck_2420_ == 0)
{
v___x_2415_ = v___x_2407_;
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_a_2413_);
lean_dec(v___x_2407_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2420_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v___x_2418_; 
if (v_isShared_2416_ == 0)
{
v___x_2418_ = v___x_2415_;
goto v_reusejp_2417_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_a_2413_);
v___x_2418_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2417_;
}
v_reusejp_2417_:
{
return v___x_2418_;
}
}
}
}
else
{
lean_object* v_a_2421_; lean_object* v___x_2423_; uint8_t v_isShared_2424_; uint8_t v_isSharedCheck_2428_; 
lean_del_object(v___x_2398_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2421_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2428_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2428_ == 0)
{
v___x_2423_ = v___x_2405_;
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
else
{
lean_inc(v_a_2421_);
lean_dec(v___x_2405_);
v___x_2423_ = lean_box(0);
v_isShared_2424_ = v_isSharedCheck_2428_;
goto v_resetjp_2422_;
}
v_resetjp_2422_:
{
lean_object* v___x_2426_; 
if (v_isShared_2424_ == 0)
{
v___x_2426_ = v___x_2423_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_a_2421_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
else
{
lean_object* v_a_2429_; lean_object* v___x_2431_; uint8_t v_isShared_2432_; uint8_t v_isSharedCheck_2436_; 
lean_del_object(v___x_2398_);
lean_dec(v_val_2396_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2429_ = lean_ctor_get(v___x_2400_, 0);
v_isSharedCheck_2436_ = !lean_is_exclusive(v___x_2400_);
if (v_isSharedCheck_2436_ == 0)
{
v___x_2431_ = v___x_2400_;
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
else
{
lean_inc(v_a_2429_);
lean_dec(v___x_2400_);
v___x_2431_ = lean_box(0);
v_isShared_2432_ = v_isSharedCheck_2436_;
goto v_resetjp_2430_;
}
v_resetjp_2430_:
{
lean_object* v___x_2434_; 
if (v_isShared_2432_ == 0)
{
v___x_2434_ = v___x_2431_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2435_; 
v_reuseFailAlloc_2435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2435_, 0, v_a_2429_);
v___x_2434_ = v_reuseFailAlloc_2435_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
return v___x_2434_;
}
}
}
}
}
else
{
lean_dec(v_a_2395_);
v___y_2257_ = v___y_1811_;
v___y_2258_ = v___y_1812_;
v___y_2259_ = v___y_1813_;
v___y_2260_ = v___y_1814_;
goto v___jp_2256_;
}
}
else
{
lean_object* v_a_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2438_ = lean_ctor_get(v___x_2394_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2394_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2440_ = v___x_2394_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_a_2438_);
lean_dec(v___x_2394_);
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
else
{
lean_dec(v_a_2392_);
v___y_2257_ = v___y_1811_;
v___y_2258_ = v___y_1812_;
v___y_2259_ = v___y_1813_;
v___y_2260_ = v___y_1814_;
goto v___jp_2256_;
}
}
else
{
lean_object* v_a_2446_; lean_object* v___x_2448_; uint8_t v_isShared_2449_; uint8_t v_isSharedCheck_2453_; 
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2446_ = lean_ctor_get(v___x_2391_, 0);
v_isSharedCheck_2453_ = !lean_is_exclusive(v___x_2391_);
if (v_isSharedCheck_2453_ == 0)
{
v___x_2448_ = v___x_2391_;
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
else
{
lean_inc(v_a_2446_);
lean_dec(v___x_2391_);
v___x_2448_ = lean_box(0);
v_isShared_2449_ = v_isSharedCheck_2453_;
goto v_resetjp_2447_;
}
v_resetjp_2447_:
{
lean_object* v___x_2451_; 
if (v_isShared_2449_ == 0)
{
v___x_2451_ = v___x_2448_;
goto v_reusejp_2450_;
}
else
{
lean_object* v_reuseFailAlloc_2452_; 
v_reuseFailAlloc_2452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2452_, 0, v_a_2446_);
v___x_2451_ = v_reuseFailAlloc_2452_;
goto v_reusejp_2450_;
}
v_reusejp_2450_:
{
return v___x_2451_;
}
}
}
v___jp_1955_:
{
uint8_t v_genDiseq_1962_; 
v_genDiseq_1962_ = lean_ctor_get_uint8(v_config_1805_, sizeof(void*)*1 + 2);
if (v_genDiseq_1962_ == 0)
{
lean_dec_ref(v___x_1954_);
v___y_1933_ = v___y_1959_;
v___y_1934_ = v___y_1960_;
v___y_1935_ = v___y_1956_;
v___y_1936_ = v___y_1961_;
v___y_1937_ = v___y_1957_;
v___y_1938_ = v___y_1958_;
v___y_1939_ = v___x_1910_;
goto v___jp_1932_;
}
else
{
uint8_t v___x_1963_; 
v___x_1963_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1954_);
v___y_1933_ = v___y_1959_;
v___y_1934_ = v___y_1960_;
v___y_1935_ = v___y_1956_;
v___y_1936_ = v___y_1961_;
v___y_1937_ = v___y_1957_;
v___y_1938_ = v___y_1958_;
v___y_1939_ = v___x_1963_;
goto v___jp_1932_;
}
}
v___jp_1964_:
{
if (v___y_1972_ == 0)
{
lean_dec_ref(v___y_1970_);
v___y_1956_ = v___y_1967_;
v___y_1957_ = v___y_1969_;
v___y_1958_ = v___y_1965_;
v___y_1959_ = v___y_1966_;
v___y_1960_ = v___y_1968_;
v___y_1961_ = v___y_1971_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_1973_; 
lean_dec_ref(v___x_1954_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v___x_1973_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1973_, 0, v___y_1970_);
return v___x_1973_;
}
}
v___jp_1974_:
{
uint8_t v___x_1982_; 
v___x_1982_ = l_Lean_Exception_isInterrupt(v_a_1981_);
if (v___x_1982_ == 0)
{
uint8_t v___x_1983_; 
lean_inc_ref(v_a_1981_);
v___x_1983_ = l_Lean_Exception_isRuntime(v_a_1981_);
v___y_1965_ = v___y_1975_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___y_1978_;
v___y_1968_ = v___y_1977_;
v___y_1969_ = v___y_1979_;
v___y_1970_ = v_a_1981_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___x_1983_;
goto v___jp_1964_;
}
else
{
v___y_1965_ = v___y_1975_;
v___y_1966_ = v___y_1976_;
v___y_1967_ = v___y_1978_;
v___y_1968_ = v___y_1977_;
v___y_1969_ = v___y_1979_;
v___y_1970_ = v_a_1981_;
v___y_1971_ = v___y_1980_;
v___y_1972_ = v___x_1982_;
goto v___jp_1964_;
}
}
v___jp_1984_:
{
lean_object* v___x_1991_; 
lean_inc_ref(v___x_1954_);
v___x_1991_ = l_Lean_Meta_mkDecide(v___x_1954_, v___y_1985_, v___y_1986_, v___y_1988_, v___y_1990_);
if (lean_obj_tag(v___x_1991_) == 0)
{
lean_object* v_a_1992_; lean_object* v_keyedConfig_1993_; uint8_t v_trackZetaDelta_1994_; lean_object* v_zetaDeltaSet_1995_; lean_object* v_lctx_1996_; lean_object* v_localInstances_1997_; lean_object* v_defEqCtx_x3f_1998_; lean_object* v_synthPendingDepth_1999_; lean_object* v_customCanUnfoldPredicate_x3f_2000_; uint8_t v_univApprox_2001_; uint8_t v_inTypeClassResolution_2002_; uint8_t v_cacheInferType_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; 
v_a_1992_ = lean_ctor_get(v___x_1991_, 0);
lean_inc_n(v_a_1992_, 2);
lean_dec_ref_known(v___x_1991_, 1);
v_keyedConfig_1993_ = lean_ctor_get(v___y_1985_, 0);
v_trackZetaDelta_1994_ = lean_ctor_get_uint8(v___y_1985_, sizeof(void*)*7);
v_zetaDeltaSet_1995_ = lean_ctor_get(v___y_1985_, 1);
v_lctx_1996_ = lean_ctor_get(v___y_1985_, 2);
v_localInstances_1997_ = lean_ctor_get(v___y_1985_, 3);
v_defEqCtx_x3f_1998_ = lean_ctor_get(v___y_1985_, 4);
v_synthPendingDepth_1999_ = lean_ctor_get(v___y_1985_, 5);
v_customCanUnfoldPredicate_x3f_2000_ = lean_ctor_get(v___y_1985_, 6);
v_univApprox_2001_ = lean_ctor_get_uint8(v___y_1985_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2002_ = lean_ctor_get_uint8(v___y_1985_, sizeof(void*)*7 + 2);
v_cacheInferType_2003_ = lean_ctor_get_uint8(v___y_1985_, sizeof(void*)*7 + 3);
v___x_2004_ = 1;
lean_inc_ref(v_keyedConfig_1993_);
v___x_2005_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2004_, v_keyedConfig_1993_);
lean_inc(v_customCanUnfoldPredicate_x3f_2000_);
lean_inc(v_synthPendingDepth_1999_);
lean_inc(v_defEqCtx_x3f_1998_);
lean_inc_ref(v_localInstances_1997_);
lean_inc_ref(v_lctx_1996_);
lean_inc(v_zetaDeltaSet_1995_);
v___x_2006_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2006_, 0, v___x_2005_);
lean_ctor_set(v___x_2006_, 1, v_zetaDeltaSet_1995_);
lean_ctor_set(v___x_2006_, 2, v_lctx_1996_);
lean_ctor_set(v___x_2006_, 3, v_localInstances_1997_);
lean_ctor_set(v___x_2006_, 4, v_defEqCtx_x3f_1998_);
lean_ctor_set(v___x_2006_, 5, v_synthPendingDepth_1999_);
lean_ctor_set(v___x_2006_, 6, v_customCanUnfoldPredicate_x3f_2000_);
lean_ctor_set_uint8(v___x_2006_, sizeof(void*)*7, v_trackZetaDelta_1994_);
lean_ctor_set_uint8(v___x_2006_, sizeof(void*)*7 + 1, v_univApprox_2001_);
lean_ctor_set_uint8(v___x_2006_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2002_);
lean_ctor_set_uint8(v___x_2006_, sizeof(void*)*7 + 3, v_cacheInferType_2003_);
lean_inc(v___y_1990_);
lean_inc_ref(v___y_1988_);
lean_inc(v___y_1986_);
v___x_2007_ = lean_whnf(v_a_1992_, v___x_2006_, v___y_1986_, v___y_1988_, v___y_1990_);
if (lean_obj_tag(v___x_2007_) == 0)
{
lean_object* v_a_2008_; lean_object* v___x_2009_; uint8_t v___x_2010_; 
v_a_2008_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2008_);
lean_dec_ref_known(v___x_2007_, 1);
v___x_2009_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2010_ = l_Lean_Expr_isConstOf(v_a_2008_, v___x_2009_);
lean_dec(v_a_2008_);
if (v___x_2010_ == 0)
{
lean_dec(v_a_1992_);
v___y_1956_ = v___y_1987_;
v___y_1957_ = v___y_1989_;
v___y_1958_ = v___y_1985_;
v___y_1959_ = v___y_1986_;
v___y_1960_ = v___y_1988_;
v___y_1961_ = v___y_1990_;
goto v___jp_1955_;
}
else
{
lean_object* v___x_2011_; 
lean_inc(v_a_1992_);
v___x_2011_ = l_Lean_Meta_mkEqRefl(v_a_1992_, v___y_1985_, v___y_1986_, v___y_1988_, v___y_1990_);
if (lean_obj_tag(v___x_2011_) == 0)
{
lean_object* v_a_2012_; lean_object* v___x_2013_; 
v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2012_);
lean_dec_ref_known(v___x_2011_, 1);
lean_inc(v_mvarId_1806_);
v___x_2013_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_1985_, v___y_1986_, v___y_1988_, v___y_1990_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v_nargs_2015_; lean_object* v___x_2016_; lean_object* v_dummy_2017_; lean_object* v___x_2018_; lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
v_nargs_2015_ = l_Lean_Expr_getAppNumArgs(v_a_1992_);
v___x_2016_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2017_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_2015_);
v___x_2018_ = lean_mk_array(v_nargs_2015_, v_dummy_2017_);
v___x_2019_ = lean_unsigned_to_nat(1u);
v___x_2020_ = lean_nat_sub(v_nargs_2015_, v___x_2019_);
lean_dec(v_nargs_2015_);
v___x_2021_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_1992_, v___x_2018_, v___x_2020_);
v___x_2022_ = lean_array_push(v___x_2021_, v_a_2012_);
v___x_2023_ = l_Lean_mkAppN(v___x_2016_, v___x_2022_);
lean_dec_ref(v___x_2022_);
lean_inc(v_val_1837_);
v___x_2024_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_2025_ = l_Lean_Meta_mkAbsurd(v_a_2014_, v___x_2024_, v___x_2023_, v___y_1985_, v___y_1986_, v___y_1988_, v___y_1990_);
if (lean_obj_tag(v___x_2025_) == 0)
{
lean_object* v_a_2026_; lean_object* v___x_2027_; 
v_a_2026_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2026_);
lean_dec_ref_known(v___x_2025_, 1);
lean_inc(v_mvarId_1806_);
v___x_2027_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_2026_, v___y_1986_);
if (lean_obj_tag(v___x_2027_) == 0)
{
lean_object* v___x_2029_; uint8_t v_isShared_2030_; uint8_t v_isSharedCheck_2036_; 
lean_dec_ref(v___x_1954_);
lean_dec(v_val_1837_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_isSharedCheck_2036_ = !lean_is_exclusive(v___x_2027_);
if (v_isSharedCheck_2036_ == 0)
{
lean_object* v_unused_2037_; 
v_unused_2037_ = lean_ctor_get(v___x_2027_, 0);
lean_dec(v_unused_2037_);
v___x_2029_ = v___x_2027_;
v_isShared_2030_ = v_isSharedCheck_2036_;
goto v_resetjp_2028_;
}
else
{
lean_dec(v___x_2027_);
v___x_2029_ = lean_box(0);
v_isShared_2030_ = v_isSharedCheck_2036_;
goto v_resetjp_2028_;
}
v_resetjp_2028_:
{
lean_object* v___x_2031_; lean_object* v___x_2033_; 
v___x_2031_ = lean_box(v___x_1816_);
if (v_isShared_2030_ == 0)
{
lean_ctor_set_tag(v___x_2029_, 1);
lean_ctor_set(v___x_2029_, 0, v___x_2031_);
v___x_2033_ = v___x_2029_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v___x_1841_);
v_a_1823_ = v___x_2034_;
goto v___jp_1822_;
}
}
}
else
{
lean_object* v_a_2038_; 
v_a_2038_ = lean_ctor_get(v___x_2027_, 0);
lean_inc(v_a_2038_);
lean_dec_ref_known(v___x_2027_, 1);
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1987_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1990_;
v_a_1981_ = v_a_2038_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2039_; 
v_a_2039_ = lean_ctor_get(v___x_2025_, 0);
lean_inc(v_a_2039_);
lean_dec_ref_known(v___x_2025_, 1);
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1987_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1990_;
v_a_1981_ = v_a_2039_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2040_; 
lean_dec(v_a_2012_);
lean_dec(v_a_1992_);
v_a_2040_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2040_);
lean_dec_ref_known(v___x_2013_, 1);
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1987_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1990_;
v_a_1981_ = v_a_2040_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2041_; 
lean_dec(v_a_1992_);
v_a_2041_ = lean_ctor_get(v___x_2011_, 0);
lean_inc(v_a_2041_);
lean_dec_ref_known(v___x_2011_, 1);
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1987_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1990_;
v_a_1981_ = v_a_2041_;
goto v___jp_1974_;
}
}
}
else
{
lean_object* v_a_2042_; 
lean_dec(v_a_1992_);
v_a_2042_ = lean_ctor_get(v___x_2007_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2007_, 1);
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1987_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1990_;
v_a_1981_ = v_a_2042_;
goto v___jp_1974_;
}
}
else
{
lean_object* v_a_2043_; 
v_a_2043_ = lean_ctor_get(v___x_1991_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_1991_, 1);
v___y_1975_ = v___y_1985_;
v___y_1976_ = v___y_1986_;
v___y_1977_ = v___y_1988_;
v___y_1978_ = v___y_1987_;
v___y_1979_ = v___y_1989_;
v___y_1980_ = v___y_1990_;
v_a_1981_ = v_a_2043_;
goto v___jp_1974_;
}
}
v___jp_2044_:
{
if (v___y_2051_ == 0)
{
v___y_1956_ = v___y_2047_;
v___y_1957_ = v___y_2049_;
v___y_1958_ = v___y_2045_;
v___y_1959_ = v___y_2046_;
v___y_1960_ = v___y_2048_;
v___y_1961_ = v___y_2050_;
goto v___jp_1955_;
}
else
{
v___y_1985_ = v___y_2045_;
v___y_1986_ = v___y_2046_;
v___y_1987_ = v___y_2047_;
v___y_1988_ = v___y_2048_;
v___y_1989_ = v___y_2049_;
v___y_1990_ = v___y_2050_;
goto v___jp_1984_;
}
}
v___jp_2052_:
{
if (v___y_2060_ == 0)
{
lean_dec_ref(v___y_2053_);
v___y_2045_ = v___y_2054_;
v___y_2046_ = v___y_2055_;
v___y_2047_ = v___y_2057_;
v___y_2048_ = v___y_2056_;
v___y_2049_ = v___y_2058_;
v___y_2050_ = v___y_2059_;
v___y_2051_ = v___x_1910_;
goto v___jp_2044_;
}
else
{
uint8_t v___x_2061_; 
v___x_2061_ = l_Lean_Expr_hasFVar(v___y_2053_);
lean_dec_ref(v___y_2053_);
if (v___x_2061_ == 0)
{
v___y_1985_ = v___y_2054_;
v___y_1986_ = v___y_2055_;
v___y_1987_ = v___y_2057_;
v___y_1988_ = v___y_2056_;
v___y_1989_ = v___y_2058_;
v___y_1990_ = v___y_2059_;
goto v___jp_1984_;
}
else
{
v___y_2045_ = v___y_2054_;
v___y_2046_ = v___y_2055_;
v___y_2047_ = v___y_2057_;
v___y_2048_ = v___y_2056_;
v___y_2049_ = v___y_2058_;
v___y_2050_ = v___y_2059_;
v___y_2051_ = v___x_1910_;
goto v___jp_2044_;
}
}
}
v___jp_2062_:
{
lean_object* v___x_2070_; 
lean_inc_ref(v___x_1954_);
v___x_2070_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1954_, v___y_2064_);
if (lean_obj_tag(v___x_2070_) == 0)
{
lean_object* v_a_2071_; uint8_t v___x_2072_; 
v_a_2071_ = lean_ctor_get(v___x_2070_, 0);
lean_inc(v_a_2071_);
lean_dec_ref_known(v___x_2070_, 1);
v___x_2072_ = l_Lean_Expr_hasMVar(v_a_2071_);
if (v___x_2072_ == 0)
{
v___y_2053_ = v_a_2071_;
v___y_2054_ = v___y_2063_;
v___y_2055_ = v___y_2064_;
v___y_2056_ = v___y_2065_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___y_2067_;
v___y_2059_ = v___y_2068_;
v___y_2060_ = v___y_2069_;
goto v___jp_2052_;
}
else
{
v___y_2053_ = v_a_2071_;
v___y_2054_ = v___y_2063_;
v___y_2055_ = v___y_2064_;
v___y_2056_ = v___y_2065_;
v___y_2057_ = v___y_2066_;
v___y_2058_ = v___y_2067_;
v___y_2059_ = v___y_2068_;
v___y_2060_ = v___x_1910_;
goto v___jp_2052_;
}
}
else
{
lean_object* v_a_2073_; lean_object* v___x_2075_; uint8_t v_isShared_2076_; uint8_t v_isSharedCheck_2080_; 
lean_dec_ref(v___x_1954_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2073_ = lean_ctor_get(v___x_2070_, 0);
v_isSharedCheck_2080_ = !lean_is_exclusive(v___x_2070_);
if (v_isSharedCheck_2080_ == 0)
{
v___x_2075_ = v___x_2070_;
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
else
{
lean_inc(v_a_2073_);
lean_dec(v___x_2070_);
v___x_2075_ = lean_box(0);
v_isShared_2076_ = v_isSharedCheck_2080_;
goto v_resetjp_2074_;
}
v_resetjp_2074_:
{
lean_object* v___x_2078_; 
if (v_isShared_2076_ == 0)
{
v___x_2078_ = v___x_2075_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2079_; 
v_reuseFailAlloc_2079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_a_2073_);
v___x_2078_ = v_reuseFailAlloc_2079_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
return v___x_2078_;
}
}
}
}
v___jp_2081_:
{
if (v___y_2088_ == 0)
{
v___y_1956_ = v___y_2084_;
v___y_1957_ = v___y_2086_;
v___y_1958_ = v___y_2082_;
v___y_1959_ = v___y_2083_;
v___y_1960_ = v___y_2085_;
v___y_1961_ = v___y_2087_;
goto v___jp_1955_;
}
else
{
v___y_2063_ = v___y_2082_;
v___y_2064_ = v___y_2083_;
v___y_2065_ = v___y_2085_;
v___y_2066_ = v___y_2084_;
v___y_2067_ = v___y_2086_;
v___y_2068_ = v___y_2087_;
v___y_2069_ = v___y_2088_;
goto v___jp_2062_;
}
}
v___jp_2089_:
{
uint8_t v_useDecide_2096_; 
v_useDecide_2096_ = lean_ctor_get_uint8(v_config_1805_, sizeof(void*)*1);
if (v_useDecide_2096_ == 0)
{
v___y_2082_ = v___y_2092_;
v___y_2083_ = v___y_2093_;
v___y_2084_ = v___y_2090_;
v___y_2085_ = v___y_2094_;
v___y_2086_ = v_isHEq_2091_;
v___y_2087_ = v___y_2095_;
v___y_2088_ = v___x_1910_;
goto v___jp_2081_;
}
else
{
uint8_t v___x_2097_; 
v___x_2097_ = l_Lean_Expr_hasFVar(v___x_1954_);
if (v___x_2097_ == 0)
{
v___y_2063_ = v___y_2092_;
v___y_2064_ = v___y_2093_;
v___y_2065_ = v___y_2094_;
v___y_2066_ = v___y_2090_;
v___y_2067_ = v_isHEq_2091_;
v___y_2068_ = v___y_2095_;
v___y_2069_ = v_useDecide_2096_;
goto v___jp_2062_;
}
else
{
v___y_2082_ = v___y_2092_;
v___y_2083_ = v___y_2093_;
v___y_2084_ = v___y_2090_;
v___y_2085_ = v___y_2094_;
v___y_2086_ = v_isHEq_2091_;
v___y_2087_ = v___y_2095_;
v___y_2088_ = v___x_1910_;
goto v___jp_2081_;
}
}
}
v___jp_2098_:
{
lean_object* v___x_2106_; 
v___x_2106_ = l_Lean_Meta_isExprDefEq(v___y_2105_, v___y_2104_, v___y_2099_, v___y_2100_, v___y_2103_, v___y_2101_);
if (lean_obj_tag(v___x_2106_) == 0)
{
lean_object* v_a_2107_; uint8_t v___x_2108_; 
v_a_2107_ = lean_ctor_get(v___x_2106_, 0);
lean_inc(v_a_2107_);
lean_dec_ref_known(v___x_2106_, 1);
v___x_2108_ = lean_unbox(v_a_2107_);
lean_dec(v_a_2107_);
if (v___x_2108_ == 0)
{
v___y_2090_ = v___y_2102_;
v_isHEq_2091_ = v___x_1816_;
v___y_2092_ = v___y_2099_;
v___y_2093_ = v___y_2100_;
v___y_2094_ = v___y_2103_;
v___y_2095_ = v___y_2101_;
goto v___jp_2089_;
}
else
{
lean_object* v___x_2109_; 
lean_dec_ref(v___x_1954_);
lean_dec_ref(v_config_1805_);
lean_inc(v_mvarId_1806_);
v___x_2109_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_2099_, v___y_2100_, v___y_2103_, v___y_2101_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2111_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_2112_ = l_Lean_Meta_mkEqOfHEq(v___x_2111_, v___x_1816_, v___y_2099_, v___y_2100_, v___y_2103_, v___y_2101_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v_a_2113_; lean_object* v___x_2114_; 
v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
lean_inc(v_a_2113_);
lean_dec_ref_known(v___x_2112_, 1);
v___x_2114_ = l_Lean_Meta_mkNoConfusion(v_a_2110_, v_a_2113_, v___y_2099_, v___y_2100_, v___y_2103_, v___y_2101_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_2115_, v___y_2100_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
lean_dec_ref_known(v___x_2116_, 1);
v___x_2117_ = lean_box(v___x_1816_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2117_);
v___x_2119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2119_, 0, v___x_2118_);
lean_ctor_set(v___x_2119_, 1, v___x_1841_);
v_a_1823_ = v___x_2119_;
goto v___jp_1822_;
}
else
{
lean_object* v_a_2120_; lean_object* v___x_2122_; uint8_t v_isShared_2123_; uint8_t v_isSharedCheck_2127_; 
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_2120_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2127_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2127_ == 0)
{
v___x_2122_ = v___x_2116_;
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
else
{
lean_inc(v_a_2120_);
lean_dec(v___x_2116_);
v___x_2122_ = lean_box(0);
v_isShared_2123_ = v_isSharedCheck_2127_;
goto v_resetjp_2121_;
}
v_resetjp_2121_:
{
lean_object* v___x_2125_; 
if (v_isShared_2123_ == 0)
{
v___x_2125_ = v___x_2122_;
goto v_reusejp_2124_;
}
else
{
lean_object* v_reuseFailAlloc_2126_; 
v_reuseFailAlloc_2126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2126_, 0, v_a_2120_);
v___x_2125_ = v_reuseFailAlloc_2126_;
goto v_reusejp_2124_;
}
v_reusejp_2124_:
{
return v___x_2125_;
}
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2128_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2114_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2114_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
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
lean_dec(v_a_2110_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2136_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2112_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2112_);
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
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2144_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2109_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2109_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
else
{
lean_object* v_a_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2159_; 
lean_dec_ref(v___x_1954_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2152_ = lean_ctor_get(v___x_2106_, 0);
v_isSharedCheck_2159_ = !lean_is_exclusive(v___x_2106_);
if (v_isSharedCheck_2159_ == 0)
{
v___x_2154_ = v___x_2106_;
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_a_2152_);
lean_dec(v___x_2106_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2159_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2157_; 
if (v_isShared_2155_ == 0)
{
v___x_2157_ = v___x_2154_;
goto v_reusejp_2156_;
}
else
{
lean_object* v_reuseFailAlloc_2158_; 
v_reuseFailAlloc_2158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2158_, 0, v_a_2152_);
v___x_2157_ = v_reuseFailAlloc_2158_;
goto v_reusejp_2156_;
}
v_reusejp_2156_:
{
return v___x_2157_;
}
}
}
}
v___jp_2160_:
{
lean_object* v___x_2166_; 
lean_inc_ref(v___x_1954_);
v___x_2166_ = l_Lean_Meta_matchHEq_x3f(v___x_1954_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2166_) == 0)
{
lean_object* v_a_2167_; 
v_a_2167_ = lean_ctor_get(v___x_2166_, 0);
lean_inc(v_a_2167_);
lean_dec_ref_known(v___x_2166_, 1);
if (lean_obj_tag(v_a_2167_) == 1)
{
lean_object* v_val_2168_; lean_object* v_snd_2169_; lean_object* v_snd_2170_; lean_object* v_fst_2171_; lean_object* v_fst_2172_; lean_object* v_fst_2173_; lean_object* v_snd_2174_; lean_object* v___x_2175_; 
v_val_2168_ = lean_ctor_get(v_a_2167_, 0);
lean_inc(v_val_2168_);
lean_dec_ref_known(v_a_2167_, 1);
v_snd_2169_ = lean_ctor_get(v_val_2168_, 1);
lean_inc(v_snd_2169_);
v_snd_2170_ = lean_ctor_get(v_snd_2169_, 1);
lean_inc(v_snd_2170_);
v_fst_2171_ = lean_ctor_get(v_val_2168_, 0);
lean_inc(v_fst_2171_);
lean_dec(v_val_2168_);
v_fst_2172_ = lean_ctor_get(v_snd_2169_, 0);
lean_inc(v_fst_2172_);
lean_dec(v_snd_2169_);
v_fst_2173_ = lean_ctor_get(v_snd_2170_, 0);
lean_inc(v_fst_2173_);
v_snd_2174_ = lean_ctor_get(v_snd_2170_, 1);
lean_inc(v_snd_2174_);
lean_dec(v_snd_2170_);
v___x_2175_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2172_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2175_) == 0)
{
lean_object* v_a_2176_; 
v_a_2176_ = lean_ctor_get(v___x_2175_, 0);
lean_inc(v_a_2176_);
lean_dec_ref_known(v___x_2175_, 1);
if (lean_obj_tag(v_a_2176_) == 1)
{
lean_object* v_val_2177_; lean_object* v___x_2178_; 
v_val_2177_ = lean_ctor_get(v_a_2176_, 0);
lean_inc(v_val_2177_);
lean_dec_ref_known(v_a_2176_, 1);
v___x_2178_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2174_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
if (lean_obj_tag(v___x_2178_) == 0)
{
lean_object* v_a_2179_; 
v_a_2179_ = lean_ctor_get(v___x_2178_, 0);
lean_inc(v_a_2179_);
lean_dec_ref_known(v___x_2178_, 1);
if (lean_obj_tag(v_a_2179_) == 1)
{
lean_object* v_toConstantVal_2180_; lean_object* v_val_2181_; lean_object* v_toConstantVal_2182_; lean_object* v_name_2183_; lean_object* v_name_2184_; uint8_t v___x_2185_; 
v_toConstantVal_2180_ = lean_ctor_get(v_val_2177_, 0);
lean_inc_ref(v_toConstantVal_2180_);
lean_dec(v_val_2177_);
v_val_2181_ = lean_ctor_get(v_a_2179_, 0);
lean_inc(v_val_2181_);
lean_dec_ref_known(v_a_2179_, 1);
v_toConstantVal_2182_ = lean_ctor_get(v_val_2181_, 0);
lean_inc_ref(v_toConstantVal_2182_);
lean_dec(v_val_2181_);
v_name_2183_ = lean_ctor_get(v_toConstantVal_2180_, 0);
lean_inc(v_name_2183_);
lean_dec_ref(v_toConstantVal_2180_);
v_name_2184_ = lean_ctor_get(v_toConstantVal_2182_, 0);
lean_inc(v_name_2184_);
lean_dec_ref(v_toConstantVal_2182_);
v___x_2185_ = lean_name_eq(v_name_2183_, v_name_2184_);
lean_dec(v_name_2184_);
lean_dec(v_name_2183_);
if (v___x_2185_ == 0)
{
v___y_2099_ = v___y_2162_;
v___y_2100_ = v___y_2163_;
v___y_2101_ = v___y_2165_;
v___y_2102_ = v_isEq_2161_;
v___y_2103_ = v___y_2164_;
v___y_2104_ = v_fst_2173_;
v___y_2105_ = v_fst_2171_;
goto v___jp_2098_;
}
else
{
if (v___x_1910_ == 0)
{
lean_dec(v_fst_2173_);
lean_dec(v_fst_2171_);
v___y_2090_ = v_isEq_2161_;
v_isHEq_2091_ = v___x_1816_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
v___y_2094_ = v___y_2164_;
v___y_2095_ = v___y_2165_;
goto v___jp_2089_;
}
else
{
v___y_2099_ = v___y_2162_;
v___y_2100_ = v___y_2163_;
v___y_2101_ = v___y_2165_;
v___y_2102_ = v_isEq_2161_;
v___y_2103_ = v___y_2164_;
v___y_2104_ = v_fst_2173_;
v___y_2105_ = v_fst_2171_;
goto v___jp_2098_;
}
}
}
else
{
lean_dec(v_a_2179_);
lean_dec(v_val_2177_);
lean_dec(v_fst_2173_);
lean_dec(v_fst_2171_);
v___y_2090_ = v_isEq_2161_;
v_isHEq_2091_ = v___x_1816_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
v___y_2094_ = v___y_2164_;
v___y_2095_ = v___y_2165_;
goto v___jp_2089_;
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v_val_2177_);
lean_dec(v_fst_2173_);
lean_dec(v_fst_2171_);
lean_dec_ref(v___x_1954_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2186_ = lean_ctor_get(v___x_2178_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2178_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2178_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2178_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
else
{
lean_dec(v_a_2176_);
lean_dec(v_snd_2174_);
lean_dec(v_fst_2173_);
lean_dec(v_fst_2171_);
v___y_2090_ = v_isEq_2161_;
v_isHEq_2091_ = v___x_1816_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
v___y_2094_ = v___y_2164_;
v___y_2095_ = v___y_2165_;
goto v___jp_2089_;
}
}
else
{
lean_object* v_a_2194_; lean_object* v___x_2196_; uint8_t v_isShared_2197_; uint8_t v_isSharedCheck_2201_; 
lean_dec(v_snd_2174_);
lean_dec(v_fst_2173_);
lean_dec(v_fst_2171_);
lean_dec_ref(v___x_1954_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2194_ = lean_ctor_get(v___x_2175_, 0);
v_isSharedCheck_2201_ = !lean_is_exclusive(v___x_2175_);
if (v_isSharedCheck_2201_ == 0)
{
v___x_2196_ = v___x_2175_;
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
else
{
lean_inc(v_a_2194_);
lean_dec(v___x_2175_);
v___x_2196_ = lean_box(0);
v_isShared_2197_ = v_isSharedCheck_2201_;
goto v_resetjp_2195_;
}
v_resetjp_2195_:
{
lean_object* v___x_2199_; 
if (v_isShared_2197_ == 0)
{
v___x_2199_ = v___x_2196_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v_a_2194_);
v___x_2199_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
return v___x_2199_;
}
}
}
}
else
{
lean_dec(v_a_2167_);
v___y_2090_ = v_isEq_2161_;
v_isHEq_2091_ = v___x_1910_;
v___y_2092_ = v___y_2162_;
v___y_2093_ = v___y_2163_;
v___y_2094_ = v___y_2164_;
v___y_2095_ = v___y_2165_;
goto v___jp_2089_;
}
}
else
{
lean_object* v_a_2202_; lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2209_; 
lean_dec_ref(v___x_1954_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2202_ = lean_ctor_get(v___x_2166_, 0);
v_isSharedCheck_2209_ = !lean_is_exclusive(v___x_2166_);
if (v_isSharedCheck_2209_ == 0)
{
v___x_2204_ = v___x_2166_;
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
else
{
lean_inc(v_a_2202_);
lean_dec(v___x_2166_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2209_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2207_; 
if (v_isShared_2205_ == 0)
{
v___x_2207_ = v___x_2204_;
goto v_reusejp_2206_;
}
else
{
lean_object* v_reuseFailAlloc_2208_; 
v_reuseFailAlloc_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2208_, 0, v_a_2202_);
v___x_2207_ = v_reuseFailAlloc_2208_;
goto v_reusejp_2206_;
}
v_reusejp_2206_:
{
return v___x_2207_;
}
}
}
}
v___jp_2210_:
{
lean_object* v___x_2215_; 
lean_inc_ref(v___x_1954_);
v___x_2215_ = l_Lean_Meta_matchEq_x3f(v___x_1954_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2215_) == 0)
{
lean_object* v_a_2216_; 
v_a_2216_ = lean_ctor_get(v___x_2215_, 0);
lean_inc(v_a_2216_);
lean_dec_ref_known(v___x_2215_, 1);
if (lean_obj_tag(v_a_2216_) == 1)
{
lean_object* v_val_2217_; lean_object* v_snd_2218_; lean_object* v_fst_2219_; lean_object* v_snd_2220_; lean_object* v___x_2221_; 
v_val_2217_ = lean_ctor_get(v_a_2216_, 0);
lean_inc(v_val_2217_);
lean_dec_ref_known(v_a_2216_, 1);
v_snd_2218_ = lean_ctor_get(v_val_2217_, 1);
lean_inc(v_snd_2218_);
lean_dec(v_val_2217_);
v_fst_2219_ = lean_ctor_get(v_snd_2218_, 0);
lean_inc(v_fst_2219_);
v_snd_2220_ = lean_ctor_get(v_snd_2218_, 1);
lean_inc(v_snd_2220_);
lean_dec(v_snd_2218_);
v___x_2221_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2219_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2221_) == 0)
{
lean_object* v_a_2222_; 
v_a_2222_ = lean_ctor_get(v___x_2221_, 0);
lean_inc(v_a_2222_);
lean_dec_ref_known(v___x_2221_, 1);
if (lean_obj_tag(v_a_2222_) == 1)
{
lean_object* v_val_2223_; lean_object* v___x_2224_; 
v_val_2223_ = lean_ctor_get(v_a_2222_, 0);
lean_inc(v_val_2223_);
lean_dec_ref_known(v_a_2222_, 1);
v___x_2224_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2220_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_);
if (lean_obj_tag(v___x_2224_) == 0)
{
lean_object* v_a_2225_; 
v_a_2225_ = lean_ctor_get(v___x_2224_, 0);
lean_inc(v_a_2225_);
lean_dec_ref_known(v___x_2224_, 1);
if (lean_obj_tag(v_a_2225_) == 1)
{
lean_object* v_toConstantVal_2226_; lean_object* v_val_2227_; lean_object* v_toConstantVal_2228_; lean_object* v_name_2229_; lean_object* v_name_2230_; uint8_t v___x_2231_; 
v_toConstantVal_2226_ = lean_ctor_get(v_val_2223_, 0);
lean_inc_ref(v_toConstantVal_2226_);
lean_dec(v_val_2223_);
v_val_2227_ = lean_ctor_get(v_a_2225_, 0);
lean_inc(v_val_2227_);
lean_dec_ref_known(v_a_2225_, 1);
v_toConstantVal_2228_ = lean_ctor_get(v_val_2227_, 0);
lean_inc_ref(v_toConstantVal_2228_);
lean_dec(v_val_2227_);
v_name_2229_ = lean_ctor_get(v_toConstantVal_2226_, 0);
lean_inc(v_name_2229_);
lean_dec_ref(v_toConstantVal_2226_);
v_name_2230_ = lean_ctor_get(v_toConstantVal_2228_, 0);
lean_inc(v_name_2230_);
lean_dec_ref(v_toConstantVal_2228_);
v___x_2231_ = lean_name_eq(v_name_2229_, v_name_2230_);
lean_dec(v_name_2230_);
lean_dec(v_name_2229_);
if (v___x_2231_ == 0)
{
lean_dec_ref(v___x_1954_);
lean_dec_ref(v_config_1805_);
v___y_1843_ = v___y_2211_;
v___y_1844_ = v___y_2213_;
v___y_1845_ = v___y_2214_;
v___y_1846_ = v___y_2212_;
goto v___jp_1842_;
}
else
{
if (v___x_1910_ == 0)
{
lean_del_object(v___x_1839_);
v_isEq_2161_ = v___x_1816_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
v___y_2164_ = v___y_2213_;
v___y_2165_ = v___y_2214_;
goto v___jp_2160_;
}
else
{
lean_dec_ref(v___x_1954_);
lean_dec_ref(v_config_1805_);
v___y_1843_ = v___y_2211_;
v___y_1844_ = v___y_2213_;
v___y_1845_ = v___y_2214_;
v___y_1846_ = v___y_2212_;
goto v___jp_1842_;
}
}
}
else
{
lean_dec(v_a_2225_);
lean_dec(v_val_2223_);
lean_del_object(v___x_1839_);
v_isEq_2161_ = v___x_1816_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
v___y_2164_ = v___y_2213_;
v___y_2165_ = v___y_2214_;
goto v___jp_2160_;
}
}
else
{
lean_object* v_a_2232_; lean_object* v___x_2234_; uint8_t v_isShared_2235_; uint8_t v_isSharedCheck_2239_; 
lean_dec(v_val_2223_);
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2232_ = lean_ctor_get(v___x_2224_, 0);
v_isSharedCheck_2239_ = !lean_is_exclusive(v___x_2224_);
if (v_isSharedCheck_2239_ == 0)
{
v___x_2234_ = v___x_2224_;
v_isShared_2235_ = v_isSharedCheck_2239_;
goto v_resetjp_2233_;
}
else
{
lean_inc(v_a_2232_);
lean_dec(v___x_2224_);
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
lean_dec(v_a_2222_);
lean_dec(v_snd_2220_);
lean_del_object(v___x_1839_);
v_isEq_2161_ = v___x_1816_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
v___y_2164_ = v___y_2213_;
v___y_2165_ = v___y_2214_;
goto v___jp_2160_;
}
}
else
{
lean_object* v_a_2240_; lean_object* v___x_2242_; uint8_t v_isShared_2243_; uint8_t v_isSharedCheck_2247_; 
lean_dec(v_snd_2220_);
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2240_ = lean_ctor_get(v___x_2221_, 0);
v_isSharedCheck_2247_ = !lean_is_exclusive(v___x_2221_);
if (v_isSharedCheck_2247_ == 0)
{
v___x_2242_ = v___x_2221_;
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
else
{
lean_inc(v_a_2240_);
lean_dec(v___x_2221_);
v___x_2242_ = lean_box(0);
v_isShared_2243_ = v_isSharedCheck_2247_;
goto v_resetjp_2241_;
}
v_resetjp_2241_:
{
lean_object* v___x_2245_; 
if (v_isShared_2243_ == 0)
{
v___x_2245_ = v___x_2242_;
goto v_reusejp_2244_;
}
else
{
lean_object* v_reuseFailAlloc_2246_; 
v_reuseFailAlloc_2246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2246_, 0, v_a_2240_);
v___x_2245_ = v_reuseFailAlloc_2246_;
goto v_reusejp_2244_;
}
v_reusejp_2244_:
{
return v___x_2245_;
}
}
}
}
else
{
lean_dec(v_a_2216_);
lean_del_object(v___x_1839_);
v_isEq_2161_ = v___x_1910_;
v___y_2162_ = v___y_2211_;
v___y_2163_ = v___y_2212_;
v___y_2164_ = v___y_2213_;
v___y_2165_ = v___y_2214_;
goto v___jp_2160_;
}
}
else
{
lean_object* v_a_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2255_; 
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2248_ = lean_ctor_get(v___x_2215_, 0);
v_isSharedCheck_2255_ = !lean_is_exclusive(v___x_2215_);
if (v_isSharedCheck_2255_ == 0)
{
v___x_2250_ = v___x_2215_;
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_a_2248_);
lean_dec(v___x_2215_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2255_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2253_; 
if (v_isShared_2251_ == 0)
{
v___x_2253_ = v___x_2250_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2254_; 
v_reuseFailAlloc_2254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2254_, 0, v_a_2248_);
v___x_2253_ = v_reuseFailAlloc_2254_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
return v___x_2253_;
}
}
}
}
v___jp_2256_:
{
lean_object* v___x_2261_; 
lean_inc_ref(v___x_1954_);
v___x_2261_ = l_Lean_refutableHasNotBit_x3f(v___x_1954_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2261_) == 0)
{
lean_object* v_a_2262_; 
v_a_2262_ = lean_ctor_get(v___x_2261_, 0);
lean_inc(v_a_2262_);
lean_dec_ref_known(v___x_2261_, 1);
if (lean_obj_tag(v_a_2262_) == 1)
{
lean_object* v_val_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2302_; 
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec_ref(v_config_1805_);
v_val_2263_ = lean_ctor_get(v_a_2262_, 0);
v_isSharedCheck_2302_ = !lean_is_exclusive(v_a_2262_);
if (v_isSharedCheck_2302_ == 0)
{
v___x_2265_ = v_a_2262_;
v_isShared_2266_ = v_isSharedCheck_2302_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_val_2263_);
lean_dec(v_a_2262_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2302_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2267_; 
lean_inc(v_mvarId_1806_);
v___x_2267_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2267_) == 0)
{
lean_object* v_a_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v_a_2268_ = lean_ctor_get(v___x_2267_, 0);
lean_inc(v_a_2268_);
lean_dec_ref_known(v___x_2267_, 1);
v___x_2269_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_2270_ = l_Lean_Meta_mkAbsurd(v_a_2268_, v_val_2263_, v___x_2269_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2270_) == 0)
{
lean_object* v_a_2271_; lean_object* v___x_2272_; 
v_a_2271_ = lean_ctor_get(v___x_2270_, 0);
lean_inc(v_a_2271_);
lean_dec_ref_known(v___x_2270_, 1);
v___x_2272_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_2271_, v___y_2258_);
if (lean_obj_tag(v___x_2272_) == 0)
{
lean_object* v___x_2273_; lean_object* v___x_2275_; 
lean_dec_ref_known(v___x_2272_, 1);
v___x_2273_ = lean_box(v___x_1816_);
if (v_isShared_2266_ == 0)
{
lean_ctor_set(v___x_2265_, 0, v___x_2273_);
v___x_2275_ = v___x_2265_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2277_; 
v_reuseFailAlloc_2277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2277_, 0, v___x_2273_);
v___x_2275_ = v_reuseFailAlloc_2277_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
lean_object* v___x_2276_; 
v___x_2276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2276_, 0, v___x_2275_);
lean_ctor_set(v___x_2276_, 1, v___x_1841_);
v_a_1823_ = v___x_2276_;
goto v___jp_1822_;
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
lean_del_object(v___x_2265_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_2278_ = lean_ctor_get(v___x_2272_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2272_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2272_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2272_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_del_object(v___x_2265_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2286_ = lean_ctor_get(v___x_2270_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2270_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2270_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2270_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_del_object(v___x_2265_);
lean_dec(v_val_2263_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2294_ = lean_ctor_get(v___x_2267_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2267_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2267_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2267_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
else
{
lean_object* v___x_2303_; 
lean_dec(v_a_2262_);
lean_inc_ref(v___x_1954_);
v___x_2303_ = l_Lean_Meta_matchNe_x3f(v___x_1954_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2303_) == 0)
{
lean_object* v_a_2304_; 
v_a_2304_ = lean_ctor_get(v___x_2303_, 0);
lean_inc(v_a_2304_);
lean_dec_ref_known(v___x_2303_, 1);
if (lean_obj_tag(v_a_2304_) == 1)
{
lean_object* v_val_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2374_; 
v_val_2305_ = lean_ctor_get(v_a_2304_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v_a_2304_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2307_ = v_a_2304_;
v_isShared_2308_ = v_isSharedCheck_2374_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_val_2305_);
lean_dec(v_a_2304_);
v___x_2307_ = lean_box(0);
v_isShared_2308_ = v_isSharedCheck_2374_;
goto v_resetjp_2306_;
}
v_resetjp_2306_:
{
lean_object* v_snd_2309_; lean_object* v_fst_2310_; lean_object* v_snd_2311_; lean_object* v___x_2313_; uint8_t v_isShared_2314_; uint8_t v_isSharedCheck_2373_; 
v_snd_2309_ = lean_ctor_get(v_val_2305_, 1);
lean_inc(v_snd_2309_);
lean_dec(v_val_2305_);
v_fst_2310_ = lean_ctor_get(v_snd_2309_, 0);
v_snd_2311_ = lean_ctor_get(v_snd_2309_, 1);
v_isSharedCheck_2373_ = !lean_is_exclusive(v_snd_2309_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2313_ = v_snd_2309_;
v_isShared_2314_ = v_isSharedCheck_2373_;
goto v_resetjp_2312_;
}
else
{
lean_inc(v_snd_2311_);
lean_inc(v_fst_2310_);
lean_dec(v_snd_2309_);
v___x_2313_ = lean_box(0);
v_isShared_2314_ = v_isSharedCheck_2373_;
goto v_resetjp_2312_;
}
v_resetjp_2312_:
{
lean_object* v___x_2315_; 
lean_inc(v_fst_2310_);
v___x_2315_ = l_Lean_Meta_isExprDefEq(v_fst_2310_, v_snd_2311_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2315_) == 0)
{
lean_object* v_a_2316_; uint8_t v___x_2317_; 
v_a_2316_ = lean_ctor_get(v___x_2315_, 0);
lean_inc(v_a_2316_);
lean_dec_ref_known(v___x_2315_, 1);
v___x_2317_ = lean_unbox(v_a_2316_);
lean_dec(v_a_2316_);
if (v___x_2317_ == 0)
{
lean_del_object(v___x_2313_);
lean_dec(v_fst_2310_);
lean_del_object(v___x_2307_);
v___y_2211_ = v___y_2257_;
v___y_2212_ = v___y_2258_;
v___y_2213_ = v___y_2259_;
v___y_2214_ = v___y_2260_;
goto v___jp_2210_;
}
else
{
lean_object* v___x_2318_; 
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec_ref(v_config_1805_);
lean_inc(v_mvarId_1806_);
v___x_2318_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = l_Lean_Meta_mkEqRefl(v_fst_2310_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
lean_inc(v_a_2321_);
lean_dec_ref_known(v___x_2320_, 1);
v___x_2322_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_2323_ = l_Lean_Meta_mkAbsurd(v_a_2319_, v_a_2321_, v___x_2322_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_2324_, v___y_2258_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2328_; 
lean_dec_ref_known(v___x_2325_, 1);
v___x_2326_ = lean_box(v___x_1816_);
if (v_isShared_2308_ == 0)
{
lean_ctor_set(v___x_2307_, 0, v___x_2326_);
v___x_2328_ = v___x_2307_;
goto v_reusejp_2327_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2326_);
v___x_2328_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2327_;
}
v_reusejp_2327_:
{
lean_object* v___x_2330_; 
if (v_isShared_2314_ == 0)
{
lean_ctor_set(v___x_2313_, 1, v___x_1841_);
lean_ctor_set(v___x_2313_, 0, v___x_2328_);
v___x_2330_ = v___x_2313_;
goto v_reusejp_2329_;
}
else
{
lean_object* v_reuseFailAlloc_2331_; 
v_reuseFailAlloc_2331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2331_, 0, v___x_2328_);
lean_ctor_set(v_reuseFailAlloc_2331_, 1, v___x_1841_);
v___x_2330_ = v_reuseFailAlloc_2331_;
goto v_reusejp_2329_;
}
v_reusejp_2329_:
{
v_a_1823_ = v___x_2330_;
goto v___jp_1822_;
}
}
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2335_; uint8_t v_isShared_2336_; uint8_t v_isSharedCheck_2340_; 
lean_del_object(v___x_2313_);
lean_del_object(v___x_2307_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_2333_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2340_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2340_ == 0)
{
v___x_2335_ = v___x_2325_;
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
else
{
lean_inc(v_a_2333_);
lean_dec(v___x_2325_);
v___x_2335_ = lean_box(0);
v_isShared_2336_ = v_isSharedCheck_2340_;
goto v_resetjp_2334_;
}
v_resetjp_2334_:
{
lean_object* v___x_2338_; 
if (v_isShared_2336_ == 0)
{
v___x_2338_ = v___x_2335_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v_a_2333_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_del_object(v___x_2313_);
lean_del_object(v___x_2307_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2341_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___x_2323_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___x_2323_);
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
lean_object* v_a_2349_; lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2356_; 
lean_dec(v_a_2319_);
lean_del_object(v___x_2313_);
lean_del_object(v___x_2307_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2349_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2356_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2356_ == 0)
{
v___x_2351_ = v___x_2320_;
v_isShared_2352_ = v_isSharedCheck_2356_;
goto v_resetjp_2350_;
}
else
{
lean_inc(v_a_2349_);
lean_dec(v___x_2320_);
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
}
else
{
lean_object* v_a_2357_; lean_object* v___x_2359_; uint8_t v_isShared_2360_; uint8_t v_isSharedCheck_2364_; 
lean_del_object(v___x_2313_);
lean_dec(v_fst_2310_);
lean_del_object(v___x_2307_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_2357_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2364_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2364_ == 0)
{
v___x_2359_ = v___x_2318_;
v_isShared_2360_ = v_isSharedCheck_2364_;
goto v_resetjp_2358_;
}
else
{
lean_inc(v_a_2357_);
lean_dec(v___x_2318_);
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
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_del_object(v___x_2313_);
lean_dec(v_fst_2310_);
lean_del_object(v___x_2307_);
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2365_ = lean_ctor_get(v___x_2315_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2315_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2315_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2315_);
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
}
}
else
{
lean_dec(v_a_2304_);
v___y_2211_ = v___y_2257_;
v___y_2212_ = v___y_2258_;
v___y_2213_ = v___y_2259_;
v___y_2214_ = v___y_2260_;
goto v___jp_2210_;
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2375_ = lean_ctor_get(v___x_2303_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2303_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2303_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2303_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec_ref(v___x_1954_);
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_2383_ = lean_ctor_get(v___x_2261_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2261_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2261_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2261_);
v___x_2385_ = lean_box(0);
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
v_resetjp_2384_:
{
lean_object* v___x_2388_; 
if (v_isShared_2386_ == 0)
{
v___x_2388_ = v___x_2385_;
goto v_reusejp_2387_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_a_2383_);
v___x_2388_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2387_;
}
v_reusejp_2387_:
{
return v___x_2388_;
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
v_a_1831_ = v___x_1882_;
goto v___jp_1830_;
}
v___jp_1842_:
{
lean_object* v___x_1847_; 
lean_inc(v_mvarId_1806_);
v___x_1847_ = l_Lean_MVarId_getType(v_mvarId_1806_, v___y_1843_, v___y_1846_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1847_) == 0)
{
lean_object* v_a_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v_a_1848_ = lean_ctor_get(v___x_1847_, 0);
lean_inc(v_a_1848_);
lean_dec_ref_known(v___x_1847_, 1);
v___x_1849_ = l_Lean_LocalDecl_toExpr(v_val_1837_);
v___x_1850_ = l_Lean_Meta_mkNoConfusion(v_a_1848_, v___x_1849_, v___y_1843_, v___y_1846_, v___y_1844_, v___y_1845_);
if (lean_obj_tag(v___x_1850_) == 0)
{
lean_object* v_a_1851_; lean_object* v___x_1852_; 
v_a_1851_ = lean_ctor_get(v___x_1850_, 0);
lean_inc(v_a_1851_);
lean_dec_ref_known(v___x_1850_, 1);
v___x_1852_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1806_, v_a_1851_, v___y_1846_);
if (lean_obj_tag(v___x_1852_) == 0)
{
lean_object* v___x_1853_; lean_object* v___x_1855_; 
lean_dec_ref_known(v___x_1852_, 1);
v___x_1853_ = lean_box(v___x_1816_);
if (v_isShared_1840_ == 0)
{
lean_ctor_set(v___x_1839_, 0, v___x_1853_);
v___x_1855_ = v___x_1839_;
goto v_reusejp_1854_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1853_);
v___x_1855_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1854_;
}
v_reusejp_1854_:
{
lean_object* v___x_1856_; 
v___x_1856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1855_);
lean_ctor_set(v___x_1856_, 1, v___x_1841_);
v_a_1823_ = v___x_1856_;
goto v___jp_1822_;
}
}
else
{
lean_object* v_a_1858_; lean_object* v___x_1860_; uint8_t v_isShared_1861_; uint8_t v_isSharedCheck_1865_; 
lean_del_object(v___x_1839_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_1858_ = lean_ctor_get(v___x_1852_, 0);
v_isSharedCheck_1865_ = !lean_is_exclusive(v___x_1852_);
if (v_isSharedCheck_1865_ == 0)
{
v___x_1860_ = v___x_1852_;
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
else
{
lean_inc(v_a_1858_);
lean_dec(v___x_1852_);
v___x_1860_ = lean_box(0);
v_isShared_1861_ = v_isSharedCheck_1865_;
goto v_resetjp_1859_;
}
v_resetjp_1859_:
{
lean_object* v___x_1863_; 
if (v_isShared_1861_ == 0)
{
v___x_1863_ = v___x_1860_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v_a_1858_);
v___x_1863_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
return v___x_1863_;
}
}
}
}
else
{
lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_del_object(v___x_1839_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_1866_ = lean_ctor_get(v___x_1850_, 0);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1850_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1850_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_dec(v___x_1850_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
else
{
lean_object* v_a_1874_; lean_object* v___x_1876_; uint8_t v_isShared_1877_; uint8_t v_isSharedCheck_1881_; 
lean_del_object(v___x_1839_);
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
v_a_1874_ = lean_ctor_get(v___x_1847_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1847_);
if (v_isSharedCheck_1881_ == 0)
{
v___x_1876_ = v___x_1847_;
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
else
{
lean_inc(v_a_1874_);
lean_dec(v___x_1847_);
v___x_1876_ = lean_box(0);
v_isShared_1877_ = v_isSharedCheck_1881_;
goto v_resetjp_1875_;
}
v_resetjp_1875_:
{
lean_object* v___x_1879_; 
if (v_isShared_1877_ == 0)
{
v___x_1879_ = v___x_1876_;
goto v_reusejp_1878_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_a_1874_);
v___x_1879_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1878_;
}
v_reusejp_1878_:
{
return v___x_1879_;
}
}
}
}
v___jp_1883_:
{
lean_object* v_searchFuel_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v_searchFuel_1888_ = lean_ctor_get(v_config_1805_, 0);
v___x_1889_ = l_Lean_LocalDecl_fvarId(v_val_1837_);
lean_dec(v_val_1837_);
lean_inc(v_searchFuel_1888_);
lean_inc(v_mvarId_1806_);
v___x_1890_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1806_, v___x_1889_, v_searchFuel_1888_, v___y_1886_, v___y_1885_, v___y_1887_, v___y_1884_);
if (lean_obj_tag(v___x_1890_) == 0)
{
lean_object* v_a_1891_; uint8_t v___x_1892_; 
v_a_1891_ = lean_ctor_get(v___x_1890_, 0);
lean_inc(v_a_1891_);
lean_dec_ref_known(v___x_1890_, 1);
v___x_1892_ = lean_unbox(v_a_1891_);
lean_dec(v_a_1891_);
if (v___x_1892_ == 0)
{
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_1831_ = v___x_1882_;
goto v___jp_1830_;
}
else
{
lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; 
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v___x_1893_ = lean_box(v___x_1816_);
v___x_1894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1894_, 0, v___x_1893_);
v___x_1895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1895_, 0, v___x_1894_);
lean_ctor_set(v___x_1895_, 1, v___x_1841_);
v_a_1823_ = v___x_1895_;
goto v___jp_1822_;
}
}
else
{
lean_object* v_a_1896_; lean_object* v___x_1898_; uint8_t v_isShared_1899_; uint8_t v_isSharedCheck_1903_; 
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_1896_ = lean_ctor_get(v___x_1890_, 0);
v_isSharedCheck_1903_ = !lean_is_exclusive(v___x_1890_);
if (v_isSharedCheck_1903_ == 0)
{
v___x_1898_ = v___x_1890_;
v_isShared_1899_ = v_isSharedCheck_1903_;
goto v_resetjp_1897_;
}
else
{
lean_inc(v_a_1896_);
lean_dec(v___x_1890_);
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
v___jp_1904_:
{
if (v___y_1909_ == 0)
{
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
v_a_1831_ = v___x_1882_;
goto v___jp_1830_;
}
else
{
v___y_1884_ = v___y_1905_;
v___y_1885_ = v___y_1906_;
v___y_1886_ = v___y_1907_;
v___y_1887_ = v___y_1908_;
goto v___jp_1883_;
}
}
v___jp_1911_:
{
if (v___y_1915_ == 0)
{
v___y_1884_ = v___y_1912_;
v___y_1885_ = v___y_1913_;
v___y_1886_ = v___y_1914_;
v___y_1887_ = v___y_1916_;
goto v___jp_1883_;
}
else
{
v___y_1905_ = v___y_1912_;
v___y_1906_ = v___y_1913_;
v___y_1907_ = v___y_1914_;
v___y_1908_ = v___y_1916_;
v___y_1909_ = v___x_1910_;
goto v___jp_1904_;
}
}
v___jp_1917_:
{
if (v___y_1923_ == 0)
{
v___y_1905_ = v___y_1918_;
v___y_1906_ = v___y_1919_;
v___y_1907_ = v___y_1920_;
v___y_1908_ = v___y_1922_;
v___y_1909_ = v___x_1910_;
goto v___jp_1904_;
}
else
{
v___y_1912_ = v___y_1918_;
v___y_1913_ = v___y_1919_;
v___y_1914_ = v___y_1920_;
v___y_1915_ = v___y_1921_;
v___y_1916_ = v___y_1922_;
goto v___jp_1911_;
}
}
v___jp_1924_:
{
uint8_t v_emptyType_1931_; 
v_emptyType_1931_ = lean_ctor_get_uint8(v_config_1805_, sizeof(void*)*1 + 1);
if (v_emptyType_1931_ == 0)
{
v___y_1918_ = v___y_1930_;
v___y_1919_ = v___y_1928_;
v___y_1920_ = v___y_1927_;
v___y_1921_ = v___y_1926_;
v___y_1922_ = v___y_1929_;
v___y_1923_ = v___x_1910_;
goto v___jp_1917_;
}
else
{
if (v___y_1925_ == 0)
{
v___y_1912_ = v___y_1930_;
v___y_1913_ = v___y_1928_;
v___y_1914_ = v___y_1927_;
v___y_1915_ = v___y_1926_;
v___y_1916_ = v___y_1929_;
goto v___jp_1911_;
}
else
{
v___y_1918_ = v___y_1930_;
v___y_1919_ = v___y_1928_;
v___y_1920_ = v___y_1927_;
v___y_1921_ = v___y_1926_;
v___y_1922_ = v___y_1929_;
v___y_1923_ = v___x_1910_;
goto v___jp_1917_;
}
}
}
v___jp_1932_:
{
if (v___y_1939_ == 0)
{
v___y_1925_ = v___y_1935_;
v___y_1926_ = v___y_1937_;
v___y_1927_ = v___y_1938_;
v___y_1928_ = v___y_1933_;
v___y_1929_ = v___y_1934_;
v___y_1930_ = v___y_1936_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1940_; 
lean_inc(v_val_1837_);
lean_inc(v_mvarId_1806_);
v___x_1940_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1806_, v_val_1837_, v___y_1938_, v___y_1933_, v___y_1934_, v___y_1936_);
if (lean_obj_tag(v___x_1940_) == 0)
{
lean_object* v_a_1941_; uint8_t v___x_1942_; 
v_a_1941_ = lean_ctor_get(v___x_1940_, 0);
lean_inc(v_a_1941_);
lean_dec_ref_known(v___x_1940_, 1);
v___x_1942_ = lean_unbox(v_a_1941_);
lean_dec(v_a_1941_);
if (v___x_1942_ == 0)
{
v___y_1925_ = v___y_1935_;
v___y_1926_ = v___y_1937_;
v___y_1927_ = v___y_1938_;
v___y_1928_ = v___y_1933_;
v___y_1929_ = v___y_1934_;
v___y_1930_ = v___y_1936_;
goto v___jp_1924_;
}
else
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
lean_dec(v_val_1837_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v___x_1943_ = lean_box(v___x_1816_);
v___x_1944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1944_, 0, v___x_1943_);
v___x_1945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1945_, 0, v___x_1944_);
lean_ctor_set(v___x_1945_, 1, v___x_1841_);
v_a_1823_ = v___x_1945_;
goto v___jp_1822_;
}
}
else
{
lean_object* v_a_1946_; lean_object* v___x_1948_; uint8_t v_isShared_1949_; uint8_t v_isSharedCheck_1953_; 
lean_dec(v_val_1837_);
lean_del_object(v___x_1820_);
lean_dec(v_snd_1818_);
lean_dec(v_mvarId_1806_);
lean_dec_ref(v_config_1805_);
v_a_1946_ = lean_ctor_get(v___x_1940_, 0);
v_isSharedCheck_1953_ = !lean_is_exclusive(v___x_1940_);
if (v_isSharedCheck_1953_ == 0)
{
v___x_1948_ = v___x_1940_;
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
else
{
lean_inc(v_a_1946_);
lean_dec(v___x_1940_);
v___x_1948_ = lean_box(0);
v_isShared_1949_ = v_isSharedCheck_1953_;
goto v_resetjp_1947_;
}
v_resetjp_1947_:
{
lean_object* v___x_1951_; 
if (v_isShared_1949_ == 0)
{
v___x_1951_ = v___x_1948_;
goto v_reusejp_1950_;
}
else
{
lean_object* v_reuseFailAlloc_1952_; 
v_reuseFailAlloc_1952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1952_, 0, v_a_1946_);
v___x_1951_ = v_reuseFailAlloc_1952_;
goto v_reusejp_1950_;
}
v_reusejp_1950_:
{
return v___x_1951_;
}
}
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2457_, lean_object* v_mvarId_2458_, lean_object* v_as_2459_, lean_object* v_sz_2460_, lean_object* v_i_2461_, lean_object* v_b_2462_, lean_object* v___y_2463_, lean_object* v___y_2464_, lean_object* v___y_2465_, lean_object* v___y_2466_, lean_object* v___y_2467_){
_start:
{
size_t v_sz_boxed_2468_; size_t v_i_boxed_2469_; lean_object* v_res_2470_; 
v_sz_boxed_2468_ = lean_unbox_usize(v_sz_2460_);
lean_dec(v_sz_2460_);
v_i_boxed_2469_ = lean_unbox_usize(v_i_2461_);
lean_dec(v_i_2461_);
v_res_2470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2457_, v_mvarId_2458_, v_as_2459_, v_sz_boxed_2468_, v_i_boxed_2469_, v_b_2462_, v___y_2463_, v___y_2464_, v___y_2465_, v___y_2466_);
lean_dec(v___y_2466_);
lean_dec_ref(v___y_2465_);
lean_dec(v___y_2464_);
lean_dec_ref(v___y_2463_);
lean_dec_ref(v_as_2459_);
return v_res_2470_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2471_, lean_object* v_mvarId_2472_, lean_object* v_as_2473_, size_t v_sz_2474_, size_t v_i_2475_, lean_object* v_b_2476_, lean_object* v___y_2477_, lean_object* v___y_2478_, lean_object* v___y_2479_, lean_object* v___y_2480_){
_start:
{
uint8_t v___x_2482_; 
v___x_2482_ = lean_usize_dec_lt(v_i_2475_, v_sz_2474_);
if (v___x_2482_ == 0)
{
lean_object* v___x_2483_; 
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v___x_2483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2483_, 0, v_b_2476_);
return v___x_2483_;
}
else
{
lean_object* v_snd_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_3121_; 
v_snd_2484_ = lean_ctor_get(v_b_2476_, 1);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_b_2476_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; 
v_unused_3122_ = lean_ctor_get(v_b_2476_, 0);
lean_dec(v_unused_3122_);
v___x_2486_ = v_b_2476_;
v_isShared_2487_ = v_isSharedCheck_3121_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_snd_2484_);
lean_dec(v_b_2476_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_3121_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v_a_2489_; lean_object* v___x_2495_; lean_object* v_a_2497_; lean_object* v_a_2502_; 
v___x_2495_ = lean_box(0);
v_a_2502_ = lean_array_uget(v_as_2473_, v_i_2475_);
if (lean_obj_tag(v_a_2502_) == 0)
{
lean_del_object(v___x_2486_);
v_a_2497_ = v_snd_2484_;
goto v___jp_2496_;
}
else
{
lean_object* v_val_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_3120_; 
v_val_2503_ = lean_ctor_get(v_a_2502_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_a_2502_);
if (v_isSharedCheck_3120_ == 0)
{
v___x_2505_ = v_a_2502_;
v_isShared_2506_ = v_isSharedCheck_3120_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_val_2503_);
lean_dec(v_a_2502_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_3120_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v___x_2507_; lean_object* v___y_2509_; lean_object* v___y_2510_; lean_object* v___y_2511_; lean_object* v___y_2512_; lean_object* v___x_2548_; lean_object* v___y_2550_; lean_object* v___y_2551_; lean_object* v___y_2552_; lean_object* v___y_2553_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2574_; uint8_t v___y_2575_; uint8_t v___x_2576_; lean_object* v___y_2578_; lean_object* v___y_2579_; uint8_t v___y_2580_; lean_object* v___y_2581_; lean_object* v___y_2582_; lean_object* v___y_2584_; lean_object* v___y_2585_; uint8_t v___y_2586_; lean_object* v___y_2587_; lean_object* v___y_2588_; uint8_t v___y_2589_; uint8_t v___y_2591_; uint8_t v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; lean_object* v___y_2595_; lean_object* v___y_2596_; lean_object* v___y_2599_; lean_object* v___y_2600_; uint8_t v___y_2601_; uint8_t v___y_2602_; lean_object* v___y_2603_; lean_object* v___y_2604_; uint8_t v___y_2605_; 
v___x_2507_ = lean_box(0);
v___x_2548_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2576_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2503_);
if (v___x_2576_ == 0)
{
lean_object* v___x_2620_; uint8_t v___y_2622_; uint8_t v___y_2623_; lean_object* v___y_2624_; lean_object* v___y_2625_; lean_object* v___y_2626_; lean_object* v___y_2627_; lean_object* v___y_2631_; uint8_t v___y_2632_; uint8_t v___y_2633_; lean_object* v___y_2634_; lean_object* v___y_2635_; lean_object* v___y_2636_; lean_object* v___y_2637_; uint8_t v___y_2638_; lean_object* v___y_2641_; lean_object* v___y_2642_; uint8_t v___y_2643_; uint8_t v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v_a_2647_; lean_object* v___y_2651_; uint8_t v___y_2652_; uint8_t v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; lean_object* v___y_2656_; lean_object* v___y_2711_; uint8_t v___y_2712_; uint8_t v___y_2713_; lean_object* v___y_2714_; lean_object* v___y_2715_; lean_object* v___y_2716_; uint8_t v___y_2717_; lean_object* v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2721_; uint8_t v___y_2722_; uint8_t v___y_2723_; lean_object* v___y_2724_; lean_object* v___y_2725_; uint8_t v___y_2726_; lean_object* v___y_2729_; lean_object* v___y_2730_; uint8_t v___y_2731_; uint8_t v___y_2732_; lean_object* v___y_2733_; lean_object* v___y_2734_; uint8_t v___y_2735_; lean_object* v___y_2748_; uint8_t v___y_2749_; uint8_t v___y_2750_; lean_object* v___y_2751_; lean_object* v___y_2752_; lean_object* v___y_2753_; uint8_t v___y_2754_; uint8_t v___y_2756_; uint8_t v_isHEq_2757_; lean_object* v___y_2758_; lean_object* v___y_2759_; lean_object* v___y_2760_; lean_object* v___y_2761_; lean_object* v___y_2765_; lean_object* v___y_2766_; uint8_t v___y_2767_; lean_object* v___y_2768_; lean_object* v___y_2769_; lean_object* v___y_2770_; lean_object* v___y_2771_; uint8_t v_isEq_2827_; lean_object* v___y_2828_; lean_object* v___y_2829_; lean_object* v___y_2830_; lean_object* v___y_2831_; lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2923_; lean_object* v___y_2924_; lean_object* v___y_2925_; lean_object* v___y_2926_; lean_object* v___x_3057_; 
v___x_2620_ = l_Lean_LocalDecl_type(v_val_2503_);
lean_inc_ref(v___x_2620_);
v___x_3057_ = l_Lean_Meta_matchNot_x3f(v___x_2620_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_3057_) == 0)
{
lean_object* v_a_3058_; 
v_a_3058_ = lean_ctor_get(v___x_3057_, 0);
lean_inc(v_a_3058_);
lean_dec_ref_known(v___x_3057_, 1);
if (lean_obj_tag(v_a_3058_) == 1)
{
lean_object* v_val_3059_; lean_object* v___x_3060_; 
v_val_3059_ = lean_ctor_get(v_a_3058_, 0);
lean_inc(v_val_3059_);
lean_dec_ref_known(v_a_3058_, 1);
v___x_3060_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3059_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_3060_) == 0)
{
lean_object* v_a_3061_; 
v_a_3061_ = lean_ctor_get(v___x_3060_, 0);
lean_inc(v_a_3061_);
lean_dec_ref_known(v___x_3060_, 1);
if (lean_obj_tag(v_a_3061_) == 1)
{
lean_object* v_val_3062_; lean_object* v___x_3064_; uint8_t v_isShared_3065_; uint8_t v_isSharedCheck_3103_; 
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec_ref(v_config_2471_);
v_val_3062_ = lean_ctor_get(v_a_3061_, 0);
v_isSharedCheck_3103_ = !lean_is_exclusive(v_a_3061_);
if (v_isSharedCheck_3103_ == 0)
{
v___x_3064_ = v_a_3061_;
v_isShared_3065_ = v_isSharedCheck_3103_;
goto v_resetjp_3063_;
}
else
{
lean_inc(v_val_3062_);
lean_dec(v_a_3061_);
v___x_3064_ = lean_box(0);
v_isShared_3065_ = v_isSharedCheck_3103_;
goto v_resetjp_3063_;
}
v_resetjp_3063_:
{
lean_object* v___x_3066_; 
lean_inc(v_mvarId_2472_);
v___x_3066_ = l_Lean_MVarId_getType(v_mvarId_2472_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_3066_) == 0)
{
lean_object* v_a_3067_; lean_object* v___x_3068_; lean_object* v___x_3069_; lean_object* v___x_3070_; lean_object* v___x_3071_; 
v_a_3067_ = lean_ctor_get(v___x_3066_, 0);
lean_inc(v_a_3067_);
lean_dec_ref_known(v___x_3066_, 1);
v___x_3068_ = l_Lean_LocalDecl_toExpr(v_val_2503_);
v___x_3069_ = l_Lean_mkFVar(v_val_3062_);
v___x_3070_ = l_Lean_Expr_app___override(v___x_3068_, v___x_3069_);
v___x_3071_ = l_Lean_Meta_mkFalseElim(v_a_3067_, v___x_3070_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
if (lean_obj_tag(v___x_3071_) == 0)
{
lean_object* v_a_3072_; lean_object* v___x_3073_; 
v_a_3072_ = lean_ctor_get(v___x_3071_, 0);
lean_inc(v_a_3072_);
lean_dec_ref_known(v___x_3071_, 1);
v___x_3073_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2472_, v_a_3072_, v___y_2478_);
if (lean_obj_tag(v___x_3073_) == 0)
{
lean_object* v___x_3074_; lean_object* v___x_3076_; 
lean_dec_ref_known(v___x_3073_, 1);
v___x_3074_ = lean_box(v___x_2482_);
if (v_isShared_3065_ == 0)
{
lean_ctor_set(v___x_3064_, 0, v___x_3074_);
v___x_3076_ = v___x_3064_;
goto v_reusejp_3075_;
}
else
{
lean_object* v_reuseFailAlloc_3078_; 
v_reuseFailAlloc_3078_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3074_);
v___x_3076_ = v_reuseFailAlloc_3078_;
goto v_reusejp_3075_;
}
v_reusejp_3075_:
{
lean_object* v___x_3077_; 
v___x_3077_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3077_, 0, v___x_3076_);
lean_ctor_set(v___x_3077_, 1, v___x_2507_);
v_a_2489_ = v___x_3077_;
goto v___jp_2488_;
}
}
else
{
lean_object* v_a_3079_; lean_object* v___x_3081_; uint8_t v_isShared_3082_; uint8_t v_isSharedCheck_3086_; 
lean_del_object(v___x_3064_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
v_a_3079_ = lean_ctor_get(v___x_3073_, 0);
v_isSharedCheck_3086_ = !lean_is_exclusive(v___x_3073_);
if (v_isSharedCheck_3086_ == 0)
{
v___x_3081_ = v___x_3073_;
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
else
{
lean_inc(v_a_3079_);
lean_dec(v___x_3073_);
v___x_3081_ = lean_box(0);
v_isShared_3082_ = v_isSharedCheck_3086_;
goto v_resetjp_3080_;
}
v_resetjp_3080_:
{
lean_object* v___x_3084_; 
if (v_isShared_3082_ == 0)
{
v___x_3084_ = v___x_3081_;
goto v_reusejp_3083_;
}
else
{
lean_object* v_reuseFailAlloc_3085_; 
v_reuseFailAlloc_3085_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3085_, 0, v_a_3079_);
v___x_3084_ = v_reuseFailAlloc_3085_;
goto v_reusejp_3083_;
}
v_reusejp_3083_:
{
return v___x_3084_;
}
}
}
}
else
{
lean_object* v_a_3087_; lean_object* v___x_3089_; uint8_t v_isShared_3090_; uint8_t v_isSharedCheck_3094_; 
lean_del_object(v___x_3064_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_3087_ = lean_ctor_get(v___x_3071_, 0);
v_isSharedCheck_3094_ = !lean_is_exclusive(v___x_3071_);
if (v_isSharedCheck_3094_ == 0)
{
v___x_3089_ = v___x_3071_;
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
else
{
lean_inc(v_a_3087_);
lean_dec(v___x_3071_);
v___x_3089_ = lean_box(0);
v_isShared_3090_ = v_isSharedCheck_3094_;
goto v_resetjp_3088_;
}
v_resetjp_3088_:
{
lean_object* v___x_3092_; 
if (v_isShared_3090_ == 0)
{
v___x_3092_ = v___x_3089_;
goto v_reusejp_3091_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v_a_3087_);
v___x_3092_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3091_;
}
v_reusejp_3091_:
{
return v___x_3092_;
}
}
}
}
else
{
lean_object* v_a_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3102_; 
lean_del_object(v___x_3064_);
lean_dec(v_val_3062_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_3095_ = lean_ctor_get(v___x_3066_, 0);
v_isSharedCheck_3102_ = !lean_is_exclusive(v___x_3066_);
if (v_isSharedCheck_3102_ == 0)
{
v___x_3097_ = v___x_3066_;
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_a_3095_);
lean_dec(v___x_3066_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3102_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3100_; 
if (v_isShared_3098_ == 0)
{
v___x_3100_ = v___x_3097_;
goto v_reusejp_3099_;
}
else
{
lean_object* v_reuseFailAlloc_3101_; 
v_reuseFailAlloc_3101_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3101_, 0, v_a_3095_);
v___x_3100_ = v_reuseFailAlloc_3101_;
goto v_reusejp_3099_;
}
v_reusejp_3099_:
{
return v___x_3100_;
}
}
}
}
}
else
{
lean_dec(v_a_3061_);
v___y_2923_ = v___y_2477_;
v___y_2924_ = v___y_2478_;
v___y_2925_ = v___y_2479_;
v___y_2926_ = v___y_2480_;
goto v___jp_2922_;
}
}
else
{
lean_object* v_a_3104_; lean_object* v___x_3106_; uint8_t v_isShared_3107_; uint8_t v_isSharedCheck_3111_; 
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_3104_ = lean_ctor_get(v___x_3060_, 0);
v_isSharedCheck_3111_ = !lean_is_exclusive(v___x_3060_);
if (v_isSharedCheck_3111_ == 0)
{
v___x_3106_ = v___x_3060_;
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
else
{
lean_inc(v_a_3104_);
lean_dec(v___x_3060_);
v___x_3106_ = lean_box(0);
v_isShared_3107_ = v_isSharedCheck_3111_;
goto v_resetjp_3105_;
}
v_resetjp_3105_:
{
lean_object* v___x_3109_; 
if (v_isShared_3107_ == 0)
{
v___x_3109_ = v___x_3106_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v_a_3104_);
v___x_3109_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
return v___x_3109_;
}
}
}
}
else
{
lean_dec(v_a_3058_);
v___y_2923_ = v___y_2477_;
v___y_2924_ = v___y_2478_;
v___y_2925_ = v___y_2479_;
v___y_2926_ = v___y_2480_;
goto v___jp_2922_;
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_3112_ = lean_ctor_get(v___x_3057_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3057_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3057_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3057_);
v___x_3114_ = lean_box(0);
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
v_resetjp_3113_:
{
lean_object* v___x_3117_; 
if (v_isShared_3115_ == 0)
{
v___x_3117_ = v___x_3114_;
goto v_reusejp_3116_;
}
else
{
lean_object* v_reuseFailAlloc_3118_; 
v_reuseFailAlloc_3118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3118_, 0, v_a_3112_);
v___x_3117_ = v_reuseFailAlloc_3118_;
goto v_reusejp_3116_;
}
v_reusejp_3116_:
{
return v___x_3117_;
}
}
}
v___jp_2621_:
{
uint8_t v_genDiseq_2628_; 
v_genDiseq_2628_ = lean_ctor_get_uint8(v_config_2471_, sizeof(void*)*1 + 2);
if (v_genDiseq_2628_ == 0)
{
lean_dec_ref(v___x_2620_);
v___y_2599_ = v___y_2627_;
v___y_2600_ = v___y_2626_;
v___y_2601_ = v___y_2623_;
v___y_2602_ = v___y_2622_;
v___y_2603_ = v___y_2625_;
v___y_2604_ = v___y_2624_;
v___y_2605_ = v___x_2576_;
goto v___jp_2598_;
}
else
{
uint8_t v___x_2629_; 
v___x_2629_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2620_);
v___y_2599_ = v___y_2627_;
v___y_2600_ = v___y_2626_;
v___y_2601_ = v___y_2623_;
v___y_2602_ = v___y_2622_;
v___y_2603_ = v___y_2625_;
v___y_2604_ = v___y_2624_;
v___y_2605_ = v___x_2629_;
goto v___jp_2598_;
}
}
v___jp_2630_:
{
if (v___y_2638_ == 0)
{
lean_dec_ref(v___y_2636_);
v___y_2622_ = v___y_2633_;
v___y_2623_ = v___y_2632_;
v___y_2624_ = v___y_2635_;
v___y_2625_ = v___y_2637_;
v___y_2626_ = v___y_2631_;
v___y_2627_ = v___y_2634_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2639_; 
lean_dec_ref(v___x_2620_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v___x_2639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2639_, 0, v___y_2636_);
return v___x_2639_;
}
}
v___jp_2640_:
{
uint8_t v___x_2648_; 
v___x_2648_ = l_Lean_Exception_isInterrupt(v_a_2647_);
if (v___x_2648_ == 0)
{
uint8_t v___x_2649_; 
lean_inc_ref(v_a_2647_);
v___x_2649_ = l_Lean_Exception_isRuntime(v_a_2647_);
v___y_2631_ = v___y_2641_;
v___y_2632_ = v___y_2644_;
v___y_2633_ = v___y_2643_;
v___y_2634_ = v___y_2642_;
v___y_2635_ = v___y_2645_;
v___y_2636_ = v_a_2647_;
v___y_2637_ = v___y_2646_;
v___y_2638_ = v___x_2649_;
goto v___jp_2630_;
}
else
{
v___y_2631_ = v___y_2641_;
v___y_2632_ = v___y_2644_;
v___y_2633_ = v___y_2643_;
v___y_2634_ = v___y_2642_;
v___y_2635_ = v___y_2645_;
v___y_2636_ = v_a_2647_;
v___y_2637_ = v___y_2646_;
v___y_2638_ = v___x_2648_;
goto v___jp_2630_;
}
}
v___jp_2650_:
{
lean_object* v___x_2657_; 
lean_inc_ref(v___x_2620_);
v___x_2657_ = l_Lean_Meta_mkDecide(v___x_2620_, v___y_2655_, v___y_2656_, v___y_2651_, v___y_2654_);
if (lean_obj_tag(v___x_2657_) == 0)
{
lean_object* v_a_2658_; lean_object* v_keyedConfig_2659_; uint8_t v_trackZetaDelta_2660_; lean_object* v_zetaDeltaSet_2661_; lean_object* v_lctx_2662_; lean_object* v_localInstances_2663_; lean_object* v_defEqCtx_x3f_2664_; lean_object* v_synthPendingDepth_2665_; lean_object* v_customCanUnfoldPredicate_x3f_2666_; uint8_t v_univApprox_2667_; uint8_t v_inTypeClassResolution_2668_; uint8_t v_cacheInferType_2669_; uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; 
v_a_2658_ = lean_ctor_get(v___x_2657_, 0);
lean_inc_n(v_a_2658_, 2);
lean_dec_ref_known(v___x_2657_, 1);
v_keyedConfig_2659_ = lean_ctor_get(v___y_2655_, 0);
v_trackZetaDelta_2660_ = lean_ctor_get_uint8(v___y_2655_, sizeof(void*)*7);
v_zetaDeltaSet_2661_ = lean_ctor_get(v___y_2655_, 1);
v_lctx_2662_ = lean_ctor_get(v___y_2655_, 2);
v_localInstances_2663_ = lean_ctor_get(v___y_2655_, 3);
v_defEqCtx_x3f_2664_ = lean_ctor_get(v___y_2655_, 4);
v_synthPendingDepth_2665_ = lean_ctor_get(v___y_2655_, 5);
v_customCanUnfoldPredicate_x3f_2666_ = lean_ctor_get(v___y_2655_, 6);
v_univApprox_2667_ = lean_ctor_get_uint8(v___y_2655_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2668_ = lean_ctor_get_uint8(v___y_2655_, sizeof(void*)*7 + 2);
v_cacheInferType_2669_ = lean_ctor_get_uint8(v___y_2655_, sizeof(void*)*7 + 3);
v___x_2670_ = 1;
lean_inc_ref(v_keyedConfig_2659_);
v___x_2671_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2670_, v_keyedConfig_2659_);
lean_inc(v_customCanUnfoldPredicate_x3f_2666_);
lean_inc(v_synthPendingDepth_2665_);
lean_inc(v_defEqCtx_x3f_2664_);
lean_inc_ref(v_localInstances_2663_);
lean_inc_ref(v_lctx_2662_);
lean_inc(v_zetaDeltaSet_2661_);
v___x_2672_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2672_, 0, v___x_2671_);
lean_ctor_set(v___x_2672_, 1, v_zetaDeltaSet_2661_);
lean_ctor_set(v___x_2672_, 2, v_lctx_2662_);
lean_ctor_set(v___x_2672_, 3, v_localInstances_2663_);
lean_ctor_set(v___x_2672_, 4, v_defEqCtx_x3f_2664_);
lean_ctor_set(v___x_2672_, 5, v_synthPendingDepth_2665_);
lean_ctor_set(v___x_2672_, 6, v_customCanUnfoldPredicate_x3f_2666_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7, v_trackZetaDelta_2660_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7 + 1, v_univApprox_2667_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2668_);
lean_ctor_set_uint8(v___x_2672_, sizeof(void*)*7 + 3, v_cacheInferType_2669_);
lean_inc(v___y_2654_);
lean_inc_ref(v___y_2651_);
lean_inc(v___y_2656_);
v___x_2673_ = lean_whnf(v_a_2658_, v___x_2672_, v___y_2656_, v___y_2651_, v___y_2654_);
if (lean_obj_tag(v___x_2673_) == 0)
{
lean_object* v_a_2674_; lean_object* v___x_2675_; uint8_t v___x_2676_; 
v_a_2674_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2674_);
lean_dec_ref_known(v___x_2673_, 1);
v___x_2675_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2676_ = l_Lean_Expr_isConstOf(v_a_2674_, v___x_2675_);
lean_dec(v_a_2674_);
if (v___x_2676_ == 0)
{
lean_dec(v_a_2658_);
v___y_2622_ = v___y_2653_;
v___y_2623_ = v___y_2652_;
v___y_2624_ = v___y_2655_;
v___y_2625_ = v___y_2656_;
v___y_2626_ = v___y_2651_;
v___y_2627_ = v___y_2654_;
goto v___jp_2621_;
}
else
{
lean_object* v___x_2677_; 
lean_inc(v_a_2658_);
v___x_2677_ = l_Lean_Meta_mkEqRefl(v_a_2658_, v___y_2655_, v___y_2656_, v___y_2651_, v___y_2654_);
if (lean_obj_tag(v___x_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2679_; 
v_a_2678_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___x_2677_, 1);
lean_inc(v_mvarId_2472_);
v___x_2679_ = l_Lean_MVarId_getType(v_mvarId_2472_, v___y_2655_, v___y_2656_, v___y_2651_, v___y_2654_);
if (lean_obj_tag(v___x_2679_) == 0)
{
lean_object* v_a_2680_; lean_object* v_nargs_2681_; lean_object* v___x_2682_; lean_object* v_dummy_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; 
v_a_2680_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2680_);
lean_dec_ref_known(v___x_2679_, 1);
v_nargs_2681_ = l_Lean_Expr_getAppNumArgs(v_a_2658_);
v___x_2682_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2683_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_2681_);
v___x_2684_ = lean_mk_array(v_nargs_2681_, v_dummy_2683_);
v___x_2685_ = lean_unsigned_to_nat(1u);
v___x_2686_ = lean_nat_sub(v_nargs_2681_, v___x_2685_);
lean_dec(v_nargs_2681_);
v___x_2687_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2658_, v___x_2684_, v___x_2686_);
v___x_2688_ = lean_array_push(v___x_2687_, v_a_2678_);
v___x_2689_ = l_Lean_mkAppN(v___x_2682_, v___x_2688_);
lean_dec_ref(v___x_2688_);
lean_inc(v_val_2503_);
v___x_2690_ = l_Lean_LocalDecl_toExpr(v_val_2503_);
v___x_2691_ = l_Lean_Meta_mkAbsurd(v_a_2680_, v___x_2690_, v___x_2689_, v___y_2655_, v___y_2656_, v___y_2651_, v___y_2654_);
if (lean_obj_tag(v___x_2691_) == 0)
{
lean_object* v_a_2692_; lean_object* v___x_2693_; 
v_a_2692_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2692_);
lean_dec_ref_known(v___x_2691_, 1);
lean_inc(v_mvarId_2472_);
v___x_2693_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2472_, v_a_2692_, v___y_2656_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v___x_2695_; uint8_t v_isShared_2696_; uint8_t v_isSharedCheck_2702_; 
lean_dec_ref(v___x_2620_);
lean_dec(v_val_2503_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_isSharedCheck_2702_ = !lean_is_exclusive(v___x_2693_);
if (v_isSharedCheck_2702_ == 0)
{
lean_object* v_unused_2703_; 
v_unused_2703_ = lean_ctor_get(v___x_2693_, 0);
lean_dec(v_unused_2703_);
v___x_2695_ = v___x_2693_;
v_isShared_2696_ = v_isSharedCheck_2702_;
goto v_resetjp_2694_;
}
else
{
lean_dec(v___x_2693_);
v___x_2695_ = lean_box(0);
v_isShared_2696_ = v_isSharedCheck_2702_;
goto v_resetjp_2694_;
}
v_resetjp_2694_:
{
lean_object* v___x_2697_; lean_object* v___x_2699_; 
v___x_2697_ = lean_box(v___x_2482_);
if (v_isShared_2696_ == 0)
{
lean_ctor_set_tag(v___x_2695_, 1);
lean_ctor_set(v___x_2695_, 0, v___x_2697_);
v___x_2699_ = v___x_2695_;
goto v_reusejp_2698_;
}
else
{
lean_object* v_reuseFailAlloc_2701_; 
v_reuseFailAlloc_2701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2701_, 0, v___x_2697_);
v___x_2699_ = v_reuseFailAlloc_2701_;
goto v_reusejp_2698_;
}
v_reusejp_2698_:
{
lean_object* v___x_2700_; 
v___x_2700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2700_, 0, v___x_2699_);
lean_ctor_set(v___x_2700_, 1, v___x_2507_);
v_a_2489_ = v___x_2700_;
goto v___jp_2488_;
}
}
}
else
{
lean_object* v_a_2704_; 
v_a_2704_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2704_);
lean_dec_ref_known(v___x_2693_, 1);
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2654_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2652_;
v___y_2645_ = v___y_2655_;
v___y_2646_ = v___y_2656_;
v_a_2647_ = v_a_2704_;
goto v___jp_2640_;
}
}
else
{
lean_object* v_a_2705_; 
v_a_2705_ = lean_ctor_get(v___x_2691_, 0);
lean_inc(v_a_2705_);
lean_dec_ref_known(v___x_2691_, 1);
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2654_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2652_;
v___y_2645_ = v___y_2655_;
v___y_2646_ = v___y_2656_;
v_a_2647_ = v_a_2705_;
goto v___jp_2640_;
}
}
else
{
lean_object* v_a_2706_; 
lean_dec(v_a_2678_);
lean_dec(v_a_2658_);
v_a_2706_ = lean_ctor_get(v___x_2679_, 0);
lean_inc(v_a_2706_);
lean_dec_ref_known(v___x_2679_, 1);
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2654_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2652_;
v___y_2645_ = v___y_2655_;
v___y_2646_ = v___y_2656_;
v_a_2647_ = v_a_2706_;
goto v___jp_2640_;
}
}
else
{
lean_object* v_a_2707_; 
lean_dec(v_a_2658_);
v_a_2707_ = lean_ctor_get(v___x_2677_, 0);
lean_inc(v_a_2707_);
lean_dec_ref_known(v___x_2677_, 1);
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2654_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2652_;
v___y_2645_ = v___y_2655_;
v___y_2646_ = v___y_2656_;
v_a_2647_ = v_a_2707_;
goto v___jp_2640_;
}
}
}
else
{
lean_object* v_a_2708_; 
lean_dec(v_a_2658_);
v_a_2708_ = lean_ctor_get(v___x_2673_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2673_, 1);
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2654_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2652_;
v___y_2645_ = v___y_2655_;
v___y_2646_ = v___y_2656_;
v_a_2647_ = v_a_2708_;
goto v___jp_2640_;
}
}
else
{
lean_object* v_a_2709_; 
v_a_2709_ = lean_ctor_get(v___x_2657_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2657_, 1);
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2654_;
v___y_2643_ = v___y_2653_;
v___y_2644_ = v___y_2652_;
v___y_2645_ = v___y_2655_;
v___y_2646_ = v___y_2656_;
v_a_2647_ = v_a_2709_;
goto v___jp_2640_;
}
}
v___jp_2710_:
{
if (v___y_2717_ == 0)
{
v___y_2622_ = v___y_2713_;
v___y_2623_ = v___y_2712_;
v___y_2624_ = v___y_2715_;
v___y_2625_ = v___y_2716_;
v___y_2626_ = v___y_2711_;
v___y_2627_ = v___y_2714_;
goto v___jp_2621_;
}
else
{
v___y_2651_ = v___y_2711_;
v___y_2652_ = v___y_2712_;
v___y_2653_ = v___y_2713_;
v___y_2654_ = v___y_2714_;
v___y_2655_ = v___y_2715_;
v___y_2656_ = v___y_2716_;
goto v___jp_2650_;
}
}
v___jp_2718_:
{
if (v___y_2726_ == 0)
{
lean_dec_ref(v___y_2720_);
v___y_2711_ = v___y_2719_;
v___y_2712_ = v___y_2723_;
v___y_2713_ = v___y_2722_;
v___y_2714_ = v___y_2721_;
v___y_2715_ = v___y_2724_;
v___y_2716_ = v___y_2725_;
v___y_2717_ = v___x_2576_;
goto v___jp_2710_;
}
else
{
uint8_t v___x_2727_; 
v___x_2727_ = l_Lean_Expr_hasFVar(v___y_2720_);
lean_dec_ref(v___y_2720_);
if (v___x_2727_ == 0)
{
v___y_2651_ = v___y_2719_;
v___y_2652_ = v___y_2723_;
v___y_2653_ = v___y_2722_;
v___y_2654_ = v___y_2721_;
v___y_2655_ = v___y_2724_;
v___y_2656_ = v___y_2725_;
goto v___jp_2650_;
}
else
{
v___y_2711_ = v___y_2719_;
v___y_2712_ = v___y_2723_;
v___y_2713_ = v___y_2722_;
v___y_2714_ = v___y_2721_;
v___y_2715_ = v___y_2724_;
v___y_2716_ = v___y_2725_;
v___y_2717_ = v___x_2576_;
goto v___jp_2710_;
}
}
}
v___jp_2728_:
{
lean_object* v___x_2736_; 
lean_inc_ref(v___x_2620_);
v___x_2736_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2620_, v___y_2734_);
if (lean_obj_tag(v___x_2736_) == 0)
{
lean_object* v_a_2737_; uint8_t v___x_2738_; 
v_a_2737_ = lean_ctor_get(v___x_2736_, 0);
lean_inc(v_a_2737_);
lean_dec_ref_known(v___x_2736_, 1);
v___x_2738_ = l_Lean_Expr_hasMVar(v_a_2737_);
if (v___x_2738_ == 0)
{
v___y_2719_ = v___y_2729_;
v___y_2720_ = v_a_2737_;
v___y_2721_ = v___y_2730_;
v___y_2722_ = v___y_2731_;
v___y_2723_ = v___y_2732_;
v___y_2724_ = v___y_2733_;
v___y_2725_ = v___y_2734_;
v___y_2726_ = v___y_2735_;
goto v___jp_2718_;
}
else
{
v___y_2719_ = v___y_2729_;
v___y_2720_ = v_a_2737_;
v___y_2721_ = v___y_2730_;
v___y_2722_ = v___y_2731_;
v___y_2723_ = v___y_2732_;
v___y_2724_ = v___y_2733_;
v___y_2725_ = v___y_2734_;
v___y_2726_ = v___x_2576_;
goto v___jp_2718_;
}
}
else
{
lean_object* v_a_2739_; lean_object* v___x_2741_; uint8_t v_isShared_2742_; uint8_t v_isSharedCheck_2746_; 
lean_dec_ref(v___x_2620_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_2739_ = lean_ctor_get(v___x_2736_, 0);
v_isSharedCheck_2746_ = !lean_is_exclusive(v___x_2736_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2741_ = v___x_2736_;
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
else
{
lean_inc(v_a_2739_);
lean_dec(v___x_2736_);
v___x_2741_ = lean_box(0);
v_isShared_2742_ = v_isSharedCheck_2746_;
goto v_resetjp_2740_;
}
v_resetjp_2740_:
{
lean_object* v___x_2744_; 
if (v_isShared_2742_ == 0)
{
v___x_2744_ = v___x_2741_;
goto v_reusejp_2743_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_a_2739_);
v___x_2744_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2743_;
}
v_reusejp_2743_:
{
return v___x_2744_;
}
}
}
}
v___jp_2747_:
{
if (v___y_2754_ == 0)
{
v___y_2622_ = v___y_2750_;
v___y_2623_ = v___y_2749_;
v___y_2624_ = v___y_2752_;
v___y_2625_ = v___y_2753_;
v___y_2626_ = v___y_2748_;
v___y_2627_ = v___y_2751_;
goto v___jp_2621_;
}
else
{
v___y_2729_ = v___y_2748_;
v___y_2730_ = v___y_2751_;
v___y_2731_ = v___y_2750_;
v___y_2732_ = v___y_2749_;
v___y_2733_ = v___y_2752_;
v___y_2734_ = v___y_2753_;
v___y_2735_ = v___y_2754_;
goto v___jp_2728_;
}
}
v___jp_2755_:
{
uint8_t v_useDecide_2762_; 
v_useDecide_2762_ = lean_ctor_get_uint8(v_config_2471_, sizeof(void*)*1);
if (v_useDecide_2762_ == 0)
{
v___y_2748_ = v___y_2760_;
v___y_2749_ = v_isHEq_2757_;
v___y_2750_ = v___y_2756_;
v___y_2751_ = v___y_2761_;
v___y_2752_ = v___y_2758_;
v___y_2753_ = v___y_2759_;
v___y_2754_ = v___x_2576_;
goto v___jp_2747_;
}
else
{
uint8_t v___x_2763_; 
v___x_2763_ = l_Lean_Expr_hasFVar(v___x_2620_);
if (v___x_2763_ == 0)
{
v___y_2729_ = v___y_2760_;
v___y_2730_ = v___y_2761_;
v___y_2731_ = v___y_2756_;
v___y_2732_ = v_isHEq_2757_;
v___y_2733_ = v___y_2758_;
v___y_2734_ = v___y_2759_;
v___y_2735_ = v_useDecide_2762_;
goto v___jp_2728_;
}
else
{
v___y_2748_ = v___y_2760_;
v___y_2749_ = v_isHEq_2757_;
v___y_2750_ = v___y_2756_;
v___y_2751_ = v___y_2761_;
v___y_2752_ = v___y_2758_;
v___y_2753_ = v___y_2759_;
v___y_2754_ = v___x_2576_;
goto v___jp_2747_;
}
}
}
v___jp_2764_:
{
lean_object* v___x_2772_; 
v___x_2772_ = l_Lean_Meta_isExprDefEq(v___y_2771_, v___y_2769_, v___y_2768_, v___y_2765_, v___y_2766_, v___y_2770_);
if (lean_obj_tag(v___x_2772_) == 0)
{
lean_object* v_a_2773_; uint8_t v___x_2774_; 
v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
lean_inc(v_a_2773_);
lean_dec_ref_known(v___x_2772_, 1);
v___x_2774_ = lean_unbox(v_a_2773_);
lean_dec(v_a_2773_);
if (v___x_2774_ == 0)
{
v___y_2756_ = v___y_2767_;
v_isHEq_2757_ = v___x_2482_;
v___y_2758_ = v___y_2768_;
v___y_2759_ = v___y_2765_;
v___y_2760_ = v___y_2766_;
v___y_2761_ = v___y_2770_;
goto v___jp_2755_;
}
else
{
lean_object* v___x_2775_; 
lean_dec_ref(v___x_2620_);
lean_dec_ref(v_config_2471_);
lean_inc(v_mvarId_2472_);
v___x_2775_ = l_Lean_MVarId_getType(v_mvarId_2472_, v___y_2768_, v___y_2765_, v___y_2766_, v___y_2770_);
if (lean_obj_tag(v___x_2775_) == 0)
{
lean_object* v_a_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; 
v_a_2776_ = lean_ctor_get(v___x_2775_, 0);
lean_inc(v_a_2776_);
lean_dec_ref_known(v___x_2775_, 1);
v___x_2777_ = l_Lean_LocalDecl_toExpr(v_val_2503_);
v___x_2778_ = l_Lean_Meta_mkEqOfHEq(v___x_2777_, v___x_2482_, v___y_2768_, v___y_2765_, v___y_2766_, v___y_2770_);
if (lean_obj_tag(v___x_2778_) == 0)
{
lean_object* v_a_2779_; lean_object* v___x_2780_; 
v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
lean_inc(v_a_2779_);
lean_dec_ref_known(v___x_2778_, 1);
v___x_2780_ = l_Lean_Meta_mkNoConfusion(v_a_2776_, v_a_2779_, v___y_2768_, v___y_2765_, v___y_2766_, v___y_2770_);
if (lean_obj_tag(v___x_2780_) == 0)
{
lean_object* v_a_2781_; lean_object* v___x_2782_; 
v_a_2781_ = lean_ctor_get(v___x_2780_, 0);
lean_inc(v_a_2781_);
lean_dec_ref_known(v___x_2780_, 1);
v___x_2782_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2472_, v_a_2781_, v___y_2765_);
if (lean_obj_tag(v___x_2782_) == 0)
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
lean_dec_ref_known(v___x_2782_, 1);
v___x_2783_ = lean_box(v___x_2482_);
v___x_2784_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2783_);
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v___x_2784_);
lean_ctor_set(v___x_2785_, 1, v___x_2507_);
v_a_2489_ = v___x_2785_;
goto v___jp_2488_;
}
else
{
lean_object* v_a_2786_; lean_object* v___x_2788_; uint8_t v_isShared_2789_; uint8_t v_isSharedCheck_2793_; 
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
v_a_2786_ = lean_ctor_get(v___x_2782_, 0);
v_isSharedCheck_2793_ = !lean_is_exclusive(v___x_2782_);
if (v_isSharedCheck_2793_ == 0)
{
v___x_2788_ = v___x_2782_;
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
else
{
lean_inc(v_a_2786_);
lean_dec(v___x_2782_);
v___x_2788_ = lean_box(0);
v_isShared_2789_ = v_isSharedCheck_2793_;
goto v_resetjp_2787_;
}
v_resetjp_2787_:
{
lean_object* v___x_2791_; 
if (v_isShared_2789_ == 0)
{
v___x_2791_ = v___x_2788_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2792_; 
v_reuseFailAlloc_2792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2792_, 0, v_a_2786_);
v___x_2791_ = v_reuseFailAlloc_2792_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
return v___x_2791_;
}
}
}
}
else
{
lean_object* v_a_2794_; lean_object* v___x_2796_; uint8_t v_isShared_2797_; uint8_t v_isSharedCheck_2801_; 
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_2794_ = lean_ctor_get(v___x_2780_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2780_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2796_ = v___x_2780_;
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
else
{
lean_inc(v_a_2794_);
lean_dec(v___x_2780_);
v___x_2796_ = lean_box(0);
v_isShared_2797_ = v_isSharedCheck_2801_;
goto v_resetjp_2795_;
}
v_resetjp_2795_:
{
lean_object* v___x_2799_; 
if (v_isShared_2797_ == 0)
{
v___x_2799_ = v___x_2796_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_a_2794_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
else
{
lean_object* v_a_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2809_; 
lean_dec(v_a_2776_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_2802_ = lean_ctor_get(v___x_2778_, 0);
v_isSharedCheck_2809_ = !lean_is_exclusive(v___x_2778_);
if (v_isSharedCheck_2809_ == 0)
{
v___x_2804_ = v___x_2778_;
v_isShared_2805_ = v_isSharedCheck_2809_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_a_2802_);
lean_dec(v___x_2778_);
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
else
{
lean_object* v_a_2810_; lean_object* v___x_2812_; uint8_t v_isShared_2813_; uint8_t v_isSharedCheck_2817_; 
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_2810_ = lean_ctor_get(v___x_2775_, 0);
v_isSharedCheck_2817_ = !lean_is_exclusive(v___x_2775_);
if (v_isSharedCheck_2817_ == 0)
{
v___x_2812_ = v___x_2775_;
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
else
{
lean_inc(v_a_2810_);
lean_dec(v___x_2775_);
v___x_2812_ = lean_box(0);
v_isShared_2813_ = v_isSharedCheck_2817_;
goto v_resetjp_2811_;
}
v_resetjp_2811_:
{
lean_object* v___x_2815_; 
if (v_isShared_2813_ == 0)
{
v___x_2815_ = v___x_2812_;
goto v_reusejp_2814_;
}
else
{
lean_object* v_reuseFailAlloc_2816_; 
v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
v___x_2815_ = v_reuseFailAlloc_2816_;
goto v_reusejp_2814_;
}
v_reusejp_2814_:
{
return v___x_2815_;
}
}
}
}
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec_ref(v___x_2620_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_2818_ = lean_ctor_get(v___x_2772_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2772_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2772_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2772_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
v___jp_2826_:
{
lean_object* v___x_2832_; 
lean_inc_ref(v___x_2620_);
v___x_2832_ = l_Lean_Meta_matchHEq_x3f(v___x_2620_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2832_) == 0)
{
lean_object* v_a_2833_; 
v_a_2833_ = lean_ctor_get(v___x_2832_, 0);
lean_inc(v_a_2833_);
lean_dec_ref_known(v___x_2832_, 1);
if (lean_obj_tag(v_a_2833_) == 1)
{
lean_object* v_val_2834_; lean_object* v_snd_2835_; lean_object* v_snd_2836_; lean_object* v_fst_2837_; lean_object* v_fst_2838_; lean_object* v_fst_2839_; lean_object* v_snd_2840_; lean_object* v___x_2841_; 
v_val_2834_ = lean_ctor_get(v_a_2833_, 0);
lean_inc(v_val_2834_);
lean_dec_ref_known(v_a_2833_, 1);
v_snd_2835_ = lean_ctor_get(v_val_2834_, 1);
lean_inc(v_snd_2835_);
v_snd_2836_ = lean_ctor_get(v_snd_2835_, 1);
lean_inc(v_snd_2836_);
v_fst_2837_ = lean_ctor_get(v_val_2834_, 0);
lean_inc(v_fst_2837_);
lean_dec(v_val_2834_);
v_fst_2838_ = lean_ctor_get(v_snd_2835_, 0);
lean_inc(v_fst_2838_);
lean_dec(v_snd_2835_);
v_fst_2839_ = lean_ctor_get(v_snd_2836_, 0);
lean_inc(v_fst_2839_);
v_snd_2840_ = lean_ctor_get(v_snd_2836_, 1);
lean_inc(v_snd_2840_);
lean_dec(v_snd_2836_);
v___x_2841_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2838_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2841_) == 0)
{
lean_object* v_a_2842_; 
v_a_2842_ = lean_ctor_get(v___x_2841_, 0);
lean_inc(v_a_2842_);
lean_dec_ref_known(v___x_2841_, 1);
if (lean_obj_tag(v_a_2842_) == 1)
{
lean_object* v_val_2843_; lean_object* v___x_2844_; 
v_val_2843_ = lean_ctor_get(v_a_2842_, 0);
lean_inc(v_val_2843_);
lean_dec_ref_known(v_a_2842_, 1);
v___x_2844_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2840_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
if (lean_obj_tag(v_a_2845_) == 1)
{
lean_object* v_toConstantVal_2846_; lean_object* v_val_2847_; lean_object* v_toConstantVal_2848_; lean_object* v_name_2849_; lean_object* v_name_2850_; uint8_t v___x_2851_; 
v_toConstantVal_2846_ = lean_ctor_get(v_val_2843_, 0);
lean_inc_ref(v_toConstantVal_2846_);
lean_dec(v_val_2843_);
v_val_2847_ = lean_ctor_get(v_a_2845_, 0);
lean_inc(v_val_2847_);
lean_dec_ref_known(v_a_2845_, 1);
v_toConstantVal_2848_ = lean_ctor_get(v_val_2847_, 0);
lean_inc_ref(v_toConstantVal_2848_);
lean_dec(v_val_2847_);
v_name_2849_ = lean_ctor_get(v_toConstantVal_2846_, 0);
lean_inc(v_name_2849_);
lean_dec_ref(v_toConstantVal_2846_);
v_name_2850_ = lean_ctor_get(v_toConstantVal_2848_, 0);
lean_inc(v_name_2850_);
lean_dec_ref(v_toConstantVal_2848_);
v___x_2851_ = lean_name_eq(v_name_2849_, v_name_2850_);
lean_dec(v_name_2850_);
lean_dec(v_name_2849_);
if (v___x_2851_ == 0)
{
v___y_2765_ = v___y_2829_;
v___y_2766_ = v___y_2830_;
v___y_2767_ = v_isEq_2827_;
v___y_2768_ = v___y_2828_;
v___y_2769_ = v_fst_2839_;
v___y_2770_ = v___y_2831_;
v___y_2771_ = v_fst_2837_;
goto v___jp_2764_;
}
else
{
if (v___x_2576_ == 0)
{
lean_dec(v_fst_2839_);
lean_dec(v_fst_2837_);
v___y_2756_ = v_isEq_2827_;
v_isHEq_2757_ = v___x_2482_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
v___y_2760_ = v___y_2830_;
v___y_2761_ = v___y_2831_;
goto v___jp_2755_;
}
else
{
v___y_2765_ = v___y_2829_;
v___y_2766_ = v___y_2830_;
v___y_2767_ = v_isEq_2827_;
v___y_2768_ = v___y_2828_;
v___y_2769_ = v_fst_2839_;
v___y_2770_ = v___y_2831_;
v___y_2771_ = v_fst_2837_;
goto v___jp_2764_;
}
}
}
else
{
lean_dec(v_a_2845_);
lean_dec(v_val_2843_);
lean_dec(v_fst_2839_);
lean_dec(v_fst_2837_);
v___y_2756_ = v_isEq_2827_;
v_isHEq_2757_ = v___x_2482_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
v___y_2760_ = v___y_2830_;
v___y_2761_ = v___y_2831_;
goto v___jp_2755_;
}
}
else
{
lean_object* v_a_2852_; lean_object* v___x_2854_; uint8_t v_isShared_2855_; uint8_t v_isSharedCheck_2859_; 
lean_dec(v_val_2843_);
lean_dec(v_fst_2839_);
lean_dec(v_fst_2837_);
lean_dec_ref(v___x_2620_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_2852_ = lean_ctor_get(v___x_2844_, 0);
v_isSharedCheck_2859_ = !lean_is_exclusive(v___x_2844_);
if (v_isSharedCheck_2859_ == 0)
{
v___x_2854_ = v___x_2844_;
v_isShared_2855_ = v_isSharedCheck_2859_;
goto v_resetjp_2853_;
}
else
{
lean_inc(v_a_2852_);
lean_dec(v___x_2844_);
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
lean_dec(v_a_2842_);
lean_dec(v_snd_2840_);
lean_dec(v_fst_2839_);
lean_dec(v_fst_2837_);
v___y_2756_ = v_isEq_2827_;
v_isHEq_2757_ = v___x_2482_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
v___y_2760_ = v___y_2830_;
v___y_2761_ = v___y_2831_;
goto v___jp_2755_;
}
}
else
{
lean_object* v_a_2860_; lean_object* v___x_2862_; uint8_t v_isShared_2863_; uint8_t v_isSharedCheck_2867_; 
lean_dec(v_snd_2840_);
lean_dec(v_fst_2839_);
lean_dec(v_fst_2837_);
lean_dec_ref(v___x_2620_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_2860_ = lean_ctor_get(v___x_2841_, 0);
v_isSharedCheck_2867_ = !lean_is_exclusive(v___x_2841_);
if (v_isSharedCheck_2867_ == 0)
{
v___x_2862_ = v___x_2841_;
v_isShared_2863_ = v_isSharedCheck_2867_;
goto v_resetjp_2861_;
}
else
{
lean_inc(v_a_2860_);
lean_dec(v___x_2841_);
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
lean_dec(v_a_2833_);
v___y_2756_ = v_isEq_2827_;
v_isHEq_2757_ = v___x_2576_;
v___y_2758_ = v___y_2828_;
v___y_2759_ = v___y_2829_;
v___y_2760_ = v___y_2830_;
v___y_2761_ = v___y_2831_;
goto v___jp_2755_;
}
}
else
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2875_; 
lean_dec_ref(v___x_2620_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_2868_ = lean_ctor_get(v___x_2832_, 0);
v_isSharedCheck_2875_ = !lean_is_exclusive(v___x_2832_);
if (v_isSharedCheck_2875_ == 0)
{
v___x_2870_ = v___x_2832_;
v_isShared_2871_ = v_isSharedCheck_2875_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2832_);
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
v___jp_2876_:
{
lean_object* v___x_2881_; 
lean_inc_ref(v___x_2620_);
v___x_2881_ = l_Lean_Meta_matchEq_x3f(v___x_2620_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2881_) == 0)
{
lean_object* v_a_2882_; 
v_a_2882_ = lean_ctor_get(v___x_2881_, 0);
lean_inc(v_a_2882_);
lean_dec_ref_known(v___x_2881_, 1);
if (lean_obj_tag(v_a_2882_) == 1)
{
lean_object* v_val_2883_; lean_object* v_snd_2884_; lean_object* v_fst_2885_; lean_object* v_snd_2886_; lean_object* v___x_2887_; 
v_val_2883_ = lean_ctor_get(v_a_2882_, 0);
lean_inc(v_val_2883_);
lean_dec_ref_known(v_a_2882_, 1);
v_snd_2884_ = lean_ctor_get(v_val_2883_, 1);
lean_inc(v_snd_2884_);
lean_dec(v_val_2883_);
v_fst_2885_ = lean_ctor_get(v_snd_2884_, 0);
lean_inc(v_fst_2885_);
v_snd_2886_ = lean_ctor_get(v_snd_2884_, 1);
lean_inc(v_snd_2886_);
lean_dec(v_snd_2884_);
v___x_2887_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2885_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2887_) == 0)
{
lean_object* v_a_2888_; 
v_a_2888_ = lean_ctor_get(v___x_2887_, 0);
lean_inc(v_a_2888_);
lean_dec_ref_known(v___x_2887_, 1);
if (lean_obj_tag(v_a_2888_) == 1)
{
lean_object* v_val_2889_; lean_object* v___x_2890_; 
v_val_2889_ = lean_ctor_get(v_a_2888_, 0);
lean_inc(v_val_2889_);
lean_dec_ref_known(v_a_2888_, 1);
v___x_2890_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2886_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2880_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v_a_2891_; 
v_a_2891_ = lean_ctor_get(v___x_2890_, 0);
lean_inc(v_a_2891_);
lean_dec_ref_known(v___x_2890_, 1);
if (lean_obj_tag(v_a_2891_) == 1)
{
lean_object* v_toConstantVal_2892_; lean_object* v_val_2893_; lean_object* v_toConstantVal_2894_; lean_object* v_name_2895_; lean_object* v_name_2896_; uint8_t v___x_2897_; 
v_toConstantVal_2892_ = lean_ctor_get(v_val_2889_, 0);
lean_inc_ref(v_toConstantVal_2892_);
lean_dec(v_val_2889_);
v_val_2893_ = lean_ctor_get(v_a_2891_, 0);
lean_inc(v_val_2893_);
lean_dec_ref_known(v_a_2891_, 1);
v_toConstantVal_2894_ = lean_ctor_get(v_val_2893_, 0);
lean_inc_ref(v_toConstantVal_2894_);
lean_dec(v_val_2893_);
v_name_2895_ = lean_ctor_get(v_toConstantVal_2892_, 0);
lean_inc(v_name_2895_);
lean_dec_ref(v_toConstantVal_2892_);
v_name_2896_ = lean_ctor_get(v_toConstantVal_2894_, 0);
lean_inc(v_name_2896_);
lean_dec_ref(v_toConstantVal_2894_);
v___x_2897_ = lean_name_eq(v_name_2895_, v_name_2896_);
lean_dec(v_name_2896_);
lean_dec(v_name_2895_);
if (v___x_2897_ == 0)
{
lean_dec_ref(v___x_2620_);
lean_dec_ref(v_config_2471_);
v___y_2509_ = v___y_2879_;
v___y_2510_ = v___y_2878_;
v___y_2511_ = v___y_2880_;
v___y_2512_ = v___y_2877_;
goto v___jp_2508_;
}
else
{
if (v___x_2576_ == 0)
{
lean_del_object(v___x_2505_);
v_isEq_2827_ = v___x_2482_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v___y_2879_;
v___y_2831_ = v___y_2880_;
goto v___jp_2826_;
}
else
{
lean_dec_ref(v___x_2620_);
lean_dec_ref(v_config_2471_);
v___y_2509_ = v___y_2879_;
v___y_2510_ = v___y_2878_;
v___y_2511_ = v___y_2880_;
v___y_2512_ = v___y_2877_;
goto v___jp_2508_;
}
}
}
else
{
lean_dec(v_a_2891_);
lean_dec(v_val_2889_);
lean_del_object(v___x_2505_);
v_isEq_2827_ = v___x_2482_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v___y_2879_;
v___y_2831_ = v___y_2880_;
goto v___jp_2826_;
}
}
else
{
lean_object* v_a_2898_; lean_object* v___x_2900_; uint8_t v_isShared_2901_; uint8_t v_isSharedCheck_2905_; 
lean_dec(v_val_2889_);
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_2898_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2900_ = v___x_2890_;
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
else
{
lean_inc(v_a_2898_);
lean_dec(v___x_2890_);
v___x_2900_ = lean_box(0);
v_isShared_2901_ = v_isSharedCheck_2905_;
goto v_resetjp_2899_;
}
v_resetjp_2899_:
{
lean_object* v___x_2903_; 
if (v_isShared_2901_ == 0)
{
v___x_2903_ = v___x_2900_;
goto v_reusejp_2902_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_a_2898_);
v___x_2903_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2902_;
}
v_reusejp_2902_:
{
return v___x_2903_;
}
}
}
}
else
{
lean_dec(v_a_2888_);
lean_dec(v_snd_2886_);
lean_del_object(v___x_2505_);
v_isEq_2827_ = v___x_2482_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v___y_2879_;
v___y_2831_ = v___y_2880_;
goto v___jp_2826_;
}
}
else
{
lean_object* v_a_2906_; lean_object* v___x_2908_; uint8_t v_isShared_2909_; uint8_t v_isSharedCheck_2913_; 
lean_dec(v_snd_2886_);
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_2906_ = lean_ctor_get(v___x_2887_, 0);
v_isSharedCheck_2913_ = !lean_is_exclusive(v___x_2887_);
if (v_isSharedCheck_2913_ == 0)
{
v___x_2908_ = v___x_2887_;
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
else
{
lean_inc(v_a_2906_);
lean_dec(v___x_2887_);
v___x_2908_ = lean_box(0);
v_isShared_2909_ = v_isSharedCheck_2913_;
goto v_resetjp_2907_;
}
v_resetjp_2907_:
{
lean_object* v___x_2911_; 
if (v_isShared_2909_ == 0)
{
v___x_2911_ = v___x_2908_;
goto v_reusejp_2910_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_a_2906_);
v___x_2911_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2910_;
}
v_reusejp_2910_:
{
return v___x_2911_;
}
}
}
}
else
{
lean_dec(v_a_2882_);
lean_del_object(v___x_2505_);
v_isEq_2827_ = v___x_2576_;
v___y_2828_ = v___y_2877_;
v___y_2829_ = v___y_2878_;
v___y_2830_ = v___y_2879_;
v___y_2831_ = v___y_2880_;
goto v___jp_2826_;
}
}
else
{
lean_object* v_a_2914_; lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_2914_ = lean_ctor_get(v___x_2881_, 0);
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2881_);
if (v_isSharedCheck_2921_ == 0)
{
v___x_2916_ = v___x_2881_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_inc(v_a_2914_);
lean_dec(v___x_2881_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_a_2914_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
}
v___jp_2922_:
{
lean_object* v___x_2927_; 
lean_inc_ref(v___x_2620_);
v___x_2927_ = l_Lean_refutableHasNotBit_x3f(v___x_2620_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2927_) == 0)
{
lean_object* v_a_2928_; 
v_a_2928_ = lean_ctor_get(v___x_2927_, 0);
lean_inc(v_a_2928_);
lean_dec_ref_known(v___x_2927_, 1);
if (lean_obj_tag(v_a_2928_) == 1)
{
lean_object* v_val_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2968_; 
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec_ref(v_config_2471_);
v_val_2929_ = lean_ctor_get(v_a_2928_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v_a_2928_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2931_ = v_a_2928_;
v_isShared_2932_ = v_isSharedCheck_2968_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_val_2929_);
lean_dec(v_a_2928_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2968_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2933_; 
lean_inc(v_mvarId_2472_);
v___x_2933_ = l_Lean_MVarId_getType(v_mvarId_2472_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2933_) == 0)
{
lean_object* v_a_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
lean_inc(v_a_2934_);
lean_dec_ref_known(v___x_2933_, 1);
v___x_2935_ = l_Lean_LocalDecl_toExpr(v_val_2503_);
v___x_2936_ = l_Lean_Meta_mkAbsurd(v_a_2934_, v_val_2929_, v___x_2935_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2936_) == 0)
{
lean_object* v_a_2937_; lean_object* v___x_2938_; 
v_a_2937_ = lean_ctor_get(v___x_2936_, 0);
lean_inc(v_a_2937_);
lean_dec_ref_known(v___x_2936_, 1);
v___x_2938_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2472_, v_a_2937_, v___y_2924_);
if (lean_obj_tag(v___x_2938_) == 0)
{
lean_object* v___x_2939_; lean_object* v___x_2941_; 
lean_dec_ref_known(v___x_2938_, 1);
v___x_2939_ = lean_box(v___x_2482_);
if (v_isShared_2932_ == 0)
{
lean_ctor_set(v___x_2931_, 0, v___x_2939_);
v___x_2941_ = v___x_2931_;
goto v_reusejp_2940_;
}
else
{
lean_object* v_reuseFailAlloc_2943_; 
v_reuseFailAlloc_2943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2939_);
v___x_2941_ = v_reuseFailAlloc_2943_;
goto v_reusejp_2940_;
}
v_reusejp_2940_:
{
lean_object* v___x_2942_; 
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2507_);
v_a_2489_ = v___x_2942_;
goto v___jp_2488_;
}
}
else
{
lean_object* v_a_2944_; lean_object* v___x_2946_; uint8_t v_isShared_2947_; uint8_t v_isSharedCheck_2951_; 
lean_del_object(v___x_2931_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
v_a_2944_ = lean_ctor_get(v___x_2938_, 0);
v_isSharedCheck_2951_ = !lean_is_exclusive(v___x_2938_);
if (v_isSharedCheck_2951_ == 0)
{
v___x_2946_ = v___x_2938_;
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
else
{
lean_inc(v_a_2944_);
lean_dec(v___x_2938_);
v___x_2946_ = lean_box(0);
v_isShared_2947_ = v_isSharedCheck_2951_;
goto v_resetjp_2945_;
}
v_resetjp_2945_:
{
lean_object* v___x_2949_; 
if (v_isShared_2947_ == 0)
{
v___x_2949_ = v___x_2946_;
goto v_reusejp_2948_;
}
else
{
lean_object* v_reuseFailAlloc_2950_; 
v_reuseFailAlloc_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2950_, 0, v_a_2944_);
v___x_2949_ = v_reuseFailAlloc_2950_;
goto v_reusejp_2948_;
}
v_reusejp_2948_:
{
return v___x_2949_;
}
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_del_object(v___x_2931_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_2952_ = lean_ctor_get(v___x_2936_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2936_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2936_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2936_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
else
{
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_del_object(v___x_2931_);
lean_dec(v_val_2929_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_2960_ = lean_ctor_get(v___x_2933_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2933_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2933_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2933_);
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
}
else
{
lean_object* v___x_2969_; 
lean_dec(v_a_2928_);
lean_inc_ref(v___x_2620_);
v___x_2969_ = l_Lean_Meta_matchNe_x3f(v___x_2620_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
if (lean_obj_tag(v_a_2970_) == 1)
{
lean_object* v_val_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_3040_; 
v_val_2971_ = lean_ctor_get(v_a_2970_, 0);
v_isSharedCheck_3040_ = !lean_is_exclusive(v_a_2970_);
if (v_isSharedCheck_3040_ == 0)
{
v___x_2973_ = v_a_2970_;
v_isShared_2974_ = v_isSharedCheck_3040_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_val_2971_);
lean_dec(v_a_2970_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_3040_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v_snd_2975_; lean_object* v_fst_2976_; lean_object* v_snd_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3039_; 
v_snd_2975_ = lean_ctor_get(v_val_2971_, 1);
lean_inc(v_snd_2975_);
lean_dec(v_val_2971_);
v_fst_2976_ = lean_ctor_get(v_snd_2975_, 0);
v_snd_2977_ = lean_ctor_get(v_snd_2975_, 1);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_snd_2975_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_2979_ = v_snd_2975_;
v_isShared_2980_ = v_isSharedCheck_3039_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_snd_2977_);
lean_inc(v_fst_2976_);
lean_dec(v_snd_2975_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3039_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2981_; 
lean_inc(v_fst_2976_);
v___x_2981_ = l_Lean_Meta_isExprDefEq(v_fst_2976_, v_snd_2977_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2981_) == 0)
{
lean_object* v_a_2982_; uint8_t v___x_2983_; 
v_a_2982_ = lean_ctor_get(v___x_2981_, 0);
lean_inc(v_a_2982_);
lean_dec_ref_known(v___x_2981_, 1);
v___x_2983_ = lean_unbox(v_a_2982_);
lean_dec(v_a_2982_);
if (v___x_2983_ == 0)
{
lean_del_object(v___x_2979_);
lean_dec(v_fst_2976_);
lean_del_object(v___x_2973_);
v___y_2877_ = v___y_2923_;
v___y_2878_ = v___y_2924_;
v___y_2879_ = v___y_2925_;
v___y_2880_ = v___y_2926_;
goto v___jp_2876_;
}
else
{
lean_object* v___x_2984_; 
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec_ref(v_config_2471_);
lean_inc(v_mvarId_2472_);
v___x_2984_ = l_Lean_MVarId_getType(v_mvarId_2472_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2984_) == 0)
{
lean_object* v_a_2985_; lean_object* v___x_2986_; 
v_a_2985_ = lean_ctor_get(v___x_2984_, 0);
lean_inc(v_a_2985_);
lean_dec_ref_known(v___x_2984_, 1);
v___x_2986_ = l_Lean_Meta_mkEqRefl(v_fst_2976_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2986_) == 0)
{
lean_object* v_a_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; 
v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
lean_inc(v_a_2987_);
lean_dec_ref_known(v___x_2986_, 1);
v___x_2988_ = l_Lean_LocalDecl_toExpr(v_val_2503_);
v___x_2989_ = l_Lean_Meta_mkAbsurd(v_a_2985_, v_a_2987_, v___x_2988_, v___y_2923_, v___y_2924_, v___y_2925_, v___y_2926_);
if (lean_obj_tag(v___x_2989_) == 0)
{
lean_object* v_a_2990_; lean_object* v___x_2991_; 
v_a_2990_ = lean_ctor_get(v___x_2989_, 0);
lean_inc(v_a_2990_);
lean_dec_ref_known(v___x_2989_, 1);
v___x_2991_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2472_, v_a_2990_, v___y_2924_);
if (lean_obj_tag(v___x_2991_) == 0)
{
lean_object* v___x_2992_; lean_object* v___x_2994_; 
lean_dec_ref_known(v___x_2991_, 1);
v___x_2992_ = lean_box(v___x_2482_);
if (v_isShared_2974_ == 0)
{
lean_ctor_set(v___x_2973_, 0, v___x_2992_);
v___x_2994_ = v___x_2973_;
goto v_reusejp_2993_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v___x_2992_);
v___x_2994_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2993_;
}
v_reusejp_2993_:
{
lean_object* v___x_2996_; 
if (v_isShared_2980_ == 0)
{
lean_ctor_set(v___x_2979_, 1, v___x_2507_);
lean_ctor_set(v___x_2979_, 0, v___x_2994_);
v___x_2996_ = v___x_2979_;
goto v_reusejp_2995_;
}
else
{
lean_object* v_reuseFailAlloc_2997_; 
v_reuseFailAlloc_2997_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2997_, 0, v___x_2994_);
lean_ctor_set(v_reuseFailAlloc_2997_, 1, v___x_2507_);
v___x_2996_ = v_reuseFailAlloc_2997_;
goto v_reusejp_2995_;
}
v_reusejp_2995_:
{
v_a_2489_ = v___x_2996_;
goto v___jp_2488_;
}
}
}
else
{
lean_object* v_a_2999_; lean_object* v___x_3001_; uint8_t v_isShared_3002_; uint8_t v_isSharedCheck_3006_; 
lean_del_object(v___x_2979_);
lean_del_object(v___x_2973_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
v_a_2999_ = lean_ctor_get(v___x_2991_, 0);
v_isSharedCheck_3006_ = !lean_is_exclusive(v___x_2991_);
if (v_isSharedCheck_3006_ == 0)
{
v___x_3001_ = v___x_2991_;
v_isShared_3002_ = v_isSharedCheck_3006_;
goto v_resetjp_3000_;
}
else
{
lean_inc(v_a_2999_);
lean_dec(v___x_2991_);
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
}
else
{
lean_object* v_a_3007_; lean_object* v___x_3009_; uint8_t v_isShared_3010_; uint8_t v_isSharedCheck_3014_; 
lean_del_object(v___x_2979_);
lean_del_object(v___x_2973_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_3007_ = lean_ctor_get(v___x_2989_, 0);
v_isSharedCheck_3014_ = !lean_is_exclusive(v___x_2989_);
if (v_isSharedCheck_3014_ == 0)
{
v___x_3009_ = v___x_2989_;
v_isShared_3010_ = v_isSharedCheck_3014_;
goto v_resetjp_3008_;
}
else
{
lean_inc(v_a_3007_);
lean_dec(v___x_2989_);
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
else
{
lean_object* v_a_3015_; lean_object* v___x_3017_; uint8_t v_isShared_3018_; uint8_t v_isSharedCheck_3022_; 
lean_dec(v_a_2985_);
lean_del_object(v___x_2979_);
lean_del_object(v___x_2973_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_3015_ = lean_ctor_get(v___x_2986_, 0);
v_isSharedCheck_3022_ = !lean_is_exclusive(v___x_2986_);
if (v_isSharedCheck_3022_ == 0)
{
v___x_3017_ = v___x_2986_;
v_isShared_3018_ = v_isSharedCheck_3022_;
goto v_resetjp_3016_;
}
else
{
lean_inc(v_a_3015_);
lean_dec(v___x_2986_);
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
lean_object* v_a_3023_; lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3030_; 
lean_del_object(v___x_2979_);
lean_dec(v_fst_2976_);
lean_del_object(v___x_2973_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_3023_ = lean_ctor_get(v___x_2984_, 0);
v_isSharedCheck_3030_ = !lean_is_exclusive(v___x_2984_);
if (v_isSharedCheck_3030_ == 0)
{
v___x_3025_ = v___x_2984_;
v_isShared_3026_ = v_isSharedCheck_3030_;
goto v_resetjp_3024_;
}
else
{
lean_inc(v_a_3023_);
lean_dec(v___x_2984_);
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
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_del_object(v___x_2979_);
lean_dec(v_fst_2976_);
lean_del_object(v___x_2973_);
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_3031_ = lean_ctor_get(v___x_2981_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_2981_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_2981_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_2981_);
v___x_3033_ = lean_box(0);
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
v_resetjp_3032_:
{
lean_object* v___x_3036_; 
if (v_isShared_3034_ == 0)
{
v___x_3036_ = v___x_3033_;
goto v_reusejp_3035_;
}
else
{
lean_object* v_reuseFailAlloc_3037_; 
v_reuseFailAlloc_3037_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3037_, 0, v_a_3031_);
v___x_3036_ = v_reuseFailAlloc_3037_;
goto v_reusejp_3035_;
}
v_reusejp_3035_:
{
return v___x_3036_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2970_);
v___y_2877_ = v___y_2923_;
v___y_2878_ = v___y_2924_;
v___y_2879_ = v___y_2925_;
v___y_2880_ = v___y_2926_;
goto v___jp_2876_;
}
}
else
{
lean_object* v_a_3041_; lean_object* v___x_3043_; uint8_t v_isShared_3044_; uint8_t v_isSharedCheck_3048_; 
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_3041_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_3048_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_3048_ == 0)
{
v___x_3043_ = v___x_2969_;
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
else
{
lean_inc(v_a_3041_);
lean_dec(v___x_2969_);
v___x_3043_ = lean_box(0);
v_isShared_3044_ = v_isSharedCheck_3048_;
goto v_resetjp_3042_;
}
v_resetjp_3042_:
{
lean_object* v___x_3046_; 
if (v_isShared_3044_ == 0)
{
v___x_3046_ = v___x_3043_;
goto v_reusejp_3045_;
}
else
{
lean_object* v_reuseFailAlloc_3047_; 
v_reuseFailAlloc_3047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3047_, 0, v_a_3041_);
v___x_3046_ = v_reuseFailAlloc_3047_;
goto v_reusejp_3045_;
}
v_reusejp_3045_:
{
return v___x_3046_;
}
}
}
}
}
else
{
lean_object* v_a_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3056_; 
lean_dec_ref(v___x_2620_);
lean_del_object(v___x_2505_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_3049_ = lean_ctor_get(v___x_2927_, 0);
v_isSharedCheck_3056_ = !lean_is_exclusive(v___x_2927_);
if (v_isSharedCheck_3056_ == 0)
{
v___x_3051_ = v___x_2927_;
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_a_3049_);
lean_dec(v___x_2927_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3056_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
lean_object* v___x_3054_; 
if (v_isShared_3052_ == 0)
{
v___x_3054_ = v___x_3051_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3055_; 
v_reuseFailAlloc_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3055_, 0, v_a_3049_);
v___x_3054_ = v_reuseFailAlloc_3055_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
return v___x_3054_;
}
}
}
}
}
else
{
lean_del_object(v___x_2505_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
v_a_2497_ = v___x_2548_;
goto v___jp_2496_;
}
v___jp_2508_:
{
lean_object* v___x_2513_; 
lean_inc(v_mvarId_2472_);
v___x_2513_ = l_Lean_MVarId_getType(v_mvarId_2472_, v___y_2512_, v___y_2510_, v___y_2509_, v___y_2511_);
if (lean_obj_tag(v___x_2513_) == 0)
{
lean_object* v_a_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v_a_2514_ = lean_ctor_get(v___x_2513_, 0);
lean_inc(v_a_2514_);
lean_dec_ref_known(v___x_2513_, 1);
v___x_2515_ = l_Lean_LocalDecl_toExpr(v_val_2503_);
v___x_2516_ = l_Lean_Meta_mkNoConfusion(v_a_2514_, v___x_2515_, v___y_2512_, v___y_2510_, v___y_2509_, v___y_2511_);
if (lean_obj_tag(v___x_2516_) == 0)
{
lean_object* v_a_2517_; lean_object* v___x_2518_; 
v_a_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc(v_a_2517_);
lean_dec_ref_known(v___x_2516_, 1);
v___x_2518_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2472_, v_a_2517_, v___y_2510_);
if (lean_obj_tag(v___x_2518_) == 0)
{
lean_object* v___x_2519_; lean_object* v___x_2521_; 
lean_dec_ref_known(v___x_2518_, 1);
v___x_2519_ = lean_box(v___x_2482_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v___x_2519_);
v___x_2521_ = v___x_2505_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2523_; 
v_reuseFailAlloc_2523_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2523_, 0, v___x_2519_);
v___x_2521_ = v_reuseFailAlloc_2523_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
lean_object* v___x_2522_; 
v___x_2522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2522_, 0, v___x_2521_);
lean_ctor_set(v___x_2522_, 1, v___x_2507_);
v_a_2489_ = v___x_2522_;
goto v___jp_2488_;
}
}
else
{
lean_object* v_a_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2531_; 
lean_del_object(v___x_2505_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
v_a_2524_ = lean_ctor_get(v___x_2518_, 0);
v_isSharedCheck_2531_ = !lean_is_exclusive(v___x_2518_);
if (v_isSharedCheck_2531_ == 0)
{
v___x_2526_ = v___x_2518_;
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
else
{
lean_inc(v_a_2524_);
lean_dec(v___x_2518_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2531_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2529_; 
if (v_isShared_2527_ == 0)
{
v___x_2529_ = v___x_2526_;
goto v_reusejp_2528_;
}
else
{
lean_object* v_reuseFailAlloc_2530_; 
v_reuseFailAlloc_2530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2530_, 0, v_a_2524_);
v___x_2529_ = v_reuseFailAlloc_2530_;
goto v_reusejp_2528_;
}
v_reusejp_2528_:
{
return v___x_2529_;
}
}
}
}
else
{
lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2539_; 
lean_del_object(v___x_2505_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_2532_ = lean_ctor_get(v___x_2516_, 0);
v_isSharedCheck_2539_ = !lean_is_exclusive(v___x_2516_);
if (v_isSharedCheck_2539_ == 0)
{
v___x_2534_ = v___x_2516_;
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_dec(v___x_2516_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2539_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2537_; 
if (v_isShared_2535_ == 0)
{
v___x_2537_ = v___x_2534_;
goto v_reusejp_2536_;
}
else
{
lean_object* v_reuseFailAlloc_2538_; 
v_reuseFailAlloc_2538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2538_, 0, v_a_2532_);
v___x_2537_ = v_reuseFailAlloc_2538_;
goto v_reusejp_2536_;
}
v_reusejp_2536_:
{
return v___x_2537_;
}
}
}
}
else
{
lean_object* v_a_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2547_; 
lean_del_object(v___x_2505_);
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
v_a_2540_ = lean_ctor_get(v___x_2513_, 0);
v_isSharedCheck_2547_ = !lean_is_exclusive(v___x_2513_);
if (v_isSharedCheck_2547_ == 0)
{
v___x_2542_ = v___x_2513_;
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_a_2540_);
lean_dec(v___x_2513_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2547_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2545_; 
if (v_isShared_2543_ == 0)
{
v___x_2545_ = v___x_2542_;
goto v_reusejp_2544_;
}
else
{
lean_object* v_reuseFailAlloc_2546_; 
v_reuseFailAlloc_2546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2546_, 0, v_a_2540_);
v___x_2545_ = v_reuseFailAlloc_2546_;
goto v_reusejp_2544_;
}
v_reusejp_2544_:
{
return v___x_2545_;
}
}
}
}
v___jp_2549_:
{
lean_object* v_searchFuel_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_searchFuel_2554_ = lean_ctor_get(v_config_2471_, 0);
v___x_2555_ = l_Lean_LocalDecl_fvarId(v_val_2503_);
lean_dec(v_val_2503_);
lean_inc(v_searchFuel_2554_);
lean_inc(v_mvarId_2472_);
v___x_2556_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2472_, v___x_2555_, v_searchFuel_2554_, v___y_2551_, v___y_2550_, v___y_2553_, v___y_2552_);
if (lean_obj_tag(v___x_2556_) == 0)
{
lean_object* v_a_2557_; uint8_t v___x_2558_; 
v_a_2557_ = lean_ctor_get(v___x_2556_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v___x_2556_, 1);
v___x_2558_ = lean_unbox(v_a_2557_);
lean_dec(v_a_2557_);
if (v___x_2558_ == 0)
{
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
v_a_2497_ = v___x_2548_;
goto v___jp_2496_;
}
else
{
lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; 
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v___x_2559_ = lean_box(v___x_2482_);
v___x_2560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2559_);
v___x_2561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2561_, 0, v___x_2560_);
lean_ctor_set(v___x_2561_, 1, v___x_2507_);
v_a_2489_ = v___x_2561_;
goto v___jp_2488_;
}
}
else
{
lean_object* v_a_2562_; lean_object* v___x_2564_; uint8_t v_isShared_2565_; uint8_t v_isSharedCheck_2569_; 
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_2562_ = lean_ctor_get(v___x_2556_, 0);
v_isSharedCheck_2569_ = !lean_is_exclusive(v___x_2556_);
if (v_isSharedCheck_2569_ == 0)
{
v___x_2564_ = v___x_2556_;
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
else
{
lean_inc(v_a_2562_);
lean_dec(v___x_2556_);
v___x_2564_ = lean_box(0);
v_isShared_2565_ = v_isSharedCheck_2569_;
goto v_resetjp_2563_;
}
v_resetjp_2563_:
{
lean_object* v___x_2567_; 
if (v_isShared_2565_ == 0)
{
v___x_2567_ = v___x_2564_;
goto v_reusejp_2566_;
}
else
{
lean_object* v_reuseFailAlloc_2568_; 
v_reuseFailAlloc_2568_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2568_, 0, v_a_2562_);
v___x_2567_ = v_reuseFailAlloc_2568_;
goto v_reusejp_2566_;
}
v_reusejp_2566_:
{
return v___x_2567_;
}
}
}
}
v___jp_2570_:
{
if (v___y_2575_ == 0)
{
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
v_a_2497_ = v___x_2548_;
goto v___jp_2496_;
}
else
{
v___y_2550_ = v___y_2571_;
v___y_2551_ = v___y_2572_;
v___y_2552_ = v___y_2574_;
v___y_2553_ = v___y_2573_;
goto v___jp_2549_;
}
}
v___jp_2577_:
{
if (v___y_2580_ == 0)
{
v___y_2550_ = v___y_2578_;
v___y_2551_ = v___y_2579_;
v___y_2552_ = v___y_2582_;
v___y_2553_ = v___y_2581_;
goto v___jp_2549_;
}
else
{
v___y_2571_ = v___y_2578_;
v___y_2572_ = v___y_2579_;
v___y_2573_ = v___y_2581_;
v___y_2574_ = v___y_2582_;
v___y_2575_ = v___x_2576_;
goto v___jp_2570_;
}
}
v___jp_2583_:
{
if (v___y_2589_ == 0)
{
v___y_2571_ = v___y_2584_;
v___y_2572_ = v___y_2585_;
v___y_2573_ = v___y_2588_;
v___y_2574_ = v___y_2587_;
v___y_2575_ = v___x_2576_;
goto v___jp_2570_;
}
else
{
v___y_2578_ = v___y_2584_;
v___y_2579_ = v___y_2585_;
v___y_2580_ = v___y_2586_;
v___y_2581_ = v___y_2588_;
v___y_2582_ = v___y_2587_;
goto v___jp_2577_;
}
}
v___jp_2590_:
{
uint8_t v_emptyType_2597_; 
v_emptyType_2597_ = lean_ctor_get_uint8(v_config_2471_, sizeof(void*)*1 + 1);
if (v_emptyType_2597_ == 0)
{
v___y_2584_ = v___y_2594_;
v___y_2585_ = v___y_2593_;
v___y_2586_ = v___y_2592_;
v___y_2587_ = v___y_2596_;
v___y_2588_ = v___y_2595_;
v___y_2589_ = v___x_2576_;
goto v___jp_2583_;
}
else
{
if (v___y_2591_ == 0)
{
v___y_2578_ = v___y_2594_;
v___y_2579_ = v___y_2593_;
v___y_2580_ = v___y_2592_;
v___y_2581_ = v___y_2595_;
v___y_2582_ = v___y_2596_;
goto v___jp_2577_;
}
else
{
v___y_2584_ = v___y_2594_;
v___y_2585_ = v___y_2593_;
v___y_2586_ = v___y_2592_;
v___y_2587_ = v___y_2596_;
v___y_2588_ = v___y_2595_;
v___y_2589_ = v___x_2576_;
goto v___jp_2583_;
}
}
}
v___jp_2598_:
{
if (v___y_2605_ == 0)
{
v___y_2591_ = v___y_2602_;
v___y_2592_ = v___y_2601_;
v___y_2593_ = v___y_2604_;
v___y_2594_ = v___y_2603_;
v___y_2595_ = v___y_2600_;
v___y_2596_ = v___y_2599_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2606_; 
lean_inc(v_val_2503_);
lean_inc(v_mvarId_2472_);
v___x_2606_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2472_, v_val_2503_, v___y_2604_, v___y_2603_, v___y_2600_, v___y_2599_);
if (lean_obj_tag(v___x_2606_) == 0)
{
lean_object* v_a_2607_; uint8_t v___x_2608_; 
v_a_2607_ = lean_ctor_get(v___x_2606_, 0);
lean_inc(v_a_2607_);
lean_dec_ref_known(v___x_2606_, 1);
v___x_2608_ = lean_unbox(v_a_2607_);
lean_dec(v_a_2607_);
if (v___x_2608_ == 0)
{
v___y_2591_ = v___y_2602_;
v___y_2592_ = v___y_2601_;
v___y_2593_ = v___y_2604_;
v___y_2594_ = v___y_2603_;
v___y_2595_ = v___y_2600_;
v___y_2596_ = v___y_2599_;
goto v___jp_2590_;
}
else
{
lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
lean_dec(v_val_2503_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v___x_2609_ = lean_box(v___x_2482_);
v___x_2610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2507_);
v_a_2489_ = v___x_2611_;
goto v___jp_2488_;
}
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec(v_val_2503_);
lean_del_object(v___x_2486_);
lean_dec(v_snd_2484_);
lean_dec(v_mvarId_2472_);
lean_dec_ref(v_config_2471_);
v_a_2612_ = lean_ctor_get(v___x_2606_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2606_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2606_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2606_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
}
}
v___jp_2488_:
{
lean_object* v___x_2490_; lean_object* v___x_2492_; 
v___x_2490_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2490_, 0, v_a_2489_);
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2490_);
v___x_2492_ = v___x_2486_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2494_; 
v_reuseFailAlloc_2494_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2494_, 0, v___x_2490_);
lean_ctor_set(v_reuseFailAlloc_2494_, 1, v_snd_2484_);
v___x_2492_ = v_reuseFailAlloc_2494_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
lean_object* v___x_2493_; 
v___x_2493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2493_, 0, v___x_2492_);
return v___x_2493_;
}
}
v___jp_2496_:
{
lean_object* v___x_2498_; size_t v___x_2499_; size_t v___x_2500_; lean_object* v___x_2501_; 
v___x_2498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2498_, 0, v___x_2495_);
lean_ctor_set(v___x_2498_, 1, v_a_2497_);
v___x_2499_ = ((size_t)1ULL);
v___x_2500_ = lean_usize_add(v_i_2475_, v___x_2499_);
v___x_2501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2471_, v_mvarId_2472_, v_as_2473_, v_sz_2474_, v___x_2500_, v___x_2498_, v___y_2477_, v___y_2478_, v___y_2479_, v___y_2480_);
return v___x_2501_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3123_, lean_object* v_mvarId_3124_, lean_object* v_as_3125_, lean_object* v_sz_3126_, lean_object* v_i_3127_, lean_object* v_b_3128_, lean_object* v___y_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
size_t v_sz_boxed_3134_; size_t v_i_boxed_3135_; lean_object* v_res_3136_; 
v_sz_boxed_3134_ = lean_unbox_usize(v_sz_3126_);
lean_dec(v_sz_3126_);
v_i_boxed_3135_ = lean_unbox_usize(v_i_3127_);
lean_dec(v_i_3127_);
v_res_3136_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3123_, v_mvarId_3124_, v_as_3125_, v_sz_boxed_3134_, v_i_boxed_3135_, v_b_3128_, v___y_3129_, v___y_3130_, v___y_3131_, v___y_3132_);
lean_dec(v___y_3132_);
lean_dec_ref(v___y_3131_);
lean_dec(v___y_3130_);
lean_dec_ref(v___y_3129_);
lean_dec_ref(v_as_3125_);
return v_res_3136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3140_, lean_object* v_mvarId_3141_, lean_object* v_as_3142_, size_t v_sz_3143_, size_t v_i_3144_, lean_object* v_b_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
uint8_t v___x_3151_; 
v___x_3151_ = lean_usize_dec_lt(v_i_3144_, v_sz_3143_);
if (v___x_3151_ == 0)
{
lean_object* v___x_3152_; 
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v___x_3152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3152_, 0, v_b_3145_);
return v___x_3152_;
}
else
{
lean_object* v_snd_3153_; lean_object* v___x_3155_; uint8_t v_isShared_3156_; uint8_t v_isSharedCheck_3810_; 
v_snd_3153_ = lean_ctor_get(v_b_3145_, 1);
v_isSharedCheck_3810_ = !lean_is_exclusive(v_b_3145_);
if (v_isSharedCheck_3810_ == 0)
{
lean_object* v_unused_3811_; 
v_unused_3811_ = lean_ctor_get(v_b_3145_, 0);
lean_dec(v_unused_3811_);
v___x_3155_ = v_b_3145_;
v_isShared_3156_ = v_isSharedCheck_3810_;
goto v_resetjp_3154_;
}
else
{
lean_inc(v_snd_3153_);
lean_dec(v_b_3145_);
v___x_3155_ = lean_box(0);
v_isShared_3156_ = v_isSharedCheck_3810_;
goto v_resetjp_3154_;
}
v_resetjp_3154_:
{
lean_object* v_a_3158_; lean_object* v___x_3164_; lean_object* v_a_3166_; lean_object* v_a_3171_; 
v___x_3164_ = lean_box(0);
v_a_3171_ = lean_array_uget(v_as_3142_, v_i_3144_);
if (lean_obj_tag(v_a_3171_) == 0)
{
lean_del_object(v___x_3155_);
v_a_3166_ = v_snd_3153_;
goto v___jp_3165_;
}
else
{
lean_object* v_val_3172_; lean_object* v___x_3174_; uint8_t v_isShared_3175_; uint8_t v_isSharedCheck_3809_; 
v_val_3172_ = lean_ctor_get(v_a_3171_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v_a_3171_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3174_ = v_a_3171_;
v_isShared_3175_ = v_isSharedCheck_3809_;
goto v_resetjp_3173_;
}
else
{
lean_inc(v_val_3172_);
lean_dec(v_a_3171_);
v___x_3174_ = lean_box(0);
v_isShared_3175_ = v_isSharedCheck_3809_;
goto v_resetjp_3173_;
}
v_resetjp_3173_:
{
lean_object* v___x_3176_; lean_object* v___y_3178_; lean_object* v___y_3179_; lean_object* v___y_3180_; lean_object* v___y_3181_; lean_object* v___x_3218_; lean_object* v___y_3220_; lean_object* v___y_3221_; lean_object* v___y_3222_; lean_object* v___y_3223_; lean_object* v___y_3242_; lean_object* v___y_3243_; lean_object* v___y_3244_; lean_object* v___y_3245_; uint8_t v___y_3246_; uint8_t v___x_3247_; lean_object* v___y_3249_; lean_object* v___y_3250_; uint8_t v___y_3251_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3255_; lean_object* v___y_3256_; uint8_t v___y_3257_; lean_object* v___y_3258_; lean_object* v___y_3259_; uint8_t v___y_3260_; uint8_t v___y_3262_; uint8_t v___y_3263_; lean_object* v___y_3264_; lean_object* v___y_3265_; lean_object* v___y_3266_; lean_object* v___y_3267_; lean_object* v___y_3270_; uint8_t v___y_3271_; lean_object* v___y_3272_; lean_object* v___y_3273_; lean_object* v___y_3274_; uint8_t v___y_3275_; uint8_t v___y_3276_; 
v___x_3176_ = lean_box(0);
v___x_3218_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3247_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3172_);
if (v___x_3247_ == 0)
{
lean_object* v___x_3292_; uint8_t v___y_3294_; uint8_t v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3303_; uint8_t v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; uint8_t v___y_3308_; lean_object* v___y_3309_; uint8_t v___y_3310_; lean_object* v___y_3313_; uint8_t v___y_3314_; lean_object* v___y_3315_; lean_object* v___y_3316_; lean_object* v___y_3317_; uint8_t v___y_3318_; lean_object* v_a_3319_; lean_object* v___y_3323_; uint8_t v___y_3324_; lean_object* v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; uint8_t v___y_3328_; lean_object* v___y_3390_; uint8_t v___y_3391_; lean_object* v___y_3392_; lean_object* v___y_3393_; lean_object* v___y_3394_; uint8_t v___y_3395_; uint8_t v___y_3396_; lean_object* v___y_3398_; uint8_t v___y_3399_; lean_object* v___y_3400_; lean_object* v___y_3401_; lean_object* v___y_3402_; lean_object* v___y_3403_; uint8_t v___y_3404_; uint8_t v___y_3405_; lean_object* v___y_3408_; uint8_t v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; uint8_t v___y_3413_; uint8_t v___y_3414_; lean_object* v___y_3427_; uint8_t v___y_3428_; lean_object* v___y_3429_; lean_object* v___y_3430_; lean_object* v___y_3431_; uint8_t v___y_3432_; uint8_t v___y_3433_; uint8_t v___y_3435_; uint8_t v_isHEq_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; uint8_t v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; uint8_t v_isEq_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3510_; lean_object* v___y_3511_; lean_object* v___y_3557_; lean_object* v___y_3558_; lean_object* v___y_3559_; lean_object* v___y_3560_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___x_3739_; 
v___x_3292_ = l_Lean_LocalDecl_type(v_val_3172_);
lean_inc_ref(v___x_3292_);
v___x_3739_ = l_Lean_Meta_matchNot_x3f(v___x_3292_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v_a_3740_; 
v_a_3740_ = lean_ctor_get(v___x_3739_, 0);
lean_inc(v_a_3740_);
lean_dec_ref_known(v___x_3739_, 1);
if (lean_obj_tag(v_a_3740_) == 1)
{
lean_object* v_val_3741_; lean_object* v___x_3743_; uint8_t v_isShared_3744_; uint8_t v_isSharedCheck_3800_; 
v_val_3741_ = lean_ctor_get(v_a_3740_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v_a_3740_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3743_ = v_a_3740_;
v_isShared_3744_ = v_isSharedCheck_3800_;
goto v_resetjp_3742_;
}
else
{
lean_inc(v_val_3741_);
lean_dec(v_a_3740_);
v___x_3743_ = lean_box(0);
v_isShared_3744_ = v_isSharedCheck_3800_;
goto v_resetjp_3742_;
}
v_resetjp_3742_:
{
lean_object* v___x_3745_; 
v___x_3745_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3741_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
if (lean_obj_tag(v___x_3745_) == 0)
{
lean_object* v_a_3746_; 
v_a_3746_ = lean_ctor_get(v___x_3745_, 0);
lean_inc(v_a_3746_);
lean_dec_ref_known(v___x_3745_, 1);
if (lean_obj_tag(v_a_3746_) == 1)
{
lean_object* v_val_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3791_; 
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec_ref(v_config_3140_);
v_val_3747_ = lean_ctor_get(v_a_3746_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_a_3746_);
if (v_isSharedCheck_3791_ == 0)
{
v___x_3749_ = v_a_3746_;
v_isShared_3750_ = v_isSharedCheck_3791_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_val_3747_);
lean_dec(v_a_3746_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3791_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; 
lean_inc(v_mvarId_3141_);
v___x_3751_ = l_Lean_MVarId_getType(v_mvarId_3141_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
if (lean_obj_tag(v___x_3751_) == 0)
{
lean_object* v_a_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; 
v_a_3752_ = lean_ctor_get(v___x_3751_, 0);
lean_inc(v_a_3752_);
lean_dec_ref_known(v___x_3751_, 1);
v___x_3753_ = l_Lean_LocalDecl_toExpr(v_val_3172_);
v___x_3754_ = l_Lean_mkFVar(v_val_3747_);
v___x_3755_ = l_Lean_Expr_app___override(v___x_3753_, v___x_3754_);
v___x_3756_ = l_Lean_Meta_mkFalseElim(v_a_3752_, v___x_3755_, v___y_3146_, v___y_3147_, v___y_3148_, v___y_3149_);
if (lean_obj_tag(v___x_3756_) == 0)
{
lean_object* v_a_3757_; lean_object* v___x_3758_; 
v_a_3757_ = lean_ctor_get(v___x_3756_, 0);
lean_inc(v_a_3757_);
lean_dec_ref_known(v___x_3756_, 1);
v___x_3758_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3141_, v_a_3757_, v___y_3147_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v___x_3759_; lean_object* v___x_3761_; 
lean_dec_ref_known(v___x_3758_, 1);
v___x_3759_ = lean_box(v___x_3151_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set(v___x_3749_, 0, v___x_3759_);
v___x_3761_ = v___x_3749_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3766_; 
v_reuseFailAlloc_3766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3766_, 0, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3766_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
lean_object* v___x_3762_; lean_object* v___x_3764_; 
v___x_3762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3761_);
lean_ctor_set(v___x_3762_, 1, v___x_3176_);
if (v_isShared_3744_ == 0)
{
lean_ctor_set_tag(v___x_3743_, 0);
lean_ctor_set(v___x_3743_, 0, v___x_3762_);
v___x_3764_ = v___x_3743_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3765_; 
v_reuseFailAlloc_3765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3765_, 0, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3765_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
v_a_3158_ = v___x_3764_;
goto v___jp_3157_;
}
}
}
else
{
lean_object* v_a_3767_; lean_object* v___x_3769_; uint8_t v_isShared_3770_; uint8_t v_isSharedCheck_3774_; 
lean_del_object(v___x_3749_);
lean_del_object(v___x_3743_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
v_a_3767_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3774_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3774_ == 0)
{
v___x_3769_ = v___x_3758_;
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
else
{
lean_inc(v_a_3767_);
lean_dec(v___x_3758_);
v___x_3769_ = lean_box(0);
v_isShared_3770_ = v_isSharedCheck_3774_;
goto v_resetjp_3768_;
}
v_resetjp_3768_:
{
lean_object* v___x_3772_; 
if (v_isShared_3770_ == 0)
{
v___x_3772_ = v___x_3769_;
goto v_reusejp_3771_;
}
else
{
lean_object* v_reuseFailAlloc_3773_; 
v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
v___x_3772_ = v_reuseFailAlloc_3773_;
goto v_reusejp_3771_;
}
v_reusejp_3771_:
{
return v___x_3772_;
}
}
}
}
else
{
lean_object* v_a_3775_; lean_object* v___x_3777_; uint8_t v_isShared_3778_; uint8_t v_isSharedCheck_3782_; 
lean_del_object(v___x_3749_);
lean_del_object(v___x_3743_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3775_ = lean_ctor_get(v___x_3756_, 0);
v_isSharedCheck_3782_ = !lean_is_exclusive(v___x_3756_);
if (v_isSharedCheck_3782_ == 0)
{
v___x_3777_ = v___x_3756_;
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
else
{
lean_inc(v_a_3775_);
lean_dec(v___x_3756_);
v___x_3777_ = lean_box(0);
v_isShared_3778_ = v_isSharedCheck_3782_;
goto v_resetjp_3776_;
}
v_resetjp_3776_:
{
lean_object* v___x_3780_; 
if (v_isShared_3778_ == 0)
{
v___x_3780_ = v___x_3777_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v_a_3775_);
v___x_3780_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
return v___x_3780_;
}
}
}
}
else
{
lean_object* v_a_3783_; lean_object* v___x_3785_; uint8_t v_isShared_3786_; uint8_t v_isSharedCheck_3790_; 
lean_del_object(v___x_3749_);
lean_dec(v_val_3747_);
lean_del_object(v___x_3743_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3783_ = lean_ctor_get(v___x_3751_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v___x_3751_);
if (v_isSharedCheck_3790_ == 0)
{
v___x_3785_ = v___x_3751_;
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
else
{
lean_inc(v_a_3783_);
lean_dec(v___x_3751_);
v___x_3785_ = lean_box(0);
v_isShared_3786_ = v_isSharedCheck_3790_;
goto v_resetjp_3784_;
}
v_resetjp_3784_:
{
lean_object* v___x_3788_; 
if (v_isShared_3786_ == 0)
{
v___x_3788_ = v___x_3785_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v_a_3783_);
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
}
else
{
lean_dec(v_a_3746_);
lean_del_object(v___x_3743_);
v___y_3603_ = v___y_3146_;
v___y_3604_ = v___y_3147_;
v___y_3605_ = v___y_3148_;
v___y_3606_ = v___y_3149_;
goto v___jp_3602_;
}
}
else
{
lean_object* v_a_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3799_; 
lean_del_object(v___x_3743_);
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3792_ = lean_ctor_get(v___x_3745_, 0);
v_isSharedCheck_3799_ = !lean_is_exclusive(v___x_3745_);
if (v_isSharedCheck_3799_ == 0)
{
v___x_3794_ = v___x_3745_;
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_a_3792_);
lean_dec(v___x_3745_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3799_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3797_; 
if (v_isShared_3795_ == 0)
{
v___x_3797_ = v___x_3794_;
goto v_reusejp_3796_;
}
else
{
lean_object* v_reuseFailAlloc_3798_; 
v_reuseFailAlloc_3798_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3798_, 0, v_a_3792_);
v___x_3797_ = v_reuseFailAlloc_3798_;
goto v_reusejp_3796_;
}
v_reusejp_3796_:
{
return v___x_3797_;
}
}
}
}
}
else
{
lean_dec(v_a_3740_);
v___y_3603_ = v___y_3146_;
v___y_3604_ = v___y_3147_;
v___y_3605_ = v___y_3148_;
v___y_3606_ = v___y_3149_;
goto v___jp_3602_;
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3801_ = lean_ctor_get(v___x_3739_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3739_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3739_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3739_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
v___jp_3293_:
{
uint8_t v_genDiseq_3300_; 
v_genDiseq_3300_ = lean_ctor_get_uint8(v_config_3140_, sizeof(void*)*1 + 2);
if (v_genDiseq_3300_ == 0)
{
lean_dec_ref(v___x_3292_);
v___y_3270_ = v___y_3296_;
v___y_3271_ = v___y_3294_;
v___y_3272_ = v___y_3299_;
v___y_3273_ = v___y_3298_;
v___y_3274_ = v___y_3297_;
v___y_3275_ = v___y_3295_;
v___y_3276_ = v___x_3247_;
goto v___jp_3269_;
}
else
{
uint8_t v___x_3301_; 
v___x_3301_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3292_);
v___y_3270_ = v___y_3296_;
v___y_3271_ = v___y_3294_;
v___y_3272_ = v___y_3299_;
v___y_3273_ = v___y_3298_;
v___y_3274_ = v___y_3297_;
v___y_3275_ = v___y_3295_;
v___y_3276_ = v___x_3301_;
goto v___jp_3269_;
}
}
v___jp_3302_:
{
if (v___y_3310_ == 0)
{
lean_dec_ref(v___y_3309_);
v___y_3294_ = v___y_3304_;
v___y_3295_ = v___y_3308_;
v___y_3296_ = v___y_3305_;
v___y_3297_ = v___y_3307_;
v___y_3298_ = v___y_3303_;
v___y_3299_ = v___y_3306_;
goto v___jp_3293_;
}
else
{
lean_object* v___x_3311_; 
lean_dec_ref(v___x_3292_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v___x_3311_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3311_, 0, v___y_3309_);
return v___x_3311_;
}
}
v___jp_3312_:
{
uint8_t v___x_3320_; 
v___x_3320_ = l_Lean_Exception_isInterrupt(v_a_3319_);
if (v___x_3320_ == 0)
{
uint8_t v___x_3321_; 
lean_inc_ref(v_a_3319_);
v___x_3321_ = l_Lean_Exception_isRuntime(v_a_3319_);
v___y_3303_ = v___y_3313_;
v___y_3304_ = v___y_3314_;
v___y_3305_ = v___y_3315_;
v___y_3306_ = v___y_3316_;
v___y_3307_ = v___y_3317_;
v___y_3308_ = v___y_3318_;
v___y_3309_ = v_a_3319_;
v___y_3310_ = v___x_3321_;
goto v___jp_3302_;
}
else
{
v___y_3303_ = v___y_3313_;
v___y_3304_ = v___y_3314_;
v___y_3305_ = v___y_3315_;
v___y_3306_ = v___y_3316_;
v___y_3307_ = v___y_3317_;
v___y_3308_ = v___y_3318_;
v___y_3309_ = v_a_3319_;
v___y_3310_ = v___x_3320_;
goto v___jp_3302_;
}
}
v___jp_3322_:
{
lean_object* v___x_3329_; 
lean_inc_ref(v___x_3292_);
v___x_3329_ = l_Lean_Meta_mkDecide(v___x_3292_, v___y_3325_, v___y_3327_, v___y_3323_, v___y_3326_);
if (lean_obj_tag(v___x_3329_) == 0)
{
lean_object* v_a_3330_; lean_object* v_keyedConfig_3331_; uint8_t v_trackZetaDelta_3332_; lean_object* v_zetaDeltaSet_3333_; lean_object* v_lctx_3334_; lean_object* v_localInstances_3335_; lean_object* v_defEqCtx_x3f_3336_; lean_object* v_synthPendingDepth_3337_; lean_object* v_customCanUnfoldPredicate_x3f_3338_; uint8_t v_univApprox_3339_; uint8_t v_inTypeClassResolution_3340_; uint8_t v_cacheInferType_3341_; uint8_t v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; 
v_a_3330_ = lean_ctor_get(v___x_3329_, 0);
lean_inc_n(v_a_3330_, 2);
lean_dec_ref_known(v___x_3329_, 1);
v_keyedConfig_3331_ = lean_ctor_get(v___y_3325_, 0);
v_trackZetaDelta_3332_ = lean_ctor_get_uint8(v___y_3325_, sizeof(void*)*7);
v_zetaDeltaSet_3333_ = lean_ctor_get(v___y_3325_, 1);
v_lctx_3334_ = lean_ctor_get(v___y_3325_, 2);
v_localInstances_3335_ = lean_ctor_get(v___y_3325_, 3);
v_defEqCtx_x3f_3336_ = lean_ctor_get(v___y_3325_, 4);
v_synthPendingDepth_3337_ = lean_ctor_get(v___y_3325_, 5);
v_customCanUnfoldPredicate_x3f_3338_ = lean_ctor_get(v___y_3325_, 6);
v_univApprox_3339_ = lean_ctor_get_uint8(v___y_3325_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3340_ = lean_ctor_get_uint8(v___y_3325_, sizeof(void*)*7 + 2);
v_cacheInferType_3341_ = lean_ctor_get_uint8(v___y_3325_, sizeof(void*)*7 + 3);
v___x_3342_ = 1;
lean_inc_ref(v_keyedConfig_3331_);
v___x_3343_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3342_, v_keyedConfig_3331_);
lean_inc(v_customCanUnfoldPredicate_x3f_3338_);
lean_inc(v_synthPendingDepth_3337_);
lean_inc(v_defEqCtx_x3f_3336_);
lean_inc_ref(v_localInstances_3335_);
lean_inc_ref(v_lctx_3334_);
lean_inc(v_zetaDeltaSet_3333_);
v___x_3344_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3344_, 0, v___x_3343_);
lean_ctor_set(v___x_3344_, 1, v_zetaDeltaSet_3333_);
lean_ctor_set(v___x_3344_, 2, v_lctx_3334_);
lean_ctor_set(v___x_3344_, 3, v_localInstances_3335_);
lean_ctor_set(v___x_3344_, 4, v_defEqCtx_x3f_3336_);
lean_ctor_set(v___x_3344_, 5, v_synthPendingDepth_3337_);
lean_ctor_set(v___x_3344_, 6, v_customCanUnfoldPredicate_x3f_3338_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7, v_trackZetaDelta_3332_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 1, v_univApprox_3339_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3340_);
lean_ctor_set_uint8(v___x_3344_, sizeof(void*)*7 + 3, v_cacheInferType_3341_);
lean_inc(v___y_3326_);
lean_inc_ref(v___y_3323_);
lean_inc(v___y_3327_);
v___x_3345_ = lean_whnf(v_a_3330_, v___x_3344_, v___y_3327_, v___y_3323_, v___y_3326_);
if (lean_obj_tag(v___x_3345_) == 0)
{
lean_object* v_a_3346_; lean_object* v___x_3347_; uint8_t v___x_3348_; 
v_a_3346_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3346_);
lean_dec_ref_known(v___x_3345_, 1);
v___x_3347_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3348_ = l_Lean_Expr_isConstOf(v_a_3346_, v___x_3347_);
lean_dec(v_a_3346_);
if (v___x_3348_ == 0)
{
lean_dec(v_a_3330_);
v___y_3294_ = v___y_3324_;
v___y_3295_ = v___y_3328_;
v___y_3296_ = v___y_3325_;
v___y_3297_ = v___y_3327_;
v___y_3298_ = v___y_3323_;
v___y_3299_ = v___y_3326_;
goto v___jp_3293_;
}
else
{
lean_object* v___x_3349_; 
lean_inc(v_a_3330_);
v___x_3349_ = l_Lean_Meta_mkEqRefl(v_a_3330_, v___y_3325_, v___y_3327_, v___y_3323_, v___y_3326_);
if (lean_obj_tag(v___x_3349_) == 0)
{
lean_object* v_a_3350_; lean_object* v___x_3351_; 
v_a_3350_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3350_);
lean_dec_ref_known(v___x_3349_, 1);
lean_inc(v_mvarId_3141_);
v___x_3351_ = l_Lean_MVarId_getType(v_mvarId_3141_, v___y_3325_, v___y_3327_, v___y_3323_, v___y_3326_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; lean_object* v_nargs_3353_; lean_object* v___x_3354_; lean_object* v_dummy_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v___x_3351_, 1);
v_nargs_3353_ = l_Lean_Expr_getAppNumArgs(v_a_3330_);
v___x_3354_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3355_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_3353_);
v___x_3356_ = lean_mk_array(v_nargs_3353_, v_dummy_3355_);
v___x_3357_ = lean_unsigned_to_nat(1u);
v___x_3358_ = lean_nat_sub(v_nargs_3353_, v___x_3357_);
lean_dec(v_nargs_3353_);
v___x_3359_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3330_, v___x_3356_, v___x_3358_);
v___x_3360_ = lean_array_push(v___x_3359_, v_a_3350_);
v___x_3361_ = l_Lean_mkAppN(v___x_3354_, v___x_3360_);
lean_dec_ref(v___x_3360_);
lean_inc(v_val_3172_);
v___x_3362_ = l_Lean_LocalDecl_toExpr(v_val_3172_);
v___x_3363_ = l_Lean_Meta_mkAbsurd(v_a_3352_, v___x_3362_, v___x_3361_, v___y_3325_, v___y_3327_, v___y_3323_, v___y_3326_);
if (lean_obj_tag(v___x_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3366_; uint8_t v_isShared_3367_; uint8_t v_isSharedCheck_3383_; 
v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3363_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3366_ = v___x_3363_;
v_isShared_3367_ = v_isSharedCheck_3383_;
goto v_resetjp_3365_;
}
else
{
lean_inc(v_a_3364_);
lean_dec(v___x_3363_);
v___x_3366_ = lean_box(0);
v_isShared_3367_ = v_isSharedCheck_3383_;
goto v_resetjp_3365_;
}
v_resetjp_3365_:
{
lean_object* v___x_3368_; 
lean_inc(v_mvarId_3141_);
v___x_3368_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3141_, v_a_3364_, v___y_3327_);
if (lean_obj_tag(v___x_3368_) == 0)
{
lean_object* v___x_3370_; uint8_t v_isShared_3371_; uint8_t v_isSharedCheck_3380_; 
lean_dec_ref(v___x_3292_);
lean_dec(v_val_3172_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3368_);
if (v_isSharedCheck_3380_ == 0)
{
lean_object* v_unused_3381_; 
v_unused_3381_ = lean_ctor_get(v___x_3368_, 0);
lean_dec(v_unused_3381_);
v___x_3370_ = v___x_3368_;
v_isShared_3371_ = v_isSharedCheck_3380_;
goto v_resetjp_3369_;
}
else
{
lean_dec(v___x_3368_);
v___x_3370_ = lean_box(0);
v_isShared_3371_ = v_isSharedCheck_3380_;
goto v_resetjp_3369_;
}
v_resetjp_3369_:
{
lean_object* v___x_3372_; lean_object* v___x_3374_; 
v___x_3372_ = lean_box(v___x_3151_);
if (v_isShared_3371_ == 0)
{
lean_ctor_set_tag(v___x_3370_, 1);
lean_ctor_set(v___x_3370_, 0, v___x_3372_);
v___x_3374_ = v___x_3370_;
goto v_reusejp_3373_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3372_);
v___x_3374_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3373_;
}
v_reusejp_3373_:
{
lean_object* v___x_3375_; lean_object* v___x_3377_; 
v___x_3375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3374_);
lean_ctor_set(v___x_3375_, 1, v___x_3176_);
if (v_isShared_3367_ == 0)
{
lean_ctor_set(v___x_3366_, 0, v___x_3375_);
v___x_3377_ = v___x_3366_;
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
v_a_3158_ = v___x_3377_;
goto v___jp_3157_;
}
}
}
}
else
{
lean_object* v_a_3382_; 
lean_del_object(v___x_3366_);
v_a_3382_ = lean_ctor_get(v___x_3368_, 0);
lean_inc(v_a_3382_);
lean_dec_ref_known(v___x_3368_, 1);
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3325_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v___y_3318_ = v___y_3328_;
v_a_3319_ = v_a_3382_;
goto v___jp_3312_;
}
}
}
else
{
lean_object* v_a_3384_; 
v_a_3384_ = lean_ctor_get(v___x_3363_, 0);
lean_inc(v_a_3384_);
lean_dec_ref_known(v___x_3363_, 1);
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3325_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v___y_3318_ = v___y_3328_;
v_a_3319_ = v_a_3384_;
goto v___jp_3312_;
}
}
else
{
lean_object* v_a_3385_; 
lean_dec(v_a_3350_);
lean_dec(v_a_3330_);
v_a_3385_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3385_);
lean_dec_ref_known(v___x_3351_, 1);
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3325_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v___y_3318_ = v___y_3328_;
v_a_3319_ = v_a_3385_;
goto v___jp_3312_;
}
}
else
{
lean_object* v_a_3386_; 
lean_dec(v_a_3330_);
v_a_3386_ = lean_ctor_get(v___x_3349_, 0);
lean_inc(v_a_3386_);
lean_dec_ref_known(v___x_3349_, 1);
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3325_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v___y_3318_ = v___y_3328_;
v_a_3319_ = v_a_3386_;
goto v___jp_3312_;
}
}
}
else
{
lean_object* v_a_3387_; 
lean_dec(v_a_3330_);
v_a_3387_ = lean_ctor_get(v___x_3345_, 0);
lean_inc(v_a_3387_);
lean_dec_ref_known(v___x_3345_, 1);
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3325_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v___y_3318_ = v___y_3328_;
v_a_3319_ = v_a_3387_;
goto v___jp_3312_;
}
}
else
{
lean_object* v_a_3388_; 
v_a_3388_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_a_3388_);
lean_dec_ref_known(v___x_3329_, 1);
v___y_3313_ = v___y_3323_;
v___y_3314_ = v___y_3324_;
v___y_3315_ = v___y_3325_;
v___y_3316_ = v___y_3326_;
v___y_3317_ = v___y_3327_;
v___y_3318_ = v___y_3328_;
v_a_3319_ = v_a_3388_;
goto v___jp_3312_;
}
}
v___jp_3389_:
{
if (v___y_3396_ == 0)
{
v___y_3294_ = v___y_3391_;
v___y_3295_ = v___y_3395_;
v___y_3296_ = v___y_3392_;
v___y_3297_ = v___y_3394_;
v___y_3298_ = v___y_3390_;
v___y_3299_ = v___y_3393_;
goto v___jp_3293_;
}
else
{
v___y_3323_ = v___y_3390_;
v___y_3324_ = v___y_3391_;
v___y_3325_ = v___y_3392_;
v___y_3326_ = v___y_3393_;
v___y_3327_ = v___y_3394_;
v___y_3328_ = v___y_3395_;
goto v___jp_3322_;
}
}
v___jp_3397_:
{
if (v___y_3405_ == 0)
{
lean_dec_ref(v___y_3403_);
v___y_3390_ = v___y_3398_;
v___y_3391_ = v___y_3399_;
v___y_3392_ = v___y_3400_;
v___y_3393_ = v___y_3401_;
v___y_3394_ = v___y_3402_;
v___y_3395_ = v___y_3404_;
v___y_3396_ = v___x_3247_;
goto v___jp_3389_;
}
else
{
uint8_t v___x_3406_; 
v___x_3406_ = l_Lean_Expr_hasFVar(v___y_3403_);
lean_dec_ref(v___y_3403_);
if (v___x_3406_ == 0)
{
v___y_3323_ = v___y_3398_;
v___y_3324_ = v___y_3399_;
v___y_3325_ = v___y_3400_;
v___y_3326_ = v___y_3401_;
v___y_3327_ = v___y_3402_;
v___y_3328_ = v___y_3404_;
goto v___jp_3322_;
}
else
{
v___y_3390_ = v___y_3398_;
v___y_3391_ = v___y_3399_;
v___y_3392_ = v___y_3400_;
v___y_3393_ = v___y_3401_;
v___y_3394_ = v___y_3402_;
v___y_3395_ = v___y_3404_;
v___y_3396_ = v___x_3247_;
goto v___jp_3389_;
}
}
}
v___jp_3407_:
{
lean_object* v___x_3415_; 
lean_inc_ref(v___x_3292_);
v___x_3415_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3292_, v___y_3412_);
if (lean_obj_tag(v___x_3415_) == 0)
{
lean_object* v_a_3416_; uint8_t v___x_3417_; 
v_a_3416_ = lean_ctor_get(v___x_3415_, 0);
lean_inc(v_a_3416_);
lean_dec_ref_known(v___x_3415_, 1);
v___x_3417_ = l_Lean_Expr_hasMVar(v_a_3416_);
if (v___x_3417_ == 0)
{
v___y_3398_ = v___y_3408_;
v___y_3399_ = v___y_3409_;
v___y_3400_ = v___y_3410_;
v___y_3401_ = v___y_3411_;
v___y_3402_ = v___y_3412_;
v___y_3403_ = v_a_3416_;
v___y_3404_ = v___y_3413_;
v___y_3405_ = v___y_3414_;
goto v___jp_3397_;
}
else
{
v___y_3398_ = v___y_3408_;
v___y_3399_ = v___y_3409_;
v___y_3400_ = v___y_3410_;
v___y_3401_ = v___y_3411_;
v___y_3402_ = v___y_3412_;
v___y_3403_ = v_a_3416_;
v___y_3404_ = v___y_3413_;
v___y_3405_ = v___x_3247_;
goto v___jp_3397_;
}
}
else
{
lean_object* v_a_3418_; lean_object* v___x_3420_; uint8_t v_isShared_3421_; uint8_t v_isSharedCheck_3425_; 
lean_dec_ref(v___x_3292_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3418_ = lean_ctor_get(v___x_3415_, 0);
v_isSharedCheck_3425_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3425_ == 0)
{
v___x_3420_ = v___x_3415_;
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
else
{
lean_inc(v_a_3418_);
lean_dec(v___x_3415_);
v___x_3420_ = lean_box(0);
v_isShared_3421_ = v_isSharedCheck_3425_;
goto v_resetjp_3419_;
}
v_resetjp_3419_:
{
lean_object* v___x_3423_; 
if (v_isShared_3421_ == 0)
{
v___x_3423_ = v___x_3420_;
goto v_reusejp_3422_;
}
else
{
lean_object* v_reuseFailAlloc_3424_; 
v_reuseFailAlloc_3424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3424_, 0, v_a_3418_);
v___x_3423_ = v_reuseFailAlloc_3424_;
goto v_reusejp_3422_;
}
v_reusejp_3422_:
{
return v___x_3423_;
}
}
}
}
v___jp_3426_:
{
if (v___y_3433_ == 0)
{
v___y_3294_ = v___y_3428_;
v___y_3295_ = v___y_3432_;
v___y_3296_ = v___y_3429_;
v___y_3297_ = v___y_3431_;
v___y_3298_ = v___y_3427_;
v___y_3299_ = v___y_3430_;
goto v___jp_3293_;
}
else
{
v___y_3408_ = v___y_3427_;
v___y_3409_ = v___y_3428_;
v___y_3410_ = v___y_3429_;
v___y_3411_ = v___y_3430_;
v___y_3412_ = v___y_3431_;
v___y_3413_ = v___y_3432_;
v___y_3414_ = v___y_3433_;
goto v___jp_3407_;
}
}
v___jp_3434_:
{
uint8_t v_useDecide_3441_; 
v_useDecide_3441_ = lean_ctor_get_uint8(v_config_3140_, sizeof(void*)*1);
if (v_useDecide_3441_ == 0)
{
v___y_3427_ = v___y_3439_;
v___y_3428_ = v_isHEq_3436_;
v___y_3429_ = v___y_3437_;
v___y_3430_ = v___y_3440_;
v___y_3431_ = v___y_3438_;
v___y_3432_ = v___y_3435_;
v___y_3433_ = v___x_3247_;
goto v___jp_3426_;
}
else
{
uint8_t v___x_3442_; 
v___x_3442_ = l_Lean_Expr_hasFVar(v___x_3292_);
if (v___x_3442_ == 0)
{
v___y_3408_ = v___y_3439_;
v___y_3409_ = v_isHEq_3436_;
v___y_3410_ = v___y_3437_;
v___y_3411_ = v___y_3440_;
v___y_3412_ = v___y_3438_;
v___y_3413_ = v___y_3435_;
v___y_3414_ = v_useDecide_3441_;
goto v___jp_3407_;
}
else
{
v___y_3427_ = v___y_3439_;
v___y_3428_ = v_isHEq_3436_;
v___y_3429_ = v___y_3437_;
v___y_3430_ = v___y_3440_;
v___y_3431_ = v___y_3438_;
v___y_3432_ = v___y_3435_;
v___y_3433_ = v___x_3247_;
goto v___jp_3426_;
}
}
}
v___jp_3443_:
{
lean_object* v___x_3451_; 
v___x_3451_ = l_Lean_Meta_isExprDefEq(v___y_3450_, v___y_3449_, v___y_3448_, v___y_3446_, v___y_3444_, v___y_3445_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; uint8_t v___x_3453_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3453_ = lean_unbox(v_a_3452_);
lean_dec(v_a_3452_);
if (v___x_3453_ == 0)
{
v___y_3435_ = v___y_3447_;
v_isHEq_3436_ = v___x_3151_;
v___y_3437_ = v___y_3448_;
v___y_3438_ = v___y_3446_;
v___y_3439_ = v___y_3444_;
v___y_3440_ = v___y_3445_;
goto v___jp_3434_;
}
else
{
lean_object* v___x_3454_; 
lean_dec_ref(v___x_3292_);
lean_dec_ref(v_config_3140_);
lean_inc(v_mvarId_3141_);
v___x_3454_ = l_Lean_MVarId_getType(v_mvarId_3141_, v___y_3448_, v___y_3446_, v___y_3444_, v___y_3445_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_object* v_a_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v_a_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_a_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v___x_3456_ = l_Lean_LocalDecl_toExpr(v_val_3172_);
v___x_3457_ = l_Lean_Meta_mkEqOfHEq(v___x_3456_, v___x_3151_, v___y_3448_, v___y_3446_, v___y_3444_, v___y_3445_);
if (lean_obj_tag(v___x_3457_) == 0)
{
lean_object* v_a_3458_; lean_object* v___x_3459_; 
v_a_3458_ = lean_ctor_get(v___x_3457_, 0);
lean_inc(v_a_3458_);
lean_dec_ref_known(v___x_3457_, 1);
v___x_3459_ = l_Lean_Meta_mkNoConfusion(v_a_3455_, v_a_3458_, v___y_3448_, v___y_3446_, v___y_3444_, v___y_3445_);
if (lean_obj_tag(v___x_3459_) == 0)
{
lean_object* v_a_3460_; lean_object* v___x_3461_; 
v_a_3460_ = lean_ctor_get(v___x_3459_, 0);
lean_inc(v_a_3460_);
lean_dec_ref_known(v___x_3459_, 1);
v___x_3461_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3141_, v_a_3460_, v___y_3446_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v___x_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___x_3465_; 
lean_dec_ref_known(v___x_3461_, 1);
v___x_3462_ = lean_box(v___x_3151_);
v___x_3463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3462_);
v___x_3464_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3463_);
lean_ctor_set(v___x_3464_, 1, v___x_3176_);
v___x_3465_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3465_, 0, v___x_3464_);
v_a_3158_ = v___x_3465_;
goto v___jp_3157_;
}
else
{
lean_object* v_a_3466_; lean_object* v___x_3468_; uint8_t v_isShared_3469_; uint8_t v_isSharedCheck_3473_; 
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
v_a_3466_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3473_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3473_ == 0)
{
v___x_3468_ = v___x_3461_;
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
else
{
lean_inc(v_a_3466_);
lean_dec(v___x_3461_);
v___x_3468_ = lean_box(0);
v_isShared_3469_ = v_isSharedCheck_3473_;
goto v_resetjp_3467_;
}
v_resetjp_3467_:
{
lean_object* v___x_3471_; 
if (v_isShared_3469_ == 0)
{
v___x_3471_ = v___x_3468_;
goto v_reusejp_3470_;
}
else
{
lean_object* v_reuseFailAlloc_3472_; 
v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
v___x_3471_ = v_reuseFailAlloc_3472_;
goto v_reusejp_3470_;
}
v_reusejp_3470_:
{
return v___x_3471_;
}
}
}
}
else
{
lean_object* v_a_3474_; lean_object* v___x_3476_; uint8_t v_isShared_3477_; uint8_t v_isSharedCheck_3481_; 
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3474_ = lean_ctor_get(v___x_3459_, 0);
v_isSharedCheck_3481_ = !lean_is_exclusive(v___x_3459_);
if (v_isSharedCheck_3481_ == 0)
{
v___x_3476_ = v___x_3459_;
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
else
{
lean_inc(v_a_3474_);
lean_dec(v___x_3459_);
v___x_3476_ = lean_box(0);
v_isShared_3477_ = v_isSharedCheck_3481_;
goto v_resetjp_3475_;
}
v_resetjp_3475_:
{
lean_object* v___x_3479_; 
if (v_isShared_3477_ == 0)
{
v___x_3479_ = v___x_3476_;
goto v_reusejp_3478_;
}
else
{
lean_object* v_reuseFailAlloc_3480_; 
v_reuseFailAlloc_3480_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3480_, 0, v_a_3474_);
v___x_3479_ = v_reuseFailAlloc_3480_;
goto v_reusejp_3478_;
}
v_reusejp_3478_:
{
return v___x_3479_;
}
}
}
}
else
{
lean_object* v_a_3482_; lean_object* v___x_3484_; uint8_t v_isShared_3485_; uint8_t v_isSharedCheck_3489_; 
lean_dec(v_a_3455_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3482_ = lean_ctor_get(v___x_3457_, 0);
v_isSharedCheck_3489_ = !lean_is_exclusive(v___x_3457_);
if (v_isSharedCheck_3489_ == 0)
{
v___x_3484_ = v___x_3457_;
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
else
{
lean_inc(v_a_3482_);
lean_dec(v___x_3457_);
v___x_3484_ = lean_box(0);
v_isShared_3485_ = v_isSharedCheck_3489_;
goto v_resetjp_3483_;
}
v_resetjp_3483_:
{
lean_object* v___x_3487_; 
if (v_isShared_3485_ == 0)
{
v___x_3487_ = v___x_3484_;
goto v_reusejp_3486_;
}
else
{
lean_object* v_reuseFailAlloc_3488_; 
v_reuseFailAlloc_3488_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3488_, 0, v_a_3482_);
v___x_3487_ = v_reuseFailAlloc_3488_;
goto v_reusejp_3486_;
}
v_reusejp_3486_:
{
return v___x_3487_;
}
}
}
}
else
{
lean_object* v_a_3490_; lean_object* v___x_3492_; uint8_t v_isShared_3493_; uint8_t v_isSharedCheck_3497_; 
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3490_ = lean_ctor_get(v___x_3454_, 0);
v_isSharedCheck_3497_ = !lean_is_exclusive(v___x_3454_);
if (v_isSharedCheck_3497_ == 0)
{
v___x_3492_ = v___x_3454_;
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
else
{
lean_inc(v_a_3490_);
lean_dec(v___x_3454_);
v___x_3492_ = lean_box(0);
v_isShared_3493_ = v_isSharedCheck_3497_;
goto v_resetjp_3491_;
}
v_resetjp_3491_:
{
lean_object* v___x_3495_; 
if (v_isShared_3493_ == 0)
{
v___x_3495_ = v___x_3492_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3496_; 
v_reuseFailAlloc_3496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3496_, 0, v_a_3490_);
v___x_3495_ = v_reuseFailAlloc_3496_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
return v___x_3495_;
}
}
}
}
}
else
{
lean_object* v_a_3498_; lean_object* v___x_3500_; uint8_t v_isShared_3501_; uint8_t v_isSharedCheck_3505_; 
lean_dec_ref(v___x_3292_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3498_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3505_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3505_ == 0)
{
v___x_3500_ = v___x_3451_;
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
else
{
lean_inc(v_a_3498_);
lean_dec(v___x_3451_);
v___x_3500_ = lean_box(0);
v_isShared_3501_ = v_isSharedCheck_3505_;
goto v_resetjp_3499_;
}
v_resetjp_3499_:
{
lean_object* v___x_3503_; 
if (v_isShared_3501_ == 0)
{
v___x_3503_ = v___x_3500_;
goto v_reusejp_3502_;
}
else
{
lean_object* v_reuseFailAlloc_3504_; 
v_reuseFailAlloc_3504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3504_, 0, v_a_3498_);
v___x_3503_ = v_reuseFailAlloc_3504_;
goto v_reusejp_3502_;
}
v_reusejp_3502_:
{
return v___x_3503_;
}
}
}
}
v___jp_3506_:
{
lean_object* v___x_3512_; 
lean_inc_ref(v___x_3292_);
v___x_3512_ = l_Lean_Meta_matchHEq_x3f(v___x_3292_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v_a_3513_; 
v_a_3513_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_a_3513_);
lean_dec_ref_known(v___x_3512_, 1);
if (lean_obj_tag(v_a_3513_) == 1)
{
lean_object* v_val_3514_; lean_object* v_snd_3515_; lean_object* v_snd_3516_; lean_object* v_fst_3517_; lean_object* v_fst_3518_; lean_object* v_fst_3519_; lean_object* v_snd_3520_; lean_object* v___x_3521_; 
v_val_3514_ = lean_ctor_get(v_a_3513_, 0);
lean_inc(v_val_3514_);
lean_dec_ref_known(v_a_3513_, 1);
v_snd_3515_ = lean_ctor_get(v_val_3514_, 1);
lean_inc(v_snd_3515_);
v_snd_3516_ = lean_ctor_get(v_snd_3515_, 1);
lean_inc(v_snd_3516_);
v_fst_3517_ = lean_ctor_get(v_val_3514_, 0);
lean_inc(v_fst_3517_);
lean_dec(v_val_3514_);
v_fst_3518_ = lean_ctor_get(v_snd_3515_, 0);
lean_inc(v_fst_3518_);
lean_dec(v_snd_3515_);
v_fst_3519_ = lean_ctor_get(v_snd_3516_, 0);
lean_inc(v_fst_3519_);
v_snd_3520_ = lean_ctor_get(v_snd_3516_, 1);
lean_inc(v_snd_3520_);
lean_dec(v_snd_3516_);
v___x_3521_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3518_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
if (lean_obj_tag(v___x_3521_) == 0)
{
lean_object* v_a_3522_; 
v_a_3522_ = lean_ctor_get(v___x_3521_, 0);
lean_inc(v_a_3522_);
lean_dec_ref_known(v___x_3521_, 1);
if (lean_obj_tag(v_a_3522_) == 1)
{
lean_object* v_val_3523_; lean_object* v___x_3524_; 
v_val_3523_ = lean_ctor_get(v_a_3522_, 0);
lean_inc(v_val_3523_);
lean_dec_ref_known(v_a_3522_, 1);
v___x_3524_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3520_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
if (lean_obj_tag(v___x_3524_) == 0)
{
lean_object* v_a_3525_; 
v_a_3525_ = lean_ctor_get(v___x_3524_, 0);
lean_inc(v_a_3525_);
lean_dec_ref_known(v___x_3524_, 1);
if (lean_obj_tag(v_a_3525_) == 1)
{
lean_object* v_toConstantVal_3526_; lean_object* v_val_3527_; lean_object* v_toConstantVal_3528_; lean_object* v_name_3529_; lean_object* v_name_3530_; uint8_t v___x_3531_; 
v_toConstantVal_3526_ = lean_ctor_get(v_val_3523_, 0);
lean_inc_ref(v_toConstantVal_3526_);
lean_dec(v_val_3523_);
v_val_3527_ = lean_ctor_get(v_a_3525_, 0);
lean_inc(v_val_3527_);
lean_dec_ref_known(v_a_3525_, 1);
v_toConstantVal_3528_ = lean_ctor_get(v_val_3527_, 0);
lean_inc_ref(v_toConstantVal_3528_);
lean_dec(v_val_3527_);
v_name_3529_ = lean_ctor_get(v_toConstantVal_3526_, 0);
lean_inc(v_name_3529_);
lean_dec_ref(v_toConstantVal_3526_);
v_name_3530_ = lean_ctor_get(v_toConstantVal_3528_, 0);
lean_inc(v_name_3530_);
lean_dec_ref(v_toConstantVal_3528_);
v___x_3531_ = lean_name_eq(v_name_3529_, v_name_3530_);
lean_dec(v_name_3530_);
lean_dec(v_name_3529_);
if (v___x_3531_ == 0)
{
v___y_3444_ = v___y_3510_;
v___y_3445_ = v___y_3511_;
v___y_3446_ = v___y_3509_;
v___y_3447_ = v_isEq_3507_;
v___y_3448_ = v___y_3508_;
v___y_3449_ = v_fst_3519_;
v___y_3450_ = v_fst_3517_;
goto v___jp_3443_;
}
else
{
if (v___x_3247_ == 0)
{
lean_dec(v_fst_3519_);
lean_dec(v_fst_3517_);
v___y_3435_ = v_isEq_3507_;
v_isHEq_3436_ = v___x_3151_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
v___y_3439_ = v___y_3510_;
v___y_3440_ = v___y_3511_;
goto v___jp_3434_;
}
else
{
v___y_3444_ = v___y_3510_;
v___y_3445_ = v___y_3511_;
v___y_3446_ = v___y_3509_;
v___y_3447_ = v_isEq_3507_;
v___y_3448_ = v___y_3508_;
v___y_3449_ = v_fst_3519_;
v___y_3450_ = v_fst_3517_;
goto v___jp_3443_;
}
}
}
else
{
lean_dec(v_a_3525_);
lean_dec(v_val_3523_);
lean_dec(v_fst_3519_);
lean_dec(v_fst_3517_);
v___y_3435_ = v_isEq_3507_;
v_isHEq_3436_ = v___x_3151_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
v___y_3439_ = v___y_3510_;
v___y_3440_ = v___y_3511_;
goto v___jp_3434_;
}
}
else
{
lean_object* v_a_3532_; lean_object* v___x_3534_; uint8_t v_isShared_3535_; uint8_t v_isSharedCheck_3539_; 
lean_dec(v_val_3523_);
lean_dec(v_fst_3519_);
lean_dec(v_fst_3517_);
lean_dec_ref(v___x_3292_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3532_ = lean_ctor_get(v___x_3524_, 0);
v_isSharedCheck_3539_ = !lean_is_exclusive(v___x_3524_);
if (v_isSharedCheck_3539_ == 0)
{
v___x_3534_ = v___x_3524_;
v_isShared_3535_ = v_isSharedCheck_3539_;
goto v_resetjp_3533_;
}
else
{
lean_inc(v_a_3532_);
lean_dec(v___x_3524_);
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
lean_dec(v_a_3522_);
lean_dec(v_snd_3520_);
lean_dec(v_fst_3519_);
lean_dec(v_fst_3517_);
v___y_3435_ = v_isEq_3507_;
v_isHEq_3436_ = v___x_3151_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
v___y_3439_ = v___y_3510_;
v___y_3440_ = v___y_3511_;
goto v___jp_3434_;
}
}
else
{
lean_object* v_a_3540_; lean_object* v___x_3542_; uint8_t v_isShared_3543_; uint8_t v_isSharedCheck_3547_; 
lean_dec(v_snd_3520_);
lean_dec(v_fst_3519_);
lean_dec(v_fst_3517_);
lean_dec_ref(v___x_3292_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3540_ = lean_ctor_get(v___x_3521_, 0);
v_isSharedCheck_3547_ = !lean_is_exclusive(v___x_3521_);
if (v_isSharedCheck_3547_ == 0)
{
v___x_3542_ = v___x_3521_;
v_isShared_3543_ = v_isSharedCheck_3547_;
goto v_resetjp_3541_;
}
else
{
lean_inc(v_a_3540_);
lean_dec(v___x_3521_);
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
lean_dec(v_a_3513_);
v___y_3435_ = v_isEq_3507_;
v_isHEq_3436_ = v___x_3247_;
v___y_3437_ = v___y_3508_;
v___y_3438_ = v___y_3509_;
v___y_3439_ = v___y_3510_;
v___y_3440_ = v___y_3511_;
goto v___jp_3434_;
}
}
else
{
lean_object* v_a_3548_; lean_object* v___x_3550_; uint8_t v_isShared_3551_; uint8_t v_isSharedCheck_3555_; 
lean_dec_ref(v___x_3292_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3548_ = lean_ctor_get(v___x_3512_, 0);
v_isSharedCheck_3555_ = !lean_is_exclusive(v___x_3512_);
if (v_isSharedCheck_3555_ == 0)
{
v___x_3550_ = v___x_3512_;
v_isShared_3551_ = v_isSharedCheck_3555_;
goto v_resetjp_3549_;
}
else
{
lean_inc(v_a_3548_);
lean_dec(v___x_3512_);
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
v___jp_3556_:
{
lean_object* v___x_3561_; 
lean_inc_ref(v___x_3292_);
v___x_3561_ = l_Lean_Meta_matchEq_x3f(v___x_3292_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
if (lean_obj_tag(v___x_3561_) == 0)
{
lean_object* v_a_3562_; 
v_a_3562_ = lean_ctor_get(v___x_3561_, 0);
lean_inc(v_a_3562_);
lean_dec_ref_known(v___x_3561_, 1);
if (lean_obj_tag(v_a_3562_) == 1)
{
lean_object* v_val_3563_; lean_object* v_snd_3564_; lean_object* v_fst_3565_; lean_object* v_snd_3566_; lean_object* v___x_3567_; 
v_val_3563_ = lean_ctor_get(v_a_3562_, 0);
lean_inc(v_val_3563_);
lean_dec_ref_known(v_a_3562_, 1);
v_snd_3564_ = lean_ctor_get(v_val_3563_, 1);
lean_inc(v_snd_3564_);
lean_dec(v_val_3563_);
v_fst_3565_ = lean_ctor_get(v_snd_3564_, 0);
lean_inc(v_fst_3565_);
v_snd_3566_ = lean_ctor_get(v_snd_3564_, 1);
lean_inc(v_snd_3566_);
lean_dec(v_snd_3564_);
v___x_3567_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3565_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
if (lean_obj_tag(v___x_3567_) == 0)
{
lean_object* v_a_3568_; 
v_a_3568_ = lean_ctor_get(v___x_3567_, 0);
lean_inc(v_a_3568_);
lean_dec_ref_known(v___x_3567_, 1);
if (lean_obj_tag(v_a_3568_) == 1)
{
lean_object* v_val_3569_; lean_object* v___x_3570_; 
v_val_3569_ = lean_ctor_get(v_a_3568_, 0);
lean_inc(v_val_3569_);
lean_dec_ref_known(v_a_3568_, 1);
v___x_3570_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3566_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
if (lean_obj_tag(v___x_3570_) == 0)
{
lean_object* v_a_3571_; 
v_a_3571_ = lean_ctor_get(v___x_3570_, 0);
lean_inc(v_a_3571_);
lean_dec_ref_known(v___x_3570_, 1);
if (lean_obj_tag(v_a_3571_) == 1)
{
lean_object* v_toConstantVal_3572_; lean_object* v_val_3573_; lean_object* v_toConstantVal_3574_; lean_object* v_name_3575_; lean_object* v_name_3576_; uint8_t v___x_3577_; 
v_toConstantVal_3572_ = lean_ctor_get(v_val_3569_, 0);
lean_inc_ref(v_toConstantVal_3572_);
lean_dec(v_val_3569_);
v_val_3573_ = lean_ctor_get(v_a_3571_, 0);
lean_inc(v_val_3573_);
lean_dec_ref_known(v_a_3571_, 1);
v_toConstantVal_3574_ = lean_ctor_get(v_val_3573_, 0);
lean_inc_ref(v_toConstantVal_3574_);
lean_dec(v_val_3573_);
v_name_3575_ = lean_ctor_get(v_toConstantVal_3572_, 0);
lean_inc(v_name_3575_);
lean_dec_ref(v_toConstantVal_3572_);
v_name_3576_ = lean_ctor_get(v_toConstantVal_3574_, 0);
lean_inc(v_name_3576_);
lean_dec_ref(v_toConstantVal_3574_);
v___x_3577_ = lean_name_eq(v_name_3575_, v_name_3576_);
lean_dec(v_name_3576_);
lean_dec(v_name_3575_);
if (v___x_3577_ == 0)
{
lean_dec_ref(v___x_3292_);
lean_dec_ref(v_config_3140_);
v___y_3178_ = v___y_3560_;
v___y_3179_ = v___y_3559_;
v___y_3180_ = v___y_3558_;
v___y_3181_ = v___y_3557_;
goto v___jp_3177_;
}
else
{
if (v___x_3247_ == 0)
{
lean_del_object(v___x_3174_);
v_isEq_3507_ = v___x_3151_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
v___y_3510_ = v___y_3559_;
v___y_3511_ = v___y_3560_;
goto v___jp_3506_;
}
else
{
lean_dec_ref(v___x_3292_);
lean_dec_ref(v_config_3140_);
v___y_3178_ = v___y_3560_;
v___y_3179_ = v___y_3559_;
v___y_3180_ = v___y_3558_;
v___y_3181_ = v___y_3557_;
goto v___jp_3177_;
}
}
}
else
{
lean_dec(v_a_3571_);
lean_dec(v_val_3569_);
lean_del_object(v___x_3174_);
v_isEq_3507_ = v___x_3151_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
v___y_3510_ = v___y_3559_;
v___y_3511_ = v___y_3560_;
goto v___jp_3506_;
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_val_3569_);
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3578_ = lean_ctor_get(v___x_3570_, 0);
v_isSharedCheck_3585_ = !lean_is_exclusive(v___x_3570_);
if (v_isSharedCheck_3585_ == 0)
{
v___x_3580_ = v___x_3570_;
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
else
{
lean_inc(v_a_3578_);
lean_dec(v___x_3570_);
v___x_3580_ = lean_box(0);
v_isShared_3581_ = v_isSharedCheck_3585_;
goto v_resetjp_3579_;
}
v_resetjp_3579_:
{
lean_object* v___x_3583_; 
if (v_isShared_3581_ == 0)
{
v___x_3583_ = v___x_3580_;
goto v_reusejp_3582_;
}
else
{
lean_object* v_reuseFailAlloc_3584_; 
v_reuseFailAlloc_3584_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3584_, 0, v_a_3578_);
v___x_3583_ = v_reuseFailAlloc_3584_;
goto v_reusejp_3582_;
}
v_reusejp_3582_:
{
return v___x_3583_;
}
}
}
}
else
{
lean_dec(v_a_3568_);
lean_dec(v_snd_3566_);
lean_del_object(v___x_3174_);
v_isEq_3507_ = v___x_3151_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
v___y_3510_ = v___y_3559_;
v___y_3511_ = v___y_3560_;
goto v___jp_3506_;
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v_snd_3566_);
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3586_ = lean_ctor_get(v___x_3567_, 0);
v_isSharedCheck_3593_ = !lean_is_exclusive(v___x_3567_);
if (v_isSharedCheck_3593_ == 0)
{
v___x_3588_ = v___x_3567_;
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
else
{
lean_inc(v_a_3586_);
lean_dec(v___x_3567_);
v___x_3588_ = lean_box(0);
v_isShared_3589_ = v_isSharedCheck_3593_;
goto v_resetjp_3587_;
}
v_resetjp_3587_:
{
lean_object* v___x_3591_; 
if (v_isShared_3589_ == 0)
{
v___x_3591_ = v___x_3588_;
goto v_reusejp_3590_;
}
else
{
lean_object* v_reuseFailAlloc_3592_; 
v_reuseFailAlloc_3592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3592_, 0, v_a_3586_);
v___x_3591_ = v_reuseFailAlloc_3592_;
goto v_reusejp_3590_;
}
v_reusejp_3590_:
{
return v___x_3591_;
}
}
}
}
else
{
lean_dec(v_a_3562_);
lean_del_object(v___x_3174_);
v_isEq_3507_ = v___x_3247_;
v___y_3508_ = v___y_3557_;
v___y_3509_ = v___y_3558_;
v___y_3510_ = v___y_3559_;
v___y_3511_ = v___y_3560_;
goto v___jp_3506_;
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3594_ = lean_ctor_get(v___x_3561_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3561_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3561_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3561_);
v___x_3596_ = lean_box(0);
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
v_resetjp_3595_:
{
lean_object* v___x_3599_; 
if (v_isShared_3597_ == 0)
{
v___x_3599_ = v___x_3596_;
goto v_reusejp_3598_;
}
else
{
lean_object* v_reuseFailAlloc_3600_; 
v_reuseFailAlloc_3600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3600_, 0, v_a_3594_);
v___x_3599_ = v_reuseFailAlloc_3600_;
goto v_reusejp_3598_;
}
v_reusejp_3598_:
{
return v___x_3599_;
}
}
}
}
v___jp_3602_:
{
lean_object* v___x_3607_; 
lean_inc_ref(v___x_3292_);
v___x_3607_ = l_Lean_refutableHasNotBit_x3f(v___x_3292_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
if (lean_obj_tag(v_a_3608_) == 1)
{
lean_object* v_val_3609_; lean_object* v___x_3611_; uint8_t v_isShared_3612_; uint8_t v_isSharedCheck_3649_; 
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec_ref(v_config_3140_);
v_val_3609_ = lean_ctor_get(v_a_3608_, 0);
v_isSharedCheck_3649_ = !lean_is_exclusive(v_a_3608_);
if (v_isSharedCheck_3649_ == 0)
{
v___x_3611_ = v_a_3608_;
v_isShared_3612_ = v_isSharedCheck_3649_;
goto v_resetjp_3610_;
}
else
{
lean_inc(v_val_3609_);
lean_dec(v_a_3608_);
v___x_3611_ = lean_box(0);
v_isShared_3612_ = v_isSharedCheck_3649_;
goto v_resetjp_3610_;
}
v_resetjp_3610_:
{
lean_object* v___x_3613_; 
lean_inc(v_mvarId_3141_);
v___x_3613_ = l_Lean_MVarId_getType(v_mvarId_3141_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
v___x_3615_ = l_Lean_LocalDecl_toExpr(v_val_3172_);
v___x_3616_ = l_Lean_Meta_mkAbsurd(v_a_3614_, v_val_3609_, v___x_3615_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; lean_object* v___x_3618_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
v___x_3618_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3141_, v_a_3617_, v___y_3604_);
if (lean_obj_tag(v___x_3618_) == 0)
{
lean_object* v___x_3619_; lean_object* v___x_3621_; 
lean_dec_ref_known(v___x_3618_, 1);
v___x_3619_ = lean_box(v___x_3151_);
if (v_isShared_3612_ == 0)
{
lean_ctor_set(v___x_3611_, 0, v___x_3619_);
v___x_3621_ = v___x_3611_;
goto v_reusejp_3620_;
}
else
{
lean_object* v_reuseFailAlloc_3624_; 
v_reuseFailAlloc_3624_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3624_, 0, v___x_3619_);
v___x_3621_ = v_reuseFailAlloc_3624_;
goto v_reusejp_3620_;
}
v_reusejp_3620_:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3622_, 0, v___x_3621_);
lean_ctor_set(v___x_3622_, 1, v___x_3176_);
v___x_3623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3622_);
v_a_3158_ = v___x_3623_;
goto v___jp_3157_;
}
}
else
{
lean_object* v_a_3625_; lean_object* v___x_3627_; uint8_t v_isShared_3628_; uint8_t v_isSharedCheck_3632_; 
lean_del_object(v___x_3611_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
v_a_3625_ = lean_ctor_get(v___x_3618_, 0);
v_isSharedCheck_3632_ = !lean_is_exclusive(v___x_3618_);
if (v_isSharedCheck_3632_ == 0)
{
v___x_3627_ = v___x_3618_;
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
else
{
lean_inc(v_a_3625_);
lean_dec(v___x_3618_);
v___x_3627_ = lean_box(0);
v_isShared_3628_ = v_isSharedCheck_3632_;
goto v_resetjp_3626_;
}
v_resetjp_3626_:
{
lean_object* v___x_3630_; 
if (v_isShared_3628_ == 0)
{
v___x_3630_ = v___x_3627_;
goto v_reusejp_3629_;
}
else
{
lean_object* v_reuseFailAlloc_3631_; 
v_reuseFailAlloc_3631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3631_, 0, v_a_3625_);
v___x_3630_ = v_reuseFailAlloc_3631_;
goto v_reusejp_3629_;
}
v_reusejp_3629_:
{
return v___x_3630_;
}
}
}
}
else
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3640_; 
lean_del_object(v___x_3611_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3633_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3640_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3640_ == 0)
{
v___x_3635_ = v___x_3616_;
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3616_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3640_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v___x_3638_; 
if (v_isShared_3636_ == 0)
{
v___x_3638_ = v___x_3635_;
goto v_reusejp_3637_;
}
else
{
lean_object* v_reuseFailAlloc_3639_; 
v_reuseFailAlloc_3639_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3639_, 0, v_a_3633_);
v___x_3638_ = v_reuseFailAlloc_3639_;
goto v_reusejp_3637_;
}
v_reusejp_3637_:
{
return v___x_3638_;
}
}
}
}
else
{
lean_object* v_a_3641_; lean_object* v___x_3643_; uint8_t v_isShared_3644_; uint8_t v_isSharedCheck_3648_; 
lean_del_object(v___x_3611_);
lean_dec(v_val_3609_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3641_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3648_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3648_ == 0)
{
v___x_3643_ = v___x_3613_;
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
else
{
lean_inc(v_a_3641_);
lean_dec(v___x_3613_);
v___x_3643_ = lean_box(0);
v_isShared_3644_ = v_isSharedCheck_3648_;
goto v_resetjp_3642_;
}
v_resetjp_3642_:
{
lean_object* v___x_3646_; 
if (v_isShared_3644_ == 0)
{
v___x_3646_ = v___x_3643_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3647_; 
v_reuseFailAlloc_3647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3647_, 0, v_a_3641_);
v___x_3646_ = v_reuseFailAlloc_3647_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
return v___x_3646_;
}
}
}
}
}
else
{
lean_object* v___x_3650_; 
lean_dec(v_a_3608_);
lean_inc_ref(v___x_3292_);
v___x_3650_ = l_Lean_Meta_matchNe_x3f(v___x_3292_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3650_) == 0)
{
lean_object* v_a_3651_; 
v_a_3651_ = lean_ctor_get(v___x_3650_, 0);
lean_inc(v_a_3651_);
lean_dec_ref_known(v___x_3650_, 1);
if (lean_obj_tag(v_a_3651_) == 1)
{
lean_object* v_val_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3722_; 
v_val_3652_ = lean_ctor_get(v_a_3651_, 0);
v_isSharedCheck_3722_ = !lean_is_exclusive(v_a_3651_);
if (v_isSharedCheck_3722_ == 0)
{
v___x_3654_ = v_a_3651_;
v_isShared_3655_ = v_isSharedCheck_3722_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_val_3652_);
lean_dec(v_a_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3722_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v_snd_3656_; lean_object* v_fst_3657_; lean_object* v_snd_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3721_; 
v_snd_3656_ = lean_ctor_get(v_val_3652_, 1);
lean_inc(v_snd_3656_);
lean_dec(v_val_3652_);
v_fst_3657_ = lean_ctor_get(v_snd_3656_, 0);
v_snd_3658_ = lean_ctor_get(v_snd_3656_, 1);
v_isSharedCheck_3721_ = !lean_is_exclusive(v_snd_3656_);
if (v_isSharedCheck_3721_ == 0)
{
v___x_3660_ = v_snd_3656_;
v_isShared_3661_ = v_isSharedCheck_3721_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_snd_3658_);
lean_inc(v_fst_3657_);
lean_dec(v_snd_3656_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3721_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; 
lean_inc(v_fst_3657_);
v___x_3662_ = l_Lean_Meta_isExprDefEq(v_fst_3657_, v_snd_3658_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; uint8_t v___x_3664_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v___x_3664_ = lean_unbox(v_a_3663_);
lean_dec(v_a_3663_);
if (v___x_3664_ == 0)
{
lean_del_object(v___x_3660_);
lean_dec(v_fst_3657_);
lean_del_object(v___x_3654_);
v___y_3557_ = v___y_3603_;
v___y_3558_ = v___y_3604_;
v___y_3559_ = v___y_3605_;
v___y_3560_ = v___y_3606_;
goto v___jp_3556_;
}
else
{
lean_object* v___x_3665_; 
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec_ref(v_config_3140_);
lean_inc(v_mvarId_3141_);
v___x_3665_ = l_Lean_MVarId_getType(v_mvarId_3141_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3665_) == 0)
{
lean_object* v_a_3666_; lean_object* v___x_3667_; 
v_a_3666_ = lean_ctor_get(v___x_3665_, 0);
lean_inc(v_a_3666_);
lean_dec_ref_known(v___x_3665_, 1);
v___x_3667_ = l_Lean_Meta_mkEqRefl(v_fst_3657_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3667_) == 0)
{
lean_object* v_a_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; 
v_a_3668_ = lean_ctor_get(v___x_3667_, 0);
lean_inc(v_a_3668_);
lean_dec_ref_known(v___x_3667_, 1);
v___x_3669_ = l_Lean_LocalDecl_toExpr(v_val_3172_);
v___x_3670_ = l_Lean_Meta_mkAbsurd(v_a_3666_, v_a_3668_, v___x_3669_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3670_) == 0)
{
lean_object* v_a_3671_; lean_object* v___x_3672_; 
v_a_3671_ = lean_ctor_get(v___x_3670_, 0);
lean_inc(v_a_3671_);
lean_dec_ref_known(v___x_3670_, 1);
v___x_3672_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3141_, v_a_3671_, v___y_3604_);
if (lean_obj_tag(v___x_3672_) == 0)
{
lean_object* v___x_3673_; lean_object* v___x_3675_; 
lean_dec_ref_known(v___x_3672_, 1);
v___x_3673_ = lean_box(v___x_3151_);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v___x_3673_);
v___x_3675_ = v___x_3654_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3680_; 
v_reuseFailAlloc_3680_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3680_, 0, v___x_3673_);
v___x_3675_ = v_reuseFailAlloc_3680_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
lean_object* v___x_3677_; 
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 1, v___x_3176_);
lean_ctor_set(v___x_3660_, 0, v___x_3675_);
v___x_3677_ = v___x_3660_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3675_);
lean_ctor_set(v_reuseFailAlloc_3679_, 1, v___x_3176_);
v___x_3677_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
lean_object* v___x_3678_; 
v___x_3678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3677_);
v_a_3158_ = v___x_3678_;
goto v___jp_3157_;
}
}
}
else
{
lean_object* v_a_3681_; lean_object* v___x_3683_; uint8_t v_isShared_3684_; uint8_t v_isSharedCheck_3688_; 
lean_del_object(v___x_3660_);
lean_del_object(v___x_3654_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
v_a_3681_ = lean_ctor_get(v___x_3672_, 0);
v_isSharedCheck_3688_ = !lean_is_exclusive(v___x_3672_);
if (v_isSharedCheck_3688_ == 0)
{
v___x_3683_ = v___x_3672_;
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
else
{
lean_inc(v_a_3681_);
lean_dec(v___x_3672_);
v___x_3683_ = lean_box(0);
v_isShared_3684_ = v_isSharedCheck_3688_;
goto v_resetjp_3682_;
}
v_resetjp_3682_:
{
lean_object* v___x_3686_; 
if (v_isShared_3684_ == 0)
{
v___x_3686_ = v___x_3683_;
goto v_reusejp_3685_;
}
else
{
lean_object* v_reuseFailAlloc_3687_; 
v_reuseFailAlloc_3687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3687_, 0, v_a_3681_);
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
else
{
lean_object* v_a_3689_; lean_object* v___x_3691_; uint8_t v_isShared_3692_; uint8_t v_isSharedCheck_3696_; 
lean_del_object(v___x_3660_);
lean_del_object(v___x_3654_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3689_ = lean_ctor_get(v___x_3670_, 0);
v_isSharedCheck_3696_ = !lean_is_exclusive(v___x_3670_);
if (v_isSharedCheck_3696_ == 0)
{
v___x_3691_ = v___x_3670_;
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
else
{
lean_inc(v_a_3689_);
lean_dec(v___x_3670_);
v___x_3691_ = lean_box(0);
v_isShared_3692_ = v_isSharedCheck_3696_;
goto v_resetjp_3690_;
}
v_resetjp_3690_:
{
lean_object* v___x_3694_; 
if (v_isShared_3692_ == 0)
{
v___x_3694_ = v___x_3691_;
goto v_reusejp_3693_;
}
else
{
lean_object* v_reuseFailAlloc_3695_; 
v_reuseFailAlloc_3695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3695_, 0, v_a_3689_);
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
else
{
lean_object* v_a_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3704_; 
lean_dec(v_a_3666_);
lean_del_object(v___x_3660_);
lean_del_object(v___x_3654_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3697_ = lean_ctor_get(v___x_3667_, 0);
v_isSharedCheck_3704_ = !lean_is_exclusive(v___x_3667_);
if (v_isSharedCheck_3704_ == 0)
{
v___x_3699_ = v___x_3667_;
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_a_3697_);
lean_dec(v___x_3667_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3704_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v___x_3702_; 
if (v_isShared_3700_ == 0)
{
v___x_3702_ = v___x_3699_;
goto v_reusejp_3701_;
}
else
{
lean_object* v_reuseFailAlloc_3703_; 
v_reuseFailAlloc_3703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3703_, 0, v_a_3697_);
v___x_3702_ = v_reuseFailAlloc_3703_;
goto v_reusejp_3701_;
}
v_reusejp_3701_:
{
return v___x_3702_;
}
}
}
}
else
{
lean_object* v_a_3705_; lean_object* v___x_3707_; uint8_t v_isShared_3708_; uint8_t v_isSharedCheck_3712_; 
lean_del_object(v___x_3660_);
lean_dec(v_fst_3657_);
lean_del_object(v___x_3654_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3705_ = lean_ctor_get(v___x_3665_, 0);
v_isSharedCheck_3712_ = !lean_is_exclusive(v___x_3665_);
if (v_isSharedCheck_3712_ == 0)
{
v___x_3707_ = v___x_3665_;
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
else
{
lean_inc(v_a_3705_);
lean_dec(v___x_3665_);
v___x_3707_ = lean_box(0);
v_isShared_3708_ = v_isSharedCheck_3712_;
goto v_resetjp_3706_;
}
v_resetjp_3706_:
{
lean_object* v___x_3710_; 
if (v_isShared_3708_ == 0)
{
v___x_3710_ = v___x_3707_;
goto v_reusejp_3709_;
}
else
{
lean_object* v_reuseFailAlloc_3711_; 
v_reuseFailAlloc_3711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3711_, 0, v_a_3705_);
v___x_3710_ = v_reuseFailAlloc_3711_;
goto v_reusejp_3709_;
}
v_reusejp_3709_:
{
return v___x_3710_;
}
}
}
}
}
else
{
lean_object* v_a_3713_; lean_object* v___x_3715_; uint8_t v_isShared_3716_; uint8_t v_isSharedCheck_3720_; 
lean_del_object(v___x_3660_);
lean_dec(v_fst_3657_);
lean_del_object(v___x_3654_);
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3713_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3715_ = v___x_3662_;
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
else
{
lean_inc(v_a_3713_);
lean_dec(v___x_3662_);
v___x_3715_ = lean_box(0);
v_isShared_3716_ = v_isSharedCheck_3720_;
goto v_resetjp_3714_;
}
v_resetjp_3714_:
{
lean_object* v___x_3718_; 
if (v_isShared_3716_ == 0)
{
v___x_3718_ = v___x_3715_;
goto v_reusejp_3717_;
}
else
{
lean_object* v_reuseFailAlloc_3719_; 
v_reuseFailAlloc_3719_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3719_, 0, v_a_3713_);
v___x_3718_ = v_reuseFailAlloc_3719_;
goto v_reusejp_3717_;
}
v_reusejp_3717_:
{
return v___x_3718_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3651_);
v___y_3557_ = v___y_3603_;
v___y_3558_ = v___y_3604_;
v___y_3559_ = v___y_3605_;
v___y_3560_ = v___y_3606_;
goto v___jp_3556_;
}
}
else
{
lean_object* v_a_3723_; lean_object* v___x_3725_; uint8_t v_isShared_3726_; uint8_t v_isSharedCheck_3730_; 
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3723_ = lean_ctor_get(v___x_3650_, 0);
v_isSharedCheck_3730_ = !lean_is_exclusive(v___x_3650_);
if (v_isSharedCheck_3730_ == 0)
{
v___x_3725_ = v___x_3650_;
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
else
{
lean_inc(v_a_3723_);
lean_dec(v___x_3650_);
v___x_3725_ = lean_box(0);
v_isShared_3726_ = v_isSharedCheck_3730_;
goto v_resetjp_3724_;
}
v_resetjp_3724_:
{
lean_object* v___x_3728_; 
if (v_isShared_3726_ == 0)
{
v___x_3728_ = v___x_3725_;
goto v_reusejp_3727_;
}
else
{
lean_object* v_reuseFailAlloc_3729_; 
v_reuseFailAlloc_3729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3723_);
v___x_3728_ = v_reuseFailAlloc_3729_;
goto v_reusejp_3727_;
}
v_reusejp_3727_:
{
return v___x_3728_;
}
}
}
}
}
else
{
lean_object* v_a_3731_; lean_object* v___x_3733_; uint8_t v_isShared_3734_; uint8_t v_isSharedCheck_3738_; 
lean_dec_ref(v___x_3292_);
lean_del_object(v___x_3174_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3731_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3738_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3738_ == 0)
{
v___x_3733_ = v___x_3607_;
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
else
{
lean_inc(v_a_3731_);
lean_dec(v___x_3607_);
v___x_3733_ = lean_box(0);
v_isShared_3734_ = v_isSharedCheck_3738_;
goto v_resetjp_3732_;
}
v_resetjp_3732_:
{
lean_object* v___x_3736_; 
if (v_isShared_3734_ == 0)
{
v___x_3736_ = v___x_3733_;
goto v_reusejp_3735_;
}
else
{
lean_object* v_reuseFailAlloc_3737_; 
v_reuseFailAlloc_3737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3737_, 0, v_a_3731_);
v___x_3736_ = v_reuseFailAlloc_3737_;
goto v_reusejp_3735_;
}
v_reusejp_3735_:
{
return v___x_3736_;
}
}
}
}
}
else
{
lean_del_object(v___x_3174_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
v_a_3166_ = v___x_3218_;
goto v___jp_3165_;
}
v___jp_3177_:
{
lean_object* v___x_3182_; 
lean_inc(v_mvarId_3141_);
v___x_3182_ = l_Lean_MVarId_getType(v_mvarId_3141_, v___y_3181_, v___y_3180_, v___y_3179_, v___y_3178_);
if (lean_obj_tag(v___x_3182_) == 0)
{
lean_object* v_a_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v_a_3183_ = lean_ctor_get(v___x_3182_, 0);
lean_inc(v_a_3183_);
lean_dec_ref_known(v___x_3182_, 1);
v___x_3184_ = l_Lean_LocalDecl_toExpr(v_val_3172_);
v___x_3185_ = l_Lean_Meta_mkNoConfusion(v_a_3183_, v___x_3184_, v___y_3181_, v___y_3180_, v___y_3179_, v___y_3178_);
if (lean_obj_tag(v___x_3185_) == 0)
{
lean_object* v_a_3186_; lean_object* v___x_3187_; 
v_a_3186_ = lean_ctor_get(v___x_3185_, 0);
lean_inc(v_a_3186_);
lean_dec_ref_known(v___x_3185_, 1);
v___x_3187_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3141_, v_a_3186_, v___y_3180_);
if (lean_obj_tag(v___x_3187_) == 0)
{
lean_object* v___x_3188_; lean_object* v___x_3190_; 
lean_dec_ref_known(v___x_3187_, 1);
v___x_3188_ = lean_box(v___x_3151_);
if (v_isShared_3175_ == 0)
{
lean_ctor_set(v___x_3174_, 0, v___x_3188_);
v___x_3190_ = v___x_3174_;
goto v_reusejp_3189_;
}
else
{
lean_object* v_reuseFailAlloc_3193_; 
v_reuseFailAlloc_3193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3193_, 0, v___x_3188_);
v___x_3190_ = v_reuseFailAlloc_3193_;
goto v_reusejp_3189_;
}
v_reusejp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v___x_3176_);
v___x_3192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
v_a_3158_ = v___x_3192_;
goto v___jp_3157_;
}
}
else
{
lean_object* v_a_3194_; lean_object* v___x_3196_; uint8_t v_isShared_3197_; uint8_t v_isSharedCheck_3201_; 
lean_del_object(v___x_3174_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
v_a_3194_ = lean_ctor_get(v___x_3187_, 0);
v_isSharedCheck_3201_ = !lean_is_exclusive(v___x_3187_);
if (v_isSharedCheck_3201_ == 0)
{
v___x_3196_ = v___x_3187_;
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
else
{
lean_inc(v_a_3194_);
lean_dec(v___x_3187_);
v___x_3196_ = lean_box(0);
v_isShared_3197_ = v_isSharedCheck_3201_;
goto v_resetjp_3195_;
}
v_resetjp_3195_:
{
lean_object* v___x_3199_; 
if (v_isShared_3197_ == 0)
{
v___x_3199_ = v___x_3196_;
goto v_reusejp_3198_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_a_3194_);
v___x_3199_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3198_;
}
v_reusejp_3198_:
{
return v___x_3199_;
}
}
}
}
else
{
lean_object* v_a_3202_; lean_object* v___x_3204_; uint8_t v_isShared_3205_; uint8_t v_isSharedCheck_3209_; 
lean_del_object(v___x_3174_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3202_ = lean_ctor_get(v___x_3185_, 0);
v_isSharedCheck_3209_ = !lean_is_exclusive(v___x_3185_);
if (v_isSharedCheck_3209_ == 0)
{
v___x_3204_ = v___x_3185_;
v_isShared_3205_ = v_isSharedCheck_3209_;
goto v_resetjp_3203_;
}
else
{
lean_inc(v_a_3202_);
lean_dec(v___x_3185_);
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
else
{
lean_object* v_a_3210_; lean_object* v___x_3212_; uint8_t v_isShared_3213_; uint8_t v_isSharedCheck_3217_; 
lean_del_object(v___x_3174_);
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
v_a_3210_ = lean_ctor_get(v___x_3182_, 0);
v_isSharedCheck_3217_ = !lean_is_exclusive(v___x_3182_);
if (v_isSharedCheck_3217_ == 0)
{
v___x_3212_ = v___x_3182_;
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
else
{
lean_inc(v_a_3210_);
lean_dec(v___x_3182_);
v___x_3212_ = lean_box(0);
v_isShared_3213_ = v_isSharedCheck_3217_;
goto v_resetjp_3211_;
}
v_resetjp_3211_:
{
lean_object* v___x_3215_; 
if (v_isShared_3213_ == 0)
{
v___x_3215_ = v___x_3212_;
goto v_reusejp_3214_;
}
else
{
lean_object* v_reuseFailAlloc_3216_; 
v_reuseFailAlloc_3216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3216_, 0, v_a_3210_);
v___x_3215_ = v_reuseFailAlloc_3216_;
goto v_reusejp_3214_;
}
v_reusejp_3214_:
{
return v___x_3215_;
}
}
}
}
v___jp_3219_:
{
lean_object* v_searchFuel_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; 
v_searchFuel_3224_ = lean_ctor_get(v_config_3140_, 0);
v___x_3225_ = l_Lean_LocalDecl_fvarId(v_val_3172_);
lean_dec(v_val_3172_);
lean_inc(v_searchFuel_3224_);
lean_inc(v_mvarId_3141_);
v___x_3226_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3141_, v___x_3225_, v_searchFuel_3224_, v___y_3221_, v___y_3222_, v___y_3220_, v___y_3223_);
if (lean_obj_tag(v___x_3226_) == 0)
{
lean_object* v_a_3227_; uint8_t v___x_3228_; 
v_a_3227_ = lean_ctor_get(v___x_3226_, 0);
lean_inc(v_a_3227_);
lean_dec_ref_known(v___x_3226_, 1);
v___x_3228_ = lean_unbox(v_a_3227_);
lean_dec(v_a_3227_);
if (v___x_3228_ == 0)
{
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
v_a_3166_ = v___x_3218_;
goto v___jp_3165_;
}
else
{
lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; 
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v___x_3229_ = lean_box(v___x_3151_);
v___x_3230_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3230_, 0, v___x_3229_);
v___x_3231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3231_, 0, v___x_3230_);
lean_ctor_set(v___x_3231_, 1, v___x_3176_);
v___x_3232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3232_, 0, v___x_3231_);
v_a_3158_ = v___x_3232_;
goto v___jp_3157_;
}
}
else
{
lean_object* v_a_3233_; lean_object* v___x_3235_; uint8_t v_isShared_3236_; uint8_t v_isSharedCheck_3240_; 
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3233_ = lean_ctor_get(v___x_3226_, 0);
v_isSharedCheck_3240_ = !lean_is_exclusive(v___x_3226_);
if (v_isSharedCheck_3240_ == 0)
{
v___x_3235_ = v___x_3226_;
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
else
{
lean_inc(v_a_3233_);
lean_dec(v___x_3226_);
v___x_3235_ = lean_box(0);
v_isShared_3236_ = v_isSharedCheck_3240_;
goto v_resetjp_3234_;
}
v_resetjp_3234_:
{
lean_object* v___x_3238_; 
if (v_isShared_3236_ == 0)
{
v___x_3238_ = v___x_3235_;
goto v_reusejp_3237_;
}
else
{
lean_object* v_reuseFailAlloc_3239_; 
v_reuseFailAlloc_3239_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3239_, 0, v_a_3233_);
v___x_3238_ = v_reuseFailAlloc_3239_;
goto v_reusejp_3237_;
}
v_reusejp_3237_:
{
return v___x_3238_;
}
}
}
}
v___jp_3241_:
{
if (v___y_3246_ == 0)
{
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
v_a_3166_ = v___x_3218_;
goto v___jp_3165_;
}
else
{
v___y_3220_ = v___y_3243_;
v___y_3221_ = v___y_3242_;
v___y_3222_ = v___y_3244_;
v___y_3223_ = v___y_3245_;
goto v___jp_3219_;
}
}
v___jp_3248_:
{
if (v___y_3251_ == 0)
{
v___y_3220_ = v___y_3250_;
v___y_3221_ = v___y_3249_;
v___y_3222_ = v___y_3252_;
v___y_3223_ = v___y_3253_;
goto v___jp_3219_;
}
else
{
v___y_3242_ = v___y_3249_;
v___y_3243_ = v___y_3250_;
v___y_3244_ = v___y_3252_;
v___y_3245_ = v___y_3253_;
v___y_3246_ = v___x_3247_;
goto v___jp_3241_;
}
}
v___jp_3254_:
{
if (v___y_3260_ == 0)
{
v___y_3242_ = v___y_3256_;
v___y_3243_ = v___y_3255_;
v___y_3244_ = v___y_3258_;
v___y_3245_ = v___y_3259_;
v___y_3246_ = v___x_3247_;
goto v___jp_3241_;
}
else
{
v___y_3249_ = v___y_3256_;
v___y_3250_ = v___y_3255_;
v___y_3251_ = v___y_3257_;
v___y_3252_ = v___y_3258_;
v___y_3253_ = v___y_3259_;
goto v___jp_3248_;
}
}
v___jp_3261_:
{
uint8_t v_emptyType_3268_; 
v_emptyType_3268_ = lean_ctor_get_uint8(v_config_3140_, sizeof(void*)*1 + 1);
if (v_emptyType_3268_ == 0)
{
v___y_3255_ = v___y_3266_;
v___y_3256_ = v___y_3264_;
v___y_3257_ = v___y_3262_;
v___y_3258_ = v___y_3265_;
v___y_3259_ = v___y_3267_;
v___y_3260_ = v___x_3247_;
goto v___jp_3254_;
}
else
{
if (v___y_3263_ == 0)
{
v___y_3249_ = v___y_3264_;
v___y_3250_ = v___y_3266_;
v___y_3251_ = v___y_3262_;
v___y_3252_ = v___y_3265_;
v___y_3253_ = v___y_3267_;
goto v___jp_3248_;
}
else
{
v___y_3255_ = v___y_3266_;
v___y_3256_ = v___y_3264_;
v___y_3257_ = v___y_3262_;
v___y_3258_ = v___y_3265_;
v___y_3259_ = v___y_3267_;
v___y_3260_ = v___x_3247_;
goto v___jp_3254_;
}
}
}
v___jp_3269_:
{
if (v___y_3276_ == 0)
{
v___y_3262_ = v___y_3271_;
v___y_3263_ = v___y_3275_;
v___y_3264_ = v___y_3270_;
v___y_3265_ = v___y_3274_;
v___y_3266_ = v___y_3273_;
v___y_3267_ = v___y_3272_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3277_; 
lean_inc(v_val_3172_);
lean_inc(v_mvarId_3141_);
v___x_3277_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3141_, v_val_3172_, v___y_3270_, v___y_3274_, v___y_3273_, v___y_3272_);
if (lean_obj_tag(v___x_3277_) == 0)
{
lean_object* v_a_3278_; uint8_t v___x_3279_; 
v_a_3278_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_a_3278_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3279_ = lean_unbox(v_a_3278_);
lean_dec(v_a_3278_);
if (v___x_3279_ == 0)
{
v___y_3262_ = v___y_3271_;
v___y_3263_ = v___y_3275_;
v___y_3264_ = v___y_3270_;
v___y_3265_ = v___y_3274_;
v___y_3266_ = v___y_3273_;
v___y_3267_ = v___y_3272_;
goto v___jp_3261_;
}
else
{
lean_object* v___x_3280_; lean_object* v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
lean_dec(v_val_3172_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v___x_3280_ = lean_box(v___x_3151_);
v___x_3281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3281_, 0, v___x_3280_);
v___x_3282_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3282_, 0, v___x_3281_);
lean_ctor_set(v___x_3282_, 1, v___x_3176_);
v___x_3283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3283_, 0, v___x_3282_);
v_a_3158_ = v___x_3283_;
goto v___jp_3157_;
}
}
else
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
lean_dec(v_val_3172_);
lean_del_object(v___x_3155_);
lean_dec(v_snd_3153_);
lean_dec(v_mvarId_3141_);
lean_dec_ref(v_config_3140_);
v_a_3284_ = lean_ctor_get(v___x_3277_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3277_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3277_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3277_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
}
}
}
}
v___jp_3157_:
{
lean_object* v___x_3159_; lean_object* v___x_3161_; 
v___x_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3159_, 0, v_a_3158_);
if (v_isShared_3156_ == 0)
{
lean_ctor_set(v___x_3155_, 0, v___x_3159_);
v___x_3161_ = v___x_3155_;
goto v_reusejp_3160_;
}
else
{
lean_object* v_reuseFailAlloc_3163_; 
v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3159_);
lean_ctor_set(v_reuseFailAlloc_3163_, 1, v_snd_3153_);
v___x_3161_ = v_reuseFailAlloc_3163_;
goto v_reusejp_3160_;
}
v_reusejp_3160_:
{
lean_object* v___x_3162_; 
v___x_3162_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3162_, 0, v___x_3161_);
return v___x_3162_;
}
}
v___jp_3165_:
{
lean_object* v___x_3167_; size_t v___x_3168_; size_t v___x_3169_; 
v___x_3167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3167_, 0, v___x_3164_);
lean_ctor_set(v___x_3167_, 1, v_a_3166_);
v___x_3168_ = ((size_t)1ULL);
v___x_3169_ = lean_usize_add(v_i_3144_, v___x_3168_);
v_i_3144_ = v___x_3169_;
v_b_3145_ = v___x_3167_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3812_, lean_object* v_mvarId_3813_, lean_object* v_as_3814_, lean_object* v_sz_3815_, lean_object* v_i_3816_, lean_object* v_b_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_, lean_object* v___y_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_){
_start:
{
size_t v_sz_boxed_3823_; size_t v_i_boxed_3824_; lean_object* v_res_3825_; 
v_sz_boxed_3823_ = lean_unbox_usize(v_sz_3815_);
lean_dec(v_sz_3815_);
v_i_boxed_3824_ = lean_unbox_usize(v_i_3816_);
lean_dec(v_i_3816_);
v_res_3825_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3812_, v_mvarId_3813_, v_as_3814_, v_sz_boxed_3823_, v_i_boxed_3824_, v_b_3817_, v___y_3818_, v___y_3819_, v___y_3820_, v___y_3821_);
lean_dec(v___y_3821_);
lean_dec_ref(v___y_3820_);
lean_dec(v___y_3819_);
lean_dec_ref(v___y_3818_);
lean_dec_ref(v_as_3814_);
return v_res_3825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3826_, lean_object* v_mvarId_3827_, lean_object* v_as_3828_, size_t v_sz_3829_, size_t v_i_3830_, lean_object* v_b_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_){
_start:
{
uint8_t v___x_3837_; 
v___x_3837_ = lean_usize_dec_lt(v_i_3830_, v_sz_3829_);
if (v___x_3837_ == 0)
{
lean_object* v___x_3838_; 
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v___x_3838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3838_, 0, v_b_3831_);
return v___x_3838_;
}
else
{
lean_object* v_snd_3839_; lean_object* v___x_3841_; uint8_t v_isShared_3842_; uint8_t v_isSharedCheck_4496_; 
v_snd_3839_ = lean_ctor_get(v_b_3831_, 1);
v_isSharedCheck_4496_ = !lean_is_exclusive(v_b_3831_);
if (v_isSharedCheck_4496_ == 0)
{
lean_object* v_unused_4497_; 
v_unused_4497_ = lean_ctor_get(v_b_3831_, 0);
lean_dec(v_unused_4497_);
v___x_3841_ = v_b_3831_;
v_isShared_3842_ = v_isSharedCheck_4496_;
goto v_resetjp_3840_;
}
else
{
lean_inc(v_snd_3839_);
lean_dec(v_b_3831_);
v___x_3841_ = lean_box(0);
v_isShared_3842_ = v_isSharedCheck_4496_;
goto v_resetjp_3840_;
}
v_resetjp_3840_:
{
lean_object* v_a_3844_; lean_object* v___x_3850_; lean_object* v_a_3852_; lean_object* v_a_3857_; 
v___x_3850_ = lean_box(0);
v_a_3857_ = lean_array_uget(v_as_3828_, v_i_3830_);
if (lean_obj_tag(v_a_3857_) == 0)
{
lean_del_object(v___x_3841_);
v_a_3852_ = v_snd_3839_;
goto v___jp_3851_;
}
else
{
lean_object* v_val_3858_; lean_object* v___x_3860_; uint8_t v_isShared_3861_; uint8_t v_isSharedCheck_4495_; 
v_val_3858_ = lean_ctor_get(v_a_3857_, 0);
v_isSharedCheck_4495_ = !lean_is_exclusive(v_a_3857_);
if (v_isSharedCheck_4495_ == 0)
{
v___x_3860_ = v_a_3857_;
v_isShared_3861_ = v_isSharedCheck_4495_;
goto v_resetjp_3859_;
}
else
{
lean_inc(v_val_3858_);
lean_dec(v_a_3857_);
v___x_3860_ = lean_box(0);
v_isShared_3861_ = v_isSharedCheck_4495_;
goto v_resetjp_3859_;
}
v_resetjp_3859_:
{
lean_object* v___x_3862_; lean_object* v___y_3864_; lean_object* v___y_3865_; lean_object* v___y_3866_; lean_object* v___y_3867_; lean_object* v___x_3904_; lean_object* v___y_3906_; lean_object* v___y_3907_; lean_object* v___y_3908_; lean_object* v___y_3909_; lean_object* v___y_3928_; lean_object* v___y_3929_; lean_object* v___y_3930_; lean_object* v___y_3931_; uint8_t v___y_3932_; uint8_t v___x_3933_; lean_object* v___y_3935_; lean_object* v___y_3936_; lean_object* v___y_3937_; lean_object* v___y_3938_; uint8_t v___y_3939_; lean_object* v___y_3941_; lean_object* v___y_3942_; lean_object* v___y_3943_; lean_object* v___y_3944_; uint8_t v___y_3945_; uint8_t v___y_3946_; uint8_t v___y_3948_; uint8_t v___y_3949_; lean_object* v___y_3950_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; uint8_t v___y_3956_; lean_object* v___y_3957_; lean_object* v___y_3958_; lean_object* v___y_3959_; lean_object* v___y_3960_; uint8_t v___y_3961_; uint8_t v___y_3962_; 
v___x_3862_ = lean_box(0);
v___x_3904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3933_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3858_);
if (v___x_3933_ == 0)
{
lean_object* v___x_3978_; uint8_t v___y_3980_; uint8_t v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3985_; uint8_t v___y_3989_; lean_object* v___y_3990_; lean_object* v___y_3991_; lean_object* v___y_3992_; lean_object* v___y_3993_; uint8_t v___y_3994_; lean_object* v___y_3995_; uint8_t v___y_3996_; uint8_t v___y_3999_; lean_object* v___y_4000_; lean_object* v___y_4001_; lean_object* v___y_4002_; uint8_t v___y_4003_; lean_object* v___y_4004_; lean_object* v_a_4005_; uint8_t v___y_4009_; lean_object* v___y_4010_; lean_object* v___y_4011_; lean_object* v___y_4012_; uint8_t v___y_4013_; lean_object* v___y_4014_; uint8_t v___y_4076_; lean_object* v___y_4077_; lean_object* v___y_4078_; lean_object* v___y_4079_; uint8_t v___y_4080_; lean_object* v___y_4081_; uint8_t v___y_4082_; lean_object* v___y_4084_; uint8_t v___y_4085_; lean_object* v___y_4086_; lean_object* v___y_4087_; lean_object* v___y_4088_; uint8_t v___y_4089_; lean_object* v___y_4090_; uint8_t v___y_4091_; uint8_t v___y_4094_; lean_object* v___y_4095_; lean_object* v___y_4096_; lean_object* v___y_4097_; uint8_t v___y_4098_; lean_object* v___y_4099_; uint8_t v___y_4100_; uint8_t v___y_4113_; lean_object* v___y_4114_; lean_object* v___y_4115_; lean_object* v___y_4116_; uint8_t v___y_4117_; lean_object* v___y_4118_; uint8_t v___y_4119_; uint8_t v___y_4121_; uint8_t v_isHEq_4122_; lean_object* v___y_4123_; lean_object* v___y_4124_; lean_object* v___y_4125_; lean_object* v___y_4126_; uint8_t v___y_4130_; lean_object* v___y_4131_; lean_object* v___y_4132_; lean_object* v___y_4133_; lean_object* v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; uint8_t v_isEq_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; lean_object* v___y_4196_; lean_object* v___y_4197_; lean_object* v___y_4243_; lean_object* v___y_4244_; lean_object* v___y_4245_; lean_object* v___y_4246_; lean_object* v___y_4289_; lean_object* v___y_4290_; lean_object* v___y_4291_; lean_object* v___y_4292_; lean_object* v___x_4425_; 
v___x_3978_ = l_Lean_LocalDecl_type(v_val_3858_);
lean_inc_ref(v___x_3978_);
v___x_4425_ = l_Lean_Meta_matchNot_x3f(v___x_3978_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref_known(v___x_4425_, 1);
if (lean_obj_tag(v_a_4426_) == 1)
{
lean_object* v_val_4427_; lean_object* v___x_4429_; uint8_t v_isShared_4430_; uint8_t v_isSharedCheck_4486_; 
v_val_4427_ = lean_ctor_get(v_a_4426_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v_a_4426_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4429_ = v_a_4426_;
v_isShared_4430_ = v_isSharedCheck_4486_;
goto v_resetjp_4428_;
}
else
{
lean_inc(v_val_4427_);
lean_dec(v_a_4426_);
v___x_4429_ = lean_box(0);
v_isShared_4430_ = v_isSharedCheck_4486_;
goto v_resetjp_4428_;
}
v_resetjp_4428_:
{
lean_object* v___x_4431_; 
v___x_4431_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4427_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_4431_) == 0)
{
lean_object* v_a_4432_; 
v_a_4432_ = lean_ctor_get(v___x_4431_, 0);
lean_inc(v_a_4432_);
lean_dec_ref_known(v___x_4431_, 1);
if (lean_obj_tag(v_a_4432_) == 1)
{
lean_object* v_val_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4477_; 
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec_ref(v_config_3826_);
v_val_4433_ = lean_ctor_get(v_a_4432_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v_a_4432_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4435_ = v_a_4432_;
v_isShared_4436_ = v_isSharedCheck_4477_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_val_4433_);
lean_dec(v_a_4432_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4477_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4437_; 
lean_inc(v_mvarId_3827_);
v___x_4437_ = l_Lean_MVarId_getType(v_mvarId_3827_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_4437_) == 0)
{
lean_object* v_a_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; 
v_a_4438_ = lean_ctor_get(v___x_4437_, 0);
lean_inc(v_a_4438_);
lean_dec_ref_known(v___x_4437_, 1);
v___x_4439_ = l_Lean_LocalDecl_toExpr(v_val_3858_);
v___x_4440_ = l_Lean_mkFVar(v_val_4433_);
v___x_4441_ = l_Lean_Expr_app___override(v___x_4439_, v___x_4440_);
v___x_4442_ = l_Lean_Meta_mkFalseElim(v_a_4438_, v___x_4441_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v_a_4443_; lean_object* v___x_4444_; 
v_a_4443_ = lean_ctor_get(v___x_4442_, 0);
lean_inc(v_a_4443_);
lean_dec_ref_known(v___x_4442_, 1);
v___x_4444_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3827_, v_a_4443_, v___y_3833_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v___x_4445_; lean_object* v___x_4447_; 
lean_dec_ref_known(v___x_4444_, 1);
v___x_4445_ = lean_box(v___x_3837_);
if (v_isShared_4436_ == 0)
{
lean_ctor_set(v___x_4435_, 0, v___x_4445_);
v___x_4447_ = v___x_4435_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v___x_4445_);
v___x_4447_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
lean_object* v___x_4448_; lean_object* v___x_4450_; 
v___x_4448_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4448_, 0, v___x_4447_);
lean_ctor_set(v___x_4448_, 1, v___x_3862_);
if (v_isShared_4430_ == 0)
{
lean_ctor_set_tag(v___x_4429_, 0);
lean_ctor_set(v___x_4429_, 0, v___x_4448_);
v___x_4450_ = v___x_4429_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v___x_4448_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
v_a_3844_ = v___x_4450_;
goto v___jp_3843_;
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_del_object(v___x_4435_);
lean_del_object(v___x_4429_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
v_a_4453_ = lean_ctor_get(v___x_4444_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4444_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4444_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4444_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_del_object(v___x_4435_);
lean_del_object(v___x_4429_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_4461_ = lean_ctor_get(v___x_4442_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4442_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4442_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4442_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
else
{
lean_object* v_a_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4476_; 
lean_del_object(v___x_4435_);
lean_dec(v_val_4433_);
lean_del_object(v___x_4429_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_4469_ = lean_ctor_get(v___x_4437_, 0);
v_isSharedCheck_4476_ = !lean_is_exclusive(v___x_4437_);
if (v_isSharedCheck_4476_ == 0)
{
v___x_4471_ = v___x_4437_;
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_a_4469_);
lean_dec(v___x_4437_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4476_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4474_; 
if (v_isShared_4472_ == 0)
{
v___x_4474_ = v___x_4471_;
goto v_reusejp_4473_;
}
else
{
lean_object* v_reuseFailAlloc_4475_; 
v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
v___x_4474_ = v_reuseFailAlloc_4475_;
goto v_reusejp_4473_;
}
v_reusejp_4473_:
{
return v___x_4474_;
}
}
}
}
}
else
{
lean_dec(v_a_4432_);
lean_del_object(v___x_4429_);
v___y_4289_ = v___y_3832_;
v___y_4290_ = v___y_3833_;
v___y_4291_ = v___y_3834_;
v___y_4292_ = v___y_3835_;
goto v___jp_4288_;
}
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_del_object(v___x_4429_);
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4478_ = lean_ctor_get(v___x_4431_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4431_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4431_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4431_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
}
else
{
lean_dec(v_a_4426_);
v___y_4289_ = v___y_3832_;
v___y_4290_ = v___y_3833_;
v___y_4291_ = v___y_3834_;
v___y_4292_ = v___y_3835_;
goto v___jp_4288_;
}
}
else
{
lean_object* v_a_4487_; lean_object* v___x_4489_; uint8_t v_isShared_4490_; uint8_t v_isSharedCheck_4494_; 
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4487_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4494_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4494_ == 0)
{
v___x_4489_ = v___x_4425_;
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
else
{
lean_inc(v_a_4487_);
lean_dec(v___x_4425_);
v___x_4489_ = lean_box(0);
v_isShared_4490_ = v_isSharedCheck_4494_;
goto v_resetjp_4488_;
}
v_resetjp_4488_:
{
lean_object* v___x_4492_; 
if (v_isShared_4490_ == 0)
{
v___x_4492_ = v___x_4489_;
goto v_reusejp_4491_;
}
else
{
lean_object* v_reuseFailAlloc_4493_; 
v_reuseFailAlloc_4493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4493_, 0, v_a_4487_);
v___x_4492_ = v_reuseFailAlloc_4493_;
goto v_reusejp_4491_;
}
v_reusejp_4491_:
{
return v___x_4492_;
}
}
}
v___jp_3979_:
{
uint8_t v_genDiseq_3986_; 
v_genDiseq_3986_ = lean_ctor_get_uint8(v_config_3826_, sizeof(void*)*1 + 2);
if (v_genDiseq_3986_ == 0)
{
lean_dec_ref(v___x_3978_);
v___y_3956_ = v___y_3980_;
v___y_3957_ = v___y_3984_;
v___y_3958_ = v___y_3982_;
v___y_3959_ = v___y_3983_;
v___y_3960_ = v___y_3985_;
v___y_3961_ = v___y_3981_;
v___y_3962_ = v___x_3933_;
goto v___jp_3955_;
}
else
{
uint8_t v___x_3987_; 
v___x_3987_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3978_);
v___y_3956_ = v___y_3980_;
v___y_3957_ = v___y_3984_;
v___y_3958_ = v___y_3982_;
v___y_3959_ = v___y_3983_;
v___y_3960_ = v___y_3985_;
v___y_3961_ = v___y_3981_;
v___y_3962_ = v___x_3987_;
goto v___jp_3955_;
}
}
v___jp_3988_:
{
if (v___y_3996_ == 0)
{
lean_dec_ref(v___y_3992_);
v___y_3980_ = v___y_3989_;
v___y_3981_ = v___y_3994_;
v___y_3982_ = v___y_3993_;
v___y_3983_ = v___y_3995_;
v___y_3984_ = v___y_3991_;
v___y_3985_ = v___y_3990_;
goto v___jp_3979_;
}
else
{
lean_object* v___x_3997_; 
lean_dec_ref(v___x_3978_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v___x_3997_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3997_, 0, v___y_3992_);
return v___x_3997_;
}
}
v___jp_3998_:
{
uint8_t v___x_4006_; 
v___x_4006_ = l_Lean_Exception_isInterrupt(v_a_4005_);
if (v___x_4006_ == 0)
{
uint8_t v___x_4007_; 
lean_inc_ref(v_a_4005_);
v___x_4007_ = l_Lean_Exception_isRuntime(v_a_4005_);
v___y_3989_ = v___y_3999_;
v___y_3990_ = v___y_4001_;
v___y_3991_ = v___y_4000_;
v___y_3992_ = v_a_4005_;
v___y_3993_ = v___y_4002_;
v___y_3994_ = v___y_4003_;
v___y_3995_ = v___y_4004_;
v___y_3996_ = v___x_4007_;
goto v___jp_3988_;
}
else
{
v___y_3989_ = v___y_3999_;
v___y_3990_ = v___y_4001_;
v___y_3991_ = v___y_4000_;
v___y_3992_ = v_a_4005_;
v___y_3993_ = v___y_4002_;
v___y_3994_ = v___y_4003_;
v___y_3995_ = v___y_4004_;
v___y_3996_ = v___x_4006_;
goto v___jp_3988_;
}
}
v___jp_4008_:
{
lean_object* v___x_4015_; 
lean_inc_ref(v___x_3978_);
v___x_4015_ = l_Lean_Meta_mkDecide(v___x_3978_, v___y_4012_, v___y_4014_, v___y_4011_, v___y_4010_);
if (lean_obj_tag(v___x_4015_) == 0)
{
lean_object* v_a_4016_; lean_object* v_keyedConfig_4017_; uint8_t v_trackZetaDelta_4018_; lean_object* v_zetaDeltaSet_4019_; lean_object* v_lctx_4020_; lean_object* v_localInstances_4021_; lean_object* v_defEqCtx_x3f_4022_; lean_object* v_synthPendingDepth_4023_; lean_object* v_customCanUnfoldPredicate_x3f_4024_; uint8_t v_univApprox_4025_; uint8_t v_inTypeClassResolution_4026_; uint8_t v_cacheInferType_4027_; uint8_t v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; 
v_a_4016_ = lean_ctor_get(v___x_4015_, 0);
lean_inc_n(v_a_4016_, 2);
lean_dec_ref_known(v___x_4015_, 1);
v_keyedConfig_4017_ = lean_ctor_get(v___y_4012_, 0);
v_trackZetaDelta_4018_ = lean_ctor_get_uint8(v___y_4012_, sizeof(void*)*7);
v_zetaDeltaSet_4019_ = lean_ctor_get(v___y_4012_, 1);
v_lctx_4020_ = lean_ctor_get(v___y_4012_, 2);
v_localInstances_4021_ = lean_ctor_get(v___y_4012_, 3);
v_defEqCtx_x3f_4022_ = lean_ctor_get(v___y_4012_, 4);
v_synthPendingDepth_4023_ = lean_ctor_get(v___y_4012_, 5);
v_customCanUnfoldPredicate_x3f_4024_ = lean_ctor_get(v___y_4012_, 6);
v_univApprox_4025_ = lean_ctor_get_uint8(v___y_4012_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4026_ = lean_ctor_get_uint8(v___y_4012_, sizeof(void*)*7 + 2);
v_cacheInferType_4027_ = lean_ctor_get_uint8(v___y_4012_, sizeof(void*)*7 + 3);
v___x_4028_ = 1;
lean_inc_ref(v_keyedConfig_4017_);
v___x_4029_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4028_, v_keyedConfig_4017_);
lean_inc(v_customCanUnfoldPredicate_x3f_4024_);
lean_inc(v_synthPendingDepth_4023_);
lean_inc(v_defEqCtx_x3f_4022_);
lean_inc_ref(v_localInstances_4021_);
lean_inc_ref(v_lctx_4020_);
lean_inc(v_zetaDeltaSet_4019_);
v___x_4030_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
lean_ctor_set(v___x_4030_, 1, v_zetaDeltaSet_4019_);
lean_ctor_set(v___x_4030_, 2, v_lctx_4020_);
lean_ctor_set(v___x_4030_, 3, v_localInstances_4021_);
lean_ctor_set(v___x_4030_, 4, v_defEqCtx_x3f_4022_);
lean_ctor_set(v___x_4030_, 5, v_synthPendingDepth_4023_);
lean_ctor_set(v___x_4030_, 6, v_customCanUnfoldPredicate_x3f_4024_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*7, v_trackZetaDelta_4018_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*7 + 1, v_univApprox_4025_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4026_);
lean_ctor_set_uint8(v___x_4030_, sizeof(void*)*7 + 3, v_cacheInferType_4027_);
lean_inc(v___y_4010_);
lean_inc_ref(v___y_4011_);
lean_inc(v___y_4014_);
v___x_4031_ = lean_whnf(v_a_4016_, v___x_4030_, v___y_4014_, v___y_4011_, v___y_4010_);
if (lean_obj_tag(v___x_4031_) == 0)
{
lean_object* v_a_4032_; lean_object* v___x_4033_; uint8_t v___x_4034_; 
v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4032_);
lean_dec_ref_known(v___x_4031_, 1);
v___x_4033_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_4034_ = l_Lean_Expr_isConstOf(v_a_4032_, v___x_4033_);
lean_dec(v_a_4032_);
if (v___x_4034_ == 0)
{
lean_dec(v_a_4016_);
v___y_3980_ = v___y_4009_;
v___y_3981_ = v___y_4013_;
v___y_3982_ = v___y_4012_;
v___y_3983_ = v___y_4014_;
v___y_3984_ = v___y_4011_;
v___y_3985_ = v___y_4010_;
goto v___jp_3979_;
}
else
{
lean_object* v___x_4035_; 
lean_inc(v_a_4016_);
v___x_4035_ = l_Lean_Meta_mkEqRefl(v_a_4016_, v___y_4012_, v___y_4014_, v___y_4011_, v___y_4010_);
if (lean_obj_tag(v___x_4035_) == 0)
{
lean_object* v_a_4036_; lean_object* v___x_4037_; 
v_a_4036_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4036_);
lean_dec_ref_known(v___x_4035_, 1);
lean_inc(v_mvarId_3827_);
v___x_4037_ = l_Lean_MVarId_getType(v_mvarId_3827_, v___y_4012_, v___y_4014_, v___y_4011_, v___y_4010_);
if (lean_obj_tag(v___x_4037_) == 0)
{
lean_object* v_a_4038_; lean_object* v_nargs_4039_; lean_object* v___x_4040_; lean_object* v_dummy_4041_; lean_object* v___x_4042_; lean_object* v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; lean_object* v___x_4046_; lean_object* v___x_4047_; lean_object* v___x_4048_; lean_object* v___x_4049_; 
v_a_4038_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4038_);
lean_dec_ref_known(v___x_4037_, 1);
v_nargs_4039_ = l_Lean_Expr_getAppNumArgs(v_a_4016_);
v___x_4040_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_4041_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
lean_inc(v_nargs_4039_);
v___x_4042_ = lean_mk_array(v_nargs_4039_, v_dummy_4041_);
v___x_4043_ = lean_unsigned_to_nat(1u);
v___x_4044_ = lean_nat_sub(v_nargs_4039_, v___x_4043_);
lean_dec(v_nargs_4039_);
v___x_4045_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_4016_, v___x_4042_, v___x_4044_);
v___x_4046_ = lean_array_push(v___x_4045_, v_a_4036_);
v___x_4047_ = l_Lean_mkAppN(v___x_4040_, v___x_4046_);
lean_dec_ref(v___x_4046_);
lean_inc(v_val_3858_);
v___x_4048_ = l_Lean_LocalDecl_toExpr(v_val_3858_);
v___x_4049_ = l_Lean_Meta_mkAbsurd(v_a_4038_, v___x_4048_, v___x_4047_, v___y_4012_, v___y_4014_, v___y_4011_, v___y_4010_);
if (lean_obj_tag(v___x_4049_) == 0)
{
lean_object* v_a_4050_; lean_object* v___x_4052_; uint8_t v_isShared_4053_; uint8_t v_isSharedCheck_4069_; 
v_a_4050_ = lean_ctor_get(v___x_4049_, 0);
v_isSharedCheck_4069_ = !lean_is_exclusive(v___x_4049_);
if (v_isSharedCheck_4069_ == 0)
{
v___x_4052_ = v___x_4049_;
v_isShared_4053_ = v_isSharedCheck_4069_;
goto v_resetjp_4051_;
}
else
{
lean_inc(v_a_4050_);
lean_dec(v___x_4049_);
v___x_4052_ = lean_box(0);
v_isShared_4053_ = v_isSharedCheck_4069_;
goto v_resetjp_4051_;
}
v_resetjp_4051_:
{
lean_object* v___x_4054_; 
lean_inc(v_mvarId_3827_);
v___x_4054_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3827_, v_a_4050_, v___y_4014_);
if (lean_obj_tag(v___x_4054_) == 0)
{
lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4066_; 
lean_dec_ref(v___x_3978_);
lean_dec(v_val_3858_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_isSharedCheck_4066_ = !lean_is_exclusive(v___x_4054_);
if (v_isSharedCheck_4066_ == 0)
{
lean_object* v_unused_4067_; 
v_unused_4067_ = lean_ctor_get(v___x_4054_, 0);
lean_dec(v_unused_4067_);
v___x_4056_ = v___x_4054_;
v_isShared_4057_ = v_isSharedCheck_4066_;
goto v_resetjp_4055_;
}
else
{
lean_dec(v___x_4054_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4066_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4058_; lean_object* v___x_4060_; 
v___x_4058_ = lean_box(v___x_3837_);
if (v_isShared_4057_ == 0)
{
lean_ctor_set_tag(v___x_4056_, 1);
lean_ctor_set(v___x_4056_, 0, v___x_4058_);
v___x_4060_ = v___x_4056_;
goto v_reusejp_4059_;
}
else
{
lean_object* v_reuseFailAlloc_4065_; 
v_reuseFailAlloc_4065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4065_, 0, v___x_4058_);
v___x_4060_ = v_reuseFailAlloc_4065_;
goto v_reusejp_4059_;
}
v_reusejp_4059_:
{
lean_object* v___x_4061_; lean_object* v___x_4063_; 
v___x_4061_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
lean_ctor_set(v___x_4061_, 1, v___x_3862_);
if (v_isShared_4053_ == 0)
{
lean_ctor_set(v___x_4052_, 0, v___x_4061_);
v___x_4063_ = v___x_4052_;
goto v_reusejp_4062_;
}
else
{
lean_object* v_reuseFailAlloc_4064_; 
v_reuseFailAlloc_4064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4064_, 0, v___x_4061_);
v___x_4063_ = v_reuseFailAlloc_4064_;
goto v_reusejp_4062_;
}
v_reusejp_4062_:
{
v_a_3844_ = v___x_4063_;
goto v___jp_3843_;
}
}
}
}
else
{
lean_object* v_a_4068_; 
lean_del_object(v___x_4052_);
v_a_4068_ = lean_ctor_get(v___x_4054_, 0);
lean_inc(v_a_4068_);
lean_dec_ref_known(v___x_4054_, 1);
v___y_3999_ = v___y_4009_;
v___y_4000_ = v___y_4011_;
v___y_4001_ = v___y_4010_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v___y_4004_ = v___y_4014_;
v_a_4005_ = v_a_4068_;
goto v___jp_3998_;
}
}
}
else
{
lean_object* v_a_4070_; 
v_a_4070_ = lean_ctor_get(v___x_4049_, 0);
lean_inc(v_a_4070_);
lean_dec_ref_known(v___x_4049_, 1);
v___y_3999_ = v___y_4009_;
v___y_4000_ = v___y_4011_;
v___y_4001_ = v___y_4010_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v___y_4004_ = v___y_4014_;
v_a_4005_ = v_a_4070_;
goto v___jp_3998_;
}
}
else
{
lean_object* v_a_4071_; 
lean_dec(v_a_4036_);
lean_dec(v_a_4016_);
v_a_4071_ = lean_ctor_get(v___x_4037_, 0);
lean_inc(v_a_4071_);
lean_dec_ref_known(v___x_4037_, 1);
v___y_3999_ = v___y_4009_;
v___y_4000_ = v___y_4011_;
v___y_4001_ = v___y_4010_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v___y_4004_ = v___y_4014_;
v_a_4005_ = v_a_4071_;
goto v___jp_3998_;
}
}
else
{
lean_object* v_a_4072_; 
lean_dec(v_a_4016_);
v_a_4072_ = lean_ctor_get(v___x_4035_, 0);
lean_inc(v_a_4072_);
lean_dec_ref_known(v___x_4035_, 1);
v___y_3999_ = v___y_4009_;
v___y_4000_ = v___y_4011_;
v___y_4001_ = v___y_4010_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v___y_4004_ = v___y_4014_;
v_a_4005_ = v_a_4072_;
goto v___jp_3998_;
}
}
}
else
{
lean_object* v_a_4073_; 
lean_dec(v_a_4016_);
v_a_4073_ = lean_ctor_get(v___x_4031_, 0);
lean_inc(v_a_4073_);
lean_dec_ref_known(v___x_4031_, 1);
v___y_3999_ = v___y_4009_;
v___y_4000_ = v___y_4011_;
v___y_4001_ = v___y_4010_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v___y_4004_ = v___y_4014_;
v_a_4005_ = v_a_4073_;
goto v___jp_3998_;
}
}
else
{
lean_object* v_a_4074_; 
v_a_4074_ = lean_ctor_get(v___x_4015_, 0);
lean_inc(v_a_4074_);
lean_dec_ref_known(v___x_4015_, 1);
v___y_3999_ = v___y_4009_;
v___y_4000_ = v___y_4011_;
v___y_4001_ = v___y_4010_;
v___y_4002_ = v___y_4012_;
v___y_4003_ = v___y_4013_;
v___y_4004_ = v___y_4014_;
v_a_4005_ = v_a_4074_;
goto v___jp_3998_;
}
}
v___jp_4075_:
{
if (v___y_4082_ == 0)
{
v___y_3980_ = v___y_4076_;
v___y_3981_ = v___y_4080_;
v___y_3982_ = v___y_4079_;
v___y_3983_ = v___y_4081_;
v___y_3984_ = v___y_4078_;
v___y_3985_ = v___y_4077_;
goto v___jp_3979_;
}
else
{
v___y_4009_ = v___y_4076_;
v___y_4010_ = v___y_4077_;
v___y_4011_ = v___y_4078_;
v___y_4012_ = v___y_4079_;
v___y_4013_ = v___y_4080_;
v___y_4014_ = v___y_4081_;
goto v___jp_4008_;
}
}
v___jp_4083_:
{
if (v___y_4091_ == 0)
{
lean_dec_ref(v___y_4084_);
v___y_4076_ = v___y_4085_;
v___y_4077_ = v___y_4087_;
v___y_4078_ = v___y_4086_;
v___y_4079_ = v___y_4088_;
v___y_4080_ = v___y_4089_;
v___y_4081_ = v___y_4090_;
v___y_4082_ = v___x_3933_;
goto v___jp_4075_;
}
else
{
uint8_t v___x_4092_; 
v___x_4092_ = l_Lean_Expr_hasFVar(v___y_4084_);
lean_dec_ref(v___y_4084_);
if (v___x_4092_ == 0)
{
v___y_4009_ = v___y_4085_;
v___y_4010_ = v___y_4087_;
v___y_4011_ = v___y_4086_;
v___y_4012_ = v___y_4088_;
v___y_4013_ = v___y_4089_;
v___y_4014_ = v___y_4090_;
goto v___jp_4008_;
}
else
{
v___y_4076_ = v___y_4085_;
v___y_4077_ = v___y_4087_;
v___y_4078_ = v___y_4086_;
v___y_4079_ = v___y_4088_;
v___y_4080_ = v___y_4089_;
v___y_4081_ = v___y_4090_;
v___y_4082_ = v___x_3933_;
goto v___jp_4075_;
}
}
}
v___jp_4093_:
{
lean_object* v___x_4101_; 
lean_inc_ref(v___x_3978_);
v___x_4101_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3978_, v___y_4099_);
if (lean_obj_tag(v___x_4101_) == 0)
{
lean_object* v_a_4102_; uint8_t v___x_4103_; 
v_a_4102_ = lean_ctor_get(v___x_4101_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4101_, 1);
v___x_4103_ = l_Lean_Expr_hasMVar(v_a_4102_);
if (v___x_4103_ == 0)
{
v___y_4084_ = v_a_4102_;
v___y_4085_ = v___y_4094_;
v___y_4086_ = v___y_4095_;
v___y_4087_ = v___y_4096_;
v___y_4088_ = v___y_4097_;
v___y_4089_ = v___y_4098_;
v___y_4090_ = v___y_4099_;
v___y_4091_ = v___y_4100_;
goto v___jp_4083_;
}
else
{
v___y_4084_ = v_a_4102_;
v___y_4085_ = v___y_4094_;
v___y_4086_ = v___y_4095_;
v___y_4087_ = v___y_4096_;
v___y_4088_ = v___y_4097_;
v___y_4089_ = v___y_4098_;
v___y_4090_ = v___y_4099_;
v___y_4091_ = v___x_3933_;
goto v___jp_4083_;
}
}
else
{
lean_object* v_a_4104_; lean_object* v___x_4106_; uint8_t v_isShared_4107_; uint8_t v_isSharedCheck_4111_; 
lean_dec_ref(v___x_3978_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4104_ = lean_ctor_get(v___x_4101_, 0);
v_isSharedCheck_4111_ = !lean_is_exclusive(v___x_4101_);
if (v_isSharedCheck_4111_ == 0)
{
v___x_4106_ = v___x_4101_;
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
else
{
lean_inc(v_a_4104_);
lean_dec(v___x_4101_);
v___x_4106_ = lean_box(0);
v_isShared_4107_ = v_isSharedCheck_4111_;
goto v_resetjp_4105_;
}
v_resetjp_4105_:
{
lean_object* v___x_4109_; 
if (v_isShared_4107_ == 0)
{
v___x_4109_ = v___x_4106_;
goto v_reusejp_4108_;
}
else
{
lean_object* v_reuseFailAlloc_4110_; 
v_reuseFailAlloc_4110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4110_, 0, v_a_4104_);
v___x_4109_ = v_reuseFailAlloc_4110_;
goto v_reusejp_4108_;
}
v_reusejp_4108_:
{
return v___x_4109_;
}
}
}
}
v___jp_4112_:
{
if (v___y_4119_ == 0)
{
v___y_3980_ = v___y_4113_;
v___y_3981_ = v___y_4117_;
v___y_3982_ = v___y_4116_;
v___y_3983_ = v___y_4118_;
v___y_3984_ = v___y_4115_;
v___y_3985_ = v___y_4114_;
goto v___jp_3979_;
}
else
{
v___y_4094_ = v___y_4113_;
v___y_4095_ = v___y_4115_;
v___y_4096_ = v___y_4114_;
v___y_4097_ = v___y_4116_;
v___y_4098_ = v___y_4117_;
v___y_4099_ = v___y_4118_;
v___y_4100_ = v___y_4119_;
goto v___jp_4093_;
}
}
v___jp_4120_:
{
uint8_t v_useDecide_4127_; 
v_useDecide_4127_ = lean_ctor_get_uint8(v_config_3826_, sizeof(void*)*1);
if (v_useDecide_4127_ == 0)
{
v___y_4113_ = v___y_4121_;
v___y_4114_ = v___y_4126_;
v___y_4115_ = v___y_4125_;
v___y_4116_ = v___y_4123_;
v___y_4117_ = v_isHEq_4122_;
v___y_4118_ = v___y_4124_;
v___y_4119_ = v___x_3933_;
goto v___jp_4112_;
}
else
{
uint8_t v___x_4128_; 
v___x_4128_ = l_Lean_Expr_hasFVar(v___x_3978_);
if (v___x_4128_ == 0)
{
v___y_4094_ = v___y_4121_;
v___y_4095_ = v___y_4125_;
v___y_4096_ = v___y_4126_;
v___y_4097_ = v___y_4123_;
v___y_4098_ = v_isHEq_4122_;
v___y_4099_ = v___y_4124_;
v___y_4100_ = v_useDecide_4127_;
goto v___jp_4093_;
}
else
{
v___y_4113_ = v___y_4121_;
v___y_4114_ = v___y_4126_;
v___y_4115_ = v___y_4125_;
v___y_4116_ = v___y_4123_;
v___y_4117_ = v_isHEq_4122_;
v___y_4118_ = v___y_4124_;
v___y_4119_ = v___x_3933_;
goto v___jp_4112_;
}
}
}
v___jp_4129_:
{
lean_object* v___x_4137_; 
v___x_4137_ = l_Lean_Meta_isExprDefEq(v___y_4134_, v___y_4136_, v___y_4133_, v___y_4132_, v___y_4135_, v___y_4131_);
if (lean_obj_tag(v___x_4137_) == 0)
{
lean_object* v_a_4138_; uint8_t v___x_4139_; 
v_a_4138_ = lean_ctor_get(v___x_4137_, 0);
lean_inc(v_a_4138_);
lean_dec_ref_known(v___x_4137_, 1);
v___x_4139_ = lean_unbox(v_a_4138_);
lean_dec(v_a_4138_);
if (v___x_4139_ == 0)
{
v___y_4121_ = v___y_4130_;
v_isHEq_4122_ = v___x_3837_;
v___y_4123_ = v___y_4133_;
v___y_4124_ = v___y_4132_;
v___y_4125_ = v___y_4135_;
v___y_4126_ = v___y_4131_;
goto v___jp_4120_;
}
else
{
lean_object* v___x_4140_; 
lean_dec_ref(v___x_3978_);
lean_dec_ref(v_config_3826_);
lean_inc(v_mvarId_3827_);
v___x_4140_ = l_Lean_MVarId_getType(v_mvarId_3827_, v___y_4133_, v___y_4132_, v___y_4135_, v___y_4131_);
if (lean_obj_tag(v___x_4140_) == 0)
{
lean_object* v_a_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; 
v_a_4141_ = lean_ctor_get(v___x_4140_, 0);
lean_inc(v_a_4141_);
lean_dec_ref_known(v___x_4140_, 1);
v___x_4142_ = l_Lean_LocalDecl_toExpr(v_val_3858_);
v___x_4143_ = l_Lean_Meta_mkEqOfHEq(v___x_4142_, v___x_3837_, v___y_4133_, v___y_4132_, v___y_4135_, v___y_4131_);
if (lean_obj_tag(v___x_4143_) == 0)
{
lean_object* v_a_4144_; lean_object* v___x_4145_; 
v_a_4144_ = lean_ctor_get(v___x_4143_, 0);
lean_inc(v_a_4144_);
lean_dec_ref_known(v___x_4143_, 1);
v___x_4145_ = l_Lean_Meta_mkNoConfusion(v_a_4141_, v_a_4144_, v___y_4133_, v___y_4132_, v___y_4135_, v___y_4131_);
if (lean_obj_tag(v___x_4145_) == 0)
{
lean_object* v_a_4146_; lean_object* v___x_4147_; 
v_a_4146_ = lean_ctor_get(v___x_4145_, 0);
lean_inc(v_a_4146_);
lean_dec_ref_known(v___x_4145_, 1);
v___x_4147_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3827_, v_a_4146_, v___y_4132_);
if (lean_obj_tag(v___x_4147_) == 0)
{
lean_object* v___x_4148_; lean_object* v___x_4149_; lean_object* v___x_4150_; lean_object* v___x_4151_; 
lean_dec_ref_known(v___x_4147_, 1);
v___x_4148_ = lean_box(v___x_3837_);
v___x_4149_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4149_, 0, v___x_4148_);
v___x_4150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4150_, 0, v___x_4149_);
lean_ctor_set(v___x_4150_, 1, v___x_3862_);
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v___x_4150_);
v_a_3844_ = v___x_4151_;
goto v___jp_3843_;
}
else
{
lean_object* v_a_4152_; lean_object* v___x_4154_; uint8_t v_isShared_4155_; uint8_t v_isSharedCheck_4159_; 
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
v_a_4152_ = lean_ctor_get(v___x_4147_, 0);
v_isSharedCheck_4159_ = !lean_is_exclusive(v___x_4147_);
if (v_isSharedCheck_4159_ == 0)
{
v___x_4154_ = v___x_4147_;
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
else
{
lean_inc(v_a_4152_);
lean_dec(v___x_4147_);
v___x_4154_ = lean_box(0);
v_isShared_4155_ = v_isSharedCheck_4159_;
goto v_resetjp_4153_;
}
v_resetjp_4153_:
{
lean_object* v___x_4157_; 
if (v_isShared_4155_ == 0)
{
v___x_4157_ = v___x_4154_;
goto v_reusejp_4156_;
}
else
{
lean_object* v_reuseFailAlloc_4158_; 
v_reuseFailAlloc_4158_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4158_, 0, v_a_4152_);
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
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_4160_ = lean_ctor_get(v___x_4145_, 0);
v_isSharedCheck_4167_ = !lean_is_exclusive(v___x_4145_);
if (v_isSharedCheck_4167_ == 0)
{
v___x_4162_ = v___x_4145_;
v_isShared_4163_ = v_isSharedCheck_4167_;
goto v_resetjp_4161_;
}
else
{
lean_inc(v_a_4160_);
lean_dec(v___x_4145_);
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
else
{
lean_object* v_a_4168_; lean_object* v___x_4170_; uint8_t v_isShared_4171_; uint8_t v_isSharedCheck_4175_; 
lean_dec(v_a_4141_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_4168_ = lean_ctor_get(v___x_4143_, 0);
v_isSharedCheck_4175_ = !lean_is_exclusive(v___x_4143_);
if (v_isSharedCheck_4175_ == 0)
{
v___x_4170_ = v___x_4143_;
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
else
{
lean_inc(v_a_4168_);
lean_dec(v___x_4143_);
v___x_4170_ = lean_box(0);
v_isShared_4171_ = v_isSharedCheck_4175_;
goto v_resetjp_4169_;
}
v_resetjp_4169_:
{
lean_object* v___x_4173_; 
if (v_isShared_4171_ == 0)
{
v___x_4173_ = v___x_4170_;
goto v_reusejp_4172_;
}
else
{
lean_object* v_reuseFailAlloc_4174_; 
v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4174_, 0, v_a_4168_);
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
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_4176_ = lean_ctor_get(v___x_4140_, 0);
v_isSharedCheck_4183_ = !lean_is_exclusive(v___x_4140_);
if (v_isSharedCheck_4183_ == 0)
{
v___x_4178_ = v___x_4140_;
v_isShared_4179_ = v_isSharedCheck_4183_;
goto v_resetjp_4177_;
}
else
{
lean_inc(v_a_4176_);
lean_dec(v___x_4140_);
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
else
{
lean_object* v_a_4184_; lean_object* v___x_4186_; uint8_t v_isShared_4187_; uint8_t v_isSharedCheck_4191_; 
lean_dec_ref(v___x_3978_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4184_ = lean_ctor_get(v___x_4137_, 0);
v_isSharedCheck_4191_ = !lean_is_exclusive(v___x_4137_);
if (v_isSharedCheck_4191_ == 0)
{
v___x_4186_ = v___x_4137_;
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
else
{
lean_inc(v_a_4184_);
lean_dec(v___x_4137_);
v___x_4186_ = lean_box(0);
v_isShared_4187_ = v_isSharedCheck_4191_;
goto v_resetjp_4185_;
}
v_resetjp_4185_:
{
lean_object* v___x_4189_; 
if (v_isShared_4187_ == 0)
{
v___x_4189_ = v___x_4186_;
goto v_reusejp_4188_;
}
else
{
lean_object* v_reuseFailAlloc_4190_; 
v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
v___x_4189_ = v_reuseFailAlloc_4190_;
goto v_reusejp_4188_;
}
v_reusejp_4188_:
{
return v___x_4189_;
}
}
}
}
v___jp_4192_:
{
lean_object* v___x_4198_; 
lean_inc_ref(v___x_3978_);
v___x_4198_ = l_Lean_Meta_matchHEq_x3f(v___x_3978_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4198_, 1);
if (lean_obj_tag(v_a_4199_) == 1)
{
lean_object* v_val_4200_; lean_object* v_snd_4201_; lean_object* v_snd_4202_; lean_object* v_fst_4203_; lean_object* v_fst_4204_; lean_object* v_fst_4205_; lean_object* v_snd_4206_; lean_object* v___x_4207_; 
v_val_4200_ = lean_ctor_get(v_a_4199_, 0);
lean_inc(v_val_4200_);
lean_dec_ref_known(v_a_4199_, 1);
v_snd_4201_ = lean_ctor_get(v_val_4200_, 1);
lean_inc(v_snd_4201_);
v_snd_4202_ = lean_ctor_get(v_snd_4201_, 1);
lean_inc(v_snd_4202_);
v_fst_4203_ = lean_ctor_get(v_val_4200_, 0);
lean_inc(v_fst_4203_);
lean_dec(v_val_4200_);
v_fst_4204_ = lean_ctor_get(v_snd_4201_, 0);
lean_inc(v_fst_4204_);
lean_dec(v_snd_4201_);
v_fst_4205_ = lean_ctor_get(v_snd_4202_, 0);
lean_inc(v_fst_4205_);
v_snd_4206_ = lean_ctor_get(v_snd_4202_, 1);
lean_inc(v_snd_4206_);
lean_dec(v_snd_4202_);
v___x_4207_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4204_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4207_) == 0)
{
lean_object* v_a_4208_; 
v_a_4208_ = lean_ctor_get(v___x_4207_, 0);
lean_inc(v_a_4208_);
lean_dec_ref_known(v___x_4207_, 1);
if (lean_obj_tag(v_a_4208_) == 1)
{
lean_object* v_val_4209_; lean_object* v___x_4210_; 
v_val_4209_ = lean_ctor_get(v_a_4208_, 0);
lean_inc(v_val_4209_);
lean_dec_ref_known(v_a_4208_, 1);
v___x_4210_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4206_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
if (lean_obj_tag(v___x_4210_) == 0)
{
lean_object* v_a_4211_; 
v_a_4211_ = lean_ctor_get(v___x_4210_, 0);
lean_inc(v_a_4211_);
lean_dec_ref_known(v___x_4210_, 1);
if (lean_obj_tag(v_a_4211_) == 1)
{
lean_object* v_toConstantVal_4212_; lean_object* v_val_4213_; lean_object* v_toConstantVal_4214_; lean_object* v_name_4215_; lean_object* v_name_4216_; uint8_t v___x_4217_; 
v_toConstantVal_4212_ = lean_ctor_get(v_val_4209_, 0);
lean_inc_ref(v_toConstantVal_4212_);
lean_dec(v_val_4209_);
v_val_4213_ = lean_ctor_get(v_a_4211_, 0);
lean_inc(v_val_4213_);
lean_dec_ref_known(v_a_4211_, 1);
v_toConstantVal_4214_ = lean_ctor_get(v_val_4213_, 0);
lean_inc_ref(v_toConstantVal_4214_);
lean_dec(v_val_4213_);
v_name_4215_ = lean_ctor_get(v_toConstantVal_4212_, 0);
lean_inc(v_name_4215_);
lean_dec_ref(v_toConstantVal_4212_);
v_name_4216_ = lean_ctor_get(v_toConstantVal_4214_, 0);
lean_inc(v_name_4216_);
lean_dec_ref(v_toConstantVal_4214_);
v___x_4217_ = lean_name_eq(v_name_4215_, v_name_4216_);
lean_dec(v_name_4216_);
lean_dec(v_name_4215_);
if (v___x_4217_ == 0)
{
v___y_4130_ = v_isEq_4193_;
v___y_4131_ = v___y_4197_;
v___y_4132_ = v___y_4195_;
v___y_4133_ = v___y_4194_;
v___y_4134_ = v_fst_4203_;
v___y_4135_ = v___y_4196_;
v___y_4136_ = v_fst_4205_;
goto v___jp_4129_;
}
else
{
if (v___x_3933_ == 0)
{
lean_dec(v_fst_4205_);
lean_dec(v_fst_4203_);
v___y_4121_ = v_isEq_4193_;
v_isHEq_4122_ = v___x_3837_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
v___y_4125_ = v___y_4196_;
v___y_4126_ = v___y_4197_;
goto v___jp_4120_;
}
else
{
v___y_4130_ = v_isEq_4193_;
v___y_4131_ = v___y_4197_;
v___y_4132_ = v___y_4195_;
v___y_4133_ = v___y_4194_;
v___y_4134_ = v_fst_4203_;
v___y_4135_ = v___y_4196_;
v___y_4136_ = v_fst_4205_;
goto v___jp_4129_;
}
}
}
else
{
lean_dec(v_a_4211_);
lean_dec(v_val_4209_);
lean_dec(v_fst_4205_);
lean_dec(v_fst_4203_);
v___y_4121_ = v_isEq_4193_;
v_isHEq_4122_ = v___x_3837_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
v___y_4125_ = v___y_4196_;
v___y_4126_ = v___y_4197_;
goto v___jp_4120_;
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
lean_dec(v_val_4209_);
lean_dec(v_fst_4205_);
lean_dec(v_fst_4203_);
lean_dec_ref(v___x_3978_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4218_ = lean_ctor_get(v___x_4210_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4210_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4210_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4210_);
v___x_4220_ = lean_box(0);
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
v_resetjp_4219_:
{
lean_object* v___x_4223_; 
if (v_isShared_4221_ == 0)
{
v___x_4223_ = v___x_4220_;
goto v_reusejp_4222_;
}
else
{
lean_object* v_reuseFailAlloc_4224_; 
v_reuseFailAlloc_4224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4224_, 0, v_a_4218_);
v___x_4223_ = v_reuseFailAlloc_4224_;
goto v_reusejp_4222_;
}
v_reusejp_4222_:
{
return v___x_4223_;
}
}
}
}
else
{
lean_dec(v_a_4208_);
lean_dec(v_snd_4206_);
lean_dec(v_fst_4205_);
lean_dec(v_fst_4203_);
v___y_4121_ = v_isEq_4193_;
v_isHEq_4122_ = v___x_3837_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
v___y_4125_ = v___y_4196_;
v___y_4126_ = v___y_4197_;
goto v___jp_4120_;
}
}
else
{
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec(v_snd_4206_);
lean_dec(v_fst_4205_);
lean_dec(v_fst_4203_);
lean_dec_ref(v___x_3978_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4226_ = lean_ctor_get(v___x_4207_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4207_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4207_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4207_);
v___x_4228_ = lean_box(0);
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
v_resetjp_4227_:
{
lean_object* v___x_4231_; 
if (v_isShared_4229_ == 0)
{
v___x_4231_ = v___x_4228_;
goto v_reusejp_4230_;
}
else
{
lean_object* v_reuseFailAlloc_4232_; 
v_reuseFailAlloc_4232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4232_, 0, v_a_4226_);
v___x_4231_ = v_reuseFailAlloc_4232_;
goto v_reusejp_4230_;
}
v_reusejp_4230_:
{
return v___x_4231_;
}
}
}
}
else
{
lean_dec(v_a_4199_);
v___y_4121_ = v_isEq_4193_;
v_isHEq_4122_ = v___x_3933_;
v___y_4123_ = v___y_4194_;
v___y_4124_ = v___y_4195_;
v___y_4125_ = v___y_4196_;
v___y_4126_ = v___y_4197_;
goto v___jp_4120_;
}
}
else
{
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_dec_ref(v___x_3978_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4234_ = lean_ctor_get(v___x_4198_, 0);
v_isSharedCheck_4241_ = !lean_is_exclusive(v___x_4198_);
if (v_isSharedCheck_4241_ == 0)
{
v___x_4236_ = v___x_4198_;
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_a_4234_);
lean_dec(v___x_4198_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4241_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4239_; 
if (v_isShared_4237_ == 0)
{
v___x_4239_ = v___x_4236_;
goto v_reusejp_4238_;
}
else
{
lean_object* v_reuseFailAlloc_4240_; 
v_reuseFailAlloc_4240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4240_, 0, v_a_4234_);
v___x_4239_ = v_reuseFailAlloc_4240_;
goto v_reusejp_4238_;
}
v_reusejp_4238_:
{
return v___x_4239_;
}
}
}
}
v___jp_4242_:
{
lean_object* v___x_4247_; 
lean_inc_ref(v___x_3978_);
v___x_4247_ = l_Lean_Meta_matchEq_x3f(v___x_3978_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
if (lean_obj_tag(v___x_4247_) == 0)
{
lean_object* v_a_4248_; 
v_a_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc(v_a_4248_);
lean_dec_ref_known(v___x_4247_, 1);
if (lean_obj_tag(v_a_4248_) == 1)
{
lean_object* v_val_4249_; lean_object* v_snd_4250_; lean_object* v_fst_4251_; lean_object* v_snd_4252_; lean_object* v___x_4253_; 
v_val_4249_ = lean_ctor_get(v_a_4248_, 0);
lean_inc(v_val_4249_);
lean_dec_ref_known(v_a_4248_, 1);
v_snd_4250_ = lean_ctor_get(v_val_4249_, 1);
lean_inc(v_snd_4250_);
lean_dec(v_val_4249_);
v_fst_4251_ = lean_ctor_get(v_snd_4250_, 0);
lean_inc(v_fst_4251_);
v_snd_4252_ = lean_ctor_get(v_snd_4250_, 1);
lean_inc(v_snd_4252_);
lean_dec(v_snd_4250_);
v___x_4253_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4251_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
if (lean_obj_tag(v___x_4253_) == 0)
{
lean_object* v_a_4254_; 
v_a_4254_ = lean_ctor_get(v___x_4253_, 0);
lean_inc(v_a_4254_);
lean_dec_ref_known(v___x_4253_, 1);
if (lean_obj_tag(v_a_4254_) == 1)
{
lean_object* v_val_4255_; lean_object* v___x_4256_; 
v_val_4255_ = lean_ctor_get(v_a_4254_, 0);
lean_inc(v_val_4255_);
lean_dec_ref_known(v_a_4254_, 1);
v___x_4256_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4252_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v___x_4256_, 1);
if (lean_obj_tag(v_a_4257_) == 1)
{
lean_object* v_toConstantVal_4258_; lean_object* v_val_4259_; lean_object* v_toConstantVal_4260_; lean_object* v_name_4261_; lean_object* v_name_4262_; uint8_t v___x_4263_; 
v_toConstantVal_4258_ = lean_ctor_get(v_val_4255_, 0);
lean_inc_ref(v_toConstantVal_4258_);
lean_dec(v_val_4255_);
v_val_4259_ = lean_ctor_get(v_a_4257_, 0);
lean_inc(v_val_4259_);
lean_dec_ref_known(v_a_4257_, 1);
v_toConstantVal_4260_ = lean_ctor_get(v_val_4259_, 0);
lean_inc_ref(v_toConstantVal_4260_);
lean_dec(v_val_4259_);
v_name_4261_ = lean_ctor_get(v_toConstantVal_4258_, 0);
lean_inc(v_name_4261_);
lean_dec_ref(v_toConstantVal_4258_);
v_name_4262_ = lean_ctor_get(v_toConstantVal_4260_, 0);
lean_inc(v_name_4262_);
lean_dec_ref(v_toConstantVal_4260_);
v___x_4263_ = lean_name_eq(v_name_4261_, v_name_4262_);
lean_dec(v_name_4262_);
lean_dec(v_name_4261_);
if (v___x_4263_ == 0)
{
lean_dec_ref(v___x_3978_);
lean_dec_ref(v_config_3826_);
v___y_3864_ = v___y_4246_;
v___y_3865_ = v___y_4245_;
v___y_3866_ = v___y_4243_;
v___y_3867_ = v___y_4244_;
goto v___jp_3863_;
}
else
{
if (v___x_3933_ == 0)
{
lean_del_object(v___x_3860_);
v_isEq_4193_ = v___x_3837_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
v___y_4196_ = v___y_4245_;
v___y_4197_ = v___y_4246_;
goto v___jp_4192_;
}
else
{
lean_dec_ref(v___x_3978_);
lean_dec_ref(v_config_3826_);
v___y_3864_ = v___y_4246_;
v___y_3865_ = v___y_4245_;
v___y_3866_ = v___y_4243_;
v___y_3867_ = v___y_4244_;
goto v___jp_3863_;
}
}
}
else
{
lean_dec(v_a_4257_);
lean_dec(v_val_4255_);
lean_del_object(v___x_3860_);
v_isEq_4193_ = v___x_3837_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
v___y_4196_ = v___y_4245_;
v___y_4197_ = v___y_4246_;
goto v___jp_4192_;
}
}
else
{
lean_object* v_a_4264_; lean_object* v___x_4266_; uint8_t v_isShared_4267_; uint8_t v_isSharedCheck_4271_; 
lean_dec(v_val_4255_);
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4264_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4271_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4271_ == 0)
{
v___x_4266_ = v___x_4256_;
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
else
{
lean_inc(v_a_4264_);
lean_dec(v___x_4256_);
v___x_4266_ = lean_box(0);
v_isShared_4267_ = v_isSharedCheck_4271_;
goto v_resetjp_4265_;
}
v_resetjp_4265_:
{
lean_object* v___x_4269_; 
if (v_isShared_4267_ == 0)
{
v___x_4269_ = v___x_4266_;
goto v_reusejp_4268_;
}
else
{
lean_object* v_reuseFailAlloc_4270_; 
v_reuseFailAlloc_4270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4270_, 0, v_a_4264_);
v___x_4269_ = v_reuseFailAlloc_4270_;
goto v_reusejp_4268_;
}
v_reusejp_4268_:
{
return v___x_4269_;
}
}
}
}
else
{
lean_dec(v_a_4254_);
lean_dec(v_snd_4252_);
lean_del_object(v___x_3860_);
v_isEq_4193_ = v___x_3837_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
v___y_4196_ = v___y_4245_;
v___y_4197_ = v___y_4246_;
goto v___jp_4192_;
}
}
else
{
lean_object* v_a_4272_; lean_object* v___x_4274_; uint8_t v_isShared_4275_; uint8_t v_isSharedCheck_4279_; 
lean_dec(v_snd_4252_);
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4272_ = lean_ctor_get(v___x_4253_, 0);
v_isSharedCheck_4279_ = !lean_is_exclusive(v___x_4253_);
if (v_isSharedCheck_4279_ == 0)
{
v___x_4274_ = v___x_4253_;
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
else
{
lean_inc(v_a_4272_);
lean_dec(v___x_4253_);
v___x_4274_ = lean_box(0);
v_isShared_4275_ = v_isSharedCheck_4279_;
goto v_resetjp_4273_;
}
v_resetjp_4273_:
{
lean_object* v___x_4277_; 
if (v_isShared_4275_ == 0)
{
v___x_4277_ = v___x_4274_;
goto v_reusejp_4276_;
}
else
{
lean_object* v_reuseFailAlloc_4278_; 
v_reuseFailAlloc_4278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4278_, 0, v_a_4272_);
v___x_4277_ = v_reuseFailAlloc_4278_;
goto v_reusejp_4276_;
}
v_reusejp_4276_:
{
return v___x_4277_;
}
}
}
}
else
{
lean_dec(v_a_4248_);
lean_del_object(v___x_3860_);
v_isEq_4193_ = v___x_3933_;
v___y_4194_ = v___y_4243_;
v___y_4195_ = v___y_4244_;
v___y_4196_ = v___y_4245_;
v___y_4197_ = v___y_4246_;
goto v___jp_4192_;
}
}
else
{
lean_object* v_a_4280_; lean_object* v___x_4282_; uint8_t v_isShared_4283_; uint8_t v_isSharedCheck_4287_; 
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4280_ = lean_ctor_get(v___x_4247_, 0);
v_isSharedCheck_4287_ = !lean_is_exclusive(v___x_4247_);
if (v_isSharedCheck_4287_ == 0)
{
v___x_4282_ = v___x_4247_;
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
else
{
lean_inc(v_a_4280_);
lean_dec(v___x_4247_);
v___x_4282_ = lean_box(0);
v_isShared_4283_ = v_isSharedCheck_4287_;
goto v_resetjp_4281_;
}
v_resetjp_4281_:
{
lean_object* v___x_4285_; 
if (v_isShared_4283_ == 0)
{
v___x_4285_ = v___x_4282_;
goto v_reusejp_4284_;
}
else
{
lean_object* v_reuseFailAlloc_4286_; 
v_reuseFailAlloc_4286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4286_, 0, v_a_4280_);
v___x_4285_ = v_reuseFailAlloc_4286_;
goto v_reusejp_4284_;
}
v_reusejp_4284_:
{
return v___x_4285_;
}
}
}
}
v___jp_4288_:
{
lean_object* v___x_4293_; 
lean_inc_ref(v___x_3978_);
v___x_4293_ = l_Lean_refutableHasNotBit_x3f(v___x_3978_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4293_) == 0)
{
lean_object* v_a_4294_; 
v_a_4294_ = lean_ctor_get(v___x_4293_, 0);
lean_inc(v_a_4294_);
lean_dec_ref_known(v___x_4293_, 1);
if (lean_obj_tag(v_a_4294_) == 1)
{
lean_object* v_val_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4335_; 
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec_ref(v_config_3826_);
v_val_4295_ = lean_ctor_get(v_a_4294_, 0);
v_isSharedCheck_4335_ = !lean_is_exclusive(v_a_4294_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4297_ = v_a_4294_;
v_isShared_4298_ = v_isSharedCheck_4335_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_val_4295_);
lean_dec(v_a_4294_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4335_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4299_; 
lean_inc(v_mvarId_3827_);
v___x_4299_ = l_Lean_MVarId_getType(v_mvarId_3827_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4299_) == 0)
{
lean_object* v_a_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; 
v_a_4300_ = lean_ctor_get(v___x_4299_, 0);
lean_inc(v_a_4300_);
lean_dec_ref_known(v___x_4299_, 1);
v___x_4301_ = l_Lean_LocalDecl_toExpr(v_val_3858_);
v___x_4302_ = l_Lean_Meta_mkAbsurd(v_a_4300_, v_val_4295_, v___x_4301_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4302_) == 0)
{
lean_object* v_a_4303_; lean_object* v___x_4304_; 
v_a_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc(v_a_4303_);
lean_dec_ref_known(v___x_4302_, 1);
v___x_4304_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3827_, v_a_4303_, v___y_4290_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v___x_4305_; lean_object* v___x_4307_; 
lean_dec_ref_known(v___x_4304_, 1);
v___x_4305_ = lean_box(v___x_3837_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 0, v___x_4305_);
v___x_4307_ = v___x_4297_;
goto v_reusejp_4306_;
}
else
{
lean_object* v_reuseFailAlloc_4310_; 
v_reuseFailAlloc_4310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4310_, 0, v___x_4305_);
v___x_4307_ = v_reuseFailAlloc_4310_;
goto v_reusejp_4306_;
}
v_reusejp_4306_:
{
lean_object* v___x_4308_; lean_object* v___x_4309_; 
v___x_4308_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4308_, 0, v___x_4307_);
lean_ctor_set(v___x_4308_, 1, v___x_3862_);
v___x_4309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
v_a_3844_ = v___x_4309_;
goto v___jp_3843_;
}
}
else
{
lean_object* v_a_4311_; lean_object* v___x_4313_; uint8_t v_isShared_4314_; uint8_t v_isSharedCheck_4318_; 
lean_del_object(v___x_4297_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
v_a_4311_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4318_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4318_ == 0)
{
v___x_4313_ = v___x_4304_;
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
else
{
lean_inc(v_a_4311_);
lean_dec(v___x_4304_);
v___x_4313_ = lean_box(0);
v_isShared_4314_ = v_isSharedCheck_4318_;
goto v_resetjp_4312_;
}
v_resetjp_4312_:
{
lean_object* v___x_4316_; 
if (v_isShared_4314_ == 0)
{
v___x_4316_ = v___x_4313_;
goto v_reusejp_4315_;
}
else
{
lean_object* v_reuseFailAlloc_4317_; 
v_reuseFailAlloc_4317_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4317_, 0, v_a_4311_);
v___x_4316_ = v_reuseFailAlloc_4317_;
goto v_reusejp_4315_;
}
v_reusejp_4315_:
{
return v___x_4316_;
}
}
}
}
else
{
lean_object* v_a_4319_; lean_object* v___x_4321_; uint8_t v_isShared_4322_; uint8_t v_isSharedCheck_4326_; 
lean_del_object(v___x_4297_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_4319_ = lean_ctor_get(v___x_4302_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4302_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4321_ = v___x_4302_;
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
else
{
lean_inc(v_a_4319_);
lean_dec(v___x_4302_);
v___x_4321_ = lean_box(0);
v_isShared_4322_ = v_isSharedCheck_4326_;
goto v_resetjp_4320_;
}
v_resetjp_4320_:
{
lean_object* v___x_4324_; 
if (v_isShared_4322_ == 0)
{
v___x_4324_ = v___x_4321_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v_a_4319_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_del_object(v___x_4297_);
lean_dec(v_val_4295_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_4327_ = lean_ctor_get(v___x_4299_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4299_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4299_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4299_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
}
else
{
lean_object* v___x_4336_; 
lean_dec(v_a_4294_);
lean_inc_ref(v___x_3978_);
v___x_4336_ = l_Lean_Meta_matchNe_x3f(v___x_3978_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4336_) == 0)
{
lean_object* v_a_4337_; 
v_a_4337_ = lean_ctor_get(v___x_4336_, 0);
lean_inc(v_a_4337_);
lean_dec_ref_known(v___x_4336_, 1);
if (lean_obj_tag(v_a_4337_) == 1)
{
lean_object* v_val_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4408_; 
v_val_4338_ = lean_ctor_get(v_a_4337_, 0);
v_isSharedCheck_4408_ = !lean_is_exclusive(v_a_4337_);
if (v_isSharedCheck_4408_ == 0)
{
v___x_4340_ = v_a_4337_;
v_isShared_4341_ = v_isSharedCheck_4408_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_val_4338_);
lean_dec(v_a_4337_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4408_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v_snd_4342_; lean_object* v_fst_4343_; lean_object* v_snd_4344_; lean_object* v___x_4346_; uint8_t v_isShared_4347_; uint8_t v_isSharedCheck_4407_; 
v_snd_4342_ = lean_ctor_get(v_val_4338_, 1);
lean_inc(v_snd_4342_);
lean_dec(v_val_4338_);
v_fst_4343_ = lean_ctor_get(v_snd_4342_, 0);
v_snd_4344_ = lean_ctor_get(v_snd_4342_, 1);
v_isSharedCheck_4407_ = !lean_is_exclusive(v_snd_4342_);
if (v_isSharedCheck_4407_ == 0)
{
v___x_4346_ = v_snd_4342_;
v_isShared_4347_ = v_isSharedCheck_4407_;
goto v_resetjp_4345_;
}
else
{
lean_inc(v_snd_4344_);
lean_inc(v_fst_4343_);
lean_dec(v_snd_4342_);
v___x_4346_ = lean_box(0);
v_isShared_4347_ = v_isSharedCheck_4407_;
goto v_resetjp_4345_;
}
v_resetjp_4345_:
{
lean_object* v___x_4348_; 
lean_inc(v_fst_4343_);
v___x_4348_ = l_Lean_Meta_isExprDefEq(v_fst_4343_, v_snd_4344_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4348_) == 0)
{
lean_object* v_a_4349_; uint8_t v___x_4350_; 
v_a_4349_ = lean_ctor_get(v___x_4348_, 0);
lean_inc(v_a_4349_);
lean_dec_ref_known(v___x_4348_, 1);
v___x_4350_ = lean_unbox(v_a_4349_);
lean_dec(v_a_4349_);
if (v___x_4350_ == 0)
{
lean_del_object(v___x_4346_);
lean_dec(v_fst_4343_);
lean_del_object(v___x_4340_);
v___y_4243_ = v___y_4289_;
v___y_4244_ = v___y_4290_;
v___y_4245_ = v___y_4291_;
v___y_4246_ = v___y_4292_;
goto v___jp_4242_;
}
else
{
lean_object* v___x_4351_; 
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec_ref(v_config_3826_);
lean_inc(v_mvarId_3827_);
v___x_4351_ = l_Lean_MVarId_getType(v_mvarId_3827_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; lean_object* v___x_4353_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4351_, 1);
v___x_4353_ = l_Lean_Meta_mkEqRefl(v_fst_4343_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4353_) == 0)
{
lean_object* v_a_4354_; lean_object* v___x_4355_; lean_object* v___x_4356_; 
v_a_4354_ = lean_ctor_get(v___x_4353_, 0);
lean_inc(v_a_4354_);
lean_dec_ref_known(v___x_4353_, 1);
v___x_4355_ = l_Lean_LocalDecl_toExpr(v_val_3858_);
v___x_4356_ = l_Lean_Meta_mkAbsurd(v_a_4352_, v_a_4354_, v___x_4355_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
if (lean_obj_tag(v___x_4356_) == 0)
{
lean_object* v_a_4357_; lean_object* v___x_4358_; 
v_a_4357_ = lean_ctor_get(v___x_4356_, 0);
lean_inc(v_a_4357_);
lean_dec_ref_known(v___x_4356_, 1);
v___x_4358_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3827_, v_a_4357_, v___y_4290_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v___x_4359_; lean_object* v___x_4361_; 
lean_dec_ref_known(v___x_4358_, 1);
v___x_4359_ = lean_box(v___x_3837_);
if (v_isShared_4341_ == 0)
{
lean_ctor_set(v___x_4340_, 0, v___x_4359_);
v___x_4361_ = v___x_4340_;
goto v_reusejp_4360_;
}
else
{
lean_object* v_reuseFailAlloc_4366_; 
v_reuseFailAlloc_4366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4366_, 0, v___x_4359_);
v___x_4361_ = v_reuseFailAlloc_4366_;
goto v_reusejp_4360_;
}
v_reusejp_4360_:
{
lean_object* v___x_4363_; 
if (v_isShared_4347_ == 0)
{
lean_ctor_set(v___x_4346_, 1, v___x_3862_);
lean_ctor_set(v___x_4346_, 0, v___x_4361_);
v___x_4363_ = v___x_4346_;
goto v_reusejp_4362_;
}
else
{
lean_object* v_reuseFailAlloc_4365_; 
v_reuseFailAlloc_4365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4365_, 0, v___x_4361_);
lean_ctor_set(v_reuseFailAlloc_4365_, 1, v___x_3862_);
v___x_4363_ = v_reuseFailAlloc_4365_;
goto v_reusejp_4362_;
}
v_reusejp_4362_:
{
lean_object* v___x_4364_; 
v___x_4364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4364_, 0, v___x_4363_);
v_a_3844_ = v___x_4364_;
goto v___jp_3843_;
}
}
}
else
{
lean_object* v_a_4367_; lean_object* v___x_4369_; uint8_t v_isShared_4370_; uint8_t v_isSharedCheck_4374_; 
lean_del_object(v___x_4346_);
lean_del_object(v___x_4340_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
v_a_4367_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4374_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4374_ == 0)
{
v___x_4369_ = v___x_4358_;
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
else
{
lean_inc(v_a_4367_);
lean_dec(v___x_4358_);
v___x_4369_ = lean_box(0);
v_isShared_4370_ = v_isSharedCheck_4374_;
goto v_resetjp_4368_;
}
v_resetjp_4368_:
{
lean_object* v___x_4372_; 
if (v_isShared_4370_ == 0)
{
v___x_4372_ = v___x_4369_;
goto v_reusejp_4371_;
}
else
{
lean_object* v_reuseFailAlloc_4373_; 
v_reuseFailAlloc_4373_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4373_, 0, v_a_4367_);
v___x_4372_ = v_reuseFailAlloc_4373_;
goto v_reusejp_4371_;
}
v_reusejp_4371_:
{
return v___x_4372_;
}
}
}
}
else
{
lean_object* v_a_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
lean_del_object(v___x_4346_);
lean_del_object(v___x_4340_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_4375_ = lean_ctor_get(v___x_4356_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4356_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4356_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_a_4375_);
lean_dec(v___x_4356_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_a_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
lean_dec(v_a_4352_);
lean_del_object(v___x_4346_);
lean_del_object(v___x_4340_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_4383_ = lean_ctor_get(v___x_4353_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4353_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4353_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4353_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
v___x_4388_ = v_reuseFailAlloc_4389_;
goto v_reusejp_4387_;
}
v_reusejp_4387_:
{
return v___x_4388_;
}
}
}
}
else
{
lean_object* v_a_4391_; lean_object* v___x_4393_; uint8_t v_isShared_4394_; uint8_t v_isSharedCheck_4398_; 
lean_del_object(v___x_4346_);
lean_dec(v_fst_4343_);
lean_del_object(v___x_4340_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_4391_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4398_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4398_ == 0)
{
v___x_4393_ = v___x_4351_;
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
else
{
lean_inc(v_a_4391_);
lean_dec(v___x_4351_);
v___x_4393_ = lean_box(0);
v_isShared_4394_ = v_isSharedCheck_4398_;
goto v_resetjp_4392_;
}
v_resetjp_4392_:
{
lean_object* v___x_4396_; 
if (v_isShared_4394_ == 0)
{
v___x_4396_ = v___x_4393_;
goto v_reusejp_4395_;
}
else
{
lean_object* v_reuseFailAlloc_4397_; 
v_reuseFailAlloc_4397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4397_, 0, v_a_4391_);
v___x_4396_ = v_reuseFailAlloc_4397_;
goto v_reusejp_4395_;
}
v_reusejp_4395_:
{
return v___x_4396_;
}
}
}
}
}
else
{
lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4406_; 
lean_del_object(v___x_4346_);
lean_dec(v_fst_4343_);
lean_del_object(v___x_4340_);
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4399_ = lean_ctor_get(v___x_4348_, 0);
v_isSharedCheck_4406_ = !lean_is_exclusive(v___x_4348_);
if (v_isSharedCheck_4406_ == 0)
{
v___x_4401_ = v___x_4348_;
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4348_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4406_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4404_; 
if (v_isShared_4402_ == 0)
{
v___x_4404_ = v___x_4401_;
goto v_reusejp_4403_;
}
else
{
lean_object* v_reuseFailAlloc_4405_; 
v_reuseFailAlloc_4405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4405_, 0, v_a_4399_);
v___x_4404_ = v_reuseFailAlloc_4405_;
goto v_reusejp_4403_;
}
v_reusejp_4403_:
{
return v___x_4404_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4337_);
v___y_4243_ = v___y_4289_;
v___y_4244_ = v___y_4290_;
v___y_4245_ = v___y_4291_;
v___y_4246_ = v___y_4292_;
goto v___jp_4242_;
}
}
else
{
lean_object* v_a_4409_; lean_object* v___x_4411_; uint8_t v_isShared_4412_; uint8_t v_isSharedCheck_4416_; 
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4409_ = lean_ctor_get(v___x_4336_, 0);
v_isSharedCheck_4416_ = !lean_is_exclusive(v___x_4336_);
if (v_isSharedCheck_4416_ == 0)
{
v___x_4411_ = v___x_4336_;
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
else
{
lean_inc(v_a_4409_);
lean_dec(v___x_4336_);
v___x_4411_ = lean_box(0);
v_isShared_4412_ = v_isSharedCheck_4416_;
goto v_resetjp_4410_;
}
v_resetjp_4410_:
{
lean_object* v___x_4414_; 
if (v_isShared_4412_ == 0)
{
v___x_4414_ = v___x_4411_;
goto v_reusejp_4413_;
}
else
{
lean_object* v_reuseFailAlloc_4415_; 
v_reuseFailAlloc_4415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4415_, 0, v_a_4409_);
v___x_4414_ = v_reuseFailAlloc_4415_;
goto v_reusejp_4413_;
}
v_reusejp_4413_:
{
return v___x_4414_;
}
}
}
}
}
else
{
lean_object* v_a_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4424_; 
lean_dec_ref(v___x_3978_);
lean_del_object(v___x_3860_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_4417_ = lean_ctor_get(v___x_4293_, 0);
v_isSharedCheck_4424_ = !lean_is_exclusive(v___x_4293_);
if (v_isSharedCheck_4424_ == 0)
{
v___x_4419_ = v___x_4293_;
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_a_4417_);
lean_dec(v___x_4293_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4424_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4422_; 
if (v_isShared_4420_ == 0)
{
v___x_4422_ = v___x_4419_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v_a_4417_);
v___x_4422_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
return v___x_4422_;
}
}
}
}
}
else
{
lean_del_object(v___x_3860_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
v_a_3852_ = v___x_3904_;
goto v___jp_3851_;
}
v___jp_3863_:
{
lean_object* v___x_3868_; 
lean_inc(v_mvarId_3827_);
v___x_3868_ = l_Lean_MVarId_getType(v_mvarId_3827_, v___y_3866_, v___y_3867_, v___y_3865_, v___y_3864_);
if (lean_obj_tag(v___x_3868_) == 0)
{
lean_object* v_a_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v_a_3869_ = lean_ctor_get(v___x_3868_, 0);
lean_inc(v_a_3869_);
lean_dec_ref_known(v___x_3868_, 1);
v___x_3870_ = l_Lean_LocalDecl_toExpr(v_val_3858_);
v___x_3871_ = l_Lean_Meta_mkNoConfusion(v_a_3869_, v___x_3870_, v___y_3866_, v___y_3867_, v___y_3865_, v___y_3864_);
if (lean_obj_tag(v___x_3871_) == 0)
{
lean_object* v_a_3872_; lean_object* v___x_3873_; 
v_a_3872_ = lean_ctor_get(v___x_3871_, 0);
lean_inc(v_a_3872_);
lean_dec_ref_known(v___x_3871_, 1);
v___x_3873_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3827_, v_a_3872_, v___y_3867_);
if (lean_obj_tag(v___x_3873_) == 0)
{
lean_object* v___x_3874_; lean_object* v___x_3876_; 
lean_dec_ref_known(v___x_3873_, 1);
v___x_3874_ = lean_box(v___x_3837_);
if (v_isShared_3861_ == 0)
{
lean_ctor_set(v___x_3860_, 0, v___x_3874_);
v___x_3876_ = v___x_3860_;
goto v_reusejp_3875_;
}
else
{
lean_object* v_reuseFailAlloc_3879_; 
v_reuseFailAlloc_3879_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3879_, 0, v___x_3874_);
v___x_3876_ = v_reuseFailAlloc_3879_;
goto v_reusejp_3875_;
}
v_reusejp_3875_:
{
lean_object* v___x_3877_; lean_object* v___x_3878_; 
v___x_3877_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3876_);
lean_ctor_set(v___x_3877_, 1, v___x_3862_);
v___x_3878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3878_, 0, v___x_3877_);
v_a_3844_ = v___x_3878_;
goto v___jp_3843_;
}
}
else
{
lean_object* v_a_3880_; lean_object* v___x_3882_; uint8_t v_isShared_3883_; uint8_t v_isSharedCheck_3887_; 
lean_del_object(v___x_3860_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
v_a_3880_ = lean_ctor_get(v___x_3873_, 0);
v_isSharedCheck_3887_ = !lean_is_exclusive(v___x_3873_);
if (v_isSharedCheck_3887_ == 0)
{
v___x_3882_ = v___x_3873_;
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
else
{
lean_inc(v_a_3880_);
lean_dec(v___x_3873_);
v___x_3882_ = lean_box(0);
v_isShared_3883_ = v_isSharedCheck_3887_;
goto v_resetjp_3881_;
}
v_resetjp_3881_:
{
lean_object* v___x_3885_; 
if (v_isShared_3883_ == 0)
{
v___x_3885_ = v___x_3882_;
goto v_reusejp_3884_;
}
else
{
lean_object* v_reuseFailAlloc_3886_; 
v_reuseFailAlloc_3886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3886_, 0, v_a_3880_);
v___x_3885_ = v_reuseFailAlloc_3886_;
goto v_reusejp_3884_;
}
v_reusejp_3884_:
{
return v___x_3885_;
}
}
}
}
else
{
lean_object* v_a_3888_; lean_object* v___x_3890_; uint8_t v_isShared_3891_; uint8_t v_isSharedCheck_3895_; 
lean_del_object(v___x_3860_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_3888_ = lean_ctor_get(v___x_3871_, 0);
v_isSharedCheck_3895_ = !lean_is_exclusive(v___x_3871_);
if (v_isSharedCheck_3895_ == 0)
{
v___x_3890_ = v___x_3871_;
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
else
{
lean_inc(v_a_3888_);
lean_dec(v___x_3871_);
v___x_3890_ = lean_box(0);
v_isShared_3891_ = v_isSharedCheck_3895_;
goto v_resetjp_3889_;
}
v_resetjp_3889_:
{
lean_object* v___x_3893_; 
if (v_isShared_3891_ == 0)
{
v___x_3893_ = v___x_3890_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v_a_3888_);
v___x_3893_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
return v___x_3893_;
}
}
}
}
else
{
lean_object* v_a_3896_; lean_object* v___x_3898_; uint8_t v_isShared_3899_; uint8_t v_isSharedCheck_3903_; 
lean_del_object(v___x_3860_);
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
v_a_3896_ = lean_ctor_get(v___x_3868_, 0);
v_isSharedCheck_3903_ = !lean_is_exclusive(v___x_3868_);
if (v_isSharedCheck_3903_ == 0)
{
v___x_3898_ = v___x_3868_;
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
else
{
lean_inc(v_a_3896_);
lean_dec(v___x_3868_);
v___x_3898_ = lean_box(0);
v_isShared_3899_ = v_isSharedCheck_3903_;
goto v_resetjp_3897_;
}
v_resetjp_3897_:
{
lean_object* v___x_3901_; 
if (v_isShared_3899_ == 0)
{
v___x_3901_ = v___x_3898_;
goto v_reusejp_3900_;
}
else
{
lean_object* v_reuseFailAlloc_3902_; 
v_reuseFailAlloc_3902_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_a_3896_);
v___x_3901_ = v_reuseFailAlloc_3902_;
goto v_reusejp_3900_;
}
v_reusejp_3900_:
{
return v___x_3901_;
}
}
}
}
v___jp_3905_:
{
lean_object* v_searchFuel_3910_; lean_object* v___x_3911_; lean_object* v___x_3912_; 
v_searchFuel_3910_ = lean_ctor_get(v_config_3826_, 0);
v___x_3911_ = l_Lean_LocalDecl_fvarId(v_val_3858_);
lean_dec(v_val_3858_);
lean_inc(v_searchFuel_3910_);
lean_inc(v_mvarId_3827_);
v___x_3912_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3827_, v___x_3911_, v_searchFuel_3910_, v___y_3909_, v___y_3907_, v___y_3906_, v___y_3908_);
if (lean_obj_tag(v___x_3912_) == 0)
{
lean_object* v_a_3913_; uint8_t v___x_3914_; 
v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc(v_a_3913_);
lean_dec_ref_known(v___x_3912_, 1);
v___x_3914_ = lean_unbox(v_a_3913_);
lean_dec(v_a_3913_);
if (v___x_3914_ == 0)
{
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
v_a_3852_ = v___x_3904_;
goto v___jp_3851_;
}
else
{
lean_object* v___x_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v___x_3915_ = lean_box(v___x_3837_);
v___x_3916_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3916_, 0, v___x_3915_);
v___x_3917_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3917_, 0, v___x_3916_);
lean_ctor_set(v___x_3917_, 1, v___x_3862_);
v___x_3918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
v_a_3844_ = v___x_3918_;
goto v___jp_3843_;
}
}
else
{
lean_object* v_a_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3926_; 
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_3919_ = lean_ctor_get(v___x_3912_, 0);
v_isSharedCheck_3926_ = !lean_is_exclusive(v___x_3912_);
if (v_isSharedCheck_3926_ == 0)
{
v___x_3921_ = v___x_3912_;
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_a_3919_);
lean_dec(v___x_3912_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3926_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3924_; 
if (v_isShared_3922_ == 0)
{
v___x_3924_ = v___x_3921_;
goto v_reusejp_3923_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v_a_3919_);
v___x_3924_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3923_;
}
v_reusejp_3923_:
{
return v___x_3924_;
}
}
}
}
v___jp_3927_:
{
if (v___y_3932_ == 0)
{
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
v_a_3852_ = v___x_3904_;
goto v___jp_3851_;
}
else
{
v___y_3906_ = v___y_3929_;
v___y_3907_ = v___y_3928_;
v___y_3908_ = v___y_3930_;
v___y_3909_ = v___y_3931_;
goto v___jp_3905_;
}
}
v___jp_3934_:
{
if (v___y_3939_ == 0)
{
v___y_3906_ = v___y_3936_;
v___y_3907_ = v___y_3935_;
v___y_3908_ = v___y_3937_;
v___y_3909_ = v___y_3938_;
goto v___jp_3905_;
}
else
{
v___y_3928_ = v___y_3935_;
v___y_3929_ = v___y_3936_;
v___y_3930_ = v___y_3937_;
v___y_3931_ = v___y_3938_;
v___y_3932_ = v___x_3933_;
goto v___jp_3927_;
}
}
v___jp_3940_:
{
if (v___y_3946_ == 0)
{
v___y_3928_ = v___y_3942_;
v___y_3929_ = v___y_3941_;
v___y_3930_ = v___y_3943_;
v___y_3931_ = v___y_3944_;
v___y_3932_ = v___x_3933_;
goto v___jp_3927_;
}
else
{
v___y_3935_ = v___y_3942_;
v___y_3936_ = v___y_3941_;
v___y_3937_ = v___y_3943_;
v___y_3938_ = v___y_3944_;
v___y_3939_ = v___y_3945_;
goto v___jp_3934_;
}
}
v___jp_3947_:
{
uint8_t v_emptyType_3954_; 
v_emptyType_3954_ = lean_ctor_get_uint8(v_config_3826_, sizeof(void*)*1 + 1);
if (v_emptyType_3954_ == 0)
{
v___y_3941_ = v___y_3952_;
v___y_3942_ = v___y_3951_;
v___y_3943_ = v___y_3953_;
v___y_3944_ = v___y_3950_;
v___y_3945_ = v___y_3949_;
v___y_3946_ = v___x_3933_;
goto v___jp_3940_;
}
else
{
if (v___y_3948_ == 0)
{
v___y_3935_ = v___y_3951_;
v___y_3936_ = v___y_3952_;
v___y_3937_ = v___y_3953_;
v___y_3938_ = v___y_3950_;
v___y_3939_ = v___y_3949_;
goto v___jp_3934_;
}
else
{
v___y_3941_ = v___y_3952_;
v___y_3942_ = v___y_3951_;
v___y_3943_ = v___y_3953_;
v___y_3944_ = v___y_3950_;
v___y_3945_ = v___y_3949_;
v___y_3946_ = v___x_3933_;
goto v___jp_3940_;
}
}
}
v___jp_3955_:
{
if (v___y_3962_ == 0)
{
v___y_3948_ = v___y_3956_;
v___y_3949_ = v___y_3961_;
v___y_3950_ = v___y_3958_;
v___y_3951_ = v___y_3959_;
v___y_3952_ = v___y_3957_;
v___y_3953_ = v___y_3960_;
goto v___jp_3947_;
}
else
{
lean_object* v___x_3963_; 
lean_inc(v_val_3858_);
lean_inc(v_mvarId_3827_);
v___x_3963_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3827_, v_val_3858_, v___y_3958_, v___y_3959_, v___y_3957_, v___y_3960_);
if (lean_obj_tag(v___x_3963_) == 0)
{
lean_object* v_a_3964_; uint8_t v___x_3965_; 
v_a_3964_ = lean_ctor_get(v___x_3963_, 0);
lean_inc(v_a_3964_);
lean_dec_ref_known(v___x_3963_, 1);
v___x_3965_ = lean_unbox(v_a_3964_);
lean_dec(v_a_3964_);
if (v___x_3965_ == 0)
{
v___y_3948_ = v___y_3956_;
v___y_3949_ = v___y_3961_;
v___y_3950_ = v___y_3958_;
v___y_3951_ = v___y_3959_;
v___y_3952_ = v___y_3957_;
v___y_3953_ = v___y_3960_;
goto v___jp_3947_;
}
else
{
lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; 
lean_dec(v_val_3858_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v___x_3966_ = lean_box(v___x_3837_);
v___x_3967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3967_, 0, v___x_3966_);
v___x_3968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3967_);
lean_ctor_set(v___x_3968_, 1, v___x_3862_);
v___x_3969_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3969_, 0, v___x_3968_);
v_a_3844_ = v___x_3969_;
goto v___jp_3843_;
}
}
else
{
lean_object* v_a_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3977_; 
lean_dec(v_val_3858_);
lean_del_object(v___x_3841_);
lean_dec(v_snd_3839_);
lean_dec(v_mvarId_3827_);
lean_dec_ref(v_config_3826_);
v_a_3970_ = lean_ctor_get(v___x_3963_, 0);
v_isSharedCheck_3977_ = !lean_is_exclusive(v___x_3963_);
if (v_isSharedCheck_3977_ == 0)
{
v___x_3972_ = v___x_3963_;
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_a_3970_);
lean_dec(v___x_3963_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3977_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3975_; 
if (v_isShared_3973_ == 0)
{
v___x_3975_ = v___x_3972_;
goto v_reusejp_3974_;
}
else
{
lean_object* v_reuseFailAlloc_3976_; 
v_reuseFailAlloc_3976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3976_, 0, v_a_3970_);
v___x_3975_ = v_reuseFailAlloc_3976_;
goto v_reusejp_3974_;
}
v_reusejp_3974_:
{
return v___x_3975_;
}
}
}
}
}
}
}
v___jp_3843_:
{
lean_object* v___x_3845_; lean_object* v___x_3847_; 
v___x_3845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3845_, 0, v_a_3844_);
if (v_isShared_3842_ == 0)
{
lean_ctor_set(v___x_3841_, 0, v___x_3845_);
v___x_3847_ = v___x_3841_;
goto v_reusejp_3846_;
}
else
{
lean_object* v_reuseFailAlloc_3849_; 
v_reuseFailAlloc_3849_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3849_, 0, v___x_3845_);
lean_ctor_set(v_reuseFailAlloc_3849_, 1, v_snd_3839_);
v___x_3847_ = v_reuseFailAlloc_3849_;
goto v_reusejp_3846_;
}
v_reusejp_3846_:
{
lean_object* v___x_3848_; 
v___x_3848_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3848_, 0, v___x_3847_);
return v___x_3848_;
}
}
v___jp_3851_:
{
lean_object* v___x_3853_; size_t v___x_3854_; size_t v___x_3855_; lean_object* v___x_3856_; 
v___x_3853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3853_, 0, v___x_3850_);
lean_ctor_set(v___x_3853_, 1, v_a_3852_);
v___x_3854_ = ((size_t)1ULL);
v___x_3855_ = lean_usize_add(v_i_3830_, v___x_3854_);
v___x_3856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3826_, v_mvarId_3827_, v_as_3828_, v_sz_3829_, v___x_3855_, v___x_3853_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
return v___x_3856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4498_, lean_object* v_mvarId_4499_, lean_object* v_as_4500_, lean_object* v_sz_4501_, lean_object* v_i_4502_, lean_object* v_b_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_){
_start:
{
size_t v_sz_boxed_4509_; size_t v_i_boxed_4510_; lean_object* v_res_4511_; 
v_sz_boxed_4509_ = lean_unbox_usize(v_sz_4501_);
lean_dec(v_sz_4501_);
v_i_boxed_4510_ = lean_unbox_usize(v_i_4502_);
lean_dec(v_i_4502_);
v_res_4511_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4498_, v_mvarId_4499_, v_as_4500_, v_sz_boxed_4509_, v_i_boxed_4510_, v_b_4503_, v___y_4504_, v___y_4505_, v___y_4506_, v___y_4507_);
lean_dec(v___y_4507_);
lean_dec_ref(v___y_4506_);
lean_dec(v___y_4505_);
lean_dec_ref(v___y_4504_);
lean_dec_ref(v_as_4500_);
return v_res_4511_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4512_, lean_object* v_config_4513_, lean_object* v_mvarId_4514_, lean_object* v_n_4515_, lean_object* v_b_4516_, lean_object* v___y_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_){
_start:
{
if (lean_obj_tag(v_n_4515_) == 0)
{
lean_object* v_cs_4522_; lean_object* v___x_4523_; lean_object* v___x_4524_; size_t v_sz_4525_; size_t v___x_4526_; lean_object* v___x_4527_; 
v_cs_4522_ = lean_ctor_get(v_n_4515_, 0);
v___x_4523_ = lean_box(0);
v___x_4524_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4524_, 0, v___x_4523_);
lean_ctor_set(v___x_4524_, 1, v_b_4516_);
v_sz_4525_ = lean_array_size(v_cs_4522_);
v___x_4526_ = ((size_t)0ULL);
v___x_4527_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4512_, v_config_4513_, v_mvarId_4514_, v_cs_4522_, v_sz_4525_, v___x_4526_, v___x_4524_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
if (lean_obj_tag(v___x_4527_) == 0)
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4542_; 
v_a_4528_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4542_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4542_ == 0)
{
v___x_4530_ = v___x_4527_;
v_isShared_4531_ = v_isSharedCheck_4542_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4527_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4542_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v_fst_4532_; 
v_fst_4532_ = lean_ctor_get(v_a_4528_, 0);
if (lean_obj_tag(v_fst_4532_) == 0)
{
lean_object* v_snd_4533_; lean_object* v___x_4534_; lean_object* v___x_4536_; 
v_snd_4533_ = lean_ctor_get(v_a_4528_, 1);
lean_inc(v_snd_4533_);
lean_dec(v_a_4528_);
v___x_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4534_, 0, v_snd_4533_);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v___x_4534_);
v___x_4536_ = v___x_4530_;
goto v_reusejp_4535_;
}
else
{
lean_object* v_reuseFailAlloc_4537_; 
v_reuseFailAlloc_4537_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4537_, 0, v___x_4534_);
v___x_4536_ = v_reuseFailAlloc_4537_;
goto v_reusejp_4535_;
}
v_reusejp_4535_:
{
return v___x_4536_;
}
}
else
{
lean_object* v_val_4538_; lean_object* v___x_4540_; 
lean_inc_ref(v_fst_4532_);
lean_dec(v_a_4528_);
v_val_4538_ = lean_ctor_get(v_fst_4532_, 0);
lean_inc(v_val_4538_);
lean_dec_ref_known(v_fst_4532_, 1);
if (v_isShared_4531_ == 0)
{
lean_ctor_set(v___x_4530_, 0, v_val_4538_);
v___x_4540_ = v___x_4530_;
goto v_reusejp_4539_;
}
else
{
lean_object* v_reuseFailAlloc_4541_; 
v_reuseFailAlloc_4541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4541_, 0, v_val_4538_);
v___x_4540_ = v_reuseFailAlloc_4541_;
goto v_reusejp_4539_;
}
v_reusejp_4539_:
{
return v___x_4540_;
}
}
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
v_a_4543_ = lean_ctor_get(v___x_4527_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4527_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4527_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4527_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
}
else
{
lean_object* v_vs_4551_; lean_object* v___x_4552_; lean_object* v___x_4553_; size_t v_sz_4554_; size_t v___x_4555_; lean_object* v___x_4556_; 
v_vs_4551_ = lean_ctor_get(v_n_4515_, 0);
v___x_4552_ = lean_box(0);
v___x_4553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4553_, 0, v___x_4552_);
lean_ctor_set(v___x_4553_, 1, v_b_4516_);
v_sz_4554_ = lean_array_size(v_vs_4551_);
v___x_4555_ = ((size_t)0ULL);
v___x_4556_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4513_, v_mvarId_4514_, v_vs_4551_, v_sz_4554_, v___x_4555_, v___x_4553_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
if (lean_obj_tag(v___x_4556_) == 0)
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4571_; 
v_a_4557_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4571_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4571_ == 0)
{
v___x_4559_ = v___x_4556_;
v_isShared_4560_ = v_isSharedCheck_4571_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4556_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4571_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v_fst_4561_; 
v_fst_4561_ = lean_ctor_get(v_a_4557_, 0);
if (lean_obj_tag(v_fst_4561_) == 0)
{
lean_object* v_snd_4562_; lean_object* v___x_4563_; lean_object* v___x_4565_; 
v_snd_4562_ = lean_ctor_get(v_a_4557_, 1);
lean_inc(v_snd_4562_);
lean_dec(v_a_4557_);
v___x_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4563_, 0, v_snd_4562_);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 0, v___x_4563_);
v___x_4565_ = v___x_4559_;
goto v_reusejp_4564_;
}
else
{
lean_object* v_reuseFailAlloc_4566_; 
v_reuseFailAlloc_4566_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4566_, 0, v___x_4563_);
v___x_4565_ = v_reuseFailAlloc_4566_;
goto v_reusejp_4564_;
}
v_reusejp_4564_:
{
return v___x_4565_;
}
}
else
{
lean_object* v_val_4567_; lean_object* v___x_4569_; 
lean_inc_ref(v_fst_4561_);
lean_dec(v_a_4557_);
v_val_4567_ = lean_ctor_get(v_fst_4561_, 0);
lean_inc(v_val_4567_);
lean_dec_ref_known(v_fst_4561_, 1);
if (v_isShared_4560_ == 0)
{
lean_ctor_set(v___x_4559_, 0, v_val_4567_);
v___x_4569_ = v___x_4559_;
goto v_reusejp_4568_;
}
else
{
lean_object* v_reuseFailAlloc_4570_; 
v_reuseFailAlloc_4570_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4570_, 0, v_val_4567_);
v___x_4569_ = v_reuseFailAlloc_4570_;
goto v_reusejp_4568_;
}
v_reusejp_4568_:
{
return v___x_4569_;
}
}
}
}
else
{
lean_object* v_a_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4579_; 
v_a_4572_ = lean_ctor_get(v___x_4556_, 0);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4556_);
if (v_isSharedCheck_4579_ == 0)
{
v___x_4574_ = v___x_4556_;
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_a_4572_);
lean_dec(v___x_4556_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4579_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
lean_object* v___x_4577_; 
if (v_isShared_4575_ == 0)
{
v___x_4577_ = v___x_4574_;
goto v_reusejp_4576_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v_a_4572_);
v___x_4577_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4576_;
}
v_reusejp_4576_:
{
return v___x_4577_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4580_, lean_object* v_config_4581_, lean_object* v_mvarId_4582_, lean_object* v_as_4583_, size_t v_sz_4584_, size_t v_i_4585_, lean_object* v_b_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_){
_start:
{
uint8_t v___x_4592_; 
v___x_4592_ = lean_usize_dec_lt(v_i_4585_, v_sz_4584_);
if (v___x_4592_ == 0)
{
lean_object* v___x_4593_; 
lean_dec(v_mvarId_4582_);
lean_dec_ref(v_config_4581_);
v___x_4593_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4593_, 0, v_b_4586_);
return v___x_4593_;
}
else
{
lean_object* v_snd_4594_; lean_object* v___x_4596_; uint8_t v_isShared_4597_; uint8_t v_isSharedCheck_4628_; 
v_snd_4594_ = lean_ctor_get(v_b_4586_, 1);
v_isSharedCheck_4628_ = !lean_is_exclusive(v_b_4586_);
if (v_isSharedCheck_4628_ == 0)
{
lean_object* v_unused_4629_; 
v_unused_4629_ = lean_ctor_get(v_b_4586_, 0);
lean_dec(v_unused_4629_);
v___x_4596_ = v_b_4586_;
v_isShared_4597_ = v_isSharedCheck_4628_;
goto v_resetjp_4595_;
}
else
{
lean_inc(v_snd_4594_);
lean_dec(v_b_4586_);
v___x_4596_ = lean_box(0);
v_isShared_4597_ = v_isSharedCheck_4628_;
goto v_resetjp_4595_;
}
v_resetjp_4595_:
{
lean_object* v_a_4598_; lean_object* v___x_4599_; 
v_a_4598_ = lean_array_uget_borrowed(v_as_4583_, v_i_4585_);
lean_inc(v_snd_4594_);
lean_inc(v_mvarId_4582_);
lean_inc_ref(v_config_4581_);
v___x_4599_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4580_, v_config_4581_, v_mvarId_4582_, v_a_4598_, v_snd_4594_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v_a_4600_; lean_object* v___x_4602_; uint8_t v_isShared_4603_; uint8_t v_isSharedCheck_4619_; 
v_a_4600_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4619_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4619_ == 0)
{
v___x_4602_ = v___x_4599_;
v_isShared_4603_ = v_isSharedCheck_4619_;
goto v_resetjp_4601_;
}
else
{
lean_inc(v_a_4600_);
lean_dec(v___x_4599_);
v___x_4602_ = lean_box(0);
v_isShared_4603_ = v_isSharedCheck_4619_;
goto v_resetjp_4601_;
}
v_resetjp_4601_:
{
if (lean_obj_tag(v_a_4600_) == 0)
{
lean_object* v___x_4604_; lean_object* v___x_4606_; 
lean_dec(v_mvarId_4582_);
lean_dec_ref(v_config_4581_);
v___x_4604_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4604_, 0, v_a_4600_);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 0, v___x_4604_);
v___x_4606_ = v___x_4596_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4610_; 
v_reuseFailAlloc_4610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4610_, 0, v___x_4604_);
lean_ctor_set(v_reuseFailAlloc_4610_, 1, v_snd_4594_);
v___x_4606_ = v_reuseFailAlloc_4610_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
lean_object* v___x_4608_; 
if (v_isShared_4603_ == 0)
{
lean_ctor_set(v___x_4602_, 0, v___x_4606_);
v___x_4608_ = v___x_4602_;
goto v_reusejp_4607_;
}
else
{
lean_object* v_reuseFailAlloc_4609_; 
v_reuseFailAlloc_4609_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4609_, 0, v___x_4606_);
v___x_4608_ = v_reuseFailAlloc_4609_;
goto v_reusejp_4607_;
}
v_reusejp_4607_:
{
return v___x_4608_;
}
}
}
else
{
lean_object* v_a_4611_; lean_object* v___x_4612_; lean_object* v___x_4614_; 
lean_del_object(v___x_4602_);
lean_dec(v_snd_4594_);
v_a_4611_ = lean_ctor_get(v_a_4600_, 0);
lean_inc(v_a_4611_);
lean_dec_ref_known(v_a_4600_, 1);
v___x_4612_ = lean_box(0);
if (v_isShared_4597_ == 0)
{
lean_ctor_set(v___x_4596_, 1, v_a_4611_);
lean_ctor_set(v___x_4596_, 0, v___x_4612_);
v___x_4614_ = v___x_4596_;
goto v_reusejp_4613_;
}
else
{
lean_object* v_reuseFailAlloc_4618_; 
v_reuseFailAlloc_4618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4618_, 0, v___x_4612_);
lean_ctor_set(v_reuseFailAlloc_4618_, 1, v_a_4611_);
v___x_4614_ = v_reuseFailAlloc_4618_;
goto v_reusejp_4613_;
}
v_reusejp_4613_:
{
size_t v___x_4615_; size_t v___x_4616_; 
v___x_4615_ = ((size_t)1ULL);
v___x_4616_ = lean_usize_add(v_i_4585_, v___x_4615_);
v_i_4585_ = v___x_4616_;
v_b_4586_ = v___x_4614_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4620_; lean_object* v___x_4622_; uint8_t v_isShared_4623_; uint8_t v_isSharedCheck_4627_; 
lean_del_object(v___x_4596_);
lean_dec(v_snd_4594_);
lean_dec(v_mvarId_4582_);
lean_dec_ref(v_config_4581_);
v_a_4620_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4627_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4627_ == 0)
{
v___x_4622_ = v___x_4599_;
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
else
{
lean_inc(v_a_4620_);
lean_dec(v___x_4599_);
v___x_4622_ = lean_box(0);
v_isShared_4623_ = v_isSharedCheck_4627_;
goto v_resetjp_4621_;
}
v_resetjp_4621_:
{
lean_object* v___x_4625_; 
if (v_isShared_4623_ == 0)
{
v___x_4625_ = v___x_4622_;
goto v_reusejp_4624_;
}
else
{
lean_object* v_reuseFailAlloc_4626_; 
v_reuseFailAlloc_4626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4626_, 0, v_a_4620_);
v___x_4625_ = v_reuseFailAlloc_4626_;
goto v_reusejp_4624_;
}
v_reusejp_4624_:
{
return v___x_4625_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4630_, lean_object* v_config_4631_, lean_object* v_mvarId_4632_, lean_object* v_as_4633_, lean_object* v_sz_4634_, lean_object* v_i_4635_, lean_object* v_b_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_, lean_object* v___y_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_){
_start:
{
size_t v_sz_boxed_4642_; size_t v_i_boxed_4643_; lean_object* v_res_4644_; 
v_sz_boxed_4642_ = lean_unbox_usize(v_sz_4634_);
lean_dec(v_sz_4634_);
v_i_boxed_4643_ = lean_unbox_usize(v_i_4635_);
lean_dec(v_i_4635_);
v_res_4644_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4630_, v_config_4631_, v_mvarId_4632_, v_as_4633_, v_sz_boxed_4642_, v_i_boxed_4643_, v_b_4636_, v___y_4637_, v___y_4638_, v___y_4639_, v___y_4640_);
lean_dec(v___y_4640_);
lean_dec_ref(v___y_4639_);
lean_dec(v___y_4638_);
lean_dec_ref(v___y_4637_);
lean_dec_ref(v_as_4633_);
lean_dec_ref(v_init_4630_);
return v_res_4644_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4645_, lean_object* v_config_4646_, lean_object* v_mvarId_4647_, lean_object* v_n_4648_, lean_object* v_b_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4645_, v_config_4646_, v_mvarId_4647_, v_n_4648_, v_b_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec_ref(v_n_4648_);
lean_dec_ref(v_init_4645_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4656_, lean_object* v_mvarId_4657_, lean_object* v_t_4658_, lean_object* v_init_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_){
_start:
{
lean_object* v_root_4665_; lean_object* v_tail_4666_; lean_object* v___x_4667_; 
v_root_4665_ = lean_ctor_get(v_t_4658_, 0);
v_tail_4666_ = lean_ctor_get(v_t_4658_, 1);
lean_inc(v_mvarId_4657_);
lean_inc_ref(v_config_4656_);
lean_inc_ref(v_init_4659_);
v___x_4667_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4659_, v_config_4656_, v_mvarId_4657_, v_root_4665_, v_init_4659_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
lean_dec_ref(v_init_4659_);
if (lean_obj_tag(v___x_4667_) == 0)
{
lean_object* v_a_4668_; lean_object* v___x_4670_; uint8_t v_isShared_4671_; uint8_t v_isSharedCheck_4704_; 
v_a_4668_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4704_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4704_ == 0)
{
v___x_4670_ = v___x_4667_;
v_isShared_4671_ = v_isSharedCheck_4704_;
goto v_resetjp_4669_;
}
else
{
lean_inc(v_a_4668_);
lean_dec(v___x_4667_);
v___x_4670_ = lean_box(0);
v_isShared_4671_ = v_isSharedCheck_4704_;
goto v_resetjp_4669_;
}
v_resetjp_4669_:
{
if (lean_obj_tag(v_a_4668_) == 0)
{
lean_object* v_a_4672_; lean_object* v___x_4674_; 
lean_dec(v_mvarId_4657_);
lean_dec_ref(v_config_4656_);
v_a_4672_ = lean_ctor_get(v_a_4668_, 0);
lean_inc(v_a_4672_);
lean_dec_ref_known(v_a_4668_, 1);
if (v_isShared_4671_ == 0)
{
lean_ctor_set(v___x_4670_, 0, v_a_4672_);
v___x_4674_ = v___x_4670_;
goto v_reusejp_4673_;
}
else
{
lean_object* v_reuseFailAlloc_4675_; 
v_reuseFailAlloc_4675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4675_, 0, v_a_4672_);
v___x_4674_ = v_reuseFailAlloc_4675_;
goto v_reusejp_4673_;
}
v_reusejp_4673_:
{
return v___x_4674_;
}
}
else
{
lean_object* v_a_4676_; lean_object* v___x_4677_; lean_object* v___x_4678_; size_t v_sz_4679_; size_t v___x_4680_; lean_object* v___x_4681_; 
lean_del_object(v___x_4670_);
v_a_4676_ = lean_ctor_get(v_a_4668_, 0);
lean_inc(v_a_4676_);
lean_dec_ref_known(v_a_4668_, 1);
v___x_4677_ = lean_box(0);
v___x_4678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4678_, 0, v___x_4677_);
lean_ctor_set(v___x_4678_, 1, v_a_4676_);
v_sz_4679_ = lean_array_size(v_tail_4666_);
v___x_4680_ = ((size_t)0ULL);
v___x_4681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4656_, v_mvarId_4657_, v_tail_4666_, v_sz_4679_, v___x_4680_, v___x_4678_, v___y_4660_, v___y_4661_, v___y_4662_, v___y_4663_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v___x_4684_; uint8_t v_isShared_4685_; uint8_t v_isSharedCheck_4695_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4695_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4695_ == 0)
{
v___x_4684_ = v___x_4681_;
v_isShared_4685_ = v_isSharedCheck_4695_;
goto v_resetjp_4683_;
}
else
{
lean_inc(v_a_4682_);
lean_dec(v___x_4681_);
v___x_4684_ = lean_box(0);
v_isShared_4685_ = v_isSharedCheck_4695_;
goto v_resetjp_4683_;
}
v_resetjp_4683_:
{
lean_object* v_fst_4686_; 
v_fst_4686_ = lean_ctor_get(v_a_4682_, 0);
if (lean_obj_tag(v_fst_4686_) == 0)
{
lean_object* v_snd_4687_; lean_object* v___x_4689_; 
v_snd_4687_ = lean_ctor_get(v_a_4682_, 1);
lean_inc(v_snd_4687_);
lean_dec(v_a_4682_);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v_snd_4687_);
v___x_4689_ = v___x_4684_;
goto v_reusejp_4688_;
}
else
{
lean_object* v_reuseFailAlloc_4690_; 
v_reuseFailAlloc_4690_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4690_, 0, v_snd_4687_);
v___x_4689_ = v_reuseFailAlloc_4690_;
goto v_reusejp_4688_;
}
v_reusejp_4688_:
{
return v___x_4689_;
}
}
else
{
lean_object* v_val_4691_; lean_object* v___x_4693_; 
lean_inc_ref(v_fst_4686_);
lean_dec(v_a_4682_);
v_val_4691_ = lean_ctor_get(v_fst_4686_, 0);
lean_inc(v_val_4691_);
lean_dec_ref_known(v_fst_4686_, 1);
if (v_isShared_4685_ == 0)
{
lean_ctor_set(v___x_4684_, 0, v_val_4691_);
v___x_4693_ = v___x_4684_;
goto v_reusejp_4692_;
}
else
{
lean_object* v_reuseFailAlloc_4694_; 
v_reuseFailAlloc_4694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4694_, 0, v_val_4691_);
v___x_4693_ = v_reuseFailAlloc_4694_;
goto v_reusejp_4692_;
}
v_reusejp_4692_:
{
return v___x_4693_;
}
}
}
}
else
{
lean_object* v_a_4696_; lean_object* v___x_4698_; uint8_t v_isShared_4699_; uint8_t v_isSharedCheck_4703_; 
v_a_4696_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4703_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4703_ == 0)
{
v___x_4698_ = v___x_4681_;
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
else
{
lean_inc(v_a_4696_);
lean_dec(v___x_4681_);
v___x_4698_ = lean_box(0);
v_isShared_4699_ = v_isSharedCheck_4703_;
goto v_resetjp_4697_;
}
v_resetjp_4697_:
{
lean_object* v___x_4701_; 
if (v_isShared_4699_ == 0)
{
v___x_4701_ = v___x_4698_;
goto v_reusejp_4700_;
}
else
{
lean_object* v_reuseFailAlloc_4702_; 
v_reuseFailAlloc_4702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4702_, 0, v_a_4696_);
v___x_4701_ = v_reuseFailAlloc_4702_;
goto v_reusejp_4700_;
}
v_reusejp_4700_:
{
return v___x_4701_;
}
}
}
}
}
}
else
{
lean_object* v_a_4705_; lean_object* v___x_4707_; uint8_t v_isShared_4708_; uint8_t v_isSharedCheck_4712_; 
lean_dec(v_mvarId_4657_);
lean_dec_ref(v_config_4656_);
v_a_4705_ = lean_ctor_get(v___x_4667_, 0);
v_isSharedCheck_4712_ = !lean_is_exclusive(v___x_4667_);
if (v_isSharedCheck_4712_ == 0)
{
v___x_4707_ = v___x_4667_;
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
else
{
lean_inc(v_a_4705_);
lean_dec(v___x_4667_);
v___x_4707_ = lean_box(0);
v_isShared_4708_ = v_isSharedCheck_4712_;
goto v_resetjp_4706_;
}
v_resetjp_4706_:
{
lean_object* v___x_4710_; 
if (v_isShared_4708_ == 0)
{
v___x_4710_ = v___x_4707_;
goto v_reusejp_4709_;
}
else
{
lean_object* v_reuseFailAlloc_4711_; 
v_reuseFailAlloc_4711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4711_, 0, v_a_4705_);
v___x_4710_ = v_reuseFailAlloc_4711_;
goto v_reusejp_4709_;
}
v_reusejp_4709_:
{
return v___x_4710_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4713_, lean_object* v_mvarId_4714_, lean_object* v_t_4715_, lean_object* v_init_4716_, lean_object* v___y_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v_res_4722_; 
v_res_4722_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4713_, v_mvarId_4714_, v_t_4715_, v_init_4716_, v___y_4717_, v___y_4718_, v___y_4719_, v___y_4720_);
lean_dec(v___y_4720_);
lean_dec_ref(v___y_4719_);
lean_dec(v___y_4718_);
lean_dec_ref(v___y_4717_);
lean_dec_ref(v_t_4715_);
return v_res_4722_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4723_, lean_object* v___x_4724_, lean_object* v_config_4725_, lean_object* v___y_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
lean_object* v___x_4731_; 
lean_inc(v_mvarId_4723_);
v___x_4731_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4723_, v___x_4724_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
if (lean_obj_tag(v___x_4731_) == 0)
{
lean_object* v___x_4732_; 
lean_dec_ref_known(v___x_4731_, 1);
lean_inc(v_mvarId_4723_);
v___x_4732_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4723_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
if (lean_obj_tag(v___x_4732_) == 0)
{
lean_object* v_a_4733_; lean_object* v___x_4735_; uint8_t v_isShared_4736_; uint8_t v_isSharedCheck_4766_; 
v_a_4733_ = lean_ctor_get(v___x_4732_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4732_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4735_ = v___x_4732_;
v_isShared_4736_ = v_isSharedCheck_4766_;
goto v_resetjp_4734_;
}
else
{
lean_inc(v_a_4733_);
lean_dec(v___x_4732_);
v___x_4735_ = lean_box(0);
v_isShared_4736_ = v_isSharedCheck_4766_;
goto v_resetjp_4734_;
}
v_resetjp_4734_:
{
uint8_t v___x_4737_; 
v___x_4737_ = lean_unbox(v_a_4733_);
if (v___x_4737_ == 0)
{
lean_object* v_lctx_4738_; lean_object* v_decls_4739_; lean_object* v___x_4740_; lean_object* v___x_4741_; 
lean_del_object(v___x_4735_);
v_lctx_4738_ = lean_ctor_get(v___y_4726_, 2);
v_decls_4739_ = lean_ctor_get(v_lctx_4738_, 1);
v___x_4740_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4741_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4725_, v_mvarId_4723_, v_decls_4739_, v___x_4740_, v___y_4726_, v___y_4727_, v___y_4728_, v___y_4729_);
if (lean_obj_tag(v___x_4741_) == 0)
{
lean_object* v_a_4742_; lean_object* v___x_4744_; uint8_t v_isShared_4745_; uint8_t v_isSharedCheck_4754_; 
v_a_4742_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4744_ = v___x_4741_;
v_isShared_4745_ = v_isSharedCheck_4754_;
goto v_resetjp_4743_;
}
else
{
lean_inc(v_a_4742_);
lean_dec(v___x_4741_);
v___x_4744_ = lean_box(0);
v_isShared_4745_ = v_isSharedCheck_4754_;
goto v_resetjp_4743_;
}
v_resetjp_4743_:
{
lean_object* v_fst_4746_; 
v_fst_4746_ = lean_ctor_get(v_a_4742_, 0);
lean_inc(v_fst_4746_);
lean_dec(v_a_4742_);
if (lean_obj_tag(v_fst_4746_) == 0)
{
lean_object* v___x_4748_; 
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 0, v_a_4733_);
v___x_4748_ = v___x_4744_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4733_);
v___x_4748_ = v_reuseFailAlloc_4749_;
goto v_reusejp_4747_;
}
v_reusejp_4747_:
{
return v___x_4748_;
}
}
else
{
lean_object* v_val_4750_; lean_object* v___x_4752_; 
lean_dec(v_a_4733_);
v_val_4750_ = lean_ctor_get(v_fst_4746_, 0);
lean_inc(v_val_4750_);
lean_dec_ref_known(v_fst_4746_, 1);
if (v_isShared_4745_ == 0)
{
lean_ctor_set(v___x_4744_, 0, v_val_4750_);
v___x_4752_ = v___x_4744_;
goto v_reusejp_4751_;
}
else
{
lean_object* v_reuseFailAlloc_4753_; 
v_reuseFailAlloc_4753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4753_, 0, v_val_4750_);
v___x_4752_ = v_reuseFailAlloc_4753_;
goto v_reusejp_4751_;
}
v_reusejp_4751_:
{
return v___x_4752_;
}
}
}
}
else
{
lean_object* v_a_4755_; lean_object* v___x_4757_; uint8_t v_isShared_4758_; uint8_t v_isSharedCheck_4762_; 
lean_dec(v_a_4733_);
v_a_4755_ = lean_ctor_get(v___x_4741_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4741_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4741_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4741_);
v___x_4757_ = lean_box(0);
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
v_resetjp_4756_:
{
lean_object* v___x_4760_; 
if (v_isShared_4758_ == 0)
{
v___x_4760_ = v___x_4757_;
goto v_reusejp_4759_;
}
else
{
lean_object* v_reuseFailAlloc_4761_; 
v_reuseFailAlloc_4761_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4761_, 0, v_a_4755_);
v___x_4760_ = v_reuseFailAlloc_4761_;
goto v_reusejp_4759_;
}
v_reusejp_4759_:
{
return v___x_4760_;
}
}
}
}
else
{
lean_object* v___x_4764_; 
lean_dec_ref(v_config_4725_);
lean_dec(v_mvarId_4723_);
if (v_isShared_4736_ == 0)
{
v___x_4764_ = v___x_4735_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4733_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
}
else
{
lean_dec_ref(v_config_4725_);
lean_dec(v_mvarId_4723_);
return v___x_4732_;
}
}
else
{
lean_object* v_a_4767_; lean_object* v___x_4769_; uint8_t v_isShared_4770_; uint8_t v_isSharedCheck_4774_; 
lean_dec_ref(v_config_4725_);
lean_dec(v_mvarId_4723_);
v_a_4767_ = lean_ctor_get(v___x_4731_, 0);
v_isSharedCheck_4774_ = !lean_is_exclusive(v___x_4731_);
if (v_isSharedCheck_4774_ == 0)
{
v___x_4769_ = v___x_4731_;
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
else
{
lean_inc(v_a_4767_);
lean_dec(v___x_4731_);
v___x_4769_ = lean_box(0);
v_isShared_4770_ = v_isSharedCheck_4774_;
goto v_resetjp_4768_;
}
v_resetjp_4768_:
{
lean_object* v___x_4772_; 
if (v_isShared_4770_ == 0)
{
v___x_4772_ = v___x_4769_;
goto v_reusejp_4771_;
}
else
{
lean_object* v_reuseFailAlloc_4773_; 
v_reuseFailAlloc_4773_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4773_, 0, v_a_4767_);
v___x_4772_ = v_reuseFailAlloc_4773_;
goto v_reusejp_4771_;
}
v_reusejp_4771_:
{
return v___x_4772_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4775_, lean_object* v___x_4776_, lean_object* v_config_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v_res_4783_; 
v_res_4783_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4775_, v___x_4776_, v_config_4777_, v___y_4778_, v___y_4779_, v___y_4780_, v___y_4781_);
lean_dec(v___y_4781_);
lean_dec_ref(v___y_4780_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
return v_res_4783_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4786_, lean_object* v_config_4787_, lean_object* v_a_4788_, lean_object* v_a_4789_, lean_object* v_a_4790_, lean_object* v_a_4791_){
_start:
{
lean_object* v___x_4793_; lean_object* v___f_4794_; lean_object* v___x_4795_; 
v___x_4793_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4786_);
v___f_4794_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4794_, 0, v_mvarId_4786_);
lean_closure_set(v___f_4794_, 1, v___x_4793_);
lean_closure_set(v___f_4794_, 2, v_config_4787_);
v___x_4795_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4786_, v___f_4794_, v_a_4788_, v_a_4789_, v_a_4790_, v_a_4791_);
return v___x_4795_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4796_, lean_object* v_config_4797_, lean_object* v_a_4798_, lean_object* v_a_4799_, lean_object* v_a_4800_, lean_object* v_a_4801_, lean_object* v_a_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l_Lean_MVarId_contradictionCore(v_mvarId_4796_, v_config_4797_, v_a_4798_, v_a_4799_, v_a_4800_, v_a_4801_);
lean_dec(v_a_4801_);
lean_dec_ref(v_a_4800_);
lean_dec(v_a_4799_);
lean_dec_ref(v_a_4798_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4804_, lean_object* v_config_4805_, lean_object* v_a_4806_, lean_object* v_a_4807_, lean_object* v_a_4808_, lean_object* v_a_4809_){
_start:
{
lean_object* v___x_4811_; 
lean_inc(v_mvarId_4804_);
v___x_4811_ = l_Lean_MVarId_contradictionCore(v_mvarId_4804_, v_config_4805_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_);
if (lean_obj_tag(v___x_4811_) == 0)
{
lean_object* v_a_4812_; lean_object* v___x_4814_; uint8_t v_isShared_4815_; uint8_t v_isSharedCheck_4824_; 
v_a_4812_ = lean_ctor_get(v___x_4811_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4811_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4814_ = v___x_4811_;
v_isShared_4815_ = v_isSharedCheck_4824_;
goto v_resetjp_4813_;
}
else
{
lean_inc(v_a_4812_);
lean_dec(v___x_4811_);
v___x_4814_ = lean_box(0);
v_isShared_4815_ = v_isSharedCheck_4824_;
goto v_resetjp_4813_;
}
v_resetjp_4813_:
{
uint8_t v___x_4816_; 
v___x_4816_ = lean_unbox(v_a_4812_);
lean_dec(v_a_4812_);
if (v___x_4816_ == 0)
{
lean_object* v___x_4817_; lean_object* v___x_4818_; lean_object* v___x_4819_; 
lean_del_object(v___x_4814_);
v___x_4817_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4818_ = lean_box(0);
v___x_4819_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4817_, v_mvarId_4804_, v___x_4818_, v_a_4806_, v_a_4807_, v_a_4808_, v_a_4809_);
return v___x_4819_;
}
else
{
lean_object* v___x_4820_; lean_object* v___x_4822_; 
lean_dec(v_mvarId_4804_);
v___x_4820_ = lean_box(0);
if (v_isShared_4815_ == 0)
{
lean_ctor_set(v___x_4814_, 0, v___x_4820_);
v___x_4822_ = v___x_4814_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v___x_4820_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
}
else
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4832_; 
lean_dec(v_mvarId_4804_);
v_a_4825_ = lean_ctor_get(v___x_4811_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4811_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4827_ = v___x_4811_;
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4811_);
v___x_4827_ = lean_box(0);
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
v_resetjp_4826_:
{
lean_object* v___x_4830_; 
if (v_isShared_4828_ == 0)
{
v___x_4830_ = v___x_4827_;
goto v_reusejp_4829_;
}
else
{
lean_object* v_reuseFailAlloc_4831_; 
v_reuseFailAlloc_4831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4831_, 0, v_a_4825_);
v___x_4830_ = v_reuseFailAlloc_4831_;
goto v_reusejp_4829_;
}
v_reusejp_4829_:
{
return v___x_4830_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4833_, lean_object* v_config_4834_, lean_object* v_a_4835_, lean_object* v_a_4836_, lean_object* v_a_4837_, lean_object* v_a_4838_, lean_object* v_a_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l_Lean_MVarId_contradiction(v_mvarId_4833_, v_config_4834_, v_a_4835_, v_a_4836_, v_a_4837_, v_a_4838_);
lean_dec(v_a_4838_);
lean_dec_ref(v_a_4837_);
lean_dec(v_a_4836_);
lean_dec_ref(v_a_4835_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4903_; uint8_t v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4903_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4904_ = 0;
v___x_4905_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4906_ = l_Lean_registerTraceClass(v___x_4903_, v___x_4904_, v___x_4905_);
return v___x_4906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4908_;
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
