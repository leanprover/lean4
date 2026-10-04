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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAbsurd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecide(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Context_config(lean_object*);
uint8_t l_Lean_Meta_instBEqTransparencyMode_beq(uint8_t, uint8_t);
lean_object* l_Lean_Meta_ConfigWithKey_setTransparency(uint8_t, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_ctor_set(v_reuseFailAlloc_201_, 10, v_instanceTypedMVars_188_);
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
lean_inc(v_a_500_);
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
lean_object* v___x_570_; lean_object* v_env_571_; uint8_t v___x_572_; lean_object* v_env_573_; lean_object* v___x_574_; lean_object* v_toCold_575_; lean_object* v_mctx_576_; lean_object* v_lctx_577_; lean_object* v_options_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_570_ = lean_st_ref_get(v___y_568_);
v_env_571_ = lean_ctor_get(v___x_570_, 0);
lean_inc_ref(v_env_571_);
lean_dec(v___x_570_);
v___x_572_ = 0;
v_env_573_ = l_Lean_Environment_setRecordingDeps(v_env_571_, v___x_572_);
v___x_574_ = lean_st_ref_get(v___y_566_);
v_toCold_575_ = lean_ctor_get(v___y_567_, 0);
v_mctx_576_ = lean_ctor_get(v___x_574_, 0);
lean_inc_ref(v_mctx_576_);
lean_dec(v___x_574_);
v_lctx_577_ = lean_ctor_get(v___y_565_, 2);
v_options_578_ = lean_ctor_get(v_toCold_575_, 2);
lean_inc_ref(v_options_578_);
lean_inc_ref(v_lctx_577_);
v___x_579_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_579_, 0, v_env_573_);
lean_ctor_set(v___x_579_, 1, v_mctx_576_);
lean_ctor_set(v___x_579_, 2, v_lctx_577_);
lean_ctor_set(v___x_579_, 3, v_options_578_);
v___x_580_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
lean_ctor_set(v___x_580_, 1, v_msgData_564_);
v___x_581_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object* v_msgData_582_, lean_object* v___y_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_){
_start:
{
lean_object* v_res_588_; 
v_res_588_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_582_, v___y_583_, v___y_584_, v___y_585_, v___y_586_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
lean_dec(v___y_584_);
lean_dec_ref(v___y_583_);
return v_res_588_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_589_; double v___x_590_; 
v___x_589_ = lean_unsigned_to_nat(0u);
v___x_590_ = lean_float_of_nat(v___x_589_);
return v___x_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_594_, lean_object* v_msg_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_){
_start:
{
lean_object* v_ref_601_; lean_object* v___x_602_; lean_object* v_a_603_; lean_object* v___x_605_; uint8_t v_isShared_606_; uint8_t v_isSharedCheck_648_; 
v_ref_601_ = lean_ctor_get(v___y_598_, 2);
v___x_602_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_);
v_a_603_ = lean_ctor_get(v___x_602_, 0);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_602_);
if (v_isSharedCheck_648_ == 0)
{
v___x_605_ = v___x_602_;
v_isShared_606_ = v_isSharedCheck_648_;
goto v_resetjp_604_;
}
else
{
lean_inc(v_a_603_);
lean_dec(v___x_602_);
v___x_605_ = lean_box(0);
v_isShared_606_ = v_isSharedCheck_648_;
goto v_resetjp_604_;
}
v_resetjp_604_:
{
lean_object* v___x_607_; lean_object* v_traceState_608_; lean_object* v_env_609_; lean_object* v_nextMacroScope_610_; lean_object* v_ngen_611_; lean_object* v_auxDeclNGen_612_; lean_object* v_cache_613_; lean_object* v_recordedDeps_614_; lean_object* v_messages_615_; lean_object* v_infoState_616_; lean_object* v_snapshotTasks_617_; lean_object* v___x_619_; uint8_t v_isShared_620_; uint8_t v_isSharedCheck_647_; 
v___x_607_ = lean_st_ref_take(v___y_599_);
v_traceState_608_ = lean_ctor_get(v___x_607_, 4);
v_env_609_ = lean_ctor_get(v___x_607_, 0);
v_nextMacroScope_610_ = lean_ctor_get(v___x_607_, 1);
v_ngen_611_ = lean_ctor_get(v___x_607_, 2);
v_auxDeclNGen_612_ = lean_ctor_get(v___x_607_, 3);
v_cache_613_ = lean_ctor_get(v___x_607_, 5);
v_recordedDeps_614_ = lean_ctor_get(v___x_607_, 6);
v_messages_615_ = lean_ctor_get(v___x_607_, 7);
v_infoState_616_ = lean_ctor_get(v___x_607_, 8);
v_snapshotTasks_617_ = lean_ctor_get(v___x_607_, 9);
v_isSharedCheck_647_ = !lean_is_exclusive(v___x_607_);
if (v_isSharedCheck_647_ == 0)
{
v___x_619_ = v___x_607_;
v_isShared_620_ = v_isSharedCheck_647_;
goto v_resetjp_618_;
}
else
{
lean_inc(v_snapshotTasks_617_);
lean_inc(v_infoState_616_);
lean_inc(v_messages_615_);
lean_inc(v_recordedDeps_614_);
lean_inc(v_cache_613_);
lean_inc(v_traceState_608_);
lean_inc(v_auxDeclNGen_612_);
lean_inc(v_ngen_611_);
lean_inc(v_nextMacroScope_610_);
lean_inc(v_env_609_);
lean_dec(v___x_607_);
v___x_619_ = lean_box(0);
v_isShared_620_ = v_isSharedCheck_647_;
goto v_resetjp_618_;
}
v_resetjp_618_:
{
uint64_t v_tid_621_; lean_object* v_traces_622_; lean_object* v___x_624_; uint8_t v_isShared_625_; uint8_t v_isSharedCheck_646_; 
v_tid_621_ = lean_ctor_get_uint64(v_traceState_608_, sizeof(void*)*1);
v_traces_622_ = lean_ctor_get(v_traceState_608_, 0);
v_isSharedCheck_646_ = !lean_is_exclusive(v_traceState_608_);
if (v_isSharedCheck_646_ == 0)
{
v___x_624_ = v_traceState_608_;
v_isShared_625_ = v_isSharedCheck_646_;
goto v_resetjp_623_;
}
else
{
lean_inc(v_traces_622_);
lean_dec(v_traceState_608_);
v___x_624_ = lean_box(0);
v_isShared_625_ = v_isSharedCheck_646_;
goto v_resetjp_623_;
}
v_resetjp_623_:
{
lean_object* v___x_626_; lean_object* v___x_627_; double v___x_628_; uint8_t v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_637_; 
v___x_626_ = lean_box(0);
v___x_627_ = lean_box(0);
v___x_628_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_629_ = 0;
v___x_630_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_631_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_631_, 0, v_cls_594_);
lean_ctor_set(v___x_631_, 1, v___x_627_);
lean_ctor_set(v___x_631_, 2, v___x_630_);
lean_ctor_set_float(v___x_631_, sizeof(void*)*3, v___x_628_);
lean_ctor_set_float(v___x_631_, sizeof(void*)*3 + 8, v___x_628_);
lean_ctor_set_uint8(v___x_631_, sizeof(void*)*3 + 16, v___x_629_);
v___x_632_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_633_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_633_, 0, v___x_631_);
lean_ctor_set(v___x_633_, 1, v_a_603_);
lean_ctor_set(v___x_633_, 2, v___x_632_);
lean_inc(v_ref_601_);
v___x_634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_634_, 0, v_ref_601_);
lean_ctor_set(v___x_634_, 1, v___x_633_);
v___x_635_ = l_Lean_PersistentArray_push___redArg(v_traces_622_, v___x_634_);
if (v_isShared_625_ == 0)
{
lean_ctor_set(v___x_624_, 0, v___x_635_);
v___x_637_ = v___x_624_;
goto v_reusejp_636_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v___x_635_);
lean_ctor_set_uint64(v_reuseFailAlloc_645_, sizeof(void*)*1, v_tid_621_);
v___x_637_ = v_reuseFailAlloc_645_;
goto v_reusejp_636_;
}
v_reusejp_636_:
{
lean_object* v___x_639_; 
if (v_isShared_620_ == 0)
{
lean_ctor_set(v___x_619_, 4, v___x_637_);
v___x_639_ = v___x_619_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v_env_609_);
lean_ctor_set(v_reuseFailAlloc_644_, 1, v_nextMacroScope_610_);
lean_ctor_set(v_reuseFailAlloc_644_, 2, v_ngen_611_);
lean_ctor_set(v_reuseFailAlloc_644_, 3, v_auxDeclNGen_612_);
lean_ctor_set(v_reuseFailAlloc_644_, 4, v___x_637_);
lean_ctor_set(v_reuseFailAlloc_644_, 5, v_cache_613_);
lean_ctor_set(v_reuseFailAlloc_644_, 6, v_recordedDeps_614_);
lean_ctor_set(v_reuseFailAlloc_644_, 7, v_messages_615_);
lean_ctor_set(v_reuseFailAlloc_644_, 8, v_infoState_616_);
lean_ctor_set(v_reuseFailAlloc_644_, 9, v_snapshotTasks_617_);
v___x_639_ = v_reuseFailAlloc_644_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
lean_object* v___x_640_; lean_object* v___x_642_; 
v___x_640_ = lean_st_ref_put(v___y_599_, v___x_639_);
if (v_isShared_606_ == 0)
{
lean_ctor_set(v___x_605_, 0, v___x_626_);
v___x_642_ = v___x_605_;
goto v_reusejp_641_;
}
else
{
lean_object* v_reuseFailAlloc_643_; 
v_reuseFailAlloc_643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_643_, 0, v___x_626_);
v___x_642_ = v_reuseFailAlloc_643_;
goto v_reusejp_641_;
}
v_reusejp_641_:
{
return v___x_642_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_649_, lean_object* v_msg_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_649_, v_msg_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_);
lean_dec(v___y_654_);
lean_dec_ref(v___y_653_);
lean_dec(v___y_652_);
lean_dec_ref(v___y_651_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_664_, lean_object* v_mvarId_665_, lean_object* v_fields_666_, lean_object* v_sz_667_, lean_object* v___x_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_){
_start:
{
size_t v_sz_boxed_677_; size_t v___x_16041__boxed_678_; uint8_t v___x_16043__boxed_679_; lean_object* v_res_680_; 
v_sz_boxed_677_ = lean_unbox_usize(v_sz_667_);
lean_dec(v_sz_667_);
v___x_16041__boxed_678_ = lean_unbox_usize(v___x_668_);
lean_dec(v___x_668_);
v___x_16043__boxed_679_ = lean_unbox(v___x_670_);
v_res_680_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_664_, v_mvarId_665_, v_fields_666_, v_sz_boxed_677_, v___x_16041__boxed_678_, v___x_669_, v___x_16043__boxed_679_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
lean_dec(v___y_675_);
lean_dec_ref(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v___y_671_);
lean_dec_ref(v_fields_666_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_681_, lean_object* v_as_682_, size_t v_sz_683_, size_t v_i_684_, lean_object* v_b_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_){
_start:
{
uint8_t v___x_692_; 
v___x_692_ = lean_usize_dec_lt(v_i_684_, v_sz_683_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
v___x_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_693_, 0, v_b_685_);
return v___x_693_;
}
else
{
lean_object* v_a_694_; lean_object* v_toInductionSubgoal_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v_b_685_);
v_a_694_ = lean_array_uget(v_as_682_, v_i_684_);
v_toInductionSubgoal_695_ = lean_ctor_get(v_a_694_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_a_694_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v_a_694_, 1);
lean_dec(v_unused_737_);
v___x_697_ = v_a_694_;
v_isShared_698_ = v_isSharedCheck_736_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_toInductionSubgoal_695_);
lean_dec(v_a_694_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_736_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v_mvarId_699_; lean_object* v_fields_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; uint8_t v___x_704_; size_t v_sz_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___f_709_; lean_object* v___x_710_; 
v_mvarId_699_ = lean_ctor_get(v_toInductionSubgoal_695_, 0);
lean_inc_n(v_mvarId_699_, 2);
v_fields_700_ = lean_ctor_get(v_toInductionSubgoal_695_, 1);
lean_inc_ref(v_fields_700_);
v___x_701_ = lean_box(0);
v___x_702_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_703_ = lean_unsigned_to_nat(0u);
v___x_704_ = lean_nat_dec_eq(v_val_681_, v___x_703_);
v_sz_705_ = lean_array_size(v_fields_700_);
v___x_706_ = lean_box_usize(v_sz_705_);
v___x_707_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_708_ = lean_box(v___x_704_);
v___f_709_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_709_, 0, v_toInductionSubgoal_695_);
lean_closure_set(v___f_709_, 1, v_mvarId_699_);
lean_closure_set(v___f_709_, 2, v_fields_700_);
lean_closure_set(v___f_709_, 3, v___x_706_);
lean_closure_set(v___f_709_, 4, v___x_707_);
lean_closure_set(v___f_709_, 5, v___x_702_);
lean_closure_set(v___f_709_, 6, v___x_708_);
v___x_710_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_699_, v___f_709_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
if (lean_obj_tag(v___x_710_) == 0)
{
lean_object* v_a_711_; lean_object* v___x_713_; uint8_t v_isShared_714_; uint8_t v_isSharedCheck_727_; 
v_a_711_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_727_ == 0)
{
v___x_713_ = v___x_710_;
v_isShared_714_ = v_isSharedCheck_727_;
goto v_resetjp_712_;
}
else
{
lean_inc(v_a_711_);
lean_dec(v___x_710_);
v___x_713_ = lean_box(0);
v_isShared_714_ = v_isSharedCheck_727_;
goto v_resetjp_712_;
}
v_resetjp_712_:
{
uint8_t v___x_715_; 
v___x_715_ = lean_unbox(v_a_711_);
lean_dec(v_a_711_);
if (v___x_715_ == 0)
{
lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_719_; 
v___x_716_ = lean_box(v___x_704_);
v___x_717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_717_, 0, v___x_716_);
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v___x_701_);
lean_ctor_set(v___x_697_, 0, v___x_717_);
v___x_719_ = v___x_697_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v___x_701_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_714_ == 0)
{
lean_ctor_set(v___x_713_, 0, v___x_719_);
v___x_721_ = v___x_713_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
else
{
size_t v___x_724_; size_t v___x_725_; 
lean_del_object(v___x_713_);
lean_del_object(v___x_697_);
v___x_724_ = ((size_t)1ULL);
v___x_725_ = lean_usize_add(v_i_684_, v___x_724_);
v_i_684_ = v___x_725_;
v_b_685_ = v___x_702_;
goto _start;
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_del_object(v___x_697_);
v_a_728_ = lean_ctor_get(v___x_710_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_710_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_710_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_710_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
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
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; 
v___x_748_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_749_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__6));
v___x_750_ = l_Lean_Name_append(v___x_749_, v___x_748_);
return v___x_750_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_753_ = l_Lean_stringToMessageData(v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_754_, lean_object* v_fvarId_755_, lean_object* v___x_756_, uint8_t v___x_757_, lean_object* v___x_758_, lean_object* v_val_759_, uint8_t v___x_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_){
_start:
{
lean_object* v___x_767_; 
v___x_767_ = l_Lean_MVarId_cases(v_mvarId_754_, v_fvarId_755_, v___x_756_, v___x_757_, v___x_758_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_767_) == 0)
{
lean_object* v_a_768_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v_toCold_801_; lean_object* v_options_802_; uint8_t v_hasTrace_803_; 
v_a_768_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_a_768_);
lean_dec_ref_known(v___x_767_, 1);
v_toCold_801_ = lean_ctor_get(v___y_764_, 0);
v_options_802_ = lean_ctor_get(v_toCold_801_, 2);
v_hasTrace_803_ = lean_ctor_get_uint8(v_options_802_, sizeof(void*)*1);
if (v_hasTrace_803_ == 0)
{
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
v___y_772_ = v___y_763_;
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
goto v___jp_769_;
}
else
{
lean_object* v_inheritedTraceOptions_804_; lean_object* v___x_805_; lean_object* v___x_806_; uint8_t v___x_807_; 
v_inheritedTraceOptions_804_ = lean_ctor_get(v_toCold_801_, 11);
v___x_805_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_806_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_807_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_804_, v_options_802_, v___x_806_);
if (v___x_807_ == 0)
{
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
v___y_772_ = v___y_763_;
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
goto v___jp_769_;
}
else
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; 
v___x_808_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_809_ = lean_array_get_size(v_a_768_);
v___x_810_ = l_Nat_reprFast(v___x_809_);
v___x_811_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
v___x_812_ = l_Lean_MessageData_ofFormat(v___x_811_);
v___x_813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_808_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_805_, v___x_813_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_814_) == 0)
{
lean_dec_ref_known(v___x_814_, 1);
v___y_770_ = v___y_761_;
v___y_771_ = v___y_762_;
v___y_772_ = v___y_763_;
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
goto v___jp_769_;
}
else
{
lean_object* v_a_815_; lean_object* v___x_817_; uint8_t v_isShared_818_; uint8_t v_isSharedCheck_822_; 
lean_dec(v_a_768_);
v_a_815_ = lean_ctor_get(v___x_814_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v___x_814_);
if (v_isSharedCheck_822_ == 0)
{
v___x_817_ = v___x_814_;
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
else
{
lean_inc(v_a_815_);
lean_dec(v___x_814_);
v___x_817_ = lean_box(0);
v_isShared_818_ = v_isSharedCheck_822_;
goto v_resetjp_816_;
}
v_resetjp_816_:
{
lean_object* v___x_820_; 
if (v_isShared_818_ == 0)
{
v___x_820_ = v___x_817_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_a_815_);
v___x_820_ = v_reuseFailAlloc_821_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
return v___x_820_;
}
}
}
}
}
v___jp_769_:
{
lean_object* v___x_775_; size_t v_sz_776_; size_t v___x_777_; lean_object* v___x_778_; 
v___x_775_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_776_ = lean_array_size(v_a_768_);
v___x_777_ = ((size_t)0ULL);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_759_, v_a_768_, v_sz_776_, v___x_777_, v___x_775_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_);
lean_dec(v_a_768_);
if (lean_obj_tag(v___x_778_) == 0)
{
lean_object* v_a_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_792_; 
v_a_779_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_792_ == 0)
{
v___x_781_ = v___x_778_;
v_isShared_782_ = v_isSharedCheck_792_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_a_779_);
lean_dec(v___x_778_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_792_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v_fst_783_; 
v_fst_783_ = lean_ctor_get(v_a_779_, 0);
lean_inc(v_fst_783_);
lean_dec(v_a_779_);
if (lean_obj_tag(v_fst_783_) == 0)
{
lean_object* v___x_784_; lean_object* v___x_786_; 
v___x_784_ = lean_box(v___x_760_);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v___x_784_);
v___x_786_ = v___x_781_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_787_; 
v_reuseFailAlloc_787_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_787_, 0, v___x_784_);
v___x_786_ = v_reuseFailAlloc_787_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
return v___x_786_;
}
}
else
{
lean_object* v_val_788_; lean_object* v___x_790_; 
v_val_788_ = lean_ctor_get(v_fst_783_, 0);
lean_inc(v_val_788_);
lean_dec_ref_known(v_fst_783_, 1);
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 0, v_val_788_);
v___x_790_ = v___x_781_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v_val_788_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
else
{
lean_object* v_a_793_; lean_object* v___x_795_; uint8_t v_isShared_796_; uint8_t v_isSharedCheck_800_; 
v_a_793_ = lean_ctor_get(v___x_778_, 0);
v_isSharedCheck_800_ = !lean_is_exclusive(v___x_778_);
if (v_isSharedCheck_800_ == 0)
{
v___x_795_ = v___x_778_;
v_isShared_796_ = v_isSharedCheck_800_;
goto v_resetjp_794_;
}
else
{
lean_inc(v_a_793_);
lean_dec(v___x_778_);
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
}
else
{
lean_object* v_a_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_868_; 
v_a_823_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_868_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_868_ == 0)
{
v___x_825_ = v___x_767_;
v_isShared_826_ = v_isSharedCheck_868_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_a_823_);
lean_dec(v___x_767_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_868_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
uint8_t v___y_828_; uint8_t v___x_866_; 
v___x_866_ = l_Lean_Exception_isInterrupt(v_a_823_);
if (v___x_866_ == 0)
{
uint8_t v___x_867_; 
lean_inc(v_a_823_);
v___x_867_ = l_Lean_Exception_isRuntime(v_a_823_);
v___y_828_ = v___x_867_;
goto v___jp_827_;
}
else
{
v___y_828_ = v___x_866_;
goto v___jp_827_;
}
v___jp_827_:
{
if (v___y_828_ == 0)
{
lean_object* v_toCold_829_; lean_object* v_options_830_; uint8_t v_hasTrace_831_; 
v_toCold_829_ = lean_ctor_get(v___y_764_, 0);
v_options_830_ = lean_ctor_get(v_toCold_829_, 2);
v_hasTrace_831_ = lean_ctor_get_uint8(v_options_830_, sizeof(void*)*1);
if (v_hasTrace_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_834_; 
lean_dec(v_a_823_);
v___x_832_ = lean_box(v___x_757_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 0);
lean_ctor_set(v___x_825_, 0, v___x_832_);
v___x_834_ = v___x_825_;
goto v_reusejp_833_;
}
else
{
lean_object* v_reuseFailAlloc_835_; 
v_reuseFailAlloc_835_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_832_);
v___x_834_ = v_reuseFailAlloc_835_;
goto v_reusejp_833_;
}
v_reusejp_833_:
{
return v___x_834_;
}
}
else
{
lean_object* v_inheritedTraceOptions_836_; lean_object* v___x_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_inheritedTraceOptions_836_ = lean_ctor_get(v_toCold_829_, 11);
v___x_837_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_838_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_839_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_836_, v_options_830_, v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; lean_object* v___x_842_; 
lean_dec(v_a_823_);
v___x_840_ = lean_box(v___x_757_);
if (v_isShared_826_ == 0)
{
lean_ctor_set_tag(v___x_825_, 0);
lean_ctor_set(v___x_825_, 0, v___x_840_);
v___x_842_ = v___x_825_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_843_; 
v_reuseFailAlloc_843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_843_, 0, v___x_840_);
v___x_842_ = v_reuseFailAlloc_843_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
return v___x_842_;
}
}
else
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_del_object(v___x_825_);
v___x_844_ = l_Lean_Exception_toMessageData(v_a_823_);
v___x_845_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_837_, v___x_844_, v___y_762_, v___y_763_, v___y_764_, v___y_765_);
if (lean_obj_tag(v___x_845_) == 0)
{
lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_853_; 
v_isSharedCheck_853_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_853_ == 0)
{
lean_object* v_unused_854_; 
v_unused_854_ = lean_ctor_get(v___x_845_, 0);
lean_dec(v_unused_854_);
v___x_847_ = v___x_845_;
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
else
{
lean_dec(v___x_845_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_853_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v___x_849_; lean_object* v___x_851_; 
v___x_849_ = lean_box(v___x_757_);
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 0, v___x_849_);
v___x_851_ = v___x_847_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v___x_849_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
else
{
lean_object* v_a_855_; lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_862_; 
v_a_855_ = lean_ctor_get(v___x_845_, 0);
v_isSharedCheck_862_ = !lean_is_exclusive(v___x_845_);
if (v_isSharedCheck_862_ == 0)
{
v___x_857_ = v___x_845_;
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
else
{
lean_inc(v_a_855_);
lean_dec(v___x_845_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_862_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v___x_860_; 
if (v_isShared_858_ == 0)
{
v___x_860_ = v___x_857_;
goto v_reusejp_859_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_a_855_);
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
else
{
lean_object* v___x_864_; 
if (v_isShared_826_ == 0)
{
v___x_864_ = v___x_825_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_a_823_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_869_, lean_object* v_fvarId_870_, lean_object* v___x_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v_val_874_, lean_object* v___x_875_, lean_object* v___y_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
uint8_t v___x_16163__boxed_882_; uint8_t v___x_16166__boxed_883_; lean_object* v_res_884_; 
v___x_16163__boxed_882_ = lean_unbox(v___x_872_);
v___x_16166__boxed_883_ = lean_unbox(v___x_875_);
v_res_884_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_869_, v_fvarId_870_, v___x_871_, v___x_16163__boxed_882_, v___x_873_, v_val_874_, v___x_16166__boxed_883_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
lean_dec(v___y_878_);
lean_dec_ref(v___y_877_);
lean_dec(v___y_876_);
lean_dec(v_val_874_);
return v_res_884_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_886_; lean_object* v___x_887_; 
v___x_886_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_887_ = l_Lean_stringToMessageData(v___x_886_);
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_888_, lean_object* v_fvarId_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v___x_900_; lean_object* v___x_901_; uint8_t v___x_902_; 
v___x_900_ = lean_st_ref_get(v_a_890_);
v___x_901_ = lean_unsigned_to_nat(0u);
v___x_902_ = lean_nat_dec_eq(v___x_900_, v___x_901_);
if (v___x_902_ == 0)
{
uint8_t v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___f_912_; lean_object* v___x_913_; 
v___x_903_ = 1;
v___x_904_ = lean_st_ref_take(v_a_890_);
v___x_905_ = lean_unsigned_to_nat(1u);
v___x_906_ = lean_nat_sub(v___x_904_, v___x_905_);
lean_dec(v___x_904_);
v___x_907_ = lean_st_ref_put(v_a_890_, v___x_906_);
v___x_908_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_909_ = lean_box(0);
v___x_910_ = lean_box(v___x_902_);
v___x_911_ = lean_box(v___x_903_);
v___f_912_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_912_, 0, v_mvarId_888_);
lean_closure_set(v___f_912_, 1, v_fvarId_889_);
lean_closure_set(v___f_912_, 2, v___x_908_);
lean_closure_set(v___f_912_, 3, v___x_910_);
lean_closure_set(v___f_912_, 4, v___x_909_);
lean_closure_set(v___f_912_, 5, v___x_900_);
lean_closure_set(v___f_912_, 6, v___x_911_);
v___x_913_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_912_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
return v___x_913_;
}
else
{
lean_object* v_toCold_914_; lean_object* v_options_915_; uint8_t v_hasTrace_916_; 
lean_dec(v___x_900_);
lean_dec(v_fvarId_889_);
lean_dec(v_mvarId_888_);
v_toCold_914_ = lean_ctor_get(v_a_893_, 0);
v_options_915_ = lean_ctor_get(v_toCold_914_, 2);
v_hasTrace_916_ = lean_ctor_get_uint8(v_options_915_, sizeof(void*)*1);
if (v_hasTrace_916_ == 0)
{
goto v___jp_896_;
}
else
{
lean_object* v_inheritedTraceOptions_917_; lean_object* v___x_918_; lean_object* v___x_919_; uint8_t v___x_920_; 
v_inheritedTraceOptions_917_ = lean_ctor_get(v_toCold_914_, 11);
v___x_918_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_919_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_917_, v_options_915_, v___x_919_);
if (v___x_920_ == 0)
{
goto v___jp_896_;
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_921_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_922_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_918_, v___x_921_, v_a_891_, v_a_892_, v_a_893_, v_a_894_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_dec_ref_known(v___x_922_, 1);
goto v___jp_896_;
}
else
{
lean_object* v_a_923_; lean_object* v___x_925_; uint8_t v_isShared_926_; uint8_t v_isSharedCheck_930_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_930_ == 0)
{
v___x_925_ = v___x_922_;
v_isShared_926_ = v_isSharedCheck_930_;
goto v_resetjp_924_;
}
else
{
lean_inc(v_a_923_);
lean_dec(v___x_922_);
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
v___jp_896_:
{
uint8_t v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = 0;
v___x_898_ = lean_box(v___x_897_);
v___x_899_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_899_, 0, v___x_898_);
return v___x_899_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_931_, lean_object* v___x_932_, lean_object* v_as_933_, size_t v_sz_934_, size_t v_i_935_, lean_object* v_b_936_, lean_object* v___y_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_){
_start:
{
lean_object* v_a_944_; uint8_t v___x_948_; 
v___x_948_ = lean_usize_dec_lt(v_i_935_, v_sz_934_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; 
lean_dec(v___x_932_);
lean_dec_ref(v___x_931_);
v___x_949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_949_, 0, v_b_936_);
return v___x_949_;
}
else
{
lean_object* v_subst_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v_a_953_; lean_object* v___x_954_; uint8_t v___x_955_; 
lean_dec_ref(v_b_936_);
v_subst_950_ = lean_ctor_get(v___x_931_, 2);
v___x_951_ = lean_box(0);
v___x_952_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_953_ = lean_array_uget_borrowed(v_as_933_, v_i_935_);
lean_inc(v_subst_950_);
v___x_954_ = l_Lean_Meta_FVarSubst_apply(v_subst_950_, v_a_953_);
v___x_955_ = l_Lean_Expr_isFVar(v___x_954_);
if (v___x_955_ == 0)
{
lean_dec_ref(v___x_954_);
v_a_944_ = v___x_952_;
goto v___jp_943_;
}
else
{
lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_956_ = l_Lean_Expr_fvarId_x21(v___x_954_);
lean_dec_ref(v___x_954_);
lean_inc(v___x_956_);
v___x_957_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_956_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
if (lean_obj_tag(v___x_957_) == 0)
{
lean_object* v_a_958_; uint8_t v___x_959_; 
v_a_958_ = lean_ctor_get(v___x_957_, 0);
lean_inc(v_a_958_);
lean_dec_ref_known(v___x_957_, 1);
v___x_959_ = lean_unbox(v_a_958_);
lean_dec(v_a_958_);
if (v___x_959_ == 0)
{
lean_dec(v___x_956_);
v_a_944_ = v___x_952_;
goto v___jp_943_;
}
else
{
lean_object* v___x_960_; 
lean_inc(v___x_932_);
v___x_960_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_932_, v___x_956_, v___y_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_);
if (lean_obj_tag(v___x_960_) == 0)
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_972_; 
v_a_961_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_972_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_972_ == 0)
{
v___x_963_ = v___x_960_;
v_isShared_964_ = v_isSharedCheck_972_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_960_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_972_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
uint8_t v___x_965_; 
v___x_965_ = lean_unbox(v_a_961_);
lean_dec(v_a_961_);
if (v___x_965_ == 0)
{
lean_del_object(v___x_963_);
v_a_944_ = v___x_952_;
goto v___jp_943_;
}
else
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_970_; 
lean_dec(v___x_932_);
lean_dec_ref(v___x_931_);
v___x_966_ = lean_box(v___x_955_);
v___x_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_967_, 0, v___x_966_);
v___x_968_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
lean_ctor_set(v___x_968_, 1, v___x_951_);
if (v_isShared_964_ == 0)
{
lean_ctor_set(v___x_963_, 0, v___x_968_);
v___x_970_ = v___x_963_;
goto v_reusejp_969_;
}
else
{
lean_object* v_reuseFailAlloc_971_; 
v_reuseFailAlloc_971_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_971_, 0, v___x_968_);
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
else
{
lean_object* v_a_973_; lean_object* v___x_975_; uint8_t v_isShared_976_; uint8_t v_isSharedCheck_980_; 
lean_dec(v___x_932_);
lean_dec_ref(v___x_931_);
v_a_973_ = lean_ctor_get(v___x_960_, 0);
v_isSharedCheck_980_ = !lean_is_exclusive(v___x_960_);
if (v_isSharedCheck_980_ == 0)
{
v___x_975_ = v___x_960_;
v_isShared_976_ = v_isSharedCheck_980_;
goto v_resetjp_974_;
}
else
{
lean_inc(v_a_973_);
lean_dec(v___x_960_);
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
else
{
lean_object* v_a_981_; lean_object* v___x_983_; uint8_t v_isShared_984_; uint8_t v_isSharedCheck_988_; 
lean_dec(v___x_956_);
lean_dec(v___x_932_);
lean_dec_ref(v___x_931_);
v_a_981_ = lean_ctor_get(v___x_957_, 0);
v_isSharedCheck_988_ = !lean_is_exclusive(v___x_957_);
if (v_isSharedCheck_988_ == 0)
{
v___x_983_ = v___x_957_;
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
else
{
lean_inc(v_a_981_);
lean_dec(v___x_957_);
v___x_983_ = lean_box(0);
v_isShared_984_ = v_isSharedCheck_988_;
goto v_resetjp_982_;
}
v_resetjp_982_:
{
lean_object* v___x_986_; 
if (v_isShared_984_ == 0)
{
v___x_986_ = v___x_983_;
goto v_reusejp_985_;
}
else
{
lean_object* v_reuseFailAlloc_987_; 
v_reuseFailAlloc_987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_987_, 0, v_a_981_);
v___x_986_ = v_reuseFailAlloc_987_;
goto v_reusejp_985_;
}
v_reusejp_985_:
{
return v___x_986_;
}
}
}
}
}
v___jp_943_:
{
size_t v___x_945_; size_t v___x_946_; 
v___x_945_ = ((size_t)1ULL);
v___x_946_ = lean_usize_add(v_i_935_, v___x_945_);
lean_inc_ref(v_a_944_);
v_i_935_ = v___x_946_;
v_b_936_ = v_a_944_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_989_, lean_object* v_mvarId_990_, lean_object* v_fields_991_, size_t v_sz_992_, size_t v___x_993_, lean_object* v___x_994_, uint8_t v___x_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_989_, v_mvarId_990_, v_fields_991_, v_sz_992_, v___x_993_, v___x_994_, v___y_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
if (lean_obj_tag(v___x_1002_) == 0)
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1016_; 
v_a_1003_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1016_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1016_ == 0)
{
v___x_1005_ = v___x_1002_;
v_isShared_1006_ = v_isSharedCheck_1016_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_1002_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1016_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v_fst_1007_; 
v_fst_1007_ = lean_ctor_get(v_a_1003_, 0);
lean_inc(v_fst_1007_);
lean_dec(v_a_1003_);
if (lean_obj_tag(v_fst_1007_) == 0)
{
lean_object* v___x_1008_; lean_object* v___x_1010_; 
v___x_1008_ = lean_box(v___x_995_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v___x_1008_);
v___x_1010_ = v___x_1005_;
goto v_reusejp_1009_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v___x_1008_);
v___x_1010_ = v_reuseFailAlloc_1011_;
goto v_reusejp_1009_;
}
v_reusejp_1009_:
{
return v___x_1010_;
}
}
else
{
lean_object* v_val_1012_; lean_object* v___x_1014_; 
v_val_1012_ = lean_ctor_get(v_fst_1007_, 0);
lean_inc(v_val_1012_);
lean_dec_ref_known(v_fst_1007_, 1);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 0, v_val_1012_);
v___x_1014_ = v___x_1005_;
goto v_reusejp_1013_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_val_1012_);
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
else
{
lean_object* v_a_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1024_; 
v_a_1017_ = lean_ctor_get(v___x_1002_, 0);
v_isSharedCheck_1024_ = !lean_is_exclusive(v___x_1002_);
if (v_isSharedCheck_1024_ == 0)
{
v___x_1019_ = v___x_1002_;
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_a_1017_);
lean_dec(v___x_1002_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1024_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1022_; 
if (v_isShared_1020_ == 0)
{
v___x_1022_ = v___x_1019_;
goto v_reusejp_1021_;
}
else
{
lean_object* v_reuseFailAlloc_1023_; 
v_reuseFailAlloc_1023_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1023_, 0, v_a_1017_);
v___x_1022_ = v_reuseFailAlloc_1023_;
goto v_reusejp_1021_;
}
v_reusejp_1021_:
{
return v___x_1022_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1025_, lean_object* v_as_1026_, lean_object* v_sz_1027_, lean_object* v_i_1028_, lean_object* v_b_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_){
_start:
{
size_t v_sz_boxed_1036_; size_t v_i_boxed_1037_; lean_object* v_res_1038_; 
v_sz_boxed_1036_ = lean_unbox_usize(v_sz_1027_);
lean_dec(v_sz_1027_);
v_i_boxed_1037_ = lean_unbox_usize(v_i_1028_);
lean_dec(v_i_1028_);
v_res_1038_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1025_, v_as_1026_, v_sz_boxed_1036_, v_i_boxed_1037_, v_b_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_);
lean_dec(v___y_1034_);
lean_dec_ref(v___y_1033_);
lean_dec(v___y_1032_);
lean_dec_ref(v___y_1031_);
lean_dec(v___y_1030_);
lean_dec_ref(v_as_1026_);
lean_dec(v_val_1025_);
return v_res_1038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1039_, lean_object* v___x_1040_, lean_object* v_as_1041_, lean_object* v_sz_1042_, lean_object* v_i_1043_, lean_object* v_b_1044_, lean_object* v___y_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_){
_start:
{
size_t v_sz_boxed_1051_; size_t v_i_boxed_1052_; lean_object* v_res_1053_; 
v_sz_boxed_1051_ = lean_unbox_usize(v_sz_1042_);
lean_dec(v_sz_1042_);
v_i_boxed_1052_ = lean_unbox_usize(v_i_1043_);
lean_dec(v_i_1043_);
v_res_1053_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1039_, v___x_1040_, v_as_1041_, v_sz_boxed_1051_, v_i_boxed_1052_, v_b_1044_, v___y_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_);
lean_dec(v___y_1049_);
lean_dec_ref(v___y_1048_);
lean_dec(v___y_1047_);
lean_dec_ref(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec_ref(v_as_1041_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1054_, lean_object* v_fvarId_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v_res_1062_; 
v_res_1062_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1054_, v_fvarId_1055_, v_a_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
lean_dec(v_a_1058_);
lean_dec_ref(v_a_1057_);
lean_dec(v_a_1056_);
return v_res_1062_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1063_, lean_object* v_msg_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
lean_object* v___x_1071_; 
v___x_1071_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1063_, v_msg_1064_, v___y_1066_, v___y_1067_, v___y_1068_, v___y_1069_);
return v___x_1071_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1072_, lean_object* v_msg_1073_, lean_object* v___y_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_){
_start:
{
lean_object* v_res_1080_; 
v_res_1080_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1072_, v_msg_1073_, v___y_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_);
lean_dec(v___y_1078_);
lean_dec_ref(v___y_1077_);
lean_dec(v___y_1076_);
lean_dec_ref(v___y_1075_);
lean_dec(v___y_1074_);
return v_res_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_Meta_saveState___redArg(v___y_1083_, v___y_1085_);
if (lean_obj_tag(v___x_1087_) == 0)
{
lean_object* v_a_1088_; lean_object* v___y_1090_; lean_object* v___y_1091_; uint8_t v___y_1092_; lean_object* v___y_1111_; lean_object* v_a_1112_; lean_object* v___x_1115_; 
v_a_1088_ = lean_ctor_get(v___x_1087_, 0);
lean_inc(v_a_1088_);
lean_dec_ref_known(v___x_1087_, 1);
lean_inc(v___y_1085_);
lean_inc_ref(v___y_1084_);
lean_inc(v___y_1083_);
lean_inc_ref(v___y_1082_);
v___x_1115_ = lean_apply_5(v_x_1081_, v___y_1082_, v___y_1083_, v___y_1084_, v___y_1085_, lean_box(0));
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v_a_1116_; uint8_t v___x_1117_; 
v_a_1116_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1116_);
v___x_1117_ = lean_unbox(v_a_1116_);
if (v___x_1117_ == 0)
{
lean_object* v___x_1118_; 
lean_dec_ref_known(v___x_1115_, 1);
lean_inc(v_a_1088_);
v___x_1118_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1088_, v___y_1083_, v___y_1085_);
if (lean_obj_tag(v___x_1118_) == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1125_; 
lean_dec(v_a_1088_);
v_isSharedCheck_1125_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1125_ == 0)
{
lean_object* v_unused_1126_; 
v_unused_1126_ = lean_ctor_get(v___x_1118_, 0);
lean_dec(v_unused_1126_);
v___x_1120_ = v___x_1118_;
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v___x_1118_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1125_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v___x_1123_; 
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v_a_1116_);
v___x_1123_ = v___x_1120_;
goto v_reusejp_1122_;
}
else
{
lean_object* v_reuseFailAlloc_1124_; 
v_reuseFailAlloc_1124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1124_, 0, v_a_1116_);
v___x_1123_ = v_reuseFailAlloc_1124_;
goto v_reusejp_1122_;
}
v_reusejp_1122_:
{
return v___x_1123_;
}
}
}
else
{
lean_object* v_a_1127_; lean_object* v___x_1129_; uint8_t v_isShared_1130_; uint8_t v_isSharedCheck_1134_; 
lean_dec(v_a_1116_);
v_a_1127_ = lean_ctor_get(v___x_1118_, 0);
v_isSharedCheck_1134_ = !lean_is_exclusive(v___x_1118_);
if (v_isSharedCheck_1134_ == 0)
{
v___x_1129_ = v___x_1118_;
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
else
{
lean_inc(v_a_1127_);
lean_dec(v___x_1118_);
v___x_1129_ = lean_box(0);
v_isShared_1130_ = v_isSharedCheck_1134_;
goto v_resetjp_1128_;
}
v_resetjp_1128_:
{
lean_object* v___x_1132_; 
lean_inc(v_a_1127_);
if (v_isShared_1130_ == 0)
{
v___x_1132_ = v___x_1129_;
goto v_reusejp_1131_;
}
else
{
lean_object* v_reuseFailAlloc_1133_; 
v_reuseFailAlloc_1133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1133_, 0, v_a_1127_);
v___x_1132_ = v_reuseFailAlloc_1133_;
goto v_reusejp_1131_;
}
v_reusejp_1131_:
{
v___y_1111_ = v___x_1132_;
v_a_1112_ = v_a_1127_;
goto v___jp_1110_;
}
}
}
}
else
{
lean_dec(v_a_1116_);
lean_dec(v_a_1088_);
return v___x_1115_;
}
}
else
{
lean_object* v_a_1135_; 
v_a_1135_ = lean_ctor_get(v___x_1115_, 0);
lean_inc(v_a_1135_);
v___y_1111_ = v___x_1115_;
v_a_1112_ = v_a_1135_;
goto v___jp_1110_;
}
v___jp_1089_:
{
if (v___y_1092_ == 0)
{
lean_object* v___x_1093_; 
lean_dec_ref(v___y_1090_);
v___x_1093_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1088_, v___y_1083_, v___y_1085_);
if (lean_obj_tag(v___x_1093_) == 0)
{
lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1100_; 
v_isSharedCheck_1100_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1100_ == 0)
{
lean_object* v_unused_1101_; 
v_unused_1101_ = lean_ctor_get(v___x_1093_, 0);
lean_dec(v_unused_1101_);
v___x_1095_ = v___x_1093_;
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
else
{
lean_dec(v___x_1093_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1100_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1098_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set_tag(v___x_1095_, 1);
lean_ctor_set(v___x_1095_, 0, v___y_1091_);
v___x_1098_ = v___x_1095_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___y_1091_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
else
{
lean_object* v_a_1102_; lean_object* v___x_1104_; uint8_t v_isShared_1105_; uint8_t v_isSharedCheck_1109_; 
lean_dec_ref(v___y_1091_);
v_a_1102_ = lean_ctor_get(v___x_1093_, 0);
v_isSharedCheck_1109_ = !lean_is_exclusive(v___x_1093_);
if (v_isSharedCheck_1109_ == 0)
{
v___x_1104_ = v___x_1093_;
v_isShared_1105_ = v_isSharedCheck_1109_;
goto v_resetjp_1103_;
}
else
{
lean_inc(v_a_1102_);
lean_dec(v___x_1093_);
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
lean_dec_ref(v___y_1091_);
lean_dec(v_a_1088_);
return v___y_1090_;
}
}
v___jp_1110_:
{
uint8_t v___x_1113_; 
v___x_1113_ = l_Lean_Exception_isInterrupt(v_a_1112_);
if (v___x_1113_ == 0)
{
uint8_t v___x_1114_; 
lean_inc_ref(v_a_1112_);
v___x_1114_ = l_Lean_Exception_isRuntime(v_a_1112_);
v___y_1090_ = v___y_1111_;
v___y_1091_ = v_a_1112_;
v___y_1092_ = v___x_1114_;
goto v___jp_1089_;
}
else
{
v___y_1090_ = v___y_1111_;
v___y_1091_ = v_a_1112_;
v___y_1092_ = v___x_1113_;
goto v___jp_1089_;
}
}
}
else
{
lean_object* v_a_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1143_; 
lean_dec_ref(v_x_1081_);
v_a_1136_ = lean_ctor_get(v___x_1087_, 0);
v_isSharedCheck_1143_ = !lean_is_exclusive(v___x_1087_);
if (v_isSharedCheck_1143_ == 0)
{
v___x_1138_ = v___x_1087_;
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_a_1136_);
lean_dec(v___x_1087_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1143_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1141_; 
if (v_isShared_1139_ == 0)
{
v___x_1141_ = v___x_1138_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_a_1136_);
v___x_1141_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
return v___x_1141_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1144_, lean_object* v___y_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1144_, v___y_1145_, v___y_1146_, v___y_1147_, v___y_1148_);
lean_dec(v___y_1148_);
lean_dec_ref(v___y_1147_);
lean_dec(v___y_1146_);
lean_dec_ref(v___y_1145_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1151_, lean_object* v_x_1152_, lean_object* v___y_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_){
_start:
{
lean_object* v___x_1158_; 
v___x_1158_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1151_, v_x_1152_, v___y_1153_, v___y_1154_, v___y_1155_, v___y_1156_);
if (lean_obj_tag(v___x_1158_) == 0)
{
lean_object* v_a_1159_; lean_object* v___x_1161_; uint8_t v_isShared_1162_; uint8_t v_isSharedCheck_1166_; 
v_a_1159_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1166_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1166_ == 0)
{
v___x_1161_ = v___x_1158_;
v_isShared_1162_ = v_isSharedCheck_1166_;
goto v_resetjp_1160_;
}
else
{
lean_inc(v_a_1159_);
lean_dec(v___x_1158_);
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
v_reuseFailAlloc_1165_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1174_; 
v_a_1167_ = lean_ctor_get(v___x_1158_, 0);
v_isSharedCheck_1174_ = !lean_is_exclusive(v___x_1158_);
if (v_isSharedCheck_1174_ == 0)
{
v___x_1169_ = v___x_1158_;
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_a_1167_);
lean_dec(v___x_1158_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1174_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v___x_1172_; 
if (v_isShared_1170_ == 0)
{
v___x_1172_ = v___x_1169_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1173_; 
v_reuseFailAlloc_1173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1173_, 0, v_a_1167_);
v___x_1172_ = v_reuseFailAlloc_1173_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
return v___x_1172_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1175_, lean_object* v_x_1176_, lean_object* v___y_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_){
_start:
{
lean_object* v_res_1182_; 
v_res_1182_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1175_, v_x_1176_, v___y_1177_, v___y_1178_, v___y_1179_, v___y_1180_);
lean_dec(v___y_1180_);
lean_dec_ref(v___y_1179_);
lean_dec(v___y_1178_);
lean_dec_ref(v___y_1177_);
return v_res_1182_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1183_, lean_object* v_mvarId_1184_, lean_object* v_x_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1184_, v_x_1185_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1192_, lean_object* v_mvarId_1193_, lean_object* v_x_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_){
_start:
{
lean_object* v_res_1200_; 
v_res_1200_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1192_, v_mvarId_1193_, v_x_1194_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
lean_dec(v___y_1196_);
lean_dec_ref(v___y_1195_);
return v_res_1200_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1201_, lean_object* v_fuel_1202_, lean_object* v_fvarId_1203_, lean_object* v___y_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_){
_start:
{
lean_object* v___x_1209_; 
v___x_1209_ = l_Lean_MVarId_exfalso(v_mvarId_1201_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1209_) == 0)
{
lean_object* v_a_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; 
v_a_1210_ = lean_ctor_get(v___x_1209_, 0);
lean_inc(v_a_1210_);
lean_dec_ref_known(v___x_1209_, 1);
v___x_1211_ = lean_st_mk_ref(v_fuel_1202_);
v___x_1212_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1210_, v_fvarId_1203_, v___x_1211_, v___y_1204_, v___y_1205_, v___y_1206_, v___y_1207_);
if (lean_obj_tag(v___x_1212_) == 0)
{
lean_object* v_a_1213_; lean_object* v___x_1215_; uint8_t v_isShared_1216_; uint8_t v_isSharedCheck_1221_; 
v_a_1213_ = lean_ctor_get(v___x_1212_, 0);
v_isSharedCheck_1221_ = !lean_is_exclusive(v___x_1212_);
if (v_isSharedCheck_1221_ == 0)
{
v___x_1215_ = v___x_1212_;
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
else
{
lean_inc(v_a_1213_);
lean_dec(v___x_1212_);
v___x_1215_ = lean_box(0);
v_isShared_1216_ = v_isSharedCheck_1221_;
goto v_resetjp_1214_;
}
v_resetjp_1214_:
{
lean_object* v___x_1217_; lean_object* v___x_1219_; 
v___x_1217_ = lean_st_ref_get(v___x_1211_);
lean_dec(v___x_1211_);
lean_dec(v___x_1217_);
if (v_isShared_1216_ == 0)
{
v___x_1219_ = v___x_1215_;
goto v_reusejp_1218_;
}
else
{
lean_object* v_reuseFailAlloc_1220_; 
v_reuseFailAlloc_1220_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1220_, 0, v_a_1213_);
v___x_1219_ = v_reuseFailAlloc_1220_;
goto v_reusejp_1218_;
}
v_reusejp_1218_:
{
return v___x_1219_;
}
}
}
else
{
lean_dec(v___x_1211_);
return v___x_1212_;
}
}
else
{
lean_object* v_a_1222_; lean_object* v___x_1224_; uint8_t v_isShared_1225_; uint8_t v_isSharedCheck_1229_; 
lean_dec(v_fvarId_1203_);
lean_dec(v_fuel_1202_);
v_a_1222_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1229_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1229_ == 0)
{
v___x_1224_ = v___x_1209_;
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
else
{
lean_inc(v_a_1222_);
lean_dec(v___x_1209_);
v___x_1224_ = lean_box(0);
v_isShared_1225_ = v_isSharedCheck_1229_;
goto v_resetjp_1223_;
}
v_resetjp_1223_:
{
lean_object* v___x_1227_; 
if (v_isShared_1225_ == 0)
{
v___x_1227_ = v___x_1224_;
goto v_reusejp_1226_;
}
else
{
lean_object* v_reuseFailAlloc_1228_; 
v_reuseFailAlloc_1228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1228_, 0, v_a_1222_);
v___x_1227_ = v_reuseFailAlloc_1228_;
goto v_reusejp_1226_;
}
v_reusejp_1226_:
{
return v___x_1227_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1230_, lean_object* v_fuel_1231_, lean_object* v_fvarId_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1230_, v_fuel_1231_, v_fvarId_1232_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1239_, lean_object* v___f_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_){
_start:
{
lean_object* v___x_1246_; 
v___x_1246_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1239_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
if (lean_obj_tag(v___x_1246_) == 0)
{
lean_object* v_a_1247_; uint8_t v___x_1248_; 
v_a_1247_ = lean_ctor_get(v___x_1246_, 0);
v___x_1248_ = lean_unbox(v_a_1247_);
if (v___x_1248_ == 0)
{
lean_dec_ref(v___f_1240_);
return v___x_1246_;
}
else
{
lean_object* v___x_1249_; 
lean_dec_ref_known(v___x_1246_, 1);
v___x_1249_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1240_, v___y_1241_, v___y_1242_, v___y_1243_, v___y_1244_);
return v___x_1249_;
}
}
else
{
lean_dec_ref(v___f_1240_);
return v___x_1246_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1250_, lean_object* v___f_1251_, lean_object* v___y_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1250_, v___f_1251_, v___y_1252_, v___y_1253_, v___y_1254_, v___y_1255_);
lean_dec(v___y_1255_);
lean_dec_ref(v___y_1254_);
lean_dec(v___y_1253_);
lean_dec_ref(v___y_1252_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1258_, lean_object* v_fvarId_1259_, lean_object* v_fuel_1260_, lean_object* v_a_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_){
_start:
{
lean_object* v___f_1266_; lean_object* v___f_1267_; lean_object* v___x_1268_; 
lean_inc(v_fvarId_1259_);
lean_inc(v_mvarId_1258_);
v___f_1266_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1266_, 0, v_mvarId_1258_);
lean_closure_set(v___f_1266_, 1, v_fuel_1260_);
lean_closure_set(v___f_1266_, 2, v_fvarId_1259_);
v___f_1267_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1267_, 0, v_fvarId_1259_);
lean_closure_set(v___f_1267_, 1, v___f_1266_);
v___x_1268_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1258_, v___f_1267_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1269_, lean_object* v_fvarId_1270_, lean_object* v_fuel_1271_, lean_object* v_a_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1269_, v_fvarId_1270_, v_fuel_1271_, v_a_1272_, v_a_1273_, v_a_1274_, v_a_1275_);
lean_dec(v_a_1275_);
lean_dec_ref(v_a_1274_);
lean_dec(v_a_1273_);
lean_dec_ref(v_a_1272_);
return v_res_1277_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1278_){
_start:
{
uint8_t v___x_1279_; 
v___x_1279_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1280_){
_start:
{
uint8_t v_res_1281_; lean_object* v_r_1282_; 
v_res_1281_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1280_);
v_r_1282_ = lean_box(v_res_1281_);
return v_r_1282_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1283_, lean_object* v_acc_1284_){
_start:
{
if (lean_obj_tag(v_e_1283_) == 7)
{
lean_object* v_binderType_1285_; lean_object* v_body_1286_; uint8_t v___y_1288_; lean_object* v___x_1292_; uint8_t v___x_1293_; 
v_binderType_1285_ = lean_ctor_get(v_e_1283_, 1);
v_body_1286_ = lean_ctor_get(v_e_1283_, 2);
v___x_1292_ = lean_unsigned_to_nat(0u);
v___x_1293_ = lean_expr_has_loose_bvar(v_body_1286_, v___x_1292_);
if (v___x_1293_ == 0)
{
uint8_t v___x_1294_; 
v___x_1294_ = l_Lean_Expr_isEq(v_binderType_1285_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Expr_isHEq(v_binderType_1285_);
v___y_1288_ = v___x_1295_;
goto v___jp_1287_;
}
else
{
v___y_1288_ = v___x_1294_;
goto v___jp_1287_;
}
}
else
{
uint8_t v___x_1296_; 
v___x_1296_ = 0;
v___y_1288_ = v___x_1296_;
goto v___jp_1287_;
}
v___jp_1287_:
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
v___x_1289_ = lean_box(v___y_1288_);
v___x_1290_ = lean_array_push(v_acc_1284_, v___x_1289_);
v_e_1283_ = v_body_1286_;
v_acc_1284_ = v___x_1290_;
goto _start;
}
}
else
{
return v_acc_1284_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1297_, lean_object* v_acc_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1297_, v_acc_1298_);
lean_dec_ref(v_e_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1302_){
_start:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1304_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1302_, v___x_1303_);
return v___x_1304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1305_){
_start:
{
lean_object* v_res_1306_; 
v_res_1306_ = l_Lean_Meta_mkGenDiseqMask(v_e_1305_);
lean_dec_ref(v_e_1305_);
return v_res_1306_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___f_1314_; lean_object* v___x_4344__overap_1315_; lean_object* v___x_1316_; 
v___f_1314_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_4344__overap_1315_ = lean_panic_fn_borrowed(v___f_1314_, v_msg_1308_);
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
v___x_1316_ = lean_apply_5(v___x_4344__overap_1315_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, lean_box(0));
return v___x_1316_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1324_, lean_object* v___y_1325_){
_start:
{
uint8_t v___x_1327_; 
v___x_1327_ = l_Lean_Expr_hasMVar(v_e_1324_);
if (v___x_1327_ == 0)
{
lean_object* v___x_1328_; 
v___x_1328_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1328_, 0, v_e_1324_);
return v___x_1328_;
}
else
{
lean_object* v___x_1329_; lean_object* v_mctx_1330_; lean_object* v___x_1331_; lean_object* v_fst_1332_; lean_object* v_snd_1333_; lean_object* v___x_1334_; lean_object* v_cache_1335_; lean_object* v_zetaDeltaFVarIds_1336_; lean_object* v_postponed_1337_; lean_object* v_diag_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1347_; 
v___x_1329_ = lean_st_ref_get(v___y_1325_);
v_mctx_1330_ = lean_ctor_get(v___x_1329_, 0);
lean_inc_ref(v_mctx_1330_);
lean_dec(v___x_1329_);
v___x_1331_ = l_Lean_instantiateMVarsCore(v_mctx_1330_, v_e_1324_);
v_fst_1332_ = lean_ctor_get(v___x_1331_, 0);
lean_inc(v_fst_1332_);
v_snd_1333_ = lean_ctor_get(v___x_1331_, 1);
lean_inc(v_snd_1333_);
lean_dec_ref(v___x_1331_);
v___x_1334_ = lean_st_ref_take(v___y_1325_);
v_cache_1335_ = lean_ctor_get(v___x_1334_, 1);
v_zetaDeltaFVarIds_1336_ = lean_ctor_get(v___x_1334_, 2);
v_postponed_1337_ = lean_ctor_get(v___x_1334_, 3);
v_diag_1338_ = lean_ctor_get(v___x_1334_, 4);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1347_ == 0)
{
lean_object* v_unused_1348_; 
v_unused_1348_ = lean_ctor_get(v___x_1334_, 0);
lean_dec(v_unused_1348_);
v___x_1340_ = v___x_1334_;
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_diag_1338_);
lean_inc(v_postponed_1337_);
lean_inc(v_zetaDeltaFVarIds_1336_);
lean_inc(v_cache_1335_);
lean_dec(v___x_1334_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1347_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v_snd_1333_);
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_snd_1333_);
lean_ctor_set(v_reuseFailAlloc_1346_, 1, v_cache_1335_);
lean_ctor_set(v_reuseFailAlloc_1346_, 2, v_zetaDeltaFVarIds_1336_);
lean_ctor_set(v_reuseFailAlloc_1346_, 3, v_postponed_1337_);
lean_ctor_set(v_reuseFailAlloc_1346_, 4, v_diag_1338_);
v___x_1343_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = lean_st_ref_put(v___y_1325_, v___x_1343_);
v___x_1345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1345_, 0, v_fst_1332_);
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_){
_start:
{
lean_object* v_res_1352_; 
v_res_1352_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1349_, v___y_1350_);
lean_dec(v___y_1350_);
return v_res_1352_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1353_, v___y_1355_);
return v___x_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_){
_start:
{
lean_object* v_res_1366_; 
v_res_1366_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1360_, v___y_1361_, v___y_1362_, v___y_1363_, v___y_1364_);
lean_dec(v___y_1364_);
lean_dec_ref(v___y_1363_);
lean_dec(v___y_1362_);
lean_dec_ref(v___y_1361_);
return v_res_1366_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1367_, uint8_t v_allowLevelAssignments_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1368_, v_k_1367_, v___y_1369_, v___y_1370_, v___y_1371_, v___y_1372_);
if (lean_obj_tag(v___x_1374_) == 0)
{
lean_object* v_a_1375_; lean_object* v___x_1377_; uint8_t v_isShared_1378_; uint8_t v_isSharedCheck_1382_; 
v_a_1375_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1377_ = v___x_1374_;
v_isShared_1378_ = v_isSharedCheck_1382_;
goto v_resetjp_1376_;
}
else
{
lean_inc(v_a_1375_);
lean_dec(v___x_1374_);
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
v_reuseFailAlloc_1381_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1383_; lean_object* v___x_1385_; uint8_t v_isShared_1386_; uint8_t v_isSharedCheck_1390_; 
v_a_1383_ = lean_ctor_get(v___x_1374_, 0);
v_isSharedCheck_1390_ = !lean_is_exclusive(v___x_1374_);
if (v_isSharedCheck_1390_ == 0)
{
v___x_1385_ = v___x_1374_;
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
else
{
lean_inc(v_a_1383_);
lean_dec(v___x_1374_);
v___x_1385_ = lean_box(0);
v_isShared_1386_ = v_isSharedCheck_1390_;
goto v_resetjp_1384_;
}
v_resetjp_1384_:
{
lean_object* v___x_1388_; 
if (v_isShared_1386_ == 0)
{
v___x_1388_ = v___x_1385_;
goto v_reusejp_1387_;
}
else
{
lean_object* v_reuseFailAlloc_1389_; 
v_reuseFailAlloc_1389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1389_, 0, v_a_1383_);
v___x_1388_ = v_reuseFailAlloc_1389_;
goto v_reusejp_1387_;
}
v_reusejp_1387_:
{
return v___x_1388_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1391_, lean_object* v_allowLevelAssignments_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1398_; lean_object* v_res_1399_; 
v_allowLevelAssignments_boxed_1398_ = lean_unbox(v_allowLevelAssignments_1392_);
v_res_1399_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1391_, v_allowLevelAssignments_boxed_1398_, v___y_1393_, v___y_1394_, v___y_1395_, v___y_1396_);
lean_dec(v___y_1396_);
lean_dec_ref(v___y_1395_);
lean_dec(v___y_1394_);
lean_dec_ref(v___y_1393_);
return v_res_1399_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1400_, lean_object* v_k_1401_, uint8_t v_allowLevelAssignments_1402_, lean_object* v___y_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1401_, v_allowLevelAssignments_1402_, v___y_1403_, v___y_1404_, v___y_1405_, v___y_1406_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1409_, lean_object* v_k_1410_, lean_object* v_allowLevelAssignments_1411_, lean_object* v___y_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1417_; lean_object* v_res_1418_; 
v_allowLevelAssignments_boxed_1417_ = lean_unbox(v_allowLevelAssignments_1411_);
v_res_1418_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1409_, v_k_1410_, v_allowLevelAssignments_boxed_1417_, v___y_1412_, v___y_1413_, v___y_1414_, v___y_1415_);
lean_dec(v___y_1415_);
lean_dec_ref(v___y_1414_);
lean_dec(v___y_1413_);
lean_dec_ref(v___y_1412_);
return v_res_1418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1421_, size_t v_sz_1422_, size_t v_i_1423_, lean_object* v_b_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_a_1431_; uint8_t v___x_1435_; 
v___x_1435_ = lean_usize_dec_lt(v_i_1423_, v_sz_1422_);
if (v___x_1435_ == 0)
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1436_, 0, v_b_1424_);
return v___x_1436_;
}
else
{
lean_object* v_snd_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1599_; 
v_snd_1437_ = lean_ctor_get(v_b_1424_, 1);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_b_1424_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; 
v_unused_1600_ = lean_ctor_get(v_b_1424_, 0);
lean_dec(v_unused_1600_);
v___x_1439_ = v_b_1424_;
v_isShared_1440_ = v_isSharedCheck_1599_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_snd_1437_);
lean_dec(v_b_1424_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1599_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v_array_1441_; lean_object* v_start_1442_; lean_object* v_stop_1443_; lean_object* v___x_1444_; uint8_t v___x_1445_; 
v_array_1441_ = lean_ctor_get(v_snd_1437_, 0);
v_start_1442_ = lean_ctor_get(v_snd_1437_, 1);
v_stop_1443_ = lean_ctor_get(v_snd_1437_, 2);
v___x_1444_ = lean_box(0);
v___x_1445_ = lean_nat_dec_lt(v_start_1442_, v_stop_1443_);
if (v___x_1445_ == 0)
{
lean_object* v___x_1447_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1447_ = v___x_1439_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1449_; 
v_reuseFailAlloc_1449_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1449_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1449_, 1, v_snd_1437_);
v___x_1447_ = v_reuseFailAlloc_1449_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
return v___x_1448_;
}
}
else
{
lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1595_; 
lean_inc(v_stop_1443_);
lean_inc(v_start_1442_);
lean_inc_ref(v_array_1441_);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_snd_1437_);
if (v_isSharedCheck_1595_ == 0)
{
lean_object* v_unused_1596_; lean_object* v_unused_1597_; lean_object* v_unused_1598_; 
v_unused_1596_ = lean_ctor_get(v_snd_1437_, 2);
lean_dec(v_unused_1596_);
v_unused_1597_ = lean_ctor_get(v_snd_1437_, 1);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_snd_1437_, 0);
lean_dec(v_unused_1598_);
v___x_1451_ = v_snd_1437_;
v_isShared_1452_ = v_isSharedCheck_1595_;
goto v_resetjp_1450_;
}
else
{
lean_dec(v_snd_1437_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1595_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1457_; 
v___x_1453_ = lean_array_fget(v_array_1441_, v_start_1442_);
v___x_1454_ = lean_unsigned_to_nat(1u);
v___x_1455_ = lean_nat_add(v_start_1442_, v___x_1454_);
lean_dec(v_start_1442_);
if (v_isShared_1452_ == 0)
{
lean_ctor_set(v___x_1451_, 1, v___x_1455_);
v___x_1457_ = v___x_1451_;
goto v_reusejp_1456_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v_array_1441_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1455_);
lean_ctor_set(v_reuseFailAlloc_1594_, 2, v_stop_1443_);
v___x_1457_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1456_;
}
v_reusejp_1456_:
{
uint8_t v___x_1458_; 
v___x_1458_ = lean_unbox(v___x_1453_);
lean_dec(v___x_1453_);
if (v___x_1458_ == 0)
{
lean_object* v___x_1460_; 
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1457_);
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1460_ = v___x_1439_;
goto v_reusejp_1459_;
}
else
{
lean_object* v_reuseFailAlloc_1461_; 
v_reuseFailAlloc_1461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1461_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1461_, 1, v___x_1457_);
v___x_1460_ = v_reuseFailAlloc_1461_;
goto v_reusejp_1459_;
}
v_reusejp_1459_:
{
v_a_1431_ = v___x_1460_;
goto v___jp_1430_;
}
}
else
{
lean_object* v_a_1462_; lean_object* v___y_1464_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___x_1534_; 
v_a_1462_ = lean_array_uget_borrowed(v_as_1421_, v_i_1423_);
lean_inc(v___y_1428_);
lean_inc_ref(v___y_1427_);
lean_inc(v___y_1426_);
lean_inc_ref(v___y_1425_);
lean_inc(v_a_1462_);
v___x_1534_ = lean_infer_type(v_a_1462_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v___x_1536_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v___x_1536_ = l_Lean_Meta_matchEq_x3f(v_a_1535_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1536_) == 0)
{
lean_object* v_a_1537_; 
v_a_1537_ = lean_ctor_get(v___x_1536_, 0);
lean_inc(v_a_1537_);
lean_dec_ref_known(v___x_1536_, 1);
if (lean_obj_tag(v_a_1537_) == 1)
{
lean_object* v_val_1538_; lean_object* v_snd_1539_; lean_object* v_fst_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1576_; 
v_val_1538_ = lean_ctor_get(v_a_1537_, 0);
lean_inc(v_val_1538_);
lean_dec_ref_known(v_a_1537_, 1);
v_snd_1539_ = lean_ctor_get(v_val_1538_, 1);
lean_inc(v_snd_1539_);
lean_dec(v_val_1538_);
v_fst_1540_ = lean_ctor_get(v_snd_1539_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v_snd_1539_);
if (v_isSharedCheck_1576_ == 0)
{
lean_object* v_unused_1577_; 
v_unused_1577_ = lean_ctor_get(v_snd_1539_, 1);
lean_dec(v_unused_1577_);
v___x_1542_ = v_snd_1539_;
v_isShared_1543_ = v_isSharedCheck_1576_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_fst_1540_);
lean_dec(v_snd_1539_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1576_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1544_; 
v___x_1544_ = l_Lean_Meta_mkEqRefl(v_fst_1540_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1544_) == 0)
{
lean_object* v_a_1545_; lean_object* v___x_1546_; 
v_a_1545_ = lean_ctor_get(v___x_1544_, 0);
lean_inc(v_a_1545_);
lean_dec_ref_known(v___x_1544_, 1);
lean_inc(v_a_1462_);
v___x_1546_ = l_Lean_Meta_isExprDefEq(v_a_1462_, v_a_1545_, v___y_1425_, v___y_1426_, v___y_1427_, v___y_1428_);
if (lean_obj_tag(v___x_1546_) == 0)
{
lean_object* v_a_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1559_; 
v_a_1547_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1549_ = v___x_1546_;
v_isShared_1550_ = v_isSharedCheck_1559_;
goto v_resetjp_1548_;
}
else
{
lean_inc(v_a_1547_);
lean_dec(v___x_1546_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1559_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
uint8_t v___x_1551_; 
v___x_1551_ = lean_unbox(v_a_1547_);
lean_dec(v_a_1547_);
if (v___x_1551_ == 0)
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
lean_del_object(v___x_1439_);
v___x_1552_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1543_ == 0)
{
lean_ctor_set(v___x_1542_, 1, v___x_1457_);
lean_ctor_set(v___x_1542_, 0, v___x_1552_);
v___x_1554_ = v___x_1542_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1558_, 1, v___x_1457_);
v___x_1554_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
lean_object* v___x_1556_; 
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 0, v___x_1554_);
v___x_1556_ = v___x_1549_;
goto v_reusejp_1555_;
}
else
{
lean_object* v_reuseFailAlloc_1557_; 
v_reuseFailAlloc_1557_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1557_, 0, v___x_1554_);
v___x_1556_ = v_reuseFailAlloc_1557_;
goto v_reusejp_1555_;
}
v_reusejp_1555_:
{
return v___x_1556_;
}
}
}
else
{
lean_del_object(v___x_1549_);
lean_del_object(v___x_1542_);
v___y_1464_ = v___y_1425_;
v___y_1465_ = v___y_1426_;
v___y_1466_ = v___y_1427_;
v___y_1467_ = v___y_1428_;
goto v___jp_1463_;
}
}
}
else
{
lean_object* v_a_1560_; lean_object* v___x_1562_; uint8_t v_isShared_1563_; uint8_t v_isSharedCheck_1567_; 
lean_del_object(v___x_1542_);
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1560_ = lean_ctor_get(v___x_1546_, 0);
v_isSharedCheck_1567_ = !lean_is_exclusive(v___x_1546_);
if (v_isSharedCheck_1567_ == 0)
{
v___x_1562_ = v___x_1546_;
v_isShared_1563_ = v_isSharedCheck_1567_;
goto v_resetjp_1561_;
}
else
{
lean_inc(v_a_1560_);
lean_dec(v___x_1546_);
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
else
{
lean_object* v_a_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1575_; 
lean_del_object(v___x_1542_);
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1568_ = lean_ctor_get(v___x_1544_, 0);
v_isSharedCheck_1575_ = !lean_is_exclusive(v___x_1544_);
if (v_isSharedCheck_1575_ == 0)
{
v___x_1570_ = v___x_1544_;
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_a_1568_);
lean_dec(v___x_1544_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1575_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1573_; 
if (v_isShared_1571_ == 0)
{
v___x_1573_ = v___x_1570_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_a_1568_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
}
else
{
lean_dec(v_a_1537_);
v___y_1464_ = v___y_1425_;
v___y_1465_ = v___y_1426_;
v___y_1466_ = v___y_1427_;
v___y_1467_ = v___y_1428_;
goto v___jp_1463_;
}
}
else
{
lean_object* v_a_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1585_; 
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1578_ = lean_ctor_get(v___x_1536_, 0);
v_isSharedCheck_1585_ = !lean_is_exclusive(v___x_1536_);
if (v_isSharedCheck_1585_ == 0)
{
v___x_1580_ = v___x_1536_;
v_isShared_1581_ = v_isSharedCheck_1585_;
goto v_resetjp_1579_;
}
else
{
lean_inc(v_a_1578_);
lean_dec(v___x_1536_);
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
}
else
{
lean_object* v_a_1586_; lean_object* v___x_1588_; uint8_t v_isShared_1589_; uint8_t v_isSharedCheck_1593_; 
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1586_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1593_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1593_ == 0)
{
v___x_1588_ = v___x_1534_;
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
else
{
lean_inc(v_a_1586_);
lean_dec(v___x_1534_);
v___x_1588_ = lean_box(0);
v_isShared_1589_ = v_isSharedCheck_1593_;
goto v_resetjp_1587_;
}
v_resetjp_1587_:
{
lean_object* v___x_1591_; 
if (v_isShared_1589_ == 0)
{
v___x_1591_ = v___x_1588_;
goto v_reusejp_1590_;
}
else
{
lean_object* v_reuseFailAlloc_1592_; 
v_reuseFailAlloc_1592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1592_, 0, v_a_1586_);
v___x_1591_ = v_reuseFailAlloc_1592_;
goto v_reusejp_1590_;
}
v_reusejp_1590_:
{
return v___x_1591_;
}
}
}
v___jp_1463_:
{
lean_object* v___x_1468_; 
lean_inc(v___y_1467_);
lean_inc_ref(v___y_1466_);
lean_inc(v___y_1465_);
lean_inc_ref(v___y_1464_);
lean_inc(v_a_1462_);
v___x_1468_ = lean_infer_type(v_a_1462_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1468_) == 0)
{
lean_object* v_a_1469_; lean_object* v___x_1470_; 
v_a_1469_ = lean_ctor_get(v___x_1468_, 0);
lean_inc(v_a_1469_);
lean_dec_ref_known(v___x_1468_, 1);
v___x_1470_ = l_Lean_Meta_matchHEq_x3f(v_a_1469_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1470_) == 0)
{
lean_object* v_a_1471_; 
v_a_1471_ = lean_ctor_get(v___x_1470_, 0);
lean_inc(v_a_1471_);
lean_dec_ref_known(v___x_1470_, 1);
if (lean_obj_tag(v_a_1471_) == 1)
{
lean_object* v_val_1472_; lean_object* v_snd_1473_; lean_object* v_fst_1474_; lean_object* v___x_1476_; uint8_t v_isShared_1477_; uint8_t v_isSharedCheck_1513_; 
lean_del_object(v___x_1439_);
v_val_1472_ = lean_ctor_get(v_a_1471_, 0);
lean_inc(v_val_1472_);
lean_dec_ref_known(v_a_1471_, 1);
v_snd_1473_ = lean_ctor_get(v_val_1472_, 1);
lean_inc(v_snd_1473_);
lean_dec(v_val_1472_);
v_fst_1474_ = lean_ctor_get(v_snd_1473_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_snd_1473_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; 
v_unused_1514_ = lean_ctor_get(v_snd_1473_, 1);
lean_dec(v_unused_1514_);
v___x_1476_ = v_snd_1473_;
v_isShared_1477_ = v_isSharedCheck_1513_;
goto v_resetjp_1475_;
}
else
{
lean_inc(v_fst_1474_);
lean_dec(v_snd_1473_);
v___x_1476_ = lean_box(0);
v_isShared_1477_ = v_isSharedCheck_1513_;
goto v_resetjp_1475_;
}
v_resetjp_1475_:
{
lean_object* v___x_1478_; 
v___x_1478_ = l_Lean_Meta_mkHEqRefl(v_fst_1474_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1478_) == 0)
{
lean_object* v_a_1479_; lean_object* v___x_1480_; 
v_a_1479_ = lean_ctor_get(v___x_1478_, 0);
lean_inc(v_a_1479_);
lean_dec_ref_known(v___x_1478_, 1);
lean_inc(v_a_1462_);
v___x_1480_ = l_Lean_Meta_isExprDefEq(v_a_1462_, v_a_1479_, v___y_1464_, v___y_1465_, v___y_1466_, v___y_1467_);
if (lean_obj_tag(v___x_1480_) == 0)
{
lean_object* v_a_1481_; lean_object* v___x_1483_; uint8_t v_isShared_1484_; uint8_t v_isSharedCheck_1496_; 
v_a_1481_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1483_ = v___x_1480_;
v_isShared_1484_ = v_isSharedCheck_1496_;
goto v_resetjp_1482_;
}
else
{
lean_inc(v_a_1481_);
lean_dec(v___x_1480_);
v___x_1483_ = lean_box(0);
v_isShared_1484_ = v_isSharedCheck_1496_;
goto v_resetjp_1482_;
}
v_resetjp_1482_:
{
uint8_t v___x_1485_; 
v___x_1485_ = lean_unbox(v_a_1481_);
lean_dec(v_a_1481_);
if (v___x_1485_ == 0)
{
lean_object* v___x_1486_; lean_object* v___x_1488_; 
v___x_1486_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v___x_1457_);
lean_ctor_set(v___x_1476_, 0, v___x_1486_);
v___x_1488_ = v___x_1476_;
goto v_reusejp_1487_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1486_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1457_);
v___x_1488_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1487_;
}
v_reusejp_1487_:
{
lean_object* v___x_1490_; 
if (v_isShared_1484_ == 0)
{
lean_ctor_set(v___x_1483_, 0, v___x_1488_);
v___x_1490_ = v___x_1483_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_object* v___x_1494_; 
lean_del_object(v___x_1483_);
if (v_isShared_1477_ == 0)
{
lean_ctor_set(v___x_1476_, 1, v___x_1457_);
lean_ctor_set(v___x_1476_, 0, v___x_1444_);
v___x_1494_ = v___x_1476_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v___x_1457_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
v_a_1431_ = v___x_1494_;
goto v___jp_1430_;
}
}
}
}
else
{
lean_object* v_a_1497_; lean_object* v___x_1499_; uint8_t v_isShared_1500_; uint8_t v_isSharedCheck_1504_; 
lean_del_object(v___x_1476_);
lean_dec_ref(v___x_1457_);
v_a_1497_ = lean_ctor_get(v___x_1480_, 0);
v_isSharedCheck_1504_ = !lean_is_exclusive(v___x_1480_);
if (v_isSharedCheck_1504_ == 0)
{
v___x_1499_ = v___x_1480_;
v_isShared_1500_ = v_isSharedCheck_1504_;
goto v_resetjp_1498_;
}
else
{
lean_inc(v_a_1497_);
lean_dec(v___x_1480_);
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
else
{
lean_object* v_a_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1512_; 
lean_del_object(v___x_1476_);
lean_dec_ref(v___x_1457_);
v_a_1505_ = lean_ctor_get(v___x_1478_, 0);
v_isSharedCheck_1512_ = !lean_is_exclusive(v___x_1478_);
if (v_isSharedCheck_1512_ == 0)
{
v___x_1507_ = v___x_1478_;
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
else
{
lean_inc(v_a_1505_);
lean_dec(v___x_1478_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1512_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1510_; 
if (v_isShared_1508_ == 0)
{
v___x_1510_ = v___x_1507_;
goto v_reusejp_1509_;
}
else
{
lean_object* v_reuseFailAlloc_1511_; 
v_reuseFailAlloc_1511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1511_, 0, v_a_1505_);
v___x_1510_ = v_reuseFailAlloc_1511_;
goto v_reusejp_1509_;
}
v_reusejp_1509_:
{
return v___x_1510_;
}
}
}
}
}
else
{
lean_object* v___x_1516_; 
lean_dec(v_a_1471_);
if (v_isShared_1440_ == 0)
{
lean_ctor_set(v___x_1439_, 1, v___x_1457_);
lean_ctor_set(v___x_1439_, 0, v___x_1444_);
v___x_1516_ = v___x_1439_;
goto v_reusejp_1515_;
}
else
{
lean_object* v_reuseFailAlloc_1517_; 
v_reuseFailAlloc_1517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1444_);
lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1457_);
v___x_1516_ = v_reuseFailAlloc_1517_;
goto v_reusejp_1515_;
}
v_reusejp_1515_:
{
v_a_1431_ = v___x_1516_;
goto v___jp_1430_;
}
}
}
else
{
lean_object* v_a_1518_; lean_object* v___x_1520_; uint8_t v_isShared_1521_; uint8_t v_isSharedCheck_1525_; 
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1518_ = lean_ctor_get(v___x_1470_, 0);
v_isSharedCheck_1525_ = !lean_is_exclusive(v___x_1470_);
if (v_isSharedCheck_1525_ == 0)
{
v___x_1520_ = v___x_1470_;
v_isShared_1521_ = v_isSharedCheck_1525_;
goto v_resetjp_1519_;
}
else
{
lean_inc(v_a_1518_);
lean_dec(v___x_1470_);
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
else
{
lean_object* v_a_1526_; lean_object* v___x_1528_; uint8_t v_isShared_1529_; uint8_t v_isSharedCheck_1533_; 
lean_dec_ref(v___x_1457_);
lean_del_object(v___x_1439_);
v_a_1526_ = lean_ctor_get(v___x_1468_, 0);
v_isSharedCheck_1533_ = !lean_is_exclusive(v___x_1468_);
if (v_isSharedCheck_1533_ == 0)
{
v___x_1528_ = v___x_1468_;
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
else
{
lean_inc(v_a_1526_);
lean_dec(v___x_1468_);
v___x_1528_ = lean_box(0);
v_isShared_1529_ = v_isSharedCheck_1533_;
goto v_resetjp_1527_;
}
v_resetjp_1527_:
{
lean_object* v___x_1531_; 
if (v_isShared_1529_ == 0)
{
v___x_1531_ = v___x_1528_;
goto v_reusejp_1530_;
}
else
{
lean_object* v_reuseFailAlloc_1532_; 
v_reuseFailAlloc_1532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1532_, 0, v_a_1526_);
v___x_1531_ = v_reuseFailAlloc_1532_;
goto v_reusejp_1530_;
}
v_reusejp_1530_:
{
return v___x_1531_;
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
v___jp_1430_:
{
size_t v___x_1432_; size_t v___x_1433_; 
v___x_1432_ = ((size_t)1ULL);
v___x_1433_ = lean_usize_add(v_i_1423_, v___x_1432_);
v_i_1423_ = v___x_1433_;
v_b_1424_ = v_a_1431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1601_, lean_object* v_sz_1602_, lean_object* v_i_1603_, lean_object* v_b_1604_, lean_object* v___y_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_){
_start:
{
size_t v_sz_boxed_1610_; size_t v_i_boxed_1611_; lean_object* v_res_1612_; 
v_sz_boxed_1610_ = lean_unbox_usize(v_sz_1602_);
lean_dec(v_sz_1602_);
v_i_boxed_1611_ = lean_unbox_usize(v_i_1603_);
lean_dec(v_i_1603_);
v_res_1612_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1601_, v_sz_boxed_1610_, v_i_boxed_1611_, v_b_1604_, v___y_1605_, v___y_1606_, v___y_1607_, v___y_1608_);
lean_dec(v___y_1608_);
lean_dec_ref(v___y_1607_);
lean_dec(v___y_1606_);
lean_dec_ref(v___y_1605_);
lean_dec_ref(v_as_1601_);
return v_res_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1613_, uint8_t v___x_1614_, lean_object* v_localDecl_1615_, lean_object* v_mvarId_1616_, lean_object* v___y_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_){
_start:
{
lean_object* v___x_1622_; 
lean_inc_ref(v___x_1613_);
v___x_1622_ = l_Lean_Meta_forallMetaTelescope(v___x_1613_, v___x_1614_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1622_) == 0)
{
lean_object* v_a_1623_; lean_object* v_fst_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1713_; 
v_a_1623_ = lean_ctor_get(v___x_1622_, 0);
lean_inc(v_a_1623_);
lean_dec_ref_known(v___x_1622_, 1);
v_fst_1624_ = lean_ctor_get(v_a_1623_, 0);
v_isSharedCheck_1713_ = !lean_is_exclusive(v_a_1623_);
if (v_isSharedCheck_1713_ == 0)
{
lean_object* v_unused_1714_; 
v_unused_1714_ = lean_ctor_get(v_a_1623_, 1);
lean_dec(v_unused_1714_);
v___x_1626_ = v_a_1623_;
v_isShared_1627_ = v_isSharedCheck_1713_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_fst_1624_);
lean_dec(v_a_1623_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1713_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; 
v___x_1628_ = l_Lean_Meta_mkGenDiseqMask(v___x_1613_);
lean_dec_ref(v___x_1613_);
v___x_1629_ = lean_unsigned_to_nat(0u);
v___x_1630_ = lean_array_get_size(v___x_1628_);
v___x_1631_ = l_Array_toSubarray___redArg(v___x_1628_, v___x_1629_, v___x_1630_);
v___x_1632_ = lean_box(0);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 1, v___x_1631_);
lean_ctor_set(v___x_1626_, 0, v___x_1632_);
v___x_1634_ = v___x_1626_;
goto v_reusejp_1633_;
}
else
{
lean_object* v_reuseFailAlloc_1712_; 
v_reuseFailAlloc_1712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1712_, 0, v___x_1632_);
lean_ctor_set(v_reuseFailAlloc_1712_, 1, v___x_1631_);
v___x_1634_ = v_reuseFailAlloc_1712_;
goto v_reusejp_1633_;
}
v_reusejp_1633_:
{
size_t v_sz_1635_; size_t v___x_1636_; lean_object* v___x_1637_; 
v_sz_1635_ = lean_array_size(v_fst_1624_);
v___x_1636_ = ((size_t)0ULL);
v___x_1637_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1624_, v_sz_1635_, v___x_1636_, v___x_1634_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1637_) == 0)
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1703_; 
v_a_1638_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1703_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1703_ == 0)
{
v___x_1640_ = v___x_1637_;
v_isShared_1641_ = v_isSharedCheck_1703_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1637_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1703_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v_fst_1642_; 
v_fst_1642_ = lean_ctor_get(v_a_1638_, 0);
lean_inc(v_fst_1642_);
lean_dec(v_a_1638_);
if (lean_obj_tag(v_fst_1642_) == 0)
{
lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_a_1646_; lean_object* v___x_1648_; uint8_t v_isShared_1649_; uint8_t v_isSharedCheck_1698_; 
lean_del_object(v___x_1640_);
v___x_1643_ = l_Lean_LocalDecl_toExpr(v_localDecl_1615_);
v___x_1644_ = l_Lean_mkAppN(v___x_1643_, v_fst_1624_);
lean_dec(v_fst_1624_);
v___x_1645_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1644_, v___y_1618_);
v_a_1646_ = lean_ctor_get(v___x_1645_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1645_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1648_ = v___x_1645_;
v_isShared_1649_ = v_isSharedCheck_1698_;
goto v_resetjp_1647_;
}
else
{
lean_inc(v_a_1646_);
lean_dec(v___x_1645_);
v___x_1648_ = lean_box(0);
v_isShared_1649_ = v_isSharedCheck_1698_;
goto v_resetjp_1647_;
}
v_resetjp_1647_:
{
lean_object* v___x_1650_; 
lean_inc(v_a_1646_);
v___x_1650_ = l_Lean_Meta_hasAssignableMVar(v_a_1646_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_a_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1689_; 
v_a_1651_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1689_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1689_ == 0)
{
v___x_1653_ = v___x_1650_;
v_isShared_1654_ = v_isSharedCheck_1689_;
goto v_resetjp_1652_;
}
else
{
lean_inc(v_a_1651_);
lean_dec(v___x_1650_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1689_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
uint8_t v___x_1655_; 
v___x_1655_ = lean_unbox(v_a_1651_);
lean_dec(v_a_1651_);
if (v___x_1655_ == 0)
{
lean_object* v___x_1656_; 
lean_del_object(v___x_1653_);
v___x_1656_ = l_Lean_MVarId_getType(v_mvarId_1616_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1656_) == 0)
{
lean_object* v_a_1657_; lean_object* v___x_1658_; 
v_a_1657_ = lean_ctor_get(v___x_1656_, 0);
lean_inc(v_a_1657_);
lean_dec_ref_known(v___x_1656_, 1);
v___x_1658_ = l_Lean_Meta_mkFalseElim(v_a_1657_, v_a_1646_, v___y_1617_, v___y_1618_, v___y_1619_, v___y_1620_);
if (lean_obj_tag(v___x_1658_) == 0)
{
lean_object* v_a_1659_; lean_object* v___x_1661_; uint8_t v_isShared_1662_; uint8_t v_isSharedCheck_1669_; 
v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1669_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1669_ == 0)
{
v___x_1661_ = v___x_1658_;
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
else
{
lean_inc(v_a_1659_);
lean_dec(v___x_1658_);
v___x_1661_ = lean_box(0);
v_isShared_1662_ = v_isSharedCheck_1669_;
goto v_resetjp_1660_;
}
v_resetjp_1660_:
{
lean_object* v___x_1664_; 
if (v_isShared_1649_ == 0)
{
lean_ctor_set_tag(v___x_1648_, 1);
lean_ctor_set(v___x_1648_, 0, v_a_1659_);
v___x_1664_ = v___x_1648_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_a_1659_);
v___x_1664_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
lean_object* v___x_1666_; 
if (v_isShared_1662_ == 0)
{
lean_ctor_set(v___x_1661_, 0, v___x_1664_);
v___x_1666_ = v___x_1661_;
goto v_reusejp_1665_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
v___x_1666_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1665_;
}
v_reusejp_1665_:
{
return v___x_1666_;
}
}
}
}
else
{
lean_object* v_a_1670_; lean_object* v___x_1672_; uint8_t v_isShared_1673_; uint8_t v_isSharedCheck_1677_; 
lean_del_object(v___x_1648_);
v_a_1670_ = lean_ctor_get(v___x_1658_, 0);
v_isSharedCheck_1677_ = !lean_is_exclusive(v___x_1658_);
if (v_isSharedCheck_1677_ == 0)
{
v___x_1672_ = v___x_1658_;
v_isShared_1673_ = v_isSharedCheck_1677_;
goto v_resetjp_1671_;
}
else
{
lean_inc(v_a_1670_);
lean_dec(v___x_1658_);
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
lean_object* v_a_1678_; lean_object* v___x_1680_; uint8_t v_isShared_1681_; uint8_t v_isSharedCheck_1685_; 
lean_del_object(v___x_1648_);
lean_dec(v_a_1646_);
v_a_1678_ = lean_ctor_get(v___x_1656_, 0);
v_isSharedCheck_1685_ = !lean_is_exclusive(v___x_1656_);
if (v_isSharedCheck_1685_ == 0)
{
v___x_1680_ = v___x_1656_;
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
else
{
lean_inc(v_a_1678_);
lean_dec(v___x_1656_);
v___x_1680_ = lean_box(0);
v_isShared_1681_ = v_isSharedCheck_1685_;
goto v_resetjp_1679_;
}
v_resetjp_1679_:
{
lean_object* v___x_1683_; 
if (v_isShared_1681_ == 0)
{
v___x_1683_ = v___x_1680_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_a_1678_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
else
{
lean_object* v___x_1687_; 
lean_del_object(v___x_1648_);
lean_dec(v_a_1646_);
lean_dec(v_mvarId_1616_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 0, v___x_1632_);
v___x_1687_ = v___x_1653_;
goto v_reusejp_1686_;
}
else
{
lean_object* v_reuseFailAlloc_1688_; 
v_reuseFailAlloc_1688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1688_, 0, v___x_1632_);
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
else
{
lean_object* v_a_1690_; lean_object* v___x_1692_; uint8_t v_isShared_1693_; uint8_t v_isSharedCheck_1697_; 
lean_del_object(v___x_1648_);
lean_dec(v_a_1646_);
lean_dec(v_mvarId_1616_);
v_a_1690_ = lean_ctor_get(v___x_1650_, 0);
v_isSharedCheck_1697_ = !lean_is_exclusive(v___x_1650_);
if (v_isSharedCheck_1697_ == 0)
{
v___x_1692_ = v___x_1650_;
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
else
{
lean_inc(v_a_1690_);
lean_dec(v___x_1650_);
v___x_1692_ = lean_box(0);
v_isShared_1693_ = v_isSharedCheck_1697_;
goto v_resetjp_1691_;
}
v_resetjp_1691_:
{
lean_object* v___x_1695_; 
if (v_isShared_1693_ == 0)
{
v___x_1695_ = v___x_1692_;
goto v_reusejp_1694_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_a_1690_);
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
}
else
{
lean_object* v_val_1699_; lean_object* v___x_1701_; 
lean_dec(v_fst_1624_);
lean_dec(v_mvarId_1616_);
lean_dec_ref(v_localDecl_1615_);
v_val_1699_ = lean_ctor_get(v_fst_1642_, 0);
lean_inc(v_val_1699_);
lean_dec_ref_known(v_fst_1642_, 1);
if (v_isShared_1641_ == 0)
{
lean_ctor_set(v___x_1640_, 0, v_val_1699_);
v___x_1701_ = v___x_1640_;
goto v_reusejp_1700_;
}
else
{
lean_object* v_reuseFailAlloc_1702_; 
v_reuseFailAlloc_1702_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1702_, 0, v_val_1699_);
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
else
{
lean_object* v_a_1704_; lean_object* v___x_1706_; uint8_t v_isShared_1707_; uint8_t v_isSharedCheck_1711_; 
lean_dec(v_fst_1624_);
lean_dec(v_mvarId_1616_);
lean_dec_ref(v_localDecl_1615_);
v_a_1704_ = lean_ctor_get(v___x_1637_, 0);
v_isSharedCheck_1711_ = !lean_is_exclusive(v___x_1637_);
if (v_isSharedCheck_1711_ == 0)
{
v___x_1706_ = v___x_1637_;
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
else
{
lean_inc(v_a_1704_);
lean_dec(v___x_1637_);
v___x_1706_ = lean_box(0);
v_isShared_1707_ = v_isSharedCheck_1711_;
goto v_resetjp_1705_;
}
v_resetjp_1705_:
{
lean_object* v___x_1709_; 
if (v_isShared_1707_ == 0)
{
v___x_1709_ = v___x_1706_;
goto v_reusejp_1708_;
}
else
{
lean_object* v_reuseFailAlloc_1710_; 
v_reuseFailAlloc_1710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1710_, 0, v_a_1704_);
v___x_1709_ = v_reuseFailAlloc_1710_;
goto v_reusejp_1708_;
}
v_reusejp_1708_:
{
return v___x_1709_;
}
}
}
}
}
}
else
{
lean_object* v_a_1715_; lean_object* v___x_1717_; uint8_t v_isShared_1718_; uint8_t v_isSharedCheck_1722_; 
lean_dec(v_mvarId_1616_);
lean_dec_ref(v_localDecl_1615_);
lean_dec_ref(v___x_1613_);
v_a_1715_ = lean_ctor_get(v___x_1622_, 0);
v_isSharedCheck_1722_ = !lean_is_exclusive(v___x_1622_);
if (v_isSharedCheck_1722_ == 0)
{
v___x_1717_ = v___x_1622_;
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
else
{
lean_inc(v_a_1715_);
lean_dec(v___x_1622_);
v___x_1717_ = lean_box(0);
v_isShared_1718_ = v_isSharedCheck_1722_;
goto v_resetjp_1716_;
}
v_resetjp_1716_:
{
lean_object* v___x_1720_; 
if (v_isShared_1718_ == 0)
{
v___x_1720_ = v___x_1717_;
goto v_reusejp_1719_;
}
else
{
lean_object* v_reuseFailAlloc_1721_; 
v_reuseFailAlloc_1721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1721_, 0, v_a_1715_);
v___x_1720_ = v_reuseFailAlloc_1721_;
goto v_reusejp_1719_;
}
v_reusejp_1719_:
{
return v___x_1720_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1723_, lean_object* v___x_1724_, lean_object* v_localDecl_1725_, lean_object* v_mvarId_1726_, lean_object* v___y_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_){
_start:
{
uint8_t v___x_6078__boxed_1732_; lean_object* v_res_1733_; 
v___x_6078__boxed_1732_ = lean_unbox(v___x_1724_);
v_res_1733_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1723_, v___x_6078__boxed_1732_, v_localDecl_1725_, v_mvarId_1726_, v___y_1727_, v___y_1728_, v___y_1729_, v___y_1730_);
lean_dec(v___y_1730_);
lean_dec_ref(v___y_1729_);
lean_dec(v___y_1728_);
lean_dec_ref(v___y_1727_);
return v_res_1733_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; 
v___x_1737_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1738_ = lean_unsigned_to_nat(2u);
v___x_1739_ = lean_unsigned_to_nat(120u);
v___x_1740_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1742_ = l_mkPanicMessageWithDecl(v___x_1741_, v___x_1740_, v___x_1739_, v___x_1738_, v___x_1737_);
return v___x_1742_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1743_, lean_object* v_localDecl_1744_, lean_object* v_a_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_){
_start:
{
lean_object* v___x_1750_; uint8_t v___x_1751_; 
v___x_1750_ = l_Lean_LocalDecl_type(v_localDecl_1744_);
lean_inc_ref(v___x_1750_);
v___x_1751_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1750_);
if (v___x_1751_ == 0)
{
lean_object* v___x_1752_; lean_object* v___x_1753_; 
lean_dec_ref(v___x_1750_);
lean_dec_ref(v_localDecl_1744_);
lean_dec(v_mvarId_1743_);
v___x_1752_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1753_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1752_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
return v___x_1753_;
}
else
{
uint8_t v___x_1754_; lean_object* v___x_1755_; lean_object* v___f_1756_; uint8_t v___x_1757_; lean_object* v___x_1758_; 
v___x_1754_ = 0;
v___x_1755_ = lean_box(v___x_1754_);
lean_inc(v_mvarId_1743_);
v___f_1756_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1756_, 0, v___x_1750_);
lean_closure_set(v___f_1756_, 1, v___x_1755_);
lean_closure_set(v___f_1756_, 2, v_localDecl_1744_);
lean_closure_set(v___f_1756_, 3, v_mvarId_1743_);
v___x_1757_ = 0;
v___x_1758_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1756_, v___x_1757_, v_a_1745_, v_a_1746_, v_a_1747_, v_a_1748_);
if (lean_obj_tag(v___x_1758_) == 0)
{
lean_object* v_a_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1778_; 
v_a_1759_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1761_ = v___x_1758_;
v_isShared_1762_ = v_isSharedCheck_1778_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_a_1759_);
lean_dec(v___x_1758_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1778_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
if (lean_obj_tag(v_a_1759_) == 1)
{
lean_object* v_val_1763_; lean_object* v___x_1764_; lean_object* v___x_1766_; uint8_t v_isShared_1767_; uint8_t v_isSharedCheck_1772_; 
lean_del_object(v___x_1761_);
v_val_1763_ = lean_ctor_get(v_a_1759_, 0);
lean_inc(v_val_1763_);
lean_dec_ref_known(v_a_1759_, 1);
v___x_1764_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1743_, v_val_1763_, v_a_1746_);
v_isSharedCheck_1772_ = !lean_is_exclusive(v___x_1764_);
if (v_isSharedCheck_1772_ == 0)
{
lean_object* v_unused_1773_; 
v_unused_1773_ = lean_ctor_get(v___x_1764_, 0);
lean_dec(v_unused_1773_);
v___x_1766_ = v___x_1764_;
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
else
{
lean_dec(v___x_1764_);
v___x_1766_ = lean_box(0);
v_isShared_1767_ = v_isSharedCheck_1772_;
goto v_resetjp_1765_;
}
v_resetjp_1765_:
{
lean_object* v___x_1768_; lean_object* v___x_1770_; 
v___x_1768_ = lean_box(v___x_1751_);
if (v_isShared_1767_ == 0)
{
lean_ctor_set(v___x_1766_, 0, v___x_1768_);
v___x_1770_ = v___x_1766_;
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
else
{
lean_object* v___x_1774_; lean_object* v___x_1776_; 
lean_dec(v_a_1759_);
lean_dec(v_mvarId_1743_);
v___x_1774_ = lean_box(v___x_1757_);
if (v_isShared_1762_ == 0)
{
lean_ctor_set(v___x_1761_, 0, v___x_1774_);
v___x_1776_ = v___x_1761_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v___x_1774_);
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
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
lean_dec(v_mvarId_1743_);
v_a_1779_ = lean_ctor_get(v___x_1758_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1758_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1758_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1758_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1787_, lean_object* v_localDecl_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1787_, v_localDecl_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
lean_dec_ref(v_a_1789_);
return v_res_1794_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_box(0);
v___x_1807_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1808_ = l_Lean_mkConst(v___x_1807_, v___x_1806_);
return v___x_1808_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1809_; lean_object* v_dummy_1810_; 
v___x_1809_ = lean_box(0);
v_dummy_1810_ = l_Lean_Expr_sort___override(v___x_1809_);
return v_dummy_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1811_, lean_object* v_mvarId_1812_, lean_object* v_as_1813_, size_t v_sz_1814_, size_t v_i_1815_, lean_object* v_b_1816_, lean_object* v___y_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_){
_start:
{
uint8_t v___x_1822_; 
v___x_1822_ = lean_usize_dec_lt(v_i_1815_, v_sz_1814_);
if (v___x_1822_ == 0)
{
lean_object* v___x_1823_; 
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v___x_1823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1823_, 0, v_b_1816_);
return v___x_1823_;
}
else
{
lean_object* v_snd_1824_; lean_object* v___x_1826_; uint8_t v_isShared_1827_; uint8_t v_isSharedCheck_2474_; 
v_snd_1824_ = lean_ctor_get(v_b_1816_, 1);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_b_1816_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v_b_1816_, 0);
lean_dec(v_unused_2475_);
v___x_1826_ = v_b_1816_;
v_isShared_1827_ = v_isSharedCheck_2474_;
goto v_resetjp_1825_;
}
else
{
lean_inc(v_snd_1824_);
lean_dec(v_b_1816_);
v___x_1826_ = lean_box(0);
v_isShared_1827_ = v_isSharedCheck_2474_;
goto v_resetjp_1825_;
}
v_resetjp_1825_:
{
lean_object* v_a_1829_; lean_object* v___x_1835_; lean_object* v_a_1837_; lean_object* v_a_1842_; 
v___x_1835_ = lean_box(0);
v_a_1842_ = lean_array_uget(v_as_1813_, v_i_1815_);
if (lean_obj_tag(v_a_1842_) == 0)
{
lean_del_object(v___x_1826_);
v_a_1837_ = v_snd_1824_;
goto v___jp_1836_;
}
else
{
lean_object* v_val_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_2473_; 
v_val_1843_ = lean_ctor_get(v_a_1842_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v_a_1842_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_1845_ = v_a_1842_;
v_isShared_1846_ = v_isSharedCheck_2473_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_val_1843_);
lean_dec(v_a_1842_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_2473_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___y_1849_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___x_1888_; lean_object* v___y_1890_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1911_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; uint8_t v___y_1915_; uint8_t v___x_1916_; lean_object* v___y_1918_; lean_object* v___y_1919_; uint8_t v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1924_; lean_object* v___y_1925_; uint8_t v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; uint8_t v___y_1929_; uint8_t v___y_1931_; uint8_t v___y_1932_; lean_object* v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1939_; lean_object* v___y_1940_; uint8_t v___y_1941_; lean_object* v___y_1942_; uint8_t v___y_1943_; lean_object* v___y_1944_; uint8_t v___y_1945_; 
v___x_1847_ = lean_box(0);
v___x_1888_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1916_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1843_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1960_; uint8_t v___y_1962_; uint8_t v___y_1963_; lean_object* v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1971_; lean_object* v___y_1972_; uint8_t v___y_1973_; lean_object* v___y_1974_; uint8_t v___y_1975_; lean_object* v___y_1976_; lean_object* v___y_1977_; uint8_t v___y_1978_; lean_object* v___y_1981_; uint8_t v___y_1982_; lean_object* v___y_1983_; uint8_t v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v_a_1987_; lean_object* v___y_1991_; lean_object* v___y_1992_; uint8_t v___y_1993_; lean_object* v___y_1994_; uint8_t v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_2035_; uint8_t v___y_2036_; lean_object* v___y_2037_; uint8_t v___y_2038_; lean_object* v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2064_; uint8_t v___y_2065_; lean_object* v___y_2066_; uint8_t v___y_2067_; lean_object* v___y_2068_; lean_object* v___y_2069_; uint8_t v___y_2070_; lean_object* v___y_2072_; uint8_t v___y_2073_; lean_object* v___y_2074_; uint8_t v___y_2075_; lean_object* v___y_2076_; lean_object* v___y_2077_; lean_object* v___y_2078_; uint8_t v___y_2079_; lean_object* v___y_2082_; uint8_t v___y_2083_; lean_object* v___y_2084_; uint8_t v___y_2085_; lean_object* v___y_2086_; lean_object* v___y_2087_; uint8_t v___y_2088_; lean_object* v___y_2101_; uint8_t v___y_2102_; lean_object* v___y_2103_; uint8_t v___y_2104_; lean_object* v___y_2105_; lean_object* v___y_2106_; uint8_t v___y_2107_; uint8_t v___y_2109_; uint8_t v_isHEq_2110_; lean_object* v___y_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; uint8_t v___y_2123_; lean_object* v___y_2124_; uint8_t v_isEq_2180_; lean_object* v___y_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2230_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2276_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___x_2410_; 
v___x_1960_ = l_Lean_LocalDecl_type(v_val_1843_);
lean_inc_ref(v___x_1960_);
v___x_2410_ = l_Lean_Meta_matchNot_x3f(v___x_1960_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_2410_) == 0)
{
lean_object* v_a_2411_; 
v_a_2411_ = lean_ctor_get(v___x_2410_, 0);
lean_inc(v_a_2411_);
lean_dec_ref_known(v___x_2410_, 1);
if (lean_obj_tag(v_a_2411_) == 1)
{
lean_object* v_val_2412_; lean_object* v___x_2413_; 
v_val_2412_ = lean_ctor_get(v_a_2411_, 0);
lean_inc(v_val_2412_);
lean_dec_ref_known(v_a_2411_, 1);
v___x_2413_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2412_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_2413_) == 0)
{
lean_object* v_a_2414_; 
v_a_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc(v_a_2414_);
lean_dec_ref_known(v___x_2413_, 1);
if (lean_obj_tag(v_a_2414_) == 1)
{
lean_object* v_val_2415_; lean_object* v___x_2417_; uint8_t v_isShared_2418_; uint8_t v_isSharedCheck_2456_; 
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec_ref(v_config_1811_);
v_val_2415_ = lean_ctor_get(v_a_2414_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_a_2414_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2417_ = v_a_2414_;
v_isShared_2418_ = v_isSharedCheck_2456_;
goto v_resetjp_2416_;
}
else
{
lean_inc(v_val_2415_);
lean_dec(v_a_2414_);
v___x_2417_ = lean_box(0);
v_isShared_2418_ = v_isSharedCheck_2456_;
goto v_resetjp_2416_;
}
v_resetjp_2416_:
{
lean_object* v___x_2419_; 
lean_inc(v_mvarId_1812_);
v___x_2419_ = l_Lean_MVarId_getType(v_mvarId_1812_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_2419_) == 0)
{
lean_object* v_a_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v_a_2420_ = lean_ctor_get(v___x_2419_, 0);
lean_inc(v_a_2420_);
lean_dec_ref_known(v___x_2419_, 1);
v___x_2421_ = l_Lean_LocalDecl_toExpr(v_val_1843_);
v___x_2422_ = l_Lean_mkFVar(v_val_2415_);
v___x_2423_ = l_Lean_Expr_app___override(v___x_2421_, v___x_2422_);
v___x_2424_ = l_Lean_Meta_mkFalseElim(v_a_2420_, v___x_2423_, v___y_1817_, v___y_1818_, v___y_1819_, v___y_1820_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2426_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2426_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1812_, v_a_2425_, v___y_1818_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v___x_2427_; lean_object* v___x_2429_; 
lean_dec_ref_known(v___x_2426_, 1);
v___x_2427_ = lean_box(v___x_1822_);
if (v_isShared_2418_ == 0)
{
lean_ctor_set(v___x_2417_, 0, v___x_2427_);
v___x_2429_ = v___x_2417_;
goto v_reusejp_2428_;
}
else
{
lean_object* v_reuseFailAlloc_2431_; 
v_reuseFailAlloc_2431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2431_, 0, v___x_2427_);
v___x_2429_ = v_reuseFailAlloc_2431_;
goto v_reusejp_2428_;
}
v_reusejp_2428_:
{
lean_object* v___x_2430_; 
v___x_2430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2429_);
lean_ctor_set(v___x_2430_, 1, v___x_1847_);
v_a_1829_ = v___x_2430_;
goto v___jp_1828_;
}
}
else
{
lean_object* v_a_2432_; lean_object* v___x_2434_; uint8_t v_isShared_2435_; uint8_t v_isSharedCheck_2439_; 
lean_del_object(v___x_2417_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
v_a_2432_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2439_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2439_ == 0)
{
v___x_2434_ = v___x_2426_;
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
else
{
lean_inc(v_a_2432_);
lean_dec(v___x_2426_);
v___x_2434_ = lean_box(0);
v_isShared_2435_ = v_isSharedCheck_2439_;
goto v_resetjp_2433_;
}
v_resetjp_2433_:
{
lean_object* v___x_2437_; 
if (v_isShared_2435_ == 0)
{
v___x_2437_ = v___x_2434_;
goto v_reusejp_2436_;
}
else
{
lean_object* v_reuseFailAlloc_2438_; 
v_reuseFailAlloc_2438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2438_, 0, v_a_2432_);
v___x_2437_ = v_reuseFailAlloc_2438_;
goto v_reusejp_2436_;
}
v_reusejp_2436_:
{
return v___x_2437_;
}
}
}
}
else
{
lean_object* v_a_2440_; lean_object* v___x_2442_; uint8_t v_isShared_2443_; uint8_t v_isSharedCheck_2447_; 
lean_del_object(v___x_2417_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_2440_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2447_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2447_ == 0)
{
v___x_2442_ = v___x_2424_;
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
else
{
lean_inc(v_a_2440_);
lean_dec(v___x_2424_);
v___x_2442_ = lean_box(0);
v_isShared_2443_ = v_isSharedCheck_2447_;
goto v_resetjp_2441_;
}
v_resetjp_2441_:
{
lean_object* v___x_2445_; 
if (v_isShared_2443_ == 0)
{
v___x_2445_ = v___x_2442_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2446_; 
v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2440_);
v___x_2445_ = v_reuseFailAlloc_2446_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
return v___x_2445_;
}
}
}
}
else
{
lean_object* v_a_2448_; lean_object* v___x_2450_; uint8_t v_isShared_2451_; uint8_t v_isSharedCheck_2455_; 
lean_del_object(v___x_2417_);
lean_dec(v_val_2415_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_2448_ = lean_ctor_get(v___x_2419_, 0);
v_isSharedCheck_2455_ = !lean_is_exclusive(v___x_2419_);
if (v_isSharedCheck_2455_ == 0)
{
v___x_2450_ = v___x_2419_;
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
else
{
lean_inc(v_a_2448_);
lean_dec(v___x_2419_);
v___x_2450_ = lean_box(0);
v_isShared_2451_ = v_isSharedCheck_2455_;
goto v_resetjp_2449_;
}
v_resetjp_2449_:
{
lean_object* v___x_2453_; 
if (v_isShared_2451_ == 0)
{
v___x_2453_ = v___x_2450_;
goto v_reusejp_2452_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_a_2448_);
v___x_2453_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2452_;
}
v_reusejp_2452_:
{
return v___x_2453_;
}
}
}
}
}
else
{
lean_dec(v_a_2414_);
v___y_2276_ = v___y_1817_;
v___y_2277_ = v___y_1818_;
v___y_2278_ = v___y_1819_;
v___y_2279_ = v___y_1820_;
goto v___jp_2275_;
}
}
else
{
lean_object* v_a_2457_; lean_object* v___x_2459_; uint8_t v_isShared_2460_; uint8_t v_isSharedCheck_2464_; 
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2457_ = lean_ctor_get(v___x_2413_, 0);
v_isSharedCheck_2464_ = !lean_is_exclusive(v___x_2413_);
if (v_isSharedCheck_2464_ == 0)
{
v___x_2459_ = v___x_2413_;
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
else
{
lean_inc(v_a_2457_);
lean_dec(v___x_2413_);
v___x_2459_ = lean_box(0);
v_isShared_2460_ = v_isSharedCheck_2464_;
goto v_resetjp_2458_;
}
v_resetjp_2458_:
{
lean_object* v___x_2462_; 
if (v_isShared_2460_ == 0)
{
v___x_2462_ = v___x_2459_;
goto v_reusejp_2461_;
}
else
{
lean_object* v_reuseFailAlloc_2463_; 
v_reuseFailAlloc_2463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2463_, 0, v_a_2457_);
v___x_2462_ = v_reuseFailAlloc_2463_;
goto v_reusejp_2461_;
}
v_reusejp_2461_:
{
return v___x_2462_;
}
}
}
}
else
{
lean_dec(v_a_2411_);
v___y_2276_ = v___y_1817_;
v___y_2277_ = v___y_1818_;
v___y_2278_ = v___y_1819_;
v___y_2279_ = v___y_1820_;
goto v___jp_2275_;
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2465_ = lean_ctor_get(v___x_2410_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2410_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2410_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2410_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
v___jp_1961_:
{
uint8_t v_genDiseq_1968_; 
v_genDiseq_1968_ = lean_ctor_get_uint8(v_config_1811_, sizeof(void*)*1 + 2);
if (v_genDiseq_1968_ == 0)
{
lean_dec_ref(v___x_1960_);
v___y_1939_ = v___y_1967_;
v___y_1940_ = v___y_1966_;
v___y_1941_ = v___y_1962_;
v___y_1942_ = v___y_1965_;
v___y_1943_ = v___y_1963_;
v___y_1944_ = v___y_1964_;
v___y_1945_ = v___x_1916_;
goto v___jp_1938_;
}
else
{
uint8_t v___x_1969_; 
v___x_1969_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1960_);
v___y_1939_ = v___y_1967_;
v___y_1940_ = v___y_1966_;
v___y_1941_ = v___y_1962_;
v___y_1942_ = v___y_1965_;
v___y_1943_ = v___y_1963_;
v___y_1944_ = v___y_1964_;
v___y_1945_ = v___x_1969_;
goto v___jp_1938_;
}
}
v___jp_1970_:
{
if (v___y_1978_ == 0)
{
lean_dec_ref(v___y_1971_);
v___y_1962_ = v___y_1973_;
v___y_1963_ = v___y_1975_;
v___y_1964_ = v___y_1976_;
v___y_1965_ = v___y_1977_;
v___y_1966_ = v___y_1974_;
v___y_1967_ = v___y_1972_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_1979_; 
lean_dec_ref(v___x_1960_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v___x_1979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1979_, 0, v___y_1971_);
return v___x_1979_;
}
}
v___jp_1980_:
{
uint8_t v___x_1988_; 
v___x_1988_ = l_Lean_Exception_isInterrupt(v_a_1987_);
if (v___x_1988_ == 0)
{
uint8_t v___x_1989_; 
lean_inc_ref(v_a_1987_);
v___x_1989_ = l_Lean_Exception_isRuntime(v_a_1987_);
v___y_1971_ = v_a_1987_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___y_1983_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1985_;
v___y_1977_ = v___y_1986_;
v___y_1978_ = v___x_1989_;
goto v___jp_1970_;
}
else
{
v___y_1971_ = v_a_1987_;
v___y_1972_ = v___y_1981_;
v___y_1973_ = v___y_1982_;
v___y_1974_ = v___y_1983_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1985_;
v___y_1977_ = v___y_1986_;
v___y_1978_ = v___x_1988_;
goto v___jp_1970_;
}
}
v___jp_1990_:
{
if (lean_obj_tag(v___y_1998_) == 0)
{
lean_object* v_a_1999_; lean_object* v___x_2000_; uint8_t v___x_2001_; 
v_a_1999_ = lean_ctor_get(v___y_1998_, 0);
lean_inc(v_a_1999_);
lean_dec_ref_known(v___y_1998_, 1);
v___x_2000_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2001_ = l_Lean_Expr_isConstOf(v_a_1999_, v___x_2000_);
lean_dec(v_a_1999_);
if (v___x_2001_ == 0)
{
lean_dec_ref(v___y_1991_);
v___y_1962_ = v___y_1993_;
v___y_1963_ = v___y_1995_;
v___y_1964_ = v___y_1996_;
v___y_1965_ = v___y_1997_;
v___y_1966_ = v___y_1994_;
v___y_1967_ = v___y_1992_;
goto v___jp_1961_;
}
else
{
lean_object* v___x_2002_; 
lean_inc_ref(v___y_1991_);
v___x_2002_ = l_Lean_Meta_mkEqRefl(v___y_1991_, v___y_1996_, v___y_1997_, v___y_1994_, v___y_1992_);
if (lean_obj_tag(v___x_2002_) == 0)
{
lean_object* v_a_2003_; lean_object* v___x_2004_; lean_object* v_dummy_2005_; lean_object* v_nargs_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v_a_2003_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2003_);
lean_dec_ref_known(v___x_2002_, 1);
v___x_2004_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2006_ = l_Lean_Expr_getAppNumArgs(v___y_1991_);
lean_inc(v_nargs_2006_);
v___x_2007_ = lean_mk_array(v_nargs_2006_, v_dummy_2005_);
v___x_2008_ = lean_unsigned_to_nat(1u);
v___x_2009_ = lean_nat_sub(v_nargs_2006_, v___x_2008_);
lean_dec(v_nargs_2006_);
v___x_2010_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_1991_, v___x_2007_, v___x_2009_);
v___x_2011_ = lean_array_push(v___x_2010_, v_a_2003_);
v___x_2012_ = l_Lean_mkAppN(v___x_2004_, v___x_2011_);
lean_dec_ref(v___x_2011_);
lean_inc(v_mvarId_1812_);
v___x_2013_ = l_Lean_MVarId_getType(v_mvarId_1812_, v___y_1996_, v___y_1997_, v___y_1994_, v___y_1992_);
if (lean_obj_tag(v___x_2013_) == 0)
{
lean_object* v_a_2014_; lean_object* v___x_2015_; lean_object* v___x_2016_; 
v_a_2014_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2014_);
lean_dec_ref_known(v___x_2013_, 1);
lean_inc(v_val_1843_);
v___x_2015_ = l_Lean_LocalDecl_toExpr(v_val_1843_);
v___x_2016_ = l_Lean_Meta_mkAbsurd(v_a_2014_, v___x_2015_, v___x_2012_, v___y_1996_, v___y_1997_, v___y_1994_, v___y_1992_);
if (lean_obj_tag(v___x_2016_) == 0)
{
lean_object* v_a_2017_; lean_object* v___x_2018_; 
v_a_2017_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2017_);
lean_dec_ref_known(v___x_2016_, 1);
lean_inc(v_mvarId_1812_);
v___x_2018_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1812_, v_a_2017_, v___y_1997_);
if (lean_obj_tag(v___x_2018_) == 0)
{
lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2027_; 
lean_dec_ref(v___x_1960_);
lean_dec(v_val_1843_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_isSharedCheck_2027_ = !lean_is_exclusive(v___x_2018_);
if (v_isSharedCheck_2027_ == 0)
{
lean_object* v_unused_2028_; 
v_unused_2028_ = lean_ctor_get(v___x_2018_, 0);
lean_dec(v_unused_2028_);
v___x_2020_ = v___x_2018_;
v_isShared_2021_ = v_isSharedCheck_2027_;
goto v_resetjp_2019_;
}
else
{
lean_dec(v___x_2018_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2027_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2024_; 
v___x_2022_ = lean_box(v___x_1822_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set_tag(v___x_2020_, 1);
lean_ctor_set(v___x_2020_, 0, v___x_2022_);
v___x_2024_ = v___x_2020_;
goto v_reusejp_2023_;
}
else
{
lean_object* v_reuseFailAlloc_2026_; 
v_reuseFailAlloc_2026_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2026_, 0, v___x_2022_);
v___x_2024_ = v_reuseFailAlloc_2026_;
goto v_reusejp_2023_;
}
v_reusejp_2023_:
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2025_, 0, v___x_2024_);
lean_ctor_set(v___x_2025_, 1, v___x_1847_);
v_a_1829_ = v___x_2025_;
goto v___jp_1828_;
}
}
}
else
{
lean_object* v_a_2029_; 
v_a_2029_ = lean_ctor_get(v___x_2018_, 0);
lean_inc(v_a_2029_);
lean_dec_ref_known(v___x_2018_, 1);
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v___y_1985_ = v___y_1996_;
v___y_1986_ = v___y_1997_;
v_a_1987_ = v_a_2029_;
goto v___jp_1980_;
}
}
else
{
lean_object* v_a_2030_; 
v_a_2030_ = lean_ctor_get(v___x_2016_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2016_, 1);
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v___y_1985_ = v___y_1996_;
v___y_1986_ = v___y_1997_;
v_a_1987_ = v_a_2030_;
goto v___jp_1980_;
}
}
else
{
lean_object* v_a_2031_; 
lean_dec_ref(v___x_2012_);
v_a_2031_ = lean_ctor_get(v___x_2013_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2013_, 1);
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v___y_1985_ = v___y_1996_;
v___y_1986_ = v___y_1997_;
v_a_1987_ = v_a_2031_;
goto v___jp_1980_;
}
}
else
{
lean_object* v_a_2032_; 
lean_dec_ref(v___y_1991_);
v_a_2032_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2002_, 1);
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v___y_1985_ = v___y_1996_;
v___y_1986_ = v___y_1997_;
v_a_1987_ = v_a_2032_;
goto v___jp_1980_;
}
}
}
else
{
lean_object* v_a_2033_; 
lean_dec_ref(v___y_1991_);
v_a_2033_ = lean_ctor_get(v___y_1998_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___y_1998_, 1);
v___y_1981_ = v___y_1992_;
v___y_1982_ = v___y_1993_;
v___y_1983_ = v___y_1994_;
v___y_1984_ = v___y_1995_;
v___y_1985_ = v___y_1996_;
v___y_1986_ = v___y_1997_;
v_a_1987_ = v_a_2033_;
goto v___jp_1980_;
}
}
v___jp_2034_:
{
lean_object* v___x_2041_; 
lean_inc_ref(v___x_1960_);
v___x_2041_ = l_Lean_Meta_mkDecide(v___x_1960_, v___y_2039_, v___y_2040_, v___y_2037_, v___y_2035_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_object* v_a_2042_; lean_object* v___x_2043_; uint8_t v_transparency_2044_; uint8_t v___x_2045_; uint8_t v___x_2046_; 
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2042_);
lean_dec_ref_known(v___x_2041_, 1);
v___x_2043_ = l_Lean_Meta_Context_config(v___y_2039_);
v_transparency_2044_ = lean_ctor_get_uint8(v___x_2043_, 9);
lean_dec_ref(v___x_2043_);
v___x_2045_ = 1;
v___x_2046_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2044_, v___x_2045_);
if (v___x_2046_ == 0)
{
lean_object* v_keyedConfig_2047_; uint8_t v_trackZetaDelta_2048_; lean_object* v_zetaDeltaSet_2049_; lean_object* v_lctx_2050_; lean_object* v_localInstances_2051_; lean_object* v_defEqCtx_x3f_2052_; lean_object* v_synthPendingDepth_2053_; lean_object* v_customCanUnfoldPredicate_x3f_2054_; uint8_t v_univApprox_2055_; uint8_t v_inTypeClassResolution_2056_; uint8_t v_cacheInferType_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; 
v_keyedConfig_2047_ = lean_ctor_get(v___y_2039_, 0);
v_trackZetaDelta_2048_ = lean_ctor_get_uint8(v___y_2039_, sizeof(void*)*7);
v_zetaDeltaSet_2049_ = lean_ctor_get(v___y_2039_, 1);
v_lctx_2050_ = lean_ctor_get(v___y_2039_, 2);
v_localInstances_2051_ = lean_ctor_get(v___y_2039_, 3);
v_defEqCtx_x3f_2052_ = lean_ctor_get(v___y_2039_, 4);
v_synthPendingDepth_2053_ = lean_ctor_get(v___y_2039_, 5);
v_customCanUnfoldPredicate_x3f_2054_ = lean_ctor_get(v___y_2039_, 6);
v_univApprox_2055_ = lean_ctor_get_uint8(v___y_2039_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2056_ = lean_ctor_get_uint8(v___y_2039_, sizeof(void*)*7 + 2);
v_cacheInferType_2057_ = lean_ctor_get_uint8(v___y_2039_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2047_);
v___x_2058_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2045_, v_keyedConfig_2047_);
lean_inc(v_customCanUnfoldPredicate_x3f_2054_);
lean_inc(v_synthPendingDepth_2053_);
lean_inc(v_defEqCtx_x3f_2052_);
lean_inc_ref(v_localInstances_2051_);
lean_inc_ref(v_lctx_2050_);
lean_inc(v_zetaDeltaSet_2049_);
v___x_2059_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2059_, 0, v___x_2058_);
lean_ctor_set(v___x_2059_, 1, v_zetaDeltaSet_2049_);
lean_ctor_set(v___x_2059_, 2, v_lctx_2050_);
lean_ctor_set(v___x_2059_, 3, v_localInstances_2051_);
lean_ctor_set(v___x_2059_, 4, v_defEqCtx_x3f_2052_);
lean_ctor_set(v___x_2059_, 5, v_synthPendingDepth_2053_);
lean_ctor_set(v___x_2059_, 6, v_customCanUnfoldPredicate_x3f_2054_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*7, v_trackZetaDelta_2048_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*7 + 1, v_univApprox_2055_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2056_);
lean_ctor_set_uint8(v___x_2059_, sizeof(void*)*7 + 3, v_cacheInferType_2057_);
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2037_);
lean_inc(v___y_2040_);
lean_inc(v_a_2042_);
v___x_2060_ = lean_whnf(v_a_2042_, v___x_2059_, v___y_2040_, v___y_2037_, v___y_2035_);
v___y_1991_ = v_a_2042_;
v___y_1992_ = v___y_2035_;
v___y_1993_ = v___y_2036_;
v___y_1994_ = v___y_2037_;
v___y_1995_ = v___y_2038_;
v___y_1996_ = v___y_2039_;
v___y_1997_ = v___y_2040_;
v___y_1998_ = v___x_2060_;
goto v___jp_1990_;
}
else
{
lean_object* v___x_2061_; 
lean_inc(v___y_2035_);
lean_inc_ref(v___y_2037_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2039_);
lean_inc(v_a_2042_);
v___x_2061_ = lean_whnf(v_a_2042_, v___y_2039_, v___y_2040_, v___y_2037_, v___y_2035_);
v___y_1991_ = v_a_2042_;
v___y_1992_ = v___y_2035_;
v___y_1993_ = v___y_2036_;
v___y_1994_ = v___y_2037_;
v___y_1995_ = v___y_2038_;
v___y_1996_ = v___y_2039_;
v___y_1997_ = v___y_2040_;
v___y_1998_ = v___x_2061_;
goto v___jp_1990_;
}
}
else
{
lean_object* v_a_2062_; 
v_a_2062_ = lean_ctor_get(v___x_2041_, 0);
lean_inc(v_a_2062_);
lean_dec_ref_known(v___x_2041_, 1);
v___y_1981_ = v___y_2035_;
v___y_1982_ = v___y_2036_;
v___y_1983_ = v___y_2037_;
v___y_1984_ = v___y_2038_;
v___y_1985_ = v___y_2039_;
v___y_1986_ = v___y_2040_;
v_a_1987_ = v_a_2062_;
goto v___jp_1980_;
}
}
v___jp_2063_:
{
if (v___y_2070_ == 0)
{
v___y_1962_ = v___y_2065_;
v___y_1963_ = v___y_2067_;
v___y_1964_ = v___y_2068_;
v___y_1965_ = v___y_2069_;
v___y_1966_ = v___y_2066_;
v___y_1967_ = v___y_2064_;
goto v___jp_1961_;
}
else
{
v___y_2035_ = v___y_2064_;
v___y_2036_ = v___y_2065_;
v___y_2037_ = v___y_2066_;
v___y_2038_ = v___y_2067_;
v___y_2039_ = v___y_2068_;
v___y_2040_ = v___y_2069_;
goto v___jp_2034_;
}
}
v___jp_2071_:
{
if (v___y_2079_ == 0)
{
lean_dec_ref(v___y_2078_);
v___y_2064_ = v___y_2072_;
v___y_2065_ = v___y_2073_;
v___y_2066_ = v___y_2074_;
v___y_2067_ = v___y_2075_;
v___y_2068_ = v___y_2076_;
v___y_2069_ = v___y_2077_;
v___y_2070_ = v___x_1916_;
goto v___jp_2063_;
}
else
{
uint8_t v___x_2080_; 
v___x_2080_ = l_Lean_Expr_hasFVar(v___y_2078_);
lean_dec_ref(v___y_2078_);
if (v___x_2080_ == 0)
{
v___y_2035_ = v___y_2072_;
v___y_2036_ = v___y_2073_;
v___y_2037_ = v___y_2074_;
v___y_2038_ = v___y_2075_;
v___y_2039_ = v___y_2076_;
v___y_2040_ = v___y_2077_;
goto v___jp_2034_;
}
else
{
v___y_2064_ = v___y_2072_;
v___y_2065_ = v___y_2073_;
v___y_2066_ = v___y_2074_;
v___y_2067_ = v___y_2075_;
v___y_2068_ = v___y_2076_;
v___y_2069_ = v___y_2077_;
v___y_2070_ = v___x_1916_;
goto v___jp_2063_;
}
}
}
v___jp_2081_:
{
lean_object* v___x_2089_; 
lean_inc_ref(v___x_1960_);
v___x_2089_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1960_, v___y_2087_);
if (lean_obj_tag(v___x_2089_) == 0)
{
lean_object* v_a_2090_; uint8_t v___x_2091_; 
v_a_2090_ = lean_ctor_get(v___x_2089_, 0);
lean_inc(v_a_2090_);
lean_dec_ref_known(v___x_2089_, 1);
v___x_2091_ = l_Lean_Expr_hasMVar(v_a_2090_);
if (v___x_2091_ == 0)
{
v___y_2072_ = v___y_2082_;
v___y_2073_ = v___y_2083_;
v___y_2074_ = v___y_2084_;
v___y_2075_ = v___y_2085_;
v___y_2076_ = v___y_2086_;
v___y_2077_ = v___y_2087_;
v___y_2078_ = v_a_2090_;
v___y_2079_ = v___y_2088_;
goto v___jp_2071_;
}
else
{
v___y_2072_ = v___y_2082_;
v___y_2073_ = v___y_2083_;
v___y_2074_ = v___y_2084_;
v___y_2075_ = v___y_2085_;
v___y_2076_ = v___y_2086_;
v___y_2077_ = v___y_2087_;
v___y_2078_ = v_a_2090_;
v___y_2079_ = v___x_1916_;
goto v___jp_2071_;
}
}
else
{
lean_object* v_a_2092_; lean_object* v___x_2094_; uint8_t v_isShared_2095_; uint8_t v_isSharedCheck_2099_; 
lean_dec_ref(v___x_1960_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2092_ = lean_ctor_get(v___x_2089_, 0);
v_isSharedCheck_2099_ = !lean_is_exclusive(v___x_2089_);
if (v_isSharedCheck_2099_ == 0)
{
v___x_2094_ = v___x_2089_;
v_isShared_2095_ = v_isSharedCheck_2099_;
goto v_resetjp_2093_;
}
else
{
lean_inc(v_a_2092_);
lean_dec(v___x_2089_);
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
v___jp_2100_:
{
if (v___y_2107_ == 0)
{
v___y_1962_ = v___y_2102_;
v___y_1963_ = v___y_2104_;
v___y_1964_ = v___y_2105_;
v___y_1965_ = v___y_2106_;
v___y_1966_ = v___y_2103_;
v___y_1967_ = v___y_2101_;
goto v___jp_1961_;
}
else
{
v___y_2082_ = v___y_2101_;
v___y_2083_ = v___y_2102_;
v___y_2084_ = v___y_2103_;
v___y_2085_ = v___y_2104_;
v___y_2086_ = v___y_2105_;
v___y_2087_ = v___y_2106_;
v___y_2088_ = v___y_2107_;
goto v___jp_2081_;
}
}
v___jp_2108_:
{
uint8_t v_useDecide_2115_; 
v_useDecide_2115_ = lean_ctor_get_uint8(v_config_1811_, sizeof(void*)*1);
if (v_useDecide_2115_ == 0)
{
v___y_2101_ = v___y_2114_;
v___y_2102_ = v_isHEq_2110_;
v___y_2103_ = v___y_2113_;
v___y_2104_ = v___y_2109_;
v___y_2105_ = v___y_2111_;
v___y_2106_ = v___y_2112_;
v___y_2107_ = v___x_1916_;
goto v___jp_2100_;
}
else
{
uint8_t v___x_2116_; 
v___x_2116_ = l_Lean_Expr_hasFVar(v___x_1960_);
if (v___x_2116_ == 0)
{
v___y_2082_ = v___y_2114_;
v___y_2083_ = v_isHEq_2110_;
v___y_2084_ = v___y_2113_;
v___y_2085_ = v___y_2109_;
v___y_2086_ = v___y_2111_;
v___y_2087_ = v___y_2112_;
v___y_2088_ = v_useDecide_2115_;
goto v___jp_2081_;
}
else
{
v___y_2101_ = v___y_2114_;
v___y_2102_ = v_isHEq_2110_;
v___y_2103_ = v___y_2113_;
v___y_2104_ = v___y_2109_;
v___y_2105_ = v___y_2111_;
v___y_2106_ = v___y_2112_;
v___y_2107_ = v___x_1916_;
goto v___jp_2100_;
}
}
}
v___jp_2117_:
{
lean_object* v___x_2125_; 
v___x_2125_ = l_Lean_Meta_isExprDefEq(v___y_2120_, v___y_2119_, v___y_2124_, v___y_2118_, v___y_2122_, v___y_2121_);
if (lean_obj_tag(v___x_2125_) == 0)
{
lean_object* v_a_2126_; uint8_t v___x_2127_; 
v_a_2126_ = lean_ctor_get(v___x_2125_, 0);
lean_inc(v_a_2126_);
lean_dec_ref_known(v___x_2125_, 1);
v___x_2127_ = lean_unbox(v_a_2126_);
lean_dec(v_a_2126_);
if (v___x_2127_ == 0)
{
v___y_2109_ = v___y_2123_;
v_isHEq_2110_ = v___x_1822_;
v___y_2111_ = v___y_2124_;
v___y_2112_ = v___y_2118_;
v___y_2113_ = v___y_2122_;
v___y_2114_ = v___y_2121_;
goto v___jp_2108_;
}
else
{
lean_object* v___x_2128_; 
lean_dec_ref(v___x_1960_);
lean_dec_ref(v_config_1811_);
lean_inc(v_mvarId_1812_);
v___x_2128_ = l_Lean_MVarId_getType(v_mvarId_1812_, v___y_2124_, v___y_2118_, v___y_2122_, v___y_2121_);
if (lean_obj_tag(v___x_2128_) == 0)
{
lean_object* v_a_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v_a_2129_ = lean_ctor_get(v___x_2128_, 0);
lean_inc(v_a_2129_);
lean_dec_ref_known(v___x_2128_, 1);
v___x_2130_ = l_Lean_LocalDecl_toExpr(v_val_1843_);
v___x_2131_ = l_Lean_Meta_mkEqOfHEq(v___x_2130_, v___x_1822_, v___y_2124_, v___y_2118_, v___y_2122_, v___y_2121_);
if (lean_obj_tag(v___x_2131_) == 0)
{
lean_object* v_a_2132_; lean_object* v___x_2133_; 
v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
lean_inc(v_a_2132_);
lean_dec_ref_known(v___x_2131_, 1);
v___x_2133_ = l_Lean_Meta_mkNoConfusion(v_a_2129_, v_a_2132_, v___y_2124_, v___y_2118_, v___y_2122_, v___y_2121_);
if (lean_obj_tag(v___x_2133_) == 0)
{
lean_object* v_a_2134_; lean_object* v___x_2135_; 
v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
lean_inc(v_a_2134_);
lean_dec_ref_known(v___x_2133_, 1);
v___x_2135_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1812_, v_a_2134_, v___y_2118_);
if (lean_obj_tag(v___x_2135_) == 0)
{
lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; 
lean_dec_ref_known(v___x_2135_, 1);
v___x_2136_ = lean_box(v___x_1822_);
v___x_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2137_, 0, v___x_2136_);
v___x_2138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
lean_ctor_set(v___x_2138_, 1, v___x_1847_);
v_a_1829_ = v___x_2138_;
goto v___jp_1828_;
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
v_a_2139_ = lean_ctor_get(v___x_2135_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2135_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2135_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2135_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
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
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
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
lean_object* v_a_2155_; lean_object* v___x_2157_; uint8_t v_isShared_2158_; uint8_t v_isSharedCheck_2162_; 
lean_dec(v_a_2129_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_2155_ = lean_ctor_get(v___x_2131_, 0);
v_isSharedCheck_2162_ = !lean_is_exclusive(v___x_2131_);
if (v_isSharedCheck_2162_ == 0)
{
v___x_2157_ = v___x_2131_;
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
else
{
lean_inc(v_a_2155_);
lean_dec(v___x_2131_);
v___x_2157_ = lean_box(0);
v_isShared_2158_ = v_isSharedCheck_2162_;
goto v_resetjp_2156_;
}
v_resetjp_2156_:
{
lean_object* v___x_2160_; 
if (v_isShared_2158_ == 0)
{
v___x_2160_ = v___x_2157_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v_a_2155_);
v___x_2160_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
return v___x_2160_;
}
}
}
}
else
{
lean_object* v_a_2163_; lean_object* v___x_2165_; uint8_t v_isShared_2166_; uint8_t v_isSharedCheck_2170_; 
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_2163_ = lean_ctor_get(v___x_2128_, 0);
v_isSharedCheck_2170_ = !lean_is_exclusive(v___x_2128_);
if (v_isSharedCheck_2170_ == 0)
{
v___x_2165_ = v___x_2128_;
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
else
{
lean_inc(v_a_2163_);
lean_dec(v___x_2128_);
v___x_2165_ = lean_box(0);
v_isShared_2166_ = v_isSharedCheck_2170_;
goto v_resetjp_2164_;
}
v_resetjp_2164_:
{
lean_object* v___x_2168_; 
if (v_isShared_2166_ == 0)
{
v___x_2168_ = v___x_2165_;
goto v_reusejp_2167_;
}
else
{
lean_object* v_reuseFailAlloc_2169_; 
v_reuseFailAlloc_2169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2169_, 0, v_a_2163_);
v___x_2168_ = v_reuseFailAlloc_2169_;
goto v_reusejp_2167_;
}
v_reusejp_2167_:
{
return v___x_2168_;
}
}
}
}
}
else
{
lean_object* v_a_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2178_; 
lean_dec_ref(v___x_1960_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2171_ = lean_ctor_get(v___x_2125_, 0);
v_isSharedCheck_2178_ = !lean_is_exclusive(v___x_2125_);
if (v_isSharedCheck_2178_ == 0)
{
v___x_2173_ = v___x_2125_;
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_a_2171_);
lean_dec(v___x_2125_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2178_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v___x_2176_; 
if (v_isShared_2174_ == 0)
{
v___x_2176_ = v___x_2173_;
goto v_reusejp_2175_;
}
else
{
lean_object* v_reuseFailAlloc_2177_; 
v_reuseFailAlloc_2177_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2177_, 0, v_a_2171_);
v___x_2176_ = v_reuseFailAlloc_2177_;
goto v_reusejp_2175_;
}
v_reusejp_2175_:
{
return v___x_2176_;
}
}
}
}
v___jp_2179_:
{
lean_object* v___x_2185_; 
lean_inc_ref(v___x_1960_);
v___x_2185_ = l_Lean_Meta_matchHEq_x3f(v___x_1960_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
if (lean_obj_tag(v___x_2185_) == 0)
{
lean_object* v_a_2186_; 
v_a_2186_ = lean_ctor_get(v___x_2185_, 0);
lean_inc(v_a_2186_);
lean_dec_ref_known(v___x_2185_, 1);
if (lean_obj_tag(v_a_2186_) == 1)
{
lean_object* v_val_2187_; lean_object* v_snd_2188_; lean_object* v_snd_2189_; lean_object* v_fst_2190_; lean_object* v_fst_2191_; lean_object* v_fst_2192_; lean_object* v_snd_2193_; lean_object* v___x_2194_; 
v_val_2187_ = lean_ctor_get(v_a_2186_, 0);
lean_inc(v_val_2187_);
lean_dec_ref_known(v_a_2186_, 1);
v_snd_2188_ = lean_ctor_get(v_val_2187_, 1);
lean_inc(v_snd_2188_);
v_snd_2189_ = lean_ctor_get(v_snd_2188_, 1);
lean_inc(v_snd_2189_);
v_fst_2190_ = lean_ctor_get(v_val_2187_, 0);
lean_inc(v_fst_2190_);
lean_dec(v_val_2187_);
v_fst_2191_ = lean_ctor_get(v_snd_2188_, 0);
lean_inc(v_fst_2191_);
lean_dec(v_snd_2188_);
v_fst_2192_ = lean_ctor_get(v_snd_2189_, 0);
lean_inc(v_fst_2192_);
v_snd_2193_ = lean_ctor_get(v_snd_2189_, 1);
lean_inc(v_snd_2193_);
lean_dec(v_snd_2189_);
v___x_2194_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2191_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
if (lean_obj_tag(v___x_2194_) == 0)
{
lean_object* v_a_2195_; 
v_a_2195_ = lean_ctor_get(v___x_2194_, 0);
lean_inc(v_a_2195_);
lean_dec_ref_known(v___x_2194_, 1);
if (lean_obj_tag(v_a_2195_) == 1)
{
lean_object* v_val_2196_; lean_object* v___x_2197_; 
v_val_2196_ = lean_ctor_get(v_a_2195_, 0);
lean_inc(v_val_2196_);
lean_dec_ref_known(v_a_2195_, 1);
v___x_2197_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2193_, v___y_2181_, v___y_2182_, v___y_2183_, v___y_2184_);
if (lean_obj_tag(v___x_2197_) == 0)
{
lean_object* v_a_2198_; 
v_a_2198_ = lean_ctor_get(v___x_2197_, 0);
lean_inc(v_a_2198_);
lean_dec_ref_known(v___x_2197_, 1);
if (lean_obj_tag(v_a_2198_) == 1)
{
lean_object* v_toConstantVal_2199_; lean_object* v_val_2200_; lean_object* v_toConstantVal_2201_; lean_object* v_name_2202_; lean_object* v_name_2203_; uint8_t v___x_2204_; 
v_toConstantVal_2199_ = lean_ctor_get(v_val_2196_, 0);
lean_inc_ref(v_toConstantVal_2199_);
lean_dec(v_val_2196_);
v_val_2200_ = lean_ctor_get(v_a_2198_, 0);
lean_inc(v_val_2200_);
lean_dec_ref_known(v_a_2198_, 1);
v_toConstantVal_2201_ = lean_ctor_get(v_val_2200_, 0);
lean_inc_ref(v_toConstantVal_2201_);
lean_dec(v_val_2200_);
v_name_2202_ = lean_ctor_get(v_toConstantVal_2199_, 0);
lean_inc(v_name_2202_);
lean_dec_ref(v_toConstantVal_2199_);
v_name_2203_ = lean_ctor_get(v_toConstantVal_2201_, 0);
lean_inc(v_name_2203_);
lean_dec_ref(v_toConstantVal_2201_);
v___x_2204_ = lean_name_eq(v_name_2202_, v_name_2203_);
lean_dec(v_name_2203_);
lean_dec(v_name_2202_);
if (v___x_2204_ == 0)
{
v___y_2118_ = v___y_2182_;
v___y_2119_ = v_fst_2192_;
v___y_2120_ = v_fst_2190_;
v___y_2121_ = v___y_2184_;
v___y_2122_ = v___y_2183_;
v___y_2123_ = v_isEq_2180_;
v___y_2124_ = v___y_2181_;
goto v___jp_2117_;
}
else
{
if (v___x_1916_ == 0)
{
lean_dec(v_fst_2192_);
lean_dec(v_fst_2190_);
v___y_2109_ = v_isEq_2180_;
v_isHEq_2110_ = v___x_1822_;
v___y_2111_ = v___y_2181_;
v___y_2112_ = v___y_2182_;
v___y_2113_ = v___y_2183_;
v___y_2114_ = v___y_2184_;
goto v___jp_2108_;
}
else
{
v___y_2118_ = v___y_2182_;
v___y_2119_ = v_fst_2192_;
v___y_2120_ = v_fst_2190_;
v___y_2121_ = v___y_2184_;
v___y_2122_ = v___y_2183_;
v___y_2123_ = v_isEq_2180_;
v___y_2124_ = v___y_2181_;
goto v___jp_2117_;
}
}
}
else
{
lean_dec(v_a_2198_);
lean_dec(v_val_2196_);
lean_dec(v_fst_2192_);
lean_dec(v_fst_2190_);
v___y_2109_ = v_isEq_2180_;
v_isHEq_2110_ = v___x_1822_;
v___y_2111_ = v___y_2181_;
v___y_2112_ = v___y_2182_;
v___y_2113_ = v___y_2183_;
v___y_2114_ = v___y_2184_;
goto v___jp_2108_;
}
}
else
{
lean_object* v_a_2205_; lean_object* v___x_2207_; uint8_t v_isShared_2208_; uint8_t v_isSharedCheck_2212_; 
lean_dec(v_val_2196_);
lean_dec(v_fst_2192_);
lean_dec(v_fst_2190_);
lean_dec_ref(v___x_1960_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2205_ = lean_ctor_get(v___x_2197_, 0);
v_isSharedCheck_2212_ = !lean_is_exclusive(v___x_2197_);
if (v_isSharedCheck_2212_ == 0)
{
v___x_2207_ = v___x_2197_;
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
else
{
lean_inc(v_a_2205_);
lean_dec(v___x_2197_);
v___x_2207_ = lean_box(0);
v_isShared_2208_ = v_isSharedCheck_2212_;
goto v_resetjp_2206_;
}
v_resetjp_2206_:
{
lean_object* v___x_2210_; 
if (v_isShared_2208_ == 0)
{
v___x_2210_ = v___x_2207_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_a_2205_);
v___x_2210_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
return v___x_2210_;
}
}
}
}
else
{
lean_dec(v_a_2195_);
lean_dec(v_snd_2193_);
lean_dec(v_fst_2192_);
lean_dec(v_fst_2190_);
v___y_2109_ = v_isEq_2180_;
v_isHEq_2110_ = v___x_1822_;
v___y_2111_ = v___y_2181_;
v___y_2112_ = v___y_2182_;
v___y_2113_ = v___y_2183_;
v___y_2114_ = v___y_2184_;
goto v___jp_2108_;
}
}
else
{
lean_object* v_a_2213_; lean_object* v___x_2215_; uint8_t v_isShared_2216_; uint8_t v_isSharedCheck_2220_; 
lean_dec(v_snd_2193_);
lean_dec(v_fst_2192_);
lean_dec(v_fst_2190_);
lean_dec_ref(v___x_1960_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2213_ = lean_ctor_get(v___x_2194_, 0);
v_isSharedCheck_2220_ = !lean_is_exclusive(v___x_2194_);
if (v_isSharedCheck_2220_ == 0)
{
v___x_2215_ = v___x_2194_;
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
else
{
lean_inc(v_a_2213_);
lean_dec(v___x_2194_);
v___x_2215_ = lean_box(0);
v_isShared_2216_ = v_isSharedCheck_2220_;
goto v_resetjp_2214_;
}
v_resetjp_2214_:
{
lean_object* v___x_2218_; 
if (v_isShared_2216_ == 0)
{
v___x_2218_ = v___x_2215_;
goto v_reusejp_2217_;
}
else
{
lean_object* v_reuseFailAlloc_2219_; 
v_reuseFailAlloc_2219_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_a_2213_);
v___x_2218_ = v_reuseFailAlloc_2219_;
goto v_reusejp_2217_;
}
v_reusejp_2217_:
{
return v___x_2218_;
}
}
}
}
else
{
lean_dec(v_a_2186_);
v___y_2109_ = v_isEq_2180_;
v_isHEq_2110_ = v___x_1916_;
v___y_2111_ = v___y_2181_;
v___y_2112_ = v___y_2182_;
v___y_2113_ = v___y_2183_;
v___y_2114_ = v___y_2184_;
goto v___jp_2108_;
}
}
else
{
lean_object* v_a_2221_; lean_object* v___x_2223_; uint8_t v_isShared_2224_; uint8_t v_isSharedCheck_2228_; 
lean_dec_ref(v___x_1960_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2221_ = lean_ctor_get(v___x_2185_, 0);
v_isSharedCheck_2228_ = !lean_is_exclusive(v___x_2185_);
if (v_isSharedCheck_2228_ == 0)
{
v___x_2223_ = v___x_2185_;
v_isShared_2224_ = v_isSharedCheck_2228_;
goto v_resetjp_2222_;
}
else
{
lean_inc(v_a_2221_);
lean_dec(v___x_2185_);
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
v___jp_2229_:
{
lean_object* v___x_2234_; 
lean_inc_ref(v___x_1960_);
v___x_2234_ = l_Lean_Meta_matchEq_x3f(v___x_1960_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
if (lean_obj_tag(v_a_2235_) == 1)
{
lean_object* v_val_2236_; lean_object* v_snd_2237_; lean_object* v_fst_2238_; lean_object* v_snd_2239_; lean_object* v___x_2240_; 
v_val_2236_ = lean_ctor_get(v_a_2235_, 0);
lean_inc(v_val_2236_);
lean_dec_ref_known(v_a_2235_, 1);
v_snd_2237_ = lean_ctor_get(v_val_2236_, 1);
lean_inc(v_snd_2237_);
lean_dec(v_val_2236_);
v_fst_2238_ = lean_ctor_get(v_snd_2237_, 0);
lean_inc(v_fst_2238_);
v_snd_2239_ = lean_ctor_get(v_snd_2237_, 1);
lean_inc(v_snd_2239_);
lean_dec(v_snd_2237_);
v___x_2240_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2238_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
if (lean_obj_tag(v_a_2241_) == 1)
{
lean_object* v_val_2242_; lean_object* v___x_2243_; 
v_val_2242_ = lean_ctor_get(v_a_2241_, 0);
lean_inc(v_val_2242_);
lean_dec_ref_known(v_a_2241_, 1);
v___x_2243_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2239_, v___y_2230_, v___y_2231_, v___y_2232_, v___y_2233_);
if (lean_obj_tag(v___x_2243_) == 0)
{
lean_object* v_a_2244_; 
v_a_2244_ = lean_ctor_get(v___x_2243_, 0);
lean_inc(v_a_2244_);
lean_dec_ref_known(v___x_2243_, 1);
if (lean_obj_tag(v_a_2244_) == 1)
{
lean_object* v_toConstantVal_2245_; lean_object* v_val_2246_; lean_object* v_toConstantVal_2247_; lean_object* v_name_2248_; lean_object* v_name_2249_; uint8_t v___x_2250_; 
v_toConstantVal_2245_ = lean_ctor_get(v_val_2242_, 0);
lean_inc_ref(v_toConstantVal_2245_);
lean_dec(v_val_2242_);
v_val_2246_ = lean_ctor_get(v_a_2244_, 0);
lean_inc(v_val_2246_);
lean_dec_ref_known(v_a_2244_, 1);
v_toConstantVal_2247_ = lean_ctor_get(v_val_2246_, 0);
lean_inc_ref(v_toConstantVal_2247_);
lean_dec(v_val_2246_);
v_name_2248_ = lean_ctor_get(v_toConstantVal_2245_, 0);
lean_inc(v_name_2248_);
lean_dec_ref(v_toConstantVal_2245_);
v_name_2249_ = lean_ctor_get(v_toConstantVal_2247_, 0);
lean_inc(v_name_2249_);
lean_dec_ref(v_toConstantVal_2247_);
v___x_2250_ = lean_name_eq(v_name_2248_, v_name_2249_);
lean_dec(v_name_2249_);
lean_dec(v_name_2248_);
if (v___x_2250_ == 0)
{
lean_dec_ref(v___x_1960_);
lean_dec_ref(v_config_1811_);
v___y_1849_ = v___y_2231_;
v___y_1850_ = v___y_2232_;
v___y_1851_ = v___y_2233_;
v___y_1852_ = v___y_2230_;
goto v___jp_1848_;
}
else
{
if (v___x_1916_ == 0)
{
lean_del_object(v___x_1845_);
v_isEq_2180_ = v___x_1822_;
v___y_2181_ = v___y_2230_;
v___y_2182_ = v___y_2231_;
v___y_2183_ = v___y_2232_;
v___y_2184_ = v___y_2233_;
goto v___jp_2179_;
}
else
{
lean_dec_ref(v___x_1960_);
lean_dec_ref(v_config_1811_);
v___y_1849_ = v___y_2231_;
v___y_1850_ = v___y_2232_;
v___y_1851_ = v___y_2233_;
v___y_1852_ = v___y_2230_;
goto v___jp_1848_;
}
}
}
else
{
lean_dec(v_a_2244_);
lean_dec(v_val_2242_);
lean_del_object(v___x_1845_);
v_isEq_2180_ = v___x_1822_;
v___y_2181_ = v___y_2230_;
v___y_2182_ = v___y_2231_;
v___y_2183_ = v___y_2232_;
v___y_2184_ = v___y_2233_;
goto v___jp_2179_;
}
}
else
{
lean_object* v_a_2251_; lean_object* v___x_2253_; uint8_t v_isShared_2254_; uint8_t v_isSharedCheck_2258_; 
lean_dec(v_val_2242_);
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2251_ = lean_ctor_get(v___x_2243_, 0);
v_isSharedCheck_2258_ = !lean_is_exclusive(v___x_2243_);
if (v_isSharedCheck_2258_ == 0)
{
v___x_2253_ = v___x_2243_;
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
else
{
lean_inc(v_a_2251_);
lean_dec(v___x_2243_);
v___x_2253_ = lean_box(0);
v_isShared_2254_ = v_isSharedCheck_2258_;
goto v_resetjp_2252_;
}
v_resetjp_2252_:
{
lean_object* v___x_2256_; 
if (v_isShared_2254_ == 0)
{
v___x_2256_ = v___x_2253_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2257_; 
v_reuseFailAlloc_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2257_, 0, v_a_2251_);
v___x_2256_ = v_reuseFailAlloc_2257_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
return v___x_2256_;
}
}
}
}
else
{
lean_dec(v_a_2241_);
lean_dec(v_snd_2239_);
lean_del_object(v___x_1845_);
v_isEq_2180_ = v___x_1822_;
v___y_2181_ = v___y_2230_;
v___y_2182_ = v___y_2231_;
v___y_2183_ = v___y_2232_;
v___y_2184_ = v___y_2233_;
goto v___jp_2179_;
}
}
else
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2266_; 
lean_dec(v_snd_2239_);
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2259_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2261_ = v___x_2240_;
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2240_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2266_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v___x_2264_; 
if (v_isShared_2262_ == 0)
{
v___x_2264_ = v___x_2261_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_a_2259_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_dec(v_a_2235_);
lean_del_object(v___x_1845_);
v_isEq_2180_ = v___x_1916_;
v___y_2181_ = v___y_2230_;
v___y_2182_ = v___y_2231_;
v___y_2183_ = v___y_2232_;
v___y_2184_ = v___y_2233_;
goto v___jp_2179_;
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2267_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2234_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2234_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
v___jp_2275_:
{
lean_object* v___x_2280_; 
lean_inc_ref(v___x_1960_);
v___x_2280_ = l_Lean_refutableHasNotBit_x3f(v___x_1960_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2280_) == 0)
{
lean_object* v_a_2281_; 
v_a_2281_ = lean_ctor_get(v___x_2280_, 0);
lean_inc(v_a_2281_);
lean_dec_ref_known(v___x_2280_, 1);
if (lean_obj_tag(v_a_2281_) == 1)
{
lean_object* v_val_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2321_; 
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec_ref(v_config_1811_);
v_val_2282_ = lean_ctor_get(v_a_2281_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v_a_2281_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2284_ = v_a_2281_;
v_isShared_2285_ = v_isSharedCheck_2321_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_val_2282_);
lean_dec(v_a_2281_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2321_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2286_; 
lean_inc(v_mvarId_1812_);
v___x_2286_ = l_Lean_MVarId_getType(v_mvarId_1812_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2286_) == 0)
{
lean_object* v_a_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v_a_2287_ = lean_ctor_get(v___x_2286_, 0);
lean_inc(v_a_2287_);
lean_dec_ref_known(v___x_2286_, 1);
v___x_2288_ = l_Lean_LocalDecl_toExpr(v_val_1843_);
v___x_2289_ = l_Lean_Meta_mkAbsurd(v_a_2287_, v_val_2282_, v___x_2288_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2289_) == 0)
{
lean_object* v_a_2290_; lean_object* v___x_2291_; 
v_a_2290_ = lean_ctor_get(v___x_2289_, 0);
lean_inc(v_a_2290_);
lean_dec_ref_known(v___x_2289_, 1);
v___x_2291_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1812_, v_a_2290_, v___y_2277_);
if (lean_obj_tag(v___x_2291_) == 0)
{
lean_object* v___x_2292_; lean_object* v___x_2294_; 
lean_dec_ref_known(v___x_2291_, 1);
v___x_2292_ = lean_box(v___x_1822_);
if (v_isShared_2285_ == 0)
{
lean_ctor_set(v___x_2284_, 0, v___x_2292_);
v___x_2294_ = v___x_2284_;
goto v_reusejp_2293_;
}
else
{
lean_object* v_reuseFailAlloc_2296_; 
v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2292_);
v___x_2294_ = v_reuseFailAlloc_2296_;
goto v_reusejp_2293_;
}
v_reusejp_2293_:
{
lean_object* v___x_2295_; 
v___x_2295_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2295_, 0, v___x_2294_);
lean_ctor_set(v___x_2295_, 1, v___x_1847_);
v_a_1829_ = v___x_2295_;
goto v___jp_1828_;
}
}
else
{
lean_object* v_a_2297_; lean_object* v___x_2299_; uint8_t v_isShared_2300_; uint8_t v_isSharedCheck_2304_; 
lean_del_object(v___x_2284_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
v_a_2297_ = lean_ctor_get(v___x_2291_, 0);
v_isSharedCheck_2304_ = !lean_is_exclusive(v___x_2291_);
if (v_isSharedCheck_2304_ == 0)
{
v___x_2299_ = v___x_2291_;
v_isShared_2300_ = v_isSharedCheck_2304_;
goto v_resetjp_2298_;
}
else
{
lean_inc(v_a_2297_);
lean_dec(v___x_2291_);
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
lean_object* v_a_2305_; lean_object* v___x_2307_; uint8_t v_isShared_2308_; uint8_t v_isSharedCheck_2312_; 
lean_del_object(v___x_2284_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_2305_ = lean_ctor_get(v___x_2289_, 0);
v_isSharedCheck_2312_ = !lean_is_exclusive(v___x_2289_);
if (v_isSharedCheck_2312_ == 0)
{
v___x_2307_ = v___x_2289_;
v_isShared_2308_ = v_isSharedCheck_2312_;
goto v_resetjp_2306_;
}
else
{
lean_inc(v_a_2305_);
lean_dec(v___x_2289_);
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
lean_object* v_a_2313_; lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2320_; 
lean_del_object(v___x_2284_);
lean_dec(v_val_2282_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_2313_ = lean_ctor_get(v___x_2286_, 0);
v_isSharedCheck_2320_ = !lean_is_exclusive(v___x_2286_);
if (v_isSharedCheck_2320_ == 0)
{
v___x_2315_ = v___x_2286_;
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
else
{
lean_inc(v_a_2313_);
lean_dec(v___x_2286_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2320_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2318_; 
if (v_isShared_2316_ == 0)
{
v___x_2318_ = v___x_2315_;
goto v_reusejp_2317_;
}
else
{
lean_object* v_reuseFailAlloc_2319_; 
v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2313_);
v___x_2318_ = v_reuseFailAlloc_2319_;
goto v_reusejp_2317_;
}
v_reusejp_2317_:
{
return v___x_2318_;
}
}
}
}
}
else
{
lean_object* v___x_2322_; 
lean_dec(v_a_2281_);
lean_inc_ref(v___x_1960_);
v___x_2322_ = l_Lean_Meta_matchNe_x3f(v___x_1960_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2322_) == 0)
{
lean_object* v_a_2323_; 
v_a_2323_ = lean_ctor_get(v___x_2322_, 0);
lean_inc(v_a_2323_);
lean_dec_ref_known(v___x_2322_, 1);
if (lean_obj_tag(v_a_2323_) == 1)
{
lean_object* v_val_2324_; lean_object* v___x_2326_; uint8_t v_isShared_2327_; uint8_t v_isSharedCheck_2393_; 
v_val_2324_ = lean_ctor_get(v_a_2323_, 0);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_a_2323_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2326_ = v_a_2323_;
v_isShared_2327_ = v_isSharedCheck_2393_;
goto v_resetjp_2325_;
}
else
{
lean_inc(v_val_2324_);
lean_dec(v_a_2323_);
v___x_2326_ = lean_box(0);
v_isShared_2327_ = v_isSharedCheck_2393_;
goto v_resetjp_2325_;
}
v_resetjp_2325_:
{
lean_object* v_snd_2328_; lean_object* v_fst_2329_; lean_object* v_snd_2330_; lean_object* v___x_2332_; uint8_t v_isShared_2333_; uint8_t v_isSharedCheck_2392_; 
v_snd_2328_ = lean_ctor_get(v_val_2324_, 1);
lean_inc(v_snd_2328_);
lean_dec(v_val_2324_);
v_fst_2329_ = lean_ctor_get(v_snd_2328_, 0);
v_snd_2330_ = lean_ctor_get(v_snd_2328_, 1);
v_isSharedCheck_2392_ = !lean_is_exclusive(v_snd_2328_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2332_ = v_snd_2328_;
v_isShared_2333_ = v_isSharedCheck_2392_;
goto v_resetjp_2331_;
}
else
{
lean_inc(v_snd_2330_);
lean_inc(v_fst_2329_);
lean_dec(v_snd_2328_);
v___x_2332_ = lean_box(0);
v_isShared_2333_ = v_isSharedCheck_2392_;
goto v_resetjp_2331_;
}
v_resetjp_2331_:
{
lean_object* v___x_2334_; 
lean_inc(v_fst_2329_);
v___x_2334_ = l_Lean_Meta_isExprDefEq(v_fst_2329_, v_snd_2330_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2334_) == 0)
{
lean_object* v_a_2335_; uint8_t v___x_2336_; 
v_a_2335_ = lean_ctor_get(v___x_2334_, 0);
lean_inc(v_a_2335_);
lean_dec_ref_known(v___x_2334_, 1);
v___x_2336_ = lean_unbox(v_a_2335_);
lean_dec(v_a_2335_);
if (v___x_2336_ == 0)
{
lean_del_object(v___x_2332_);
lean_dec(v_fst_2329_);
lean_del_object(v___x_2326_);
v___y_2230_ = v___y_2276_;
v___y_2231_ = v___y_2277_;
v___y_2232_ = v___y_2278_;
v___y_2233_ = v___y_2279_;
goto v___jp_2229_;
}
else
{
lean_object* v___x_2337_; 
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec_ref(v_config_1811_);
lean_inc(v_mvarId_1812_);
v___x_2337_ = l_Lean_MVarId_getType(v_mvarId_1812_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2337_) == 0)
{
lean_object* v_a_2338_; lean_object* v___x_2339_; 
v_a_2338_ = lean_ctor_get(v___x_2337_, 0);
lean_inc(v_a_2338_);
lean_dec_ref_known(v___x_2337_, 1);
v___x_2339_ = l_Lean_Meta_mkEqRefl(v_fst_2329_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2339_) == 0)
{
lean_object* v_a_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v_a_2340_ = lean_ctor_get(v___x_2339_, 0);
lean_inc(v_a_2340_);
lean_dec_ref_known(v___x_2339_, 1);
v___x_2341_ = l_Lean_LocalDecl_toExpr(v_val_1843_);
v___x_2342_ = l_Lean_Meta_mkAbsurd(v_a_2338_, v_a_2340_, v___x_2341_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_);
if (lean_obj_tag(v___x_2342_) == 0)
{
lean_object* v_a_2343_; lean_object* v___x_2344_; 
v_a_2343_ = lean_ctor_get(v___x_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___x_2342_, 1);
v___x_2344_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1812_, v_a_2343_, v___y_2277_);
if (lean_obj_tag(v___x_2344_) == 0)
{
lean_object* v___x_2345_; lean_object* v___x_2347_; 
lean_dec_ref_known(v___x_2344_, 1);
v___x_2345_ = lean_box(v___x_1822_);
if (v_isShared_2327_ == 0)
{
lean_ctor_set(v___x_2326_, 0, v___x_2345_);
v___x_2347_ = v___x_2326_;
goto v_reusejp_2346_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2345_);
v___x_2347_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2346_;
}
v_reusejp_2346_:
{
lean_object* v___x_2349_; 
if (v_isShared_2333_ == 0)
{
lean_ctor_set(v___x_2332_, 1, v___x_1847_);
lean_ctor_set(v___x_2332_, 0, v___x_2347_);
v___x_2349_ = v___x_2332_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v___x_2347_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v___x_1847_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
v_a_1829_ = v___x_2349_;
goto v___jp_1828_;
}
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_del_object(v___x_2332_);
lean_del_object(v___x_2326_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
v_a_2352_ = lean_ctor_get(v___x_2344_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___x_2344_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___x_2344_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___x_2344_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_del_object(v___x_2332_);
lean_del_object(v___x_2326_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_2360_ = lean_ctor_get(v___x_2342_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2342_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2342_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2342_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v_a_2338_);
lean_del_object(v___x_2332_);
lean_del_object(v___x_2326_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_2368_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2339_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2339_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_del_object(v___x_2332_);
lean_dec(v_fst_2329_);
lean_del_object(v___x_2326_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_2376_ = lean_ctor_get(v___x_2337_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2337_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2337_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2337_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
else
{
lean_object* v_a_2384_; lean_object* v___x_2386_; uint8_t v_isShared_2387_; uint8_t v_isSharedCheck_2391_; 
lean_del_object(v___x_2332_);
lean_dec(v_fst_2329_);
lean_del_object(v___x_2326_);
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2384_ = lean_ctor_get(v___x_2334_, 0);
v_isSharedCheck_2391_ = !lean_is_exclusive(v___x_2334_);
if (v_isSharedCheck_2391_ == 0)
{
v___x_2386_ = v___x_2334_;
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
else
{
lean_inc(v_a_2384_);
lean_dec(v___x_2334_);
v___x_2386_ = lean_box(0);
v_isShared_2387_ = v_isSharedCheck_2391_;
goto v_resetjp_2385_;
}
v_resetjp_2385_:
{
lean_object* v___x_2389_; 
if (v_isShared_2387_ == 0)
{
v___x_2389_ = v___x_2386_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2390_; 
v_reuseFailAlloc_2390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2390_, 0, v_a_2384_);
v___x_2389_ = v_reuseFailAlloc_2390_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
return v___x_2389_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2323_);
v___y_2230_ = v___y_2276_;
v___y_2231_ = v___y_2277_;
v___y_2232_ = v___y_2278_;
v___y_2233_ = v___y_2279_;
goto v___jp_2229_;
}
}
else
{
lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2401_; 
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2394_ = lean_ctor_get(v___x_2322_, 0);
v_isSharedCheck_2401_ = !lean_is_exclusive(v___x_2322_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2396_ = v___x_2322_;
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_dec(v___x_2322_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2401_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
lean_object* v___x_2399_; 
if (v_isShared_2397_ == 0)
{
v___x_2399_ = v___x_2396_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_a_2394_);
v___x_2399_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
return v___x_2399_;
}
}
}
}
}
else
{
lean_object* v_a_2402_; lean_object* v___x_2404_; uint8_t v_isShared_2405_; uint8_t v_isSharedCheck_2409_; 
lean_dec_ref(v___x_1960_);
lean_del_object(v___x_1845_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_2402_ = lean_ctor_get(v___x_2280_, 0);
v_isSharedCheck_2409_ = !lean_is_exclusive(v___x_2280_);
if (v_isSharedCheck_2409_ == 0)
{
v___x_2404_ = v___x_2280_;
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
else
{
lean_inc(v_a_2402_);
lean_dec(v___x_2280_);
v___x_2404_ = lean_box(0);
v_isShared_2405_ = v_isSharedCheck_2409_;
goto v_resetjp_2403_;
}
v_resetjp_2403_:
{
lean_object* v___x_2407_; 
if (v_isShared_2405_ == 0)
{
v___x_2407_ = v___x_2404_;
goto v_reusejp_2406_;
}
else
{
lean_object* v_reuseFailAlloc_2408_; 
v_reuseFailAlloc_2408_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_a_2402_);
v___x_2407_ = v_reuseFailAlloc_2408_;
goto v_reusejp_2406_;
}
v_reusejp_2406_:
{
return v___x_2407_;
}
}
}
}
}
else
{
lean_del_object(v___x_1845_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
v_a_1837_ = v___x_1888_;
goto v___jp_1836_;
}
v___jp_1848_:
{
lean_object* v___x_1853_; 
lean_inc(v_mvarId_1812_);
v___x_1853_ = l_Lean_MVarId_getType(v_mvarId_1812_, v___y_1852_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1853_) == 0)
{
lean_object* v_a_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; 
v_a_1854_ = lean_ctor_get(v___x_1853_, 0);
lean_inc(v_a_1854_);
lean_dec_ref_known(v___x_1853_, 1);
v___x_1855_ = l_Lean_LocalDecl_toExpr(v_val_1843_);
v___x_1856_ = l_Lean_Meta_mkNoConfusion(v_a_1854_, v___x_1855_, v___y_1852_, v___y_1849_, v___y_1850_, v___y_1851_);
if (lean_obj_tag(v___x_1856_) == 0)
{
lean_object* v_a_1857_; lean_object* v___x_1858_; 
v_a_1857_ = lean_ctor_get(v___x_1856_, 0);
lean_inc(v_a_1857_);
lean_dec_ref_known(v___x_1856_, 1);
v___x_1858_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1812_, v_a_1857_, v___y_1849_);
if (lean_obj_tag(v___x_1858_) == 0)
{
lean_object* v___x_1859_; lean_object* v___x_1861_; 
lean_dec_ref_known(v___x_1858_, 1);
v___x_1859_ = lean_box(v___x_1822_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 0, v___x_1859_);
v___x_1861_ = v___x_1845_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
lean_object* v___x_1862_; 
v___x_1862_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1862_, 0, v___x_1861_);
lean_ctor_set(v___x_1862_, 1, v___x_1847_);
v_a_1829_ = v___x_1862_;
goto v___jp_1828_;
}
}
else
{
lean_object* v_a_1864_; lean_object* v___x_1866_; uint8_t v_isShared_1867_; uint8_t v_isSharedCheck_1871_; 
lean_del_object(v___x_1845_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
v_a_1864_ = lean_ctor_get(v___x_1858_, 0);
v_isSharedCheck_1871_ = !lean_is_exclusive(v___x_1858_);
if (v_isSharedCheck_1871_ == 0)
{
v___x_1866_ = v___x_1858_;
v_isShared_1867_ = v_isSharedCheck_1871_;
goto v_resetjp_1865_;
}
else
{
lean_inc(v_a_1864_);
lean_dec(v___x_1858_);
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
lean_del_object(v___x_1845_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_1872_ = lean_ctor_get(v___x_1856_, 0);
v_isSharedCheck_1879_ = !lean_is_exclusive(v___x_1856_);
if (v_isSharedCheck_1879_ == 0)
{
v___x_1874_ = v___x_1856_;
v_isShared_1875_ = v_isSharedCheck_1879_;
goto v_resetjp_1873_;
}
else
{
lean_inc(v_a_1872_);
lean_dec(v___x_1856_);
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
else
{
lean_object* v_a_1880_; lean_object* v___x_1882_; uint8_t v_isShared_1883_; uint8_t v_isSharedCheck_1887_; 
lean_del_object(v___x_1845_);
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
v_a_1880_ = lean_ctor_get(v___x_1853_, 0);
v_isSharedCheck_1887_ = !lean_is_exclusive(v___x_1853_);
if (v_isSharedCheck_1887_ == 0)
{
v___x_1882_ = v___x_1853_;
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
else
{
lean_inc(v_a_1880_);
lean_dec(v___x_1853_);
v___x_1882_ = lean_box(0);
v_isShared_1883_ = v_isSharedCheck_1887_;
goto v_resetjp_1881_;
}
v_resetjp_1881_:
{
lean_object* v___x_1885_; 
if (v_isShared_1883_ == 0)
{
v___x_1885_ = v___x_1882_;
goto v_reusejp_1884_;
}
else
{
lean_object* v_reuseFailAlloc_1886_; 
v_reuseFailAlloc_1886_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1886_, 0, v_a_1880_);
v___x_1885_ = v_reuseFailAlloc_1886_;
goto v_reusejp_1884_;
}
v_reusejp_1884_:
{
return v___x_1885_;
}
}
}
}
v___jp_1889_:
{
lean_object* v_searchFuel_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; 
v_searchFuel_1894_ = lean_ctor_get(v_config_1811_, 0);
v___x_1895_ = l_Lean_LocalDecl_fvarId(v_val_1843_);
lean_dec(v_val_1843_);
lean_inc(v_searchFuel_1894_);
lean_inc(v_mvarId_1812_);
v___x_1896_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1812_, v___x_1895_, v_searchFuel_1894_, v___y_1893_, v___y_1890_, v___y_1892_, v___y_1891_);
if (lean_obj_tag(v___x_1896_) == 0)
{
lean_object* v_a_1897_; uint8_t v___x_1898_; 
v_a_1897_ = lean_ctor_get(v___x_1896_, 0);
lean_inc(v_a_1897_);
lean_dec_ref_known(v___x_1896_, 1);
v___x_1898_ = lean_unbox(v_a_1897_);
lean_dec(v_a_1897_);
if (v___x_1898_ == 0)
{
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
v_a_1837_ = v___x_1888_;
goto v___jp_1836_;
}
else
{
lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; 
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v___x_1899_ = lean_box(v___x_1822_);
v___x_1900_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1900_, 0, v___x_1899_);
v___x_1901_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
lean_ctor_set(v___x_1901_, 1, v___x_1847_);
v_a_1829_ = v___x_1901_;
goto v___jp_1828_;
}
}
else
{
lean_object* v_a_1902_; lean_object* v___x_1904_; uint8_t v_isShared_1905_; uint8_t v_isSharedCheck_1909_; 
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_1902_ = lean_ctor_get(v___x_1896_, 0);
v_isSharedCheck_1909_ = !lean_is_exclusive(v___x_1896_);
if (v_isSharedCheck_1909_ == 0)
{
v___x_1904_ = v___x_1896_;
v_isShared_1905_ = v_isSharedCheck_1909_;
goto v_resetjp_1903_;
}
else
{
lean_inc(v_a_1902_);
lean_dec(v___x_1896_);
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
v___jp_1910_:
{
if (v___y_1915_ == 0)
{
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
v_a_1837_ = v___x_1888_;
goto v___jp_1836_;
}
else
{
v___y_1890_ = v___y_1911_;
v___y_1891_ = v___y_1912_;
v___y_1892_ = v___y_1913_;
v___y_1893_ = v___y_1914_;
goto v___jp_1889_;
}
}
v___jp_1917_:
{
if (v___y_1920_ == 0)
{
v___y_1890_ = v___y_1918_;
v___y_1891_ = v___y_1919_;
v___y_1892_ = v___y_1921_;
v___y_1893_ = v___y_1922_;
goto v___jp_1889_;
}
else
{
v___y_1911_ = v___y_1918_;
v___y_1912_ = v___y_1919_;
v___y_1913_ = v___y_1921_;
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___x_1916_;
goto v___jp_1910_;
}
}
v___jp_1923_:
{
if (v___y_1929_ == 0)
{
v___y_1911_ = v___y_1924_;
v___y_1912_ = v___y_1925_;
v___y_1913_ = v___y_1927_;
v___y_1914_ = v___y_1928_;
v___y_1915_ = v___x_1916_;
goto v___jp_1910_;
}
else
{
v___y_1918_ = v___y_1924_;
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___y_1926_;
v___y_1921_ = v___y_1927_;
v___y_1922_ = v___y_1928_;
goto v___jp_1917_;
}
}
v___jp_1930_:
{
uint8_t v_emptyType_1937_; 
v_emptyType_1937_ = lean_ctor_get_uint8(v_config_1811_, sizeof(void*)*1 + 1);
if (v_emptyType_1937_ == 0)
{
v___y_1924_ = v___y_1934_;
v___y_1925_ = v___y_1936_;
v___y_1926_ = v___y_1931_;
v___y_1927_ = v___y_1935_;
v___y_1928_ = v___y_1933_;
v___y_1929_ = v___x_1916_;
goto v___jp_1923_;
}
else
{
if (v___y_1932_ == 0)
{
v___y_1918_ = v___y_1934_;
v___y_1919_ = v___y_1936_;
v___y_1920_ = v___y_1931_;
v___y_1921_ = v___y_1935_;
v___y_1922_ = v___y_1933_;
goto v___jp_1917_;
}
else
{
v___y_1924_ = v___y_1934_;
v___y_1925_ = v___y_1936_;
v___y_1926_ = v___y_1931_;
v___y_1927_ = v___y_1935_;
v___y_1928_ = v___y_1933_;
v___y_1929_ = v___x_1916_;
goto v___jp_1923_;
}
}
}
v___jp_1938_:
{
if (v___y_1945_ == 0)
{
v___y_1931_ = v___y_1941_;
v___y_1932_ = v___y_1943_;
v___y_1933_ = v___y_1944_;
v___y_1934_ = v___y_1942_;
v___y_1935_ = v___y_1940_;
v___y_1936_ = v___y_1939_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1946_; 
lean_inc(v_val_1843_);
lean_inc(v_mvarId_1812_);
v___x_1946_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1812_, v_val_1843_, v___y_1944_, v___y_1942_, v___y_1940_, v___y_1939_);
if (lean_obj_tag(v___x_1946_) == 0)
{
lean_object* v_a_1947_; uint8_t v___x_1948_; 
v_a_1947_ = lean_ctor_get(v___x_1946_, 0);
lean_inc(v_a_1947_);
lean_dec_ref_known(v___x_1946_, 1);
v___x_1948_ = lean_unbox(v_a_1947_);
lean_dec(v_a_1947_);
if (v___x_1948_ == 0)
{
v___y_1931_ = v___y_1941_;
v___y_1932_ = v___y_1943_;
v___y_1933_ = v___y_1944_;
v___y_1934_ = v___y_1942_;
v___y_1935_ = v___y_1940_;
v___y_1936_ = v___y_1939_;
goto v___jp_1930_;
}
else
{
lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; 
lean_dec(v_val_1843_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v___x_1949_ = lean_box(v___x_1822_);
v___x_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1950_, 0, v___x_1949_);
v___x_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
lean_ctor_set(v___x_1951_, 1, v___x_1847_);
v_a_1829_ = v___x_1951_;
goto v___jp_1828_;
}
}
else
{
lean_object* v_a_1952_; lean_object* v___x_1954_; uint8_t v_isShared_1955_; uint8_t v_isSharedCheck_1959_; 
lean_dec(v_val_1843_);
lean_del_object(v___x_1826_);
lean_dec(v_snd_1824_);
lean_dec(v_mvarId_1812_);
lean_dec_ref(v_config_1811_);
v_a_1952_ = lean_ctor_get(v___x_1946_, 0);
v_isSharedCheck_1959_ = !lean_is_exclusive(v___x_1946_);
if (v_isSharedCheck_1959_ == 0)
{
v___x_1954_ = v___x_1946_;
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
else
{
lean_inc(v_a_1952_);
lean_dec(v___x_1946_);
v___x_1954_ = lean_box(0);
v_isShared_1955_ = v_isSharedCheck_1959_;
goto v_resetjp_1953_;
}
v_resetjp_1953_:
{
lean_object* v___x_1957_; 
if (v_isShared_1955_ == 0)
{
v___x_1957_ = v___x_1954_;
goto v_reusejp_1956_;
}
else
{
lean_object* v_reuseFailAlloc_1958_; 
v_reuseFailAlloc_1958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1958_, 0, v_a_1952_);
v___x_1957_ = v_reuseFailAlloc_1958_;
goto v_reusejp_1956_;
}
v_reusejp_1956_:
{
return v___x_1957_;
}
}
}
}
}
}
}
v___jp_1828_:
{
lean_object* v___x_1830_; lean_object* v___x_1832_; 
v___x_1830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1830_, 0, v_a_1829_);
if (v_isShared_1827_ == 0)
{
lean_ctor_set(v___x_1826_, 0, v___x_1830_);
v___x_1832_ = v___x_1826_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1834_; 
v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1830_);
lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_snd_1824_);
v___x_1832_ = v_reuseFailAlloc_1834_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
return v___x_1833_;
}
}
v___jp_1836_:
{
lean_object* v___x_1838_; size_t v___x_1839_; size_t v___x_1840_; 
v___x_1838_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1838_, 0, v___x_1835_);
lean_ctor_set(v___x_1838_, 1, v_a_1837_);
v___x_1839_ = ((size_t)1ULL);
v___x_1840_ = lean_usize_add(v_i_1815_, v___x_1839_);
v_i_1815_ = v___x_1840_;
v_b_1816_ = v___x_1838_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2476_, lean_object* v_mvarId_2477_, lean_object* v_as_2478_, lean_object* v_sz_2479_, lean_object* v_i_2480_, lean_object* v_b_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
size_t v_sz_boxed_2487_; size_t v_i_boxed_2488_; lean_object* v_res_2489_; 
v_sz_boxed_2487_ = lean_unbox_usize(v_sz_2479_);
lean_dec(v_sz_2479_);
v_i_boxed_2488_ = lean_unbox_usize(v_i_2480_);
lean_dec(v_i_2480_);
v_res_2489_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2476_, v_mvarId_2477_, v_as_2478_, v_sz_boxed_2487_, v_i_boxed_2488_, v_b_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_as_2478_);
return v_res_2489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2490_, lean_object* v_mvarId_2491_, lean_object* v_as_2492_, size_t v_sz_2493_, size_t v_i_2494_, lean_object* v_b_2495_, lean_object* v___y_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_){
_start:
{
uint8_t v___x_2501_; 
v___x_2501_ = lean_usize_dec_lt(v_i_2494_, v_sz_2493_);
if (v___x_2501_ == 0)
{
lean_object* v___x_2502_; 
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v___x_2502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2502_, 0, v_b_2495_);
return v___x_2502_;
}
else
{
lean_object* v_snd_2503_; lean_object* v___x_2505_; uint8_t v_isShared_2506_; uint8_t v_isSharedCheck_3153_; 
v_snd_2503_ = lean_ctor_get(v_b_2495_, 1);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_b_2495_);
if (v_isSharedCheck_3153_ == 0)
{
lean_object* v_unused_3154_; 
v_unused_3154_ = lean_ctor_get(v_b_2495_, 0);
lean_dec(v_unused_3154_);
v___x_2505_ = v_b_2495_;
v_isShared_2506_ = v_isSharedCheck_3153_;
goto v_resetjp_2504_;
}
else
{
lean_inc(v_snd_2503_);
lean_dec(v_b_2495_);
v___x_2505_ = lean_box(0);
v_isShared_2506_ = v_isSharedCheck_3153_;
goto v_resetjp_2504_;
}
v_resetjp_2504_:
{
lean_object* v_a_2508_; lean_object* v___x_2514_; lean_object* v_a_2516_; lean_object* v_a_2521_; 
v___x_2514_ = lean_box(0);
v_a_2521_ = lean_array_uget(v_as_2492_, v_i_2494_);
if (lean_obj_tag(v_a_2521_) == 0)
{
lean_del_object(v___x_2505_);
v_a_2516_ = v_snd_2503_;
goto v___jp_2515_;
}
else
{
lean_object* v_val_2522_; lean_object* v___x_2524_; uint8_t v_isShared_2525_; uint8_t v_isSharedCheck_3152_; 
v_val_2522_ = lean_ctor_get(v_a_2521_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v_a_2521_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_2524_ = v_a_2521_;
v_isShared_2525_ = v_isSharedCheck_3152_;
goto v_resetjp_2523_;
}
else
{
lean_inc(v_val_2522_);
lean_dec(v_a_2521_);
v___x_2524_ = lean_box(0);
v_isShared_2525_ = v_isSharedCheck_3152_;
goto v_resetjp_2523_;
}
v_resetjp_2523_:
{
lean_object* v___x_2526_; lean_object* v___y_2528_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___x_2567_; lean_object* v___y_2569_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2590_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; uint8_t v___y_2594_; uint8_t v___x_2595_; uint8_t v___y_2597_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; lean_object* v___y_2601_; uint8_t v___y_2603_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; lean_object* v___y_2607_; uint8_t v___y_2608_; uint8_t v___y_2610_; uint8_t v___y_2611_; lean_object* v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; uint8_t v___y_2618_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; uint8_t v___y_2622_; lean_object* v___y_2623_; uint8_t v___y_2624_; 
v___x_2526_ = lean_box(0);
v___x_2567_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2595_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2522_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2639_; uint8_t v___y_2641_; uint8_t v___y_2642_; lean_object* v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2650_; uint8_t v___y_2651_; lean_object* v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; uint8_t v___y_2655_; lean_object* v___y_2656_; uint8_t v___y_2657_; lean_object* v___y_2660_; lean_object* v___y_2661_; uint8_t v___y_2662_; lean_object* v___y_2663_; uint8_t v___y_2664_; lean_object* v___y_2665_; lean_object* v_a_2666_; lean_object* v___y_2670_; uint8_t v___y_2671_; lean_object* v___y_2672_; lean_object* v___y_2673_; uint8_t v___y_2674_; lean_object* v___y_2675_; lean_object* v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2714_; uint8_t v___y_2715_; lean_object* v___y_2716_; lean_object* v___y_2717_; uint8_t v___y_2718_; lean_object* v___y_2719_; lean_object* v___y_2743_; uint8_t v___y_2744_; lean_object* v___y_2745_; lean_object* v___y_2746_; uint8_t v___y_2747_; lean_object* v___y_2748_; uint8_t v___y_2749_; lean_object* v___y_2751_; lean_object* v___y_2752_; uint8_t v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; uint8_t v___y_2756_; lean_object* v___y_2757_; uint8_t v___y_2758_; lean_object* v___y_2761_; uint8_t v___y_2762_; lean_object* v___y_2763_; lean_object* v___y_2764_; uint8_t v___y_2765_; lean_object* v___y_2766_; uint8_t v___y_2767_; lean_object* v___y_2780_; uint8_t v___y_2781_; lean_object* v___y_2782_; lean_object* v___y_2783_; uint8_t v___y_2784_; lean_object* v___y_2785_; uint8_t v___y_2786_; uint8_t v___y_2788_; uint8_t v_isHEq_2789_; lean_object* v___y_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2797_; lean_object* v___y_2798_; uint8_t v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; uint8_t v_isEq_2859_; lean_object* v___y_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2955_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___x_3089_; 
v___x_2639_ = l_Lean_LocalDecl_type(v_val_2522_);
lean_inc_ref(v___x_2639_);
v___x_3089_ = l_Lean_Meta_matchNot_x3f(v___x_2639_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_3089_) == 0)
{
lean_object* v_a_3090_; 
v_a_3090_ = lean_ctor_get(v___x_3089_, 0);
lean_inc(v_a_3090_);
lean_dec_ref_known(v___x_3089_, 1);
if (lean_obj_tag(v_a_3090_) == 1)
{
lean_object* v_val_3091_; lean_object* v___x_3092_; 
v_val_3091_ = lean_ctor_get(v_a_3090_, 0);
lean_inc(v_val_3091_);
lean_dec_ref_known(v_a_3090_, 1);
v___x_3092_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3091_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_3092_) == 0)
{
lean_object* v_a_3093_; 
v_a_3093_ = lean_ctor_get(v___x_3092_, 0);
lean_inc(v_a_3093_);
lean_dec_ref_known(v___x_3092_, 1);
if (lean_obj_tag(v_a_3093_) == 1)
{
lean_object* v_val_3094_; lean_object* v___x_3096_; uint8_t v_isShared_3097_; uint8_t v_isSharedCheck_3135_; 
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec_ref(v_config_2490_);
v_val_3094_ = lean_ctor_get(v_a_3093_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v_a_3093_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3096_ = v_a_3093_;
v_isShared_3097_ = v_isSharedCheck_3135_;
goto v_resetjp_3095_;
}
else
{
lean_inc(v_val_3094_);
lean_dec(v_a_3093_);
v___x_3096_ = lean_box(0);
v_isShared_3097_ = v_isSharedCheck_3135_;
goto v_resetjp_3095_;
}
v_resetjp_3095_:
{
lean_object* v___x_3098_; 
lean_inc(v_mvarId_2491_);
v___x_3098_ = l_Lean_MVarId_getType(v_mvarId_2491_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_3098_) == 0)
{
lean_object* v_a_3099_; lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; 
v_a_3099_ = lean_ctor_get(v___x_3098_, 0);
lean_inc(v_a_3099_);
lean_dec_ref_known(v___x_3098_, 1);
v___x_3100_ = l_Lean_LocalDecl_toExpr(v_val_2522_);
v___x_3101_ = l_Lean_mkFVar(v_val_3094_);
v___x_3102_ = l_Lean_Expr_app___override(v___x_3100_, v___x_3101_);
v___x_3103_ = l_Lean_Meta_mkFalseElim(v_a_3099_, v___x_3102_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3105_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc(v_a_3104_);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3105_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2491_, v_a_3104_, v___y_2497_);
if (lean_obj_tag(v___x_3105_) == 0)
{
lean_object* v___x_3106_; lean_object* v___x_3108_; 
lean_dec_ref_known(v___x_3105_, 1);
v___x_3106_ = lean_box(v___x_2501_);
if (v_isShared_3097_ == 0)
{
lean_ctor_set(v___x_3096_, 0, v___x_3106_);
v___x_3108_ = v___x_3096_;
goto v_reusejp_3107_;
}
else
{
lean_object* v_reuseFailAlloc_3110_; 
v_reuseFailAlloc_3110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3110_, 0, v___x_3106_);
v___x_3108_ = v_reuseFailAlloc_3110_;
goto v_reusejp_3107_;
}
v_reusejp_3107_:
{
lean_object* v___x_3109_; 
v___x_3109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3109_, 0, v___x_3108_);
lean_ctor_set(v___x_3109_, 1, v___x_2526_);
v_a_2508_ = v___x_3109_;
goto v___jp_2507_;
}
}
else
{
lean_object* v_a_3111_; lean_object* v___x_3113_; uint8_t v_isShared_3114_; uint8_t v_isSharedCheck_3118_; 
lean_del_object(v___x_3096_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
v_a_3111_ = lean_ctor_get(v___x_3105_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v___x_3105_);
if (v_isSharedCheck_3118_ == 0)
{
v___x_3113_ = v___x_3105_;
v_isShared_3114_ = v_isSharedCheck_3118_;
goto v_resetjp_3112_;
}
else
{
lean_inc(v_a_3111_);
lean_dec(v___x_3105_);
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
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_del_object(v___x_3096_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_3119_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3103_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3103_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_del_object(v___x_3096_);
lean_dec(v_val_3094_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_3127_ = lean_ctor_get(v___x_3098_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3098_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3098_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3098_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
}
else
{
lean_dec(v_a_3093_);
v___y_2955_ = v___y_2496_;
v___y_2956_ = v___y_2497_;
v___y_2957_ = v___y_2498_;
v___y_2958_ = v___y_2499_;
goto v___jp_2954_;
}
}
else
{
lean_object* v_a_3136_; lean_object* v___x_3138_; uint8_t v_isShared_3139_; uint8_t v_isSharedCheck_3143_; 
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_3136_ = lean_ctor_get(v___x_3092_, 0);
v_isSharedCheck_3143_ = !lean_is_exclusive(v___x_3092_);
if (v_isSharedCheck_3143_ == 0)
{
v___x_3138_ = v___x_3092_;
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
else
{
lean_inc(v_a_3136_);
lean_dec(v___x_3092_);
v___x_3138_ = lean_box(0);
v_isShared_3139_ = v_isSharedCheck_3143_;
goto v_resetjp_3137_;
}
v_resetjp_3137_:
{
lean_object* v___x_3141_; 
if (v_isShared_3139_ == 0)
{
v___x_3141_ = v___x_3138_;
goto v_reusejp_3140_;
}
else
{
lean_object* v_reuseFailAlloc_3142_; 
v_reuseFailAlloc_3142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3142_, 0, v_a_3136_);
v___x_3141_ = v_reuseFailAlloc_3142_;
goto v_reusejp_3140_;
}
v_reusejp_3140_:
{
return v___x_3141_;
}
}
}
}
else
{
lean_dec(v_a_3090_);
v___y_2955_ = v___y_2496_;
v___y_2956_ = v___y_2497_;
v___y_2957_ = v___y_2498_;
v___y_2958_ = v___y_2499_;
goto v___jp_2954_;
}
}
else
{
lean_object* v_a_3144_; lean_object* v___x_3146_; uint8_t v_isShared_3147_; uint8_t v_isSharedCheck_3151_; 
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_3144_ = lean_ctor_get(v___x_3089_, 0);
v_isSharedCheck_3151_ = !lean_is_exclusive(v___x_3089_);
if (v_isSharedCheck_3151_ == 0)
{
v___x_3146_ = v___x_3089_;
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
else
{
lean_inc(v_a_3144_);
lean_dec(v___x_3089_);
v___x_3146_ = lean_box(0);
v_isShared_3147_ = v_isSharedCheck_3151_;
goto v_resetjp_3145_;
}
v_resetjp_3145_:
{
lean_object* v___x_3149_; 
if (v_isShared_3147_ == 0)
{
v___x_3149_ = v___x_3146_;
goto v_reusejp_3148_;
}
else
{
lean_object* v_reuseFailAlloc_3150_; 
v_reuseFailAlloc_3150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3150_, 0, v_a_3144_);
v___x_3149_ = v_reuseFailAlloc_3150_;
goto v_reusejp_3148_;
}
v_reusejp_3148_:
{
return v___x_3149_;
}
}
}
v___jp_2640_:
{
uint8_t v_genDiseq_2647_; 
v_genDiseq_2647_ = lean_ctor_get_uint8(v_config_2490_, sizeof(void*)*1 + 2);
if (v_genDiseq_2647_ == 0)
{
lean_dec_ref(v___x_2639_);
v___y_2618_ = v___y_2641_;
v___y_2619_ = v___y_2644_;
v___y_2620_ = v___y_2643_;
v___y_2621_ = v___y_2645_;
v___y_2622_ = v___y_2642_;
v___y_2623_ = v___y_2646_;
v___y_2624_ = v___x_2595_;
goto v___jp_2617_;
}
else
{
uint8_t v___x_2648_; 
v___x_2648_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2639_);
v___y_2618_ = v___y_2641_;
v___y_2619_ = v___y_2644_;
v___y_2620_ = v___y_2643_;
v___y_2621_ = v___y_2645_;
v___y_2622_ = v___y_2642_;
v___y_2623_ = v___y_2646_;
v___y_2624_ = v___x_2648_;
goto v___jp_2617_;
}
}
v___jp_2649_:
{
if (v___y_2657_ == 0)
{
lean_dec_ref(v___y_2653_);
v___y_2641_ = v___y_2651_;
v___y_2642_ = v___y_2655_;
v___y_2643_ = v___y_2654_;
v___y_2644_ = v___y_2652_;
v___y_2645_ = v___y_2656_;
v___y_2646_ = v___y_2650_;
goto v___jp_2640_;
}
else
{
lean_object* v___x_2658_; 
lean_dec_ref(v___x_2639_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v___x_2658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2658_, 0, v___y_2653_);
return v___x_2658_;
}
}
v___jp_2659_:
{
uint8_t v___x_2667_; 
v___x_2667_ = l_Lean_Exception_isInterrupt(v_a_2666_);
if (v___x_2667_ == 0)
{
uint8_t v___x_2668_; 
lean_inc_ref(v_a_2666_);
v___x_2668_ = l_Lean_Exception_isRuntime(v_a_2666_);
v___y_2650_ = v___y_2660_;
v___y_2651_ = v___y_2662_;
v___y_2652_ = v___y_2661_;
v___y_2653_ = v_a_2666_;
v___y_2654_ = v___y_2663_;
v___y_2655_ = v___y_2664_;
v___y_2656_ = v___y_2665_;
v___y_2657_ = v___x_2668_;
goto v___jp_2649_;
}
else
{
v___y_2650_ = v___y_2660_;
v___y_2651_ = v___y_2662_;
v___y_2652_ = v___y_2661_;
v___y_2653_ = v_a_2666_;
v___y_2654_ = v___y_2663_;
v___y_2655_ = v___y_2664_;
v___y_2656_ = v___y_2665_;
v___y_2657_ = v___x_2667_;
goto v___jp_2649_;
}
}
v___jp_2669_:
{
if (lean_obj_tag(v___y_2677_) == 0)
{
lean_object* v_a_2678_; lean_object* v___x_2679_; uint8_t v___x_2680_; 
v_a_2678_ = lean_ctor_get(v___y_2677_, 0);
lean_inc(v_a_2678_);
lean_dec_ref_known(v___y_2677_, 1);
v___x_2679_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2680_ = l_Lean_Expr_isConstOf(v_a_2678_, v___x_2679_);
lean_dec(v_a_2678_);
if (v___x_2680_ == 0)
{
lean_dec_ref(v___y_2676_);
v___y_2641_ = v___y_2671_;
v___y_2642_ = v___y_2674_;
v___y_2643_ = v___y_2673_;
v___y_2644_ = v___y_2672_;
v___y_2645_ = v___y_2675_;
v___y_2646_ = v___y_2670_;
goto v___jp_2640_;
}
else
{
lean_object* v___x_2681_; 
lean_inc_ref(v___y_2676_);
v___x_2681_ = l_Lean_Meta_mkEqRefl(v___y_2676_, v___y_2673_, v___y_2672_, v___y_2675_, v___y_2670_);
if (lean_obj_tag(v___x_2681_) == 0)
{
lean_object* v_a_2682_; lean_object* v___x_2683_; lean_object* v_dummy_2684_; lean_object* v_nargs_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v_a_2682_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2682_);
lean_dec_ref_known(v___x_2681_, 1);
v___x_2683_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2684_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2685_ = l_Lean_Expr_getAppNumArgs(v___y_2676_);
lean_inc(v_nargs_2685_);
v___x_2686_ = lean_mk_array(v_nargs_2685_, v_dummy_2684_);
v___x_2687_ = lean_unsigned_to_nat(1u);
v___x_2688_ = lean_nat_sub(v_nargs_2685_, v___x_2687_);
lean_dec(v_nargs_2685_);
v___x_2689_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2676_, v___x_2686_, v___x_2688_);
v___x_2690_ = lean_array_push(v___x_2689_, v_a_2682_);
v___x_2691_ = l_Lean_mkAppN(v___x_2683_, v___x_2690_);
lean_dec_ref(v___x_2690_);
lean_inc(v_mvarId_2491_);
v___x_2692_ = l_Lean_MVarId_getType(v_mvarId_2491_, v___y_2673_, v___y_2672_, v___y_2675_, v___y_2670_);
if (lean_obj_tag(v___x_2692_) == 0)
{
lean_object* v_a_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_a_2693_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2693_);
lean_dec_ref_known(v___x_2692_, 1);
lean_inc(v_val_2522_);
v___x_2694_ = l_Lean_LocalDecl_toExpr(v_val_2522_);
v___x_2695_ = l_Lean_Meta_mkAbsurd(v_a_2693_, v___x_2694_, v___x_2691_, v___y_2673_, v___y_2672_, v___y_2675_, v___y_2670_);
if (lean_obj_tag(v___x_2695_) == 0)
{
lean_object* v_a_2696_; lean_object* v___x_2697_; 
v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2696_);
lean_dec_ref_known(v___x_2695_, 1);
lean_inc(v_mvarId_2491_);
v___x_2697_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2491_, v_a_2696_, v___y_2672_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2706_; 
lean_dec_ref(v___x_2639_);
lean_dec(v_val_2522_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_isSharedCheck_2706_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2706_ == 0)
{
lean_object* v_unused_2707_; 
v_unused_2707_ = lean_ctor_get(v___x_2697_, 0);
lean_dec(v_unused_2707_);
v___x_2699_ = v___x_2697_;
v_isShared_2700_ = v_isSharedCheck_2706_;
goto v_resetjp_2698_;
}
else
{
lean_dec(v___x_2697_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2706_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
lean_object* v___x_2701_; lean_object* v___x_2703_; 
v___x_2701_ = lean_box(v___x_2501_);
if (v_isShared_2700_ == 0)
{
lean_ctor_set_tag(v___x_2699_, 1);
lean_ctor_set(v___x_2699_, 0, v___x_2701_);
v___x_2703_ = v___x_2699_;
goto v_reusejp_2702_;
}
else
{
lean_object* v_reuseFailAlloc_2705_; 
v_reuseFailAlloc_2705_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2705_, 0, v___x_2701_);
v___x_2703_ = v_reuseFailAlloc_2705_;
goto v_reusejp_2702_;
}
v_reusejp_2702_:
{
lean_object* v___x_2704_; 
v___x_2704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2703_);
lean_ctor_set(v___x_2704_, 1, v___x_2526_);
v_a_2508_ = v___x_2704_;
goto v___jp_2507_;
}
}
}
else
{
lean_object* v_a_2708_; 
v_a_2708_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2708_);
lean_dec_ref_known(v___x_2697_, 1);
v___y_2660_ = v___y_2670_;
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2671_;
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2674_;
v___y_2665_ = v___y_2675_;
v_a_2666_ = v_a_2708_;
goto v___jp_2659_;
}
}
else
{
lean_object* v_a_2709_; 
v_a_2709_ = lean_ctor_get(v___x_2695_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2695_, 1);
v___y_2660_ = v___y_2670_;
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2671_;
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2674_;
v___y_2665_ = v___y_2675_;
v_a_2666_ = v_a_2709_;
goto v___jp_2659_;
}
}
else
{
lean_object* v_a_2710_; 
lean_dec_ref(v___x_2691_);
v_a_2710_ = lean_ctor_get(v___x_2692_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2692_, 1);
v___y_2660_ = v___y_2670_;
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2671_;
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2674_;
v___y_2665_ = v___y_2675_;
v_a_2666_ = v_a_2710_;
goto v___jp_2659_;
}
}
else
{
lean_object* v_a_2711_; 
lean_dec_ref(v___y_2676_);
v_a_2711_ = lean_ctor_get(v___x_2681_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2681_, 1);
v___y_2660_ = v___y_2670_;
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2671_;
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2674_;
v___y_2665_ = v___y_2675_;
v_a_2666_ = v_a_2711_;
goto v___jp_2659_;
}
}
}
else
{
lean_object* v_a_2712_; 
lean_dec_ref(v___y_2676_);
v_a_2712_ = lean_ctor_get(v___y_2677_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___y_2677_, 1);
v___y_2660_ = v___y_2670_;
v___y_2661_ = v___y_2672_;
v___y_2662_ = v___y_2671_;
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2674_;
v___y_2665_ = v___y_2675_;
v_a_2666_ = v_a_2712_;
goto v___jp_2659_;
}
}
v___jp_2713_:
{
lean_object* v___x_2720_; 
lean_inc_ref(v___x_2639_);
v___x_2720_ = l_Lean_Meta_mkDecide(v___x_2639_, v___y_2717_, v___y_2716_, v___y_2719_, v___y_2714_);
if (lean_obj_tag(v___x_2720_) == 0)
{
lean_object* v_a_2721_; lean_object* v___x_2722_; uint8_t v_transparency_2723_; uint8_t v___x_2724_; uint8_t v___x_2725_; 
v_a_2721_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2721_);
lean_dec_ref_known(v___x_2720_, 1);
v___x_2722_ = l_Lean_Meta_Context_config(v___y_2717_);
v_transparency_2723_ = lean_ctor_get_uint8(v___x_2722_, 9);
lean_dec_ref(v___x_2722_);
v___x_2724_ = 1;
v___x_2725_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2723_, v___x_2724_);
if (v___x_2725_ == 0)
{
lean_object* v_keyedConfig_2726_; uint8_t v_trackZetaDelta_2727_; lean_object* v_zetaDeltaSet_2728_; lean_object* v_lctx_2729_; lean_object* v_localInstances_2730_; lean_object* v_defEqCtx_x3f_2731_; lean_object* v_synthPendingDepth_2732_; lean_object* v_customCanUnfoldPredicate_x3f_2733_; uint8_t v_univApprox_2734_; uint8_t v_inTypeClassResolution_2735_; uint8_t v_cacheInferType_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v_keyedConfig_2726_ = lean_ctor_get(v___y_2717_, 0);
v_trackZetaDelta_2727_ = lean_ctor_get_uint8(v___y_2717_, sizeof(void*)*7);
v_zetaDeltaSet_2728_ = lean_ctor_get(v___y_2717_, 1);
v_lctx_2729_ = lean_ctor_get(v___y_2717_, 2);
v_localInstances_2730_ = lean_ctor_get(v___y_2717_, 3);
v_defEqCtx_x3f_2731_ = lean_ctor_get(v___y_2717_, 4);
v_synthPendingDepth_2732_ = lean_ctor_get(v___y_2717_, 5);
v_customCanUnfoldPredicate_x3f_2733_ = lean_ctor_get(v___y_2717_, 6);
v_univApprox_2734_ = lean_ctor_get_uint8(v___y_2717_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2735_ = lean_ctor_get_uint8(v___y_2717_, sizeof(void*)*7 + 2);
v_cacheInferType_2736_ = lean_ctor_get_uint8(v___y_2717_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2726_);
v___x_2737_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2724_, v_keyedConfig_2726_);
lean_inc(v_customCanUnfoldPredicate_x3f_2733_);
lean_inc(v_synthPendingDepth_2732_);
lean_inc(v_defEqCtx_x3f_2731_);
lean_inc_ref(v_localInstances_2730_);
lean_inc_ref(v_lctx_2729_);
lean_inc(v_zetaDeltaSet_2728_);
v___x_2738_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
lean_ctor_set(v___x_2738_, 1, v_zetaDeltaSet_2728_);
lean_ctor_set(v___x_2738_, 2, v_lctx_2729_);
lean_ctor_set(v___x_2738_, 3, v_localInstances_2730_);
lean_ctor_set(v___x_2738_, 4, v_defEqCtx_x3f_2731_);
lean_ctor_set(v___x_2738_, 5, v_synthPendingDepth_2732_);
lean_ctor_set(v___x_2738_, 6, v_customCanUnfoldPredicate_x3f_2733_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*7, v_trackZetaDelta_2727_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*7 + 1, v_univApprox_2734_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2735_);
lean_ctor_set_uint8(v___x_2738_, sizeof(void*)*7 + 3, v_cacheInferType_2736_);
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2719_);
lean_inc(v___y_2716_);
lean_inc(v_a_2721_);
v___x_2739_ = lean_whnf(v_a_2721_, v___x_2738_, v___y_2716_, v___y_2719_, v___y_2714_);
v___y_2670_ = v___y_2714_;
v___y_2671_ = v___y_2715_;
v___y_2672_ = v___y_2716_;
v___y_2673_ = v___y_2717_;
v___y_2674_ = v___y_2718_;
v___y_2675_ = v___y_2719_;
v___y_2676_ = v_a_2721_;
v___y_2677_ = v___x_2739_;
goto v___jp_2669_;
}
else
{
lean_object* v___x_2740_; 
lean_inc(v___y_2714_);
lean_inc_ref(v___y_2719_);
lean_inc(v___y_2716_);
lean_inc_ref(v___y_2717_);
lean_inc(v_a_2721_);
v___x_2740_ = lean_whnf(v_a_2721_, v___y_2717_, v___y_2716_, v___y_2719_, v___y_2714_);
v___y_2670_ = v___y_2714_;
v___y_2671_ = v___y_2715_;
v___y_2672_ = v___y_2716_;
v___y_2673_ = v___y_2717_;
v___y_2674_ = v___y_2718_;
v___y_2675_ = v___y_2719_;
v___y_2676_ = v_a_2721_;
v___y_2677_ = v___x_2740_;
goto v___jp_2669_;
}
}
else
{
lean_object* v_a_2741_; 
v_a_2741_ = lean_ctor_get(v___x_2720_, 0);
lean_inc(v_a_2741_);
lean_dec_ref_known(v___x_2720_, 1);
v___y_2660_ = v___y_2714_;
v___y_2661_ = v___y_2716_;
v___y_2662_ = v___y_2715_;
v___y_2663_ = v___y_2717_;
v___y_2664_ = v___y_2718_;
v___y_2665_ = v___y_2719_;
v_a_2666_ = v_a_2741_;
goto v___jp_2659_;
}
}
v___jp_2742_:
{
if (v___y_2749_ == 0)
{
v___y_2641_ = v___y_2744_;
v___y_2642_ = v___y_2747_;
v___y_2643_ = v___y_2746_;
v___y_2644_ = v___y_2745_;
v___y_2645_ = v___y_2748_;
v___y_2646_ = v___y_2743_;
goto v___jp_2640_;
}
else
{
v___y_2714_ = v___y_2743_;
v___y_2715_ = v___y_2744_;
v___y_2716_ = v___y_2745_;
v___y_2717_ = v___y_2746_;
v___y_2718_ = v___y_2747_;
v___y_2719_ = v___y_2748_;
goto v___jp_2713_;
}
}
v___jp_2750_:
{
if (v___y_2758_ == 0)
{
lean_dec_ref(v___y_2755_);
v___y_2743_ = v___y_2751_;
v___y_2744_ = v___y_2753_;
v___y_2745_ = v___y_2752_;
v___y_2746_ = v___y_2754_;
v___y_2747_ = v___y_2756_;
v___y_2748_ = v___y_2757_;
v___y_2749_ = v___x_2595_;
goto v___jp_2742_;
}
else
{
uint8_t v___x_2759_; 
v___x_2759_ = l_Lean_Expr_hasFVar(v___y_2755_);
lean_dec_ref(v___y_2755_);
if (v___x_2759_ == 0)
{
v___y_2714_ = v___y_2751_;
v___y_2715_ = v___y_2753_;
v___y_2716_ = v___y_2752_;
v___y_2717_ = v___y_2754_;
v___y_2718_ = v___y_2756_;
v___y_2719_ = v___y_2757_;
goto v___jp_2713_;
}
else
{
v___y_2743_ = v___y_2751_;
v___y_2744_ = v___y_2753_;
v___y_2745_ = v___y_2752_;
v___y_2746_ = v___y_2754_;
v___y_2747_ = v___y_2756_;
v___y_2748_ = v___y_2757_;
v___y_2749_ = v___x_2595_;
goto v___jp_2742_;
}
}
}
v___jp_2760_:
{
lean_object* v___x_2768_; 
lean_inc_ref(v___x_2639_);
v___x_2768_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2639_, v___y_2763_);
if (lean_obj_tag(v___x_2768_) == 0)
{
lean_object* v_a_2769_; uint8_t v___x_2770_; 
v_a_2769_ = lean_ctor_get(v___x_2768_, 0);
lean_inc(v_a_2769_);
lean_dec_ref_known(v___x_2768_, 1);
v___x_2770_ = l_Lean_Expr_hasMVar(v_a_2769_);
if (v___x_2770_ == 0)
{
v___y_2751_ = v___y_2761_;
v___y_2752_ = v___y_2763_;
v___y_2753_ = v___y_2762_;
v___y_2754_ = v___y_2764_;
v___y_2755_ = v_a_2769_;
v___y_2756_ = v___y_2765_;
v___y_2757_ = v___y_2766_;
v___y_2758_ = v___y_2767_;
goto v___jp_2750_;
}
else
{
v___y_2751_ = v___y_2761_;
v___y_2752_ = v___y_2763_;
v___y_2753_ = v___y_2762_;
v___y_2754_ = v___y_2764_;
v___y_2755_ = v_a_2769_;
v___y_2756_ = v___y_2765_;
v___y_2757_ = v___y_2766_;
v___y_2758_ = v___x_2595_;
goto v___jp_2750_;
}
}
else
{
lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec_ref(v___x_2639_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_2771_ = lean_ctor_get(v___x_2768_, 0);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2768_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2768_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_dec(v___x_2768_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
v___jp_2779_:
{
if (v___y_2786_ == 0)
{
v___y_2641_ = v___y_2781_;
v___y_2642_ = v___y_2784_;
v___y_2643_ = v___y_2783_;
v___y_2644_ = v___y_2782_;
v___y_2645_ = v___y_2785_;
v___y_2646_ = v___y_2780_;
goto v___jp_2640_;
}
else
{
v___y_2761_ = v___y_2780_;
v___y_2762_ = v___y_2781_;
v___y_2763_ = v___y_2782_;
v___y_2764_ = v___y_2783_;
v___y_2765_ = v___y_2784_;
v___y_2766_ = v___y_2785_;
v___y_2767_ = v___y_2786_;
goto v___jp_2760_;
}
}
v___jp_2787_:
{
uint8_t v_useDecide_2794_; 
v_useDecide_2794_ = lean_ctor_get_uint8(v_config_2490_, sizeof(void*)*1);
if (v_useDecide_2794_ == 0)
{
v___y_2780_ = v___y_2793_;
v___y_2781_ = v_isHEq_2789_;
v___y_2782_ = v___y_2791_;
v___y_2783_ = v___y_2790_;
v___y_2784_ = v___y_2788_;
v___y_2785_ = v___y_2792_;
v___y_2786_ = v___x_2595_;
goto v___jp_2779_;
}
else
{
uint8_t v___x_2795_; 
v___x_2795_ = l_Lean_Expr_hasFVar(v___x_2639_);
if (v___x_2795_ == 0)
{
v___y_2761_ = v___y_2793_;
v___y_2762_ = v_isHEq_2789_;
v___y_2763_ = v___y_2791_;
v___y_2764_ = v___y_2790_;
v___y_2765_ = v___y_2788_;
v___y_2766_ = v___y_2792_;
v___y_2767_ = v_useDecide_2794_;
goto v___jp_2760_;
}
else
{
v___y_2780_ = v___y_2793_;
v___y_2781_ = v_isHEq_2789_;
v___y_2782_ = v___y_2791_;
v___y_2783_ = v___y_2790_;
v___y_2784_ = v___y_2788_;
v___y_2785_ = v___y_2792_;
v___y_2786_ = v___x_2595_;
goto v___jp_2779_;
}
}
}
v___jp_2796_:
{
lean_object* v___x_2804_; 
v___x_2804_ = l_Lean_Meta_isExprDefEq(v___y_2798_, v___y_2802_, v___y_2803_, v___y_2801_, v___y_2797_, v___y_2800_);
if (lean_obj_tag(v___x_2804_) == 0)
{
lean_object* v_a_2805_; uint8_t v___x_2806_; 
v_a_2805_ = lean_ctor_get(v___x_2804_, 0);
lean_inc(v_a_2805_);
lean_dec_ref_known(v___x_2804_, 1);
v___x_2806_ = lean_unbox(v_a_2805_);
lean_dec(v_a_2805_);
if (v___x_2806_ == 0)
{
v___y_2788_ = v___y_2799_;
v_isHEq_2789_ = v___x_2501_;
v___y_2790_ = v___y_2803_;
v___y_2791_ = v___y_2801_;
v___y_2792_ = v___y_2797_;
v___y_2793_ = v___y_2800_;
goto v___jp_2787_;
}
else
{
lean_object* v___x_2807_; 
lean_dec_ref(v___x_2639_);
lean_dec_ref(v_config_2490_);
lean_inc(v_mvarId_2491_);
v___x_2807_ = l_Lean_MVarId_getType(v_mvarId_2491_, v___y_2803_, v___y_2801_, v___y_2797_, v___y_2800_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = l_Lean_LocalDecl_toExpr(v_val_2522_);
v___x_2810_ = l_Lean_Meta_mkEqOfHEq(v___x_2809_, v___x_2501_, v___y_2803_, v___y_2801_, v___y_2797_, v___y_2800_);
if (lean_obj_tag(v___x_2810_) == 0)
{
lean_object* v_a_2811_; lean_object* v___x_2812_; 
v_a_2811_ = lean_ctor_get(v___x_2810_, 0);
lean_inc(v_a_2811_);
lean_dec_ref_known(v___x_2810_, 1);
v___x_2812_ = l_Lean_Meta_mkNoConfusion(v_a_2808_, v_a_2811_, v___y_2803_, v___y_2801_, v___y_2797_, v___y_2800_);
if (lean_obj_tag(v___x_2812_) == 0)
{
lean_object* v_a_2813_; lean_object* v___x_2814_; 
v_a_2813_ = lean_ctor_get(v___x_2812_, 0);
lean_inc(v_a_2813_);
lean_dec_ref_known(v___x_2812_, 1);
v___x_2814_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2491_, v_a_2813_, v___y_2801_);
if (lean_obj_tag(v___x_2814_) == 0)
{
lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
lean_dec_ref_known(v___x_2814_, 1);
v___x_2815_ = lean_box(v___x_2501_);
v___x_2816_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2816_, 0, v___x_2815_);
v___x_2817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
lean_ctor_set(v___x_2817_, 1, v___x_2526_);
v_a_2508_ = v___x_2817_;
goto v___jp_2507_;
}
else
{
lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
v_a_2818_ = lean_ctor_get(v___x_2814_, 0);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2814_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2814_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_dec(v___x_2814_);
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
else
{
lean_object* v_a_2826_; lean_object* v___x_2828_; uint8_t v_isShared_2829_; uint8_t v_isSharedCheck_2833_; 
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_2826_ = lean_ctor_get(v___x_2812_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2812_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2828_ = v___x_2812_;
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
else
{
lean_inc(v_a_2826_);
lean_dec(v___x_2812_);
v___x_2828_ = lean_box(0);
v_isShared_2829_ = v_isSharedCheck_2833_;
goto v_resetjp_2827_;
}
v_resetjp_2827_:
{
lean_object* v___x_2831_; 
if (v_isShared_2829_ == 0)
{
v___x_2831_ = v___x_2828_;
goto v_reusejp_2830_;
}
else
{
lean_object* v_reuseFailAlloc_2832_; 
v_reuseFailAlloc_2832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2832_, 0, v_a_2826_);
v___x_2831_ = v_reuseFailAlloc_2832_;
goto v_reusejp_2830_;
}
v_reusejp_2830_:
{
return v___x_2831_;
}
}
}
}
else
{
lean_object* v_a_2834_; lean_object* v___x_2836_; uint8_t v_isShared_2837_; uint8_t v_isSharedCheck_2841_; 
lean_dec(v_a_2808_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_2834_ = lean_ctor_get(v___x_2810_, 0);
v_isSharedCheck_2841_ = !lean_is_exclusive(v___x_2810_);
if (v_isSharedCheck_2841_ == 0)
{
v___x_2836_ = v___x_2810_;
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
else
{
lean_inc(v_a_2834_);
lean_dec(v___x_2810_);
v___x_2836_ = lean_box(0);
v_isShared_2837_ = v_isSharedCheck_2841_;
goto v_resetjp_2835_;
}
v_resetjp_2835_:
{
lean_object* v___x_2839_; 
if (v_isShared_2837_ == 0)
{
v___x_2839_ = v___x_2836_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2834_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
else
{
lean_object* v_a_2842_; lean_object* v___x_2844_; uint8_t v_isShared_2845_; uint8_t v_isSharedCheck_2849_; 
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_2842_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2849_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2844_ = v___x_2807_;
v_isShared_2845_ = v_isSharedCheck_2849_;
goto v_resetjp_2843_;
}
else
{
lean_inc(v_a_2842_);
lean_dec(v___x_2807_);
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
}
else
{
lean_object* v_a_2850_; lean_object* v___x_2852_; uint8_t v_isShared_2853_; uint8_t v_isSharedCheck_2857_; 
lean_dec_ref(v___x_2639_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_2850_ = lean_ctor_get(v___x_2804_, 0);
v_isSharedCheck_2857_ = !lean_is_exclusive(v___x_2804_);
if (v_isSharedCheck_2857_ == 0)
{
v___x_2852_ = v___x_2804_;
v_isShared_2853_ = v_isSharedCheck_2857_;
goto v_resetjp_2851_;
}
else
{
lean_inc(v_a_2850_);
lean_dec(v___x_2804_);
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
v___jp_2858_:
{
lean_object* v___x_2864_; 
lean_inc_ref(v___x_2639_);
v___x_2864_ = l_Lean_Meta_matchHEq_x3f(v___x_2639_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2864_) == 0)
{
lean_object* v_a_2865_; 
v_a_2865_ = lean_ctor_get(v___x_2864_, 0);
lean_inc(v_a_2865_);
lean_dec_ref_known(v___x_2864_, 1);
if (lean_obj_tag(v_a_2865_) == 1)
{
lean_object* v_val_2866_; lean_object* v_snd_2867_; lean_object* v_snd_2868_; lean_object* v_fst_2869_; lean_object* v_fst_2870_; lean_object* v_fst_2871_; lean_object* v_snd_2872_; lean_object* v___x_2873_; 
v_val_2866_ = lean_ctor_get(v_a_2865_, 0);
lean_inc(v_val_2866_);
lean_dec_ref_known(v_a_2865_, 1);
v_snd_2867_ = lean_ctor_get(v_val_2866_, 1);
lean_inc(v_snd_2867_);
v_snd_2868_ = lean_ctor_get(v_snd_2867_, 1);
lean_inc(v_snd_2868_);
v_fst_2869_ = lean_ctor_get(v_val_2866_, 0);
lean_inc(v_fst_2869_);
lean_dec(v_val_2866_);
v_fst_2870_ = lean_ctor_get(v_snd_2867_, 0);
lean_inc(v_fst_2870_);
lean_dec(v_snd_2867_);
v_fst_2871_ = lean_ctor_get(v_snd_2868_, 0);
lean_inc(v_fst_2871_);
v_snd_2872_ = lean_ctor_get(v_snd_2868_, 1);
lean_inc(v_snd_2872_);
lean_dec(v_snd_2868_);
v___x_2873_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2870_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2873_) == 0)
{
lean_object* v_a_2874_; 
v_a_2874_ = lean_ctor_get(v___x_2873_, 0);
lean_inc(v_a_2874_);
lean_dec_ref_known(v___x_2873_, 1);
if (lean_obj_tag(v_a_2874_) == 1)
{
lean_object* v_val_2875_; lean_object* v___x_2876_; 
v_val_2875_ = lean_ctor_get(v_a_2874_, 0);
lean_inc(v_val_2875_);
lean_dec_ref_known(v_a_2874_, 1);
v___x_2876_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2872_, v___y_2860_, v___y_2861_, v___y_2862_, v___y_2863_);
if (lean_obj_tag(v___x_2876_) == 0)
{
lean_object* v_a_2877_; 
v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
lean_inc(v_a_2877_);
lean_dec_ref_known(v___x_2876_, 1);
if (lean_obj_tag(v_a_2877_) == 1)
{
lean_object* v_toConstantVal_2878_; lean_object* v_val_2879_; lean_object* v_toConstantVal_2880_; lean_object* v_name_2881_; lean_object* v_name_2882_; uint8_t v___x_2883_; 
v_toConstantVal_2878_ = lean_ctor_get(v_val_2875_, 0);
lean_inc_ref(v_toConstantVal_2878_);
lean_dec(v_val_2875_);
v_val_2879_ = lean_ctor_get(v_a_2877_, 0);
lean_inc(v_val_2879_);
lean_dec_ref_known(v_a_2877_, 1);
v_toConstantVal_2880_ = lean_ctor_get(v_val_2879_, 0);
lean_inc_ref(v_toConstantVal_2880_);
lean_dec(v_val_2879_);
v_name_2881_ = lean_ctor_get(v_toConstantVal_2878_, 0);
lean_inc(v_name_2881_);
lean_dec_ref(v_toConstantVal_2878_);
v_name_2882_ = lean_ctor_get(v_toConstantVal_2880_, 0);
lean_inc(v_name_2882_);
lean_dec_ref(v_toConstantVal_2880_);
v___x_2883_ = lean_name_eq(v_name_2881_, v_name_2882_);
lean_dec(v_name_2882_);
lean_dec(v_name_2881_);
if (v___x_2883_ == 0)
{
v___y_2797_ = v___y_2862_;
v___y_2798_ = v_fst_2869_;
v___y_2799_ = v_isEq_2859_;
v___y_2800_ = v___y_2863_;
v___y_2801_ = v___y_2861_;
v___y_2802_ = v_fst_2871_;
v___y_2803_ = v___y_2860_;
goto v___jp_2796_;
}
else
{
if (v___x_2595_ == 0)
{
lean_dec(v_fst_2871_);
lean_dec(v_fst_2869_);
v___y_2788_ = v_isEq_2859_;
v_isHEq_2789_ = v___x_2501_;
v___y_2790_ = v___y_2860_;
v___y_2791_ = v___y_2861_;
v___y_2792_ = v___y_2862_;
v___y_2793_ = v___y_2863_;
goto v___jp_2787_;
}
else
{
v___y_2797_ = v___y_2862_;
v___y_2798_ = v_fst_2869_;
v___y_2799_ = v_isEq_2859_;
v___y_2800_ = v___y_2863_;
v___y_2801_ = v___y_2861_;
v___y_2802_ = v_fst_2871_;
v___y_2803_ = v___y_2860_;
goto v___jp_2796_;
}
}
}
else
{
lean_dec(v_a_2877_);
lean_dec(v_val_2875_);
lean_dec(v_fst_2871_);
lean_dec(v_fst_2869_);
v___y_2788_ = v_isEq_2859_;
v_isHEq_2789_ = v___x_2501_;
v___y_2790_ = v___y_2860_;
v___y_2791_ = v___y_2861_;
v___y_2792_ = v___y_2862_;
v___y_2793_ = v___y_2863_;
goto v___jp_2787_;
}
}
else
{
lean_object* v_a_2884_; lean_object* v___x_2886_; uint8_t v_isShared_2887_; uint8_t v_isSharedCheck_2891_; 
lean_dec(v_val_2875_);
lean_dec(v_fst_2871_);
lean_dec(v_fst_2869_);
lean_dec_ref(v___x_2639_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_2884_ = lean_ctor_get(v___x_2876_, 0);
v_isSharedCheck_2891_ = !lean_is_exclusive(v___x_2876_);
if (v_isSharedCheck_2891_ == 0)
{
v___x_2886_ = v___x_2876_;
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
else
{
lean_inc(v_a_2884_);
lean_dec(v___x_2876_);
v___x_2886_ = lean_box(0);
v_isShared_2887_ = v_isSharedCheck_2891_;
goto v_resetjp_2885_;
}
v_resetjp_2885_:
{
lean_object* v___x_2889_; 
if (v_isShared_2887_ == 0)
{
v___x_2889_ = v___x_2886_;
goto v_reusejp_2888_;
}
else
{
lean_object* v_reuseFailAlloc_2890_; 
v_reuseFailAlloc_2890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2890_, 0, v_a_2884_);
v___x_2889_ = v_reuseFailAlloc_2890_;
goto v_reusejp_2888_;
}
v_reusejp_2888_:
{
return v___x_2889_;
}
}
}
}
else
{
lean_dec(v_a_2874_);
lean_dec(v_snd_2872_);
lean_dec(v_fst_2871_);
lean_dec(v_fst_2869_);
v___y_2788_ = v_isEq_2859_;
v_isHEq_2789_ = v___x_2501_;
v___y_2790_ = v___y_2860_;
v___y_2791_ = v___y_2861_;
v___y_2792_ = v___y_2862_;
v___y_2793_ = v___y_2863_;
goto v___jp_2787_;
}
}
else
{
lean_object* v_a_2892_; lean_object* v___x_2894_; uint8_t v_isShared_2895_; uint8_t v_isSharedCheck_2899_; 
lean_dec(v_snd_2872_);
lean_dec(v_fst_2871_);
lean_dec(v_fst_2869_);
lean_dec_ref(v___x_2639_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_2892_ = lean_ctor_get(v___x_2873_, 0);
v_isSharedCheck_2899_ = !lean_is_exclusive(v___x_2873_);
if (v_isSharedCheck_2899_ == 0)
{
v___x_2894_ = v___x_2873_;
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
else
{
lean_inc(v_a_2892_);
lean_dec(v___x_2873_);
v___x_2894_ = lean_box(0);
v_isShared_2895_ = v_isSharedCheck_2899_;
goto v_resetjp_2893_;
}
v_resetjp_2893_:
{
lean_object* v___x_2897_; 
if (v_isShared_2895_ == 0)
{
v___x_2897_ = v___x_2894_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2898_; 
v_reuseFailAlloc_2898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2898_, 0, v_a_2892_);
v___x_2897_ = v_reuseFailAlloc_2898_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
return v___x_2897_;
}
}
}
}
else
{
lean_dec(v_a_2865_);
v___y_2788_ = v_isEq_2859_;
v_isHEq_2789_ = v___x_2595_;
v___y_2790_ = v___y_2860_;
v___y_2791_ = v___y_2861_;
v___y_2792_ = v___y_2862_;
v___y_2793_ = v___y_2863_;
goto v___jp_2787_;
}
}
else
{
lean_object* v_a_2900_; lean_object* v___x_2902_; uint8_t v_isShared_2903_; uint8_t v_isSharedCheck_2907_; 
lean_dec_ref(v___x_2639_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_2900_ = lean_ctor_get(v___x_2864_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2864_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2902_ = v___x_2864_;
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
else
{
lean_inc(v_a_2900_);
lean_dec(v___x_2864_);
v___x_2902_ = lean_box(0);
v_isShared_2903_ = v_isSharedCheck_2907_;
goto v_resetjp_2901_;
}
v_resetjp_2901_:
{
lean_object* v___x_2905_; 
if (v_isShared_2903_ == 0)
{
v___x_2905_ = v___x_2902_;
goto v_reusejp_2904_;
}
else
{
lean_object* v_reuseFailAlloc_2906_; 
v_reuseFailAlloc_2906_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2906_, 0, v_a_2900_);
v___x_2905_ = v_reuseFailAlloc_2906_;
goto v_reusejp_2904_;
}
v_reusejp_2904_:
{
return v___x_2905_;
}
}
}
}
v___jp_2908_:
{
lean_object* v___x_2913_; 
lean_inc_ref(v___x_2639_);
v___x_2913_ = l_Lean_Meta_matchEq_x3f(v___x_2639_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v_a_2914_; 
v_a_2914_ = lean_ctor_get(v___x_2913_, 0);
lean_inc(v_a_2914_);
lean_dec_ref_known(v___x_2913_, 1);
if (lean_obj_tag(v_a_2914_) == 1)
{
lean_object* v_val_2915_; lean_object* v_snd_2916_; lean_object* v_fst_2917_; lean_object* v_snd_2918_; lean_object* v___x_2919_; 
v_val_2915_ = lean_ctor_get(v_a_2914_, 0);
lean_inc(v_val_2915_);
lean_dec_ref_known(v_a_2914_, 1);
v_snd_2916_ = lean_ctor_get(v_val_2915_, 1);
lean_inc(v_snd_2916_);
lean_dec(v_val_2915_);
v_fst_2917_ = lean_ctor_get(v_snd_2916_, 0);
lean_inc(v_fst_2917_);
v_snd_2918_ = lean_ctor_get(v_snd_2916_, 1);
lean_inc(v_snd_2918_);
lean_dec(v_snd_2916_);
v___x_2919_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2917_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
if (lean_obj_tag(v___x_2919_) == 0)
{
lean_object* v_a_2920_; 
v_a_2920_ = lean_ctor_get(v___x_2919_, 0);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2919_, 1);
if (lean_obj_tag(v_a_2920_) == 1)
{
lean_object* v_val_2921_; lean_object* v___x_2922_; 
v_val_2921_ = lean_ctor_get(v_a_2920_, 0);
lean_inc(v_val_2921_);
lean_dec_ref_known(v_a_2920_, 1);
v___x_2922_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2918_, v___y_2909_, v___y_2910_, v___y_2911_, v___y_2912_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
lean_inc(v_a_2923_);
lean_dec_ref_known(v___x_2922_, 1);
if (lean_obj_tag(v_a_2923_) == 1)
{
lean_object* v_toConstantVal_2924_; lean_object* v_val_2925_; lean_object* v_toConstantVal_2926_; lean_object* v_name_2927_; lean_object* v_name_2928_; uint8_t v___x_2929_; 
v_toConstantVal_2924_ = lean_ctor_get(v_val_2921_, 0);
lean_inc_ref(v_toConstantVal_2924_);
lean_dec(v_val_2921_);
v_val_2925_ = lean_ctor_get(v_a_2923_, 0);
lean_inc(v_val_2925_);
lean_dec_ref_known(v_a_2923_, 1);
v_toConstantVal_2926_ = lean_ctor_get(v_val_2925_, 0);
lean_inc_ref(v_toConstantVal_2926_);
lean_dec(v_val_2925_);
v_name_2927_ = lean_ctor_get(v_toConstantVal_2924_, 0);
lean_inc(v_name_2927_);
lean_dec_ref(v_toConstantVal_2924_);
v_name_2928_ = lean_ctor_get(v_toConstantVal_2926_, 0);
lean_inc(v_name_2928_);
lean_dec_ref(v_toConstantVal_2926_);
v___x_2929_ = lean_name_eq(v_name_2927_, v_name_2928_);
lean_dec(v_name_2928_);
lean_dec(v_name_2927_);
if (v___x_2929_ == 0)
{
lean_dec_ref(v___x_2639_);
lean_dec_ref(v_config_2490_);
v___y_2528_ = v___y_2912_;
v___y_2529_ = v___y_2909_;
v___y_2530_ = v___y_2911_;
v___y_2531_ = v___y_2910_;
goto v___jp_2527_;
}
else
{
if (v___x_2595_ == 0)
{
lean_del_object(v___x_2524_);
v_isEq_2859_ = v___x_2501_;
v___y_2860_ = v___y_2909_;
v___y_2861_ = v___y_2910_;
v___y_2862_ = v___y_2911_;
v___y_2863_ = v___y_2912_;
goto v___jp_2858_;
}
else
{
lean_dec_ref(v___x_2639_);
lean_dec_ref(v_config_2490_);
v___y_2528_ = v___y_2912_;
v___y_2529_ = v___y_2909_;
v___y_2530_ = v___y_2911_;
v___y_2531_ = v___y_2910_;
goto v___jp_2527_;
}
}
}
else
{
lean_dec(v_a_2923_);
lean_dec(v_val_2921_);
lean_del_object(v___x_2524_);
v_isEq_2859_ = v___x_2501_;
v___y_2860_ = v___y_2909_;
v___y_2861_ = v___y_2910_;
v___y_2862_ = v___y_2911_;
v___y_2863_ = v___y_2912_;
goto v___jp_2858_;
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_dec(v_val_2921_);
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_2930_ = lean_ctor_get(v___x_2922_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2922_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2922_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
}
else
{
lean_dec(v_a_2920_);
lean_dec(v_snd_2918_);
lean_del_object(v___x_2524_);
v_isEq_2859_ = v___x_2501_;
v___y_2860_ = v___y_2909_;
v___y_2861_ = v___y_2910_;
v___y_2862_ = v___y_2911_;
v___y_2863_ = v___y_2912_;
goto v___jp_2858_;
}
}
else
{
lean_object* v_a_2938_; lean_object* v___x_2940_; uint8_t v_isShared_2941_; uint8_t v_isSharedCheck_2945_; 
lean_dec(v_snd_2918_);
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_2938_ = lean_ctor_get(v___x_2919_, 0);
v_isSharedCheck_2945_ = !lean_is_exclusive(v___x_2919_);
if (v_isSharedCheck_2945_ == 0)
{
v___x_2940_ = v___x_2919_;
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
else
{
lean_inc(v_a_2938_);
lean_dec(v___x_2919_);
v___x_2940_ = lean_box(0);
v_isShared_2941_ = v_isSharedCheck_2945_;
goto v_resetjp_2939_;
}
v_resetjp_2939_:
{
lean_object* v___x_2943_; 
if (v_isShared_2941_ == 0)
{
v___x_2943_ = v___x_2940_;
goto v_reusejp_2942_;
}
else
{
lean_object* v_reuseFailAlloc_2944_; 
v_reuseFailAlloc_2944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2944_, 0, v_a_2938_);
v___x_2943_ = v_reuseFailAlloc_2944_;
goto v_reusejp_2942_;
}
v_reusejp_2942_:
{
return v___x_2943_;
}
}
}
}
else
{
lean_dec(v_a_2914_);
lean_del_object(v___x_2524_);
v_isEq_2859_ = v___x_2595_;
v___y_2860_ = v___y_2909_;
v___y_2861_ = v___y_2910_;
v___y_2862_ = v___y_2911_;
v___y_2863_ = v___y_2912_;
goto v___jp_2858_;
}
}
else
{
lean_object* v_a_2946_; lean_object* v___x_2948_; uint8_t v_isShared_2949_; uint8_t v_isSharedCheck_2953_; 
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_2946_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2953_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2953_ == 0)
{
v___x_2948_ = v___x_2913_;
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
else
{
lean_inc(v_a_2946_);
lean_dec(v___x_2913_);
v___x_2948_ = lean_box(0);
v_isShared_2949_ = v_isSharedCheck_2953_;
goto v_resetjp_2947_;
}
v_resetjp_2947_:
{
lean_object* v___x_2951_; 
if (v_isShared_2949_ == 0)
{
v___x_2951_ = v___x_2948_;
goto v_reusejp_2950_;
}
else
{
lean_object* v_reuseFailAlloc_2952_; 
v_reuseFailAlloc_2952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2952_, 0, v_a_2946_);
v___x_2951_ = v_reuseFailAlloc_2952_;
goto v_reusejp_2950_;
}
v_reusejp_2950_:
{
return v___x_2951_;
}
}
}
}
v___jp_2954_:
{
lean_object* v___x_2959_; 
lean_inc_ref(v___x_2639_);
v___x_2959_ = l_Lean_refutableHasNotBit_x3f(v___x_2639_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_2959_) == 0)
{
lean_object* v_a_2960_; 
v_a_2960_ = lean_ctor_get(v___x_2959_, 0);
lean_inc(v_a_2960_);
lean_dec_ref_known(v___x_2959_, 1);
if (lean_obj_tag(v_a_2960_) == 1)
{
lean_object* v_val_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_3000_; 
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec_ref(v_config_2490_);
v_val_2961_ = lean_ctor_get(v_a_2960_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v_a_2960_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2963_ = v_a_2960_;
v_isShared_2964_ = v_isSharedCheck_3000_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_val_2961_);
lean_dec(v_a_2960_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_3000_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2965_; 
lean_inc(v_mvarId_2491_);
v___x_2965_ = l_Lean_MVarId_getType(v_mvarId_2491_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v_a_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; 
v_a_2966_ = lean_ctor_get(v___x_2965_, 0);
lean_inc(v_a_2966_);
lean_dec_ref_known(v___x_2965_, 1);
v___x_2967_ = l_Lean_LocalDecl_toExpr(v_val_2522_);
v___x_2968_ = l_Lean_Meta_mkAbsurd(v_a_2966_, v_val_2961_, v___x_2967_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_2968_) == 0)
{
lean_object* v_a_2969_; lean_object* v___x_2970_; 
v_a_2969_ = lean_ctor_get(v___x_2968_, 0);
lean_inc(v_a_2969_);
lean_dec_ref_known(v___x_2968_, 1);
v___x_2970_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2491_, v_a_2969_, v___y_2956_);
if (lean_obj_tag(v___x_2970_) == 0)
{
lean_object* v___x_2971_; lean_object* v___x_2973_; 
lean_dec_ref_known(v___x_2970_, 1);
v___x_2971_ = lean_box(v___x_2501_);
if (v_isShared_2964_ == 0)
{
lean_ctor_set(v___x_2963_, 0, v___x_2971_);
v___x_2973_ = v___x_2963_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v___x_2971_);
v___x_2973_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
lean_object* v___x_2974_; 
v___x_2974_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2974_, 0, v___x_2973_);
lean_ctor_set(v___x_2974_, 1, v___x_2526_);
v_a_2508_ = v___x_2974_;
goto v___jp_2507_;
}
}
else
{
lean_object* v_a_2976_; lean_object* v___x_2978_; uint8_t v_isShared_2979_; uint8_t v_isSharedCheck_2983_; 
lean_del_object(v___x_2963_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
v_a_2976_ = lean_ctor_get(v___x_2970_, 0);
v_isSharedCheck_2983_ = !lean_is_exclusive(v___x_2970_);
if (v_isSharedCheck_2983_ == 0)
{
v___x_2978_ = v___x_2970_;
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
else
{
lean_inc(v_a_2976_);
lean_dec(v___x_2970_);
v___x_2978_ = lean_box(0);
v_isShared_2979_ = v_isSharedCheck_2983_;
goto v_resetjp_2977_;
}
v_resetjp_2977_:
{
lean_object* v___x_2981_; 
if (v_isShared_2979_ == 0)
{
v___x_2981_ = v___x_2978_;
goto v_reusejp_2980_;
}
else
{
lean_object* v_reuseFailAlloc_2982_; 
v_reuseFailAlloc_2982_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2982_, 0, v_a_2976_);
v___x_2981_ = v_reuseFailAlloc_2982_;
goto v_reusejp_2980_;
}
v_reusejp_2980_:
{
return v___x_2981_;
}
}
}
}
else
{
lean_object* v_a_2984_; lean_object* v___x_2986_; uint8_t v_isShared_2987_; uint8_t v_isSharedCheck_2991_; 
lean_del_object(v___x_2963_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_2984_ = lean_ctor_get(v___x_2968_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2968_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2986_ = v___x_2968_;
v_isShared_2987_ = v_isSharedCheck_2991_;
goto v_resetjp_2985_;
}
else
{
lean_inc(v_a_2984_);
lean_dec(v___x_2968_);
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
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_del_object(v___x_2963_);
lean_dec(v_val_2961_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_2992_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2965_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2965_);
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
}
else
{
lean_object* v___x_3001_; 
lean_dec(v_a_2960_);
lean_inc_ref(v___x_2639_);
v___x_3001_ = l_Lean_Meta_matchNe_x3f(v___x_2639_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
if (lean_obj_tag(v_a_3002_) == 1)
{
lean_object* v_val_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3072_; 
v_val_3003_ = lean_ctor_get(v_a_3002_, 0);
v_isSharedCheck_3072_ = !lean_is_exclusive(v_a_3002_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3005_ = v_a_3002_;
v_isShared_3006_ = v_isSharedCheck_3072_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_val_3003_);
lean_dec(v_a_3002_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3072_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v_snd_3007_; lean_object* v_fst_3008_; lean_object* v_snd_3009_; lean_object* v___x_3011_; uint8_t v_isShared_3012_; uint8_t v_isSharedCheck_3071_; 
v_snd_3007_ = lean_ctor_get(v_val_3003_, 1);
lean_inc(v_snd_3007_);
lean_dec(v_val_3003_);
v_fst_3008_ = lean_ctor_get(v_snd_3007_, 0);
v_snd_3009_ = lean_ctor_get(v_snd_3007_, 1);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_snd_3007_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3011_ = v_snd_3007_;
v_isShared_3012_ = v_isSharedCheck_3071_;
goto v_resetjp_3010_;
}
else
{
lean_inc(v_snd_3009_);
lean_inc(v_fst_3008_);
lean_dec(v_snd_3007_);
v___x_3011_ = lean_box(0);
v_isShared_3012_ = v_isSharedCheck_3071_;
goto v_resetjp_3010_;
}
v_resetjp_3010_:
{
lean_object* v___x_3013_; 
lean_inc(v_fst_3008_);
v___x_3013_ = l_Lean_Meta_isExprDefEq(v_fst_3008_, v_snd_3009_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; uint8_t v___x_3015_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc(v_a_3014_);
lean_dec_ref_known(v___x_3013_, 1);
v___x_3015_ = lean_unbox(v_a_3014_);
lean_dec(v_a_3014_);
if (v___x_3015_ == 0)
{
lean_del_object(v___x_3011_);
lean_dec(v_fst_3008_);
lean_del_object(v___x_3005_);
v___y_2909_ = v___y_2955_;
v___y_2910_ = v___y_2956_;
v___y_2911_ = v___y_2957_;
v___y_2912_ = v___y_2958_;
goto v___jp_2908_;
}
else
{
lean_object* v___x_3016_; 
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec_ref(v_config_2490_);
lean_inc(v_mvarId_2491_);
v___x_3016_ = l_Lean_MVarId_getType(v_mvarId_2491_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v___x_3018_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v___x_3018_ = l_Lean_Meta_mkEqRefl(v_fst_3008_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v___x_3020_ = l_Lean_LocalDecl_toExpr(v_val_2522_);
v___x_3021_ = l_Lean_Meta_mkAbsurd(v_a_3017_, v_a_3019_, v___x_3020_, v___y_2955_, v___y_2956_, v___y_2957_, v___y_2958_);
if (lean_obj_tag(v___x_3021_) == 0)
{
lean_object* v_a_3022_; lean_object* v___x_3023_; 
v_a_3022_ = lean_ctor_get(v___x_3021_, 0);
lean_inc(v_a_3022_);
lean_dec_ref_known(v___x_3021_, 1);
v___x_3023_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2491_, v_a_3022_, v___y_2956_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v___x_3024_; lean_object* v___x_3026_; 
lean_dec_ref_known(v___x_3023_, 1);
v___x_3024_ = lean_box(v___x_2501_);
if (v_isShared_3006_ == 0)
{
lean_ctor_set(v___x_3005_, 0, v___x_3024_);
v___x_3026_ = v___x_3005_;
goto v_reusejp_3025_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3024_);
v___x_3026_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3025_;
}
v_reusejp_3025_:
{
lean_object* v___x_3028_; 
if (v_isShared_3012_ == 0)
{
lean_ctor_set(v___x_3011_, 1, v___x_2526_);
lean_ctor_set(v___x_3011_, 0, v___x_3026_);
v___x_3028_ = v___x_3011_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3029_; 
v_reuseFailAlloc_3029_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3029_, 0, v___x_3026_);
lean_ctor_set(v_reuseFailAlloc_3029_, 1, v___x_2526_);
v___x_3028_ = v_reuseFailAlloc_3029_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
v_a_2508_ = v___x_3028_;
goto v___jp_2507_;
}
}
}
else
{
lean_object* v_a_3031_; lean_object* v___x_3033_; uint8_t v_isShared_3034_; uint8_t v_isSharedCheck_3038_; 
lean_del_object(v___x_3011_);
lean_del_object(v___x_3005_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
v_a_3031_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3038_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3038_ == 0)
{
v___x_3033_ = v___x_3023_;
v_isShared_3034_ = v_isSharedCheck_3038_;
goto v_resetjp_3032_;
}
else
{
lean_inc(v_a_3031_);
lean_dec(v___x_3023_);
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
else
{
lean_object* v_a_3039_; lean_object* v___x_3041_; uint8_t v_isShared_3042_; uint8_t v_isSharedCheck_3046_; 
lean_del_object(v___x_3011_);
lean_del_object(v___x_3005_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_3039_ = lean_ctor_get(v___x_3021_, 0);
v_isSharedCheck_3046_ = !lean_is_exclusive(v___x_3021_);
if (v_isSharedCheck_3046_ == 0)
{
v___x_3041_ = v___x_3021_;
v_isShared_3042_ = v_isSharedCheck_3046_;
goto v_resetjp_3040_;
}
else
{
lean_inc(v_a_3039_);
lean_dec(v___x_3021_);
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
else
{
lean_object* v_a_3047_; lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3054_; 
lean_dec(v_a_3017_);
lean_del_object(v___x_3011_);
lean_del_object(v___x_3005_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_3047_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3054_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3054_ == 0)
{
v___x_3049_ = v___x_3018_;
v_isShared_3050_ = v_isSharedCheck_3054_;
goto v_resetjp_3048_;
}
else
{
lean_inc(v_a_3047_);
lean_dec(v___x_3018_);
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
else
{
lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_del_object(v___x_3011_);
lean_dec(v_fst_3008_);
lean_del_object(v___x_3005_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_3055_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3016_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3016_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
}
else
{
lean_object* v_a_3063_; lean_object* v___x_3065_; uint8_t v_isShared_3066_; uint8_t v_isSharedCheck_3070_; 
lean_del_object(v___x_3011_);
lean_dec(v_fst_3008_);
lean_del_object(v___x_3005_);
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_3063_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3070_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3070_ == 0)
{
v___x_3065_ = v___x_3013_;
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
else
{
lean_inc(v_a_3063_);
lean_dec(v___x_3013_);
v___x_3065_ = lean_box(0);
v_isShared_3066_ = v_isSharedCheck_3070_;
goto v_resetjp_3064_;
}
v_resetjp_3064_:
{
lean_object* v___x_3068_; 
if (v_isShared_3066_ == 0)
{
v___x_3068_ = v___x_3065_;
goto v_reusejp_3067_;
}
else
{
lean_object* v_reuseFailAlloc_3069_; 
v_reuseFailAlloc_3069_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3069_, 0, v_a_3063_);
v___x_3068_ = v_reuseFailAlloc_3069_;
goto v_reusejp_3067_;
}
v_reusejp_3067_:
{
return v___x_3068_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3002_);
v___y_2909_ = v___y_2955_;
v___y_2910_ = v___y_2956_;
v___y_2911_ = v___y_2957_;
v___y_2912_ = v___y_2958_;
goto v___jp_2908_;
}
}
else
{
lean_object* v_a_3073_; lean_object* v___x_3075_; uint8_t v_isShared_3076_; uint8_t v_isSharedCheck_3080_; 
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_3073_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3075_ = v___x_3001_;
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
else
{
lean_inc(v_a_3073_);
lean_dec(v___x_3001_);
v___x_3075_ = lean_box(0);
v_isShared_3076_ = v_isSharedCheck_3080_;
goto v_resetjp_3074_;
}
v_resetjp_3074_:
{
lean_object* v___x_3078_; 
if (v_isShared_3076_ == 0)
{
v___x_3078_ = v___x_3075_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3079_; 
v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
v___x_3078_ = v_reuseFailAlloc_3079_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
return v___x_3078_;
}
}
}
}
}
else
{
lean_object* v_a_3081_; lean_object* v___x_3083_; uint8_t v_isShared_3084_; uint8_t v_isSharedCheck_3088_; 
lean_dec_ref(v___x_2639_);
lean_del_object(v___x_2524_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_3081_ = lean_ctor_get(v___x_2959_, 0);
v_isSharedCheck_3088_ = !lean_is_exclusive(v___x_2959_);
if (v_isSharedCheck_3088_ == 0)
{
v___x_3083_ = v___x_2959_;
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
else
{
lean_inc(v_a_3081_);
lean_dec(v___x_2959_);
v___x_3083_ = lean_box(0);
v_isShared_3084_ = v_isSharedCheck_3088_;
goto v_resetjp_3082_;
}
v_resetjp_3082_:
{
lean_object* v___x_3086_; 
if (v_isShared_3084_ == 0)
{
v___x_3086_ = v___x_3083_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3087_; 
v_reuseFailAlloc_3087_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
v___x_3086_ = v_reuseFailAlloc_3087_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
return v___x_3086_;
}
}
}
}
}
else
{
lean_del_object(v___x_2524_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
v_a_2516_ = v___x_2567_;
goto v___jp_2515_;
}
v___jp_2527_:
{
lean_object* v___x_2532_; 
lean_inc(v_mvarId_2491_);
v___x_2532_ = l_Lean_MVarId_getType(v_mvarId_2491_, v___y_2529_, v___y_2531_, v___y_2530_, v___y_2528_);
if (lean_obj_tag(v___x_2532_) == 0)
{
lean_object* v_a_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v_a_2533_ = lean_ctor_get(v___x_2532_, 0);
lean_inc(v_a_2533_);
lean_dec_ref_known(v___x_2532_, 1);
v___x_2534_ = l_Lean_LocalDecl_toExpr(v_val_2522_);
v___x_2535_ = l_Lean_Meta_mkNoConfusion(v_a_2533_, v___x_2534_, v___y_2529_, v___y_2531_, v___y_2530_, v___y_2528_);
if (lean_obj_tag(v___x_2535_) == 0)
{
lean_object* v_a_2536_; lean_object* v___x_2537_; 
v_a_2536_ = lean_ctor_get(v___x_2535_, 0);
lean_inc(v_a_2536_);
lean_dec_ref_known(v___x_2535_, 1);
v___x_2537_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2491_, v_a_2536_, v___y_2531_);
if (lean_obj_tag(v___x_2537_) == 0)
{
lean_object* v___x_2538_; lean_object* v___x_2540_; 
lean_dec_ref_known(v___x_2537_, 1);
v___x_2538_ = lean_box(v___x_2501_);
if (v_isShared_2525_ == 0)
{
lean_ctor_set(v___x_2524_, 0, v___x_2538_);
v___x_2540_ = v___x_2524_;
goto v_reusejp_2539_;
}
else
{
lean_object* v_reuseFailAlloc_2542_; 
v_reuseFailAlloc_2542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2542_, 0, v___x_2538_);
v___x_2540_ = v_reuseFailAlloc_2542_;
goto v_reusejp_2539_;
}
v_reusejp_2539_:
{
lean_object* v___x_2541_; 
v___x_2541_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2540_);
lean_ctor_set(v___x_2541_, 1, v___x_2526_);
v_a_2508_ = v___x_2541_;
goto v___jp_2507_;
}
}
else
{
lean_object* v_a_2543_; lean_object* v___x_2545_; uint8_t v_isShared_2546_; uint8_t v_isSharedCheck_2550_; 
lean_del_object(v___x_2524_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
v_a_2543_ = lean_ctor_get(v___x_2537_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2537_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2545_ = v___x_2537_;
v_isShared_2546_ = v_isSharedCheck_2550_;
goto v_resetjp_2544_;
}
else
{
lean_inc(v_a_2543_);
lean_dec(v___x_2537_);
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
else
{
lean_object* v_a_2551_; lean_object* v___x_2553_; uint8_t v_isShared_2554_; uint8_t v_isSharedCheck_2558_; 
lean_del_object(v___x_2524_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_2551_ = lean_ctor_get(v___x_2535_, 0);
v_isSharedCheck_2558_ = !lean_is_exclusive(v___x_2535_);
if (v_isSharedCheck_2558_ == 0)
{
v___x_2553_ = v___x_2535_;
v_isShared_2554_ = v_isSharedCheck_2558_;
goto v_resetjp_2552_;
}
else
{
lean_inc(v_a_2551_);
lean_dec(v___x_2535_);
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
else
{
lean_object* v_a_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2566_; 
lean_del_object(v___x_2524_);
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
v_a_2559_ = lean_ctor_get(v___x_2532_, 0);
v_isSharedCheck_2566_ = !lean_is_exclusive(v___x_2532_);
if (v_isSharedCheck_2566_ == 0)
{
v___x_2561_ = v___x_2532_;
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_a_2559_);
lean_dec(v___x_2532_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2566_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v___x_2564_; 
if (v_isShared_2562_ == 0)
{
v___x_2564_ = v___x_2561_;
goto v_reusejp_2563_;
}
else
{
lean_object* v_reuseFailAlloc_2565_; 
v_reuseFailAlloc_2565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2565_, 0, v_a_2559_);
v___x_2564_ = v_reuseFailAlloc_2565_;
goto v_reusejp_2563_;
}
v_reusejp_2563_:
{
return v___x_2564_;
}
}
}
}
v___jp_2568_:
{
lean_object* v_searchFuel_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v_searchFuel_2573_ = lean_ctor_get(v_config_2490_, 0);
v___x_2574_ = l_Lean_LocalDecl_fvarId(v_val_2522_);
lean_dec(v_val_2522_);
lean_inc(v_searchFuel_2573_);
lean_inc(v_mvarId_2491_);
v___x_2575_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2491_, v___x_2574_, v_searchFuel_2573_, v___y_2570_, v___y_2569_, v___y_2571_, v___y_2572_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; uint8_t v___x_2577_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = lean_unbox(v_a_2576_);
lean_dec(v_a_2576_);
if (v___x_2577_ == 0)
{
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
v_a_2516_ = v___x_2567_;
goto v___jp_2515_;
}
else
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v___x_2578_ = lean_box(v___x_2501_);
v___x_2579_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2579_, 0, v___x_2578_);
v___x_2580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2526_);
v_a_2508_ = v___x_2580_;
goto v___jp_2507_;
}
}
else
{
lean_object* v_a_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2588_; 
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_2581_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2588_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2588_ == 0)
{
v___x_2583_ = v___x_2575_;
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
else
{
lean_inc(v_a_2581_);
lean_dec(v___x_2575_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2588_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2586_; 
if (v_isShared_2584_ == 0)
{
v___x_2586_ = v___x_2583_;
goto v_reusejp_2585_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_a_2581_);
v___x_2586_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2585_;
}
v_reusejp_2585_:
{
return v___x_2586_;
}
}
}
}
v___jp_2589_:
{
if (v___y_2594_ == 0)
{
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
v_a_2516_ = v___x_2567_;
goto v___jp_2515_;
}
else
{
v___y_2569_ = v___y_2590_;
v___y_2570_ = v___y_2591_;
v___y_2571_ = v___y_2592_;
v___y_2572_ = v___y_2593_;
goto v___jp_2568_;
}
}
v___jp_2596_:
{
if (v___y_2597_ == 0)
{
v___y_2569_ = v___y_2598_;
v___y_2570_ = v___y_2599_;
v___y_2571_ = v___y_2600_;
v___y_2572_ = v___y_2601_;
goto v___jp_2568_;
}
else
{
v___y_2590_ = v___y_2598_;
v___y_2591_ = v___y_2599_;
v___y_2592_ = v___y_2600_;
v___y_2593_ = v___y_2601_;
v___y_2594_ = v___x_2595_;
goto v___jp_2589_;
}
}
v___jp_2602_:
{
if (v___y_2608_ == 0)
{
v___y_2590_ = v___y_2604_;
v___y_2591_ = v___y_2605_;
v___y_2592_ = v___y_2606_;
v___y_2593_ = v___y_2607_;
v___y_2594_ = v___x_2595_;
goto v___jp_2589_;
}
else
{
v___y_2597_ = v___y_2603_;
v___y_2598_ = v___y_2604_;
v___y_2599_ = v___y_2605_;
v___y_2600_ = v___y_2606_;
v___y_2601_ = v___y_2607_;
goto v___jp_2596_;
}
}
v___jp_2609_:
{
uint8_t v_emptyType_2616_; 
v_emptyType_2616_ = lean_ctor_get_uint8(v_config_2490_, sizeof(void*)*1 + 1);
if (v_emptyType_2616_ == 0)
{
v___y_2603_ = v___y_2610_;
v___y_2604_ = v___y_2613_;
v___y_2605_ = v___y_2612_;
v___y_2606_ = v___y_2614_;
v___y_2607_ = v___y_2615_;
v___y_2608_ = v___x_2595_;
goto v___jp_2602_;
}
else
{
if (v___y_2611_ == 0)
{
v___y_2597_ = v___y_2610_;
v___y_2598_ = v___y_2613_;
v___y_2599_ = v___y_2612_;
v___y_2600_ = v___y_2614_;
v___y_2601_ = v___y_2615_;
goto v___jp_2596_;
}
else
{
v___y_2603_ = v___y_2610_;
v___y_2604_ = v___y_2613_;
v___y_2605_ = v___y_2612_;
v___y_2606_ = v___y_2614_;
v___y_2607_ = v___y_2615_;
v___y_2608_ = v___x_2595_;
goto v___jp_2602_;
}
}
}
v___jp_2617_:
{
if (v___y_2624_ == 0)
{
v___y_2610_ = v___y_2618_;
v___y_2611_ = v___y_2622_;
v___y_2612_ = v___y_2620_;
v___y_2613_ = v___y_2619_;
v___y_2614_ = v___y_2621_;
v___y_2615_ = v___y_2623_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2625_; 
lean_inc(v_val_2522_);
lean_inc(v_mvarId_2491_);
v___x_2625_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2491_, v_val_2522_, v___y_2620_, v___y_2619_, v___y_2621_, v___y_2623_);
if (lean_obj_tag(v___x_2625_) == 0)
{
lean_object* v_a_2626_; uint8_t v___x_2627_; 
v_a_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_a_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v___x_2627_ = lean_unbox(v_a_2626_);
lean_dec(v_a_2626_);
if (v___x_2627_ == 0)
{
v___y_2610_ = v___y_2618_;
v___y_2611_ = v___y_2622_;
v___y_2612_ = v___y_2620_;
v___y_2613_ = v___y_2619_;
v___y_2614_ = v___y_2621_;
v___y_2615_ = v___y_2623_;
goto v___jp_2609_;
}
else
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; 
lean_dec(v_val_2522_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v___x_2628_ = lean_box(v___x_2501_);
v___x_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2629_, 0, v___x_2628_);
v___x_2630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
lean_ctor_set(v___x_2630_, 1, v___x_2526_);
v_a_2508_ = v___x_2630_;
goto v___jp_2507_;
}
}
else
{
lean_object* v_a_2631_; lean_object* v___x_2633_; uint8_t v_isShared_2634_; uint8_t v_isSharedCheck_2638_; 
lean_dec(v_val_2522_);
lean_del_object(v___x_2505_);
lean_dec(v_snd_2503_);
lean_dec(v_mvarId_2491_);
lean_dec_ref(v_config_2490_);
v_a_2631_ = lean_ctor_get(v___x_2625_, 0);
v_isSharedCheck_2638_ = !lean_is_exclusive(v___x_2625_);
if (v_isSharedCheck_2638_ == 0)
{
v___x_2633_ = v___x_2625_;
v_isShared_2634_ = v_isSharedCheck_2638_;
goto v_resetjp_2632_;
}
else
{
lean_inc(v_a_2631_);
lean_dec(v___x_2625_);
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
}
}
v___jp_2507_:
{
lean_object* v___x_2509_; lean_object* v___x_2511_; 
v___x_2509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2509_, 0, v_a_2508_);
if (v_isShared_2506_ == 0)
{
lean_ctor_set(v___x_2505_, 0, v___x_2509_);
v___x_2511_ = v___x_2505_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2513_, 1, v_snd_2503_);
v___x_2511_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
return v___x_2512_;
}
}
v___jp_2515_:
{
lean_object* v___x_2517_; size_t v___x_2518_; size_t v___x_2519_; lean_object* v___x_2520_; 
v___x_2517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2514_);
lean_ctor_set(v___x_2517_, 1, v_a_2516_);
v___x_2518_ = ((size_t)1ULL);
v___x_2519_ = lean_usize_add(v_i_2494_, v___x_2518_);
v___x_2520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2490_, v_mvarId_2491_, v_as_2492_, v_sz_2493_, v___x_2519_, v___x_2517_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_);
return v___x_2520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3155_, lean_object* v_mvarId_3156_, lean_object* v_as_3157_, lean_object* v_sz_3158_, lean_object* v_i_3159_, lean_object* v_b_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
size_t v_sz_boxed_3166_; size_t v_i_boxed_3167_; lean_object* v_res_3168_; 
v_sz_boxed_3166_ = lean_unbox_usize(v_sz_3158_);
lean_dec(v_sz_3158_);
v_i_boxed_3167_ = lean_unbox_usize(v_i_3159_);
lean_dec(v_i_3159_);
v_res_3168_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3155_, v_mvarId_3156_, v_as_3157_, v_sz_boxed_3166_, v_i_boxed_3167_, v_b_3160_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec_ref(v_as_3157_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3172_, lean_object* v_mvarId_3173_, lean_object* v_as_3174_, size_t v_sz_3175_, size_t v_i_3176_, lean_object* v_b_3177_, lean_object* v___y_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_){
_start:
{
uint8_t v___x_3183_; 
v___x_3183_ = lean_usize_dec_lt(v_i_3176_, v_sz_3175_);
if (v___x_3183_ == 0)
{
lean_object* v___x_3184_; 
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v___x_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3184_, 0, v_b_3177_);
return v___x_3184_;
}
else
{
lean_object* v_snd_3185_; lean_object* v___x_3187_; uint8_t v_isShared_3188_; uint8_t v_isSharedCheck_3855_; 
v_snd_3185_ = lean_ctor_get(v_b_3177_, 1);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_b_3177_);
if (v_isSharedCheck_3855_ == 0)
{
lean_object* v_unused_3856_; 
v_unused_3856_ = lean_ctor_get(v_b_3177_, 0);
lean_dec(v_unused_3856_);
v___x_3187_ = v_b_3177_;
v_isShared_3188_ = v_isSharedCheck_3855_;
goto v_resetjp_3186_;
}
else
{
lean_inc(v_snd_3185_);
lean_dec(v_b_3177_);
v___x_3187_ = lean_box(0);
v_isShared_3188_ = v_isSharedCheck_3855_;
goto v_resetjp_3186_;
}
v_resetjp_3186_:
{
lean_object* v_a_3190_; lean_object* v___x_3196_; lean_object* v_a_3198_; lean_object* v_a_3203_; 
v___x_3196_ = lean_box(0);
v_a_3203_ = lean_array_uget(v_as_3174_, v_i_3176_);
if (lean_obj_tag(v_a_3203_) == 0)
{
lean_del_object(v___x_3187_);
v_a_3198_ = v_snd_3185_;
goto v___jp_3197_;
}
else
{
lean_object* v_val_3204_; lean_object* v___x_3206_; uint8_t v_isShared_3207_; uint8_t v_isSharedCheck_3854_; 
v_val_3204_ = lean_ctor_get(v_a_3203_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v_a_3203_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3206_ = v_a_3203_;
v_isShared_3207_ = v_isSharedCheck_3854_;
goto v_resetjp_3205_;
}
else
{
lean_inc(v_val_3204_);
lean_dec(v_a_3203_);
v___x_3206_ = lean_box(0);
v_isShared_3207_ = v_isSharedCheck_3854_;
goto v_resetjp_3205_;
}
v_resetjp_3205_:
{
lean_object* v___x_3208_; lean_object* v___y_3210_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___x_3250_; lean_object* v___y_3252_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3274_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; uint8_t v___y_3278_; uint8_t v___x_3279_; uint8_t v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; uint8_t v___y_3287_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; uint8_t v___y_3292_; uint8_t v___y_3294_; uint8_t v___y_3295_; lean_object* v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3302_; uint8_t v___y_3303_; uint8_t v___y_3304_; lean_object* v___y_3305_; lean_object* v___y_3306_; lean_object* v___y_3307_; uint8_t v___y_3308_; 
v___x_3208_ = lean_box(0);
v___x_3250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3279_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3204_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3324_; uint8_t v___y_3326_; uint8_t v___y_3327_; lean_object* v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; uint8_t v___y_3335_; uint8_t v___y_3336_; lean_object* v___y_3337_; lean_object* v___y_3338_; lean_object* v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; uint8_t v___y_3342_; uint8_t v___y_3345_; uint8_t v___y_3346_; lean_object* v___y_3347_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; lean_object* v_a_3351_; lean_object* v___y_3355_; uint8_t v___y_3356_; uint8_t v___y_3357_; lean_object* v___y_3358_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; uint8_t v___y_3406_; uint8_t v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; uint8_t v___y_3435_; uint8_t v___y_3436_; lean_object* v___y_3437_; lean_object* v___y_3438_; lean_object* v___y_3439_; lean_object* v___y_3440_; uint8_t v___y_3441_; uint8_t v___y_3443_; uint8_t v___y_3444_; lean_object* v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; uint8_t v___y_3450_; uint8_t v___y_3453_; uint8_t v___y_3454_; lean_object* v___y_3455_; lean_object* v___y_3456_; lean_object* v___y_3457_; lean_object* v___y_3458_; uint8_t v___y_3459_; uint8_t v___y_3472_; uint8_t v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3476_; lean_object* v___y_3477_; uint8_t v___y_3478_; uint8_t v___y_3480_; uint8_t v_isHEq_3481_; lean_object* v___y_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3489_; lean_object* v___y_3490_; uint8_t v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; uint8_t v_isEq_3552_; lean_object* v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3648_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___x_3784_; 
v___x_3324_ = l_Lean_LocalDecl_type(v_val_3204_);
lean_inc_ref(v___x_3324_);
v___x_3784_ = l_Lean_Meta_matchNot_x3f(v___x_3324_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3784_) == 0)
{
lean_object* v_a_3785_; 
v_a_3785_ = lean_ctor_get(v___x_3784_, 0);
lean_inc(v_a_3785_);
lean_dec_ref_known(v___x_3784_, 1);
if (lean_obj_tag(v_a_3785_) == 1)
{
lean_object* v_val_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3845_; 
v_val_3786_ = lean_ctor_get(v_a_3785_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v_a_3785_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3788_ = v_a_3785_;
v_isShared_3789_ = v_isSharedCheck_3845_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_val_3786_);
lean_dec(v_a_3785_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3845_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3790_; 
v___x_3790_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3786_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3790_) == 0)
{
lean_object* v_a_3791_; 
v_a_3791_ = lean_ctor_get(v___x_3790_, 0);
lean_inc(v_a_3791_);
lean_dec_ref_known(v___x_3790_, 1);
if (lean_obj_tag(v_a_3791_) == 1)
{
lean_object* v_val_3792_; lean_object* v___x_3794_; uint8_t v_isShared_3795_; uint8_t v_isSharedCheck_3836_; 
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec_ref(v_config_3172_);
v_val_3792_ = lean_ctor_get(v_a_3791_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v_a_3791_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3794_ = v_a_3791_;
v_isShared_3795_ = v_isSharedCheck_3836_;
goto v_resetjp_3793_;
}
else
{
lean_inc(v_val_3792_);
lean_dec(v_a_3791_);
v___x_3794_ = lean_box(0);
v_isShared_3795_ = v_isSharedCheck_3836_;
goto v_resetjp_3793_;
}
v_resetjp_3793_:
{
lean_object* v___x_3796_; 
lean_inc(v_mvarId_3173_);
v___x_3796_ = l_Lean_MVarId_getType(v_mvarId_3173_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3796_) == 0)
{
lean_object* v_a_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; 
v_a_3797_ = lean_ctor_get(v___x_3796_, 0);
lean_inc(v_a_3797_);
lean_dec_ref_known(v___x_3796_, 1);
v___x_3798_ = l_Lean_LocalDecl_toExpr(v_val_3204_);
v___x_3799_ = l_Lean_mkFVar(v_val_3792_);
v___x_3800_ = l_Lean_Expr_app___override(v___x_3798_, v___x_3799_);
v___x_3801_ = l_Lean_Meta_mkFalseElim(v_a_3797_, v___x_3800_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3803_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
lean_inc(v_a_3802_);
lean_dec_ref_known(v___x_3801_, 1);
v___x_3803_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3173_, v_a_3802_, v___y_3179_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v___x_3804_; lean_object* v___x_3806_; 
lean_dec_ref_known(v___x_3803_, 1);
v___x_3804_ = lean_box(v___x_3183_);
if (v_isShared_3795_ == 0)
{
lean_ctor_set(v___x_3794_, 0, v___x_3804_);
v___x_3806_ = v___x_3794_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3804_);
v___x_3806_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3807_, 0, v___x_3806_);
lean_ctor_set(v___x_3807_, 1, v___x_3208_);
if (v_isShared_3789_ == 0)
{
lean_ctor_set_tag(v___x_3788_, 0);
lean_ctor_set(v___x_3788_, 0, v___x_3807_);
v___x_3809_ = v___x_3788_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
v_a_3190_ = v___x_3809_;
goto v___jp_3189_;
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v___x_3814_; uint8_t v_isShared_3815_; uint8_t v_isSharedCheck_3819_; 
lean_del_object(v___x_3794_);
lean_del_object(v___x_3788_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
v_a_3812_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3819_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3819_ == 0)
{
v___x_3814_ = v___x_3803_;
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
else
{
lean_inc(v_a_3812_);
lean_dec(v___x_3803_);
v___x_3814_ = lean_box(0);
v_isShared_3815_ = v_isSharedCheck_3819_;
goto v_resetjp_3813_;
}
v_resetjp_3813_:
{
lean_object* v___x_3817_; 
if (v_isShared_3815_ == 0)
{
v___x_3817_ = v___x_3814_;
goto v_reusejp_3816_;
}
else
{
lean_object* v_reuseFailAlloc_3818_; 
v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3812_);
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
lean_del_object(v___x_3794_);
lean_del_object(v___x_3788_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3820_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3827_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3827_ == 0)
{
v___x_3822_ = v___x_3801_;
v_isShared_3823_ = v_isSharedCheck_3827_;
goto v_resetjp_3821_;
}
else
{
lean_inc(v_a_3820_);
lean_dec(v___x_3801_);
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
else
{
lean_object* v_a_3828_; lean_object* v___x_3830_; uint8_t v_isShared_3831_; uint8_t v_isSharedCheck_3835_; 
lean_del_object(v___x_3794_);
lean_dec(v_val_3792_);
lean_del_object(v___x_3788_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3828_ = lean_ctor_get(v___x_3796_, 0);
v_isSharedCheck_3835_ = !lean_is_exclusive(v___x_3796_);
if (v_isSharedCheck_3835_ == 0)
{
v___x_3830_ = v___x_3796_;
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
else
{
lean_inc(v_a_3828_);
lean_dec(v___x_3796_);
v___x_3830_ = lean_box(0);
v_isShared_3831_ = v_isSharedCheck_3835_;
goto v_resetjp_3829_;
}
v_resetjp_3829_:
{
lean_object* v___x_3833_; 
if (v_isShared_3831_ == 0)
{
v___x_3833_ = v___x_3830_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v_a_3828_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
return v___x_3833_;
}
}
}
}
}
else
{
lean_dec(v_a_3791_);
lean_del_object(v___x_3788_);
v___y_3648_ = v___y_3178_;
v___y_3649_ = v___y_3179_;
v___y_3650_ = v___y_3180_;
v___y_3651_ = v___y_3181_;
goto v___jp_3647_;
}
}
else
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3844_; 
lean_del_object(v___x_3788_);
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3837_ = lean_ctor_get(v___x_3790_, 0);
v_isSharedCheck_3844_ = !lean_is_exclusive(v___x_3790_);
if (v_isSharedCheck_3844_ == 0)
{
v___x_3839_ = v___x_3790_;
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3790_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3844_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
lean_object* v___x_3842_; 
if (v_isShared_3840_ == 0)
{
v___x_3842_ = v___x_3839_;
goto v_reusejp_3841_;
}
else
{
lean_object* v_reuseFailAlloc_3843_; 
v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
v___x_3842_ = v_reuseFailAlloc_3843_;
goto v_reusejp_3841_;
}
v_reusejp_3841_:
{
return v___x_3842_;
}
}
}
}
}
else
{
lean_dec(v_a_3785_);
v___y_3648_ = v___y_3178_;
v___y_3649_ = v___y_3179_;
v___y_3650_ = v___y_3180_;
v___y_3651_ = v___y_3181_;
goto v___jp_3647_;
}
}
else
{
lean_object* v_a_3846_; lean_object* v___x_3848_; uint8_t v_isShared_3849_; uint8_t v_isSharedCheck_3853_; 
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3846_ = lean_ctor_get(v___x_3784_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v___x_3784_);
if (v_isSharedCheck_3853_ == 0)
{
v___x_3848_ = v___x_3784_;
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
else
{
lean_inc(v_a_3846_);
lean_dec(v___x_3784_);
v___x_3848_ = lean_box(0);
v_isShared_3849_ = v_isSharedCheck_3853_;
goto v_resetjp_3847_;
}
v_resetjp_3847_:
{
lean_object* v___x_3851_; 
if (v_isShared_3849_ == 0)
{
v___x_3851_ = v___x_3848_;
goto v_reusejp_3850_;
}
else
{
lean_object* v_reuseFailAlloc_3852_; 
v_reuseFailAlloc_3852_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3852_, 0, v_a_3846_);
v___x_3851_ = v_reuseFailAlloc_3852_;
goto v_reusejp_3850_;
}
v_reusejp_3850_:
{
return v___x_3851_;
}
}
}
v___jp_3325_:
{
uint8_t v_genDiseq_3332_; 
v_genDiseq_3332_ = lean_ctor_get_uint8(v_config_3172_, sizeof(void*)*1 + 2);
if (v_genDiseq_3332_ == 0)
{
lean_dec_ref(v___x_3324_);
v___y_3302_ = v___y_3329_;
v___y_3303_ = v___y_3327_;
v___y_3304_ = v___y_3326_;
v___y_3305_ = v___y_3330_;
v___y_3306_ = v___y_3328_;
v___y_3307_ = v___y_3331_;
v___y_3308_ = v___x_3279_;
goto v___jp_3301_;
}
else
{
uint8_t v___x_3333_; 
v___x_3333_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3324_);
v___y_3302_ = v___y_3329_;
v___y_3303_ = v___y_3327_;
v___y_3304_ = v___y_3326_;
v___y_3305_ = v___y_3330_;
v___y_3306_ = v___y_3328_;
v___y_3307_ = v___y_3331_;
v___y_3308_ = v___x_3333_;
goto v___jp_3301_;
}
}
v___jp_3334_:
{
if (v___y_3342_ == 0)
{
lean_dec_ref(v___y_3339_);
v___y_3326_ = v___y_3336_;
v___y_3327_ = v___y_3335_;
v___y_3328_ = v___y_3341_;
v___y_3329_ = v___y_3338_;
v___y_3330_ = v___y_3337_;
v___y_3331_ = v___y_3340_;
goto v___jp_3325_;
}
else
{
lean_object* v___x_3343_; 
lean_dec_ref(v___x_3324_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v___x_3343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3343_, 0, v___y_3339_);
return v___x_3343_;
}
}
v___jp_3344_:
{
uint8_t v___x_3352_; 
v___x_3352_ = l_Lean_Exception_isInterrupt(v_a_3351_);
if (v___x_3352_ == 0)
{
uint8_t v___x_3353_; 
lean_inc_ref(v_a_3351_);
v___x_3353_ = l_Lean_Exception_isRuntime(v_a_3351_);
v___y_3335_ = v___y_3346_;
v___y_3336_ = v___y_3345_;
v___y_3337_ = v___y_3348_;
v___y_3338_ = v___y_3347_;
v___y_3339_ = v_a_3351_;
v___y_3340_ = v___y_3349_;
v___y_3341_ = v___y_3350_;
v___y_3342_ = v___x_3353_;
goto v___jp_3334_;
}
else
{
v___y_3335_ = v___y_3346_;
v___y_3336_ = v___y_3345_;
v___y_3337_ = v___y_3348_;
v___y_3338_ = v___y_3347_;
v___y_3339_ = v_a_3351_;
v___y_3340_ = v___y_3349_;
v___y_3341_ = v___y_3350_;
v___y_3342_ = v___x_3352_;
goto v___jp_3334_;
}
}
v___jp_3354_:
{
if (lean_obj_tag(v___y_3362_) == 0)
{
lean_object* v_a_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v_a_3363_ = lean_ctor_get(v___y_3362_, 0);
lean_inc(v_a_3363_);
lean_dec_ref_known(v___y_3362_, 1);
v___x_3364_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3365_ = l_Lean_Expr_isConstOf(v_a_3363_, v___x_3364_);
lean_dec(v_a_3363_);
if (v___x_3365_ == 0)
{
lean_dec_ref(v___y_3355_);
v___y_3326_ = v___y_3357_;
v___y_3327_ = v___y_3356_;
v___y_3328_ = v___y_3361_;
v___y_3329_ = v___y_3359_;
v___y_3330_ = v___y_3358_;
v___y_3331_ = v___y_3360_;
goto v___jp_3325_;
}
else
{
lean_object* v___x_3366_; 
lean_inc_ref(v___y_3355_);
v___x_3366_ = l_Lean_Meta_mkEqRefl(v___y_3355_, v___y_3361_, v___y_3359_, v___y_3358_, v___y_3360_);
if (lean_obj_tag(v___x_3366_) == 0)
{
lean_object* v_a_3367_; lean_object* v___x_3368_; lean_object* v_dummy_3369_; lean_object* v_nargs_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_a_3367_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3367_);
lean_dec_ref_known(v___x_3366_, 1);
v___x_3368_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3369_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3370_ = l_Lean_Expr_getAppNumArgs(v___y_3355_);
lean_inc(v_nargs_3370_);
v___x_3371_ = lean_mk_array(v_nargs_3370_, v_dummy_3369_);
v___x_3372_ = lean_unsigned_to_nat(1u);
v___x_3373_ = lean_nat_sub(v_nargs_3370_, v___x_3372_);
lean_dec(v_nargs_3370_);
v___x_3374_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3355_, v___x_3371_, v___x_3373_);
v___x_3375_ = lean_array_push(v___x_3374_, v_a_3367_);
v___x_3376_ = l_Lean_mkAppN(v___x_3368_, v___x_3375_);
lean_dec_ref(v___x_3375_);
lean_inc(v_mvarId_3173_);
v___x_3377_ = l_Lean_MVarId_getType(v_mvarId_3173_, v___y_3361_, v___y_3359_, v___y_3358_, v___y_3360_);
if (lean_obj_tag(v___x_3377_) == 0)
{
lean_object* v_a_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; 
v_a_3378_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3378_);
lean_dec_ref_known(v___x_3377_, 1);
lean_inc(v_val_3204_);
v___x_3379_ = l_Lean_LocalDecl_toExpr(v_val_3204_);
v___x_3380_ = l_Lean_Meta_mkAbsurd(v_a_3378_, v___x_3379_, v___x_3376_, v___y_3361_, v___y_3359_, v___y_3358_, v___y_3360_);
if (lean_obj_tag(v___x_3380_) == 0)
{
lean_object* v_a_3381_; lean_object* v___x_3383_; uint8_t v_isShared_3384_; uint8_t v_isSharedCheck_3400_; 
v_a_3381_ = lean_ctor_get(v___x_3380_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v___x_3380_);
if (v_isSharedCheck_3400_ == 0)
{
v___x_3383_ = v___x_3380_;
v_isShared_3384_ = v_isSharedCheck_3400_;
goto v_resetjp_3382_;
}
else
{
lean_inc(v_a_3381_);
lean_dec(v___x_3380_);
v___x_3383_ = lean_box(0);
v_isShared_3384_ = v_isSharedCheck_3400_;
goto v_resetjp_3382_;
}
v_resetjp_3382_:
{
lean_object* v___x_3385_; 
lean_inc(v_mvarId_3173_);
v___x_3385_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3173_, v_a_3381_, v___y_3359_);
if (lean_obj_tag(v___x_3385_) == 0)
{
lean_object* v___x_3387_; uint8_t v_isShared_3388_; uint8_t v_isSharedCheck_3397_; 
lean_dec_ref(v___x_3324_);
lean_dec(v_val_3204_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_isSharedCheck_3397_ = !lean_is_exclusive(v___x_3385_);
if (v_isSharedCheck_3397_ == 0)
{
lean_object* v_unused_3398_; 
v_unused_3398_ = lean_ctor_get(v___x_3385_, 0);
lean_dec(v_unused_3398_);
v___x_3387_ = v___x_3385_;
v_isShared_3388_ = v_isSharedCheck_3397_;
goto v_resetjp_3386_;
}
else
{
lean_dec(v___x_3385_);
v___x_3387_ = lean_box(0);
v_isShared_3388_ = v_isSharedCheck_3397_;
goto v_resetjp_3386_;
}
v_resetjp_3386_:
{
lean_object* v___x_3389_; lean_object* v___x_3391_; 
v___x_3389_ = lean_box(v___x_3183_);
if (v_isShared_3388_ == 0)
{
lean_ctor_set_tag(v___x_3387_, 1);
lean_ctor_set(v___x_3387_, 0, v___x_3389_);
v___x_3391_ = v___x_3387_;
goto v_reusejp_3390_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3389_);
v___x_3391_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3390_;
}
v_reusejp_3390_:
{
lean_object* v___x_3392_; lean_object* v___x_3394_; 
v___x_3392_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3392_, 0, v___x_3391_);
lean_ctor_set(v___x_3392_, 1, v___x_3208_);
if (v_isShared_3384_ == 0)
{
lean_ctor_set(v___x_3383_, 0, v___x_3392_);
v___x_3394_ = v___x_3383_;
goto v_reusejp_3393_;
}
else
{
lean_object* v_reuseFailAlloc_3395_; 
v_reuseFailAlloc_3395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3395_, 0, v___x_3392_);
v___x_3394_ = v_reuseFailAlloc_3395_;
goto v_reusejp_3393_;
}
v_reusejp_3393_:
{
v_a_3190_ = v___x_3394_;
goto v___jp_3189_;
}
}
}
}
else
{
lean_object* v_a_3399_; 
lean_del_object(v___x_3383_);
v_a_3399_ = lean_ctor_get(v___x_3385_, 0);
lean_inc(v_a_3399_);
lean_dec_ref_known(v___x_3385_, 1);
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3358_;
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3361_;
v_a_3351_ = v_a_3399_;
goto v___jp_3344_;
}
}
}
else
{
lean_object* v_a_3401_; 
v_a_3401_ = lean_ctor_get(v___x_3380_, 0);
lean_inc(v_a_3401_);
lean_dec_ref_known(v___x_3380_, 1);
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3358_;
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3361_;
v_a_3351_ = v_a_3401_;
goto v___jp_3344_;
}
}
else
{
lean_object* v_a_3402_; 
lean_dec_ref(v___x_3376_);
v_a_3402_ = lean_ctor_get(v___x_3377_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3377_, 1);
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3358_;
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3361_;
v_a_3351_ = v_a_3402_;
goto v___jp_3344_;
}
}
else
{
lean_object* v_a_3403_; 
lean_dec_ref(v___y_3355_);
v_a_3403_ = lean_ctor_get(v___x_3366_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3366_, 1);
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3358_;
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3361_;
v_a_3351_ = v_a_3403_;
goto v___jp_3344_;
}
}
}
else
{
lean_object* v_a_3404_; 
lean_dec_ref(v___y_3355_);
v_a_3404_ = lean_ctor_get(v___y_3362_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___y_3362_, 1);
v___y_3345_ = v___y_3357_;
v___y_3346_ = v___y_3356_;
v___y_3347_ = v___y_3359_;
v___y_3348_ = v___y_3358_;
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3361_;
v_a_3351_ = v_a_3404_;
goto v___jp_3344_;
}
}
v___jp_3405_:
{
lean_object* v___x_3412_; 
lean_inc_ref(v___x_3324_);
v___x_3412_ = l_Lean_Meta_mkDecide(v___x_3324_, v___y_3411_, v___y_3409_, v___y_3408_, v___y_3410_);
if (lean_obj_tag(v___x_3412_) == 0)
{
lean_object* v_a_3413_; lean_object* v___x_3414_; uint8_t v_transparency_3415_; uint8_t v___x_3416_; uint8_t v___x_3417_; 
v_a_3413_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3413_);
lean_dec_ref_known(v___x_3412_, 1);
v___x_3414_ = l_Lean_Meta_Context_config(v___y_3411_);
v_transparency_3415_ = lean_ctor_get_uint8(v___x_3414_, 9);
lean_dec_ref(v___x_3414_);
v___x_3416_ = 1;
v___x_3417_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3415_, v___x_3416_);
if (v___x_3417_ == 0)
{
lean_object* v_keyedConfig_3418_; uint8_t v_trackZetaDelta_3419_; lean_object* v_zetaDeltaSet_3420_; lean_object* v_lctx_3421_; lean_object* v_localInstances_3422_; lean_object* v_defEqCtx_x3f_3423_; lean_object* v_synthPendingDepth_3424_; lean_object* v_customCanUnfoldPredicate_x3f_3425_; uint8_t v_univApprox_3426_; uint8_t v_inTypeClassResolution_3427_; uint8_t v_cacheInferType_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v_keyedConfig_3418_ = lean_ctor_get(v___y_3411_, 0);
v_trackZetaDelta_3419_ = lean_ctor_get_uint8(v___y_3411_, sizeof(void*)*7);
v_zetaDeltaSet_3420_ = lean_ctor_get(v___y_3411_, 1);
v_lctx_3421_ = lean_ctor_get(v___y_3411_, 2);
v_localInstances_3422_ = lean_ctor_get(v___y_3411_, 3);
v_defEqCtx_x3f_3423_ = lean_ctor_get(v___y_3411_, 4);
v_synthPendingDepth_3424_ = lean_ctor_get(v___y_3411_, 5);
v_customCanUnfoldPredicate_x3f_3425_ = lean_ctor_get(v___y_3411_, 6);
v_univApprox_3426_ = lean_ctor_get_uint8(v___y_3411_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3427_ = lean_ctor_get_uint8(v___y_3411_, sizeof(void*)*7 + 2);
v_cacheInferType_3428_ = lean_ctor_get_uint8(v___y_3411_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3418_);
v___x_3429_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3416_, v_keyedConfig_3418_);
lean_inc(v_customCanUnfoldPredicate_x3f_3425_);
lean_inc(v_synthPendingDepth_3424_);
lean_inc(v_defEqCtx_x3f_3423_);
lean_inc_ref(v_localInstances_3422_);
lean_inc_ref(v_lctx_3421_);
lean_inc(v_zetaDeltaSet_3420_);
v___x_3430_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
lean_ctor_set(v___x_3430_, 1, v_zetaDeltaSet_3420_);
lean_ctor_set(v___x_3430_, 2, v_lctx_3421_);
lean_ctor_set(v___x_3430_, 3, v_localInstances_3422_);
lean_ctor_set(v___x_3430_, 4, v_defEqCtx_x3f_3423_);
lean_ctor_set(v___x_3430_, 5, v_synthPendingDepth_3424_);
lean_ctor_set(v___x_3430_, 6, v_customCanUnfoldPredicate_x3f_3425_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*7, v_trackZetaDelta_3419_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*7 + 1, v_univApprox_3426_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3427_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*7 + 3, v_cacheInferType_3428_);
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3408_);
lean_inc(v___y_3409_);
lean_inc(v_a_3413_);
v___x_3431_ = lean_whnf(v_a_3413_, v___x_3430_, v___y_3409_, v___y_3408_, v___y_3410_);
v___y_3355_ = v_a_3413_;
v___y_3356_ = v___y_3407_;
v___y_3357_ = v___y_3406_;
v___y_3358_ = v___y_3408_;
v___y_3359_ = v___y_3409_;
v___y_3360_ = v___y_3410_;
v___y_3361_ = v___y_3411_;
v___y_3362_ = v___x_3431_;
goto v___jp_3354_;
}
else
{
lean_object* v___x_3432_; 
lean_inc(v___y_3410_);
lean_inc_ref(v___y_3408_);
lean_inc(v___y_3409_);
lean_inc_ref(v___y_3411_);
lean_inc(v_a_3413_);
v___x_3432_ = lean_whnf(v_a_3413_, v___y_3411_, v___y_3409_, v___y_3408_, v___y_3410_);
v___y_3355_ = v_a_3413_;
v___y_3356_ = v___y_3407_;
v___y_3357_ = v___y_3406_;
v___y_3358_ = v___y_3408_;
v___y_3359_ = v___y_3409_;
v___y_3360_ = v___y_3410_;
v___y_3361_ = v___y_3411_;
v___y_3362_ = v___x_3432_;
goto v___jp_3354_;
}
}
else
{
lean_object* v_a_3433_; 
v_a_3433_ = lean_ctor_get(v___x_3412_, 0);
lean_inc(v_a_3433_);
lean_dec_ref_known(v___x_3412_, 1);
v___y_3345_ = v___y_3406_;
v___y_3346_ = v___y_3407_;
v___y_3347_ = v___y_3409_;
v___y_3348_ = v___y_3408_;
v___y_3349_ = v___y_3410_;
v___y_3350_ = v___y_3411_;
v_a_3351_ = v_a_3433_;
goto v___jp_3344_;
}
}
v___jp_3434_:
{
if (v___y_3441_ == 0)
{
v___y_3326_ = v___y_3436_;
v___y_3327_ = v___y_3435_;
v___y_3328_ = v___y_3440_;
v___y_3329_ = v___y_3438_;
v___y_3330_ = v___y_3437_;
v___y_3331_ = v___y_3439_;
goto v___jp_3325_;
}
else
{
v___y_3406_ = v___y_3436_;
v___y_3407_ = v___y_3435_;
v___y_3408_ = v___y_3437_;
v___y_3409_ = v___y_3438_;
v___y_3410_ = v___y_3439_;
v___y_3411_ = v___y_3440_;
goto v___jp_3405_;
}
}
v___jp_3442_:
{
if (v___y_3450_ == 0)
{
lean_dec_ref(v___y_3448_);
v___y_3435_ = v___y_3444_;
v___y_3436_ = v___y_3443_;
v___y_3437_ = v___y_3446_;
v___y_3438_ = v___y_3445_;
v___y_3439_ = v___y_3447_;
v___y_3440_ = v___y_3449_;
v___y_3441_ = v___x_3279_;
goto v___jp_3434_;
}
else
{
uint8_t v___x_3451_; 
v___x_3451_ = l_Lean_Expr_hasFVar(v___y_3448_);
lean_dec_ref(v___y_3448_);
if (v___x_3451_ == 0)
{
v___y_3406_ = v___y_3443_;
v___y_3407_ = v___y_3444_;
v___y_3408_ = v___y_3446_;
v___y_3409_ = v___y_3445_;
v___y_3410_ = v___y_3447_;
v___y_3411_ = v___y_3449_;
goto v___jp_3405_;
}
else
{
v___y_3435_ = v___y_3444_;
v___y_3436_ = v___y_3443_;
v___y_3437_ = v___y_3446_;
v___y_3438_ = v___y_3445_;
v___y_3439_ = v___y_3447_;
v___y_3440_ = v___y_3449_;
v___y_3441_ = v___x_3279_;
goto v___jp_3434_;
}
}
}
v___jp_3452_:
{
lean_object* v___x_3460_; 
lean_inc_ref(v___x_3324_);
v___x_3460_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3324_, v___y_3456_);
if (lean_obj_tag(v___x_3460_) == 0)
{
lean_object* v_a_3461_; uint8_t v___x_3462_; 
v_a_3461_ = lean_ctor_get(v___x_3460_, 0);
lean_inc(v_a_3461_);
lean_dec_ref_known(v___x_3460_, 1);
v___x_3462_ = l_Lean_Expr_hasMVar(v_a_3461_);
if (v___x_3462_ == 0)
{
v___y_3443_ = v___y_3454_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3456_;
v___y_3446_ = v___y_3455_;
v___y_3447_ = v___y_3457_;
v___y_3448_ = v_a_3461_;
v___y_3449_ = v___y_3458_;
v___y_3450_ = v___y_3459_;
goto v___jp_3442_;
}
else
{
v___y_3443_ = v___y_3454_;
v___y_3444_ = v___y_3453_;
v___y_3445_ = v___y_3456_;
v___y_3446_ = v___y_3455_;
v___y_3447_ = v___y_3457_;
v___y_3448_ = v_a_3461_;
v___y_3449_ = v___y_3458_;
v___y_3450_ = v___x_3279_;
goto v___jp_3442_;
}
}
else
{
lean_object* v_a_3463_; lean_object* v___x_3465_; uint8_t v_isShared_3466_; uint8_t v_isSharedCheck_3470_; 
lean_dec_ref(v___x_3324_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3463_ = lean_ctor_get(v___x_3460_, 0);
v_isSharedCheck_3470_ = !lean_is_exclusive(v___x_3460_);
if (v_isSharedCheck_3470_ == 0)
{
v___x_3465_ = v___x_3460_;
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
else
{
lean_inc(v_a_3463_);
lean_dec(v___x_3460_);
v___x_3465_ = lean_box(0);
v_isShared_3466_ = v_isSharedCheck_3470_;
goto v_resetjp_3464_;
}
v_resetjp_3464_:
{
lean_object* v___x_3468_; 
if (v_isShared_3466_ == 0)
{
v___x_3468_ = v___x_3465_;
goto v_reusejp_3467_;
}
else
{
lean_object* v_reuseFailAlloc_3469_; 
v_reuseFailAlloc_3469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3469_, 0, v_a_3463_);
v___x_3468_ = v_reuseFailAlloc_3469_;
goto v_reusejp_3467_;
}
v_reusejp_3467_:
{
return v___x_3468_;
}
}
}
}
v___jp_3471_:
{
if (v___y_3478_ == 0)
{
v___y_3326_ = v___y_3473_;
v___y_3327_ = v___y_3472_;
v___y_3328_ = v___y_3477_;
v___y_3329_ = v___y_3475_;
v___y_3330_ = v___y_3474_;
v___y_3331_ = v___y_3476_;
goto v___jp_3325_;
}
else
{
v___y_3453_ = v___y_3472_;
v___y_3454_ = v___y_3473_;
v___y_3455_ = v___y_3474_;
v___y_3456_ = v___y_3475_;
v___y_3457_ = v___y_3476_;
v___y_3458_ = v___y_3477_;
v___y_3459_ = v___y_3478_;
goto v___jp_3452_;
}
}
v___jp_3479_:
{
uint8_t v_useDecide_3486_; 
v_useDecide_3486_ = lean_ctor_get_uint8(v_config_3172_, sizeof(void*)*1);
if (v_useDecide_3486_ == 0)
{
v___y_3472_ = v_isHEq_3481_;
v___y_3473_ = v___y_3480_;
v___y_3474_ = v___y_3484_;
v___y_3475_ = v___y_3483_;
v___y_3476_ = v___y_3485_;
v___y_3477_ = v___y_3482_;
v___y_3478_ = v___x_3279_;
goto v___jp_3471_;
}
else
{
uint8_t v___x_3487_; 
v___x_3487_ = l_Lean_Expr_hasFVar(v___x_3324_);
if (v___x_3487_ == 0)
{
v___y_3453_ = v_isHEq_3481_;
v___y_3454_ = v___y_3480_;
v___y_3455_ = v___y_3484_;
v___y_3456_ = v___y_3483_;
v___y_3457_ = v___y_3485_;
v___y_3458_ = v___y_3482_;
v___y_3459_ = v_useDecide_3486_;
goto v___jp_3452_;
}
else
{
v___y_3472_ = v_isHEq_3481_;
v___y_3473_ = v___y_3480_;
v___y_3474_ = v___y_3484_;
v___y_3475_ = v___y_3483_;
v___y_3476_ = v___y_3485_;
v___y_3477_ = v___y_3482_;
v___y_3478_ = v___x_3279_;
goto v___jp_3471_;
}
}
}
v___jp_3488_:
{
lean_object* v___x_3496_; 
v___x_3496_ = l_Lean_Meta_isExprDefEq(v___y_3489_, v___y_3495_, v___y_3490_, v___y_3494_, v___y_3493_, v___y_3492_);
if (lean_obj_tag(v___x_3496_) == 0)
{
lean_object* v_a_3497_; uint8_t v___x_3498_; 
v_a_3497_ = lean_ctor_get(v___x_3496_, 0);
lean_inc(v_a_3497_);
lean_dec_ref_known(v___x_3496_, 1);
v___x_3498_ = lean_unbox(v_a_3497_);
lean_dec(v_a_3497_);
if (v___x_3498_ == 0)
{
v___y_3480_ = v___y_3491_;
v_isHEq_3481_ = v___x_3183_;
v___y_3482_ = v___y_3490_;
v___y_3483_ = v___y_3494_;
v___y_3484_ = v___y_3493_;
v___y_3485_ = v___y_3492_;
goto v___jp_3479_;
}
else
{
lean_object* v___x_3499_; 
lean_dec_ref(v___x_3324_);
lean_dec_ref(v_config_3172_);
lean_inc(v_mvarId_3173_);
v___x_3499_ = l_Lean_MVarId_getType(v_mvarId_3173_, v___y_3490_, v___y_3494_, v___y_3493_, v___y_3492_);
if (lean_obj_tag(v___x_3499_) == 0)
{
lean_object* v_a_3500_; lean_object* v___x_3501_; lean_object* v___x_3502_; 
v_a_3500_ = lean_ctor_get(v___x_3499_, 0);
lean_inc(v_a_3500_);
lean_dec_ref_known(v___x_3499_, 1);
v___x_3501_ = l_Lean_LocalDecl_toExpr(v_val_3204_);
v___x_3502_ = l_Lean_Meta_mkEqOfHEq(v___x_3501_, v___x_3183_, v___y_3490_, v___y_3494_, v___y_3493_, v___y_3492_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_object* v_a_3503_; lean_object* v___x_3504_; 
v_a_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_a_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v___x_3504_ = l_Lean_Meta_mkNoConfusion(v_a_3500_, v_a_3503_, v___y_3490_, v___y_3494_, v___y_3493_, v___y_3492_);
if (lean_obj_tag(v___x_3504_) == 0)
{
lean_object* v_a_3505_; lean_object* v___x_3506_; 
v_a_3505_ = lean_ctor_get(v___x_3504_, 0);
lean_inc(v_a_3505_);
lean_dec_ref_known(v___x_3504_, 1);
v___x_3506_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3173_, v_a_3505_, v___y_3494_);
if (lean_obj_tag(v___x_3506_) == 0)
{
lean_object* v___x_3507_; lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; 
lean_dec_ref_known(v___x_3506_, 1);
v___x_3507_ = lean_box(v___x_3183_);
v___x_3508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3508_, 0, v___x_3507_);
v___x_3509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
lean_ctor_set(v___x_3509_, 1, v___x_3208_);
v___x_3510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
v_a_3190_ = v___x_3510_;
goto v___jp_3189_;
}
else
{
lean_object* v_a_3511_; lean_object* v___x_3513_; uint8_t v_isShared_3514_; uint8_t v_isSharedCheck_3518_; 
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
v_a_3511_ = lean_ctor_get(v___x_3506_, 0);
v_isSharedCheck_3518_ = !lean_is_exclusive(v___x_3506_);
if (v_isSharedCheck_3518_ == 0)
{
v___x_3513_ = v___x_3506_;
v_isShared_3514_ = v_isSharedCheck_3518_;
goto v_resetjp_3512_;
}
else
{
lean_inc(v_a_3511_);
lean_dec(v___x_3506_);
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
else
{
lean_object* v_a_3519_; lean_object* v___x_3521_; uint8_t v_isShared_3522_; uint8_t v_isSharedCheck_3526_; 
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3519_ = lean_ctor_get(v___x_3504_, 0);
v_isSharedCheck_3526_ = !lean_is_exclusive(v___x_3504_);
if (v_isSharedCheck_3526_ == 0)
{
v___x_3521_ = v___x_3504_;
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
else
{
lean_inc(v_a_3519_);
lean_dec(v___x_3504_);
v___x_3521_ = lean_box(0);
v_isShared_3522_ = v_isSharedCheck_3526_;
goto v_resetjp_3520_;
}
v_resetjp_3520_:
{
lean_object* v___x_3524_; 
if (v_isShared_3522_ == 0)
{
v___x_3524_ = v___x_3521_;
goto v_reusejp_3523_;
}
else
{
lean_object* v_reuseFailAlloc_3525_; 
v_reuseFailAlloc_3525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3525_, 0, v_a_3519_);
v___x_3524_ = v_reuseFailAlloc_3525_;
goto v_reusejp_3523_;
}
v_reusejp_3523_:
{
return v___x_3524_;
}
}
}
}
else
{
lean_object* v_a_3527_; lean_object* v___x_3529_; uint8_t v_isShared_3530_; uint8_t v_isSharedCheck_3534_; 
lean_dec(v_a_3500_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3527_ = lean_ctor_get(v___x_3502_, 0);
v_isSharedCheck_3534_ = !lean_is_exclusive(v___x_3502_);
if (v_isSharedCheck_3534_ == 0)
{
v___x_3529_ = v___x_3502_;
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
else
{
lean_inc(v_a_3527_);
lean_dec(v___x_3502_);
v___x_3529_ = lean_box(0);
v_isShared_3530_ = v_isSharedCheck_3534_;
goto v_resetjp_3528_;
}
v_resetjp_3528_:
{
lean_object* v___x_3532_; 
if (v_isShared_3530_ == 0)
{
v___x_3532_ = v___x_3529_;
goto v_reusejp_3531_;
}
else
{
lean_object* v_reuseFailAlloc_3533_; 
v_reuseFailAlloc_3533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3533_, 0, v_a_3527_);
v___x_3532_ = v_reuseFailAlloc_3533_;
goto v_reusejp_3531_;
}
v_reusejp_3531_:
{
return v___x_3532_;
}
}
}
}
else
{
lean_object* v_a_3535_; lean_object* v___x_3537_; uint8_t v_isShared_3538_; uint8_t v_isSharedCheck_3542_; 
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3535_ = lean_ctor_get(v___x_3499_, 0);
v_isSharedCheck_3542_ = !lean_is_exclusive(v___x_3499_);
if (v_isSharedCheck_3542_ == 0)
{
v___x_3537_ = v___x_3499_;
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
else
{
lean_inc(v_a_3535_);
lean_dec(v___x_3499_);
v___x_3537_ = lean_box(0);
v_isShared_3538_ = v_isSharedCheck_3542_;
goto v_resetjp_3536_;
}
v_resetjp_3536_:
{
lean_object* v___x_3540_; 
if (v_isShared_3538_ == 0)
{
v___x_3540_ = v___x_3537_;
goto v_reusejp_3539_;
}
else
{
lean_object* v_reuseFailAlloc_3541_; 
v_reuseFailAlloc_3541_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3541_, 0, v_a_3535_);
v___x_3540_ = v_reuseFailAlloc_3541_;
goto v_reusejp_3539_;
}
v_reusejp_3539_:
{
return v___x_3540_;
}
}
}
}
}
else
{
lean_object* v_a_3543_; lean_object* v___x_3545_; uint8_t v_isShared_3546_; uint8_t v_isSharedCheck_3550_; 
lean_dec_ref(v___x_3324_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3543_ = lean_ctor_get(v___x_3496_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v___x_3496_);
if (v_isSharedCheck_3550_ == 0)
{
v___x_3545_ = v___x_3496_;
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
else
{
lean_inc(v_a_3543_);
lean_dec(v___x_3496_);
v___x_3545_ = lean_box(0);
v_isShared_3546_ = v_isSharedCheck_3550_;
goto v_resetjp_3544_;
}
v_resetjp_3544_:
{
lean_object* v___x_3548_; 
if (v_isShared_3546_ == 0)
{
v___x_3548_ = v___x_3545_;
goto v_reusejp_3547_;
}
else
{
lean_object* v_reuseFailAlloc_3549_; 
v_reuseFailAlloc_3549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3549_, 0, v_a_3543_);
v___x_3548_ = v_reuseFailAlloc_3549_;
goto v_reusejp_3547_;
}
v_reusejp_3547_:
{
return v___x_3548_;
}
}
}
}
v___jp_3551_:
{
lean_object* v___x_3557_; 
lean_inc_ref(v___x_3324_);
v___x_3557_ = l_Lean_Meta_matchHEq_x3f(v___x_3324_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
if (lean_obj_tag(v___x_3557_) == 0)
{
lean_object* v_a_3558_; 
v_a_3558_ = lean_ctor_get(v___x_3557_, 0);
lean_inc(v_a_3558_);
lean_dec_ref_known(v___x_3557_, 1);
if (lean_obj_tag(v_a_3558_) == 1)
{
lean_object* v_val_3559_; lean_object* v_snd_3560_; lean_object* v_snd_3561_; lean_object* v_fst_3562_; lean_object* v_fst_3563_; lean_object* v_fst_3564_; lean_object* v_snd_3565_; lean_object* v___x_3566_; 
v_val_3559_ = lean_ctor_get(v_a_3558_, 0);
lean_inc(v_val_3559_);
lean_dec_ref_known(v_a_3558_, 1);
v_snd_3560_ = lean_ctor_get(v_val_3559_, 1);
lean_inc(v_snd_3560_);
v_snd_3561_ = lean_ctor_get(v_snd_3560_, 1);
lean_inc(v_snd_3561_);
v_fst_3562_ = lean_ctor_get(v_val_3559_, 0);
lean_inc(v_fst_3562_);
lean_dec(v_val_3559_);
v_fst_3563_ = lean_ctor_get(v_snd_3560_, 0);
lean_inc(v_fst_3563_);
lean_dec(v_snd_3560_);
v_fst_3564_ = lean_ctor_get(v_snd_3561_, 0);
lean_inc(v_fst_3564_);
v_snd_3565_ = lean_ctor_get(v_snd_3561_, 1);
lean_inc(v_snd_3565_);
lean_dec(v_snd_3561_);
v___x_3566_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3563_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
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
v___x_3569_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3565_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
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
v___y_3489_ = v_fst_3562_;
v___y_3490_ = v___y_3553_;
v___y_3491_ = v_isEq_3552_;
v___y_3492_ = v___y_3556_;
v___y_3493_ = v___y_3555_;
v___y_3494_ = v___y_3554_;
v___y_3495_ = v_fst_3564_;
goto v___jp_3488_;
}
else
{
if (v___x_3279_ == 0)
{
lean_dec(v_fst_3564_);
lean_dec(v_fst_3562_);
v___y_3480_ = v_isEq_3552_;
v_isHEq_3481_ = v___x_3183_;
v___y_3482_ = v___y_3553_;
v___y_3483_ = v___y_3554_;
v___y_3484_ = v___y_3555_;
v___y_3485_ = v___y_3556_;
goto v___jp_3479_;
}
else
{
v___y_3489_ = v_fst_3562_;
v___y_3490_ = v___y_3553_;
v___y_3491_ = v_isEq_3552_;
v___y_3492_ = v___y_3556_;
v___y_3493_ = v___y_3555_;
v___y_3494_ = v___y_3554_;
v___y_3495_ = v_fst_3564_;
goto v___jp_3488_;
}
}
}
else
{
lean_dec(v_a_3570_);
lean_dec(v_val_3568_);
lean_dec(v_fst_3564_);
lean_dec(v_fst_3562_);
v___y_3480_ = v_isEq_3552_;
v_isHEq_3481_ = v___x_3183_;
v___y_3482_ = v___y_3553_;
v___y_3483_ = v___y_3554_;
v___y_3484_ = v___y_3555_;
v___y_3485_ = v___y_3556_;
goto v___jp_3479_;
}
}
else
{
lean_object* v_a_3577_; lean_object* v___x_3579_; uint8_t v_isShared_3580_; uint8_t v_isSharedCheck_3584_; 
lean_dec(v_val_3568_);
lean_dec(v_fst_3564_);
lean_dec(v_fst_3562_);
lean_dec_ref(v___x_3324_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
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
lean_dec(v_fst_3564_);
lean_dec(v_fst_3562_);
v___y_3480_ = v_isEq_3552_;
v_isHEq_3481_ = v___x_3183_;
v___y_3482_ = v___y_3553_;
v___y_3483_ = v___y_3554_;
v___y_3484_ = v___y_3555_;
v___y_3485_ = v___y_3556_;
goto v___jp_3479_;
}
}
else
{
lean_object* v_a_3585_; lean_object* v___x_3587_; uint8_t v_isShared_3588_; uint8_t v_isSharedCheck_3592_; 
lean_dec(v_snd_3565_);
lean_dec(v_fst_3564_);
lean_dec(v_fst_3562_);
lean_dec_ref(v___x_3324_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
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
lean_dec(v_a_3558_);
v___y_3480_ = v_isEq_3552_;
v_isHEq_3481_ = v___x_3279_;
v___y_3482_ = v___y_3553_;
v___y_3483_ = v___y_3554_;
v___y_3484_ = v___y_3555_;
v___y_3485_ = v___y_3556_;
goto v___jp_3479_;
}
}
else
{
lean_object* v_a_3593_; lean_object* v___x_3595_; uint8_t v_isShared_3596_; uint8_t v_isSharedCheck_3600_; 
lean_dec_ref(v___x_3324_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3593_ = lean_ctor_get(v___x_3557_, 0);
v_isSharedCheck_3600_ = !lean_is_exclusive(v___x_3557_);
if (v_isSharedCheck_3600_ == 0)
{
v___x_3595_ = v___x_3557_;
v_isShared_3596_ = v_isSharedCheck_3600_;
goto v_resetjp_3594_;
}
else
{
lean_inc(v_a_3593_);
lean_dec(v___x_3557_);
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
lean_inc_ref(v___x_3324_);
v___x_3606_ = l_Lean_Meta_matchEq_x3f(v___x_3324_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3606_) == 0)
{
lean_object* v_a_3607_; 
v_a_3607_ = lean_ctor_get(v___x_3606_, 0);
lean_inc(v_a_3607_);
lean_dec_ref_known(v___x_3606_, 1);
if (lean_obj_tag(v_a_3607_) == 1)
{
lean_object* v_val_3608_; lean_object* v_snd_3609_; lean_object* v_fst_3610_; lean_object* v_snd_3611_; lean_object* v___x_3612_; 
v_val_3608_ = lean_ctor_get(v_a_3607_, 0);
lean_inc(v_val_3608_);
lean_dec_ref_known(v_a_3607_, 1);
v_snd_3609_ = lean_ctor_get(v_val_3608_, 1);
lean_inc(v_snd_3609_);
lean_dec(v_val_3608_);
v_fst_3610_ = lean_ctor_get(v_snd_3609_, 0);
lean_inc(v_fst_3610_);
v_snd_3611_ = lean_ctor_get(v_snd_3609_, 1);
lean_inc(v_snd_3611_);
lean_dec(v_snd_3609_);
v___x_3612_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3610_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
lean_inc(v_a_3613_);
lean_dec_ref_known(v___x_3612_, 1);
if (lean_obj_tag(v_a_3613_) == 1)
{
lean_object* v_val_3614_; lean_object* v___x_3615_; 
v_val_3614_ = lean_ctor_get(v_a_3613_, 0);
lean_inc(v_val_3614_);
lean_dec_ref_known(v_a_3613_, 1);
v___x_3615_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3611_, v___y_3602_, v___y_3603_, v___y_3604_, v___y_3605_);
if (lean_obj_tag(v___x_3615_) == 0)
{
lean_object* v_a_3616_; 
v_a_3616_ = lean_ctor_get(v___x_3615_, 0);
lean_inc(v_a_3616_);
lean_dec_ref_known(v___x_3615_, 1);
if (lean_obj_tag(v_a_3616_) == 1)
{
lean_object* v_toConstantVal_3617_; lean_object* v_val_3618_; lean_object* v_toConstantVal_3619_; lean_object* v_name_3620_; lean_object* v_name_3621_; uint8_t v___x_3622_; 
v_toConstantVal_3617_ = lean_ctor_get(v_val_3614_, 0);
lean_inc_ref(v_toConstantVal_3617_);
lean_dec(v_val_3614_);
v_val_3618_ = lean_ctor_get(v_a_3616_, 0);
lean_inc(v_val_3618_);
lean_dec_ref_known(v_a_3616_, 1);
v_toConstantVal_3619_ = lean_ctor_get(v_val_3618_, 0);
lean_inc_ref(v_toConstantVal_3619_);
lean_dec(v_val_3618_);
v_name_3620_ = lean_ctor_get(v_toConstantVal_3617_, 0);
lean_inc(v_name_3620_);
lean_dec_ref(v_toConstantVal_3617_);
v_name_3621_ = lean_ctor_get(v_toConstantVal_3619_, 0);
lean_inc(v_name_3621_);
lean_dec_ref(v_toConstantVal_3619_);
v___x_3622_ = lean_name_eq(v_name_3620_, v_name_3621_);
lean_dec(v_name_3621_);
lean_dec(v_name_3620_);
if (v___x_3622_ == 0)
{
lean_dec_ref(v___x_3324_);
lean_dec_ref(v_config_3172_);
v___y_3210_ = v___y_3603_;
v___y_3211_ = v___y_3604_;
v___y_3212_ = v___y_3602_;
v___y_3213_ = v___y_3605_;
goto v___jp_3209_;
}
else
{
if (v___x_3279_ == 0)
{
lean_del_object(v___x_3206_);
v_isEq_3552_ = v___x_3183_;
v___y_3553_ = v___y_3602_;
v___y_3554_ = v___y_3603_;
v___y_3555_ = v___y_3604_;
v___y_3556_ = v___y_3605_;
goto v___jp_3551_;
}
else
{
lean_dec_ref(v___x_3324_);
lean_dec_ref(v_config_3172_);
v___y_3210_ = v___y_3603_;
v___y_3211_ = v___y_3604_;
v___y_3212_ = v___y_3602_;
v___y_3213_ = v___y_3605_;
goto v___jp_3209_;
}
}
}
else
{
lean_dec(v_a_3616_);
lean_dec(v_val_3614_);
lean_del_object(v___x_3206_);
v_isEq_3552_ = v___x_3183_;
v___y_3553_ = v___y_3602_;
v___y_3554_ = v___y_3603_;
v___y_3555_ = v___y_3604_;
v___y_3556_ = v___y_3605_;
goto v___jp_3551_;
}
}
else
{
lean_object* v_a_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3630_; 
lean_dec(v_val_3614_);
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3623_ = lean_ctor_get(v___x_3615_, 0);
v_isSharedCheck_3630_ = !lean_is_exclusive(v___x_3615_);
if (v_isSharedCheck_3630_ == 0)
{
v___x_3625_ = v___x_3615_;
v_isShared_3626_ = v_isSharedCheck_3630_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_a_3623_);
lean_dec(v___x_3615_);
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
lean_dec(v_a_3613_);
lean_dec(v_snd_3611_);
lean_del_object(v___x_3206_);
v_isEq_3552_ = v___x_3183_;
v___y_3553_ = v___y_3602_;
v___y_3554_ = v___y_3603_;
v___y_3555_ = v___y_3604_;
v___y_3556_ = v___y_3605_;
goto v___jp_3551_;
}
}
else
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3638_; 
lean_dec(v_snd_3611_);
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3631_ = lean_ctor_get(v___x_3612_, 0);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3633_ = v___x_3612_;
v_isShared_3634_ = v_isSharedCheck_3638_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3612_);
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
lean_dec(v_a_3607_);
lean_del_object(v___x_3206_);
v_isEq_3552_ = v___x_3279_;
v___y_3553_ = v___y_3602_;
v___y_3554_ = v___y_3603_;
v___y_3555_ = v___y_3604_;
v___y_3556_ = v___y_3605_;
goto v___jp_3551_;
}
}
else
{
lean_object* v_a_3639_; lean_object* v___x_3641_; uint8_t v_isShared_3642_; uint8_t v_isSharedCheck_3646_; 
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3639_ = lean_ctor_get(v___x_3606_, 0);
v_isSharedCheck_3646_ = !lean_is_exclusive(v___x_3606_);
if (v_isSharedCheck_3646_ == 0)
{
v___x_3641_ = v___x_3606_;
v_isShared_3642_ = v_isSharedCheck_3646_;
goto v_resetjp_3640_;
}
else
{
lean_inc(v_a_3639_);
lean_dec(v___x_3606_);
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
v___jp_3647_:
{
lean_object* v___x_3652_; 
lean_inc_ref(v___x_3324_);
v___x_3652_ = l_Lean_refutableHasNotBit_x3f(v___x_3324_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3652_) == 0)
{
lean_object* v_a_3653_; 
v_a_3653_ = lean_ctor_get(v___x_3652_, 0);
lean_inc(v_a_3653_);
lean_dec_ref_known(v___x_3652_, 1);
if (lean_obj_tag(v_a_3653_) == 1)
{
lean_object* v_val_3654_; lean_object* v___x_3656_; uint8_t v_isShared_3657_; uint8_t v_isSharedCheck_3694_; 
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec_ref(v_config_3172_);
v_val_3654_ = lean_ctor_get(v_a_3653_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v_a_3653_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3656_ = v_a_3653_;
v_isShared_3657_ = v_isSharedCheck_3694_;
goto v_resetjp_3655_;
}
else
{
lean_inc(v_val_3654_);
lean_dec(v_a_3653_);
v___x_3656_ = lean_box(0);
v_isShared_3657_ = v_isSharedCheck_3694_;
goto v_resetjp_3655_;
}
v_resetjp_3655_:
{
lean_object* v___x_3658_; 
lean_inc(v_mvarId_3173_);
v___x_3658_ = l_Lean_MVarId_getType(v_mvarId_3173_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3658_) == 0)
{
lean_object* v_a_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; 
v_a_3659_ = lean_ctor_get(v___x_3658_, 0);
lean_inc(v_a_3659_);
lean_dec_ref_known(v___x_3658_, 1);
v___x_3660_ = l_Lean_LocalDecl_toExpr(v_val_3204_);
v___x_3661_ = l_Lean_Meta_mkAbsurd(v_a_3659_, v_val_3654_, v___x_3660_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3661_) == 0)
{
lean_object* v_a_3662_; lean_object* v___x_3663_; 
v_a_3662_ = lean_ctor_get(v___x_3661_, 0);
lean_inc(v_a_3662_);
lean_dec_ref_known(v___x_3661_, 1);
v___x_3663_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3173_, v_a_3662_, v___y_3649_);
if (lean_obj_tag(v___x_3663_) == 0)
{
lean_object* v___x_3664_; lean_object* v___x_3666_; 
lean_dec_ref_known(v___x_3663_, 1);
v___x_3664_ = lean_box(v___x_3183_);
if (v_isShared_3657_ == 0)
{
lean_ctor_set(v___x_3656_, 0, v___x_3664_);
v___x_3666_ = v___x_3656_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3669_; 
v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3669_, 0, v___x_3664_);
v___x_3666_ = v_reuseFailAlloc_3669_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; 
v___x_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3666_);
lean_ctor_set(v___x_3667_, 1, v___x_3208_);
v___x_3668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
v_a_3190_ = v___x_3668_;
goto v___jp_3189_;
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
lean_del_object(v___x_3656_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
v_a_3670_ = lean_ctor_get(v___x_3663_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3663_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3663_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3663_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
else
{
lean_object* v_a_3678_; lean_object* v___x_3680_; uint8_t v_isShared_3681_; uint8_t v_isSharedCheck_3685_; 
lean_del_object(v___x_3656_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3678_ = lean_ctor_get(v___x_3661_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v___x_3661_);
if (v_isSharedCheck_3685_ == 0)
{
v___x_3680_ = v___x_3661_;
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
else
{
lean_inc(v_a_3678_);
lean_dec(v___x_3661_);
v___x_3680_ = lean_box(0);
v_isShared_3681_ = v_isSharedCheck_3685_;
goto v_resetjp_3679_;
}
v_resetjp_3679_:
{
lean_object* v___x_3683_; 
if (v_isShared_3681_ == 0)
{
v___x_3683_ = v___x_3680_;
goto v_reusejp_3682_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v_a_3678_);
v___x_3683_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3682_;
}
v_reusejp_3682_:
{
return v___x_3683_;
}
}
}
}
else
{
lean_object* v_a_3686_; lean_object* v___x_3688_; uint8_t v_isShared_3689_; uint8_t v_isSharedCheck_3693_; 
lean_del_object(v___x_3656_);
lean_dec(v_val_3654_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3686_ = lean_ctor_get(v___x_3658_, 0);
v_isSharedCheck_3693_ = !lean_is_exclusive(v___x_3658_);
if (v_isSharedCheck_3693_ == 0)
{
v___x_3688_ = v___x_3658_;
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
else
{
lean_inc(v_a_3686_);
lean_dec(v___x_3658_);
v___x_3688_ = lean_box(0);
v_isShared_3689_ = v_isSharedCheck_3693_;
goto v_resetjp_3687_;
}
v_resetjp_3687_:
{
lean_object* v___x_3691_; 
if (v_isShared_3689_ == 0)
{
v___x_3691_ = v___x_3688_;
goto v_reusejp_3690_;
}
else
{
lean_object* v_reuseFailAlloc_3692_; 
v_reuseFailAlloc_3692_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3692_, 0, v_a_3686_);
v___x_3691_ = v_reuseFailAlloc_3692_;
goto v_reusejp_3690_;
}
v_reusejp_3690_:
{
return v___x_3691_;
}
}
}
}
}
else
{
lean_object* v___x_3695_; 
lean_dec(v_a_3653_);
lean_inc_ref(v___x_3324_);
v___x_3695_ = l_Lean_Meta_matchNe_x3f(v___x_3324_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3695_) == 0)
{
lean_object* v_a_3696_; 
v_a_3696_ = lean_ctor_get(v___x_3695_, 0);
lean_inc(v_a_3696_);
lean_dec_ref_known(v___x_3695_, 1);
if (lean_obj_tag(v_a_3696_) == 1)
{
lean_object* v_val_3697_; lean_object* v___x_3699_; uint8_t v_isShared_3700_; uint8_t v_isSharedCheck_3767_; 
v_val_3697_ = lean_ctor_get(v_a_3696_, 0);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_a_3696_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3699_ = v_a_3696_;
v_isShared_3700_ = v_isSharedCheck_3767_;
goto v_resetjp_3698_;
}
else
{
lean_inc(v_val_3697_);
lean_dec(v_a_3696_);
v___x_3699_ = lean_box(0);
v_isShared_3700_ = v_isSharedCheck_3767_;
goto v_resetjp_3698_;
}
v_resetjp_3698_:
{
lean_object* v_snd_3701_; lean_object* v_fst_3702_; lean_object* v_snd_3703_; lean_object* v___x_3705_; uint8_t v_isShared_3706_; uint8_t v_isSharedCheck_3766_; 
v_snd_3701_ = lean_ctor_get(v_val_3697_, 1);
lean_inc(v_snd_3701_);
lean_dec(v_val_3697_);
v_fst_3702_ = lean_ctor_get(v_snd_3701_, 0);
v_snd_3703_ = lean_ctor_get(v_snd_3701_, 1);
v_isSharedCheck_3766_ = !lean_is_exclusive(v_snd_3701_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3705_ = v_snd_3701_;
v_isShared_3706_ = v_isSharedCheck_3766_;
goto v_resetjp_3704_;
}
else
{
lean_inc(v_snd_3703_);
lean_inc(v_fst_3702_);
lean_dec(v_snd_3701_);
v___x_3705_ = lean_box(0);
v_isShared_3706_ = v_isSharedCheck_3766_;
goto v_resetjp_3704_;
}
v_resetjp_3704_:
{
lean_object* v___x_3707_; 
lean_inc(v_fst_3702_);
v___x_3707_ = l_Lean_Meta_isExprDefEq(v_fst_3702_, v_snd_3703_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3707_) == 0)
{
lean_object* v_a_3708_; uint8_t v___x_3709_; 
v_a_3708_ = lean_ctor_get(v___x_3707_, 0);
lean_inc(v_a_3708_);
lean_dec_ref_known(v___x_3707_, 1);
v___x_3709_ = lean_unbox(v_a_3708_);
lean_dec(v_a_3708_);
if (v___x_3709_ == 0)
{
lean_del_object(v___x_3705_);
lean_dec(v_fst_3702_);
lean_del_object(v___x_3699_);
v___y_3602_ = v___y_3648_;
v___y_3603_ = v___y_3649_;
v___y_3604_ = v___y_3650_;
v___y_3605_ = v___y_3651_;
goto v___jp_3601_;
}
else
{
lean_object* v___x_3710_; 
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec_ref(v_config_3172_);
lean_inc(v_mvarId_3173_);
v___x_3710_ = l_Lean_MVarId_getType(v_mvarId_3173_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v_a_3711_; lean_object* v___x_3712_; 
v_a_3711_ = lean_ctor_get(v___x_3710_, 0);
lean_inc(v_a_3711_);
lean_dec_ref_known(v___x_3710_, 1);
v___x_3712_ = l_Lean_Meta_mkEqRefl(v_fst_3702_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3712_) == 0)
{
lean_object* v_a_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; 
v_a_3713_ = lean_ctor_get(v___x_3712_, 0);
lean_inc(v_a_3713_);
lean_dec_ref_known(v___x_3712_, 1);
v___x_3714_ = l_Lean_LocalDecl_toExpr(v_val_3204_);
v___x_3715_ = l_Lean_Meta_mkAbsurd(v_a_3711_, v_a_3713_, v___x_3714_, v___y_3648_, v___y_3649_, v___y_3650_, v___y_3651_);
if (lean_obj_tag(v___x_3715_) == 0)
{
lean_object* v_a_3716_; lean_object* v___x_3717_; 
v_a_3716_ = lean_ctor_get(v___x_3715_, 0);
lean_inc(v_a_3716_);
lean_dec_ref_known(v___x_3715_, 1);
v___x_3717_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3173_, v_a_3716_, v___y_3649_);
if (lean_obj_tag(v___x_3717_) == 0)
{
lean_object* v___x_3718_; lean_object* v___x_3720_; 
lean_dec_ref_known(v___x_3717_, 1);
v___x_3718_ = lean_box(v___x_3183_);
if (v_isShared_3700_ == 0)
{
lean_ctor_set(v___x_3699_, 0, v___x_3718_);
v___x_3720_ = v___x_3699_;
goto v_reusejp_3719_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3718_);
v___x_3720_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3719_;
}
v_reusejp_3719_:
{
lean_object* v___x_3722_; 
if (v_isShared_3706_ == 0)
{
lean_ctor_set(v___x_3705_, 1, v___x_3208_);
lean_ctor_set(v___x_3705_, 0, v___x_3720_);
v___x_3722_ = v___x_3705_;
goto v_reusejp_3721_;
}
else
{
lean_object* v_reuseFailAlloc_3724_; 
v_reuseFailAlloc_3724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3724_, 0, v___x_3720_);
lean_ctor_set(v_reuseFailAlloc_3724_, 1, v___x_3208_);
v___x_3722_ = v_reuseFailAlloc_3724_;
goto v_reusejp_3721_;
}
v_reusejp_3721_:
{
lean_object* v___x_3723_; 
v___x_3723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3722_);
v_a_3190_ = v___x_3723_;
goto v___jp_3189_;
}
}
}
else
{
lean_object* v_a_3726_; lean_object* v___x_3728_; uint8_t v_isShared_3729_; uint8_t v_isSharedCheck_3733_; 
lean_del_object(v___x_3705_);
lean_del_object(v___x_3699_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
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
lean_object* v_a_3734_; lean_object* v___x_3736_; uint8_t v_isShared_3737_; uint8_t v_isSharedCheck_3741_; 
lean_del_object(v___x_3705_);
lean_del_object(v___x_3699_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3734_ = lean_ctor_get(v___x_3715_, 0);
v_isSharedCheck_3741_ = !lean_is_exclusive(v___x_3715_);
if (v_isSharedCheck_3741_ == 0)
{
v___x_3736_ = v___x_3715_;
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
else
{
lean_inc(v_a_3734_);
lean_dec(v___x_3715_);
v___x_3736_ = lean_box(0);
v_isShared_3737_ = v_isSharedCheck_3741_;
goto v_resetjp_3735_;
}
v_resetjp_3735_:
{
lean_object* v___x_3739_; 
if (v_isShared_3737_ == 0)
{
v___x_3739_ = v___x_3736_;
goto v_reusejp_3738_;
}
else
{
lean_object* v_reuseFailAlloc_3740_; 
v_reuseFailAlloc_3740_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3740_, 0, v_a_3734_);
v___x_3739_ = v_reuseFailAlloc_3740_;
goto v_reusejp_3738_;
}
v_reusejp_3738_:
{
return v___x_3739_;
}
}
}
}
else
{
lean_object* v_a_3742_; lean_object* v___x_3744_; uint8_t v_isShared_3745_; uint8_t v_isSharedCheck_3749_; 
lean_dec(v_a_3711_);
lean_del_object(v___x_3705_);
lean_del_object(v___x_3699_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3742_ = lean_ctor_get(v___x_3712_, 0);
v_isSharedCheck_3749_ = !lean_is_exclusive(v___x_3712_);
if (v_isSharedCheck_3749_ == 0)
{
v___x_3744_ = v___x_3712_;
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
else
{
lean_inc(v_a_3742_);
lean_dec(v___x_3712_);
v___x_3744_ = lean_box(0);
v_isShared_3745_ = v_isSharedCheck_3749_;
goto v_resetjp_3743_;
}
v_resetjp_3743_:
{
lean_object* v___x_3747_; 
if (v_isShared_3745_ == 0)
{
v___x_3747_ = v___x_3744_;
goto v_reusejp_3746_;
}
else
{
lean_object* v_reuseFailAlloc_3748_; 
v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
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
lean_del_object(v___x_3705_);
lean_dec(v_fst_3702_);
lean_del_object(v___x_3699_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3750_ = lean_ctor_get(v___x_3710_, 0);
v_isSharedCheck_3757_ = !lean_is_exclusive(v___x_3710_);
if (v_isSharedCheck_3757_ == 0)
{
v___x_3752_ = v___x_3710_;
v_isShared_3753_ = v_isSharedCheck_3757_;
goto v_resetjp_3751_;
}
else
{
lean_inc(v_a_3750_);
lean_dec(v___x_3710_);
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
}
else
{
lean_object* v_a_3758_; lean_object* v___x_3760_; uint8_t v_isShared_3761_; uint8_t v_isSharedCheck_3765_; 
lean_del_object(v___x_3705_);
lean_dec(v_fst_3702_);
lean_del_object(v___x_3699_);
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3758_ = lean_ctor_get(v___x_3707_, 0);
v_isSharedCheck_3765_ = !lean_is_exclusive(v___x_3707_);
if (v_isSharedCheck_3765_ == 0)
{
v___x_3760_ = v___x_3707_;
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
else
{
lean_inc(v_a_3758_);
lean_dec(v___x_3707_);
v___x_3760_ = lean_box(0);
v_isShared_3761_ = v_isSharedCheck_3765_;
goto v_resetjp_3759_;
}
v_resetjp_3759_:
{
lean_object* v___x_3763_; 
if (v_isShared_3761_ == 0)
{
v___x_3763_ = v___x_3760_;
goto v_reusejp_3762_;
}
else
{
lean_object* v_reuseFailAlloc_3764_; 
v_reuseFailAlloc_3764_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3764_, 0, v_a_3758_);
v___x_3763_ = v_reuseFailAlloc_3764_;
goto v_reusejp_3762_;
}
v_reusejp_3762_:
{
return v___x_3763_;
}
}
}
}
}
}
else
{
lean_dec(v_a_3696_);
v___y_3602_ = v___y_3648_;
v___y_3603_ = v___y_3649_;
v___y_3604_ = v___y_3650_;
v___y_3605_ = v___y_3651_;
goto v___jp_3601_;
}
}
else
{
lean_object* v_a_3768_; lean_object* v___x_3770_; uint8_t v_isShared_3771_; uint8_t v_isSharedCheck_3775_; 
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3768_ = lean_ctor_get(v___x_3695_, 0);
v_isSharedCheck_3775_ = !lean_is_exclusive(v___x_3695_);
if (v_isSharedCheck_3775_ == 0)
{
v___x_3770_ = v___x_3695_;
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
else
{
lean_inc(v_a_3768_);
lean_dec(v___x_3695_);
v___x_3770_ = lean_box(0);
v_isShared_3771_ = v_isSharedCheck_3775_;
goto v_resetjp_3769_;
}
v_resetjp_3769_:
{
lean_object* v___x_3773_; 
if (v_isShared_3771_ == 0)
{
v___x_3773_ = v___x_3770_;
goto v_reusejp_3772_;
}
else
{
lean_object* v_reuseFailAlloc_3774_; 
v_reuseFailAlloc_3774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3774_, 0, v_a_3768_);
v___x_3773_ = v_reuseFailAlloc_3774_;
goto v_reusejp_3772_;
}
v_reusejp_3772_:
{
return v___x_3773_;
}
}
}
}
}
else
{
lean_object* v_a_3776_; lean_object* v___x_3778_; uint8_t v_isShared_3779_; uint8_t v_isSharedCheck_3783_; 
lean_dec_ref(v___x_3324_);
lean_del_object(v___x_3206_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3776_ = lean_ctor_get(v___x_3652_, 0);
v_isSharedCheck_3783_ = !lean_is_exclusive(v___x_3652_);
if (v_isSharedCheck_3783_ == 0)
{
v___x_3778_ = v___x_3652_;
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
else
{
lean_inc(v_a_3776_);
lean_dec(v___x_3652_);
v___x_3778_ = lean_box(0);
v_isShared_3779_ = v_isSharedCheck_3783_;
goto v_resetjp_3777_;
}
v_resetjp_3777_:
{
lean_object* v___x_3781_; 
if (v_isShared_3779_ == 0)
{
v___x_3781_ = v___x_3778_;
goto v_reusejp_3780_;
}
else
{
lean_object* v_reuseFailAlloc_3782_; 
v_reuseFailAlloc_3782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3782_, 0, v_a_3776_);
v___x_3781_ = v_reuseFailAlloc_3782_;
goto v_reusejp_3780_;
}
v_reusejp_3780_:
{
return v___x_3781_;
}
}
}
}
}
else
{
lean_del_object(v___x_3206_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
v_a_3198_ = v___x_3250_;
goto v___jp_3197_;
}
v___jp_3209_:
{
lean_object* v___x_3214_; 
lean_inc(v_mvarId_3173_);
v___x_3214_ = l_Lean_MVarId_getType(v_mvarId_3173_, v___y_3212_, v___y_3210_, v___y_3211_, v___y_3213_);
if (lean_obj_tag(v___x_3214_) == 0)
{
lean_object* v_a_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; 
v_a_3215_ = lean_ctor_get(v___x_3214_, 0);
lean_inc(v_a_3215_);
lean_dec_ref_known(v___x_3214_, 1);
v___x_3216_ = l_Lean_LocalDecl_toExpr(v_val_3204_);
v___x_3217_ = l_Lean_Meta_mkNoConfusion(v_a_3215_, v___x_3216_, v___y_3212_, v___y_3210_, v___y_3211_, v___y_3213_);
if (lean_obj_tag(v___x_3217_) == 0)
{
lean_object* v_a_3218_; lean_object* v___x_3219_; 
v_a_3218_ = lean_ctor_get(v___x_3217_, 0);
lean_inc(v_a_3218_);
lean_dec_ref_known(v___x_3217_, 1);
v___x_3219_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3173_, v_a_3218_, v___y_3210_);
if (lean_obj_tag(v___x_3219_) == 0)
{
lean_object* v___x_3220_; lean_object* v___x_3222_; 
lean_dec_ref_known(v___x_3219_, 1);
v___x_3220_ = lean_box(v___x_3183_);
if (v_isShared_3207_ == 0)
{
lean_ctor_set(v___x_3206_, 0, v___x_3220_);
v___x_3222_ = v___x_3206_;
goto v_reusejp_3221_;
}
else
{
lean_object* v_reuseFailAlloc_3225_; 
v_reuseFailAlloc_3225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3225_, 0, v___x_3220_);
v___x_3222_ = v_reuseFailAlloc_3225_;
goto v_reusejp_3221_;
}
v_reusejp_3221_:
{
lean_object* v___x_3223_; lean_object* v___x_3224_; 
v___x_3223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3223_, 0, v___x_3222_);
lean_ctor_set(v___x_3223_, 1, v___x_3208_);
v___x_3224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
v_a_3190_ = v___x_3224_;
goto v___jp_3189_;
}
}
else
{
lean_object* v_a_3226_; lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3233_; 
lean_del_object(v___x_3206_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
v_a_3226_ = lean_ctor_get(v___x_3219_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3219_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3228_ = v___x_3219_;
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
else
{
lean_inc(v_a_3226_);
lean_dec(v___x_3219_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3233_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3231_; 
if (v_isShared_3229_ == 0)
{
v___x_3231_ = v___x_3228_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v_a_3226_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_a_3234_; lean_object* v___x_3236_; uint8_t v_isShared_3237_; uint8_t v_isSharedCheck_3241_; 
lean_del_object(v___x_3206_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3234_ = lean_ctor_get(v___x_3217_, 0);
v_isSharedCheck_3241_ = !lean_is_exclusive(v___x_3217_);
if (v_isSharedCheck_3241_ == 0)
{
v___x_3236_ = v___x_3217_;
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
else
{
lean_inc(v_a_3234_);
lean_dec(v___x_3217_);
v___x_3236_ = lean_box(0);
v_isShared_3237_ = v_isSharedCheck_3241_;
goto v_resetjp_3235_;
}
v_resetjp_3235_:
{
lean_object* v___x_3239_; 
if (v_isShared_3237_ == 0)
{
v___x_3239_ = v___x_3236_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3240_; 
v_reuseFailAlloc_3240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3240_, 0, v_a_3234_);
v___x_3239_ = v_reuseFailAlloc_3240_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
return v___x_3239_;
}
}
}
}
else
{
lean_object* v_a_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3249_; 
lean_del_object(v___x_3206_);
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
v_a_3242_ = lean_ctor_get(v___x_3214_, 0);
v_isSharedCheck_3249_ = !lean_is_exclusive(v___x_3214_);
if (v_isSharedCheck_3249_ == 0)
{
v___x_3244_ = v___x_3214_;
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_a_3242_);
lean_dec(v___x_3214_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3249_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3247_; 
if (v_isShared_3245_ == 0)
{
v___x_3247_ = v___x_3244_;
goto v_reusejp_3246_;
}
else
{
lean_object* v_reuseFailAlloc_3248_; 
v_reuseFailAlloc_3248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3248_, 0, v_a_3242_);
v___x_3247_ = v_reuseFailAlloc_3248_;
goto v_reusejp_3246_;
}
v_reusejp_3246_:
{
return v___x_3247_;
}
}
}
}
v___jp_3251_:
{
lean_object* v_searchFuel_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; 
v_searchFuel_3256_ = lean_ctor_get(v_config_3172_, 0);
v___x_3257_ = l_Lean_LocalDecl_fvarId(v_val_3204_);
lean_dec(v_val_3204_);
lean_inc(v_searchFuel_3256_);
lean_inc(v_mvarId_3173_);
v___x_3258_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3173_, v___x_3257_, v_searchFuel_3256_, v___y_3253_, v___y_3255_, v___y_3254_, v___y_3252_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v_a_3259_; uint8_t v___x_3260_; 
v_a_3259_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_a_3259_);
lean_dec_ref_known(v___x_3258_, 1);
v___x_3260_ = lean_unbox(v_a_3259_);
lean_dec(v_a_3259_);
if (v___x_3260_ == 0)
{
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
v_a_3198_ = v___x_3250_;
goto v___jp_3197_;
}
else
{
lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; 
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v___x_3261_ = lean_box(v___x_3183_);
v___x_3262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
v___x_3263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
lean_ctor_set(v___x_3263_, 1, v___x_3208_);
v___x_3264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
v_a_3190_ = v___x_3264_;
goto v___jp_3189_;
}
}
else
{
lean_object* v_a_3265_; lean_object* v___x_3267_; uint8_t v_isShared_3268_; uint8_t v_isSharedCheck_3272_; 
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3265_ = lean_ctor_get(v___x_3258_, 0);
v_isSharedCheck_3272_ = !lean_is_exclusive(v___x_3258_);
if (v_isSharedCheck_3272_ == 0)
{
v___x_3267_ = v___x_3258_;
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
else
{
lean_inc(v_a_3265_);
lean_dec(v___x_3258_);
v___x_3267_ = lean_box(0);
v_isShared_3268_ = v_isSharedCheck_3272_;
goto v_resetjp_3266_;
}
v_resetjp_3266_:
{
lean_object* v___x_3270_; 
if (v_isShared_3268_ == 0)
{
v___x_3270_ = v___x_3267_;
goto v_reusejp_3269_;
}
else
{
lean_object* v_reuseFailAlloc_3271_; 
v_reuseFailAlloc_3271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3271_, 0, v_a_3265_);
v___x_3270_ = v_reuseFailAlloc_3271_;
goto v_reusejp_3269_;
}
v_reusejp_3269_:
{
return v___x_3270_;
}
}
}
}
v___jp_3273_:
{
if (v___y_3278_ == 0)
{
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
v_a_3198_ = v___x_3250_;
goto v___jp_3197_;
}
else
{
v___y_3252_ = v___y_3275_;
v___y_3253_ = v___y_3274_;
v___y_3254_ = v___y_3276_;
v___y_3255_ = v___y_3277_;
goto v___jp_3251_;
}
}
v___jp_3280_:
{
if (v___y_3281_ == 0)
{
v___y_3252_ = v___y_3283_;
v___y_3253_ = v___y_3282_;
v___y_3254_ = v___y_3284_;
v___y_3255_ = v___y_3285_;
goto v___jp_3251_;
}
else
{
v___y_3274_ = v___y_3282_;
v___y_3275_ = v___y_3283_;
v___y_3276_ = v___y_3284_;
v___y_3277_ = v___y_3285_;
v___y_3278_ = v___x_3279_;
goto v___jp_3273_;
}
}
v___jp_3286_:
{
if (v___y_3292_ == 0)
{
v___y_3274_ = v___y_3289_;
v___y_3275_ = v___y_3288_;
v___y_3276_ = v___y_3290_;
v___y_3277_ = v___y_3291_;
v___y_3278_ = v___x_3279_;
goto v___jp_3273_;
}
else
{
v___y_3281_ = v___y_3287_;
v___y_3282_ = v___y_3289_;
v___y_3283_ = v___y_3288_;
v___y_3284_ = v___y_3290_;
v___y_3285_ = v___y_3291_;
goto v___jp_3280_;
}
}
v___jp_3293_:
{
uint8_t v_emptyType_3300_; 
v_emptyType_3300_ = lean_ctor_get_uint8(v_config_3172_, sizeof(void*)*1 + 1);
if (v_emptyType_3300_ == 0)
{
v___y_3287_ = v___y_3295_;
v___y_3288_ = v___y_3299_;
v___y_3289_ = v___y_3296_;
v___y_3290_ = v___y_3298_;
v___y_3291_ = v___y_3297_;
v___y_3292_ = v___x_3279_;
goto v___jp_3286_;
}
else
{
if (v___y_3294_ == 0)
{
v___y_3281_ = v___y_3295_;
v___y_3282_ = v___y_3296_;
v___y_3283_ = v___y_3299_;
v___y_3284_ = v___y_3298_;
v___y_3285_ = v___y_3297_;
goto v___jp_3280_;
}
else
{
v___y_3287_ = v___y_3295_;
v___y_3288_ = v___y_3299_;
v___y_3289_ = v___y_3296_;
v___y_3290_ = v___y_3298_;
v___y_3291_ = v___y_3297_;
v___y_3292_ = v___x_3279_;
goto v___jp_3286_;
}
}
}
v___jp_3301_:
{
if (v___y_3308_ == 0)
{
v___y_3294_ = v___y_3304_;
v___y_3295_ = v___y_3303_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3302_;
v___y_3298_ = v___y_3305_;
v___y_3299_ = v___y_3307_;
goto v___jp_3293_;
}
else
{
lean_object* v___x_3309_; 
lean_inc(v_val_3204_);
lean_inc(v_mvarId_3173_);
v___x_3309_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3173_, v_val_3204_, v___y_3306_, v___y_3302_, v___y_3305_, v___y_3307_);
if (lean_obj_tag(v___x_3309_) == 0)
{
lean_object* v_a_3310_; uint8_t v___x_3311_; 
v_a_3310_ = lean_ctor_get(v___x_3309_, 0);
lean_inc(v_a_3310_);
lean_dec_ref_known(v___x_3309_, 1);
v___x_3311_ = lean_unbox(v_a_3310_);
lean_dec(v_a_3310_);
if (v___x_3311_ == 0)
{
v___y_3294_ = v___y_3304_;
v___y_3295_ = v___y_3303_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3302_;
v___y_3298_ = v___y_3305_;
v___y_3299_ = v___y_3307_;
goto v___jp_3293_;
}
else
{
lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; 
lean_dec(v_val_3204_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v___x_3312_ = lean_box(v___x_3183_);
v___x_3313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
v___x_3314_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
lean_ctor_set(v___x_3314_, 1, v___x_3208_);
v___x_3315_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
v_a_3190_ = v___x_3315_;
goto v___jp_3189_;
}
}
else
{
lean_object* v_a_3316_; lean_object* v___x_3318_; uint8_t v_isShared_3319_; uint8_t v_isSharedCheck_3323_; 
lean_dec(v_val_3204_);
lean_del_object(v___x_3187_);
lean_dec(v_snd_3185_);
lean_dec(v_mvarId_3173_);
lean_dec_ref(v_config_3172_);
v_a_3316_ = lean_ctor_get(v___x_3309_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3309_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3318_ = v___x_3309_;
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
else
{
lean_inc(v_a_3316_);
lean_dec(v___x_3309_);
v___x_3318_ = lean_box(0);
v_isShared_3319_ = v_isSharedCheck_3323_;
goto v_resetjp_3317_;
}
v_resetjp_3317_:
{
lean_object* v___x_3321_; 
if (v_isShared_3319_ == 0)
{
v___x_3321_ = v___x_3318_;
goto v_reusejp_3320_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v_a_3316_);
v___x_3321_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3320_;
}
v_reusejp_3320_:
{
return v___x_3321_;
}
}
}
}
}
}
}
v___jp_3189_:
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
v___x_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3191_, 0, v_a_3190_);
if (v_isShared_3188_ == 0)
{
lean_ctor_set(v___x_3187_, 0, v___x_3191_);
v___x_3193_ = v___x_3187_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3191_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v_snd_3185_);
v___x_3193_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
lean_object* v___x_3194_; 
v___x_3194_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3194_, 0, v___x_3193_);
return v___x_3194_;
}
}
v___jp_3197_:
{
lean_object* v___x_3199_; size_t v___x_3200_; size_t v___x_3201_; 
v___x_3199_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3199_, 0, v___x_3196_);
lean_ctor_set(v___x_3199_, 1, v_a_3198_);
v___x_3200_ = ((size_t)1ULL);
v___x_3201_ = lean_usize_add(v_i_3176_, v___x_3200_);
v_i_3176_ = v___x_3201_;
v_b_3177_ = v___x_3199_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3857_, lean_object* v_mvarId_3858_, lean_object* v_as_3859_, lean_object* v_sz_3860_, lean_object* v_i_3861_, lean_object* v_b_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_){
_start:
{
size_t v_sz_boxed_3868_; size_t v_i_boxed_3869_; lean_object* v_res_3870_; 
v_sz_boxed_3868_ = lean_unbox_usize(v_sz_3860_);
lean_dec(v_sz_3860_);
v_i_boxed_3869_ = lean_unbox_usize(v_i_3861_);
lean_dec(v_i_3861_);
v_res_3870_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3857_, v_mvarId_3858_, v_as_3859_, v_sz_boxed_3868_, v_i_boxed_3869_, v_b_3862_, v___y_3863_, v___y_3864_, v___y_3865_, v___y_3866_);
lean_dec(v___y_3866_);
lean_dec_ref(v___y_3865_);
lean_dec(v___y_3864_);
lean_dec_ref(v___y_3863_);
lean_dec_ref(v_as_3859_);
return v_res_3870_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3871_, lean_object* v_mvarId_3872_, lean_object* v_as_3873_, size_t v_sz_3874_, size_t v_i_3875_, lean_object* v_b_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_){
_start:
{
uint8_t v___x_3882_; 
v___x_3882_ = lean_usize_dec_lt(v_i_3875_, v_sz_3874_);
if (v___x_3882_ == 0)
{
lean_object* v___x_3883_; 
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v_b_3876_);
return v___x_3883_;
}
else
{
lean_object* v_snd_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_4554_; 
v_snd_3884_ = lean_ctor_get(v_b_3876_, 1);
v_isSharedCheck_4554_ = !lean_is_exclusive(v_b_3876_);
if (v_isSharedCheck_4554_ == 0)
{
lean_object* v_unused_4555_; 
v_unused_4555_ = lean_ctor_get(v_b_3876_, 0);
lean_dec(v_unused_4555_);
v___x_3886_ = v_b_3876_;
v_isShared_3887_ = v_isSharedCheck_4554_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_snd_3884_);
lean_dec(v_b_3876_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_4554_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v_a_3889_; lean_object* v___x_3895_; lean_object* v_a_3897_; lean_object* v_a_3902_; 
v___x_3895_ = lean_box(0);
v_a_3902_ = lean_array_uget(v_as_3873_, v_i_3875_);
if (lean_obj_tag(v_a_3902_) == 0)
{
lean_del_object(v___x_3886_);
v_a_3897_ = v_snd_3884_;
goto v___jp_3896_;
}
else
{
lean_object* v_val_3903_; lean_object* v___x_3905_; uint8_t v_isShared_3906_; uint8_t v_isSharedCheck_4553_; 
v_val_3903_ = lean_ctor_get(v_a_3902_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v_a_3902_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_3905_ = v_a_3902_;
v_isShared_3906_ = v_isSharedCheck_4553_;
goto v_resetjp_3904_;
}
else
{
lean_inc(v_val_3903_);
lean_dec(v_a_3902_);
v___x_3905_ = lean_box(0);
v_isShared_3906_ = v_isSharedCheck_4553_;
goto v_resetjp_3904_;
}
v_resetjp_3904_:
{
lean_object* v___x_3907_; lean_object* v___y_3909_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___x_3949_; lean_object* v___y_3951_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3973_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; uint8_t v___y_3977_; uint8_t v___x_3978_; lean_object* v___y_3980_; lean_object* v___y_3981_; lean_object* v___y_3982_; uint8_t v___y_3983_; lean_object* v___y_3984_; lean_object* v___y_3986_; lean_object* v___y_3987_; uint8_t v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; uint8_t v___y_3991_; uint8_t v___y_3993_; uint8_t v___y_3994_; lean_object* v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; uint8_t v___y_4001_; lean_object* v___y_4002_; uint8_t v___y_4003_; lean_object* v___y_4004_; lean_object* v___y_4005_; lean_object* v___y_4006_; uint8_t v___y_4007_; 
v___x_3907_ = lean_box(0);
v___x_3949_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3978_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3903_);
if (v___x_3978_ == 0)
{
lean_object* v___x_4023_; uint8_t v___y_4025_; uint8_t v___y_4026_; lean_object* v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; uint8_t v___y_4034_; lean_object* v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; uint8_t v___y_4039_; lean_object* v___y_4040_; uint8_t v___y_4041_; uint8_t v___y_4044_; lean_object* v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; uint8_t v___y_4048_; lean_object* v___y_4049_; lean_object* v_a_4050_; uint8_t v___y_4054_; lean_object* v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; uint8_t v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; lean_object* v___y_4061_; uint8_t v___y_4105_; lean_object* v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; uint8_t v___y_4109_; lean_object* v___y_4110_; uint8_t v___y_4134_; lean_object* v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; uint8_t v___y_4138_; lean_object* v___y_4139_; uint8_t v___y_4140_; uint8_t v___y_4142_; lean_object* v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; uint8_t v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; uint8_t v___y_4149_; uint8_t v___y_4152_; lean_object* v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; uint8_t v___y_4156_; lean_object* v___y_4157_; uint8_t v___y_4158_; uint8_t v___y_4171_; lean_object* v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; uint8_t v___y_4175_; lean_object* v___y_4176_; uint8_t v___y_4177_; uint8_t v___y_4179_; uint8_t v_isHEq_4180_; lean_object* v___y_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; uint8_t v___y_4188_; lean_object* v___y_4189_; lean_object* v___y_4190_; lean_object* v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; uint8_t v_isEq_4251_; lean_object* v___y_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4301_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4347_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___x_4483_; 
v___x_4023_ = l_Lean_LocalDecl_type(v_val_3903_);
lean_inc_ref(v___x_4023_);
v___x_4483_ = l_Lean_Meta_matchNot_x3f(v___x_4023_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
if (lean_obj_tag(v___x_4483_) == 0)
{
lean_object* v_a_4484_; 
v_a_4484_ = lean_ctor_get(v___x_4483_, 0);
lean_inc(v_a_4484_);
lean_dec_ref_known(v___x_4483_, 1);
if (lean_obj_tag(v_a_4484_) == 1)
{
lean_object* v_val_4485_; lean_object* v___x_4487_; uint8_t v_isShared_4488_; uint8_t v_isSharedCheck_4544_; 
v_val_4485_ = lean_ctor_get(v_a_4484_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v_a_4484_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4487_ = v_a_4484_;
v_isShared_4488_ = v_isSharedCheck_4544_;
goto v_resetjp_4486_;
}
else
{
lean_inc(v_val_4485_);
lean_dec(v_a_4484_);
v___x_4487_ = lean_box(0);
v_isShared_4488_ = v_isSharedCheck_4544_;
goto v_resetjp_4486_;
}
v_resetjp_4486_:
{
lean_object* v___x_4489_; 
v___x_4489_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4485_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
if (lean_obj_tag(v___x_4489_) == 0)
{
lean_object* v_a_4490_; 
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
lean_inc(v_a_4490_);
lean_dec_ref_known(v___x_4489_, 1);
if (lean_obj_tag(v_a_4490_) == 1)
{
lean_object* v_val_4491_; lean_object* v___x_4493_; uint8_t v_isShared_4494_; uint8_t v_isSharedCheck_4535_; 
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec_ref(v_config_3871_);
v_val_4491_ = lean_ctor_get(v_a_4490_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v_a_4490_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4493_ = v_a_4490_;
v_isShared_4494_ = v_isSharedCheck_4535_;
goto v_resetjp_4492_;
}
else
{
lean_inc(v_val_4491_);
lean_dec(v_a_4490_);
v___x_4493_ = lean_box(0);
v_isShared_4494_ = v_isSharedCheck_4535_;
goto v_resetjp_4492_;
}
v_resetjp_4492_:
{
lean_object* v___x_4495_; 
lean_inc(v_mvarId_3872_);
v___x_4495_ = l_Lean_MVarId_getType(v_mvarId_3872_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
if (lean_obj_tag(v___x_4495_) == 0)
{
lean_object* v_a_4496_; lean_object* v___x_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; 
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref_known(v___x_4495_, 1);
v___x_4497_ = l_Lean_LocalDecl_toExpr(v_val_3903_);
v___x_4498_ = l_Lean_mkFVar(v_val_4491_);
v___x_4499_ = l_Lean_Expr_app___override(v___x_4497_, v___x_4498_);
v___x_4500_ = l_Lean_Meta_mkFalseElim(v_a_4496_, v___x_4499_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; lean_object* v___x_4502_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref_known(v___x_4500_, 1);
v___x_4502_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3872_, v_a_4501_, v___y_3878_);
if (lean_obj_tag(v___x_4502_) == 0)
{
lean_object* v___x_4503_; lean_object* v___x_4505_; 
lean_dec_ref_known(v___x_4502_, 1);
v___x_4503_ = lean_box(v___x_3882_);
if (v_isShared_4494_ == 0)
{
lean_ctor_set(v___x_4493_, 0, v___x_4503_);
v___x_4505_ = v___x_4493_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4503_);
v___x_4505_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
lean_object* v___x_4506_; lean_object* v___x_4508_; 
v___x_4506_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4506_, 0, v___x_4505_);
lean_ctor_set(v___x_4506_, 1, v___x_3907_);
if (v_isShared_4488_ == 0)
{
lean_ctor_set_tag(v___x_4487_, 0);
lean_ctor_set(v___x_4487_, 0, v___x_4506_);
v___x_4508_ = v___x_4487_;
goto v_reusejp_4507_;
}
else
{
lean_object* v_reuseFailAlloc_4509_; 
v_reuseFailAlloc_4509_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4509_, 0, v___x_4506_);
v___x_4508_ = v_reuseFailAlloc_4509_;
goto v_reusejp_4507_;
}
v_reusejp_4507_:
{
v_a_3889_ = v___x_4508_;
goto v___jp_3888_;
}
}
}
else
{
lean_object* v_a_4511_; lean_object* v___x_4513_; uint8_t v_isShared_4514_; uint8_t v_isSharedCheck_4518_; 
lean_del_object(v___x_4493_);
lean_del_object(v___x_4487_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
v_a_4511_ = lean_ctor_get(v___x_4502_, 0);
v_isSharedCheck_4518_ = !lean_is_exclusive(v___x_4502_);
if (v_isSharedCheck_4518_ == 0)
{
v___x_4513_ = v___x_4502_;
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
else
{
lean_inc(v_a_4511_);
lean_dec(v___x_4502_);
v___x_4513_ = lean_box(0);
v_isShared_4514_ = v_isSharedCheck_4518_;
goto v_resetjp_4512_;
}
v_resetjp_4512_:
{
lean_object* v___x_4516_; 
if (v_isShared_4514_ == 0)
{
v___x_4516_ = v___x_4513_;
goto v_reusejp_4515_;
}
else
{
lean_object* v_reuseFailAlloc_4517_; 
v_reuseFailAlloc_4517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4517_, 0, v_a_4511_);
v___x_4516_ = v_reuseFailAlloc_4517_;
goto v_reusejp_4515_;
}
v_reusejp_4515_:
{
return v___x_4516_;
}
}
}
}
else
{
lean_object* v_a_4519_; lean_object* v___x_4521_; uint8_t v_isShared_4522_; uint8_t v_isSharedCheck_4526_; 
lean_del_object(v___x_4493_);
lean_del_object(v___x_4487_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_4519_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4526_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4526_ == 0)
{
v___x_4521_ = v___x_4500_;
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
else
{
lean_inc(v_a_4519_);
lean_dec(v___x_4500_);
v___x_4521_ = lean_box(0);
v_isShared_4522_ = v_isSharedCheck_4526_;
goto v_resetjp_4520_;
}
v_resetjp_4520_:
{
lean_object* v___x_4524_; 
if (v_isShared_4522_ == 0)
{
v___x_4524_ = v___x_4521_;
goto v_reusejp_4523_;
}
else
{
lean_object* v_reuseFailAlloc_4525_; 
v_reuseFailAlloc_4525_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4525_, 0, v_a_4519_);
v___x_4524_ = v_reuseFailAlloc_4525_;
goto v_reusejp_4523_;
}
v_reusejp_4523_:
{
return v___x_4524_;
}
}
}
}
else
{
lean_object* v_a_4527_; lean_object* v___x_4529_; uint8_t v_isShared_4530_; uint8_t v_isSharedCheck_4534_; 
lean_del_object(v___x_4493_);
lean_dec(v_val_4491_);
lean_del_object(v___x_4487_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_4527_ = lean_ctor_get(v___x_4495_, 0);
v_isSharedCheck_4534_ = !lean_is_exclusive(v___x_4495_);
if (v_isSharedCheck_4534_ == 0)
{
v___x_4529_ = v___x_4495_;
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
else
{
lean_inc(v_a_4527_);
lean_dec(v___x_4495_);
v___x_4529_ = lean_box(0);
v_isShared_4530_ = v_isSharedCheck_4534_;
goto v_resetjp_4528_;
}
v_resetjp_4528_:
{
lean_object* v___x_4532_; 
if (v_isShared_4530_ == 0)
{
v___x_4532_ = v___x_4529_;
goto v_reusejp_4531_;
}
else
{
lean_object* v_reuseFailAlloc_4533_; 
v_reuseFailAlloc_4533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4533_, 0, v_a_4527_);
v___x_4532_ = v_reuseFailAlloc_4533_;
goto v_reusejp_4531_;
}
v_reusejp_4531_:
{
return v___x_4532_;
}
}
}
}
}
else
{
lean_dec(v_a_4490_);
lean_del_object(v___x_4487_);
v___y_4347_ = v___y_3877_;
v___y_4348_ = v___y_3878_;
v___y_4349_ = v___y_3879_;
v___y_4350_ = v___y_3880_;
goto v___jp_4346_;
}
}
else
{
lean_object* v_a_4536_; lean_object* v___x_4538_; uint8_t v_isShared_4539_; uint8_t v_isSharedCheck_4543_; 
lean_del_object(v___x_4487_);
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4536_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4543_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4543_ == 0)
{
v___x_4538_ = v___x_4489_;
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
else
{
lean_inc(v_a_4536_);
lean_dec(v___x_4489_);
v___x_4538_ = lean_box(0);
v_isShared_4539_ = v_isSharedCheck_4543_;
goto v_resetjp_4537_;
}
v_resetjp_4537_:
{
lean_object* v___x_4541_; 
if (v_isShared_4539_ == 0)
{
v___x_4541_ = v___x_4538_;
goto v_reusejp_4540_;
}
else
{
lean_object* v_reuseFailAlloc_4542_; 
v_reuseFailAlloc_4542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4542_, 0, v_a_4536_);
v___x_4541_ = v_reuseFailAlloc_4542_;
goto v_reusejp_4540_;
}
v_reusejp_4540_:
{
return v___x_4541_;
}
}
}
}
}
else
{
lean_dec(v_a_4484_);
v___y_4347_ = v___y_3877_;
v___y_4348_ = v___y_3878_;
v___y_4349_ = v___y_3879_;
v___y_4350_ = v___y_3880_;
goto v___jp_4346_;
}
}
else
{
lean_object* v_a_4545_; lean_object* v___x_4547_; uint8_t v_isShared_4548_; uint8_t v_isSharedCheck_4552_; 
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4545_ = lean_ctor_get(v___x_4483_, 0);
v_isSharedCheck_4552_ = !lean_is_exclusive(v___x_4483_);
if (v_isSharedCheck_4552_ == 0)
{
v___x_4547_ = v___x_4483_;
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
else
{
lean_inc(v_a_4545_);
lean_dec(v___x_4483_);
v___x_4547_ = lean_box(0);
v_isShared_4548_ = v_isSharedCheck_4552_;
goto v_resetjp_4546_;
}
v_resetjp_4546_:
{
lean_object* v___x_4550_; 
if (v_isShared_4548_ == 0)
{
v___x_4550_ = v___x_4547_;
goto v_reusejp_4549_;
}
else
{
lean_object* v_reuseFailAlloc_4551_; 
v_reuseFailAlloc_4551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4551_, 0, v_a_4545_);
v___x_4550_ = v_reuseFailAlloc_4551_;
goto v_reusejp_4549_;
}
v_reusejp_4549_:
{
return v___x_4550_;
}
}
}
v___jp_4024_:
{
uint8_t v_genDiseq_4031_; 
v_genDiseq_4031_ = lean_ctor_get_uint8(v_config_3871_, sizeof(void*)*1 + 2);
if (v_genDiseq_4031_ == 0)
{
lean_dec_ref(v___x_4023_);
v___y_4001_ = v___y_4025_;
v___y_4002_ = v___y_4030_;
v___y_4003_ = v___y_4026_;
v___y_4004_ = v___y_4027_;
v___y_4005_ = v___y_4028_;
v___y_4006_ = v___y_4029_;
v___y_4007_ = v___x_3978_;
goto v___jp_4000_;
}
else
{
uint8_t v___x_4032_; 
v___x_4032_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4023_);
v___y_4001_ = v___y_4025_;
v___y_4002_ = v___y_4030_;
v___y_4003_ = v___y_4026_;
v___y_4004_ = v___y_4027_;
v___y_4005_ = v___y_4028_;
v___y_4006_ = v___y_4029_;
v___y_4007_ = v___x_4032_;
goto v___jp_4000_;
}
}
v___jp_4033_:
{
if (v___y_4041_ == 0)
{
lean_dec_ref(v___y_4035_);
v___y_4025_ = v___y_4034_;
v___y_4026_ = v___y_4039_;
v___y_4027_ = v___y_4036_;
v___y_4028_ = v___y_4040_;
v___y_4029_ = v___y_4037_;
v___y_4030_ = v___y_4038_;
goto v___jp_4024_;
}
else
{
lean_object* v___x_4042_; 
lean_dec_ref(v___x_4023_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v___x_4042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4042_, 0, v___y_4035_);
return v___x_4042_;
}
}
v___jp_4043_:
{
uint8_t v___x_4051_; 
v___x_4051_ = l_Lean_Exception_isInterrupt(v_a_4050_);
if (v___x_4051_ == 0)
{
uint8_t v___x_4052_; 
lean_inc_ref(v_a_4050_);
v___x_4052_ = l_Lean_Exception_isRuntime(v_a_4050_);
v___y_4034_ = v___y_4044_;
v___y_4035_ = v_a_4050_;
v___y_4036_ = v___y_4045_;
v___y_4037_ = v___y_4046_;
v___y_4038_ = v___y_4047_;
v___y_4039_ = v___y_4048_;
v___y_4040_ = v___y_4049_;
v___y_4041_ = v___x_4052_;
goto v___jp_4033_;
}
else
{
v___y_4034_ = v___y_4044_;
v___y_4035_ = v_a_4050_;
v___y_4036_ = v___y_4045_;
v___y_4037_ = v___y_4046_;
v___y_4038_ = v___y_4047_;
v___y_4039_ = v___y_4048_;
v___y_4040_ = v___y_4049_;
v___y_4041_ = v___x_4051_;
goto v___jp_4033_;
}
}
v___jp_4053_:
{
if (lean_obj_tag(v___y_4061_) == 0)
{
lean_object* v_a_4062_; lean_object* v___x_4063_; uint8_t v___x_4064_; 
v_a_4062_ = lean_ctor_get(v___y_4061_, 0);
lean_inc(v_a_4062_);
lean_dec_ref_known(v___y_4061_, 1);
v___x_4063_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_4064_ = l_Lean_Expr_isConstOf(v_a_4062_, v___x_4063_);
lean_dec(v_a_4062_);
if (v___x_4064_ == 0)
{
lean_dec_ref(v___y_4060_);
v___y_4025_ = v___y_4054_;
v___y_4026_ = v___y_4058_;
v___y_4027_ = v___y_4055_;
v___y_4028_ = v___y_4059_;
v___y_4029_ = v___y_4056_;
v___y_4030_ = v___y_4057_;
goto v___jp_4024_;
}
else
{
lean_object* v___x_4065_; 
lean_inc_ref(v___y_4060_);
v___x_4065_ = l_Lean_Meta_mkEqRefl(v___y_4060_, v___y_4055_, v___y_4059_, v___y_4056_, v___y_4057_);
if (lean_obj_tag(v___x_4065_) == 0)
{
lean_object* v_a_4066_; lean_object* v___x_4067_; lean_object* v_dummy_4068_; lean_object* v_nargs_4069_; lean_object* v___x_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; 
v_a_4066_ = lean_ctor_get(v___x_4065_, 0);
lean_inc(v_a_4066_);
lean_dec_ref_known(v___x_4065_, 1);
v___x_4067_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_4068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_4069_ = l_Lean_Expr_getAppNumArgs(v___y_4060_);
lean_inc(v_nargs_4069_);
v___x_4070_ = lean_mk_array(v_nargs_4069_, v_dummy_4068_);
v___x_4071_ = lean_unsigned_to_nat(1u);
v___x_4072_ = lean_nat_sub(v_nargs_4069_, v___x_4071_);
lean_dec(v_nargs_4069_);
v___x_4073_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_4060_, v___x_4070_, v___x_4072_);
v___x_4074_ = lean_array_push(v___x_4073_, v_a_4066_);
v___x_4075_ = l_Lean_mkAppN(v___x_4067_, v___x_4074_);
lean_dec_ref(v___x_4074_);
lean_inc(v_mvarId_3872_);
v___x_4076_ = l_Lean_MVarId_getType(v_mvarId_3872_, v___y_4055_, v___y_4059_, v___y_4056_, v___y_4057_);
if (lean_obj_tag(v___x_4076_) == 0)
{
lean_object* v_a_4077_; lean_object* v___x_4078_; lean_object* v___x_4079_; 
v_a_4077_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4077_);
lean_dec_ref_known(v___x_4076_, 1);
lean_inc(v_val_3903_);
v___x_4078_ = l_Lean_LocalDecl_toExpr(v_val_3903_);
v___x_4079_ = l_Lean_Meta_mkAbsurd(v_a_4077_, v___x_4078_, v___x_4075_, v___y_4055_, v___y_4059_, v___y_4056_, v___y_4057_);
if (lean_obj_tag(v___x_4079_) == 0)
{
lean_object* v_a_4080_; lean_object* v___x_4082_; uint8_t v_isShared_4083_; uint8_t v_isSharedCheck_4099_; 
v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
v_isSharedCheck_4099_ = !lean_is_exclusive(v___x_4079_);
if (v_isSharedCheck_4099_ == 0)
{
v___x_4082_ = v___x_4079_;
v_isShared_4083_ = v_isSharedCheck_4099_;
goto v_resetjp_4081_;
}
else
{
lean_inc(v_a_4080_);
lean_dec(v___x_4079_);
v___x_4082_ = lean_box(0);
v_isShared_4083_ = v_isSharedCheck_4099_;
goto v_resetjp_4081_;
}
v_resetjp_4081_:
{
lean_object* v___x_4084_; 
lean_inc(v_mvarId_3872_);
v___x_4084_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3872_, v_a_4080_, v___y_4059_);
if (lean_obj_tag(v___x_4084_) == 0)
{
lean_object* v___x_4086_; uint8_t v_isShared_4087_; uint8_t v_isSharedCheck_4096_; 
lean_dec_ref(v___x_4023_);
lean_dec(v_val_3903_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_isSharedCheck_4096_ = !lean_is_exclusive(v___x_4084_);
if (v_isSharedCheck_4096_ == 0)
{
lean_object* v_unused_4097_; 
v_unused_4097_ = lean_ctor_get(v___x_4084_, 0);
lean_dec(v_unused_4097_);
v___x_4086_ = v___x_4084_;
v_isShared_4087_ = v_isSharedCheck_4096_;
goto v_resetjp_4085_;
}
else
{
lean_dec(v___x_4084_);
v___x_4086_ = lean_box(0);
v_isShared_4087_ = v_isSharedCheck_4096_;
goto v_resetjp_4085_;
}
v_resetjp_4085_:
{
lean_object* v___x_4088_; lean_object* v___x_4090_; 
v___x_4088_ = lean_box(v___x_3882_);
if (v_isShared_4087_ == 0)
{
lean_ctor_set_tag(v___x_4086_, 1);
lean_ctor_set(v___x_4086_, 0, v___x_4088_);
v___x_4090_ = v___x_4086_;
goto v_reusejp_4089_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4088_);
v___x_4090_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4089_;
}
v_reusejp_4089_:
{
lean_object* v___x_4091_; lean_object* v___x_4093_; 
v___x_4091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4091_, 0, v___x_4090_);
lean_ctor_set(v___x_4091_, 1, v___x_3907_);
if (v_isShared_4083_ == 0)
{
lean_ctor_set(v___x_4082_, 0, v___x_4091_);
v___x_4093_ = v___x_4082_;
goto v_reusejp_4092_;
}
else
{
lean_object* v_reuseFailAlloc_4094_; 
v_reuseFailAlloc_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4094_, 0, v___x_4091_);
v___x_4093_ = v_reuseFailAlloc_4094_;
goto v_reusejp_4092_;
}
v_reusejp_4092_:
{
v_a_3889_ = v___x_4093_;
goto v___jp_3888_;
}
}
}
}
else
{
lean_object* v_a_4098_; 
lean_del_object(v___x_4082_);
v_a_4098_ = lean_ctor_get(v___x_4084_, 0);
lean_inc(v_a_4098_);
lean_dec_ref_known(v___x_4084_, 1);
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v___y_4058_;
v___y_4049_ = v___y_4059_;
v_a_4050_ = v_a_4098_;
goto v___jp_4043_;
}
}
}
else
{
lean_object* v_a_4100_; 
v_a_4100_ = lean_ctor_get(v___x_4079_, 0);
lean_inc(v_a_4100_);
lean_dec_ref_known(v___x_4079_, 1);
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v___y_4058_;
v___y_4049_ = v___y_4059_;
v_a_4050_ = v_a_4100_;
goto v___jp_4043_;
}
}
else
{
lean_object* v_a_4101_; 
lean_dec_ref(v___x_4075_);
v_a_4101_ = lean_ctor_get(v___x_4076_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___x_4076_, 1);
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v___y_4058_;
v___y_4049_ = v___y_4059_;
v_a_4050_ = v_a_4101_;
goto v___jp_4043_;
}
}
else
{
lean_object* v_a_4102_; 
lean_dec_ref(v___y_4060_);
v_a_4102_ = lean_ctor_get(v___x_4065_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4065_, 1);
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v___y_4058_;
v___y_4049_ = v___y_4059_;
v_a_4050_ = v_a_4102_;
goto v___jp_4043_;
}
}
}
else
{
lean_object* v_a_4103_; 
lean_dec_ref(v___y_4060_);
v_a_4103_ = lean_ctor_get(v___y_4061_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v___y_4061_, 1);
v___y_4044_ = v___y_4054_;
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4056_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v___y_4058_;
v___y_4049_ = v___y_4059_;
v_a_4050_ = v_a_4103_;
goto v___jp_4043_;
}
}
v___jp_4104_:
{
lean_object* v___x_4111_; 
lean_inc_ref(v___x_4023_);
v___x_4111_ = l_Lean_Meta_mkDecide(v___x_4023_, v___y_4106_, v___y_4110_, v___y_4107_, v___y_4108_);
if (lean_obj_tag(v___x_4111_) == 0)
{
lean_object* v_a_4112_; lean_object* v___x_4113_; uint8_t v_transparency_4114_; uint8_t v___x_4115_; uint8_t v___x_4116_; 
v_a_4112_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4112_);
lean_dec_ref_known(v___x_4111_, 1);
v___x_4113_ = l_Lean_Meta_Context_config(v___y_4106_);
v_transparency_4114_ = lean_ctor_get_uint8(v___x_4113_, 9);
lean_dec_ref(v___x_4113_);
v___x_4115_ = 1;
v___x_4116_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4114_, v___x_4115_);
if (v___x_4116_ == 0)
{
lean_object* v_keyedConfig_4117_; uint8_t v_trackZetaDelta_4118_; lean_object* v_zetaDeltaSet_4119_; lean_object* v_lctx_4120_; lean_object* v_localInstances_4121_; lean_object* v_defEqCtx_x3f_4122_; lean_object* v_synthPendingDepth_4123_; lean_object* v_customCanUnfoldPredicate_x3f_4124_; uint8_t v_univApprox_4125_; uint8_t v_inTypeClassResolution_4126_; uint8_t v_cacheInferType_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v_keyedConfig_4117_ = lean_ctor_get(v___y_4106_, 0);
v_trackZetaDelta_4118_ = lean_ctor_get_uint8(v___y_4106_, sizeof(void*)*7);
v_zetaDeltaSet_4119_ = lean_ctor_get(v___y_4106_, 1);
v_lctx_4120_ = lean_ctor_get(v___y_4106_, 2);
v_localInstances_4121_ = lean_ctor_get(v___y_4106_, 3);
v_defEqCtx_x3f_4122_ = lean_ctor_get(v___y_4106_, 4);
v_synthPendingDepth_4123_ = lean_ctor_get(v___y_4106_, 5);
v_customCanUnfoldPredicate_x3f_4124_ = lean_ctor_get(v___y_4106_, 6);
v_univApprox_4125_ = lean_ctor_get_uint8(v___y_4106_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4126_ = lean_ctor_get_uint8(v___y_4106_, sizeof(void*)*7 + 2);
v_cacheInferType_4127_ = lean_ctor_get_uint8(v___y_4106_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4117_);
v___x_4128_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4115_, v_keyedConfig_4117_);
lean_inc(v_customCanUnfoldPredicate_x3f_4124_);
lean_inc(v_synthPendingDepth_4123_);
lean_inc(v_defEqCtx_x3f_4122_);
lean_inc_ref(v_localInstances_4121_);
lean_inc_ref(v_lctx_4120_);
lean_inc(v_zetaDeltaSet_4119_);
v___x_4129_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4129_, 0, v___x_4128_);
lean_ctor_set(v___x_4129_, 1, v_zetaDeltaSet_4119_);
lean_ctor_set(v___x_4129_, 2, v_lctx_4120_);
lean_ctor_set(v___x_4129_, 3, v_localInstances_4121_);
lean_ctor_set(v___x_4129_, 4, v_defEqCtx_x3f_4122_);
lean_ctor_set(v___x_4129_, 5, v_synthPendingDepth_4123_);
lean_ctor_set(v___x_4129_, 6, v_customCanUnfoldPredicate_x3f_4124_);
lean_ctor_set_uint8(v___x_4129_, sizeof(void*)*7, v_trackZetaDelta_4118_);
lean_ctor_set_uint8(v___x_4129_, sizeof(void*)*7 + 1, v_univApprox_4125_);
lean_ctor_set_uint8(v___x_4129_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4126_);
lean_ctor_set_uint8(v___x_4129_, sizeof(void*)*7 + 3, v_cacheInferType_4127_);
lean_inc(v___y_4108_);
lean_inc_ref(v___y_4107_);
lean_inc(v___y_4110_);
lean_inc(v_a_4112_);
v___x_4130_ = lean_whnf(v_a_4112_, v___x_4129_, v___y_4110_, v___y_4107_, v___y_4108_);
v___y_4054_ = v___y_4105_;
v___y_4055_ = v___y_4106_;
v___y_4056_ = v___y_4107_;
v___y_4057_ = v___y_4108_;
v___y_4058_ = v___y_4109_;
v___y_4059_ = v___y_4110_;
v___y_4060_ = v_a_4112_;
v___y_4061_ = v___x_4130_;
goto v___jp_4053_;
}
else
{
lean_object* v___x_4131_; 
lean_inc(v___y_4108_);
lean_inc_ref(v___y_4107_);
lean_inc(v___y_4110_);
lean_inc_ref(v___y_4106_);
lean_inc(v_a_4112_);
v___x_4131_ = lean_whnf(v_a_4112_, v___y_4106_, v___y_4110_, v___y_4107_, v___y_4108_);
v___y_4054_ = v___y_4105_;
v___y_4055_ = v___y_4106_;
v___y_4056_ = v___y_4107_;
v___y_4057_ = v___y_4108_;
v___y_4058_ = v___y_4109_;
v___y_4059_ = v___y_4110_;
v___y_4060_ = v_a_4112_;
v___y_4061_ = v___x_4131_;
goto v___jp_4053_;
}
}
else
{
lean_object* v_a_4132_; 
v_a_4132_ = lean_ctor_get(v___x_4111_, 0);
lean_inc(v_a_4132_);
lean_dec_ref_known(v___x_4111_, 1);
v___y_4044_ = v___y_4105_;
v___y_4045_ = v___y_4106_;
v___y_4046_ = v___y_4107_;
v___y_4047_ = v___y_4108_;
v___y_4048_ = v___y_4109_;
v___y_4049_ = v___y_4110_;
v_a_4050_ = v_a_4132_;
goto v___jp_4043_;
}
}
v___jp_4133_:
{
if (v___y_4140_ == 0)
{
v___y_4025_ = v___y_4134_;
v___y_4026_ = v___y_4138_;
v___y_4027_ = v___y_4135_;
v___y_4028_ = v___y_4139_;
v___y_4029_ = v___y_4136_;
v___y_4030_ = v___y_4137_;
goto v___jp_4024_;
}
else
{
v___y_4105_ = v___y_4134_;
v___y_4106_ = v___y_4135_;
v___y_4107_ = v___y_4136_;
v___y_4108_ = v___y_4137_;
v___y_4109_ = v___y_4138_;
v___y_4110_ = v___y_4139_;
goto v___jp_4104_;
}
}
v___jp_4141_:
{
if (v___y_4149_ == 0)
{
lean_dec_ref(v___y_4148_);
v___y_4134_ = v___y_4142_;
v___y_4135_ = v___y_4143_;
v___y_4136_ = v___y_4144_;
v___y_4137_ = v___y_4145_;
v___y_4138_ = v___y_4146_;
v___y_4139_ = v___y_4147_;
v___y_4140_ = v___x_3978_;
goto v___jp_4133_;
}
else
{
uint8_t v___x_4150_; 
v___x_4150_ = l_Lean_Expr_hasFVar(v___y_4148_);
lean_dec_ref(v___y_4148_);
if (v___x_4150_ == 0)
{
v___y_4105_ = v___y_4142_;
v___y_4106_ = v___y_4143_;
v___y_4107_ = v___y_4144_;
v___y_4108_ = v___y_4145_;
v___y_4109_ = v___y_4146_;
v___y_4110_ = v___y_4147_;
goto v___jp_4104_;
}
else
{
v___y_4134_ = v___y_4142_;
v___y_4135_ = v___y_4143_;
v___y_4136_ = v___y_4144_;
v___y_4137_ = v___y_4145_;
v___y_4138_ = v___y_4146_;
v___y_4139_ = v___y_4147_;
v___y_4140_ = v___x_3978_;
goto v___jp_4133_;
}
}
}
v___jp_4151_:
{
lean_object* v___x_4159_; 
lean_inc_ref(v___x_4023_);
v___x_4159_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4023_, v___y_4157_);
if (lean_obj_tag(v___x_4159_) == 0)
{
lean_object* v_a_4160_; uint8_t v___x_4161_; 
v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
lean_inc(v_a_4160_);
lean_dec_ref_known(v___x_4159_, 1);
v___x_4161_ = l_Lean_Expr_hasMVar(v_a_4160_);
if (v___x_4161_ == 0)
{
v___y_4142_ = v___y_4152_;
v___y_4143_ = v___y_4153_;
v___y_4144_ = v___y_4154_;
v___y_4145_ = v___y_4155_;
v___y_4146_ = v___y_4156_;
v___y_4147_ = v___y_4157_;
v___y_4148_ = v_a_4160_;
v___y_4149_ = v___y_4158_;
goto v___jp_4141_;
}
else
{
v___y_4142_ = v___y_4152_;
v___y_4143_ = v___y_4153_;
v___y_4144_ = v___y_4154_;
v___y_4145_ = v___y_4155_;
v___y_4146_ = v___y_4156_;
v___y_4147_ = v___y_4157_;
v___y_4148_ = v_a_4160_;
v___y_4149_ = v___x_3978_;
goto v___jp_4141_;
}
}
else
{
lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4169_; 
lean_dec_ref(v___x_4023_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4162_ = lean_ctor_get(v___x_4159_, 0);
v_isSharedCheck_4169_ = !lean_is_exclusive(v___x_4159_);
if (v_isSharedCheck_4169_ == 0)
{
v___x_4164_ = v___x_4159_;
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4159_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4169_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4167_; 
if (v_isShared_4165_ == 0)
{
v___x_4167_ = v___x_4164_;
goto v_reusejp_4166_;
}
else
{
lean_object* v_reuseFailAlloc_4168_; 
v_reuseFailAlloc_4168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4168_, 0, v_a_4162_);
v___x_4167_ = v_reuseFailAlloc_4168_;
goto v_reusejp_4166_;
}
v_reusejp_4166_:
{
return v___x_4167_;
}
}
}
}
v___jp_4170_:
{
if (v___y_4177_ == 0)
{
v___y_4025_ = v___y_4171_;
v___y_4026_ = v___y_4175_;
v___y_4027_ = v___y_4172_;
v___y_4028_ = v___y_4176_;
v___y_4029_ = v___y_4173_;
v___y_4030_ = v___y_4174_;
goto v___jp_4024_;
}
else
{
v___y_4152_ = v___y_4171_;
v___y_4153_ = v___y_4172_;
v___y_4154_ = v___y_4173_;
v___y_4155_ = v___y_4174_;
v___y_4156_ = v___y_4175_;
v___y_4157_ = v___y_4176_;
v___y_4158_ = v___y_4177_;
goto v___jp_4151_;
}
}
v___jp_4178_:
{
uint8_t v_useDecide_4185_; 
v_useDecide_4185_ = lean_ctor_get_uint8(v_config_3871_, sizeof(void*)*1);
if (v_useDecide_4185_ == 0)
{
v___y_4171_ = v___y_4179_;
v___y_4172_ = v___y_4181_;
v___y_4173_ = v___y_4183_;
v___y_4174_ = v___y_4184_;
v___y_4175_ = v_isHEq_4180_;
v___y_4176_ = v___y_4182_;
v___y_4177_ = v___x_3978_;
goto v___jp_4170_;
}
else
{
uint8_t v___x_4186_; 
v___x_4186_ = l_Lean_Expr_hasFVar(v___x_4023_);
if (v___x_4186_ == 0)
{
v___y_4152_ = v___y_4179_;
v___y_4153_ = v___y_4181_;
v___y_4154_ = v___y_4183_;
v___y_4155_ = v___y_4184_;
v___y_4156_ = v_isHEq_4180_;
v___y_4157_ = v___y_4182_;
v___y_4158_ = v_useDecide_4185_;
goto v___jp_4151_;
}
else
{
v___y_4171_ = v___y_4179_;
v___y_4172_ = v___y_4181_;
v___y_4173_ = v___y_4183_;
v___y_4174_ = v___y_4184_;
v___y_4175_ = v_isHEq_4180_;
v___y_4176_ = v___y_4182_;
v___y_4177_ = v___x_3978_;
goto v___jp_4170_;
}
}
}
v___jp_4187_:
{
lean_object* v___x_4195_; 
v___x_4195_ = l_Lean_Meta_isExprDefEq(v___y_4194_, v___y_4192_, v___y_4189_, v___y_4191_, v___y_4190_, v___y_4193_);
if (lean_obj_tag(v___x_4195_) == 0)
{
lean_object* v_a_4196_; uint8_t v___x_4197_; 
v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
lean_inc(v_a_4196_);
lean_dec_ref_known(v___x_4195_, 1);
v___x_4197_ = lean_unbox(v_a_4196_);
lean_dec(v_a_4196_);
if (v___x_4197_ == 0)
{
v___y_4179_ = v___y_4188_;
v_isHEq_4180_ = v___x_3882_;
v___y_4181_ = v___y_4189_;
v___y_4182_ = v___y_4191_;
v___y_4183_ = v___y_4190_;
v___y_4184_ = v___y_4193_;
goto v___jp_4178_;
}
else
{
lean_object* v___x_4198_; 
lean_dec_ref(v___x_4023_);
lean_dec_ref(v_config_3871_);
lean_inc(v_mvarId_3872_);
v___x_4198_ = l_Lean_MVarId_getType(v_mvarId_3872_, v___y_4189_, v___y_4191_, v___y_4190_, v___y_4193_);
if (lean_obj_tag(v___x_4198_) == 0)
{
lean_object* v_a_4199_; lean_object* v___x_4200_; lean_object* v___x_4201_; 
v_a_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc(v_a_4199_);
lean_dec_ref_known(v___x_4198_, 1);
v___x_4200_ = l_Lean_LocalDecl_toExpr(v_val_3903_);
v___x_4201_ = l_Lean_Meta_mkEqOfHEq(v___x_4200_, v___x_3882_, v___y_4189_, v___y_4191_, v___y_4190_, v___y_4193_);
if (lean_obj_tag(v___x_4201_) == 0)
{
lean_object* v_a_4202_; lean_object* v___x_4203_; 
v_a_4202_ = lean_ctor_get(v___x_4201_, 0);
lean_inc(v_a_4202_);
lean_dec_ref_known(v___x_4201_, 1);
v___x_4203_ = l_Lean_Meta_mkNoConfusion(v_a_4199_, v_a_4202_, v___y_4189_, v___y_4191_, v___y_4190_, v___y_4193_);
if (lean_obj_tag(v___x_4203_) == 0)
{
lean_object* v_a_4204_; lean_object* v___x_4205_; 
v_a_4204_ = lean_ctor_get(v___x_4203_, 0);
lean_inc(v_a_4204_);
lean_dec_ref_known(v___x_4203_, 1);
v___x_4205_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3872_, v_a_4204_, v___y_4191_);
if (lean_obj_tag(v___x_4205_) == 0)
{
lean_object* v___x_4206_; lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; 
lean_dec_ref_known(v___x_4205_, 1);
v___x_4206_ = lean_box(v___x_3882_);
v___x_4207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4207_, 0, v___x_4206_);
v___x_4208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
lean_ctor_set(v___x_4208_, 1, v___x_3907_);
v___x_4209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
v_a_3889_ = v___x_4209_;
goto v___jp_3888_;
}
else
{
lean_object* v_a_4210_; lean_object* v___x_4212_; uint8_t v_isShared_4213_; uint8_t v_isSharedCheck_4217_; 
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
v_a_4210_ = lean_ctor_get(v___x_4205_, 0);
v_isSharedCheck_4217_ = !lean_is_exclusive(v___x_4205_);
if (v_isSharedCheck_4217_ == 0)
{
v___x_4212_ = v___x_4205_;
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
else
{
lean_inc(v_a_4210_);
lean_dec(v___x_4205_);
v___x_4212_ = lean_box(0);
v_isShared_4213_ = v_isSharedCheck_4217_;
goto v_resetjp_4211_;
}
v_resetjp_4211_:
{
lean_object* v___x_4215_; 
if (v_isShared_4213_ == 0)
{
v___x_4215_ = v___x_4212_;
goto v_reusejp_4214_;
}
else
{
lean_object* v_reuseFailAlloc_4216_; 
v_reuseFailAlloc_4216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4216_, 0, v_a_4210_);
v___x_4215_ = v_reuseFailAlloc_4216_;
goto v_reusejp_4214_;
}
v_reusejp_4214_:
{
return v___x_4215_;
}
}
}
}
else
{
lean_object* v_a_4218_; lean_object* v___x_4220_; uint8_t v_isShared_4221_; uint8_t v_isSharedCheck_4225_; 
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_4218_ = lean_ctor_get(v___x_4203_, 0);
v_isSharedCheck_4225_ = !lean_is_exclusive(v___x_4203_);
if (v_isSharedCheck_4225_ == 0)
{
v___x_4220_ = v___x_4203_;
v_isShared_4221_ = v_isSharedCheck_4225_;
goto v_resetjp_4219_;
}
else
{
lean_inc(v_a_4218_);
lean_dec(v___x_4203_);
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
lean_object* v_a_4226_; lean_object* v___x_4228_; uint8_t v_isShared_4229_; uint8_t v_isSharedCheck_4233_; 
lean_dec(v_a_4199_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_4226_ = lean_ctor_get(v___x_4201_, 0);
v_isSharedCheck_4233_ = !lean_is_exclusive(v___x_4201_);
if (v_isSharedCheck_4233_ == 0)
{
v___x_4228_ = v___x_4201_;
v_isShared_4229_ = v_isSharedCheck_4233_;
goto v_resetjp_4227_;
}
else
{
lean_inc(v_a_4226_);
lean_dec(v___x_4201_);
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
lean_object* v_a_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4241_; 
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
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
}
else
{
lean_object* v_a_4242_; lean_object* v___x_4244_; uint8_t v_isShared_4245_; uint8_t v_isSharedCheck_4249_; 
lean_dec_ref(v___x_4023_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4242_ = lean_ctor_get(v___x_4195_, 0);
v_isSharedCheck_4249_ = !lean_is_exclusive(v___x_4195_);
if (v_isSharedCheck_4249_ == 0)
{
v___x_4244_ = v___x_4195_;
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
else
{
lean_inc(v_a_4242_);
lean_dec(v___x_4195_);
v___x_4244_ = lean_box(0);
v_isShared_4245_ = v_isSharedCheck_4249_;
goto v_resetjp_4243_;
}
v_resetjp_4243_:
{
lean_object* v___x_4247_; 
if (v_isShared_4245_ == 0)
{
v___x_4247_ = v___x_4244_;
goto v_reusejp_4246_;
}
else
{
lean_object* v_reuseFailAlloc_4248_; 
v_reuseFailAlloc_4248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4248_, 0, v_a_4242_);
v___x_4247_ = v_reuseFailAlloc_4248_;
goto v_reusejp_4246_;
}
v_reusejp_4246_:
{
return v___x_4247_;
}
}
}
}
v___jp_4250_:
{
lean_object* v___x_4256_; 
lean_inc_ref(v___x_4023_);
v___x_4256_ = l_Lean_Meta_matchHEq_x3f(v___x_4023_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
if (lean_obj_tag(v___x_4256_) == 0)
{
lean_object* v_a_4257_; 
v_a_4257_ = lean_ctor_get(v___x_4256_, 0);
lean_inc(v_a_4257_);
lean_dec_ref_known(v___x_4256_, 1);
if (lean_obj_tag(v_a_4257_) == 1)
{
lean_object* v_val_4258_; lean_object* v_snd_4259_; lean_object* v_snd_4260_; lean_object* v_fst_4261_; lean_object* v_fst_4262_; lean_object* v_fst_4263_; lean_object* v_snd_4264_; lean_object* v___x_4265_; 
v_val_4258_ = lean_ctor_get(v_a_4257_, 0);
lean_inc(v_val_4258_);
lean_dec_ref_known(v_a_4257_, 1);
v_snd_4259_ = lean_ctor_get(v_val_4258_, 1);
lean_inc(v_snd_4259_);
v_snd_4260_ = lean_ctor_get(v_snd_4259_, 1);
lean_inc(v_snd_4260_);
v_fst_4261_ = lean_ctor_get(v_val_4258_, 0);
lean_inc(v_fst_4261_);
lean_dec(v_val_4258_);
v_fst_4262_ = lean_ctor_get(v_snd_4259_, 0);
lean_inc(v_fst_4262_);
lean_dec(v_snd_4259_);
v_fst_4263_ = lean_ctor_get(v_snd_4260_, 0);
lean_inc(v_fst_4263_);
v_snd_4264_ = lean_ctor_get(v_snd_4260_, 1);
lean_inc(v_snd_4264_);
lean_dec(v_snd_4260_);
v___x_4265_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4262_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
if (lean_obj_tag(v___x_4265_) == 0)
{
lean_object* v_a_4266_; 
v_a_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc(v_a_4266_);
lean_dec_ref_known(v___x_4265_, 1);
if (lean_obj_tag(v_a_4266_) == 1)
{
lean_object* v_val_4267_; lean_object* v___x_4268_; 
v_val_4267_ = lean_ctor_get(v_a_4266_, 0);
lean_inc(v_val_4267_);
lean_dec_ref_known(v_a_4266_, 1);
v___x_4268_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4264_, v___y_4252_, v___y_4253_, v___y_4254_, v___y_4255_);
if (lean_obj_tag(v___x_4268_) == 0)
{
lean_object* v_a_4269_; 
v_a_4269_ = lean_ctor_get(v___x_4268_, 0);
lean_inc(v_a_4269_);
lean_dec_ref_known(v___x_4268_, 1);
if (lean_obj_tag(v_a_4269_) == 1)
{
lean_object* v_toConstantVal_4270_; lean_object* v_val_4271_; lean_object* v_toConstantVal_4272_; lean_object* v_name_4273_; lean_object* v_name_4274_; uint8_t v___x_4275_; 
v_toConstantVal_4270_ = lean_ctor_get(v_val_4267_, 0);
lean_inc_ref(v_toConstantVal_4270_);
lean_dec(v_val_4267_);
v_val_4271_ = lean_ctor_get(v_a_4269_, 0);
lean_inc(v_val_4271_);
lean_dec_ref_known(v_a_4269_, 1);
v_toConstantVal_4272_ = lean_ctor_get(v_val_4271_, 0);
lean_inc_ref(v_toConstantVal_4272_);
lean_dec(v_val_4271_);
v_name_4273_ = lean_ctor_get(v_toConstantVal_4270_, 0);
lean_inc(v_name_4273_);
lean_dec_ref(v_toConstantVal_4270_);
v_name_4274_ = lean_ctor_get(v_toConstantVal_4272_, 0);
lean_inc(v_name_4274_);
lean_dec_ref(v_toConstantVal_4272_);
v___x_4275_ = lean_name_eq(v_name_4273_, v_name_4274_);
lean_dec(v_name_4274_);
lean_dec(v_name_4273_);
if (v___x_4275_ == 0)
{
v___y_4188_ = v_isEq_4251_;
v___y_4189_ = v___y_4252_;
v___y_4190_ = v___y_4254_;
v___y_4191_ = v___y_4253_;
v___y_4192_ = v_fst_4263_;
v___y_4193_ = v___y_4255_;
v___y_4194_ = v_fst_4261_;
goto v___jp_4187_;
}
else
{
if (v___x_3978_ == 0)
{
lean_dec(v_fst_4263_);
lean_dec(v_fst_4261_);
v___y_4179_ = v_isEq_4251_;
v_isHEq_4180_ = v___x_3882_;
v___y_4181_ = v___y_4252_;
v___y_4182_ = v___y_4253_;
v___y_4183_ = v___y_4254_;
v___y_4184_ = v___y_4255_;
goto v___jp_4178_;
}
else
{
v___y_4188_ = v_isEq_4251_;
v___y_4189_ = v___y_4252_;
v___y_4190_ = v___y_4254_;
v___y_4191_ = v___y_4253_;
v___y_4192_ = v_fst_4263_;
v___y_4193_ = v___y_4255_;
v___y_4194_ = v_fst_4261_;
goto v___jp_4187_;
}
}
}
else
{
lean_dec(v_a_4269_);
lean_dec(v_val_4267_);
lean_dec(v_fst_4263_);
lean_dec(v_fst_4261_);
v___y_4179_ = v_isEq_4251_;
v_isHEq_4180_ = v___x_3882_;
v___y_4181_ = v___y_4252_;
v___y_4182_ = v___y_4253_;
v___y_4183_ = v___y_4254_;
v___y_4184_ = v___y_4255_;
goto v___jp_4178_;
}
}
else
{
lean_object* v_a_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
lean_dec(v_val_4267_);
lean_dec(v_fst_4263_);
lean_dec(v_fst_4261_);
lean_dec_ref(v___x_4023_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4276_ = lean_ctor_get(v___x_4268_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4268_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4268_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_a_4276_);
lean_dec(v___x_4268_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_a_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
else
{
lean_dec(v_a_4266_);
lean_dec(v_snd_4264_);
lean_dec(v_fst_4263_);
lean_dec(v_fst_4261_);
v___y_4179_ = v_isEq_4251_;
v_isHEq_4180_ = v___x_3882_;
v___y_4181_ = v___y_4252_;
v___y_4182_ = v___y_4253_;
v___y_4183_ = v___y_4254_;
v___y_4184_ = v___y_4255_;
goto v___jp_4178_;
}
}
else
{
lean_object* v_a_4284_; lean_object* v___x_4286_; uint8_t v_isShared_4287_; uint8_t v_isSharedCheck_4291_; 
lean_dec(v_snd_4264_);
lean_dec(v_fst_4263_);
lean_dec(v_fst_4261_);
lean_dec_ref(v___x_4023_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4284_ = lean_ctor_get(v___x_4265_, 0);
v_isSharedCheck_4291_ = !lean_is_exclusive(v___x_4265_);
if (v_isSharedCheck_4291_ == 0)
{
v___x_4286_ = v___x_4265_;
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
else
{
lean_inc(v_a_4284_);
lean_dec(v___x_4265_);
v___x_4286_ = lean_box(0);
v_isShared_4287_ = v_isSharedCheck_4291_;
goto v_resetjp_4285_;
}
v_resetjp_4285_:
{
lean_object* v___x_4289_; 
if (v_isShared_4287_ == 0)
{
v___x_4289_ = v___x_4286_;
goto v_reusejp_4288_;
}
else
{
lean_object* v_reuseFailAlloc_4290_; 
v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
v___x_4289_ = v_reuseFailAlloc_4290_;
goto v_reusejp_4288_;
}
v_reusejp_4288_:
{
return v___x_4289_;
}
}
}
}
else
{
lean_dec(v_a_4257_);
v___y_4179_ = v_isEq_4251_;
v_isHEq_4180_ = v___x_3978_;
v___y_4181_ = v___y_4252_;
v___y_4182_ = v___y_4253_;
v___y_4183_ = v___y_4254_;
v___y_4184_ = v___y_4255_;
goto v___jp_4178_;
}
}
else
{
lean_object* v_a_4292_; lean_object* v___x_4294_; uint8_t v_isShared_4295_; uint8_t v_isSharedCheck_4299_; 
lean_dec_ref(v___x_4023_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4292_ = lean_ctor_get(v___x_4256_, 0);
v_isSharedCheck_4299_ = !lean_is_exclusive(v___x_4256_);
if (v_isSharedCheck_4299_ == 0)
{
v___x_4294_ = v___x_4256_;
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
else
{
lean_inc(v_a_4292_);
lean_dec(v___x_4256_);
v___x_4294_ = lean_box(0);
v_isShared_4295_ = v_isSharedCheck_4299_;
goto v_resetjp_4293_;
}
v_resetjp_4293_:
{
lean_object* v___x_4297_; 
if (v_isShared_4295_ == 0)
{
v___x_4297_ = v___x_4294_;
goto v_reusejp_4296_;
}
else
{
lean_object* v_reuseFailAlloc_4298_; 
v_reuseFailAlloc_4298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4298_, 0, v_a_4292_);
v___x_4297_ = v_reuseFailAlloc_4298_;
goto v_reusejp_4296_;
}
v_reusejp_4296_:
{
return v___x_4297_;
}
}
}
}
v___jp_4300_:
{
lean_object* v___x_4305_; 
lean_inc_ref(v___x_4023_);
v___x_4305_ = l_Lean_Meta_matchEq_x3f(v___x_4023_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v_a_4306_; 
v_a_4306_ = lean_ctor_get(v___x_4305_, 0);
lean_inc(v_a_4306_);
lean_dec_ref_known(v___x_4305_, 1);
if (lean_obj_tag(v_a_4306_) == 1)
{
lean_object* v_val_4307_; lean_object* v_snd_4308_; lean_object* v_fst_4309_; lean_object* v_snd_4310_; lean_object* v___x_4311_; 
v_val_4307_ = lean_ctor_get(v_a_4306_, 0);
lean_inc(v_val_4307_);
lean_dec_ref_known(v_a_4306_, 1);
v_snd_4308_ = lean_ctor_get(v_val_4307_, 1);
lean_inc(v_snd_4308_);
lean_dec(v_val_4307_);
v_fst_4309_ = lean_ctor_get(v_snd_4308_, 0);
lean_inc(v_fst_4309_);
v_snd_4310_ = lean_ctor_get(v_snd_4308_, 1);
lean_inc(v_snd_4310_);
lean_dec(v_snd_4308_);
v___x_4311_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4309_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
lean_inc(v_a_4312_);
lean_dec_ref_known(v___x_4311_, 1);
if (lean_obj_tag(v_a_4312_) == 1)
{
lean_object* v_val_4313_; lean_object* v___x_4314_; 
v_val_4313_ = lean_ctor_get(v_a_4312_, 0);
lean_inc(v_val_4313_);
lean_dec_ref_known(v_a_4312_, 1);
v___x_4314_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4310_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref_known(v___x_4314_, 1);
if (lean_obj_tag(v_a_4315_) == 1)
{
lean_object* v_toConstantVal_4316_; lean_object* v_val_4317_; lean_object* v_toConstantVal_4318_; lean_object* v_name_4319_; lean_object* v_name_4320_; uint8_t v___x_4321_; 
v_toConstantVal_4316_ = lean_ctor_get(v_val_4313_, 0);
lean_inc_ref(v_toConstantVal_4316_);
lean_dec(v_val_4313_);
v_val_4317_ = lean_ctor_get(v_a_4315_, 0);
lean_inc(v_val_4317_);
lean_dec_ref_known(v_a_4315_, 1);
v_toConstantVal_4318_ = lean_ctor_get(v_val_4317_, 0);
lean_inc_ref(v_toConstantVal_4318_);
lean_dec(v_val_4317_);
v_name_4319_ = lean_ctor_get(v_toConstantVal_4316_, 0);
lean_inc(v_name_4319_);
lean_dec_ref(v_toConstantVal_4316_);
v_name_4320_ = lean_ctor_get(v_toConstantVal_4318_, 0);
lean_inc(v_name_4320_);
lean_dec_ref(v_toConstantVal_4318_);
v___x_4321_ = lean_name_eq(v_name_4319_, v_name_4320_);
lean_dec(v_name_4320_);
lean_dec(v_name_4319_);
if (v___x_4321_ == 0)
{
lean_dec_ref(v___x_4023_);
lean_dec_ref(v_config_3871_);
v___y_3909_ = v___y_4302_;
v___y_3910_ = v___y_4301_;
v___y_3911_ = v___y_4303_;
v___y_3912_ = v___y_4304_;
goto v___jp_3908_;
}
else
{
if (v___x_3978_ == 0)
{
lean_del_object(v___x_3905_);
v_isEq_4251_ = v___x_3882_;
v___y_4252_ = v___y_4301_;
v___y_4253_ = v___y_4302_;
v___y_4254_ = v___y_4303_;
v___y_4255_ = v___y_4304_;
goto v___jp_4250_;
}
else
{
lean_dec_ref(v___x_4023_);
lean_dec_ref(v_config_3871_);
v___y_3909_ = v___y_4302_;
v___y_3910_ = v___y_4301_;
v___y_3911_ = v___y_4303_;
v___y_3912_ = v___y_4304_;
goto v___jp_3908_;
}
}
}
else
{
lean_dec(v_a_4315_);
lean_dec(v_val_4313_);
lean_del_object(v___x_3905_);
v_isEq_4251_ = v___x_3882_;
v___y_4252_ = v___y_4301_;
v___y_4253_ = v___y_4302_;
v___y_4254_ = v___y_4303_;
v___y_4255_ = v___y_4304_;
goto v___jp_4250_;
}
}
else
{
lean_object* v_a_4322_; lean_object* v___x_4324_; uint8_t v_isShared_4325_; uint8_t v_isSharedCheck_4329_; 
lean_dec(v_val_4313_);
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4322_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4329_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4329_ == 0)
{
v___x_4324_ = v___x_4314_;
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
else
{
lean_inc(v_a_4322_);
lean_dec(v___x_4314_);
v___x_4324_ = lean_box(0);
v_isShared_4325_ = v_isSharedCheck_4329_;
goto v_resetjp_4323_;
}
v_resetjp_4323_:
{
lean_object* v___x_4327_; 
if (v_isShared_4325_ == 0)
{
v___x_4327_ = v___x_4324_;
goto v_reusejp_4326_;
}
else
{
lean_object* v_reuseFailAlloc_4328_; 
v_reuseFailAlloc_4328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_a_4322_);
v___x_4327_ = v_reuseFailAlloc_4328_;
goto v_reusejp_4326_;
}
v_reusejp_4326_:
{
return v___x_4327_;
}
}
}
}
else
{
lean_dec(v_a_4312_);
lean_dec(v_snd_4310_);
lean_del_object(v___x_3905_);
v_isEq_4251_ = v___x_3882_;
v___y_4252_ = v___y_4301_;
v___y_4253_ = v___y_4302_;
v___y_4254_ = v___y_4303_;
v___y_4255_ = v___y_4304_;
goto v___jp_4250_;
}
}
else
{
lean_object* v_a_4330_; lean_object* v___x_4332_; uint8_t v_isShared_4333_; uint8_t v_isSharedCheck_4337_; 
lean_dec(v_snd_4310_);
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4330_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4337_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4337_ == 0)
{
v___x_4332_ = v___x_4311_;
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
else
{
lean_inc(v_a_4330_);
lean_dec(v___x_4311_);
v___x_4332_ = lean_box(0);
v_isShared_4333_ = v_isSharedCheck_4337_;
goto v_resetjp_4331_;
}
v_resetjp_4331_:
{
lean_object* v___x_4335_; 
if (v_isShared_4333_ == 0)
{
v___x_4335_ = v___x_4332_;
goto v_reusejp_4334_;
}
else
{
lean_object* v_reuseFailAlloc_4336_; 
v_reuseFailAlloc_4336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4336_, 0, v_a_4330_);
v___x_4335_ = v_reuseFailAlloc_4336_;
goto v_reusejp_4334_;
}
v_reusejp_4334_:
{
return v___x_4335_;
}
}
}
}
else
{
lean_dec(v_a_4306_);
lean_del_object(v___x_3905_);
v_isEq_4251_ = v___x_3978_;
v___y_4252_ = v___y_4301_;
v___y_4253_ = v___y_4302_;
v___y_4254_ = v___y_4303_;
v___y_4255_ = v___y_4304_;
goto v___jp_4250_;
}
}
else
{
lean_object* v_a_4338_; lean_object* v___x_4340_; uint8_t v_isShared_4341_; uint8_t v_isSharedCheck_4345_; 
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4338_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4340_ = v___x_4305_;
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
else
{
lean_inc(v_a_4338_);
lean_dec(v___x_4305_);
v___x_4340_ = lean_box(0);
v_isShared_4341_ = v_isSharedCheck_4345_;
goto v_resetjp_4339_;
}
v_resetjp_4339_:
{
lean_object* v___x_4343_; 
if (v_isShared_4341_ == 0)
{
v___x_4343_ = v___x_4340_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
}
v___jp_4346_:
{
lean_object* v___x_4351_; 
lean_inc_ref(v___x_4023_);
v___x_4351_ = l_Lean_refutableHasNotBit_x3f(v___x_4023_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4351_) == 0)
{
lean_object* v_a_4352_; 
v_a_4352_ = lean_ctor_get(v___x_4351_, 0);
lean_inc(v_a_4352_);
lean_dec_ref_known(v___x_4351_, 1);
if (lean_obj_tag(v_a_4352_) == 1)
{
lean_object* v_val_4353_; lean_object* v___x_4355_; uint8_t v_isShared_4356_; uint8_t v_isSharedCheck_4393_; 
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec_ref(v_config_3871_);
v_val_4353_ = lean_ctor_get(v_a_4352_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v_a_4352_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4355_ = v_a_4352_;
v_isShared_4356_ = v_isSharedCheck_4393_;
goto v_resetjp_4354_;
}
else
{
lean_inc(v_val_4353_);
lean_dec(v_a_4352_);
v___x_4355_ = lean_box(0);
v_isShared_4356_ = v_isSharedCheck_4393_;
goto v_resetjp_4354_;
}
v_resetjp_4354_:
{
lean_object* v___x_4357_; 
lean_inc(v_mvarId_3872_);
v___x_4357_ = l_Lean_MVarId_getType(v_mvarId_3872_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4357_) == 0)
{
lean_object* v_a_4358_; lean_object* v___x_4359_; lean_object* v___x_4360_; 
v_a_4358_ = lean_ctor_get(v___x_4357_, 0);
lean_inc(v_a_4358_);
lean_dec_ref_known(v___x_4357_, 1);
v___x_4359_ = l_Lean_LocalDecl_toExpr(v_val_3903_);
v___x_4360_ = l_Lean_Meta_mkAbsurd(v_a_4358_, v_val_4353_, v___x_4359_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___x_4362_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4360_, 1);
v___x_4362_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3872_, v_a_4361_, v___y_4348_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v___x_4363_; lean_object* v___x_4365_; 
lean_dec_ref_known(v___x_4362_, 1);
v___x_4363_ = lean_box(v___x_3882_);
if (v_isShared_4356_ == 0)
{
lean_ctor_set(v___x_4355_, 0, v___x_4363_);
v___x_4365_ = v___x_4355_;
goto v_reusejp_4364_;
}
else
{
lean_object* v_reuseFailAlloc_4368_; 
v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4368_, 0, v___x_4363_);
v___x_4365_ = v_reuseFailAlloc_4368_;
goto v_reusejp_4364_;
}
v_reusejp_4364_:
{
lean_object* v___x_4366_; lean_object* v___x_4367_; 
v___x_4366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4366_, 0, v___x_4365_);
lean_ctor_set(v___x_4366_, 1, v___x_3907_);
v___x_4367_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
v_a_3889_ = v___x_4367_;
goto v___jp_3888_;
}
}
else
{
lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4376_; 
lean_del_object(v___x_4355_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
v_a_4369_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4376_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4376_ == 0)
{
v___x_4371_ = v___x_4362_;
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4362_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4376_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4374_; 
if (v_isShared_4372_ == 0)
{
v___x_4374_ = v___x_4371_;
goto v_reusejp_4373_;
}
else
{
lean_object* v_reuseFailAlloc_4375_; 
v_reuseFailAlloc_4375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4375_, 0, v_a_4369_);
v___x_4374_ = v_reuseFailAlloc_4375_;
goto v_reusejp_4373_;
}
v_reusejp_4373_:
{
return v___x_4374_;
}
}
}
}
else
{
lean_object* v_a_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_del_object(v___x_4355_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_4377_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4360_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_a_4377_);
lean_dec(v___x_4360_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_a_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
else
{
lean_object* v_a_4385_; lean_object* v___x_4387_; uint8_t v_isShared_4388_; uint8_t v_isSharedCheck_4392_; 
lean_del_object(v___x_4355_);
lean_dec(v_val_4353_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_4385_ = lean_ctor_get(v___x_4357_, 0);
v_isSharedCheck_4392_ = !lean_is_exclusive(v___x_4357_);
if (v_isSharedCheck_4392_ == 0)
{
v___x_4387_ = v___x_4357_;
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
else
{
lean_inc(v_a_4385_);
lean_dec(v___x_4357_);
v___x_4387_ = lean_box(0);
v_isShared_4388_ = v_isSharedCheck_4392_;
goto v_resetjp_4386_;
}
v_resetjp_4386_:
{
lean_object* v___x_4390_; 
if (v_isShared_4388_ == 0)
{
v___x_4390_ = v___x_4387_;
goto v_reusejp_4389_;
}
else
{
lean_object* v_reuseFailAlloc_4391_; 
v_reuseFailAlloc_4391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4391_, 0, v_a_4385_);
v___x_4390_ = v_reuseFailAlloc_4391_;
goto v_reusejp_4389_;
}
v_reusejp_4389_:
{
return v___x_4390_;
}
}
}
}
}
else
{
lean_object* v___x_4394_; 
lean_dec(v_a_4352_);
lean_inc_ref(v___x_4023_);
v___x_4394_ = l_Lean_Meta_matchNe_x3f(v___x_4023_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
if (lean_obj_tag(v_a_4395_) == 1)
{
lean_object* v_val_4396_; lean_object* v___x_4398_; uint8_t v_isShared_4399_; uint8_t v_isSharedCheck_4466_; 
v_val_4396_ = lean_ctor_get(v_a_4395_, 0);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_a_4395_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4398_ = v_a_4395_;
v_isShared_4399_ = v_isSharedCheck_4466_;
goto v_resetjp_4397_;
}
else
{
lean_inc(v_val_4396_);
lean_dec(v_a_4395_);
v___x_4398_ = lean_box(0);
v_isShared_4399_ = v_isSharedCheck_4466_;
goto v_resetjp_4397_;
}
v_resetjp_4397_:
{
lean_object* v_snd_4400_; lean_object* v_fst_4401_; lean_object* v_snd_4402_; lean_object* v___x_4404_; uint8_t v_isShared_4405_; uint8_t v_isSharedCheck_4465_; 
v_snd_4400_ = lean_ctor_get(v_val_4396_, 1);
lean_inc(v_snd_4400_);
lean_dec(v_val_4396_);
v_fst_4401_ = lean_ctor_get(v_snd_4400_, 0);
v_snd_4402_ = lean_ctor_get(v_snd_4400_, 1);
v_isSharedCheck_4465_ = !lean_is_exclusive(v_snd_4400_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4404_ = v_snd_4400_;
v_isShared_4405_ = v_isSharedCheck_4465_;
goto v_resetjp_4403_;
}
else
{
lean_inc(v_snd_4402_);
lean_inc(v_fst_4401_);
lean_dec(v_snd_4400_);
v___x_4404_ = lean_box(0);
v_isShared_4405_ = v_isSharedCheck_4465_;
goto v_resetjp_4403_;
}
v_resetjp_4403_:
{
lean_object* v___x_4406_; 
lean_inc(v_fst_4401_);
v___x_4406_ = l_Lean_Meta_isExprDefEq(v_fst_4401_, v_snd_4402_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4406_) == 0)
{
lean_object* v_a_4407_; uint8_t v___x_4408_; 
v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc(v_a_4407_);
lean_dec_ref_known(v___x_4406_, 1);
v___x_4408_ = lean_unbox(v_a_4407_);
lean_dec(v_a_4407_);
if (v___x_4408_ == 0)
{
lean_del_object(v___x_4404_);
lean_dec(v_fst_4401_);
lean_del_object(v___x_4398_);
v___y_4301_ = v___y_4347_;
v___y_4302_ = v___y_4348_;
v___y_4303_ = v___y_4349_;
v___y_4304_ = v___y_4350_;
goto v___jp_4300_;
}
else
{
lean_object* v___x_4409_; 
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec_ref(v_config_3871_);
lean_inc(v_mvarId_3872_);
v___x_4409_ = l_Lean_MVarId_getType(v_mvarId_3872_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4409_) == 0)
{
lean_object* v_a_4410_; lean_object* v___x_4411_; 
v_a_4410_ = lean_ctor_get(v___x_4409_, 0);
lean_inc(v_a_4410_);
lean_dec_ref_known(v___x_4409_, 1);
v___x_4411_ = l_Lean_Meta_mkEqRefl(v_fst_4401_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4411_) == 0)
{
lean_object* v_a_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v_a_4412_ = lean_ctor_get(v___x_4411_, 0);
lean_inc(v_a_4412_);
lean_dec_ref_known(v___x_4411_, 1);
v___x_4413_ = l_Lean_LocalDecl_toExpr(v_val_3903_);
v___x_4414_ = l_Lean_Meta_mkAbsurd(v_a_4410_, v_a_4412_, v___x_4413_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_object* v_a_4415_; lean_object* v___x_4416_; 
v_a_4415_ = lean_ctor_get(v___x_4414_, 0);
lean_inc(v_a_4415_);
lean_dec_ref_known(v___x_4414_, 1);
v___x_4416_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3872_, v_a_4415_, v___y_4348_);
if (lean_obj_tag(v___x_4416_) == 0)
{
lean_object* v___x_4417_; lean_object* v___x_4419_; 
lean_dec_ref_known(v___x_4416_, 1);
v___x_4417_ = lean_box(v___x_3882_);
if (v_isShared_4399_ == 0)
{
lean_ctor_set(v___x_4398_, 0, v___x_4417_);
v___x_4419_ = v___x_4398_;
goto v_reusejp_4418_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4417_);
v___x_4419_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4418_;
}
v_reusejp_4418_:
{
lean_object* v___x_4421_; 
if (v_isShared_4405_ == 0)
{
lean_ctor_set(v___x_4404_, 1, v___x_3907_);
lean_ctor_set(v___x_4404_, 0, v___x_4419_);
v___x_4421_ = v___x_4404_;
goto v_reusejp_4420_;
}
else
{
lean_object* v_reuseFailAlloc_4423_; 
v_reuseFailAlloc_4423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4423_, 0, v___x_4419_);
lean_ctor_set(v_reuseFailAlloc_4423_, 1, v___x_3907_);
v___x_4421_ = v_reuseFailAlloc_4423_;
goto v_reusejp_4420_;
}
v_reusejp_4420_:
{
lean_object* v___x_4422_; 
v___x_4422_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4421_);
v_a_3889_ = v___x_4422_;
goto v___jp_3888_;
}
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_del_object(v___x_4404_);
lean_del_object(v___x_4398_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
v_a_4425_ = lean_ctor_get(v___x_4416_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4416_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4416_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4416_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_del_object(v___x_4404_);
lean_del_object(v___x_4398_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_4433_ = lean_ctor_get(v___x_4414_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4414_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4414_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4414_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
else
{
lean_object* v_a_4441_; lean_object* v___x_4443_; uint8_t v_isShared_4444_; uint8_t v_isSharedCheck_4448_; 
lean_dec(v_a_4410_);
lean_del_object(v___x_4404_);
lean_del_object(v___x_4398_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_4441_ = lean_ctor_get(v___x_4411_, 0);
v_isSharedCheck_4448_ = !lean_is_exclusive(v___x_4411_);
if (v_isSharedCheck_4448_ == 0)
{
v___x_4443_ = v___x_4411_;
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
else
{
lean_inc(v_a_4441_);
lean_dec(v___x_4411_);
v___x_4443_ = lean_box(0);
v_isShared_4444_ = v_isSharedCheck_4448_;
goto v_resetjp_4442_;
}
v_resetjp_4442_:
{
lean_object* v___x_4446_; 
if (v_isShared_4444_ == 0)
{
v___x_4446_ = v___x_4443_;
goto v_reusejp_4445_;
}
else
{
lean_object* v_reuseFailAlloc_4447_; 
v_reuseFailAlloc_4447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4447_, 0, v_a_4441_);
v___x_4446_ = v_reuseFailAlloc_4447_;
goto v_reusejp_4445_;
}
v_reusejp_4445_:
{
return v___x_4446_;
}
}
}
}
else
{
lean_object* v_a_4449_; lean_object* v___x_4451_; uint8_t v_isShared_4452_; uint8_t v_isSharedCheck_4456_; 
lean_del_object(v___x_4404_);
lean_dec(v_fst_4401_);
lean_del_object(v___x_4398_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_4449_ = lean_ctor_get(v___x_4409_, 0);
v_isSharedCheck_4456_ = !lean_is_exclusive(v___x_4409_);
if (v_isSharedCheck_4456_ == 0)
{
v___x_4451_ = v___x_4409_;
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
else
{
lean_inc(v_a_4449_);
lean_dec(v___x_4409_);
v___x_4451_ = lean_box(0);
v_isShared_4452_ = v_isSharedCheck_4456_;
goto v_resetjp_4450_;
}
v_resetjp_4450_:
{
lean_object* v___x_4454_; 
if (v_isShared_4452_ == 0)
{
v___x_4454_ = v___x_4451_;
goto v_reusejp_4453_;
}
else
{
lean_object* v_reuseFailAlloc_4455_; 
v_reuseFailAlloc_4455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4455_, 0, v_a_4449_);
v___x_4454_ = v_reuseFailAlloc_4455_;
goto v_reusejp_4453_;
}
v_reusejp_4453_:
{
return v___x_4454_;
}
}
}
}
}
else
{
lean_object* v_a_4457_; lean_object* v___x_4459_; uint8_t v_isShared_4460_; uint8_t v_isSharedCheck_4464_; 
lean_del_object(v___x_4404_);
lean_dec(v_fst_4401_);
lean_del_object(v___x_4398_);
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4457_ = lean_ctor_get(v___x_4406_, 0);
v_isSharedCheck_4464_ = !lean_is_exclusive(v___x_4406_);
if (v_isSharedCheck_4464_ == 0)
{
v___x_4459_ = v___x_4406_;
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
else
{
lean_inc(v_a_4457_);
lean_dec(v___x_4406_);
v___x_4459_ = lean_box(0);
v_isShared_4460_ = v_isSharedCheck_4464_;
goto v_resetjp_4458_;
}
v_resetjp_4458_:
{
lean_object* v___x_4462_; 
if (v_isShared_4460_ == 0)
{
v___x_4462_ = v___x_4459_;
goto v_reusejp_4461_;
}
else
{
lean_object* v_reuseFailAlloc_4463_; 
v_reuseFailAlloc_4463_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4463_, 0, v_a_4457_);
v___x_4462_ = v_reuseFailAlloc_4463_;
goto v_reusejp_4461_;
}
v_reusejp_4461_:
{
return v___x_4462_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4395_);
v___y_4301_ = v___y_4347_;
v___y_4302_ = v___y_4348_;
v___y_4303_ = v___y_4349_;
v___y_4304_ = v___y_4350_;
goto v___jp_4300_;
}
}
else
{
lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4474_; 
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4467_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4474_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4474_ == 0)
{
v___x_4469_ = v___x_4394_;
v_isShared_4470_ = v_isSharedCheck_4474_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4394_);
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
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec_ref(v___x_4023_);
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4475_ = lean_ctor_get(v___x_4351_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4351_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4351_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4351_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
}
}
else
{
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
v_a_3897_ = v___x_3949_;
goto v___jp_3896_;
}
v___jp_3908_:
{
lean_object* v___x_3913_; 
lean_inc(v_mvarId_3872_);
v___x_3913_ = l_Lean_MVarId_getType(v_mvarId_3872_, v___y_3910_, v___y_3909_, v___y_3911_, v___y_3912_);
if (lean_obj_tag(v___x_3913_) == 0)
{
lean_object* v_a_3914_; lean_object* v___x_3915_; lean_object* v___x_3916_; 
v_a_3914_ = lean_ctor_get(v___x_3913_, 0);
lean_inc(v_a_3914_);
lean_dec_ref_known(v___x_3913_, 1);
v___x_3915_ = l_Lean_LocalDecl_toExpr(v_val_3903_);
v___x_3916_ = l_Lean_Meta_mkNoConfusion(v_a_3914_, v___x_3915_, v___y_3910_, v___y_3909_, v___y_3911_, v___y_3912_);
if (lean_obj_tag(v___x_3916_) == 0)
{
lean_object* v_a_3917_; lean_object* v___x_3918_; 
v_a_3917_ = lean_ctor_get(v___x_3916_, 0);
lean_inc(v_a_3917_);
lean_dec_ref_known(v___x_3916_, 1);
v___x_3918_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3872_, v_a_3917_, v___y_3909_);
if (lean_obj_tag(v___x_3918_) == 0)
{
lean_object* v___x_3919_; lean_object* v___x_3921_; 
lean_dec_ref_known(v___x_3918_, 1);
v___x_3919_ = lean_box(v___x_3882_);
if (v_isShared_3906_ == 0)
{
lean_ctor_set(v___x_3905_, 0, v___x_3919_);
v___x_3921_ = v___x_3905_;
goto v_reusejp_3920_;
}
else
{
lean_object* v_reuseFailAlloc_3924_; 
v_reuseFailAlloc_3924_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3924_, 0, v___x_3919_);
v___x_3921_ = v_reuseFailAlloc_3924_;
goto v_reusejp_3920_;
}
v_reusejp_3920_:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3921_);
lean_ctor_set(v___x_3922_, 1, v___x_3907_);
v___x_3923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
v_a_3889_ = v___x_3923_;
goto v___jp_3888_;
}
}
else
{
lean_object* v_a_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3932_; 
lean_del_object(v___x_3905_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
v_a_3925_ = lean_ctor_get(v___x_3918_, 0);
v_isSharedCheck_3932_ = !lean_is_exclusive(v___x_3918_);
if (v_isSharedCheck_3932_ == 0)
{
v___x_3927_ = v___x_3918_;
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_a_3925_);
lean_dec(v___x_3918_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3932_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3930_; 
if (v_isShared_3928_ == 0)
{
v___x_3930_ = v___x_3927_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3931_; 
v_reuseFailAlloc_3931_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3931_, 0, v_a_3925_);
v___x_3930_ = v_reuseFailAlloc_3931_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
return v___x_3930_;
}
}
}
}
else
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3940_; 
lean_del_object(v___x_3905_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_3933_ = lean_ctor_get(v___x_3916_, 0);
v_isSharedCheck_3940_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3940_ == 0)
{
v___x_3935_ = v___x_3916_;
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3916_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3940_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
lean_object* v___x_3938_; 
if (v_isShared_3936_ == 0)
{
v___x_3938_ = v___x_3935_;
goto v_reusejp_3937_;
}
else
{
lean_object* v_reuseFailAlloc_3939_; 
v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
v___x_3938_ = v_reuseFailAlloc_3939_;
goto v_reusejp_3937_;
}
v_reusejp_3937_:
{
return v___x_3938_;
}
}
}
}
else
{
lean_object* v_a_3941_; lean_object* v___x_3943_; uint8_t v_isShared_3944_; uint8_t v_isSharedCheck_3948_; 
lean_del_object(v___x_3905_);
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
v_a_3941_ = lean_ctor_get(v___x_3913_, 0);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3913_);
if (v_isSharedCheck_3948_ == 0)
{
v___x_3943_ = v___x_3913_;
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
else
{
lean_inc(v_a_3941_);
lean_dec(v___x_3913_);
v___x_3943_ = lean_box(0);
v_isShared_3944_ = v_isSharedCheck_3948_;
goto v_resetjp_3942_;
}
v_resetjp_3942_:
{
lean_object* v___x_3946_; 
if (v_isShared_3944_ == 0)
{
v___x_3946_ = v___x_3943_;
goto v_reusejp_3945_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
v___x_3946_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3945_;
}
v_reusejp_3945_:
{
return v___x_3946_;
}
}
}
}
v___jp_3950_:
{
lean_object* v_searchFuel_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; 
v_searchFuel_3955_ = lean_ctor_get(v_config_3871_, 0);
v___x_3956_ = l_Lean_LocalDecl_fvarId(v_val_3903_);
lean_dec(v_val_3903_);
lean_inc(v_searchFuel_3955_);
lean_inc(v_mvarId_3872_);
v___x_3957_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3872_, v___x_3956_, v_searchFuel_3955_, v___y_3952_, v___y_3953_, v___y_3954_, v___y_3951_);
if (lean_obj_tag(v___x_3957_) == 0)
{
lean_object* v_a_3958_; uint8_t v___x_3959_; 
v_a_3958_ = lean_ctor_get(v___x_3957_, 0);
lean_inc(v_a_3958_);
lean_dec_ref_known(v___x_3957_, 1);
v___x_3959_ = lean_unbox(v_a_3958_);
lean_dec(v_a_3958_);
if (v___x_3959_ == 0)
{
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
v_a_3897_ = v___x_3949_;
goto v___jp_3896_;
}
else
{
lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; 
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v___x_3960_ = lean_box(v___x_3882_);
v___x_3961_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3960_);
v___x_3962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
lean_ctor_set(v___x_3962_, 1, v___x_3907_);
v___x_3963_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
v_a_3889_ = v___x_3963_;
goto v___jp_3888_;
}
}
else
{
lean_object* v_a_3964_; lean_object* v___x_3966_; uint8_t v_isShared_3967_; uint8_t v_isSharedCheck_3971_; 
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_3964_ = lean_ctor_get(v___x_3957_, 0);
v_isSharedCheck_3971_ = !lean_is_exclusive(v___x_3957_);
if (v_isSharedCheck_3971_ == 0)
{
v___x_3966_ = v___x_3957_;
v_isShared_3967_ = v_isSharedCheck_3971_;
goto v_resetjp_3965_;
}
else
{
lean_inc(v_a_3964_);
lean_dec(v___x_3957_);
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
v___jp_3972_:
{
if (v___y_3977_ == 0)
{
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
v_a_3897_ = v___x_3949_;
goto v___jp_3896_;
}
else
{
v___y_3951_ = v___y_3974_;
v___y_3952_ = v___y_3973_;
v___y_3953_ = v___y_3975_;
v___y_3954_ = v___y_3976_;
goto v___jp_3950_;
}
}
v___jp_3979_:
{
if (v___y_3983_ == 0)
{
v___y_3951_ = v___y_3981_;
v___y_3952_ = v___y_3980_;
v___y_3953_ = v___y_3982_;
v___y_3954_ = v___y_3984_;
goto v___jp_3950_;
}
else
{
v___y_3973_ = v___y_3980_;
v___y_3974_ = v___y_3981_;
v___y_3975_ = v___y_3982_;
v___y_3976_ = v___y_3984_;
v___y_3977_ = v___x_3978_;
goto v___jp_3972_;
}
}
v___jp_3985_:
{
if (v___y_3991_ == 0)
{
v___y_3973_ = v___y_3987_;
v___y_3974_ = v___y_3986_;
v___y_3975_ = v___y_3989_;
v___y_3976_ = v___y_3990_;
v___y_3977_ = v___x_3978_;
goto v___jp_3972_;
}
else
{
v___y_3980_ = v___y_3987_;
v___y_3981_ = v___y_3986_;
v___y_3982_ = v___y_3989_;
v___y_3983_ = v___y_3988_;
v___y_3984_ = v___y_3990_;
goto v___jp_3979_;
}
}
v___jp_3992_:
{
uint8_t v_emptyType_3999_; 
v_emptyType_3999_ = lean_ctor_get_uint8(v_config_3871_, sizeof(void*)*1 + 1);
if (v_emptyType_3999_ == 0)
{
v___y_3986_ = v___y_3998_;
v___y_3987_ = v___y_3995_;
v___y_3988_ = v___y_3994_;
v___y_3989_ = v___y_3996_;
v___y_3990_ = v___y_3997_;
v___y_3991_ = v___x_3978_;
goto v___jp_3985_;
}
else
{
if (v___y_3993_ == 0)
{
v___y_3980_ = v___y_3995_;
v___y_3981_ = v___y_3998_;
v___y_3982_ = v___y_3996_;
v___y_3983_ = v___y_3994_;
v___y_3984_ = v___y_3997_;
goto v___jp_3979_;
}
else
{
v___y_3986_ = v___y_3998_;
v___y_3987_ = v___y_3995_;
v___y_3988_ = v___y_3994_;
v___y_3989_ = v___y_3996_;
v___y_3990_ = v___y_3997_;
v___y_3991_ = v___x_3978_;
goto v___jp_3985_;
}
}
}
v___jp_4000_:
{
if (v___y_4007_ == 0)
{
v___y_3993_ = v___y_4001_;
v___y_3994_ = v___y_4003_;
v___y_3995_ = v___y_4004_;
v___y_3996_ = v___y_4005_;
v___y_3997_ = v___y_4006_;
v___y_3998_ = v___y_4002_;
goto v___jp_3992_;
}
else
{
lean_object* v___x_4008_; 
lean_inc(v_val_3903_);
lean_inc(v_mvarId_3872_);
v___x_4008_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3872_, v_val_3903_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4002_);
if (lean_obj_tag(v___x_4008_) == 0)
{
lean_object* v_a_4009_; uint8_t v___x_4010_; 
v_a_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc(v_a_4009_);
lean_dec_ref_known(v___x_4008_, 1);
v___x_4010_ = lean_unbox(v_a_4009_);
lean_dec(v_a_4009_);
if (v___x_4010_ == 0)
{
v___y_3993_ = v___y_4001_;
v___y_3994_ = v___y_4003_;
v___y_3995_ = v___y_4004_;
v___y_3996_ = v___y_4005_;
v___y_3997_ = v___y_4006_;
v___y_3998_ = v___y_4002_;
goto v___jp_3992_;
}
else
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; 
lean_dec(v_val_3903_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v___x_4011_ = lean_box(v___x_3882_);
v___x_4012_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
v___x_4013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
lean_ctor_set(v___x_4013_, 1, v___x_3907_);
v___x_4014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
v_a_3889_ = v___x_4014_;
goto v___jp_3888_;
}
}
else
{
lean_object* v_a_4015_; lean_object* v___x_4017_; uint8_t v_isShared_4018_; uint8_t v_isSharedCheck_4022_; 
lean_dec(v_val_3903_);
lean_del_object(v___x_3886_);
lean_dec(v_snd_3884_);
lean_dec(v_mvarId_3872_);
lean_dec_ref(v_config_3871_);
v_a_4015_ = lean_ctor_get(v___x_4008_, 0);
v_isSharedCheck_4022_ = !lean_is_exclusive(v___x_4008_);
if (v_isSharedCheck_4022_ == 0)
{
v___x_4017_ = v___x_4008_;
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
else
{
lean_inc(v_a_4015_);
lean_dec(v___x_4008_);
v___x_4017_ = lean_box(0);
v_isShared_4018_ = v_isSharedCheck_4022_;
goto v_resetjp_4016_;
}
v_resetjp_4016_:
{
lean_object* v___x_4020_; 
if (v_isShared_4018_ == 0)
{
v___x_4020_ = v___x_4017_;
goto v_reusejp_4019_;
}
else
{
lean_object* v_reuseFailAlloc_4021_; 
v_reuseFailAlloc_4021_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4021_, 0, v_a_4015_);
v___x_4020_ = v_reuseFailAlloc_4021_;
goto v_reusejp_4019_;
}
v_reusejp_4019_:
{
return v___x_4020_;
}
}
}
}
}
}
}
v___jp_3888_:
{
lean_object* v___x_3890_; lean_object* v___x_3892_; 
v___x_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3890_, 0, v_a_3889_);
if (v_isShared_3887_ == 0)
{
lean_ctor_set(v___x_3886_, 0, v___x_3890_);
v___x_3892_ = v___x_3886_;
goto v_reusejp_3891_;
}
else
{
lean_object* v_reuseFailAlloc_3894_; 
v_reuseFailAlloc_3894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3894_, 0, v___x_3890_);
lean_ctor_set(v_reuseFailAlloc_3894_, 1, v_snd_3884_);
v___x_3892_ = v_reuseFailAlloc_3894_;
goto v_reusejp_3891_;
}
v_reusejp_3891_:
{
lean_object* v___x_3893_; 
v___x_3893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3892_);
return v___x_3893_;
}
}
v___jp_3896_:
{
lean_object* v___x_3898_; size_t v___x_3899_; size_t v___x_3900_; lean_object* v___x_3901_; 
v___x_3898_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3898_, 0, v___x_3895_);
lean_ctor_set(v___x_3898_, 1, v_a_3897_);
v___x_3899_ = ((size_t)1ULL);
v___x_3900_ = lean_usize_add(v_i_3875_, v___x_3899_);
v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3871_, v_mvarId_3872_, v_as_3873_, v_sz_3874_, v___x_3900_, v___x_3898_, v___y_3877_, v___y_3878_, v___y_3879_, v___y_3880_);
return v___x_3901_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4556_, lean_object* v_mvarId_4557_, lean_object* v_as_4558_, lean_object* v_sz_4559_, lean_object* v_i_4560_, lean_object* v_b_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_){
_start:
{
size_t v_sz_boxed_4567_; size_t v_i_boxed_4568_; lean_object* v_res_4569_; 
v_sz_boxed_4567_ = lean_unbox_usize(v_sz_4559_);
lean_dec(v_sz_4559_);
v_i_boxed_4568_ = lean_unbox_usize(v_i_4560_);
lean_dec(v_i_4560_);
v_res_4569_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4556_, v_mvarId_4557_, v_as_4558_, v_sz_boxed_4567_, v_i_boxed_4568_, v_b_4561_, v___y_4562_, v___y_4563_, v___y_4564_, v___y_4565_);
lean_dec(v___y_4565_);
lean_dec_ref(v___y_4564_);
lean_dec(v___y_4563_);
lean_dec_ref(v___y_4562_);
lean_dec_ref(v_as_4558_);
return v_res_4569_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4570_, lean_object* v_config_4571_, lean_object* v_mvarId_4572_, lean_object* v_n_4573_, lean_object* v_b_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
if (lean_obj_tag(v_n_4573_) == 0)
{
lean_object* v_cs_4580_; lean_object* v___x_4581_; lean_object* v___x_4582_; size_t v_sz_4583_; size_t v___x_4584_; lean_object* v___x_4585_; 
v_cs_4580_ = lean_ctor_get(v_n_4573_, 0);
v___x_4581_ = lean_box(0);
v___x_4582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4582_, 0, v___x_4581_);
lean_ctor_set(v___x_4582_, 1, v_b_4574_);
v_sz_4583_ = lean_array_size(v_cs_4580_);
v___x_4584_ = ((size_t)0ULL);
v___x_4585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4570_, v_config_4571_, v_mvarId_4572_, v_cs_4580_, v_sz_4583_, v___x_4584_, v___x_4582_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
if (lean_obj_tag(v___x_4585_) == 0)
{
lean_object* v_a_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4600_; 
v_a_4586_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4600_ == 0)
{
v___x_4588_ = v___x_4585_;
v_isShared_4589_ = v_isSharedCheck_4600_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_a_4586_);
lean_dec(v___x_4585_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4600_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v_fst_4590_; 
v_fst_4590_ = lean_ctor_get(v_a_4586_, 0);
if (lean_obj_tag(v_fst_4590_) == 0)
{
lean_object* v_snd_4591_; lean_object* v___x_4592_; lean_object* v___x_4594_; 
v_snd_4591_ = lean_ctor_get(v_a_4586_, 1);
lean_inc(v_snd_4591_);
lean_dec(v_a_4586_);
v___x_4592_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4592_, 0, v_snd_4591_);
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 0, v___x_4592_);
v___x_4594_ = v___x_4588_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4595_; 
v_reuseFailAlloc_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4595_, 0, v___x_4592_);
v___x_4594_ = v_reuseFailAlloc_4595_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
return v___x_4594_;
}
}
else
{
lean_object* v_val_4596_; lean_object* v___x_4598_; 
lean_inc_ref(v_fst_4590_);
lean_dec(v_a_4586_);
v_val_4596_ = lean_ctor_get(v_fst_4590_, 0);
lean_inc(v_val_4596_);
lean_dec_ref_known(v_fst_4590_, 1);
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 0, v_val_4596_);
v___x_4598_ = v___x_4588_;
goto v_reusejp_4597_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_val_4596_);
v___x_4598_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4597_;
}
v_reusejp_4597_:
{
return v___x_4598_;
}
}
}
}
else
{
lean_object* v_a_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
v_a_4601_ = lean_ctor_get(v___x_4585_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4585_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_a_4601_);
lean_dec(v___x_4585_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_a_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
else
{
lean_object* v_vs_4609_; lean_object* v___x_4610_; lean_object* v___x_4611_; size_t v_sz_4612_; size_t v___x_4613_; lean_object* v___x_4614_; 
v_vs_4609_ = lean_ctor_get(v_n_4573_, 0);
v___x_4610_ = lean_box(0);
v___x_4611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4611_, 0, v___x_4610_);
lean_ctor_set(v___x_4611_, 1, v_b_4574_);
v_sz_4612_ = lean_array_size(v_vs_4609_);
v___x_4613_ = ((size_t)0ULL);
v___x_4614_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4571_, v_mvarId_4572_, v_vs_4609_, v_sz_4612_, v___x_4613_, v___x_4611_, v___y_4575_, v___y_4576_, v___y_4577_, v___y_4578_);
if (lean_obj_tag(v___x_4614_) == 0)
{
lean_object* v_a_4615_; lean_object* v___x_4617_; uint8_t v_isShared_4618_; uint8_t v_isSharedCheck_4629_; 
v_a_4615_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4629_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4629_ == 0)
{
v___x_4617_ = v___x_4614_;
v_isShared_4618_ = v_isSharedCheck_4629_;
goto v_resetjp_4616_;
}
else
{
lean_inc(v_a_4615_);
lean_dec(v___x_4614_);
v___x_4617_ = lean_box(0);
v_isShared_4618_ = v_isSharedCheck_4629_;
goto v_resetjp_4616_;
}
v_resetjp_4616_:
{
lean_object* v_fst_4619_; 
v_fst_4619_ = lean_ctor_get(v_a_4615_, 0);
if (lean_obj_tag(v_fst_4619_) == 0)
{
lean_object* v_snd_4620_; lean_object* v___x_4621_; lean_object* v___x_4623_; 
v_snd_4620_ = lean_ctor_get(v_a_4615_, 1);
lean_inc(v_snd_4620_);
lean_dec(v_a_4615_);
v___x_4621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4621_, 0, v_snd_4620_);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v___x_4621_);
v___x_4623_ = v___x_4617_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4624_; 
v_reuseFailAlloc_4624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4624_, 0, v___x_4621_);
v___x_4623_ = v_reuseFailAlloc_4624_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
return v___x_4623_;
}
}
else
{
lean_object* v_val_4625_; lean_object* v___x_4627_; 
lean_inc_ref(v_fst_4619_);
lean_dec(v_a_4615_);
v_val_4625_ = lean_ctor_get(v_fst_4619_, 0);
lean_inc(v_val_4625_);
lean_dec_ref_known(v_fst_4619_, 1);
if (v_isShared_4618_ == 0)
{
lean_ctor_set(v___x_4617_, 0, v_val_4625_);
v___x_4627_ = v___x_4617_;
goto v_reusejp_4626_;
}
else
{
lean_object* v_reuseFailAlloc_4628_; 
v_reuseFailAlloc_4628_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4628_, 0, v_val_4625_);
v___x_4627_ = v_reuseFailAlloc_4628_;
goto v_reusejp_4626_;
}
v_reusejp_4626_:
{
return v___x_4627_;
}
}
}
}
else
{
lean_object* v_a_4630_; lean_object* v___x_4632_; uint8_t v_isShared_4633_; uint8_t v_isSharedCheck_4637_; 
v_a_4630_ = lean_ctor_get(v___x_4614_, 0);
v_isSharedCheck_4637_ = !lean_is_exclusive(v___x_4614_);
if (v_isSharedCheck_4637_ == 0)
{
v___x_4632_ = v___x_4614_;
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
else
{
lean_inc(v_a_4630_);
lean_dec(v___x_4614_);
v___x_4632_ = lean_box(0);
v_isShared_4633_ = v_isSharedCheck_4637_;
goto v_resetjp_4631_;
}
v_resetjp_4631_:
{
lean_object* v___x_4635_; 
if (v_isShared_4633_ == 0)
{
v___x_4635_ = v___x_4632_;
goto v_reusejp_4634_;
}
else
{
lean_object* v_reuseFailAlloc_4636_; 
v_reuseFailAlloc_4636_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4636_, 0, v_a_4630_);
v___x_4635_ = v_reuseFailAlloc_4636_;
goto v_reusejp_4634_;
}
v_reusejp_4634_:
{
return v___x_4635_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4638_, lean_object* v_config_4639_, lean_object* v_mvarId_4640_, lean_object* v_as_4641_, size_t v_sz_4642_, size_t v_i_4643_, lean_object* v_b_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_){
_start:
{
uint8_t v___x_4650_; 
v___x_4650_ = lean_usize_dec_lt(v_i_4643_, v_sz_4642_);
if (v___x_4650_ == 0)
{
lean_object* v___x_4651_; 
lean_dec(v_mvarId_4640_);
lean_dec_ref(v_config_4639_);
v___x_4651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4651_, 0, v_b_4644_);
return v___x_4651_;
}
else
{
lean_object* v_snd_4652_; lean_object* v___x_4654_; uint8_t v_isShared_4655_; uint8_t v_isSharedCheck_4686_; 
v_snd_4652_ = lean_ctor_get(v_b_4644_, 1);
v_isSharedCheck_4686_ = !lean_is_exclusive(v_b_4644_);
if (v_isSharedCheck_4686_ == 0)
{
lean_object* v_unused_4687_; 
v_unused_4687_ = lean_ctor_get(v_b_4644_, 0);
lean_dec(v_unused_4687_);
v___x_4654_ = v_b_4644_;
v_isShared_4655_ = v_isSharedCheck_4686_;
goto v_resetjp_4653_;
}
else
{
lean_inc(v_snd_4652_);
lean_dec(v_b_4644_);
v___x_4654_ = lean_box(0);
v_isShared_4655_ = v_isSharedCheck_4686_;
goto v_resetjp_4653_;
}
v_resetjp_4653_:
{
lean_object* v___x_4656_; lean_object* v_a_4657_; lean_object* v___x_4658_; 
v___x_4656_ = lean_box(0);
v_a_4657_ = lean_array_uget_borrowed(v_as_4641_, v_i_4643_);
lean_inc(v_snd_4652_);
lean_inc(v_mvarId_4640_);
lean_inc_ref(v_config_4639_);
v___x_4658_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4638_, v_config_4639_, v_mvarId_4640_, v_a_4657_, v_snd_4652_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
if (lean_obj_tag(v___x_4658_) == 0)
{
lean_object* v_a_4659_; lean_object* v___x_4661_; uint8_t v_isShared_4662_; uint8_t v_isSharedCheck_4677_; 
v_a_4659_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4677_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4677_ == 0)
{
v___x_4661_ = v___x_4658_;
v_isShared_4662_ = v_isSharedCheck_4677_;
goto v_resetjp_4660_;
}
else
{
lean_inc(v_a_4659_);
lean_dec(v___x_4658_);
v___x_4661_ = lean_box(0);
v_isShared_4662_ = v_isSharedCheck_4677_;
goto v_resetjp_4660_;
}
v_resetjp_4660_:
{
if (lean_obj_tag(v_a_4659_) == 0)
{
lean_object* v___x_4663_; lean_object* v___x_4665_; 
lean_dec(v_mvarId_4640_);
lean_dec_ref(v_config_4639_);
v___x_4663_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4663_, 0, v_a_4659_);
if (v_isShared_4655_ == 0)
{
lean_ctor_set(v___x_4654_, 0, v___x_4663_);
v___x_4665_ = v___x_4654_;
goto v_reusejp_4664_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v___x_4663_);
lean_ctor_set(v_reuseFailAlloc_4669_, 1, v_snd_4652_);
v___x_4665_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4664_;
}
v_reusejp_4664_:
{
lean_object* v___x_4667_; 
if (v_isShared_4662_ == 0)
{
lean_ctor_set(v___x_4661_, 0, v___x_4665_);
v___x_4667_ = v___x_4661_;
goto v_reusejp_4666_;
}
else
{
lean_object* v_reuseFailAlloc_4668_; 
v_reuseFailAlloc_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4668_, 0, v___x_4665_);
v___x_4667_ = v_reuseFailAlloc_4668_;
goto v_reusejp_4666_;
}
v_reusejp_4666_:
{
return v___x_4667_;
}
}
}
else
{
lean_object* v_a_4670_; lean_object* v___x_4672_; 
lean_del_object(v___x_4661_);
lean_dec(v_snd_4652_);
v_a_4670_ = lean_ctor_get(v_a_4659_, 0);
lean_inc(v_a_4670_);
lean_dec_ref_known(v_a_4659_, 1);
if (v_isShared_4655_ == 0)
{
lean_ctor_set(v___x_4654_, 1, v_a_4670_);
lean_ctor_set(v___x_4654_, 0, v___x_4656_);
v___x_4672_ = v___x_4654_;
goto v_reusejp_4671_;
}
else
{
lean_object* v_reuseFailAlloc_4676_; 
v_reuseFailAlloc_4676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4676_, 0, v___x_4656_);
lean_ctor_set(v_reuseFailAlloc_4676_, 1, v_a_4670_);
v___x_4672_ = v_reuseFailAlloc_4676_;
goto v_reusejp_4671_;
}
v_reusejp_4671_:
{
size_t v___x_4673_; size_t v___x_4674_; 
v___x_4673_ = ((size_t)1ULL);
v___x_4674_ = lean_usize_add(v_i_4643_, v___x_4673_);
v_i_4643_ = v___x_4674_;
v_b_4644_ = v___x_4672_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4685_; 
lean_del_object(v___x_4654_);
lean_dec(v_snd_4652_);
lean_dec(v_mvarId_4640_);
lean_dec_ref(v_config_4639_);
v_a_4678_ = lean_ctor_get(v___x_4658_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4658_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4680_ = v___x_4658_;
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4658_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4685_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4683_; 
if (v_isShared_4681_ == 0)
{
v___x_4683_ = v___x_4680_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v_a_4678_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4688_, lean_object* v_config_4689_, lean_object* v_mvarId_4690_, lean_object* v_as_4691_, lean_object* v_sz_4692_, lean_object* v_i_4693_, lean_object* v_b_4694_, lean_object* v___y_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_){
_start:
{
size_t v_sz_boxed_4700_; size_t v_i_boxed_4701_; lean_object* v_res_4702_; 
v_sz_boxed_4700_ = lean_unbox_usize(v_sz_4692_);
lean_dec(v_sz_4692_);
v_i_boxed_4701_ = lean_unbox_usize(v_i_4693_);
lean_dec(v_i_4693_);
v_res_4702_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4688_, v_config_4689_, v_mvarId_4690_, v_as_4691_, v_sz_boxed_4700_, v_i_boxed_4701_, v_b_4694_, v___y_4695_, v___y_4696_, v___y_4697_, v___y_4698_);
lean_dec(v___y_4698_);
lean_dec_ref(v___y_4697_);
lean_dec(v___y_4696_);
lean_dec_ref(v___y_4695_);
lean_dec_ref(v_as_4691_);
lean_dec_ref(v_init_4688_);
return v_res_4702_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4703_, lean_object* v_config_4704_, lean_object* v_mvarId_4705_, lean_object* v_n_4706_, lean_object* v_b_4707_, lean_object* v___y_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_){
_start:
{
lean_object* v_res_4713_; 
v_res_4713_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4703_, v_config_4704_, v_mvarId_4705_, v_n_4706_, v_b_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_);
lean_dec(v___y_4711_);
lean_dec_ref(v___y_4710_);
lean_dec(v___y_4709_);
lean_dec_ref(v___y_4708_);
lean_dec_ref(v_n_4706_);
lean_dec_ref(v_init_4703_);
return v_res_4713_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4714_, lean_object* v_mvarId_4715_, lean_object* v_t_4716_, lean_object* v_init_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v_root_4723_; lean_object* v_tail_4724_; lean_object* v___x_4725_; 
v_root_4723_ = lean_ctor_get(v_t_4716_, 0);
v_tail_4724_ = lean_ctor_get(v_t_4716_, 1);
lean_inc(v_mvarId_4715_);
lean_inc_ref(v_config_4714_);
lean_inc_ref(v_init_4717_);
v___x_4725_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4717_, v_config_4714_, v_mvarId_4715_, v_root_4723_, v_init_4717_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
lean_dec_ref(v_init_4717_);
if (lean_obj_tag(v___x_4725_) == 0)
{
lean_object* v_a_4726_; lean_object* v___x_4728_; uint8_t v_isShared_4729_; uint8_t v_isSharedCheck_4762_; 
v_a_4726_ = lean_ctor_get(v___x_4725_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4725_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4728_ = v___x_4725_;
v_isShared_4729_ = v_isSharedCheck_4762_;
goto v_resetjp_4727_;
}
else
{
lean_inc(v_a_4726_);
lean_dec(v___x_4725_);
v___x_4728_ = lean_box(0);
v_isShared_4729_ = v_isSharedCheck_4762_;
goto v_resetjp_4727_;
}
v_resetjp_4727_:
{
if (lean_obj_tag(v_a_4726_) == 0)
{
lean_object* v_a_4730_; lean_object* v___x_4732_; 
lean_dec(v_mvarId_4715_);
lean_dec_ref(v_config_4714_);
v_a_4730_ = lean_ctor_get(v_a_4726_, 0);
lean_inc(v_a_4730_);
lean_dec_ref_known(v_a_4726_, 1);
if (v_isShared_4729_ == 0)
{
lean_ctor_set(v___x_4728_, 0, v_a_4730_);
v___x_4732_ = v___x_4728_;
goto v_reusejp_4731_;
}
else
{
lean_object* v_reuseFailAlloc_4733_; 
v_reuseFailAlloc_4733_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4733_, 0, v_a_4730_);
v___x_4732_ = v_reuseFailAlloc_4733_;
goto v_reusejp_4731_;
}
v_reusejp_4731_:
{
return v___x_4732_;
}
}
else
{
lean_object* v_a_4734_; lean_object* v___x_4735_; lean_object* v___x_4736_; size_t v_sz_4737_; size_t v___x_4738_; lean_object* v___x_4739_; 
lean_del_object(v___x_4728_);
v_a_4734_ = lean_ctor_get(v_a_4726_, 0);
lean_inc(v_a_4734_);
lean_dec_ref_known(v_a_4726_, 1);
v___x_4735_ = lean_box(0);
v___x_4736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4736_, 0, v___x_4735_);
lean_ctor_set(v___x_4736_, 1, v_a_4734_);
v_sz_4737_ = lean_array_size(v_tail_4724_);
v___x_4738_ = ((size_t)0ULL);
v___x_4739_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4714_, v_mvarId_4715_, v_tail_4724_, v_sz_4737_, v___x_4738_, v___x_4736_, v___y_4718_, v___y_4719_, v___y_4720_, v___y_4721_);
if (lean_obj_tag(v___x_4739_) == 0)
{
lean_object* v_a_4740_; lean_object* v___x_4742_; uint8_t v_isShared_4743_; uint8_t v_isSharedCheck_4753_; 
v_a_4740_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4753_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4753_ == 0)
{
v___x_4742_ = v___x_4739_;
v_isShared_4743_ = v_isSharedCheck_4753_;
goto v_resetjp_4741_;
}
else
{
lean_inc(v_a_4740_);
lean_dec(v___x_4739_);
v___x_4742_ = lean_box(0);
v_isShared_4743_ = v_isSharedCheck_4753_;
goto v_resetjp_4741_;
}
v_resetjp_4741_:
{
lean_object* v_fst_4744_; 
v_fst_4744_ = lean_ctor_get(v_a_4740_, 0);
if (lean_obj_tag(v_fst_4744_) == 0)
{
lean_object* v_snd_4745_; lean_object* v___x_4747_; 
v_snd_4745_ = lean_ctor_get(v_a_4740_, 1);
lean_inc(v_snd_4745_);
lean_dec(v_a_4740_);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v_snd_4745_);
v___x_4747_ = v___x_4742_;
goto v_reusejp_4746_;
}
else
{
lean_object* v_reuseFailAlloc_4748_; 
v_reuseFailAlloc_4748_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4748_, 0, v_snd_4745_);
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
lean_inc_ref(v_fst_4744_);
lean_dec(v_a_4740_);
v_val_4749_ = lean_ctor_get(v_fst_4744_, 0);
lean_inc(v_val_4749_);
lean_dec_ref_known(v_fst_4744_, 1);
if (v_isShared_4743_ == 0)
{
lean_ctor_set(v___x_4742_, 0, v_val_4749_);
v___x_4751_ = v___x_4742_;
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
v_a_4754_ = lean_ctor_get(v___x_4739_, 0);
v_isSharedCheck_4761_ = !lean_is_exclusive(v___x_4739_);
if (v_isSharedCheck_4761_ == 0)
{
v___x_4756_ = v___x_4739_;
v_isShared_4757_ = v_isSharedCheck_4761_;
goto v_resetjp_4755_;
}
else
{
lean_inc(v_a_4754_);
lean_dec(v___x_4739_);
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
}
}
else
{
lean_object* v_a_4763_; lean_object* v___x_4765_; uint8_t v_isShared_4766_; uint8_t v_isSharedCheck_4770_; 
lean_dec(v_mvarId_4715_);
lean_dec_ref(v_config_4714_);
v_a_4763_ = lean_ctor_get(v___x_4725_, 0);
v_isSharedCheck_4770_ = !lean_is_exclusive(v___x_4725_);
if (v_isSharedCheck_4770_ == 0)
{
v___x_4765_ = v___x_4725_;
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
else
{
lean_inc(v_a_4763_);
lean_dec(v___x_4725_);
v___x_4765_ = lean_box(0);
v_isShared_4766_ = v_isSharedCheck_4770_;
goto v_resetjp_4764_;
}
v_resetjp_4764_:
{
lean_object* v___x_4768_; 
if (v_isShared_4766_ == 0)
{
v___x_4768_ = v___x_4765_;
goto v_reusejp_4767_;
}
else
{
lean_object* v_reuseFailAlloc_4769_; 
v_reuseFailAlloc_4769_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4769_, 0, v_a_4763_);
v___x_4768_ = v_reuseFailAlloc_4769_;
goto v_reusejp_4767_;
}
v_reusejp_4767_:
{
return v___x_4768_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4771_, lean_object* v_mvarId_4772_, lean_object* v_t_4773_, lean_object* v_init_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v_res_4780_; 
v_res_4780_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4771_, v_mvarId_4772_, v_t_4773_, v_init_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_);
lean_dec(v___y_4778_);
lean_dec_ref(v___y_4777_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec_ref(v_t_4773_);
return v_res_4780_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4781_, lean_object* v___x_4782_, lean_object* v_config_4783_, lean_object* v___y_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v___x_4789_; 
lean_inc(v_mvarId_4781_);
v___x_4789_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4781_, v___x_4782_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
if (lean_obj_tag(v___x_4789_) == 0)
{
lean_object* v___x_4790_; 
lean_dec_ref_known(v___x_4789_, 1);
lean_inc(v_mvarId_4781_);
v___x_4790_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4781_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v_a_4791_; lean_object* v___x_4793_; uint8_t v_isShared_4794_; uint8_t v_isSharedCheck_4824_; 
v_a_4791_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4793_ = v___x_4790_;
v_isShared_4794_ = v_isSharedCheck_4824_;
goto v_resetjp_4792_;
}
else
{
lean_inc(v_a_4791_);
lean_dec(v___x_4790_);
v___x_4793_ = lean_box(0);
v_isShared_4794_ = v_isSharedCheck_4824_;
goto v_resetjp_4792_;
}
v_resetjp_4792_:
{
uint8_t v___x_4795_; 
v___x_4795_ = lean_unbox(v_a_4791_);
if (v___x_4795_ == 0)
{
lean_object* v_lctx_4796_; lean_object* v_decls_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; 
lean_del_object(v___x_4793_);
v_lctx_4796_ = lean_ctor_get(v___y_4784_, 2);
v_decls_4797_ = lean_ctor_get(v_lctx_4796_, 1);
v___x_4798_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4799_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4783_, v_mvarId_4781_, v_decls_4797_, v___x_4798_, v___y_4784_, v___y_4785_, v___y_4786_, v___y_4787_);
if (lean_obj_tag(v___x_4799_) == 0)
{
lean_object* v_a_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4812_; 
v_a_4800_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4812_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4812_ == 0)
{
v___x_4802_ = v___x_4799_;
v_isShared_4803_ = v_isSharedCheck_4812_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_a_4800_);
lean_dec(v___x_4799_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4812_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v_fst_4804_; 
v_fst_4804_ = lean_ctor_get(v_a_4800_, 0);
lean_inc(v_fst_4804_);
lean_dec(v_a_4800_);
if (lean_obj_tag(v_fst_4804_) == 0)
{
lean_object* v___x_4806_; 
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v_a_4791_);
v___x_4806_ = v___x_4802_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4807_; 
v_reuseFailAlloc_4807_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4807_, 0, v_a_4791_);
v___x_4806_ = v_reuseFailAlloc_4807_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
return v___x_4806_;
}
}
else
{
lean_object* v_val_4808_; lean_object* v___x_4810_; 
lean_dec(v_a_4791_);
v_val_4808_ = lean_ctor_get(v_fst_4804_, 0);
lean_inc(v_val_4808_);
lean_dec_ref_known(v_fst_4804_, 1);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 0, v_val_4808_);
v___x_4810_ = v___x_4802_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v_val_4808_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
else
{
lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4820_; 
lean_dec(v_a_4791_);
v_a_4813_ = lean_ctor_get(v___x_4799_, 0);
v_isSharedCheck_4820_ = !lean_is_exclusive(v___x_4799_);
if (v_isSharedCheck_4820_ == 0)
{
v___x_4815_ = v___x_4799_;
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4799_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4820_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4818_; 
if (v_isShared_4816_ == 0)
{
v___x_4818_ = v___x_4815_;
goto v_reusejp_4817_;
}
else
{
lean_object* v_reuseFailAlloc_4819_; 
v_reuseFailAlloc_4819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_a_4813_);
v___x_4818_ = v_reuseFailAlloc_4819_;
goto v_reusejp_4817_;
}
v_reusejp_4817_:
{
return v___x_4818_;
}
}
}
}
else
{
lean_object* v___x_4822_; 
lean_dec_ref(v_config_4783_);
lean_dec(v_mvarId_4781_);
if (v_isShared_4794_ == 0)
{
v___x_4822_ = v___x_4793_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4791_);
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
lean_dec_ref(v_config_4783_);
lean_dec(v_mvarId_4781_);
return v___x_4790_;
}
}
else
{
lean_object* v_a_4825_; lean_object* v___x_4827_; uint8_t v_isShared_4828_; uint8_t v_isSharedCheck_4832_; 
lean_dec_ref(v_config_4783_);
lean_dec(v_mvarId_4781_);
v_a_4825_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4832_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4832_ == 0)
{
v___x_4827_ = v___x_4789_;
v_isShared_4828_ = v_isSharedCheck_4832_;
goto v_resetjp_4826_;
}
else
{
lean_inc(v_a_4825_);
lean_dec(v___x_4789_);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4833_, lean_object* v___x_4834_, lean_object* v_config_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_){
_start:
{
lean_object* v_res_4841_; 
v_res_4841_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4833_, v___x_4834_, v_config_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_);
lean_dec(v___y_4839_);
lean_dec_ref(v___y_4838_);
lean_dec(v___y_4837_);
lean_dec_ref(v___y_4836_);
return v_res_4841_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4844_, lean_object* v_config_4845_, lean_object* v_a_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_){
_start:
{
lean_object* v___x_4851_; lean_object* v___f_4852_; lean_object* v___x_4853_; 
v___x_4851_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4844_);
v___f_4852_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4852_, 0, v_mvarId_4844_);
lean_closure_set(v___f_4852_, 1, v___x_4851_);
lean_closure_set(v___f_4852_, 2, v_config_4845_);
v___x_4853_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4844_, v___f_4852_, v_a_4846_, v_a_4847_, v_a_4848_, v_a_4849_);
return v___x_4853_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4854_, lean_object* v_config_4855_, lean_object* v_a_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_){
_start:
{
lean_object* v_res_4861_; 
v_res_4861_ = l_Lean_MVarId_contradictionCore(v_mvarId_4854_, v_config_4855_, v_a_4856_, v_a_4857_, v_a_4858_, v_a_4859_);
lean_dec(v_a_4859_);
lean_dec_ref(v_a_4858_);
lean_dec(v_a_4857_);
lean_dec_ref(v_a_4856_);
return v_res_4861_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4862_, lean_object* v_config_4863_, lean_object* v_a_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_){
_start:
{
lean_object* v___x_4869_; 
lean_inc(v_mvarId_4862_);
v___x_4869_ = l_Lean_MVarId_contradictionCore(v_mvarId_4862_, v_config_4863_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
if (lean_obj_tag(v___x_4869_) == 0)
{
lean_object* v_a_4870_; lean_object* v___x_4872_; uint8_t v_isShared_4873_; uint8_t v_isSharedCheck_4882_; 
v_a_4870_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4882_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4882_ == 0)
{
v___x_4872_ = v___x_4869_;
v_isShared_4873_ = v_isSharedCheck_4882_;
goto v_resetjp_4871_;
}
else
{
lean_inc(v_a_4870_);
lean_dec(v___x_4869_);
v___x_4872_ = lean_box(0);
v_isShared_4873_ = v_isSharedCheck_4882_;
goto v_resetjp_4871_;
}
v_resetjp_4871_:
{
uint8_t v___x_4874_; 
v___x_4874_ = lean_unbox(v_a_4870_);
lean_dec(v_a_4870_);
if (v___x_4874_ == 0)
{
lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; 
lean_del_object(v___x_4872_);
v___x_4875_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4876_ = lean_box(0);
v___x_4877_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4875_, v_mvarId_4862_, v___x_4876_, v_a_4864_, v_a_4865_, v_a_4866_, v_a_4867_);
return v___x_4877_;
}
else
{
lean_object* v___x_4878_; lean_object* v___x_4880_; 
lean_dec(v_mvarId_4862_);
v___x_4878_ = lean_box(0);
if (v_isShared_4873_ == 0)
{
lean_ctor_set(v___x_4872_, 0, v___x_4878_);
v___x_4880_ = v___x_4872_;
goto v_reusejp_4879_;
}
else
{
lean_object* v_reuseFailAlloc_4881_; 
v_reuseFailAlloc_4881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4881_, 0, v___x_4878_);
v___x_4880_ = v_reuseFailAlloc_4881_;
goto v_reusejp_4879_;
}
v_reusejp_4879_:
{
return v___x_4880_;
}
}
}
}
else
{
lean_object* v_a_4883_; lean_object* v___x_4885_; uint8_t v_isShared_4886_; uint8_t v_isSharedCheck_4890_; 
lean_dec(v_mvarId_4862_);
v_a_4883_ = lean_ctor_get(v___x_4869_, 0);
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4869_);
if (v_isSharedCheck_4890_ == 0)
{
v___x_4885_ = v___x_4869_;
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
else
{
lean_inc(v_a_4883_);
lean_dec(v___x_4869_);
v___x_4885_ = lean_box(0);
v_isShared_4886_ = v_isSharedCheck_4890_;
goto v_resetjp_4884_;
}
v_resetjp_4884_:
{
lean_object* v___x_4888_; 
if (v_isShared_4886_ == 0)
{
v___x_4888_ = v___x_4885_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v_a_4883_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4891_, lean_object* v_config_4892_, lean_object* v_a_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_){
_start:
{
lean_object* v_res_4898_; 
v_res_4898_ = l_Lean_MVarId_contradiction(v_mvarId_4891_, v_config_4892_, v_a_4893_, v_a_4894_, v_a_4895_, v_a_4896_);
lean_dec(v_a_4896_);
lean_dec_ref(v_a_4895_);
lean_dec(v_a_4894_);
lean_dec_ref(v_a_4893_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4961_; uint8_t v___x_4962_; lean_object* v___x_4963_; lean_object* v___x_4964_; 
v___x_4961_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4962_ = 0;
v___x_4963_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4964_ = l_Lean_registerTraceClass(v___x_4961_, v___x_4962_, v___x_4963_);
return v___x_4964_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4965_){
_start:
{
lean_object* v_res_4966_; 
v_res_4966_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4966_;
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
