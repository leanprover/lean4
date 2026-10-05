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
lean_inc(v_a_501_);
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
lean_object* v___x_571_; lean_object* v_env_572_; uint8_t v___x_573_; lean_object* v_env_574_; lean_object* v___x_575_; lean_object* v_toCold_576_; lean_object* v_mctx_577_; lean_object* v_lctx_578_; lean_object* v_options_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; 
v___x_571_ = lean_st_ref_get(v___y_569_);
v_env_572_ = lean_ctor_get(v___x_571_, 0);
lean_inc_ref(v_env_572_);
lean_dec(v___x_571_);
v___x_573_ = 0;
v_env_574_ = l_Lean_Environment_setRecordingDeps(v_env_572_, v___x_573_);
v___x_575_ = lean_st_ref_get(v___y_567_);
v_toCold_576_ = lean_ctor_get(v___y_568_, 0);
v_mctx_577_ = lean_ctor_get(v___x_575_, 0);
lean_inc_ref(v_mctx_577_);
lean_dec(v___x_575_);
v_lctx_578_ = lean_ctor_get(v___y_566_, 2);
v_options_579_ = lean_ctor_get(v_toCold_576_, 2);
lean_inc_ref(v_options_579_);
lean_inc_ref(v_lctx_578_);
v___x_580_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_580_, 0, v_env_574_);
lean_ctor_set(v___x_580_, 1, v_mctx_577_);
lean_ctor_set(v___x_580_, 2, v_lctx_578_);
lean_ctor_set(v___x_580_, 3, v_options_579_);
v___x_581_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v_msgData_565_);
v___x_582_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_582_, 0, v___x_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3___boxed(lean_object* v_msgData_583_, lean_object* v___y_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msgData_583_, v___y_584_, v___y_585_, v___y_586_, v___y_587_);
lean_dec(v___y_587_);
lean_dec_ref(v___y_586_);
lean_dec(v___y_585_);
lean_dec_ref(v___y_584_);
return v_res_589_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_590_; double v___x_591_; 
v___x_590_ = lean_unsigned_to_nat(0u);
v___x_591_ = lean_float_of_nat(v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(lean_object* v_cls_595_, lean_object* v_msg_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_){
_start:
{
lean_object* v_ref_602_; lean_object* v___x_603_; lean_object* v_a_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_649_; 
v_ref_602_ = lean_ctor_get(v___y_599_, 2);
v___x_603_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3_spec__3(v_msg_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_);
v_a_604_ = lean_ctor_get(v___x_603_, 0);
v_isSharedCheck_649_ = !lean_is_exclusive(v___x_603_);
if (v_isSharedCheck_649_ == 0)
{
v___x_606_ = v___x_603_;
v_isShared_607_ = v_isSharedCheck_649_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_a_604_);
lean_dec(v___x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_649_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v_traceState_609_; lean_object* v_env_610_; lean_object* v_nextMacroScope_611_; lean_object* v_ngen_612_; lean_object* v_auxDeclNGen_613_; lean_object* v_cache_614_; lean_object* v_recordedDeps_615_; lean_object* v_messages_616_; lean_object* v_infoState_617_; lean_object* v_snapshotTasks_618_; lean_object* v___x_620_; uint8_t v_isShared_621_; uint8_t v_isSharedCheck_648_; 
v___x_608_ = lean_st_ref_take(v___y_600_);
v_traceState_609_ = lean_ctor_get(v___x_608_, 4);
v_env_610_ = lean_ctor_get(v___x_608_, 0);
v_nextMacroScope_611_ = lean_ctor_get(v___x_608_, 1);
v_ngen_612_ = lean_ctor_get(v___x_608_, 2);
v_auxDeclNGen_613_ = lean_ctor_get(v___x_608_, 3);
v_cache_614_ = lean_ctor_get(v___x_608_, 5);
v_recordedDeps_615_ = lean_ctor_get(v___x_608_, 6);
v_messages_616_ = lean_ctor_get(v___x_608_, 7);
v_infoState_617_ = lean_ctor_get(v___x_608_, 8);
v_snapshotTasks_618_ = lean_ctor_get(v___x_608_, 9);
v_isSharedCheck_648_ = !lean_is_exclusive(v___x_608_);
if (v_isSharedCheck_648_ == 0)
{
v___x_620_ = v___x_608_;
v_isShared_621_ = v_isSharedCheck_648_;
goto v_resetjp_619_;
}
else
{
lean_inc(v_snapshotTasks_618_);
lean_inc(v_infoState_617_);
lean_inc(v_messages_616_);
lean_inc(v_recordedDeps_615_);
lean_inc(v_cache_614_);
lean_inc(v_traceState_609_);
lean_inc(v_auxDeclNGen_613_);
lean_inc(v_ngen_612_);
lean_inc(v_nextMacroScope_611_);
lean_inc(v_env_610_);
lean_dec(v___x_608_);
v___x_620_ = lean_box(0);
v_isShared_621_ = v_isSharedCheck_648_;
goto v_resetjp_619_;
}
v_resetjp_619_:
{
uint64_t v_tid_622_; lean_object* v_traces_623_; lean_object* v___x_625_; uint8_t v_isShared_626_; uint8_t v_isSharedCheck_647_; 
v_tid_622_ = lean_ctor_get_uint64(v_traceState_609_, sizeof(void*)*1);
v_traces_623_ = lean_ctor_get(v_traceState_609_, 0);
v_isSharedCheck_647_ = !lean_is_exclusive(v_traceState_609_);
if (v_isSharedCheck_647_ == 0)
{
v___x_625_ = v_traceState_609_;
v_isShared_626_ = v_isSharedCheck_647_;
goto v_resetjp_624_;
}
else
{
lean_inc(v_traces_623_);
lean_dec(v_traceState_609_);
v___x_625_ = lean_box(0);
v_isShared_626_ = v_isSharedCheck_647_;
goto v_resetjp_624_;
}
v_resetjp_624_:
{
lean_object* v___x_627_; lean_object* v___x_628_; double v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_638_; 
v___x_627_ = lean_box(0);
v___x_628_ = lean_box(0);
v___x_629_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__0);
v___x_630_ = 0;
v___x_631_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__1));
v___x_632_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_632_, 0, v_cls_595_);
lean_ctor_set(v___x_632_, 1, v___x_628_);
lean_ctor_set(v___x_632_, 2, v___x_631_);
lean_ctor_set_float(v___x_632_, sizeof(void*)*3, v___x_629_);
lean_ctor_set_float(v___x_632_, sizeof(void*)*3 + 8, v___x_629_);
lean_ctor_set_uint8(v___x_632_, sizeof(void*)*3 + 16, v___x_630_);
v___x_633_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___closed__2));
v___x_634_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_634_, 0, v___x_632_);
lean_ctor_set(v___x_634_, 1, v_a_604_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
lean_inc(v_ref_602_);
v___x_635_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_635_, 0, v_ref_602_);
lean_ctor_set(v___x_635_, 1, v___x_634_);
v___x_636_ = l_Lean_PersistentArray_push___redArg(v_traces_623_, v___x_635_);
if (v_isShared_626_ == 0)
{
lean_ctor_set(v___x_625_, 0, v___x_636_);
v___x_638_ = v___x_625_;
goto v_reusejp_637_;
}
else
{
lean_object* v_reuseFailAlloc_646_; 
v_reuseFailAlloc_646_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_646_, 0, v___x_636_);
lean_ctor_set_uint64(v_reuseFailAlloc_646_, sizeof(void*)*1, v_tid_622_);
v___x_638_ = v_reuseFailAlloc_646_;
goto v_reusejp_637_;
}
v_reusejp_637_:
{
lean_object* v___x_640_; 
if (v_isShared_621_ == 0)
{
lean_ctor_set(v___x_620_, 4, v___x_638_);
v___x_640_ = v___x_620_;
goto v_reusejp_639_;
}
else
{
lean_object* v_reuseFailAlloc_645_; 
v_reuseFailAlloc_645_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_645_, 0, v_env_610_);
lean_ctor_set(v_reuseFailAlloc_645_, 1, v_nextMacroScope_611_);
lean_ctor_set(v_reuseFailAlloc_645_, 2, v_ngen_612_);
lean_ctor_set(v_reuseFailAlloc_645_, 3, v_auxDeclNGen_613_);
lean_ctor_set(v_reuseFailAlloc_645_, 4, v___x_638_);
lean_ctor_set(v_reuseFailAlloc_645_, 5, v_cache_614_);
lean_ctor_set(v_reuseFailAlloc_645_, 6, v_recordedDeps_615_);
lean_ctor_set(v_reuseFailAlloc_645_, 7, v_messages_616_);
lean_ctor_set(v_reuseFailAlloc_645_, 8, v_infoState_617_);
lean_ctor_set(v_reuseFailAlloc_645_, 9, v_snapshotTasks_618_);
v___x_640_ = v_reuseFailAlloc_645_;
goto v_reusejp_639_;
}
v_reusejp_639_:
{
lean_object* v___x_641_; lean_object* v___x_643_; 
v___x_641_ = lean_st_ref_put(v___y_600_, v___x_640_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 0, v___x_627_);
v___x_643_ = v___x_606_;
goto v_reusejp_642_;
}
else
{
lean_object* v_reuseFailAlloc_644_; 
v_reuseFailAlloc_644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_644_, 0, v___x_627_);
v___x_643_ = v_reuseFailAlloc_644_;
goto v_reusejp_642_;
}
v_reusejp_642_:
{
return v___x_643_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg___boxed(lean_object* v_cls_650_, lean_object* v_msg_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_){
_start:
{
lean_object* v_res_657_; 
v_res_657_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_650_, v_msg_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
return v_res_657_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed(lean_object* v_toInductionSubgoal_665_, lean_object* v_mvarId_666_, lean_object* v_fields_667_, lean_object* v_sz_668_, lean_object* v___x_669_, lean_object* v___x_670_, lean_object* v___x_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_){
_start:
{
size_t v_sz_boxed_678_; size_t v___x_16041__boxed_679_; uint8_t v___x_16043__boxed_680_; lean_object* v_res_681_; 
v_sz_boxed_678_ = lean_unbox_usize(v_sz_668_);
lean_dec(v_sz_668_);
v___x_16041__boxed_679_ = lean_unbox_usize(v___x_669_);
lean_dec(v___x_669_);
v___x_16043__boxed_680_ = lean_unbox(v___x_671_);
v_res_681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(v_toInductionSubgoal_665_, v_mvarId_666_, v_fields_667_, v_sz_boxed_678_, v___x_16041__boxed_679_, v___x_670_, v___x_16043__boxed_680_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec_ref(v___y_673_);
lean_dec(v___y_672_);
lean_dec_ref(v_fields_667_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(lean_object* v_val_682_, lean_object* v_as_683_, size_t v_sz_684_, size_t v_i_685_, lean_object* v_b_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
uint8_t v___x_693_; 
v___x_693_ = lean_usize_dec_lt(v_i_685_, v_sz_684_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
v___x_694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_694_, 0, v_b_686_);
return v___x_694_;
}
else
{
lean_object* v_a_695_; lean_object* v_toInductionSubgoal_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_737_; 
lean_dec_ref(v_b_686_);
v_a_695_ = lean_array_uget(v_as_683_, v_i_685_);
v_toInductionSubgoal_696_ = lean_ctor_get(v_a_695_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v_a_695_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v_a_695_, 1);
lean_dec(v_unused_738_);
v___x_698_ = v_a_695_;
v_isShared_699_ = v_isSharedCheck_737_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_toInductionSubgoal_696_);
lean_dec(v_a_695_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_737_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v_mvarId_700_; lean_object* v_fields_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; uint8_t v___x_705_; size_t v_sz_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___f_710_; lean_object* v___x_711_; 
v_mvarId_700_ = lean_ctor_get(v_toInductionSubgoal_696_, 0);
lean_inc_n(v_mvarId_700_, 2);
v_fields_701_ = lean_ctor_get(v_toInductionSubgoal_696_, 1);
lean_inc_ref(v_fields_701_);
v___x_702_ = lean_box(0);
v___x_703_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_704_ = lean_unsigned_to_nat(0u);
v___x_705_ = lean_nat_dec_eq(v_val_682_, v___x_704_);
v_sz_706_ = lean_array_size(v_fields_701_);
v___x_707_ = lean_box_usize(v_sz_706_);
v___x_708_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed__const__1));
v___x_709_ = lean_box(v___x_705_);
v___f_710_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0___boxed), 13, 7);
lean_closure_set(v___f_710_, 0, v_toInductionSubgoal_696_);
lean_closure_set(v___f_710_, 1, v_mvarId_700_);
lean_closure_set(v___f_710_, 2, v_fields_701_);
lean_closure_set(v___f_710_, 3, v___x_707_);
lean_closure_set(v___f_710_, 4, v___x_708_);
lean_closure_set(v___f_710_, 5, v___x_703_);
lean_closure_set(v___f_710_, 6, v___x_709_);
v___x_711_ = l_Lean_MVarId_withContext___at___00Lean_Meta_ElimEmptyInductive_elim_spec__1___redArg(v_mvarId_700_, v___f_710_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
if (lean_obj_tag(v___x_711_) == 0)
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_728_; 
v_a_712_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_728_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_728_ == 0)
{
v___x_714_ = v___x_711_;
v_isShared_715_ = v_isSharedCheck_728_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_711_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_728_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
uint8_t v___x_716_; 
v___x_716_ = lean_unbox(v_a_712_);
lean_dec(v_a_712_);
if (v___x_716_ == 0)
{
lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_720_; 
v___x_717_ = lean_box(v___x_705_);
v___x_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_718_, 0, v___x_717_);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v___x_702_);
lean_ctor_set(v___x_698_, 0, v___x_718_);
v___x_720_ = v___x_698_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_724_, 1, v___x_702_);
v___x_720_ = v_reuseFailAlloc_724_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
lean_object* v___x_722_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v___x_720_);
v___x_722_ = v___x_714_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_720_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
return v___x_722_;
}
}
}
else
{
size_t v___x_725_; size_t v___x_726_; 
lean_del_object(v___x_714_);
lean_del_object(v___x_698_);
v___x_725_ = ((size_t)1ULL);
v___x_726_ = lean_usize_add(v_i_685_, v___x_725_);
v_i_685_ = v___x_726_;
v_b_686_ = v___x_703_;
goto _start;
}
}
}
else
{
lean_object* v_a_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_del_object(v___x_698_);
v_a_729_ = lean_ctor_get(v___x_711_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v___x_711_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v___x_711_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_a_729_);
lean_dec(v___x_711_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_a_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
return v___x_734_;
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
lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_749_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_750_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__6));
v___x_751_ = l_Lean_Name_append(v___x_750_, v___x_749_);
return v___x_751_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1(void){
_start:
{
lean_object* v___x_753_; lean_object* v___x_754_; 
v___x_753_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__0));
v___x_754_ = l_Lean_stringToMessageData(v___x_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0(lean_object* v_mvarId_755_, lean_object* v_fvarId_756_, lean_object* v___x_757_, uint8_t v___x_758_, lean_object* v___x_759_, lean_object* v_val_760_, uint8_t v___x_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v___x_768_; 
v___x_768_ = l_Lean_MVarId_cases(v_mvarId_755_, v_fvarId_756_, v___x_757_, v___x_758_, v___x_759_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_768_) == 0)
{
lean_object* v_a_769_; lean_object* v___y_771_; lean_object* v___y_772_; lean_object* v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v_toCold_802_; lean_object* v_options_803_; uint8_t v_hasTrace_804_; 
v_a_769_ = lean_ctor_get(v___x_768_, 0);
lean_inc(v_a_769_);
lean_dec_ref_known(v___x_768_, 1);
v_toCold_802_ = lean_ctor_get(v___y_765_, 0);
v_options_803_ = lean_ctor_get(v_toCold_802_, 2);
v_hasTrace_804_ = lean_ctor_get_uint8(v_options_803_, sizeof(void*)*1);
if (v_hasTrace_804_ == 0)
{
v___y_771_ = v___y_762_;
v___y_772_ = v___y_763_;
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
goto v___jp_770_;
}
else
{
lean_object* v_inheritedTraceOptions_805_; lean_object* v___x_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_inheritedTraceOptions_805_ = lean_ctor_get(v_toCold_802_, 11);
v___x_806_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_807_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_808_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_805_, v_options_803_, v___x_807_);
if (v___x_808_ == 0)
{
v___y_771_ = v___y_762_;
v___y_772_ = v___y_763_;
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
goto v___jp_770_;
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_809_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1, &l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___lam__0___closed__1);
v___x_810_ = lean_array_get_size(v_a_769_);
v___x_811_ = l_Nat_reprFast(v___x_810_);
v___x_812_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_812_, 0, v___x_811_);
v___x_813_ = l_Lean_MessageData_ofFormat(v___x_812_);
v___x_814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_814_, 0, v___x_809_);
lean_ctor_set(v___x_814_, 1, v___x_813_);
v___x_815_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_806_, v___x_814_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_815_) == 0)
{
lean_dec_ref_known(v___x_815_, 1);
v___y_771_ = v___y_762_;
v___y_772_ = v___y_763_;
v___y_773_ = v___y_764_;
v___y_774_ = v___y_765_;
v___y_775_ = v___y_766_;
goto v___jp_770_;
}
else
{
lean_object* v_a_816_; lean_object* v___x_818_; uint8_t v_isShared_819_; uint8_t v_isSharedCheck_823_; 
lean_dec(v_a_769_);
v_a_816_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_823_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_823_ == 0)
{
v___x_818_ = v___x_815_;
v_isShared_819_ = v_isSharedCheck_823_;
goto v_resetjp_817_;
}
else
{
lean_inc(v_a_816_);
lean_dec(v___x_815_);
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
}
v___jp_770_:
{
lean_object* v___x_776_; size_t v_sz_777_; size_t v___x_778_; lean_object* v___x_779_; 
v___x_776_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_sz_777_ = lean_array_size(v_a_769_);
v___x_778_ = ((size_t)0ULL);
v___x_779_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_760_, v_a_769_, v_sz_777_, v___x_778_, v___x_776_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_);
lean_dec(v_a_769_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_793_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_793_ == 0)
{
v___x_782_ = v___x_779_;
v_isShared_783_ = v_isSharedCheck_793_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_a_780_);
lean_dec(v___x_779_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_793_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v_fst_784_; 
v_fst_784_ = lean_ctor_get(v_a_780_, 0);
lean_inc(v_fst_784_);
lean_dec(v_a_780_);
if (lean_obj_tag(v_fst_784_) == 0)
{
lean_object* v___x_785_; lean_object* v___x_787_; 
v___x_785_ = lean_box(v___x_761_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v___x_785_);
v___x_787_ = v___x_782_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
else
{
lean_object* v_val_789_; lean_object* v___x_791_; 
v_val_789_ = lean_ctor_get(v_fst_784_, 0);
lean_inc(v_val_789_);
lean_dec_ref_known(v_fst_784_, 1);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 0, v_val_789_);
v___x_791_ = v___x_782_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_val_789_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
else
{
lean_object* v_a_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_801_; 
v_a_794_ = lean_ctor_get(v___x_779_, 0);
v_isSharedCheck_801_ = !lean_is_exclusive(v___x_779_);
if (v_isSharedCheck_801_ == 0)
{
v___x_796_ = v___x_779_;
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_a_794_);
lean_dec(v___x_779_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_801_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_799_; 
if (v_isShared_797_ == 0)
{
v___x_799_ = v___x_796_;
goto v_reusejp_798_;
}
else
{
lean_object* v_reuseFailAlloc_800_; 
v_reuseFailAlloc_800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_800_, 0, v_a_794_);
v___x_799_ = v_reuseFailAlloc_800_;
goto v_reusejp_798_;
}
v_reusejp_798_:
{
return v___x_799_;
}
}
}
}
}
else
{
lean_object* v_a_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_869_; 
v_a_824_ = lean_ctor_get(v___x_768_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_768_);
if (v_isSharedCheck_869_ == 0)
{
v___x_826_ = v___x_768_;
v_isShared_827_ = v_isSharedCheck_869_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_a_824_);
lean_dec(v___x_768_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_869_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
uint8_t v___y_829_; uint8_t v___x_867_; 
v___x_867_ = l_Lean_Exception_isInterrupt(v_a_824_);
if (v___x_867_ == 0)
{
uint8_t v___x_868_; 
lean_inc(v_a_824_);
v___x_868_ = l_Lean_Exception_isRuntime(v_a_824_);
v___y_829_ = v___x_868_;
goto v___jp_828_;
}
else
{
v___y_829_ = v___x_867_;
goto v___jp_828_;
}
v___jp_828_:
{
if (v___y_829_ == 0)
{
lean_object* v_toCold_830_; lean_object* v_options_831_; uint8_t v_hasTrace_832_; 
v_toCold_830_ = lean_ctor_get(v___y_765_, 0);
v_options_831_ = lean_ctor_get(v_toCold_830_, 2);
v_hasTrace_832_ = lean_ctor_get_uint8(v_options_831_, sizeof(void*)*1);
if (v_hasTrace_832_ == 0)
{
lean_object* v___x_833_; lean_object* v___x_835_; 
lean_dec(v_a_824_);
v___x_833_ = lean_box(v___x_758_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_833_);
v___x_835_ = v___x_826_;
goto v_reusejp_834_;
}
else
{
lean_object* v_reuseFailAlloc_836_; 
v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
v___x_835_ = v_reuseFailAlloc_836_;
goto v_reusejp_834_;
}
v_reusejp_834_:
{
return v___x_835_;
}
}
else
{
lean_object* v_inheritedTraceOptions_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v_inheritedTraceOptions_837_ = lean_ctor_get(v_toCold_830_, 11);
v___x_838_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_839_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_840_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_837_, v_options_831_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_843_; 
lean_dec(v_a_824_);
v___x_841_ = lean_box(v___x_758_);
if (v_isShared_827_ == 0)
{
lean_ctor_set_tag(v___x_826_, 0);
lean_ctor_set(v___x_826_, 0, v___x_841_);
v___x_843_ = v___x_826_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; 
lean_del_object(v___x_826_);
v___x_845_ = l_Lean_Exception_toMessageData(v_a_824_);
v___x_846_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_838_, v___x_845_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
if (lean_obj_tag(v___x_846_) == 0)
{
lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v___x_846_, 0);
lean_dec(v_unused_855_);
v___x_848_ = v___x_846_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_dec(v___x_846_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_box(v___x_758_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
else
{
lean_object* v_a_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_863_; 
v_a_856_ = lean_ctor_get(v___x_846_, 0);
v_isSharedCheck_863_ = !lean_is_exclusive(v___x_846_);
if (v_isSharedCheck_863_ == 0)
{
v___x_858_ = v___x_846_;
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_a_856_);
lean_dec(v___x_846_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_863_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_859_ == 0)
{
v___x_861_ = v___x_858_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_a_856_);
v___x_861_ = v_reuseFailAlloc_862_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
return v___x_861_;
}
}
}
}
}
}
else
{
lean_object* v___x_865_; 
if (v_isShared_827_ == 0)
{
v___x_865_ = v___x_826_;
goto v_reusejp_864_;
}
else
{
lean_object* v_reuseFailAlloc_866_; 
v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_866_, 0, v_a_824_);
v___x_865_ = v_reuseFailAlloc_866_;
goto v_reusejp_864_;
}
v_reusejp_864_:
{
return v___x_865_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed(lean_object* v_mvarId_870_, lean_object* v_fvarId_871_, lean_object* v___x_872_, lean_object* v___x_873_, lean_object* v___x_874_, lean_object* v_val_875_, lean_object* v___x_876_, lean_object* v___y_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_){
_start:
{
uint8_t v___x_16163__boxed_883_; uint8_t v___x_16166__boxed_884_; lean_object* v_res_885_; 
v___x_16163__boxed_883_ = lean_unbox(v___x_873_);
v___x_16166__boxed_884_ = lean_unbox(v___x_876_);
v_res_885_ = l_Lean_Meta_ElimEmptyInductive_elim___lam__0(v_mvarId_870_, v_fvarId_871_, v___x_872_, v___x_16163__boxed_883_, v___x_874_, v_val_875_, v___x_16166__boxed_884_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
lean_dec(v___y_881_);
lean_dec_ref(v___y_880_);
lean_dec(v___y_879_);
lean_dec_ref(v___y_878_);
lean_dec(v___y_877_);
lean_dec(v_val_875_);
return v_res_885_;
}
}
static lean_object* _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9(void){
_start:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__8));
v___x_888_ = l_Lean_stringToMessageData(v___x_887_);
return v___x_888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim(lean_object* v_mvarId_889_, lean_object* v_fvarId_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_){
_start:
{
lean_object* v___x_901_; lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_901_ = lean_st_ref_get(v_a_891_);
v___x_902_ = lean_unsigned_to_nat(0u);
v___x_903_ = lean_nat_dec_eq(v___x_901_, v___x_902_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___f_913_; lean_object* v___x_914_; 
v___x_904_ = 1;
v___x_905_ = lean_st_ref_take(v_a_891_);
v___x_906_ = lean_unsigned_to_nat(1u);
v___x_907_ = lean_nat_sub(v___x_905_, v___x_906_);
lean_dec(v___x_905_);
v___x_908_ = lean_st_ref_put(v_a_891_, v___x_907_);
v___x_909_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__0));
v___x_910_ = lean_box(0);
v___x_911_ = lean_box(v___x_903_);
v___x_912_ = lean_box(v___x_904_);
v___f_913_ = lean_alloc_closure((void*)(l_Lean_Meta_ElimEmptyInductive_elim___lam__0___boxed), 13, 7);
lean_closure_set(v___f_913_, 0, v_mvarId_889_);
lean_closure_set(v___f_913_, 1, v_fvarId_890_);
lean_closure_set(v___f_913_, 2, v___x_909_);
lean_closure_set(v___f_913_, 3, v___x_911_);
lean_closure_set(v___f_913_, 4, v___x_910_);
lean_closure_set(v___f_913_, 5, v___x_901_);
lean_closure_set(v___f_913_, 6, v___x_912_);
v___x_914_ = l_Lean_commitWhen___at___00Lean_Meta_ElimEmptyInductive_elim_spec__4(v___f_913_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
return v___x_914_;
}
else
{
lean_object* v_toCold_915_; lean_object* v_options_916_; uint8_t v_hasTrace_917_; 
lean_dec(v___x_901_);
lean_dec(v_fvarId_890_);
lean_dec(v_mvarId_889_);
v_toCold_915_ = lean_ctor_get(v_a_894_, 0);
v_options_916_ = lean_ctor_get(v_toCold_915_, 2);
v_hasTrace_917_ = lean_ctor_get_uint8(v_options_916_, sizeof(void*)*1);
if (v_hasTrace_917_ == 0)
{
goto v___jp_897_;
}
else
{
lean_object* v_inheritedTraceOptions_918_; lean_object* v___x_919_; lean_object* v___x_920_; uint8_t v___x_921_; 
v_inheritedTraceOptions_918_ = lean_ctor_get(v_toCold_915_, 11);
v___x_919_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_920_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__7, &l_Lean_Meta_ElimEmptyInductive_elim___closed__7_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__7);
v___x_921_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_918_, v_options_916_, v___x_920_);
if (v___x_921_ == 0)
{
goto v___jp_897_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_obj_once(&l_Lean_Meta_ElimEmptyInductive_elim___closed__9, &l_Lean_Meta_ElimEmptyInductive_elim___closed__9_once, _init_l_Lean_Meta_ElimEmptyInductive_elim___closed__9);
v___x_923_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v___x_919_, v___x_922_, v_a_892_, v_a_893_, v_a_894_, v_a_895_);
if (lean_obj_tag(v___x_923_) == 0)
{
lean_dec_ref_known(v___x_923_, 1);
goto v___jp_897_;
}
else
{
lean_object* v_a_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_931_; 
v_a_924_ = lean_ctor_get(v___x_923_, 0);
v_isSharedCheck_931_ = !lean_is_exclusive(v___x_923_);
if (v_isSharedCheck_931_ == 0)
{
v___x_926_ = v___x_923_;
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_a_924_);
lean_dec(v___x_923_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_931_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_929_; 
if (v_isShared_927_ == 0)
{
v___x_929_ = v___x_926_;
goto v_reusejp_928_;
}
else
{
lean_object* v_reuseFailAlloc_930_; 
v_reuseFailAlloc_930_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_930_, 0, v_a_924_);
v___x_929_ = v_reuseFailAlloc_930_;
goto v_reusejp_928_;
}
v_reusejp_928_:
{
return v___x_929_;
}
}
}
}
}
}
v___jp_897_:
{
uint8_t v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_898_ = 0;
v___x_899_ = lean_box(v___x_898_);
v___x_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_900_, 0, v___x_899_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(lean_object* v___x_932_, lean_object* v___x_933_, lean_object* v_as_934_, size_t v_sz_935_, size_t v_i_936_, lean_object* v_b_937_, lean_object* v___y_938_, lean_object* v___y_939_, lean_object* v___y_940_, lean_object* v___y_941_, lean_object* v___y_942_){
_start:
{
lean_object* v_a_945_; uint8_t v___x_949_; 
v___x_949_ = lean_usize_dec_lt(v_i_936_, v_sz_935_);
if (v___x_949_ == 0)
{
lean_object* v___x_950_; 
lean_dec(v___x_933_);
lean_dec_ref(v___x_932_);
v___x_950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_950_, 0, v_b_937_);
return v___x_950_;
}
else
{
lean_object* v_subst_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v_a_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
lean_dec_ref(v_b_937_);
v_subst_951_ = lean_ctor_get(v___x_932_, 2);
v___x_952_ = lean_box(0);
v___x_953_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v_a_954_ = lean_array_uget_borrowed(v_as_934_, v_i_936_);
lean_inc(v_subst_951_);
v___x_955_ = l_Lean_Meta_FVarSubst_apply(v_subst_951_, v_a_954_);
v___x_956_ = l_Lean_Expr_isFVar(v___x_955_);
if (v___x_956_ == 0)
{
lean_dec_ref(v___x_955_);
v_a_945_ = v___x_953_;
goto v___jp_944_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; 
v___x_957_ = l_Lean_Expr_fvarId_x21(v___x_955_);
lean_dec_ref(v___x_955_);
lean_inc(v___x_957_);
v___x_958_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v___x_957_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_958_) == 0)
{
lean_object* v_a_959_; uint8_t v___x_960_; 
v_a_959_ = lean_ctor_get(v___x_958_, 0);
lean_inc(v_a_959_);
lean_dec_ref_known(v___x_958_, 1);
v___x_960_ = lean_unbox(v_a_959_);
lean_dec(v_a_959_);
if (v___x_960_ == 0)
{
lean_dec(v___x_957_);
v_a_945_ = v___x_953_;
goto v___jp_944_;
}
else
{
lean_object* v___x_961_; 
lean_inc(v___x_933_);
v___x_961_ = l_Lean_Meta_ElimEmptyInductive_elim(v___x_933_, v___x_957_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_);
if (lean_obj_tag(v___x_961_) == 0)
{
lean_object* v_a_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_973_; 
v_a_962_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_973_ == 0)
{
v___x_964_ = v___x_961_;
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_a_962_);
lean_dec(v___x_961_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_973_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
uint8_t v___x_966_; 
v___x_966_ = lean_unbox(v_a_962_);
lean_dec(v_a_962_);
if (v___x_966_ == 0)
{
lean_del_object(v___x_964_);
v_a_945_ = v___x_953_;
goto v___jp_944_;
}
else
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
lean_dec(v___x_933_);
lean_dec_ref(v___x_932_);
v___x_967_ = lean_box(v___x_956_);
v___x_968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_968_, 0, v___x_967_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v___x_952_);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 0, v___x_969_);
v___x_971_ = v___x_964_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
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
else
{
lean_object* v_a_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_981_; 
lean_dec(v___x_933_);
lean_dec_ref(v___x_932_);
v_a_974_ = lean_ctor_get(v___x_961_, 0);
v_isSharedCheck_981_ = !lean_is_exclusive(v___x_961_);
if (v_isSharedCheck_981_ == 0)
{
v___x_976_ = v___x_961_;
v_isShared_977_ = v_isSharedCheck_981_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_a_974_);
lean_dec(v___x_961_);
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
else
{
lean_object* v_a_982_; lean_object* v___x_984_; uint8_t v_isShared_985_; uint8_t v_isSharedCheck_989_; 
lean_dec(v___x_957_);
lean_dec(v___x_933_);
lean_dec_ref(v___x_932_);
v_a_982_ = lean_ctor_get(v___x_958_, 0);
v_isSharedCheck_989_ = !lean_is_exclusive(v___x_958_);
if (v_isSharedCheck_989_ == 0)
{
v___x_984_ = v___x_958_;
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
else
{
lean_inc(v_a_982_);
lean_dec(v___x_958_);
v___x_984_ = lean_box(0);
v_isShared_985_ = v_isSharedCheck_989_;
goto v_resetjp_983_;
}
v_resetjp_983_:
{
lean_object* v___x_987_; 
if (v_isShared_985_ == 0)
{
v___x_987_ = v___x_984_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_a_982_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
v___jp_944_:
{
size_t v___x_946_; size_t v___x_947_; 
v___x_946_ = ((size_t)1ULL);
v___x_947_ = lean_usize_add(v_i_936_, v___x_946_);
lean_inc_ref(v_a_945_);
v_i_936_ = v___x_947_;
v_b_937_ = v_a_945_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___lam__0(lean_object* v_toInductionSubgoal_990_, lean_object* v_mvarId_991_, lean_object* v_fields_992_, size_t v_sz_993_, size_t v___x_994_, lean_object* v___x_995_, uint8_t v___x_996_, lean_object* v___y_997_, lean_object* v___y_998_, lean_object* v___y_999_, lean_object* v___y_1000_, lean_object* v___y_1001_){
_start:
{
lean_object* v___x_1003_; 
v___x_1003_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v_toInductionSubgoal_990_, v_mvarId_991_, v_fields_992_, v_sz_993_, v___x_994_, v___x_995_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
if (lean_obj_tag(v___x_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1017_; 
v_a_1004_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1017_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1017_ == 0)
{
v___x_1006_ = v___x_1003_;
v_isShared_1007_ = v_isSharedCheck_1017_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_a_1004_);
lean_dec(v___x_1003_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1017_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v_fst_1008_; 
v_fst_1008_ = lean_ctor_get(v_a_1004_, 0);
lean_inc(v_fst_1008_);
lean_dec(v_a_1004_);
if (lean_obj_tag(v_fst_1008_) == 0)
{
lean_object* v___x_1009_; lean_object* v___x_1011_; 
v___x_1009_ = lean_box(v___x_996_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v___x_1009_);
v___x_1011_ = v___x_1006_;
goto v_reusejp_1010_;
}
else
{
lean_object* v_reuseFailAlloc_1012_; 
v_reuseFailAlloc_1012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1012_, 0, v___x_1009_);
v___x_1011_ = v_reuseFailAlloc_1012_;
goto v_reusejp_1010_;
}
v_reusejp_1010_:
{
return v___x_1011_;
}
}
else
{
lean_object* v_val_1013_; lean_object* v___x_1015_; 
v_val_1013_ = lean_ctor_get(v_fst_1008_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v_fst_1008_, 1);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 0, v_val_1013_);
v___x_1015_ = v___x_1006_;
goto v_reusejp_1014_;
}
else
{
lean_object* v_reuseFailAlloc_1016_; 
v_reuseFailAlloc_1016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_val_1013_);
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
else
{
lean_object* v_a_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1025_; 
v_a_1018_ = lean_ctor_get(v___x_1003_, 0);
v_isSharedCheck_1025_ = !lean_is_exclusive(v___x_1003_);
if (v_isSharedCheck_1025_ == 0)
{
v___x_1020_ = v___x_1003_;
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_a_1018_);
lean_dec(v___x_1003_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1025_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1023_; 
if (v_isShared_1021_ == 0)
{
v___x_1023_ = v___x_1020_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1024_; 
v_reuseFailAlloc_1024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
v___x_1023_ = v_reuseFailAlloc_1024_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
return v___x_1023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___boxed(lean_object* v_val_1026_, lean_object* v_as_1027_, lean_object* v_sz_1028_, lean_object* v_i_1029_, lean_object* v_b_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_){
_start:
{
size_t v_sz_boxed_1037_; size_t v_i_boxed_1038_; lean_object* v_res_1039_; 
v_sz_boxed_1037_ = lean_unbox_usize(v_sz_1028_);
lean_dec(v_sz_1028_);
v_i_boxed_1038_ = lean_unbox_usize(v_i_1029_);
lean_dec(v_i_1029_);
v_res_1039_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2(v_val_1026_, v_as_1027_, v_sz_boxed_1037_, v_i_boxed_1038_, v_b_1030_, v___y_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_);
lean_dec(v___y_1035_);
lean_dec_ref(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec(v___y_1031_);
lean_dec_ref(v_as_1027_);
lean_dec(v_val_1026_);
return v_res_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0___boxed(lean_object* v___x_1040_, lean_object* v___x_1041_, lean_object* v_as_1042_, lean_object* v_sz_1043_, lean_object* v_i_1044_, lean_object* v_b_1045_, lean_object* v___y_1046_, lean_object* v___y_1047_, lean_object* v___y_1048_, lean_object* v___y_1049_, lean_object* v___y_1050_, lean_object* v___y_1051_){
_start:
{
size_t v_sz_boxed_1052_; size_t v_i_boxed_1053_; lean_object* v_res_1054_; 
v_sz_boxed_1052_ = lean_unbox_usize(v_sz_1043_);
lean_dec(v_sz_1043_);
v_i_boxed_1053_ = lean_unbox_usize(v_i_1044_);
lean_dec(v_i_1044_);
v_res_1054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__0(v___x_1040_, v___x_1041_, v_as_1042_, v_sz_boxed_1052_, v_i_boxed_1053_, v_b_1045_, v___y_1046_, v___y_1047_, v___y_1048_, v___y_1049_, v___y_1050_);
lean_dec(v___y_1050_);
lean_dec_ref(v___y_1049_);
lean_dec(v___y_1048_);
lean_dec_ref(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec_ref(v_as_1042_);
return v_res_1054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ElimEmptyInductive_elim___boxed(lean_object* v_mvarId_1055_, lean_object* v_fvarId_1056_, lean_object* v_a_1057_, lean_object* v_a_1058_, lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_){
_start:
{
lean_object* v_res_1063_; 
v_res_1063_ = l_Lean_Meta_ElimEmptyInductive_elim(v_mvarId_1055_, v_fvarId_1056_, v_a_1057_, v_a_1058_, v_a_1059_, v_a_1060_, v_a_1061_);
lean_dec(v_a_1061_);
lean_dec_ref(v_a_1060_);
lean_dec(v_a_1059_);
lean_dec_ref(v_a_1058_);
lean_dec(v_a_1057_);
return v_res_1063_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(lean_object* v_cls_1064_, lean_object* v_msg_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___redArg(v_cls_1064_, v_msg_1065_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3___boxed(lean_object* v_cls_1073_, lean_object* v_msg_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_, lean_object* v___y_1077_, lean_object* v___y_1078_, lean_object* v___y_1079_, lean_object* v___y_1080_){
_start:
{
lean_object* v_res_1081_; 
v_res_1081_ = l_Lean_addTrace___at___00Lean_Meta_ElimEmptyInductive_elim_spec__3(v_cls_1073_, v_msg_1074_, v___y_1075_, v___y_1076_, v___y_1077_, v___y_1078_, v___y_1079_);
lean_dec(v___y_1079_);
lean_dec_ref(v___y_1078_);
lean_dec(v___y_1077_);
lean_dec_ref(v___y_1076_);
lean_dec(v___y_1075_);
return v_res_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(lean_object* v_x_1082_, lean_object* v___y_1083_, lean_object* v___y_1084_, lean_object* v___y_1085_, lean_object* v___y_1086_){
_start:
{
lean_object* v___x_1088_; 
v___x_1088_ = l_Lean_Meta_saveState___redArg(v___y_1084_, v___y_1086_);
if (lean_obj_tag(v___x_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___y_1091_; lean_object* v___y_1092_; uint8_t v___y_1093_; lean_object* v___y_1112_; lean_object* v_a_1113_; lean_object* v___x_1116_; 
v_a_1089_ = lean_ctor_get(v___x_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref_known(v___x_1088_, 1);
lean_inc(v___y_1086_);
lean_inc_ref(v___y_1085_);
lean_inc(v___y_1084_);
lean_inc_ref(v___y_1083_);
v___x_1116_ = lean_apply_5(v_x_1082_, v___y_1083_, v___y_1084_, v___y_1085_, v___y_1086_, lean_box(0));
if (lean_obj_tag(v___x_1116_) == 0)
{
lean_object* v_a_1117_; uint8_t v___x_1118_; 
v_a_1117_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1117_);
v___x_1118_ = lean_unbox(v_a_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; 
lean_dec_ref_known(v___x_1116_, 1);
lean_inc(v_a_1089_);
v___x_1119_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1089_, v___y_1084_, v___y_1086_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1126_; 
lean_dec(v_a_1089_);
v_isSharedCheck_1126_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1126_ == 0)
{
lean_object* v_unused_1127_; 
v_unused_1127_ = lean_ctor_get(v___x_1119_, 0);
lean_dec(v_unused_1127_);
v___x_1121_ = v___x_1119_;
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
else
{
lean_dec(v___x_1119_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1126_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1124_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 0, v_a_1117_);
v___x_1124_ = v___x_1121_;
goto v_reusejp_1123_;
}
else
{
lean_object* v_reuseFailAlloc_1125_; 
v_reuseFailAlloc_1125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1125_, 0, v_a_1117_);
v___x_1124_ = v_reuseFailAlloc_1125_;
goto v_reusejp_1123_;
}
v_reusejp_1123_:
{
return v___x_1124_;
}
}
}
else
{
lean_object* v_a_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1135_; 
lean_dec(v_a_1117_);
v_a_1128_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1135_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1135_ == 0)
{
v___x_1130_ = v___x_1119_;
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_a_1128_);
lean_dec(v___x_1119_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1135_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___x_1133_; 
lean_inc(v_a_1128_);
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
v___y_1112_ = v___x_1133_;
v_a_1113_ = v_a_1128_;
goto v___jp_1111_;
}
}
}
}
else
{
lean_dec(v_a_1117_);
lean_dec(v_a_1089_);
return v___x_1116_;
}
}
else
{
lean_object* v_a_1136_; 
v_a_1136_ = lean_ctor_get(v___x_1116_, 0);
lean_inc(v_a_1136_);
v___y_1112_ = v___x_1116_;
v_a_1113_ = v_a_1136_;
goto v___jp_1111_;
}
v___jp_1090_:
{
if (v___y_1093_ == 0)
{
lean_object* v___x_1094_; 
lean_dec_ref(v___y_1092_);
v___x_1094_ = l_Lean_Meta_SavedState_restore___redArg(v_a_1089_, v___y_1084_, v___y_1086_);
if (lean_obj_tag(v___x_1094_) == 0)
{
lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1101_; 
v_isSharedCheck_1101_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; 
v_unused_1102_ = lean_ctor_get(v___x_1094_, 0);
lean_dec(v_unused_1102_);
v___x_1096_ = v___x_1094_;
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
else
{
lean_dec(v___x_1094_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1101_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1099_; 
if (v_isShared_1097_ == 0)
{
lean_ctor_set_tag(v___x_1096_, 1);
lean_ctor_set(v___x_1096_, 0, v___y_1091_);
v___x_1099_ = v___x_1096_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___y_1091_);
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
lean_object* v_a_1103_; lean_object* v___x_1105_; uint8_t v_isShared_1106_; uint8_t v_isSharedCheck_1110_; 
lean_dec_ref(v___y_1091_);
v_a_1103_ = lean_ctor_get(v___x_1094_, 0);
v_isSharedCheck_1110_ = !lean_is_exclusive(v___x_1094_);
if (v_isSharedCheck_1110_ == 0)
{
v___x_1105_ = v___x_1094_;
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
else
{
lean_inc(v_a_1103_);
lean_dec(v___x_1094_);
v___x_1105_ = lean_box(0);
v_isShared_1106_ = v_isSharedCheck_1110_;
goto v_resetjp_1104_;
}
v_resetjp_1104_:
{
lean_object* v___x_1108_; 
if (v_isShared_1106_ == 0)
{
v___x_1108_ = v___x_1105_;
goto v_reusejp_1107_;
}
else
{
lean_object* v_reuseFailAlloc_1109_; 
v_reuseFailAlloc_1109_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1109_, 0, v_a_1103_);
v___x_1108_ = v_reuseFailAlloc_1109_;
goto v_reusejp_1107_;
}
v_reusejp_1107_:
{
return v___x_1108_;
}
}
}
}
else
{
lean_dec_ref(v___y_1091_);
lean_dec(v_a_1089_);
return v___y_1092_;
}
}
v___jp_1111_:
{
uint8_t v___x_1114_; 
v___x_1114_ = l_Lean_Exception_isInterrupt(v_a_1113_);
if (v___x_1114_ == 0)
{
uint8_t v___x_1115_; 
lean_inc_ref(v_a_1113_);
v___x_1115_ = l_Lean_Exception_isRuntime(v_a_1113_);
v___y_1091_ = v_a_1113_;
v___y_1092_ = v___y_1112_;
v___y_1093_ = v___x_1115_;
goto v___jp_1090_;
}
else
{
v___y_1091_ = v_a_1113_;
v___y_1092_ = v___y_1112_;
v___y_1093_ = v___x_1114_;
goto v___jp_1090_;
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec_ref(v_x_1082_);
v_a_1137_ = lean_ctor_get(v___x_1088_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1088_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1088_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1088_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0___boxed(lean_object* v_x_1145_, lean_object* v___y_1146_, lean_object* v___y_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_, lean_object* v___y_1150_){
_start:
{
lean_object* v_res_1151_; 
v_res_1151_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v_x_1145_, v___y_1146_, v___y_1147_, v___y_1148_, v___y_1149_);
lean_dec(v___y_1149_);
lean_dec_ref(v___y_1148_);
lean_dec(v___y_1147_);
lean_dec_ref(v___y_1146_);
return v_res_1151_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(lean_object* v_mvarId_1152_, lean_object* v_x_1153_, lean_object* v___y_1154_, lean_object* v___y_1155_, lean_object* v___y_1156_, lean_object* v___y_1157_){
_start:
{
lean_object* v___x_1159_; 
v___x_1159_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_1152_, v_x_1153_, v___y_1154_, v___y_1155_, v___y_1156_, v___y_1157_);
if (lean_obj_tag(v___x_1159_) == 0)
{
lean_object* v_a_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1167_; 
v_a_1160_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1162_ = v___x_1159_;
v_isShared_1163_ = v_isSharedCheck_1167_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_a_1160_);
lean_dec(v___x_1159_);
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
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1175_; 
v_a_1168_ = lean_ctor_get(v___x_1159_, 0);
v_isSharedCheck_1175_ = !lean_is_exclusive(v___x_1159_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1170_ = v___x_1159_;
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_a_1168_);
lean_dec(v___x_1159_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1175_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v___x_1173_; 
if (v_isShared_1171_ == 0)
{
v___x_1173_ = v___x_1170_;
goto v_reusejp_1172_;
}
else
{
lean_object* v_reuseFailAlloc_1174_; 
v_reuseFailAlloc_1174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1174_, 0, v_a_1168_);
v___x_1173_ = v_reuseFailAlloc_1174_;
goto v_reusejp_1172_;
}
v_reusejp_1172_:
{
return v___x_1173_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg___boxed(lean_object* v_mvarId_1176_, lean_object* v_x_1177_, lean_object* v___y_1178_, lean_object* v___y_1179_, lean_object* v___y_1180_, lean_object* v___y_1181_, lean_object* v___y_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1176_, v_x_1177_, v___y_1178_, v___y_1179_, v___y_1180_, v___y_1181_);
lean_dec(v___y_1181_);
lean_dec_ref(v___y_1180_);
lean_dec(v___y_1179_);
lean_dec_ref(v___y_1178_);
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(lean_object* v_00_u03b1_1184_, lean_object* v_mvarId_1185_, lean_object* v_x_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_, lean_object* v___y_1190_){
_start:
{
lean_object* v___x_1192_; 
v___x_1192_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1185_, v_x_1186_, v___y_1187_, v___y_1188_, v___y_1189_, v___y_1190_);
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___boxed(lean_object* v_00_u03b1_1193_, lean_object* v_mvarId_1194_, lean_object* v_x_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1(v_00_u03b1_1193_, v_mvarId_1194_, v_x_1195_, v___y_1196_, v___y_1197_, v___y_1198_, v___y_1199_);
lean_dec(v___y_1199_);
lean_dec_ref(v___y_1198_);
lean_dec(v___y_1197_);
lean_dec_ref(v___y_1196_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(lean_object* v_mvarId_1202_, lean_object* v_fuel_1203_, lean_object* v_fvarId_1204_, lean_object* v___y_1205_, lean_object* v___y_1206_, lean_object* v___y_1207_, lean_object* v___y_1208_){
_start:
{
lean_object* v___x_1210_; 
v___x_1210_ = l_Lean_MVarId_exfalso(v_mvarId_1202_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1210_) == 0)
{
lean_object* v_a_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; 
v_a_1211_ = lean_ctor_get(v___x_1210_, 0);
lean_inc(v_a_1211_);
lean_dec_ref_known(v___x_1210_, 1);
v___x_1212_ = lean_st_mk_ref(v_fuel_1203_);
v___x_1213_ = l_Lean_Meta_ElimEmptyInductive_elim(v_a_1211_, v_fvarId_1204_, v___x_1212_, v___y_1205_, v___y_1206_, v___y_1207_, v___y_1208_);
if (lean_obj_tag(v___x_1213_) == 0)
{
lean_object* v_a_1214_; lean_object* v___x_1216_; uint8_t v_isShared_1217_; uint8_t v_isSharedCheck_1222_; 
v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
v_isSharedCheck_1222_ = !lean_is_exclusive(v___x_1213_);
if (v_isSharedCheck_1222_ == 0)
{
v___x_1216_ = v___x_1213_;
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
else
{
lean_inc(v_a_1214_);
lean_dec(v___x_1213_);
v___x_1216_ = lean_box(0);
v_isShared_1217_ = v_isSharedCheck_1222_;
goto v_resetjp_1215_;
}
v_resetjp_1215_:
{
lean_object* v___x_1218_; lean_object* v___x_1220_; 
v___x_1218_ = lean_st_ref_get(v___x_1212_);
lean_dec(v___x_1212_);
lean_dec(v___x_1218_);
if (v_isShared_1217_ == 0)
{
v___x_1220_ = v___x_1216_;
goto v_reusejp_1219_;
}
else
{
lean_object* v_reuseFailAlloc_1221_; 
v_reuseFailAlloc_1221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1221_, 0, v_a_1214_);
v___x_1220_ = v_reuseFailAlloc_1221_;
goto v_reusejp_1219_;
}
v_reusejp_1219_:
{
return v___x_1220_;
}
}
}
else
{
lean_dec(v___x_1212_);
return v___x_1213_;
}
}
else
{
lean_object* v_a_1223_; lean_object* v___x_1225_; uint8_t v_isShared_1226_; uint8_t v_isSharedCheck_1230_; 
lean_dec(v_fvarId_1204_);
lean_dec(v_fuel_1203_);
v_a_1223_ = lean_ctor_get(v___x_1210_, 0);
v_isSharedCheck_1230_ = !lean_is_exclusive(v___x_1210_);
if (v_isSharedCheck_1230_ == 0)
{
v___x_1225_ = v___x_1210_;
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
else
{
lean_inc(v_a_1223_);
lean_dec(v___x_1210_);
v___x_1225_ = lean_box(0);
v_isShared_1226_ = v_isSharedCheck_1230_;
goto v_resetjp_1224_;
}
v_resetjp_1224_:
{
lean_object* v___x_1228_; 
if (v_isShared_1226_ == 0)
{
v___x_1228_ = v___x_1225_;
goto v_reusejp_1227_;
}
else
{
lean_object* v_reuseFailAlloc_1229_; 
v_reuseFailAlloc_1229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1229_, 0, v_a_1223_);
v___x_1228_ = v_reuseFailAlloc_1229_;
goto v_reusejp_1227_;
}
v_reusejp_1227_:
{
return v___x_1228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed(lean_object* v_mvarId_1231_, lean_object* v_fuel_1232_, lean_object* v_fvarId_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0(v_mvarId_1231_, v_fuel_1232_, v_fvarId_1233_, v___y_1234_, v___y_1235_, v___y_1236_, v___y_1237_);
lean_dec(v___y_1237_);
lean_dec_ref(v___y_1236_);
lean_dec(v___y_1235_);
lean_dec_ref(v___y_1234_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(lean_object* v_fvarId_1240_, lean_object* v___f_1241_, lean_object* v___y_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_){
_start:
{
lean_object* v___x_1247_; 
v___x_1247_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isElimEmptyInductiveCandidate(v_fvarId_1240_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
if (lean_obj_tag(v___x_1247_) == 0)
{
lean_object* v_a_1248_; uint8_t v___x_1249_; 
v_a_1248_ = lean_ctor_get(v___x_1247_, 0);
v___x_1249_ = lean_unbox(v_a_1248_);
if (v___x_1249_ == 0)
{
lean_dec_ref(v___f_1241_);
return v___x_1247_;
}
else
{
lean_object* v___x_1250_; 
lean_dec_ref_known(v___x_1247_, 1);
v___x_1250_ = l_Lean_commitWhen___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__0(v___f_1241_, v___y_1242_, v___y_1243_, v___y_1244_, v___y_1245_);
return v___x_1250_;
}
}
else
{
lean_dec_ref(v___f_1241_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed(lean_object* v_fvarId_1251_, lean_object* v___f_1252_, lean_object* v___y_1253_, lean_object* v___y_1254_, lean_object* v___y_1255_, lean_object* v___y_1256_, lean_object* v___y_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1(v_fvarId_1251_, v___f_1252_, v___y_1253_, v___y_1254_, v___y_1255_, v___y_1256_);
lean_dec(v___y_1256_);
lean_dec_ref(v___y_1255_);
lean_dec(v___y_1254_);
lean_dec_ref(v___y_1253_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(lean_object* v_mvarId_1259_, lean_object* v_fvarId_1260_, lean_object* v_fuel_1261_, lean_object* v_a_1262_, lean_object* v_a_1263_, lean_object* v_a_1264_, lean_object* v_a_1265_){
_start:
{
lean_object* v___f_1267_; lean_object* v___f_1268_; lean_object* v___x_1269_; 
lean_inc(v_fvarId_1260_);
lean_inc(v_mvarId_1259_);
v___f_1267_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1267_, 0, v_mvarId_1259_);
lean_closure_set(v___f_1267_, 1, v_fuel_1261_);
lean_closure_set(v___f_1267_, 2, v_fvarId_1260_);
v___f_1268_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___lam__1___boxed), 7, 2);
lean_closure_set(v___f_1268_, 0, v_fvarId_1260_);
lean_closure_set(v___f_1268_, 1, v___f_1267_);
v___x_1269_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_1259_, v___f_1268_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive___boxed(lean_object* v_mvarId_1270_, lean_object* v_fvarId_1271_, lean_object* v_fuel_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1270_, v_fvarId_1271_, v_fuel_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
lean_dec(v_a_1276_);
lean_dec_ref(v_a_1275_);
lean_dec(v_a_1274_);
lean_dec_ref(v_a_1273_);
return v_res_1278_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(lean_object* v_e_1279_){
_start:
{
uint8_t v___x_1280_; 
v___x_1280_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v_e_1279_);
return v___x_1280_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq___boxed(lean_object* v_e_1281_){
_start:
{
uint8_t v_res_1282_; lean_object* v_r_1283_; 
v_res_1282_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_isGenDiseq(v_e_1281_);
v_r_1283_ = lean_box(v_res_1282_);
return v_r_1283_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(lean_object* v_e_1284_, lean_object* v_acc_1285_){
_start:
{
if (lean_obj_tag(v_e_1284_) == 7)
{
lean_object* v_binderType_1286_; lean_object* v_body_1287_; uint8_t v___y_1289_; lean_object* v___x_1293_; uint8_t v___x_1294_; 
v_binderType_1286_ = lean_ctor_get(v_e_1284_, 1);
v_body_1287_ = lean_ctor_get(v_e_1284_, 2);
v___x_1293_ = lean_unsigned_to_nat(0u);
v___x_1294_ = lean_expr_has_loose_bvar(v_body_1287_, v___x_1293_);
if (v___x_1294_ == 0)
{
uint8_t v___x_1295_; 
v___x_1295_ = l_Lean_Expr_isEq(v_binderType_1286_);
if (v___x_1295_ == 0)
{
uint8_t v___x_1296_; 
v___x_1296_ = l_Lean_Expr_isHEq(v_binderType_1286_);
v___y_1289_ = v___x_1296_;
goto v___jp_1288_;
}
else
{
v___y_1289_ = v___x_1295_;
goto v___jp_1288_;
}
}
else
{
uint8_t v___x_1297_; 
v___x_1297_ = 0;
v___y_1289_ = v___x_1297_;
goto v___jp_1288_;
}
v___jp_1288_:
{
lean_object* v___x_1290_; lean_object* v___x_1291_; 
v___x_1290_ = lean_box(v___y_1289_);
v___x_1291_ = lean_array_push(v_acc_1285_, v___x_1290_);
v_e_1284_ = v_body_1287_;
v_acc_1285_ = v___x_1291_;
goto _start;
}
}
else
{
return v_acc_1285_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go___boxed(lean_object* v_e_1298_, lean_object* v_acc_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1298_, v_acc_1299_);
lean_dec_ref(v_e_1298_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask(lean_object* v_e_1303_){
_start:
{
lean_object* v___x_1304_; lean_object* v___x_1305_; 
v___x_1304_ = ((lean_object*)(l_Lean_Meta_mkGenDiseqMask___closed__0));
v___x_1305_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_mkGenDiseqMask_go(v_e_1303_, v___x_1304_);
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkGenDiseqMask___boxed(lean_object* v_e_1306_){
_start:
{
lean_object* v_res_1307_; 
v_res_1307_ = l_Lean_Meta_mkGenDiseqMask(v_e_1306_);
lean_dec_ref(v_e_1306_);
return v_res_1307_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(lean_object* v_msg_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v___f_1315_; lean_object* v___x_4344__overap_1316_; lean_object* v___x_1317_; 
v___f_1315_ = ((lean_object*)(l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___closed__0));
v___x_4344__overap_1316_ = lean_panic_fn_borrowed(v___f_1315_, v_msg_1309_);
lean_inc(v___y_1313_);
lean_inc_ref(v___y_1312_);
lean_inc(v___y_1311_);
lean_inc_ref(v___y_1310_);
v___x_1317_ = lean_apply_5(v___x_4344__overap_1316_, v___y_1310_, v___y_1311_, v___y_1312_, v___y_1313_, lean_box(0));
return v___x_1317_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0___boxed(lean_object* v_msg_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_, lean_object* v___y_1323_){
_start:
{
lean_object* v_res_1324_; 
v_res_1324_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v_msg_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
lean_dec(v___y_1322_);
lean_dec_ref(v___y_1321_);
lean_dec(v___y_1320_);
lean_dec_ref(v___y_1319_);
return v_res_1324_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(lean_object* v_e_1325_, lean_object* v___y_1326_){
_start:
{
uint8_t v___x_1328_; 
v___x_1328_ = l_Lean_Expr_hasMVar(v_e_1325_);
if (v___x_1328_ == 0)
{
lean_object* v___x_1329_; 
v___x_1329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1329_, 0, v_e_1325_);
return v___x_1329_;
}
else
{
lean_object* v___x_1330_; lean_object* v_mctx_1331_; lean_object* v___x_1332_; lean_object* v_fst_1333_; lean_object* v_snd_1334_; lean_object* v___x_1335_; lean_object* v_cache_1336_; lean_object* v_zetaDeltaFVarIds_1337_; lean_object* v_postponed_1338_; lean_object* v_diag_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1348_; 
v___x_1330_ = lean_st_ref_get(v___y_1326_);
v_mctx_1331_ = lean_ctor_get(v___x_1330_, 0);
lean_inc_ref(v_mctx_1331_);
lean_dec(v___x_1330_);
v___x_1332_ = l_Lean_instantiateMVarsCore(v_mctx_1331_, v_e_1325_);
v_fst_1333_ = lean_ctor_get(v___x_1332_, 0);
lean_inc(v_fst_1333_);
v_snd_1334_ = lean_ctor_get(v___x_1332_, 1);
lean_inc(v_snd_1334_);
lean_dec_ref(v___x_1332_);
v___x_1335_ = lean_st_ref_take(v___y_1326_);
v_cache_1336_ = lean_ctor_get(v___x_1335_, 1);
v_zetaDeltaFVarIds_1337_ = lean_ctor_get(v___x_1335_, 2);
v_postponed_1338_ = lean_ctor_get(v___x_1335_, 3);
v_diag_1339_ = lean_ctor_get(v___x_1335_, 4);
v_isSharedCheck_1348_ = !lean_is_exclusive(v___x_1335_);
if (v_isSharedCheck_1348_ == 0)
{
lean_object* v_unused_1349_; 
v_unused_1349_ = lean_ctor_get(v___x_1335_, 0);
lean_dec(v_unused_1349_);
v___x_1341_ = v___x_1335_;
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_diag_1339_);
lean_inc(v_postponed_1338_);
lean_inc(v_zetaDeltaFVarIds_1337_);
lean_inc(v_cache_1336_);
lean_dec(v___x_1335_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1344_; 
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 0, v_snd_1334_);
v___x_1344_ = v___x_1341_;
goto v_reusejp_1343_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_snd_1334_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_cache_1336_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_zetaDeltaFVarIds_1337_);
lean_ctor_set(v_reuseFailAlloc_1347_, 3, v_postponed_1338_);
lean_ctor_set(v_reuseFailAlloc_1347_, 4, v_diag_1339_);
v___x_1344_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1343_;
}
v_reusejp_1343_:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = lean_st_ref_put(v___y_1326_, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1346_, 0, v_fst_1333_);
return v___x_1346_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg___boxed(lean_object* v_e_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_){
_start:
{
lean_object* v_res_1353_; 
v_res_1353_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1350_, v___y_1351_);
lean_dec(v___y_1351_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(lean_object* v_e_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_){
_start:
{
lean_object* v___x_1360_; 
v___x_1360_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v_e_1354_, v___y_1356_);
return v___x_1360_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___boxed(lean_object* v_e_1361_, lean_object* v___y_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v_res_1367_; 
v_res_1367_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2(v_e_1361_, v___y_1362_, v___y_1363_, v___y_1364_, v___y_1365_);
lean_dec(v___y_1365_);
lean_dec_ref(v___y_1364_);
lean_dec(v___y_1363_);
lean_dec_ref(v___y_1362_);
return v_res_1367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(lean_object* v_k_1368_, uint8_t v_allowLevelAssignments_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_){
_start:
{
lean_object* v___x_1375_; 
v___x_1375_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1369_, v_k_1368_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
if (lean_obj_tag(v___x_1375_) == 0)
{
lean_object* v_a_1376_; lean_object* v___x_1378_; uint8_t v_isShared_1379_; uint8_t v_isSharedCheck_1383_; 
v_a_1376_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1383_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1383_ == 0)
{
v___x_1378_ = v___x_1375_;
v_isShared_1379_ = v_isSharedCheck_1383_;
goto v_resetjp_1377_;
}
else
{
lean_inc(v_a_1376_);
lean_dec(v___x_1375_);
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
v_reuseFailAlloc_1382_ = lean_alloc_ctor(0, 1, 0);
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
else
{
lean_object* v_a_1384_; lean_object* v___x_1386_; uint8_t v_isShared_1387_; uint8_t v_isSharedCheck_1391_; 
v_a_1384_ = lean_ctor_get(v___x_1375_, 0);
v_isSharedCheck_1391_ = !lean_is_exclusive(v___x_1375_);
if (v_isSharedCheck_1391_ == 0)
{
v___x_1386_ = v___x_1375_;
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
else
{
lean_inc(v_a_1384_);
lean_dec(v___x_1375_);
v___x_1386_ = lean_box(0);
v_isShared_1387_ = v_isSharedCheck_1391_;
goto v_resetjp_1385_;
}
v_resetjp_1385_:
{
lean_object* v___x_1389_; 
if (v_isShared_1387_ == 0)
{
v___x_1389_ = v___x_1386_;
goto v_reusejp_1388_;
}
else
{
lean_object* v_reuseFailAlloc_1390_; 
v_reuseFailAlloc_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1390_, 0, v_a_1384_);
v___x_1389_ = v_reuseFailAlloc_1390_;
goto v_reusejp_1388_;
}
v_reusejp_1388_:
{
return v___x_1389_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg___boxed(lean_object* v_k_1392_, lean_object* v_allowLevelAssignments_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_, lean_object* v___y_1398_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1399_; lean_object* v_res_1400_; 
v_allowLevelAssignments_boxed_1399_ = lean_unbox(v_allowLevelAssignments_1393_);
v_res_1400_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1392_, v_allowLevelAssignments_boxed_1399_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
lean_dec(v___y_1397_);
lean_dec_ref(v___y_1396_);
lean_dec(v___y_1395_);
lean_dec_ref(v___y_1394_);
return v_res_1400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(lean_object* v_00_u03b1_1401_, lean_object* v_k_1402_, uint8_t v_allowLevelAssignments_1403_, lean_object* v___y_1404_, lean_object* v___y_1405_, lean_object* v___y_1406_, lean_object* v___y_1407_){
_start:
{
lean_object* v___x_1409_; 
v___x_1409_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v_k_1402_, v_allowLevelAssignments_1403_, v___y_1404_, v___y_1405_, v___y_1406_, v___y_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___boxed(lean_object* v_00_u03b1_1410_, lean_object* v_k_1411_, lean_object* v_allowLevelAssignments_1412_, lean_object* v___y_1413_, lean_object* v___y_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1418_; lean_object* v_res_1419_; 
v_allowLevelAssignments_boxed_1418_ = lean_unbox(v_allowLevelAssignments_1412_);
v_res_1419_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3(v_00_u03b1_1410_, v_k_1411_, v_allowLevelAssignments_boxed_1418_, v___y_1413_, v___y_1414_, v___y_1415_, v___y_1416_);
lean_dec(v___y_1416_);
lean_dec_ref(v___y_1415_);
lean_dec(v___y_1414_);
lean_dec_ref(v___y_1413_);
return v_res_1419_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(lean_object* v_as_1422_, size_t v_sz_1423_, size_t v_i_1424_, lean_object* v_b_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_, lean_object* v___y_1429_){
_start:
{
lean_object* v_a_1432_; uint8_t v___x_1436_; 
v___x_1436_ = lean_usize_dec_lt(v_i_1424_, v_sz_1423_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
v___x_1437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1437_, 0, v_b_1425_);
return v___x_1437_;
}
else
{
lean_object* v_snd_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1600_; 
v_snd_1438_ = lean_ctor_get(v_b_1425_, 1);
v_isSharedCheck_1600_ = !lean_is_exclusive(v_b_1425_);
if (v_isSharedCheck_1600_ == 0)
{
lean_object* v_unused_1601_; 
v_unused_1601_ = lean_ctor_get(v_b_1425_, 0);
lean_dec(v_unused_1601_);
v___x_1440_ = v_b_1425_;
v_isShared_1441_ = v_isSharedCheck_1600_;
goto v_resetjp_1439_;
}
else
{
lean_inc(v_snd_1438_);
lean_dec(v_b_1425_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1600_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v_array_1442_; lean_object* v_start_1443_; lean_object* v_stop_1444_; lean_object* v___x_1445_; uint8_t v___x_1446_; 
v_array_1442_ = lean_ctor_get(v_snd_1438_, 0);
v_start_1443_ = lean_ctor_get(v_snd_1438_, 1);
v_stop_1444_ = lean_ctor_get(v_snd_1438_, 2);
v___x_1445_ = lean_box(0);
v___x_1446_ = lean_nat_dec_lt(v_start_1443_, v_stop_1444_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1448_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 0, v___x_1445_);
v___x_1448_ = v___x_1440_;
goto v_reusejp_1447_;
}
else
{
lean_object* v_reuseFailAlloc_1450_; 
v_reuseFailAlloc_1450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1450_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1450_, 1, v_snd_1438_);
v___x_1448_ = v_reuseFailAlloc_1450_;
goto v_reusejp_1447_;
}
v_reusejp_1447_:
{
lean_object* v___x_1449_; 
v___x_1449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1449_, 0, v___x_1448_);
return v___x_1449_;
}
}
else
{
lean_object* v___x_1452_; uint8_t v_isShared_1453_; uint8_t v_isSharedCheck_1596_; 
lean_inc(v_stop_1444_);
lean_inc(v_start_1443_);
lean_inc_ref(v_array_1442_);
v_isSharedCheck_1596_ = !lean_is_exclusive(v_snd_1438_);
if (v_isSharedCheck_1596_ == 0)
{
lean_object* v_unused_1597_; lean_object* v_unused_1598_; lean_object* v_unused_1599_; 
v_unused_1597_ = lean_ctor_get(v_snd_1438_, 2);
lean_dec(v_unused_1597_);
v_unused_1598_ = lean_ctor_get(v_snd_1438_, 1);
lean_dec(v_unused_1598_);
v_unused_1599_ = lean_ctor_get(v_snd_1438_, 0);
lean_dec(v_unused_1599_);
v___x_1452_ = v_snd_1438_;
v_isShared_1453_ = v_isSharedCheck_1596_;
goto v_resetjp_1451_;
}
else
{
lean_dec(v_snd_1438_);
v___x_1452_ = lean_box(0);
v_isShared_1453_ = v_isSharedCheck_1596_;
goto v_resetjp_1451_;
}
v_resetjp_1451_:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1458_; 
v___x_1454_ = lean_array_fget(v_array_1442_, v_start_1443_);
v___x_1455_ = lean_unsigned_to_nat(1u);
v___x_1456_ = lean_nat_add(v_start_1443_, v___x_1455_);
lean_dec(v_start_1443_);
if (v_isShared_1453_ == 0)
{
lean_ctor_set(v___x_1452_, 1, v___x_1456_);
v___x_1458_ = v___x_1452_;
goto v_reusejp_1457_;
}
else
{
lean_object* v_reuseFailAlloc_1595_; 
v_reuseFailAlloc_1595_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1595_, 0, v_array_1442_);
lean_ctor_set(v_reuseFailAlloc_1595_, 1, v___x_1456_);
lean_ctor_set(v_reuseFailAlloc_1595_, 2, v_stop_1444_);
v___x_1458_ = v_reuseFailAlloc_1595_;
goto v_reusejp_1457_;
}
v_reusejp_1457_:
{
uint8_t v___x_1459_; 
v___x_1459_ = lean_unbox(v___x_1454_);
lean_dec(v___x_1454_);
if (v___x_1459_ == 0)
{
lean_object* v___x_1461_; 
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 1, v___x_1458_);
lean_ctor_set(v___x_1440_, 0, v___x_1445_);
v___x_1461_ = v___x_1440_;
goto v_reusejp_1460_;
}
else
{
lean_object* v_reuseFailAlloc_1462_; 
v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1462_, 1, v___x_1458_);
v___x_1461_ = v_reuseFailAlloc_1462_;
goto v_reusejp_1460_;
}
v_reusejp_1460_:
{
v_a_1432_ = v___x_1461_;
goto v___jp_1431_;
}
}
else
{
lean_object* v_a_1463_; lean_object* v___y_1465_; lean_object* v___y_1466_; lean_object* v___y_1467_; lean_object* v___y_1468_; lean_object* v___x_1535_; 
v_a_1463_ = lean_array_uget_borrowed(v_as_1422_, v_i_1424_);
lean_inc(v___y_1429_);
lean_inc_ref(v___y_1428_);
lean_inc(v___y_1427_);
lean_inc_ref(v___y_1426_);
lean_inc(v_a_1463_);
v___x_1535_ = lean_infer_type(v_a_1463_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1535_) == 0)
{
lean_object* v_a_1536_; lean_object* v___x_1537_; 
v_a_1536_ = lean_ctor_get(v___x_1535_, 0);
lean_inc(v_a_1536_);
lean_dec_ref_known(v___x_1535_, 1);
v___x_1537_ = l_Lean_Meta_matchEq_x3f(v_a_1536_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_a_1538_; 
v_a_1538_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_a_1538_);
lean_dec_ref_known(v___x_1537_, 1);
if (lean_obj_tag(v_a_1538_) == 1)
{
lean_object* v_val_1539_; lean_object* v_snd_1540_; lean_object* v_fst_1541_; lean_object* v___x_1543_; uint8_t v_isShared_1544_; uint8_t v_isSharedCheck_1577_; 
v_val_1539_ = lean_ctor_get(v_a_1538_, 0);
lean_inc(v_val_1539_);
lean_dec_ref_known(v_a_1538_, 1);
v_snd_1540_ = lean_ctor_get(v_val_1539_, 1);
lean_inc(v_snd_1540_);
lean_dec(v_val_1539_);
v_fst_1541_ = lean_ctor_get(v_snd_1540_, 0);
v_isSharedCheck_1577_ = !lean_is_exclusive(v_snd_1540_);
if (v_isSharedCheck_1577_ == 0)
{
lean_object* v_unused_1578_; 
v_unused_1578_ = lean_ctor_get(v_snd_1540_, 1);
lean_dec(v_unused_1578_);
v___x_1543_ = v_snd_1540_;
v_isShared_1544_ = v_isSharedCheck_1577_;
goto v_resetjp_1542_;
}
else
{
lean_inc(v_fst_1541_);
lean_dec(v_snd_1540_);
v___x_1543_ = lean_box(0);
v_isShared_1544_ = v_isSharedCheck_1577_;
goto v_resetjp_1542_;
}
v_resetjp_1542_:
{
lean_object* v___x_1545_; 
v___x_1545_ = l_Lean_Meta_mkEqRefl(v_fst_1541_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1545_) == 0)
{
lean_object* v_a_1546_; lean_object* v___x_1547_; 
v_a_1546_ = lean_ctor_get(v___x_1545_, 0);
lean_inc(v_a_1546_);
lean_dec_ref_known(v___x_1545_, 1);
lean_inc(v_a_1463_);
v___x_1547_ = l_Lean_Meta_isExprDefEq(v_a_1463_, v_a_1546_, v___y_1426_, v___y_1427_, v___y_1428_, v___y_1429_);
if (lean_obj_tag(v___x_1547_) == 0)
{
lean_object* v_a_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1560_; 
v_a_1548_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1560_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1550_ = v___x_1547_;
v_isShared_1551_ = v_isSharedCheck_1560_;
goto v_resetjp_1549_;
}
else
{
lean_inc(v_a_1548_);
lean_dec(v___x_1547_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1560_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
uint8_t v___x_1552_; 
v___x_1552_ = lean_unbox(v_a_1548_);
lean_dec(v_a_1548_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1555_; 
lean_del_object(v___x_1440_);
v___x_1553_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1544_ == 0)
{
lean_ctor_set(v___x_1543_, 1, v___x_1458_);
lean_ctor_set(v___x_1543_, 0, v___x_1553_);
v___x_1555_ = v___x_1543_;
goto v_reusejp_1554_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v___x_1553_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1458_);
v___x_1555_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1554_;
}
v_reusejp_1554_:
{
lean_object* v___x_1557_; 
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 0, v___x_1555_);
v___x_1557_ = v___x_1550_;
goto v_reusejp_1556_;
}
else
{
lean_object* v_reuseFailAlloc_1558_; 
v_reuseFailAlloc_1558_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1558_, 0, v___x_1555_);
v___x_1557_ = v_reuseFailAlloc_1558_;
goto v_reusejp_1556_;
}
v_reusejp_1556_:
{
return v___x_1557_;
}
}
}
else
{
lean_del_object(v___x_1550_);
lean_del_object(v___x_1543_);
v___y_1465_ = v___y_1426_;
v___y_1466_ = v___y_1427_;
v___y_1467_ = v___y_1428_;
v___y_1468_ = v___y_1429_;
goto v___jp_1464_;
}
}
}
else
{
lean_object* v_a_1561_; lean_object* v___x_1563_; uint8_t v_isShared_1564_; uint8_t v_isSharedCheck_1568_; 
lean_del_object(v___x_1543_);
lean_dec_ref(v___x_1458_);
lean_del_object(v___x_1440_);
v_a_1561_ = lean_ctor_get(v___x_1547_, 0);
v_isSharedCheck_1568_ = !lean_is_exclusive(v___x_1547_);
if (v_isSharedCheck_1568_ == 0)
{
v___x_1563_ = v___x_1547_;
v_isShared_1564_ = v_isSharedCheck_1568_;
goto v_resetjp_1562_;
}
else
{
lean_inc(v_a_1561_);
lean_dec(v___x_1547_);
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
else
{
lean_object* v_a_1569_; lean_object* v___x_1571_; uint8_t v_isShared_1572_; uint8_t v_isSharedCheck_1576_; 
lean_del_object(v___x_1543_);
lean_dec_ref(v___x_1458_);
lean_del_object(v___x_1440_);
v_a_1569_ = lean_ctor_get(v___x_1545_, 0);
v_isSharedCheck_1576_ = !lean_is_exclusive(v___x_1545_);
if (v_isSharedCheck_1576_ == 0)
{
v___x_1571_ = v___x_1545_;
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
else
{
lean_inc(v_a_1569_);
lean_dec(v___x_1545_);
v___x_1571_ = lean_box(0);
v_isShared_1572_ = v_isSharedCheck_1576_;
goto v_resetjp_1570_;
}
v_resetjp_1570_:
{
lean_object* v___x_1574_; 
if (v_isShared_1572_ == 0)
{
v___x_1574_ = v___x_1571_;
goto v_reusejp_1573_;
}
else
{
lean_object* v_reuseFailAlloc_1575_; 
v_reuseFailAlloc_1575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1575_, 0, v_a_1569_);
v___x_1574_ = v_reuseFailAlloc_1575_;
goto v_reusejp_1573_;
}
v_reusejp_1573_:
{
return v___x_1574_;
}
}
}
}
}
else
{
lean_dec(v_a_1538_);
v___y_1465_ = v___y_1426_;
v___y_1466_ = v___y_1427_;
v___y_1467_ = v___y_1428_;
v___y_1468_ = v___y_1429_;
goto v___jp_1464_;
}
}
else
{
lean_object* v_a_1579_; lean_object* v___x_1581_; uint8_t v_isShared_1582_; uint8_t v_isSharedCheck_1586_; 
lean_dec_ref(v___x_1458_);
lean_del_object(v___x_1440_);
v_a_1579_ = lean_ctor_get(v___x_1537_, 0);
v_isSharedCheck_1586_ = !lean_is_exclusive(v___x_1537_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1581_ = v___x_1537_;
v_isShared_1582_ = v_isSharedCheck_1586_;
goto v_resetjp_1580_;
}
else
{
lean_inc(v_a_1579_);
lean_dec(v___x_1537_);
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
}
else
{
lean_object* v_a_1587_; lean_object* v___x_1589_; uint8_t v_isShared_1590_; uint8_t v_isSharedCheck_1594_; 
lean_dec_ref(v___x_1458_);
lean_del_object(v___x_1440_);
v_a_1587_ = lean_ctor_get(v___x_1535_, 0);
v_isSharedCheck_1594_ = !lean_is_exclusive(v___x_1535_);
if (v_isSharedCheck_1594_ == 0)
{
v___x_1589_ = v___x_1535_;
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
else
{
lean_inc(v_a_1587_);
lean_dec(v___x_1535_);
v___x_1589_ = lean_box(0);
v_isShared_1590_ = v_isSharedCheck_1594_;
goto v_resetjp_1588_;
}
v_resetjp_1588_:
{
lean_object* v___x_1592_; 
if (v_isShared_1590_ == 0)
{
v___x_1592_ = v___x_1589_;
goto v_reusejp_1591_;
}
else
{
lean_object* v_reuseFailAlloc_1593_; 
v_reuseFailAlloc_1593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1593_, 0, v_a_1587_);
v___x_1592_ = v_reuseFailAlloc_1593_;
goto v_reusejp_1591_;
}
v_reusejp_1591_:
{
return v___x_1592_;
}
}
}
v___jp_1464_:
{
lean_object* v___x_1469_; 
lean_inc(v___y_1468_);
lean_inc_ref(v___y_1467_);
lean_inc(v___y_1466_);
lean_inc_ref(v___y_1465_);
lean_inc(v_a_1463_);
v___x_1469_ = lean_infer_type(v_a_1463_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1469_) == 0)
{
lean_object* v_a_1470_; lean_object* v___x_1471_; 
v_a_1470_ = lean_ctor_get(v___x_1469_, 0);
lean_inc(v_a_1470_);
lean_dec_ref_known(v___x_1469_, 1);
v___x_1471_ = l_Lean_Meta_matchHEq_x3f(v_a_1470_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1471_) == 0)
{
lean_object* v_a_1472_; 
v_a_1472_ = lean_ctor_get(v___x_1471_, 0);
lean_inc(v_a_1472_);
lean_dec_ref_known(v___x_1471_, 1);
if (lean_obj_tag(v_a_1472_) == 1)
{
lean_object* v_val_1473_; lean_object* v_snd_1474_; lean_object* v_fst_1475_; lean_object* v___x_1477_; uint8_t v_isShared_1478_; uint8_t v_isSharedCheck_1514_; 
lean_del_object(v___x_1440_);
v_val_1473_ = lean_ctor_get(v_a_1472_, 0);
lean_inc(v_val_1473_);
lean_dec_ref_known(v_a_1472_, 1);
v_snd_1474_ = lean_ctor_get(v_val_1473_, 1);
lean_inc(v_snd_1474_);
lean_dec(v_val_1473_);
v_fst_1475_ = lean_ctor_get(v_snd_1474_, 0);
v_isSharedCheck_1514_ = !lean_is_exclusive(v_snd_1474_);
if (v_isSharedCheck_1514_ == 0)
{
lean_object* v_unused_1515_; 
v_unused_1515_ = lean_ctor_get(v_snd_1474_, 1);
lean_dec(v_unused_1515_);
v___x_1477_ = v_snd_1474_;
v_isShared_1478_ = v_isSharedCheck_1514_;
goto v_resetjp_1476_;
}
else
{
lean_inc(v_fst_1475_);
lean_dec(v_snd_1474_);
v___x_1477_ = lean_box(0);
v_isShared_1478_ = v_isSharedCheck_1514_;
goto v_resetjp_1476_;
}
v_resetjp_1476_:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Meta_mkHEqRefl(v_fst_1475_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1481_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
lean_inc(v_a_1480_);
lean_dec_ref_known(v___x_1479_, 1);
lean_inc(v_a_1463_);
v___x_1481_ = l_Lean_Meta_isExprDefEq(v_a_1463_, v_a_1480_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1497_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1497_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1497_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
uint8_t v___x_1486_; 
v___x_1486_ = lean_unbox(v_a_1482_);
lean_dec(v_a_1482_);
if (v___x_1486_ == 0)
{
lean_object* v___x_1487_; lean_object* v___x_1489_; 
v___x_1487_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___closed__0));
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v___x_1458_);
lean_ctor_set(v___x_1477_, 0, v___x_1487_);
v___x_1489_ = v___x_1477_;
goto v_reusejp_1488_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v___x_1487_);
lean_ctor_set(v_reuseFailAlloc_1493_, 1, v___x_1458_);
v___x_1489_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1488_;
}
v_reusejp_1488_:
{
lean_object* v___x_1491_; 
if (v_isShared_1485_ == 0)
{
lean_ctor_set(v___x_1484_, 0, v___x_1489_);
v___x_1491_ = v___x_1484_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v___x_1489_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
else
{
lean_object* v___x_1495_; 
lean_del_object(v___x_1484_);
if (v_isShared_1478_ == 0)
{
lean_ctor_set(v___x_1477_, 1, v___x_1458_);
lean_ctor_set(v___x_1477_, 0, v___x_1445_);
v___x_1495_ = v___x_1477_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1496_, 1, v___x_1458_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
v_a_1432_ = v___x_1495_;
goto v___jp_1431_;
}
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
lean_del_object(v___x_1477_);
lean_dec_ref(v___x_1458_);
v_a_1498_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1481_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1481_);
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
else
{
lean_object* v_a_1506_; lean_object* v___x_1508_; uint8_t v_isShared_1509_; uint8_t v_isSharedCheck_1513_; 
lean_del_object(v___x_1477_);
lean_dec_ref(v___x_1458_);
v_a_1506_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1513_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1513_ == 0)
{
v___x_1508_ = v___x_1479_;
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
else
{
lean_inc(v_a_1506_);
lean_dec(v___x_1479_);
v___x_1508_ = lean_box(0);
v_isShared_1509_ = v_isSharedCheck_1513_;
goto v_resetjp_1507_;
}
v_resetjp_1507_:
{
lean_object* v___x_1511_; 
if (v_isShared_1509_ == 0)
{
v___x_1511_ = v___x_1508_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_a_1506_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
}
else
{
lean_object* v___x_1517_; 
lean_dec(v_a_1472_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 1, v___x_1458_);
lean_ctor_set(v___x_1440_, 0, v___x_1445_);
v___x_1517_ = v___x_1440_;
goto v_reusejp_1516_;
}
else
{
lean_object* v_reuseFailAlloc_1518_; 
v_reuseFailAlloc_1518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1518_, 0, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1518_, 1, v___x_1458_);
v___x_1517_ = v_reuseFailAlloc_1518_;
goto v_reusejp_1516_;
}
v_reusejp_1516_:
{
v_a_1432_ = v___x_1517_;
goto v___jp_1431_;
}
}
}
else
{
lean_object* v_a_1519_; lean_object* v___x_1521_; uint8_t v_isShared_1522_; uint8_t v_isSharedCheck_1526_; 
lean_dec_ref(v___x_1458_);
lean_del_object(v___x_1440_);
v_a_1519_ = lean_ctor_get(v___x_1471_, 0);
v_isSharedCheck_1526_ = !lean_is_exclusive(v___x_1471_);
if (v_isSharedCheck_1526_ == 0)
{
v___x_1521_ = v___x_1471_;
v_isShared_1522_ = v_isSharedCheck_1526_;
goto v_resetjp_1520_;
}
else
{
lean_inc(v_a_1519_);
lean_dec(v___x_1471_);
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
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec_ref(v___x_1458_);
lean_del_object(v___x_1440_);
v_a_1527_ = lean_ctor_get(v___x_1469_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1469_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1469_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1469_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
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
v___jp_1431_:
{
size_t v___x_1433_; size_t v___x_1434_; 
v___x_1433_ = ((size_t)1ULL);
v___x_1434_ = lean_usize_add(v_i_1424_, v___x_1433_);
v_i_1424_ = v___x_1434_;
v_b_1425_ = v_a_1432_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1___boxed(lean_object* v_as_1602_, lean_object* v_sz_1603_, lean_object* v_i_1604_, lean_object* v_b_1605_, lean_object* v___y_1606_, lean_object* v___y_1607_, lean_object* v___y_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_){
_start:
{
size_t v_sz_boxed_1611_; size_t v_i_boxed_1612_; lean_object* v_res_1613_; 
v_sz_boxed_1611_ = lean_unbox_usize(v_sz_1603_);
lean_dec(v_sz_1603_);
v_i_boxed_1612_ = lean_unbox_usize(v_i_1604_);
lean_dec(v_i_1604_);
v_res_1613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_as_1602_, v_sz_boxed_1611_, v_i_boxed_1612_, v_b_1605_, v___y_1606_, v___y_1607_, v___y_1608_, v___y_1609_);
lean_dec(v___y_1609_);
lean_dec_ref(v___y_1608_);
lean_dec(v___y_1607_);
lean_dec_ref(v___y_1606_);
lean_dec_ref(v_as_1602_);
return v_res_1613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(lean_object* v___x_1614_, uint8_t v___x_1615_, lean_object* v_localDecl_1616_, lean_object* v_mvarId_1617_, lean_object* v___y_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_){
_start:
{
lean_object* v___x_1623_; 
lean_inc_ref(v___x_1614_);
v___x_1623_ = l_Lean_Meta_forallMetaTelescope(v___x_1614_, v___x_1615_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1623_) == 0)
{
lean_object* v_a_1624_; lean_object* v_fst_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1714_; 
v_a_1624_ = lean_ctor_get(v___x_1623_, 0);
lean_inc(v_a_1624_);
lean_dec_ref_known(v___x_1623_, 1);
v_fst_1625_ = lean_ctor_get(v_a_1624_, 0);
v_isSharedCheck_1714_ = !lean_is_exclusive(v_a_1624_);
if (v_isSharedCheck_1714_ == 0)
{
lean_object* v_unused_1715_; 
v_unused_1715_ = lean_ctor_get(v_a_1624_, 1);
lean_dec(v_unused_1715_);
v___x_1627_ = v_a_1624_;
v_isShared_1628_ = v_isSharedCheck_1714_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_fst_1625_);
lean_dec(v_a_1624_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1714_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1635_; 
v___x_1629_ = l_Lean_Meta_mkGenDiseqMask(v___x_1614_);
lean_dec_ref(v___x_1614_);
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = lean_array_get_size(v___x_1629_);
v___x_1632_ = l_Array_toSubarray___redArg(v___x_1629_, v___x_1630_, v___x_1631_);
v___x_1633_ = lean_box(0);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v___x_1632_);
lean_ctor_set(v___x_1627_, 0, v___x_1633_);
v___x_1635_ = v___x_1627_;
goto v_reusejp_1634_;
}
else
{
lean_object* v_reuseFailAlloc_1713_; 
v_reuseFailAlloc_1713_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1713_, 0, v___x_1633_);
lean_ctor_set(v_reuseFailAlloc_1713_, 1, v___x_1632_);
v___x_1635_ = v_reuseFailAlloc_1713_;
goto v_reusejp_1634_;
}
v_reusejp_1634_:
{
size_t v_sz_1636_; size_t v___x_1637_; lean_object* v___x_1638_; 
v_sz_1636_ = lean_array_size(v_fst_1625_);
v___x_1637_ = ((size_t)0ULL);
v___x_1638_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__1(v_fst_1625_, v_sz_1636_, v___x_1637_, v___x_1635_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1638_) == 0)
{
lean_object* v_a_1639_; lean_object* v___x_1641_; uint8_t v_isShared_1642_; uint8_t v_isSharedCheck_1704_; 
v_a_1639_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1704_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1704_ == 0)
{
v___x_1641_ = v___x_1638_;
v_isShared_1642_ = v_isSharedCheck_1704_;
goto v_resetjp_1640_;
}
else
{
lean_inc(v_a_1639_);
lean_dec(v___x_1638_);
v___x_1641_ = lean_box(0);
v_isShared_1642_ = v_isSharedCheck_1704_;
goto v_resetjp_1640_;
}
v_resetjp_1640_:
{
lean_object* v_fst_1643_; 
v_fst_1643_ = lean_ctor_get(v_a_1639_, 0);
lean_inc(v_fst_1643_);
lean_dec(v_a_1639_);
if (lean_obj_tag(v_fst_1643_) == 0)
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v_a_1647_; lean_object* v___x_1649_; uint8_t v_isShared_1650_; uint8_t v_isSharedCheck_1699_; 
lean_del_object(v___x_1641_);
v___x_1644_ = l_Lean_LocalDecl_toExpr(v_localDecl_1616_);
v___x_1645_ = l_Lean_mkAppN(v___x_1644_, v_fst_1625_);
lean_dec(v_fst_1625_);
v___x_1646_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1645_, v___y_1619_);
v_a_1647_ = lean_ctor_get(v___x_1646_, 0);
v_isSharedCheck_1699_ = !lean_is_exclusive(v___x_1646_);
if (v_isSharedCheck_1699_ == 0)
{
v___x_1649_ = v___x_1646_;
v_isShared_1650_ = v_isSharedCheck_1699_;
goto v_resetjp_1648_;
}
else
{
lean_inc(v_a_1647_);
lean_dec(v___x_1646_);
v___x_1649_ = lean_box(0);
v_isShared_1650_ = v_isSharedCheck_1699_;
goto v_resetjp_1648_;
}
v_resetjp_1648_:
{
lean_object* v___x_1651_; 
lean_inc(v_a_1647_);
v___x_1651_ = l_Lean_Meta_hasAssignableMVar(v_a_1647_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1651_) == 0)
{
lean_object* v_a_1652_; lean_object* v___x_1654_; uint8_t v_isShared_1655_; uint8_t v_isSharedCheck_1690_; 
v_a_1652_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1690_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1690_ == 0)
{
v___x_1654_ = v___x_1651_;
v_isShared_1655_ = v_isSharedCheck_1690_;
goto v_resetjp_1653_;
}
else
{
lean_inc(v_a_1652_);
lean_dec(v___x_1651_);
v___x_1654_ = lean_box(0);
v_isShared_1655_ = v_isSharedCheck_1690_;
goto v_resetjp_1653_;
}
v_resetjp_1653_:
{
uint8_t v___x_1656_; 
v___x_1656_ = lean_unbox(v_a_1652_);
lean_dec(v_a_1652_);
if (v___x_1656_ == 0)
{
lean_object* v___x_1657_; 
lean_del_object(v___x_1654_);
v___x_1657_ = l_Lean_MVarId_getType(v_mvarId_1617_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1657_) == 0)
{
lean_object* v_a_1658_; lean_object* v___x_1659_; 
v_a_1658_ = lean_ctor_get(v___x_1657_, 0);
lean_inc(v_a_1658_);
lean_dec_ref_known(v___x_1657_, 1);
v___x_1659_ = l_Lean_Meta_mkFalseElim(v_a_1658_, v_a_1647_, v___y_1618_, v___y_1619_, v___y_1620_, v___y_1621_);
if (lean_obj_tag(v___x_1659_) == 0)
{
lean_object* v_a_1660_; lean_object* v___x_1662_; uint8_t v_isShared_1663_; uint8_t v_isSharedCheck_1670_; 
v_a_1660_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1670_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1662_ = v___x_1659_;
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
else
{
lean_inc(v_a_1660_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_box(0);
v_isShared_1663_ = v_isSharedCheck_1670_;
goto v_resetjp_1661_;
}
v_resetjp_1661_:
{
lean_object* v___x_1665_; 
if (v_isShared_1650_ == 0)
{
lean_ctor_set_tag(v___x_1649_, 1);
lean_ctor_set(v___x_1649_, 0, v_a_1660_);
v___x_1665_ = v___x_1649_;
goto v_reusejp_1664_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_a_1660_);
v___x_1665_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1664_;
}
v_reusejp_1664_:
{
lean_object* v___x_1667_; 
if (v_isShared_1663_ == 0)
{
lean_ctor_set(v___x_1662_, 0, v___x_1665_);
v___x_1667_ = v___x_1662_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1665_);
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
lean_object* v_a_1671_; lean_object* v___x_1673_; uint8_t v_isShared_1674_; uint8_t v_isSharedCheck_1678_; 
lean_del_object(v___x_1649_);
v_a_1671_ = lean_ctor_get(v___x_1659_, 0);
v_isSharedCheck_1678_ = !lean_is_exclusive(v___x_1659_);
if (v_isSharedCheck_1678_ == 0)
{
v___x_1673_ = v___x_1659_;
v_isShared_1674_ = v_isSharedCheck_1678_;
goto v_resetjp_1672_;
}
else
{
lean_inc(v_a_1671_);
lean_dec(v___x_1659_);
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
lean_object* v_a_1679_; lean_object* v___x_1681_; uint8_t v_isShared_1682_; uint8_t v_isSharedCheck_1686_; 
lean_del_object(v___x_1649_);
lean_dec(v_a_1647_);
v_a_1679_ = lean_ctor_get(v___x_1657_, 0);
v_isSharedCheck_1686_ = !lean_is_exclusive(v___x_1657_);
if (v_isSharedCheck_1686_ == 0)
{
v___x_1681_ = v___x_1657_;
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
else
{
lean_inc(v_a_1679_);
lean_dec(v___x_1657_);
v___x_1681_ = lean_box(0);
v_isShared_1682_ = v_isSharedCheck_1686_;
goto v_resetjp_1680_;
}
v_resetjp_1680_:
{
lean_object* v___x_1684_; 
if (v_isShared_1682_ == 0)
{
v___x_1684_ = v___x_1681_;
goto v_reusejp_1683_;
}
else
{
lean_object* v_reuseFailAlloc_1685_; 
v_reuseFailAlloc_1685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1685_, 0, v_a_1679_);
v___x_1684_ = v_reuseFailAlloc_1685_;
goto v_reusejp_1683_;
}
v_reusejp_1683_:
{
return v___x_1684_;
}
}
}
}
else
{
lean_object* v___x_1688_; 
lean_del_object(v___x_1649_);
lean_dec(v_a_1647_);
lean_dec(v_mvarId_1617_);
if (v_isShared_1655_ == 0)
{
lean_ctor_set(v___x_1654_, 0, v___x_1633_);
v___x_1688_ = v___x_1654_;
goto v_reusejp_1687_;
}
else
{
lean_object* v_reuseFailAlloc_1689_; 
v_reuseFailAlloc_1689_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1689_, 0, v___x_1633_);
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
else
{
lean_object* v_a_1691_; lean_object* v___x_1693_; uint8_t v_isShared_1694_; uint8_t v_isSharedCheck_1698_; 
lean_del_object(v___x_1649_);
lean_dec(v_a_1647_);
lean_dec(v_mvarId_1617_);
v_a_1691_ = lean_ctor_get(v___x_1651_, 0);
v_isSharedCheck_1698_ = !lean_is_exclusive(v___x_1651_);
if (v_isSharedCheck_1698_ == 0)
{
v___x_1693_ = v___x_1651_;
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
else
{
lean_inc(v_a_1691_);
lean_dec(v___x_1651_);
v___x_1693_ = lean_box(0);
v_isShared_1694_ = v_isSharedCheck_1698_;
goto v_resetjp_1692_;
}
v_resetjp_1692_:
{
lean_object* v___x_1696_; 
if (v_isShared_1694_ == 0)
{
v___x_1696_ = v___x_1693_;
goto v_reusejp_1695_;
}
else
{
lean_object* v_reuseFailAlloc_1697_; 
v_reuseFailAlloc_1697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1697_, 0, v_a_1691_);
v___x_1696_ = v_reuseFailAlloc_1697_;
goto v_reusejp_1695_;
}
v_reusejp_1695_:
{
return v___x_1696_;
}
}
}
}
}
else
{
lean_object* v_val_1700_; lean_object* v___x_1702_; 
lean_dec(v_fst_1625_);
lean_dec(v_mvarId_1617_);
lean_dec_ref(v_localDecl_1616_);
v_val_1700_ = lean_ctor_get(v_fst_1643_, 0);
lean_inc(v_val_1700_);
lean_dec_ref_known(v_fst_1643_, 1);
if (v_isShared_1642_ == 0)
{
lean_ctor_set(v___x_1641_, 0, v_val_1700_);
v___x_1702_ = v___x_1641_;
goto v_reusejp_1701_;
}
else
{
lean_object* v_reuseFailAlloc_1703_; 
v_reuseFailAlloc_1703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1703_, 0, v_val_1700_);
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
else
{
lean_object* v_a_1705_; lean_object* v___x_1707_; uint8_t v_isShared_1708_; uint8_t v_isSharedCheck_1712_; 
lean_dec(v_fst_1625_);
lean_dec(v_mvarId_1617_);
lean_dec_ref(v_localDecl_1616_);
v_a_1705_ = lean_ctor_get(v___x_1638_, 0);
v_isSharedCheck_1712_ = !lean_is_exclusive(v___x_1638_);
if (v_isSharedCheck_1712_ == 0)
{
v___x_1707_ = v___x_1638_;
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
else
{
lean_inc(v_a_1705_);
lean_dec(v___x_1638_);
v___x_1707_ = lean_box(0);
v_isShared_1708_ = v_isSharedCheck_1712_;
goto v_resetjp_1706_;
}
v_resetjp_1706_:
{
lean_object* v___x_1710_; 
if (v_isShared_1708_ == 0)
{
v___x_1710_ = v___x_1707_;
goto v_reusejp_1709_;
}
else
{
lean_object* v_reuseFailAlloc_1711_; 
v_reuseFailAlloc_1711_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1711_, 0, v_a_1705_);
v___x_1710_ = v_reuseFailAlloc_1711_;
goto v_reusejp_1709_;
}
v_reusejp_1709_:
{
return v___x_1710_;
}
}
}
}
}
}
else
{
lean_object* v_a_1716_; lean_object* v___x_1718_; uint8_t v_isShared_1719_; uint8_t v_isSharedCheck_1723_; 
lean_dec(v_mvarId_1617_);
lean_dec_ref(v_localDecl_1616_);
lean_dec_ref(v___x_1614_);
v_a_1716_ = lean_ctor_get(v___x_1623_, 0);
v_isSharedCheck_1723_ = !lean_is_exclusive(v___x_1623_);
if (v_isSharedCheck_1723_ == 0)
{
v___x_1718_ = v___x_1623_;
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
else
{
lean_inc(v_a_1716_);
lean_dec(v___x_1623_);
v___x_1718_ = lean_box(0);
v_isShared_1719_ = v_isSharedCheck_1723_;
goto v_resetjp_1717_;
}
v_resetjp_1717_:
{
lean_object* v___x_1721_; 
if (v_isShared_1719_ == 0)
{
v___x_1721_ = v___x_1718_;
goto v_reusejp_1720_;
}
else
{
lean_object* v_reuseFailAlloc_1722_; 
v_reuseFailAlloc_1722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1722_, 0, v_a_1716_);
v___x_1721_ = v_reuseFailAlloc_1722_;
goto v_reusejp_1720_;
}
v_reusejp_1720_:
{
return v___x_1721_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed(lean_object* v___x_1724_, lean_object* v___x_1725_, lean_object* v_localDecl_1726_, lean_object* v_mvarId_1727_, lean_object* v___y_1728_, lean_object* v___y_1729_, lean_object* v___y_1730_, lean_object* v___y_1731_, lean_object* v___y_1732_){
_start:
{
uint8_t v___x_6078__boxed_1733_; lean_object* v_res_1734_; 
v___x_6078__boxed_1733_ = lean_unbox(v___x_1725_);
v_res_1734_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0(v___x_1724_, v___x_6078__boxed_1733_, v_localDecl_1726_, v_mvarId_1727_, v___y_1728_, v___y_1729_, v___y_1730_, v___y_1731_);
lean_dec(v___y_1731_);
lean_dec_ref(v___y_1730_);
lean_dec(v___y_1729_);
lean_dec_ref(v___y_1728_);
return v_res_1734_;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3(void){
_start:
{
lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; 
v___x_1738_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__2));
v___x_1739_ = lean_unsigned_to_nat(2u);
v___x_1740_ = lean_unsigned_to_nat(120u);
v___x_1741_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__1));
v___x_1742_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__0));
v___x_1743_ = l_mkPanicMessageWithDecl(v___x_1742_, v___x_1741_, v___x_1740_, v___x_1739_, v___x_1738_);
return v___x_1743_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(lean_object* v_mvarId_1744_, lean_object* v_localDecl_1745_, lean_object* v_a_1746_, lean_object* v_a_1747_, lean_object* v_a_1748_, lean_object* v_a_1749_){
_start:
{
lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1751_ = l_Lean_LocalDecl_type(v_localDecl_1745_);
lean_inc_ref(v___x_1751_);
v___x_1752_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec_ref(v___x_1751_);
lean_dec_ref(v_localDecl_1745_);
lean_dec(v_mvarId_1744_);
v___x_1753_ = lean_obj_once(&l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3, &l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3_once, _init_l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___closed__3);
v___x_1754_ = l_panic___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__0(v___x_1753_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
return v___x_1754_;
}
else
{
uint8_t v___x_1755_; lean_object* v___x_1756_; lean_object* v___f_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1755_ = 0;
v___x_1756_ = lean_box(v___x_1755_);
lean_inc(v_mvarId_1744_);
v___f_1757_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___lam__0___boxed), 9, 4);
lean_closure_set(v___f_1757_, 0, v___x_1751_);
lean_closure_set(v___f_1757_, 1, v___x_1756_);
lean_closure_set(v___f_1757_, 2, v_localDecl_1745_);
lean_closure_set(v___f_1757_, 3, v_mvarId_1744_);
v___x_1758_ = 0;
v___x_1759_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__3___redArg(v___f_1757_, v___x_1758_, v_a_1746_, v_a_1747_, v_a_1748_, v_a_1749_);
if (lean_obj_tag(v___x_1759_) == 0)
{
lean_object* v_a_1760_; lean_object* v___x_1762_; uint8_t v_isShared_1763_; uint8_t v_isSharedCheck_1779_; 
v_a_1760_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1779_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1779_ == 0)
{
v___x_1762_ = v___x_1759_;
v_isShared_1763_ = v_isSharedCheck_1779_;
goto v_resetjp_1761_;
}
else
{
lean_inc(v_a_1760_);
lean_dec(v___x_1759_);
v___x_1762_ = lean_box(0);
v_isShared_1763_ = v_isSharedCheck_1779_;
goto v_resetjp_1761_;
}
v_resetjp_1761_:
{
if (lean_obj_tag(v_a_1760_) == 1)
{
lean_object* v_val_1764_; lean_object* v___x_1765_; lean_object* v___x_1767_; uint8_t v_isShared_1768_; uint8_t v_isSharedCheck_1773_; 
lean_del_object(v___x_1762_);
v_val_1764_ = lean_ctor_get(v_a_1760_, 0);
lean_inc(v_val_1764_);
lean_dec_ref_known(v_a_1760_, 1);
v___x_1765_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1744_, v_val_1764_, v_a_1747_);
v_isSharedCheck_1773_ = !lean_is_exclusive(v___x_1765_);
if (v_isSharedCheck_1773_ == 0)
{
lean_object* v_unused_1774_; 
v_unused_1774_ = lean_ctor_get(v___x_1765_, 0);
lean_dec(v_unused_1774_);
v___x_1767_ = v___x_1765_;
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
else
{
lean_dec(v___x_1765_);
v___x_1767_ = lean_box(0);
v_isShared_1768_ = v_isSharedCheck_1773_;
goto v_resetjp_1766_;
}
v_resetjp_1766_:
{
lean_object* v___x_1769_; lean_object* v___x_1771_; 
v___x_1769_ = lean_box(v___x_1752_);
if (v_isShared_1768_ == 0)
{
lean_ctor_set(v___x_1767_, 0, v___x_1769_);
v___x_1771_ = v___x_1767_;
goto v_reusejp_1770_;
}
else
{
lean_object* v_reuseFailAlloc_1772_; 
v_reuseFailAlloc_1772_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1772_, 0, v___x_1769_);
v___x_1771_ = v_reuseFailAlloc_1772_;
goto v_reusejp_1770_;
}
v_reusejp_1770_:
{
return v___x_1771_;
}
}
}
else
{
lean_object* v___x_1775_; lean_object* v___x_1777_; 
lean_dec(v_a_1760_);
lean_dec(v_mvarId_1744_);
v___x_1775_ = lean_box(v___x_1758_);
if (v_isShared_1763_ == 0)
{
lean_ctor_set(v___x_1762_, 0, v___x_1775_);
v___x_1777_ = v___x_1762_;
goto v_reusejp_1776_;
}
else
{
lean_object* v_reuseFailAlloc_1778_; 
v_reuseFailAlloc_1778_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1778_, 0, v___x_1775_);
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
else
{
lean_object* v_a_1780_; lean_object* v___x_1782_; uint8_t v_isShared_1783_; uint8_t v_isSharedCheck_1787_; 
lean_dec(v_mvarId_1744_);
v_a_1780_ = lean_ctor_get(v___x_1759_, 0);
v_isSharedCheck_1787_ = !lean_is_exclusive(v___x_1759_);
if (v_isSharedCheck_1787_ == 0)
{
v___x_1782_ = v___x_1759_;
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
else
{
lean_inc(v_a_1780_);
lean_dec(v___x_1759_);
v___x_1782_ = lean_box(0);
v_isShared_1783_ = v_isSharedCheck_1787_;
goto v_resetjp_1781_;
}
v_resetjp_1781_:
{
lean_object* v___x_1785_; 
if (v_isShared_1783_ == 0)
{
v___x_1785_ = v___x_1782_;
goto v_reusejp_1784_;
}
else
{
lean_object* v_reuseFailAlloc_1786_; 
v_reuseFailAlloc_1786_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
v___x_1785_ = v_reuseFailAlloc_1786_;
goto v_reusejp_1784_;
}
v_reusejp_1784_:
{
return v___x_1785_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq___boxed(lean_object* v_mvarId_1788_, lean_object* v_localDecl_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_){
_start:
{
lean_object* v_res_1795_; 
v_res_1795_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1788_, v_localDecl_1789_, v_a_1790_, v_a_1791_, v_a_1792_, v_a_1793_);
lean_dec(v_a_1793_);
lean_dec_ref(v_a_1792_);
lean_dec(v_a_1791_);
lean_dec_ref(v_a_1790_);
return v_res_1795_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1807_ = lean_box(0);
v___x_1808_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__5));
v___x_1809_ = l_Lean_mkConst(v___x_1808_, v___x_1807_);
return v___x_1809_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7(void){
_start:
{
lean_object* v___x_1810_; lean_object* v_dummy_1811_; 
v___x_1810_ = lean_box(0);
v_dummy_1811_ = l_Lean_Expr_sort___override(v___x_1810_);
return v_dummy_1811_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(lean_object* v_config_1812_, lean_object* v_mvarId_1813_, lean_object* v_as_1814_, size_t v_sz_1815_, size_t v_i_1816_, lean_object* v_b_1817_, lean_object* v___y_1818_, lean_object* v___y_1819_, lean_object* v___y_1820_, lean_object* v___y_1821_){
_start:
{
uint8_t v___x_1823_; 
v___x_1823_ = lean_usize_dec_lt(v_i_1816_, v_sz_1815_);
if (v___x_1823_ == 0)
{
lean_object* v___x_1824_; 
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v___x_1824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1824_, 0, v_b_1817_);
return v___x_1824_;
}
else
{
lean_object* v_snd_1825_; lean_object* v___x_1827_; uint8_t v_isShared_1828_; uint8_t v_isSharedCheck_2475_; 
v_snd_1825_ = lean_ctor_get(v_b_1817_, 1);
v_isSharedCheck_2475_ = !lean_is_exclusive(v_b_1817_);
if (v_isSharedCheck_2475_ == 0)
{
lean_object* v_unused_2476_; 
v_unused_2476_ = lean_ctor_get(v_b_1817_, 0);
lean_dec(v_unused_2476_);
v___x_1827_ = v_b_1817_;
v_isShared_1828_ = v_isSharedCheck_2475_;
goto v_resetjp_1826_;
}
else
{
lean_inc(v_snd_1825_);
lean_dec(v_b_1817_);
v___x_1827_ = lean_box(0);
v_isShared_1828_ = v_isSharedCheck_2475_;
goto v_resetjp_1826_;
}
v_resetjp_1826_:
{
lean_object* v_a_1830_; lean_object* v___x_1836_; lean_object* v_a_1838_; lean_object* v_a_1843_; 
v___x_1836_ = lean_box(0);
v_a_1843_ = lean_array_uget(v_as_1814_, v_i_1816_);
if (lean_obj_tag(v_a_1843_) == 0)
{
lean_del_object(v___x_1827_);
v_a_1838_ = v_snd_1825_;
goto v___jp_1837_;
}
else
{
lean_object* v_val_1844_; lean_object* v___x_1846_; uint8_t v_isShared_1847_; uint8_t v_isSharedCheck_2474_; 
v_val_1844_ = lean_ctor_get(v_a_1843_, 0);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_a_1843_);
if (v_isSharedCheck_2474_ == 0)
{
v___x_1846_ = v_a_1843_;
v_isShared_1847_ = v_isSharedCheck_2474_;
goto v_resetjp_1845_;
}
else
{
lean_inc(v_val_1844_);
lean_dec(v_a_1843_);
v___x_1846_ = lean_box(0);
v_isShared_1847_ = v_isSharedCheck_2474_;
goto v_resetjp_1845_;
}
v_resetjp_1845_:
{
lean_object* v___x_1848_; lean_object* v___y_1850_; lean_object* v___y_1851_; lean_object* v___y_1852_; lean_object* v___y_1853_; lean_object* v___x_1889_; lean_object* v___y_1891_; lean_object* v___y_1892_; lean_object* v___y_1893_; lean_object* v___y_1894_; lean_object* v___y_1912_; lean_object* v___y_1913_; lean_object* v___y_1914_; lean_object* v___y_1915_; uint8_t v___y_1916_; uint8_t v___x_1917_; uint8_t v___y_1919_; lean_object* v___y_1920_; lean_object* v___y_1921_; lean_object* v___y_1922_; lean_object* v___y_1923_; uint8_t v___y_1925_; lean_object* v___y_1926_; lean_object* v___y_1927_; lean_object* v___y_1928_; lean_object* v___y_1929_; uint8_t v___y_1930_; uint8_t v___y_1932_; uint8_t v___y_1933_; lean_object* v___y_1934_; lean_object* v___y_1935_; lean_object* v___y_1936_; lean_object* v___y_1937_; lean_object* v___y_1940_; uint8_t v___y_1941_; lean_object* v___y_1942_; lean_object* v___y_1943_; lean_object* v___y_1944_; uint8_t v___y_1945_; uint8_t v___y_1946_; 
v___x_1848_ = lean_box(0);
v___x_1889_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_1917_ = l_Lean_LocalDecl_isImplementationDetail(v_val_1844_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1961_; uint8_t v___y_1963_; uint8_t v___y_1964_; lean_object* v___y_1965_; lean_object* v___y_1966_; lean_object* v___y_1967_; lean_object* v___y_1968_; uint8_t v___y_1972_; lean_object* v___y_1973_; lean_object* v___y_1974_; lean_object* v___y_1975_; uint8_t v___y_1976_; lean_object* v___y_1977_; lean_object* v___y_1978_; uint8_t v___y_1979_; uint8_t v___y_1982_; lean_object* v___y_1983_; lean_object* v___y_1984_; uint8_t v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v_a_1988_; uint8_t v___y_1992_; lean_object* v___y_1993_; lean_object* v___y_1994_; uint8_t v___y_1995_; lean_object* v___y_1996_; lean_object* v___y_1997_; lean_object* v___y_1998_; lean_object* v___y_1999_; uint8_t v___y_2036_; lean_object* v___y_2037_; lean_object* v___y_2038_; uint8_t v___y_2039_; lean_object* v___y_2040_; lean_object* v___y_2041_; uint8_t v___y_2065_; lean_object* v___y_2066_; lean_object* v___y_2067_; uint8_t v___y_2068_; lean_object* v___y_2069_; lean_object* v___y_2070_; uint8_t v___y_2071_; lean_object* v___y_2073_; uint8_t v___y_2074_; lean_object* v___y_2075_; lean_object* v___y_2076_; uint8_t v___y_2077_; lean_object* v___y_2078_; lean_object* v___y_2079_; uint8_t v___y_2080_; uint8_t v___y_2083_; lean_object* v___y_2084_; lean_object* v___y_2085_; uint8_t v___y_2086_; lean_object* v___y_2087_; lean_object* v___y_2088_; uint8_t v___y_2089_; uint8_t v___y_2102_; lean_object* v___y_2103_; lean_object* v___y_2104_; uint8_t v___y_2105_; lean_object* v___y_2106_; lean_object* v___y_2107_; uint8_t v___y_2108_; uint8_t v___y_2110_; uint8_t v_isHEq_2111_; lean_object* v___y_2112_; lean_object* v___y_2113_; lean_object* v___y_2114_; lean_object* v___y_2115_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; lean_object* v___y_2123_; uint8_t v___y_2124_; lean_object* v___y_2125_; uint8_t v_isEq_2181_; lean_object* v___y_2182_; lean_object* v___y_2183_; lean_object* v___y_2184_; lean_object* v___y_2185_; lean_object* v___y_2231_; lean_object* v___y_2232_; lean_object* v___y_2233_; lean_object* v___y_2234_; lean_object* v___y_2277_; lean_object* v___y_2278_; lean_object* v___y_2279_; lean_object* v___y_2280_; lean_object* v___x_2411_; 
v___x_1961_ = l_Lean_LocalDecl_type(v_val_1844_);
lean_inc_ref(v___x_1961_);
v___x_2411_ = l_Lean_Meta_matchNot_x3f(v___x_1961_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v_a_2412_; 
v_a_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc(v_a_2412_);
lean_dec_ref_known(v___x_2411_, 1);
if (lean_obj_tag(v_a_2412_) == 1)
{
lean_object* v_val_2413_; lean_object* v___x_2414_; 
v_val_2413_ = lean_ctor_get(v_a_2412_, 0);
lean_inc(v_val_2413_);
lean_dec_ref_known(v_a_2412_, 1);
v___x_2414_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_2413_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2414_) == 0)
{
lean_object* v_a_2415_; 
v_a_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc(v_a_2415_);
lean_dec_ref_known(v___x_2414_, 1);
if (lean_obj_tag(v_a_2415_) == 1)
{
lean_object* v_val_2416_; lean_object* v___x_2418_; uint8_t v_isShared_2419_; uint8_t v_isSharedCheck_2457_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec_ref(v_config_1812_);
v_val_2416_ = lean_ctor_get(v_a_2415_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v_a_2415_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2418_ = v_a_2415_;
v_isShared_2419_ = v_isSharedCheck_2457_;
goto v_resetjp_2417_;
}
else
{
lean_inc(v_val_2416_);
lean_dec(v_a_2415_);
v___x_2418_ = lean_box(0);
v_isShared_2419_ = v_isSharedCheck_2457_;
goto v_resetjp_2417_;
}
v_resetjp_2417_:
{
lean_object* v___x_2420_; 
lean_inc(v_mvarId_1813_);
v___x_2420_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2420_) == 0)
{
lean_object* v_a_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
lean_inc(v_a_2421_);
lean_dec_ref_known(v___x_2420_, 1);
v___x_2422_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_2423_ = l_Lean_mkFVar(v_val_2416_);
v___x_2424_ = l_Lean_Expr_app___override(v___x_2422_, v___x_2423_);
v___x_2425_ = l_Lean_Meta_mkFalseElim(v_a_2421_, v___x_2424_, v___y_1818_, v___y_1819_, v___y_1820_, v___y_1821_);
if (lean_obj_tag(v___x_2425_) == 0)
{
lean_object* v_a_2426_; lean_object* v___x_2427_; 
v_a_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_a_2426_);
lean_dec_ref_known(v___x_2425_, 1);
v___x_2427_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_2426_, v___y_1819_);
if (lean_obj_tag(v___x_2427_) == 0)
{
lean_object* v___x_2428_; lean_object* v___x_2430_; 
lean_dec_ref_known(v___x_2427_, 1);
v___x_2428_ = lean_box(v___x_1823_);
if (v_isShared_2419_ == 0)
{
lean_ctor_set(v___x_2418_, 0, v___x_2428_);
v___x_2430_ = v___x_2418_;
goto v_reusejp_2429_;
}
else
{
lean_object* v_reuseFailAlloc_2432_; 
v_reuseFailAlloc_2432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2428_);
v___x_2430_ = v_reuseFailAlloc_2432_;
goto v_reusejp_2429_;
}
v_reusejp_2429_:
{
lean_object* v___x_2431_; 
v___x_2431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2431_, 0, v___x_2430_);
lean_ctor_set(v___x_2431_, 1, v___x_1848_);
v_a_1830_ = v___x_2431_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_2433_; lean_object* v___x_2435_; uint8_t v_isShared_2436_; uint8_t v_isSharedCheck_2440_; 
lean_del_object(v___x_2418_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_2433_ = lean_ctor_get(v___x_2427_, 0);
v_isSharedCheck_2440_ = !lean_is_exclusive(v___x_2427_);
if (v_isSharedCheck_2440_ == 0)
{
v___x_2435_ = v___x_2427_;
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
else
{
lean_inc(v_a_2433_);
lean_dec(v___x_2427_);
v___x_2435_ = lean_box(0);
v_isShared_2436_ = v_isSharedCheck_2440_;
goto v_resetjp_2434_;
}
v_resetjp_2434_:
{
lean_object* v___x_2438_; 
if (v_isShared_2436_ == 0)
{
v___x_2438_ = v___x_2435_;
goto v_reusejp_2437_;
}
else
{
lean_object* v_reuseFailAlloc_2439_; 
v_reuseFailAlloc_2439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2439_, 0, v_a_2433_);
v___x_2438_ = v_reuseFailAlloc_2439_;
goto v_reusejp_2437_;
}
v_reusejp_2437_:
{
return v___x_2438_;
}
}
}
}
else
{
lean_object* v_a_2441_; lean_object* v___x_2443_; uint8_t v_isShared_2444_; uint8_t v_isSharedCheck_2448_; 
lean_del_object(v___x_2418_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2441_ = lean_ctor_get(v___x_2425_, 0);
v_isSharedCheck_2448_ = !lean_is_exclusive(v___x_2425_);
if (v_isSharedCheck_2448_ == 0)
{
v___x_2443_ = v___x_2425_;
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
else
{
lean_inc(v_a_2441_);
lean_dec(v___x_2425_);
v___x_2443_ = lean_box(0);
v_isShared_2444_ = v_isSharedCheck_2448_;
goto v_resetjp_2442_;
}
v_resetjp_2442_:
{
lean_object* v___x_2446_; 
if (v_isShared_2444_ == 0)
{
v___x_2446_ = v___x_2443_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v_a_2441_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
}
}
else
{
lean_object* v_a_2449_; lean_object* v___x_2451_; uint8_t v_isShared_2452_; uint8_t v_isSharedCheck_2456_; 
lean_del_object(v___x_2418_);
lean_dec(v_val_2416_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2449_ = lean_ctor_get(v___x_2420_, 0);
v_isSharedCheck_2456_ = !lean_is_exclusive(v___x_2420_);
if (v_isSharedCheck_2456_ == 0)
{
v___x_2451_ = v___x_2420_;
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
else
{
lean_inc(v_a_2449_);
lean_dec(v___x_2420_);
v___x_2451_ = lean_box(0);
v_isShared_2452_ = v_isSharedCheck_2456_;
goto v_resetjp_2450_;
}
v_resetjp_2450_:
{
lean_object* v___x_2454_; 
if (v_isShared_2452_ == 0)
{
v___x_2454_ = v___x_2451_;
goto v_reusejp_2453_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_a_2449_);
v___x_2454_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2453_;
}
v_reusejp_2453_:
{
return v___x_2454_;
}
}
}
}
}
else
{
lean_dec(v_a_2415_);
v___y_2277_ = v___y_1818_;
v___y_2278_ = v___y_1819_;
v___y_2279_ = v___y_1820_;
v___y_2280_ = v___y_1821_;
goto v___jp_2276_;
}
}
else
{
lean_object* v_a_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2465_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2458_ = lean_ctor_get(v___x_2414_, 0);
v_isSharedCheck_2465_ = !lean_is_exclusive(v___x_2414_);
if (v_isSharedCheck_2465_ == 0)
{
v___x_2460_ = v___x_2414_;
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_a_2458_);
lean_dec(v___x_2414_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2465_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v___x_2463_; 
if (v_isShared_2461_ == 0)
{
v___x_2463_ = v___x_2460_;
goto v_reusejp_2462_;
}
else
{
lean_object* v_reuseFailAlloc_2464_; 
v_reuseFailAlloc_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2464_, 0, v_a_2458_);
v___x_2463_ = v_reuseFailAlloc_2464_;
goto v_reusejp_2462_;
}
v_reusejp_2462_:
{
return v___x_2463_;
}
}
}
}
else
{
lean_dec(v_a_2412_);
v___y_2277_ = v___y_1818_;
v___y_2278_ = v___y_1819_;
v___y_2279_ = v___y_1820_;
v___y_2280_ = v___y_1821_;
goto v___jp_2276_;
}
}
else
{
lean_object* v_a_2466_; lean_object* v___x_2468_; uint8_t v_isShared_2469_; uint8_t v_isSharedCheck_2473_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2466_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2473_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2473_ == 0)
{
v___x_2468_ = v___x_2411_;
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
else
{
lean_inc(v_a_2466_);
lean_dec(v___x_2411_);
v___x_2468_ = lean_box(0);
v_isShared_2469_ = v_isSharedCheck_2473_;
goto v_resetjp_2467_;
}
v_resetjp_2467_:
{
lean_object* v___x_2471_; 
if (v_isShared_2469_ == 0)
{
v___x_2471_ = v___x_2468_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v_a_2466_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
v___jp_1962_:
{
uint8_t v_genDiseq_1969_; 
v_genDiseq_1969_ = lean_ctor_get_uint8(v_config_1812_, sizeof(void*)*1 + 2);
if (v_genDiseq_1969_ == 0)
{
lean_dec_ref(v___x_1961_);
v___y_1940_ = v___y_1968_;
v___y_1941_ = v___y_1963_;
v___y_1942_ = v___y_1967_;
v___y_1943_ = v___y_1966_;
v___y_1944_ = v___y_1965_;
v___y_1945_ = v___y_1964_;
v___y_1946_ = v___x_1917_;
goto v___jp_1939_;
}
else
{
uint8_t v___x_1970_; 
v___x_1970_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_1961_);
v___y_1940_ = v___y_1968_;
v___y_1941_ = v___y_1963_;
v___y_1942_ = v___y_1967_;
v___y_1943_ = v___y_1966_;
v___y_1944_ = v___y_1965_;
v___y_1945_ = v___y_1964_;
v___y_1946_ = v___x_1970_;
goto v___jp_1939_;
}
}
v___jp_1971_:
{
if (v___y_1979_ == 0)
{
lean_dec_ref(v___y_1974_);
v___y_1963_ = v___y_1972_;
v___y_1964_ = v___y_1976_;
v___y_1965_ = v___y_1978_;
v___y_1966_ = v___y_1977_;
v___y_1967_ = v___y_1975_;
v___y_1968_ = v___y_1973_;
goto v___jp_1962_;
}
else
{
lean_object* v___x_1980_; 
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v___x_1980_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1980_, 0, v___y_1974_);
return v___x_1980_;
}
}
v___jp_1981_:
{
uint8_t v___x_1989_; 
v___x_1989_ = l_Lean_Exception_isInterrupt(v_a_1988_);
if (v___x_1989_ == 0)
{
uint8_t v___x_1990_; 
lean_inc_ref(v_a_1988_);
v___x_1990_ = l_Lean_Exception_isRuntime(v_a_1988_);
v___y_1972_ = v___y_1982_;
v___y_1973_ = v___y_1983_;
v___y_1974_ = v_a_1988_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1985_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1986_;
v___y_1979_ = v___x_1990_;
goto v___jp_1971_;
}
else
{
v___y_1972_ = v___y_1982_;
v___y_1973_ = v___y_1983_;
v___y_1974_ = v_a_1988_;
v___y_1975_ = v___y_1984_;
v___y_1976_ = v___y_1985_;
v___y_1977_ = v___y_1987_;
v___y_1978_ = v___y_1986_;
v___y_1979_ = v___x_1989_;
goto v___jp_1971_;
}
}
v___jp_1991_:
{
if (lean_obj_tag(v___y_1999_) == 0)
{
lean_object* v_a_2000_; lean_object* v___x_2001_; uint8_t v___x_2002_; 
v_a_2000_ = lean_ctor_get(v___y_1999_, 0);
lean_inc(v_a_2000_);
lean_dec_ref_known(v___y_1999_, 1);
v___x_2001_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2002_ = l_Lean_Expr_isConstOf(v_a_2000_, v___x_2001_);
lean_dec(v_a_2000_);
if (v___x_2002_ == 0)
{
lean_dec_ref(v___y_1996_);
v___y_1963_ = v___y_1992_;
v___y_1964_ = v___y_1995_;
v___y_1965_ = v___y_1998_;
v___y_1966_ = v___y_1997_;
v___y_1967_ = v___y_1994_;
v___y_1968_ = v___y_1993_;
goto v___jp_1962_;
}
else
{
lean_object* v___x_2003_; 
lean_inc_ref(v___y_1996_);
v___x_2003_ = l_Lean_Meta_mkEqRefl(v___y_1996_, v___y_1998_, v___y_1997_, v___y_1994_, v___y_1993_);
if (lean_obj_tag(v___x_2003_) == 0)
{
lean_object* v_a_2004_; lean_object* v___x_2005_; lean_object* v_dummy_2006_; lean_object* v_nargs_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; 
v_a_2004_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2004_);
lean_dec_ref_known(v___x_2003_, 1);
v___x_2005_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2006_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2007_ = l_Lean_Expr_getAppNumArgs(v___y_1996_);
lean_inc(v_nargs_2007_);
v___x_2008_ = lean_mk_array(v_nargs_2007_, v_dummy_2006_);
v___x_2009_ = lean_unsigned_to_nat(1u);
v___x_2010_ = lean_nat_sub(v_nargs_2007_, v___x_2009_);
lean_dec(v_nargs_2007_);
v___x_2011_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_1996_, v___x_2008_, v___x_2010_);
v___x_2012_ = lean_array_push(v___x_2011_, v_a_2004_);
v___x_2013_ = l_Lean_mkAppN(v___x_2005_, v___x_2012_);
lean_dec_ref(v___x_2012_);
lean_inc(v_mvarId_1813_);
v___x_2014_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_1998_, v___y_1997_, v___y_1994_, v___y_1993_);
if (lean_obj_tag(v___x_2014_) == 0)
{
lean_object* v_a_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; 
v_a_2015_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2015_);
lean_dec_ref_known(v___x_2014_, 1);
lean_inc(v_val_1844_);
v___x_2016_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_2017_ = l_Lean_Meta_mkAbsurd(v_a_2015_, v___x_2016_, v___x_2013_, v___y_1998_, v___y_1997_, v___y_1994_, v___y_1993_);
if (lean_obj_tag(v___x_2017_) == 0)
{
lean_object* v_a_2018_; lean_object* v___x_2019_; 
v_a_2018_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2018_);
lean_dec_ref_known(v___x_2017_, 1);
lean_inc(v_mvarId_1813_);
v___x_2019_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_2018_, v___y_1997_);
if (lean_obj_tag(v___x_2019_) == 0)
{
lean_object* v___x_2021_; uint8_t v_isShared_2022_; uint8_t v_isSharedCheck_2028_; 
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_isSharedCheck_2028_ = !lean_is_exclusive(v___x_2019_);
if (v_isSharedCheck_2028_ == 0)
{
lean_object* v_unused_2029_; 
v_unused_2029_ = lean_ctor_get(v___x_2019_, 0);
lean_dec(v_unused_2029_);
v___x_2021_ = v___x_2019_;
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
else
{
lean_dec(v___x_2019_);
v___x_2021_ = lean_box(0);
v_isShared_2022_ = v_isSharedCheck_2028_;
goto v_resetjp_2020_;
}
v_resetjp_2020_:
{
lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2023_ = lean_box(v___x_1823_);
if (v_isShared_2022_ == 0)
{
lean_ctor_set_tag(v___x_2021_, 1);
lean_ctor_set(v___x_2021_, 0, v___x_2023_);
v___x_2025_ = v___x_2021_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2026_, 0, v___x_2025_);
lean_ctor_set(v___x_2026_, 1, v___x_1848_);
v_a_1830_ = v___x_2026_;
goto v___jp_1829_;
}
}
}
else
{
lean_object* v_a_2030_; 
v_a_2030_ = lean_ctor_get(v___x_2019_, 0);
lean_inc(v_a_2030_);
lean_dec_ref_known(v___x_2019_, 1);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1998_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2030_;
goto v___jp_1981_;
}
}
else
{
lean_object* v_a_2031_; 
v_a_2031_ = lean_ctor_get(v___x_2017_, 0);
lean_inc(v_a_2031_);
lean_dec_ref_known(v___x_2017_, 1);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1998_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2031_;
goto v___jp_1981_;
}
}
else
{
lean_object* v_a_2032_; 
lean_dec_ref(v___x_2013_);
v_a_2032_ = lean_ctor_get(v___x_2014_, 0);
lean_inc(v_a_2032_);
lean_dec_ref_known(v___x_2014_, 1);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1998_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2032_;
goto v___jp_1981_;
}
}
else
{
lean_object* v_a_2033_; 
lean_dec_ref(v___y_1996_);
v_a_2033_ = lean_ctor_get(v___x_2003_, 0);
lean_inc(v_a_2033_);
lean_dec_ref_known(v___x_2003_, 1);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1998_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2033_;
goto v___jp_1981_;
}
}
}
else
{
lean_object* v_a_2034_; 
lean_dec_ref(v___y_1996_);
v_a_2034_ = lean_ctor_get(v___y_1999_, 0);
lean_inc(v_a_2034_);
lean_dec_ref_known(v___y_1999_, 1);
v___y_1982_ = v___y_1992_;
v___y_1983_ = v___y_1993_;
v___y_1984_ = v___y_1994_;
v___y_1985_ = v___y_1995_;
v___y_1986_ = v___y_1998_;
v___y_1987_ = v___y_1997_;
v_a_1988_ = v_a_2034_;
goto v___jp_1981_;
}
}
v___jp_2035_:
{
lean_object* v___x_2042_; 
lean_inc_ref(v___x_1961_);
v___x_2042_ = l_Lean_Meta_mkDecide(v___x_1961_, v___y_2041_, v___y_2040_, v___y_2038_, v___y_2037_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_object* v_a_2043_; lean_object* v___x_2044_; uint8_t v_transparency_2045_; uint8_t v___x_2046_; uint8_t v___x_2047_; 
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2043_);
lean_dec_ref_known(v___x_2042_, 1);
v___x_2044_ = l_Lean_Meta_Context_config(v___y_2041_);
v_transparency_2045_ = lean_ctor_get_uint8(v___x_2044_, 9);
lean_dec_ref(v___x_2044_);
v___x_2046_ = 1;
v___x_2047_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2045_, v___x_2046_);
if (v___x_2047_ == 0)
{
lean_object* v_keyedConfig_2048_; uint8_t v_trackZetaDelta_2049_; lean_object* v_zetaDeltaSet_2050_; lean_object* v_lctx_2051_; lean_object* v_localInstances_2052_; lean_object* v_defEqCtx_x3f_2053_; lean_object* v_synthPendingDepth_2054_; lean_object* v_customCanUnfoldPredicate_x3f_2055_; uint8_t v_univApprox_2056_; uint8_t v_inTypeClassResolution_2057_; uint8_t v_cacheInferType_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v_keyedConfig_2048_ = lean_ctor_get(v___y_2041_, 0);
v_trackZetaDelta_2049_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*7);
v_zetaDeltaSet_2050_ = lean_ctor_get(v___y_2041_, 1);
v_lctx_2051_ = lean_ctor_get(v___y_2041_, 2);
v_localInstances_2052_ = lean_ctor_get(v___y_2041_, 3);
v_defEqCtx_x3f_2053_ = lean_ctor_get(v___y_2041_, 4);
v_synthPendingDepth_2054_ = lean_ctor_get(v___y_2041_, 5);
v_customCanUnfoldPredicate_x3f_2055_ = lean_ctor_get(v___y_2041_, 6);
v_univApprox_2056_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2057_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*7 + 2);
v_cacheInferType_2058_ = lean_ctor_get_uint8(v___y_2041_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2048_);
v___x_2059_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2046_, v_keyedConfig_2048_);
lean_inc(v_customCanUnfoldPredicate_x3f_2055_);
lean_inc(v_synthPendingDepth_2054_);
lean_inc(v_defEqCtx_x3f_2053_);
lean_inc_ref(v_localInstances_2052_);
lean_inc_ref(v_lctx_2051_);
lean_inc(v_zetaDeltaSet_2050_);
v___x_2060_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2060_, 0, v___x_2059_);
lean_ctor_set(v___x_2060_, 1, v_zetaDeltaSet_2050_);
lean_ctor_set(v___x_2060_, 2, v_lctx_2051_);
lean_ctor_set(v___x_2060_, 3, v_localInstances_2052_);
lean_ctor_set(v___x_2060_, 4, v_defEqCtx_x3f_2053_);
lean_ctor_set(v___x_2060_, 5, v_synthPendingDepth_2054_);
lean_ctor_set(v___x_2060_, 6, v_customCanUnfoldPredicate_x3f_2055_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*7, v_trackZetaDelta_2049_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*7 + 1, v_univApprox_2056_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2057_);
lean_ctor_set_uint8(v___x_2060_, sizeof(void*)*7 + 3, v_cacheInferType_2058_);
lean_inc(v___y_2037_);
lean_inc_ref(v___y_2038_);
lean_inc(v___y_2040_);
lean_inc(v_a_2043_);
v___x_2061_ = lean_whnf(v_a_2043_, v___x_2060_, v___y_2040_, v___y_2038_, v___y_2037_);
v___y_1992_ = v___y_2036_;
v___y_1993_ = v___y_2037_;
v___y_1994_ = v___y_2038_;
v___y_1995_ = v___y_2039_;
v___y_1996_ = v_a_2043_;
v___y_1997_ = v___y_2040_;
v___y_1998_ = v___y_2041_;
v___y_1999_ = v___x_2061_;
goto v___jp_1991_;
}
else
{
lean_object* v___x_2062_; 
lean_inc(v___y_2037_);
lean_inc_ref(v___y_2038_);
lean_inc(v___y_2040_);
lean_inc_ref(v___y_2041_);
lean_inc(v_a_2043_);
v___x_2062_ = lean_whnf(v_a_2043_, v___y_2041_, v___y_2040_, v___y_2038_, v___y_2037_);
v___y_1992_ = v___y_2036_;
v___y_1993_ = v___y_2037_;
v___y_1994_ = v___y_2038_;
v___y_1995_ = v___y_2039_;
v___y_1996_ = v_a_2043_;
v___y_1997_ = v___y_2040_;
v___y_1998_ = v___y_2041_;
v___y_1999_ = v___x_2062_;
goto v___jp_1991_;
}
}
else
{
lean_object* v_a_2063_; 
v_a_2063_ = lean_ctor_get(v___x_2042_, 0);
lean_inc(v_a_2063_);
lean_dec_ref_known(v___x_2042_, 1);
v___y_1982_ = v___y_2036_;
v___y_1983_ = v___y_2037_;
v___y_1984_ = v___y_2038_;
v___y_1985_ = v___y_2039_;
v___y_1986_ = v___y_2041_;
v___y_1987_ = v___y_2040_;
v_a_1988_ = v_a_2063_;
goto v___jp_1981_;
}
}
v___jp_2064_:
{
if (v___y_2071_ == 0)
{
v___y_1963_ = v___y_2065_;
v___y_1964_ = v___y_2068_;
v___y_1965_ = v___y_2070_;
v___y_1966_ = v___y_2069_;
v___y_1967_ = v___y_2067_;
v___y_1968_ = v___y_2066_;
goto v___jp_1962_;
}
else
{
v___y_2036_ = v___y_2065_;
v___y_2037_ = v___y_2066_;
v___y_2038_ = v___y_2067_;
v___y_2039_ = v___y_2068_;
v___y_2040_ = v___y_2069_;
v___y_2041_ = v___y_2070_;
goto v___jp_2035_;
}
}
v___jp_2072_:
{
if (v___y_2080_ == 0)
{
lean_dec_ref(v___y_2073_);
v___y_2065_ = v___y_2074_;
v___y_2066_ = v___y_2075_;
v___y_2067_ = v___y_2076_;
v___y_2068_ = v___y_2077_;
v___y_2069_ = v___y_2079_;
v___y_2070_ = v___y_2078_;
v___y_2071_ = v___x_1917_;
goto v___jp_2064_;
}
else
{
uint8_t v___x_2081_; 
v___x_2081_ = l_Lean_Expr_hasFVar(v___y_2073_);
lean_dec_ref(v___y_2073_);
if (v___x_2081_ == 0)
{
v___y_2036_ = v___y_2074_;
v___y_2037_ = v___y_2075_;
v___y_2038_ = v___y_2076_;
v___y_2039_ = v___y_2077_;
v___y_2040_ = v___y_2079_;
v___y_2041_ = v___y_2078_;
goto v___jp_2035_;
}
else
{
v___y_2065_ = v___y_2074_;
v___y_2066_ = v___y_2075_;
v___y_2067_ = v___y_2076_;
v___y_2068_ = v___y_2077_;
v___y_2069_ = v___y_2079_;
v___y_2070_ = v___y_2078_;
v___y_2071_ = v___x_1917_;
goto v___jp_2064_;
}
}
}
v___jp_2082_:
{
lean_object* v___x_2090_; 
lean_inc_ref(v___x_1961_);
v___x_2090_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_1961_, v___y_2088_);
if (lean_obj_tag(v___x_2090_) == 0)
{
lean_object* v_a_2091_; uint8_t v___x_2092_; 
v_a_2091_ = lean_ctor_get(v___x_2090_, 0);
lean_inc(v_a_2091_);
lean_dec_ref_known(v___x_2090_, 1);
v___x_2092_ = l_Lean_Expr_hasMVar(v_a_2091_);
if (v___x_2092_ == 0)
{
v___y_2073_ = v_a_2091_;
v___y_2074_ = v___y_2083_;
v___y_2075_ = v___y_2084_;
v___y_2076_ = v___y_2085_;
v___y_2077_ = v___y_2086_;
v___y_2078_ = v___y_2087_;
v___y_2079_ = v___y_2088_;
v___y_2080_ = v___y_2089_;
goto v___jp_2072_;
}
else
{
v___y_2073_ = v_a_2091_;
v___y_2074_ = v___y_2083_;
v___y_2075_ = v___y_2084_;
v___y_2076_ = v___y_2085_;
v___y_2077_ = v___y_2086_;
v___y_2078_ = v___y_2087_;
v___y_2079_ = v___y_2088_;
v___y_2080_ = v___x_1917_;
goto v___jp_2072_;
}
}
else
{
lean_object* v_a_2093_; lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2093_ = lean_ctor_get(v___x_2090_, 0);
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2090_);
if (v_isSharedCheck_2100_ == 0)
{
v___x_2095_ = v___x_2090_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_inc(v_a_2093_);
lean_dec(v___x_2090_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_a_2093_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
}
v___jp_2101_:
{
if (v___y_2108_ == 0)
{
v___y_1963_ = v___y_2102_;
v___y_1964_ = v___y_2105_;
v___y_1965_ = v___y_2107_;
v___y_1966_ = v___y_2106_;
v___y_1967_ = v___y_2104_;
v___y_1968_ = v___y_2103_;
goto v___jp_1962_;
}
else
{
v___y_2083_ = v___y_2102_;
v___y_2084_ = v___y_2103_;
v___y_2085_ = v___y_2104_;
v___y_2086_ = v___y_2105_;
v___y_2087_ = v___y_2107_;
v___y_2088_ = v___y_2106_;
v___y_2089_ = v___y_2108_;
goto v___jp_2082_;
}
}
v___jp_2109_:
{
uint8_t v_useDecide_2116_; 
v_useDecide_2116_ = lean_ctor_get_uint8(v_config_1812_, sizeof(void*)*1);
if (v_useDecide_2116_ == 0)
{
v___y_2102_ = v_isHEq_2111_;
v___y_2103_ = v___y_2115_;
v___y_2104_ = v___y_2114_;
v___y_2105_ = v___y_2110_;
v___y_2106_ = v___y_2113_;
v___y_2107_ = v___y_2112_;
v___y_2108_ = v___x_1917_;
goto v___jp_2101_;
}
else
{
uint8_t v___x_2117_; 
v___x_2117_ = l_Lean_Expr_hasFVar(v___x_1961_);
if (v___x_2117_ == 0)
{
v___y_2083_ = v_isHEq_2111_;
v___y_2084_ = v___y_2115_;
v___y_2085_ = v___y_2114_;
v___y_2086_ = v___y_2110_;
v___y_2087_ = v___y_2112_;
v___y_2088_ = v___y_2113_;
v___y_2089_ = v_useDecide_2116_;
goto v___jp_2082_;
}
else
{
v___y_2102_ = v_isHEq_2111_;
v___y_2103_ = v___y_2115_;
v___y_2104_ = v___y_2114_;
v___y_2105_ = v___y_2110_;
v___y_2106_ = v___y_2113_;
v___y_2107_ = v___y_2112_;
v___y_2108_ = v___x_1917_;
goto v___jp_2101_;
}
}
}
v___jp_2118_:
{
lean_object* v___x_2126_; 
v___x_2126_ = l_Lean_Meta_isExprDefEq(v___y_2119_, v___y_2123_, v___y_2121_, v___y_2125_, v___y_2120_, v___y_2122_);
if (lean_obj_tag(v___x_2126_) == 0)
{
lean_object* v_a_2127_; uint8_t v___x_2128_; 
v_a_2127_ = lean_ctor_get(v___x_2126_, 0);
lean_inc(v_a_2127_);
lean_dec_ref_known(v___x_2126_, 1);
v___x_2128_ = lean_unbox(v_a_2127_);
lean_dec(v_a_2127_);
if (v___x_2128_ == 0)
{
v___y_2110_ = v___y_2124_;
v_isHEq_2111_ = v___x_1823_;
v___y_2112_ = v___y_2121_;
v___y_2113_ = v___y_2125_;
v___y_2114_ = v___y_2120_;
v___y_2115_ = v___y_2122_;
goto v___jp_2109_;
}
else
{
lean_object* v___x_2129_; 
lean_dec_ref(v___x_1961_);
lean_dec_ref(v_config_1812_);
lean_inc(v_mvarId_1813_);
v___x_2129_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_2121_, v___y_2125_, v___y_2120_, v___y_2122_);
if (lean_obj_tag(v___x_2129_) == 0)
{
lean_object* v_a_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; 
v_a_2130_ = lean_ctor_get(v___x_2129_, 0);
lean_inc(v_a_2130_);
lean_dec_ref_known(v___x_2129_, 1);
v___x_2131_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_2132_ = l_Lean_Meta_mkEqOfHEq(v___x_2131_, v___x_1823_, v___y_2121_, v___y_2125_, v___y_2120_, v___y_2122_);
if (lean_obj_tag(v___x_2132_) == 0)
{
lean_object* v_a_2133_; lean_object* v___x_2134_; 
v_a_2133_ = lean_ctor_get(v___x_2132_, 0);
lean_inc(v_a_2133_);
lean_dec_ref_known(v___x_2132_, 1);
v___x_2134_ = l_Lean_Meta_mkNoConfusion(v_a_2130_, v_a_2133_, v___y_2121_, v___y_2125_, v___y_2120_, v___y_2122_);
if (lean_obj_tag(v___x_2134_) == 0)
{
lean_object* v_a_2135_; lean_object* v___x_2136_; 
v_a_2135_ = lean_ctor_get(v___x_2134_, 0);
lean_inc(v_a_2135_);
lean_dec_ref_known(v___x_2134_, 1);
v___x_2136_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_2135_, v___y_2125_);
if (lean_obj_tag(v___x_2136_) == 0)
{
lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec_ref_known(v___x_2136_, 1);
v___x_2137_ = lean_box(v___x_1823_);
v___x_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2138_, 0, v___x_2137_);
v___x_2139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2139_, 0, v___x_2138_);
lean_ctor_set(v___x_2139_, 1, v___x_1848_);
v_a_1830_ = v___x_2139_;
goto v___jp_1829_;
}
else
{
lean_object* v_a_2140_; lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2147_; 
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_2140_ = lean_ctor_get(v___x_2136_, 0);
v_isSharedCheck_2147_ = !lean_is_exclusive(v___x_2136_);
if (v_isSharedCheck_2147_ == 0)
{
v___x_2142_ = v___x_2136_;
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
else
{
lean_inc(v_a_2140_);
lean_dec(v___x_2136_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2147_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2145_; 
if (v_isShared_2143_ == 0)
{
v___x_2145_ = v___x_2142_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2146_; 
v_reuseFailAlloc_2146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_a_2140_);
v___x_2145_ = v_reuseFailAlloc_2146_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
return v___x_2145_;
}
}
}
}
else
{
lean_object* v_a_2148_; lean_object* v___x_2150_; uint8_t v_isShared_2151_; uint8_t v_isSharedCheck_2155_; 
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2148_ = lean_ctor_get(v___x_2134_, 0);
v_isSharedCheck_2155_ = !lean_is_exclusive(v___x_2134_);
if (v_isSharedCheck_2155_ == 0)
{
v___x_2150_ = v___x_2134_;
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
else
{
lean_inc(v_a_2148_);
lean_dec(v___x_2134_);
v___x_2150_ = lean_box(0);
v_isShared_2151_ = v_isSharedCheck_2155_;
goto v_resetjp_2149_;
}
v_resetjp_2149_:
{
lean_object* v___x_2153_; 
if (v_isShared_2151_ == 0)
{
v___x_2153_ = v___x_2150_;
goto v_reusejp_2152_;
}
else
{
lean_object* v_reuseFailAlloc_2154_; 
v_reuseFailAlloc_2154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2154_, 0, v_a_2148_);
v___x_2153_ = v_reuseFailAlloc_2154_;
goto v_reusejp_2152_;
}
v_reusejp_2152_:
{
return v___x_2153_;
}
}
}
}
else
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2163_; 
lean_dec(v_a_2130_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2156_ = lean_ctor_get(v___x_2132_, 0);
v_isSharedCheck_2163_ = !lean_is_exclusive(v___x_2132_);
if (v_isSharedCheck_2163_ == 0)
{
v___x_2158_ = v___x_2132_;
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2132_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2163_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v___x_2161_; 
if (v_isShared_2159_ == 0)
{
v___x_2161_ = v___x_2158_;
goto v_reusejp_2160_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v_a_2156_);
v___x_2161_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2160_;
}
v_reusejp_2160_:
{
return v___x_2161_;
}
}
}
}
else
{
lean_object* v_a_2164_; lean_object* v___x_2166_; uint8_t v_isShared_2167_; uint8_t v_isSharedCheck_2171_; 
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2164_ = lean_ctor_get(v___x_2129_, 0);
v_isSharedCheck_2171_ = !lean_is_exclusive(v___x_2129_);
if (v_isSharedCheck_2171_ == 0)
{
v___x_2166_ = v___x_2129_;
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
else
{
lean_inc(v_a_2164_);
lean_dec(v___x_2129_);
v___x_2166_ = lean_box(0);
v_isShared_2167_ = v_isSharedCheck_2171_;
goto v_resetjp_2165_;
}
v_resetjp_2165_:
{
lean_object* v___x_2169_; 
if (v_isShared_2167_ == 0)
{
v___x_2169_ = v___x_2166_;
goto v_reusejp_2168_;
}
else
{
lean_object* v_reuseFailAlloc_2170_; 
v_reuseFailAlloc_2170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2170_, 0, v_a_2164_);
v___x_2169_ = v_reuseFailAlloc_2170_;
goto v_reusejp_2168_;
}
v_reusejp_2168_:
{
return v___x_2169_;
}
}
}
}
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2174_; uint8_t v_isShared_2175_; uint8_t v_isSharedCheck_2179_; 
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2172_ = lean_ctor_get(v___x_2126_, 0);
v_isSharedCheck_2179_ = !lean_is_exclusive(v___x_2126_);
if (v_isSharedCheck_2179_ == 0)
{
v___x_2174_ = v___x_2126_;
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
else
{
lean_inc(v_a_2172_);
lean_dec(v___x_2126_);
v___x_2174_ = lean_box(0);
v_isShared_2175_ = v_isSharedCheck_2179_;
goto v_resetjp_2173_;
}
v_resetjp_2173_:
{
lean_object* v___x_2177_; 
if (v_isShared_2175_ == 0)
{
v___x_2177_ = v___x_2174_;
goto v_reusejp_2176_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_a_2172_);
v___x_2177_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2176_;
}
v_reusejp_2176_:
{
return v___x_2177_;
}
}
}
}
v___jp_2180_:
{
lean_object* v___x_2186_; 
lean_inc_ref(v___x_1961_);
v___x_2186_ = l_Lean_Meta_matchHEq_x3f(v___x_1961_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
if (lean_obj_tag(v___x_2186_) == 0)
{
lean_object* v_a_2187_; 
v_a_2187_ = lean_ctor_get(v___x_2186_, 0);
lean_inc(v_a_2187_);
lean_dec_ref_known(v___x_2186_, 1);
if (lean_obj_tag(v_a_2187_) == 1)
{
lean_object* v_val_2188_; lean_object* v_snd_2189_; lean_object* v_snd_2190_; lean_object* v_fst_2191_; lean_object* v_fst_2192_; lean_object* v_fst_2193_; lean_object* v_snd_2194_; lean_object* v___x_2195_; 
v_val_2188_ = lean_ctor_get(v_a_2187_, 0);
lean_inc(v_val_2188_);
lean_dec_ref_known(v_a_2187_, 1);
v_snd_2189_ = lean_ctor_get(v_val_2188_, 1);
lean_inc(v_snd_2189_);
v_snd_2190_ = lean_ctor_get(v_snd_2189_, 1);
lean_inc(v_snd_2190_);
v_fst_2191_ = lean_ctor_get(v_val_2188_, 0);
lean_inc(v_fst_2191_);
lean_dec(v_val_2188_);
v_fst_2192_ = lean_ctor_get(v_snd_2189_, 0);
lean_inc(v_fst_2192_);
lean_dec(v_snd_2189_);
v_fst_2193_ = lean_ctor_get(v_snd_2190_, 0);
lean_inc(v_fst_2193_);
v_snd_2194_ = lean_ctor_get(v_snd_2190_, 1);
lean_inc(v_snd_2194_);
lean_dec(v_snd_2190_);
v___x_2195_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2192_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
if (lean_obj_tag(v___x_2195_) == 0)
{
lean_object* v_a_2196_; 
v_a_2196_ = lean_ctor_get(v___x_2195_, 0);
lean_inc(v_a_2196_);
lean_dec_ref_known(v___x_2195_, 1);
if (lean_obj_tag(v_a_2196_) == 1)
{
lean_object* v_val_2197_; lean_object* v___x_2198_; 
v_val_2197_ = lean_ctor_get(v_a_2196_, 0);
lean_inc(v_val_2197_);
lean_dec_ref_known(v_a_2196_, 1);
v___x_2198_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2194_, v___y_2182_, v___y_2183_, v___y_2184_, v___y_2185_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
lean_inc(v_a_2199_);
lean_dec_ref_known(v___x_2198_, 1);
if (lean_obj_tag(v_a_2199_) == 1)
{
lean_object* v_toConstantVal_2200_; lean_object* v_val_2201_; lean_object* v_toConstantVal_2202_; lean_object* v_name_2203_; lean_object* v_name_2204_; uint8_t v___x_2205_; 
v_toConstantVal_2200_ = lean_ctor_get(v_val_2197_, 0);
lean_inc_ref(v_toConstantVal_2200_);
lean_dec(v_val_2197_);
v_val_2201_ = lean_ctor_get(v_a_2199_, 0);
lean_inc(v_val_2201_);
lean_dec_ref_known(v_a_2199_, 1);
v_toConstantVal_2202_ = lean_ctor_get(v_val_2201_, 0);
lean_inc_ref(v_toConstantVal_2202_);
lean_dec(v_val_2201_);
v_name_2203_ = lean_ctor_get(v_toConstantVal_2200_, 0);
lean_inc(v_name_2203_);
lean_dec_ref(v_toConstantVal_2200_);
v_name_2204_ = lean_ctor_get(v_toConstantVal_2202_, 0);
lean_inc(v_name_2204_);
lean_dec_ref(v_toConstantVal_2202_);
v___x_2205_ = lean_name_eq(v_name_2203_, v_name_2204_);
lean_dec(v_name_2204_);
lean_dec(v_name_2203_);
if (v___x_2205_ == 0)
{
v___y_2119_ = v_fst_2191_;
v___y_2120_ = v___y_2184_;
v___y_2121_ = v___y_2182_;
v___y_2122_ = v___y_2185_;
v___y_2123_ = v_fst_2193_;
v___y_2124_ = v_isEq_2181_;
v___y_2125_ = v___y_2183_;
goto v___jp_2118_;
}
else
{
if (v___x_1917_ == 0)
{
lean_dec(v_fst_2193_);
lean_dec(v_fst_2191_);
v___y_2110_ = v_isEq_2181_;
v_isHEq_2111_ = v___x_1823_;
v___y_2112_ = v___y_2182_;
v___y_2113_ = v___y_2183_;
v___y_2114_ = v___y_2184_;
v___y_2115_ = v___y_2185_;
goto v___jp_2109_;
}
else
{
v___y_2119_ = v_fst_2191_;
v___y_2120_ = v___y_2184_;
v___y_2121_ = v___y_2182_;
v___y_2122_ = v___y_2185_;
v___y_2123_ = v_fst_2193_;
v___y_2124_ = v_isEq_2181_;
v___y_2125_ = v___y_2183_;
goto v___jp_2118_;
}
}
}
else
{
lean_dec(v_a_2199_);
lean_dec(v_val_2197_);
lean_dec(v_fst_2193_);
lean_dec(v_fst_2191_);
v___y_2110_ = v_isEq_2181_;
v_isHEq_2111_ = v___x_1823_;
v___y_2112_ = v___y_2182_;
v___y_2113_ = v___y_2183_;
v___y_2114_ = v___y_2184_;
v___y_2115_ = v___y_2185_;
goto v___jp_2109_;
}
}
else
{
lean_object* v_a_2206_; lean_object* v___x_2208_; uint8_t v_isShared_2209_; uint8_t v_isSharedCheck_2213_; 
lean_dec(v_val_2197_);
lean_dec(v_fst_2193_);
lean_dec(v_fst_2191_);
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2206_ = lean_ctor_get(v___x_2198_, 0);
v_isSharedCheck_2213_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2213_ == 0)
{
v___x_2208_ = v___x_2198_;
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
else
{
lean_inc(v_a_2206_);
lean_dec(v___x_2198_);
v___x_2208_ = lean_box(0);
v_isShared_2209_ = v_isSharedCheck_2213_;
goto v_resetjp_2207_;
}
v_resetjp_2207_:
{
lean_object* v___x_2211_; 
if (v_isShared_2209_ == 0)
{
v___x_2211_ = v___x_2208_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_a_2206_);
v___x_2211_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
return v___x_2211_;
}
}
}
}
else
{
lean_dec(v_a_2196_);
lean_dec(v_snd_2194_);
lean_dec(v_fst_2193_);
lean_dec(v_fst_2191_);
v___y_2110_ = v_isEq_2181_;
v_isHEq_2111_ = v___x_1823_;
v___y_2112_ = v___y_2182_;
v___y_2113_ = v___y_2183_;
v___y_2114_ = v___y_2184_;
v___y_2115_ = v___y_2185_;
goto v___jp_2109_;
}
}
else
{
lean_object* v_a_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2221_; 
lean_dec(v_snd_2194_);
lean_dec(v_fst_2193_);
lean_dec(v_fst_2191_);
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2214_ = lean_ctor_get(v___x_2195_, 0);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2195_);
if (v_isSharedCheck_2221_ == 0)
{
v___x_2216_ = v___x_2195_;
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_a_2214_);
lean_dec(v___x_2195_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2221_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v___x_2219_; 
if (v_isShared_2217_ == 0)
{
v___x_2219_ = v___x_2216_;
goto v_reusejp_2218_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_a_2214_);
v___x_2219_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2218_;
}
v_reusejp_2218_:
{
return v___x_2219_;
}
}
}
}
else
{
lean_dec(v_a_2187_);
v___y_2110_ = v_isEq_2181_;
v_isHEq_2111_ = v___x_1917_;
v___y_2112_ = v___y_2182_;
v___y_2113_ = v___y_2183_;
v___y_2114_ = v___y_2184_;
v___y_2115_ = v___y_2185_;
goto v___jp_2109_;
}
}
else
{
lean_object* v_a_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2229_; 
lean_dec_ref(v___x_1961_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2222_ = lean_ctor_get(v___x_2186_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2186_);
if (v_isSharedCheck_2229_ == 0)
{
v___x_2224_ = v___x_2186_;
v_isShared_2225_ = v_isSharedCheck_2229_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_a_2222_);
lean_dec(v___x_2186_);
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
v___jp_2230_:
{
lean_object* v___x_2235_; 
lean_inc_ref(v___x_1961_);
v___x_2235_ = l_Lean_Meta_matchEq_x3f(v___x_1961_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2235_) == 0)
{
lean_object* v_a_2236_; 
v_a_2236_ = lean_ctor_get(v___x_2235_, 0);
lean_inc(v_a_2236_);
lean_dec_ref_known(v___x_2235_, 1);
if (lean_obj_tag(v_a_2236_) == 1)
{
lean_object* v_val_2237_; lean_object* v_snd_2238_; lean_object* v_fst_2239_; lean_object* v_snd_2240_; lean_object* v___x_2241_; 
v_val_2237_ = lean_ctor_get(v_a_2236_, 0);
lean_inc(v_val_2237_);
lean_dec_ref_known(v_a_2236_, 1);
v_snd_2238_ = lean_ctor_get(v_val_2237_, 1);
lean_inc(v_snd_2238_);
lean_dec(v_val_2237_);
v_fst_2239_ = lean_ctor_get(v_snd_2238_, 0);
lean_inc(v_fst_2239_);
v_snd_2240_ = lean_ctor_get(v_snd_2238_, 1);
lean_inc(v_snd_2240_);
lean_dec(v_snd_2238_);
v___x_2241_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2239_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2241_, 1);
if (lean_obj_tag(v_a_2242_) == 1)
{
lean_object* v_val_2243_; lean_object* v___x_2244_; 
v_val_2243_ = lean_ctor_get(v_a_2242_, 0);
lean_inc(v_val_2243_);
lean_dec_ref_known(v_a_2242_, 1);
v___x_2244_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2240_, v___y_2231_, v___y_2232_, v___y_2233_, v___y_2234_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2244_, 1);
if (lean_obj_tag(v_a_2245_) == 1)
{
lean_object* v_toConstantVal_2246_; lean_object* v_val_2247_; lean_object* v_toConstantVal_2248_; lean_object* v_name_2249_; lean_object* v_name_2250_; uint8_t v___x_2251_; 
v_toConstantVal_2246_ = lean_ctor_get(v_val_2243_, 0);
lean_inc_ref(v_toConstantVal_2246_);
lean_dec(v_val_2243_);
v_val_2247_ = lean_ctor_get(v_a_2245_, 0);
lean_inc(v_val_2247_);
lean_dec_ref_known(v_a_2245_, 1);
v_toConstantVal_2248_ = lean_ctor_get(v_val_2247_, 0);
lean_inc_ref(v_toConstantVal_2248_);
lean_dec(v_val_2247_);
v_name_2249_ = lean_ctor_get(v_toConstantVal_2246_, 0);
lean_inc(v_name_2249_);
lean_dec_ref(v_toConstantVal_2246_);
v_name_2250_ = lean_ctor_get(v_toConstantVal_2248_, 0);
lean_inc(v_name_2250_);
lean_dec_ref(v_toConstantVal_2248_);
v___x_2251_ = lean_name_eq(v_name_2249_, v_name_2250_);
lean_dec(v_name_2250_);
lean_dec(v_name_2249_);
if (v___x_2251_ == 0)
{
lean_dec_ref(v___x_1961_);
lean_dec_ref(v_config_1812_);
v___y_1850_ = v___y_2232_;
v___y_1851_ = v___y_2234_;
v___y_1852_ = v___y_2233_;
v___y_1853_ = v___y_2231_;
goto v___jp_1849_;
}
else
{
if (v___x_1917_ == 0)
{
lean_del_object(v___x_1846_);
v_isEq_2181_ = v___x_1823_;
v___y_2182_ = v___y_2231_;
v___y_2183_ = v___y_2232_;
v___y_2184_ = v___y_2233_;
v___y_2185_ = v___y_2234_;
goto v___jp_2180_;
}
else
{
lean_dec_ref(v___x_1961_);
lean_dec_ref(v_config_1812_);
v___y_1850_ = v___y_2232_;
v___y_1851_ = v___y_2234_;
v___y_1852_ = v___y_2233_;
v___y_1853_ = v___y_2231_;
goto v___jp_1849_;
}
}
}
else
{
lean_dec(v_a_2245_);
lean_dec(v_val_2243_);
lean_del_object(v___x_1846_);
v_isEq_2181_ = v___x_1823_;
v___y_2182_ = v___y_2231_;
v___y_2183_ = v___y_2232_;
v___y_2184_ = v___y_2233_;
v___y_2185_ = v___y_2234_;
goto v___jp_2180_;
}
}
else
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2259_; 
lean_dec(v_val_2243_);
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2252_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2259_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2259_ == 0)
{
v___x_2254_ = v___x_2244_;
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2244_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2259_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v___x_2257_; 
if (v_isShared_2255_ == 0)
{
v___x_2257_ = v___x_2254_;
goto v_reusejp_2256_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_a_2252_);
v___x_2257_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2256_;
}
v_reusejp_2256_:
{
return v___x_2257_;
}
}
}
}
else
{
lean_dec(v_a_2242_);
lean_dec(v_snd_2240_);
lean_del_object(v___x_1846_);
v_isEq_2181_ = v___x_1823_;
v___y_2182_ = v___y_2231_;
v___y_2183_ = v___y_2232_;
v___y_2184_ = v___y_2233_;
v___y_2185_ = v___y_2234_;
goto v___jp_2180_;
}
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2262_; uint8_t v_isShared_2263_; uint8_t v_isSharedCheck_2267_; 
lean_dec(v_snd_2240_);
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2260_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2262_ = v___x_2241_;
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
else
{
lean_inc(v_a_2260_);
lean_dec(v___x_2241_);
v___x_2262_ = lean_box(0);
v_isShared_2263_ = v_isSharedCheck_2267_;
goto v_resetjp_2261_;
}
v_resetjp_2261_:
{
lean_object* v___x_2265_; 
if (v_isShared_2263_ == 0)
{
v___x_2265_ = v___x_2262_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_a_2260_);
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
lean_dec(v_a_2236_);
lean_del_object(v___x_1846_);
v_isEq_2181_ = v___x_1917_;
v___y_2182_ = v___y_2231_;
v___y_2183_ = v___y_2232_;
v___y_2184_ = v___y_2233_;
v___y_2185_ = v___y_2234_;
goto v___jp_2180_;
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2268_ = lean_ctor_get(v___x_2235_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2235_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2235_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2235_);
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
v___jp_2276_:
{
lean_object* v___x_2281_; 
lean_inc_ref(v___x_1961_);
v___x_2281_ = l_Lean_refutableHasNotBit_x3f(v___x_1961_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2281_) == 0)
{
lean_object* v_a_2282_; 
v_a_2282_ = lean_ctor_get(v___x_2281_, 0);
lean_inc(v_a_2282_);
lean_dec_ref_known(v___x_2281_, 1);
if (lean_obj_tag(v_a_2282_) == 1)
{
lean_object* v_val_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2322_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec_ref(v_config_1812_);
v_val_2283_ = lean_ctor_get(v_a_2282_, 0);
v_isSharedCheck_2322_ = !lean_is_exclusive(v_a_2282_);
if (v_isSharedCheck_2322_ == 0)
{
v___x_2285_ = v_a_2282_;
v_isShared_2286_ = v_isSharedCheck_2322_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_val_2283_);
lean_dec(v_a_2282_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2322_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2287_; 
lean_inc(v_mvarId_1813_);
v___x_2287_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2287_) == 0)
{
lean_object* v_a_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v_a_2288_ = lean_ctor_get(v___x_2287_, 0);
lean_inc(v_a_2288_);
lean_dec_ref_known(v___x_2287_, 1);
v___x_2289_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_2290_ = l_Lean_Meta_mkAbsurd(v_a_2288_, v_val_2283_, v___x_2289_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2290_) == 0)
{
lean_object* v_a_2291_; lean_object* v___x_2292_; 
v_a_2291_ = lean_ctor_get(v___x_2290_, 0);
lean_inc(v_a_2291_);
lean_dec_ref_known(v___x_2290_, 1);
v___x_2292_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_2291_, v___y_2278_);
if (lean_obj_tag(v___x_2292_) == 0)
{
lean_object* v___x_2293_; lean_object* v___x_2295_; 
lean_dec_ref_known(v___x_2292_, 1);
v___x_2293_ = lean_box(v___x_1823_);
if (v_isShared_2286_ == 0)
{
lean_ctor_set(v___x_2285_, 0, v___x_2293_);
v___x_2295_ = v___x_2285_;
goto v_reusejp_2294_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2293_);
v___x_2295_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2294_;
}
v_reusejp_2294_:
{
lean_object* v___x_2296_; 
v___x_2296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2296_, 0, v___x_2295_);
lean_ctor_set(v___x_2296_, 1, v___x_1848_);
v_a_1830_ = v___x_2296_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_2298_; lean_object* v___x_2300_; uint8_t v_isShared_2301_; uint8_t v_isSharedCheck_2305_; 
lean_del_object(v___x_2285_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_2298_ = lean_ctor_get(v___x_2292_, 0);
v_isSharedCheck_2305_ = !lean_is_exclusive(v___x_2292_);
if (v_isSharedCheck_2305_ == 0)
{
v___x_2300_ = v___x_2292_;
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
else
{
lean_inc(v_a_2298_);
lean_dec(v___x_2292_);
v___x_2300_ = lean_box(0);
v_isShared_2301_ = v_isSharedCheck_2305_;
goto v_resetjp_2299_;
}
v_resetjp_2299_:
{
lean_object* v___x_2303_; 
if (v_isShared_2301_ == 0)
{
v___x_2303_ = v___x_2300_;
goto v_reusejp_2302_;
}
else
{
lean_object* v_reuseFailAlloc_2304_; 
v_reuseFailAlloc_2304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2304_, 0, v_a_2298_);
v___x_2303_ = v_reuseFailAlloc_2304_;
goto v_reusejp_2302_;
}
v_reusejp_2302_:
{
return v___x_2303_;
}
}
}
}
else
{
lean_object* v_a_2306_; lean_object* v___x_2308_; uint8_t v_isShared_2309_; uint8_t v_isSharedCheck_2313_; 
lean_del_object(v___x_2285_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2306_ = lean_ctor_get(v___x_2290_, 0);
v_isSharedCheck_2313_ = !lean_is_exclusive(v___x_2290_);
if (v_isSharedCheck_2313_ == 0)
{
v___x_2308_ = v___x_2290_;
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
else
{
lean_inc(v_a_2306_);
lean_dec(v___x_2290_);
v___x_2308_ = lean_box(0);
v_isShared_2309_ = v_isSharedCheck_2313_;
goto v_resetjp_2307_;
}
v_resetjp_2307_:
{
lean_object* v___x_2311_; 
if (v_isShared_2309_ == 0)
{
v___x_2311_ = v___x_2308_;
goto v_reusejp_2310_;
}
else
{
lean_object* v_reuseFailAlloc_2312_; 
v_reuseFailAlloc_2312_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2312_, 0, v_a_2306_);
v___x_2311_ = v_reuseFailAlloc_2312_;
goto v_reusejp_2310_;
}
v_reusejp_2310_:
{
return v___x_2311_;
}
}
}
}
else
{
lean_object* v_a_2314_; lean_object* v___x_2316_; uint8_t v_isShared_2317_; uint8_t v_isSharedCheck_2321_; 
lean_del_object(v___x_2285_);
lean_dec(v_val_2283_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2314_ = lean_ctor_get(v___x_2287_, 0);
v_isSharedCheck_2321_ = !lean_is_exclusive(v___x_2287_);
if (v_isSharedCheck_2321_ == 0)
{
v___x_2316_ = v___x_2287_;
v_isShared_2317_ = v_isSharedCheck_2321_;
goto v_resetjp_2315_;
}
else
{
lean_inc(v_a_2314_);
lean_dec(v___x_2287_);
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
else
{
lean_object* v___x_2323_; 
lean_dec(v_a_2282_);
lean_inc_ref(v___x_1961_);
v___x_2323_ = l_Lean_Meta_matchNe_x3f(v___x_1961_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
if (lean_obj_tag(v_a_2324_) == 1)
{
lean_object* v_val_2325_; lean_object* v___x_2327_; uint8_t v_isShared_2328_; uint8_t v_isSharedCheck_2394_; 
v_val_2325_ = lean_ctor_get(v_a_2324_, 0);
v_isSharedCheck_2394_ = !lean_is_exclusive(v_a_2324_);
if (v_isSharedCheck_2394_ == 0)
{
v___x_2327_ = v_a_2324_;
v_isShared_2328_ = v_isSharedCheck_2394_;
goto v_resetjp_2326_;
}
else
{
lean_inc(v_val_2325_);
lean_dec(v_a_2324_);
v___x_2327_ = lean_box(0);
v_isShared_2328_ = v_isSharedCheck_2394_;
goto v_resetjp_2326_;
}
v_resetjp_2326_:
{
lean_object* v_snd_2329_; lean_object* v_fst_2330_; lean_object* v_snd_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2393_; 
v_snd_2329_ = lean_ctor_get(v_val_2325_, 1);
lean_inc(v_snd_2329_);
lean_dec(v_val_2325_);
v_fst_2330_ = lean_ctor_get(v_snd_2329_, 0);
v_snd_2331_ = lean_ctor_get(v_snd_2329_, 1);
v_isSharedCheck_2393_ = !lean_is_exclusive(v_snd_2329_);
if (v_isSharedCheck_2393_ == 0)
{
v___x_2333_ = v_snd_2329_;
v_isShared_2334_ = v_isSharedCheck_2393_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_snd_2331_);
lean_inc(v_fst_2330_);
lean_dec(v_snd_2329_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2393_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v___x_2335_; 
lean_inc(v_fst_2330_);
v___x_2335_ = l_Lean_Meta_isExprDefEq(v_fst_2330_, v_snd_2331_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2335_) == 0)
{
lean_object* v_a_2336_; uint8_t v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___x_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___x_2335_, 1);
v___x_2337_ = lean_unbox(v_a_2336_);
lean_dec(v_a_2336_);
if (v___x_2337_ == 0)
{
lean_del_object(v___x_2333_);
lean_dec(v_fst_2330_);
lean_del_object(v___x_2327_);
v___y_2231_ = v___y_2277_;
v___y_2232_ = v___y_2278_;
v___y_2233_ = v___y_2279_;
v___y_2234_ = v___y_2280_;
goto v___jp_2230_;
}
else
{
lean_object* v___x_2338_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec_ref(v_config_1812_);
lean_inc(v_mvarId_1813_);
v___x_2338_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2338_) == 0)
{
lean_object* v_a_2339_; lean_object* v___x_2340_; 
v_a_2339_ = lean_ctor_get(v___x_2338_, 0);
lean_inc(v_a_2339_);
lean_dec_ref_known(v___x_2338_, 1);
v___x_2340_ = l_Lean_Meta_mkEqRefl(v_fst_2330_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2340_) == 0)
{
lean_object* v_a_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v_a_2341_ = lean_ctor_get(v___x_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___x_2340_, 1);
v___x_2342_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_2343_ = l_Lean_Meta_mkAbsurd(v_a_2339_, v_a_2341_, v___x_2342_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_);
if (lean_obj_tag(v___x_2343_) == 0)
{
lean_object* v_a_2344_; lean_object* v___x_2345_; 
v_a_2344_ = lean_ctor_get(v___x_2343_, 0);
lean_inc(v_a_2344_);
lean_dec_ref_known(v___x_2343_, 1);
v___x_2345_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_2344_, v___y_2278_);
if (lean_obj_tag(v___x_2345_) == 0)
{
lean_object* v___x_2346_; lean_object* v___x_2348_; 
lean_dec_ref_known(v___x_2345_, 1);
v___x_2346_ = lean_box(v___x_1823_);
if (v_isShared_2328_ == 0)
{
lean_ctor_set(v___x_2327_, 0, v___x_2346_);
v___x_2348_ = v___x_2327_;
goto v_reusejp_2347_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v___x_2346_);
v___x_2348_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2347_;
}
v_reusejp_2347_:
{
lean_object* v___x_2350_; 
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 1, v___x_1848_);
lean_ctor_set(v___x_2333_, 0, v___x_2348_);
v___x_2350_ = v___x_2333_;
goto v_reusejp_2349_;
}
else
{
lean_object* v_reuseFailAlloc_2351_; 
v_reuseFailAlloc_2351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2351_, 0, v___x_2348_);
lean_ctor_set(v_reuseFailAlloc_2351_, 1, v___x_1848_);
v___x_2350_ = v_reuseFailAlloc_2351_;
goto v_reusejp_2349_;
}
v_reusejp_2349_:
{
v_a_1830_ = v___x_2350_;
goto v___jp_1829_;
}
}
}
else
{
lean_object* v_a_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2360_; 
lean_del_object(v___x_2333_);
lean_del_object(v___x_2327_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_2353_ = lean_ctor_get(v___x_2345_, 0);
v_isSharedCheck_2360_ = !lean_is_exclusive(v___x_2345_);
if (v_isSharedCheck_2360_ == 0)
{
v___x_2355_ = v___x_2345_;
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_a_2353_);
lean_dec(v___x_2345_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2360_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2356_ == 0)
{
v___x_2358_ = v___x_2355_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2359_; 
v_reuseFailAlloc_2359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2353_);
v___x_2358_ = v_reuseFailAlloc_2359_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
return v___x_2358_;
}
}
}
}
else
{
lean_object* v_a_2361_; lean_object* v___x_2363_; uint8_t v_isShared_2364_; uint8_t v_isSharedCheck_2368_; 
lean_del_object(v___x_2333_);
lean_del_object(v___x_2327_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2361_ = lean_ctor_get(v___x_2343_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2343_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2363_ = v___x_2343_;
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
else
{
lean_inc(v_a_2361_);
lean_dec(v___x_2343_);
v___x_2363_ = lean_box(0);
v_isShared_2364_ = v_isSharedCheck_2368_;
goto v_resetjp_2362_;
}
v_resetjp_2362_:
{
lean_object* v___x_2366_; 
if (v_isShared_2364_ == 0)
{
v___x_2366_ = v___x_2363_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v_a_2361_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
else
{
lean_object* v_a_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2376_; 
lean_dec(v_a_2339_);
lean_del_object(v___x_2333_);
lean_del_object(v___x_2327_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2369_ = lean_ctor_get(v___x_2340_, 0);
v_isSharedCheck_2376_ = !lean_is_exclusive(v___x_2340_);
if (v_isSharedCheck_2376_ == 0)
{
v___x_2371_ = v___x_2340_;
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_a_2369_);
lean_dec(v___x_2340_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2376_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2374_; 
if (v_isShared_2372_ == 0)
{
v___x_2374_ = v___x_2371_;
goto v_reusejp_2373_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
v___x_2374_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2373_;
}
v_reusejp_2373_:
{
return v___x_2374_;
}
}
}
}
else
{
lean_object* v_a_2377_; lean_object* v___x_2379_; uint8_t v_isShared_2380_; uint8_t v_isSharedCheck_2384_; 
lean_del_object(v___x_2333_);
lean_dec(v_fst_2330_);
lean_del_object(v___x_2327_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_2377_ = lean_ctor_get(v___x_2338_, 0);
v_isSharedCheck_2384_ = !lean_is_exclusive(v___x_2338_);
if (v_isSharedCheck_2384_ == 0)
{
v___x_2379_ = v___x_2338_;
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
else
{
lean_inc(v_a_2377_);
lean_dec(v___x_2338_);
v___x_2379_ = lean_box(0);
v_isShared_2380_ = v_isSharedCheck_2384_;
goto v_resetjp_2378_;
}
v_resetjp_2378_:
{
lean_object* v___x_2382_; 
if (v_isShared_2380_ == 0)
{
v___x_2382_ = v___x_2379_;
goto v_reusejp_2381_;
}
else
{
lean_object* v_reuseFailAlloc_2383_; 
v_reuseFailAlloc_2383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2383_, 0, v_a_2377_);
v___x_2382_ = v_reuseFailAlloc_2383_;
goto v_reusejp_2381_;
}
v_reusejp_2381_:
{
return v___x_2382_;
}
}
}
}
}
else
{
lean_object* v_a_2385_; lean_object* v___x_2387_; uint8_t v_isShared_2388_; uint8_t v_isSharedCheck_2392_; 
lean_del_object(v___x_2333_);
lean_dec(v_fst_2330_);
lean_del_object(v___x_2327_);
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2385_ = lean_ctor_get(v___x_2335_, 0);
v_isSharedCheck_2392_ = !lean_is_exclusive(v___x_2335_);
if (v_isSharedCheck_2392_ == 0)
{
v___x_2387_ = v___x_2335_;
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
else
{
lean_inc(v_a_2385_);
lean_dec(v___x_2335_);
v___x_2387_ = lean_box(0);
v_isShared_2388_ = v_isSharedCheck_2392_;
goto v_resetjp_2386_;
}
v_resetjp_2386_:
{
lean_object* v___x_2390_; 
if (v_isShared_2388_ == 0)
{
v___x_2390_ = v___x_2387_;
goto v_reusejp_2389_;
}
else
{
lean_object* v_reuseFailAlloc_2391_; 
v_reuseFailAlloc_2391_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2391_, 0, v_a_2385_);
v___x_2390_ = v_reuseFailAlloc_2391_;
goto v_reusejp_2389_;
}
v_reusejp_2389_:
{
return v___x_2390_;
}
}
}
}
}
}
else
{
lean_dec(v_a_2324_);
v___y_2231_ = v___y_2277_;
v___y_2232_ = v___y_2278_;
v___y_2233_ = v___y_2279_;
v___y_2234_ = v___y_2280_;
goto v___jp_2230_;
}
}
else
{
lean_object* v_a_2395_; lean_object* v___x_2397_; uint8_t v_isShared_2398_; uint8_t v_isSharedCheck_2402_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2395_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2402_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2402_ == 0)
{
v___x_2397_ = v___x_2323_;
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
else
{
lean_inc(v_a_2395_);
lean_dec(v___x_2323_);
v___x_2397_ = lean_box(0);
v_isShared_2398_ = v_isSharedCheck_2402_;
goto v_resetjp_2396_;
}
v_resetjp_2396_:
{
lean_object* v___x_2400_; 
if (v_isShared_2398_ == 0)
{
v___x_2400_ = v___x_2397_;
goto v_reusejp_2399_;
}
else
{
lean_object* v_reuseFailAlloc_2401_; 
v_reuseFailAlloc_2401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2401_, 0, v_a_2395_);
v___x_2400_ = v_reuseFailAlloc_2401_;
goto v_reusejp_2399_;
}
v_reusejp_2399_:
{
return v___x_2400_;
}
}
}
}
}
else
{
lean_object* v_a_2403_; lean_object* v___x_2405_; uint8_t v_isShared_2406_; uint8_t v_isSharedCheck_2410_; 
lean_dec_ref(v___x_1961_);
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_2403_ = lean_ctor_get(v___x_2281_, 0);
v_isSharedCheck_2410_ = !lean_is_exclusive(v___x_2281_);
if (v_isSharedCheck_2410_ == 0)
{
v___x_2405_ = v___x_2281_;
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
else
{
lean_inc(v_a_2403_);
lean_dec(v___x_2281_);
v___x_2405_ = lean_box(0);
v_isShared_2406_ = v_isSharedCheck_2410_;
goto v_resetjp_2404_;
}
v_resetjp_2404_:
{
lean_object* v___x_2408_; 
if (v_isShared_2406_ == 0)
{
v___x_2408_ = v___x_2405_;
goto v_reusejp_2407_;
}
else
{
lean_object* v_reuseFailAlloc_2409_; 
v_reuseFailAlloc_2409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2409_, 0, v_a_2403_);
v___x_2408_ = v_reuseFailAlloc_2409_;
goto v_reusejp_2407_;
}
v_reusejp_2407_:
{
return v___x_2408_;
}
}
}
}
}
else
{
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_1838_ = v___x_1889_;
goto v___jp_1837_;
}
v___jp_1849_:
{
lean_object* v___x_1854_; 
lean_inc(v_mvarId_1813_);
v___x_1854_ = l_Lean_MVarId_getType(v_mvarId_1813_, v___y_1853_, v___y_1850_, v___y_1852_, v___y_1851_);
if (lean_obj_tag(v___x_1854_) == 0)
{
lean_object* v_a_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v_a_1855_ = lean_ctor_get(v___x_1854_, 0);
lean_inc(v_a_1855_);
lean_dec_ref_known(v___x_1854_, 1);
v___x_1856_ = l_Lean_LocalDecl_toExpr(v_val_1844_);
v___x_1857_ = l_Lean_Meta_mkNoConfusion(v_a_1855_, v___x_1856_, v___y_1853_, v___y_1850_, v___y_1852_, v___y_1851_);
if (lean_obj_tag(v___x_1857_) == 0)
{
lean_object* v_a_1858_; lean_object* v___x_1859_; 
v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
lean_inc(v_a_1858_);
lean_dec_ref_known(v___x_1857_, 1);
v___x_1859_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_1813_, v_a_1858_, v___y_1850_);
if (lean_obj_tag(v___x_1859_) == 0)
{
lean_object* v___x_1860_; lean_object* v___x_1862_; 
lean_dec_ref_known(v___x_1859_, 1);
v___x_1860_ = lean_box(v___x_1823_);
if (v_isShared_1847_ == 0)
{
lean_ctor_set(v___x_1846_, 0, v___x_1860_);
v___x_1862_ = v___x_1846_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1864_; 
v_reuseFailAlloc_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1864_, 0, v___x_1860_);
v___x_1862_ = v_reuseFailAlloc_1864_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1863_, 0, v___x_1862_);
lean_ctor_set(v___x_1863_, 1, v___x_1848_);
v_a_1830_ = v___x_1863_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_1865_; lean_object* v___x_1867_; uint8_t v_isShared_1868_; uint8_t v_isSharedCheck_1872_; 
lean_del_object(v___x_1846_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_1865_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1872_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1872_ == 0)
{
v___x_1867_ = v___x_1859_;
v_isShared_1868_ = v_isSharedCheck_1872_;
goto v_resetjp_1866_;
}
else
{
lean_inc(v_a_1865_);
lean_dec(v___x_1859_);
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
lean_del_object(v___x_1846_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_1873_ = lean_ctor_get(v___x_1857_, 0);
v_isSharedCheck_1880_ = !lean_is_exclusive(v___x_1857_);
if (v_isSharedCheck_1880_ == 0)
{
v___x_1875_ = v___x_1857_;
v_isShared_1876_ = v_isSharedCheck_1880_;
goto v_resetjp_1874_;
}
else
{
lean_inc(v_a_1873_);
lean_dec(v___x_1857_);
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
else
{
lean_object* v_a_1881_; lean_object* v___x_1883_; uint8_t v_isShared_1884_; uint8_t v_isSharedCheck_1888_; 
lean_del_object(v___x_1846_);
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
v_a_1881_ = lean_ctor_get(v___x_1854_, 0);
v_isSharedCheck_1888_ = !lean_is_exclusive(v___x_1854_);
if (v_isSharedCheck_1888_ == 0)
{
v___x_1883_ = v___x_1854_;
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
else
{
lean_inc(v_a_1881_);
lean_dec(v___x_1854_);
v___x_1883_ = lean_box(0);
v_isShared_1884_ = v_isSharedCheck_1888_;
goto v_resetjp_1882_;
}
v_resetjp_1882_:
{
lean_object* v___x_1886_; 
if (v_isShared_1884_ == 0)
{
v___x_1886_ = v___x_1883_;
goto v_reusejp_1885_;
}
else
{
lean_object* v_reuseFailAlloc_1887_; 
v_reuseFailAlloc_1887_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1887_, 0, v_a_1881_);
v___x_1886_ = v_reuseFailAlloc_1887_;
goto v_reusejp_1885_;
}
v_reusejp_1885_:
{
return v___x_1886_;
}
}
}
}
v___jp_1890_:
{
lean_object* v_searchFuel_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v_searchFuel_1895_ = lean_ctor_get(v_config_1812_, 0);
v___x_1896_ = l_Lean_LocalDecl_fvarId(v_val_1844_);
lean_dec(v_val_1844_);
lean_inc(v_searchFuel_1895_);
lean_inc(v_mvarId_1813_);
v___x_1897_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_1813_, v___x_1896_, v_searchFuel_1895_, v___y_1891_, v___y_1894_, v___y_1893_, v___y_1892_);
if (lean_obj_tag(v___x_1897_) == 0)
{
lean_object* v_a_1898_; uint8_t v___x_1899_; 
v_a_1898_ = lean_ctor_get(v___x_1897_, 0);
lean_inc(v_a_1898_);
lean_dec_ref_known(v___x_1897_, 1);
v___x_1899_ = lean_unbox(v_a_1898_);
lean_dec(v_a_1898_);
if (v___x_1899_ == 0)
{
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_1838_ = v___x_1889_;
goto v___jp_1837_;
}
else
{
lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v___x_1900_ = lean_box(v___x_1823_);
v___x_1901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1900_);
v___x_1902_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1902_, 0, v___x_1901_);
lean_ctor_set(v___x_1902_, 1, v___x_1848_);
v_a_1830_ = v___x_1902_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_1903_; lean_object* v___x_1905_; uint8_t v_isShared_1906_; uint8_t v_isSharedCheck_1910_; 
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_1903_ = lean_ctor_get(v___x_1897_, 0);
v_isSharedCheck_1910_ = !lean_is_exclusive(v___x_1897_);
if (v_isSharedCheck_1910_ == 0)
{
v___x_1905_ = v___x_1897_;
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
else
{
lean_inc(v_a_1903_);
lean_dec(v___x_1897_);
v___x_1905_ = lean_box(0);
v_isShared_1906_ = v_isSharedCheck_1910_;
goto v_resetjp_1904_;
}
v_resetjp_1904_:
{
lean_object* v___x_1908_; 
if (v_isShared_1906_ == 0)
{
v___x_1908_ = v___x_1905_;
goto v_reusejp_1907_;
}
else
{
lean_object* v_reuseFailAlloc_1909_; 
v_reuseFailAlloc_1909_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1909_, 0, v_a_1903_);
v___x_1908_ = v_reuseFailAlloc_1909_;
goto v_reusejp_1907_;
}
v_reusejp_1907_:
{
return v___x_1908_;
}
}
}
}
v___jp_1911_:
{
if (v___y_1916_ == 0)
{
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
v_a_1838_ = v___x_1889_;
goto v___jp_1837_;
}
else
{
v___y_1891_ = v___y_1912_;
v___y_1892_ = v___y_1913_;
v___y_1893_ = v___y_1914_;
v___y_1894_ = v___y_1915_;
goto v___jp_1890_;
}
}
v___jp_1918_:
{
if (v___y_1919_ == 0)
{
v___y_1891_ = v___y_1920_;
v___y_1892_ = v___y_1921_;
v___y_1893_ = v___y_1922_;
v___y_1894_ = v___y_1923_;
goto v___jp_1890_;
}
else
{
v___y_1912_ = v___y_1920_;
v___y_1913_ = v___y_1921_;
v___y_1914_ = v___y_1922_;
v___y_1915_ = v___y_1923_;
v___y_1916_ = v___x_1917_;
goto v___jp_1911_;
}
}
v___jp_1924_:
{
if (v___y_1930_ == 0)
{
v___y_1912_ = v___y_1926_;
v___y_1913_ = v___y_1927_;
v___y_1914_ = v___y_1928_;
v___y_1915_ = v___y_1929_;
v___y_1916_ = v___x_1917_;
goto v___jp_1911_;
}
else
{
v___y_1919_ = v___y_1925_;
v___y_1920_ = v___y_1926_;
v___y_1921_ = v___y_1927_;
v___y_1922_ = v___y_1928_;
v___y_1923_ = v___y_1929_;
goto v___jp_1918_;
}
}
v___jp_1931_:
{
uint8_t v_emptyType_1938_; 
v_emptyType_1938_ = lean_ctor_get_uint8(v_config_1812_, sizeof(void*)*1 + 1);
if (v_emptyType_1938_ == 0)
{
v___y_1925_ = v___y_1932_;
v___y_1926_ = v___y_1934_;
v___y_1927_ = v___y_1937_;
v___y_1928_ = v___y_1936_;
v___y_1929_ = v___y_1935_;
v___y_1930_ = v___x_1917_;
goto v___jp_1924_;
}
else
{
if (v___y_1933_ == 0)
{
v___y_1919_ = v___y_1932_;
v___y_1920_ = v___y_1934_;
v___y_1921_ = v___y_1937_;
v___y_1922_ = v___y_1936_;
v___y_1923_ = v___y_1935_;
goto v___jp_1918_;
}
else
{
v___y_1925_ = v___y_1932_;
v___y_1926_ = v___y_1934_;
v___y_1927_ = v___y_1937_;
v___y_1928_ = v___y_1936_;
v___y_1929_ = v___y_1935_;
v___y_1930_ = v___x_1917_;
goto v___jp_1924_;
}
}
}
v___jp_1939_:
{
if (v___y_1946_ == 0)
{
v___y_1932_ = v___y_1941_;
v___y_1933_ = v___y_1945_;
v___y_1934_ = v___y_1944_;
v___y_1935_ = v___y_1943_;
v___y_1936_ = v___y_1942_;
v___y_1937_ = v___y_1940_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1947_; 
lean_inc(v_val_1844_);
lean_inc(v_mvarId_1813_);
v___x_1947_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_1813_, v_val_1844_, v___y_1944_, v___y_1943_, v___y_1942_, v___y_1940_);
if (lean_obj_tag(v___x_1947_) == 0)
{
lean_object* v_a_1948_; uint8_t v___x_1949_; 
v_a_1948_ = lean_ctor_get(v___x_1947_, 0);
lean_inc(v_a_1948_);
lean_dec_ref_known(v___x_1947_, 1);
v___x_1949_ = lean_unbox(v_a_1948_);
lean_dec(v_a_1948_);
if (v___x_1949_ == 0)
{
v___y_1932_ = v___y_1941_;
v___y_1933_ = v___y_1945_;
v___y_1934_ = v___y_1944_;
v___y_1935_ = v___y_1943_;
v___y_1936_ = v___y_1942_;
v___y_1937_ = v___y_1940_;
goto v___jp_1931_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
lean_dec(v_val_1844_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v___x_1950_ = lean_box(v___x_1823_);
v___x_1951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1951_, 0, v___x_1950_);
v___x_1952_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v___x_1848_);
v_a_1830_ = v___x_1952_;
goto v___jp_1829_;
}
}
else
{
lean_object* v_a_1953_; lean_object* v___x_1955_; uint8_t v_isShared_1956_; uint8_t v_isSharedCheck_1960_; 
lean_dec(v_val_1844_);
lean_del_object(v___x_1827_);
lean_dec(v_snd_1825_);
lean_dec(v_mvarId_1813_);
lean_dec_ref(v_config_1812_);
v_a_1953_ = lean_ctor_get(v___x_1947_, 0);
v_isSharedCheck_1960_ = !lean_is_exclusive(v___x_1947_);
if (v_isSharedCheck_1960_ == 0)
{
v___x_1955_ = v___x_1947_;
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
else
{
lean_inc(v_a_1953_);
lean_dec(v___x_1947_);
v___x_1955_ = lean_box(0);
v_isShared_1956_ = v_isSharedCheck_1960_;
goto v_resetjp_1954_;
}
v_resetjp_1954_:
{
lean_object* v___x_1958_; 
if (v_isShared_1956_ == 0)
{
v___x_1958_ = v___x_1955_;
goto v_reusejp_1957_;
}
else
{
lean_object* v_reuseFailAlloc_1959_; 
v_reuseFailAlloc_1959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1959_, 0, v_a_1953_);
v___x_1958_ = v_reuseFailAlloc_1959_;
goto v_reusejp_1957_;
}
v_reusejp_1957_:
{
return v___x_1958_;
}
}
}
}
}
}
}
v___jp_1829_:
{
lean_object* v___x_1831_; lean_object* v___x_1833_; 
v___x_1831_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1831_, 0, v_a_1830_);
if (v_isShared_1828_ == 0)
{
lean_ctor_set(v___x_1827_, 0, v___x_1831_);
v___x_1833_ = v___x_1827_;
goto v_reusejp_1832_;
}
else
{
lean_object* v_reuseFailAlloc_1835_; 
v_reuseFailAlloc_1835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1835_, 0, v___x_1831_);
lean_ctor_set(v_reuseFailAlloc_1835_, 1, v_snd_1825_);
v___x_1833_ = v_reuseFailAlloc_1835_;
goto v_reusejp_1832_;
}
v_reusejp_1832_:
{
lean_object* v___x_1834_; 
v___x_1834_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1834_, 0, v___x_1833_);
return v___x_1834_;
}
}
v___jp_1837_:
{
lean_object* v___x_1839_; size_t v___x_1840_; size_t v___x_1841_; 
v___x_1839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1839_, 0, v___x_1836_);
lean_ctor_set(v___x_1839_, 1, v_a_1838_);
v___x_1840_ = ((size_t)1ULL);
v___x_1841_ = lean_usize_add(v_i_1816_, v___x_1840_);
v_i_1816_ = v___x_1841_;
v_b_1817_ = v___x_1839_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___boxed(lean_object* v_config_2477_, lean_object* v_mvarId_2478_, lean_object* v_as_2479_, lean_object* v_sz_2480_, lean_object* v_i_2481_, lean_object* v_b_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_, lean_object* v___y_2487_){
_start:
{
size_t v_sz_boxed_2488_; size_t v_i_boxed_2489_; lean_object* v_res_2490_; 
v_sz_boxed_2488_ = lean_unbox_usize(v_sz_2480_);
lean_dec(v_sz_2480_);
v_i_boxed_2489_ = lean_unbox_usize(v_i_2481_);
lean_dec(v_i_2481_);
v_res_2490_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2477_, v_mvarId_2478_, v_as_2479_, v_sz_boxed_2488_, v_i_boxed_2489_, v_b_2482_, v___y_2483_, v___y_2484_, v___y_2485_, v___y_2486_);
lean_dec(v___y_2486_);
lean_dec_ref(v___y_2485_);
lean_dec(v___y_2484_);
lean_dec_ref(v___y_2483_);
lean_dec_ref(v_as_2479_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(lean_object* v_config_2491_, lean_object* v_mvarId_2492_, lean_object* v_as_2493_, size_t v_sz_2494_, size_t v_i_2495_, lean_object* v_b_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_){
_start:
{
uint8_t v___x_2502_; 
v___x_2502_ = lean_usize_dec_lt(v_i_2495_, v_sz_2494_);
if (v___x_2502_ == 0)
{
lean_object* v___x_2503_; 
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v___x_2503_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2503_, 0, v_b_2496_);
return v___x_2503_;
}
else
{
lean_object* v_snd_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_3154_; 
v_snd_2504_ = lean_ctor_get(v_b_2496_, 1);
v_isSharedCheck_3154_ = !lean_is_exclusive(v_b_2496_);
if (v_isSharedCheck_3154_ == 0)
{
lean_object* v_unused_3155_; 
v_unused_3155_ = lean_ctor_get(v_b_2496_, 0);
lean_dec(v_unused_3155_);
v___x_2506_ = v_b_2496_;
v_isShared_2507_ = v_isSharedCheck_3154_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_snd_2504_);
lean_dec(v_b_2496_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_3154_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v_a_2509_; lean_object* v___x_2515_; lean_object* v_a_2517_; lean_object* v_a_2522_; 
v___x_2515_ = lean_box(0);
v_a_2522_ = lean_array_uget(v_as_2493_, v_i_2495_);
if (lean_obj_tag(v_a_2522_) == 0)
{
lean_del_object(v___x_2506_);
v_a_2517_ = v_snd_2504_;
goto v___jp_2516_;
}
else
{
lean_object* v_val_2523_; lean_object* v___x_2525_; uint8_t v_isShared_2526_; uint8_t v_isSharedCheck_3153_; 
v_val_2523_ = lean_ctor_get(v_a_2522_, 0);
v_isSharedCheck_3153_ = !lean_is_exclusive(v_a_2522_);
if (v_isSharedCheck_3153_ == 0)
{
v___x_2525_ = v_a_2522_;
v_isShared_2526_ = v_isSharedCheck_3153_;
goto v_resetjp_2524_;
}
else
{
lean_inc(v_val_2523_);
lean_dec(v_a_2522_);
v___x_2525_ = lean_box(0);
v_isShared_2526_ = v_isSharedCheck_3153_;
goto v_resetjp_2524_;
}
v_resetjp_2524_:
{
lean_object* v___x_2527_; lean_object* v___y_2529_; lean_object* v___y_2530_; lean_object* v___y_2531_; lean_object* v___y_2532_; lean_object* v___x_2568_; lean_object* v___y_2570_; lean_object* v___y_2571_; lean_object* v___y_2572_; lean_object* v___y_2573_; lean_object* v___y_2591_; lean_object* v___y_2592_; lean_object* v___y_2593_; lean_object* v___y_2594_; uint8_t v___y_2595_; uint8_t v___x_2596_; lean_object* v___y_2598_; lean_object* v___y_2599_; lean_object* v___y_2600_; uint8_t v___y_2601_; lean_object* v___y_2602_; lean_object* v___y_2604_; lean_object* v___y_2605_; lean_object* v___y_2606_; uint8_t v___y_2607_; lean_object* v___y_2608_; uint8_t v___y_2609_; uint8_t v___y_2611_; uint8_t v___y_2612_; lean_object* v___y_2613_; lean_object* v___y_2614_; lean_object* v___y_2615_; lean_object* v___y_2616_; lean_object* v___y_2619_; lean_object* v___y_2620_; lean_object* v___y_2621_; lean_object* v___y_2622_; uint8_t v___y_2623_; uint8_t v___y_2624_; uint8_t v___y_2625_; 
v___x_2527_ = lean_box(0);
v___x_2568_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__0));
v___x_2596_ = l_Lean_LocalDecl_isImplementationDetail(v_val_2523_);
if (v___x_2596_ == 0)
{
lean_object* v___x_2640_; uint8_t v___y_2642_; uint8_t v___y_2643_; lean_object* v___y_2644_; lean_object* v___y_2645_; lean_object* v___y_2646_; lean_object* v___y_2647_; lean_object* v___y_2651_; uint8_t v___y_2652_; lean_object* v___y_2653_; lean_object* v___y_2654_; lean_object* v___y_2655_; uint8_t v___y_2656_; lean_object* v___y_2657_; uint8_t v___y_2658_; lean_object* v___y_2661_; uint8_t v___y_2662_; lean_object* v___y_2663_; lean_object* v___y_2664_; uint8_t v___y_2665_; lean_object* v___y_2666_; lean_object* v_a_2667_; lean_object* v___y_2671_; uint8_t v___y_2672_; lean_object* v___y_2673_; lean_object* v___y_2674_; lean_object* v___y_2675_; uint8_t v___y_2676_; lean_object* v___y_2677_; lean_object* v___y_2678_; lean_object* v___y_2715_; uint8_t v___y_2716_; lean_object* v___y_2717_; lean_object* v___y_2718_; uint8_t v___y_2719_; lean_object* v___y_2720_; lean_object* v___y_2744_; uint8_t v___y_2745_; lean_object* v___y_2746_; lean_object* v___y_2747_; uint8_t v___y_2748_; lean_object* v___y_2749_; uint8_t v___y_2750_; lean_object* v___y_2752_; uint8_t v___y_2753_; lean_object* v___y_2754_; lean_object* v___y_2755_; uint8_t v___y_2756_; lean_object* v___y_2757_; lean_object* v___y_2758_; uint8_t v___y_2759_; lean_object* v___y_2762_; uint8_t v___y_2763_; lean_object* v___y_2764_; lean_object* v___y_2765_; uint8_t v___y_2766_; lean_object* v___y_2767_; uint8_t v___y_2768_; lean_object* v___y_2781_; uint8_t v___y_2782_; lean_object* v___y_2783_; lean_object* v___y_2784_; uint8_t v___y_2785_; lean_object* v___y_2786_; uint8_t v___y_2787_; uint8_t v___y_2789_; uint8_t v_isHEq_2790_; lean_object* v___y_2791_; lean_object* v___y_2792_; lean_object* v___y_2793_; lean_object* v___y_2794_; lean_object* v___y_2798_; uint8_t v___y_2799_; lean_object* v___y_2800_; lean_object* v___y_2801_; lean_object* v___y_2802_; lean_object* v___y_2803_; lean_object* v___y_2804_; uint8_t v_isEq_2860_; lean_object* v___y_2861_; lean_object* v___y_2862_; lean_object* v___y_2863_; lean_object* v___y_2864_; lean_object* v___y_2910_; lean_object* v___y_2911_; lean_object* v___y_2912_; lean_object* v___y_2913_; lean_object* v___y_2956_; lean_object* v___y_2957_; lean_object* v___y_2958_; lean_object* v___y_2959_; lean_object* v___x_3090_; 
v___x_2640_ = l_Lean_LocalDecl_type(v_val_2523_);
lean_inc_ref(v___x_2640_);
v___x_3090_ = l_Lean_Meta_matchNot_x3f(v___x_2640_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_3090_) == 0)
{
lean_object* v_a_3091_; 
v_a_3091_ = lean_ctor_get(v___x_3090_, 0);
lean_inc(v_a_3091_);
lean_dec_ref_known(v___x_3090_, 1);
if (lean_obj_tag(v_a_3091_) == 1)
{
lean_object* v_val_3092_; lean_object* v___x_3093_; 
v_val_3092_ = lean_ctor_get(v_a_3091_, 0);
lean_inc(v_val_3092_);
lean_dec_ref_known(v_a_3091_, 1);
v___x_3093_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3092_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_3093_) == 0)
{
lean_object* v_a_3094_; 
v_a_3094_ = lean_ctor_get(v___x_3093_, 0);
lean_inc(v_a_3094_);
lean_dec_ref_known(v___x_3093_, 1);
if (lean_obj_tag(v_a_3094_) == 1)
{
lean_object* v_val_3095_; lean_object* v___x_3097_; uint8_t v_isShared_3098_; uint8_t v_isSharedCheck_3136_; 
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec_ref(v_config_2491_);
v_val_3095_ = lean_ctor_get(v_a_3094_, 0);
v_isSharedCheck_3136_ = !lean_is_exclusive(v_a_3094_);
if (v_isSharedCheck_3136_ == 0)
{
v___x_3097_ = v_a_3094_;
v_isShared_3098_ = v_isSharedCheck_3136_;
goto v_resetjp_3096_;
}
else
{
lean_inc(v_val_3095_);
lean_dec(v_a_3094_);
v___x_3097_ = lean_box(0);
v_isShared_3098_ = v_isSharedCheck_3136_;
goto v_resetjp_3096_;
}
v_resetjp_3096_:
{
lean_object* v___x_3099_; 
lean_inc(v_mvarId_2492_);
v___x_3099_ = l_Lean_MVarId_getType(v_mvarId_2492_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_3099_) == 0)
{
lean_object* v_a_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; 
v_a_3100_ = lean_ctor_get(v___x_3099_, 0);
lean_inc(v_a_3100_);
lean_dec_ref_known(v___x_3099_, 1);
v___x_3101_ = l_Lean_LocalDecl_toExpr(v_val_2523_);
v___x_3102_ = l_Lean_mkFVar(v_val_3095_);
v___x_3103_ = l_Lean_Expr_app___override(v___x_3101_, v___x_3102_);
v___x_3104_ = l_Lean_Meta_mkFalseElim(v_a_3100_, v___x_3103_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3106_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_a_3105_);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3106_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2492_, v_a_3105_, v___y_2498_);
if (lean_obj_tag(v___x_3106_) == 0)
{
lean_object* v___x_3107_; lean_object* v___x_3109_; 
lean_dec_ref_known(v___x_3106_, 1);
v___x_3107_ = lean_box(v___x_2502_);
if (v_isShared_3098_ == 0)
{
lean_ctor_set(v___x_3097_, 0, v___x_3107_);
v___x_3109_ = v___x_3097_;
goto v_reusejp_3108_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v___x_3107_);
v___x_3109_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3108_;
}
v_reusejp_3108_:
{
lean_object* v___x_3110_; 
v___x_3110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3110_, 0, v___x_3109_);
lean_ctor_set(v___x_3110_, 1, v___x_2527_);
v_a_2509_ = v___x_3110_;
goto v___jp_2508_;
}
}
else
{
lean_object* v_a_3112_; lean_object* v___x_3114_; uint8_t v_isShared_3115_; uint8_t v_isSharedCheck_3119_; 
lean_del_object(v___x_3097_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
v_a_3112_ = lean_ctor_get(v___x_3106_, 0);
v_isSharedCheck_3119_ = !lean_is_exclusive(v___x_3106_);
if (v_isSharedCheck_3119_ == 0)
{
v___x_3114_ = v___x_3106_;
v_isShared_3115_ = v_isSharedCheck_3119_;
goto v_resetjp_3113_;
}
else
{
lean_inc(v_a_3112_);
lean_dec(v___x_3106_);
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
}
else
{
lean_object* v_a_3120_; lean_object* v___x_3122_; uint8_t v_isShared_3123_; uint8_t v_isSharedCheck_3127_; 
lean_del_object(v___x_3097_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_3120_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3127_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3127_ == 0)
{
v___x_3122_ = v___x_3104_;
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
else
{
lean_inc(v_a_3120_);
lean_dec(v___x_3104_);
v___x_3122_ = lean_box(0);
v_isShared_3123_ = v_isSharedCheck_3127_;
goto v_resetjp_3121_;
}
v_resetjp_3121_:
{
lean_object* v___x_3125_; 
if (v_isShared_3123_ == 0)
{
v___x_3125_ = v___x_3122_;
goto v_reusejp_3124_;
}
else
{
lean_object* v_reuseFailAlloc_3126_; 
v_reuseFailAlloc_3126_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3126_, 0, v_a_3120_);
v___x_3125_ = v_reuseFailAlloc_3126_;
goto v_reusejp_3124_;
}
v_reusejp_3124_:
{
return v___x_3125_;
}
}
}
}
else
{
lean_object* v_a_3128_; lean_object* v___x_3130_; uint8_t v_isShared_3131_; uint8_t v_isSharedCheck_3135_; 
lean_del_object(v___x_3097_);
lean_dec(v_val_3095_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_3128_ = lean_ctor_get(v___x_3099_, 0);
v_isSharedCheck_3135_ = !lean_is_exclusive(v___x_3099_);
if (v_isSharedCheck_3135_ == 0)
{
v___x_3130_ = v___x_3099_;
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
else
{
lean_inc(v_a_3128_);
lean_dec(v___x_3099_);
v___x_3130_ = lean_box(0);
v_isShared_3131_ = v_isSharedCheck_3135_;
goto v_resetjp_3129_;
}
v_resetjp_3129_:
{
lean_object* v___x_3133_; 
if (v_isShared_3131_ == 0)
{
v___x_3133_ = v___x_3130_;
goto v_reusejp_3132_;
}
else
{
lean_object* v_reuseFailAlloc_3134_; 
v_reuseFailAlloc_3134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3134_, 0, v_a_3128_);
v___x_3133_ = v_reuseFailAlloc_3134_;
goto v_reusejp_3132_;
}
v_reusejp_3132_:
{
return v___x_3133_;
}
}
}
}
}
else
{
lean_dec(v_a_3094_);
v___y_2956_ = v___y_2497_;
v___y_2957_ = v___y_2498_;
v___y_2958_ = v___y_2499_;
v___y_2959_ = v___y_2500_;
goto v___jp_2955_;
}
}
else
{
lean_object* v_a_3137_; lean_object* v___x_3139_; uint8_t v_isShared_3140_; uint8_t v_isSharedCheck_3144_; 
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_3137_ = lean_ctor_get(v___x_3093_, 0);
v_isSharedCheck_3144_ = !lean_is_exclusive(v___x_3093_);
if (v_isSharedCheck_3144_ == 0)
{
v___x_3139_ = v___x_3093_;
v_isShared_3140_ = v_isSharedCheck_3144_;
goto v_resetjp_3138_;
}
else
{
lean_inc(v_a_3137_);
lean_dec(v___x_3093_);
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
lean_dec(v_a_3091_);
v___y_2956_ = v___y_2497_;
v___y_2957_ = v___y_2498_;
v___y_2958_ = v___y_2499_;
v___y_2959_ = v___y_2500_;
goto v___jp_2955_;
}
}
else
{
lean_object* v_a_3145_; lean_object* v___x_3147_; uint8_t v_isShared_3148_; uint8_t v_isSharedCheck_3152_; 
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_3145_ = lean_ctor_get(v___x_3090_, 0);
v_isSharedCheck_3152_ = !lean_is_exclusive(v___x_3090_);
if (v_isSharedCheck_3152_ == 0)
{
v___x_3147_ = v___x_3090_;
v_isShared_3148_ = v_isSharedCheck_3152_;
goto v_resetjp_3146_;
}
else
{
lean_inc(v_a_3145_);
lean_dec(v___x_3090_);
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
v___jp_2641_:
{
uint8_t v_genDiseq_2648_; 
v_genDiseq_2648_ = lean_ctor_get_uint8(v_config_2491_, sizeof(void*)*1 + 2);
if (v_genDiseq_2648_ == 0)
{
lean_dec_ref(v___x_2640_);
v___y_2619_ = v___y_2647_;
v___y_2620_ = v___y_2646_;
v___y_2621_ = v___y_2645_;
v___y_2622_ = v___y_2644_;
v___y_2623_ = v___y_2642_;
v___y_2624_ = v___y_2643_;
v___y_2625_ = v___x_2596_;
goto v___jp_2618_;
}
else
{
uint8_t v___x_2649_; 
v___x_2649_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_2640_);
v___y_2619_ = v___y_2647_;
v___y_2620_ = v___y_2646_;
v___y_2621_ = v___y_2645_;
v___y_2622_ = v___y_2644_;
v___y_2623_ = v___y_2642_;
v___y_2624_ = v___y_2643_;
v___y_2625_ = v___x_2649_;
goto v___jp_2618_;
}
}
v___jp_2650_:
{
if (v___y_2658_ == 0)
{
lean_dec_ref(v___y_2654_);
v___y_2642_ = v___y_2652_;
v___y_2643_ = v___y_2656_;
v___y_2644_ = v___y_2651_;
v___y_2645_ = v___y_2653_;
v___y_2646_ = v___y_2655_;
v___y_2647_ = v___y_2657_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2659_; 
lean_dec_ref(v___x_2640_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v___x_2659_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2659_, 0, v___y_2654_);
return v___x_2659_;
}
}
v___jp_2660_:
{
uint8_t v___x_2668_; 
v___x_2668_ = l_Lean_Exception_isInterrupt(v_a_2667_);
if (v___x_2668_ == 0)
{
uint8_t v___x_2669_; 
lean_inc_ref(v_a_2667_);
v___x_2669_ = l_Lean_Exception_isRuntime(v_a_2667_);
v___y_2651_ = v___y_2661_;
v___y_2652_ = v___y_2662_;
v___y_2653_ = v___y_2663_;
v___y_2654_ = v_a_2667_;
v___y_2655_ = v___y_2664_;
v___y_2656_ = v___y_2665_;
v___y_2657_ = v___y_2666_;
v___y_2658_ = v___x_2669_;
goto v___jp_2650_;
}
else
{
v___y_2651_ = v___y_2661_;
v___y_2652_ = v___y_2662_;
v___y_2653_ = v___y_2663_;
v___y_2654_ = v_a_2667_;
v___y_2655_ = v___y_2664_;
v___y_2656_ = v___y_2665_;
v___y_2657_ = v___y_2666_;
v___y_2658_ = v___x_2668_;
goto v___jp_2650_;
}
}
v___jp_2670_:
{
if (lean_obj_tag(v___y_2678_) == 0)
{
lean_object* v_a_2679_; lean_object* v___x_2680_; uint8_t v___x_2681_; 
v_a_2679_ = lean_ctor_get(v___y_2678_, 0);
lean_inc(v_a_2679_);
lean_dec_ref_known(v___y_2678_, 1);
v___x_2680_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_2681_ = l_Lean_Expr_isConstOf(v_a_2679_, v___x_2680_);
lean_dec(v_a_2679_);
if (v___x_2681_ == 0)
{
lean_dec_ref(v___y_2674_);
v___y_2642_ = v___y_2672_;
v___y_2643_ = v___y_2676_;
v___y_2644_ = v___y_2671_;
v___y_2645_ = v___y_2673_;
v___y_2646_ = v___y_2675_;
v___y_2647_ = v___y_2677_;
goto v___jp_2641_;
}
else
{
lean_object* v___x_2682_; 
lean_inc_ref(v___y_2674_);
v___x_2682_ = l_Lean_Meta_mkEqRefl(v___y_2674_, v___y_2671_, v___y_2673_, v___y_2675_, v___y_2677_);
if (lean_obj_tag(v___x_2682_) == 0)
{
lean_object* v_a_2683_; lean_object* v___x_2684_; lean_object* v_dummy_2685_; lean_object* v_nargs_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; 
v_a_2683_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2683_);
lean_dec_ref_known(v___x_2682_, 1);
v___x_2684_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_2685_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_2686_ = l_Lean_Expr_getAppNumArgs(v___y_2674_);
lean_inc(v_nargs_2686_);
v___x_2687_ = lean_mk_array(v_nargs_2686_, v_dummy_2685_);
v___x_2688_ = lean_unsigned_to_nat(1u);
v___x_2689_ = lean_nat_sub(v_nargs_2686_, v___x_2688_);
lean_dec(v_nargs_2686_);
v___x_2690_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_2674_, v___x_2687_, v___x_2689_);
v___x_2691_ = lean_array_push(v___x_2690_, v_a_2683_);
v___x_2692_ = l_Lean_mkAppN(v___x_2684_, v___x_2691_);
lean_dec_ref(v___x_2691_);
lean_inc(v_mvarId_2492_);
v___x_2693_ = l_Lean_MVarId_getType(v_mvarId_2492_, v___y_2671_, v___y_2673_, v___y_2675_, v___y_2677_);
if (lean_obj_tag(v___x_2693_) == 0)
{
lean_object* v_a_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v_a_2694_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2694_);
lean_dec_ref_known(v___x_2693_, 1);
lean_inc(v_val_2523_);
v___x_2695_ = l_Lean_LocalDecl_toExpr(v_val_2523_);
v___x_2696_ = l_Lean_Meta_mkAbsurd(v_a_2694_, v___x_2695_, v___x_2692_, v___y_2671_, v___y_2673_, v___y_2675_, v___y_2677_);
if (lean_obj_tag(v___x_2696_) == 0)
{
lean_object* v_a_2697_; lean_object* v___x_2698_; 
v_a_2697_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2697_);
lean_dec_ref_known(v___x_2696_, 1);
lean_inc(v_mvarId_2492_);
v___x_2698_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2492_, v_a_2697_, v___y_2673_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v___x_2700_; uint8_t v_isShared_2701_; uint8_t v_isSharedCheck_2707_; 
lean_dec_ref(v___x_2640_);
lean_dec(v_val_2523_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_isSharedCheck_2707_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2707_ == 0)
{
lean_object* v_unused_2708_; 
v_unused_2708_ = lean_ctor_get(v___x_2698_, 0);
lean_dec(v_unused_2708_);
v___x_2700_ = v___x_2698_;
v_isShared_2701_ = v_isSharedCheck_2707_;
goto v_resetjp_2699_;
}
else
{
lean_dec(v___x_2698_);
v___x_2700_ = lean_box(0);
v_isShared_2701_ = v_isSharedCheck_2707_;
goto v_resetjp_2699_;
}
v_resetjp_2699_:
{
lean_object* v___x_2702_; lean_object* v___x_2704_; 
v___x_2702_ = lean_box(v___x_2502_);
if (v_isShared_2701_ == 0)
{
lean_ctor_set_tag(v___x_2700_, 1);
lean_ctor_set(v___x_2700_, 0, v___x_2702_);
v___x_2704_ = v___x_2700_;
goto v_reusejp_2703_;
}
else
{
lean_object* v_reuseFailAlloc_2706_; 
v_reuseFailAlloc_2706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___x_2702_);
v___x_2704_ = v_reuseFailAlloc_2706_;
goto v_reusejp_2703_;
}
v_reusejp_2703_:
{
lean_object* v___x_2705_; 
v___x_2705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2704_);
lean_ctor_set(v___x_2705_, 1, v___x_2527_);
v_a_2509_ = v___x_2705_;
goto v___jp_2508_;
}
}
}
else
{
lean_object* v_a_2709_; 
v_a_2709_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2709_);
lean_dec_ref_known(v___x_2698_, 1);
v___y_2661_ = v___y_2671_;
v___y_2662_ = v___y_2672_;
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2675_;
v___y_2665_ = v___y_2676_;
v___y_2666_ = v___y_2677_;
v_a_2667_ = v_a_2709_;
goto v___jp_2660_;
}
}
else
{
lean_object* v_a_2710_; 
v_a_2710_ = lean_ctor_get(v___x_2696_, 0);
lean_inc(v_a_2710_);
lean_dec_ref_known(v___x_2696_, 1);
v___y_2661_ = v___y_2671_;
v___y_2662_ = v___y_2672_;
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2675_;
v___y_2665_ = v___y_2676_;
v___y_2666_ = v___y_2677_;
v_a_2667_ = v_a_2710_;
goto v___jp_2660_;
}
}
else
{
lean_object* v_a_2711_; 
lean_dec_ref(v___x_2692_);
v_a_2711_ = lean_ctor_get(v___x_2693_, 0);
lean_inc(v_a_2711_);
lean_dec_ref_known(v___x_2693_, 1);
v___y_2661_ = v___y_2671_;
v___y_2662_ = v___y_2672_;
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2675_;
v___y_2665_ = v___y_2676_;
v___y_2666_ = v___y_2677_;
v_a_2667_ = v_a_2711_;
goto v___jp_2660_;
}
}
else
{
lean_object* v_a_2712_; 
lean_dec_ref(v___y_2674_);
v_a_2712_ = lean_ctor_get(v___x_2682_, 0);
lean_inc(v_a_2712_);
lean_dec_ref_known(v___x_2682_, 1);
v___y_2661_ = v___y_2671_;
v___y_2662_ = v___y_2672_;
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2675_;
v___y_2665_ = v___y_2676_;
v___y_2666_ = v___y_2677_;
v_a_2667_ = v_a_2712_;
goto v___jp_2660_;
}
}
}
else
{
lean_object* v_a_2713_; 
lean_dec_ref(v___y_2674_);
v_a_2713_ = lean_ctor_get(v___y_2678_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___y_2678_, 1);
v___y_2661_ = v___y_2671_;
v___y_2662_ = v___y_2672_;
v___y_2663_ = v___y_2673_;
v___y_2664_ = v___y_2675_;
v___y_2665_ = v___y_2676_;
v___y_2666_ = v___y_2677_;
v_a_2667_ = v_a_2713_;
goto v___jp_2660_;
}
}
v___jp_2714_:
{
lean_object* v___x_2721_; 
lean_inc_ref(v___x_2640_);
v___x_2721_ = l_Lean_Meta_mkDecide(v___x_2640_, v___y_2715_, v___y_2717_, v___y_2718_, v___y_2720_);
if (lean_obj_tag(v___x_2721_) == 0)
{
lean_object* v_a_2722_; lean_object* v___x_2723_; uint8_t v_transparency_2724_; uint8_t v___x_2725_; uint8_t v___x_2726_; 
v_a_2722_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2722_);
lean_dec_ref_known(v___x_2721_, 1);
v___x_2723_ = l_Lean_Meta_Context_config(v___y_2715_);
v_transparency_2724_ = lean_ctor_get_uint8(v___x_2723_, 9);
lean_dec_ref(v___x_2723_);
v___x_2725_ = 1;
v___x_2726_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_2724_, v___x_2725_);
if (v___x_2726_ == 0)
{
lean_object* v_keyedConfig_2727_; uint8_t v_trackZetaDelta_2728_; lean_object* v_zetaDeltaSet_2729_; lean_object* v_lctx_2730_; lean_object* v_localInstances_2731_; lean_object* v_defEqCtx_x3f_2732_; lean_object* v_synthPendingDepth_2733_; lean_object* v_customCanUnfoldPredicate_x3f_2734_; uint8_t v_univApprox_2735_; uint8_t v_inTypeClassResolution_2736_; uint8_t v_cacheInferType_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; 
v_keyedConfig_2727_ = lean_ctor_get(v___y_2715_, 0);
v_trackZetaDelta_2728_ = lean_ctor_get_uint8(v___y_2715_, sizeof(void*)*7);
v_zetaDeltaSet_2729_ = lean_ctor_get(v___y_2715_, 1);
v_lctx_2730_ = lean_ctor_get(v___y_2715_, 2);
v_localInstances_2731_ = lean_ctor_get(v___y_2715_, 3);
v_defEqCtx_x3f_2732_ = lean_ctor_get(v___y_2715_, 4);
v_synthPendingDepth_2733_ = lean_ctor_get(v___y_2715_, 5);
v_customCanUnfoldPredicate_x3f_2734_ = lean_ctor_get(v___y_2715_, 6);
v_univApprox_2735_ = lean_ctor_get_uint8(v___y_2715_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_2736_ = lean_ctor_get_uint8(v___y_2715_, sizeof(void*)*7 + 2);
v_cacheInferType_2737_ = lean_ctor_get_uint8(v___y_2715_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_2727_);
v___x_2738_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_2725_, v_keyedConfig_2727_);
lean_inc(v_customCanUnfoldPredicate_x3f_2734_);
lean_inc(v_synthPendingDepth_2733_);
lean_inc(v_defEqCtx_x3f_2732_);
lean_inc_ref(v_localInstances_2731_);
lean_inc_ref(v_lctx_2730_);
lean_inc(v_zetaDeltaSet_2729_);
v___x_2739_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
lean_ctor_set(v___x_2739_, 1, v_zetaDeltaSet_2729_);
lean_ctor_set(v___x_2739_, 2, v_lctx_2730_);
lean_ctor_set(v___x_2739_, 3, v_localInstances_2731_);
lean_ctor_set(v___x_2739_, 4, v_defEqCtx_x3f_2732_);
lean_ctor_set(v___x_2739_, 5, v_synthPendingDepth_2733_);
lean_ctor_set(v___x_2739_, 6, v_customCanUnfoldPredicate_x3f_2734_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*7, v_trackZetaDelta_2728_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*7 + 1, v_univApprox_2735_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*7 + 2, v_inTypeClassResolution_2736_);
lean_ctor_set_uint8(v___x_2739_, sizeof(void*)*7 + 3, v_cacheInferType_2737_);
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc(v_a_2722_);
v___x_2740_ = lean_whnf(v_a_2722_, v___x_2739_, v___y_2717_, v___y_2718_, v___y_2720_);
v___y_2671_ = v___y_2715_;
v___y_2672_ = v___y_2716_;
v___y_2673_ = v___y_2717_;
v___y_2674_ = v_a_2722_;
v___y_2675_ = v___y_2718_;
v___y_2676_ = v___y_2719_;
v___y_2677_ = v___y_2720_;
v___y_2678_ = v___x_2740_;
goto v___jp_2670_;
}
else
{
lean_object* v___x_2741_; 
lean_inc(v___y_2720_);
lean_inc_ref(v___y_2718_);
lean_inc(v___y_2717_);
lean_inc_ref(v___y_2715_);
lean_inc(v_a_2722_);
v___x_2741_ = lean_whnf(v_a_2722_, v___y_2715_, v___y_2717_, v___y_2718_, v___y_2720_);
v___y_2671_ = v___y_2715_;
v___y_2672_ = v___y_2716_;
v___y_2673_ = v___y_2717_;
v___y_2674_ = v_a_2722_;
v___y_2675_ = v___y_2718_;
v___y_2676_ = v___y_2719_;
v___y_2677_ = v___y_2720_;
v___y_2678_ = v___x_2741_;
goto v___jp_2670_;
}
}
else
{
lean_object* v_a_2742_; 
v_a_2742_ = lean_ctor_get(v___x_2721_, 0);
lean_inc(v_a_2742_);
lean_dec_ref_known(v___x_2721_, 1);
v___y_2661_ = v___y_2715_;
v___y_2662_ = v___y_2716_;
v___y_2663_ = v___y_2717_;
v___y_2664_ = v___y_2718_;
v___y_2665_ = v___y_2719_;
v___y_2666_ = v___y_2720_;
v_a_2667_ = v_a_2742_;
goto v___jp_2660_;
}
}
v___jp_2743_:
{
if (v___y_2750_ == 0)
{
v___y_2642_ = v___y_2745_;
v___y_2643_ = v___y_2748_;
v___y_2644_ = v___y_2744_;
v___y_2645_ = v___y_2746_;
v___y_2646_ = v___y_2747_;
v___y_2647_ = v___y_2749_;
goto v___jp_2641_;
}
else
{
v___y_2715_ = v___y_2744_;
v___y_2716_ = v___y_2745_;
v___y_2717_ = v___y_2746_;
v___y_2718_ = v___y_2747_;
v___y_2719_ = v___y_2748_;
v___y_2720_ = v___y_2749_;
goto v___jp_2714_;
}
}
v___jp_2751_:
{
if (v___y_2759_ == 0)
{
lean_dec_ref(v___y_2757_);
v___y_2744_ = v___y_2752_;
v___y_2745_ = v___y_2753_;
v___y_2746_ = v___y_2754_;
v___y_2747_ = v___y_2755_;
v___y_2748_ = v___y_2756_;
v___y_2749_ = v___y_2758_;
v___y_2750_ = v___x_2596_;
goto v___jp_2743_;
}
else
{
uint8_t v___x_2760_; 
v___x_2760_ = l_Lean_Expr_hasFVar(v___y_2757_);
lean_dec_ref(v___y_2757_);
if (v___x_2760_ == 0)
{
v___y_2715_ = v___y_2752_;
v___y_2716_ = v___y_2753_;
v___y_2717_ = v___y_2754_;
v___y_2718_ = v___y_2755_;
v___y_2719_ = v___y_2756_;
v___y_2720_ = v___y_2758_;
goto v___jp_2714_;
}
else
{
v___y_2744_ = v___y_2752_;
v___y_2745_ = v___y_2753_;
v___y_2746_ = v___y_2754_;
v___y_2747_ = v___y_2755_;
v___y_2748_ = v___y_2756_;
v___y_2749_ = v___y_2758_;
v___y_2750_ = v___x_2596_;
goto v___jp_2743_;
}
}
}
v___jp_2761_:
{
lean_object* v___x_2769_; 
lean_inc_ref(v___x_2640_);
v___x_2769_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_2640_, v___y_2764_);
if (lean_obj_tag(v___x_2769_) == 0)
{
lean_object* v_a_2770_; uint8_t v___x_2771_; 
v_a_2770_ = lean_ctor_get(v___x_2769_, 0);
lean_inc(v_a_2770_);
lean_dec_ref_known(v___x_2769_, 1);
v___x_2771_ = l_Lean_Expr_hasMVar(v_a_2770_);
if (v___x_2771_ == 0)
{
v___y_2752_ = v___y_2762_;
v___y_2753_ = v___y_2763_;
v___y_2754_ = v___y_2764_;
v___y_2755_ = v___y_2765_;
v___y_2756_ = v___y_2766_;
v___y_2757_ = v_a_2770_;
v___y_2758_ = v___y_2767_;
v___y_2759_ = v___y_2768_;
goto v___jp_2751_;
}
else
{
v___y_2752_ = v___y_2762_;
v___y_2753_ = v___y_2763_;
v___y_2754_ = v___y_2764_;
v___y_2755_ = v___y_2765_;
v___y_2756_ = v___y_2766_;
v___y_2757_ = v_a_2770_;
v___y_2758_ = v___y_2767_;
v___y_2759_ = v___x_2596_;
goto v___jp_2751_;
}
}
else
{
lean_object* v_a_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2779_; 
lean_dec_ref(v___x_2640_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_2772_ = lean_ctor_get(v___x_2769_, 0);
v_isSharedCheck_2779_ = !lean_is_exclusive(v___x_2769_);
if (v_isSharedCheck_2779_ == 0)
{
v___x_2774_ = v___x_2769_;
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_a_2772_);
lean_dec(v___x_2769_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2779_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2777_; 
if (v_isShared_2775_ == 0)
{
v___x_2777_ = v___x_2774_;
goto v_reusejp_2776_;
}
else
{
lean_object* v_reuseFailAlloc_2778_; 
v_reuseFailAlloc_2778_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2778_, 0, v_a_2772_);
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
v___jp_2780_:
{
if (v___y_2787_ == 0)
{
v___y_2642_ = v___y_2782_;
v___y_2643_ = v___y_2785_;
v___y_2644_ = v___y_2781_;
v___y_2645_ = v___y_2783_;
v___y_2646_ = v___y_2784_;
v___y_2647_ = v___y_2786_;
goto v___jp_2641_;
}
else
{
v___y_2762_ = v___y_2781_;
v___y_2763_ = v___y_2782_;
v___y_2764_ = v___y_2783_;
v___y_2765_ = v___y_2784_;
v___y_2766_ = v___y_2785_;
v___y_2767_ = v___y_2786_;
v___y_2768_ = v___y_2787_;
goto v___jp_2761_;
}
}
v___jp_2788_:
{
uint8_t v_useDecide_2795_; 
v_useDecide_2795_ = lean_ctor_get_uint8(v_config_2491_, sizeof(void*)*1);
if (v_useDecide_2795_ == 0)
{
v___y_2781_ = v___y_2791_;
v___y_2782_ = v___y_2789_;
v___y_2783_ = v___y_2792_;
v___y_2784_ = v___y_2793_;
v___y_2785_ = v_isHEq_2790_;
v___y_2786_ = v___y_2794_;
v___y_2787_ = v___x_2596_;
goto v___jp_2780_;
}
else
{
uint8_t v___x_2796_; 
v___x_2796_ = l_Lean_Expr_hasFVar(v___x_2640_);
if (v___x_2796_ == 0)
{
v___y_2762_ = v___y_2791_;
v___y_2763_ = v___y_2789_;
v___y_2764_ = v___y_2792_;
v___y_2765_ = v___y_2793_;
v___y_2766_ = v_isHEq_2790_;
v___y_2767_ = v___y_2794_;
v___y_2768_ = v_useDecide_2795_;
goto v___jp_2761_;
}
else
{
v___y_2781_ = v___y_2791_;
v___y_2782_ = v___y_2789_;
v___y_2783_ = v___y_2792_;
v___y_2784_ = v___y_2793_;
v___y_2785_ = v_isHEq_2790_;
v___y_2786_ = v___y_2794_;
v___y_2787_ = v___x_2596_;
goto v___jp_2780_;
}
}
}
v___jp_2797_:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lean_Meta_isExprDefEq(v___y_2804_, v___y_2800_, v___y_2798_, v___y_2801_, v___y_2803_, v___y_2802_);
if (lean_obj_tag(v___x_2805_) == 0)
{
lean_object* v_a_2806_; uint8_t v___x_2807_; 
v_a_2806_ = lean_ctor_get(v___x_2805_, 0);
lean_inc(v_a_2806_);
lean_dec_ref_known(v___x_2805_, 1);
v___x_2807_ = lean_unbox(v_a_2806_);
lean_dec(v_a_2806_);
if (v___x_2807_ == 0)
{
v___y_2789_ = v___y_2799_;
v_isHEq_2790_ = v___x_2502_;
v___y_2791_ = v___y_2798_;
v___y_2792_ = v___y_2801_;
v___y_2793_ = v___y_2803_;
v___y_2794_ = v___y_2802_;
goto v___jp_2788_;
}
else
{
lean_object* v___x_2808_; 
lean_dec_ref(v___x_2640_);
lean_dec_ref(v_config_2491_);
lean_inc(v_mvarId_2492_);
v___x_2808_ = l_Lean_MVarId_getType(v_mvarId_2492_, v___y_2798_, v___y_2801_, v___y_2803_, v___y_2802_);
if (lean_obj_tag(v___x_2808_) == 0)
{
lean_object* v_a_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; 
v_a_2809_ = lean_ctor_get(v___x_2808_, 0);
lean_inc(v_a_2809_);
lean_dec_ref_known(v___x_2808_, 1);
v___x_2810_ = l_Lean_LocalDecl_toExpr(v_val_2523_);
v___x_2811_ = l_Lean_Meta_mkEqOfHEq(v___x_2810_, v___x_2502_, v___y_2798_, v___y_2801_, v___y_2803_, v___y_2802_);
if (lean_obj_tag(v___x_2811_) == 0)
{
lean_object* v_a_2812_; lean_object* v___x_2813_; 
v_a_2812_ = lean_ctor_get(v___x_2811_, 0);
lean_inc(v_a_2812_);
lean_dec_ref_known(v___x_2811_, 1);
v___x_2813_ = l_Lean_Meta_mkNoConfusion(v_a_2809_, v_a_2812_, v___y_2798_, v___y_2801_, v___y_2803_, v___y_2802_);
if (lean_obj_tag(v___x_2813_) == 0)
{
lean_object* v_a_2814_; lean_object* v___x_2815_; 
v_a_2814_ = lean_ctor_get(v___x_2813_, 0);
lean_inc(v_a_2814_);
lean_dec_ref_known(v___x_2813_, 1);
v___x_2815_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2492_, v_a_2814_, v___y_2801_);
if (lean_obj_tag(v___x_2815_) == 0)
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
lean_dec_ref_known(v___x_2815_, 1);
v___x_2816_ = lean_box(v___x_2502_);
v___x_2817_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2816_);
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v___x_2527_);
v_a_2509_ = v___x_2818_;
goto v___jp_2508_;
}
else
{
lean_object* v_a_2819_; lean_object* v___x_2821_; uint8_t v_isShared_2822_; uint8_t v_isSharedCheck_2826_; 
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
v_a_2819_ = lean_ctor_get(v___x_2815_, 0);
v_isSharedCheck_2826_ = !lean_is_exclusive(v___x_2815_);
if (v_isSharedCheck_2826_ == 0)
{
v___x_2821_ = v___x_2815_;
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
else
{
lean_inc(v_a_2819_);
lean_dec(v___x_2815_);
v___x_2821_ = lean_box(0);
v_isShared_2822_ = v_isSharedCheck_2826_;
goto v_resetjp_2820_;
}
v_resetjp_2820_:
{
lean_object* v___x_2824_; 
if (v_isShared_2822_ == 0)
{
v___x_2824_ = v___x_2821_;
goto v_reusejp_2823_;
}
else
{
lean_object* v_reuseFailAlloc_2825_; 
v_reuseFailAlloc_2825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2825_, 0, v_a_2819_);
v___x_2824_ = v_reuseFailAlloc_2825_;
goto v_reusejp_2823_;
}
v_reusejp_2823_:
{
return v___x_2824_;
}
}
}
}
else
{
lean_object* v_a_2827_; lean_object* v___x_2829_; uint8_t v_isShared_2830_; uint8_t v_isSharedCheck_2834_; 
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_2827_ = lean_ctor_get(v___x_2813_, 0);
v_isSharedCheck_2834_ = !lean_is_exclusive(v___x_2813_);
if (v_isSharedCheck_2834_ == 0)
{
v___x_2829_ = v___x_2813_;
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
else
{
lean_inc(v_a_2827_);
lean_dec(v___x_2813_);
v___x_2829_ = lean_box(0);
v_isShared_2830_ = v_isSharedCheck_2834_;
goto v_resetjp_2828_;
}
v_resetjp_2828_:
{
lean_object* v___x_2832_; 
if (v_isShared_2830_ == 0)
{
v___x_2832_ = v___x_2829_;
goto v_reusejp_2831_;
}
else
{
lean_object* v_reuseFailAlloc_2833_; 
v_reuseFailAlloc_2833_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2833_, 0, v_a_2827_);
v___x_2832_ = v_reuseFailAlloc_2833_;
goto v_reusejp_2831_;
}
v_reusejp_2831_:
{
return v___x_2832_;
}
}
}
}
else
{
lean_object* v_a_2835_; lean_object* v___x_2837_; uint8_t v_isShared_2838_; uint8_t v_isSharedCheck_2842_; 
lean_dec(v_a_2809_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_2835_ = lean_ctor_get(v___x_2811_, 0);
v_isSharedCheck_2842_ = !lean_is_exclusive(v___x_2811_);
if (v_isSharedCheck_2842_ == 0)
{
v___x_2837_ = v___x_2811_;
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
else
{
lean_inc(v_a_2835_);
lean_dec(v___x_2811_);
v___x_2837_ = lean_box(0);
v_isShared_2838_ = v_isSharedCheck_2842_;
goto v_resetjp_2836_;
}
v_resetjp_2836_:
{
lean_object* v___x_2840_; 
if (v_isShared_2838_ == 0)
{
v___x_2840_ = v___x_2837_;
goto v_reusejp_2839_;
}
else
{
lean_object* v_reuseFailAlloc_2841_; 
v_reuseFailAlloc_2841_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2841_, 0, v_a_2835_);
v___x_2840_ = v_reuseFailAlloc_2841_;
goto v_reusejp_2839_;
}
v_reusejp_2839_:
{
return v___x_2840_;
}
}
}
}
else
{
lean_object* v_a_2843_; lean_object* v___x_2845_; uint8_t v_isShared_2846_; uint8_t v_isSharedCheck_2850_; 
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_2843_ = lean_ctor_get(v___x_2808_, 0);
v_isSharedCheck_2850_ = !lean_is_exclusive(v___x_2808_);
if (v_isSharedCheck_2850_ == 0)
{
v___x_2845_ = v___x_2808_;
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
else
{
lean_inc(v_a_2843_);
lean_dec(v___x_2808_);
v___x_2845_ = lean_box(0);
v_isShared_2846_ = v_isSharedCheck_2850_;
goto v_resetjp_2844_;
}
v_resetjp_2844_:
{
lean_object* v___x_2848_; 
if (v_isShared_2846_ == 0)
{
v___x_2848_ = v___x_2845_;
goto v_reusejp_2847_;
}
else
{
lean_object* v_reuseFailAlloc_2849_; 
v_reuseFailAlloc_2849_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2849_, 0, v_a_2843_);
v___x_2848_ = v_reuseFailAlloc_2849_;
goto v_reusejp_2847_;
}
v_reusejp_2847_:
{
return v___x_2848_;
}
}
}
}
}
else
{
lean_object* v_a_2851_; lean_object* v___x_2853_; uint8_t v_isShared_2854_; uint8_t v_isSharedCheck_2858_; 
lean_dec_ref(v___x_2640_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_2851_ = lean_ctor_get(v___x_2805_, 0);
v_isSharedCheck_2858_ = !lean_is_exclusive(v___x_2805_);
if (v_isSharedCheck_2858_ == 0)
{
v___x_2853_ = v___x_2805_;
v_isShared_2854_ = v_isSharedCheck_2858_;
goto v_resetjp_2852_;
}
else
{
lean_inc(v_a_2851_);
lean_dec(v___x_2805_);
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
v___jp_2859_:
{
lean_object* v___x_2865_; 
lean_inc_ref(v___x_2640_);
v___x_2865_ = l_Lean_Meta_matchHEq_x3f(v___x_2640_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
lean_inc(v_a_2866_);
lean_dec_ref_known(v___x_2865_, 1);
if (lean_obj_tag(v_a_2866_) == 1)
{
lean_object* v_val_2867_; lean_object* v_snd_2868_; lean_object* v_snd_2869_; lean_object* v_fst_2870_; lean_object* v_fst_2871_; lean_object* v_fst_2872_; lean_object* v_snd_2873_; lean_object* v___x_2874_; 
v_val_2867_ = lean_ctor_get(v_a_2866_, 0);
lean_inc(v_val_2867_);
lean_dec_ref_known(v_a_2866_, 1);
v_snd_2868_ = lean_ctor_get(v_val_2867_, 1);
lean_inc(v_snd_2868_);
v_snd_2869_ = lean_ctor_get(v_snd_2868_, 1);
lean_inc(v_snd_2869_);
v_fst_2870_ = lean_ctor_get(v_val_2867_, 0);
lean_inc(v_fst_2870_);
lean_dec(v_val_2867_);
v_fst_2871_ = lean_ctor_get(v_snd_2868_, 0);
lean_inc(v_fst_2871_);
lean_dec(v_snd_2868_);
v_fst_2872_ = lean_ctor_get(v_snd_2869_, 0);
lean_inc(v_fst_2872_);
v_snd_2873_ = lean_ctor_get(v_snd_2869_, 1);
lean_inc(v_snd_2873_);
lean_dec(v_snd_2869_);
v___x_2874_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2871_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2874_) == 0)
{
lean_object* v_a_2875_; 
v_a_2875_ = lean_ctor_get(v___x_2874_, 0);
lean_inc(v_a_2875_);
lean_dec_ref_known(v___x_2874_, 1);
if (lean_obj_tag(v_a_2875_) == 1)
{
lean_object* v_val_2876_; lean_object* v___x_2877_; 
v_val_2876_ = lean_ctor_get(v_a_2875_, 0);
lean_inc(v_val_2876_);
lean_dec_ref_known(v_a_2875_, 1);
v___x_2877_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2873_, v___y_2861_, v___y_2862_, v___y_2863_, v___y_2864_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
if (lean_obj_tag(v_a_2878_) == 1)
{
lean_object* v_toConstantVal_2879_; lean_object* v_val_2880_; lean_object* v_toConstantVal_2881_; lean_object* v_name_2882_; lean_object* v_name_2883_; uint8_t v___x_2884_; 
v_toConstantVal_2879_ = lean_ctor_get(v_val_2876_, 0);
lean_inc_ref(v_toConstantVal_2879_);
lean_dec(v_val_2876_);
v_val_2880_ = lean_ctor_get(v_a_2878_, 0);
lean_inc(v_val_2880_);
lean_dec_ref_known(v_a_2878_, 1);
v_toConstantVal_2881_ = lean_ctor_get(v_val_2880_, 0);
lean_inc_ref(v_toConstantVal_2881_);
lean_dec(v_val_2880_);
v_name_2882_ = lean_ctor_get(v_toConstantVal_2879_, 0);
lean_inc(v_name_2882_);
lean_dec_ref(v_toConstantVal_2879_);
v_name_2883_ = lean_ctor_get(v_toConstantVal_2881_, 0);
lean_inc(v_name_2883_);
lean_dec_ref(v_toConstantVal_2881_);
v___x_2884_ = lean_name_eq(v_name_2882_, v_name_2883_);
lean_dec(v_name_2883_);
lean_dec(v_name_2882_);
if (v___x_2884_ == 0)
{
v___y_2798_ = v___y_2861_;
v___y_2799_ = v_isEq_2860_;
v___y_2800_ = v_fst_2872_;
v___y_2801_ = v___y_2862_;
v___y_2802_ = v___y_2864_;
v___y_2803_ = v___y_2863_;
v___y_2804_ = v_fst_2870_;
goto v___jp_2797_;
}
else
{
if (v___x_2596_ == 0)
{
lean_dec(v_fst_2872_);
lean_dec(v_fst_2870_);
v___y_2789_ = v_isEq_2860_;
v_isHEq_2790_ = v___x_2502_;
v___y_2791_ = v___y_2861_;
v___y_2792_ = v___y_2862_;
v___y_2793_ = v___y_2863_;
v___y_2794_ = v___y_2864_;
goto v___jp_2788_;
}
else
{
v___y_2798_ = v___y_2861_;
v___y_2799_ = v_isEq_2860_;
v___y_2800_ = v_fst_2872_;
v___y_2801_ = v___y_2862_;
v___y_2802_ = v___y_2864_;
v___y_2803_ = v___y_2863_;
v___y_2804_ = v_fst_2870_;
goto v___jp_2797_;
}
}
}
else
{
lean_dec(v_a_2878_);
lean_dec(v_val_2876_);
lean_dec(v_fst_2872_);
lean_dec(v_fst_2870_);
v___y_2789_ = v_isEq_2860_;
v_isHEq_2790_ = v___x_2502_;
v___y_2791_ = v___y_2861_;
v___y_2792_ = v___y_2862_;
v___y_2793_ = v___y_2863_;
v___y_2794_ = v___y_2864_;
goto v___jp_2788_;
}
}
else
{
lean_object* v_a_2885_; lean_object* v___x_2887_; uint8_t v_isShared_2888_; uint8_t v_isSharedCheck_2892_; 
lean_dec(v_val_2876_);
lean_dec(v_fst_2872_);
lean_dec(v_fst_2870_);
lean_dec_ref(v___x_2640_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_2885_ = lean_ctor_get(v___x_2877_, 0);
v_isSharedCheck_2892_ = !lean_is_exclusive(v___x_2877_);
if (v_isSharedCheck_2892_ == 0)
{
v___x_2887_ = v___x_2877_;
v_isShared_2888_ = v_isSharedCheck_2892_;
goto v_resetjp_2886_;
}
else
{
lean_inc(v_a_2885_);
lean_dec(v___x_2877_);
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
lean_dec(v_a_2875_);
lean_dec(v_snd_2873_);
lean_dec(v_fst_2872_);
lean_dec(v_fst_2870_);
v___y_2789_ = v_isEq_2860_;
v_isHEq_2790_ = v___x_2502_;
v___y_2791_ = v___y_2861_;
v___y_2792_ = v___y_2862_;
v___y_2793_ = v___y_2863_;
v___y_2794_ = v___y_2864_;
goto v___jp_2788_;
}
}
else
{
lean_object* v_a_2893_; lean_object* v___x_2895_; uint8_t v_isShared_2896_; uint8_t v_isSharedCheck_2900_; 
lean_dec(v_snd_2873_);
lean_dec(v_fst_2872_);
lean_dec(v_fst_2870_);
lean_dec_ref(v___x_2640_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_2893_ = lean_ctor_get(v___x_2874_, 0);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2874_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2895_ = v___x_2874_;
v_isShared_2896_ = v_isSharedCheck_2900_;
goto v_resetjp_2894_;
}
else
{
lean_inc(v_a_2893_);
lean_dec(v___x_2874_);
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
lean_dec(v_a_2866_);
v___y_2789_ = v_isEq_2860_;
v_isHEq_2790_ = v___x_2596_;
v___y_2791_ = v___y_2861_;
v___y_2792_ = v___y_2862_;
v___y_2793_ = v___y_2863_;
v___y_2794_ = v___y_2864_;
goto v___jp_2788_;
}
}
else
{
lean_object* v_a_2901_; lean_object* v___x_2903_; uint8_t v_isShared_2904_; uint8_t v_isSharedCheck_2908_; 
lean_dec_ref(v___x_2640_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_2901_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2903_ = v___x_2865_;
v_isShared_2904_ = v_isSharedCheck_2908_;
goto v_resetjp_2902_;
}
else
{
lean_inc(v_a_2901_);
lean_dec(v___x_2865_);
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
v___jp_2909_:
{
lean_object* v___x_2914_; 
lean_inc_ref(v___x_2640_);
v___x_2914_ = l_Lean_Meta_matchEq_x3f(v___x_2640_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v_a_2915_; 
v_a_2915_ = lean_ctor_get(v___x_2914_, 0);
lean_inc(v_a_2915_);
lean_dec_ref_known(v___x_2914_, 1);
if (lean_obj_tag(v_a_2915_) == 1)
{
lean_object* v_val_2916_; lean_object* v_snd_2917_; lean_object* v_fst_2918_; lean_object* v_snd_2919_; lean_object* v___x_2920_; 
v_val_2916_ = lean_ctor_get(v_a_2915_, 0);
lean_inc(v_val_2916_);
lean_dec_ref_known(v_a_2915_, 1);
v_snd_2917_ = lean_ctor_get(v_val_2916_, 1);
lean_inc(v_snd_2917_);
lean_dec(v_val_2916_);
v_fst_2918_ = lean_ctor_get(v_snd_2917_, 0);
lean_inc(v_fst_2918_);
v_snd_2919_ = lean_ctor_get(v_snd_2917_, 1);
lean_inc(v_snd_2919_);
lean_dec(v_snd_2917_);
v___x_2920_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_2918_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
if (lean_obj_tag(v___x_2920_) == 0)
{
lean_object* v_a_2921_; 
v_a_2921_ = lean_ctor_get(v___x_2920_, 0);
lean_inc(v_a_2921_);
lean_dec_ref_known(v___x_2920_, 1);
if (lean_obj_tag(v_a_2921_) == 1)
{
lean_object* v_val_2922_; lean_object* v___x_2923_; 
v_val_2922_ = lean_ctor_get(v_a_2921_, 0);
lean_inc(v_val_2922_);
lean_dec_ref_known(v_a_2921_, 1);
v___x_2923_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_2919_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
if (lean_obj_tag(v___x_2923_) == 0)
{
lean_object* v_a_2924_; 
v_a_2924_ = lean_ctor_get(v___x_2923_, 0);
lean_inc(v_a_2924_);
lean_dec_ref_known(v___x_2923_, 1);
if (lean_obj_tag(v_a_2924_) == 1)
{
lean_object* v_toConstantVal_2925_; lean_object* v_val_2926_; lean_object* v_toConstantVal_2927_; lean_object* v_name_2928_; lean_object* v_name_2929_; uint8_t v___x_2930_; 
v_toConstantVal_2925_ = lean_ctor_get(v_val_2922_, 0);
lean_inc_ref(v_toConstantVal_2925_);
lean_dec(v_val_2922_);
v_val_2926_ = lean_ctor_get(v_a_2924_, 0);
lean_inc(v_val_2926_);
lean_dec_ref_known(v_a_2924_, 1);
v_toConstantVal_2927_ = lean_ctor_get(v_val_2926_, 0);
lean_inc_ref(v_toConstantVal_2927_);
lean_dec(v_val_2926_);
v_name_2928_ = lean_ctor_get(v_toConstantVal_2925_, 0);
lean_inc(v_name_2928_);
lean_dec_ref(v_toConstantVal_2925_);
v_name_2929_ = lean_ctor_get(v_toConstantVal_2927_, 0);
lean_inc(v_name_2929_);
lean_dec_ref(v_toConstantVal_2927_);
v___x_2930_ = lean_name_eq(v_name_2928_, v_name_2929_);
lean_dec(v_name_2929_);
lean_dec(v_name_2928_);
if (v___x_2930_ == 0)
{
lean_dec_ref(v___x_2640_);
lean_dec_ref(v_config_2491_);
v___y_2529_ = v___y_2913_;
v___y_2530_ = v___y_2911_;
v___y_2531_ = v___y_2910_;
v___y_2532_ = v___y_2912_;
goto v___jp_2528_;
}
else
{
if (v___x_2596_ == 0)
{
lean_del_object(v___x_2525_);
v_isEq_2860_ = v___x_2502_;
v___y_2861_ = v___y_2910_;
v___y_2862_ = v___y_2911_;
v___y_2863_ = v___y_2912_;
v___y_2864_ = v___y_2913_;
goto v___jp_2859_;
}
else
{
lean_dec_ref(v___x_2640_);
lean_dec_ref(v_config_2491_);
v___y_2529_ = v___y_2913_;
v___y_2530_ = v___y_2911_;
v___y_2531_ = v___y_2910_;
v___y_2532_ = v___y_2912_;
goto v___jp_2528_;
}
}
}
else
{
lean_dec(v_a_2924_);
lean_dec(v_val_2922_);
lean_del_object(v___x_2525_);
v_isEq_2860_ = v___x_2502_;
v___y_2861_ = v___y_2910_;
v___y_2862_ = v___y_2911_;
v___y_2863_ = v___y_2912_;
v___y_2864_ = v___y_2913_;
goto v___jp_2859_;
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_dec(v_val_2922_);
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_2931_ = lean_ctor_get(v___x_2923_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2923_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2923_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2923_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
}
}
}
}
else
{
lean_dec(v_a_2921_);
lean_dec(v_snd_2919_);
lean_del_object(v___x_2525_);
v_isEq_2860_ = v___x_2502_;
v___y_2861_ = v___y_2910_;
v___y_2862_ = v___y_2911_;
v___y_2863_ = v___y_2912_;
v___y_2864_ = v___y_2913_;
goto v___jp_2859_;
}
}
else
{
lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec(v_snd_2919_);
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_2939_ = lean_ctor_get(v___x_2920_, 0);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2920_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2920_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_dec(v___x_2920_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
else
{
lean_dec(v_a_2915_);
lean_del_object(v___x_2525_);
v_isEq_2860_ = v___x_2596_;
v___y_2861_ = v___y_2910_;
v___y_2862_ = v___y_2911_;
v___y_2863_ = v___y_2912_;
v___y_2864_ = v___y_2913_;
goto v___jp_2859_;
}
}
else
{
lean_object* v_a_2947_; lean_object* v___x_2949_; uint8_t v_isShared_2950_; uint8_t v_isSharedCheck_2954_; 
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_2947_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2954_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2954_ == 0)
{
v___x_2949_ = v___x_2914_;
v_isShared_2950_ = v_isSharedCheck_2954_;
goto v_resetjp_2948_;
}
else
{
lean_inc(v_a_2947_);
lean_dec(v___x_2914_);
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
}
v___jp_2955_:
{
lean_object* v___x_2960_; 
lean_inc_ref(v___x_2640_);
v___x_2960_ = l_Lean_refutableHasNotBit_x3f(v___x_2640_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2960_) == 0)
{
lean_object* v_a_2961_; 
v_a_2961_ = lean_ctor_get(v___x_2960_, 0);
lean_inc(v_a_2961_);
lean_dec_ref_known(v___x_2960_, 1);
if (lean_obj_tag(v_a_2961_) == 1)
{
lean_object* v_val_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_3001_; 
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec_ref(v_config_2491_);
v_val_2962_ = lean_ctor_get(v_a_2961_, 0);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_a_2961_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2964_ = v_a_2961_;
v_isShared_2965_ = v_isSharedCheck_3001_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_val_2962_);
lean_dec(v_a_2961_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_3001_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2966_; 
lean_inc(v_mvarId_2492_);
v___x_2966_ = l_Lean_MVarId_getType(v_mvarId_2492_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2966_) == 0)
{
lean_object* v_a_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
lean_inc(v_a_2967_);
lean_dec_ref_known(v___x_2966_, 1);
v___x_2968_ = l_Lean_LocalDecl_toExpr(v_val_2523_);
v___x_2969_ = l_Lean_Meta_mkAbsurd(v_a_2967_, v_val_2962_, v___x_2968_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_2969_) == 0)
{
lean_object* v_a_2970_; lean_object* v___x_2971_; 
v_a_2970_ = lean_ctor_get(v___x_2969_, 0);
lean_inc(v_a_2970_);
lean_dec_ref_known(v___x_2969_, 1);
v___x_2971_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2492_, v_a_2970_, v___y_2957_);
if (lean_obj_tag(v___x_2971_) == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2974_; 
lean_dec_ref_known(v___x_2971_, 1);
v___x_2972_ = lean_box(v___x_2502_);
if (v_isShared_2965_ == 0)
{
lean_ctor_set(v___x_2964_, 0, v___x_2972_);
v___x_2974_ = v___x_2964_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2972_);
v___x_2974_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
lean_object* v___x_2975_; 
v___x_2975_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2975_, 0, v___x_2974_);
lean_ctor_set(v___x_2975_, 1, v___x_2527_);
v_a_2509_ = v___x_2975_;
goto v___jp_2508_;
}
}
else
{
lean_object* v_a_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_2984_; 
lean_del_object(v___x_2964_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
v_a_2977_ = lean_ctor_get(v___x_2971_, 0);
v_isSharedCheck_2984_ = !lean_is_exclusive(v___x_2971_);
if (v_isSharedCheck_2984_ == 0)
{
v___x_2979_ = v___x_2971_;
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_a_2977_);
lean_dec(v___x_2971_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_2984_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___x_2982_; 
if (v_isShared_2980_ == 0)
{
v___x_2982_ = v___x_2979_;
goto v_reusejp_2981_;
}
else
{
lean_object* v_reuseFailAlloc_2983_; 
v_reuseFailAlloc_2983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2983_, 0, v_a_2977_);
v___x_2982_ = v_reuseFailAlloc_2983_;
goto v_reusejp_2981_;
}
v_reusejp_2981_:
{
return v___x_2982_;
}
}
}
}
else
{
lean_object* v_a_2985_; lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_2992_; 
lean_del_object(v___x_2964_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_2985_ = lean_ctor_get(v___x_2969_, 0);
v_isSharedCheck_2992_ = !lean_is_exclusive(v___x_2969_);
if (v_isSharedCheck_2992_ == 0)
{
v___x_2987_ = v___x_2969_;
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
else
{
lean_inc(v_a_2985_);
lean_dec(v___x_2969_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_2992_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
if (v_isShared_2988_ == 0)
{
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_a_2985_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
}
}
else
{
lean_object* v_a_2993_; lean_object* v___x_2995_; uint8_t v_isShared_2996_; uint8_t v_isSharedCheck_3000_; 
lean_del_object(v___x_2964_);
lean_dec(v_val_2962_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_2993_ = lean_ctor_get(v___x_2966_, 0);
v_isSharedCheck_3000_ = !lean_is_exclusive(v___x_2966_);
if (v_isSharedCheck_3000_ == 0)
{
v___x_2995_ = v___x_2966_;
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
else
{
lean_inc(v_a_2993_);
lean_dec(v___x_2966_);
v___x_2995_ = lean_box(0);
v_isShared_2996_ = v_isSharedCheck_3000_;
goto v_resetjp_2994_;
}
v_resetjp_2994_:
{
lean_object* v___x_2998_; 
if (v_isShared_2996_ == 0)
{
v___x_2998_ = v___x_2995_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_a_2993_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
}
}
}
else
{
lean_object* v___x_3002_; 
lean_dec(v_a_2961_);
lean_inc_ref(v___x_2640_);
v___x_3002_ = l_Lean_Meta_matchNe_x3f(v___x_2640_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3002_) == 0)
{
lean_object* v_a_3003_; 
v_a_3003_ = lean_ctor_get(v___x_3002_, 0);
lean_inc(v_a_3003_);
lean_dec_ref_known(v___x_3002_, 1);
if (lean_obj_tag(v_a_3003_) == 1)
{
lean_object* v_val_3004_; lean_object* v___x_3006_; uint8_t v_isShared_3007_; uint8_t v_isSharedCheck_3073_; 
v_val_3004_ = lean_ctor_get(v_a_3003_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v_a_3003_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3006_ = v_a_3003_;
v_isShared_3007_ = v_isSharedCheck_3073_;
goto v_resetjp_3005_;
}
else
{
lean_inc(v_val_3004_);
lean_dec(v_a_3003_);
v___x_3006_ = lean_box(0);
v_isShared_3007_ = v_isSharedCheck_3073_;
goto v_resetjp_3005_;
}
v_resetjp_3005_:
{
lean_object* v_snd_3008_; lean_object* v_fst_3009_; lean_object* v_snd_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3072_; 
v_snd_3008_ = lean_ctor_get(v_val_3004_, 1);
lean_inc(v_snd_3008_);
lean_dec(v_val_3004_);
v_fst_3009_ = lean_ctor_get(v_snd_3008_, 0);
v_snd_3010_ = lean_ctor_get(v_snd_3008_, 1);
v_isSharedCheck_3072_ = !lean_is_exclusive(v_snd_3008_);
if (v_isSharedCheck_3072_ == 0)
{
v___x_3012_ = v_snd_3008_;
v_isShared_3013_ = v_isSharedCheck_3072_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_snd_3010_);
lean_inc(v_fst_3009_);
lean_dec(v_snd_3008_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3072_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; 
lean_inc(v_fst_3009_);
v___x_3014_ = l_Lean_Meta_isExprDefEq(v_fst_3009_, v_snd_3010_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; uint8_t v___x_3016_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc(v_a_3015_);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = lean_unbox(v_a_3015_);
lean_dec(v_a_3015_);
if (v___x_3016_ == 0)
{
lean_del_object(v___x_3012_);
lean_dec(v_fst_3009_);
lean_del_object(v___x_3006_);
v___y_2910_ = v___y_2956_;
v___y_2911_ = v___y_2957_;
v___y_2912_ = v___y_2958_;
v___y_2913_ = v___y_2959_;
goto v___jp_2909_;
}
else
{
lean_object* v___x_3017_; 
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec_ref(v_config_2491_);
lean_inc(v_mvarId_2492_);
v___x_3017_ = l_Lean_MVarId_getType(v_mvarId_2492_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v___x_3019_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v___x_3019_ = l_Lean_Meta_mkEqRefl(v_fst_3009_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v_a_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v_a_3020_ = lean_ctor_get(v___x_3019_, 0);
lean_inc(v_a_3020_);
lean_dec_ref_known(v___x_3019_, 1);
v___x_3021_ = l_Lean_LocalDecl_toExpr(v_val_2523_);
v___x_3022_ = l_Lean_Meta_mkAbsurd(v_a_3018_, v_a_3020_, v___x_3021_, v___y_2956_, v___y_2957_, v___y_2958_, v___y_2959_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___x_3024_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
v___x_3024_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2492_, v_a_3023_, v___y_2957_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v___x_3025_; lean_object* v___x_3027_; 
lean_dec_ref_known(v___x_3024_, 1);
v___x_3025_ = lean_box(v___x_2502_);
if (v_isShared_3007_ == 0)
{
lean_ctor_set(v___x_3006_, 0, v___x_3025_);
v___x_3027_ = v___x_3006_;
goto v_reusejp_3026_;
}
else
{
lean_object* v_reuseFailAlloc_3031_; 
v_reuseFailAlloc_3031_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3031_, 0, v___x_3025_);
v___x_3027_ = v_reuseFailAlloc_3031_;
goto v_reusejp_3026_;
}
v_reusejp_3026_:
{
lean_object* v___x_3029_; 
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 1, v___x_2527_);
lean_ctor_set(v___x_3012_, 0, v___x_3027_);
v___x_3029_ = v___x_3012_;
goto v_reusejp_3028_;
}
else
{
lean_object* v_reuseFailAlloc_3030_; 
v_reuseFailAlloc_3030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3030_, 0, v___x_3027_);
lean_ctor_set(v_reuseFailAlloc_3030_, 1, v___x_2527_);
v___x_3029_ = v_reuseFailAlloc_3030_;
goto v_reusejp_3028_;
}
v_reusejp_3028_:
{
v_a_2509_ = v___x_3029_;
goto v___jp_2508_;
}
}
}
else
{
lean_object* v_a_3032_; lean_object* v___x_3034_; uint8_t v_isShared_3035_; uint8_t v_isSharedCheck_3039_; 
lean_del_object(v___x_3012_);
lean_del_object(v___x_3006_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
v_a_3032_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3039_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3039_ == 0)
{
v___x_3034_ = v___x_3024_;
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
else
{
lean_inc(v_a_3032_);
lean_dec(v___x_3024_);
v___x_3034_ = lean_box(0);
v_isShared_3035_ = v_isSharedCheck_3039_;
goto v_resetjp_3033_;
}
v_resetjp_3033_:
{
lean_object* v___x_3037_; 
if (v_isShared_3035_ == 0)
{
v___x_3037_ = v___x_3034_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3032_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_object* v_a_3040_; lean_object* v___x_3042_; uint8_t v_isShared_3043_; uint8_t v_isSharedCheck_3047_; 
lean_del_object(v___x_3012_);
lean_del_object(v___x_3006_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_3040_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3047_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3047_ == 0)
{
v___x_3042_ = v___x_3022_;
v_isShared_3043_ = v_isSharedCheck_3047_;
goto v_resetjp_3041_;
}
else
{
lean_inc(v_a_3040_);
lean_dec(v___x_3022_);
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
else
{
lean_object* v_a_3048_; lean_object* v___x_3050_; uint8_t v_isShared_3051_; uint8_t v_isSharedCheck_3055_; 
lean_dec(v_a_3018_);
lean_del_object(v___x_3012_);
lean_del_object(v___x_3006_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_3048_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3055_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3055_ == 0)
{
v___x_3050_ = v___x_3019_;
v_isShared_3051_ = v_isSharedCheck_3055_;
goto v_resetjp_3049_;
}
else
{
lean_inc(v_a_3048_);
lean_dec(v___x_3019_);
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
else
{
lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_del_object(v___x_3012_);
lean_dec(v_fst_3009_);
lean_del_object(v___x_3006_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_3056_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3017_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3017_);
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
}
else
{
lean_object* v_a_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3071_; 
lean_del_object(v___x_3012_);
lean_dec(v_fst_3009_);
lean_del_object(v___x_3006_);
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_3064_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3071_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3071_ == 0)
{
v___x_3066_ = v___x_3014_;
v_isShared_3067_ = v_isSharedCheck_3071_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_a_3064_);
lean_dec(v___x_3014_);
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
}
else
{
lean_dec(v_a_3003_);
v___y_2910_ = v___y_2956_;
v___y_2911_ = v___y_2957_;
v___y_2912_ = v___y_2958_;
v___y_2913_ = v___y_2959_;
goto v___jp_2909_;
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_3074_ = lean_ctor_get(v___x_3002_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_3002_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_3002_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_3002_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
}
else
{
lean_object* v_a_3082_; lean_object* v___x_3084_; uint8_t v_isShared_3085_; uint8_t v_isSharedCheck_3089_; 
lean_dec_ref(v___x_2640_);
lean_del_object(v___x_2525_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_3082_ = lean_ctor_get(v___x_2960_, 0);
v_isSharedCheck_3089_ = !lean_is_exclusive(v___x_2960_);
if (v_isSharedCheck_3089_ == 0)
{
v___x_3084_ = v___x_2960_;
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
else
{
lean_inc(v_a_3082_);
lean_dec(v___x_2960_);
v___x_3084_ = lean_box(0);
v_isShared_3085_ = v_isSharedCheck_3089_;
goto v_resetjp_3083_;
}
v_resetjp_3083_:
{
lean_object* v___x_3087_; 
if (v_isShared_3085_ == 0)
{
v___x_3087_ = v___x_3084_;
goto v_reusejp_3086_;
}
else
{
lean_object* v_reuseFailAlloc_3088_; 
v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
v___x_3087_ = v_reuseFailAlloc_3088_;
goto v_reusejp_3086_;
}
v_reusejp_3086_:
{
return v___x_3087_;
}
}
}
}
}
else
{
lean_del_object(v___x_2525_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
v_a_2517_ = v___x_2568_;
goto v___jp_2516_;
}
v___jp_2528_:
{
lean_object* v___x_2533_; 
lean_inc(v_mvarId_2492_);
v___x_2533_ = l_Lean_MVarId_getType(v_mvarId_2492_, v___y_2531_, v___y_2530_, v___y_2532_, v___y_2529_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v_a_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
v_a_2534_ = lean_ctor_get(v___x_2533_, 0);
lean_inc(v_a_2534_);
lean_dec_ref_known(v___x_2533_, 1);
v___x_2535_ = l_Lean_LocalDecl_toExpr(v_val_2523_);
v___x_2536_ = l_Lean_Meta_mkNoConfusion(v_a_2534_, v___x_2535_, v___y_2531_, v___y_2530_, v___y_2532_, v___y_2529_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2538_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v___x_2538_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_2492_, v_a_2537_, v___y_2530_);
if (lean_obj_tag(v___x_2538_) == 0)
{
lean_object* v___x_2539_; lean_object* v___x_2541_; 
lean_dec_ref_known(v___x_2538_, 1);
v___x_2539_ = lean_box(v___x_2502_);
if (v_isShared_2526_ == 0)
{
lean_ctor_set(v___x_2525_, 0, v___x_2539_);
v___x_2541_ = v___x_2525_;
goto v_reusejp_2540_;
}
else
{
lean_object* v_reuseFailAlloc_2543_; 
v_reuseFailAlloc_2543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2539_);
v___x_2541_ = v_reuseFailAlloc_2543_;
goto v_reusejp_2540_;
}
v_reusejp_2540_:
{
lean_object* v___x_2542_; 
v___x_2542_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2542_, 0, v___x_2541_);
lean_ctor_set(v___x_2542_, 1, v___x_2527_);
v_a_2509_ = v___x_2542_;
goto v___jp_2508_;
}
}
else
{
lean_object* v_a_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2551_; 
lean_del_object(v___x_2525_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
v_a_2544_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2546_ = v___x_2538_;
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
else
{
lean_inc(v_a_2544_);
lean_dec(v___x_2538_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2551_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2549_; 
if (v_isShared_2547_ == 0)
{
v___x_2549_ = v___x_2546_;
goto v_reusejp_2548_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_a_2544_);
v___x_2549_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2548_;
}
v_reusejp_2548_:
{
return v___x_2549_;
}
}
}
}
else
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2559_; 
lean_del_object(v___x_2525_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_2552_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2554_ = v___x_2536_;
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___x_2536_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2559_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
lean_object* v___x_2557_; 
if (v_isShared_2555_ == 0)
{
v___x_2557_ = v___x_2554_;
goto v_reusejp_2556_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_a_2552_);
v___x_2557_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2556_;
}
v_reusejp_2556_:
{
return v___x_2557_;
}
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_del_object(v___x_2525_);
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
v_a_2560_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___x_2533_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___x_2533_);
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
v___jp_2569_:
{
lean_object* v_searchFuel_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v_searchFuel_2574_ = lean_ctor_get(v_config_2491_, 0);
v___x_2575_ = l_Lean_LocalDecl_fvarId(v_val_2523_);
lean_dec(v_val_2523_);
lean_inc(v_searchFuel_2574_);
lean_inc(v_mvarId_2492_);
v___x_2576_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_2492_, v___x_2575_, v_searchFuel_2574_, v___y_2570_, v___y_2573_, v___y_2572_, v___y_2571_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; uint8_t v___x_2578_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = lean_unbox(v_a_2577_);
lean_dec(v_a_2577_);
if (v___x_2578_ == 0)
{
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
v_a_2517_ = v___x_2568_;
goto v___jp_2516_;
}
else
{
lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; 
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v___x_2579_ = lean_box(v___x_2502_);
v___x_2580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
v___x_2581_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2581_, 0, v___x_2580_);
lean_ctor_set(v___x_2581_, 1, v___x_2527_);
v_a_2509_ = v___x_2581_;
goto v___jp_2508_;
}
}
else
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2589_; 
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_2582_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2589_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2589_ == 0)
{
v___x_2584_ = v___x_2576_;
v_isShared_2585_ = v_isSharedCheck_2589_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___x_2576_);
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
v___jp_2590_:
{
if (v___y_2595_ == 0)
{
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
v_a_2517_ = v___x_2568_;
goto v___jp_2516_;
}
else
{
v___y_2570_ = v___y_2591_;
v___y_2571_ = v___y_2592_;
v___y_2572_ = v___y_2593_;
v___y_2573_ = v___y_2594_;
goto v___jp_2569_;
}
}
v___jp_2597_:
{
if (v___y_2601_ == 0)
{
v___y_2570_ = v___y_2598_;
v___y_2571_ = v___y_2599_;
v___y_2572_ = v___y_2600_;
v___y_2573_ = v___y_2602_;
goto v___jp_2569_;
}
else
{
v___y_2591_ = v___y_2598_;
v___y_2592_ = v___y_2599_;
v___y_2593_ = v___y_2600_;
v___y_2594_ = v___y_2602_;
v___y_2595_ = v___x_2596_;
goto v___jp_2590_;
}
}
v___jp_2603_:
{
if (v___y_2609_ == 0)
{
v___y_2591_ = v___y_2604_;
v___y_2592_ = v___y_2605_;
v___y_2593_ = v___y_2606_;
v___y_2594_ = v___y_2608_;
v___y_2595_ = v___x_2596_;
goto v___jp_2590_;
}
else
{
v___y_2598_ = v___y_2604_;
v___y_2599_ = v___y_2605_;
v___y_2600_ = v___y_2606_;
v___y_2601_ = v___y_2607_;
v___y_2602_ = v___y_2608_;
goto v___jp_2597_;
}
}
v___jp_2610_:
{
uint8_t v_emptyType_2617_; 
v_emptyType_2617_ = lean_ctor_get_uint8(v_config_2491_, sizeof(void*)*1 + 1);
if (v_emptyType_2617_ == 0)
{
v___y_2604_ = v___y_2613_;
v___y_2605_ = v___y_2616_;
v___y_2606_ = v___y_2615_;
v___y_2607_ = v___y_2612_;
v___y_2608_ = v___y_2614_;
v___y_2609_ = v___x_2596_;
goto v___jp_2603_;
}
else
{
if (v___y_2611_ == 0)
{
v___y_2598_ = v___y_2613_;
v___y_2599_ = v___y_2616_;
v___y_2600_ = v___y_2615_;
v___y_2601_ = v___y_2612_;
v___y_2602_ = v___y_2614_;
goto v___jp_2597_;
}
else
{
v___y_2604_ = v___y_2613_;
v___y_2605_ = v___y_2616_;
v___y_2606_ = v___y_2615_;
v___y_2607_ = v___y_2612_;
v___y_2608_ = v___y_2614_;
v___y_2609_ = v___x_2596_;
goto v___jp_2603_;
}
}
}
v___jp_2618_:
{
if (v___y_2625_ == 0)
{
v___y_2611_ = v___y_2623_;
v___y_2612_ = v___y_2624_;
v___y_2613_ = v___y_2622_;
v___y_2614_ = v___y_2621_;
v___y_2615_ = v___y_2620_;
v___y_2616_ = v___y_2619_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2626_; 
lean_inc(v_val_2523_);
lean_inc(v_mvarId_2492_);
v___x_2626_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_2492_, v_val_2523_, v___y_2622_, v___y_2621_, v___y_2620_, v___y_2619_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v_a_2627_; uint8_t v___x_2628_; 
v_a_2627_ = lean_ctor_get(v___x_2626_, 0);
lean_inc(v_a_2627_);
lean_dec_ref_known(v___x_2626_, 1);
v___x_2628_ = lean_unbox(v_a_2627_);
lean_dec(v_a_2627_);
if (v___x_2628_ == 0)
{
v___y_2611_ = v___y_2623_;
v___y_2612_ = v___y_2624_;
v___y_2613_ = v___y_2622_;
v___y_2614_ = v___y_2621_;
v___y_2615_ = v___y_2620_;
v___y_2616_ = v___y_2619_;
goto v___jp_2610_;
}
else
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
lean_dec(v_val_2523_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v___x_2629_ = lean_box(v___x_2502_);
v___x_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2630_, 0, v___x_2629_);
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2630_);
lean_ctor_set(v___x_2631_, 1, v___x_2527_);
v_a_2509_ = v___x_2631_;
goto v___jp_2508_;
}
}
else
{
lean_object* v_a_2632_; lean_object* v___x_2634_; uint8_t v_isShared_2635_; uint8_t v_isSharedCheck_2639_; 
lean_dec(v_val_2523_);
lean_del_object(v___x_2506_);
lean_dec(v_snd_2504_);
lean_dec(v_mvarId_2492_);
lean_dec_ref(v_config_2491_);
v_a_2632_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2639_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2639_ == 0)
{
v___x_2634_ = v___x_2626_;
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
else
{
lean_inc(v_a_2632_);
lean_dec(v___x_2626_);
v___x_2634_ = lean_box(0);
v_isShared_2635_ = v_isSharedCheck_2639_;
goto v_resetjp_2633_;
}
v_resetjp_2633_:
{
lean_object* v___x_2637_; 
if (v_isShared_2635_ == 0)
{
v___x_2637_ = v___x_2634_;
goto v_reusejp_2636_;
}
else
{
lean_object* v_reuseFailAlloc_2638_; 
v_reuseFailAlloc_2638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2638_, 0, v_a_2632_);
v___x_2637_ = v_reuseFailAlloc_2638_;
goto v_reusejp_2636_;
}
v_reusejp_2636_:
{
return v___x_2637_;
}
}
}
}
}
}
}
v___jp_2508_:
{
lean_object* v___x_2510_; lean_object* v___x_2512_; 
v___x_2510_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2510_, 0, v_a_2509_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 0, v___x_2510_);
v___x_2512_ = v___x_2506_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v___x_2510_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_snd_2504_);
v___x_2512_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
lean_object* v___x_2513_; 
v___x_2513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2512_);
return v___x_2513_;
}
}
v___jp_2516_:
{
lean_object* v___x_2518_; size_t v___x_2519_; size_t v___x_2520_; lean_object* v___x_2521_; 
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2515_);
lean_ctor_set(v___x_2518_, 1, v_a_2517_);
v___x_2519_ = ((size_t)1ULL);
v___x_2520_ = lean_usize_add(v_i_2495_, v___x_2519_);
v___x_2521_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4(v_config_2491_, v_mvarId_2492_, v_as_2493_, v_sz_2494_, v___x_2520_, v___x_2518_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
return v___x_2521_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1___boxed(lean_object* v_config_3156_, lean_object* v_mvarId_3157_, lean_object* v_as_3158_, lean_object* v_sz_3159_, lean_object* v_i_3160_, lean_object* v_b_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
size_t v_sz_boxed_3167_; size_t v_i_boxed_3168_; lean_object* v_res_3169_; 
v_sz_boxed_3167_ = lean_unbox_usize(v_sz_3159_);
lean_dec(v_sz_3159_);
v_i_boxed_3168_ = lean_unbox_usize(v_i_3160_);
lean_dec(v_i_3160_);
v_res_3169_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_3156_, v_mvarId_3157_, v_as_3158_, v_sz_boxed_3167_, v_i_boxed_3168_, v_b_3161_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec_ref(v_as_3158_);
return v_res_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(lean_object* v_config_3173_, lean_object* v_mvarId_3174_, lean_object* v_as_3175_, size_t v_sz_3176_, size_t v_i_3177_, lean_object* v_b_3178_, lean_object* v___y_3179_, lean_object* v___y_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_){
_start:
{
uint8_t v___x_3184_; 
v___x_3184_ = lean_usize_dec_lt(v_i_3177_, v_sz_3176_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; 
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v___x_3185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3185_, 0, v_b_3178_);
return v___x_3185_;
}
else
{
lean_object* v_snd_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3856_; 
v_snd_3186_ = lean_ctor_get(v_b_3178_, 1);
v_isSharedCheck_3856_ = !lean_is_exclusive(v_b_3178_);
if (v_isSharedCheck_3856_ == 0)
{
lean_object* v_unused_3857_; 
v_unused_3857_ = lean_ctor_get(v_b_3178_, 0);
lean_dec(v_unused_3857_);
v___x_3188_ = v_b_3178_;
v_isShared_3189_ = v_isSharedCheck_3856_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_snd_3186_);
lean_dec(v_b_3178_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3856_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v_a_3191_; lean_object* v___x_3197_; lean_object* v_a_3199_; lean_object* v_a_3204_; 
v___x_3197_ = lean_box(0);
v_a_3204_ = lean_array_uget(v_as_3175_, v_i_3177_);
if (lean_obj_tag(v_a_3204_) == 0)
{
lean_del_object(v___x_3188_);
v_a_3199_ = v_snd_3186_;
goto v___jp_3198_;
}
else
{
lean_object* v_val_3205_; lean_object* v___x_3207_; uint8_t v_isShared_3208_; uint8_t v_isSharedCheck_3855_; 
v_val_3205_ = lean_ctor_get(v_a_3204_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v_a_3204_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3207_ = v_a_3204_;
v_isShared_3208_ = v_isSharedCheck_3855_;
goto v_resetjp_3206_;
}
else
{
lean_inc(v_val_3205_);
lean_dec(v_a_3204_);
v___x_3207_ = lean_box(0);
v_isShared_3208_ = v_isSharedCheck_3855_;
goto v_resetjp_3206_;
}
v_resetjp_3206_:
{
lean_object* v___x_3209_; lean_object* v___y_3211_; lean_object* v___y_3212_; lean_object* v___y_3213_; lean_object* v___y_3214_; lean_object* v___x_3251_; lean_object* v___y_3253_; lean_object* v___y_3254_; lean_object* v___y_3255_; lean_object* v___y_3256_; lean_object* v___y_3275_; lean_object* v___y_3276_; lean_object* v___y_3277_; lean_object* v___y_3278_; uint8_t v___y_3279_; uint8_t v___x_3280_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; uint8_t v___y_3286_; lean_object* v___y_3288_; lean_object* v___y_3289_; lean_object* v___y_3290_; uint8_t v___y_3291_; lean_object* v___y_3292_; uint8_t v___y_3293_; uint8_t v___y_3295_; uint8_t v___y_3296_; lean_object* v___y_3297_; lean_object* v___y_3298_; lean_object* v___y_3299_; lean_object* v___y_3300_; lean_object* v___y_3303_; uint8_t v___y_3304_; lean_object* v___y_3305_; uint8_t v___y_3306_; lean_object* v___y_3307_; lean_object* v___y_3308_; uint8_t v___y_3309_; 
v___x_3209_ = lean_box(0);
v___x_3251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3280_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3205_);
if (v___x_3280_ == 0)
{
lean_object* v___x_3325_; uint8_t v___y_3327_; uint8_t v___y_3328_; lean_object* v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3331_; lean_object* v___y_3332_; lean_object* v___y_3336_; uint8_t v___y_3337_; lean_object* v___y_3338_; uint8_t v___y_3339_; lean_object* v___y_3340_; lean_object* v___y_3341_; lean_object* v___y_3342_; uint8_t v___y_3343_; lean_object* v___y_3346_; uint8_t v___y_3347_; lean_object* v___y_3348_; uint8_t v___y_3349_; lean_object* v___y_3350_; lean_object* v___y_3351_; lean_object* v_a_3352_; lean_object* v___y_3356_; lean_object* v___y_3357_; uint8_t v___y_3358_; lean_object* v___y_3359_; uint8_t v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3407_; uint8_t v___y_3408_; lean_object* v___y_3409_; uint8_t v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3436_; uint8_t v___y_3437_; lean_object* v___y_3438_; uint8_t v___y_3439_; lean_object* v___y_3440_; lean_object* v___y_3441_; uint8_t v___y_3442_; lean_object* v___y_3444_; uint8_t v___y_3445_; lean_object* v___y_3446_; lean_object* v___y_3447_; uint8_t v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3450_; uint8_t v___y_3451_; lean_object* v___y_3454_; uint8_t v___y_3455_; lean_object* v___y_3456_; uint8_t v___y_3457_; lean_object* v___y_3458_; lean_object* v___y_3459_; uint8_t v___y_3460_; lean_object* v___y_3473_; uint8_t v___y_3474_; lean_object* v___y_3475_; uint8_t v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; uint8_t v___y_3479_; uint8_t v___y_3481_; uint8_t v_isHEq_3482_; lean_object* v___y_3483_; lean_object* v___y_3484_; lean_object* v___y_3485_; lean_object* v___y_3486_; lean_object* v___y_3490_; uint8_t v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; lean_object* v___y_3494_; lean_object* v___y_3495_; lean_object* v___y_3496_; uint8_t v_isEq_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; lean_object* v___y_3556_; lean_object* v___y_3557_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3649_; lean_object* v___y_3650_; lean_object* v___y_3651_; lean_object* v___y_3652_; lean_object* v___x_3785_; 
v___x_3325_ = l_Lean_LocalDecl_type(v_val_3205_);
lean_inc_ref(v___x_3325_);
v___x_3785_ = l_Lean_Meta_matchNot_x3f(v___x_3325_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3785_) == 0)
{
lean_object* v_a_3786_; 
v_a_3786_ = lean_ctor_get(v___x_3785_, 0);
lean_inc(v_a_3786_);
lean_dec_ref_known(v___x_3785_, 1);
if (lean_obj_tag(v_a_3786_) == 1)
{
lean_object* v_val_3787_; lean_object* v___x_3789_; uint8_t v_isShared_3790_; uint8_t v_isSharedCheck_3846_; 
v_val_3787_ = lean_ctor_get(v_a_3786_, 0);
v_isSharedCheck_3846_ = !lean_is_exclusive(v_a_3786_);
if (v_isSharedCheck_3846_ == 0)
{
v___x_3789_ = v_a_3786_;
v_isShared_3790_ = v_isSharedCheck_3846_;
goto v_resetjp_3788_;
}
else
{
lean_inc(v_val_3787_);
lean_dec(v_a_3786_);
v___x_3789_ = lean_box(0);
v_isShared_3790_ = v_isSharedCheck_3846_;
goto v_resetjp_3788_;
}
v_resetjp_3788_:
{
lean_object* v___x_3791_; 
v___x_3791_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_3787_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3791_) == 0)
{
lean_object* v_a_3792_; 
v_a_3792_ = lean_ctor_get(v___x_3791_, 0);
lean_inc(v_a_3792_);
lean_dec_ref_known(v___x_3791_, 1);
if (lean_obj_tag(v_a_3792_) == 1)
{
lean_object* v_val_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3837_; 
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec_ref(v_config_3173_);
v_val_3793_ = lean_ctor_get(v_a_3792_, 0);
v_isSharedCheck_3837_ = !lean_is_exclusive(v_a_3792_);
if (v_isSharedCheck_3837_ == 0)
{
v___x_3795_ = v_a_3792_;
v_isShared_3796_ = v_isSharedCheck_3837_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_val_3793_);
lean_dec(v_a_3792_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3837_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3797_; 
lean_inc(v_mvarId_3174_);
v___x_3797_ = l_Lean_MVarId_getType(v_mvarId_3174_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3797_) == 0)
{
lean_object* v_a_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; 
v_a_3798_ = lean_ctor_get(v___x_3797_, 0);
lean_inc(v_a_3798_);
lean_dec_ref_known(v___x_3797_, 1);
v___x_3799_ = l_Lean_LocalDecl_toExpr(v_val_3205_);
v___x_3800_ = l_Lean_mkFVar(v_val_3793_);
v___x_3801_ = l_Lean_Expr_app___override(v___x_3799_, v___x_3800_);
v___x_3802_ = l_Lean_Meta_mkFalseElim(v_a_3798_, v___x_3801_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3804_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
lean_inc(v_a_3803_);
lean_dec_ref_known(v___x_3802_, 1);
v___x_3804_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3174_, v_a_3803_, v___y_3180_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v___x_3805_; lean_object* v___x_3807_; 
lean_dec_ref_known(v___x_3804_, 1);
v___x_3805_ = lean_box(v___x_3184_);
if (v_isShared_3796_ == 0)
{
lean_ctor_set(v___x_3795_, 0, v___x_3805_);
v___x_3807_ = v___x_3795_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3812_; 
v_reuseFailAlloc_3812_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3812_, 0, v___x_3805_);
v___x_3807_ = v_reuseFailAlloc_3812_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
lean_object* v___x_3808_; lean_object* v___x_3810_; 
v___x_3808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3807_);
lean_ctor_set(v___x_3808_, 1, v___x_3209_);
if (v_isShared_3790_ == 0)
{
lean_ctor_set_tag(v___x_3789_, 0);
lean_ctor_set(v___x_3789_, 0, v___x_3808_);
v___x_3810_ = v___x_3789_;
goto v_reusejp_3809_;
}
else
{
lean_object* v_reuseFailAlloc_3811_; 
v_reuseFailAlloc_3811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3811_, 0, v___x_3808_);
v___x_3810_ = v_reuseFailAlloc_3811_;
goto v_reusejp_3809_;
}
v_reusejp_3809_:
{
v_a_3191_ = v___x_3810_;
goto v___jp_3190_;
}
}
}
else
{
lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_del_object(v___x_3795_);
lean_del_object(v___x_3789_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
v_a_3813_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3804_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_dec(v___x_3804_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_del_object(v___x_3795_);
lean_del_object(v___x_3789_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3821_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3802_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3802_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
else
{
lean_object* v_a_3829_; lean_object* v___x_3831_; uint8_t v_isShared_3832_; uint8_t v_isSharedCheck_3836_; 
lean_del_object(v___x_3795_);
lean_dec(v_val_3793_);
lean_del_object(v___x_3789_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3829_ = lean_ctor_get(v___x_3797_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3797_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3831_ = v___x_3797_;
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
else
{
lean_inc(v_a_3829_);
lean_dec(v___x_3797_);
v___x_3831_ = lean_box(0);
v_isShared_3832_ = v_isSharedCheck_3836_;
goto v_resetjp_3830_;
}
v_resetjp_3830_:
{
lean_object* v___x_3834_; 
if (v_isShared_3832_ == 0)
{
v___x_3834_ = v___x_3831_;
goto v_reusejp_3833_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v_a_3829_);
v___x_3834_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3833_;
}
v_reusejp_3833_:
{
return v___x_3834_;
}
}
}
}
}
else
{
lean_dec(v_a_3792_);
lean_del_object(v___x_3789_);
v___y_3649_ = v___y_3179_;
v___y_3650_ = v___y_3180_;
v___y_3651_ = v___y_3181_;
v___y_3652_ = v___y_3182_;
goto v___jp_3648_;
}
}
else
{
lean_object* v_a_3838_; lean_object* v___x_3840_; uint8_t v_isShared_3841_; uint8_t v_isSharedCheck_3845_; 
lean_del_object(v___x_3789_);
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3838_ = lean_ctor_get(v___x_3791_, 0);
v_isSharedCheck_3845_ = !lean_is_exclusive(v___x_3791_);
if (v_isSharedCheck_3845_ == 0)
{
v___x_3840_ = v___x_3791_;
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
else
{
lean_inc(v_a_3838_);
lean_dec(v___x_3791_);
v___x_3840_ = lean_box(0);
v_isShared_3841_ = v_isSharedCheck_3845_;
goto v_resetjp_3839_;
}
v_resetjp_3839_:
{
lean_object* v___x_3843_; 
if (v_isShared_3841_ == 0)
{
v___x_3843_ = v___x_3840_;
goto v_reusejp_3842_;
}
else
{
lean_object* v_reuseFailAlloc_3844_; 
v_reuseFailAlloc_3844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3844_, 0, v_a_3838_);
v___x_3843_ = v_reuseFailAlloc_3844_;
goto v_reusejp_3842_;
}
v_reusejp_3842_:
{
return v___x_3843_;
}
}
}
}
}
else
{
lean_dec(v_a_3786_);
v___y_3649_ = v___y_3179_;
v___y_3650_ = v___y_3180_;
v___y_3651_ = v___y_3181_;
v___y_3652_ = v___y_3182_;
goto v___jp_3648_;
}
}
else
{
lean_object* v_a_3847_; lean_object* v___x_3849_; uint8_t v_isShared_3850_; uint8_t v_isSharedCheck_3854_; 
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3847_ = lean_ctor_get(v___x_3785_, 0);
v_isSharedCheck_3854_ = !lean_is_exclusive(v___x_3785_);
if (v_isSharedCheck_3854_ == 0)
{
v___x_3849_ = v___x_3785_;
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
else
{
lean_inc(v_a_3847_);
lean_dec(v___x_3785_);
v___x_3849_ = lean_box(0);
v_isShared_3850_ = v_isSharedCheck_3854_;
goto v_resetjp_3848_;
}
v_resetjp_3848_:
{
lean_object* v___x_3852_; 
if (v_isShared_3850_ == 0)
{
v___x_3852_ = v___x_3849_;
goto v_reusejp_3851_;
}
else
{
lean_object* v_reuseFailAlloc_3853_; 
v_reuseFailAlloc_3853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_a_3847_);
v___x_3852_ = v_reuseFailAlloc_3853_;
goto v_reusejp_3851_;
}
v_reusejp_3851_:
{
return v___x_3852_;
}
}
}
v___jp_3326_:
{
uint8_t v_genDiseq_3333_; 
v_genDiseq_3333_ = lean_ctor_get_uint8(v_config_3173_, sizeof(void*)*1 + 2);
if (v_genDiseq_3333_ == 0)
{
lean_dec_ref(v___x_3325_);
v___y_3303_ = v___y_3330_;
v___y_3304_ = v___y_3327_;
v___y_3305_ = v___y_3331_;
v___y_3306_ = v___y_3328_;
v___y_3307_ = v___y_3332_;
v___y_3308_ = v___y_3329_;
v___y_3309_ = v___x_3280_;
goto v___jp_3302_;
}
else
{
uint8_t v___x_3334_; 
v___x_3334_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_3325_);
v___y_3303_ = v___y_3330_;
v___y_3304_ = v___y_3327_;
v___y_3305_ = v___y_3331_;
v___y_3306_ = v___y_3328_;
v___y_3307_ = v___y_3332_;
v___y_3308_ = v___y_3329_;
v___y_3309_ = v___x_3334_;
goto v___jp_3302_;
}
}
v___jp_3335_:
{
if (v___y_3343_ == 0)
{
lean_dec_ref(v___y_3340_);
v___y_3327_ = v___y_3337_;
v___y_3328_ = v___y_3339_;
v___y_3329_ = v___y_3342_;
v___y_3330_ = v___y_3338_;
v___y_3331_ = v___y_3336_;
v___y_3332_ = v___y_3341_;
goto v___jp_3326_;
}
else
{
lean_object* v___x_3344_; 
lean_dec_ref(v___x_3325_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v___x_3344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3344_, 0, v___y_3340_);
return v___x_3344_;
}
}
v___jp_3345_:
{
uint8_t v___x_3353_; 
v___x_3353_ = l_Lean_Exception_isInterrupt(v_a_3352_);
if (v___x_3353_ == 0)
{
uint8_t v___x_3354_; 
lean_inc_ref(v_a_3352_);
v___x_3354_ = l_Lean_Exception_isRuntime(v_a_3352_);
v___y_3336_ = v___y_3346_;
v___y_3337_ = v___y_3347_;
v___y_3338_ = v___y_3348_;
v___y_3339_ = v___y_3349_;
v___y_3340_ = v_a_3352_;
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3350_;
v___y_3343_ = v___x_3354_;
goto v___jp_3335_;
}
else
{
v___y_3336_ = v___y_3346_;
v___y_3337_ = v___y_3347_;
v___y_3338_ = v___y_3348_;
v___y_3339_ = v___y_3349_;
v___y_3340_ = v_a_3352_;
v___y_3341_ = v___y_3351_;
v___y_3342_ = v___y_3350_;
v___y_3343_ = v___x_3353_;
goto v___jp_3335_;
}
}
v___jp_3355_:
{
if (lean_obj_tag(v___y_3363_) == 0)
{
lean_object* v_a_3364_; lean_object* v___x_3365_; uint8_t v___x_3366_; 
v_a_3364_ = lean_ctor_get(v___y_3363_, 0);
lean_inc(v_a_3364_);
lean_dec_ref_known(v___y_3363_, 1);
v___x_3365_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_3366_ = l_Lean_Expr_isConstOf(v_a_3364_, v___x_3365_);
lean_dec(v_a_3364_);
if (v___x_3366_ == 0)
{
lean_dec_ref(v___y_3356_);
v___y_3327_ = v___y_3358_;
v___y_3328_ = v___y_3360_;
v___y_3329_ = v___y_3362_;
v___y_3330_ = v___y_3359_;
v___y_3331_ = v___y_3357_;
v___y_3332_ = v___y_3361_;
goto v___jp_3326_;
}
else
{
lean_object* v___x_3367_; 
lean_inc_ref(v___y_3356_);
v___x_3367_ = l_Lean_Meta_mkEqRefl(v___y_3356_, v___y_3362_, v___y_3359_, v___y_3357_, v___y_3361_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v_a_3368_; lean_object* v___x_3369_; lean_object* v_dummy_3370_; lean_object* v_nargs_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_a_3368_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3368_);
lean_dec_ref_known(v___x_3367_, 1);
v___x_3369_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_3370_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_3371_ = l_Lean_Expr_getAppNumArgs(v___y_3356_);
lean_inc(v_nargs_3371_);
v___x_3372_ = lean_mk_array(v_nargs_3371_, v_dummy_3370_);
v___x_3373_ = lean_unsigned_to_nat(1u);
v___x_3374_ = lean_nat_sub(v_nargs_3371_, v___x_3373_);
lean_dec(v_nargs_3371_);
v___x_3375_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_3356_, v___x_3372_, v___x_3374_);
v___x_3376_ = lean_array_push(v___x_3375_, v_a_3368_);
v___x_3377_ = l_Lean_mkAppN(v___x_3369_, v___x_3376_);
lean_dec_ref(v___x_3376_);
lean_inc(v_mvarId_3174_);
v___x_3378_ = l_Lean_MVarId_getType(v_mvarId_3174_, v___y_3362_, v___y_3359_, v___y_3357_, v___y_3361_);
if (lean_obj_tag(v___x_3378_) == 0)
{
lean_object* v_a_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; 
v_a_3379_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3379_);
lean_dec_ref_known(v___x_3378_, 1);
lean_inc(v_val_3205_);
v___x_3380_ = l_Lean_LocalDecl_toExpr(v_val_3205_);
v___x_3381_ = l_Lean_Meta_mkAbsurd(v_a_3379_, v___x_3380_, v___x_3377_, v___y_3362_, v___y_3359_, v___y_3357_, v___y_3361_);
if (lean_obj_tag(v___x_3381_) == 0)
{
lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3401_; 
v_a_3382_ = lean_ctor_get(v___x_3381_, 0);
v_isSharedCheck_3401_ = !lean_is_exclusive(v___x_3381_);
if (v_isSharedCheck_3401_ == 0)
{
v___x_3384_ = v___x_3381_;
v_isShared_3385_ = v_isSharedCheck_3401_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_dec(v___x_3381_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3401_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3386_; 
lean_inc(v_mvarId_3174_);
v___x_3386_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3174_, v_a_3382_, v___y_3359_);
if (lean_obj_tag(v___x_3386_) == 0)
{
lean_object* v___x_3388_; uint8_t v_isShared_3389_; uint8_t v_isSharedCheck_3398_; 
lean_dec_ref(v___x_3325_);
lean_dec(v_val_3205_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_isSharedCheck_3398_ = !lean_is_exclusive(v___x_3386_);
if (v_isSharedCheck_3398_ == 0)
{
lean_object* v_unused_3399_; 
v_unused_3399_ = lean_ctor_get(v___x_3386_, 0);
lean_dec(v_unused_3399_);
v___x_3388_ = v___x_3386_;
v_isShared_3389_ = v_isSharedCheck_3398_;
goto v_resetjp_3387_;
}
else
{
lean_dec(v___x_3386_);
v___x_3388_ = lean_box(0);
v_isShared_3389_ = v_isSharedCheck_3398_;
goto v_resetjp_3387_;
}
v_resetjp_3387_:
{
lean_object* v___x_3390_; lean_object* v___x_3392_; 
v___x_3390_ = lean_box(v___x_3184_);
if (v_isShared_3389_ == 0)
{
lean_ctor_set_tag(v___x_3388_, 1);
lean_ctor_set(v___x_3388_, 0, v___x_3390_);
v___x_3392_ = v___x_3388_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v___x_3390_);
v___x_3392_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
lean_object* v___x_3393_; lean_object* v___x_3395_; 
v___x_3393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3393_, 0, v___x_3392_);
lean_ctor_set(v___x_3393_, 1, v___x_3209_);
if (v_isShared_3385_ == 0)
{
lean_ctor_set(v___x_3384_, 0, v___x_3393_);
v___x_3395_ = v___x_3384_;
goto v_reusejp_3394_;
}
else
{
lean_object* v_reuseFailAlloc_3396_; 
v_reuseFailAlloc_3396_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3396_, 0, v___x_3393_);
v___x_3395_ = v_reuseFailAlloc_3396_;
goto v_reusejp_3394_;
}
v_reusejp_3394_:
{
v_a_3191_ = v___x_3395_;
goto v___jp_3190_;
}
}
}
}
else
{
lean_object* v_a_3400_; 
lean_del_object(v___x_3384_);
v_a_3400_ = lean_ctor_get(v___x_3386_, 0);
lean_inc(v_a_3400_);
lean_dec_ref_known(v___x_3386_, 1);
v___y_3346_ = v___y_3357_;
v___y_3347_ = v___y_3358_;
v___y_3348_ = v___y_3359_;
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3362_;
v___y_3351_ = v___y_3361_;
v_a_3352_ = v_a_3400_;
goto v___jp_3345_;
}
}
}
else
{
lean_object* v_a_3402_; 
v_a_3402_ = lean_ctor_get(v___x_3381_, 0);
lean_inc(v_a_3402_);
lean_dec_ref_known(v___x_3381_, 1);
v___y_3346_ = v___y_3357_;
v___y_3347_ = v___y_3358_;
v___y_3348_ = v___y_3359_;
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3362_;
v___y_3351_ = v___y_3361_;
v_a_3352_ = v_a_3402_;
goto v___jp_3345_;
}
}
else
{
lean_object* v_a_3403_; 
lean_dec_ref(v___x_3377_);
v_a_3403_ = lean_ctor_get(v___x_3378_, 0);
lean_inc(v_a_3403_);
lean_dec_ref_known(v___x_3378_, 1);
v___y_3346_ = v___y_3357_;
v___y_3347_ = v___y_3358_;
v___y_3348_ = v___y_3359_;
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3362_;
v___y_3351_ = v___y_3361_;
v_a_3352_ = v_a_3403_;
goto v___jp_3345_;
}
}
else
{
lean_object* v_a_3404_; 
lean_dec_ref(v___y_3356_);
v_a_3404_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_a_3404_);
lean_dec_ref_known(v___x_3367_, 1);
v___y_3346_ = v___y_3357_;
v___y_3347_ = v___y_3358_;
v___y_3348_ = v___y_3359_;
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3362_;
v___y_3351_ = v___y_3361_;
v_a_3352_ = v_a_3404_;
goto v___jp_3345_;
}
}
}
else
{
lean_object* v_a_3405_; 
lean_dec_ref(v___y_3356_);
v_a_3405_ = lean_ctor_get(v___y_3363_, 0);
lean_inc(v_a_3405_);
lean_dec_ref_known(v___y_3363_, 1);
v___y_3346_ = v___y_3357_;
v___y_3347_ = v___y_3358_;
v___y_3348_ = v___y_3359_;
v___y_3349_ = v___y_3360_;
v___y_3350_ = v___y_3362_;
v___y_3351_ = v___y_3361_;
v_a_3352_ = v_a_3405_;
goto v___jp_3345_;
}
}
v___jp_3406_:
{
lean_object* v___x_3413_; 
lean_inc_ref(v___x_3325_);
v___x_3413_ = l_Lean_Meta_mkDecide(v___x_3325_, v___y_3412_, v___y_3409_, v___y_3407_, v___y_3411_);
if (lean_obj_tag(v___x_3413_) == 0)
{
lean_object* v_a_3414_; lean_object* v___x_3415_; uint8_t v_transparency_3416_; uint8_t v___x_3417_; uint8_t v___x_3418_; 
v_a_3414_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3414_);
lean_dec_ref_known(v___x_3413_, 1);
v___x_3415_ = l_Lean_Meta_Context_config(v___y_3412_);
v_transparency_3416_ = lean_ctor_get_uint8(v___x_3415_, 9);
lean_dec_ref(v___x_3415_);
v___x_3417_ = 1;
v___x_3418_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3416_, v___x_3417_);
if (v___x_3418_ == 0)
{
lean_object* v_keyedConfig_3419_; uint8_t v_trackZetaDelta_3420_; lean_object* v_zetaDeltaSet_3421_; lean_object* v_lctx_3422_; lean_object* v_localInstances_3423_; lean_object* v_defEqCtx_x3f_3424_; lean_object* v_synthPendingDepth_3425_; lean_object* v_customCanUnfoldPredicate_x3f_3426_; uint8_t v_univApprox_3427_; uint8_t v_inTypeClassResolution_3428_; uint8_t v_cacheInferType_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; 
v_keyedConfig_3419_ = lean_ctor_get(v___y_3412_, 0);
v_trackZetaDelta_3420_ = lean_ctor_get_uint8(v___y_3412_, sizeof(void*)*7);
v_zetaDeltaSet_3421_ = lean_ctor_get(v___y_3412_, 1);
v_lctx_3422_ = lean_ctor_get(v___y_3412_, 2);
v_localInstances_3423_ = lean_ctor_get(v___y_3412_, 3);
v_defEqCtx_x3f_3424_ = lean_ctor_get(v___y_3412_, 4);
v_synthPendingDepth_3425_ = lean_ctor_get(v___y_3412_, 5);
v_customCanUnfoldPredicate_x3f_3426_ = lean_ctor_get(v___y_3412_, 6);
v_univApprox_3427_ = lean_ctor_get_uint8(v___y_3412_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3428_ = lean_ctor_get_uint8(v___y_3412_, sizeof(void*)*7 + 2);
v_cacheInferType_3429_ = lean_ctor_get_uint8(v___y_3412_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3419_);
v___x_3430_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3417_, v_keyedConfig_3419_);
lean_inc(v_customCanUnfoldPredicate_x3f_3426_);
lean_inc(v_synthPendingDepth_3425_);
lean_inc(v_defEqCtx_x3f_3424_);
lean_inc_ref(v_localInstances_3423_);
lean_inc_ref(v_lctx_3422_);
lean_inc(v_zetaDeltaSet_3421_);
v___x_3431_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
lean_ctor_set(v___x_3431_, 1, v_zetaDeltaSet_3421_);
lean_ctor_set(v___x_3431_, 2, v_lctx_3422_);
lean_ctor_set(v___x_3431_, 3, v_localInstances_3423_);
lean_ctor_set(v___x_3431_, 4, v_defEqCtx_x3f_3424_);
lean_ctor_set(v___x_3431_, 5, v_synthPendingDepth_3425_);
lean_ctor_set(v___x_3431_, 6, v_customCanUnfoldPredicate_x3f_3426_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*7, v_trackZetaDelta_3420_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*7 + 1, v_univApprox_3427_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3428_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*7 + 3, v_cacheInferType_3429_);
lean_inc(v___y_3411_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3409_);
lean_inc(v_a_3414_);
v___x_3432_ = lean_whnf(v_a_3414_, v___x_3431_, v___y_3409_, v___y_3407_, v___y_3411_);
v___y_3356_ = v_a_3414_;
v___y_3357_ = v___y_3407_;
v___y_3358_ = v___y_3408_;
v___y_3359_ = v___y_3409_;
v___y_3360_ = v___y_3410_;
v___y_3361_ = v___y_3411_;
v___y_3362_ = v___y_3412_;
v___y_3363_ = v___x_3432_;
goto v___jp_3355_;
}
else
{
lean_object* v___x_3433_; 
lean_inc(v___y_3411_);
lean_inc_ref(v___y_3407_);
lean_inc(v___y_3409_);
lean_inc_ref(v___y_3412_);
lean_inc(v_a_3414_);
v___x_3433_ = lean_whnf(v_a_3414_, v___y_3412_, v___y_3409_, v___y_3407_, v___y_3411_);
v___y_3356_ = v_a_3414_;
v___y_3357_ = v___y_3407_;
v___y_3358_ = v___y_3408_;
v___y_3359_ = v___y_3409_;
v___y_3360_ = v___y_3410_;
v___y_3361_ = v___y_3411_;
v___y_3362_ = v___y_3412_;
v___y_3363_ = v___x_3433_;
goto v___jp_3355_;
}
}
else
{
lean_object* v_a_3434_; 
v_a_3434_ = lean_ctor_get(v___x_3413_, 0);
lean_inc(v_a_3434_);
lean_dec_ref_known(v___x_3413_, 1);
v___y_3346_ = v___y_3407_;
v___y_3347_ = v___y_3408_;
v___y_3348_ = v___y_3409_;
v___y_3349_ = v___y_3410_;
v___y_3350_ = v___y_3412_;
v___y_3351_ = v___y_3411_;
v_a_3352_ = v_a_3434_;
goto v___jp_3345_;
}
}
v___jp_3435_:
{
if (v___y_3442_ == 0)
{
v___y_3327_ = v___y_3437_;
v___y_3328_ = v___y_3439_;
v___y_3329_ = v___y_3441_;
v___y_3330_ = v___y_3438_;
v___y_3331_ = v___y_3436_;
v___y_3332_ = v___y_3440_;
goto v___jp_3326_;
}
else
{
v___y_3407_ = v___y_3436_;
v___y_3408_ = v___y_3437_;
v___y_3409_ = v___y_3438_;
v___y_3410_ = v___y_3439_;
v___y_3411_ = v___y_3440_;
v___y_3412_ = v___y_3441_;
goto v___jp_3406_;
}
}
v___jp_3443_:
{
if (v___y_3451_ == 0)
{
lean_dec_ref(v___y_3447_);
v___y_3436_ = v___y_3444_;
v___y_3437_ = v___y_3445_;
v___y_3438_ = v___y_3446_;
v___y_3439_ = v___y_3448_;
v___y_3440_ = v___y_3450_;
v___y_3441_ = v___y_3449_;
v___y_3442_ = v___x_3280_;
goto v___jp_3435_;
}
else
{
uint8_t v___x_3452_; 
v___x_3452_ = l_Lean_Expr_hasFVar(v___y_3447_);
lean_dec_ref(v___y_3447_);
if (v___x_3452_ == 0)
{
v___y_3407_ = v___y_3444_;
v___y_3408_ = v___y_3445_;
v___y_3409_ = v___y_3446_;
v___y_3410_ = v___y_3448_;
v___y_3411_ = v___y_3450_;
v___y_3412_ = v___y_3449_;
goto v___jp_3406_;
}
else
{
v___y_3436_ = v___y_3444_;
v___y_3437_ = v___y_3445_;
v___y_3438_ = v___y_3446_;
v___y_3439_ = v___y_3448_;
v___y_3440_ = v___y_3450_;
v___y_3441_ = v___y_3449_;
v___y_3442_ = v___x_3280_;
goto v___jp_3435_;
}
}
}
v___jp_3453_:
{
lean_object* v___x_3461_; 
lean_inc_ref(v___x_3325_);
v___x_3461_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_3325_, v___y_3456_);
if (lean_obj_tag(v___x_3461_) == 0)
{
lean_object* v_a_3462_; uint8_t v___x_3463_; 
v_a_3462_ = lean_ctor_get(v___x_3461_, 0);
lean_inc(v_a_3462_);
lean_dec_ref_known(v___x_3461_, 1);
v___x_3463_ = l_Lean_Expr_hasMVar(v_a_3462_);
if (v___x_3463_ == 0)
{
v___y_3444_ = v___y_3454_;
v___y_3445_ = v___y_3455_;
v___y_3446_ = v___y_3456_;
v___y_3447_ = v_a_3462_;
v___y_3448_ = v___y_3457_;
v___y_3449_ = v___y_3458_;
v___y_3450_ = v___y_3459_;
v___y_3451_ = v___y_3460_;
goto v___jp_3443_;
}
else
{
v___y_3444_ = v___y_3454_;
v___y_3445_ = v___y_3455_;
v___y_3446_ = v___y_3456_;
v___y_3447_ = v_a_3462_;
v___y_3448_ = v___y_3457_;
v___y_3449_ = v___y_3458_;
v___y_3450_ = v___y_3459_;
v___y_3451_ = v___x_3280_;
goto v___jp_3443_;
}
}
else
{
lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec_ref(v___x_3325_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3464_ = lean_ctor_get(v___x_3461_, 0);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3461_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3461_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_dec(v___x_3461_);
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
v___jp_3472_:
{
if (v___y_3479_ == 0)
{
v___y_3327_ = v___y_3474_;
v___y_3328_ = v___y_3476_;
v___y_3329_ = v___y_3478_;
v___y_3330_ = v___y_3475_;
v___y_3331_ = v___y_3473_;
v___y_3332_ = v___y_3477_;
goto v___jp_3326_;
}
else
{
v___y_3454_ = v___y_3473_;
v___y_3455_ = v___y_3474_;
v___y_3456_ = v___y_3475_;
v___y_3457_ = v___y_3476_;
v___y_3458_ = v___y_3478_;
v___y_3459_ = v___y_3477_;
v___y_3460_ = v___y_3479_;
goto v___jp_3453_;
}
}
v___jp_3480_:
{
uint8_t v_useDecide_3487_; 
v_useDecide_3487_ = lean_ctor_get_uint8(v_config_3173_, sizeof(void*)*1);
if (v_useDecide_3487_ == 0)
{
v___y_3473_ = v___y_3485_;
v___y_3474_ = v___y_3481_;
v___y_3475_ = v___y_3484_;
v___y_3476_ = v_isHEq_3482_;
v___y_3477_ = v___y_3486_;
v___y_3478_ = v___y_3483_;
v___y_3479_ = v___x_3280_;
goto v___jp_3472_;
}
else
{
uint8_t v___x_3488_; 
v___x_3488_ = l_Lean_Expr_hasFVar(v___x_3325_);
if (v___x_3488_ == 0)
{
v___y_3454_ = v___y_3485_;
v___y_3455_ = v___y_3481_;
v___y_3456_ = v___y_3484_;
v___y_3457_ = v_isHEq_3482_;
v___y_3458_ = v___y_3483_;
v___y_3459_ = v___y_3486_;
v___y_3460_ = v_useDecide_3487_;
goto v___jp_3453_;
}
else
{
v___y_3473_ = v___y_3485_;
v___y_3474_ = v___y_3481_;
v___y_3475_ = v___y_3484_;
v___y_3476_ = v_isHEq_3482_;
v___y_3477_ = v___y_3486_;
v___y_3478_ = v___y_3483_;
v___y_3479_ = v___x_3280_;
goto v___jp_3472_;
}
}
}
v___jp_3489_:
{
lean_object* v___x_3497_; 
v___x_3497_ = l_Lean_Meta_isExprDefEq(v___y_3494_, v___y_3492_, v___y_3495_, v___y_3496_, v___y_3493_, v___y_3490_);
if (lean_obj_tag(v___x_3497_) == 0)
{
lean_object* v_a_3498_; uint8_t v___x_3499_; 
v_a_3498_ = lean_ctor_get(v___x_3497_, 0);
lean_inc(v_a_3498_);
lean_dec_ref_known(v___x_3497_, 1);
v___x_3499_ = lean_unbox(v_a_3498_);
lean_dec(v_a_3498_);
if (v___x_3499_ == 0)
{
v___y_3481_ = v___y_3491_;
v_isHEq_3482_ = v___x_3184_;
v___y_3483_ = v___y_3495_;
v___y_3484_ = v___y_3496_;
v___y_3485_ = v___y_3493_;
v___y_3486_ = v___y_3490_;
goto v___jp_3480_;
}
else
{
lean_object* v___x_3500_; 
lean_dec_ref(v___x_3325_);
lean_dec_ref(v_config_3173_);
lean_inc(v_mvarId_3174_);
v___x_3500_ = l_Lean_MVarId_getType(v_mvarId_3174_, v___y_3495_, v___y_3496_, v___y_3493_, v___y_3490_);
if (lean_obj_tag(v___x_3500_) == 0)
{
lean_object* v_a_3501_; lean_object* v___x_3502_; lean_object* v___x_3503_; 
v_a_3501_ = lean_ctor_get(v___x_3500_, 0);
lean_inc(v_a_3501_);
lean_dec_ref_known(v___x_3500_, 1);
v___x_3502_ = l_Lean_LocalDecl_toExpr(v_val_3205_);
v___x_3503_ = l_Lean_Meta_mkEqOfHEq(v___x_3502_, v___x_3184_, v___y_3495_, v___y_3496_, v___y_3493_, v___y_3490_);
if (lean_obj_tag(v___x_3503_) == 0)
{
lean_object* v_a_3504_; lean_object* v___x_3505_; 
v_a_3504_ = lean_ctor_get(v___x_3503_, 0);
lean_inc(v_a_3504_);
lean_dec_ref_known(v___x_3503_, 1);
v___x_3505_ = l_Lean_Meta_mkNoConfusion(v_a_3501_, v_a_3504_, v___y_3495_, v___y_3496_, v___y_3493_, v___y_3490_);
if (lean_obj_tag(v___x_3505_) == 0)
{
lean_object* v_a_3506_; lean_object* v___x_3507_; 
v_a_3506_ = lean_ctor_get(v___x_3505_, 0);
lean_inc(v_a_3506_);
lean_dec_ref_known(v___x_3505_, 1);
v___x_3507_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3174_, v_a_3506_, v___y_3496_);
if (lean_obj_tag(v___x_3507_) == 0)
{
lean_object* v___x_3508_; lean_object* v___x_3509_; lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_dec_ref_known(v___x_3507_, 1);
v___x_3508_ = lean_box(v___x_3184_);
v___x_3509_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3509_, 0, v___x_3508_);
v___x_3510_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3510_, 0, v___x_3509_);
lean_ctor_set(v___x_3510_, 1, v___x_3209_);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
v_a_3191_ = v___x_3511_;
goto v___jp_3190_;
}
else
{
lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3519_; 
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
v_a_3512_ = lean_ctor_get(v___x_3507_, 0);
v_isSharedCheck_3519_ = !lean_is_exclusive(v___x_3507_);
if (v_isSharedCheck_3519_ == 0)
{
v___x_3514_ = v___x_3507_;
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3507_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3519_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3517_; 
if (v_isShared_3515_ == 0)
{
v___x_3517_ = v___x_3514_;
goto v_reusejp_3516_;
}
else
{
lean_object* v_reuseFailAlloc_3518_; 
v_reuseFailAlloc_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3518_, 0, v_a_3512_);
v___x_3517_ = v_reuseFailAlloc_3518_;
goto v_reusejp_3516_;
}
v_reusejp_3516_:
{
return v___x_3517_;
}
}
}
}
else
{
lean_object* v_a_3520_; lean_object* v___x_3522_; uint8_t v_isShared_3523_; uint8_t v_isSharedCheck_3527_; 
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3520_ = lean_ctor_get(v___x_3505_, 0);
v_isSharedCheck_3527_ = !lean_is_exclusive(v___x_3505_);
if (v_isSharedCheck_3527_ == 0)
{
v___x_3522_ = v___x_3505_;
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
else
{
lean_inc(v_a_3520_);
lean_dec(v___x_3505_);
v___x_3522_ = lean_box(0);
v_isShared_3523_ = v_isSharedCheck_3527_;
goto v_resetjp_3521_;
}
v_resetjp_3521_:
{
lean_object* v___x_3525_; 
if (v_isShared_3523_ == 0)
{
v___x_3525_ = v___x_3522_;
goto v_reusejp_3524_;
}
else
{
lean_object* v_reuseFailAlloc_3526_; 
v_reuseFailAlloc_3526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3526_, 0, v_a_3520_);
v___x_3525_ = v_reuseFailAlloc_3526_;
goto v_reusejp_3524_;
}
v_reusejp_3524_:
{
return v___x_3525_;
}
}
}
}
else
{
lean_object* v_a_3528_; lean_object* v___x_3530_; uint8_t v_isShared_3531_; uint8_t v_isSharedCheck_3535_; 
lean_dec(v_a_3501_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3528_ = lean_ctor_get(v___x_3503_, 0);
v_isSharedCheck_3535_ = !lean_is_exclusive(v___x_3503_);
if (v_isSharedCheck_3535_ == 0)
{
v___x_3530_ = v___x_3503_;
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
else
{
lean_inc(v_a_3528_);
lean_dec(v___x_3503_);
v___x_3530_ = lean_box(0);
v_isShared_3531_ = v_isSharedCheck_3535_;
goto v_resetjp_3529_;
}
v_resetjp_3529_:
{
lean_object* v___x_3533_; 
if (v_isShared_3531_ == 0)
{
v___x_3533_ = v___x_3530_;
goto v_reusejp_3532_;
}
else
{
lean_object* v_reuseFailAlloc_3534_; 
v_reuseFailAlloc_3534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3534_, 0, v_a_3528_);
v___x_3533_ = v_reuseFailAlloc_3534_;
goto v_reusejp_3532_;
}
v_reusejp_3532_:
{
return v___x_3533_;
}
}
}
}
else
{
lean_object* v_a_3536_; lean_object* v___x_3538_; uint8_t v_isShared_3539_; uint8_t v_isSharedCheck_3543_; 
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3536_ = lean_ctor_get(v___x_3500_, 0);
v_isSharedCheck_3543_ = !lean_is_exclusive(v___x_3500_);
if (v_isSharedCheck_3543_ == 0)
{
v___x_3538_ = v___x_3500_;
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
else
{
lean_inc(v_a_3536_);
lean_dec(v___x_3500_);
v___x_3538_ = lean_box(0);
v_isShared_3539_ = v_isSharedCheck_3543_;
goto v_resetjp_3537_;
}
v_resetjp_3537_:
{
lean_object* v___x_3541_; 
if (v_isShared_3539_ == 0)
{
v___x_3541_ = v___x_3538_;
goto v_reusejp_3540_;
}
else
{
lean_object* v_reuseFailAlloc_3542_; 
v_reuseFailAlloc_3542_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3542_, 0, v_a_3536_);
v___x_3541_ = v_reuseFailAlloc_3542_;
goto v_reusejp_3540_;
}
v_reusejp_3540_:
{
return v___x_3541_;
}
}
}
}
}
else
{
lean_object* v_a_3544_; lean_object* v___x_3546_; uint8_t v_isShared_3547_; uint8_t v_isSharedCheck_3551_; 
lean_dec_ref(v___x_3325_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3544_ = lean_ctor_get(v___x_3497_, 0);
v_isSharedCheck_3551_ = !lean_is_exclusive(v___x_3497_);
if (v_isSharedCheck_3551_ == 0)
{
v___x_3546_ = v___x_3497_;
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
else
{
lean_inc(v_a_3544_);
lean_dec(v___x_3497_);
v___x_3546_ = lean_box(0);
v_isShared_3547_ = v_isSharedCheck_3551_;
goto v_resetjp_3545_;
}
v_resetjp_3545_:
{
lean_object* v___x_3549_; 
if (v_isShared_3547_ == 0)
{
v___x_3549_ = v___x_3546_;
goto v_reusejp_3548_;
}
else
{
lean_object* v_reuseFailAlloc_3550_; 
v_reuseFailAlloc_3550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3550_, 0, v_a_3544_);
v___x_3549_ = v_reuseFailAlloc_3550_;
goto v_reusejp_3548_;
}
v_reusejp_3548_:
{
return v___x_3549_;
}
}
}
}
v___jp_3552_:
{
lean_object* v___x_3558_; 
lean_inc_ref(v___x_3325_);
v___x_3558_ = l_Lean_Meta_matchHEq_x3f(v___x_3325_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
if (lean_obj_tag(v___x_3558_) == 0)
{
lean_object* v_a_3559_; 
v_a_3559_ = lean_ctor_get(v___x_3558_, 0);
lean_inc(v_a_3559_);
lean_dec_ref_known(v___x_3558_, 1);
if (lean_obj_tag(v_a_3559_) == 1)
{
lean_object* v_val_3560_; lean_object* v_snd_3561_; lean_object* v_snd_3562_; lean_object* v_fst_3563_; lean_object* v_fst_3564_; lean_object* v_fst_3565_; lean_object* v_snd_3566_; lean_object* v___x_3567_; 
v_val_3560_ = lean_ctor_get(v_a_3559_, 0);
lean_inc(v_val_3560_);
lean_dec_ref_known(v_a_3559_, 1);
v_snd_3561_ = lean_ctor_get(v_val_3560_, 1);
lean_inc(v_snd_3561_);
v_snd_3562_ = lean_ctor_get(v_snd_3561_, 1);
lean_inc(v_snd_3562_);
v_fst_3563_ = lean_ctor_get(v_val_3560_, 0);
lean_inc(v_fst_3563_);
lean_dec(v_val_3560_);
v_fst_3564_ = lean_ctor_get(v_snd_3561_, 0);
lean_inc(v_fst_3564_);
lean_dec(v_snd_3561_);
v_fst_3565_ = lean_ctor_get(v_snd_3562_, 0);
lean_inc(v_fst_3565_);
v_snd_3566_ = lean_ctor_get(v_snd_3562_, 1);
lean_inc(v_snd_3566_);
lean_dec(v_snd_3562_);
v___x_3567_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3564_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
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
v___x_3570_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3566_, v___y_3554_, v___y_3555_, v___y_3556_, v___y_3557_);
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
v___y_3490_ = v___y_3557_;
v___y_3491_ = v_isEq_3553_;
v___y_3492_ = v_fst_3565_;
v___y_3493_ = v___y_3556_;
v___y_3494_ = v_fst_3563_;
v___y_3495_ = v___y_3554_;
v___y_3496_ = v___y_3555_;
goto v___jp_3489_;
}
else
{
if (v___x_3280_ == 0)
{
lean_dec(v_fst_3565_);
lean_dec(v_fst_3563_);
v___y_3481_ = v_isEq_3553_;
v_isHEq_3482_ = v___x_3184_;
v___y_3483_ = v___y_3554_;
v___y_3484_ = v___y_3555_;
v___y_3485_ = v___y_3556_;
v___y_3486_ = v___y_3557_;
goto v___jp_3480_;
}
else
{
v___y_3490_ = v___y_3557_;
v___y_3491_ = v_isEq_3553_;
v___y_3492_ = v_fst_3565_;
v___y_3493_ = v___y_3556_;
v___y_3494_ = v_fst_3563_;
v___y_3495_ = v___y_3554_;
v___y_3496_ = v___y_3555_;
goto v___jp_3489_;
}
}
}
else
{
lean_dec(v_a_3571_);
lean_dec(v_val_3569_);
lean_dec(v_fst_3565_);
lean_dec(v_fst_3563_);
v___y_3481_ = v_isEq_3553_;
v_isHEq_3482_ = v___x_3184_;
v___y_3483_ = v___y_3554_;
v___y_3484_ = v___y_3555_;
v___y_3485_ = v___y_3556_;
v___y_3486_ = v___y_3557_;
goto v___jp_3480_;
}
}
else
{
lean_object* v_a_3578_; lean_object* v___x_3580_; uint8_t v_isShared_3581_; uint8_t v_isSharedCheck_3585_; 
lean_dec(v_val_3569_);
lean_dec(v_fst_3565_);
lean_dec(v_fst_3563_);
lean_dec_ref(v___x_3325_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
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
lean_dec(v_fst_3565_);
lean_dec(v_fst_3563_);
v___y_3481_ = v_isEq_3553_;
v_isHEq_3482_ = v___x_3184_;
v___y_3483_ = v___y_3554_;
v___y_3484_ = v___y_3555_;
v___y_3485_ = v___y_3556_;
v___y_3486_ = v___y_3557_;
goto v___jp_3480_;
}
}
else
{
lean_object* v_a_3586_; lean_object* v___x_3588_; uint8_t v_isShared_3589_; uint8_t v_isSharedCheck_3593_; 
lean_dec(v_snd_3566_);
lean_dec(v_fst_3565_);
lean_dec(v_fst_3563_);
lean_dec_ref(v___x_3325_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
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
lean_dec(v_a_3559_);
v___y_3481_ = v_isEq_3553_;
v_isHEq_3482_ = v___x_3280_;
v___y_3483_ = v___y_3554_;
v___y_3484_ = v___y_3555_;
v___y_3485_ = v___y_3556_;
v___y_3486_ = v___y_3557_;
goto v___jp_3480_;
}
}
else
{
lean_object* v_a_3594_; lean_object* v___x_3596_; uint8_t v_isShared_3597_; uint8_t v_isSharedCheck_3601_; 
lean_dec_ref(v___x_3325_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3594_ = lean_ctor_get(v___x_3558_, 0);
v_isSharedCheck_3601_ = !lean_is_exclusive(v___x_3558_);
if (v_isSharedCheck_3601_ == 0)
{
v___x_3596_ = v___x_3558_;
v_isShared_3597_ = v_isSharedCheck_3601_;
goto v_resetjp_3595_;
}
else
{
lean_inc(v_a_3594_);
lean_dec(v___x_3558_);
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
lean_inc_ref(v___x_3325_);
v___x_3607_ = l_Lean_Meta_matchEq_x3f(v___x_3325_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3607_) == 0)
{
lean_object* v_a_3608_; 
v_a_3608_ = lean_ctor_get(v___x_3607_, 0);
lean_inc(v_a_3608_);
lean_dec_ref_known(v___x_3607_, 1);
if (lean_obj_tag(v_a_3608_) == 1)
{
lean_object* v_val_3609_; lean_object* v_snd_3610_; lean_object* v_fst_3611_; lean_object* v_snd_3612_; lean_object* v___x_3613_; 
v_val_3609_ = lean_ctor_get(v_a_3608_, 0);
lean_inc(v_val_3609_);
lean_dec_ref_known(v_a_3608_, 1);
v_snd_3610_ = lean_ctor_get(v_val_3609_, 1);
lean_inc(v_snd_3610_);
lean_dec(v_val_3609_);
v_fst_3611_ = lean_ctor_get(v_snd_3610_, 0);
lean_inc(v_fst_3611_);
v_snd_3612_ = lean_ctor_get(v_snd_3610_, 1);
lean_inc(v_snd_3612_);
lean_dec(v_snd_3610_);
v___x_3613_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_3611_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3613_) == 0)
{
lean_object* v_a_3614_; 
v_a_3614_ = lean_ctor_get(v___x_3613_, 0);
lean_inc(v_a_3614_);
lean_dec_ref_known(v___x_3613_, 1);
if (lean_obj_tag(v_a_3614_) == 1)
{
lean_object* v_val_3615_; lean_object* v___x_3616_; 
v_val_3615_ = lean_ctor_get(v_a_3614_, 0);
lean_inc(v_val_3615_);
lean_dec_ref_known(v_a_3614_, 1);
v___x_3616_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_3612_, v___y_3603_, v___y_3604_, v___y_3605_, v___y_3606_);
if (lean_obj_tag(v___x_3616_) == 0)
{
lean_object* v_a_3617_; 
v_a_3617_ = lean_ctor_get(v___x_3616_, 0);
lean_inc(v_a_3617_);
lean_dec_ref_known(v___x_3616_, 1);
if (lean_obj_tag(v_a_3617_) == 1)
{
lean_object* v_toConstantVal_3618_; lean_object* v_val_3619_; lean_object* v_toConstantVal_3620_; lean_object* v_name_3621_; lean_object* v_name_3622_; uint8_t v___x_3623_; 
v_toConstantVal_3618_ = lean_ctor_get(v_val_3615_, 0);
lean_inc_ref(v_toConstantVal_3618_);
lean_dec(v_val_3615_);
v_val_3619_ = lean_ctor_get(v_a_3617_, 0);
lean_inc(v_val_3619_);
lean_dec_ref_known(v_a_3617_, 1);
v_toConstantVal_3620_ = lean_ctor_get(v_val_3619_, 0);
lean_inc_ref(v_toConstantVal_3620_);
lean_dec(v_val_3619_);
v_name_3621_ = lean_ctor_get(v_toConstantVal_3618_, 0);
lean_inc(v_name_3621_);
lean_dec_ref(v_toConstantVal_3618_);
v_name_3622_ = lean_ctor_get(v_toConstantVal_3620_, 0);
lean_inc(v_name_3622_);
lean_dec_ref(v_toConstantVal_3620_);
v___x_3623_ = lean_name_eq(v_name_3621_, v_name_3622_);
lean_dec(v_name_3622_);
lean_dec(v_name_3621_);
if (v___x_3623_ == 0)
{
lean_dec_ref(v___x_3325_);
lean_dec_ref(v_config_3173_);
v___y_3211_ = v___y_3606_;
v___y_3212_ = v___y_3603_;
v___y_3213_ = v___y_3605_;
v___y_3214_ = v___y_3604_;
goto v___jp_3210_;
}
else
{
if (v___x_3280_ == 0)
{
lean_del_object(v___x_3207_);
v_isEq_3553_ = v___x_3184_;
v___y_3554_ = v___y_3603_;
v___y_3555_ = v___y_3604_;
v___y_3556_ = v___y_3605_;
v___y_3557_ = v___y_3606_;
goto v___jp_3552_;
}
else
{
lean_dec_ref(v___x_3325_);
lean_dec_ref(v_config_3173_);
v___y_3211_ = v___y_3606_;
v___y_3212_ = v___y_3603_;
v___y_3213_ = v___y_3605_;
v___y_3214_ = v___y_3604_;
goto v___jp_3210_;
}
}
}
else
{
lean_dec(v_a_3617_);
lean_dec(v_val_3615_);
lean_del_object(v___x_3207_);
v_isEq_3553_ = v___x_3184_;
v___y_3554_ = v___y_3603_;
v___y_3555_ = v___y_3604_;
v___y_3556_ = v___y_3605_;
v___y_3557_ = v___y_3606_;
goto v___jp_3552_;
}
}
else
{
lean_object* v_a_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3631_; 
lean_dec(v_val_3615_);
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3624_ = lean_ctor_get(v___x_3616_, 0);
v_isSharedCheck_3631_ = !lean_is_exclusive(v___x_3616_);
if (v_isSharedCheck_3631_ == 0)
{
v___x_3626_ = v___x_3616_;
v_isShared_3627_ = v_isSharedCheck_3631_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_a_3624_);
lean_dec(v___x_3616_);
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
lean_dec(v_a_3614_);
lean_dec(v_snd_3612_);
lean_del_object(v___x_3207_);
v_isEq_3553_ = v___x_3184_;
v___y_3554_ = v___y_3603_;
v___y_3555_ = v___y_3604_;
v___y_3556_ = v___y_3605_;
v___y_3557_ = v___y_3606_;
goto v___jp_3552_;
}
}
else
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3639_; 
lean_dec(v_snd_3612_);
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3632_ = lean_ctor_get(v___x_3613_, 0);
v_isSharedCheck_3639_ = !lean_is_exclusive(v___x_3613_);
if (v_isSharedCheck_3639_ == 0)
{
v___x_3634_ = v___x_3613_;
v_isShared_3635_ = v_isSharedCheck_3639_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3613_);
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
lean_dec(v_a_3608_);
lean_del_object(v___x_3207_);
v_isEq_3553_ = v___x_3280_;
v___y_3554_ = v___y_3603_;
v___y_3555_ = v___y_3604_;
v___y_3556_ = v___y_3605_;
v___y_3557_ = v___y_3606_;
goto v___jp_3552_;
}
}
else
{
lean_object* v_a_3640_; lean_object* v___x_3642_; uint8_t v_isShared_3643_; uint8_t v_isSharedCheck_3647_; 
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3640_ = lean_ctor_get(v___x_3607_, 0);
v_isSharedCheck_3647_ = !lean_is_exclusive(v___x_3607_);
if (v_isSharedCheck_3647_ == 0)
{
v___x_3642_ = v___x_3607_;
v_isShared_3643_ = v_isSharedCheck_3647_;
goto v_resetjp_3641_;
}
else
{
lean_inc(v_a_3640_);
lean_dec(v___x_3607_);
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
v___jp_3648_:
{
lean_object* v___x_3653_; 
lean_inc_ref(v___x_3325_);
v___x_3653_ = l_Lean_refutableHasNotBit_x3f(v___x_3325_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3653_) == 0)
{
lean_object* v_a_3654_; 
v_a_3654_ = lean_ctor_get(v___x_3653_, 0);
lean_inc(v_a_3654_);
lean_dec_ref_known(v___x_3653_, 1);
if (lean_obj_tag(v_a_3654_) == 1)
{
lean_object* v_val_3655_; lean_object* v___x_3657_; uint8_t v_isShared_3658_; uint8_t v_isSharedCheck_3695_; 
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec_ref(v_config_3173_);
v_val_3655_ = lean_ctor_get(v_a_3654_, 0);
v_isSharedCheck_3695_ = !lean_is_exclusive(v_a_3654_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3657_ = v_a_3654_;
v_isShared_3658_ = v_isSharedCheck_3695_;
goto v_resetjp_3656_;
}
else
{
lean_inc(v_val_3655_);
lean_dec(v_a_3654_);
v___x_3657_ = lean_box(0);
v_isShared_3658_ = v_isSharedCheck_3695_;
goto v_resetjp_3656_;
}
v_resetjp_3656_:
{
lean_object* v___x_3659_; 
lean_inc(v_mvarId_3174_);
v___x_3659_ = l_Lean_MVarId_getType(v_mvarId_3174_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3659_) == 0)
{
lean_object* v_a_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; 
v_a_3660_ = lean_ctor_get(v___x_3659_, 0);
lean_inc(v_a_3660_);
lean_dec_ref_known(v___x_3659_, 1);
v___x_3661_ = l_Lean_LocalDecl_toExpr(v_val_3205_);
v___x_3662_ = l_Lean_Meta_mkAbsurd(v_a_3660_, v_val_3655_, v___x_3661_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3664_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
lean_inc(v_a_3663_);
lean_dec_ref_known(v___x_3662_, 1);
v___x_3664_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3174_, v_a_3663_, v___y_3650_);
if (lean_obj_tag(v___x_3664_) == 0)
{
lean_object* v___x_3665_; lean_object* v___x_3667_; 
lean_dec_ref_known(v___x_3664_, 1);
v___x_3665_ = lean_box(v___x_3184_);
if (v_isShared_3658_ == 0)
{
lean_ctor_set(v___x_3657_, 0, v___x_3665_);
v___x_3667_ = v___x_3657_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3670_; 
v_reuseFailAlloc_3670_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3670_, 0, v___x_3665_);
v___x_3667_ = v_reuseFailAlloc_3670_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
lean_object* v___x_3668_; lean_object* v___x_3669_; 
v___x_3668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___x_3667_);
lean_ctor_set(v___x_3668_, 1, v___x_3209_);
v___x_3669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3669_, 0, v___x_3668_);
v_a_3191_ = v___x_3669_;
goto v___jp_3190_;
}
}
else
{
lean_object* v_a_3671_; lean_object* v___x_3673_; uint8_t v_isShared_3674_; uint8_t v_isSharedCheck_3678_; 
lean_del_object(v___x_3657_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
v_a_3671_ = lean_ctor_get(v___x_3664_, 0);
v_isSharedCheck_3678_ = !lean_is_exclusive(v___x_3664_);
if (v_isSharedCheck_3678_ == 0)
{
v___x_3673_ = v___x_3664_;
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
else
{
lean_inc(v_a_3671_);
lean_dec(v___x_3664_);
v___x_3673_ = lean_box(0);
v_isShared_3674_ = v_isSharedCheck_3678_;
goto v_resetjp_3672_;
}
v_resetjp_3672_:
{
lean_object* v___x_3676_; 
if (v_isShared_3674_ == 0)
{
v___x_3676_ = v___x_3673_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_a_3671_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
return v___x_3676_;
}
}
}
}
else
{
lean_object* v_a_3679_; lean_object* v___x_3681_; uint8_t v_isShared_3682_; uint8_t v_isSharedCheck_3686_; 
lean_del_object(v___x_3657_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3679_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3681_ = v___x_3662_;
v_isShared_3682_ = v_isSharedCheck_3686_;
goto v_resetjp_3680_;
}
else
{
lean_inc(v_a_3679_);
lean_dec(v___x_3662_);
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
lean_del_object(v___x_3657_);
lean_dec(v_val_3655_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3687_ = lean_ctor_get(v___x_3659_, 0);
v_isSharedCheck_3694_ = !lean_is_exclusive(v___x_3659_);
if (v_isSharedCheck_3694_ == 0)
{
v___x_3689_ = v___x_3659_;
v_isShared_3690_ = v_isSharedCheck_3694_;
goto v_resetjp_3688_;
}
else
{
lean_inc(v_a_3687_);
lean_dec(v___x_3659_);
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
}
else
{
lean_object* v___x_3696_; 
lean_dec(v_a_3654_);
lean_inc_ref(v___x_3325_);
v___x_3696_ = l_Lean_Meta_matchNe_x3f(v___x_3325_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3696_) == 0)
{
lean_object* v_a_3697_; 
v_a_3697_ = lean_ctor_get(v___x_3696_, 0);
lean_inc(v_a_3697_);
lean_dec_ref_known(v___x_3696_, 1);
if (lean_obj_tag(v_a_3697_) == 1)
{
lean_object* v_val_3698_; lean_object* v___x_3700_; uint8_t v_isShared_3701_; uint8_t v_isSharedCheck_3768_; 
v_val_3698_ = lean_ctor_get(v_a_3697_, 0);
v_isSharedCheck_3768_ = !lean_is_exclusive(v_a_3697_);
if (v_isSharedCheck_3768_ == 0)
{
v___x_3700_ = v_a_3697_;
v_isShared_3701_ = v_isSharedCheck_3768_;
goto v_resetjp_3699_;
}
else
{
lean_inc(v_val_3698_);
lean_dec(v_a_3697_);
v___x_3700_ = lean_box(0);
v_isShared_3701_ = v_isSharedCheck_3768_;
goto v_resetjp_3699_;
}
v_resetjp_3699_:
{
lean_object* v_snd_3702_; lean_object* v_fst_3703_; lean_object* v_snd_3704_; lean_object* v___x_3706_; uint8_t v_isShared_3707_; uint8_t v_isSharedCheck_3767_; 
v_snd_3702_ = lean_ctor_get(v_val_3698_, 1);
lean_inc(v_snd_3702_);
lean_dec(v_val_3698_);
v_fst_3703_ = lean_ctor_get(v_snd_3702_, 0);
v_snd_3704_ = lean_ctor_get(v_snd_3702_, 1);
v_isSharedCheck_3767_ = !lean_is_exclusive(v_snd_3702_);
if (v_isSharedCheck_3767_ == 0)
{
v___x_3706_ = v_snd_3702_;
v_isShared_3707_ = v_isSharedCheck_3767_;
goto v_resetjp_3705_;
}
else
{
lean_inc(v_snd_3704_);
lean_inc(v_fst_3703_);
lean_dec(v_snd_3702_);
v___x_3706_ = lean_box(0);
v_isShared_3707_ = v_isSharedCheck_3767_;
goto v_resetjp_3705_;
}
v_resetjp_3705_:
{
lean_object* v___x_3708_; 
lean_inc(v_fst_3703_);
v___x_3708_ = l_Lean_Meta_isExprDefEq(v_fst_3703_, v_snd_3704_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3708_) == 0)
{
lean_object* v_a_3709_; uint8_t v___x_3710_; 
v_a_3709_ = lean_ctor_get(v___x_3708_, 0);
lean_inc(v_a_3709_);
lean_dec_ref_known(v___x_3708_, 1);
v___x_3710_ = lean_unbox(v_a_3709_);
lean_dec(v_a_3709_);
if (v___x_3710_ == 0)
{
lean_del_object(v___x_3706_);
lean_dec(v_fst_3703_);
lean_del_object(v___x_3700_);
v___y_3603_ = v___y_3649_;
v___y_3604_ = v___y_3650_;
v___y_3605_ = v___y_3651_;
v___y_3606_ = v___y_3652_;
goto v___jp_3602_;
}
else
{
lean_object* v___x_3711_; 
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec_ref(v_config_3173_);
lean_inc(v_mvarId_3174_);
v___x_3711_ = l_Lean_MVarId_getType(v_mvarId_3174_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3711_) == 0)
{
lean_object* v_a_3712_; lean_object* v___x_3713_; 
v_a_3712_ = lean_ctor_get(v___x_3711_, 0);
lean_inc(v_a_3712_);
lean_dec_ref_known(v___x_3711_, 1);
v___x_3713_ = l_Lean_Meta_mkEqRefl(v_fst_3703_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3713_) == 0)
{
lean_object* v_a_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; 
v_a_3714_ = lean_ctor_get(v___x_3713_, 0);
lean_inc(v_a_3714_);
lean_dec_ref_known(v___x_3713_, 1);
v___x_3715_ = l_Lean_LocalDecl_toExpr(v_val_3205_);
v___x_3716_ = l_Lean_Meta_mkAbsurd(v_a_3712_, v_a_3714_, v___x_3715_, v___y_3649_, v___y_3650_, v___y_3651_, v___y_3652_);
if (lean_obj_tag(v___x_3716_) == 0)
{
lean_object* v_a_3717_; lean_object* v___x_3718_; 
v_a_3717_ = lean_ctor_get(v___x_3716_, 0);
lean_inc(v_a_3717_);
lean_dec_ref_known(v___x_3716_, 1);
v___x_3718_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3174_, v_a_3717_, v___y_3650_);
if (lean_obj_tag(v___x_3718_) == 0)
{
lean_object* v___x_3719_; lean_object* v___x_3721_; 
lean_dec_ref_known(v___x_3718_, 1);
v___x_3719_ = lean_box(v___x_3184_);
if (v_isShared_3701_ == 0)
{
lean_ctor_set(v___x_3700_, 0, v___x_3719_);
v___x_3721_ = v___x_3700_;
goto v_reusejp_3720_;
}
else
{
lean_object* v_reuseFailAlloc_3726_; 
v_reuseFailAlloc_3726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3726_, 0, v___x_3719_);
v___x_3721_ = v_reuseFailAlloc_3726_;
goto v_reusejp_3720_;
}
v_reusejp_3720_:
{
lean_object* v___x_3723_; 
if (v_isShared_3707_ == 0)
{
lean_ctor_set(v___x_3706_, 1, v___x_3209_);
lean_ctor_set(v___x_3706_, 0, v___x_3721_);
v___x_3723_ = v___x_3706_;
goto v_reusejp_3722_;
}
else
{
lean_object* v_reuseFailAlloc_3725_; 
v_reuseFailAlloc_3725_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3725_, 0, v___x_3721_);
lean_ctor_set(v_reuseFailAlloc_3725_, 1, v___x_3209_);
v___x_3723_ = v_reuseFailAlloc_3725_;
goto v_reusejp_3722_;
}
v_reusejp_3722_:
{
lean_object* v___x_3724_; 
v___x_3724_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3724_, 0, v___x_3723_);
v_a_3191_ = v___x_3724_;
goto v___jp_3190_;
}
}
}
else
{
lean_object* v_a_3727_; lean_object* v___x_3729_; uint8_t v_isShared_3730_; uint8_t v_isSharedCheck_3734_; 
lean_del_object(v___x_3706_);
lean_del_object(v___x_3700_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
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
lean_object* v_a_3735_; lean_object* v___x_3737_; uint8_t v_isShared_3738_; uint8_t v_isSharedCheck_3742_; 
lean_del_object(v___x_3706_);
lean_del_object(v___x_3700_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3735_ = lean_ctor_get(v___x_3716_, 0);
v_isSharedCheck_3742_ = !lean_is_exclusive(v___x_3716_);
if (v_isSharedCheck_3742_ == 0)
{
v___x_3737_ = v___x_3716_;
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
else
{
lean_inc(v_a_3735_);
lean_dec(v___x_3716_);
v___x_3737_ = lean_box(0);
v_isShared_3738_ = v_isSharedCheck_3742_;
goto v_resetjp_3736_;
}
v_resetjp_3736_:
{
lean_object* v___x_3740_; 
if (v_isShared_3738_ == 0)
{
v___x_3740_ = v___x_3737_;
goto v_reusejp_3739_;
}
else
{
lean_object* v_reuseFailAlloc_3741_; 
v_reuseFailAlloc_3741_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3741_, 0, v_a_3735_);
v___x_3740_ = v_reuseFailAlloc_3741_;
goto v_reusejp_3739_;
}
v_reusejp_3739_:
{
return v___x_3740_;
}
}
}
}
else
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3750_; 
lean_dec(v_a_3712_);
lean_del_object(v___x_3706_);
lean_del_object(v___x_3700_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3743_ = lean_ctor_get(v___x_3713_, 0);
v_isSharedCheck_3750_ = !lean_is_exclusive(v___x_3713_);
if (v_isSharedCheck_3750_ == 0)
{
v___x_3745_ = v___x_3713_;
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3713_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3750_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3748_; 
if (v_isShared_3746_ == 0)
{
v___x_3748_ = v___x_3745_;
goto v_reusejp_3747_;
}
else
{
lean_object* v_reuseFailAlloc_3749_; 
v_reuseFailAlloc_3749_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3749_, 0, v_a_3743_);
v___x_3748_ = v_reuseFailAlloc_3749_;
goto v_reusejp_3747_;
}
v_reusejp_3747_:
{
return v___x_3748_;
}
}
}
}
else
{
lean_object* v_a_3751_; lean_object* v___x_3753_; uint8_t v_isShared_3754_; uint8_t v_isSharedCheck_3758_; 
lean_del_object(v___x_3706_);
lean_dec(v_fst_3703_);
lean_del_object(v___x_3700_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3751_ = lean_ctor_get(v___x_3711_, 0);
v_isSharedCheck_3758_ = !lean_is_exclusive(v___x_3711_);
if (v_isSharedCheck_3758_ == 0)
{
v___x_3753_ = v___x_3711_;
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
else
{
lean_inc(v_a_3751_);
lean_dec(v___x_3711_);
v___x_3753_ = lean_box(0);
v_isShared_3754_ = v_isSharedCheck_3758_;
goto v_resetjp_3752_;
}
v_resetjp_3752_:
{
lean_object* v___x_3756_; 
if (v_isShared_3754_ == 0)
{
v___x_3756_ = v___x_3753_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3757_; 
v_reuseFailAlloc_3757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3757_, 0, v_a_3751_);
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
}
else
{
lean_object* v_a_3759_; lean_object* v___x_3761_; uint8_t v_isShared_3762_; uint8_t v_isSharedCheck_3766_; 
lean_del_object(v___x_3706_);
lean_dec(v_fst_3703_);
lean_del_object(v___x_3700_);
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3759_ = lean_ctor_get(v___x_3708_, 0);
v_isSharedCheck_3766_ = !lean_is_exclusive(v___x_3708_);
if (v_isSharedCheck_3766_ == 0)
{
v___x_3761_ = v___x_3708_;
v_isShared_3762_ = v_isSharedCheck_3766_;
goto v_resetjp_3760_;
}
else
{
lean_inc(v_a_3759_);
lean_dec(v___x_3708_);
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
}
else
{
lean_dec(v_a_3697_);
v___y_3603_ = v___y_3649_;
v___y_3604_ = v___y_3650_;
v___y_3605_ = v___y_3651_;
v___y_3606_ = v___y_3652_;
goto v___jp_3602_;
}
}
else
{
lean_object* v_a_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3776_; 
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3769_ = lean_ctor_get(v___x_3696_, 0);
v_isSharedCheck_3776_ = !lean_is_exclusive(v___x_3696_);
if (v_isSharedCheck_3776_ == 0)
{
v___x_3771_ = v___x_3696_;
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_a_3769_);
lean_dec(v___x_3696_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3776_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3774_; 
if (v_isShared_3772_ == 0)
{
v___x_3774_ = v___x_3771_;
goto v_reusejp_3773_;
}
else
{
lean_object* v_reuseFailAlloc_3775_; 
v_reuseFailAlloc_3775_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3775_, 0, v_a_3769_);
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
}
else
{
lean_object* v_a_3777_; lean_object* v___x_3779_; uint8_t v_isShared_3780_; uint8_t v_isSharedCheck_3784_; 
lean_dec_ref(v___x_3325_);
lean_del_object(v___x_3207_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3777_ = lean_ctor_get(v___x_3653_, 0);
v_isSharedCheck_3784_ = !lean_is_exclusive(v___x_3653_);
if (v_isSharedCheck_3784_ == 0)
{
v___x_3779_ = v___x_3653_;
v_isShared_3780_ = v_isSharedCheck_3784_;
goto v_resetjp_3778_;
}
else
{
lean_inc(v_a_3777_);
lean_dec(v___x_3653_);
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
else
{
lean_del_object(v___x_3207_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
v_a_3199_ = v___x_3251_;
goto v___jp_3198_;
}
v___jp_3210_:
{
lean_object* v___x_3215_; 
lean_inc(v_mvarId_3174_);
v___x_3215_ = l_Lean_MVarId_getType(v_mvarId_3174_, v___y_3212_, v___y_3214_, v___y_3213_, v___y_3211_);
if (lean_obj_tag(v___x_3215_) == 0)
{
lean_object* v_a_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; 
v_a_3216_ = lean_ctor_get(v___x_3215_, 0);
lean_inc(v_a_3216_);
lean_dec_ref_known(v___x_3215_, 1);
v___x_3217_ = l_Lean_LocalDecl_toExpr(v_val_3205_);
v___x_3218_ = l_Lean_Meta_mkNoConfusion(v_a_3216_, v___x_3217_, v___y_3212_, v___y_3214_, v___y_3213_, v___y_3211_);
if (lean_obj_tag(v___x_3218_) == 0)
{
lean_object* v_a_3219_; lean_object* v___x_3220_; 
v_a_3219_ = lean_ctor_get(v___x_3218_, 0);
lean_inc(v_a_3219_);
lean_dec_ref_known(v___x_3218_, 1);
v___x_3220_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3174_, v_a_3219_, v___y_3214_);
if (lean_obj_tag(v___x_3220_) == 0)
{
lean_object* v___x_3221_; lean_object* v___x_3223_; 
lean_dec_ref_known(v___x_3220_, 1);
v___x_3221_ = lean_box(v___x_3184_);
if (v_isShared_3208_ == 0)
{
lean_ctor_set(v___x_3207_, 0, v___x_3221_);
v___x_3223_ = v___x_3207_;
goto v_reusejp_3222_;
}
else
{
lean_object* v_reuseFailAlloc_3226_; 
v_reuseFailAlloc_3226_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3226_, 0, v___x_3221_);
v___x_3223_ = v_reuseFailAlloc_3226_;
goto v_reusejp_3222_;
}
v_reusejp_3222_:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3224_, 0, v___x_3223_);
lean_ctor_set(v___x_3224_, 1, v___x_3209_);
v___x_3225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3224_);
v_a_3191_ = v___x_3225_;
goto v___jp_3190_;
}
}
else
{
lean_object* v_a_3227_; lean_object* v___x_3229_; uint8_t v_isShared_3230_; uint8_t v_isSharedCheck_3234_; 
lean_del_object(v___x_3207_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
v_a_3227_ = lean_ctor_get(v___x_3220_, 0);
v_isSharedCheck_3234_ = !lean_is_exclusive(v___x_3220_);
if (v_isSharedCheck_3234_ == 0)
{
v___x_3229_ = v___x_3220_;
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
else
{
lean_inc(v_a_3227_);
lean_dec(v___x_3220_);
v___x_3229_ = lean_box(0);
v_isShared_3230_ = v_isSharedCheck_3234_;
goto v_resetjp_3228_;
}
v_resetjp_3228_:
{
lean_object* v___x_3232_; 
if (v_isShared_3230_ == 0)
{
v___x_3232_ = v___x_3229_;
goto v_reusejp_3231_;
}
else
{
lean_object* v_reuseFailAlloc_3233_; 
v_reuseFailAlloc_3233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3233_, 0, v_a_3227_);
v___x_3232_ = v_reuseFailAlloc_3233_;
goto v_reusejp_3231_;
}
v_reusejp_3231_:
{
return v___x_3232_;
}
}
}
}
else
{
lean_object* v_a_3235_; lean_object* v___x_3237_; uint8_t v_isShared_3238_; uint8_t v_isSharedCheck_3242_; 
lean_del_object(v___x_3207_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3235_ = lean_ctor_get(v___x_3218_, 0);
v_isSharedCheck_3242_ = !lean_is_exclusive(v___x_3218_);
if (v_isSharedCheck_3242_ == 0)
{
v___x_3237_ = v___x_3218_;
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
else
{
lean_inc(v_a_3235_);
lean_dec(v___x_3218_);
v___x_3237_ = lean_box(0);
v_isShared_3238_ = v_isSharedCheck_3242_;
goto v_resetjp_3236_;
}
v_resetjp_3236_:
{
lean_object* v___x_3240_; 
if (v_isShared_3238_ == 0)
{
v___x_3240_ = v___x_3237_;
goto v_reusejp_3239_;
}
else
{
lean_object* v_reuseFailAlloc_3241_; 
v_reuseFailAlloc_3241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3241_, 0, v_a_3235_);
v___x_3240_ = v_reuseFailAlloc_3241_;
goto v_reusejp_3239_;
}
v_reusejp_3239_:
{
return v___x_3240_;
}
}
}
}
else
{
lean_object* v_a_3243_; lean_object* v___x_3245_; uint8_t v_isShared_3246_; uint8_t v_isSharedCheck_3250_; 
lean_del_object(v___x_3207_);
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
v_a_3243_ = lean_ctor_get(v___x_3215_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3215_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3245_ = v___x_3215_;
v_isShared_3246_ = v_isSharedCheck_3250_;
goto v_resetjp_3244_;
}
else
{
lean_inc(v_a_3243_);
lean_dec(v___x_3215_);
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
v___jp_3252_:
{
lean_object* v_searchFuel_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v_searchFuel_3257_ = lean_ctor_get(v_config_3173_, 0);
v___x_3258_ = l_Lean_LocalDecl_fvarId(v_val_3205_);
lean_dec(v_val_3205_);
lean_inc(v_searchFuel_3257_);
lean_inc(v_mvarId_3174_);
v___x_3259_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3174_, v___x_3258_, v_searchFuel_3257_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
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
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
v_a_3199_ = v___x_3251_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; 
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v___x_3262_ = lean_box(v___x_3184_);
v___x_3263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3263_, 0, v___x_3262_);
v___x_3264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3264_, 0, v___x_3263_);
lean_ctor_set(v___x_3264_, 1, v___x_3209_);
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v___x_3264_);
v_a_3191_ = v___x_3265_;
goto v___jp_3190_;
}
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3273_; 
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3266_ = lean_ctor_get(v___x_3259_, 0);
v_isSharedCheck_3273_ = !lean_is_exclusive(v___x_3259_);
if (v_isSharedCheck_3273_ == 0)
{
v___x_3268_ = v___x_3259_;
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
else
{
lean_inc(v_a_3266_);
lean_dec(v___x_3259_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3273_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3271_; 
if (v_isShared_3269_ == 0)
{
v___x_3271_ = v___x_3268_;
goto v_reusejp_3270_;
}
else
{
lean_object* v_reuseFailAlloc_3272_; 
v_reuseFailAlloc_3272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3272_, 0, v_a_3266_);
v___x_3271_ = v_reuseFailAlloc_3272_;
goto v_reusejp_3270_;
}
v_reusejp_3270_:
{
return v___x_3271_;
}
}
}
}
v___jp_3274_:
{
if (v___y_3279_ == 0)
{
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
v_a_3199_ = v___x_3251_;
goto v___jp_3198_;
}
else
{
v___y_3253_ = v___y_3275_;
v___y_3254_ = v___y_3276_;
v___y_3255_ = v___y_3277_;
v___y_3256_ = v___y_3278_;
goto v___jp_3252_;
}
}
v___jp_3281_:
{
if (v___y_3286_ == 0)
{
v___y_3253_ = v___y_3282_;
v___y_3254_ = v___y_3283_;
v___y_3255_ = v___y_3284_;
v___y_3256_ = v___y_3285_;
goto v___jp_3252_;
}
else
{
v___y_3275_ = v___y_3282_;
v___y_3276_ = v___y_3283_;
v___y_3277_ = v___y_3284_;
v___y_3278_ = v___y_3285_;
v___y_3279_ = v___x_3280_;
goto v___jp_3274_;
}
}
v___jp_3287_:
{
if (v___y_3293_ == 0)
{
v___y_3275_ = v___y_3288_;
v___y_3276_ = v___y_3289_;
v___y_3277_ = v___y_3290_;
v___y_3278_ = v___y_3292_;
v___y_3279_ = v___x_3280_;
goto v___jp_3274_;
}
else
{
v___y_3282_ = v___y_3288_;
v___y_3283_ = v___y_3289_;
v___y_3284_ = v___y_3290_;
v___y_3285_ = v___y_3292_;
v___y_3286_ = v___y_3291_;
goto v___jp_3281_;
}
}
v___jp_3294_:
{
uint8_t v_emptyType_3301_; 
v_emptyType_3301_ = lean_ctor_get_uint8(v_config_3173_, sizeof(void*)*1 + 1);
if (v_emptyType_3301_ == 0)
{
v___y_3288_ = v___y_3297_;
v___y_3289_ = v___y_3298_;
v___y_3290_ = v___y_3299_;
v___y_3291_ = v___y_3296_;
v___y_3292_ = v___y_3300_;
v___y_3293_ = v___x_3280_;
goto v___jp_3287_;
}
else
{
if (v___y_3295_ == 0)
{
v___y_3282_ = v___y_3297_;
v___y_3283_ = v___y_3298_;
v___y_3284_ = v___y_3299_;
v___y_3285_ = v___y_3300_;
v___y_3286_ = v___y_3296_;
goto v___jp_3281_;
}
else
{
v___y_3288_ = v___y_3297_;
v___y_3289_ = v___y_3298_;
v___y_3290_ = v___y_3299_;
v___y_3291_ = v___y_3296_;
v___y_3292_ = v___y_3300_;
v___y_3293_ = v___x_3280_;
goto v___jp_3287_;
}
}
}
v___jp_3302_:
{
if (v___y_3309_ == 0)
{
v___y_3295_ = v___y_3304_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3308_;
v___y_3298_ = v___y_3303_;
v___y_3299_ = v___y_3305_;
v___y_3300_ = v___y_3307_;
goto v___jp_3294_;
}
else
{
lean_object* v___x_3310_; 
lean_inc(v_val_3205_);
lean_inc(v_mvarId_3174_);
v___x_3310_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3174_, v_val_3205_, v___y_3308_, v___y_3303_, v___y_3305_, v___y_3307_);
if (lean_obj_tag(v___x_3310_) == 0)
{
lean_object* v_a_3311_; uint8_t v___x_3312_; 
v_a_3311_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_a_3311_);
lean_dec_ref_known(v___x_3310_, 1);
v___x_3312_ = lean_unbox(v_a_3311_);
lean_dec(v_a_3311_);
if (v___x_3312_ == 0)
{
v___y_3295_ = v___y_3304_;
v___y_3296_ = v___y_3306_;
v___y_3297_ = v___y_3308_;
v___y_3298_ = v___y_3303_;
v___y_3299_ = v___y_3305_;
v___y_3300_ = v___y_3307_;
goto v___jp_3294_;
}
else
{
lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; 
lean_dec(v_val_3205_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v___x_3313_ = lean_box(v___x_3184_);
v___x_3314_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
v___x_3315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3314_);
lean_ctor_set(v___x_3315_, 1, v___x_3209_);
v___x_3316_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3315_);
v_a_3191_ = v___x_3316_;
goto v___jp_3190_;
}
}
else
{
lean_object* v_a_3317_; lean_object* v___x_3319_; uint8_t v_isShared_3320_; uint8_t v_isSharedCheck_3324_; 
lean_dec(v_val_3205_);
lean_del_object(v___x_3188_);
lean_dec(v_snd_3186_);
lean_dec(v_mvarId_3174_);
lean_dec_ref(v_config_3173_);
v_a_3317_ = lean_ctor_get(v___x_3310_, 0);
v_isSharedCheck_3324_ = !lean_is_exclusive(v___x_3310_);
if (v_isSharedCheck_3324_ == 0)
{
v___x_3319_ = v___x_3310_;
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
else
{
lean_inc(v_a_3317_);
lean_dec(v___x_3310_);
v___x_3319_ = lean_box(0);
v_isShared_3320_ = v_isSharedCheck_3324_;
goto v_resetjp_3318_;
}
v_resetjp_3318_:
{
lean_object* v___x_3322_; 
if (v_isShared_3320_ == 0)
{
v___x_3322_ = v___x_3319_;
goto v_reusejp_3321_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_a_3317_);
v___x_3322_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3321_;
}
v_reusejp_3321_:
{
return v___x_3322_;
}
}
}
}
}
}
}
v___jp_3190_:
{
lean_object* v___x_3192_; lean_object* v___x_3194_; 
v___x_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3192_, 0, v_a_3191_);
if (v_isShared_3189_ == 0)
{
lean_ctor_set(v___x_3188_, 0, v___x_3192_);
v___x_3194_ = v___x_3188_;
goto v_reusejp_3193_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v___x_3192_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_snd_3186_);
v___x_3194_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3193_;
}
v_reusejp_3193_:
{
lean_object* v___x_3195_; 
v___x_3195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3195_, 0, v___x_3194_);
return v___x_3195_;
}
}
v___jp_3198_:
{
lean_object* v___x_3200_; size_t v___x_3201_; size_t v___x_3202_; 
v___x_3200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3200_, 0, v___x_3197_);
lean_ctor_set(v___x_3200_, 1, v_a_3199_);
v___x_3201_ = ((size_t)1ULL);
v___x_3202_ = lean_usize_add(v_i_3177_, v___x_3201_);
v_i_3177_ = v___x_3202_;
v_b_3178_ = v___x_3200_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_config_3858_, lean_object* v_mvarId_3859_, lean_object* v_as_3860_, lean_object* v_sz_3861_, lean_object* v_i_3862_, lean_object* v_b_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_){
_start:
{
size_t v_sz_boxed_3869_; size_t v_i_boxed_3870_; lean_object* v_res_3871_; 
v_sz_boxed_3869_ = lean_unbox_usize(v_sz_3861_);
lean_dec(v_sz_3861_);
v_i_boxed_3870_ = lean_unbox_usize(v_i_3862_);
lean_dec(v_i_3862_);
v_res_3871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3858_, v_mvarId_3859_, v_as_3860_, v_sz_boxed_3869_, v_i_boxed_3870_, v_b_3863_, v___y_3864_, v___y_3865_, v___y_3866_, v___y_3867_);
lean_dec(v___y_3867_);
lean_dec_ref(v___y_3866_);
lean_dec(v___y_3865_);
lean_dec_ref(v___y_3864_);
lean_dec_ref(v_as_3860_);
return v_res_3871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(lean_object* v_config_3872_, lean_object* v_mvarId_3873_, lean_object* v_as_3874_, size_t v_sz_3875_, size_t v_i_3876_, lean_object* v_b_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
uint8_t v___x_3883_; 
v___x_3883_ = lean_usize_dec_lt(v_i_3876_, v_sz_3875_);
if (v___x_3883_ == 0)
{
lean_object* v___x_3884_; 
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v___x_3884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3884_, 0, v_b_3877_);
return v___x_3884_;
}
else
{
lean_object* v_snd_3885_; lean_object* v___x_3887_; uint8_t v_isShared_3888_; uint8_t v_isSharedCheck_4555_; 
v_snd_3885_ = lean_ctor_get(v_b_3877_, 1);
v_isSharedCheck_4555_ = !lean_is_exclusive(v_b_3877_);
if (v_isSharedCheck_4555_ == 0)
{
lean_object* v_unused_4556_; 
v_unused_4556_ = lean_ctor_get(v_b_3877_, 0);
lean_dec(v_unused_4556_);
v___x_3887_ = v_b_3877_;
v_isShared_3888_ = v_isSharedCheck_4555_;
goto v_resetjp_3886_;
}
else
{
lean_inc(v_snd_3885_);
lean_dec(v_b_3877_);
v___x_3887_ = lean_box(0);
v_isShared_3888_ = v_isSharedCheck_4555_;
goto v_resetjp_3886_;
}
v_resetjp_3886_:
{
lean_object* v_a_3890_; lean_object* v___x_3896_; lean_object* v_a_3898_; lean_object* v_a_3903_; 
v___x_3896_ = lean_box(0);
v_a_3903_ = lean_array_uget(v_as_3874_, v_i_3876_);
if (lean_obj_tag(v_a_3903_) == 0)
{
lean_del_object(v___x_3887_);
v_a_3898_ = v_snd_3885_;
goto v___jp_3897_;
}
else
{
lean_object* v_val_3904_; lean_object* v___x_3906_; uint8_t v_isShared_3907_; uint8_t v_isSharedCheck_4554_; 
v_val_3904_ = lean_ctor_get(v_a_3903_, 0);
v_isSharedCheck_4554_ = !lean_is_exclusive(v_a_3903_);
if (v_isSharedCheck_4554_ == 0)
{
v___x_3906_ = v_a_3903_;
v_isShared_3907_ = v_isSharedCheck_4554_;
goto v_resetjp_3905_;
}
else
{
lean_inc(v_val_3904_);
lean_dec(v_a_3903_);
v___x_3906_ = lean_box(0);
v_isShared_3907_ = v_isSharedCheck_4554_;
goto v_resetjp_3905_;
}
v_resetjp_3905_:
{
lean_object* v___x_3908_; lean_object* v___y_3910_; lean_object* v___y_3911_; lean_object* v___y_3912_; lean_object* v___y_3913_; lean_object* v___x_3950_; lean_object* v___y_3952_; lean_object* v___y_3953_; lean_object* v___y_3954_; lean_object* v___y_3955_; lean_object* v___y_3974_; lean_object* v___y_3975_; lean_object* v___y_3976_; lean_object* v___y_3977_; uint8_t v___y_3978_; uint8_t v___x_3979_; lean_object* v___y_3981_; lean_object* v___y_3982_; lean_object* v___y_3983_; lean_object* v___y_3984_; uint8_t v___y_3985_; lean_object* v___y_3987_; lean_object* v___y_3988_; lean_object* v___y_3989_; lean_object* v___y_3990_; uint8_t v___y_3991_; uint8_t v___y_3992_; uint8_t v___y_3994_; uint8_t v___y_3995_; lean_object* v___y_3996_; lean_object* v___y_3997_; lean_object* v___y_3998_; lean_object* v___y_3999_; uint8_t v___y_4002_; lean_object* v___y_4003_; lean_object* v___y_4004_; uint8_t v___y_4005_; lean_object* v___y_4006_; lean_object* v___y_4007_; uint8_t v___y_4008_; 
v___x_3908_ = lean_box(0);
v___x_3950_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3___closed__0));
v___x_3979_ = l_Lean_LocalDecl_isImplementationDetail(v_val_3904_);
if (v___x_3979_ == 0)
{
lean_object* v___x_4024_; uint8_t v___y_4026_; uint8_t v___y_4027_; lean_object* v___y_4028_; lean_object* v___y_4029_; lean_object* v___y_4030_; lean_object* v___y_4031_; uint8_t v___y_4035_; lean_object* v___y_4036_; lean_object* v___y_4037_; lean_object* v___y_4038_; lean_object* v___y_4039_; lean_object* v___y_4040_; uint8_t v___y_4041_; uint8_t v___y_4042_; uint8_t v___y_4045_; lean_object* v___y_4046_; lean_object* v___y_4047_; lean_object* v___y_4048_; lean_object* v___y_4049_; uint8_t v___y_4050_; lean_object* v_a_4051_; uint8_t v___y_4055_; lean_object* v___y_4056_; lean_object* v___y_4057_; lean_object* v___y_4058_; lean_object* v___y_4059_; lean_object* v___y_4060_; uint8_t v___y_4061_; lean_object* v___y_4062_; uint8_t v___y_4106_; lean_object* v___y_4107_; lean_object* v___y_4108_; lean_object* v___y_4109_; lean_object* v___y_4110_; uint8_t v___y_4111_; uint8_t v___y_4135_; lean_object* v___y_4136_; lean_object* v___y_4137_; lean_object* v___y_4138_; lean_object* v___y_4139_; uint8_t v___y_4140_; uint8_t v___y_4141_; uint8_t v___y_4143_; lean_object* v___y_4144_; lean_object* v___y_4145_; lean_object* v___y_4146_; lean_object* v___y_4147_; lean_object* v___y_4148_; uint8_t v___y_4149_; uint8_t v___y_4150_; uint8_t v___y_4153_; lean_object* v___y_4154_; lean_object* v___y_4155_; lean_object* v___y_4156_; lean_object* v___y_4157_; uint8_t v___y_4158_; uint8_t v___y_4159_; uint8_t v___y_4172_; lean_object* v___y_4173_; lean_object* v___y_4174_; lean_object* v___y_4175_; lean_object* v___y_4176_; uint8_t v___y_4177_; uint8_t v___y_4178_; uint8_t v___y_4180_; uint8_t v_isHEq_4181_; lean_object* v___y_4182_; lean_object* v___y_4183_; lean_object* v___y_4184_; lean_object* v___y_4185_; lean_object* v___y_4189_; lean_object* v___y_4190_; uint8_t v___y_4191_; lean_object* v___y_4192_; lean_object* v___y_4193_; lean_object* v___y_4194_; lean_object* v___y_4195_; uint8_t v_isEq_4252_; lean_object* v___y_4253_; lean_object* v___y_4254_; lean_object* v___y_4255_; lean_object* v___y_4256_; lean_object* v___y_4302_; lean_object* v___y_4303_; lean_object* v___y_4304_; lean_object* v___y_4305_; lean_object* v___y_4348_; lean_object* v___y_4349_; lean_object* v___y_4350_; lean_object* v___y_4351_; lean_object* v___x_4484_; 
v___x_4024_ = l_Lean_LocalDecl_type(v_val_3904_);
lean_inc_ref(v___x_4024_);
v___x_4484_ = l_Lean_Meta_matchNot_x3f(v___x_4024_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_4484_) == 0)
{
lean_object* v_a_4485_; 
v_a_4485_ = lean_ctor_get(v___x_4484_, 0);
lean_inc(v_a_4485_);
lean_dec_ref_known(v___x_4484_, 1);
if (lean_obj_tag(v_a_4485_) == 1)
{
lean_object* v_val_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4545_; 
v_val_4486_ = lean_ctor_get(v_a_4485_, 0);
v_isSharedCheck_4545_ = !lean_is_exclusive(v_a_4485_);
if (v_isSharedCheck_4545_ == 0)
{
v___x_4488_ = v_a_4485_;
v_isShared_4489_ = v_isSharedCheck_4545_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_val_4486_);
lean_dec(v_a_4485_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4545_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v___x_4490_; 
v___x_4490_ = l_Lean_Meta_findLocalDeclWithType_x3f(v_val_4486_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v_a_4491_; 
v_a_4491_ = lean_ctor_get(v___x_4490_, 0);
lean_inc(v_a_4491_);
lean_dec_ref_known(v___x_4490_, 1);
if (lean_obj_tag(v_a_4491_) == 1)
{
lean_object* v_val_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4536_; 
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec_ref(v_config_3872_);
v_val_4492_ = lean_ctor_get(v_a_4491_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v_a_4491_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4494_ = v_a_4491_;
v_isShared_4495_ = v_isSharedCheck_4536_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_val_4492_);
lean_dec(v_a_4491_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4536_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4496_; 
lean_inc(v_mvarId_3873_);
v___x_4496_ = l_Lean_MVarId_getType(v_mvarId_3873_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_4496_) == 0)
{
lean_object* v_a_4497_; lean_object* v___x_4498_; lean_object* v___x_4499_; lean_object* v___x_4500_; lean_object* v___x_4501_; 
v_a_4497_ = lean_ctor_get(v___x_4496_, 0);
lean_inc(v_a_4497_);
lean_dec_ref_known(v___x_4496_, 1);
v___x_4498_ = l_Lean_LocalDecl_toExpr(v_val_3904_);
v___x_4499_ = l_Lean_mkFVar(v_val_4492_);
v___x_4500_ = l_Lean_Expr_app___override(v___x_4498_, v___x_4499_);
v___x_4501_ = l_Lean_Meta_mkFalseElim(v_a_4497_, v___x_4500_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
if (lean_obj_tag(v___x_4501_) == 0)
{
lean_object* v_a_4502_; lean_object* v___x_4503_; 
v_a_4502_ = lean_ctor_get(v___x_4501_, 0);
lean_inc(v_a_4502_);
lean_dec_ref_known(v___x_4501_, 1);
v___x_4503_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3873_, v_a_4502_, v___y_3879_);
if (lean_obj_tag(v___x_4503_) == 0)
{
lean_object* v___x_4504_; lean_object* v___x_4506_; 
lean_dec_ref_known(v___x_4503_, 1);
v___x_4504_ = lean_box(v___x_3883_);
if (v_isShared_4495_ == 0)
{
lean_ctor_set(v___x_4494_, 0, v___x_4504_);
v___x_4506_ = v___x_4494_;
goto v_reusejp_4505_;
}
else
{
lean_object* v_reuseFailAlloc_4511_; 
v_reuseFailAlloc_4511_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4511_, 0, v___x_4504_);
v___x_4506_ = v_reuseFailAlloc_4511_;
goto v_reusejp_4505_;
}
v_reusejp_4505_:
{
lean_object* v___x_4507_; lean_object* v___x_4509_; 
v___x_4507_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4507_, 0, v___x_4506_);
lean_ctor_set(v___x_4507_, 1, v___x_3908_);
if (v_isShared_4489_ == 0)
{
lean_ctor_set_tag(v___x_4488_, 0);
lean_ctor_set(v___x_4488_, 0, v___x_4507_);
v___x_4509_ = v___x_4488_;
goto v_reusejp_4508_;
}
else
{
lean_object* v_reuseFailAlloc_4510_; 
v_reuseFailAlloc_4510_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4510_, 0, v___x_4507_);
v___x_4509_ = v_reuseFailAlloc_4510_;
goto v_reusejp_4508_;
}
v_reusejp_4508_:
{
v_a_3890_ = v___x_4509_;
goto v___jp_3889_;
}
}
}
else
{
lean_object* v_a_4512_; lean_object* v___x_4514_; uint8_t v_isShared_4515_; uint8_t v_isSharedCheck_4519_; 
lean_del_object(v___x_4494_);
lean_del_object(v___x_4488_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
v_a_4512_ = lean_ctor_get(v___x_4503_, 0);
v_isSharedCheck_4519_ = !lean_is_exclusive(v___x_4503_);
if (v_isSharedCheck_4519_ == 0)
{
v___x_4514_ = v___x_4503_;
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
else
{
lean_inc(v_a_4512_);
lean_dec(v___x_4503_);
v___x_4514_ = lean_box(0);
v_isShared_4515_ = v_isSharedCheck_4519_;
goto v_resetjp_4513_;
}
v_resetjp_4513_:
{
lean_object* v___x_4517_; 
if (v_isShared_4515_ == 0)
{
v___x_4517_ = v___x_4514_;
goto v_reusejp_4516_;
}
else
{
lean_object* v_reuseFailAlloc_4518_; 
v_reuseFailAlloc_4518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4518_, 0, v_a_4512_);
v___x_4517_ = v_reuseFailAlloc_4518_;
goto v_reusejp_4516_;
}
v_reusejp_4516_:
{
return v___x_4517_;
}
}
}
}
else
{
lean_object* v_a_4520_; lean_object* v___x_4522_; uint8_t v_isShared_4523_; uint8_t v_isSharedCheck_4527_; 
lean_del_object(v___x_4494_);
lean_del_object(v___x_4488_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_4520_ = lean_ctor_get(v___x_4501_, 0);
v_isSharedCheck_4527_ = !lean_is_exclusive(v___x_4501_);
if (v_isSharedCheck_4527_ == 0)
{
v___x_4522_ = v___x_4501_;
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
else
{
lean_inc(v_a_4520_);
lean_dec(v___x_4501_);
v___x_4522_ = lean_box(0);
v_isShared_4523_ = v_isSharedCheck_4527_;
goto v_resetjp_4521_;
}
v_resetjp_4521_:
{
lean_object* v___x_4525_; 
if (v_isShared_4523_ == 0)
{
v___x_4525_ = v___x_4522_;
goto v_reusejp_4524_;
}
else
{
lean_object* v_reuseFailAlloc_4526_; 
v_reuseFailAlloc_4526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4526_, 0, v_a_4520_);
v___x_4525_ = v_reuseFailAlloc_4526_;
goto v_reusejp_4524_;
}
v_reusejp_4524_:
{
return v___x_4525_;
}
}
}
}
else
{
lean_object* v_a_4528_; lean_object* v___x_4530_; uint8_t v_isShared_4531_; uint8_t v_isSharedCheck_4535_; 
lean_del_object(v___x_4494_);
lean_dec(v_val_4492_);
lean_del_object(v___x_4488_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_4528_ = lean_ctor_get(v___x_4496_, 0);
v_isSharedCheck_4535_ = !lean_is_exclusive(v___x_4496_);
if (v_isSharedCheck_4535_ == 0)
{
v___x_4530_ = v___x_4496_;
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
else
{
lean_inc(v_a_4528_);
lean_dec(v___x_4496_);
v___x_4530_ = lean_box(0);
v_isShared_4531_ = v_isSharedCheck_4535_;
goto v_resetjp_4529_;
}
v_resetjp_4529_:
{
lean_object* v___x_4533_; 
if (v_isShared_4531_ == 0)
{
v___x_4533_ = v___x_4530_;
goto v_reusejp_4532_;
}
else
{
lean_object* v_reuseFailAlloc_4534_; 
v_reuseFailAlloc_4534_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4534_, 0, v_a_4528_);
v___x_4533_ = v_reuseFailAlloc_4534_;
goto v_reusejp_4532_;
}
v_reusejp_4532_:
{
return v___x_4533_;
}
}
}
}
}
else
{
lean_dec(v_a_4491_);
lean_del_object(v___x_4488_);
v___y_4348_ = v___y_3878_;
v___y_4349_ = v___y_3879_;
v___y_4350_ = v___y_3880_;
v___y_4351_ = v___y_3881_;
goto v___jp_4347_;
}
}
else
{
lean_object* v_a_4537_; lean_object* v___x_4539_; uint8_t v_isShared_4540_; uint8_t v_isSharedCheck_4544_; 
lean_del_object(v___x_4488_);
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4537_ = lean_ctor_get(v___x_4490_, 0);
v_isSharedCheck_4544_ = !lean_is_exclusive(v___x_4490_);
if (v_isSharedCheck_4544_ == 0)
{
v___x_4539_ = v___x_4490_;
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
else
{
lean_inc(v_a_4537_);
lean_dec(v___x_4490_);
v___x_4539_ = lean_box(0);
v_isShared_4540_ = v_isSharedCheck_4544_;
goto v_resetjp_4538_;
}
v_resetjp_4538_:
{
lean_object* v___x_4542_; 
if (v_isShared_4540_ == 0)
{
v___x_4542_ = v___x_4539_;
goto v_reusejp_4541_;
}
else
{
lean_object* v_reuseFailAlloc_4543_; 
v_reuseFailAlloc_4543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4543_, 0, v_a_4537_);
v___x_4542_ = v_reuseFailAlloc_4543_;
goto v_reusejp_4541_;
}
v_reusejp_4541_:
{
return v___x_4542_;
}
}
}
}
}
else
{
lean_dec(v_a_4485_);
v___y_4348_ = v___y_3878_;
v___y_4349_ = v___y_3879_;
v___y_4350_ = v___y_3880_;
v___y_4351_ = v___y_3881_;
goto v___jp_4347_;
}
}
else
{
lean_object* v_a_4546_; lean_object* v___x_4548_; uint8_t v_isShared_4549_; uint8_t v_isSharedCheck_4553_; 
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4546_ = lean_ctor_get(v___x_4484_, 0);
v_isSharedCheck_4553_ = !lean_is_exclusive(v___x_4484_);
if (v_isSharedCheck_4553_ == 0)
{
v___x_4548_ = v___x_4484_;
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
else
{
lean_inc(v_a_4546_);
lean_dec(v___x_4484_);
v___x_4548_ = lean_box(0);
v_isShared_4549_ = v_isSharedCheck_4553_;
goto v_resetjp_4547_;
}
v_resetjp_4547_:
{
lean_object* v___x_4551_; 
if (v_isShared_4549_ == 0)
{
v___x_4551_ = v___x_4548_;
goto v_reusejp_4550_;
}
else
{
lean_object* v_reuseFailAlloc_4552_; 
v_reuseFailAlloc_4552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4552_, 0, v_a_4546_);
v___x_4551_ = v_reuseFailAlloc_4552_;
goto v_reusejp_4550_;
}
v_reusejp_4550_:
{
return v___x_4551_;
}
}
}
v___jp_4025_:
{
uint8_t v_genDiseq_4032_; 
v_genDiseq_4032_ = lean_ctor_get_uint8(v_config_3872_, sizeof(void*)*1 + 2);
if (v_genDiseq_4032_ == 0)
{
lean_dec_ref(v___x_4024_);
v___y_4002_ = v___y_4026_;
v___y_4003_ = v___y_4028_;
v___y_4004_ = v___y_4029_;
v___y_4005_ = v___y_4027_;
v___y_4006_ = v___y_4031_;
v___y_4007_ = v___y_4030_;
v___y_4008_ = v___x_3979_;
goto v___jp_4001_;
}
else
{
uint8_t v___x_4033_; 
v___x_4033_ = l_Lean_Meta_Simp_isEqnThmHypothesis(v___x_4024_);
v___y_4002_ = v___y_4026_;
v___y_4003_ = v___y_4028_;
v___y_4004_ = v___y_4029_;
v___y_4005_ = v___y_4027_;
v___y_4006_ = v___y_4031_;
v___y_4007_ = v___y_4030_;
v___y_4008_ = v___x_4033_;
goto v___jp_4001_;
}
}
v___jp_4034_:
{
if (v___y_4042_ == 0)
{
lean_dec_ref(v___y_4036_);
v___y_4026_ = v___y_4035_;
v___y_4027_ = v___y_4041_;
v___y_4028_ = v___y_4039_;
v___y_4029_ = v___y_4038_;
v___y_4030_ = v___y_4037_;
v___y_4031_ = v___y_4040_;
goto v___jp_4025_;
}
else
{
lean_object* v___x_4043_; 
lean_dec_ref(v___x_4024_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v___x_4043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4043_, 0, v___y_4036_);
return v___x_4043_;
}
}
v___jp_4044_:
{
uint8_t v___x_4052_; 
v___x_4052_ = l_Lean_Exception_isInterrupt(v_a_4051_);
if (v___x_4052_ == 0)
{
uint8_t v___x_4053_; 
lean_inc_ref(v_a_4051_);
v___x_4053_ = l_Lean_Exception_isRuntime(v_a_4051_);
v___y_4035_ = v___y_4045_;
v___y_4036_ = v_a_4051_;
v___y_4037_ = v___y_4048_;
v___y_4038_ = v___y_4047_;
v___y_4039_ = v___y_4046_;
v___y_4040_ = v___y_4049_;
v___y_4041_ = v___y_4050_;
v___y_4042_ = v___x_4053_;
goto v___jp_4034_;
}
else
{
v___y_4035_ = v___y_4045_;
v___y_4036_ = v_a_4051_;
v___y_4037_ = v___y_4048_;
v___y_4038_ = v___y_4047_;
v___y_4039_ = v___y_4046_;
v___y_4040_ = v___y_4049_;
v___y_4041_ = v___y_4050_;
v___y_4042_ = v___x_4052_;
goto v___jp_4034_;
}
}
v___jp_4054_:
{
if (lean_obj_tag(v___y_4062_) == 0)
{
lean_object* v_a_4063_; lean_object* v___x_4064_; uint8_t v___x_4065_; 
v_a_4063_ = lean_ctor_get(v___y_4062_, 0);
lean_inc(v_a_4063_);
lean_dec_ref_known(v___y_4062_, 1);
v___x_4064_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__3));
v___x_4065_ = l_Lean_Expr_isConstOf(v_a_4063_, v___x_4064_);
lean_dec(v_a_4063_);
if (v___x_4065_ == 0)
{
lean_dec_ref(v___y_4060_);
v___y_4026_ = v___y_4055_;
v___y_4027_ = v___y_4061_;
v___y_4028_ = v___y_4058_;
v___y_4029_ = v___y_4057_;
v___y_4030_ = v___y_4056_;
v___y_4031_ = v___y_4059_;
goto v___jp_4025_;
}
else
{
lean_object* v___x_4066_; 
lean_inc_ref(v___y_4060_);
v___x_4066_ = l_Lean_Meta_mkEqRefl(v___y_4060_, v___y_4058_, v___y_4057_, v___y_4056_, v___y_4059_);
if (lean_obj_tag(v___x_4066_) == 0)
{
lean_object* v_a_4067_; lean_object* v___x_4068_; lean_object* v_dummy_4069_; lean_object* v_nargs_4070_; lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4073_; lean_object* v___x_4074_; lean_object* v___x_4075_; lean_object* v___x_4076_; lean_object* v___x_4077_; 
v_a_4067_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4067_);
lean_dec_ref_known(v___x_4066_, 1);
v___x_4068_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__6);
v_dummy_4069_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1_spec__4___closed__7);
v_nargs_4070_ = l_Lean_Expr_getAppNumArgs(v___y_4060_);
lean_inc(v_nargs_4070_);
v___x_4071_ = lean_mk_array(v_nargs_4070_, v_dummy_4069_);
v___x_4072_ = lean_unsigned_to_nat(1u);
v___x_4073_ = lean_nat_sub(v_nargs_4070_, v___x_4072_);
lean_dec(v_nargs_4070_);
v___x_4074_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v___y_4060_, v___x_4071_, v___x_4073_);
v___x_4075_ = lean_array_push(v___x_4074_, v_a_4067_);
v___x_4076_ = l_Lean_mkAppN(v___x_4068_, v___x_4075_);
lean_dec_ref(v___x_4075_);
lean_inc(v_mvarId_3873_);
v___x_4077_ = l_Lean_MVarId_getType(v_mvarId_3873_, v___y_4058_, v___y_4057_, v___y_4056_, v___y_4059_);
if (lean_obj_tag(v___x_4077_) == 0)
{
lean_object* v_a_4078_; lean_object* v___x_4079_; lean_object* v___x_4080_; 
v_a_4078_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4078_);
lean_dec_ref_known(v___x_4077_, 1);
lean_inc(v_val_3904_);
v___x_4079_ = l_Lean_LocalDecl_toExpr(v_val_3904_);
v___x_4080_ = l_Lean_Meta_mkAbsurd(v_a_4078_, v___x_4079_, v___x_4076_, v___y_4058_, v___y_4057_, v___y_4056_, v___y_4059_);
if (lean_obj_tag(v___x_4080_) == 0)
{
lean_object* v_a_4081_; lean_object* v___x_4083_; uint8_t v_isShared_4084_; uint8_t v_isSharedCheck_4100_; 
v_a_4081_ = lean_ctor_get(v___x_4080_, 0);
v_isSharedCheck_4100_ = !lean_is_exclusive(v___x_4080_);
if (v_isSharedCheck_4100_ == 0)
{
v___x_4083_ = v___x_4080_;
v_isShared_4084_ = v_isSharedCheck_4100_;
goto v_resetjp_4082_;
}
else
{
lean_inc(v_a_4081_);
lean_dec(v___x_4080_);
v___x_4083_ = lean_box(0);
v_isShared_4084_ = v_isSharedCheck_4100_;
goto v_resetjp_4082_;
}
v_resetjp_4082_:
{
lean_object* v___x_4085_; 
lean_inc(v_mvarId_3873_);
v___x_4085_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3873_, v_a_4081_, v___y_4057_);
if (lean_obj_tag(v___x_4085_) == 0)
{
lean_object* v___x_4087_; uint8_t v_isShared_4088_; uint8_t v_isSharedCheck_4097_; 
lean_dec_ref(v___x_4024_);
lean_dec(v_val_3904_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_isSharedCheck_4097_ = !lean_is_exclusive(v___x_4085_);
if (v_isSharedCheck_4097_ == 0)
{
lean_object* v_unused_4098_; 
v_unused_4098_ = lean_ctor_get(v___x_4085_, 0);
lean_dec(v_unused_4098_);
v___x_4087_ = v___x_4085_;
v_isShared_4088_ = v_isSharedCheck_4097_;
goto v_resetjp_4086_;
}
else
{
lean_dec(v___x_4085_);
v___x_4087_ = lean_box(0);
v_isShared_4088_ = v_isSharedCheck_4097_;
goto v_resetjp_4086_;
}
v_resetjp_4086_:
{
lean_object* v___x_4089_; lean_object* v___x_4091_; 
v___x_4089_ = lean_box(v___x_3883_);
if (v_isShared_4088_ == 0)
{
lean_ctor_set_tag(v___x_4087_, 1);
lean_ctor_set(v___x_4087_, 0, v___x_4089_);
v___x_4091_ = v___x_4087_;
goto v_reusejp_4090_;
}
else
{
lean_object* v_reuseFailAlloc_4096_; 
v_reuseFailAlloc_4096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4096_, 0, v___x_4089_);
v___x_4091_ = v_reuseFailAlloc_4096_;
goto v_reusejp_4090_;
}
v_reusejp_4090_:
{
lean_object* v___x_4092_; lean_object* v___x_4094_; 
v___x_4092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4092_, 0, v___x_4091_);
lean_ctor_set(v___x_4092_, 1, v___x_3908_);
if (v_isShared_4084_ == 0)
{
lean_ctor_set(v___x_4083_, 0, v___x_4092_);
v___x_4094_ = v___x_4083_;
goto v_reusejp_4093_;
}
else
{
lean_object* v_reuseFailAlloc_4095_; 
v_reuseFailAlloc_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4095_, 0, v___x_4092_);
v___x_4094_ = v_reuseFailAlloc_4095_;
goto v_reusejp_4093_;
}
v_reusejp_4093_:
{
v_a_3890_ = v___x_4094_;
goto v___jp_3889_;
}
}
}
}
else
{
lean_object* v_a_4099_; 
lean_del_object(v___x_4083_);
v_a_4099_ = lean_ctor_get(v___x_4085_, 0);
lean_inc(v_a_4099_);
lean_dec_ref_known(v___x_4085_, 1);
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4058_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v___y_4056_;
v___y_4049_ = v___y_4059_;
v___y_4050_ = v___y_4061_;
v_a_4051_ = v_a_4099_;
goto v___jp_4044_;
}
}
}
else
{
lean_object* v_a_4101_; 
v_a_4101_ = lean_ctor_get(v___x_4080_, 0);
lean_inc(v_a_4101_);
lean_dec_ref_known(v___x_4080_, 1);
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4058_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v___y_4056_;
v___y_4049_ = v___y_4059_;
v___y_4050_ = v___y_4061_;
v_a_4051_ = v_a_4101_;
goto v___jp_4044_;
}
}
else
{
lean_object* v_a_4102_; 
lean_dec_ref(v___x_4076_);
v_a_4102_ = lean_ctor_get(v___x_4077_, 0);
lean_inc(v_a_4102_);
lean_dec_ref_known(v___x_4077_, 1);
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4058_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v___y_4056_;
v___y_4049_ = v___y_4059_;
v___y_4050_ = v___y_4061_;
v_a_4051_ = v_a_4102_;
goto v___jp_4044_;
}
}
else
{
lean_object* v_a_4103_; 
lean_dec_ref(v___y_4060_);
v_a_4103_ = lean_ctor_get(v___x_4066_, 0);
lean_inc(v_a_4103_);
lean_dec_ref_known(v___x_4066_, 1);
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4058_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v___y_4056_;
v___y_4049_ = v___y_4059_;
v___y_4050_ = v___y_4061_;
v_a_4051_ = v_a_4103_;
goto v___jp_4044_;
}
}
}
else
{
lean_object* v_a_4104_; 
lean_dec_ref(v___y_4060_);
v_a_4104_ = lean_ctor_get(v___y_4062_, 0);
lean_inc(v_a_4104_);
lean_dec_ref_known(v___y_4062_, 1);
v___y_4045_ = v___y_4055_;
v___y_4046_ = v___y_4058_;
v___y_4047_ = v___y_4057_;
v___y_4048_ = v___y_4056_;
v___y_4049_ = v___y_4059_;
v___y_4050_ = v___y_4061_;
v_a_4051_ = v_a_4104_;
goto v___jp_4044_;
}
}
v___jp_4105_:
{
lean_object* v___x_4112_; 
lean_inc_ref(v___x_4024_);
v___x_4112_ = l_Lean_Meta_mkDecide(v___x_4024_, v___y_4109_, v___y_4108_, v___y_4107_, v___y_4110_);
if (lean_obj_tag(v___x_4112_) == 0)
{
lean_object* v_a_4113_; lean_object* v___x_4114_; uint8_t v_transparency_4115_; uint8_t v___x_4116_; uint8_t v___x_4117_; 
v_a_4113_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4113_);
lean_dec_ref_known(v___x_4112_, 1);
v___x_4114_ = l_Lean_Meta_Context_config(v___y_4109_);
v_transparency_4115_ = lean_ctor_get_uint8(v___x_4114_, 9);
lean_dec_ref(v___x_4114_);
v___x_4116_ = 1;
v___x_4117_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_4115_, v___x_4116_);
if (v___x_4117_ == 0)
{
lean_object* v_keyedConfig_4118_; uint8_t v_trackZetaDelta_4119_; lean_object* v_zetaDeltaSet_4120_; lean_object* v_lctx_4121_; lean_object* v_localInstances_4122_; lean_object* v_defEqCtx_x3f_4123_; lean_object* v_synthPendingDepth_4124_; lean_object* v_customCanUnfoldPredicate_x3f_4125_; uint8_t v_univApprox_4126_; uint8_t v_inTypeClassResolution_4127_; uint8_t v_cacheInferType_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; 
v_keyedConfig_4118_ = lean_ctor_get(v___y_4109_, 0);
v_trackZetaDelta_4119_ = lean_ctor_get_uint8(v___y_4109_, sizeof(void*)*7);
v_zetaDeltaSet_4120_ = lean_ctor_get(v___y_4109_, 1);
v_lctx_4121_ = lean_ctor_get(v___y_4109_, 2);
v_localInstances_4122_ = lean_ctor_get(v___y_4109_, 3);
v_defEqCtx_x3f_4123_ = lean_ctor_get(v___y_4109_, 4);
v_synthPendingDepth_4124_ = lean_ctor_get(v___y_4109_, 5);
v_customCanUnfoldPredicate_x3f_4125_ = lean_ctor_get(v___y_4109_, 6);
v_univApprox_4126_ = lean_ctor_get_uint8(v___y_4109_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_4127_ = lean_ctor_get_uint8(v___y_4109_, sizeof(void*)*7 + 2);
v_cacheInferType_4128_ = lean_ctor_get_uint8(v___y_4109_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_4118_);
v___x_4129_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_4116_, v_keyedConfig_4118_);
lean_inc(v_customCanUnfoldPredicate_x3f_4125_);
lean_inc(v_synthPendingDepth_4124_);
lean_inc(v_defEqCtx_x3f_4123_);
lean_inc_ref(v_localInstances_4122_);
lean_inc_ref(v_lctx_4121_);
lean_inc(v_zetaDeltaSet_4120_);
v___x_4130_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
lean_ctor_set(v___x_4130_, 1, v_zetaDeltaSet_4120_);
lean_ctor_set(v___x_4130_, 2, v_lctx_4121_);
lean_ctor_set(v___x_4130_, 3, v_localInstances_4122_);
lean_ctor_set(v___x_4130_, 4, v_defEqCtx_x3f_4123_);
lean_ctor_set(v___x_4130_, 5, v_synthPendingDepth_4124_);
lean_ctor_set(v___x_4130_, 6, v_customCanUnfoldPredicate_x3f_4125_);
lean_ctor_set_uint8(v___x_4130_, sizeof(void*)*7, v_trackZetaDelta_4119_);
lean_ctor_set_uint8(v___x_4130_, sizeof(void*)*7 + 1, v_univApprox_4126_);
lean_ctor_set_uint8(v___x_4130_, sizeof(void*)*7 + 2, v_inTypeClassResolution_4127_);
lean_ctor_set_uint8(v___x_4130_, sizeof(void*)*7 + 3, v_cacheInferType_4128_);
lean_inc(v___y_4110_);
lean_inc_ref(v___y_4107_);
lean_inc(v___y_4108_);
lean_inc(v_a_4113_);
v___x_4131_ = lean_whnf(v_a_4113_, v___x_4130_, v___y_4108_, v___y_4107_, v___y_4110_);
v___y_4055_ = v___y_4106_;
v___y_4056_ = v___y_4107_;
v___y_4057_ = v___y_4108_;
v___y_4058_ = v___y_4109_;
v___y_4059_ = v___y_4110_;
v___y_4060_ = v_a_4113_;
v___y_4061_ = v___y_4111_;
v___y_4062_ = v___x_4131_;
goto v___jp_4054_;
}
else
{
lean_object* v___x_4132_; 
lean_inc(v___y_4110_);
lean_inc_ref(v___y_4107_);
lean_inc(v___y_4108_);
lean_inc_ref(v___y_4109_);
lean_inc(v_a_4113_);
v___x_4132_ = lean_whnf(v_a_4113_, v___y_4109_, v___y_4108_, v___y_4107_, v___y_4110_);
v___y_4055_ = v___y_4106_;
v___y_4056_ = v___y_4107_;
v___y_4057_ = v___y_4108_;
v___y_4058_ = v___y_4109_;
v___y_4059_ = v___y_4110_;
v___y_4060_ = v_a_4113_;
v___y_4061_ = v___y_4111_;
v___y_4062_ = v___x_4132_;
goto v___jp_4054_;
}
}
else
{
lean_object* v_a_4133_; 
v_a_4133_ = lean_ctor_get(v___x_4112_, 0);
lean_inc(v_a_4133_);
lean_dec_ref_known(v___x_4112_, 1);
v___y_4045_ = v___y_4106_;
v___y_4046_ = v___y_4109_;
v___y_4047_ = v___y_4108_;
v___y_4048_ = v___y_4107_;
v___y_4049_ = v___y_4110_;
v___y_4050_ = v___y_4111_;
v_a_4051_ = v_a_4133_;
goto v___jp_4044_;
}
}
v___jp_4134_:
{
if (v___y_4141_ == 0)
{
v___y_4026_ = v___y_4135_;
v___y_4027_ = v___y_4140_;
v___y_4028_ = v___y_4138_;
v___y_4029_ = v___y_4137_;
v___y_4030_ = v___y_4136_;
v___y_4031_ = v___y_4139_;
goto v___jp_4025_;
}
else
{
v___y_4106_ = v___y_4135_;
v___y_4107_ = v___y_4136_;
v___y_4108_ = v___y_4137_;
v___y_4109_ = v___y_4138_;
v___y_4110_ = v___y_4139_;
v___y_4111_ = v___y_4140_;
goto v___jp_4105_;
}
}
v___jp_4142_:
{
if (v___y_4150_ == 0)
{
lean_dec_ref(v___y_4148_);
v___y_4135_ = v___y_4143_;
v___y_4136_ = v___y_4146_;
v___y_4137_ = v___y_4145_;
v___y_4138_ = v___y_4144_;
v___y_4139_ = v___y_4147_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___x_3979_;
goto v___jp_4134_;
}
else
{
uint8_t v___x_4151_; 
v___x_4151_ = l_Lean_Expr_hasFVar(v___y_4148_);
lean_dec_ref(v___y_4148_);
if (v___x_4151_ == 0)
{
v___y_4106_ = v___y_4143_;
v___y_4107_ = v___y_4146_;
v___y_4108_ = v___y_4145_;
v___y_4109_ = v___y_4144_;
v___y_4110_ = v___y_4147_;
v___y_4111_ = v___y_4149_;
goto v___jp_4105_;
}
else
{
v___y_4135_ = v___y_4143_;
v___y_4136_ = v___y_4146_;
v___y_4137_ = v___y_4145_;
v___y_4138_ = v___y_4144_;
v___y_4139_ = v___y_4147_;
v___y_4140_ = v___y_4149_;
v___y_4141_ = v___x_3979_;
goto v___jp_4134_;
}
}
}
v___jp_4152_:
{
lean_object* v___x_4160_; 
lean_inc_ref(v___x_4024_);
v___x_4160_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq_spec__2___redArg(v___x_4024_, v___y_4156_);
if (lean_obj_tag(v___x_4160_) == 0)
{
lean_object* v_a_4161_; uint8_t v___x_4162_; 
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
lean_inc(v_a_4161_);
lean_dec_ref_known(v___x_4160_, 1);
v___x_4162_ = l_Lean_Expr_hasMVar(v_a_4161_);
if (v___x_4162_ == 0)
{
v___y_4143_ = v___y_4153_;
v___y_4144_ = v___y_4154_;
v___y_4145_ = v___y_4156_;
v___y_4146_ = v___y_4155_;
v___y_4147_ = v___y_4157_;
v___y_4148_ = v_a_4161_;
v___y_4149_ = v___y_4158_;
v___y_4150_ = v___y_4159_;
goto v___jp_4142_;
}
else
{
v___y_4143_ = v___y_4153_;
v___y_4144_ = v___y_4154_;
v___y_4145_ = v___y_4156_;
v___y_4146_ = v___y_4155_;
v___y_4147_ = v___y_4157_;
v___y_4148_ = v_a_4161_;
v___y_4149_ = v___y_4158_;
v___y_4150_ = v___x_3979_;
goto v___jp_4142_;
}
}
else
{
lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4170_; 
lean_dec_ref(v___x_4024_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4163_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4165_ = v___x_4160_;
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4160_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4170_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4168_; 
if (v_isShared_4166_ == 0)
{
v___x_4168_ = v___x_4165_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v_a_4163_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
v___jp_4171_:
{
if (v___y_4178_ == 0)
{
v___y_4026_ = v___y_4172_;
v___y_4027_ = v___y_4177_;
v___y_4028_ = v___y_4175_;
v___y_4029_ = v___y_4174_;
v___y_4030_ = v___y_4173_;
v___y_4031_ = v___y_4176_;
goto v___jp_4025_;
}
else
{
v___y_4153_ = v___y_4172_;
v___y_4154_ = v___y_4175_;
v___y_4155_ = v___y_4173_;
v___y_4156_ = v___y_4174_;
v___y_4157_ = v___y_4176_;
v___y_4158_ = v___y_4177_;
v___y_4159_ = v___y_4178_;
goto v___jp_4152_;
}
}
v___jp_4179_:
{
uint8_t v_useDecide_4186_; 
v_useDecide_4186_ = lean_ctor_get_uint8(v_config_3872_, sizeof(void*)*1);
if (v_useDecide_4186_ == 0)
{
v___y_4172_ = v___y_4180_;
v___y_4173_ = v___y_4184_;
v___y_4174_ = v___y_4183_;
v___y_4175_ = v___y_4182_;
v___y_4176_ = v___y_4185_;
v___y_4177_ = v_isHEq_4181_;
v___y_4178_ = v___x_3979_;
goto v___jp_4171_;
}
else
{
uint8_t v___x_4187_; 
v___x_4187_ = l_Lean_Expr_hasFVar(v___x_4024_);
if (v___x_4187_ == 0)
{
v___y_4153_ = v___y_4180_;
v___y_4154_ = v___y_4182_;
v___y_4155_ = v___y_4184_;
v___y_4156_ = v___y_4183_;
v___y_4157_ = v___y_4185_;
v___y_4158_ = v_isHEq_4181_;
v___y_4159_ = v_useDecide_4186_;
goto v___jp_4152_;
}
else
{
v___y_4172_ = v___y_4180_;
v___y_4173_ = v___y_4184_;
v___y_4174_ = v___y_4183_;
v___y_4175_ = v___y_4182_;
v___y_4176_ = v___y_4185_;
v___y_4177_ = v_isHEq_4181_;
v___y_4178_ = v___x_3979_;
goto v___jp_4171_;
}
}
}
v___jp_4188_:
{
lean_object* v___x_4196_; 
v___x_4196_ = l_Lean_Meta_isExprDefEq(v___y_4195_, v___y_4193_, v___y_4190_, v___y_4192_, v___y_4194_, v___y_4189_);
if (lean_obj_tag(v___x_4196_) == 0)
{
lean_object* v_a_4197_; uint8_t v___x_4198_; 
v_a_4197_ = lean_ctor_get(v___x_4196_, 0);
lean_inc(v_a_4197_);
lean_dec_ref_known(v___x_4196_, 1);
v___x_4198_ = lean_unbox(v_a_4197_);
lean_dec(v_a_4197_);
if (v___x_4198_ == 0)
{
v___y_4180_ = v___y_4191_;
v_isHEq_4181_ = v___x_3883_;
v___y_4182_ = v___y_4190_;
v___y_4183_ = v___y_4192_;
v___y_4184_ = v___y_4194_;
v___y_4185_ = v___y_4189_;
goto v___jp_4179_;
}
else
{
lean_object* v___x_4199_; 
lean_dec_ref(v___x_4024_);
lean_dec_ref(v_config_3872_);
lean_inc(v_mvarId_3873_);
v___x_4199_ = l_Lean_MVarId_getType(v_mvarId_3873_, v___y_4190_, v___y_4192_, v___y_4194_, v___y_4189_);
if (lean_obj_tag(v___x_4199_) == 0)
{
lean_object* v_a_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v_a_4200_ = lean_ctor_get(v___x_4199_, 0);
lean_inc(v_a_4200_);
lean_dec_ref_known(v___x_4199_, 1);
v___x_4201_ = l_Lean_LocalDecl_toExpr(v_val_3904_);
v___x_4202_ = l_Lean_Meta_mkEqOfHEq(v___x_4201_, v___x_3883_, v___y_4190_, v___y_4192_, v___y_4194_, v___y_4189_);
if (lean_obj_tag(v___x_4202_) == 0)
{
lean_object* v_a_4203_; lean_object* v___x_4204_; 
v_a_4203_ = lean_ctor_get(v___x_4202_, 0);
lean_inc(v_a_4203_);
lean_dec_ref_known(v___x_4202_, 1);
v___x_4204_ = l_Lean_Meta_mkNoConfusion(v_a_4200_, v_a_4203_, v___y_4190_, v___y_4192_, v___y_4194_, v___y_4189_);
if (lean_obj_tag(v___x_4204_) == 0)
{
lean_object* v_a_4205_; lean_object* v___x_4206_; 
v_a_4205_ = lean_ctor_get(v___x_4204_, 0);
lean_inc(v_a_4205_);
lean_dec_ref_known(v___x_4204_, 1);
v___x_4206_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3873_, v_a_4205_, v___y_4192_);
if (lean_obj_tag(v___x_4206_) == 0)
{
lean_object* v___x_4207_; lean_object* v___x_4208_; lean_object* v___x_4209_; lean_object* v___x_4210_; 
lean_dec_ref_known(v___x_4206_, 1);
v___x_4207_ = lean_box(v___x_3883_);
v___x_4208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4208_, 0, v___x_4207_);
v___x_4209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4209_, 0, v___x_4208_);
lean_ctor_set(v___x_4209_, 1, v___x_3908_);
v___x_4210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4210_, 0, v___x_4209_);
v_a_3890_ = v___x_4210_;
goto v___jp_3889_;
}
else
{
lean_object* v_a_4211_; lean_object* v___x_4213_; uint8_t v_isShared_4214_; uint8_t v_isSharedCheck_4218_; 
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
v_a_4211_ = lean_ctor_get(v___x_4206_, 0);
v_isSharedCheck_4218_ = !lean_is_exclusive(v___x_4206_);
if (v_isSharedCheck_4218_ == 0)
{
v___x_4213_ = v___x_4206_;
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
else
{
lean_inc(v_a_4211_);
lean_dec(v___x_4206_);
v___x_4213_ = lean_box(0);
v_isShared_4214_ = v_isSharedCheck_4218_;
goto v_resetjp_4212_;
}
v_resetjp_4212_:
{
lean_object* v___x_4216_; 
if (v_isShared_4214_ == 0)
{
v___x_4216_ = v___x_4213_;
goto v_reusejp_4215_;
}
else
{
lean_object* v_reuseFailAlloc_4217_; 
v_reuseFailAlloc_4217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4217_, 0, v_a_4211_);
v___x_4216_ = v_reuseFailAlloc_4217_;
goto v_reusejp_4215_;
}
v_reusejp_4215_:
{
return v___x_4216_;
}
}
}
}
else
{
lean_object* v_a_4219_; lean_object* v___x_4221_; uint8_t v_isShared_4222_; uint8_t v_isSharedCheck_4226_; 
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_4219_ = lean_ctor_get(v___x_4204_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4204_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4221_ = v___x_4204_;
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
else
{
lean_inc(v_a_4219_);
lean_dec(v___x_4204_);
v___x_4221_ = lean_box(0);
v_isShared_4222_ = v_isSharedCheck_4226_;
goto v_resetjp_4220_;
}
v_resetjp_4220_:
{
lean_object* v___x_4224_; 
if (v_isShared_4222_ == 0)
{
v___x_4224_ = v___x_4221_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v_a_4219_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
else
{
lean_object* v_a_4227_; lean_object* v___x_4229_; uint8_t v_isShared_4230_; uint8_t v_isSharedCheck_4234_; 
lean_dec(v_a_4200_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_4227_ = lean_ctor_get(v___x_4202_, 0);
v_isSharedCheck_4234_ = !lean_is_exclusive(v___x_4202_);
if (v_isSharedCheck_4234_ == 0)
{
v___x_4229_ = v___x_4202_;
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
else
{
lean_inc(v_a_4227_);
lean_dec(v___x_4202_);
v___x_4229_ = lean_box(0);
v_isShared_4230_ = v_isSharedCheck_4234_;
goto v_resetjp_4228_;
}
v_resetjp_4228_:
{
lean_object* v___x_4232_; 
if (v_isShared_4230_ == 0)
{
v___x_4232_ = v___x_4229_;
goto v_reusejp_4231_;
}
else
{
lean_object* v_reuseFailAlloc_4233_; 
v_reuseFailAlloc_4233_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4233_, 0, v_a_4227_);
v___x_4232_ = v_reuseFailAlloc_4233_;
goto v_reusejp_4231_;
}
v_reusejp_4231_:
{
return v___x_4232_;
}
}
}
}
else
{
lean_object* v_a_4235_; lean_object* v___x_4237_; uint8_t v_isShared_4238_; uint8_t v_isSharedCheck_4242_; 
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_4235_ = lean_ctor_get(v___x_4199_, 0);
v_isSharedCheck_4242_ = !lean_is_exclusive(v___x_4199_);
if (v_isSharedCheck_4242_ == 0)
{
v___x_4237_ = v___x_4199_;
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
else
{
lean_inc(v_a_4235_);
lean_dec(v___x_4199_);
v___x_4237_ = lean_box(0);
v_isShared_4238_ = v_isSharedCheck_4242_;
goto v_resetjp_4236_;
}
v_resetjp_4236_:
{
lean_object* v___x_4240_; 
if (v_isShared_4238_ == 0)
{
v___x_4240_ = v___x_4237_;
goto v_reusejp_4239_;
}
else
{
lean_object* v_reuseFailAlloc_4241_; 
v_reuseFailAlloc_4241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4241_, 0, v_a_4235_);
v___x_4240_ = v_reuseFailAlloc_4241_;
goto v_reusejp_4239_;
}
v_reusejp_4239_:
{
return v___x_4240_;
}
}
}
}
}
else
{
lean_object* v_a_4243_; lean_object* v___x_4245_; uint8_t v_isShared_4246_; uint8_t v_isSharedCheck_4250_; 
lean_dec_ref(v___x_4024_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4243_ = lean_ctor_get(v___x_4196_, 0);
v_isSharedCheck_4250_ = !lean_is_exclusive(v___x_4196_);
if (v_isSharedCheck_4250_ == 0)
{
v___x_4245_ = v___x_4196_;
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
else
{
lean_inc(v_a_4243_);
lean_dec(v___x_4196_);
v___x_4245_ = lean_box(0);
v_isShared_4246_ = v_isSharedCheck_4250_;
goto v_resetjp_4244_;
}
v_resetjp_4244_:
{
lean_object* v___x_4248_; 
if (v_isShared_4246_ == 0)
{
v___x_4248_ = v___x_4245_;
goto v_reusejp_4247_;
}
else
{
lean_object* v_reuseFailAlloc_4249_; 
v_reuseFailAlloc_4249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4249_, 0, v_a_4243_);
v___x_4248_ = v_reuseFailAlloc_4249_;
goto v_reusejp_4247_;
}
v_reusejp_4247_:
{
return v___x_4248_;
}
}
}
}
v___jp_4251_:
{
lean_object* v___x_4257_; 
lean_inc_ref(v___x_4024_);
v___x_4257_ = l_Lean_Meta_matchHEq_x3f(v___x_4024_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
if (lean_obj_tag(v___x_4257_) == 0)
{
lean_object* v_a_4258_; 
v_a_4258_ = lean_ctor_get(v___x_4257_, 0);
lean_inc(v_a_4258_);
lean_dec_ref_known(v___x_4257_, 1);
if (lean_obj_tag(v_a_4258_) == 1)
{
lean_object* v_val_4259_; lean_object* v_snd_4260_; lean_object* v_snd_4261_; lean_object* v_fst_4262_; lean_object* v_fst_4263_; lean_object* v_fst_4264_; lean_object* v_snd_4265_; lean_object* v___x_4266_; 
v_val_4259_ = lean_ctor_get(v_a_4258_, 0);
lean_inc(v_val_4259_);
lean_dec_ref_known(v_a_4258_, 1);
v_snd_4260_ = lean_ctor_get(v_val_4259_, 1);
lean_inc(v_snd_4260_);
v_snd_4261_ = lean_ctor_get(v_snd_4260_, 1);
lean_inc(v_snd_4261_);
v_fst_4262_ = lean_ctor_get(v_val_4259_, 0);
lean_inc(v_fst_4262_);
lean_dec(v_val_4259_);
v_fst_4263_ = lean_ctor_get(v_snd_4260_, 0);
lean_inc(v_fst_4263_);
lean_dec(v_snd_4260_);
v_fst_4264_ = lean_ctor_get(v_snd_4261_, 0);
lean_inc(v_fst_4264_);
v_snd_4265_ = lean_ctor_get(v_snd_4261_, 1);
lean_inc(v_snd_4265_);
lean_dec(v_snd_4261_);
v___x_4266_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4263_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
if (lean_obj_tag(v___x_4266_) == 0)
{
lean_object* v_a_4267_; 
v_a_4267_ = lean_ctor_get(v___x_4266_, 0);
lean_inc(v_a_4267_);
lean_dec_ref_known(v___x_4266_, 1);
if (lean_obj_tag(v_a_4267_) == 1)
{
lean_object* v_val_4268_; lean_object* v___x_4269_; 
v_val_4268_ = lean_ctor_get(v_a_4267_, 0);
lean_inc(v_val_4268_);
lean_dec_ref_known(v_a_4267_, 1);
v___x_4269_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4265_, v___y_4253_, v___y_4254_, v___y_4255_, v___y_4256_);
if (lean_obj_tag(v___x_4269_) == 0)
{
lean_object* v_a_4270_; 
v_a_4270_ = lean_ctor_get(v___x_4269_, 0);
lean_inc(v_a_4270_);
lean_dec_ref_known(v___x_4269_, 1);
if (lean_obj_tag(v_a_4270_) == 1)
{
lean_object* v_toConstantVal_4271_; lean_object* v_val_4272_; lean_object* v_toConstantVal_4273_; lean_object* v_name_4274_; lean_object* v_name_4275_; uint8_t v___x_4276_; 
v_toConstantVal_4271_ = lean_ctor_get(v_val_4268_, 0);
lean_inc_ref(v_toConstantVal_4271_);
lean_dec(v_val_4268_);
v_val_4272_ = lean_ctor_get(v_a_4270_, 0);
lean_inc(v_val_4272_);
lean_dec_ref_known(v_a_4270_, 1);
v_toConstantVal_4273_ = lean_ctor_get(v_val_4272_, 0);
lean_inc_ref(v_toConstantVal_4273_);
lean_dec(v_val_4272_);
v_name_4274_ = lean_ctor_get(v_toConstantVal_4271_, 0);
lean_inc(v_name_4274_);
lean_dec_ref(v_toConstantVal_4271_);
v_name_4275_ = lean_ctor_get(v_toConstantVal_4273_, 0);
lean_inc(v_name_4275_);
lean_dec_ref(v_toConstantVal_4273_);
v___x_4276_ = lean_name_eq(v_name_4274_, v_name_4275_);
lean_dec(v_name_4275_);
lean_dec(v_name_4274_);
if (v___x_4276_ == 0)
{
v___y_4189_ = v___y_4256_;
v___y_4190_ = v___y_4253_;
v___y_4191_ = v_isEq_4252_;
v___y_4192_ = v___y_4254_;
v___y_4193_ = v_fst_4264_;
v___y_4194_ = v___y_4255_;
v___y_4195_ = v_fst_4262_;
goto v___jp_4188_;
}
else
{
if (v___x_3979_ == 0)
{
lean_dec(v_fst_4264_);
lean_dec(v_fst_4262_);
v___y_4180_ = v_isEq_4252_;
v_isHEq_4181_ = v___x_3883_;
v___y_4182_ = v___y_4253_;
v___y_4183_ = v___y_4254_;
v___y_4184_ = v___y_4255_;
v___y_4185_ = v___y_4256_;
goto v___jp_4179_;
}
else
{
v___y_4189_ = v___y_4256_;
v___y_4190_ = v___y_4253_;
v___y_4191_ = v_isEq_4252_;
v___y_4192_ = v___y_4254_;
v___y_4193_ = v_fst_4264_;
v___y_4194_ = v___y_4255_;
v___y_4195_ = v_fst_4262_;
goto v___jp_4188_;
}
}
}
else
{
lean_dec(v_a_4270_);
lean_dec(v_val_4268_);
lean_dec(v_fst_4264_);
lean_dec(v_fst_4262_);
v___y_4180_ = v_isEq_4252_;
v_isHEq_4181_ = v___x_3883_;
v___y_4182_ = v___y_4253_;
v___y_4183_ = v___y_4254_;
v___y_4184_ = v___y_4255_;
v___y_4185_ = v___y_4256_;
goto v___jp_4179_;
}
}
else
{
lean_object* v_a_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v_val_4268_);
lean_dec(v_fst_4264_);
lean_dec(v_fst_4262_);
lean_dec_ref(v___x_4024_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4277_ = lean_ctor_get(v___x_4269_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4269_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4269_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_a_4277_);
lean_dec(v___x_4269_);
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
else
{
lean_dec(v_a_4267_);
lean_dec(v_snd_4265_);
lean_dec(v_fst_4264_);
lean_dec(v_fst_4262_);
v___y_4180_ = v_isEq_4252_;
v_isHEq_4181_ = v___x_3883_;
v___y_4182_ = v___y_4253_;
v___y_4183_ = v___y_4254_;
v___y_4184_ = v___y_4255_;
v___y_4185_ = v___y_4256_;
goto v___jp_4179_;
}
}
else
{
lean_object* v_a_4285_; lean_object* v___x_4287_; uint8_t v_isShared_4288_; uint8_t v_isSharedCheck_4292_; 
lean_dec(v_snd_4265_);
lean_dec(v_fst_4264_);
lean_dec(v_fst_4262_);
lean_dec_ref(v___x_4024_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4285_ = lean_ctor_get(v___x_4266_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4266_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4287_ = v___x_4266_;
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
else
{
lean_inc(v_a_4285_);
lean_dec(v___x_4266_);
v___x_4287_ = lean_box(0);
v_isShared_4288_ = v_isSharedCheck_4292_;
goto v_resetjp_4286_;
}
v_resetjp_4286_:
{
lean_object* v___x_4290_; 
if (v_isShared_4288_ == 0)
{
v___x_4290_ = v___x_4287_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v_a_4285_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
else
{
lean_dec(v_a_4258_);
v___y_4180_ = v_isEq_4252_;
v_isHEq_4181_ = v___x_3979_;
v___y_4182_ = v___y_4253_;
v___y_4183_ = v___y_4254_;
v___y_4184_ = v___y_4255_;
v___y_4185_ = v___y_4256_;
goto v___jp_4179_;
}
}
else
{
lean_object* v_a_4293_; lean_object* v___x_4295_; uint8_t v_isShared_4296_; uint8_t v_isSharedCheck_4300_; 
lean_dec_ref(v___x_4024_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4293_ = lean_ctor_get(v___x_4257_, 0);
v_isSharedCheck_4300_ = !lean_is_exclusive(v___x_4257_);
if (v_isSharedCheck_4300_ == 0)
{
v___x_4295_ = v___x_4257_;
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
else
{
lean_inc(v_a_4293_);
lean_dec(v___x_4257_);
v___x_4295_ = lean_box(0);
v_isShared_4296_ = v_isSharedCheck_4300_;
goto v_resetjp_4294_;
}
v_resetjp_4294_:
{
lean_object* v___x_4298_; 
if (v_isShared_4296_ == 0)
{
v___x_4298_ = v___x_4295_;
goto v_reusejp_4297_;
}
else
{
lean_object* v_reuseFailAlloc_4299_; 
v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
v___x_4298_ = v_reuseFailAlloc_4299_;
goto v_reusejp_4297_;
}
v_reusejp_4297_:
{
return v___x_4298_;
}
}
}
}
v___jp_4301_:
{
lean_object* v___x_4306_; 
lean_inc_ref(v___x_4024_);
v___x_4306_ = l_Lean_Meta_matchEq_x3f(v___x_4024_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4306_) == 0)
{
lean_object* v_a_4307_; 
v_a_4307_ = lean_ctor_get(v___x_4306_, 0);
lean_inc(v_a_4307_);
lean_dec_ref_known(v___x_4306_, 1);
if (lean_obj_tag(v_a_4307_) == 1)
{
lean_object* v_val_4308_; lean_object* v_snd_4309_; lean_object* v_fst_4310_; lean_object* v_snd_4311_; lean_object* v___x_4312_; 
v_val_4308_ = lean_ctor_get(v_a_4307_, 0);
lean_inc(v_val_4308_);
lean_dec_ref_known(v_a_4307_, 1);
v_snd_4309_ = lean_ctor_get(v_val_4308_, 1);
lean_inc(v_snd_4309_);
lean_dec(v_val_4308_);
v_fst_4310_ = lean_ctor_get(v_snd_4309_, 0);
lean_inc(v_fst_4310_);
v_snd_4311_ = lean_ctor_get(v_snd_4309_, 1);
lean_inc(v_snd_4311_);
lean_dec(v_snd_4309_);
v___x_4312_ = l_Lean_Meta_matchConstructorApp_x3f(v_fst_4310_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
lean_inc(v_a_4313_);
lean_dec_ref_known(v___x_4312_, 1);
if (lean_obj_tag(v_a_4313_) == 1)
{
lean_object* v_val_4314_; lean_object* v___x_4315_; 
v_val_4314_ = lean_ctor_get(v_a_4313_, 0);
lean_inc(v_val_4314_);
lean_dec_ref_known(v_a_4313_, 1);
v___x_4315_ = l_Lean_Meta_matchConstructorApp_x3f(v_snd_4311_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_);
if (lean_obj_tag(v___x_4315_) == 0)
{
lean_object* v_a_4316_; 
v_a_4316_ = lean_ctor_get(v___x_4315_, 0);
lean_inc(v_a_4316_);
lean_dec_ref_known(v___x_4315_, 1);
if (lean_obj_tag(v_a_4316_) == 1)
{
lean_object* v_toConstantVal_4317_; lean_object* v_val_4318_; lean_object* v_toConstantVal_4319_; lean_object* v_name_4320_; lean_object* v_name_4321_; uint8_t v___x_4322_; 
v_toConstantVal_4317_ = lean_ctor_get(v_val_4314_, 0);
lean_inc_ref(v_toConstantVal_4317_);
lean_dec(v_val_4314_);
v_val_4318_ = lean_ctor_get(v_a_4316_, 0);
lean_inc(v_val_4318_);
lean_dec_ref_known(v_a_4316_, 1);
v_toConstantVal_4319_ = lean_ctor_get(v_val_4318_, 0);
lean_inc_ref(v_toConstantVal_4319_);
lean_dec(v_val_4318_);
v_name_4320_ = lean_ctor_get(v_toConstantVal_4317_, 0);
lean_inc(v_name_4320_);
lean_dec_ref(v_toConstantVal_4317_);
v_name_4321_ = lean_ctor_get(v_toConstantVal_4319_, 0);
lean_inc(v_name_4321_);
lean_dec_ref(v_toConstantVal_4319_);
v___x_4322_ = lean_name_eq(v_name_4320_, v_name_4321_);
lean_dec(v_name_4321_);
lean_dec(v_name_4320_);
if (v___x_4322_ == 0)
{
lean_dec_ref(v___x_4024_);
lean_dec_ref(v_config_3872_);
v___y_3910_ = v___y_4305_;
v___y_3911_ = v___y_4304_;
v___y_3912_ = v___y_4303_;
v___y_3913_ = v___y_4302_;
goto v___jp_3909_;
}
else
{
if (v___x_3979_ == 0)
{
lean_del_object(v___x_3906_);
v_isEq_4252_ = v___x_3883_;
v___y_4253_ = v___y_4302_;
v___y_4254_ = v___y_4303_;
v___y_4255_ = v___y_4304_;
v___y_4256_ = v___y_4305_;
goto v___jp_4251_;
}
else
{
lean_dec_ref(v___x_4024_);
lean_dec_ref(v_config_3872_);
v___y_3910_ = v___y_4305_;
v___y_3911_ = v___y_4304_;
v___y_3912_ = v___y_4303_;
v___y_3913_ = v___y_4302_;
goto v___jp_3909_;
}
}
}
else
{
lean_dec(v_a_4316_);
lean_dec(v_val_4314_);
lean_del_object(v___x_3906_);
v_isEq_4252_ = v___x_3883_;
v___y_4253_ = v___y_4302_;
v___y_4254_ = v___y_4303_;
v___y_4255_ = v___y_4304_;
v___y_4256_ = v___y_4305_;
goto v___jp_4251_;
}
}
else
{
lean_object* v_a_4323_; lean_object* v___x_4325_; uint8_t v_isShared_4326_; uint8_t v_isSharedCheck_4330_; 
lean_dec(v_val_4314_);
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4323_ = lean_ctor_get(v___x_4315_, 0);
v_isSharedCheck_4330_ = !lean_is_exclusive(v___x_4315_);
if (v_isSharedCheck_4330_ == 0)
{
v___x_4325_ = v___x_4315_;
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
else
{
lean_inc(v_a_4323_);
lean_dec(v___x_4315_);
v___x_4325_ = lean_box(0);
v_isShared_4326_ = v_isSharedCheck_4330_;
goto v_resetjp_4324_;
}
v_resetjp_4324_:
{
lean_object* v___x_4328_; 
if (v_isShared_4326_ == 0)
{
v___x_4328_ = v___x_4325_;
goto v_reusejp_4327_;
}
else
{
lean_object* v_reuseFailAlloc_4329_; 
v_reuseFailAlloc_4329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4329_, 0, v_a_4323_);
v___x_4328_ = v_reuseFailAlloc_4329_;
goto v_reusejp_4327_;
}
v_reusejp_4327_:
{
return v___x_4328_;
}
}
}
}
else
{
lean_dec(v_a_4313_);
lean_dec(v_snd_4311_);
lean_del_object(v___x_3906_);
v_isEq_4252_ = v___x_3883_;
v___y_4253_ = v___y_4302_;
v___y_4254_ = v___y_4303_;
v___y_4255_ = v___y_4304_;
v___y_4256_ = v___y_4305_;
goto v___jp_4251_;
}
}
else
{
lean_object* v_a_4331_; lean_object* v___x_4333_; uint8_t v_isShared_4334_; uint8_t v_isSharedCheck_4338_; 
lean_dec(v_snd_4311_);
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4331_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4338_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4338_ == 0)
{
v___x_4333_ = v___x_4312_;
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
else
{
lean_inc(v_a_4331_);
lean_dec(v___x_4312_);
v___x_4333_ = lean_box(0);
v_isShared_4334_ = v_isSharedCheck_4338_;
goto v_resetjp_4332_;
}
v_resetjp_4332_:
{
lean_object* v___x_4336_; 
if (v_isShared_4334_ == 0)
{
v___x_4336_ = v___x_4333_;
goto v_reusejp_4335_;
}
else
{
lean_object* v_reuseFailAlloc_4337_; 
v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
v___x_4336_ = v_reuseFailAlloc_4337_;
goto v_reusejp_4335_;
}
v_reusejp_4335_:
{
return v___x_4336_;
}
}
}
}
else
{
lean_dec(v_a_4307_);
lean_del_object(v___x_3906_);
v_isEq_4252_ = v___x_3979_;
v___y_4253_ = v___y_4302_;
v___y_4254_ = v___y_4303_;
v___y_4255_ = v___y_4304_;
v___y_4256_ = v___y_4305_;
goto v___jp_4251_;
}
}
else
{
lean_object* v_a_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4346_; 
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4339_ = lean_ctor_get(v___x_4306_, 0);
v_isSharedCheck_4346_ = !lean_is_exclusive(v___x_4306_);
if (v_isSharedCheck_4346_ == 0)
{
v___x_4341_ = v___x_4306_;
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_a_4339_);
lean_dec(v___x_4306_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4346_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4344_; 
if (v_isShared_4342_ == 0)
{
v___x_4344_ = v___x_4341_;
goto v_reusejp_4343_;
}
else
{
lean_object* v_reuseFailAlloc_4345_; 
v_reuseFailAlloc_4345_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4345_, 0, v_a_4339_);
v___x_4344_ = v_reuseFailAlloc_4345_;
goto v_reusejp_4343_;
}
v_reusejp_4343_:
{
return v___x_4344_;
}
}
}
}
v___jp_4347_:
{
lean_object* v___x_4352_; 
lean_inc_ref(v___x_4024_);
v___x_4352_ = l_Lean_refutableHasNotBit_x3f(v___x_4024_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4352_) == 0)
{
lean_object* v_a_4353_; 
v_a_4353_ = lean_ctor_get(v___x_4352_, 0);
lean_inc(v_a_4353_);
lean_dec_ref_known(v___x_4352_, 1);
if (lean_obj_tag(v_a_4353_) == 1)
{
lean_object* v_val_4354_; lean_object* v___x_4356_; uint8_t v_isShared_4357_; uint8_t v_isSharedCheck_4394_; 
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec_ref(v_config_3872_);
v_val_4354_ = lean_ctor_get(v_a_4353_, 0);
v_isSharedCheck_4394_ = !lean_is_exclusive(v_a_4353_);
if (v_isSharedCheck_4394_ == 0)
{
v___x_4356_ = v_a_4353_;
v_isShared_4357_ = v_isSharedCheck_4394_;
goto v_resetjp_4355_;
}
else
{
lean_inc(v_val_4354_);
lean_dec(v_a_4353_);
v___x_4356_ = lean_box(0);
v_isShared_4357_ = v_isSharedCheck_4394_;
goto v_resetjp_4355_;
}
v_resetjp_4355_:
{
lean_object* v___x_4358_; 
lean_inc(v_mvarId_3873_);
v___x_4358_ = l_Lean_MVarId_getType(v_mvarId_3873_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4358_) == 0)
{
lean_object* v_a_4359_; lean_object* v___x_4360_; lean_object* v___x_4361_; 
v_a_4359_ = lean_ctor_get(v___x_4358_, 0);
lean_inc(v_a_4359_);
lean_dec_ref_known(v___x_4358_, 1);
v___x_4360_ = l_Lean_LocalDecl_toExpr(v_val_3904_);
v___x_4361_ = l_Lean_Meta_mkAbsurd(v_a_4359_, v_val_4354_, v___x_4360_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___x_4363_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4361_, 1);
v___x_4363_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3873_, v_a_4362_, v___y_4349_);
if (lean_obj_tag(v___x_4363_) == 0)
{
lean_object* v___x_4364_; lean_object* v___x_4366_; 
lean_dec_ref_known(v___x_4363_, 1);
v___x_4364_ = lean_box(v___x_3883_);
if (v_isShared_4357_ == 0)
{
lean_ctor_set(v___x_4356_, 0, v___x_4364_);
v___x_4366_ = v___x_4356_;
goto v_reusejp_4365_;
}
else
{
lean_object* v_reuseFailAlloc_4369_; 
v_reuseFailAlloc_4369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4369_, 0, v___x_4364_);
v___x_4366_ = v_reuseFailAlloc_4369_;
goto v_reusejp_4365_;
}
v_reusejp_4365_:
{
lean_object* v___x_4367_; lean_object* v___x_4368_; 
v___x_4367_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4367_, 0, v___x_4366_);
lean_ctor_set(v___x_4367_, 1, v___x_3908_);
v___x_4368_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4368_, 0, v___x_4367_);
v_a_3890_ = v___x_4368_;
goto v___jp_3889_;
}
}
else
{
lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4377_; 
lean_del_object(v___x_4356_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
v_a_4370_ = lean_ctor_get(v___x_4363_, 0);
v_isSharedCheck_4377_ = !lean_is_exclusive(v___x_4363_);
if (v_isSharedCheck_4377_ == 0)
{
v___x_4372_ = v___x_4363_;
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4363_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4377_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4375_; 
if (v_isShared_4373_ == 0)
{
v___x_4375_ = v___x_4372_;
goto v_reusejp_4374_;
}
else
{
lean_object* v_reuseFailAlloc_4376_; 
v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4370_);
v___x_4375_ = v_reuseFailAlloc_4376_;
goto v_reusejp_4374_;
}
v_reusejp_4374_:
{
return v___x_4375_;
}
}
}
}
else
{
lean_object* v_a_4378_; lean_object* v___x_4380_; uint8_t v_isShared_4381_; uint8_t v_isSharedCheck_4385_; 
lean_del_object(v___x_4356_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_4378_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4385_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4385_ == 0)
{
v___x_4380_ = v___x_4361_;
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
else
{
lean_inc(v_a_4378_);
lean_dec(v___x_4361_);
v___x_4380_ = lean_box(0);
v_isShared_4381_ = v_isSharedCheck_4385_;
goto v_resetjp_4379_;
}
v_resetjp_4379_:
{
lean_object* v___x_4383_; 
if (v_isShared_4381_ == 0)
{
v___x_4383_ = v___x_4380_;
goto v_reusejp_4382_;
}
else
{
lean_object* v_reuseFailAlloc_4384_; 
v_reuseFailAlloc_4384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4384_, 0, v_a_4378_);
v___x_4383_ = v_reuseFailAlloc_4384_;
goto v_reusejp_4382_;
}
v_reusejp_4382_:
{
return v___x_4383_;
}
}
}
}
else
{
lean_object* v_a_4386_; lean_object* v___x_4388_; uint8_t v_isShared_4389_; uint8_t v_isSharedCheck_4393_; 
lean_del_object(v___x_4356_);
lean_dec(v_val_4354_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_4386_ = lean_ctor_get(v___x_4358_, 0);
v_isSharedCheck_4393_ = !lean_is_exclusive(v___x_4358_);
if (v_isSharedCheck_4393_ == 0)
{
v___x_4388_ = v___x_4358_;
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
else
{
lean_inc(v_a_4386_);
lean_dec(v___x_4358_);
v___x_4388_ = lean_box(0);
v_isShared_4389_ = v_isSharedCheck_4393_;
goto v_resetjp_4387_;
}
v_resetjp_4387_:
{
lean_object* v___x_4391_; 
if (v_isShared_4389_ == 0)
{
v___x_4391_ = v___x_4388_;
goto v_reusejp_4390_;
}
else
{
lean_object* v_reuseFailAlloc_4392_; 
v_reuseFailAlloc_4392_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4392_, 0, v_a_4386_);
v___x_4391_ = v_reuseFailAlloc_4392_;
goto v_reusejp_4390_;
}
v_reusejp_4390_:
{
return v___x_4391_;
}
}
}
}
}
else
{
lean_object* v___x_4395_; 
lean_dec(v_a_4353_);
lean_inc_ref(v___x_4024_);
v___x_4395_ = l_Lean_Meta_matchNe_x3f(v___x_4024_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
if (lean_obj_tag(v_a_4396_) == 1)
{
lean_object* v_val_4397_; lean_object* v___x_4399_; uint8_t v_isShared_4400_; uint8_t v_isSharedCheck_4467_; 
v_val_4397_ = lean_ctor_get(v_a_4396_, 0);
v_isSharedCheck_4467_ = !lean_is_exclusive(v_a_4396_);
if (v_isSharedCheck_4467_ == 0)
{
v___x_4399_ = v_a_4396_;
v_isShared_4400_ = v_isSharedCheck_4467_;
goto v_resetjp_4398_;
}
else
{
lean_inc(v_val_4397_);
lean_dec(v_a_4396_);
v___x_4399_ = lean_box(0);
v_isShared_4400_ = v_isSharedCheck_4467_;
goto v_resetjp_4398_;
}
v_resetjp_4398_:
{
lean_object* v_snd_4401_; lean_object* v_fst_4402_; lean_object* v_snd_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4466_; 
v_snd_4401_ = lean_ctor_get(v_val_4397_, 1);
lean_inc(v_snd_4401_);
lean_dec(v_val_4397_);
v_fst_4402_ = lean_ctor_get(v_snd_4401_, 0);
v_snd_4403_ = lean_ctor_get(v_snd_4401_, 1);
v_isSharedCheck_4466_ = !lean_is_exclusive(v_snd_4401_);
if (v_isSharedCheck_4466_ == 0)
{
v___x_4405_ = v_snd_4401_;
v_isShared_4406_ = v_isSharedCheck_4466_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_snd_4403_);
lean_inc(v_fst_4402_);
lean_dec(v_snd_4401_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4466_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4407_; 
lean_inc(v_fst_4402_);
v___x_4407_ = l_Lean_Meta_isExprDefEq(v_fst_4402_, v_snd_4403_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4407_) == 0)
{
lean_object* v_a_4408_; uint8_t v___x_4409_; 
v_a_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc(v_a_4408_);
lean_dec_ref_known(v___x_4407_, 1);
v___x_4409_ = lean_unbox(v_a_4408_);
lean_dec(v_a_4408_);
if (v___x_4409_ == 0)
{
lean_del_object(v___x_4405_);
lean_dec(v_fst_4402_);
lean_del_object(v___x_4399_);
v___y_4302_ = v___y_4348_;
v___y_4303_ = v___y_4349_;
v___y_4304_ = v___y_4350_;
v___y_4305_ = v___y_4351_;
goto v___jp_4301_;
}
else
{
lean_object* v___x_4410_; 
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec_ref(v_config_3872_);
lean_inc(v_mvarId_3873_);
v___x_4410_ = l_Lean_MVarId_getType(v_mvarId_3873_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4412_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
lean_inc(v_a_4411_);
lean_dec_ref_known(v___x_4410_, 1);
v___x_4412_ = l_Lean_Meta_mkEqRefl(v_fst_4402_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
v___x_4414_ = l_Lean_LocalDecl_toExpr(v_val_3904_);
v___x_4415_ = l_Lean_Meta_mkAbsurd(v_a_4411_, v_a_4413_, v___x_4414_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_object* v_a_4416_; lean_object* v___x_4417_; 
v_a_4416_ = lean_ctor_get(v___x_4415_, 0);
lean_inc(v_a_4416_);
lean_dec_ref_known(v___x_4415_, 1);
v___x_4417_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3873_, v_a_4416_, v___y_4349_);
if (lean_obj_tag(v___x_4417_) == 0)
{
lean_object* v___x_4418_; lean_object* v___x_4420_; 
lean_dec_ref_known(v___x_4417_, 1);
v___x_4418_ = lean_box(v___x_3883_);
if (v_isShared_4400_ == 0)
{
lean_ctor_set(v___x_4399_, 0, v___x_4418_);
v___x_4420_ = v___x_4399_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4418_);
v___x_4420_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
lean_object* v___x_4422_; 
if (v_isShared_4406_ == 0)
{
lean_ctor_set(v___x_4405_, 1, v___x_3908_);
lean_ctor_set(v___x_4405_, 0, v___x_4420_);
v___x_4422_ = v___x_4405_;
goto v_reusejp_4421_;
}
else
{
lean_object* v_reuseFailAlloc_4424_; 
v_reuseFailAlloc_4424_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4424_, 0, v___x_4420_);
lean_ctor_set(v_reuseFailAlloc_4424_, 1, v___x_3908_);
v___x_4422_ = v_reuseFailAlloc_4424_;
goto v_reusejp_4421_;
}
v_reusejp_4421_:
{
lean_object* v___x_4423_; 
v___x_4423_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4422_);
v_a_3890_ = v___x_4423_;
goto v___jp_3889_;
}
}
}
else
{
lean_object* v_a_4426_; lean_object* v___x_4428_; uint8_t v_isShared_4429_; uint8_t v_isSharedCheck_4433_; 
lean_del_object(v___x_4405_);
lean_del_object(v___x_4399_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
v_a_4426_ = lean_ctor_get(v___x_4417_, 0);
v_isSharedCheck_4433_ = !lean_is_exclusive(v___x_4417_);
if (v_isSharedCheck_4433_ == 0)
{
v___x_4428_ = v___x_4417_;
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
else
{
lean_inc(v_a_4426_);
lean_dec(v___x_4417_);
v___x_4428_ = lean_box(0);
v_isShared_4429_ = v_isSharedCheck_4433_;
goto v_resetjp_4427_;
}
v_resetjp_4427_:
{
lean_object* v___x_4431_; 
if (v_isShared_4429_ == 0)
{
v___x_4431_ = v___x_4428_;
goto v_reusejp_4430_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4426_);
v___x_4431_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4430_;
}
v_reusejp_4430_:
{
return v___x_4431_;
}
}
}
}
else
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4441_; 
lean_del_object(v___x_4405_);
lean_del_object(v___x_4399_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_4434_ = lean_ctor_get(v___x_4415_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4415_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4436_ = v___x_4415_;
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4415_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4441_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v___x_4439_; 
if (v_isShared_4437_ == 0)
{
v___x_4439_ = v___x_4436_;
goto v_reusejp_4438_;
}
else
{
lean_object* v_reuseFailAlloc_4440_; 
v_reuseFailAlloc_4440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4440_, 0, v_a_4434_);
v___x_4439_ = v_reuseFailAlloc_4440_;
goto v_reusejp_4438_;
}
v_reusejp_4438_:
{
return v___x_4439_;
}
}
}
}
else
{
lean_object* v_a_4442_; lean_object* v___x_4444_; uint8_t v_isShared_4445_; uint8_t v_isSharedCheck_4449_; 
lean_dec(v_a_4411_);
lean_del_object(v___x_4405_);
lean_del_object(v___x_4399_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_4442_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4449_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4449_ == 0)
{
v___x_4444_ = v___x_4412_;
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
else
{
lean_inc(v_a_4442_);
lean_dec(v___x_4412_);
v___x_4444_ = lean_box(0);
v_isShared_4445_ = v_isSharedCheck_4449_;
goto v_resetjp_4443_;
}
v_resetjp_4443_:
{
lean_object* v___x_4447_; 
if (v_isShared_4445_ == 0)
{
v___x_4447_ = v___x_4444_;
goto v_reusejp_4446_;
}
else
{
lean_object* v_reuseFailAlloc_4448_; 
v_reuseFailAlloc_4448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4448_, 0, v_a_4442_);
v___x_4447_ = v_reuseFailAlloc_4448_;
goto v_reusejp_4446_;
}
v_reusejp_4446_:
{
return v___x_4447_;
}
}
}
}
else
{
lean_object* v_a_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_del_object(v___x_4405_);
lean_dec(v_fst_4402_);
lean_del_object(v___x_4399_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_4450_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4410_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_a_4450_);
lean_dec(v___x_4410_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_a_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
}
else
{
lean_object* v_a_4458_; lean_object* v___x_4460_; uint8_t v_isShared_4461_; uint8_t v_isSharedCheck_4465_; 
lean_del_object(v___x_4405_);
lean_dec(v_fst_4402_);
lean_del_object(v___x_4399_);
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4458_ = lean_ctor_get(v___x_4407_, 0);
v_isSharedCheck_4465_ = !lean_is_exclusive(v___x_4407_);
if (v_isSharedCheck_4465_ == 0)
{
v___x_4460_ = v___x_4407_;
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
else
{
lean_inc(v_a_4458_);
lean_dec(v___x_4407_);
v___x_4460_ = lean_box(0);
v_isShared_4461_ = v_isSharedCheck_4465_;
goto v_resetjp_4459_;
}
v_resetjp_4459_:
{
lean_object* v___x_4463_; 
if (v_isShared_4461_ == 0)
{
v___x_4463_ = v___x_4460_;
goto v_reusejp_4462_;
}
else
{
lean_object* v_reuseFailAlloc_4464_; 
v_reuseFailAlloc_4464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4464_, 0, v_a_4458_);
v___x_4463_ = v_reuseFailAlloc_4464_;
goto v_reusejp_4462_;
}
v_reusejp_4462_:
{
return v___x_4463_;
}
}
}
}
}
}
else
{
lean_dec(v_a_4396_);
v___y_4302_ = v___y_4348_;
v___y_4303_ = v___y_4349_;
v___y_4304_ = v___y_4350_;
v___y_4305_ = v___y_4351_;
goto v___jp_4301_;
}
}
else
{
lean_object* v_a_4468_; lean_object* v___x_4470_; uint8_t v_isShared_4471_; uint8_t v_isSharedCheck_4475_; 
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4468_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4475_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4475_ == 0)
{
v___x_4470_ = v___x_4395_;
v_isShared_4471_ = v_isSharedCheck_4475_;
goto v_resetjp_4469_;
}
else
{
lean_inc(v_a_4468_);
lean_dec(v___x_4395_);
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
lean_object* v_a_4476_; lean_object* v___x_4478_; uint8_t v_isShared_4479_; uint8_t v_isSharedCheck_4483_; 
lean_dec_ref(v___x_4024_);
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4476_ = lean_ctor_get(v___x_4352_, 0);
v_isSharedCheck_4483_ = !lean_is_exclusive(v___x_4352_);
if (v_isSharedCheck_4483_ == 0)
{
v___x_4478_ = v___x_4352_;
v_isShared_4479_ = v_isSharedCheck_4483_;
goto v_resetjp_4477_;
}
else
{
lean_inc(v_a_4476_);
lean_dec(v___x_4352_);
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
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
v_a_3898_ = v___x_3950_;
goto v___jp_3897_;
}
v___jp_3909_:
{
lean_object* v___x_3914_; 
lean_inc(v_mvarId_3873_);
v___x_3914_ = l_Lean_MVarId_getType(v_mvarId_3873_, v___y_3913_, v___y_3912_, v___y_3911_, v___y_3910_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3916_; lean_object* v___x_3917_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
lean_inc(v_a_3915_);
lean_dec_ref_known(v___x_3914_, 1);
v___x_3916_ = l_Lean_LocalDecl_toExpr(v_val_3904_);
v___x_3917_ = l_Lean_Meta_mkNoConfusion(v_a_3915_, v___x_3916_, v___y_3913_, v___y_3912_, v___y_3911_, v___y_3910_);
if (lean_obj_tag(v___x_3917_) == 0)
{
lean_object* v_a_3918_; lean_object* v___x_3919_; 
v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
lean_inc(v_a_3918_);
lean_dec_ref_known(v___x_3917_, 1);
v___x_3919_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim_spec__0___redArg(v_mvarId_3873_, v_a_3918_, v___y_3912_);
if (lean_obj_tag(v___x_3919_) == 0)
{
lean_object* v___x_3920_; lean_object* v___x_3922_; 
lean_dec_ref_known(v___x_3919_, 1);
v___x_3920_ = lean_box(v___x_3883_);
if (v_isShared_3907_ == 0)
{
lean_ctor_set(v___x_3906_, 0, v___x_3920_);
v___x_3922_ = v___x_3906_;
goto v_reusejp_3921_;
}
else
{
lean_object* v_reuseFailAlloc_3925_; 
v_reuseFailAlloc_3925_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3920_);
v___x_3922_ = v_reuseFailAlloc_3925_;
goto v_reusejp_3921_;
}
v_reusejp_3921_:
{
lean_object* v___x_3923_; lean_object* v___x_3924_; 
v___x_3923_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3923_, 0, v___x_3922_);
lean_ctor_set(v___x_3923_, 1, v___x_3908_);
v___x_3924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3924_, 0, v___x_3923_);
v_a_3890_ = v___x_3924_;
goto v___jp_3889_;
}
}
else
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3933_; 
lean_del_object(v___x_3906_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
v_a_3926_ = lean_ctor_get(v___x_3919_, 0);
v_isSharedCheck_3933_ = !lean_is_exclusive(v___x_3919_);
if (v_isSharedCheck_3933_ == 0)
{
v___x_3928_ = v___x_3919_;
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3919_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3933_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
lean_object* v___x_3931_; 
if (v_isShared_3929_ == 0)
{
v___x_3931_ = v___x_3928_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3932_; 
v_reuseFailAlloc_3932_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3932_, 0, v_a_3926_);
v___x_3931_ = v_reuseFailAlloc_3932_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
return v___x_3931_;
}
}
}
}
else
{
lean_object* v_a_3934_; lean_object* v___x_3936_; uint8_t v_isShared_3937_; uint8_t v_isSharedCheck_3941_; 
lean_del_object(v___x_3906_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_3934_ = lean_ctor_get(v___x_3917_, 0);
v_isSharedCheck_3941_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3941_ == 0)
{
v___x_3936_ = v___x_3917_;
v_isShared_3937_ = v_isSharedCheck_3941_;
goto v_resetjp_3935_;
}
else
{
lean_inc(v_a_3934_);
lean_dec(v___x_3917_);
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
else
{
lean_object* v_a_3942_; lean_object* v___x_3944_; uint8_t v_isShared_3945_; uint8_t v_isSharedCheck_3949_; 
lean_del_object(v___x_3906_);
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
v_a_3942_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3949_ == 0)
{
v___x_3944_ = v___x_3914_;
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
else
{
lean_inc(v_a_3942_);
lean_dec(v___x_3914_);
v___x_3944_ = lean_box(0);
v_isShared_3945_ = v_isSharedCheck_3949_;
goto v_resetjp_3943_;
}
v_resetjp_3943_:
{
lean_object* v___x_3947_; 
if (v_isShared_3945_ == 0)
{
v___x_3947_ = v___x_3944_;
goto v_reusejp_3946_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_a_3942_);
v___x_3947_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3946_;
}
v_reusejp_3946_:
{
return v___x_3947_;
}
}
}
}
v___jp_3951_:
{
lean_object* v_searchFuel_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; 
v_searchFuel_3956_ = lean_ctor_get(v_config_3872_, 0);
v___x_3957_ = l_Lean_LocalDecl_fvarId(v_val_3904_);
lean_dec(v_val_3904_);
lean_inc(v_searchFuel_3956_);
lean_inc(v_mvarId_3873_);
v___x_3958_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive(v_mvarId_3873_, v___x_3957_, v_searchFuel_3956_, v___y_3952_, v___y_3953_, v___y_3955_, v___y_3954_);
if (lean_obj_tag(v___x_3958_) == 0)
{
lean_object* v_a_3959_; uint8_t v___x_3960_; 
v_a_3959_ = lean_ctor_get(v___x_3958_, 0);
lean_inc(v_a_3959_);
lean_dec_ref_known(v___x_3958_, 1);
v___x_3960_ = lean_unbox(v_a_3959_);
lean_dec(v_a_3959_);
if (v___x_3960_ == 0)
{
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
v_a_3898_ = v___x_3950_;
goto v___jp_3897_;
}
else
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; 
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v___x_3961_ = lean_box(v___x_3883_);
v___x_3962_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3962_, 0, v___x_3961_);
v___x_3963_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3963_, 0, v___x_3962_);
lean_ctor_set(v___x_3963_, 1, v___x_3908_);
v___x_3964_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3964_, 0, v___x_3963_);
v_a_3890_ = v___x_3964_;
goto v___jp_3889_;
}
}
else
{
lean_object* v_a_3965_; lean_object* v___x_3967_; uint8_t v_isShared_3968_; uint8_t v_isSharedCheck_3972_; 
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_3965_ = lean_ctor_get(v___x_3958_, 0);
v_isSharedCheck_3972_ = !lean_is_exclusive(v___x_3958_);
if (v_isSharedCheck_3972_ == 0)
{
v___x_3967_ = v___x_3958_;
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
else
{
lean_inc(v_a_3965_);
lean_dec(v___x_3958_);
v___x_3967_ = lean_box(0);
v_isShared_3968_ = v_isSharedCheck_3972_;
goto v_resetjp_3966_;
}
v_resetjp_3966_:
{
lean_object* v___x_3970_; 
if (v_isShared_3968_ == 0)
{
v___x_3970_ = v___x_3967_;
goto v_reusejp_3969_;
}
else
{
lean_object* v_reuseFailAlloc_3971_; 
v_reuseFailAlloc_3971_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3971_, 0, v_a_3965_);
v___x_3970_ = v_reuseFailAlloc_3971_;
goto v_reusejp_3969_;
}
v_reusejp_3969_:
{
return v___x_3970_;
}
}
}
}
v___jp_3973_:
{
if (v___y_3978_ == 0)
{
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
v_a_3898_ = v___x_3950_;
goto v___jp_3897_;
}
else
{
v___y_3952_ = v___y_3974_;
v___y_3953_ = v___y_3975_;
v___y_3954_ = v___y_3976_;
v___y_3955_ = v___y_3977_;
goto v___jp_3951_;
}
}
v___jp_3980_:
{
if (v___y_3985_ == 0)
{
v___y_3952_ = v___y_3981_;
v___y_3953_ = v___y_3982_;
v___y_3954_ = v___y_3983_;
v___y_3955_ = v___y_3984_;
goto v___jp_3951_;
}
else
{
v___y_3974_ = v___y_3981_;
v___y_3975_ = v___y_3982_;
v___y_3976_ = v___y_3983_;
v___y_3977_ = v___y_3984_;
v___y_3978_ = v___x_3979_;
goto v___jp_3973_;
}
}
v___jp_3986_:
{
if (v___y_3992_ == 0)
{
v___y_3974_ = v___y_3987_;
v___y_3975_ = v___y_3988_;
v___y_3976_ = v___y_3989_;
v___y_3977_ = v___y_3990_;
v___y_3978_ = v___x_3979_;
goto v___jp_3973_;
}
else
{
v___y_3981_ = v___y_3987_;
v___y_3982_ = v___y_3988_;
v___y_3983_ = v___y_3989_;
v___y_3984_ = v___y_3990_;
v___y_3985_ = v___y_3991_;
goto v___jp_3980_;
}
}
v___jp_3993_:
{
uint8_t v_emptyType_4000_; 
v_emptyType_4000_ = lean_ctor_get_uint8(v_config_3872_, sizeof(void*)*1 + 1);
if (v_emptyType_4000_ == 0)
{
v___y_3987_ = v___y_3996_;
v___y_3988_ = v___y_3997_;
v___y_3989_ = v___y_3999_;
v___y_3990_ = v___y_3998_;
v___y_3991_ = v___y_3995_;
v___y_3992_ = v___x_3979_;
goto v___jp_3986_;
}
else
{
if (v___y_3994_ == 0)
{
v___y_3981_ = v___y_3996_;
v___y_3982_ = v___y_3997_;
v___y_3983_ = v___y_3999_;
v___y_3984_ = v___y_3998_;
v___y_3985_ = v___y_3995_;
goto v___jp_3980_;
}
else
{
v___y_3987_ = v___y_3996_;
v___y_3988_ = v___y_3997_;
v___y_3989_ = v___y_3999_;
v___y_3990_ = v___y_3998_;
v___y_3991_ = v___y_3995_;
v___y_3992_ = v___x_3979_;
goto v___jp_3986_;
}
}
}
v___jp_4001_:
{
if (v___y_4008_ == 0)
{
v___y_3994_ = v___y_4002_;
v___y_3995_ = v___y_4005_;
v___y_3996_ = v___y_4003_;
v___y_3997_ = v___y_4004_;
v___y_3998_ = v___y_4007_;
v___y_3999_ = v___y_4006_;
goto v___jp_3993_;
}
else
{
lean_object* v___x_4009_; 
lean_inc(v_val_3904_);
lean_inc(v_mvarId_3873_);
v___x_4009_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_processGenDiseq(v_mvarId_3873_, v_val_3904_, v___y_4003_, v___y_4004_, v___y_4007_, v___y_4006_);
if (lean_obj_tag(v___x_4009_) == 0)
{
lean_object* v_a_4010_; uint8_t v___x_4011_; 
v_a_4010_ = lean_ctor_get(v___x_4009_, 0);
lean_inc(v_a_4010_);
lean_dec_ref_known(v___x_4009_, 1);
v___x_4011_ = lean_unbox(v_a_4010_);
lean_dec(v_a_4010_);
if (v___x_4011_ == 0)
{
v___y_3994_ = v___y_4002_;
v___y_3995_ = v___y_4005_;
v___y_3996_ = v___y_4003_;
v___y_3997_ = v___y_4004_;
v___y_3998_ = v___y_4007_;
v___y_3999_ = v___y_4006_;
goto v___jp_3993_;
}
else
{
lean_object* v___x_4012_; lean_object* v___x_4013_; lean_object* v___x_4014_; lean_object* v___x_4015_; 
lean_dec(v_val_3904_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v___x_4012_ = lean_box(v___x_3883_);
v___x_4013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
v___x_4014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4014_, 0, v___x_4013_);
lean_ctor_set(v___x_4014_, 1, v___x_3908_);
v___x_4015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4015_, 0, v___x_4014_);
v_a_3890_ = v___x_4015_;
goto v___jp_3889_;
}
}
else
{
lean_object* v_a_4016_; lean_object* v___x_4018_; uint8_t v_isShared_4019_; uint8_t v_isSharedCheck_4023_; 
lean_dec(v_val_3904_);
lean_del_object(v___x_3887_);
lean_dec(v_snd_3885_);
lean_dec(v_mvarId_3873_);
lean_dec_ref(v_config_3872_);
v_a_4016_ = lean_ctor_get(v___x_4009_, 0);
v_isSharedCheck_4023_ = !lean_is_exclusive(v___x_4009_);
if (v_isSharedCheck_4023_ == 0)
{
v___x_4018_ = v___x_4009_;
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
else
{
lean_inc(v_a_4016_);
lean_dec(v___x_4009_);
v___x_4018_ = lean_box(0);
v_isShared_4019_ = v_isSharedCheck_4023_;
goto v_resetjp_4017_;
}
v_resetjp_4017_:
{
lean_object* v___x_4021_; 
if (v_isShared_4019_ == 0)
{
v___x_4021_ = v___x_4018_;
goto v_reusejp_4020_;
}
else
{
lean_object* v_reuseFailAlloc_4022_; 
v_reuseFailAlloc_4022_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4022_, 0, v_a_4016_);
v___x_4021_ = v_reuseFailAlloc_4022_;
goto v_reusejp_4020_;
}
v_reusejp_4020_:
{
return v___x_4021_;
}
}
}
}
}
}
}
v___jp_3889_:
{
lean_object* v___x_3891_; lean_object* v___x_3893_; 
v___x_3891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3891_, 0, v_a_3890_);
if (v_isShared_3888_ == 0)
{
lean_ctor_set(v___x_3887_, 0, v___x_3891_);
v___x_3893_ = v___x_3887_;
goto v_reusejp_3892_;
}
else
{
lean_object* v_reuseFailAlloc_3895_; 
v_reuseFailAlloc_3895_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3895_, 0, v___x_3891_);
lean_ctor_set(v_reuseFailAlloc_3895_, 1, v_snd_3885_);
v___x_3893_ = v_reuseFailAlloc_3895_;
goto v_reusejp_3892_;
}
v_reusejp_3892_:
{
lean_object* v___x_3894_; 
v___x_3894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3894_, 0, v___x_3893_);
return v___x_3894_;
}
}
v___jp_3897_:
{
lean_object* v___x_3899_; size_t v___x_3900_; size_t v___x_3901_; lean_object* v___x_3902_; 
v___x_3899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3899_, 0, v___x_3896_);
lean_ctor_set(v___x_3899_, 1, v_a_3898_);
v___x_3900_ = ((size_t)1ULL);
v___x_3901_ = lean_usize_add(v_i_3876_, v___x_3900_);
v___x_3902_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2_spec__3(v_config_3872_, v_mvarId_3873_, v_as_3874_, v_sz_3875_, v___x_3901_, v___x_3899_, v___y_3878_, v___y_3879_, v___y_3880_, v___y_3881_);
return v___x_3902_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2___boxed(lean_object* v_config_4557_, lean_object* v_mvarId_4558_, lean_object* v_as_4559_, lean_object* v_sz_4560_, lean_object* v_i_4561_, lean_object* v_b_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_){
_start:
{
size_t v_sz_boxed_4568_; size_t v_i_boxed_4569_; lean_object* v_res_4570_; 
v_sz_boxed_4568_ = lean_unbox_usize(v_sz_4560_);
lean_dec(v_sz_4560_);
v_i_boxed_4569_ = lean_unbox_usize(v_i_4561_);
lean_dec(v_i_4561_);
v_res_4570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4557_, v_mvarId_4558_, v_as_4559_, v_sz_boxed_4568_, v_i_boxed_4569_, v_b_4562_, v___y_4563_, v___y_4564_, v___y_4565_, v___y_4566_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
lean_dec(v___y_4564_);
lean_dec_ref(v___y_4563_);
lean_dec_ref(v_as_4559_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(lean_object* v_init_4571_, lean_object* v_config_4572_, lean_object* v_mvarId_4573_, lean_object* v_n_4574_, lean_object* v_b_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_, lean_object* v___y_4579_){
_start:
{
if (lean_obj_tag(v_n_4574_) == 0)
{
lean_object* v_cs_4581_; lean_object* v___x_4582_; lean_object* v___x_4583_; size_t v_sz_4584_; size_t v___x_4585_; lean_object* v___x_4586_; 
v_cs_4581_ = lean_ctor_get(v_n_4574_, 0);
v___x_4582_ = lean_box(0);
v___x_4583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4583_, 0, v___x_4582_);
lean_ctor_set(v___x_4583_, 1, v_b_4575_);
v_sz_4584_ = lean_array_size(v_cs_4581_);
v___x_4585_ = ((size_t)0ULL);
v___x_4586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4571_, v_config_4572_, v_mvarId_4573_, v_cs_4581_, v_sz_4584_, v___x_4585_, v___x_4583_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
if (lean_obj_tag(v___x_4586_) == 0)
{
lean_object* v_a_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4601_; 
v_a_4587_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4601_ == 0)
{
v___x_4589_ = v___x_4586_;
v_isShared_4590_ = v_isSharedCheck_4601_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_a_4587_);
lean_dec(v___x_4586_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4601_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v_fst_4591_; 
v_fst_4591_ = lean_ctor_get(v_a_4587_, 0);
if (lean_obj_tag(v_fst_4591_) == 0)
{
lean_object* v_snd_4592_; lean_object* v___x_4593_; lean_object* v___x_4595_; 
v_snd_4592_ = lean_ctor_get(v_a_4587_, 1);
lean_inc(v_snd_4592_);
lean_dec(v_a_4587_);
v___x_4593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4593_, 0, v_snd_4592_);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 0, v___x_4593_);
v___x_4595_ = v___x_4589_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v___x_4593_);
v___x_4595_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
return v___x_4595_;
}
}
else
{
lean_object* v_val_4597_; lean_object* v___x_4599_; 
lean_inc_ref(v_fst_4591_);
lean_dec(v_a_4587_);
v_val_4597_ = lean_ctor_get(v_fst_4591_, 0);
lean_inc(v_val_4597_);
lean_dec_ref_known(v_fst_4591_, 1);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 0, v_val_4597_);
v___x_4599_ = v___x_4589_;
goto v_reusejp_4598_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v_val_4597_);
v___x_4599_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4598_;
}
v_reusejp_4598_:
{
return v___x_4599_;
}
}
}
}
else
{
lean_object* v_a_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4609_; 
v_a_4602_ = lean_ctor_get(v___x_4586_, 0);
v_isSharedCheck_4609_ = !lean_is_exclusive(v___x_4586_);
if (v_isSharedCheck_4609_ == 0)
{
v___x_4604_ = v___x_4586_;
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_a_4602_);
lean_dec(v___x_4586_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4609_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
lean_object* v___x_4607_; 
if (v_isShared_4605_ == 0)
{
v___x_4607_ = v___x_4604_;
goto v_reusejp_4606_;
}
else
{
lean_object* v_reuseFailAlloc_4608_; 
v_reuseFailAlloc_4608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4608_, 0, v_a_4602_);
v___x_4607_ = v_reuseFailAlloc_4608_;
goto v_reusejp_4606_;
}
v_reusejp_4606_:
{
return v___x_4607_;
}
}
}
}
else
{
lean_object* v_vs_4610_; lean_object* v___x_4611_; lean_object* v___x_4612_; size_t v_sz_4613_; size_t v___x_4614_; lean_object* v___x_4615_; 
v_vs_4610_ = lean_ctor_get(v_n_4574_, 0);
v___x_4611_ = lean_box(0);
v___x_4612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4612_, 0, v___x_4611_);
lean_ctor_set(v___x_4612_, 1, v_b_4575_);
v_sz_4613_ = lean_array_size(v_vs_4610_);
v___x_4614_ = ((size_t)0ULL);
v___x_4615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__2(v_config_4572_, v_mvarId_4573_, v_vs_4610_, v_sz_4613_, v___x_4614_, v___x_4612_, v___y_4576_, v___y_4577_, v___y_4578_, v___y_4579_);
if (lean_obj_tag(v___x_4615_) == 0)
{
lean_object* v_a_4616_; lean_object* v___x_4618_; uint8_t v_isShared_4619_; uint8_t v_isSharedCheck_4630_; 
v_a_4616_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4630_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4630_ == 0)
{
v___x_4618_ = v___x_4615_;
v_isShared_4619_ = v_isSharedCheck_4630_;
goto v_resetjp_4617_;
}
else
{
lean_inc(v_a_4616_);
lean_dec(v___x_4615_);
v___x_4618_ = lean_box(0);
v_isShared_4619_ = v_isSharedCheck_4630_;
goto v_resetjp_4617_;
}
v_resetjp_4617_:
{
lean_object* v_fst_4620_; 
v_fst_4620_ = lean_ctor_get(v_a_4616_, 0);
if (lean_obj_tag(v_fst_4620_) == 0)
{
lean_object* v_snd_4621_; lean_object* v___x_4622_; lean_object* v___x_4624_; 
v_snd_4621_ = lean_ctor_get(v_a_4616_, 1);
lean_inc(v_snd_4621_);
lean_dec(v_a_4616_);
v___x_4622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4622_, 0, v_snd_4621_);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v___x_4622_);
v___x_4624_ = v___x_4618_;
goto v_reusejp_4623_;
}
else
{
lean_object* v_reuseFailAlloc_4625_; 
v_reuseFailAlloc_4625_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4625_, 0, v___x_4622_);
v___x_4624_ = v_reuseFailAlloc_4625_;
goto v_reusejp_4623_;
}
v_reusejp_4623_:
{
return v___x_4624_;
}
}
else
{
lean_object* v_val_4626_; lean_object* v___x_4628_; 
lean_inc_ref(v_fst_4620_);
lean_dec(v_a_4616_);
v_val_4626_ = lean_ctor_get(v_fst_4620_, 0);
lean_inc(v_val_4626_);
lean_dec_ref_known(v_fst_4620_, 1);
if (v_isShared_4619_ == 0)
{
lean_ctor_set(v___x_4618_, 0, v_val_4626_);
v___x_4628_ = v___x_4618_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4629_; 
v_reuseFailAlloc_4629_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4629_, 0, v_val_4626_);
v___x_4628_ = v_reuseFailAlloc_4629_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
return v___x_4628_;
}
}
}
}
else
{
lean_object* v_a_4631_; lean_object* v___x_4633_; uint8_t v_isShared_4634_; uint8_t v_isSharedCheck_4638_; 
v_a_4631_ = lean_ctor_get(v___x_4615_, 0);
v_isSharedCheck_4638_ = !lean_is_exclusive(v___x_4615_);
if (v_isSharedCheck_4638_ == 0)
{
v___x_4633_ = v___x_4615_;
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
else
{
lean_inc(v_a_4631_);
lean_dec(v___x_4615_);
v___x_4633_ = lean_box(0);
v_isShared_4634_ = v_isSharedCheck_4638_;
goto v_resetjp_4632_;
}
v_resetjp_4632_:
{
lean_object* v___x_4636_; 
if (v_isShared_4634_ == 0)
{
v___x_4636_ = v___x_4633_;
goto v_reusejp_4635_;
}
else
{
lean_object* v_reuseFailAlloc_4637_; 
v_reuseFailAlloc_4637_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4637_, 0, v_a_4631_);
v___x_4636_ = v_reuseFailAlloc_4637_;
goto v_reusejp_4635_;
}
v_reusejp_4635_:
{
return v___x_4636_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(lean_object* v_init_4639_, lean_object* v_config_4640_, lean_object* v_mvarId_4641_, lean_object* v_as_4642_, size_t v_sz_4643_, size_t v_i_4644_, lean_object* v_b_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
uint8_t v___x_4651_; 
v___x_4651_ = lean_usize_dec_lt(v_i_4644_, v_sz_4643_);
if (v___x_4651_ == 0)
{
lean_object* v___x_4652_; 
lean_dec(v_mvarId_4641_);
lean_dec_ref(v_config_4640_);
v___x_4652_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4652_, 0, v_b_4645_);
return v___x_4652_;
}
else
{
lean_object* v_snd_4653_; lean_object* v___x_4655_; uint8_t v_isShared_4656_; uint8_t v_isSharedCheck_4687_; 
v_snd_4653_ = lean_ctor_get(v_b_4645_, 1);
v_isSharedCheck_4687_ = !lean_is_exclusive(v_b_4645_);
if (v_isSharedCheck_4687_ == 0)
{
lean_object* v_unused_4688_; 
v_unused_4688_ = lean_ctor_get(v_b_4645_, 0);
lean_dec(v_unused_4688_);
v___x_4655_ = v_b_4645_;
v_isShared_4656_ = v_isSharedCheck_4687_;
goto v_resetjp_4654_;
}
else
{
lean_inc(v_snd_4653_);
lean_dec(v_b_4645_);
v___x_4655_ = lean_box(0);
v_isShared_4656_ = v_isSharedCheck_4687_;
goto v_resetjp_4654_;
}
v_resetjp_4654_:
{
lean_object* v___x_4657_; lean_object* v_a_4658_; lean_object* v___x_4659_; 
v___x_4657_ = lean_box(0);
v_a_4658_ = lean_array_uget_borrowed(v_as_4642_, v_i_4644_);
lean_inc(v_snd_4653_);
lean_inc(v_mvarId_4641_);
lean_inc_ref(v_config_4640_);
v___x_4659_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4639_, v_config_4640_, v_mvarId_4641_, v_a_4658_, v_snd_4653_, v___y_4646_, v___y_4647_, v___y_4648_, v___y_4649_);
if (lean_obj_tag(v___x_4659_) == 0)
{
lean_object* v_a_4660_; lean_object* v___x_4662_; uint8_t v_isShared_4663_; uint8_t v_isSharedCheck_4678_; 
v_a_4660_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4678_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4678_ == 0)
{
v___x_4662_ = v___x_4659_;
v_isShared_4663_ = v_isSharedCheck_4678_;
goto v_resetjp_4661_;
}
else
{
lean_inc(v_a_4660_);
lean_dec(v___x_4659_);
v___x_4662_ = lean_box(0);
v_isShared_4663_ = v_isSharedCheck_4678_;
goto v_resetjp_4661_;
}
v_resetjp_4661_:
{
if (lean_obj_tag(v_a_4660_) == 0)
{
lean_object* v___x_4664_; lean_object* v___x_4666_; 
lean_dec(v_mvarId_4641_);
lean_dec_ref(v_config_4640_);
v___x_4664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4664_, 0, v_a_4660_);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 0, v___x_4664_);
v___x_4666_ = v___x_4655_;
goto v_reusejp_4665_;
}
else
{
lean_object* v_reuseFailAlloc_4670_; 
v_reuseFailAlloc_4670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4670_, 0, v___x_4664_);
lean_ctor_set(v_reuseFailAlloc_4670_, 1, v_snd_4653_);
v___x_4666_ = v_reuseFailAlloc_4670_;
goto v_reusejp_4665_;
}
v_reusejp_4665_:
{
lean_object* v___x_4668_; 
if (v_isShared_4663_ == 0)
{
lean_ctor_set(v___x_4662_, 0, v___x_4666_);
v___x_4668_ = v___x_4662_;
goto v_reusejp_4667_;
}
else
{
lean_object* v_reuseFailAlloc_4669_; 
v_reuseFailAlloc_4669_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4669_, 0, v___x_4666_);
v___x_4668_ = v_reuseFailAlloc_4669_;
goto v_reusejp_4667_;
}
v_reusejp_4667_:
{
return v___x_4668_;
}
}
}
else
{
lean_object* v_a_4671_; lean_object* v___x_4673_; 
lean_del_object(v___x_4662_);
lean_dec(v_snd_4653_);
v_a_4671_ = lean_ctor_get(v_a_4660_, 0);
lean_inc(v_a_4671_);
lean_dec_ref_known(v_a_4660_, 1);
if (v_isShared_4656_ == 0)
{
lean_ctor_set(v___x_4655_, 1, v_a_4671_);
lean_ctor_set(v___x_4655_, 0, v___x_4657_);
v___x_4673_ = v___x_4655_;
goto v_reusejp_4672_;
}
else
{
lean_object* v_reuseFailAlloc_4677_; 
v_reuseFailAlloc_4677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4677_, 0, v___x_4657_);
lean_ctor_set(v_reuseFailAlloc_4677_, 1, v_a_4671_);
v___x_4673_ = v_reuseFailAlloc_4677_;
goto v_reusejp_4672_;
}
v_reusejp_4672_:
{
size_t v___x_4674_; size_t v___x_4675_; 
v___x_4674_ = ((size_t)1ULL);
v___x_4675_ = lean_usize_add(v_i_4644_, v___x_4674_);
v_i_4644_ = v___x_4675_;
v_b_4645_ = v___x_4673_;
goto _start;
}
}
}
}
else
{
lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4686_; 
lean_del_object(v___x_4655_);
lean_dec(v_snd_4653_);
lean_dec(v_mvarId_4641_);
lean_dec_ref(v_config_4640_);
v_a_4679_ = lean_ctor_get(v___x_4659_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4659_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4681_ = v___x_4659_;
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4659_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4686_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4684_; 
if (v_isShared_4682_ == 0)
{
v___x_4684_ = v___x_4681_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v_a_4679_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1___boxed(lean_object* v_init_4689_, lean_object* v_config_4690_, lean_object* v_mvarId_4691_, lean_object* v_as_4692_, lean_object* v_sz_4693_, lean_object* v_i_4694_, lean_object* v_b_4695_, lean_object* v___y_4696_, lean_object* v___y_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
size_t v_sz_boxed_4701_; size_t v_i_boxed_4702_; lean_object* v_res_4703_; 
v_sz_boxed_4701_ = lean_unbox_usize(v_sz_4693_);
lean_dec(v_sz_4693_);
v_i_boxed_4702_ = lean_unbox_usize(v_i_4694_);
lean_dec(v_i_4694_);
v_res_4703_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0_spec__1(v_init_4689_, v_config_4690_, v_mvarId_4691_, v_as_4692_, v_sz_boxed_4701_, v_i_boxed_4702_, v_b_4695_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
lean_dec(v___y_4697_);
lean_dec_ref(v___y_4696_);
lean_dec_ref(v_as_4692_);
lean_dec_ref(v_init_4689_);
return v_res_4703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0___boxed(lean_object* v_init_4704_, lean_object* v_config_4705_, lean_object* v_mvarId_4706_, lean_object* v_n_4707_, lean_object* v_b_4708_, lean_object* v___y_4709_, lean_object* v___y_4710_, lean_object* v___y_4711_, lean_object* v___y_4712_, lean_object* v___y_4713_){
_start:
{
lean_object* v_res_4714_; 
v_res_4714_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4704_, v_config_4705_, v_mvarId_4706_, v_n_4707_, v_b_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_);
lean_dec(v___y_4712_);
lean_dec_ref(v___y_4711_);
lean_dec(v___y_4710_);
lean_dec_ref(v___y_4709_);
lean_dec_ref(v_n_4707_);
lean_dec_ref(v_init_4704_);
return v_res_4714_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(lean_object* v_config_4715_, lean_object* v_mvarId_4716_, lean_object* v_t_4717_, lean_object* v_init_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_, lean_object* v___y_4722_){
_start:
{
lean_object* v_root_4724_; lean_object* v_tail_4725_; lean_object* v___x_4726_; 
v_root_4724_ = lean_ctor_get(v_t_4717_, 0);
v_tail_4725_ = lean_ctor_get(v_t_4717_, 1);
lean_inc(v_mvarId_4716_);
lean_inc_ref(v_config_4715_);
lean_inc_ref(v_init_4718_);
v___x_4726_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__0(v_init_4718_, v_config_4715_, v_mvarId_4716_, v_root_4724_, v_init_4718_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
lean_dec_ref(v_init_4718_);
if (lean_obj_tag(v___x_4726_) == 0)
{
lean_object* v_a_4727_; lean_object* v___x_4729_; uint8_t v_isShared_4730_; uint8_t v_isSharedCheck_4763_; 
v_a_4727_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4729_ = v___x_4726_;
v_isShared_4730_ = v_isSharedCheck_4763_;
goto v_resetjp_4728_;
}
else
{
lean_inc(v_a_4727_);
lean_dec(v___x_4726_);
v___x_4729_ = lean_box(0);
v_isShared_4730_ = v_isSharedCheck_4763_;
goto v_resetjp_4728_;
}
v_resetjp_4728_:
{
if (lean_obj_tag(v_a_4727_) == 0)
{
lean_object* v_a_4731_; lean_object* v___x_4733_; 
lean_dec(v_mvarId_4716_);
lean_dec_ref(v_config_4715_);
v_a_4731_ = lean_ctor_get(v_a_4727_, 0);
lean_inc(v_a_4731_);
lean_dec_ref_known(v_a_4727_, 1);
if (v_isShared_4730_ == 0)
{
lean_ctor_set(v___x_4729_, 0, v_a_4731_);
v___x_4733_ = v___x_4729_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4731_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
else
{
lean_object* v_a_4735_; lean_object* v___x_4736_; lean_object* v___x_4737_; size_t v_sz_4738_; size_t v___x_4739_; lean_object* v___x_4740_; 
lean_del_object(v___x_4729_);
v_a_4735_ = lean_ctor_get(v_a_4727_, 0);
lean_inc(v_a_4735_);
lean_dec_ref_known(v_a_4727_, 1);
v___x_4736_ = lean_box(0);
v___x_4737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4737_, 0, v___x_4736_);
lean_ctor_set(v___x_4737_, 1, v_a_4735_);
v_sz_4738_ = lean_array_size(v_tail_4725_);
v___x_4739_ = ((size_t)0ULL);
v___x_4740_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0_spec__1(v_config_4715_, v_mvarId_4716_, v_tail_4725_, v_sz_4738_, v___x_4739_, v___x_4737_, v___y_4719_, v___y_4720_, v___y_4721_, v___y_4722_);
if (lean_obj_tag(v___x_4740_) == 0)
{
lean_object* v_a_4741_; lean_object* v___x_4743_; uint8_t v_isShared_4744_; uint8_t v_isSharedCheck_4754_; 
v_a_4741_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4754_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4754_ == 0)
{
v___x_4743_ = v___x_4740_;
v_isShared_4744_ = v_isSharedCheck_4754_;
goto v_resetjp_4742_;
}
else
{
lean_inc(v_a_4741_);
lean_dec(v___x_4740_);
v___x_4743_ = lean_box(0);
v_isShared_4744_ = v_isSharedCheck_4754_;
goto v_resetjp_4742_;
}
v_resetjp_4742_:
{
lean_object* v_fst_4745_; 
v_fst_4745_ = lean_ctor_get(v_a_4741_, 0);
if (lean_obj_tag(v_fst_4745_) == 0)
{
lean_object* v_snd_4746_; lean_object* v___x_4748_; 
v_snd_4746_ = lean_ctor_get(v_a_4741_, 1);
lean_inc(v_snd_4746_);
lean_dec(v_a_4741_);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v_snd_4746_);
v___x_4748_ = v___x_4743_;
goto v_reusejp_4747_;
}
else
{
lean_object* v_reuseFailAlloc_4749_; 
v_reuseFailAlloc_4749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_snd_4746_);
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
lean_inc_ref(v_fst_4745_);
lean_dec(v_a_4741_);
v_val_4750_ = lean_ctor_get(v_fst_4745_, 0);
lean_inc(v_val_4750_);
lean_dec_ref_known(v_fst_4745_, 1);
if (v_isShared_4744_ == 0)
{
lean_ctor_set(v___x_4743_, 0, v_val_4750_);
v___x_4752_ = v___x_4743_;
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
v_a_4755_ = lean_ctor_get(v___x_4740_, 0);
v_isSharedCheck_4762_ = !lean_is_exclusive(v___x_4740_);
if (v_isSharedCheck_4762_ == 0)
{
v___x_4757_ = v___x_4740_;
v_isShared_4758_ = v_isSharedCheck_4762_;
goto v_resetjp_4756_;
}
else
{
lean_inc(v_a_4755_);
lean_dec(v___x_4740_);
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
}
}
else
{
lean_object* v_a_4764_; lean_object* v___x_4766_; uint8_t v_isShared_4767_; uint8_t v_isSharedCheck_4771_; 
lean_dec(v_mvarId_4716_);
lean_dec_ref(v_config_4715_);
v_a_4764_ = lean_ctor_get(v___x_4726_, 0);
v_isSharedCheck_4771_ = !lean_is_exclusive(v___x_4726_);
if (v_isSharedCheck_4771_ == 0)
{
v___x_4766_ = v___x_4726_;
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
else
{
lean_inc(v_a_4764_);
lean_dec(v___x_4726_);
v___x_4766_ = lean_box(0);
v_isShared_4767_ = v_isSharedCheck_4771_;
goto v_resetjp_4765_;
}
v_resetjp_4765_:
{
lean_object* v___x_4769_; 
if (v_isShared_4767_ == 0)
{
v___x_4769_ = v___x_4766_;
goto v_reusejp_4768_;
}
else
{
lean_object* v_reuseFailAlloc_4770_; 
v_reuseFailAlloc_4770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4770_, 0, v_a_4764_);
v___x_4769_ = v_reuseFailAlloc_4770_;
goto v_reusejp_4768_;
}
v_reusejp_4768_:
{
return v___x_4769_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0___boxed(lean_object* v_config_4772_, lean_object* v_mvarId_4773_, lean_object* v_t_4774_, lean_object* v_init_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_, lean_object* v___y_4780_){
_start:
{
lean_object* v_res_4781_; 
v_res_4781_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4772_, v_mvarId_4773_, v_t_4774_, v_init_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
lean_dec(v___y_4779_);
lean_dec_ref(v___y_4778_);
lean_dec(v___y_4777_);
lean_dec_ref(v___y_4776_);
lean_dec_ref(v_t_4774_);
return v_res_4781_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0(lean_object* v_mvarId_4782_, lean_object* v___x_4783_, lean_object* v_config_4784_, lean_object* v___y_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_, lean_object* v___y_4788_){
_start:
{
lean_object* v___x_4790_; 
lean_inc(v_mvarId_4782_);
v___x_4790_ = l_Lean_MVarId_checkNotAssigned(v_mvarId_4782_, v___x_4783_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4790_) == 0)
{
lean_object* v___x_4791_; 
lean_dec_ref_known(v___x_4790_, 1);
lean_inc(v_mvarId_4782_);
v___x_4791_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_nestedFalseElim(v_mvarId_4782_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4791_) == 0)
{
lean_object* v_a_4792_; lean_object* v___x_4794_; uint8_t v_isShared_4795_; uint8_t v_isSharedCheck_4825_; 
v_a_4792_ = lean_ctor_get(v___x_4791_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4794_ = v___x_4791_;
v_isShared_4795_ = v_isSharedCheck_4825_;
goto v_resetjp_4793_;
}
else
{
lean_inc(v_a_4792_);
lean_dec(v___x_4791_);
v___x_4794_ = lean_box(0);
v_isShared_4795_ = v_isSharedCheck_4825_;
goto v_resetjp_4793_;
}
v_resetjp_4793_:
{
uint8_t v___x_4796_; 
v___x_4796_ = lean_unbox(v_a_4792_);
if (v___x_4796_ == 0)
{
lean_object* v_lctx_4797_; lean_object* v_decls_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; 
lean_del_object(v___x_4794_);
v_lctx_4797_ = lean_ctor_get(v___y_4785_, 2);
v_decls_4798_ = lean_ctor_get(v_lctx_4797_, 1);
v___x_4799_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_ElimEmptyInductive_elim_spec__2___closed__0));
v___x_4800_ = l_Lean_PersistentArray_forIn___at___00Lean_MVarId_contradictionCore_spec__0(v_config_4784_, v_mvarId_4782_, v_decls_4798_, v___x_4799_, v___y_4785_, v___y_4786_, v___y_4787_, v___y_4788_);
if (lean_obj_tag(v___x_4800_) == 0)
{
lean_object* v_a_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4813_; 
v_a_4801_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4813_ == 0)
{
v___x_4803_ = v___x_4800_;
v_isShared_4804_ = v_isSharedCheck_4813_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_a_4801_);
lean_dec(v___x_4800_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4813_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v_fst_4805_; 
v_fst_4805_ = lean_ctor_get(v_a_4801_, 0);
lean_inc(v_fst_4805_);
lean_dec(v_a_4801_);
if (lean_obj_tag(v_fst_4805_) == 0)
{
lean_object* v___x_4807_; 
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 0, v_a_4792_);
v___x_4807_ = v___x_4803_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4808_; 
v_reuseFailAlloc_4808_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4808_, 0, v_a_4792_);
v___x_4807_ = v_reuseFailAlloc_4808_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
return v___x_4807_;
}
}
else
{
lean_object* v_val_4809_; lean_object* v___x_4811_; 
lean_dec(v_a_4792_);
v_val_4809_ = lean_ctor_get(v_fst_4805_, 0);
lean_inc(v_val_4809_);
lean_dec_ref_known(v_fst_4805_, 1);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 0, v_val_4809_);
v___x_4811_ = v___x_4803_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v_val_4809_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
else
{
lean_object* v_a_4814_; lean_object* v___x_4816_; uint8_t v_isShared_4817_; uint8_t v_isSharedCheck_4821_; 
lean_dec(v_a_4792_);
v_a_4814_ = lean_ctor_get(v___x_4800_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4800_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4816_ = v___x_4800_;
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
else
{
lean_inc(v_a_4814_);
lean_dec(v___x_4800_);
v___x_4816_ = lean_box(0);
v_isShared_4817_ = v_isSharedCheck_4821_;
goto v_resetjp_4815_;
}
v_resetjp_4815_:
{
lean_object* v___x_4819_; 
if (v_isShared_4817_ == 0)
{
v___x_4819_ = v___x_4816_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v_a_4814_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
else
{
lean_object* v___x_4823_; 
lean_dec_ref(v_config_4784_);
lean_dec(v_mvarId_4782_);
if (v_isShared_4795_ == 0)
{
v___x_4823_ = v___x_4794_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4792_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
else
{
lean_dec_ref(v_config_4784_);
lean_dec(v_mvarId_4782_);
return v___x_4791_;
}
}
else
{
lean_object* v_a_4826_; lean_object* v___x_4828_; uint8_t v_isShared_4829_; uint8_t v_isSharedCheck_4833_; 
lean_dec_ref(v_config_4784_);
lean_dec(v_mvarId_4782_);
v_a_4826_ = lean_ctor_get(v___x_4790_, 0);
v_isSharedCheck_4833_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4833_ == 0)
{
v___x_4828_ = v___x_4790_;
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
else
{
lean_inc(v_a_4826_);
lean_dec(v___x_4790_);
v___x_4828_ = lean_box(0);
v_isShared_4829_ = v_isSharedCheck_4833_;
goto v_resetjp_4827_;
}
v_resetjp_4827_:
{
lean_object* v___x_4831_; 
if (v_isShared_4829_ == 0)
{
v___x_4831_ = v___x_4828_;
goto v_reusejp_4830_;
}
else
{
lean_object* v_reuseFailAlloc_4832_; 
v_reuseFailAlloc_4832_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4832_, 0, v_a_4826_);
v___x_4831_ = v_reuseFailAlloc_4832_;
goto v_reusejp_4830_;
}
v_reusejp_4830_:
{
return v___x_4831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___lam__0___boxed(lean_object* v_mvarId_4834_, lean_object* v___x_4835_, lean_object* v_config_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_, lean_object* v___y_4840_, lean_object* v___y_4841_){
_start:
{
lean_object* v_res_4842_; 
v_res_4842_ = l_Lean_MVarId_contradictionCore___lam__0(v_mvarId_4834_, v___x_4835_, v_config_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_);
lean_dec(v___y_4840_);
lean_dec_ref(v___y_4839_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
return v_res_4842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore(lean_object* v_mvarId_4845_, lean_object* v_config_4846_, lean_object* v_a_4847_, lean_object* v_a_4848_, lean_object* v_a_4849_, lean_object* v_a_4850_){
_start:
{
lean_object* v___x_4852_; lean_object* v___f_4853_; lean_object* v___x_4854_; 
v___x_4852_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
lean_inc(v_mvarId_4845_);
v___f_4853_ = lean_alloc_closure((void*)(l_Lean_MVarId_contradictionCore___lam__0___boxed), 8, 3);
lean_closure_set(v___f_4853_, 0, v_mvarId_4845_);
lean_closure_set(v___f_4853_, 1, v___x_4852_);
lean_closure_set(v___f_4853_, 2, v_config_4846_);
v___x_4854_ = l_Lean_MVarId_withContext___at___00__private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_elimEmptyInductive_spec__1___redArg(v_mvarId_4845_, v___f_4853_, v_a_4847_, v_a_4848_, v_a_4849_, v_a_4850_);
return v___x_4854_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradictionCore___boxed(lean_object* v_mvarId_4855_, lean_object* v_config_4856_, lean_object* v_a_4857_, lean_object* v_a_4858_, lean_object* v_a_4859_, lean_object* v_a_4860_, lean_object* v_a_4861_){
_start:
{
lean_object* v_res_4862_; 
v_res_4862_ = l_Lean_MVarId_contradictionCore(v_mvarId_4855_, v_config_4856_, v_a_4857_, v_a_4858_, v_a_4859_, v_a_4860_);
lean_dec(v_a_4860_);
lean_dec_ref(v_a_4859_);
lean_dec(v_a_4858_);
lean_dec_ref(v_a_4857_);
return v_res_4862_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction(lean_object* v_mvarId_4863_, lean_object* v_config_4864_, lean_object* v_a_4865_, lean_object* v_a_4866_, lean_object* v_a_4867_, lean_object* v_a_4868_){
_start:
{
lean_object* v___x_4870_; 
lean_inc(v_mvarId_4863_);
v___x_4870_ = l_Lean_MVarId_contradictionCore(v_mvarId_4863_, v_config_4864_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
if (lean_obj_tag(v___x_4870_) == 0)
{
lean_object* v_a_4871_; lean_object* v___x_4873_; uint8_t v_isShared_4874_; uint8_t v_isSharedCheck_4883_; 
v_a_4871_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4883_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4883_ == 0)
{
v___x_4873_ = v___x_4870_;
v_isShared_4874_ = v_isSharedCheck_4883_;
goto v_resetjp_4872_;
}
else
{
lean_inc(v_a_4871_);
lean_dec(v___x_4870_);
v___x_4873_ = lean_box(0);
v_isShared_4874_ = v_isSharedCheck_4883_;
goto v_resetjp_4872_;
}
v_resetjp_4872_:
{
uint8_t v___x_4875_; 
v___x_4875_ = lean_unbox(v_a_4871_);
lean_dec(v_a_4871_);
if (v___x_4875_ == 0)
{
lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; 
lean_del_object(v___x_4873_);
v___x_4876_ = ((lean_object*)(l_Lean_MVarId_contradictionCore___closed__0));
v___x_4877_ = lean_box(0);
v___x_4878_ = l_Lean_Meta_throwTacticEx___redArg(v___x_4876_, v_mvarId_4863_, v___x_4877_, v_a_4865_, v_a_4866_, v_a_4867_, v_a_4868_);
return v___x_4878_;
}
else
{
lean_object* v___x_4879_; lean_object* v___x_4881_; 
lean_dec(v_mvarId_4863_);
v___x_4879_ = lean_box(0);
if (v_isShared_4874_ == 0)
{
lean_ctor_set(v___x_4873_, 0, v___x_4879_);
v___x_4881_ = v___x_4873_;
goto v_reusejp_4880_;
}
else
{
lean_object* v_reuseFailAlloc_4882_; 
v_reuseFailAlloc_4882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4882_, 0, v___x_4879_);
v___x_4881_ = v_reuseFailAlloc_4882_;
goto v_reusejp_4880_;
}
v_reusejp_4880_:
{
return v___x_4881_;
}
}
}
}
else
{
lean_object* v_a_4884_; lean_object* v___x_4886_; uint8_t v_isShared_4887_; uint8_t v_isSharedCheck_4891_; 
lean_dec(v_mvarId_4863_);
v_a_4884_ = lean_ctor_get(v___x_4870_, 0);
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4870_);
if (v_isSharedCheck_4891_ == 0)
{
v___x_4886_ = v___x_4870_;
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
else
{
lean_inc(v_a_4884_);
lean_dec(v___x_4870_);
v___x_4886_ = lean_box(0);
v_isShared_4887_ = v_isSharedCheck_4891_;
goto v_resetjp_4885_;
}
v_resetjp_4885_:
{
lean_object* v___x_4889_; 
if (v_isShared_4887_ == 0)
{
v___x_4889_ = v___x_4886_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v_a_4884_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_contradiction___boxed(lean_object* v_mvarId_4892_, lean_object* v_config_4893_, lean_object* v_a_4894_, lean_object* v_a_4895_, lean_object* v_a_4896_, lean_object* v_a_4897_, lean_object* v_a_4898_){
_start:
{
lean_object* v_res_4899_; 
v_res_4899_ = l_Lean_MVarId_contradiction(v_mvarId_4892_, v_config_4893_, v_a_4894_, v_a_4895_, v_a_4896_, v_a_4897_);
lean_dec(v_a_4897_);
lean_dec_ref(v_a_4896_);
lean_dec(v_a_4895_);
lean_dec_ref(v_a_4894_);
return v_res_4899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4962_; uint8_t v___x_4963_; lean_object* v___x_4964_; lean_object* v___x_4965_; 
v___x_4962_ = ((lean_object*)(l_Lean_Meta_ElimEmptyInductive_elim___closed__4));
v___x_4963_ = 0;
v___x_4964_ = ((lean_object*)(l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn___closed__24_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_));
v___x_4965_ = l_Lean_registerTraceClass(v___x_4962_, v___x_4963_, v___x_4964_);
return v___x_4965_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2____boxed(lean_object* v_a_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l___private_Lean_Meta_Tactic_Contradiction_0__Lean_Meta_initFn_00___x40_Lean_Meta_Tactic_Contradiction_911661800____hygCtx___hyg_2_();
return v_res_4967_;
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
